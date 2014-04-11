#include "IR.h"
#include "Var.h"
#include "RDom.h"
#include "Scope.h"
#include "IRPrinter.h"
#include "IROperator.h"
#include "IREquality.h"
#include "IRMutator.h"
#include "Substitute.h"
#include "Simplify.h"
#include "ModulusRemainder.h"
#include "Debug.h"
#include "CSE.h"

using std::map;
using std::make_pair;
using std::string;
using std::vector;
using std::ostream;
using std::cerr;
using std::endl;

namespace Halide {
namespace Internal {

template<>
EXPORT RefCount &ref_count<UnionVarContents>(const UnionVarContents *u) {return u->ref_count;}

template<>
EXPORT void destroy<UnionVarContents>(const UnionVarContents *u) {delete u;}

template<>
EXPORT RefCount &ref_count<UnionReductionContents>(const UnionReductionContents *u) {return u->ref_count;}

template<>
EXPORT void destroy<UnionReductionContents>(const UnionReductionContents *u) {delete u;}

// -----------------------------------------------------------------------------

// Does an expression depend on a particular variable?
class ExprDependsOnVar : public IRVisitor {
private:
    using IRVisitor::visit;
    void visit(const Variable *op) {
        if (op->name == var) result = true;
    }
public:
    bool result;
    string var;
    ExprDependsOnVar(string v) : result(false), var(v) {}
};

static bool expr_depends_on_var(Expr e, string v) {
    ExprDependsOnVar depends(v);
    e.accept(&depends);
    return depends.result;
}

// -----------------------------------------------------------------------------

// Substitute UnionReduction call with Function call
class SubstituteUnionWithFunc : public IRMutator {
private:
    using IRMutator::visit;
    void visit(const UnionCall *op) {
        expr = op->union_op.call_as_func(op->args, op->value_index);
    }
public:
    SubstituteUnionWithFunc() {}
};

static Expr substitute_union_with_func(Expr expr) {
    SubstituteUnionWithFunc s;
    return s.mutate(expr);
}

// -----------------------------------------------------------------------------

// Extract the list of union variables in Expr
class ExtractUnionVars : public IRVisitor {
private:
    using IRVisitor::visit;
    void visit(const Variable *op) {
        if (op->reduction_domain.defined()) {
            for (size_t i=0; i<op->reduction_domain.domain().size(); i++) {
                uvars.push_back(UnionVar(
                            op->reduction_domain.domain()[i].min,
                            op->reduction_domain.domain()[i].extent,
                            op->reduction_domain.domain()[i].var));
            }
        }
    }
public:
    vector<UnionVar> uvars;
    ExtractUnionVars() {}
};

static vector<UnionVar> extract_union_vars(vector<Expr> e) {
    vector<UnionVar> uvars;
    for (size_t i=0; i<e.size(); i++) {
        ExtractUnionVars extract;
        e[i].accept(&extract);
        for (size_t j=0; j<extract.uvars.size(); j++) {
            bool uvar_already_found = false;
            UnionVar u = extract.uvars[j];
            for (size_t k=0; k<uvars.size(); k++) {
                if (u.same_as(uvars[k]))
                    uvar_already_found = true;
            }
            if (!uvar_already_found)
                uvars.push_back(u);
        }
    }
    return uvars;
}

// -----------------------------------------------------------------------------

// Are two Expr similar, i.e.
static bool expr_same(Expr e1, Expr e2) {
    Expr e = simplify(e1-e2);
    return e.same_as(Expr(0));
}


// -----------------------------------------------------------------------------

UnionVar::UnionVar() : _contents(new UnionVarContents) {}
UnionVar::UnionVar(const IntrusivePtr<UnionVarContents> &c) : _contents(c) {}

UnionVar::UnionVar(Expr m, Expr e) {
    if (!_contents.defined()) {
        _contents = new UnionVarContents;
    }
    _contents.ptr->var = unique_name("r");
    _contents.ptr->min = m;
    _contents.ptr->extent = e;

    ReductionVariable v = {_contents.ptr->var, m, e};
    _contents.ptr->domain = ReductionDomain(vec(v));
}

UnionVar::UnionVar(Expr m, Expr e, std::string n) {
    if (!_contents.defined()) {
        _contents = new UnionVarContents;
    }
    _contents.ptr->var = n;
    _contents.ptr->min = m;
    _contents.ptr->extent = e;

    ReductionVariable v = {_contents.ptr->var, m, e};
    _contents.ptr->domain = ReductionDomain(vec(v));
}

string UnionVar::name()   const { return _contents.ptr->var;    }
Expr   UnionVar::min()    const { return _contents.ptr->min;    }
Expr   UnionVar::extent() const { return _contents.ptr->extent; }

bool UnionVar::same_as(UnionVar b) const {
    bool result = false;
    result |= (_contents.ptr->var == b._contents.ptr->var);
    result |= (_contents.ptr->min.same_as(b._contents.ptr->min));
    result |= (_contents.ptr->extent.same_as(b._contents.ptr->extent));
    // TODO: compare reduction domain too
    return result;
}

UnionVar::operator Expr() const {
    return Variable::make(Int(32),
            _contents.ptr->var,
            _contents.ptr->domain);
}

// -----------------------------------------------------------------------------

std::string erase_all_occurances(std::string& subject, std::string search) {
    size_t pos = 0;
    while ((pos = subject.find(search, pos)) != std::string::npos) {
        subject.erase(pos, search.length());
    }
    return subject;
}

// -----------------------------------------------------------------------------

UnionReduction::UnionReduction() : _contents(NULL) {
}

UnionReduction::UnionReduction(string name) : _contents(new UnionReductionContents) {
    _contents.ptr->name = unique_name(name);
}

UnionReduction::UnionReduction(const IntrusivePtr<UnionReductionContents> &c) : _contents(c) {}

UnionReduction::UnionReduction(Expr in, vector<string> args, string name) :
    UnionReduction(vec(in), args, name) {}

UnionReduction::UnionReduction(vector<Expr> in, vector<string> args, string name) {
    if (!_contents.defined()) {
        _contents = new UnionReductionContents;
    }

    _contents.ptr->name  = name;
    _contents.ptr->input = in;
    _contents.ptr->args  = args;
    _contents.ptr->uvars = extract_union_vars(in);

    // remove all unused union variables
    for (size_t i=0; i<_contents.ptr->uvars.size(); i++) {
        string v = _contents.ptr->uvars[i].name();
        bool uvar_needed = false;
        for (size_t j=0; j<_contents.ptr->input.size(); j++) {
            uvar_needed |= expr_depends_on_var(_contents.ptr->input[j], v);
        }
        if (!uvar_needed) {
            cerr << "Warning: Expression doesn't depend upon union variable " << v << endl;
            _contents.ptr->uvars.erase(_contents.ptr->uvars.begin()+i);
            i--;
        }
    }

    map<string,string> arg_to_uvar;
    map<string,string> uvar_to_arg;
    for (size_t j=0; j<_contents.ptr->uvars.size(); j++) {
        for (size_t i=0; i<_contents.ptr->args.size(); i++) {
            if (expr_depends_on_var(_contents.ptr->uvars[j].min()   , _contents.ptr->args[i]) ||
                    expr_depends_on_var(_contents.ptr->uvars[j].extent(), _contents.ptr->args[i]))
            {
                if (uvar_to_arg.find(_contents.ptr->uvars[j].name()) != uvar_to_arg.end()) {
                    cerr << "Multiple union variables dependent on argument ";
                    cerr << _contents.ptr->args[i] << endl;
                    assert(false);
                }
                if (arg_to_uvar.find(_contents.ptr->args[i]) != arg_to_uvar.end()) {
                    cerr << "Union variable " << _contents.ptr->uvars[j].name();
                    cerr << " depends upon multiple args" << endl;
                    assert(false);
                }
                uvar_to_arg[_contents.ptr->uvars[j].name()] = _contents.ptr->args[i];
                arg_to_uvar[_contents.ptr->args[i]] = _contents.ptr->uvars[j].name();
            }
        }
    }
    _contents.ptr->uvar_to_arg = uvar_to_arg;
    _contents.ptr->arg_to_uvar = arg_to_uvar;
}

UnionReduction& UnionReduction::bound(string v, Expr min, Expr max) {
    bool var_found = false;
    for (size_t i=0; !var_found && i<_contents.ptr->args.size(); i++)
        if (v == _contents.ptr->args[i])
            var_found = true;
    if (var_found) {
        _contents.ptr->lower_bound[v] = min;
        _contents.ptr->upper_bound[v] = max;
    } else {
        cerr << "Variable " << v << "not found in union operation" << endl;
        assert(false);
    }
    return *this;
}

Expr UnionReduction::lower_bound(string v) const {
    map<string,Expr>::iterator it = _contents.ptr->lower_bound.find(v);
    bool var_found = (it != _contents.ptr->lower_bound.end());
    if (!var_found) {
        cerr << "Bounds for variable " << v << " not found" << endl;
        assert(false);
    }
    return it->second;
}

Expr UnionReduction::upper_bound(string v) const {
    map<string,Expr>::iterator it = _contents.ptr->upper_bound.find(v);
    bool var_found = (it != _contents.ptr->upper_bound.end());
    if (!var_found) {
        cerr << "Bounds for variable " << v << " not found" << endl;
        assert(false);
    }
    return it->second;
}

string UnionReduction::name ()      const { return _contents.ptr->name;              }
Expr   UnionReduction::value(int i) const { return _contents.ptr->input[i];          }
Type   UnionReduction::type (int i) const { return _contents.ptr->input[i].type();   }

vector<UnionVar>       UnionReduction::uvars()      const { return _contents.ptr->uvars;      }
vector<string>         UnionReduction::args()       const { return _contents.ptr->args;       }
vector<UnionReduction> UnionReduction::sub_unions() const { return _contents.ptr->sub_unions; }

UnionReduction& UnionReduction::split(string x, int tile) {
    // check if the variable to be split exists
    // yes => then go ahead and split it
    // no  => nothing to do, return
    int split_var_idx = -1;
    for (size_t i=0; split_var_idx<0 && i<_contents.ptr->args.size(); i++) {
        if (x == _contents.ptr->args[i]) {
            split_var_idx = i;
        }
    }
    if (split_var_idx<0) return *this;

    // check if the variable to be split corresponds to a union variable
    // yes => go ahead and split
    // no => pure variable split is redundant
    if (_contents.ptr->arg_to_uvar.find(x) == _contents.ptr->arg_to_uvar.end()) {
        for (size_t i=0; i<_contents.ptr->sub_unions.size(); i++)
            _contents.ptr->sub_unions[i].split(x, tile);
        _contents.ptr->funcs.clear();
        return *this;
    }

    // find the index of the union variable mapped to the argument being split
    int split_uvar_idx = -1;
    string mapped_uvar = _contents.ptr->arg_to_uvar.find(x)->second;
    for (size_t i=0; i<_contents.ptr->uvars.size(); i++) {
        if (mapped_uvar == _contents.ptr->uvars[i].name())
            split_uvar_idx = i;
    }

    // union variable mappped to variable being split
    UnionVar rx = _contents.ptr->uvars[split_uvar_idx];

    // inner/outer variable after split
    string xi = x + "i";
    string xo = x + "o";

    // inner/outer union variables after split
    // inner term computes over the same domain as original union
    // outer terms computes over all tiles
    //UnionVar rxi(substitute(x,xi,rx.min()), substitute(x,xi,rx.extent()), rx.name()+"_i");
    UnionVar rxi(simplify(substitute(x,xi,rx.min())), Var(xi), rx.name()+"_i");
    UnionVar rxt(simplify(substitute(x,xi,rx.min())), tile, rx.name()+"_i");
    UnionVar rxo(0, Var(xo), rx.name()+"_o");

    // names of union operations to be generated
    string intra_union_name= _contents.ptr->name+"_IntraUnion_"+x;
    string intra_tail_name = _contents.ptr->name+"_IntraTail_"+x;
    string tail_union_name = _contents.ptr->name+"_TailUnion_"+x;

    vector<string> args_inner;
    vector<string> args_tail;
    vector<string> args_outer;
    vector<Expr> call_args_inner;
    vector<Expr> call_args_tail;

    // intra tile result:
    // replace rx by t.xo+rxi in expression
    // replace x by xo,xi in args
    for (size_t i=0; i<_contents.ptr->args.size(); i++) {
        if (_contents.ptr->args[i] == x) {
            args_inner.push_back(xo);
            args_inner.push_back(xi);
        } else {
            args_inner.push_back(_contents.ptr->args[i]);
        }
    }
    vector<Expr> input_expr_inner;
    for (size_t i=0; i<_contents.ptr->input.size(); i++)
        input_expr_inner.push_back(substitute(rx.name(), Var(xo)*tile + rxi, _contents.ptr->input[i]));
    UnionReduction intra_union(input_expr_inner, args_inner, intra_union_name);

    // intra tile tail:
    // replace rx by t.xo+rxi in expression
    // replace x by xo in args
    for (size_t i=0; i<_contents.ptr->args.size(); i++) {
        if (_contents.ptr->args[i] == x) {
            args_tail.push_back(xo);
            args_tail.push_back(xi); // redundant arg
        } else {
            args_tail.push_back(_contents.ptr->args[i]);
        }
    }
    vector<Expr> input_expr_tail;
    for (size_t i=0; i<_contents.ptr->input.size(); i++)
        input_expr_tail.push_back(substitute(rx.name(), Var(xo)*tile + rxt, _contents.ptr->input[i]));
    UnionReduction intra_tail(input_expr_tail, args_tail, intra_tail_name);

    // union of tails across tiles:
    // same args as intra tail
    // rxo as the only union variable
    // replace xo by rxo in call to intra tail as input expression
    for (size_t i=0; i<_contents.ptr->args.size(); i++) {
        if (_contents.ptr->args[i] == x) {
            args_outer.push_back(xo);
            call_args_tail.push_back(Var(xo));
            call_args_tail.push_back(tile-1); // redundant
        } else {
            args_outer.push_back(_contents.ptr->args[i]);
            call_args_tail.push_back(Var(_contents.ptr->args[i]));
        }
    }
    vector<Expr> input_expr_outer;
    for (size_t i=0; i<_contents.ptr->input.size(); i++)
        input_expr_outer.push_back(substitute(xo, rxo, intra_tail.call_as_union(call_args_tail,i)));
    UnionReduction tail_union(input_expr_outer, args_outer, tail_union_name);

    // uvars of parent transferred to intra tile term, with rxi extra and rx removed
    // transfer all mappings of arg to uvar from parent to sub unions
    // add mapping xi-rxi and remove x-rx for intra tile
    map<string,string>::iterator s1 = _contents.ptr->arg_to_uvar.begin();
    map<string,string>::iterator e1 = _contents.ptr->arg_to_uvar.end();
    map<string,string>::iterator s2 = _contents.ptr->uvar_to_arg.begin();
    map<string,string>::iterator e2 = _contents.ptr->uvar_to_arg.end();
    intra_union._contents.ptr->arg_to_uvar.insert(s1, e1);
    intra_union._contents.ptr->uvar_to_arg.insert(s2, e2);
    intra_union._contents.ptr->arg_to_uvar.erase(x);
    intra_union._contents.ptr->uvar_to_arg.erase(rx.name());
    intra_union._contents.ptr->arg_to_uvar.insert(make_pair(xi,rxi.name()));
    intra_union._contents.ptr->uvar_to_arg.insert(make_pair(rxi.name(),xi));

    // uvars of parent transferred to intra tile term, with rxt extra and rx removed
    // transfer all mappings of arg to uvar from parent to sub unions
    // add mapping xi-rxt and remove x-rx for intra tile
    intra_tail._contents.ptr->arg_to_uvar.insert(s1, e1);
    intra_tail._contents.ptr->uvar_to_arg.insert(s2, e2);
    intra_tail._contents.ptr->arg_to_uvar.erase(x);
    intra_tail._contents.ptr->uvar_to_arg.erase(rx.name());
    intra_tail._contents.ptr->arg_to_uvar.insert(make_pair(xi,rxt.name()));
    intra_tail._contents.ptr->uvar_to_arg.insert(make_pair(rxt.name(),xi));

    // add mapping xo-rxo and remove x-rx for inter tile
    tail_union._contents.ptr->arg_to_uvar.erase(x);
    tail_union._contents.ptr->uvar_to_arg.erase(rx.name());
    tail_union._contents.ptr->arg_to_uvar.insert(make_pair(xo,rxo.name()));
    tail_union._contents.ptr->uvar_to_arg.insert(make_pair(rxo.name(),xo));

    // transfer all bounds from parent union
    // remove bounds of split variable and add those of new vars
    // no bounds required for the intra tile tail
    //intra_union._contents.ptr->lower_bound = _contents.ptr->lower_bound;
    //intra_union._contents.ptr->lower_bound.erase(x);
    //intra_union._contents.ptr->lower_bound.insert(make_pair(xi,0));
    //tail_union ._contents.ptr->lower_bound.erase(x);
    //tail_union ._contents.ptr->lower_bound.insert(make_pair(xo,0));

    //intra_union._contents.ptr->upper_bound = _contents.ptr->upper_bound;
    //intra_union._contents.ptr->upper_bound.erase(x);
    //intra_union._contents.ptr->upper_bound.insert(make_pair(xi,rxi_extent));
    //tail_union ._contents.ptr->upper_bound.erase(x);
    //tail_union ._contents.ptr->upper_bound.insert(make_pair(xo,rxo_extent));

    // replace input expression by combination of split variants
    // outer term args: replace xo by x/tile-1
    // inner term args: replace x by x/tile, x%tile
    vector<Expr> arg_expr_inner;
    vector<Expr> arg_expr_outer;
    for (size_t i=0; i<_contents.ptr->args.size(); i++) {
        if (_contents.ptr->args[i] == x) {
            arg_expr_inner.push_back(Var(x)/tile);
            arg_expr_inner.push_back(Var(x)%tile);
            arg_expr_outer.push_back(Var(x)/tile-1);
        } else {
            arg_expr_inner.push_back(Var(_contents.ptr->args[i]));
            arg_expr_outer.push_back(Var(_contents.ptr->args[i]));
        }
    }

    for (size_t i=0; i<_contents.ptr->input.size(); i++)
        _contents.ptr->input[i] = intra_union.call_as_union(arg_expr_inner, i) +
            select(Var(x)/tile>0, tail_union.call_as_union(arg_expr_outer, i), 0);

    // store the two sub-unions
    _contents.ptr->sub_unions.push_back(intra_union);
    _contents.ptr->sub_unions.push_back(intra_tail);
    _contents.ptr->sub_unions.push_back(tail_union);

    // remove all union variables no longer required in any of the input expressions
    for (size_t i=0; i<_contents.ptr->uvars.size(); i++) {
        bool uvar_unused = true;
        string uvar_name = _contents.ptr->uvars[i].name();
        for (size_t j=0; i<_contents.ptr->input.size(); j++) {
            uvar_unused &= !expr_depends_on_var(_contents.ptr->input[j], uvar_name);
        }
        if (uvar_unused) {
            map<string,string>::iterator it = _contents.ptr->uvar_to_arg.find(uvar_name);
            if (it != _contents.ptr->uvar_to_arg.end()) {
                _contents.ptr->arg_to_uvar.erase(it->second);
                _contents.ptr->uvar_to_arg.erase(it);
            }
            _contents.ptr->uvars.erase(_contents.ptr->uvars.begin()+i);
            i--;
        }
    }

    // split all the sub-unions needed to compute this union
    for (size_t i=0; i<_contents.ptr->sub_unions.size(); i++)
        _contents.ptr->sub_unions[i].split(x, tile);

    // remove any previous conversion to Function
    _contents.ptr->funcs.clear();

    return *this;
}

EXPORT bool UnionReduction::subset_merge(UnionReduction& u1, UnionReduction& u2) {
    // check if this union operation u1 computes a subset of u2

    // all union vars of u1 must be union vars of u2
    bool uvar_check = true;
    for (size_t i=0; i<u1._contents.ptr->uvars.size(); i++) {
        bool current_uvar_found = false;
        for (size_t j=0; j<u2._contents.ptr->uvars.size(); j++) {
            current_uvar_found |= (u1._contents.ptr->uvars[i].name()==u2._contents.ptr->uvars[j].name());
        }
        uvar_check &= current_uvar_found;
    }

    // all args of u1 must be args of u2
    bool arg_check_1 = true;
    for (size_t i=0; i<u1._contents.ptr->args.size(); i++) {
        bool current_arg_found = false;
        for (size_t j=0; j<u2._contents.ptr->args.size(); j++) {
            current_arg_found |= (u1._contents.ptr->args[i] == u2._contents.ptr->args[j]);
        }
        arg_check_1 &= current_arg_found;
    }

    // all args of u2 must be args of u1
    bool arg_check_2 = true;
    for (size_t i=0; i<u2._contents.ptr->args.size(); i++) {
        bool current_arg_found = false;
        for (size_t j=0; j<u1._contents.ptr->args.size(); j++) {
            current_arg_found |= (u2._contents.ptr->args[i] == u1._contents.ptr->args[j]);
        }
        arg_check_2 &= current_arg_found;
    }

    // arg list of both much be same
    bool arg_check = arg_check_1 && arg_check_2;

    // input exp of both must be same, though called at different indices
    bool exp_check = (u1._contents.ptr->input.size() == u2._contents.ptr->input.size());
    for (size_t i=0; exp_check && i<u1._contents.ptr->input.size(); i++) {
        exp_check &= expr_same(u1._contents.ptr->input[i], u2._contents.ptr->input[i]);
    }

    // TODO: actual merging

    return (uvar_check && arg_check && exp_check);
}

EXPORT bool UnionReduction::tuple_merge(UnionReduction& u1, UnionReduction& u2) {
    // all union vars of u1 must be union vars of u2
    bool uvar_check_1 = true;
    for (size_t i=0; i<u1._contents.ptr->uvars.size(); i++) {
        bool current_uvar_found = false;
        for (size_t j=0; j<u2._contents.ptr->uvars.size(); j++) {
            current_uvar_found |= (u1._contents.ptr->uvars[i].name() == u2._contents.ptr->uvars[j].name());
        }
        uvar_check_1 &= current_uvar_found;
    }

    // all union vars of u2 must be union vars of u1
    bool uvar_check_2 = true;
    for (size_t i=0; i<u2._contents.ptr->uvars.size(); i++) {
        bool current_uvar_found = false;
        for (size_t j=0; j<u1._contents.ptr->uvars.size(); j++) {
            current_uvar_found |= (u2._contents.ptr->uvars[i].name() == u1._contents.ptr->uvars[j].name());
        }
        uvar_check_2 &= current_uvar_found;
    }

    // all args of u1 must be args of u2
    bool arg_check_1 = true;
    for (size_t i=0; i<u1._contents.ptr->args.size(); i++) {
        bool current_arg_found = false;
        for (size_t j=0; j<u2._contents.ptr->args.size(); j++) {
            current_arg_found |= (u1._contents.ptr->args[i] == u2._contents.ptr->args[j]);
        }
        arg_check_1 &= current_arg_found;
    }

    // all args of u2 must be args of u1
    bool arg_check_2 = true;
    for (size_t i=0; i<u2._contents.ptr->args.size(); i++) {
        bool current_arg_found = false;
        for (size_t j=0; j<u1._contents.ptr->args.size(); j++) {
            current_arg_found |= (u2._contents.ptr->args[i] == u1._contents.ptr->args[j]);
        }
        arg_check_2 &= current_arg_found;
    }

    if ((uvar_check_1 && arg_check_1) || (uvar_check_2 && arg_check_2)) {
        vector<Expr> input;

        vector<UnionVar> uvar_list= (uvar_check_1 ? u1._contents.ptr->uvars : u2._contents.ptr->uvars);
        vector<string>   arg_list = (arg_check_1  ? u1._contents.ptr->args  : u2._contents.ptr->args);
    } else {
        cerr << "Cannot merge " << u1.name() << " and  " << u2.name() << endl;
        assert(false);
    }

    // TODO: actual merging

    return (uvar_check_1 && arg_check_1 && uvar_check_2 && arg_check_2);
}

void UnionReduction::convert_to_func() {
    // convert the sub funcs recursively first
    for (size_t i=0; i<_contents.ptr->sub_unions.size(); i++)
        _contents.ptr->sub_unions[i].convert_to_func();

    // check if union has already been converted to function
    if (!_contents.ptr->funcs.empty() && _contents.ptr->funcs[0].has_pure_definition())
        return;

    // replace all occurances of union operations in input expr with Function calls
    vector<Expr> pure_val;
    for (size_t i=0; i<_contents.ptr->input.size(); i++)
        pure_val.push_back(substitute_union_with_func(_contents.ptr->input[i]));

    // replace all UnionVars with their mapped args
    for (size_t i=0; i<_contents.ptr->uvars.size(); i++) {
        UnionVar ux = _contents.ptr->uvars[i];
        string    x = _contents.ptr->uvar_to_arg.find(ux.name())->second;
        for (size_t j=0; j<pure_val.size(); j++)
            pure_val[j] = substitute(ux.name(), Var(x), pure_val[j]);
    }

    // pure definition
    Function func(_contents.ptr->name);
    func.define(_contents.ptr->args, pure_val);

    // loop over all union variables emitting one reduction defintion for each
    for (size_t i=0; i<_contents.ptr->uvars.size(); i++) {
        // each union_variable is mapped to RDom and arg by now
        UnionVar ux = _contents.ptr->uvars[i];
        string    x = _contents.ptr->uvar_to_arg.find(ux.name())->second;

        // find the dimension corresponding to union variable
        int dimension = -1;
        for (size_t j=0; j<_contents.ptr->args.size(); j++) {
            if (x == _contents.ptr->args[j])
                dimension = j;
        }
        if (dimension<0) {
            cerr << "Argument " << x << " not found in union operation" << endl;
            assert(false);
        }

        // create RDom
        string rdom_name = ux.name();
        rdom_name = erase_all_occurances(rdom_name,".x$r");
        rdom_name = erase_all_occurances(rdom_name,".y$r");
        rdom_name = erase_all_occurances(rdom_name,".z$r");
        //Var  xmin    = Var(func.name()+"."+x+".min."+int_to_string(dimension));
        //Var  xextent = Var(func.name()+"."+x+".extent."+int_to_string(dimension));
        Var  xmin    = Var(func.name()+"."+x+".min_realized");
        Var  xextent = Var(func.name()+"."+x+".extent_realized");
        Expr rxmin   = simplify(substitute(x, xmin   , ux.min())+1);
        Expr rxextent= simplify(substitute(x, xextent, ux.extent())-1);
        RDom rx(rxmin, rxextent, rdom_name);

        // reduction definition
        vector<Expr> reduction_args;
        vector<Expr> reduction_vargs1;
        vector<Expr> reduction_vargs2;
        for (size_t j=0; j<_contents.ptr->args.size(); j++) {
            // LHS args are same as pure definition args, except that
            // the arg mapped to union variable is replaced by RDom rx
            // call args for RHS are same as LHS except rx replaced by rx-1
            string arg = _contents.ptr->args[j];
            if (x == arg) {
                reduction_args.push_back(rx);
                reduction_vargs1.push_back(rx);
                reduction_vargs2.push_back(rx-1);
            } else {
                reduction_args  .push_back(Var(arg));
                reduction_vargs1.push_back(Var(arg));
                reduction_vargs2.push_back(Var(arg));
            }
        }
        vector<Expr> reduction_val;
        for (size_t j=0; j<_contents.ptr->input.size(); j++) {
            reduction_val.push_back(Call::make(func, reduction_vargs1, j) +
                    Call::make(func, reduction_vargs2, j));
        }

        func.define_reduction(reduction_args, reduction_val);
    }
    _contents.ptr->funcs.push_back(func);
}

vector<Function> UnionReduction::funcs() {
    vector<Function> func_list;

    // convert to funcs if not alredy done
    if (_contents.ptr->funcs.empty() ||
            !_contents.ptr->funcs[0].has_pure_definition()) {
        convert_to_func();
    }

    // first get Functions for the sub-unions
    for (size_t i=0; i<_contents.ptr->sub_unions.size(); i++) {
        vector<Function> sub_func_list = _contents.ptr->sub_unions[i].funcs();
        func_list.insert(func_list.end(), sub_func_list.begin(), sub_func_list.end());
    }

    func_list.insert(func_list.end(), _contents.ptr->funcs.begin(), _contents.ptr->funcs.end());

    return func_list;
}

EXPORT Expr UnionReduction::call_as_func(vector<Expr> args, int idx) const {
    if (_contents.ptr->funcs.empty() || !_contents.ptr->funcs[0].has_pure_definition()) {
        cerr << "Union " << _contents.ptr->name << " called as Func before conversion" << endl;
        assert(false);
    }
    if (args.size()!=_contents.ptr->args.size()) {
        cerr << "Call to union " << _contents.ptr->name << " as Func ";
        cerr << "has incorrect number of args" << endl;
        assert(false);
    }
    // each function in list is represents reduction along a particular dimension
    // last function in the list represents the complete multi-dimensional union
    return Call::make(_contents.ptr->funcs[_contents.ptr->funcs.size()-1], args, idx);
}

Expr UnionReduction::call_as_union(vector<Expr> args, int idx) const {
    if (args.size()!=_contents.ptr->args.size()) {
        cerr << "Call to union " << _contents.ptr->name << " has incorrect number of args" << endl;
        assert(false);
    }
    return UnionCall::make(*this, args, idx);
}

Expr UnionReduction::call_as_union(vector<string> args, int idx) const {
    vector<Expr> var_args(args.size());
    for (size_t i=0; i<var_args.size(); i++)
        var_args[i] = Var(args[i]);
    if (var_args.size()!=_contents.ptr->args.size()) {
        cerr << "Call to union " << _contents.ptr->name << " has incorrect number of args" << endl;
        assert(false);
    }
    return UnionCall::make(*this, var_args, idx);
}

ostream& UnionReduction::print(ostream &stream) const {
    // indent the output
    static int level = 0;

    for (size_t j=0; j<_contents.ptr->input.size(); j++) {
        stream << _contents.ptr->name << "(";
        for (size_t i=0; i<_contents.ptr->args.size(); i++) {
            stream << _contents.ptr->args[i];
            if (i != _contents.ptr->args.size()-1)
                stream << ", ";
        }
        stream << ")[" << j << "] = ";
        for (size_t i=0; i<_contents.ptr->input.size(); i++) {
            stream << _contents.ptr->input[j];

            // union variables
            if (!_contents.ptr->uvars.empty()) {
                stream << " with  ";
                for (size_t i=0; i<_contents.ptr->uvars.size(); i++) {
                    stream << _contents.ptr->uvars[i].name() << "[" <<
                        _contents.ptr->uvars[i].min() << ":" <<
                        simplify(_contents.ptr->uvars[i].min()+
                                _contents.ptr->uvars[i].extent()) << "] ";
                }
            }
        }

        // sub union dependencies
        if (!_contents.ptr->sub_unions.empty()) {
            for (size_t i=0; i<_contents.ptr->sub_unions.size(); i++) {
                level++;
                stream << "\n";
                for (int j=0; j<level; j++)
                    stream << "|    ";
                stream << "\n";
                for (int j=0; j<level; j++)
                    stream << "|----";
                _contents.ptr->sub_unions[i].print(stream);
                level--;
            }
        }
    }
    return stream;
}

// -----------------------------------------------------------------------------

ostream &operator<<(ostream &s, Internal::UnionReduction u) {
    return u.print(s);
}

}
}
