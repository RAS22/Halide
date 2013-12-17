#include "IR.h"
#include "Var.h"
#include "RDom.h"
#include "Scope.h"
#include "IRPrinter.h"
#include "IROperator.h"
#include "IREquality.h"
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
    void visit(const Let *op) {
        op->value.accept(this);
        // The name might be hidden within the body of the let, in
        // which case there's no point descending.
        if (op->name != var) {
            op->body.accept(this);
        }
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
        expr = op->union_op.call_as_func(op->args);
    }
public:
    SubstituteUnionWithFunc() {}
};

Expr substitute_union_with_func(const Expr& expr) {
    SubstituteUnionWithFunc s;
    return s.mutate(expr);
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
    _contents.ptr->var = unique_name(n);
    _contents.ptr->min = m;
    _contents.ptr->extent = e;

    ReductionVariable v = {_contents.ptr->var, m, e};
    _contents.ptr->domain = ReductionDomain(vec(v));
}

const string& UnionVar::name()   const { return _contents.ptr->var;    }
const Expr&   UnionVar::min()    const { return _contents.ptr->min;    }
const Expr&   UnionVar::extent() const { return _contents.ptr->extent; }

bool UnionVar::same_as(const UnionVar &other) const { return _contents.same_as(other._contents); }

UnionVar::operator Expr() const { return Variable::make(Int(32), _contents.ptr->var, _contents.ptr->domain); }

// -----------------------------------------------------------------------------

UnionReduction::UnionReduction() : _contents(new UnionReductionContents) {
    _contents.ptr->name = "Union_default";
}

UnionReduction::UnionReduction(const IntrusivePtr<UnionReductionContents> &c) : _contents(c) {}

UnionReduction::UnionReduction(Expr in,
        vector<string>   args,
        vector<UnionVar> uvars,
        string           name) {

    if (!_contents.defined()) {
        _contents = new UnionReductionContents;
    }

    _contents.ptr->name  = name;
    _contents.ptr->input = in;
    _contents.ptr->type  = in.type();
    _contents.ptr->args  = args;
    _contents.ptr->uvars = uvars;

    // remove all unused union variables
    for (size_t i=0; i<_contents.ptr->uvars.size(); i++) {
        string v = _contents.ptr->uvars[i].name();
        if (!expr_depends_on_var(_contents.ptr->input, v)) {
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

const Expr& UnionReduction::lower_bound(string v) const {
    map<string,Expr>::iterator it = _contents.ptr->lower_bound.find(v);
    bool var_found = (it != _contents.ptr->lower_bound.end());
    if (!var_found) {
        cerr << "Bounds for variable " << v << " not found" << endl;
        assert(false);
    }
    return it->second;
}

const Expr& UnionReduction::upper_bound(string v) const {
    map<string,Expr>::iterator it = _contents.ptr->upper_bound.find(v);
    bool var_found = (it != _contents.ptr->upper_bound.end());
    if (!var_found) {
        cerr << "Bounds for variable " << v << " not found" << endl;
        assert(false);
    }
    return it->second;
}

const string& UnionReduction::name()  const { return _contents.ptr->name; }
const Type&   UnionReduction::type()  const { return _contents.ptr->type; }
const Expr&   UnionReduction::input() const { return _contents.ptr->input;}

const vector<UnionVar>&       UnionReduction::uvars()      const { return _contents.ptr->uvars;  }
const vector<string>&         UnionReduction::args()       const { return _contents.ptr->args;   }
const vector<UnionReduction>& UnionReduction::sub_unions() const { return _contents.ptr->sub_unions; }


UnionReduction& UnionReduction::split(string x, int tile) {
    // check if the variable to be split exists
    // yes => then go ahead and split it
    // no  => nothing to do, return
    int split_var_index = -1;
    for (size_t i=0; split_var_index<0 && i<_contents.ptr->args.size(); i++) {
        if (x == _contents.ptr->args[i]) {
            split_var_index = i;
        }
    }
    if (split_var_index<0) return *this;

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
    int split_uvar_index = -1;
    string mapped_uvar = _contents.ptr->arg_to_uvar.find(x)->second;
    for (size_t i=0; i<_contents.ptr->uvars.size(); i++) {
        if (mapped_uvar == _contents.ptr->uvars[i].name())
            split_uvar_index = i;
    }

    UnionVar rx = _contents.ptr->uvars[split_uvar_index];

    // bound for variable to be split
    // necessary for determining union domains
    // raise an error if bound is not set
    Expr x_extent = upper_bound(x);

    // inner/outer variable after split
    string xi = x + "i";
    string xo = x + "o";

    // inner/outer union variables after split,
    // TODO: valid only for scan, not box filter
    Expr rxi_extent = tile;
    Expr rxo_extent = substitute(x, x_extent, rx.extent()/tile);

    UnionVar rxi(0, rxi_extent, rx.name()+"i");
    UnionVar rxo(0, rxo_extent, rx.name()+"o");

    // replace the x with xo,xi
    vector<string> args = _contents.ptr->args;
    args.insert(args.begin()+split_var_index+1, xi);
    args.insert(args.begin()+split_var_index+1, xo);
    args.erase (args.begin()+split_var_index);

    // replace the rx with rxi for intra tile input expression
    vector<UnionVar> uvar_inner = _contents.ptr->uvars;
    uvar_inner.insert(uvar_inner.begin()+split_uvar_index+1, rxi);
    uvar_inner.erase (uvar_inner.begin()+split_uvar_index);

    // intra tile result: replace rx by t.xo+rxi in input
    // expression and x by xo,xi in args
    Expr input_expr_inner = substitute(rx.name(), Var(xo)*tile + rxi, _contents.ptr->input);
    UnionReduction intra_tile(input_expr_inner, args, uvar_inner, _contents.ptr->name+"_Intra_"+x);

    // inter tile result: rxo is the only union variable,
    // replace xo by rxo in call to intra result
    vector<UnionVar> uvar_outer = vec(rxo);
    Expr input_expr_outer = substitute(xo, rxo, intra_tile.call_as_union(args));
    UnionReduction inter_tile(input_expr_outer, args, uvar_outer, _contents.ptr->name+"_Outer_"+x);

    // uvars of parent transferred to intra tile term, with rxi extra and rx removed
    // transfer all mappings of arg to uvar from parent to sub unions
    // add mapping xi-rxi and remove x-rx for intra tile
    map<string,string>::iterator s1 = _contents.ptr->arg_to_uvar.begin();
    map<string,string>::iterator e1 = _contents.ptr->arg_to_uvar.end();
    map<string,string>::iterator s2 = _contents.ptr->uvar_to_arg.begin();
    map<string,string>::iterator e2 = _contents.ptr->uvar_to_arg.end();
    intra_tile._contents.ptr->arg_to_uvar.insert(s1, e1);
    intra_tile._contents.ptr->uvar_to_arg.insert(s2, e2);
    intra_tile._contents.ptr->arg_to_uvar.erase(x);
    intra_tile._contents.ptr->uvar_to_arg.erase(rx.name());
    intra_tile._contents.ptr->arg_to_uvar.insert(make_pair(xi,rxi.name()));
    intra_tile._contents.ptr->uvar_to_arg.insert(make_pair(rxi.name(),xi));

    // add mapping xo-rxo and remove x-rx for inter tile
    inter_tile._contents.ptr->arg_to_uvar.erase(x);
    inter_tile._contents.ptr->uvar_to_arg.erase(rx.name());
    inter_tile._contents.ptr->arg_to_uvar.insert(make_pair(xo,rxo.name()));
    inter_tile._contents.ptr->uvar_to_arg.insert(make_pair(rxo.name(),xo));

    // transfer all bounds from parent union
    // remove bounds of split variable and add those of new vars
    intra_tile._contents.ptr->lower_bound = _contents.ptr->lower_bound;
    intra_tile._contents.ptr->lower_bound.insert(make_pair(xi,0));
    intra_tile._contents.ptr->lower_bound.insert(make_pair(xi,0));
    inter_tile._contents.ptr->lower_bound.erase(x);
    inter_tile._contents.ptr->lower_bound.insert(make_pair(xo,0));
    inter_tile._contents.ptr->lower_bound.insert(make_pair(xo,0));
    intra_tile._contents.ptr->lower_bound.erase(x);

    intra_tile._contents.ptr->upper_bound = _contents.ptr->upper_bound;
    intra_tile._contents.ptr->upper_bound.insert(make_pair(xi,rxi_extent));
    intra_tile._contents.ptr->upper_bound.insert(make_pair(xi,rxi_extent));
    inter_tile._contents.ptr->upper_bound.erase(x);
    inter_tile._contents.ptr->upper_bound.insert(make_pair(xo,rxo_extent));
    inter_tile._contents.ptr->upper_bound.insert(make_pair(xo,rxo_extent));
    intra_tile._contents.ptr->upper_bound.erase(x);

    // replace input expression by combination of split variants
    // outer term args: replace xo by x/tile-1 and xi by tile-1
    // inner term args: replace xo by x/tile and xi by x%tile
    vector<Expr> args_inner(args.size());
    vector<Expr> args_outer(args.size());
    for (size_t i=0; i<args.size(); i++) {
        args_inner[i] = Var(args[i]);
        args_outer[i] = Var(args[i]);
        args_outer[i] = substitute(xo, Var(x)/tile-1, args_outer[i]);
        args_outer[i] = substitute(xi, tile-1,        args_outer[i]);
        args_inner[i] = substitute(xo, Var(x)/tile, args_inner[i]);
        args_inner[i] = substitute(xi, Var(x)%tile, args_inner[i]);
    }
    _contents.ptr->input = intra_tile.call_as_union(args_inner) +
        select(Var(x)/tile>0, inter_tile.call_as_union(args_outer), 0);

    // remove all union variables no longer required in input expression
    for (size_t i=0; i<_contents.ptr->uvars.size(); i++) {
        string var_name = _contents.ptr->uvars[i].name();
        if (!expr_depends_on_var(_contents.ptr->input, var_name)) {
            map<string,string>::iterator it = _contents.ptr->uvar_to_arg.find(var_name);
            if (it != _contents.ptr->uvar_to_arg.end()) {
                _contents.ptr->arg_to_uvar.erase(it->second);
                _contents.ptr->uvar_to_arg.erase(it);
            }
            _contents.ptr->uvars.erase(_contents.ptr->uvars.begin()+i);
            i--;
        }
    }

    // store the two sub-unions
    _contents.ptr->sub_unions.push_back(intra_tile);
    _contents.ptr->sub_unions.push_back(inter_tile);

    // split all the sub-unions needed to compute this union
    for (size_t i=0; i<_contents.ptr->sub_unions.size(); i++) {
        _contents.ptr->sub_unions[i].split(x, tile);
    }

    // remove any conversion to Function
    _contents.ptr->funcs.clear();

    return *this;
}

void UnionReduction::convert_to_func() {
    // check if union has already been converted to function
    if (!_contents.ptr->funcs.empty() &&
            _contents.ptr->funcs[0].has_pure_definition()) {
        return;
    }

    // convert the sub funcs recursively first
    for (size_t i=0; i<_contents.ptr->sub_unions.size(); i++) {
        _contents.ptr->sub_unions[i].convert_to_func();
    }

    // replace all occurances of union operations in input expr with
    // equivalent Function calls (forces recursive conversion of subunions)
    // and all UnionVars with their mapped args
    Expr pure_val = substitute_union_with_func(_contents.ptr->input);
    for (size_t i=0; i<_contents.ptr->uvars.size(); i++) {
        // each union_variable is mapped to RDom and arg by now
        UnionVar ux = _contents.ptr->uvars[i];
        string    x = _contents.ptr->uvar_to_arg.find(ux.name())->second;
        pure_val = substitute(ux.name(), Var(x), pure_val);
    }

    if (_contents.ptr->uvars.empty()) {
        Function func(_contents.ptr->name+"_func");
        func.define(_contents.ptr->args, vec(pure_val));
        _contents.ptr->funcs.push_back(func);
    }
    else {
        // create RDom for each union variable
        map<string,RDom> rdom;
        for (size_t i=0; i<_contents.ptr->uvars.size(); i++) {
            string n = _contents.ptr->uvars[i].name();
            string v = _contents.ptr->uvar_to_arg.find(n)->second;
            Expr b   = simplify(lower_bound(v)+1);
            Expr e   = simplify(upper_bound(v)-1);
            rdom[_contents.ptr->uvars[i].name()] = RDom(b,e,n);
        }

        // loop over all union variables, emit one Halide reduction for each
        for (size_t i=0; i<_contents.ptr->uvars.size(); i++) {
            // each union_variable is mapped to RDom and arg by now
            UnionVar ux = _contents.ptr->uvars[i];
            string    x = _contents.ptr->uvar_to_arg.find(ux.name())->second;
            RDom     rx = rdom.find(ux.name())->second;

            string func_name = _contents.ptr->name+"_func";
            if (i < _contents.ptr->uvars.size()-1)
                func_name += "_"+ux.name();

            Function func(func_name);

            // pure definition
            if (i == 0) {
                // initialize with input expression
                func.define(_contents.ptr->args, vec(pure_val));
            }
            else {
                // initialize with output of previous dimension reduction,
                // call previous reduction at same args as this function
                vector<Expr> pure_args(_contents.ptr->args.size());
                for (size_t j=0; j<pure_args.size(); j++)
                    pure_args[j] = Var(_contents.ptr->args[j]);
                Expr pure_val = Call::make(_contents.ptr->funcs[int(i)-1], pure_args);
                func.define(_contents.ptr->args, vec(pure_val));
            }

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
            Expr reduction_val = Call::make(func, reduction_vargs1) +
                Call::make(func, reduction_vargs2);

            func.define_reduction(reduction_args, vec(reduction_val));

            _contents.ptr->funcs.push_back(func);
        }
    }
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

EXPORT Expr UnionReduction::call_as_func(const vector<Expr>& args) const {
    if (_contents.ptr->funcs.empty() ||
            !_contents.ptr->funcs[0].has_pure_definition()) {
        cerr << "Union " << _contents.ptr->name << " called as Func before conversion" << endl;
        assert(false);
    }
    if (args.size()!=_contents.ptr->args.size()) {
        cerr << "Call to union " << _contents.ptr->name << " as Func ";
        cerr << "has incorrect number of args" << endl;
        assert(false);
    }
    // last function in the list represents the complete multi-dimensional
    // union, each function in list is represents reduction along a perticular
    // dimension
    return Call::make(_contents.ptr->funcs[_contents.ptr->funcs.size()-1], args);
}

Expr UnionReduction::call_as_union(const vector<Expr> &args) const {
    if (args.size()!=_contents.ptr->args.size()) {
        cerr << "Call to union " << _contents.ptr->name << " has incorrect number of args" << endl;
        assert(false);
    }
    return UnionCall::make(*this, args);
}

Expr UnionReduction::call_as_union(const vector<string> &args) const {
    vector<Expr> var_args(args.size());
    for (size_t i=0; i<var_args.size(); i++)
        var_args[i] = Var(args[i]);
    if (var_args.size()!=_contents.ptr->args.size()) {
        cerr << "Call to union " << _contents.ptr->name << " has incorrect number of args" << endl;
        assert(false);
    }
    return UnionCall::make(*this, var_args);
}

ostream& UnionReduction::print(ostream &stream) const {
    static int level = 0;

    // union operation
    stream << _contents.ptr->name << "(";
    for (size_t i=0; i<_contents.ptr->args.size(); i++) {
        stream << _contents.ptr->args[i];
        if (i != _contents.ptr->args.size()-1)
            stream << ", ";
    }
    stream << ")" << " = " << _contents.ptr->input;

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
    return stream;
}
}

// -----------------------------------------------------------------------------

ostream &operator<<(ostream &s, Internal::UnionReduction u) {
    return u.print(s);
}

}
