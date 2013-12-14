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
using std::string;
using std::vector;
using std::ostream;
using std::endl;
using std::cerr;

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

class SubstituteUnionWithFunc : public IRVisitor {
private:
    using IRVisitor::visit;
    void visit(const Call *op) {
        if (op->call_type == Call::UnionReduction) {
            UnionReduction union_op = op->union_op;
            vector<Expr> args = op->args;
            *op = Call::make(union_op->call_as_func(op->args));
        }
    }
public:
    SubstituteUnionWithFunc() {}
};

static void substitute_union_with_func(const Expr& e) {
    SubstituteUnionWithFunc s;
    e.accept(&s);
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

const std::string& UnionVar::name()   const { return _contents.ptr->var;    }
const Expr&        UnionVar::min()    const { return _contents.ptr->min;    }
const Expr&        UnionVar::extent() const { return _contents.ptr->extent; }

bool UnionVar::same_as(const UnionVar &other) const { return _contents.same_as(other._contents); }

UnionVar::operator Expr() const { return Variable::make(Int(32), _contents.ptr->var, _contents.ptr->domain); }

// -----------------------------------------------------------------------------

UnionReduction::UnionReduction() : _contents(new UnionReductionContents) {}
UnionReduction::UnionReduction(const IntrusivePtr<UnionReductionContents> &c) : _contents(c) {}

UnionReduction::UnionReduction(Expr in,
        const vector<std::string> args,
        const vector<UnionVar>    uvars,
        std::string name) {

    for (size_t i=0; i<uvar.size(); i++) {
        string v = uvar[i].name();
        if (!expr_depends_on_var(in, v)) {
            cerr << "Expression doesn't depend upon union variable " << v.c_str() << endl;
            assert(false);
        }
    }

    if (!_contents.defined()) {
        _contents = new UnionReductionContents;
    }

    _contents.ptr->name  = name;
    _contents.ptr->input = in;
    _contents.ptr->type  = in.type();
    _contents.ptr->args  = args;
    _contents.ptr->uvars = uvars;

    // map union variables to input variables
    // only one to one mapping allowed
    std::map<std::string,int> args_to_uvar;
    std::map<std::string,int> uvar_to_arg;
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
                    cerr << " depends upon multiple arguments" << endl;
                    assert(false);
                }
                uvar_to_arg(_contents.ptr->uvars[j].name, i);
                arg_to_uvar(_contents.ptr->args[i],       j);
                mapped = true;
            }
        }
        // the following case might be intended behavior, mark it as error for now
        if (uvar_to_arg.find(_contents.ptr->uvars[j].name()) == uvar_to_arg.end()) {
            cerr << "Union variable " << _contents.ptr->uvars[j].name();
            cerr << " does not depend upon any argument" << endl;
            assert(false);
        }
    }
    _contents.ptr->uvar_to_arg = uvar_to_arg;
    _contents.ptr->arg_to_uvar = arg_to_uvar;
}

UnionReduction& UnionReduction::bound(string v, Expr max) {
    bool var_found = false;
    for (size_t i=0; !var_found && i<_contents.ptr->args.size(); i++)
        if (v == _contents.ptr->args[i])
            var_found = true;
    if (var_found) {
        _contents.ptr->bound[v] = max;
    } else {
        cerr << "Variable " << v << "not found in union operation" << endl;
        assert(false);
    }
    return *this;
}

const Expr& UnionReduction::bound(string v) const {
    map<string,Expr>::iterator it = _contents.ptr->bound.find(v);
    bool var_found = (it != _contents.ptr->bound.end());
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


    // check if any union variable is mapped to the argument
    // yes => union variable split
    // no  => pure split
    if (_contents.ptr->arg_to_uvar.find(x) != _contents.ptr->arg_to_uvar.end()) { // Union variable split
        int split_uvar_index = *(_contents.ptr->arg_to_uvar.find(x));

        UnionVar rx = _contents.ptr->uvars[split_uvar_index];

        // bound for variable to be split
        // necessary for determining union domains
        // raise an error if bound is not set
        Expr x_extent = bound(x);

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
        // expression and x by xo,xi in out variables
        Expr input_expr_inner = substitute(rx.name(), Var(xo)*tile + rxi, _contents.ptr->input);
        UnionReduction intra_tile(input_expr_inner, args, uvar_inner, _contents.ptr->name+".Intra_"+x);

        // inter tile result: rxo is the only union variable,
        // replace xo by rxo in call to intra result
        vector<UnionVar> uvar_outer = vec(rxo);
        Expr input_expr_outer = substitute(xo, rxo, intra_tile(args));
        UnionReduction inter_tile(input_expr_outer, args, uvar_outer, _contents.ptr->name+".Outer_"+x);

        // transfer all bounds from parent union
        // remove bounds of split variable and add those of new vars
        intra_tile._contents.ptr->bound = _contents.ptr->bound;
        intra_tile._contents.ptr->bound = _contents.ptr->bound;
        intra_tile._contents.ptr->bound[xi] = rxi_extent;
        intra_tile._contents.ptr->bound[xi] = rxi_extent;
        intra_tile._contents.ptr->bound[xo] = rxo_extent;
        intra_tile._contents.ptr->bound[xo] = rxo_extent;
        intra_tile._contents.ptr->bound.erase(x);
        intra_tile._contents.ptr->bound.erase(x);

        // replace input expression by combination of split variants
        // replacing xo by xo-1 and xi by tile-1 for inter tile result
        vector<Expr> args_outer;
        args_outer.resize(args.size());
        for (size_t i=0; i<args_outer.size(); i++) {
            args_outer[i] = Var(args[i]);
            if (args[i] == xo) args_outer[i] = Var(xo)-1;
            if (args[i] == xi) args_outer[i] = tile   -1;
        }
        _contents.ptr->input = inter_tile(args) + intra_tile(args_outer);

        // remove all union variables which are no longer required in input expression
        for (size_t i=0; i<_contents.ptr->uvars.size(); i++) {
            string var_name = _contents.ptr->uvars[i].name();
            if (!expr_depends_on_var(_contents.ptr->input, var_name)) {
                _contents.ptr->uvars.erase(_contents.ptr->uvars.begin()+i);
                i--;
            }
        }

        // store the two sub-unions
        _contents.ptr->sub_unions.push_back(intra_tile);
        _contents.ptr->sub_unions.push_back(inter_tile);
    }
    else { // Pure variable split

        // inner/outer variable after split
        string xi = x + "i";
        string xo = x + "o";

        _contents.ptr->name += ".Outer_"+x;

        // replace the variable in the input expression with outer*tile+inner
        _contents.ptr->input = substitute(x, Var(xo)*tile + Var(xi), _contents.ptr->input);
    }

    // split all the sub-unions needed to compute this union
    for (size_t i=0; i<_contents.ptr->sub_unions.size(); i++) {
        _contents.ptr->sub_unions[i].split(x, tile);
    }

    return *this;
}

void UnionReduction::convert_to_func() {
    // check if union has already been converted to function
    if (!_contents.ptr->funcs.empty() &&
         _contents.ptr->funcs[0].has_pure_definition) {
        return;
    }

    if (_contents.ptr->uvars.empty()) {
        // replace all occurances of union operations in input expression
        // with their equivalent Function calls
        Expr pure_val = _contents.ptr->input;
        substitute_union_with_func(pure_val);
        Function func;
        func.define(_contents.ptr->args, pure_val);
        _contents.ptr->func.push_back(func);
    }
    else {
        // create RDom for each union variable
        std::map<string,RDom> rdom;
        for (size_t i=0; i<_contents.ptr->uvars.size(); i++) {
            rdom[_contents.ptr->uvars[i].name()] = RDom(
                    _contents.ptr->uvars[i].min(),
                    _contents.ptr->uvars[i].extent(),
                    _contents.ptr->uvars[i].name())+".$r";
        }

        // loop over all union variables, emit one Halide reduction for each
        for (size_t i=0; i<_contents.ptr->uvars.size(); it++) {
            // each union_variable is surely mapped to an RDom by now
            // each union_variable is surely mapped to an arg in constructor
            UnionVar ux = _contents.ptr->uvars[i];
            RDom     rx = *(rdom[ux]);
            string    x = _contents.ptr->args[*(uvar_to_arg[ux])];

            Function func;

            // pure definition
            if (i == 0) {
                // initialize with input expression where all occurances
                // of other union reductions are replaced with their
                // Function equivalent
                Expr pure_val = _contents.ptr->input;
                substitute_union_with_func(pure_val);
                func.define(_contents.ptr->args, pure_val);
            }
            else {
                // initialize with output of previous dimension reduction,
                // call previous reduction at same args as this function
                Expr pure_val = Call::make(func[i-1], _content.ptr->args);
                func.define(_contents.ptr->args, pure_val);
            }

            // reduction definition
            vector<Expr> reduction_args;
            vector<Expr> reduction_vargs1;
            vector<Expr> reduction_vargs2;
            for (size_t i=0; i<_content.ptr->args.size(); i++) {
                // LHS args are same as pure definition args, except that
                // the arg mapped to union variable is replaced by RDom rx
                // call args for RHS are same as LHS except rx replaced by rx-1
                if (x == _content.ptr->args[i]) {
                    reduction_args.push_back(rx);
                    reduction_vargs1.push_back(rx);
                    reduction_vargs2.push_back(rx-1);
                } else {
                    reduction_args  .push_back(Var(_content.ptr->args[i]));
                    reduction_vargs1.push_back(Var(_content.ptr->args[i]));
                    reduction_vargs2.push_back(Var(_content.ptr->args[i]));
                }
            }
            Expr reduction_val = call_as_func(reduction_vargs1) +
                                 call_as_func(reduction_vargs2);

            func.define_reduction(reduction_args, reduction_val);

            _contents.ptr->func.push_back(func);
        }
    }
}


vector<Function&> UnionReduction::funcs() const {
    vector<Function&> func_list;

    // convert to funcs if not alredy done
    if (_contents.ptr->funcs.empty() ||
       !_contents.ptr->funcs[0].has_pure_definition()) {
        convert_to_func();
    }

    func_list.insert(func_list.end(), _contents.ptr->funcs.begin(), _contents.ptr->funcs.end());
    for (size_t i=0; i<_contents.ptr->sub_unions.size(); i++) {
        vector<Function&> sub_func_list = _contents.ptr->sub_unions[i].func();
        func_list.insert(func_list.end(), sub_func_list.begin(), sub_func_list.end());
    }
    return func_list;
}

EXPORT Expr call_as_func(const vector<Expr>& args) const {
    if (_contents.ptr->funcs.empty() || !_contents.ptr->funcs[0].has_pure_definition()) {
        convert_to_func();
    }
    if (args.size()==_contents.ptr->args.size()) {
        cerr << "Call to Union operation as Halide::Internal::Function ";
        cerr << "has incorrect number of arguments" << endl;
        assert(false);
    }
    // last function in the list represents the complete multi-dimensional
    // union, each function in list is represents reduction along a perticular
    // dimension
    return Call::make(_contents.ptr->funcs[_contents.ptr->funcs.size()-1], args);
}

Expr UnionReduction::operator()(Expr x, Expr y) const {
    vector<Expr> args = vec(x, y);
    if (args.size()==_contents.ptr->args.size()) {
        cerr << "Call to Union operation has incorrect number of arguments" << endl;
        assert(false);
    }
    return Call::make(*this, args);
}

Expr UnionReduction::operator()(Expr x, Expr y, Expr z) const {
    vector<Expr> args = vec(x, y, z);
    if (args.size()==_contents.ptr->args.size()) {
        cerr << "Call to Union operation has incorrect number of arguments" << endl;
        assert(false);
    }
    return Call::make(*this, args);
}

Expr UnionReduction::operator()(Expr x, Expr y, Expr z, Expr w) const {
    vector<Expr> args = vec(x, y, z, w);
    if (args.size()==_contents.ptr->args.size()) {
        cerr << "Call to Union operation has incorrect number of arguments" << endl;
        assert(false);
    }
    return Call::make(*this, args);
}

Expr UnionReduction::operator()(Expr x, Expr y, Expr z, Expr w, Expr u) const {
    vector<Expr> args = vec(x, y, z, w, u);
    if (args.size()==_contents.ptr->args.size()) {
        cerr << "Call to Union operation has incorrect number of arguments" << endl;
        assert(false);
    }
    return Call::make(*this, args);
}

Expr UnionReduction::operator()(Expr x, Expr y, Expr z, Expr w, Expr u, Expr v) const {
    vector<Expr> args = vec(x, y, z, w, u, v);
    if (args.size()==_contents.ptr->args.size()) {
        cerr << "Call to Union operation has incorrect number of arguments" << endl;
        assert(false);
    }
    return Call::make(*this, args);
}

Expr UnionReduction::operator()(vector<Expr> args) const {
    if (args.size()==_contents.ptr->args.size()) {
        cerr << "Call to Union operation has incorrect number of arguments" << endl;
        assert(false);
    }
    return Call::make(*this, args);
}

Expr UnionReduction::operator()(string x) const {
    vector<Expr> args(1);
    args.push_back(Var(x));
    if (args.size()==_contents.ptr->args.size()) {
        cerr << "Call to Union operation has incorrect number of arguments" << endl;
        assert(false);
    }
    return Call::make(*this, args);
}

Expr UnionReduction::operator()(string x, string y) const {
    vector<Expr> args(2);
    args.push_back(Var(x));
    args.push_back(Var(y));
    if (args.size()==_contents.ptr->args.size()) {
        cerr << "Call to Union operation has incorrect number of arguments" << endl;
        assert(false);
    }
    return Call::make(*this, args);
}

Expr UnionReduction::operator()(string x, string y, string z) const {
    vector<Expr> args(3);
    args.push_back(Var(x));
    args.push_back(Var(y));
    args.push_back(Var(z));
    if (args.size()==_contents.ptr->args.size()) {
        cerr << "Call to Union operation has incorrect number of arguments" << endl;
        assert(false);
    }
    return Call::make(*this, args);
}

Expr UnionReduction::operator()(string x, string y, string z, string w) const {
    vector<Expr> args(4);
    args.push_back(Var(x)); args.push_back(Var(y));
    args.push_back(Var(z)); args.push_back(Var(z));
    if (args.size()==_contents.ptr->args.size()) {
        cerr << "Call to Union operation has incorrect number of arguments" << endl;
        assert(false);
    }
    return Call::make(*this, args);
}

Expr UnionReduction::operator()(string x, string y, string z, string w, string u) const {
    vector<Expr> args(5);
    args.push_back(Var(x)); args.push_back(Var(y));
    args.push_back(Var(z)); args.push_back(Var(z));
    args.push_back(Var(u));
    if (args.size()==_contents.ptr->args.size()) {
        cerr << "Call to Union operation has incorrect number of arguments" << endl;
        assert(false);
    }
    return Call::make(*this, args);
}

Expr UnionReduction::operator()(string x, string y, string z, string w, string u, string v) const {
    vector<Expr> args(6);
    args.push_back(Var(x)); args.push_back(Var(y));
    args.push_back(Var(z)); args.push_back(Var(z));
    args.push_back(Var(u)); args.push_back(Var(v));
    if (args.size()==_contents.ptr->args.size()) {
        cerr << "Call to Union operation has incorrect number of arguments" << endl;
        assert(false);
    }
    return Call::make(*this, args);
}

Expr UnionReduction::operator()(vector<string> args) const {
    vector<Expr> var_args(args.size());
    for (size_t i=0; i<var_args.size(); i++)
        var_args[i] = Var(args[i]);
    if (var_args.size()==_contents.ptr->args.size()) {
        cerr << "Call to Union operation has incorrect number of arguments" << endl;
        assert(false);
    }
    return Call::make(*this, var_args);
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

// -----------------------------------------------------------------------------

UnionFusion::UnionFusion() {}

UnionFusion::UnionFusion(const UnionReduction& a, const UnionReduction& b) {
    assert(a.can_merge(b) && "Cannot merge union operations");
    union_op = vec(a,b);
}

UnionFusion::UnionFusion(const UnionReduction& a, const UnionReduction& b, const UnionReduction& c) {
    assert(a.can_merge(b) && "Cannot merge union operations");
    assert(a.can_merge(c) && "Cannot merge union operations");
    assert(b.can_merge(c) && "Cannot merge union operations");
    union_op = vec(a,b,c);
}

//Func UnionFusion::convert_to_func() const {
//    // if the union operation's input expression is another union
//    // operation then descend recursively
//    // Depth first traversal of the dependency directed acyclic graph
//    Func f;
//    return f;
//}

}

// -----------------------------------------------------------------------------

ostream &operator<<(ostream &s, Internal::UnionReduction u) {
    return u.print(s);
}

}
