#include "IR.h"
#include "Union.h"
#include "Util.h"
#include "IROperator.h"
#include "IRPrinter.h"
#include "Argument.h"
#include "Lower.h"
#include "StmtCompiler.h"
#include "Param.h"
#include <algorithm>
#include <iostream>
#include <string>

using std::string;
using std::vector;
using std::ostream;

namespace Halide {

using std::max;
using std::min;
using std::make_pair;
using std::string;
using std::vector;
using std::pair;

using namespace Internal;


Union::Union() : union_op("UnionDefault") {}

Union::Union(string n): union_op(name) {}

Union::Union(string n, Expr input, vector<Var> var) {
    vector<string> args(var.size());
    for (size_t i=0; i<args.size(); i++)
        args[i] = var[i].name();
    union_op(input, args, name);
}

Union::Union(string n, Expr input, Var x) {
    union_op(input, vec(x.name()), name);
}

Union::Union(string n, Expr input, Var x, Var y) {
    union_op(input, vec(x.name(), y.name()), name);
}

Union::Union(string n, Expr input, Var x, Var y, Var z) {
    union_op(input, vec(x.name(), y.name(), z.name()), name);
}

Union::Union(string n, Expr input, Var x, Var y, Var z, Var w) {
    union_op(input, vec(x.name(), y.name(), z.name(), w.name()), name);
}

string   Union::name()  const { return union_op.name(); }
Expr     Union::value() const { return union_op.value();}
Type     Union::type()  const { return union_op.type(); }
ostream& Union::print(ostream &s) const { return union_op.print(s); }

RDom Union::domain() const {
    assert(defined() && "Can't query domain of uninitialized Union");
    RDom r;
    string n = union_op.name() + "_r";
    Internal::UnionVar uvars = union_op.union_vars();
    switch (uvars.size()) {
        case 1: r(union_op.uvar_min(0), union_op.uvar_extent(0), n); break;
        case 2: r(union_op.uvar_min(0), union_op.uvar_extent(0),
                  union_op.uvar_min(1), union_op.uvar_extent(1), n); break;
        case 3: r(union_op.uvar_min(0), union_op.uvar_extent(0),
                  union_op.uvar_min(1), union_op.uvar_extent(1),
                  union_op.uvar_min(2), union_op.uvar_extent(2), n); break;
        case 4: r(union_op.uvar_min(0), union_op.uvar_extent(0),
                  union_op.uvar_min(1), union_op.uvar_extent(1),
                  union_op.uvar_min(2), union_op.uvar_extent(2),
                  union_op.uvar_min(3), union_op.uvar_extent(3), n); break;
        default: break;
    }
    return r;
}

vector<Var> Union::args() const {
    assert(defined() && "Can't query args of uninitialized Union");
    vector<string> arg_names = union_op.args();
    vector<Var>    args(arg_names.size());
    for (size_t i = 0; i < arg_names.size(); i++) {
        args[i] = Var(arg_names[i]);
    }
    return args;
}

vector<Func> Union::funcs() {
    assert(defined() && "Can't convert uninitialized Union to Func");
    vector<Function> function_list = uniop_op.funcs();
    vector<Function> func_list(function_list.size());
    for (size_t i=0; i<function_list.size(); i++) {
        Func f(function_list[i]);
        func_list[i] = f;
    }
    return func_list;
}

Union& Union::split(Var x, int tile) {
    assert(defined() && "Can't split uninitialized Union");
    union_op.split(Var(x), tile);
    return *this;
}

void Union::test() {
    std::cout << "Union test passed" << std::endl;
}

// -----------------------------------------------------------------------------

ostream &operator<<(ostream &s, Union u) {
    return u.print(s);
}

}
