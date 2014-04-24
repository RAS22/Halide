#ifndef HALIDE_UNION_REDUCTION_H
#define HALIDE_UNION_REDUCTION_H

#include "IntrusivePtr.h"
#include "Reduction.h"

#include <iostream>
#include <string>
#include <vector>
#include <map>

using std::string;
using std::map;
using std::vector;
using std::ostream;

namespace Halide {

class Var;
struct Expr;

namespace Internal {

struct UnionVarContents;
struct UnionReductionContents;

class UnionVar;
class UnionReduction;

// -----------------------------------------------------------------------------

struct UnionVarContents {
    mutable RefCount ref_count;
    string           var;
    Expr             min;
    Expr             extent;
    ReductionDomain  domain;
};

// -----------------------------------------------------------------------------

struct UnionReductionContents {
    mutable RefCount        ref_count;
    string                  name;
    vector<Expr>            input;
    vector<UnionVar>        uvars;
    vector<string>          args;
    vector<UnionReduction>  sub_unions;
    vector<Function>        funcs;
    map<string,Expr>        lower_bound;
    map<string,Expr>        upper_bound;
    map<string,string>      arg_to_uvar;
    map<string,string>      uvar_to_arg;
};

// -----------------------------------------------------------------------------

class UnionVar {
private:
    IntrusivePtr<UnionVarContents> _contents;
public:
    EXPORT UnionVar();
    EXPORT UnionVar(const IntrusivePtr<UnionVarContents>&);
    EXPORT UnionVar(Expr m, Expr e);
    EXPORT UnionVar(Expr m, Expr e, string n);
    EXPORT string name()            const;
    EXPORT Expr   min()             const;
    EXPORT Expr   extent()          const;
    EXPORT bool   same_as(UnionVar) const;
    EXPORT operator Expr()          const;
};

// -----------------------------------------------------------------------------

class UnionReduction {
private:
    IntrusivePtr<UnionReductionContents> _contents;

    // Conversion to Halide Func
    EXPORT void convert_to_func();

public:
    EXPORT UnionReduction();
    EXPORT UnionReduction(string name);
    EXPORT UnionReduction(const IntrusivePtr<UnionReductionContents>&);
    EXPORT UnionReduction(Expr in, vector<string> args, string name);
    EXPORT UnionReduction(vector<Expr> in, vector<string> args, string name);

    // Accessor functions
    EXPORT string name ()        const;
    EXPORT Expr   value(int idx) const;
    EXPORT Type   type (int idx) const;

    EXPORT vector<UnionVar>       uvars()      const;
    EXPORT vector<string>         args()       const;
    EXPORT vector<UnionReduction> sub_unions() const;

    // Conversion to Halide Func
    EXPORT vector<Function> funcs();

    // Bounds
    EXPORT UnionReduction &bound(string, Expr, Expr);
    EXPORT Expr lower_bound(string) const;
    EXPORT Expr upper_bound(string) const;

    // Splitting functions
    EXPORT UnionReduction& split(string x, int tile);

    // Merging union operations
    EXPORT static bool subset_merge(UnionReduction&, UnionReduction&);
    EXPORT static bool tuple_merge (UnionReduction&, UnionReduction&);

    // Call to the union operation
    EXPORT Expr call_as_func (vector<Expr>,  int) const;
    EXPORT Expr call_as_union(vector<Expr>,  int) const;
    EXPORT Expr call_as_union(vector<string>,int) const;

    EXPORT ostream &print(ostream&) const;
};

}

/** Print the Union operation in a human-readable form. */
EXPORT ostream &operator<<(ostream&, Internal::UnionReduction);

}

#endif
