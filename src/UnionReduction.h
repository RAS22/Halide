#ifndef HALIDE_UNION_REDUCTION_H
#define HALIDE_UNION_REDUCTION_H

#include "IntrusivePtr.h"
#include "Reduction.h"

#include <iostream>
#include <string>
#include <vector>
#include <map>

namespace Halide {

class Var;
class Expr;

namespace Internal {

struct UnionVarContents;
struct UnionReductionContents;

class UnionVar;
class UnionReduction;

// -----------------------------------------------------------------------------

struct UnionVarContents {
    mutable RefCount ref_count;
    std::string      var;
    Expr             min;
    Expr             extent;
    ReductionDomain  domain;
};

// -----------------------------------------------------------------------------

struct UnionReductionContents {
    mutable RefCount                  ref_count;
    Expr                              input;
    Type                              type;
    std::string                       name;
    std::vector<UnionVar>             uvars;
    std::vector<std::string>          args;
    std::vector<UnionReduction>       sub_unions;
    std::vector<Function>             funcs;
    std::map<std::string,Expr>        lower_bound;
    std::map<std::string,Expr>        upper_bound;
    std::map<std::string,std::string> arg_to_uvar;
    std::map<std::string,std::string> uvar_to_arg;
};

// -----------------------------------------------------------------------------

class UnionVar {
private:
    IntrusivePtr<UnionVarContents> _contents;
public:
    EXPORT UnionVar();
    EXPORT UnionVar(const IntrusivePtr<UnionVarContents>&);
    EXPORT UnionVar(Expr m, Expr e);
    EXPORT UnionVar(Expr m, Expr e, std::string n);
    EXPORT std::string name()            const;
    EXPORT Expr        min()             const;
    EXPORT Expr        extent()          const;
    EXPORT bool        same_as(UnionVar) const;
    EXPORT operator Expr()               const;
};

// -----------------------------------------------------------------------------

class UnionReduction {
private:
    IntrusivePtr<UnionReductionContents> _contents;

    // Map union variables to args
    EXPORT void convert_to_func();

public:
    EXPORT UnionReduction();
    EXPORT UnionReduction(std::string name);
    EXPORT UnionReduction(const IntrusivePtr<UnionReductionContents>&);
    EXPORT UnionReduction(Expr in, std::vector<std::string> args, std::string name);

    // Accessor functions
    EXPORT Type                        type()   const;
    EXPORT std::string                 name()   const;
    EXPORT Expr                        value()  const;
    EXPORT std::vector<UnionVar>       uvars()  const;
    EXPORT std::vector<std::string>    args()   const;
    EXPORT std::vector<UnionReduction> sub_unions() const;

    // Conversion to Halide Func
    EXPORT std::vector<Function> funcs();

    // Bounds
    EXPORT UnionReduction &bound(std::string, Expr, Expr);
    EXPORT Expr lower_bound(std::string) const;
    EXPORT Expr upper_bound(std::string) const;

    // Splitting functions
    EXPORT UnionReduction& split(std::string x, int tile);

    // Call to the union operation
    EXPORT Expr call_as_func (std::vector<Expr>) const;
    EXPORT Expr call_as_union(std::vector<Expr>) const;
    EXPORT Expr call_as_union(std::vector<std::string>) const;

    EXPORT std::ostream &print(std::ostream&) const;
};

}

/** Print the Union operation in a human-readable form. */
EXPORT std::ostream &operator<<(std::ostream&, Internal::UnionReduction);

}

#endif
