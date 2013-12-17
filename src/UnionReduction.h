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

struct UnionVarContents {
    mutable RefCount ref_count;
    std::string      var;
    Expr             min;
    Expr             extent;
    ReductionDomain  domain;
};

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

class UnionVar {
private:
    IntrusivePtr<UnionVarContents> _contents;
public:
    EXPORT UnionVar();
    EXPORT UnionVar(const IntrusivePtr<UnionVarContents>&);
    EXPORT UnionVar(Expr m, Expr e);
    EXPORT UnionVar(Expr m, Expr e, std::string n);
    EXPORT const std::string &name()     const;
    EXPORT const Expr        &min()      const;
    EXPORT const Expr        &extent()   const;
    EXPORT bool same_as(const UnionVar&) const;
    EXPORT operator Expr()               const;
};

class UnionReduction {
private:
    IntrusivePtr<UnionReductionContents> _contents;

    // Map union variables to args
    EXPORT void convert_to_func();

public:
    EXPORT UnionReduction();
    EXPORT UnionReduction(const IntrusivePtr<UnionReductionContents>&);
    EXPORT UnionReduction(Expr in,
            std::vector<std::string> args,
            std::vector<UnionVar> uvars,
            std::string name);

    // Accessor functions
    EXPORT const Type                        &type()   const;
    EXPORT const std::string                 &name()   const;
    EXPORT const Expr                        &input()  const;
    EXPORT const std::vector<UnionVar>       &uvars()  const;
    EXPORT const std::vector<std::string>    &args()   const;
    EXPORT const std::vector<UnionReduction> &sub_unions() const;

    // Conversion to Halide Func
    EXPORT std::vector<Function> funcs();

    // Bounds
    EXPORT UnionReduction &bound(std::string, Expr, Expr);
    EXPORT const Expr     &lower_bound(std::string) const;
    EXPORT const Expr     &upper_bound(std::string) const;

    // // Checking functions
    // EXPORT bool is_identical (const UnionReduction&) const;
    // EXPORT bool is_subset    (const UnionReduction&) const;
    // EXPORT bool is_same_input(const UnionReduction&) const;

    // // Checking read and write complexity
    // EXPORT int  read_complexity()  const;
    // EXPORT int  write_complexity() const;

    // Splitting functions
    EXPORT UnionReduction& split(std::string x, int tile);

    // Call to the union operation
    EXPORT Expr call_as_func (const std::vector<Expr>&) const;
    EXPORT Expr call_as_union(const std::vector<Expr>&) const;
    EXPORT Expr call_as_union(const std::vector<std::string>&) const;

    EXPORT std::ostream &print(std::ostream&) const;
};

}

/** Print the Union operation in a human-readable form. */
EXPORT std::ostream &operator<<(std::ostream&, Internal::UnionReduction);

}

#endif
