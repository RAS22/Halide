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
    mutable RefCount            ref_count;
    Expr                        input;
    Type                        type;
    std::string                 name;
    std::vector<UnionVar>       uvars;
    std::vector<std::string>    args;
    std::vector<UnionReduction> sub_unions;
    std::vector<Function>       funcs;
    std::map<std::string,Expr>  bound;
    std::map<std::string,int>   args_to_uvar;
    std::map<std::string,int>   uvar_to_arg;
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

    EXPORT void convert_to_func();
    EXPORT Expr as_func(const vector<Expr>& args) const;

public:
    EXPORT UnionReduction();
    EXPORT UnionReduction(const IntrusivePtr<UnionReductionContents>&);
    EXPORT UnionReduction(Expr in,
            const std::vector<std::string> &outvar,
            const std::vector<UnionVar> &uvar,
            const std::string &name);

    // Accessor functions
    EXPORT const Type                        &type()   const;
    EXPORT const std::string                 &name()   const;
    EXPORT const Expr                        &input()  const;
    EXPORT const std::vector<UnionVar>       &uvars()  const;
    EXPORT const std::vector<std::string>    &args()   const;
    EXPORT const std::vector<UnionReduction> &sub_unions() const;

    // Conversion to Halide Func
    EXPORT std::vector<Function&> &func() const;

    // Bounds
    EXPORT UnionReduction &bound(std::string, Expr);
    EXPORT const Expr     &bound(std::string) const;

    // // Checking functions
    // EXPORT bool is_identical (const UnionReduction&) const;
    // EXPORT bool is_subset    (const UnionReduction&) const;
    // EXPORT bool is_same_input(const UnionReduction&) const;

    // // Checking read and write complexity
    // EXPORT int  read_complexity()  const;
    // EXPORT int  write_complexity() const;

    // Splitting functions
    EXPORT UnionReduction& split(std::string x, int tile);

    // Call the union operation as an input to other unions/functions
    EXPORT Expr operator()(Expr x) const;
    EXPORT Expr operator()(Expr x, Expr y) const;
    EXPORT Expr operator()(Expr x, Expr y, Expr z) const;
    EXPORT Expr operator()(Expr x, Expr y, Expr z, Expr w) const;
    EXPORT Expr operator()(Expr x, Expr y, Expr z, Expr w, Expr u) const;
    EXPORT Expr operator()(Expr x, Expr y, Expr z, Expr w, Expr u, Expr v) const;
    EXPORT Expr operator()(std::vector<Expr>) const;

    EXPORT Expr operator()(std::string x) const;
    EXPORT Expr operator()(std::string x, std::string y) const;
    EXPORT Expr operator()(std::string x, std::string y, std::string z) const;
    EXPORT Expr operator()(std::string x, std::string y, std::string z, std::string w) const;
    EXPORT Expr operator()(std::string x, std::string y, std::string z, std::string w, std::string u) const;
    EXPORT Expr operator()(std::string x, std::string y, std::string z, std::string w, std::string u, std::string v) const;
    EXPORT Expr operator()(std::vector<std::string>) const;

    EXPORT std::ostream &print(std::ostream&) const;
};


class UnionFusion {
private:
    std::vector<UnionReduction> union_op;
public:
    EXPORT UnionFusion();
    EXPORT UnionFusion(const UnionReduction& a, const UnionReduction& b);
    EXPORT UnionFusion(const UnionReduction& a, const UnionReduction& b, const UnionReduction& c);
//    EXPORT Func convert_to_func() const;
};

}

/** Print the Union operation in a human-readable form. */
EXPORT std::ostream &operator<<(std::ostream&, Internal::UnionReduction);

}

#endif
