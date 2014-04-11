#ifndef HALIDE_UNION_H
#define HALIDE_UNION_H

#include "IR.h"
#include "Var.h"
#include "IntrusivePtr.h"
#include "Union.h"
#include "Param.h"
#include "Argument.h"
#include "RDom.h"
#include "Util.h"
#include "Tuple.h"

namespace Halide {


class Union {
    Internal::UnionReduction union_op;

public:
    EXPORT static void test();

    EXPORT Union();
    EXPORT Union(std::string name);
    EXPORT Union(std::string name, Expr input, Var x);
    EXPORT Union(std::string name, Expr input, Var x, Var y);
    EXPORT Union(std::string name, Expr input, Var x, Var y, Var z);
    EXPORT Union(std::string name, Expr input, Var x, Var y, Var z, Var w);
    EXPORT Union(std::string name, Expr input, std::vector<Var> var);

    EXPORT std::string      name()   const;
    EXPORT std::vector<Var> args()   const;
    EXPORT Expr             value()  const;
    EXPORT Type             type()   const;
    EXPORT RDom             domain() const;

    EXPORT std::vector<Func> funcs();
    EXPORT Union& split(Var x, int tile);

    EXPORT UnionRefVar operator()(Var x) const;
    EXPORT UnionRefVar operator()(Var x, Var y) const;
    EXPORT UnionRefVar operator()(Var x, Var y, Var z) const;
    EXPORT UnionRefVar operator()(Var x, Var y, Var z, Var w) const;
    EXPORT UnionRefVar operator()(Var x, Var y, Var z, Var w, Var u) const;
    EXPORT UnionRefVar operator()(Var x, Var y, Var z, Var w, Var u, Var v) const;
    EXPORT UnionRefVar operator()(std::vector<Var>) const;

    EXPORT std::ostream &print(std::ostream &s);
};

EXPORT ostream &operator<<(ostream &s, Union u);

}

#endif
