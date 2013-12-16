#include <iostream>
#include <cstdlib>
#include <cstdio>

#include "Halide.h"

using namespace Halide;
using namespace Halide::Internal;

void print(Func f, std::ostream& s) {
    if (f.defined()) {
        std::vector<Var> args = f.args();
        Expr value = f.value();
        s << f.name() << "(";
        for (size_t i=0; i<args.size(); i++) {
            s << args[i];
            if (i<args.size()-1)
                s << ",";
        }
        s << ") = " << value << "\n";
    }
    for (size_t j=0; j<f.num_reduction_definitions(); j++) {
        std::vector<Expr> args = f.reduction_args(j);
        Expr value = f.reduction_value(j);
        s << f.name() << "(";
        for (size_t i=0; i<args.size(); i++) {
            s << args[i];
            if (i<args.size()-1)
                s << ",";
        }
        s << ") = " << value << "\n";
    }
    s << std::endl;
}

int main() {
    unsigned int width = 30;
    unsigned int tile  = 5;

    Image<int> input(width, width, "Input");

    for (size_t j=0; j<width; j++)
        for (size_t i=0; i<width; i++)
            input(i,j) = rand() % 10;

    // -------------------------------------------------------------------------

    Var x("x");
    Var y("y");
    UnionVar rx(0, x, "rx");
    UnionVar ry(0, y, "ry");

    UnionReduction union_operation(
            input(rx, ry),          // expression to be union'ed
            vec(x.name(),y.name()), // output domain
            vec(rx, ry), "U");      // union domain

    union_operation
        .bound(x.name(), int(width))
        .bound(y.name(), int(width));

    // -------------------------------------------------------------------------

    std::cerr << "\nOriginal Union operation\n" << union_operation << std::endl;

    // -------------------------------------------------------------------------

    union_operation.split(x.name(), tile);
    std::cerr << "\nAfter spitting along x\n" << union_operation << std::endl;

    // -------------------------------------------------------------------------

    //union_operation.split(y.name(), tile);
    std::cerr << "\nAfter spitting along y\n" << union_operation << std::endl;

    // -------------------------------------------------------------------------

    std::cerr << "\nHalide Functions for the above" << std::endl;
    std::vector<Function> func_list = union_operation.funcs();
    for (size_t i=0; i<func_list.size(); i++) {
        Func f(func_list[i]);
        print(f, std::cerr);
    }

    return EXIT_SUCCESS;
}
