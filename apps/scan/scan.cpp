#include <iostream>
#include <cstdlib>
#include <cstdio>

#include "Halide.h"

using namespace Halide;
using namespace Halide::Internal;


int main() {
    unsigned int width = 30;
    unsigned int tile  = 5;

    Image<int> input(width, width, width, "Input");

    for (size_t k=0; k<width; k++)
        for (size_t j=0; j<width; j++)
            for (size_t i=0; i<width; i++)
                input(i,j,k) = rand() % 10;

    // -------------------------------------------------------------------------

    Var x("x");
    Var y("y");
    Var z("z");
    UnionVar rx(0, x, "rx");
    UnionVar ry(0, y, "ry");
    UnionVar rz(0, z, "rz");

    UnionReduction union_operation(
            input(rx, ry, rz),                // expression to be union'ed
            vec(x.name(),y.name(), z.name()), // output domain
            vec(rx, ry, rz));                 // union domain

    union_operation
        .bound(x.name(), int(width))
        .bound(y.name(), int(width))
        .bound(z.name(), int(width));

    // -------------------------------------------------------------------------

    std::cerr << "\nOriginal Union operation\n" << union_operation << std::endl;

    // -------------------------------------------------------------------------

    union_operation.split(x.name(), tile);
    std::cerr << "\nAfter spitting along x\n" << union_operation << std::endl;

    // -------------------------------------------------------------------------

    union_operation.split(y.name(), tile);
    std::cerr << "\nAfter spitting along y\n" << union_operation << std::endl;

    // -------------------------------------------------------------------------

    union_operation.split(z.name(), tile);
    std::cerr << "\nAfter spitting along z\n" << union_operation << std::endl;

    // -------------------------------------------------------------------------

    return EXIT_SUCCESS;
}
