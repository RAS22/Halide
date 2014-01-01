#include <iostream>
#include <cstdlib>
#include <cstdio>

#include "Halide.h"

using namespace Halide;
using namespace Halide::Internal;

std::ostream &operator<<(std::ostream &s, Func f) {
    if (f.defined()) {
        std::vector<Var> args = f.args();
        Expr value = f.value();
        s << "Func " << f.name() << ";\n";
        s << f.name() << "(";
        for (size_t i=0; i<args.size(); i++) {
            s << args[i];
            if (i<args.size()-1)
                s << ",";
        }
        s << ") = " << value << ";\n";
    }

    for (size_t j=0; j<f.num_reduction_definitions(); j++) {
        for (size_t k=0; k<f.reduction_domain(j).dimensions(); k++) {
            std::string r = f.reduction_domain(j)[k].name();
            r.erase(r.find(".x$r"));
            s << "RDom " << r  << "("
              << f.reduction_domain(j)[k].min()   << ","
              << f.reduction_domain(j)[k].extent()<< "); ";
        }
        std::vector<Expr> args = f.reduction_args(j);
        Expr value = f.reduction_value(j);
        s << f.name() << "(";
        for (size_t i=0; i<args.size(); i++) {
            s << args[i];
            if (i<args.size()-1)
                s << ",";
        }
        s << ") = " << value << ";\n";
    }
    return s;
}

int main() {
    unsigned int width = 20;
    unsigned int tile  = 5;

    Image<int> input(width, width);
    Image<int> reference(width, width);
    Image<int> output(width, width);

    // -------------------------------------------------------------------------

    for (size_t j=0; j<width; j++)
        for (size_t i=0; i<width; i++)
            input(i,j) = rand() % 5;
    for (size_t j=0; j<width; j++)
        for (size_t i=0; i<width; i++)
            reference(i,j) = input(i,j)
                + (i>0 ? reference(i-1,j) : 0)
                + (j>0 ? reference(i,j-1) : 0)
                - (i>0 && j>0 ? reference(i-1,j-1) : 0);

    Var x("x");
    Var y("y");

    // -------------------------------------------------------------------------

    Func Input("Input");
    Input(x,y) = input(clamp(x, 0, int(width-1)), clamp(y, 0, int(width-1)));

    // -------------------------------------------------------------------------

    RDom rx(0, x, "rx");
    RDom ry(0, y, "ry");
    UnionReduction union_operation(Input(rx,ry), vec(x.name(),y.name()), "U");

    // -------------------------------------------------------------------------

    std::cout << "\nOriginal Union operation\n" << union_operation << std::endl;

    union_operation.split(x.name(), tile);
    union_operation.split(y.name(), tile);
    std::cout << "\nAfter spitting along x and y\n" << union_operation << std::endl;

    // -------------------------------------------------------------------------

    Func f_main("Main");

    std::cout << "\n\nConversion into Functions\n" << std::endl;
    std::vector<Function> func_list = union_operation.funcs();
    for (size_t i=0; i<func_list.size(); i++) {
        Func f(func_list[i]);
        if (f.name() == union_operation.name()) {
            f_main = f;
        }
        std::cout << f << std::endl;
    }

    // -------------------------------------------------------------------------

    std::cout << "Compiling JIT" << std::endl;
    f_main.compile_jit();
    std::cout << "Realizing" << std::endl;
//    f_main.realize(output);
    std::cout << "done" << std::endl;

    // -------------------------------------------------------------------------

    std::cout << "Comparing" << std::endl;
    for (size_t j=0; j<width; j++) {
        for (size_t i=0; i<width; i++)
            std::cout << input(i,j) << "  ";
        std::cout << std::endl;
    }
    std::cout << std::endl;
    for (size_t j=0; j<width; j++) {
        for (size_t i=0; i<width; i++)
            std::cout << reference(i,j) << "  ";
        std::cout << std::endl;
    }
    std::cout << std::endl;
    for (size_t j=0; j<width; j++) {
        for (size_t i=0; i<width; i++)
            std::cout << output(i,j) << "  ";
        std::cout << std::endl;
    }

    // -------------------------------------------------------------------------

    int diff = 0;
    for (size_t j=0; j<width; j++)
        for (size_t i=0; i<width; i++)
            diff += std::abs(reference(i,j) - output(i,j));

    if (diff) {
        std::cerr << "Error: difference between output and reference: " << diff << std::endl;
        assert(false);
    }

    // -------------------------------------------------------------------------

    return EXIT_SUCCESS;
}
