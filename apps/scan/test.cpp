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
        s << ") = " << value << "  ";
        for (size_t k=0; k<f.reduction_domain(j).dimensions(); k++)
            s << f.reduction_domain(j)[k].name()  << "["
              << f.reduction_domain(j)[k].min()   << ","
              << simplify(f.reduction_domain(j)[k].min()+f.reduction_domain(j)[k].extent()-1) << "] ";
        s << "\n";
    }
    return s;
}

int main() {
    unsigned int width = 20;
    unsigned int tile  = 5;

    Image<int> input(width, width, "input");
    Image<int> reference(width, width, "Reference");
    Image<int> output(width, width, "Output");

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

    // -------------------------------------------------------------------------

    Var x("x");
    Var y("y");
    Var xo("xo");
    Var yo("yo");
    Var xi("xi");
    Var yi("yi");

    Func Input("Input");
    Input(x,y) = input(clamp(x, 0, int(width-1)), clamp(y, 0, int(width-1)));

    Func f_main("Main");

    // ---------

    Func U_Intra_x_Intra_y_func_rxi;
    U_Intra_x_Intra_y_func_rxi(xo,xi,yo,yi) = Input(((xo*5) + xi), ((yo*5) + yi));
    RDom rxi(1,4); U_Intra_x_Intra_y_func_rxi(xo,rxi,yo,yi) = (U_Intra_x_Intra_y_func_rxi(xo, rxi, yo, yi) + U_Intra_x_Intra_y_func_rxi(xo, (rxi - 1), yo, yi));

    Func U_Intra_x_Intra_y_func;
    U_Intra_x_Intra_y_func(xo,xi,yo,yi) = U_Intra_x_Intra_y_func_rxi(xo, xi, yo, yi);
    RDom ryi(1,4); U_Intra_x_Intra_y_func(xo,xi,yo,ryi) = (U_Intra_x_Intra_y_func(xo, xi, yo, ryi) + U_Intra_x_Intra_y_func(xo, xi, yo, (ryi - 1)));

    Func U_Intra_x_Outer_y_func;
    U_Intra_x_Outer_y_func(xo,xi,yo,yi) = U_Intra_x_Intra_y_func(xo, xi, yo, yi);
    RDom ryo(1,3); U_Intra_x_Outer_y_func(xo,xi,ryo,yi) = (U_Intra_x_Outer_y_func(xo, xi, ryo, yi) + U_Intra_x_Outer_y_func(xo, xi, (ryo - 1), yi));

    Func U_Intra_x_func;
    U_Intra_x_func(xo,xi,y) = (U_Intra_x_Intra_y_func(xo, xi, (y/5), (y % 5)) + select(((y/5) > 0), U_Intra_x_Outer_y_func(xo, xi, ((y/5) - 1), 4), 0));

    Func U_Outer_x_func;
    U_Outer_x_func(xo,xi,y) = U_Intra_x_func(xo, xi, y);
    RDom rxo(1,3); U_Outer_x_func(rxo,xi,y) = (U_Outer_x_func(rxo, xi, y) + U_Outer_x_func((rxo - 1), xi, y));

    Func U_func;
U_func(x,y) = (U_Intra_x_func((x/5), (x % 5), y) + select(((x/5) > 0), U_Outer_x_func(((x/5) - 1), 4, y), 0));

    // ---------

    f_main = U_func;

    f_main.realize(output);

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

    return EXIT_SUCCESS;
}
