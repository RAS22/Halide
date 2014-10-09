#include <stdio.h>
#include <Halide.h>
#include <math.h>

using namespace Halide;
using std::vector;

// Make sure the interleave pattern generates good vector code

int main(int argc, char **argv) {
    Func f, g, h;
    Var x, y;

    f(x) = sin(x);
    g(x) = cos(x);
    h(x) = select(x % 2 == 0, 1.0f/f(x/2), g(x/2)*17.0f);

    f.compute_root();
    g.compute_root();
    h.vectorize(x, 8);

    h.compile_to_assembly("interleave.s", vector<Argument>());

    Image<float> result = h.realize(16);
    for (int x = 0; x < 16; x++) {
        float correct = ((x % 2) == 0) ? (1.0f/(sinf(x/2))) : (cosf(x/2)*17.0f);
        float delta = result(x) - correct;
        if (delta > 0.01 || delta < -0.01) {
            printf("result(%d) = %f instead of %f\n", x, result(x), correct);
            return -1;
        }
    }


    // Test interleave 3 vectors:
    Func planar, interleaved;
    planar(x, y) = Halide::cast<float>( 3 * x + y );
    interleaved(x, y) = planar(x, y);

    Var xy("xy");
    planar
        .compute_at(interleaved, xy)
        .vectorize(x, 4);

    interleaved
        .reorder(y, x)
        .bound(y, 0, 3)
        .fuse(y, x, xy)
        .vectorize(xy, 12);

    interleaved
        .output_buffer()
        .set_min(1, 0)
        .set_stride(0, 3)
        .set_stride(1, 1)
        .set_extent(1, 3);

    interleaved.compile_to_lowered_stmt("interleave_3.stmt");
    interleaved.compile_to_bitcode("interleave_3.bc", vector<Argument>());
    interleaved.compile_to_assembly("interleave_3.s", vector<Argument>());

    Buffer buff3;
    buff3 = Buffer(Float(32), 16, 3, 0, 0, (uint8_t *)0);
    buff3.raw_buffer()->stride[0] = 3;
    buff3.raw_buffer()->stride[1] = 1;

    Realization r3(Internal::vec(buff3));
    interleaved.realize(r3);

    Image<float> result3 = r3[0];
    for (int x = 0; x < 16; x++) {
        for (int y = 0; y < 3; y++) {
            float correct = 3*x + y;
            float delta = result3(x,y) - correct;
            if (delta > 0.01 || delta < -0.01) {
                printf("result(%d) = %f instead of %f\n", x, result3(x,y), correct);
                return -1;
            }
        }
    }

    // Test interleave 4 vectors:
    Func f1, f2, f3, f4, f5;
    f1(x) = sin(x);
    f2(x) = sin(2*x);
    f3(x) = sin(3*x);
    f4(x) = sin(4*x);
    f5(x) = sin(5*x);

    Func output4;
    output4(x, y) = select(y == 0, f1(x),
                           y == 1, f2(x),
                           y == 2, f3(x),
                           f4(x));

    output4
            .reorder(y, x)
            .bound(y, 0, 4)
            .unroll(y)
            .vectorize(x, 4);

    output4.output_buffer()
            .set_min(1, 0)
            .set_stride(0, 4)
            .set_stride(1, 1)
            .set_extent(1, 4);

    output4.compile_to_lowered_stmt("interleave_4.stmt");
    output4.compile_to_bitcode("interleave_4.bc", vector<Argument>());
    output4.compile_to_assembly("interleave_4.s", vector<Argument>());

    Buffer buff4;
    buff4 = Buffer(Float(32), 16, 4, 0, 0, (uint8_t *)0);
    buff4.raw_buffer()->stride[0] = 4;
    buff4.raw_buffer()->stride[1] = 1;

    Realization r4(Internal::vec(buff4));
    output4.realize(r4);

    Image<float> result4 = r4[0];
    for (int x = 0; x < 16; x++) {
        for (int y = 0; y < 4; y++) {
            float correct = sin((y+1)*x);
            float delta = result4(x,y) - correct;
            if (delta > 0.01 || delta < -0.01) {
                printf("result(%d) = %f instead of %f\n", x, result4(x,y), correct);
                return -1;
            }
        }
    }


    // Test interleave 5 vectors:
    Func output5;
    output5(x, y) = select(y == 0, f1(x),
                           y == 1, f2(x),
                           y == 2, f3(x),
                           y == 3, f4(x),
                           f5(x));

    output5
            .reorder(y, x)
            .bound(y, 0, 5)
            .unroll(y)
            .vectorize(x, 4);

    output5.output_buffer()
            .set_min(1, 0)
            .set_stride(0, 5)
            .set_stride(1, 1)
            .set_extent(1, 5);

    output5.compile_to_lowered_stmt("interleave_5.stmt");
    output5.compile_to_bitcode("interleave_5.bc", vector<Argument>());
    output5.compile_to_assembly("interleave_5.s", vector<Argument>());

    Buffer buff5;
    buff5 = Buffer(Float(32), 16, 5, 0, 0, (uint8_t *)0);
    buff5.raw_buffer()->stride[0] = 5;
    buff5.raw_buffer()->stride[1] = 1;

    Realization r5(Internal::vec(buff5));
    output5.realize(r5);

    Image<float> result5 = r5[0];
    for (int x = 0; x < 16; x++) {
        for (int y = 0; y < 5; y++) {
            float correct = sin((y+1)*x);
            float delta = result5(x,y) - correct;
            if (delta > 0.01 || delta < -0.01) {
                printf("result(%d) = %f instead of %f\n", x, result5(x,y), correct);
                return -1;
            }
        }
    }

    // Make sure we don't interleave when the reordering would change the meaning.
    Image<uint8_t> ref;
    for (int i = 0; i < 2; i++) {
        Func output6;
        output6(x, y) = cast<uint8_t>(x);
        RDom r(0, 16);

        // A not-safe-to-merge pair of updates
        output6(2*r, 0) = cast<uint8_t>(3);
        output6(2*r+1, 0) = output6(2*r, 0)+2;

        // A safe-to-merge pair of updates
        output6(2*r, 1) = cast<uint8_t>(3);
        output6(2*r+1, 1) = cast<uint8_t>(4);

        // A safe-to-merge-but-we-don't pair of updates, because they
        // load recursively, so we conservatively bail out.
        output6(2*r, 2) += 1;
        output6(2*r+1, 2) += 2;

        // A safe-to-merge-but-not-complete triple of updates:
        output6(3*r, 3) = cast<uint8_t>(3);
        output6(3*r+1, 3) = cast<uint8_t>(4);

        // A safe-to-merge triple of updates:
        output6(3*r, 3) = cast<uint8_t>(7);
        output6(3*r+2, 3) = cast<uint8_t>(9);
        output6(3*r+1, 3) = cast<uint8_t>(8);

        if (i == 0) {
            // Making the reference output.
            ref = output6.realize(50, 4);
        } else {
            // Vectorize and compare to the reference.
            for (int j = 0; j < 11; j++) {
                output6.update(j).vectorize(r);
            }
            Image<uint8_t> out = output6.realize(50, 4);
            for (int y = 0; y < ref.height(); y++) {
                for (int x = 0; x < ref.width(); x++) {
                    if (out(x, y) != ref(x, y)) {
                        printf("result(%d, %d) = %d instead of %d\n",
                               x, y, out(x, y), ref(x, y));
                        return -1;
                    }
                }
            }
        }
    }

    printf("Success!\n");
    return 0;
}
