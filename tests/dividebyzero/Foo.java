import org.checkerframework.checker.dividebyzero.qual.*;

// A simple test case for your divide-by-zero checker.
// The file contains "// ::" comments to indicate expected
// errors and warnings; see
// https://github.com/typetools/checker-framework/blob/master/checker/tests/README.
//
// Passing this test does not guarantee a perfect grade on this assignment,
// but it is an important start. You should always write your own test cases,
// in addition to using those provided to you.
class Foo {

    public static void f() {
        int one  = 1;
        int zero = 0;
        // :: error: divide.by.zero
        int x    = one / zero;
        int y    = zero / one;
        // :: error: divide.by.zero
        int z    = x / y;
        String s = "hello";
    }

    public static void g(int y) {
        if (y == 0) {
            // :: error: divide.by.zero
            int x = 1 / y;
        } else {
            int x = 1 / y;
        }

        if (y != 0) {
            int x = 1 / y;
        } else {
            // :: error: divide.by.zero
            int x = 1 / y;
        }

        if (!(y == 0)) {
            int x = 1 / y;
        } else {
            // :: error: divide.by.zero
            int x = 1 / y;
        }

        if (!(y != 0)) {
            // :: error: divide.by.zero
            int x = 1 / y;
        } else {
            int x = 1 / y;
        }

        if (y < 0) {
            int x = 1 / y;
        }

        if (y <= 0) {
            // :: error: divide.by.zero
            int x = 1 / y;
        }

        if (y > 0) {
            int x = 1 / y;
        }

        if (y >= 0) {
            // :: error: divide.by.zero
            int x = 1 / y;
        }
    }

    public static void h() {
        int zero_the_hard_way = 0 + 0 - 0 * 0;
        // :: error: divide.by.zero
        int x = 1 / zero_the_hard_way;

        int one_the_hard_way = 0 * 1 + 1;
        int y = 1 / one_the_hard_way;
    }

    public static void l() {
        // :: error: divide.by.zero
        int a = 1 / (1 - 1);
        int y = 1;
        // :: error: divide.by.zero
        int x = 1 / (y - y);
        int z = y-y;
        // :: error: divide.by.zero
        int k = 1/z;
    }

    public static void safeAddition() {
        // both positive
        int a = 1 / (2 + 3);

        // both negative
        int b = -1 / (-4 + -6);
    }

    public static void safeSubtraction() {
        // negative minus a postive isn't zero
        int a = 1 / (-3 - 4);

        // positive minus a negative isn't zero
        int b = -5;
        int c = 10 / (1 - b);
    }

    public static void multiplicationPreservesSigns() {

        int a = 1 * 2;
        int b = 3 + a;
        int c = -1 / b;

        int d = 1 * -3;
        int e = 3 + d;
        // :: error: divide.by.zero
        int f = 2 / e;
    }

    public static void complicatedSafeSequence() {
        int c = 3;
        c += 5;
        c *= (2 + 1);
        c *= (-3 * -4);
        c += 1;
        int d = 1 / c;
    }

    public static void divisionAssignment() {
        int a = 3;
        // :: error: divide.by.zero
        a /= 0;

        int b = 10;
        // :: error: divide.by.zero
        b /= (3 * 0);
    }

    public static void branchDivision(int i) {
        int a = 1;
        if (i % 2 == 0) {
            a = -1;
        } else {
            a = 1;
        }
        // no error
        int x = i / a;
    }

    public static void loopAccumulate() {
        int x = 1;
        for (int i = 0; i < 50; i++) {
            if (i % 2 == 0) {
                x = -1*x;
            } else {
                x = 1*x;
            }
        }
        // no error
        int y = 1 / x;
    }

    public static void divideByMod() {
        int x = 4 % 2;
        // :: error: divide.by.zero
        int y = 3 / x;
    }

    public static void truncatingDivision() {
        int x = 3 / 4;
        // :: error: divide.by.zero
        int y = 3 / x;
    }

    public static void branchBySign(int x) {
        int y = 5;
        if (x < 0) {
            y -= x;
        } else {
            y += x;
        }
        // no error
        int z = 1 / y;
    }

    public static void modSigns(int x) {
        int divisor = 1;
        if (x < 0) {
            // x % 3 is non-positive
            divisor -= x % 3;
        } else {
            // x % -3 is non-negative
            divisor += x % -3;
        }
        // no error
        int y = 1 / divisor;
    }

    public static void cautiousCheck(int x) {
        int bound = x;
        if (bound < 0) {
            bound = -1*bound;
        }

        int divisor = bound + 1;
        for (int i = 0; i < bound; i++) {
            divisor--;
        }
        // in reality, the result will always be 1,
        // but without unrolling the loop or some kind of interval analysis,
        // this analysis will not be able to conclude that the divisor is nonzero
        if (divisor <= 0) {
            assert false;
        } else {
            // no error
            int z = 1 / divisor;
        }
    }


}
