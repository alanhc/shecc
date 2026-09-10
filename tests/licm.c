/* Loop-invariant code motion moves a computation whose operands do not change
 * between iterations into the preheader. Getting that wrong is not a missed
 * optimisation: hoisting something that does vary changes what the program
 * computes, and the shapes below are the ones where telling the two apart is
 * not obvious from the instruction alone.
 *
 * Each function returns a value the caller checks, so a wrong hoist shows up
 * as a wrong answer rather than as slower code.
 */

/* The plain case: a product of two values the loop never writes. It should
 * move, and the answer must not change when it does.
 */
int invariant_product(int a, int b, int n)
{
    int acc = 0;

    for (int i = 0; i < n; i++) {
        int k = a * b;
        acc = acc + k + i;
    }
    return acc;
}

/* An inner loop's counter initialisation.
 *
 * const_folding() has reduced "int j = 0" to a bare load of a constant with no
 * operands by the time this pass runs, so nothing about its inputs marks it as
 * varying, and its block genuinely dominates the outer loop's latch. Hoisting
 * it out of the enclosing loop leaves j holding whatever the previous trip
 * left, and the inner loop then runs once in total rather than once per outer
 * iteration.
 */
int nested_counter_init(int n)
{
    int acc = 0;

    for (int i = 0; i < n; i++) {
        int j = 0;
        while (j < n) {
            acc = acc + 1;
            j = j + 1;
        }
    }
    return acc;
}

/* The same hazard one level deeper, where the middle loop's counter is both a
 * stayer for the outer loop and a candidate for the inner one.
 */
int triple_nested(int n)
{
    int acc = 0;

    for (int i = 0; i < n; i++) {
        int j = 0;
        while (j < n) {
            int k = 0;
            while (k < n) {
                acc = acc + 1;
                k = k + 1;
            }
            j = j + 1;
        }
    }
    return acc;
}

/* A chain: t is invariant, and inv reads t. Marking only what has unmoving
 * operands stalls here -- inv reads a variable written inside the loop and
 * looks varying, and inv staying behind pins t. Both should move, and the
 * answer is the same either way.
 */
int invariant_chain(int p, int q, int n)
{
    int acc = 0;

    for (int i = 0; i < n; i++) {
        int t = p * q;
        int inv = t;
        acc = acc + inv;
    }
    return acc;
}

/* A value that varies because the loop writes it. Nothing here may move.
 */
int varying_accumulator(int a, int n)
{
    int acc = 1;

    for (int i = 0; i < n; i++) {
        int k = acc + a;
        acc = k;
    }
    return acc;
}

/* An operand written later in the body than the instruction reading it. The
 * read happens on the next iteration's value, so the multiplication is not
 * invariant however fixed its operands look at that point.
 */
int operand_written_below(int a, int n)
{
    int acc = 0;
    int m = 1;

    for (int i = 0; i < n; i++) {
        int k = m * a;
        acc = acc + k;
        m = m + 1;
    }
    return acc;
}

/* A loop that may run zero times. Anything hoisted into the preheader runs
 * even when the body does not, so a division would fault where the original
 * program never divided. insn_is_speculatable() is what keeps it in place.
 */
int zero_trip(int a, int b, int n)
{
    int acc = 0;

    for (int i = 0; i < n; i++) {
        int k = a / b;
        acc = acc + k;
    }
    return acc;
}

/* A call in the body. It may run a different number of times if anything
 * around it moves incorrectly, and the counter proves how often it ran.
 */
int calls = 0;

int bump(void)
{
    calls = calls + 1;
    return 2;
}

int call_in_body(int a, int n)
{
    int acc = 0;

    calls = 0;
    for (int i = 0; i < n; i++) {
        int k = a * 3;
        acc = acc + k + bump();
    }
    return acc * 100 + calls;
}

int main()
{
    /* 4 * 6 + (0 + 1 + 2 + 3) */
    if (invariant_product(2, 3, 4) != 30)
        return 1;
    /* the inner loop runs n times for each of n outer trips */
    if (nested_counter_init(4) != 16)
        return 2;
    if (nested_counter_init(1) != 1)
        return 3;
    if (triple_nested(4) != 64)
        return 4;
    /* 4 * (2 * 3) */
    if (invariant_chain(2, 3, 4) != 24)
        return 5;
    /* 3, 5, 7, 9 */
    if (varying_accumulator(2, 4) != 9)
        return 6;
    /* 1*2 + 2*2 + 3*2 + 4*2 */
    if (operand_written_below(2, 4) != 20)
        return 7;
    /* the body never runs, so the division never happens */
    if (zero_trip(6, 0, 0) != 0)
        return 8;
    if (zero_trip(6, 3, 2) != 4)
        return 9;
    /* (4 * (6 + 2)) * 100 + 4 calls */
    if (call_in_body(2, 4) != 3204)
        return 10;
    return 0;
}
