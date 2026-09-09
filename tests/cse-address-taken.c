/* An operand whose address has escaped can be written through that pointer
 * between two occurrences of an expression, so the value the first computed
 * no longer stands for the second. cse() refused a global operand for that
 * reason and not an escaped one, and reused the stale result.
 *
 * The write has to sit between the two occurrences, and both have to be in
 * one block for cse() to consider them at all.
 */

int assign_through(int *q)
{
    *q = 99;
    return 0;
}

int written_here(int a, int b)
{
    int x = a + b;
    int *p = &a;
    *p = 99;
    int y = a + b;
    return x * 1000 + y;
}

int written_by_callee(int a, int b)
{
    int x = a + b;
    assign_through(&a);
    int y = a + b;
    return x * 1000 + y;
}

int multiply(int a, int b)
{
    int x = a * b;
    int *p = &a;
    *p = 5;
    int y = a * b;
    return x * 1000 + y;
}

int main()
{
    if (written_here(1, 2) != 3101)
        return 1;
    if (written_by_callee(1, 2) != 3101)
        return 2;
    if (multiply(2, 3) != 6015)
        return 3;
    return 0;
}
