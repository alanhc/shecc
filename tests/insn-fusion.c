/* The ALU/move fusion in peephole.c rewrites {ALU rn, rs1, rs2; mv rd, rn}
 * into {ALU rd, rs1, rs2} and drops the move.  That leaves rn holding
 * whatever it held before the ALU instruction, so it is only sound when
 * nothing downstream reads rn.
 *
 * A value used twice is what makes something read it: the allocator keeps the
 * first computation in a register, copies it to the second name, and then
 * spills the original to its own stack slot.  The spill reads rn after the
 * move, and fusing over it stores the stale register instead of the result.
 *
 * Each function below computes one value, names it twice, and combines both
 * names, so the fused register is read again by the spill in every case.
 */

int mul_twice(int a, int b)
{
    int r = a * b;
    int s = a * b;
    return r + s;
}

int add_twice(int a, int b)
{
    int r = a + b;
    int s = a + b;
    return r + s;
}

/* The combining operation is itself fusible here, so the pattern appears
 * twice in one block.
 */
int mul_twice_mul(int a, int b)
{
    int r = a * b;
    int s = a * b;
    return r * s;
}

int use(int x)
{
    return x;
}

/* The second use sits in a block the first dominates rather than beside it,
 * which is where the value has to survive the branch in a slot.
 */
int across_block(int a, int b, int c)
{
    int r = a * b;
    use(r);
    if (c > 0) {
        int s = a * b;
        return r + s;
    }
    return r;
}

int main()
{
    if (mul_twice(2, 3) != 12)
        return 1;
    if (add_twice(2, 3) != 10)
        return 2;
    if (mul_twice_mul(2, 3) != 36)
        return 3;
    if (across_block(2, 3, 1) != 12)
        return 4;
    if (across_block(2, 3, -1) != 6)
        return 5;
    return 0;
}
