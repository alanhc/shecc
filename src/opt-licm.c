/*
 * shecc - Self-Hosting and Educational C Compiler.
 *
 * shecc is freely redistributable under the BSD 2 clause license. See the file
 * "LICENSE" for information on usage and redistribution of this file.
 */

/* Loop-invariant code motion.
 *
 * A computation whose operands do not move between iterations produces the same
 * value every time round, so it can run once before the loop instead of once
 * per iteration. This pass finds those instructions and moves them into the
 * preheader.
 *
 * Two properties of the IR at this point shape what the pass can assume.
 * unwind_phi() has already run, so there are no phi instructions to repair -- a
 * value merging from two paths is an ordinary assignment in each of them. That
 * also means the single-definition property is gone, so "the operands do not
 * move" cannot be read off the names; licm_def_counts() counts the writes per
 * function and only a variable written exactly once is trusted, the same test
 * strength_reduce() makes for the same reason.
 *
 * Invariance is then a fixed point: an instruction is invariant when every
 * operand is either defined outside the loop or defined by an instruction
 * already known to be invariant. Hoisting one can expose another -- the operand
 * that kept it inside has just left -- so the walk repeats until a pass moves
 * nothing.
 */

/* Stamp identifying the loop currently being examined, matched against
 * basic_block_t::loop_mark. mark_natural_loop() advances loop_scan_gen and
 * marks the loop's blocks with it.
 */
int licm_gen;

/* Whether @var is written by an instruction inside the loop being examined.
 *
 * A variable written nowhere in the loop holds the same value throughout it,
 * whether it was defined before the loop or is a parameter. Globals and
 * address-taken variables are excluded by the caller instead: a store through a
 * pointer or a call writes them without naming them in an rd.
 */
bool licm_var_in_loop(func_t *func, var_t *var)
{
    if (!var)
        return false;

    for (basic_block_t *bb = func->bbs; bb; bb = bb->rpo_next) {
        if (bb->loop_mark != licm_gen)
            continue;
        for (insn_t *insn = bb->insn_list.head; insn; insn = insn->next) {
            if (insn->rd == var)
                return true;
        }
    }
    return false;
}

/* Count, for every variable named as a destination in @func, how many
 * instructions write it.
 *
 * Only a variable with exactly one definition can be reasoned about by name:
 * with the phis unwound, one name can stand for several values, and treating
 * the second as invariant because the first was would hoist a computation past
 * the assignment that changes it.
 */
void licm_def_counts(func_t *func)
{
    for (basic_block_t *bb = func->bbs; bb; bb = bb->rpo_next) {
        for (insn_t *insn = bb->insn_list.head; insn; insn = insn->next) {
            if (insn->rd)
                insn->rd->def_cnt = 0;
        }
    }
    for (basic_block_t *bb = func->bbs; bb; bb = bb->rpo_next) {
        for (insn_t *insn = bb->insn_list.head; insn; insn = insn->next) {
            if (insn->rd)
                insn->rd->def_cnt++;
        }
    }
}

/* Whether @var is fixed for the whole of the loop being examined.
 *
 * @func: the function the loop is in.
 * @var: the operand under test, which may be NULL for a missing source.
 *
 * A missing operand is trivially fixed. Anything global or address-taken is
 * not: this pass does no alias analysis, so a store through a pointer must be
 * assumed to reach it. What remains is fixed when the loop contains no write to
 * it.
 */
bool licm_operand_fixed(func_t *func, var_t *var)
{
    if (!var)
        return true;
    if (var->is_global || var->address_taken)
        return false;

    /* Already known to be invariant: the instruction defining it is moving to
     * the preheader, so by the time anything reading it runs, it holds the
     * value it will keep for the whole loop.
     *
     * Without this the set never grows past its first member. Every value the
     * loop computes is written inside the loop, so the test below rejects it,
     * and a chain like "t = p * q; inv = t" stalls: t is invariant, but inv
     * reads a variable written in the loop and looks varying, and then inv --
     * staying behind -- pins t as well.
     */
    if (var->loop_stamp == licm_gen)
        return true;
    return !licm_var_in_loop(func, var);
}

/* Whether the loop reads @insn's destination from an instruction that is
 * staying behind.
 *
 * A read by an instruction that is itself moving is not a reason to keep this
 * one: the two travel together and their order is preserved. A read by anything
 * else means the loop wants this value on the iteration it runs, so the write
 * has to run then too.
 *
 * That distinction is what separates the two cases the earlier attempts could
 * not tell apart. "int j = 0" is read by the loop test and the increment,
 * neither of which is invariant, so it stays; the "x * y" of a hoistable
 * expression is read only by the assignment that is moving with it.
 *
 * Candidacy is read off @var_t::loop_stamp, which licm_mark_invariant() has
 * already set for every destination it intends to move.
 */
bool licm_read_by_stayer(func_t *func, insn_t *insn)
{
    var_t *var = insn->rd;

    for (basic_block_t *bb = func->bbs; bb; bb = bb->rpo_next) {
        if (bb->loop_mark != licm_gen)
            continue;
        for (insn_t *i = bb->insn_list.head; i; i = i->next) {
            if (i == insn)
                continue;
            if (i->rs1 != var && i->rs2 != var && i->rs3 != var)
                continue;
            /* A reader that is moving too does not pin this instruction. */
            if (i->rd && i->rd->loop_stamp == licm_gen)
                continue;
            return true;
        }
    }
    return false;
}

/* Whether @insn can be moved to the preheader.
 *
 * insn_is_speculatable() answers the half of the question that does not depend
 * on the loop: no side effect, and no way to fault on a path that would not
 * have reached it. Division is excluded there, so a hoisted instruction cannot
 * introduce a trap the original program avoided by never entering the loop.
 *
 * The rest is about this loop. The destination must be a plain local written
 * once, or the move changes what other readers of the name see, and each
 * operand must hold still for the duration.
 */
bool licm_is_invariant(func_t *func,
                       insn_t *insn,
                       basic_block_t *bb,
                       basic_block_t *latch)
{
    if (!insn->rd)
        return false;

    /* The instruction has to run on every iteration, or moving it changes how
     * many times it runs rather than just when. A block that does not dominate
     * the latch sits on a path round the loop that some iteration can skip.
     *
     * This is necessary but nowhere near sufficient. An inner loop's "int j =
     * 0" passes it -- its block does dominate the enclosing loop's latch -- and
     * const_folding() has by then reduced it to a constant load with no
     * operands, so nothing here marks it as varying either. What keeps it in
     * place is the stamping in licm_mark_invariant(): the inner test and
     * increment read j back and are not themselves invariant, so
     * licm_read_by_stayer() finds a reader that stays.
     */
    if (bb != latch && !is_dominate(bb, latch))
        return false;
    if (!insn_is_speculatable(insn))
        return false;
    if (insn->rd->is_global || insn->rd->address_taken)
        return false;
    /* Written elsewhere too: the name does not identify this value. */
    if (insn->rd->def_cnt != 1)
        return false;

    /* rs3 belongs to a select, which if_convert() introduces; it is not
     * speculatable above, but check it rather than rely on that ordering.
     */
    if (insn->rs3)
        return false;

    return licm_operand_fixed(func, insn->rs1) &&
           licm_operand_fixed(func, insn->rs2);
}

/* Stamp the destination of every instruction the loop could move.
 *
 * The set is a fixed point rather than one sweep: an instruction becomes
 * invariant once the operands keeping it back are known to be, so marking one
 * can admit another. Marking is what lets licm_read_by_stayer() tell a reader
 * that travels with an instruction from one that pins it, so it has to be
 * complete before any instruction is examined for the move.
 */
void licm_mark_invariant(func_t *func, basic_block_t *latch)
{
    for (basic_block_t *bb = func->bbs; bb; bb = bb->rpo_next) {
        if (bb->loop_mark != licm_gen)
            continue;
        for (insn_t *insn = bb->insn_list.head; insn; insn = insn->next) {
            if (insn->rd)
                insn->rd->loop_stamp = 0;
        }
    }

    bool changed = true;

    while (changed) {
        changed = false;
        for (basic_block_t *bb = func->bbs; bb; bb = bb->rpo_next) {
            if (bb->loop_mark != licm_gen)
                continue;
            for (insn_t *insn = bb->insn_list.head; insn; insn = insn->next) {
                if (!insn->rd || insn->rd->loop_stamp == licm_gen)
                    continue;
                if (!licm_is_invariant(func, insn, bb, latch))
                    continue;
                insn->rd->loop_stamp = licm_gen;
                changed = true;
            }
        }
    }
}

/* Whether @insn can be moved to the preheader: invariant, and read inside the
 * loop only by instructions that are moving with it.
 */
bool licm_can_hoist(func_t *func,
                    insn_t *insn,
                    basic_block_t *bb,
                    basic_block_t *latch)
{
    if (!insn->rd || insn->rd->loop_stamp != licm_gen)
        return false;
    if (!licm_is_invariant(func, insn, bb, latch))
        return false;
    return !licm_read_by_stayer(func, insn);
}

/* Move every hoistable instruction of the loop headed by @header into @pre.
 *
 * Returns the number moved. Instructions are appended to the preheader in the
 * order they are met, which is the order they appeared in the loop, so an
 * operand still precedes the instruction that reads it. A hoist can make
 * another instruction hoistable -- its blocking operand has just left the loop
 * -- so the caller repeats until this returns zero.
 */
int licm_hoist_once(func_t *func, basic_block_t *pre, basic_block_t *latch)
{
    int moved = 0;

    for (basic_block_t *bb = func->bbs; bb; bb = bb->rpo_next) {
        if (bb->loop_mark != licm_gen)
            continue;

        insn_t *next;
        for (insn_t *insn = bb->insn_list.head; insn; insn = next) {
            next = insn->next;

            if (!licm_can_hoist(func, insn, bb, latch))
                continue;

            bb_remove_insn(bb, insn);

            /* Before the block's terminator rather than after it: the preheader
             * ends in the branch or jump that enters the loop, and an
             * instruction placed after that is unreachable.
             */
            insn_t *tail = pre->insn_list.tail;

            if (tail && (tail->opcode == OP_branch || tail->opcode == OP_jump))
                bb_insert_after(pre, tail->prev, insn);
            else
                bb_append_insn(pre, insn);
            moved++;
        }
    }
    return moved;
}

/* Run LICM on the loop that the edge from @latch back to @header closes. */
void licm_loop(func_t *func, basic_block_t *header, basic_block_t *latch)
{
    /* mark_natural_loop() advances loop_scan_gen and stamps the loop's blocks
     * with it; sr_preheader() reads the same stamp through sr_gen, so the two
     * have to agree on which generation is current.
     */
    sr_gen = loop_scan_gen + 1;
    if (!mark_natural_loop(header, latch))
        return; /* the walk ran out of room, so loop_mark says nothing */
    licm_gen = sr_gen;

    /* One way in, running everything before the loop and nothing else, is where
     * a hoisted value has to land. Without it there is no block that runs
     * exactly once before the header.
     */
    basic_block_t *pre = sr_preheader(header);

    if (!pre)
        return;

    licm_mark_invariant(func, latch);

    while (licm_hoist_once(func, pre, latch))
        ;
}

void licm(void)
{
    for (func_t *func = FUNC_LIST.head; func; func = func->next) {
        if (!func->bbs)
            continue;

        licm_def_counts(func);

        /* A loop is closed by an edge to a block that dominates its source, the
         * same test strength_reduce() makes. Position along rpo_next cannot
         * stand in for it: passes that splice blocks out of the chain leave an
         * if's arms after the block they rejoin.
         */
        for (basic_block_t *latch = func->bbs; latch; latch = latch->rpo_next) {
            basic_block_t *succ[3];

            succ[0] = latch->next;
            succ[1] = latch->then_;
            succ[2] = latch->else_;

            for (int k = 0; k < 3; k++) {
                if (!succ[k] || succ[k] == latch)
                    continue;
                if (!is_dominate(succ[k], latch))
                    continue;
                licm_loop(func, succ[k], latch);
            }
        }
    }
}
