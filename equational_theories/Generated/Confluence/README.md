This directory implements Fan Zheng's idea, from the Equation 477 thread on Zulip. (TBD: write
this up in the blueprint and link there)

The idea is:
1. Chains of equality that use only an equation of the form `x = E` can be written down
    as two different simplifications of the same expression, contracting `E → x` on
    a sequence of points in the expression tree.
2. If the expression `E` cannot be matched to any of its sub-expressions, there is a unique
    fully-simplified form (the order of simplifications doesn't matter).
3. Therefore, if an equation `A = B` follows from such a law `x = E`, then the fully-reduced
    form of `A` and `B` will be equal. For expressions `E` with order 3 or 4 this means only
    trivial substitutions follow.

The script generates `confluent_equations.txt`. It checks condition 2 very naively, luckily
we have relatively few equations to check and computers are fast enough.

The file `ManuallySampled.lean` includes the implications that were unknown at the time and
are covered by these arguments.
