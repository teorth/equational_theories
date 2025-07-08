## A "liquid" law

Most laws tend to feel either "solid", in that their models have a lot of algebraic structure (or are forced to be almost trivial), or "gaseous", in that there is extensive freedom in their models, and little structure. This law is at an unusual intermediate state, that one might call "liquid". One the one hand, it implies many other laws and its models have intriguing structure, including an associated directed graph and pre-order.

Simple examples of such laws include left-absorptive magmas (with `x ◇ y = x`), as well as the cyclic group `ℤ/3ℤ` with `x ◇ y = x` for `y ≠ x` and `x ◇ x = x - 1`.  There are also many sporadic solutions, including a specific [example of order 12](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Outstanding.20equations.2C.20v1/near/478094170) that was discovered through an ATP and could also refute implications. Furthermore, given a finite magma solving this law, it is often possible to modify a few entries of the multiplication table, or extend it by adding (or removing) some elements, in sharp contrast to say the situation with finite groups, creating quite a large class of additional examples of this law.

This law cannot hold in a (non-trivial) commutative magma or quasigroup.

Its free magma is conjecturally understood and, while difficult to describe, does obey some interesting laws, such as a unique factorization property that can be used to refute some implications.  A greedy algorithm that incorporates this unique factorization law and some other axioms was used to resolve all remaining implications.

See [this chapter of the blueprint](https://teorth.github.io/equational_theories/blueprint/854-chapter.html).