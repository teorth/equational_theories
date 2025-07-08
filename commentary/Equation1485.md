## A weak central groupoid law

A challenging equation.  Discussed [here](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/1485).  It is implied by the central groupoid law ([Equation 168](https://teorth.github.io/equational_theories/implications/?168)). It is also equivalent to its dual.

Appears to be resistant to the linear magma method and the "pure" greedy algorithm method, as well as translation-invariant constructions.  However, one can use greedy extensions of "relaxed weak central groupoids" to rule out at least some implications.

Has an intriguing graph-theoretic interpretation in terms of directed graphs with some "good" paths of length two, and an interesting axiom involving 5-cycles in the graph.

The last-standing implications for this equation were resolved with a 32-element magma (that violates equations 151, 3456, 3862) that was later understood using the twisting semigroup method.

The [finite spectrum](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Order.203.20Spectra/with/527073087) of (cardinalities of finite magmas satisfying) this law conjecturally consists of [squares and twice squares](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/1485/near/480045734).

This law implies that the squaring map `S: x ↦ x◇x` obeys `S(S(S(x))) = S(x)`.  This law cannot hold in a non-trivial quasigroup or associative magma.  For commutative magmas, this law [characterizes the Sheffer stroke](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/A.20single.20axiom.20for.20Boolean.20algebra/near/519538543).

See [this chapter of the blueprint](https://teorth.github.io/equational_theories/blueprint/weak-central-groupoids-chapter.html).
