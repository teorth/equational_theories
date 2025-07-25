## A law for which greedy completion barely works

This is one of the laws where greedy completion has been shown (via extensive SAT-solver calculations) to work, but only barely.  As such, the proof of anti-implications from these laws could be extremely lengthy, to the extent that Lean may struggle to verify them.  See [this discussion](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/1076.20!.3D.3E.203/near/476933251).

In a finite magma satisfying this law, the squaring and left cubing maps `S: x ↦ x◇x` and `B: x ↦ x◇(x◇x)` are inverses bijections and `x◇(y◇x)` is `y`-independent.  In general, the squaring map `S` is only surjective and `B` is only injective (and `S(B(x)) = x`).

This law cannot hold in a (non-trivial) commutative magma or quasigroup.
