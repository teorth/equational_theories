## A law for which greedy completion barely works

This is one of the laws where greedy completion has been shown (via extensive SAT-solver calculations) to work, but only barely.  As such, the proof of anti-implications from these laws could be extremely lengthy, to the extent that Lean may struggle to verify them.  See [this discussion](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/1076.20!.3D.3E.203/near/476933251).

The dual law 2338 implies that left multiplications are injective and right multiplications are surjective.  Law 2338 together with either finiteness, or surjectivity of left multiplications, or injectivity of right multiplications, implies that the magma satisfies [law 714](https://teorth.github.io/equational_theories/implications/?714) hence is a quasigroup.

For finite magmas, or for quasigroups, laws [511](https://teorth.github.io/equational_theories/implications/?511), 714, and 2338 are equivalent.  Without such assumptions, law 714 implies law 511 and 2338, but no other implication holds.
