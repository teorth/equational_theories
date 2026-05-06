While this law implies very few other laws, it has a surprisingly large (but finite) [number of "local" consequences](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/1076.20!.3D.3E.203/near/477475464).  This makes it possible, but extremely tedious, to construct infinite models for this law by a greedy argument - currently the proofs here require a significant SAT-solver calculation!

Law 511 implies that left multiplications are surjective and right multiplications are injective.  Law 511 together with either finiteness, or injectivity of left multiplications, or surjectivity of right multiplications, implies that the magma satisfies [law 714](https://teorth.github.io/equational_theories/implications/?714) hence is a quasigroup.

For finite magmas, or for quasigroups, laws 511, 714, and [2338](https://teorth.github.io/equational_theories/implications/?2338) are equivalent.  Without such assumptions, law 714 implies law 511 and 2338, but no other implication holds.

See also [Equation 118](https://teorth.github.io/equational_theories/implications/?118) for a law with similar behavior.

