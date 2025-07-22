While this law implies very few other laws, it has a surprisingly large (but finite) [number of "local" consequences](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/1076.20!.3D.3E.203/near/477038694).  This makes it possible, but extremely tedious, to construct infinite models for this law by a greedy argument - currently the proofs here require a significant SAT-solver calculation!

The dual law 229 implies that left multiplications are injective and right multiplications are surjective.  Law 229 together with either finiteness, or surjectivity of left multiplications, or injectivity of right multiplications, implies that the magma satisfies [law 125](https://teorth.github.io/equational_theories/implications/?125) hence is a quasigroup.

For finite magmas, or for quasigroups, laws [73](https://teorth.github.io/equational_theories/implications/?73), 125, and 229 are equivalent.  Without such assumptions, law 125 implies law 73 and 229, but no other implication holds.

See also [Equation 511](https://teorth.github.io/equational_theories/implications/?511) for a law with similar behavior.
