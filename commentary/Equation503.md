## A mysterious "twinned" equation.

This law implies that left multiplications are surjective.  Finite magmas are thus left quasigroups (namely left multiplications are bijective).

In left quasigroups, this law is parastrophically equivalent to [law 476](https://teorth.github.io/equational_theories/implications/?476) in the sense that the left division operation defined by `x◇(x:y) = y` satisfies law 476 if and only if `◇` satisfies law 503, as observed in [this discussion thread](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Austin.20pairs/near/483169215).  In a quasigroup this law implies the [idempotence law 3](https://teorth.github.io/equational_theories/implications/?3) `x = x◇x`.

In addition, this equation is "twinned" with the same [law 503](https://teorth.github.io/equational_theories/implications/?503), in that it [seems to](https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/Numerical.20coincidence.3A.20476.20~.20503) imply, and be implied by, exactly the same set of equations, without being equivalent.  This is only partially explained by parastrophic equivalence.  See [this further discussion](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Twin.20pairs.20of.20equations).

The fact that this law does not imply [law 4065](https://teorth.github.io/equational_theories/implications/?4065) nor [law 3862](https://teorth.github.io/equational_theories/implications/?3862) even for finite models was resolved using a [36-element left quasigroup](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Austin.20pairs/near/485535822) obtained by [a cohomological construction](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Austin.20pairs/near/485526061).

This law cannot hold in a non-trivial group.
