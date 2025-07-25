This is a twist of [law 125](https://teorth.github.io/equational_theories/implications/?125) by the squaring map.  This law implies that left multiplications are surjective and squaring is injective.

Finite models of this equation are quasigroups (left multiplications and right multiplications are bijective), and the squaring map `S` is bijective; see [this discussion](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Austin.20pairs/near/484334184).  Other notable identites here include `x ◇ S(x) = x`, `S(x ◇ C(x)) = x`, and `S(C(x)) = C(S(x))`, where `C(x) = (x◇x)◇x` is the right cubing map.  [Equation 1629](https://teorth.github.io/equational_theories/implications/?1629) is then equivalent to the assertion that cubes are idempotent. This impication was [disproven using a magma extension](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Austin.20pairs/near/484951498), as one of the first demonstrations of the "magma cohomology" method.

This law cannot hold in a non-trivial semigroup (associative magma).

Models include the linear translation-invariant model `x ◇ y = x + a(y-x)` where `a(1-a)^2 = 1`, or the linear model `x ◇ y = ϕ x - y` where `ϕ^2 = ϕ + 1`.

The finite spectrum of (cardinalities of finite magmas satisfying) this law is [unknown](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Order.203.20Spectra/with/527073087).
