A challenging equation, discussed [here](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/1516.20-.3E.20255) and in [this chapter of the blueprint](https://teorth.github.io/equational_theories/blueprint/1516-chapter.html).  This law implies [law 255](https://teorth.github.io/equational_theories/implications/?255) in linear models, translation-invariant models, and finite magmas, but can be refuted by a complicated greedy construction.

The fact that it does not imply [law 1489](https://teorth.github.io/equational_theories/implications/?1489) even for finite models was resolved using the [cohomological method](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Austin.20pairs/near/485020624).

This law cannot hold in a non-trivial semigroup (associative magma).

This law is a twist of the [Dupont law 63](https://teorth.github.io/equational_theories/implications/?63) by the squaring map.  The finite spectrum of (cardinalities of finite magmas satisfying) this law is [unknown](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Order.203.20Spectra/with/527073087).

In quasigroups, this law implies that the squaring map `S: x ↦ x◇x` is bijective (with inverse `x ↦ (x◇(x◇x)) ◇ ((x◇(x◇x))◇x)`).
