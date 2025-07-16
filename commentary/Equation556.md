## A law for affine Gaussian modules

A magma satisfying this law is a ℤ[√-1]-module equipped with the operation `x◇y  = (√-1) (x + y) + C` for some constant `C`.  It is in particular a quasigroup (left and right multiplication are bijective) and is commutative.  The ℤ[√-1]-module structure is only fixed up to a choice of zero element.

The left division operation defined by `x ◇ (x : y) = y` satisfies [law 546](https://teorth.github.io/equational_theories/implications/?546).  Conversely, a magma satisfying law 546 is a quasigroup and its left division satisfies law 556, so the two laws are parastrophically equivalent.  They share the same finite spectrum (cardinalities of finite magmas satisfying the law): all [sums of two squares](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Order.203.20Spectra/with/526300502).

Among commutative magmas, this law is equivalent to [law 562](https://teorth.github.io/equational_theories/implications/?562), which states that `L_y ∘ L_z` is involutive for all `y,z`, and to [law 1117](https://teorth.github.io/equational_theories/implications/?1117), which states that `L_y ∘ R_z` is involutive for all `y,z`, where `L_z(x) = z◇x` and `R_z(x) = x◇z`.  Without commutativity the laws 562 and 1117 are weaker and are inequivalent to each other.

The equivalence class of this law is large (12 laws in our list of 4694 laws).
