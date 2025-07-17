## The law for pointed set fibrations over Boolean semi-symmetric quasigroups

This law is equivalent to the self-dual [law 3776](https://teorth.github.io/equational_theories/implications/?3776) `x ◇ y = (y ◇ z) ◇ (z ◇ x)`.

The submagma `P = {x ◇ y | x, y ∈ M}` is (isomorphic to) a Boolean group (abelian group of exponent 2) equipped with a group automorphism `a:P→P` of order 3, with the magma operation being `p◇q = a p + a² q` for `p,q∈P`.  It obeys the [semi-symmetric quasigroup law 14](https://teorth.github.io/equational_theories/implications/?14).  For any given element `0∈M`, the map `φ: x ↦ 0◇(x◇0) = (0◇x)◇0` is a magma morphism from `M` to `P` that leaves `P` invariant.  In particular, `x◇y = φ(x)◇φ(y)` so the magma operation on `M` consists of projecting to `P` followed by the linear operation on `P`.  Thus, magmas satisfying this law are always submagmas of linear magmas satisfying this law.

This law is implied by the [law 3385](https://teorth.github.io/equational_theories/implications/?3385) describing fibrations over Boolean groups.  This corresponds to the case where the automorphism `a:P→P` is the identity.
