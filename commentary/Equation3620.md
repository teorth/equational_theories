## The law for pointed set fibrations over Boolean semi-symmetric quasigroups

This law is equivalent to the self-dual [law 3776](https://teorth.github.io/equational_theories/implications/?3776) `x ◇ y = (y ◇ z) ◇ (z ◇ x)`.

Quasigroups satisfying this law could be dubbed Boolean semi-symmetric quasigroups.  They obey the [semi-symmetric quasigroup law 14](https://teorth.github.io/equational_theories/implications/?14), and they are (isomorphic to) a Boolean group (abelian group of exponent 2) equipped with a group automorphism `a:M→M` of order 3, with the magma operation being `x◇y = a x + a² y` for `x,y∈M`.

In a general magma satisfying this law, the submagma `P = {x ◇ y | x, y ∈ M}` is a Boolean semi-symmetric quasigroup in the above sense.  The cubing map `C: x ↦ x◇(x◇x) = (x◇x)◇x` is a magma morphism with image `P` and that reduces to the identity on `P`.  In particular, `x◇y = C(x)◇C(y)` so the magma operation on `M` consists of projecting to `P` followed by the linear operation on `P`.  Thus, magmas satisfying this law are always submagmas of linear magmas satisfying this law.

This law is implied by the [law 3385](https://teorth.github.io/equational_theories/implications/?3385) describing fibrations over Boolean groups.  This corresponds to the case where the automorphism `a:P→P` is the identity.

The set of squares is a submagma of `P`.
