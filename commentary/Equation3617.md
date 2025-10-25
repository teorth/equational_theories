## A law whose quasigroups are abelian groups

This law implies that the submagma `P = {x ◇ y | x, y ∈ M}` is a left quasigroup (left multiplications are bijective) and moreover for any `x∈M` left multiplication by `x` is a bijection of `P`.  All squares are left units in `P` and they form a submagma.  In particular the squaring map `S: x ↦ x ◇ x` is idempotent, namely `S(S(x)) = S(x)`.

The right cosets `M◇z = {x◇z|x∈M}` are pairwise equal or disjoint hence partition the magma.  For each `z`, the map `x ↦ (x◇z)◇z` is a magma morphism that projects `M` to `M◇z` (and is the identity on `M◇z`).  It is a magma isomorphism from any given coset `M◇y` to `M◇z`.  Each coset is an abelian group equipped with the operation `s◇t = -s+t` for `s,t` in that coset.

Magmas satisfying this law satisfy a very weak associativity property, law 931351, `x ◇ ((y ◇ z) ◇ w) = ((x ◇ y) ◇ z) ◇ w`, whose free magma can be described in terms of lists of lists of generators.

Quasigroups satisfying this law are abelian groups equipped with the operation `x◇y = -x+y`.  In fact it is enough to assume either injectivity or surjectivity of right multiplications.
