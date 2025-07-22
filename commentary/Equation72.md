This law states that the squaring map `S:x ↦ x◇x` is bijective and that all left multiplications square to its inverse.

The free magma with one generator for this law is isomorphic to `ℤ/3ℤ` equipped with `x◇y = y+1`.  In particular, in any magma the squaring map `S: x ↦ x◇x` and cubing maps `B: x ↦ x◇(x◇x)` and `C: x ↦ (x◇x)◇x` are bijections of order 3 with `S(x) = C(x)` and `B(x) = S(S(x))` and `S(S(S(x))) = x`.

The left division operation defined by `x ◇ (x : y) = y` (or equivalently `x : y = x ◇ (y ◇ y)`) satisfies [law 55](https://teorth.github.io/equational_theories/implications/?55), namely `x = x : (y : (y : x))`.  Conversely, in a magma satisfying law 55, if left multiplications are bijective, then left division satisfies law 72.  Thus, laws 72 and 55 are parastrophically equivalent for (left-)quasigroups.
