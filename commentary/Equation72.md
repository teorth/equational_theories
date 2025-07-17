This law states that the squaring map `S:x ↦ x◇x` is bijective and that all left multiplications square to its inverse.  It implies that `S` cubes to the identity (`S(S(S(x)))=x`), that the right and left cubing maps `C: x ↦ (x◇x)◇x` and `B: x ↦ x◇(x◇x)` are equal to `S` and its inverse, and that all left multiplications square to `B` (namely `y◇(y◇x) = B(x)`).  This law cannot hold in a non-trivial group.

The free magma with one generator for this law is isomorphic to `ℤ/3ℤ` equipped with `x◇y = y+1`.

The left division operation defined by `x ◇ (x : y) = y` (or equivalently `x : y = x ◇ (y ◇ y)`) satisfies [law 55](https://teorth.github.io/equational_theories/implications/?55), namely `x = x : (y : (y : x))`.  Conversely, in a magma satisfying law 55, if left multiplications are bijective, then left division satisfies law 72.  Thus, laws 72 and 55 are parastrophically equivalent for (left-)quasigroups.
