This law implies that left multiplications are bijective.  The product of any two right multiplications is a constant map (namely `(z◇x)◇y = (w◇x)◇y`).

The left division operation defined by `x ◇ (x : y) = y` satisfies [law 653](https://teorth.github.io/equational_theories/implications/?653), `x = x : (y : ((z : y) : x))`.  Conversely if a magma satisfies law 653 and left multiplications are bijective, then left division satisfies law 960.  Thus, the laws 960 and 653 are parastrophically equivalent for (left-)quasigroups.

The free magma with one generator for this law is isomorphic to `ℤ/3ℤ` equipped with `x◇y = y+1`.  In particular, in any magma the squaring map `S: x ↦ x◇x` and cubing maps `B: x ↦ x◇(x◇x)` and `C: x ↦ (x◇x)◇x` are bijections of order 3 with `S(x) = C(x)` and `B(x) = S(S(x))` and `S(S(S(x))) = x`.

This law cannot hold in a (non-trivial) commutative magma or quasigroup.
