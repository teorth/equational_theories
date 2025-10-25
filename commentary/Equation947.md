This law implies that right multiplications square to constant maps (namely `(y◇x)◇x` is `y`-independent, equal to the right cube `(x◇x)◇x`), and that left multiplications square to the left cubing map `x ↦ x◇(x◇x)` (and in particular are bijective).

The free magma with one generator for this law is isomorphic to `ℤ/3ℤ` equipped with `x◇y = y+1`.  In particular, in any magma the squaring map `S: x ↦ x◇x` and cubing maps `B: x ↦ x◇(x◇x)` and `C: x ↦ (x◇x)◇x` are bijections of order 3 with `S(x) = C(x)` and `B(x) = S(S(x))` and `S(S(S(x))) = x`.

This law is equivalent to [law 723](https://teorth.github.io/equational_theories/implications/?723) `x=y◇(y◇((z◇x)◇x))` together with [law 3897](https://teorth.github.io/equational_theories/implications/?3897) `x◇x = (y◇(z◇x))◇x`.

The left division operation defined by `x ◇ (x : y) = y` satisfies law 42146, `y : (x : (y : (z : x))) = z : x`.

This law cannot hold in a (non-trivial) commutative magma or quasigroup.
