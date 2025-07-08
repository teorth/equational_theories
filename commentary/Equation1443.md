## A law with many finite implications

This law has an unusually large number of independent implications that hold for finite magmas but not infinite magmas.

For each `y` the map `f: x ↦ x◇(x◇y)` is injective and `S(f(x)) = x` for `S: x ↦ x◇x` the squaring map (which is surjective).  In a finite magma the structure simplifies: `x◇(x◇y)` is `y`-independent and equal to the cube `C(x) = x◇(x◇x)`.  The squaring and cubing maps `S` and `C` are inverse bijections.  Under these conditions the law reduces to [law 1441](https://teorth.github.io/equational_theories/implications/?1441) `x = (x◇y)◇C(x)`, which can be recast (using `C(S(x))=x`) as [law 4067](https://teorth.github.io/equational_theories/implications/?4067) `S(x) = (S(x)◇y)◇x`.  On the other hand, `S(x)◇(S(x)◇y) = C(S(x)) = x` ([law 1630](https://teorth.github.io/equational_theories/implications/?1630)) holds, hence [law 23](https://teorth.github.io/equational_theories/implications/?23) `S(x)◇x = x` as well.  Combining laws 23 and 4067 yields [law 3055](https://teorth.github.io/equational_theories/implications/?3055) `x = ((S(x)◇y)◇x)◇x`.

This law cannot hold in a (non-trivial) commutative magma or quasigroup.
