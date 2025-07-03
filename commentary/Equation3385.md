## The law for pointed set fibrations over abelian groups of exponent 2

This law implies the [commutative law 43](https://teorth.github.io/equational_theories/implications/?43) and [associative law 4512](https://teorth.github.io/equational_theories/implications/?4512).

The submagma `P = {x◇y| x,y∈M}` is an abelian group of exponent 2.  In addition, all squares (not just those of elements in `P`) are equal to the identity element `0` of that group, `x◇x=0` for `x∈M`.  The map `x ↦ x ◇ 0` is a map from `M` to `P` that is the identity on `P`, and one has `x ◇ y = (x ◇ 0) ◇ (y ◇ 0)`.

Altogether the magma is a pointed set fibration over an abelian group, and the operation is projection to the base, composed with the abelian group subtraction.

The free magma on some set `S` of generators for this law is `S ⊔ 𝒫(S)` where `𝒫(S)` is the set of finite subsets of `S`, with the magma operation `s◇t={s}∆{t}`, `A◇s = s◇A = A∆{s}`, `A◇B = A∆B` where `∆` is the symmetric difference.  In particular, `s◇(s◇s) = {s} ≠ s`.
