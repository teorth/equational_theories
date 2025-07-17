## The law for pointed set fibrations over Boolean groups

This law implies the [commutative law 43](https://teorth.github.io/equational_theories/implications/?43) and [associative law 4512](https://teorth.github.io/equational_theories/implications/?4512).

The submagma `P = {x◇y| x,y∈M}` is a Boolean group (abelian group of exponent 2).  In addition, all squares (not just those of elements in `P`) are equal to the identity element `0` of that group, `x◇x=0` for `x∈M`.  The map `x ↦ x ◇ 0` is a map from `M` to `P` that is the identity on `P`, and one has `x ◇ y = (x ◇ 0) ◇ (y ◇ 0)`.

Altogether the magma is a pointed set fibration over a Boolean group, and the operation is projection to the base, composed with the abelian group operation.  Magmas satisfying this law are always submagmas of linear magmas satisfying this law.

The free magma on some set `Σ` of generators for this law is `Σ ⊔ 𝒫(Σ)` where `𝒫(Σ)` is the set of finite subsets of `Σ`, with the magma operation `s◇t={s}∆{t}`, `A◇s = s◇A = A∆{s}`, `A◇B = A∆B` where `∆` is the symmetric difference.  In particular, `s◇(s◇s) = {s} ≠ s`.
