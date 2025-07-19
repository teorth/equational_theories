## The law for pointed set fibrations over abelian groups

This law is equivalent to the Schweizer identity, law 3810 `x ◇ y = (z ◇ y) ◇ (z ◇ x)`.  Among quasigroups, it is equivalent to Tarski's [law 543](https://teorth.github.io/equational_theories/implications/?543) that characterizes abelian group subtraction.

The submagma `P = {x◇y| x,y∈M}` is an abelian group equipped with subtraction.  In addition, all squares (not just those of elements in `P`) are equal to the identity element `0` of that group, `x◇x=0` for `x∈M`.  The map `x ↦ x ◇ 0` (equivalently left cubing) is a map from `M` to `P` that is the identity on `P`, and one has `x ◇ y = (x ◇ 0) ◇ (y ◇ 0)`.

Altogether the magma is a pointed set fibration over an abelian group, and the operation is projection to the base, composed with the abelian group subtraction.  Magmas satisfying this law are always submagmas of linear magmas satisfying this law.

The free magma on some set `Σ` of generators for this law is `Σ ⊔ ℤ[Σ]` where `ℤ[Σ]` is the free abelian group on `Σ`, with the magma operation `x◇y = π(x) - π(y)` where `π` maps each `s ∈ Σ` to the corresponding basis vector in `ℤ[Σ]`, and is the identity map on `ℤ[Σ]`.
