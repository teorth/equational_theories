This law implies the [associative law 4512](https://teorth.github.io/equational_theories/implications/?4512) and the [law 4362](https://teorth.github.io/equational_theories/implications/?4362) `x◇(y◇z) = y◇(x◇z)` dual to the non-associative-permutative law.  The squaring map `S: x ↦ x◇x` is idempotent, namely `S(S(x)) = S(x)`.

For any given element `0∈M`, left-multiplication by `0` squares to the cubing map `B: x ↦ x◇x◇x`, which is a morphism projecting `M` to the submagma `P={x◇y|x,y∈M}` (namely `B` is the identity map on `P`).  The magma operation on `M` is characterized by that on `P` since `x◇y = B(x)◇B(y)`.  The submagma `P` satisfies [law 765](https://teorth.github.io/equational_theories/implications/?765).  Within this submagma, left multiplications are all involutions hence form a Boolean subgroup of the group of bijections of `P`.  It appears that `P` is always a linear model and thus that magmas satisfying this law can always be embedded in linear magmas satisfying it.

The commutative version of this law is [law 3385](https://teorth.github.io/equational_theories/implications/?3385) describing pointed set fibrations over Boolean groups.

In quasigroups, this law is equivalent to the [Boolean group law 895](https://teorth.github.io/equational_theories/implications/?895).

The free magma on some set `Σ` of generators for this law is `Σ ⊔ (𝒫(Σ) × Σ)` where `𝒫(Σ)` is the set of finite subsets of `Σ`, with the magma operation `s◇t=({s},t)`, `(A,s)◇t=(A∆{s},t)`, `s◇(B,t)=({s}∆B,t)`, and `(A,s)◇(B,t)=(A∆{s}∆B,t)` where `∆` is the symmetric difference.  In particular, `s◇s◇t = (∅,t)`.
