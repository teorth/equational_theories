This law implies the [associative law 4512](https://teorth.github.io/equational_theories/implications/?4512) and the [law 4362](https://teorth.github.io/equational_theories/implications/?4362) `x◇(y◇z) = y◇(x◇z)` dual to the non-associative-permutative law.  The squaring map `S: x ↦ x◇x` is idempotent, namely `S(S(x)) = S(x)`.

Its commutative version is [law 3385](https://teorth.github.io/equational_theories/implications/?3385).

The free magma on some set `S` of generators for this law is `S ⊔ (𝒫(S) × S)` where `𝒫(S)` is the set of finite subsets of `S`, with the magma operation `s◇t=({s},t)`, `(A,s)◇t=(A∆{s},t)`, `s◇(B,t)=({s}∆B,t)`, and `(A,s)◇(B,t)=(A∆{s}∆B,t)` where `∆` is the symmetric difference.  In particular, `s◇s◇t = (∅,t)`.
