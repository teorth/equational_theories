This law, dubbed [Stein's fourth law](https://arxiv.org/abs/1408.0991) or [transitivity](https://arxiv.org/abs/1601.01922), is a weaker form of [law 3591](https://teorth.github.io/equational_theories/implications/?3591).
It implies the [associative law 4512](https://teorth.github.io/equational_theories/implications/?4512) and a very weak commutativity law 900874, which in the associative case reduces to `x◇y◇z◇w = x◇z◇y◇w`.

The free magma on some set `S` of generators for this law is `S ⊔ (S × 𝒫(S) × S)` where `𝒫(S)` is the set of finite subsets of `S`, with the magma operation `s◇u=(s,∅,u)`, `s◇(u,B,v) = (s,{u}∆B,v)`, `(s,A,t)◇u=(s,A∆{t},u)`, `(s,A,t)◇(u,B,v)=(s,A∆{t}∆{u}∆B,v)` where `∆` is the symmetric difference.
