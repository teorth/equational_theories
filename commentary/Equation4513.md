This law implies the [associative law 4512](https://teorth.github.io/equational_theories/implications/?4512).

For a magma `M` satisfying this law, the submagma `P = {x◇y|x,y∈M}`  [the left unar law 38](https://teorth.github.io/equational_theories/implications/?38), namely its operation is left-projection composed with some function.

This law implies that the set of squares and the set of cubes are submagmas.  The squaring map `S: x ↦ x◇x`  `S(S(S(x))) = S(S(x))`.  Any idempotent element (such as `S(S(x))`) is a left zero.  This law cannot hold in a non-trivial quasigroup.

The free magma on some set `Σ` of generators for this law is `Σ ⊔ Σ×Σ×{0,1}`, with the magma operation `s◇t=(s,t,0)`, `s◇(t,_,_)=(s,t,1)`, `(s,t,_)◇_=(s,t,1)`, `(s,t,_)◇(_,_,_)=(s,t,1)`.
