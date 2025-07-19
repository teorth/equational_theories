This law is equivalent to the [associative law 4512](https://teorth.github.io/equational_theories/implications/?4512) together with [law 4361](https://teorth.github.io/equational_theories/implications/?4361) `x◇(y◇z) = x◇(w◇u)`.  In terms of the submagma `P = {x◇y|x,y∈M}`, the latter law states that `x◇p=f(x)` for some map `f:M→P`.

This law implies that the set of squares and the set of cubes are submagmas.  The squaring map `S: x ↦ x◇x` obeys `S(S(S(x))) = S(S(x))`.  Any idempotent element (such as `S(S(x))`) is a left zero.  This law cannot hold in a non-trivial quasigroup.

The free magma on some set `Σ` of generators for law 4517 is `Σ×(Σ ⊔ {0,∞})`, with the magma operation `(s,0)◇(t,0)=(s,t)`, `(s,0)◇(t,u)=(s,∞)`, `(s,0)◇(t,∞)=(s,∞)`, `(s,t)◇_=(s,∞)`, `(s,∞)◇_=(s,∞)`.
