## A law for sets equipped with a self-map satisfying `f ∘ f ∘ f = f`

This law is equivalent to stating that the magma operation is right-projection composed with squaring (namely `x◇y=y◇y`, a form of [law 39](https://teorth.github.io/equational_theories/implications/?39)) and that the squaring map `S: x ↦ x◇x` satisfies `S(S(S(S(x)))) = S(x)`.  The second condition can be replaced by the shorter [law 3253](https://teorth.github.io/equational_theories/implications/?3253) `x◇x=x◇(x◇(x◇x))`.

Such magmas are in one-to-one correspondence with sets equipped with a self-map that cubes to itself.  This law cannot hold in a non-trivial quasigroup.  Magmas satisfying this law are always submagmas of linear magmas satisfying this law.

The free magma on some set `Σ` of generators for this law is `{0,1,2}×Σ` with `f(0,s)=(1,s)`, `f(1,s)=(2,s)` and `f(2,s)=(1,s)`.

The equivalence class of this law is large (18 laws in our list of 4694 laws) and includes the two-variable law 3356 `x◇y = y◇(y◇(y◇y))`.  This is quite unusual as there are only four laws (of order at most 4) with fewer variables than their lowest-numbered equivalent: 2494, 3356, 4549, and 4545.
