## A law for sets equipped with a self-map obeying `f ∘ f ∘ f = f`

This law is equivalent to stating that the magma operation is right-projection composed with squaring (namely `x◇y=y◇y`, a form of [law 39](https://teorth.github.io/equational_theories/implications/?39)) and that the squaring map `S: M→M` obeys `S(S(S(S(x)))) = S(x)`.  The second condition can be replaced by the shorter [law 3253](https://teorth.github.io/equational_theories/implications/?3253) `x◇x=x◇(x◇(x◇x))`.

Such magmas are in one-to-one correspondence with sets equipped with a self-map that cubes to itself.  This law cannot hold in a non-trivial quasigroup.  Magmas satisfying this law are always submagmas of linear magmas satisfying this law.

The free magma on some set `S` of generators for this law is `{0,1,2}×S` with `f(0,s)=(1,s)`, `f(1,s)=(2,s)` and `f(2,s)=(1,s)`.

The equivalence class of this law is large (18 laws in our list of 4694 laws).
