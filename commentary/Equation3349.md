## A law for sets equipped with a self-map obeying `f ∘ f ∘ f = f`

This law is equivalent to stating that the magma operation is right-projection composed with squaring (namely `x◇y=y◇y`, a form of [law 39](https://teorth.github.io/equational_theories/implications/?39)) and that the squaring map `f: M→M` obeys `f ∘ f ∘ f = f` (namely `f(x) = f(f(f(x)))`, law 206733947).  The second condition can be replaced by the shorter [law 3253](https://teorth.github.io/equational_theories/implications/?3253) `x◇x=x◇(x◇(x◇x))`.

Such magmas are in one-to-one correspondence with sets equipped with a self-map that cubes to itself.

The free magma on some set `S` of generators for this law is `{0,1,2}×S` with `f(0,s)=(1,s)`, `f(1,s)=(2,s)` and `f(2,s)=(1,s)`.