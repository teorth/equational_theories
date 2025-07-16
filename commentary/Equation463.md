## A law for sets equipped with a bijection of order 4

This law is equivalent to stating that the magma operation is right-projection composed with squaring (namely `x◇y=y◇y`, a form of [law 39](https://teorth.github.io/equational_theories/implications/?39)) and that squaring is a bijection `f: M→M` whose fourth iterate is the identity (namely `x=f(f(f(f(x))))`, law 454405904268023386).  The second condition can be replaced by the shorter [law 411](https://teorth.github.io/equational_theories/implications/?411) `x=x◇(x◇(x◇(x◇x)))`.

The left division operation defined by `x ◇ (x : y) = y` satisfies the same law, namely `x = y : (x : (x : (x : x)))`.  This law cannot hold in a (non-trivial) commutative magma or (quasi)group.  Magmas satisfying this law are always submagmas of linear magmas satisfying this law.

Such magmas are in one-to-one correspondence with sets equipped with a self-map `f: M→M` with `f ∘ f ∘ f ∘ f = id`.  The free magma on some set `S` of generators for this law consists of four copies of `S` permuted cyclically by the bijection.

The equivalence class of this law is large (27 laws in our list of 4694 laws).
