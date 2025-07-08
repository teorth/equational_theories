## A law for sets equipped with a bijection of order 3

This law is equivalent to stating that the magma operation is right-projection composed with squaring (namely `x◇y=y◇y`, a form of [law 39](https://teorth.github.io/equational_theories/implications/?39)) and that squaring is a bijection `f: M→M` that cubes to the identity (namely `x = f(f(f(x)))`, law 5476400).  The second condition can be replaced by the shorter [law 47](https://teorth.github.io/equational_theories/implications/?47) `x=x◇(x◇(x◇x))`.

The left division operation defined by `x ◇ (x : y) = y` satisfies the same law, namely `x = y : (x : (x : x))`.

This law cannot hold in any (non-trivial) commutative magma or quasigroup.  This law together with associativity is equivalent to the right-projection [law 5](https://teorth.github.io/equational_theories/implications/?5).  Magmas satisfying this law are always submagmas of linear magmas satifying this law.

Such magmas are in one-to-one correspondence with sets equipped with a bijection that cubes to the identity.

The free magma on some set `S` of generators for this law consists of three copies of `S` permuted cyclically by the bijection.

The equivalence class of this law is among the largest ones (76 laws in our list of 4694 laws).
