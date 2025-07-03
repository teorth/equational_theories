## A law for sets equipped with an idempotent self-map

This law is equivalent to stating that the magma operation is right-projection composed with squaring (namely `x◇y=y◇y`, a form of [law 39](https://teorth.github.io/equational_theories/implications/?39)) and that squaring is idempotent (namely `(x◇x)◇(x◇x) = x◇x`, [law 3659](https://teorth.github.io/equational_theories/implications/?3659)).  Such magmas are in one-to-one correspondence with sets equipped with a self-map `f: M→M` with `f ∘ f = f`.  Equivalently they are pointed-set fibrations over a set `im(f)`, with the fiber over `x∈im(f)` being the preimage of `x` under `f`.

The free magma on some set `S` of generators for this law consists of `{0,1}×S` with `f(a,s)=(1,s)`, namely `(_,_) ◇ (_,s) = (1,s)`.

The equivalence class of this law is among the largest ones (37 laws in our list of 4694 laws).
