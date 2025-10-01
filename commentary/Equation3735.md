This law is equivalent to law 3738, `x◇y = (x◇z) ◇ (y◇w)` which states that the magma operation is constant on right cosets.  It is equivalent to [law 385](https://teorth.github.io/equational_theories/implications/?385) `x◇y = (x◇z)◇y` together with the [reduction law 327](https://teorth.github.io/equational_theories/implications/?327) `x◇y = x◇(y◇z)` or its specialization to `z=x` ([law 325](https://teorth.github.io/equational_theories/implications/?325)).  This law implies that the squaring map `S: x ↦ x◇x` is idempotent, namely `S(S(x))=S(x)`.

The free magma on some set `Σ` of generators for this law is `Σ × ({0} ⊔ Σ)` with the operation `(s,_)◇(t,_)=(s,t)`.

This law cannot hold in a non-trivial quasigroup.
