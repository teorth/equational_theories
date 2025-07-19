This law is equivalent to [law 4577](https://teorth.github.io/equational_theories/implications/?4577).   In terms of the submagma `P = {x ◇ y | x,y∈M}`, law 4577 states that `x ◇ p = p ◇ x = C(x)` for some (cubing) function `C: M → M` for any `x∈M` and `p∈P`.

This law implies that the set of squares and the set of cubes are submagmas.  The squaring map `S: x ↦ x◇x` obeys `S(S(x)) = S(S(y))` and hence `S(S(S(x))) = S(S(x))`.  This law cannot hold in a non-trivial quasigroup.

The free magma on some set `Σ` of generators for this law is `Σ ⊔ (Σ×Σ) ⊔ ({∞}×Σ) ⊔ {∞}` with the operation defined by `s ◇ t = (s,t)` and other `s ◇ _ = (∞,s)` and `_ ◇ t = (∞,t)`, and all other products are `∞`.
