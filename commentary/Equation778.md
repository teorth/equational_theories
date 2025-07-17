This law implies that all left multiplications are bijective.  The cubing maps `B: x ↦ x◇(x◇x)` and `C: x ↦ (x◇x)◇x` are bijections that are inverses of each other and cube to the identity (namely `x = B(B(B(x))) = C(C(C(x))) = B(C(x)) = C(B(x))`) and the squaring map `S: x ↦ x◇x` obeys `S(S(S(S(x))))=S(x)`.

The set of squares forms a submagma on which the operation obeys [law 39](https://teorth.github.io/equational_theories/implications/?39), namely it is right projection composed with squaring.

The left division operation defined by `x ◇ (x : y) = y` obeys the same law, `x = y : (z : ((z : y) : x))`.

Quasigroups satisfying this law are linear models on a Boolean group (abelian group of exponent 2), of the form `x◇y = x + y + c` or `x◇y = x + ω(y-x)` for `ω` an endomorphism satisfying `ω²+ω+id=0`.

This law is implied by the very similar and much stronger [law 765](https://teorth.github.io/equational_theories/implications/?765), `x = y ◇ (z ◇ ((y ◇ z) ◇ x))`.
