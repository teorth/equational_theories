This law states that the squaring map `S: x ↦ x◇x` is bijective, that composing it four times gives the identity (`S(S(S(S(x))))=x`), and that all left multiplications cube to the inverse of `S` (and in particular are bijective).  It implies that the cubing maps `B: x ↦ x◇(x◇x)` and `C: x ↦ (x◇x)◇x` are bijective.

The left division operation defined by `x ◇ (x : y) = y` satisfies [law 439](https://teorth.github.io/equational_theories/implications/?439) `x : (y : (y : (y : x))) = x`, and the converse holds in left quasigroups, so these laws are parastrophically equivalent in left quasigroups.  In a quasigroup this law implies the [idempotence law 3](https://teorth.github.io/equational_theories/implications/?3) `x = x◇x`.

This law cannot hold in a non-trivial group.

The proofs of the implications from this law to laws [439](https://teorth.github.io/equational_theories/implications/?439) and [3862](https://teorth.github.io/equational_theories/implications/?3862) involve an [intermediate step of high order](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Which.20implications.20are.20harder.20for.20ATPs/with/547257323), [law 454405904268023386](https://teorth.github.io/equational_theories/implications/?454405904268023386), of order 15, which states that `S(S(S(S(x)))) = x`.
