## A law whose quasigroups are affine ℤ[T,T⁻¹] modules

This law states that `L(y) ∘ R(z)` is involutive for all `y,z`, where `L(z): x ↦ z◇x` and `R(z): x ↦ x◇z` are left/right multiplications.

This law implies that left multiplications are surjective and right multiplications are injective.  In finite magmas, or in quasigroups, it is equivalent to its dual, [law 2538](https://teorth.github.io/equational_theories/implications/?2538).  Magmas satisfying this law and its dual are quasigroup and are linear, (non-uniquely) isomorphic to a ℤ[T,T⁻¹]-module with the operation `x◇y = Tx - T⁻¹y + c` for some constant `c`.  The ℤ[T,T⁻¹]-module structure is only defined up to a choice of zero element.

Commutative magmas satisfying this law are the same as magmas satisfying [law 556](https://teorth.github.io/equational_theories/implications/?556), related to affine ℤ[√-1]-modules.

Quasigroups satisfying this law together with idempotence are dubbed [golden section quasigroups](https://arxiv.org/abs/1907.06635) and are affine ℤ[φ]-modules for φ the golden ratio.

This equation admits a simple but non-trivial model on the integers `a ◇ b = 2 * a - b / 2` (with division rounded down) which can be [used to disprove an implication](https://github.com/teorth/equational_theories/pull/695).  Was [first discovered](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Outstanding.20equations.2C.20v1/near/477929143) by exploring noncommutative linear models.
