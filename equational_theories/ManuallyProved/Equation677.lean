import equational_theories.Equations.All
import Mathlib.Data.Fintype.Card

/-!
# Equation 677: Blueprint Lemmas

Formalizes lemmas from Chapter 13 of the ETP blueprint for the open
implication Equation 677 → Equation 255 on finite magmas.

* Lemma 13.1(i): Left multiplication is bijective (`eq677_leftMul_surj`, `eq677_leftMul_inj`)
* Lemma 13.1(ii): Fixer uniqueness (`eq677_fixer_unique`)
* Lemma 13.1(iii): Backward recurrence (`eq677_backward_recurrence`)
* Lemma 13.2(ii↔iii): Fixer existence ↔ E255 (`eq255_from_fixer_exists`)
* Lemma 13.2(iv): `R_x ∘ L_x` fixed-point form (`eq255_equiv_RxLx`)
* Lemma 13.2(v): `L_x ∘ R_x` fixed-point form (`eq255_equiv_LxRx`)
* Key identity (`eq677_key_identity`)
* Star equation (`eq677_star_eq`)
-/

namespace Eq677

variable {G : Type*} [Magma G]

/-- Left multiplication is surjective, with preimage `L_y⁻¹(x) = x ◇ ((y ◇ x) ◇ y)`.
Blueprint Lemma 13.1(i). -/
theorem eq677_leftMul_surj (h : Equation677 G) (y : G) :
    Function.Surjective (fun x => y ◇ x) :=
  fun x => ⟨x ◇ ((y ◇ x) ◇ y), (h x y).symm⟩

/-- The left-inverse formula: `y ◇ (x ◇ ((y ◇ x) ◇ y)) = x`.
Direct restatement of Equation 677. Blueprint Lemma 13.1(i). -/
theorem eq677_leftInv_formula (h : Equation677 G) (x y : G) :
    y ◇ (x ◇ ((y ◇ x) ◇ y)) = x :=
  (h x y).symm

/-- Blueprint Lemma 13.2(iv): E255 at x ↔ ∃ z, (x ◇ z) ◇ x = x. No finiteness needed. -/
theorem eq255_equiv_RxLx (h : Equation677 G) (x : G) :
    (∃ z, (x ◇ z) ◇ x = x) ↔ (∃ y, y ◇ x = x) := by
  constructor
  · rintro ⟨z, hz⟩; exact ⟨x ◇ z, hz⟩
  · rintro ⟨y, hy⟩
    exact ⟨y ◇ ((x ◇ y) ◇ x), by rw [eq677_leftInv_formula h y x]; exact hy⟩

variable [Finite G]

/-- Left multiplication is injective on finite magmas. Blueprint Lemma 13.1(i). -/
theorem eq677_leftMul_inj (h : Equation677 G) (y : G) :
    Function.Injective (fun x => y ◇ x) :=
  (Finite.injective_iff_surjective).mpr (eq677_leftMul_surj h y)

/-- Left cancellation: `y ◇ a = y ◇ b → a = b`. -/
theorem eq677_left_cancel (h : Equation677 G) (y : G) {a b : G}
    (hab : y ◇ a = y ◇ b) : a = b :=
  eq677_leftMul_inj h y hab

/-- Blueprint Lemma 13.1(iii). Backward recurrence: `x = (y ◇ x) ◇ ((y ◇ (y ◇ x)) ◇ y)`.
Apply E677 at `(y ◇ x, y)` and left-cancel `y`. -/
theorem eq677_backward_recurrence (h : Equation677 G) (x y : G) :
    x = (y ◇ x) ◇ ((y ◇ (y ◇ x)) ◇ y) :=
  eq677_left_cancel h y (h (y ◇ x) y)

/-- Blueprint Lemma 13.1(ii). Fixer uniqueness: if `y ◇ x = x` then `y = (x ◇ x) ◇ x`. -/
theorem eq677_fixer_unique (h : Equation677 G) {x y : G}
    (hfix : y ◇ x = x) : y = (x ◇ x) ◇ x := by
  have hinv : y ◇ (x ◇ (x ◇ y)) = x := by
    have := eq677_leftInv_formula h x y; rwa [hfix] at this
  have hxy : x = x ◇ (x ◇ y) := eq677_left_cancel h y (by rw [hfix, hinv])
  exact eq677_left_cancel h x (eq677_left_cancel h x (hxy.symm.trans (h x x)))

/-- Blueprint Lemma 13.2(ii↔iii). E255 holds at `x` iff `x` has a fixer. -/
theorem eq255_from_fixer_exists (h : Equation677 G) (x : G)
    (hfix : ∃ y : G, y ◇ x = x) : x = ((x ◇ x) ◇ x) ◇ x := by
  obtain ⟨y, hy⟩ := hfix
  rw [← eq677_fixer_unique h hy]; exact hy.symm

/-- Blueprint Lemma 13.2(v). E255 at x ↔ `L_x ∘ R_x` has a fixed point. -/
theorem eq255_equiv_LxRx (h : Equation677 G) (x : G) :
    (∃ z, x ◇ (z ◇ x) = z) ↔ (∃ y, y ◇ x = x) := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨x ◇ z, eq677_left_cancel h z
      (eq677_left_cancel h x ((eq677_leftInv_formula h z x).trans hz.symm))⟩
  · rintro ⟨y, hy⟩
    refine ⟨y ◇ ((x ◇ y) ◇ x), ?_⟩
    have h1 : x ◇ (y ◇ ((x ◇ y) ◇ x)) = y := eq677_leftInv_formula h y x
    have h2 := eq677_leftInv_formula h (y ◇ ((x ◇ y) ◇ x)) x
    rwa [h1, hy] at h2

/-- Key identity: `(y ◇ (y ◇ x)) ◇ y = x ◇ (((y ◇ x) ◇ x) ◇ (y ◇ x))`.
Compare backward recurrence at `(x, y)` with E677 at `(x, y ◇ x)`, then left-cancel. -/
theorem eq677_key_identity (h : Equation677 G) (x y : G) :
    (y ◇ (y ◇ x)) ◇ y = x ◇ (((y ◇ x) ◇ x) ◇ (y ◇ x)) :=
  eq677_left_cancel h (y ◇ x)
    ((eq677_backward_recurrence h x y).symm.trans (h x (y ◇ x)))

/-- Star equation: if `a ◇ x = b ◇ x` then `(a ◇ (a ◇ x)) ◇ a = (b ◇ (b ◇ x)) ◇ b`.
Right-cancellation failure propagates: any manipulation of E677 assuming `a ◇ x = b ◇ x`
reduces to right cancellation at a different level. -/
theorem eq677_star_eq (h : Equation677 G) (x : G) {a b : G}
    (heq : a ◇ x = b ◇ x) :
    (a ◇ (a ◇ x)) ◇ a = (b ◇ (b ◇ x)) ◇ b := by
  rw [heq]
  have h1 := eq677_backward_recurrence h x a
  have h2 := eq677_backward_recurrence h x b
  rw [heq] at h1
  exact eq677_left_cancel h (b ◇ x) (h1.symm.trans h2)

end Eq677
