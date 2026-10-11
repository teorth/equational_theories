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

/-! ### Conjugacy-closed left translations -/

/-- The left translation by `a`, packaged as an equivalence in a finite
Equation-677 magma. -/
noncomputable def eq677_leftMulEquiv (h : Equation677 G) (a : G) : G ≃ G :=
  Equiv.ofBijective (fun z => a ◇ z)
    ⟨eq677_leftMul_inj h a, eq677_leftMul_surj h a⟩

/-- Division by `a`, defined as the inverse of its left translation. -/
noncomputable def eq677_div (h : Equation677 G) (a b : G) : G :=
  (eq677_leftMulEquiv h a).symm b

lemma eq677_div_left (h : Equation677 G) (a b : G) :
    a ◇ eq677_div h a b = b :=
  (eq677_leftMulEquiv h a).apply_symm_apply b

lemma eq677_div_right (h : Equation677 G) (a b : G) :
    eq677_div h a (a ◇ b) = b :=
  (eq677_leftMulEquiv h a).symm_apply_apply b

private lemma eq677_div_master_one (h : Equation677 G) (x y : G) :
    x ◇ ((y ◇ x) ◇ y) = eq677_div h y x := by
  apply (eq677_leftMulEquiv h y).injective
  change y ◇ (x ◇ ((y ◇ x) ◇ y)) = y ◇ eq677_div h y x
  rw [eq677_div_left]
  exact (h x y).symm

private lemma eq677_div_master_two (h : Equation677 G) (x y : G) :
    (y ◇ x) ◇ y = eq677_div h x (eq677_div h y x) := by
  have h' := congrArg (eq677_leftMulEquiv h x).symm
    (eq677_div_master_one h x y)
  change (eq677_leftMulEquiv h x).symm
      ((eq677_leftMulEquiv h x) ((y ◇ x) ◇ y)) =
    (eq677_leftMulEquiv h x).symm (eq677_div h y x) at h'
  rw [(eq677_leftMulEquiv h x).symm_apply_apply] at h'
  exact h'

private lemma eq677_conjugacy_eval (h : Equation677 G)
    (hconj : ∀ a b, ∃ c, ∀ z,
      c ◇ z = a ◇ (b ◇ ((eq677_leftMulEquiv h a).symm z)))
    (a b z : G) :
    a ◇ z = eq677_div h (Classical.choose (hconj a b))
      (a ◇ (b ◇ z)) := by
  let c := Classical.choose (hconj a b)
  have hc := Classical.choose_spec (hconj a b)
  have hc' : c ◇ (a ◇ z) = a ◇ (b ◇ z) := by
    simpa [c] using hc (eq677_leftMulEquiv h a z)
  change a ◇ z = eq677_div h c (a ◇ (b ◇ z))
  calc
    a ◇ z = eq677_div h c (c ◇ (a ◇ z)) := by
      symm
      exact eq677_div_right h c (a ◇ z)
    _ = eq677_div h c (a ◇ (b ◇ z)) := by rw [hc']

private lemma eq677_inverse_conjugacy (h : Equation677 G)
    (hconj : ∀ a b, ∃ c, ∀ z,
      c ◇ z = a ◇ (b ◇ ((eq677_leftMulEquiv h a).symm z)))
    (x z y : G) :
    eq677_div h z (eq677_div h x y) =
      eq677_div h x (eq677_div h (Classical.choose (hconj x z)) y) := by
  let c := Classical.choose (hconj x z)
  have hc := Classical.choose_spec (hconj x z)
  have hc' : c ◇ (eq677_div h c y) =
      x ◇ (z ◇ (eq677_div h x (eq677_div h c y))) := by
    simpa [c] using hc (eq677_div h c y)
  have h₁ : x ◇ (z ◇ (eq677_div h x (eq677_div h c y))) = y := by
    rw [eq677_div_left] at hc'
    exact hc'.symm
  have h₂ := congrArg (eq677_div h x) h₁
  have h₃ : eq677_div h x y =
      z ◇ (eq677_div h x (eq677_div h c y)) := by
    simpa only [eq677_div_right] using h₂.symm
  have h₄ := congrArg (eq677_div h z) h₃
  simpa only [eq677_div_right] using h₄

/-- Nonempty case of `eq255_of_eq677_leftMul_conjugacy_closed`. -/
private theorem eq255_of_eq677_leftMul_conjugacy_closed_nonempty
    (h : Equation677 G)
    (hconj : ∀ a b, ∃ c, ∀ z,
      c ◇ z = a ◇ (b ◇ ((eq677_leftMulEquiv h a).symm z)))
    [Nonempty G] :
    Equation255 G := by
  classical
  let d := eq677_div h
  let c := fun a b => Classical.choose (hconj a b)
  have hinvconj (x z y : G) :
      d z (d x y) = d x (d (c x z) y) := by
    simpa [d, c] using eq677_inverse_conjugacy h hconj x z y
  have fixed_rule (a z : G) (ha : a ◇ z = z) :
      a = (z ◇ z) ◇ z := by
    have hdaz : d a z = z := by
      simpa [d, ha] using eq677_div_right h a z
    have hzaz : z ◇ a = d z z := by
      simpa [d, ha, hdaz] using eq677_div_master_two h z a
    calc
      a = d z (z ◇ a) := by
        symm
        exact eq677_div_right h z a
      _ = d z (d z z) := by rw [hzaz]
      _ = (z ◇ z) ◇ z := by
        symm
        exact eq677_div_master_two h z z
  have fixed_image (a b z : G) (hb : b ◇ z = z) :
      ∃ c, c ◇ (a ◇ z) = a ◇ z := by
    obtain ⟨c, hc⟩ := hconj a b
    refine ⟨c, ?_⟩
    simpa [hb] using hc (eq677_leftMulEquiv h a z)
  have some_fixed : ∃ a z : G, a ◇ z = z := by
    by_contra hnone
    have hno : ∀ a z : G, a ◇ z ≠ z := by
      simpa only [not_exists] using hnone
    have hdiv (x y : G) : d y x ≠ x ◇ y := by
      intro heq
      have hrow : x ◇ ((y ◇ x) ◇ y) = x ◇ y := by
        calc
          x ◇ ((y ◇ x) ◇ y) = d y x := by
            simpa [d] using eq677_div_master_one h x y
          _ = x ◇ y := heq
      have hfix : (y ◇ x) ◇ y = y :=
        eq677_left_cancel h x hrow
      exact hno (y ◇ x) y hfix
    have h7 (u v : G) : d u (d v u) ≠ u := by
      have hdiv' := hdiv (v ◇ u) v
      have h' : u ≠ (v ◇ u) ◇ v := by
        intro hu
        exact hdiv' ((eq677_div_right h v u).trans hu)
      rw [eq677_div_master_two h u v] at h'
      simpa [d] using Ne.symm h'
    have h6 (x y : G) :
        y ◇ x = d (c y (x ◇ y)) (d x y) := by
      have h' := eq677_conjugacy_eval h hconj y (x ◇ y) x
      rw [eq677_div_master_two h y x] at h'
      simpa [d, c, eq677_div_left] using h'
    have h8 (x y : G) : d (d y x) (x ◇ y) ≠ d y x := by
      have h' := h7 (d y x) (c x (y ◇ x))
      rw [← h6 y x] at h'
      exact h'
    have h9 (x y : G) : d x (d x (d y x)) ≠ x := by
      have h' := h8 (y ◇ x) y
      change d (d y (y ◇ x)) ((y ◇ x) ◇ y) ≠ d y (y ◇ x) at h'
      change eq677_div h (eq677_div h y (y ◇ x)) ((y ◇ x) ◇ y) ≠
        eq677_div h y (y ◇ x) at h'
      rw [eq677_div_right h y x, eq677_div_master_two h x y] at h'
      simpa [d] using h'
    have hcontra : False := by
      obtain ⟨x⟩ := ‹Nonempty G›
      let z := c x (x ◇ x)
      have h' := h9 x (c x z)
      rw [← hinvconj x z x, ← h6 x x] at h'
      exact h' (eq677_div_right h x x)
    exact hcontra
  obtain ⟨a₀, z₀, ha₀⟩ := some_fixed
  have all_fixed : ∀ x : G, ∃ a, a ◇ x = x := by
    intro x
    obtain ⟨a₁, ha₁⟩ := fixed_image (z₀ ◇ x) a₀ z₀ ha₀
    obtain ⟨a₂, ha₂⟩ :=
      fixed_image x a₁ ((z₀ ◇ x) ◇ z₀) ha₁
    obtain ⟨a₃, ha₃⟩ :=
      fixed_image z₀ a₂ (x ◇ ((z₀ ◇ x) ◇ z₀)) ha₂
    refine ⟨a₃, ?_⟩
    calc
      a₃ ◇ x = a₃ ◇ (z₀ ◇ (x ◇ ((z₀ ◇ x) ◇ z₀))) := by
        exact congrArg (fun t => a₃ ◇ t) (h x z₀)
      _ = z₀ ◇ (x ◇ ((z₀ ◇ x) ◇ z₀)) := ha₃
      _ = x := (h x z₀).symm
  intro x
  obtain ⟨a, hax⟩ := all_fixed x
  rw [fixed_rule a x hax] at hax
  exact hax.symm

/-- If a finite Equation-677 magma has left translations closed under
conjugation by its left translations, then it satisfies Equation 255.

The conjugacy-closure assumption is additional; this theorem does not prove
the unrestricted finite implication `Equation677 → Equation255`. -/
theorem eq255_of_eq677_leftMul_conjugacy_closed (h : Equation677 G)
    (hconj : ∀ a b, ∃ c, ∀ z,
      c ◇ z = a ◇ (b ◇ ((eq677_leftMulEquiv h a).symm z))) :
    Equation255 G := by
  by_cases hG : Nonempty G
  · letI : Nonempty G := hG
    exact eq255_of_eq677_leftMul_conjugacy_closed_nonempty h hconj
  · intro x
    exact (hG ⟨x⟩).elim

end Eq677
