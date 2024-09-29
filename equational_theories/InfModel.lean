import equational_theories.Equations
import Mathlib.Data.Fintype.Card
import Mathlib.NumberTheory.Padics.PadicVal.Basic

abbrev EquationKis (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ y) ∘ x) ∘ ((y ∘ y) ∘ z)

/--
In a finite model `EquationKis` implies `Equation2`, that the model is a subsingleton.
-/
theorem Finite.EquationKis_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : EquationKis G) :
    Equation2 G := by
  have : ∀ (y z u : G), (y ∘ y) ∘ z = (y ∘ y) ∘ u := by
    intro y
    let f (x : G) := ((y ∘ y) ∘ y) ∘ x
    let g (x : G) := x ∘ ((y ∘ y) ∘ y)
    have : Function.RightInverse f g := by
      intro x
      simp [f, g, ← h]
    intro z u
    apply this.injective
    obtain ⟨finv, hf⟩ := (Finite.surjective_of_injective this.injective).hasRightInverse
    let fy := finv ((y ∘ y) ∘ y)
    replace hf : ((y ∘ y) ∘ y) ∘ fy = (y ∘ y) ∘ y := hf _
    have := h fy y
    simp only [hf] at this
    simp [f, ← this]
  intro x u
  have y := x
  have z := x
  rw [h x y z, this y y (y ∘ y), this (y ∘ y) x u, ← this y y (y ∘ y), ← h]

/--
However, `EquationKis` doesn't imply `Equation2`.
-/
theorem EquationKis_not_implies_Equation2 : ∃ (G : Type) (_ : Magma G), EquationKis G ∧ ¬Equation2 G := by
  letI : Magma ℕ+ := { op := fun a b ↦ if a = b then 2^a.val else
    if a = 1 then 3^b.val else
    if a = 3 ^ (padicValNat 3 a) then Nat.toPNat' (padicValNat 3 a) else 1}
  refine ⟨ℕ+, this, ⟨?_, fun x ↦ nomatch (x 1 2)⟩⟩
  intro x y z
  unfold Magma.op
  simp only [↓reduceIte, PNat.pow_coe, PNat.val_ofNat]
  have t1 (y : ℕ+) : 2 ^ (y : ℕ) ≠ y := by
    apply_fun PNat.val
    simp [ne_of_gt, Nat.lt_pow_self]
  have t3 (y : ℕ+) (n : ℕ) : (2 : ℕ+) ^ (y : ℕ) ≠ 3^n := by
    apply_fun PNat.val
    simp only [PNat.pow_coe, PNat.val_ofNat, ne_eq]
    intro nh
    apply eq_of_prime_pow_eq at nh
    · contradiction
    · exact Nat.prime_two.prime
    · exact Nat.prime_three.prime
    · simp
  have t2 (y : ℕ+) : (2 : ℕ+) ^ (y : ℕ) ≠ 1 := t3 y 0
  have t4 (y : ℕ+) (n : ℕ) : (3 : ℕ+) ^ (y : ℕ) ≠ 2^n := by
    apply_fun PNat.val
    simp only [PNat.pow_coe, PNat.val_ofNat, ne_eq]
    intro nh
    apply eq_of_prime_pow_eq at nh
    · contradiction
    · exact Nat.prime_three.prime
    · exact Nat.prime_two.prime
    · simp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  simp only [t1, ↓reduceIte, t2, t3, PNat.val_ofNat, pow_one]
  by_cases hx : x = 1
  · simp only [hx, ↓reduceIte, PNat.val_ofNat, PNat.ofNat_inj, OfNat.ofNat_ne_one, ne_eq,
    Nat.succ_ne_self, not_false_eq_true, padicValNat_primes, pow_zero]
    rw [if_neg]
    split_ifs
    · apply ne_of_lt
      simp only [← PNat.coe_lt_coe, PNat.val_ofNat, PNat.pow_coe]
      apply lt_self_pow (by simp)
      apply one_lt_pow (by simp) (by simp)
    · trivial
  simp only [Ne.symm hx, ↓reduceIte, PNat.pow_coe, PNat.val_ofNat, padicValNat.prime_pow,
    PNat.coe_toPNat']
  rw [if_neg, if_neg]
  · simp [pow_eq_one_iff]
  · split
    · apply t4
    · convert t4 _ 0
