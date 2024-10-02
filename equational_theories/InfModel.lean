import equational_theories.Equations
import Mathlib.Data.Fintype.Card
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace InfModel

/--
In a finite model `Equation374794` implies `Equation2`, that the model is a subsingleton.
-/
theorem Finite.Equation374794_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation374794 G) :
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
However, `Equation374794` doesn't imply `Equation2`.
-/
theorem Equation374794_not_implies_Equation2 : ∃ (G : Type) (_ : Magma G), Equation374794 G ∧ ¬Equation2 G := by
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

theorem Finite.Equation5105_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation5105 G) :
    Equation2 G:= by
    intro x y
    let f (y w : G) := y ∘ w
    have f_onto : ∀ y : G, Function.Surjective (f y) := by
      intro y x
      use (y ∘ (y ∘ (x ∘ (x ∘ y))))
      dsimp [f]
      rw [← h]
    have f_inj : ∀ y : G, Function.Injective (f y) :=by
      intro y
      exact Finite.injective_iff_surjective.mpr (f_onto y)
    have hh: ∀ y z w : G, z ∘ y = w ∘ y := by
      intro y z w
      let g := f y
      have h1 : g (y ∘ (y ∘ (x ∘ (z ∘ y)))) = g (y ∘ (y ∘ (x ∘ (w ∘ y)))):= by dsimp [g, f]; rw [← h, ← h]
      have h2 : g (y ∘ (x ∘ (z ∘ y))) = g (y ∘ (x ∘ (w ∘ y))) := by
        dsimp [g, f]
        exact f_inj y h1
      have h3 : g (x ∘ (z ∘ y)) = g (x ∘ (w ∘ y)) := by
        dsimp [g, f]
        exact f_inj y h2
      have h4 : f x (z ∘ y) = f x (w ∘ y) := by
        dsimp [f]
        exact f_inj y h3
      exact f_inj x h4
    have hhh : ∀ a b c d: G, c ∘ (a ∘ b) = d ∘ (a ∘ b) := by
      intro a b c d
      exact hh (a ∘ b) c d
    have hhhh : ∀ a b: G, b ∘ (b ∘ (b ∘ (x ∘ (a ∘ b)))) = b ∘ (b ∘ (b ∘ (y ∘ (a ∘ b)))) := by
      intro a b
      rw [hhh a b _ _]
    calc
      x = x ∘ (x ∘ (x ∘ (x ∘ (x ∘ x)))) := by exact h x x x
      _= x ∘ (x ∘ (x ∘ (y ∘ (x ∘ x)))) := by rw [hhhh]
      _= y := by rw [←  h y x x]

theorem Finite.Equation28393_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation28393 G) :
    Equation2 G := by
    have : ∀ (y z u : G), y ∘ z = y ∘ u := by
      intro y
      let f (x : G) := ((y ∘ y) ∘ y) ∘ x
      let g (x : G) := x ∘ (y ∘ y)
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
    rw [h x y z, this ((y ∘ y) ∘ y)  x u, ← this ((y ∘ y) ∘ y) u u, ← h]

theorem Equation28393_not_implies_Equation2 : ∃ (G : Type) (_ : Magma G), Equation28393 G ∧ ¬Equation2 G := by
  letI : Magma ℕ := { op := sorry }
  refine ⟨ℕ, this, ⟨?_, fun x ↦ nomatch (x 0 1)⟩⟩
  intro x y z
  have h1 : ∀ (y: ℕ), y ∘ y = 2^y := sorry
  have h2 : ∀ (y: ℕ), (2^y) ∘ y = 3^y := sorry
  have h3 : ∀ (x y: ℕ), x ≠ 3^y → (3^y) ∘ x = 3^y * 5^x := sorry
  have h4 : ∀ (x y z: ℕ), z ≠ 3^y * 5^x → (3^y * 5^x) ∘ z = x := sorry
  have h5 : ∀ (y z: ℕ), z ≠ 3^y ∧ z ≠ 2^(3^y) → (2^(3^y)) ∘ z = 3^y := sorry
  rw [h1, h2]
  by_cases hx : x = 3^y
  .
    rw [hx, h1, h5 y (y ∘ z) sorry]
  .
    rw [h3 x y hx]
    by_cases hz : z = 3^y
    .
      sorry
    .
      rw [h4 x y (y ∘ z) sorry]

end InfModel
