import equational_theories.Equations.All
import equational_theories.MagmaOp
import Aesop
import Mathlib.Data.Fintype.Card
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import equational_theories.Mathlib.Algebra.Group.Nat
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Eval
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Tactic.ComputeDegree

namespace InfModel

/--
In a finite model `Equation374794` implies `Equation2`, that the model is a subsingleton.
-/
theorem Finite.Equation374794_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation374794 G) :
    Equation2 G := by
  have : ∀ (y z u : G), (y ◇ y) ◇ z = (y ◇ y) ◇ u := by
    intro y
    let f (x : G) := ((y ◇ y) ◇ y) ◇ x
    let g (x : G) := x ◇ ((y ◇ y) ◇ y)
    have : Function.RightInverse f g := fun x ↦ by simp [f, g, ← h]
    refine fun z u ↦ this.injective ?_
    obtain ⟨finv, hf⟩ := (Finite.surjective_of_injective this.injective).hasRightInverse
    let fy := finv ((y ◇ y) ◇ y)
    replace hf : ((y ◇ y) ◇ y) ◇ fy = (y ◇ y) ◇ y := hf _
    have := h fy y
    simp only [hf] at this
    simp [f, ← this]
  intro x u
  have y := x
  have z := x
  rw [h x y z, this y y (y ◇ y), this (y ◇ y) x u, ← this y y (y ◇ y), ← h]

/--
However, `Equation374794` doesn't imply `Equation2`.
-/
theorem Equation374794_not_implies_Equation2 : ∃ (G : Type) (_ : Magma G), Equation374794 G ∧ ¬Equation2 G := by
  letI : Magma ℕ+ := { op := fun a b ↦ if a = b then 2^a.val else
    if a = 1 then 3^b.val else
    if a = 3 ^ (padicValNat 3 a) then Nat.toPNat' (padicValNat 3 a) else 1}
  refine ⟨ℕ+, this, ⟨fun x y z ↦ ?_, fun x ↦ nomatch (x 1 2)⟩⟩
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
      apply lt_self_pow (by simp only [Nat.one_lt_ofNat])
      apply one_lt_pow₀ (by simp only [Nat.one_lt_ofNat]) (by simp)
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
  let f (y w : G) := y ◇ w
  have f_onto : ∀ y : G, Function.Surjective (f y) := by
    intro y x
    use (y ◇ (y ◇ (x ◇ (x ◇ y))))
    dsimp [f]
    rw [← h]
  have f_inj : ∀ y : G, Function.Injective (f y) :=
    fun _ ↦ Finite.injective_iff_surjective.mpr (f_onto _)
  have hh : ∀ y z w : G, z ◇ y = w ◇ y := by
    intro y z w
    let g := f y
    exact f_inj x (f_inj y (f_inj y (f_inj y (by dsimp [g, f]; rw [← h, ← h]))))
  have hhh : ∀ a b c d: G, c ◇ (a ◇ b) = d ◇ (a ◇ b) := fun _ _ _ _  ↦ hh _ _ _
  have hhhh : ∀ a b: G, b ◇ (b ◇ (b ◇ (x ◇ (a ◇ b)))) = b ◇ (b ◇ (b ◇ (y ◇ (a ◇ b)))) := by
    intro a b
    rw [hhh a b]
  calc
    x = x ◇ (x ◇ (x ◇ (x ◇ (x ◇ x)))) := h x x x
    _= x ◇ (x ◇ (x ◇ (y ◇ (x ◇ x)))) := by rw [hhhh]
    _= y := by rw [← h y x x]

theorem Finite.Equation28770_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation28770 G) :
    Equation2 G := by
  have : ∀ (y z u : G), y ◇ z = y ◇ u := by
    intro y
    let f (x : G) := ((y ◇ y) ◇ y) ◇ x
    let g (x : G) := x ◇ (y ◇ y)
    have : Function.RightInverse f g := fun _ ↦ by simp [f, g, ← h]
    apply fun _ _ ↦ this.injective _
    obtain ⟨finv, hf⟩ := (Finite.surjective_of_injective this.injective).hasRightInverse
    let fy := finv ((y ◇ y) ◇ y)
    replace hf : ((y ◇ y) ◇ y) ◇ fy = (y ◇ y) ◇ y := hf _
    have := h fy y
    simp only [hf] at this
    simp [f, ← this]
  intro x u
  have y := x
  have z := x
  rw [h x y z, this ((y ◇ y) ◇ y)  x u, ← this ((y ◇ y) ◇ y) u u, ← h]

theorem Equation28770_not_implies_Equation2 : ∃ (G : Type) (_ : Magma G), Equation28770 G ∧ ¬Equation2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  letI : Magma ℕ+ := { op := fun a b ↦ if a = b then 2^b.val else
        if a = 2^b.val then 3^b.val else
        if a = 3^(padicValNat 3 a) then a * 5^b.val else
        if a = 3^(padicValNat 3 a) * 5^(padicValNat 5 a) then Nat.toPNat' (padicValNat 5 a) else
        if a = 2^(3^(padicValNat 3 (padicValNat 2 a))) then 3^(padicValNat 3 (padicValNat 2 a)) else 1}
  refine ⟨ℕ+, this, ⟨?_, fun x ↦ nomatch (x 1 2)⟩⟩
  intro x y z
  -- t1 is from the proof of Equation374794_not_implies_Equation2
  have t1 (y : ℕ+) : 2 ^ (y : ℕ) ≠ y := by
    apply_fun PNat.val
    simp [ne_of_gt, Nat.lt_pow_self]
  have h1 : ∀ (y: ℕ+), y ◇ y = 2^y.val := by
    intro y
    unfold Magma.op
    simp
  have h2 : ∀ (y: ℕ+), (2^y.val) ◇ y = 3^y.val := by
    intro y
    unfold Magma.op
    simp [t1]
  have h3 : ∀ (x y: ℕ+), x ≠ 3^y.val → (3^y.val) ◇ x = 3^y.val * 5^x.val := by
    intro x y hxy
    unfold Magma.op
    simp only [PNat.pow_coe, PNat.val_ofNat, padicValNat.prime_pow, ↓reduceIte]
    rw [if_neg]
    case hnc => exact fun h'' => hxy (by simp [h''])
    simp only [ite_eq_right_iff]
    contrapose
    intro _
    apply_fun PNat.val
    simp only [PNat.pow_coe, PNat.val_ofNat, ne_eq]
    intro nh
    apply eq_of_prime_pow_eq at nh
    · contradiction
    · exact Nat.prime_three.prime
    · exact Nat.prime_two.prime
    · simp
  have h4 : ∀ (x y z: ℕ+), z ≠ 3^y.val * 5^x.val → (3^y.val * 5^x.val) ◇ z = x := by
    intro x y z hxyz
    unfold Magma.op
    simp only [PNat.mul_coe, PNat.pow_coe, PNat.val_ofNat]
    rw [if_neg]
    case hnc =>
      intro h'
      apply hxyz
      simp [h']
    rw [if_neg]
    case hnc =>
      apply_fun PNat.val
      simp only [PNat.mul_coe, PNat.pow_coe, PNat.val_ofNat, ne_eq]
      intro nh
      apply PNat.ne_zero z
      calc ↑z
        _ = padicValNat 2 (3^y.val * 5^x.val) := by simp [nh]
        _ = 0 := by simp [padicValNat.mul, padicValNat_prime_prime_pow]
    rw [if_neg]
    case hnc =>
      intro hc
      apply PNat.ne_zero x
      calc ↑x
        _ = padicValNat 5 ↑((3: ℕ+)^y.val * (5: ℕ+)^x.val) := by simp [padicValNat_prime_prime_pow, padicValNat.mul]
        _ = padicValNat 5 ((3: ℕ+)^(padicValNat (3: ℕ) ((3: ℕ)^y.val * (5: ℕ)^x.val))) := by simp [hc]
        _ = 0 := by simp [padicValNat_prime_prime_pow]
    rw [if_pos]
    case hc => simp [padicValNat.mul, padicValNat_prime_prime_pow]
    simp [this, Subtype.ext_iff, padicValNat.mul, padicValNat_prime_prime_pow]
  have h5 : ∀ (y z: ℕ+), z ≠ 3^y.val ∧ z ≠ 2^(3^y.val) → (2^(3^y.val)) ◇ z = 3^y.val := by
    intro y z hyz
    unfold Magma.op
    simp only [PNat.pow_coe, PNat.val_ofNat, padicValNat.prime_pow, ↓reduceIte]
    rw [if_neg, if_neg, if_neg, if_neg]
    · intro hc
      apply PNat.ne_zero ((3: ℕ+)^y.val)
      calc ↑((3: ℕ+)^y.val)
        _ = padicValNat 2 ↑(2^3^y.val: ℕ+) := by simp
        _ = padicValNat 2 _ := by rw [hc]
        _ = 0 := by simp [padicValNat_prime_prime_pow]
    · intro hc
      apply PNat.ne_zero ((3: ℕ+)^y.val)
      calc ↑((3: ℕ+)^y.val)
        _ = padicValNat 2 ↑(2^3^y.val: ℕ+) := by simp
        _ = padicValNat 2 _ := by rw [hc]
        _ = 0 := by simp [padicValNat_prime_prime_pow]
    · intro hc
      apply hyz.1
      calc z
        _ = z.val.toPNat' := by simp
        _ = (padicValNat 2 (2^z.val: ℕ+)).toPNat' := by simp
        _ = (padicValNat 2 ↑(2^3^y.val: ℕ+)).toPNat' := by rw [←hc]
        _ = (3^y.val: ℕ).toPNat' := by simp
        _ = 3^↑y := by rw [←PNat.coe_inj]; simp
    · exact fun hc ↦ (hyz.2 (by rw [hc]))
  rw [h1, h2]
  by_cases hx : x = 3^y.val
  · rw [hx, h1]
    by_cases hyz : y ◇ z = 2^(3^y.val)
    · simp [hyz, h1]
      exfalso
      have : padicValNat 2 ↑(y ◇ z) = ↑(3^y.val) := by simp [hyz]
      unfold Magma.op at this
      simp only [apply_ite PNat.val, PNat.pow_coe, PNat.val_ofNat, PNat.mul_coe, Nat.toPNat'_coe,
        apply_ite (padicValNat 2), padicValNat.prime_pow, ne_eq, Nat.reduceEqDiff,
        not_false_eq_true, padicValNat_prime_prime_pow, PNat.ne_zero, pow_eq_zero_iff,
        OfNat.ofNat_ne_zero, padicValNat.mul, add_zero, padicValNat.one, ite_self, ite_eq_iff,
        not_lt, nonpos_iff_eq_zero, padicValNat.eq_zero_iff, OfNat.ofNat_ne_one, false_or] at this
      have this' : (0: ℕ) = (3: ℕ)^y.val ↔ False :=
        Iff.intro (fun h ↦ pow_ne_zero y.val (by norm_num) h.symm) False.elim
      simp [this'] at this
      repeat simp [and_or_left, and_or_left] at this
      cases this with
      | inl h =>
        rw [h.1] at h
        simp only [true_and] at h
        exact ne_of_gt (Nat.lt_pow_self (by norm_num) z.val) h.symm
      | inr this => _
      cases this with
      | inl h =>
        have h1 := h.2.2.1
        have h2 := h.2.2.2
        rw [h1] at h2
        simp at h2
        simp [padicValNat_prime_prime_pow] at h2
        have h2 := h2.symm
        have := pow_ne_zero (3^padicValNat 3 y.val) (by norm_num: 3 ≠ 0)
        apply pow_ne_zero y.val (by norm_num: 3 ≠ 0)
        contradiction
      | inr this => _
      have this' := this.2.2.2.2.2
      apply_fun padicValNat 3 at this'
      simp [padicValNat.prime_pow] at this'
      have this' := this'.symm
      have this2 := calc y.val
        _ > Nat.log 5 y.val := by simp [Nat.log_lt_self]
        _ ≥ padicValNat 5 y.val := by simp [padicValNat_le_nat_log]
        _ ≥ Nat.log 2 (padicValNat 5 y.val) := by simp [Nat.log_le_self]
        _ ≥ padicValNat 2 (padicValNat 5 y.val) := by simp [padicValNat_le_nat_log]
        _ ≥ Nat.log 3 (padicValNat 2 (padicValNat 5 y.val)) := by simp [Nat.log_le_self]
        _ ≥ padicValNat 3 (padicValNat 2 (padicValNat 5 y.val)) := by simp [padicValNat_le_nat_log]
      have this3 := ne_of_gt this2
      exact this3 this'
    · by_cases hyz' : y ◇ z = 3^y.val
      · rw [←hyz', h2, hyz']
        exfalso
        have : padicValNat 3 ↑(y ◇ z) = ↑y.val := by simp [hyz']
        unfold Magma.op at this
        simp at this
        repeat rw [apply_ite PNat.val] at this
        repeat rw [apply_ite (padicValNat 3)] at this
        simp only [PNat.pow_coe, PNat.val_ofNat] at this
        simp only [padicValNat.prime_pow] at this
        simp [padicValNat_prime_prime_pow] at this
        repeat rw [apply_ite (padicValNat 3)] at this
        simp [padicValNat.mul, padicValNat_prime_prime_pow] at this
        repeat simp only [ite_eq_iff] at this
        simp at this
        have this' : ((0: ℕ) = y.val) ↔ False := by
          simp [false_iff]
          intro hc
          have hc := hc.symm
          have hc' := PNat.ne_zero y
          contradiction
        simp [this'] at this
        repeat simp [and_or_left, and_or_left] at this
        cases this with
        | inl h =>
          have h1 := h.2.1
          have h2 := h.2.2
          rw [h2] at h1
          have h1 := h1.symm
          apply_fun PNat.val at h1
          simp at h1
          have this2 := Nat.lt_pow_self (by norm_num: 1 < 2) y.val
          have this3 := ne_of_gt this2
          exact this3 h1
        | inr this => _
        cases this with
        | inl h =>
          have h1 := h.2.2.1
          have h2 := h.2.2.2
          rw [h2] at h1
          have h1 := h1.symm
          apply_fun PNat.val at h1
          simp at h1
          have this2 := Nat.lt_pow_self (by norm_num: 1 < 3) y.val
          have this3 := ne_of_gt this2
          exact this3 h1
        | inr this => _
        cases this with
        | inl h =>
          have h := h.2.2.2.2.2.symm
          have h' := calc y.val
            _ > Nat.log 5 y.val := by simp [Nat.log_lt_self]
            _ ≥ padicValNat 5 y.val := by simp [padicValNat_le_nat_log]
            _ ≥ Nat.log 3 (padicValNat 5 y.val) := by simp [Nat.log_le_self]
            _ ≥ padicValNat 3 (padicValNat 5 y.val) := by simp [padicValNat_le_nat_log]
          exact (ne_of_gt h') h
        | inr this => _
        have this := this.2.2.2.2.2.symm
        have this' := calc y.val
          _ > Nat.log 2 y.val := by simp [Nat.log_lt_self]
          _ ≥ padicValNat 2 y.val := by simp [padicValNat_le_nat_log]
          _ ≥ Nat.log 3 (padicValNat 2 y.val) := by simp [Nat.log_le_self]
          _ ≥ padicValNat 3 (padicValNat 2 y.val) := by simp [padicValNat_le_nat_log]
        exact (ne_of_gt this') this
      · have : (y ◇ z) ≠ 3^y.val ∧ (y ◇ z) ≠ 2^(3^y.val)  := And.intro hyz' hyz
        simp [h5 y (y ◇ z) this]
  · rw [h3 x y hx]
    by_cases hyz : y ◇ z = 3^y.val * 5^x.val
    · rw [hyz, h1]
      exfalso
      unfold Magma.op at hyz
      simp at hyz
      simp only [PNat.pow_coe, PNat.val_ofNat] at hyz
      repeat simp only [ite_eq_iff] at hyz
      cases hyz with
      | inl h =>
        have h' := h.2
        apply_fun padicValNat 2 at h'
        simp [padicValNat_prime_prime_pow, padicValNat.mul] at h'
      | inr hyz => _
      have hyz := hyz.2
      cases hyz with
      | inl h =>
        have h' := h.2.symm
        apply_fun padicValNat 5 at h'
        simp [padicValNat_prime_prime_pow, padicValNat.mul] at h'
      | inr hyz => _
      have hyz := hyz.2
      cases hyz with
      | inl h =>
        rw [h.1] at h
        have h' := h.2
        apply_fun padicValNat 3 at h'
        simp [padicValNat_prime_prime_pow, padicValNat.mul] at h'
        have this2 := Nat.lt_pow_self (by norm_num: 1 < 3) (padicValNat 3 y.val)
        have this2 := ne_of_gt this2
        exact this2 (h'.symm)
      | inr hyz => _
      have hyz := hyz.2
      cases hyz with
      | inl h =>
        rw [h.1] at h
        have h' := h.2
        simp [padicValNat_prime_prime_pow, padicValNat.mul, Nat.pow_mul] at h'
        apply_fun PNat.val at h'
        simp at h'
        repeat simp only [ite_eq_iff] at h'
        cases h' with
        | inl this =>
          have this := this.2
          have this' := calc 3 ^ (3 ^ padicValNat 3 y.val * 5 ^ padicValNat 5 y.val) * 5 ^ x.val
            _ ≥ 3 ^ (3 ^ padicValNat 3 y.val * 5 ^ padicValNat 5 y.val) := by simp [one_le_pow₀]
            _ = 3 ^ (5 ^ padicValNat 5 y.val * 3 ^ padicValNat 3 y.val) := by simp [mul_comm]
            _ = (3 ^ (5 ^ padicValNat 5 y.val)) ^ (3 ^ padicValNat 3 y.val) := by simp [pow_mul]
            _ ≥ 3 ^ (5 ^ padicValNat 5 y.val) := by apply le_self_pow₀; simp [one_le_pow₀]; apply pow_ne_zero; simp
            _ > 5 ^ padicValNat 5 y.val := by simp [Nat.lt_pow_self (by norm_num: 1 < 3)]
            _ > padicValNat 5 y.val := by simp [Nat.lt_pow_self (by norm_num: 1 < 5)]
          exact (ne_of_gt this') (this.symm)
        | inr this =>
          have this := this.2.symm
          apply_fun padicValNat 5 at this
          simp [padicValNat_prime_prime_pow, padicValNat.mul] at this
      | inr hyz => _
      have hyz := hyz.2
      cases hyz with
      | inl h =>
        have h := h.2.symm
        apply_fun padicValNat 3 at h
        simp [padicValNat_prime_prime_pow, padicValNat.mul, Nat.pow_mul] at h
        have this' := calc y.val
          _ > Nat.log 2 y.val := by simp [Nat.log_lt_self]
          _ ≥ padicValNat 2 y.val := by simp [padicValNat_le_nat_log]
          _ ≥ Nat.log 3 (padicValNat 2 y.val) := by simp [Nat.log_le_self]
          _ ≥ padicValNat 3 (padicValNat 2 y.val) := by simp [padicValNat_le_nat_log]
        exact (ne_of_gt this') h
      | inr hyz => _
      have h := hyz.2.symm
      apply_fun padicValNat 3 at h
      simp [padicValNat_prime_prime_pow, padicValNat.mul, Nat.pow_mul] at h
    · rw [h4 x y (y ◇ z) hyz]

theorem Finite.Equation3994_implies_Equation3588 (G : Type*) [Magma G] [Finite G] (h : Equation3994 G) :
    Equation3588 G := by
  intro x y z
  let S := {x | ∃ a b : G, a ◇ b = x}
  have m1 : S.MapsTo (z ◇ ·) S := by
    intro
    simp [S]
  have m2 : S.MapsTo (· ◇ z) S := by
    intro
    simp [S]
  have : S.LeftInvOn (· ◇ z) (z ◇ ·) := by
    intro x hx
    simp only [Set.mem_setOf_eq, S] at hx
    obtain ⟨a, b, rfl⟩ := hx
    simp [← h]
  have t2 := this.surjOn m1
  rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m2] at t2
  have hrio := Set.InjOn.rightInvOn_of_leftInvOn t2.injOn this m2 m1
  apply (hrio _).symm
  simp [S]

@[equational_result]
theorem Equation3994_not_implies_Equation3588 : ∃ (G : Type) (_ : Magma G), Equation3994 G ∧ ¬Equation3588 G := by
  let magN : Magma ℕ := ⟨fun x y ↦ if Even x ∧ Even y then x ^^^ y else if Even y then y + 2
    else if Even x then x - 2 else 0⟩
  use ℕ, magN
  have range : ∀ x y : ℕ, Even (x ◇ y : ℕ) := by
    intro x y
    simp only [magN]
    split_ifs
    · simp_all
    · simpa [Nat.even_add]
    · by_cases x < 2
      · rw [Nat.sub_eq_zero_of_le]
        simp
        omega
      rw [Nat.even_sub]
      · simp_all
      · omega
    · exact even_zero
  constructor
  · intro x y z
    generalize h : x ◇ y = v
    have : Even v := by rw [← h]; apply range
    by_cases hz : Even z
    · simp [magN, this, hz, Nat.xor_comm, Nat.xor_cancel_left]
    · simp [magN, hz, this, Nat.even_add]
  simp only [not_forall]
  use 1, 1, 1
  simp [magN]

/--
Dual of the above.
-/
@[equational_result]
theorem Equation3588_not_implies_Equation3994 : ∃ (G : Type) (_ : Magma G), Equation3588 G ∧ ¬ Equation3994 G := by
  obtain ⟨G', G'Magma, h3994, h3588⟩ := Equation3994_not_implies_Equation3588
  refine ⟨Op G', opMagma, ?_, ?_⟩
  · have h1 : Equation3994 G' ↔ Equation3588 (Op G') := forall_comm
    rwa [h1] at h3994
  · have h2 : Equation3994 (Op G') ↔ Equation3588 G' := forall_comm
    rwa [←h2] at h3588

-- Another Austin pair, this one with only two variables in both equations.
-- https://leanprover.zulipchat.com/#narrow/stream/458659-Equational/topic/1648.20!.3D.3E.20206/near/476842251
theorem Finite.Equation206_implies_Equation1648 (G : Type*) [Magma G] [Finite G] (h : Equation206 G) : Equation1648 G := by
  intro x y
  let S : Set G := Set.univ
  have m1 : S.MapsTo (· ◇ y) S := by
    intro
    simp [S]
  have t : S.SurjOn (· ◇ y) S := by
    intro x _
    let z := x ◇ (x ◇ y)
    use z
    simp [S, z]
    apply Eq.symm (h x y)
  rw [Set.Finite.surjOn_iff_bijOn_of_mapsTo (Set.toFinite _) m1] at t
  apply t.injOn (by simp [S]) (by simp [S])
  simp
  apply h (x ◇ y)

noncomputable def word_polynomial : FreeMagma (Fin 2) → Polynomial ℤ
  | FreeMagma.Fork w1 w2 => (1 - Polynomial.X) * word_polynomial w1 + Polynomial.X * word_polynomial w2
  | FreeMagma.Leaf z => 1 - z

theorem zero_lt_degree_word_polynomial (w: FreeMagma (Fin 2)) :
  FreeMagma.Mem 0 w → w.first = 1 → w.last = 1
  → 0 < (word_polynomial w).degree := by
  intros zero_mem_w first_w_eq_one last_w_eq_one
  suffices 2 ≤ (word_polynomial w).degree from
    Trans.trans (show 0 < 2 from by norm_num) this
  suffices word_polynomial w ≠ 0 ∧ Polynomial.X * (1 - Polynomial.X) ∣ word_polynomial w by
    have ⟨h1, h2⟩ := this
    have : (Polynomial.X * (1 - Polynomial.X): Polynomial ℤ).degree = 2 := by
      compute_degree
        <;> decide
    rw [←this]
    apply Polynomial.degree_le_of_dvd
      <;> first | exact h1 | exact h2
  split_ands
  .
    clear * - zero_mem_w
    let r' := Polynomial.map (Int.castRingHom ℚ) (word_polynomial w)
    suffices ∀ (q: ℚ), 0 < q → q < 1 → 0 < Polynomial.eval q r' by
      unfold r' at *
      clear zero_mem_w
      revert this
      apply Function.mtr
      intro this
      simp_all only [ne_eq, Decidable.not_not, Polynomial.map_zero,
                    Polynomial.eval_zero, lt_self_iff_false, imp_false, not_lt,
                    not_forall, Classical.not_imp, not_le, exists_prop]
      exists 1/2
      norm_num
    intros q zero_lt_q q_lt_one
    revert q zero_mem_w zero_lt_q q_lt_one
    suffices ∀ (q: ℚ), 0 < q → q < 1 → (0 ≤ Polynomial.eval q r' ∧
                (FreeMagma.Mem 0 w → 0 < Polynomial.eval q r')) by
      simp_all only [implies_true]
    induction w
    .
      rename_i z
      fin_cases z
      all_goals {
        simp_all only [word_polynomial, CharP.cast_eq_zero, sub_zero,
                      Polynomial.map_one, Polynomial.eval_one, zero_le_one,
                      FreeMagma.Mem, Fin.zero_eta, zero_lt_one, imp_self,
                      and_self, implies_true, r', word_polynomial,
                      Nat.cast_one, sub_self, Polynomial.map_zero,
                      Polynomial.eval_zero, le_refl, FreeMagma.Mem, Fin.mk_one,
                      zero_ne_one, lt_self_iff_false, false_implies, and_self,
                      implies_true, r']
      }
    .
      rename_i w1 w2 h1 h2
      intros q zero_lt_q q_lt_one
      replace h1 := h1 q zero_lt_q q_lt_one
      replace h2 := h2 q zero_lt_q q_lt_one
      simp_all [r', word_polynomial]
      split_ands
      .
        replace h1 := h1.1
        replace h2 := h2.1
        generalize Polynomial.eval q (Polynomial.map (Int.castRingHom ℚ)
                                      (word_polynomial w1)) = q1 at *
        generalize Polynomial.eval q (Polynomial.map (Int.castRingHom ℚ)
                                      (word_polynomial w2)) = q2 at *
        apply add_nonneg
          <;> apply mul_nonneg
        all_goals {
          try simp_all only [sub_nonneg]
          try { apply le_of_lt; assumption }
        }
      .
        have h12 := h1.2
        have h22 := h2.2
        intro mem_zero_w
        simp_all [FreeMagma.Mem]
        cases mem_zero_w
        .
          rename_i mem_zero_w1
          replace h12 := h12 mem_zero_w1
          apply add_pos_of_pos_of_nonneg
          .
            apply mul_pos
              <;> simp_all only [sub_pos]
          .
            simp_all only [mul_nonneg_iff_of_pos_left]
        .
          rename_i mem_zero_w2
          replace h22 := h22 mem_zero_w2
          apply add_pos_of_nonneg_of_pos
          .
            simp_all only [sub_pos, mul_nonneg_iff_of_pos_left]
          .
            apply mul_pos
              <;> simp_all only [sub_pos]
  .
    clear * - first_w_eq_one last_w_eq_one
    revert w
    suffices (∀ (w: FreeMagma (Fin 2)), w.first = 1 → Polynomial.X ∣ word_polynomial w)
             ∧ (∀ (w: FreeMagma (Fin 2)), w.last = 1 → (1 - Polynomial.X) ∣ word_polynomial w) by
      obtain ⟨h1, h2⟩ := this
      intros w first_w_eq_one last_w_eq_one
      cases w
      .
        rename_i z
        fin_cases z
        all_goals {
          simp_all only [Fin.zero_eta, word_polynomial, CharP.cast_eq_zero, sub_zero, Fin.mk_one, Nat.cast_one, sub_self, dvd_zero, FreeMagma.first, FreeMagma.last]
          try contradiction
        }
      .
        rename_i w1 w2
        simp_all only [FreeMagma.first, FreeMagma.last, word_polynomial]
        replace h1 := h1 w1 first_w_eq_one
        replace h2 := h2 w2 last_w_eq_one
        obtain ⟨q1, hq1⟩ := h1
        obtain ⟨q2, hq2⟩ := h2
        exists q1 + q2
        simp only [hq1, hq2]
        ring_nf
    split_ands
      <;> intros w h
    .
      induction w
      .
        rename_i z
        simp_all only [FreeMagma.first, word_polynomial]
        norm_num
      .
        rename_i w1 w2 h1 _
        simp_all only [FreeMagma.first, word_polynomial, true_implies]
        clear * - h1
        obtain ⟨q1, hq1⟩ := h1
        simp_all only
        exists q1 * (1 - Polynomial.X) + (word_polynomial w2)
        ring_nf
    .
      induction w
      .
        rename_i z
        simp_all only [FreeMagma.last, word_polynomial]
        norm_num
      .
        rename_i w1 w2 _ h2
        simp_all only [FreeMagma.last, word_polynomial, true_implies]
        clear * - h2
        obtain ⟨q2, hq2⟩ := h2
        simp_all only
        exists q2 * Polynomial.X + (word_polynomial w1)
        ring_nf

theorem Finite.two_variable_laws {α: Type} [ht : Fintype α] (hc : Fintype.card α = 2) (E: Law.MagmaLaw α) :
  ∀ (z: α),
  FreeMagma.Mem z E.lhs
  → FreeMagma.Mem z E.rhs
  → ∃ (G : Type) (hm : Magma G), Finite G ∧ ¬Equation2 G ∧ G ⊧ E := by
  intro x mem_x_lhs mem_x_rhs
  suffices hs: ∃ (k: ℕ), 1 < k ∧ (∃ (M: Magma (ZMod k)), ZMod k ⊧ E) by
    obtain ⟨k, hk, M, hm⟩ := hs
    exists ZMod k, M
    split_ands
    .
      refine' @Finite.of_fintype (ZMod k) ?_
      refine' @ZMod.fintype k ?_
      simp_all only [neZero_iff, ne_eq]
      omega
    .
      simp only [not_forall]
      refine' @Nontrivial.exists_pair_ne (ZMod k) ?_
      rw [ZMod.nontrivial_iff]
      omega
    .
      assumption
  revert α
  suffices hs: ∀ (E: Law.MagmaLaw (Fin 2)),
               FreeMagma.Mem 0 E.lhs
               → FreeMagma.Mem 0 E.rhs
               → ∃ (k: ℕ), 1 < k ∧ (∃ (M: Magma (ZMod k)), ZMod k ⊧ E) by
    intros α ht hc E x mem_x_lhs mem_x_rhs
    have := Classical.typeDecidableEq α
    let f : α → Fin 2 := fun z => if z = x then 0 else 1
    replace hs := hs (Law.MagmaLaw.map f E)
    have : Function.Injective f := by
      intro z1 z2 eq_z1_z2
      simp only [f] at eq_z1_z2
      split_ifs at eq_z1_z2
        <;> simp_all only [one_ne_zero, zero_ne_one]
      by_contra
      rename_i ne_z2_x ne_z1_x ne_z1_z2
      have : Fintype.card α < Fintype.card α := by
        conv =>
          lhs
          rw [hc]
        apply Fintype.two_lt_card_iff.2
        exists x, z1, z2
        simp_rw [eq_comm] at ne_z2_x ne_z1_x
        split_ands
          <;> assumption
      simp only [lt_self_iff_false] at this
    simp only [Law.satisfies_map_injective f this] at hs
    apply hs
      <;> simp only [Law.MagmaLaw.lhs, Law.MagmaLaw.rhs, Law.MagmaLaw.map]
    .
      clear * - mem_x_lhs
      generalize E.lhs = w at *
      revert mem_x_lhs
      induction w
        <;> simp_all only [FreeMagma.fmapHom, FreeMagma.evalHom, FreeMagma.evalInMagma, FreeMagma.Mem]
      .
        have : 0 = f x := by simp_all only [Fin.isValue, ↓reduceIte, f]
        rw [this]
        simp_all only [implies_true]
      .
        rename_i w1 w2 h1 h2
        intro h
        cases h with
        | inl h =>
          replace h1 := h1 h
          apply Or.inl
          assumption
        | inr h =>
          replace h2 := h2 h
          apply Or.inr
          assumption
    .
      clear * - mem_x_rhs
      generalize E.rhs = w at *
      revert mem_x_rhs
      induction w
        <;> simp_all only [FreeMagma.fmapHom, FreeMagma.evalHom, FreeMagma.evalInMagma, FreeMagma.Mem]
      .
        have : 0 = f x := by simp_all only [Fin.isValue, ↓reduceIte, f]
        rw [this]
        simp_all only [implies_true]
      .
        rename_i w1 w2 h1 h2
        intro h
        cases h with
        | inl h =>
          replace h1 := h1 h
          apply Or.inl
          assumption
        | inr h =>
          replace h2 := h2 h
          apply Or.inr
          assumption
  suffices hs: ∀ (w: FreeMagma (Fin 2)),
               (hw: FreeMagma.Mem 0 w)
               → ∃ (k: ℕ), 1 < k ∧ (∃ (M: Magma (ZMod k)), ZMod k ⊧ (Lf 0 ≃ w)) by
    intro E hz1 hz2
    match E with
    | ⟨FreeMagma.Fork w1 w2, FreeMagma.Fork w3 w4⟩
    | ⟨FreeMagma.Leaf a, FreeMagma.Leaf b⟩ =>
      exists 2
      simp_all only [Nat.one_lt_ofNat, true_and]
      exists Magma.mk fun x y => 0
      simp_all only [satisfies, satisfiesPhi, FreeMagma.Mem]
      intro φ
      simp_all only [FreeMagma.evalInMagma, Magma.op]
    | ⟨FreeMagma.Leaf x, w ⋆ w'⟩
    | ⟨w ⋆ w', FreeMagma.Leaf x⟩ =>
      replace hs := hs (w ⋆ w')
      simp_all only [(by simp_all only [FreeMagma.Mem]: x = 0)]
      try
        .
          simp_all only [true_implies]
          obtain ⟨G, hm, hf, hex⟩ := hs
          exists G, hm, hf
          simp_all only [satisfies, not_false_eq_true, true_and]
          intro φ
          replace hex := Law.satisfiesPhi_symm_law φ _ (hex φ)
          simp_all only [Law.MagmaLaw.symm]
  intros w hw
  by_cases h: w.first = 0 ∨ w.last = 0
  .
    clear hw
    exists 2
    simp_all only [Nat.one_lt_ofNat, true_and]
    cases h with
    | inl h =>
      exists Magma.mk fun x _ => x
      intro f
      simp_all only [←h]
      induction w
        <;> first | rfl | assumption
    | inr h =>
      exists Magma.mk fun _ y => y
      intro f
      simp_all only [←h]
      induction w
        <;> first | rfl | assumption
  .
    simp only [Fin.isValue, not_or] at h
    obtain ⟨hl, hr⟩ := h
    replace hl: w.first = 1 := by omega
    replace hr: w.last = 1 := by omega
    let r: Polynomial ℤ := word_polynomial w
    obtain ⟨b0, hb0⟩ := show ∃ (b0: ℤ), (Polynomial.eval b0 r - 1).natAbs ≠ 1 by
      suffices ∃ (b0: ℤ), Polynomial.eval b0 (r * (r - 2)) ≠ 0 by
        obtain ⟨b0, h⟩ := this
        exists b0
        revert h
        apply mt
        intro h
        simp only [Int.natAbs_eq_iff, Nat.cast_one, Int.reduceNeg, sub_eq_neg_self] at h
        cases h
        all_goals {
          simp only [Polynomial.eval_mul, Polynomial.eval_sub,
                    Polynomial.eval_ofNat, mul_eq_zero]
          first | { apply Or.inr; linarith } | { apply Or.inl; linarith }
        }
      suffices 0 < r.degree by
        replace this : 0 < (r * (r - 2)).degree := by
          suffices this': r.degree ≤ (r * (r - 2)).degree from
            Trans.trans this this'
          simp only [Polynomial.degree_mul]
          suffices 0 < (r - 2).degree by
            have' := WithBot.add_lt_add_left (a := r.degree) _ this
            .
              simp_all only [add_zero, ge_iff_le]
              apply le_of_lt
              assumption
            .
              rename_i this'
              revert this'
              apply Function.mtr
              simp only [ne_eq, Polynomial.degree_eq_bot, Decidable.not_not, not_lt]
              intro this'
              rw [this']
              simp only [Polynomial.degree_zero, bot_le]
          suffices (r - 2).degree = r.degree by simp_all only
          apply Polynomial.degree_sub_C
          assumption
        generalize r * (r - 2) = p at *
        revert this
        apply Function.mtr
        intro this
        simp_all only [ne_eq, not_exists, Decidable.not_not, not_lt]
        suffices p.degree = ⊥ by rw [this]; exact bot_le
        suffices p = 0 by subst this; exact Polynomial.degree_zero
        apply Polynomial.eq_zero_of_infinite_isRoot
        simp only [Polynomial.IsRoot.def]
        simp_all only [Set.setOf_true]
        rw [Set.infinite_univ_iff]
        exact Int.infinite
      apply zero_lt_degree_word_polynomial
        <;> assumption
    suffices ∃ (k: ℕ), 1 < k ∧ Polynomial.eval b0 r = (1: ZMod k) by
      obtain ⟨k, ⟨one_lt_k, hk⟩⟩ := this
      exists k
      simp_all only [ne_eq, true_and]
      let M: Magma (ZMod k) := Magma.mk fun u v => (1 - b0) * u + b0 * v
      exists Magma.mk fun u v => (1 - b0) * u + b0 * v
      intro f
      simp only [satisfiesPhi]
      let g1 : Fin 2 → ZMod k := fun z => if z = 0 then f 0 - f 1 else 0
      let g2 : Fin 2 → ZMod k := fun z => if z = 0 then f 1 else f 1
      exact by symm; calc w ⬝ f
        _ = (w ⬝ g1) + (w ⬝ g2) := by
          clear * -
          simp only [Fin.isValue, ite_self, FreeMagma.evalInMagma, g1, g2]
          induction w
            <;> simp only [FreeMagma.evalInMagma, Fin.isValue]
          .
            rename_i z
            fin_cases z
              <;> simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, sub_add_cancel,
                              Fin.mk_one, one_ne_zero, zero_add]
          .
            rename_i w1 w2 h1 h2
            simp only [h1, h2, Magma.op, Fin.isValue]
            ring_nf
        _ = (Polynomial.eval b0 r) * g1 0 + (w ⬝ g2) := by
          congr
          simp only [Fin.isValue, r, g1, ite_true]
          generalize f 0 - f 1 = u at *
          clear_value r
          clear * -
          induction w
            <;> simp only [FreeMagma.evalInMagma, Magma.op, word_polynomial]
          .
            rename_i z
            fin_cases z
              <;> simp_all only [Fin.zero_eta, ite_true, CharP.cast_eq_zero,
                                sub_zero, Polynomial.eval_one, Int.cast_one, one_mul, Fin.mk_one,
                                one_ne_zero, ite_false, Nat.cast_one, sub_self, Polynomial.eval_zero,
                                Int.cast_zero, zero_mul]
          .
            rename_i w1 w2 h1 h2
            simp only [h1,
                      h2,
                      ←mul_assoc (c := u),
                      ←right_distrib (c := u),
                      ←Int.coe_castRingHom,
                      ←RingHom.map_add,
                      ←RingHom.map_mul]
            simp only [Int.coe_castRingHom, Polynomial.eval_add,
                        Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
                        Polynomial.eval_X]
            simp_all only [Fin.isValue, Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_one]
        _ = (Polynomial.eval b0 r) * (f 0 - f 1) + (w ⬝ g2) := by
          simp_all only [ne_eq, Int.natAbs_eq_zero, ite_true, g1]
        _ = f 0 - f 1 + (w ⬝ g2) := by
          congr
          rw [hk]
          ring_nf
        _ = f 0 - f 1 + f 1 := by
          congr
          clear * -
          simp only [FreeMagma.evalInMagma, g2, if_true]
          induction w
          .
            rename_i z
            fin_cases z
              <;> simp only [FreeMagma.evalInMagma, Fin.zero_eta, Fin.isValue,
                            ↓reduceIte, Fin.mk_one, Fin.isValue, one_ne_zero]
          .
            rename_i w1 w2 h1 h2
            simp only [FreeMagma.evalInMagma, Magma.op, h1, h2, mul_sub_right_distrib]
            ring_nf
        _ = f 0 := by
          simp_all only [ne_eq, Int.natAbs_eq_zero, ite_true, ite_self,
                        sub_add_cancel, g1, g2]
    by_cases (Polynomial.eval b0 r - 1).natAbs = 0
    .
      exists 2
      simp only [Nat.one_lt_ofNat, Fin.isValue, true_and]
      apply eq_of_sub_eq_zero
      rw [←Int.cast_one]
      simp only [←Int.coe_castRingHom, ←RingHom.map_sub]
      simp only [Int.coe_castRingHom]
      rw [←Int.cast_zero]
      simp only [ZMod.intCast_eq_intCast_iff']
      norm_num
      rename_i h
      simp_all only [ne_eq, zero_ne_one, not_false_eq_true, Int.natAbs_eq_zero, Int.zero_emod]
    .
      let k: ℕ := (Polynomial.eval b0 r - 1).natAbs
      exists k
      split_ands
      . omega
      apply eq_of_sub_eq_zero
      rw [←Int.cast_one]
      simp only [←Int.coe_castRingHom, ←RingHom.map_sub]
      simp only [Int.coe_castRingHom]
      rw [←Int.cast_zero]
      simp only [ZMod.intCast_eq_intCast_iff']
      norm_num
      simp only [k, ←Int.dvd_iff_emod_eq_zero, Int.natAbs_dvd, dvd_refl]

end InfModel
