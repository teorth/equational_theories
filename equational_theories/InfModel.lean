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
import Mathlib.Algebra.Polynomial.RingDivision

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

theorem Finite.two_variables_laws {α: Type} [ht : Fintype α] (hc : Fintype.card α = 2) (E: Law.MagmaLaw α)
  (hE: ∃ (z: α), FreeMagma.Mem z E.rhs ∧ FreeMagma.Mem z E.lhs) :
  ∃ (G : Type) (hm : Magma G) (hf : Finite G), G ⊧ E ∧ ¬Equation2 G := by
  revert E
  suffices hs: ∀ (x: α) (w: FreeMagma α), (hE: FreeMagma.Mem x w) → ∃ (G: Type) (hm: Magma G) (hf: Finite G), G ⊧ (Lf x ≃ w) ∧ ¬Equation2 G by
    -- an arbitrary magma with at least 2 elements satisfying the constant law
    let G := Fin 2
    let M: Magma G := Magma.mk fun x y => 0
    let hf: Finite G := Finite.of_fintype G
    have hneq2: ¬Equation2 G := by
      unfold Equation2
      simp only [not_forall]
      exists 0, 1
      simp only [zero_ne_one, not_false_eq_true]
    intro E hE
    match E with
    | ⟨FreeMagma.Fork w1 w2, FreeMagma.Fork w3 w4⟩ =>
      exists G, M, hf
      split_ands
      .
        intro f
        unfold satisfiesPhi FreeMagma.evalInMagma
        rfl
      .
        exact hneq2
    | ⟨FreeMagma.Leaf a, FreeMagma.Leaf b⟩ =>
      by_cases h: a = b
      .
        rw [h]
        exists G, M, hf
        split_ands
        .
          intro f
          unfold satisfiesPhi FreeMagma.evalInMagma
          rfl
        .
          exact hneq2
      .
        obtain ⟨z, ⟨hz1, hz2⟩⟩ := hE
        simp only [Law.MagmaLaw, FreeMagma.Mem] at hz1 hz2
        rw [hz2] at hz1
        contradiction
    | ⟨w ⋆ w', FreeMagma.Leaf x⟩ =>
      obtain ⟨z, ⟨hz1, hz2⟩⟩ := hE
      simp only [Law.MagmaLaw] at hz1 hz2
      simp only [FreeMagma.Mem] at hz1
      rw [hz1] at hz2
      obtain ⟨G, ⟨M, ⟨hf, h⟩⟩⟩ := hs x (w ⋆ w') hz2
      exists G, M, hf
      simp only [h, Law.satisfies_symm, not_false_eq_true, and_self]
    | ⟨FreeMagma.Leaf x, w ⋆ w'⟩ =>
      apply hs x (w ⋆ w')
      obtain ⟨z, ⟨hz1, hz2⟩⟩ := hE
      simp_all only [not_forall, exists_and_left, exists_prop, exists_and_right, FreeMagma.Mem, exists_eq_right]
  intros x w hw
  by_cases h: w.first = x ∨ w.last = x
  .
    clear * - h
    let G := Fin 2
    exists G
    suffices hs: ∃ (hm: Magma G), ∀ (f: α → G), f x = w ⬝ f by
      clear h
      obtain ⟨hm, h⟩ := hs
      exists hm, Finite.of_fintype G
      refine' And.intro h _
      unfold Equation2
      simp only [not_forall]
      exists 0, 1
    cases h with
    | inl h =>
      exists Magma.mk fun x y => x
      intro f
      subst h
      induction w
        <;> first | rfl | assumption
    | inr h =>
      exists Magma.mk fun x y => y
      intro f
      subst h
      induction w
        <;> first | rfl | assumption
  .
    revert α
    suffices h: ∀ (w : FreeMagma (Fin 2)), w.first ≠ 0 ∧ w.last ≠ 0 → FreeMagma.Mem 0 w → ∃ (G : Type) (M : Magma G) (hf: Finite G), G ⊧ (Lf 0 ≃ w) ∧ ¬Equation2 G by
      intros α ht hc x w hw h'
      replace h': w.first ≠ x ∧ w.last ≠ x := by
        simp_all only [ne_eq, not_forall, exists_and_left, exists_prop, exists_and_right, and_imp, not_or, not_false_eq_true, and_self]
      have : ∃ (π: α ≃ Fin 2), π.toFun x = 0 := by
        have π0 := Fintype.equivFin α
        rw [hc] at π0
        letI := Classical.decEq α
        let y := if π0.invFun 0 = x then π0.invFun 1 else π0.invFun 0
        let πfwd: α → Fin 2 := fun z => if z = x then 0 else 1
        let πinv: Fin 2 → α := fun z => if z = 0 then x else y
        have : Function.LeftInverse πinv πfwd := by
          simp only [πfwd, πinv]
          simp only [Function.LeftInverse]
          intro z
          simp only [Fin.isValue, ite_eq_left_iff, one_ne_zero, imp_false, Decidable.not_not]
          rw [(by simp_all only [Fin.isValue, ne_eq, not_forall, exists_and_left, exists_prop, exists_and_right, and_imp, Equiv.toFun_as_coe, Equiv.invFun_as_coe, Equiv.symm_apply_apply]
              : z = π0.invFun (π0.toFun z))]
          generalize π0.toFun z = l
          fin_cases l
          simp_all only [Fin.isValue, ne_eq, not_forall, exists_and_left, exists_prop, exists_and_right, and_imp, Fin.zero_eta, Equiv.invFun_as_coe, ↓reduceIte, ite_eq_right_iff, implies_true, y]
          simp_all only [Fin.isValue, ne_eq, not_forall, exists_and_left, exists_prop, exists_and_right, and_imp, Fin.zero_eta, Equiv.invFun_as_coe, ↓reduceIte, ite_eq_right_iff, implies_true, y]
          simp_all only [Fin.isValue, Fin.mk_one]
          obtain ⟨left, right⟩ := h'
          split
          next h_1 =>
            subst h_1
            simp_all only [Fin.isValue]
          next
            h_1 =>
            simp_all only [Fin.isValue, ite_eq_left_iff, EmbeddingLike.apply_eq_iff_eq, zero_ne_one, imp_false, Decidable.not_not]
            rw [(by simp_all only [Fin.isValue, ne_eq, not_forall, exists_and_left, exists_prop, exists_and_right, and_imp, Equiv.toFun_as_coe, Equiv.invFun_as_coe, Equiv.symm_apply_apply]
                : x = π0.invFun (π0.toFun x))] at *
            generalize π0.toFun x = m at *
            fin_cases m
            simp_all only [Fin.isValue, Fin.zero_eta, Equiv.invFun_as_coe, EmbeddingLike.apply_eq_iff_eq,
              one_ne_zero, not_false_eq_true]
            simp_all only [Fin.isValue, Fin.mk_one, Equiv.invFun_as_coe, not_true_eq_false]
        have this' : Function.RightInverse πinv πfwd  := by
          have := Function.LeftInverse.injective this
          have : Function.Surjective πfwd := by
            apply Function.Injective.surjective_of_fintype
            .
              simp_all only [Fin.isValue, ne_eq, not_forall, exists_and_left, exists_prop, exists_and_right, and_imp,
                Equiv.invFun_as_coe, πinv, y, πfwd]
              obtain ⟨left, right⟩ := h'
              exact π0
            .
              simp_all only [Fin.isValue, ne_eq, not_forall, exists_and_left, exists_prop, exists_and_right, and_imp, Equiv.invFun_as_coe, πinv, y, πfwd]
          apply Function.LeftInverse.rightInverse_of_surjective
          assumption
          assumption
        let π: α ≃ Fin 2 := Equiv.mk
          πfwd
          πinv
          this
          this'
        exists π
        simp only [π, ite_true, πfwd]
      obtain ⟨π, hπ⟩ := this
      let w': FreeMagma (Fin 2) := FreeMagma.evalInMagma (fun z => FreeMagma.Leaf (π.toFun z)) w
      have : w'.first ≠ 0 ∧ w'.last ≠ 0 := by
        have : w'.first = π.toFun w.first := by
          clear h'
          induction w
          .
            simp_all only [ne_eq, not_forall, exists_and_left, exists_prop, exists_and_right, and_imp, FreeMagma.first, Equiv.toFun_as_coe]
          .
            rename_i w1 w2 h1 h2
            simp_all only [ne_eq, not_forall, exists_and_left, exists_prop, exists_and_right, and_imp, Equiv.toFun_as_coe, FreeMagma.first]
            sorry
        rw [this]
          ; clear this
        have : w'.last = π.toFun w.last := by
          clear h'
          induction w
          .
            simp only [ne_eq, not_forall, exists_and_left, exists_prop, exists_and_right, and_imp, FreeMagma.last, Equiv.toFun_as_coe]
          .
            rename_i w1 w2 h1 h2
            simp_all [FreeMagma.last]
            sorry
        rw [this]
          ; clear this
        obtain ⟨h1, h2⟩ := h'
        apply_fun π.invFun at hπ
        simp only [Equiv.toFun_as_coe, Equiv.invFun_as_coe, Equiv.symm_apply_apply, Fin.isValue] at hπ
        split_ands
        .
          intro hct
          apply_fun π.invFun at hct
          simp only [Equiv.toFun_as_coe, Equiv.invFun_as_coe, Equiv.symm_apply_apply, Fin.isValue] at hct
          rw [←hπ] at hct
          contradiction
        .
          intro hct
          apply_fun π.invFun at hct
          simp only [Equiv.toFun_as_coe, Equiv.invFun_as_coe, Equiv.symm_apply_apply, Fin.isValue] at hct
          rw [←hπ] at hct
          contradiction
      obtain ⟨G, ⟨M, ⟨hf, ⟨h1, h2⟩⟩⟩⟩ := h w' this sorry
      exists G, M, hf
      split_ands
      .
        clear * - h1 hπ
        intro f
        replace h1 := h1 (f ∘ π.invFun)
        simp only [satisfiesPhi, w', ←hπ] at *
          ; clear w'
        simp only [FreeMagma.evalInMagma] at *
        simp only [Function.comp] at *
        conv at h1 =>
          lhs
          simp only [Equiv.toFun_as_coe, Equiv.invFun_as_coe, Equiv.symm_apply_apply]
        rw [h1]
          ; clear h1
        induction w
        .
          rename_i z
          simp only [FreeMagma.evalInMagma, Equiv.invFun_as_coe, Equiv.toFun_as_coe, Function.comp_apply, Equiv.symm_apply_apply]
        .
          rename_i w1 w2 h1 h2
          simp [FreeMagma.evalInMagma]
          simp_all only [Equiv.invFun_as_coe, Equiv.toFun_as_coe]
      .
        assumption
    intro w h
    obtain ⟨hl, hr⟩ := h
    let MPols: Magma (Polynomial ℤ) := Magma.mk fun x y => (1 - Polynomial.X) * x + Polynomial.X * y
    let fPols: Fin 2 → Polynomial ℤ := fun z => if z = 0 then 1 else 0
    let r: Polynomial ℤ := FreeMagma.evalInMagma fPols w
    have geq_deg_r_one : r.degree ≥ 1 := sorry
    let n := r.natDegree
    have : ∃ (b0: ℤ), Polynomial.eval b0 (r * (r - 2)) ≠ 0 := by
      have hrd : r.natDegree ≥ 1 := by
        simp_all only [ne_eq, ge_iff_le, Nat.succ_le, Nat.WithBot.one_le_iff_zero_lt, Polynomial.natDegree_pos_iff_degree_pos]
      have eq_deg_r_nat_deg_r : r.degree = ↑r.natDegree := by
        apply Polynomial.degree_eq_natDegree
        simp_all only [Fin.isValue, ne_eq, ge_iff_le, le_max_iff, gt_iff_lt, r, MPols, fPols]
        intro a
        simp_all only [Fin.isValue, Polynomial.natDegree_zero, nonpos_iff_eq_zero, one_ne_zero]
      let r' := r * (r - 2)
      have hr2r : (r - 2).natDegree = r.natDegree := by
        have : (r - 2).natDegree ≤ r.natDegree := by
          have := Polynomial.degree_sub_le r 2
          have this' := Polynomial.degree_C (a := -2)
          simp at this'
          simp only [this'] at this
          have this2 : r.degree ≥ 1 := by
            rw [eq_deg_r_nat_deg_r]
            simp_all only [Fin.isValue, ne_eq, ge_iff_le, Nat.cast_nonneg, max_eq_left, Nat.one_le_cast, r, MPols, fPols]
          simp only [ge_iff_le] at this2
          have this3 : max r.degree 0 = r.degree := by
            simp only [max, Sup.sup]
            cases h: r.degree
            .
              rw [h] at this2
              contradiction
            .
              simp only [zero_le, max_eq_left]
          rw [this3] at this
          suffices (r - 2).degree ≤ r.degree by
            apply Polynomial.natDegree_le_natDegree
            assumption
          assumption
        have : (r - 2).natDegree ≥ r.natDegree := by
          have : (r - 2).coeff (r.natDegree) = r.coeff (r.natDegree) := by
            simp_all only [ne_eq, ge_iff_le, Polynomial.coeff_sub, Polynomial.coeff_natDegree, sub_eq_self]
            apply Polynomial.coeff_C_ne_zero
            simp_all only [Fin.isValue, ne_eq, r, MPols, fPols]
            intro a
            simp_all only [Fin.isValue, nonpos_iff_eq_zero, one_ne_zero]
          suffices (r - 2).coeff (r.natDegree) ≠ 0 by
            simp_all only [ne_eq, ge_iff_le, Polynomial.coeff_sub, Polynomial.coeff_natDegree, sub_eq_self, sub_zero, Polynomial.leadingCoeff_eq_zero]
            apply Polynomial.le_natDegree_of_ne_zero
            simp_all only [Polynomial.coeff_sub, Polynomial.coeff_natDegree, sub_zero, ne_eq, Polynomial.leadingCoeff_eq_zero, not_false_eq_true]
          simp_all only [Fin.isValue, ne_eq, ge_iff_le, Polynomial.coeff_sub, Polynomial.coeff_natDegree, sub_eq_self, sub_zero, Polynomial.leadingCoeff_eq_zero, r, MPols, fPols]
          apply Aesop.BuiltinRules.not_intro
          intro a
          simp_all only [Fin.isValue, Polynomial.natDegree_zero, nonpos_iff_eq_zero, one_ne_zero]
        apply Nat.le_antisymm
          <;> assumption
      have : r' ≠ 0 := by
        intro hct
        apply_fun (fun x => x.degree) at hct
        simp only [Polynomial.degree_zero, r', Polynomial.degree_mul, WithBot.add_eq_bot] at hct
        cases hct with
        | inl hct =>
          have : r.natDegree = 0 := by
            simp only [Polynomial.natDegree]
            rw [hct]
            norm_num
          rw [this] at hrd
          contradiction
        | inr hct =>
          have : (r - 2).natDegree = 0 := by
            simp only [Polynomial.natDegree]
            rw [hct]
            norm_num
          rw [hr2r] at this
          rw [this] at hrd
          contradiction
      have := Polynomial.exists_multiset_roots this
      obtain ⟨s, hs⟩ := this
      have : r'.natDegree = 2 * n := by
        simp only [Polynomial.natDegree]
        have : (r - 2).degree = r.degree := sorry
        have this' : r.degree + r.degree = some (2 * r.natDegree) := sorry
        simp only [r', Polynomial.degree_mul, this, this', WithBot.unbot', WithBot.recBotCoe]
        simp only [id_eq]
      obtain ⟨hs1, hs2⟩ := hs
      have : ∃ (b0: ℤ), b0 ∉ s := sorry
      obtain ⟨b0, hb0⟩ := this
      have : Multiset.count b0 s = 0 := by
        apply Multiset.count_eq_zero_of_not_mem
        assumption
      have : Polynomial.rootMultiplicity b0 r' = 0 := by
        simp only [←hs2]
        assumption
      have : Polynomial.eval b0 r' ≠ 0 := by
        simp only [Polynomial.rootMultiplicity_eq_zero_iff, Polynomial.IsRoot.def] at this
        intro h
        have := this h
        contradiction
      simp only [r'] at this
      exists b0
    obtain ⟨b0, h0⟩ := this
    let k: Nat := (Polynomial.eval (b0: ℤ) r - 1).natAbs
    let a0: ℤ := 1 - b0
    let M: Magma (ZMod k) := Magma.mk fun u v => a0 * u + b0 * v
    have hf: Finite (ZMod k) := by
      have : k ≠ 0 := sorry
      have : ZMod k = Fin k := by
        unfold ZMod
        simp_all only [Fin.isValue, ne_eq, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_ofNat, mul_eq_zero, not_or, Int.natAbs_eq_zero, r, MPols, fPols, k]
        obtain ⟨left, right⟩ := h0
        split
        next x heq => simp_all only [Fin.isValue, Int.natAbs_eq_zero]
        next x n_1 heq => simp_all only [Fin.isValue, Nat.succ_eq_add_one]
      rw [this]
      apply Finite.intro
      rfl
    intro hw
    exists ZMod k, M, hf
    let eval_eq: FreeMagma (Fin 2) → ZMod k → ZMod k → ZMod k := fun w u v => w ⬝ (fun z => if z = 0 then u else v)
    split_ands
    rotate_right
    .
      simp only [not_forall]
      exists 0, 1
      have : k ≠ 1 := by
        simp only [k]
        intro h
        have := Int.natAbs_eq (Polynomial.eval b0 r - 1)
        simp only [h] at this
        cases this with
        | inl h =>
          apply_fun (fun x => x - 1) at h
          simp only [Int.sub_sub] at h
          norm_num at h
          apply h0
          simp_all only [Fin.isValue, ne_eq, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_ofNat, mul_zero, not_true_eq_false, r, MPols, fPols]
        | inr h =>
          apply_fun (fun x => x + 1) at h
          norm_num at h
          apply h0
          simp_all only [Fin.isValue, ne_eq, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_ofNat, zero_sub, Int.reduceNeg, mul_neg, zero_mul, neg_zero, not_true_eq_false, r, MPols, fPols]
      intro h
      apply_fun (fun x => x.val) at h
      rw [ZMod.val_one'' this] at h
      simp only [ZMod.val_zero, zero_ne_one] at h
    .
      intro f
      unfold satisfiesPhi
        ; simp only
      conv =>
        lhs
        unfold FreeMagma.evalInMagma
      have : w ⬝ f = eval_eq w (f 0) (f 1) := by
        unfold eval_eq
        have : ∀ (f g: Fin 2 → ZMod k), f = g → w ⬝ f = w ⬝ g := by
          simp only [forall_eq', implies_true]
        apply this
        funext z
        fin_cases z
          <;> simp_all only [M, eval_eq, Fin.isValue, ne_eq, ge_iff_le, ite_self, sub_add_cancel, Fin.zero_eta, ↓reduceIte, Fin.mk_one, one_ne_zero]
      rw [this]
        ; clear this
      have : ∀ (u v), eval_eq w u v = eval_eq w (u - v) 0 + eval_eq w v v := by
        intro u v
        clear_value k
        clear * -
        simp only [eval_eq]
        induction w
        .
          rename_i z
          unfold FreeMagma.evalInMagma
          fin_cases z
          .
            simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, sub_add_cancel]
          .
            simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, zero_add]
        .
          rename_i w1 w2 h1 h2
          unfold FreeMagma.evalInMagma
          rw [h1, h2]
          unfold Magma.op
          ring_nf
      rw [this]
        ; clear this
      have : ∀ u, eval_eq w u 0 = (Polynomial.eval b0 r) * u := by
        intro u
        simp only [eval_eq, r, fPols]
        clear_value r
        clear * -
        induction w
        .
          simp only [FreeMagma.evalInMagma]
          split_ifs
            <;> simp only [Polynomial.eval_zero, Polynomial.eval_one]
            <;> ring_nf
        .
          rename_i w1 w2 h1 h2
          simp only [FreeMagma.evalInMagma,
                    Magma.op,
                    h1,
                    h2,
                     ←mul_assoc (c := u),
                     ←right_distrib (c := u),
                     ←Int.coe_castRingHom,
                     ←RingHom.map_add,
                     ←RingHom.map_mul]
          simp only [Int.coe_castRingHom, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]
      rw [this]
        ; clear this
      have : (Polynomial.eval b0 r) = (1: ZMod k) := by
        apply eq_of_sub_eq_zero
        rw [←Int.cast_one]
        simp only [←Int.coe_castRingHom, ←RingHom.map_sub]
        simp only [Int.coe_castRingHom]
        rw [←Int.cast_zero]
        simp only [ZMod.intCast_eq_intCast_iff']
        norm_num
        simp only [k, ←Int.dvd_iff_emod_eq_zero, Int.natAbs_dvd, dvd_refl]
      rw [this]
        ; clear this
        ; ring_nf
      have : ∀ u, eval_eq w u u = u := by
        intro u
        clear_value k
        clear * -
        simp only [eval_eq]
        induction w
        .
          rename_i z
          fin_cases z
            <;> simp only [FreeMagma.evalInMagma, Fin.zero_eta, Fin.isValue, ↓reduceIte, Fin.mk_one, Fin.isValue, one_ne_zero]
        .
          rename_i w1 w2 h1 h2
          simp only [FreeMagma.evalInMagma, Magma.op, h1, h2, a0]
          zify
          ring_nf
      rw [this]
        ; clear this
      ring_nf

end InfModel
