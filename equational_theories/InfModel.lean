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

theorem Finite.two_variables_laws {α: Type} [ht : Fintype α] (hc : Fintype.card α = 2) (E: Law.MagmaLaw α) :
  ∃ (G : Type) (hm : Magma G) (hf : Finite G), G ⊧ E ∧ ¬Equation2 G := by
  revert E
  suffices hs: ∀ (x: α) (w: FreeMagma α), ∃ (G: Type) (hm: Magma G) (hf: Finite G), G ⊧ (Lf x ≃ w) ∧ ¬Equation2 G by
    -- an arbitrary magma with at least 2 elements satisfying the constant law
    let G := Fin 2
    let M: Magma G := Magma.mk fun x y => 0
    let hf: Finite G := Finite.of_fintype G
    let hneq2: ¬Equation2 G := by
      unfold Equation2
      simp only [not_forall]
      exists 0, 1
    intro E
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
        sorry
    | ⟨w ⋆ w', FreeMagma.Leaf x⟩ =>
      obtain ⟨G, ⟨M, ⟨hf, h⟩⟩⟩ := hs x (w ⋆ w')
      exists G, M, hf
      simp only [h, Law.satisfies_symm, not_false_eq_true, and_self]
    | ⟨FreeMagma.Leaf x, w ⋆ w'⟩ =>
      exact hs x (w ⋆ w')
  intros x w
  by_cases h: w.first = x ∨ w.last = x
  .
    clear ht hc
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
    by_cases h': ∃ (y: α), w = (y ⋆ x) ⋆ y
    .
      obtain ⟨y, h'⟩ := h'
      let G := Fin 3
      let M: Magma G := Magma.mk fun x y => (2 * x + 2 * y) % 3
      let hf: Finite G := Finite.of_fintype G
      exists G, M, hf
      split_ands
      .
        rw [h']
        intro f
        unfold satisfiesPhi
        repeat unfold FreeMagma.evalInMagma
        unfold Magma.op
        simp only [G]
        generalize hfx: f x = fx
        generalize hfy: f y = fy
        fin_cases fx
          <;> fin_cases fy
          <;> simp_all only [not_or, ne_eq, Fin.zero_eta]
          <;> clear h'
          <;> simp only [Fin.isValue, Fin.reduceMul, Fin.zero_add, Fin.reduceMod, G, Fin.mk_one, Fin.reduceAdd, Fin.reduceFinMk]
      .
        unfold Equation2
        simp only [not_forall]
        exists 0, 1
        simp_all only [Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, not_false_eq_true, G]
    .
      clear h'
      revert α
      suffices h: ∀ (w : FreeMagma (Fin 2)), w.first ≠ 0 ∧ w.last ≠ 0 → ∃ (G : Type) (M : Magma G) (hf: Finite G), G ⊧ (Lf 0 ≃ w) ∧ ¬Equation2 G by
        intros α ht hc x w h'
        replace h': w.first ≠ x ∧ w.last ≠ x := by
          simp_all only [ne_eq, not_forall, exists_and_left, exists_prop, exists_and_right, and_imp, not_or, not_false_eq_true, and_self]
        have π := Fintype.equivFin α
        let w': FreeMagma (Fin 2) := FreeMagma.evalInMagma (fun z => FreeMagma.Leaf (π.toFun z)) w
        obtain ⟨G, ⟨M, ⟨hf, ⟨h1, h2⟩⟩⟩⟩ := h w' (by
          induction w
          rename_i z
          split_ands
          simp_all only [ne_eq, not_forall, exists_and_left, exists_prop, exists_and_right, and_imp]
          simp only [FreeMagma.first, FreeMagma.last] at *
          sorry
          sorry)
        exists G, M, hf
        split_ands
        .
          sorry
        .
          assumption
      intro w h
      obtain ⟨hl, hr⟩ := h
      let MPols: Magma (Polynomial ℤ) := Magma.mk fun x y => (1 - Polynomial.X) * x + Polynomial.X * y
      let fPols: Fin 2 → Polynomial ℤ := fun z => if z = 0 then 1 else 0
      let r: Polynomial ℤ := FreeMagma.evalInMagma fPols w
      let n := r.natDegree
      have : ∃ (b0: ℤ), |Polynomial.eval b0 (r * (r - 2))| ≠ 1 := sorry
      obtain ⟨b0, h0⟩ := this
      let k: Nat := (Polynomial.eval (b0: ℤ) r - 1).natAbs
      let a0: ℤ := 1 - b0
      let M: Magma (ZMod k) := Magma.mk fun u v => a0 * u + b0 * v
      have hf: Finite (ZMod k) := by sorry
      exists ZMod k, M, hf
      let eval_eq: FreeMagma (Fin 2) → ZMod k → ZMod k → ZMod k := fun w u v => w ⬝ (fun z => if z = 0 then u else v)
      split_ands
      rotate_right
      .
        simp only [not_forall]
        exists 0, 1
        have : k ≠ 1 := sorry
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
        have : eval_eq w (f 0) (f 1) = eval_eq w (f 0 - f 1) 0 + eval_eq w (f 1) (f 1) := by
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
        have : eval_eq w (f 0 - f 1) 0 = f 0 - f 1 := by
          have : eval_eq w (f 0 - f 1) 0 = (Polynomial.eval b0 r) * (f 0 - f 1) := by
            generalize f 0 - f 1 = u
            clear * -
            unfold eval_eq
            unfold r
            unfold fPols
            clear_value r k
            clear * -
            induction w
            .
              rename_i z
              unfold FreeMagma.evalInMagma
              split
              next h =>
                subst h
                simp_all only [Polynomial.eval_one, Int.cast_one, one_mul]
              next h => simp_all only [Polynomial.eval_zero, Int.cast_zero, zero_mul]
            .
              rename_i w1 w2 h1 h2
              unfold FreeMagma.evalInMagma
              rw [h1, h2]
              unfold Magma.op
                ; simp only
              have : ∀ (n1 n2: ZMod k), n1 - n2 = 0 → n1 = n2 := by
                intro n1 n2 h
                apply_fun (fun x => x + n2) at h
                simp_all only [sub_add_cancel, zero_add]
              apply this
                ; clear this
              conv =>
                lhs
                conv =>
                  lhs
                  unfold Magma.op
                  simp only
                  conv =>
                    lhs
                    rw [←mul_assoc]
                    simp only [←Int.coe_castRingHom, ←RingHom.map_mul]
                    simp only [Int.coe_castRingHom]
                    --
                  conv =>
                    rhs
                    rw [←mul_assoc]
                    simp only [←Int.coe_castRingHom, ←RingHom.map_mul]
                    simp only [Int.coe_castRingHom]
                    --
                  simp only [←right_distrib]
                  simp only [←Int.coe_castRingHom]
                  simp only [←RingHom.map_add]
                  simp only [Int.coe_castRingHom]
                conv =>
                  rw [sub_eq_add_neg]
                  rhs
                  rw [←neg_mul]
                  --
              rw [←right_distrib]
              have : ∀ (n1 n2: ZMod k), n1 = 0 → n1 * n2 = 0 := by
                intro n1 n2 h
                rw [h]
                ring_nf
              apply this
                ; clear this
              conv =>
                lhs
                rw [←sub_eq_add_neg]
                simp only [←Int.coe_castRingHom]
                simp only [←RingHom.map_sub]
                simp only [Int.coe_castRingHom]
              have : ∀ (n1: ℤ), n1 = 0 → (n1: ZMod k) = 0 := by
                intro n1 h
                rw [h]
                simp_all only [Int.cast_sub, Int.cast_one, Fin.isValue, Int.cast_zero, M, a0, MPols]
              apply this
                ; clear this
              simp_all only [Int.cast_sub, Int.cast_one, Fin.isValue, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X, sub_self, M, a0, MPols]
          rw [this]
          have : (Polynomial.eval b0 r) = (1: ZMod k) := by
            suffices h: (Polynomial.eval b0 (r - 1)) = ((0: ℤ): ZMod k) by
              simp only [Polynomial.eval_sub, Polynomial.eval_one, Int.cast_sub, Int.cast_one, Int.cast_zero] at h
              apply_fun (fun x => x + 1) at h
              simp only [sub_add_cancel, zero_add] at h
              assumption
            rename_i this'
            clear this'
            clear * -
            simp only [ZMod.intCast_eq_intCast_iff']
            norm_num
            unfold k
            rw [←Int.abs_eq_natAbs]
            simp_all only [Fin.isValue, Int.emod_abs, Int.emod_self, r, MPols, fPols]
          rw [this]
          ring_nf
        have : eval_eq w (f 1) (f 1) = f 1 := by
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
              simp_all only [ge_iff_le, Fin.isValue, Fin.mk_one, ite_self, one_ne_zero, ↓reduceIte, eval_eq, M, a0]
          .
            rename_i w1 w2 h1 h2
            unfold FreeMagma.evalInMagma
            rw [h1, h2]
            unfold Magma.op
            ring_nf
            zify
            ring_nf
        have this2 : eval_eq w (f 0) (f 1) = f 0 := by
          simp_all only [Fin.isValue, ne_eq, ge_iff_le, ite_self, sub_add_cancel, eval_eq, M]
        have : w ⬝ f = eval_eq w (f 0) (f 1) := by
          unfold eval_eq
          have : f = (fun z => if z = 0 then f 0 else f 1) := by
            funext z
            fin_cases z
            simp_all only [Fin.isValue, ne_eq, ge_iff_le, ite_self, sub_add_cancel, Fin.zero_eta, ↓reduceIte, eval_eq, M]
            simp_all only [Fin.isValue, ne_eq, ge_iff_le, ite_self, sub_add_cancel, Fin.mk_one, one_ne_zero, ↓reduceIte, eval_eq, M]
          simp only [←this]
        rw [this]
        rw [this2]

end InfModel
