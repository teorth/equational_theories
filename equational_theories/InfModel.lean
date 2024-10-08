import equational_theories.Equations
import equational_theories.AllEquations
import equational_theories.MagmaLaw
import equational_theories.SmallMagmas
import Mathlib.Data.Fintype.Card
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import equational_theories.ForMathlib.Algebra.Group.Nat

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
    have : Function.RightInverse f g := by
      intro x
      simp [f, g, ← h]
    intro z u
    apply this.injective
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
      apply one_lt_pow₀ (by simp) (by simp)
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
    have f_inj : ∀ y : G, Function.Injective (f y) :=by
      intro y
      exact Finite.injective_iff_surjective.mpr (f_onto y)
    have hh: ∀ y z w : G, z ◇ y = w ◇ y := by
      intro y z w
      let g := f y
      have h1 : g (y ◇ (y ◇ (x ◇ (z ◇ y)))) = g (y ◇ (y ◇ (x ◇ (w ◇ y)))):= by dsimp [g, f]; rw [← h, ← h]
      have h2 : g (y ◇ (x ◇ (z ◇ y))) = g (y ◇ (x ◇ (w ◇ y))) := by
        dsimp [g, f]
        exact f_inj y h1
      have h3 : g (x ◇ (z ◇ y)) = g (x ◇ (w ◇ y)) := by
        dsimp [g, f]
        exact f_inj y h2
      have h4 : f x (z ◇ y) = f x (w ◇ y) := by
        dsimp [f]
        exact f_inj y h3
      exact f_inj x h4
    have hhh : ∀ a b c d: G, c ◇ (a ◇ b) = d ◇ (a ◇ b) := by
      intro a b c d
      exact hh (a ◇ b) c d
    have hhhh : ∀ a b: G, b ◇ (b ◇ (b ◇ (x ◇ (a ◇ b)))) = b ◇ (b ◇ (b ◇ (y ◇ (a ◇ b)))) := by
      intro a b
      rw [hhh a b _ _]
    calc
      x = x ◇ (x ◇ (x ◇ (x ◇ (x ◇ x)))) := by exact h x x x
      _= x ◇ (x ◇ (x ◇ (y ◇ (x ◇ x)))) := by rw [hhhh]
      _= y := by rw [←  h y x x]

theorem Finite.Equation28770_implies_Equation2 (G : Type*) [Magma G] [Finite G] (h : Equation28770 G) :
    Equation2 G := by
    have : ∀ (y z u : G), y ◇ z = y ◇ u := by
      intro y
      let f (x : G) := ((y ◇ y) ◇ y) ◇ x
      let g (x : G) := x ◇ (y ◇ y)
      have : Function.RightInverse f g := by
        intro x
        simp [f, g, ← h]
      intro z u
      apply this.injective
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
    simp only [ite_true]
  have h2 : ∀ (y: ℕ+), (2^y.val) ◇ y = 3^y.val := by
    intro y
    unfold Magma.op
    simp [t1]
  have h3 : ∀ (x y: ℕ+), x ≠ 3^y.val → (3^y.val) ◇ x = 3^y.val * 5^x.val := by
    intro x y hxy
    unfold Magma.op
    simp
    rw [if_neg]
    case hnc =>
      intro h''
      apply hxy
      simp [h'']
    simp
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
    simp
    rw [if_neg]
    case hnc =>
        intro h'
        apply hxyz
        simp [h']
    rw [if_neg]
    case hnc =>
      apply_fun PNat.val
      simp [PNat.pow_coe, PNat.val_ofNat, ne_eq]
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
    case hc =>
      simp [padicValNat.mul, padicValNat_prime_prime_pow]
    simp [this, Subtype.ext_iff, padicValNat.mul, padicValNat_prime_prime_pow]
  have h5 : ∀ (y z: ℕ+), z ≠ 3^y.val ∧ z ≠ 2^(3^y.val) → (2^(3^y.val)) ◇ z = 3^y.val := by
    intro y z hyz
    unfold Magma.op
    simp
    rw [if_neg, if_neg, if_neg, if_neg]
    .
      intro hc
      apply PNat.ne_zero ((3: ℕ+)^y.val)
      calc ↑((3: ℕ+)^y.val)
        _ = padicValNat 2 ↑(2^3^y.val: ℕ+) := by simp
        _ = padicValNat 2 _ := by rw [hc]
        _ = 0 := by simp [padicValNat_prime_prime_pow]
    .
      intro hc
      apply PNat.ne_zero ((3: ℕ+)^y.val)
      calc ↑((3: ℕ+)^y.val)
        _ = padicValNat 2 ↑(2^3^y.val: ℕ+) := by simp
        _ = padicValNat 2 _ := by rw [hc]
        _ = 0 := by simp [padicValNat_prime_prime_pow]
    .
      intro hc
      apply hyz.1
      calc z
        _ = z.val.toPNat' := by simp
        _ = (padicValNat 2 (2^z.val: ℕ+)).toPNat' := by simp
        _ = (padicValNat 2 ↑(2^3^y.val: ℕ+)).toPNat' := by rw [←hc]
        _ = (3^y.val: ℕ).toPNat' := by simp
        _ = 3^↑y := by rw [←PNat.coe_inj]; simp
    .
      intro hc
      apply hyz.2
      simp [hc]
  rw [h1, h2]
  by_cases hx : x = 3^y.val
  .
    rw [hx, h1]
    by_cases hyz : y ◇ z = 2^(3^y.val)
    .
      simp [hyz, h1]
      exfalso
      have : padicValNat 2 ↑(y ◇ z) = ↑(3^y.val) := by simp [hyz]
      unfold Magma.op at this
      simp at this
      repeat rw [apply_ite PNat.val] at this
      repeat rw [apply_ite (padicValNat 2)] at this
      simp only [PNat.pow_coe, PNat.val_ofNat] at this
      simp only [padicValNat.prime_pow] at this
      simp [padicValNat_prime_prime_pow] at this
      repeat rw [apply_ite (padicValNat 2)] at this
      simp [padicValNat.mul, padicValNat_prime_prime_pow] at this
      repeat simp only [ite_eq_iff] at this
      simp at this
      have this' : (0: ℕ) = (3: ℕ)^y.val ↔ False := by
        apply Iff.intro
        .
          simp
          intro h
          apply pow_ne_zero y.val (by simp: 3 ≠ 0)
          simp [h]
        .
          intro h
          contradiction
      simp [this'] at this
      repeat simp [and_or_left, and_or_left] at this
      cases this with
      | inl h =>
        rw [h.1] at h
        simp at h
        have this2 := Nat.lt_pow_self (by simp: 1 < 3) z.val
        have this3 := ne_of_gt this2
        exact this3 (Eq.symm h)
      | inr this => _
      cases this with
      | inl h =>
        have h1 := h.2.2.1
        have h2 := h.2.2.2
        rw [h1] at h2
        simp at h2
        simp [padicValNat_prime_prime_pow] at h2
        have h2 := Eq.symm h2
        have := pow_ne_zero (3^padicValNat 3 y.val) (by simp: 3 ≠ 0)
        apply pow_ne_zero y.val (by simp: 3 ≠ 0)
        contradiction
      | inr this => _
      have this' := this.2.2.2.2.2
      apply_fun padicValNat 3 at this'
      simp [padicValNat.prime_pow] at this'
      have this' := Eq.symm this'
      have this2 := calc y.val
        _ > Nat.log 5 y.val := by simp [Nat.log_lt_self]
        _ ≥ padicValNat 5 y.val := by simp [padicValNat_le_nat_log]
        _ ≥ Nat.log 2 (padicValNat 5 y.val) := by simp [Nat.log_le_self]
        _ ≥ padicValNat 2 (padicValNat 5 y.val) := by simp [padicValNat_le_nat_log]
        _ ≥ Nat.log 3 (padicValNat 2 (padicValNat 5 y.val)) := by simp [Nat.log_le_self]
        _ ≥ padicValNat 3 (padicValNat 2 (padicValNat 5 y.val)) := by simp [padicValNat_le_nat_log]
      have this3 := ne_of_gt this2
      exact this3 this'
    .
      by_cases hyz' : y ◇ z = 3^y.val
      .
        rw [←hyz', h2, hyz']
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
          have hc := Eq.symm hc
          have hc' := PNat.ne_zero y
          contradiction
        simp [this'] at this
        repeat simp [and_or_left, and_or_left] at this
        cases this with
        | inl h =>
          have h1 := h.2.1
          have h2 := h.2.2
          rw [h2] at h1
          have h1 := Eq.symm h1
          apply_fun PNat.val at h1
          simp at h1
          have this2 := Nat.lt_pow_self (by simp: 1 < 2) y.val
          have this3 := ne_of_gt this2
          exact this3 h1
        | inr this => _
        cases this with
        | inl h =>
          have h1 := h.2.2.1
          have h2 := h.2.2.2
          rw [h2] at h1
          have h1 := Eq.symm h1
          apply_fun PNat.val at h1
          simp at h1
          have this2 := Nat.lt_pow_self (by simp: 1 < 3) y.val
          have this3 := ne_of_gt this2
          exact this3 h1
        | inr this => _
        cases this with
        | inl h =>
          have h := Eq.symm h.2.2.2.2.2
          have h' := calc y.val
            _ > Nat.log 5 y.val := by simp [Nat.log_lt_self]
            _ ≥ padicValNat 5 y.val := by simp [padicValNat_le_nat_log]
            _ ≥ Nat.log 3 (padicValNat 5 y.val) := by simp [Nat.log_le_self]
            _ ≥ padicValNat 3 (padicValNat 5 y.val) := by simp [padicValNat_le_nat_log]
          exact (ne_of_gt h') h
        | inr this => _
        have this := Eq.symm this.2.2.2.2.2
        have this' := calc y.val
          _ > Nat.log 2 y.val := by simp [Nat.log_lt_self]
          _ ≥ padicValNat 2 y.val := by simp [padicValNat_le_nat_log]
          _ ≥ Nat.log 3 (padicValNat 2 y.val) := by simp [Nat.log_le_self]
          _ ≥ padicValNat 3 (padicValNat 2 y.val) := by simp [padicValNat_le_nat_log]
        exact (ne_of_gt this') this
      .
        have : (y ◇ z) ≠ 3^y.val ∧ (y ◇ z) ≠ 2^(3^y.val)  := And.intro hyz' hyz
        simp [h5 y (y ◇ z) this]
  .
    rw [h3 x y hx]
    by_cases hyz : y ◇ z = 3^y.val * 5^x.val
    .
      rw [hyz, h1]
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
        have h' := Eq.symm h.2
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
        have this2 := Nat.lt_pow_self (by simp: 1 < 3) (padicValNat 3 y.val)
        have this2 := ne_of_gt this2
        exact this2 (Eq.symm h')
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
            _ ≥ 3 ^ (5 ^ padicValNat 5 y.val) := by apply le_self_pow; simp [one_le_pow₀]; apply pow_ne_zero; simp
            _ > 5 ^ padicValNat 5 y.val := by simp [Nat.lt_pow_self (by simp: 1 < 3)]
            _ > padicValNat 5 y.val := by simp [Nat.lt_pow_self (by simp: 1 < 5)]
          exact (ne_of_gt this') (Eq.symm this)
        | inr this =>
          have this := Eq.symm this.2
          apply_fun padicValNat 5 at this
          simp [padicValNat_prime_prime_pow, padicValNat.mul] at this
      | inr hyz => _
      have hyz := hyz.2
      cases hyz with
      | inl h =>
        have h := Eq.symm h.2
        apply_fun padicValNat 3 at h
        simp [padicValNat_prime_prime_pow, padicValNat.mul, Nat.pow_mul] at h
        have this' := calc y.val
          _ > Nat.log 2 y.val := by simp [Nat.log_lt_self]
          _ ≥ padicValNat 2 y.val := by simp [padicValNat_le_nat_log]
          _ ≥ Nat.log 3 (padicValNat 2 y.val) := by simp [Nat.log_le_self]
          _ ≥ padicValNat 3 (padicValNat 2 y.val) := by simp [padicValNat_le_nat_log]
        exact (ne_of_gt this') h
      | inr hyz => _
      have h := Eq.symm hyz.2
      apply_fun padicValNat 3 at h
      simp [padicValNat_prime_prime_pow, padicValNat.mul, Nat.pow_mul] at h
    .
      rw [h4 x y (y ◇ z) hyz]

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
  replace this := Set.InjOn.rightInvOn_of_leftInvOn (s := S) t2.injOn this m2 m1
  apply (this _).symm
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
Dual of the above, obtained by swapping x and y in the proof.
TODO: find a way to avoid this kind of code duplication.
-/
@[equational_result]
theorem Equation3588_not_implies_Equation3944 : ∃ (G : Type) (_ : Magma G), Equation3588 G ∧ ¬ Equation3994 G := by
  let magN : Magma ℕ := ⟨fun y x ↦ if Even x ∧ Even y then x ^^^ y else if Even y then y + 2
    else if Even x then x - 2 else 0⟩
  use ℕ, magN
  have range : ∀ x y : ℕ, Even (x ◇ y : ℕ) := by
    intro x y
    simp only [magN]
    split_ifs
    · simp_all
    · simpa [Nat.even_add]
    · by_cases y < 2
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

theorem Finite.two_variables_laws {α: Type} [Fintype α] (_: Fintype.card α = 2) (E: Law.MagmaLaw α) :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), satisfies G E ∧ ¬Equation2 G := by
  match E with
  | ⟨FreeMagma.Fork _ _, FreeMagma.Fork _ _⟩ =>
    -- an arbitrary magma with at least 2 elements satisfying the constant law
    let G := Fin 2
    let _: Magma G := Magma2a
    exists G, Magma2a, Finite.of_fintype G
    split_ands
    .
      intro f
      unfold satisfiesPhi FreeMagma.evalInMagma Magma.op Magma2a MemeFinOp.opOfTable
      simp only [Nat.zero_div, Nat.zero_mod, Fin.zero_eta, Fin.isValue]
    .
      unfold Equation2
      simp only [not_forall]
      exists 0, 1
      simp only [Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, not_false_eq_true, G]
  | _ => sorry

end InfModel
