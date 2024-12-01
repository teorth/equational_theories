import equational_theories.Equations.All
import equational_theories.MagmaOp
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Units
import Mathlib.Data.Finite.Prod
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith

namespace FiniteModel

lemma Finite.fn_eventually_periodic {G : Type*} [Finite G] (f : G → G) :
    ∃ s p : ℕ, p > 0 ∧ f^[s] = f^[s+p] := by
  obtain ⟨p₁, p₂, lt, heq⟩ : ∃ p₁ p₂ : ℕ, p₁ < p₂ ∧ f^[p₁] = f^[p₂] := by
    obtain ⟨p₁, p₂, ne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (Nat.iterate f ·)
    rcases le_total p₁ p₂ with h_le | h_le
    . exact ⟨p₁, p₂, Ne.lt_of_le ne h_le, heq⟩
    . exact ⟨p₂, p₁, Ne.lt_of_le (Ne.symm ne) h_le, Eq.symm heq⟩
  let p := p₂ - p₁
  have : f^[p₁] = f^[p₁ + p] := by
    unfold p
    rw [← Nat.add_sub_assoc (by linarith)]
    simp only [heq, add_tsub_cancel_left]
  exact ⟨p₁, p, by simp only [gt_iff_lt, tsub_pos_iff_lt, lt, p], this⟩

lemma Finite.fn_periodic {G : Type*} [Finite G] (f : G → G) : ∃ p : ℕ, p > 0 ∧ f^[p] = f^[2*p] := by
  obtain ⟨s, p, hpgt, hp⟩ := Finite.fn_eventually_periodic f
  have hmod (n j : ℕ) : f^[s + j] = f^[s + j + n*p] := by
    induction n with
    | zero => simp only [zero_mul, add_zero]
    | succ i ih =>
      have : s + j + (i + 1) * p = s + p + (j + i * p) := by simp_arith only [Nat.succ_mul]
      rw [this, Function.iterate_add f (s + p), ← hp, ← Function.iterate_add, ← Nat.add_assoc, ih]
  rcases eq_zero_or_pos s with h | h
  . simp only [h, zero_add] at hmod
    have : f^[p] = f^[2*p] := by simp_arith only [hmod 1 p]
    exact ⟨p, hpgt, this⟩
  . let n := s * p
    have : f^[n] = f^[2*n] := by
      unfold n
      obtain ⟨ppred, hppred⟩ := Nat.exists_eq_succ_of_ne_zero (by linarith)
      rw [hppred, Nat.succ_eq_add_one, Nat.mul_succ, Nat.add_comm]
      have : 2 * (s + s * ppred) = s + s * ppred + s * p := by simp_arith only [hppred, Nat.mul_succ]
      rw [this, ← hmod]
    have ngt : n > 0 := by apply Nat.mul_pos h hpgt
    exact ⟨n, ngt, this⟩

lemma Finite.fn_mutually_eventually_periodic {G : Type*} [Finite G] (f g : G → G) :
    ∃ p : ℕ, p > 0 ∧ f^[p] = f^[2*p] ∧ g^[p] = g^[2*p] := by
  obtain ⟨p₁, hpgt₁, hp₁⟩ := Finite.fn_periodic f
  obtain ⟨p₂, hpgt₂, hp₂⟩ := Finite.fn_periodic g
  let p := p₁ * p₂
  have hpgt : p > 0 := by simp only [gt_iff_lt, mul_pos_iff_of_pos_left, p, hpgt₁, hpgt₂]
  have periodic_dvd' {f : G → G} (p n : ℕ) (hperiod : f^[p] = f^[2*p]) : f^[p + p*n] = f^[p] := by
    induction n with
    | zero => simp only [mul_zero, add_zero]
    | succ n ih =>
      rw [Nat.mul_add, ← Nat.add_assoc, Function.iterate_add, ih, ← Function.iterate_add]
      simp_arith only [mul_one, hperiod]
  have periodic_dvd {f : G → G} (p n : ℕ) (hperiod : f^[p] = f^[2*p]) (hngt : n > 0) :
      f^[n*p] = f^[p] := by
    obtain ⟨np, hnp⟩ := @Nat.exists_eq_succ_of_ne_zero n (by linarith)
    rw [hnp, Nat.succ_eq_one_add, Nat.add_mul, Nat.one_mul, Nat.mul_comm, periodic_dvd' _ _ hperiod]
  have fperiodic : f^[p] = f^[2*p] := by
    unfold p
    rw [Nat.mul_comm, periodic_dvd p₁ _ hp₁ hpgt₂]
    symm
    have : 2 * (p₂ * p₁) = 2 * p₂ * p₁ := by linarith
    rw [this, periodic_dvd p₁ _ hp₁ (by linarith)]
  have gperiodic : g^[p] = g^[2*p] := by
    unfold p
    rw [periodic_dvd p₂ _ hp₂ hpgt₁]
    symm
    have : 2 * (p₁ * p₂) = 2 * p₁ * p₂ := by linarith
    rw [this, periodic_dvd p₂ _ hp₂ (by linarith)]
  exact ⟨p, hpgt, fperiodic, gperiodic⟩

-- https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Austin.20pairs/near/480601897

lemma Finite.f_ffg_implies_f_fgf {G: Type*} [Finite G] (f g : G -> G) (h : f = f ∘ f ∘ g) :
    f = f ∘ g ∘ f := by
  have periodic : ∃ p : ℕ, p > 1 ∧ f^[p] = f := by
    obtain ⟨s, p, hpgt, hperiodic⟩ := Finite.fn_eventually_periodic f
    let S : Set ℕ := { n | f^[n] = f^[n+p] }
    have S_nonempty : S.Nonempty := by
      use s
      simp only [Set.mem_setOf_eq, S, hperiodic]
    let n : ℕ := WellFounded.min Nat.lt_wfRel.wf S S_nonempty
    have n_mem : f^[n] = f^[n + p] := WellFounded.min_mem Nat.lt_wfRel.wf S S_nonempty
    have n_min : ∀ k ∈ S, ¬k < n := fun k hk => WellFounded.not_lt_min Nat.lt_wfRel.wf S
      S_nonempty hk
    have : n ≤ 1 := by
      by_contra nh
      simp at nh
      -- For n ≥ 2, f^[n] ∘ g must equal both f^[n-1] ≠ f^[n + p-1].
      have : f^[n - 1] = f^[n + p - 1] := by
        obtain ⟨pred, hpred⟩ := @Nat.exists_eq_add_one_of_ne_zero n (by linarith)
        obtain ⟨pred2, hpred2⟩ := @Nat.exists_eq_add_one_of_ne_zero pred (by linarith)
        simp only [hpred, hpred2, add_tsub_cancel_right, Nat.succ_add_sub_one]
        rw [Function.iterate_succ, Nat.add_comm, ← Nat.add_assoc, Function.iterate_succ]
        nth_rewrite 4 [h]
        nth_rewrite 2 [h]
        change ((f^[pred2] ∘ f) ∘ f) ∘ g = ((f^[p + pred2] ∘ f) ∘ f) ∘ g
        rw [← Function.iterate_succ, ← Function.iterate_succ, Nat.succ_eq_add_one, ← hpred2, ← hpred]
        rw [← Function.iterate_succ, ← Function.iterate_succ, Nat.succ_eq_add_one, Nat.add_assoc p,
          ← hpred2, Nat.add_assoc p, ← hpred]
        simp only [n_mem, Nat.add_comm]
      have : f^[n - 1] ≠ f^[n + p-1] := by
        have : n + p - 1 = n - 1 + p := by omega
        rw [this]
        by_contra nh2
        have t1 : n - 1 ∈ S := by simp only [Set.mem_setOf_eq, nh2, S]
        have t2 : n - 1 < n := by omega
        apply n_min (n - 1) t1 t2
      tauto
    have : n = 0 ∨ n = 1 := by omega
    rcases this with h | h
    . simp only [h, Function.iterate_zero, zero_add] at n_mem
      use p+1
      simp only [gt_iff_lt, lt_add_iff_pos_left, hpgt, Function.iterate_succ, ← n_mem,
        Function.id_comp, and_self]
    . simp only [h, Function.iterate_one] at n_mem
      use p+1
      simp only [gt_iff_lt, lt_add_iff_pos_left, hpgt, Function.iterate_succ, true_and]
      rw [← Function.iterate_succ, Nat.succ_eq_add_one, Nat.add_comm, ← n_mem]
  obtain ⟨p, pgt, hp⟩ := periodic
  nth_rewrite 1 [← hp]
  obtain ⟨ppred, hppred⟩ := @Nat.exists_eq_succ_of_ne_zero p (by linarith)
  obtain ⟨ppred2, hppred2⟩ := @Nat.exists_eq_succ_of_ne_zero ppred (by linarith)
  rw [hppred, hppred2, Function.iterate_succ, Function.iterate_succ]
  nth_rewrite 2 [h]
  change ((f^[ppred2] ∘ f) ∘ f) ∘ g ∘ f = f ∘ g ∘ f
  rw [← Function.iterate_succ, ← Function.iterate_succ, ← hppred2, ← hppred, hp]

lemma Finite.f_gff_implies_f_fgf {G: Type*} [Finite G] (f g : G -> G) (h : f = g ∘ f ∘ f) :
    f = f ∘ g ∘ f := by
  have periodic : ∃ p : ℕ, p > 1 ∧ f^[p] = f := by
    obtain ⟨s, p, hpgt, hperiodic⟩ := Finite.fn_eventually_periodic f
    let S : Set ℕ := { n | f^[n] = f^[n+p] }
    have S_nonempty : S.Nonempty := by
      use s
      simp only [Set.mem_setOf_eq, S, hperiodic]
    let n : ℕ := WellFounded.min Nat.lt_wfRel.wf S S_nonempty
    have n_mem : f^[n] = f^[n + p] := WellFounded.min_mem Nat.lt_wfRel.wf S S_nonempty
    have n_min : ∀ k ∈ S, ¬k < n := fun k hk => WellFounded.not_lt_min Nat.lt_wfRel.wf S
      S_nonempty hk
    have : n ≤ 1 := by
      by_contra nh
      simp at nh
      -- For n ≥ 2, g ∘ f^[n] must equal both f^[n-1] ≠ f^[n + p-1].
      have : f^[n - 1] = f^[n + p - 1] := by
        obtain ⟨pred, hpred⟩ := @Nat.exists_eq_add_one_of_ne_zero n (by linarith)
        obtain ⟨pred2, hpred2⟩ := @Nat.exists_eq_add_one_of_ne_zero pred (by linarith)
        simp only [hpred, hpred2, add_tsub_cancel_right, Nat.succ_add_sub_one]
        rw [Function.iterate_succ', Nat.add_comm, ← Nat.add_assoc, Function.iterate_succ']
        nth_rewrite 3 [h]
        nth_rewrite 1 [h]
        change g ∘ (f ∘ (f ∘ f^[pred2])) = g ∘ (f ∘ (f ∘ f^[p + pred2]))
        rw [← Function.iterate_succ', ← Function.iterate_succ', Nat.succ_eq_add_one, ← hpred2, ← hpred]
        rw [← Function.iterate_succ', ← Function.iterate_succ', Nat.succ_eq_add_one, Nat.add_assoc p,
          ← hpred2, Nat.add_assoc p, ← hpred]
        simp only [n_mem, Nat.add_comm]
      have : f^[n - 1] ≠ f^[n + p-1] := by
        have : n + p - 1 = n - 1 + p := by omega
        rw [this]
        by_contra nh2
        have t1 : n - 1 ∈ S := by simp only [Set.mem_setOf_eq, nh2, S]
        have t2 : n - 1 < n := by omega
        apply n_min (n - 1) t1 t2
      tauto
    have : n = 0 ∨ n = 1 := by omega
    rcases this with h | h
    . simp only [h, Function.iterate_zero, zero_add] at n_mem
      use p+1
      simp only [gt_iff_lt, lt_add_iff_pos_left, hpgt, Function.iterate_succ, ← n_mem,
        Function.id_comp, and_self]
    . simp only [h, Function.iterate_one] at n_mem
      use p+1
      simp only [gt_iff_lt, lt_add_iff_pos_left, hpgt, Function.iterate_succ, true_and]
      rw [← Function.iterate_succ, Nat.succ_eq_add_one, Nat.add_comm, ← n_mem]
  obtain ⟨p, pgt, hp⟩ := periodic
  nth_rewrite 1 [← hp]
  obtain ⟨ppred, hppred⟩ := @Nat.exists_eq_succ_of_ne_zero p (by linarith)
  obtain ⟨ppred2, hppred2⟩ := @Nat.exists_eq_succ_of_ne_zero ppred (by linarith)
  rw [hppred, hppred2, Function.iterate_succ', Function.iterate_succ']
  nth_rewrite 2 [h]
  change f ∘ g ∘ (f ∘ (f ∘ f^[ppred2])) = f ∘ g ∘ f
  rw [← Function.iterate_succ', ← Function.iterate_succ', ← hppred2, ← hppred, hp]

@[equational_result]
theorem Finite.Equation3308_implies_Equation3511 (G : Type*) [Magma G] [Finite G]
    (h : Equation3308 G) : Equation3511 G := by
  intro x y
  let f := (x ◇ ·)
  let g := (· ◇ x)
  change f y = (f ∘ g ∘ f) y
  rw [← Finite.f_ffg_implies_f_fgf f g]
  funext x
  apply h

@[equational_result]
theorem Finite.Equation3549_implies_Equation3955 (G : Type*) [Magma G] [Finite G]
    (h : Equation3549 G) : Equation3955 G := by
  intro x y
  let f := (· ◇ y)
  let g := (y ◇ ·)
  change f x = (f ∘ g ∘ f) x
  rw [← Finite.f_gff_implies_f_fgf f g]
  funext x
  apply h

end FiniteModel
