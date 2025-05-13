import Batteries.Data.List.Basic
import equational_theories.Definability.Basic
import equational_theories.Equations.All

open FirstOrder.Language
open Law
open Law.MagmaLaw

/-- The constant law 46 `x ◇ y = z ◇ w` is TermDefinable from any law `lhs = rhs`, where
lhs and rhs are the same shape, but with disjoint sets of variables. -/
theorem Equation46_termDefinableFrom_equalShape {L : NatMagmaLaw}
  (hShape : L.lhs ⬝ (fun _ ↦ Lf 0) = L.rhs ⬝ (fun _ ↦ Lf 0) := by rfl)
  (hDisjoint : L.lhs.elems.val.Disjoint L.rhs.elems := by rw [List.Disjoint]; native_decide)
  : Law46.TermDefinableFrom L := by
  --There are two cases: there is at least one function application, or both sides of L are leaves.
  cases hlhs : L.lhs
  next x =>
    --In this case, the law is of the form x = y. Thus, it is (equivalent to) equation 2
    obtain ⟨y,hy⟩ : ∃ y, L.rhs = Lf y := sorry
    have hxy : x ≠ y := sorry
    rw [show L = Lf x ≃ Lf y from sorry]
    clear hlhs hy hShape hDisjoint
    apply termDefinable_of_termStructural
    apply termStructural_of_implies
    have : (Lf x ≃ Lf y).toFin.toNat = Law2 := by
      -- have h₁ : (Lf x ≃ Lf y : NatMagmaLaw).elems.1 = [x,y] := by
      --   sorry
      -- have h₂ : Fin ((Lf x ≃ Lf y : NatMagmaLaw).elems).1.length = Fin 2 := by
      --   rw [h₁]
      --   simp
      -- simp [toFin, h₁]
      -- simp_rw [h₁]
      sorry
    unfold implies
    simp_rw [← satisfies_toFin (E := Lf x ≃ Lf y)
            , ← satisfies_toNat (E := (Lf x ≃ Lf y).toFin),
            this]
    exact Equation2_implies Law46
  --Otherwise we call back to the more interesting case of a function application
  intro G M hGL
  use ⟨fun x _ ↦ @Term.realize _ _ M.FOStructure _ (fun _ ↦ x) L.lhs.toTerm⟩
  constructor
  · rw [@Law46.models_iff]
    by_cases hG : Nonempty G
    · suffices ∃ c, ∀ (x y : G), x ◇ y = c by
        obtain ⟨c,h⟩ := this
        intros x y z w
        simp
        sorry
      sorry
    · exact (not_nonempty_iff.mp hG).elim
  · use (MagmaLanguage.lhomWithConstants _).onTerm (L.lhs.toTerm.subst fun a ↦ var 0)
    funext v
    sorry

/-- The constant law 46 `x ◇ y = z ◇ w` is TermDefinable from Equation 40 `x ◇ x = y ◇ y`. -/
theorem Equation46_termDefinableFrom_Equation40 : Law46.TermDefinableFrom Law40 :=
  Equation46_termDefinableFrom_equalShape

/-- The constant law 46 `x ◇ y = z ◇ w` is TermDefinable from 4276 `x ◇ (x ◇ x) = y ◇ (y ◇ y)`. -/
theorem Equation46_termDefinableFrom_Equation4276 : Law46.TermDefinableFrom Law4276 :=
  Equation46_termDefinableFrom_equalShape

/-- The constant law 46 `x ◇ y = z ◇ w` is TermDefinable from 4308 `x ◇ (x ◇ y) = z ◇ (z ◇ w)`. -/
theorem Equation46_termDefinableFrom_Equation4308 : Law46.TermDefinableFrom Law4308 :=
  Equation46_termDefinableFrom_equalShape

/-- The constant law 46 `x ◇ y = z ◇ w` is TermDefinable from 4336 `x ◇ (y ◇ x) = z ◇ (w ◇ z)`. -/
theorem Equation46_termDefinableFrom_Equation4336 : Law46.TermDefinableFrom Law4336 :=
  Equation46_termDefinableFrom_equalShape

/-- The constant law 46 `x ◇ y = z ◇ w` is TermDefinable from 4355 `x ◇ (y ◇ y) = z ◇ (w ◇ w)`. -/
theorem Equation46_termDefinableFrom_Equation4355 : Law46.TermDefinableFrom Law4355 :=
  Equation46_termDefinableFrom_equalShape
