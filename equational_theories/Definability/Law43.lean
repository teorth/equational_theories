import Batteries.Data.List.Basic
import equational_theories.Definability.Basic
import equational_theories.Definability.Simple
import equational_theories.Equations.All

open FirstOrder.Language
open Law
open Law.MagmaLaw

--TODO: the commutative law is definable from anything of the form f(x,y) ≃ f(y,x).
theorem Equation43_termDefinableFrom_swapped_args {L : NatMagmaLaw}
    (hL2args : ∀ e ∈ L.lhs.elems.1, e ∈ [0,1] := by decide +kernel)
    (_hR2args : ∀ e ∈ L.rhs.elems.1, e ∈ [0,1] := by decide +kernel)
    (hSymm : L.lhs ⬝ (fun x ↦ Lf $ Equiv.swap 0 1 x) = L.rhs := by rfl)
    : Law43.TermDefinableFrom L := by
  intro G M hSat
  letI := M
  have eval_eq_on_mem :
      ∀ (t : FreeMagma ℕ) (f g : ℕ → G),
        (∀ a, t.Mem a → f a = g a) → t ⬝ f = t ⬝ g := by
    intro t
    induction t with
    | Leaf a =>
        intro f g h
        exact h a rfl
    | Fork l r ihl ihr =>
        intro f g h
        change (l ⬝ f) ◇ (r ⬝ f) = (l ⬝ g) ◇ (r ⬝ g)
        rw [ihl f g (fun a ha ↦ h a (.inl ha)),
            ihr f g (fun a ha ↦ h a (.inr ha))]
  refine ⟨⟨fun x y ↦ L.lhs ⬝ fun n ↦ if n = 0 then x else y⟩, ?sat, ?defn⟩
  · intro φ
    dsimp [satisfiesPhi, Law43]
    have h := hSat (fun n ↦ if n = 0 then φ 0 else φ 1)
    dsimp [satisfiesPhi] at h
    calc
      L.lhs ⬝ (fun n ↦ if n = 0 then φ 0 else φ 1)
          = L.rhs ⬝ (fun n ↦ if n = 0 then φ 0 else φ 1) := h
      _ = (L.lhs ⬝ (fun x ↦ Lf ((Equiv.swap 0 1) x))) ⬝
            (fun n ↦ if n = 0 then φ 0 else φ 1) := by rw [hSymm]
      _ = L.lhs ⬝ (fun n ↦ if n = 0 then φ 1 else φ 0) := by
        rw [FreeMagma.SubstEval]
        apply eval_eq_on_mem
        intro a ha
        have haList : a ∈ L.lhs.elems.1 := (L.lhs.elems.2.2 a).2 ha
        have ha01 := hL2args a haList
        simp at ha01
        rcases ha01 with rfl | rfl <;> simp [FreeMagma.evalInMagma]
  · let _ := M.FOStructure
    exact ⟨
      (MagmaLanguage.lhomWithConstants (∅ : Set G)).onTerm
        (L.lhs.toTerm.subst fun n ↦
          if n = 0 then FirstOrder.Language.Term.var 0 else FirstOrder.Language.Term.var 1),
      by
        funext v
        simp [Term.realize_subst, FreeMagma.toTerm_realize]
        apply eval_eq_on_mem
        intro a ha
        by_cases ha0 : a = 0
        · simp [ha0]
        · simp [ha0]⟩

/-- The commutative law 43 `x ◇ y = y ◇ x` is TermDefinable from 40 `x ◇ x = y ◇ y`. -/
theorem Equation43_termDefinableFrom_Equation40 : Law43.TermDefinableFrom Law40 :=
  Equation43_termDefinableFrom_swapped_args

/-- The commutative law 43 `x ◇ y = y ◇ x` is TermDefinable from 4343 `x ◇ (y ◇ y) = y ◇ (x ◇ x)`. -/
theorem Equation43_termDefinableFrom_Equation4343 : Law43.TermDefinableFrom Law4343 :=
  Equation43_termDefinableFrom_swapped_args

/-- The commutative law 43 `x ◇ y = y ◇ x` is TermDefinable from 4293 `x ◇ (x ◇ y) = y ◇ (y ◇ x)`. -/
theorem Equation43_termDefinableFrom_Equation4293 : Law43.TermDefinableFrom Law4293 :=
  Equation43_termDefinableFrom_swapped_args

/-- The commutative law 43 `x ◇ y = y ◇ x` is TermDefinable from 4321 `x ◇ (y ◇ x) = y ◇ (x ◇ y)`. -/
theorem Equation43_termDefinableFrom_Equation4321 : Law43.TermDefinableFrom Law4321 :=
  Equation43_termDefinableFrom_swapped_args
