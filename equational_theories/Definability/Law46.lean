import Batteries.Data.List.Basic
import equational_theories.Definability.Basic
import equational_theories.Definability.Simple
import equational_theories.Equations.All

open FirstOrder.Language
open Law
open Law.MagmaLaw

/-- Evaluating a `FreeMagma` expression only depends on the values assigned to the variables that
actually occur in it. -/
theorem FreeMagma.evalInMagma_congr {α G} [Magma G] {φ ψ : α → G} :
    ∀ (m : FreeMagma α), (∀ a, m.Mem a → φ a = ψ a) → m ⬝ φ = m ⬝ ψ
  | Lf _, h => h _ rfl
  | m₁ ⋆ m₂, h =>
    congrArg₂ Magma.op (evalInMagma_congr m₁ fun _ ha ↦ h _ (.inl ha))
      (evalInMagma_congr m₂ fun _ ha ↦ h _ (.inr ha))

/-- The constant law 46 `x ◇ y = z ◇ w` is TermDefinable from any law `lhs = rhs`, where
lhs and rhs are the same shape, but with disjoint sets of variables. -/
theorem Equation46_termDefinableFrom_equalShape {L : NatMagmaLaw}
  (hShape : L.lhs ⬝ (fun _ ↦ Lf 0) = L.rhs ⬝ (fun _ ↦ Lf 0) := by rfl)
  (hDisjoint : L.lhs.elems.val.Disjoint L.rhs.elems := by rw [List.Disjoint]; decide +kernel)
  : Law46.TermDefinableFrom L := by
  intro G M hGL
  --The new operation ignores its second argument, and plugs its first argument into every
  --variable of `L.lhs`.
  use ⟨fun x _ ↦ @Term.realize _ _ M.FOStructure _ (fun _ ↦ x) L.lhs.toTerm⟩
  --Since the two sides have the same shape, they agree on every constant assignment. (This is
  --just `hShape` pushed forward along the evaluation homomorphism.)
  have hboth : ∀ z : G, L.lhs ⬝ (fun _ ↦ z) = L.rhs ⬝ (fun _ ↦ z) := fun z ↦ by
    have h := congrArg (FreeMagma.evalInMagma (fun _ ↦ z)) hShape
    rwa [FreeMagma.SubstEval, FreeMagma.SubstEval] at h
  --The new operation is in fact constant: feeding `x` to the variables of the left side and `x'`
  --to the (disjoint!) variables of the right side, `L` says that the two constant evaluations
  --agree.
  have hconst : ∀ x x' : G, L.lhs ⬝ (fun _ ↦ x) = L.lhs ⬝ (fun _ ↦ x') := by
    intro x x'
    let ψ : ℕ → G := fun n ↦ if n ∈ L.lhs.elems.val then x else x'
    calc L.lhs ⬝ (fun _ ↦ x)
        = L.lhs ⬝ ψ :=
          (FreeMagma.evalInMagma_congr _ fun a ha ↦ if_pos ((L.lhs.elems.2.2 a).2 ha)).symm
      _ = L.rhs ⬝ ψ := hGL ψ
      _ = L.rhs ⬝ (fun _ ↦ x') :=
          FreeMagma.evalInMagma_congr _ fun a ha ↦
            if_neg fun hm ↦ hDisjoint hm ((L.rhs.elems.2.2 a).2 ha)
      _ = L.lhs ⬝ (fun _ ↦ x') := (hboth x').symm
  constructor
  --A constant operation satisfies law 46.
  · rw [@Law46.models_iff]
    intro x y z w
    show @Term.realize _ _ M.FOStructure _ (fun _ ↦ x) L.lhs.toTerm
        = @Term.realize _ _ M.FOStructure _ (fun _ ↦ z) L.lhs.toTerm
    rw [FreeMagma.toTerm_realize, FreeMagma.toTerm_realize]
    exact hconst x z
  --And it is given by a term, namely `L.lhs` with every variable replaced by the first argument.
  · use (MagmaLanguage.lhomWithConstants _).onTerm (L.lhs.toTerm.subst fun _ ↦ var 0)
    funext v
    letI := M.FOStructure
    show @Term.realize _ _ M.FOStructure _ (fun _ ↦ v 0) L.lhs.toTerm = _
    rw [LHom.realize_onTerm, Term.realize_subst]
    rfl

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
