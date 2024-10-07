import Mathlib.Data.Finset.Basic
import equational_theories.Completeness
import equational_theories.MagmaLaw

open Law

set_option linter.unusedVariables false
def derive.getAxioms {α} [DecidableEq α] {Γ : Ctx α} {E : MagmaLaw α} (h : Γ ⊢ E) :
    Finset (MagmaLaw α) :=
  match h with
  | .Ax _ E _ => {E}
  | .Ref _ _ => {}
  | .Sym _ _ _ h => derive.getAxioms h
  | .Trans _ _ _ _ h₁ h₂ => derive.getAxioms h₁ ∪ derive.getAxioms h₂
  | .Subst _ _ _ _ h => derive.getAxioms h
  | .Cong _ _ _ _ _ h₁ h₂ => derive.getAxioms h₁ ∪ derive.getAxioms h₂

def ToCtx {α} (S : Set (MagmaLaw α)) : Ctx α := S

instance Ctx.hasSubset {α} : HasSubset (Ctx α) := Set.instHasSubset

theorem foo (S T : Set Nat) : S ⊆ S ∪ T := Set.subset_union_left

def derive.Weak {α} {Γ Δ : Ctx α}{E : MagmaLaw α}(inc : Γ ⊆ Δ) (h : Γ ⊢ E) :
    Δ ⊢ E := by
  cases h
  case Ax => refine derive.Ax _ _ (inc ?_); assumption
  case Ref => exact derive.Ref _ _
  case Sym => apply derive.Sym ; apply derive.Weak _ <;> trivial
  case Trans => apply derive.Trans <;> try apply derive.Weak <;> trivial
  case Subst => apply derive.Subst ; apply derive.Weak <;> trivial
  case Cong => apply derive.Cong <;> apply derive.Weak <;> trivial

def derive.getAxiomsEnough {α} [DecidableEq α] {Γ : Ctx α} {E : MagmaLaw α}(h : Γ ⊢ E) :
    ToCtx (derive.getAxioms h) ⊢ E := by
  cases h <;> simp [ToCtx, getAxioms]
  case Ax => constructor; rfl
  case Ref => exact derive.Ref _ _
  case Sym _ _ h => exact derive.Sym _ _ _ (derive.getAxiomsEnough _)
  case Trans _ _ _ h₁ h₂ =>
    apply derive.Trans
    · exact derive.Weak Set.subset_union_left (derive.getAxiomsEnough h₁)
    · exact derive.Weak Set.subset_union_right (derive.getAxiomsEnough h₂)
  case Subst => exact derive.Subst _ _ _ _ (derive.getAxiomsEnough _)
  case Cong _ _ _ h₁ h₂ =>
    exact derive.Cong _ _ _ _ _ (derive.Weak Set.subset_union_left (derive.getAxiomsEnough h₁))
      (derive.Weak Set.subset_union_right (derive.getAxiomsEnough h₂))

def Compactness {α} [DecidableEq α] {Γ : Ctx α} {E : MagmaLaw α}(h : Γ ⊧ E) :
    ∃ (Δ : Finset (MagmaLaw α)), Nonempty <| ToCtx Δ ⊧ E := by
  have ⟨ h'' ⟩ := Completeness _ _ h
  exact ⟨(derive.getAxioms h''), ⟨Soundness _ _ (derive.getAxiomsEnough _)⟩⟩
