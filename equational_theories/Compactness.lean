import equational_theories.Completeness
import Mathlib.Data.Finset.Basic


#print derive

#print Finset

theorem test : 4 ∈ ({4} : Finset Nat) := by simp

#check ({4} : Finset Nat) ∪ {5}

#print FreeMagma

def derive.getAxioms {α} [DecidableEq α] {Γ : Ctx α} {E : MagmaLaw α}(h : Γ ⊢ E) : Finset (MagmaLaw α) :=
match h with
| .Ax _ E _ => {E}
| .Ref _ _ => {}
| .Sym _ _ _ h => derive.getAxioms h
| .Trans _ _ _ _ h₁ h₂ => derive.getAxioms h₁ ∪ derive.getAxioms h₂
| .Subst _ _ _ _ h => derive.getAxioms h
| .Cong _ _ _ _ _ h₁ h₂ => derive.getAxioms h₁ ∪ derive.getAxioms h₂

def ToCtx {α} (S : Set (MagmaLaw α)) : Ctx α := S

#print Nonempty

#print HasSubset

instance Ctx.hasSubset {α} : HasSubset (Ctx α) := Set.instHasSubset

theorem foo (S T : Set Nat) : S ⊆ S ∪ T :=
by exact Set.subset_union_left

def derive.Weak {α} {Γ Δ : Ctx α}{E : MagmaLaw α}(inc : Γ ⊆ Δ) (h : Γ ⊢ E) :
  Δ ⊢ E :=
by
  cases h
  case Ax => apply derive.Ax; apply inc; trivial
  case Ref => apply derive.Ref
  case Sym => apply derive.Sym; apply derive.Weak <;> trivial
  case Trans => apply derive.Trans <;> try apply derive.Weak <;> trivial
  case Subst => apply derive.Subst ; apply derive.Weak <;> trivial
  case Cong => apply derive.Cong <;> apply derive.Weak <;> trivial

def derive.getAxiomsEnough {α} [DecidableEq α] {Γ : Ctx α} {E : MagmaLaw α}(h : Γ ⊢ E) :
  ToCtx (derive.getAxioms h) ⊢ E :=
by
  cases h <;> simp [ToCtx, getAxioms]
  case Ax =>
    constructor; simp
  case Ref =>
    apply derive.Ref
  case Sym _ _ h =>
    apply derive.Sym
    apply derive.getAxiomsEnough
  case Trans _ _ _ h₁ h₂ =>
    apply derive.Trans
    . have j := derive.getAxiomsEnough h₁
      apply derive.Weak
      . apply Set.subset_union_left
      . exact j
    . have j := derive.getAxiomsEnough h₂
      apply derive.Weak
      . apply Set.subset_union_right
      . exact j
  case Subst =>
    apply derive.Subst
    apply derive.getAxiomsEnough
  case Cong _ _ _ h₁ h₂ =>
    apply derive.Cong
    . have j := derive.getAxiomsEnough h₁
      apply derive.Weak
      . apply Set.subset_union_left
      . exact j
    . have j := derive.getAxiomsEnough h₂
      apply derive.Weak
      . apply Set.subset_union_right
      . exact j

def Compactness {α} [DecidableEq α] {Γ : Ctx α} {E : MagmaLaw α}(h : Γ ⊧ E) :
  ∃ (Δ : Finset (MagmaLaw α)), Nonempty <| ToCtx Δ ⊧ E :=
by
  have h' := Completeness _ _ h
  have ⟨ h'' ⟩ := h'
  exists (derive.getAxioms h'')
  constructor
  apply Soundness
  apply derive.getAxiomsEnough
