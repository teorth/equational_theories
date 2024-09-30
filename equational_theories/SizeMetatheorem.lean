import equational_theories.Completeness
import equational_theories.Counting

theorem FreeMagma.orderLtSubst {α} (t : FreeMagma α) (σ : α → FreeMagma α) :
  FreeMagma.order t ≤ FreeMagma.order (t ⬝ σ) :=
by
  cases t <;> simp [order]
  case Fork t u =>
    have h₁ := FreeMagma.orderLtSubst t σ
    have h₂ := FreeMagma.orderLtSubst u σ
    omega

-- We use min here, as we want terms of *at least* size n.
@[simp]
def MagmaLaw.size {α} (E : MagmaLaw α) : Nat := min (FreeMagma.order E.lhs) (FreeMagma.order E.rhs)

@[inline, simp]
def Ctx.IsOfSize {α} (Γ : Ctx α) (n : Nat) := ∀ E ∈ Γ, n ≤ MagmaLaw.size E

theorem derive.PreservesSize {α} (Γ : Ctx α) (n : Nat)(sizeBound : Ctx.IsOfSize Γ n) (E : MagmaLaw α)(h : Γ ⊢ E) :
  E.lhs = E.rhs ∨ n ≤ MagmaLaw.size E :=
by
  cases h
  case Ax => right; apply sizeBound; trivial
  case Ref => left; simp
  case Sym _ _ h =>
    cases (derive.PreservesSize _ _ sizeBound _ h)
    case inl eq =>
      left; simp at *; rw [eq]
    case inr h =>
      right; simp at *; omega
  case Trans _ _ _ h₁ h₂ =>
    cases (derive.PreservesSize _ _ sizeBound _ h₁) <;> cases (derive.PreservesSize _ _ sizeBound _ h₂) <;> simp at *
    case inl.inl h₁ h₂ =>
      left;
      rw [h₁, h₂]
    case inl.inr h₁ h₂ =>
      right; rw [h₁]; omega
    case inr.inl h₁ h₂ =>
      right; rw [← h₁]; omega
    case inr.inr =>
      right; omega
  case Subst t u σ h =>
    cases (derive.PreservesSize _ _ sizeBound _ h) <;> simp at *
    case inl h => left; rw [h]
    case inr =>
      right
      have h₁ := FreeMagma.orderLtSubst t σ
      have h₂ := FreeMagma.orderLtSubst u σ
      omega
  case Cong h₁ h₂ =>
    cases (derive.PreservesSize _ _ sizeBound _ h₁) <;> cases (derive.PreservesSize _ _ sizeBound _ h₂) <;> simp at *
    case inl.inl h₁ h₂ =>
      left;
      rw [h₁, h₂]; constructor <;> trivial
    case inl.inr h₁ h₂ =>
      right; rw [h₁]
      omega
    case inr.inl h₁ h₂ =>
      right; rw [← h₁]; omega
    case inr.inr =>
      right; omega

theorem models.PreservesSize {α} (Γ : Ctx α) (n : Nat)(sizeBound : Ctx.IsOfSize Γ n) (E : MagmaLaw α)(h : Γ ⊧ E) :
  E.lhs = E.rhs ∨ n ≤ MagmaLaw.size E :=
by
  have ⟨ h ⟩ := Completeness _ _ h
  apply derive.PreservesSize <;> trivial
