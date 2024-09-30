import equational_theories.Completeness

@[simp]
def FreeMagma.size {α} (t : FreeMagma α) : Nat :=
  match t with
  | .Leaf _ => 0
  | .Fork t₁ t₂ => FreeMagma.size t₁ + FreeMagma.size t₂

theorem FreeMagma.sizeLtSubst {α} (t : FreeMagma α) (σ : α → FreeMagma α) :
  FreeMagma.size t ≤ FreeMagma.size (t ⬝ σ) :=
by
  cases t <;> simp
  case Fork t u =>
    have h₁ := FreeMagma.sizeLtSubst t σ
    have h₂ := FreeMagma.sizeLtSubst u σ
    omega

-- We use min here, as we want terms of *at least* size n.
@[simp]
def MagmaLaw.size {α} (E : MagmaLaw α) : Nat := min (FreeMagma.size E.lhs) (FreeMagma.size E.rhs)

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
      right; simp at *
      rw [Nat.min_comm]
      apply h
  case Trans _ _ _ h₁ h₂ =>
    cases (derive.PreservesSize _ _ sizeBound _ h₁) <;> cases (derive.PreservesSize _ _ sizeBound _ h₂) <;> simp at *
    case inl.inl h₁ h₂ =>
      left;
      rw [h₁, h₂]
    case inl.inr h₁ h₂ =>
      right; rw [h₁]; trivial
    case inr.inl h₁ h₂ =>
      right; rw [← h₂]; trivial
    case inr.inr =>
      right; omega
  case Subst t u σ h =>
    cases (derive.PreservesSize _ _ sizeBound _ h) <;> simp at *
    case inl h => left; rw [h]
    case inr =>
      right
      have h₁ := FreeMagma.sizeLtSubst t σ
      have h₂ := FreeMagma.sizeLtSubst u σ
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
      right; rw [← h₂]; omega
    case inr.inr =>
      right; omega

theorem models.PreservesSize {α} (Γ : Ctx α) (n : Nat)(sizeBound : Ctx.IsOfSize Γ n) (E : MagmaLaw α)(h : Γ ⊧ E) :
  E.lhs = E.rhs ∨ n ≤ MagmaLaw.size E :=
by
  have ⟨ h ⟩ := Completeness _ _ h
  apply derive.PreservesSize <;> trivial
