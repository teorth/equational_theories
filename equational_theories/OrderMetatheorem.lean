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

open Law
-- We use min here, as we want terms of *at least* size n.
@[simp]
def MagmaLaw.order {α} (E : MagmaLaw α) : Nat := min (FreeMagma.order E.lhs) (FreeMagma.order E.rhs)

@[inline, simp]
def Ctx.IsOfOrder {α} (Γ : Ctx α) (n : Nat) := ∀ E ∈ Γ, n ≤ MagmaLaw.order E

theorem derive.PreservesOrder {α} (Γ : Ctx α) (n : Nat) (sizeBound : Ctx.IsOfOrder Γ n)
    (E : MagmaLaw α) (h : Γ ⊢ E) :
    E.lhs = E.rhs ∨ n ≤ MagmaLaw.order E := by
  rw [or_iff_not_imp_left, ← ne_eq]
  intro h2
  induction h with
  | Ax E h => exact sizeBound E h
  | Ref t => simp at h2
  | Sym t u _ ih => simpa [MagmaLaw.order, min_comm] using ih h2.symm
  | Trans t u v _ _ ih₁ ih₂ =>
    simp at ih₁ ih₂ h2 ⊢
    by_cases h : t = u
    · subst h
      exact ih₂ h2
    by_cases h3 : u = v
    · subst h3
      exact ih₁ h2
    exact ⟨ih₁ h |>.1, ih₂ h3 |>.2⟩
  | Subst t u σ _ ih =>
    simp at ih h2 ⊢
    specialize ih (by rintro rfl; contradiction)
    exact ⟨ih.1.trans <| t.orderLtSubst σ, ih.2.trans <| u.orderLtSubst σ⟩
  | Cong t₁ t₂ u₁ u₂ _ _ ih₁ ih₂ => 
    simp at ih₁ ih₂ h2 ⊢
    by_cases h : t₁ = t₂ <;> [specialize ih₂ (h2 h); specialize ih₁ h] <;> omega

theorem models.PreservesOrder {α} (Γ : Ctx α) (n : Nat)(sizeBound : Ctx.IsOfOrder Γ n) (E : MagmaLaw α)(h : Γ ⊧ E) :
  E.lhs = E.rhs ∨ n ≤ MagmaLaw.order E :=
by
  have ⟨ h ⟩ := Completeness _ _ h
  apply derive.PreservesOrder <;> trivial
