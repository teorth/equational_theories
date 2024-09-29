-- Statement and proof of the completeness theorem for magmas,
-- we roughly follow Baader & Nipkow's "Term Rewriting and All That",
-- and
import equational_theories.FreeMagma
import Mathlib.Data.Set.Defs

#check Set

structure SynEqn (α : Type) where
  lhs : FreeMagma α
  rhs : FreeMagma α

infix:60 " ≃ " => SynEqn.mk

#check (Lf 1 ≃ Lf 2 : SynEqn Nat)

def substFreeMagma {α β} (t : FreeMagma α) (σ : α → FreeMagma β) : FreeMagma β :=
match t with
| .Leaf a => σ a
| t₁ ⋆ t₂ => substFreeMagma t₁ σ ⋆ substFreeMagma t₂ σ

infix:66 " ⬝ " => substFreeMagma

#check ((Lf 0) ⬝ (λ i ↦ Lf i))

@[inline, simp]
def Ctx α := Set (SynEqn α)

#print Membership

#print Set.instMembership

-- FIXME: figure out how to remove this.
instance Ctx.Membership α : Membership (SynEqn α) (Ctx α) := ⟨ Set.instMembership.mem ⟩

-- We keep this in type, because we're going to want to gather
-- the (finite!) set of required axioms later.
inductive derive {α} : Ctx α → SynEqn α → Type :=
| Ax Γ E (h : E ∈ Γ) : derive Γ E
| Ref Γ t : derive Γ (t ≃ t)
| Sym Γ t u : derive Γ (t ≃ u) → derive Γ (u ≃ t)
| Trans Γ t u v : derive Γ (t ≃ u) → derive Γ (u ≃ v) → derive Γ (t ≃ v)
-- This is not as polymorphic as it could be, shouldn't be an issue at the moment
| Subst Γ t u σ : derive Γ (t ≃ u) → derive Γ (t ⬝ σ ≃ u ⬝ σ)
| Cong₁ Γ t₁ t₂ u : derive Γ (t₁ ≃ t₂) → derive Γ (t₁ ⋆ u ≃ t₂ ⋆ u)
| Cong₂ Γ t u₁ u₂ : derive Γ (u₁ ≃ u₂) → derive Γ (t ⋆ u₁ ≃ t ⋆ u₂)

def modelsEqPhi {α G : Type} [Magma G] (φ : α → G) (E : SynEqn α) : Prop :=
  evalInMagma φ E.lhs = evalInMagma φ E.rhs

def modelsEq {α : Type} (G : Type) [Magma G] (E : SynEqn α) := ∀ (φ : α → G), modelsEqPhi φ E

def modelsSet {α : Type} (G : Type) [Magma G] (Γ : Set (SynEqn α)) : Prop :=
  ∀ E ∈ Γ, modelsEq G E


def models {α} (Γ : Ctx α) (E : SynEqn α) : Prop :=
  ∀ (G : Type)[Magma G], modelsSet G Γ → modelsEq G E

infix:50 " ⊧ " => (models)

infix:50 " ⊢ " => (derive)

theorem SubstEval {α} G [Magma G] (t : FreeMagma α) (σ : α → FreeMagma α) (φ : α → G) :
  evalInMagma φ (t ⬝ σ) = evalInMagma (evalInMagma φ ∘ σ) t :=
by
  cases t
  case Leaf => simp [evalInMagma, substFreeMagma]
  case Fork t₁ t₂ =>
  simp [evalInMagma, substFreeMagma]
  repeat rw [SubstEval]

theorem Soundness {α} (Γ : Ctx α) E (h : Γ ⊢ E) : Γ ⊧ E :=
by
  intros G _
  cases h
  case Ax mem => intros mset; apply mset; trivial
  case Ref => intros; intro; simp[modelsEqPhi]
  -- FIXME: try aesop here, might be a 1-liner
  case Sym t u prf =>
    intros φ mset
    have h := Soundness _ _ prf
    simp [models, modelsEqPhi] at *
    symm; apply h; trivial
  case Trans _ _ _ prf₁ prf₂ =>
    intros φ mset
    have h₁ := Soundness _ _ prf₁
    have h₂ := Soundness _ _ prf₂
    simp [models, modelsEqPhi] at *
    rw [h₁, h₂] <;> trivial
  case Subst t u σ prf =>
    intros φ mset
    have h := Soundness _ _ prf
    simp [models, modelsEqPhi, evalInMagma] at *
    repeat rw [SubstEval]
    rw [h]; trivial
  case Cong₁ _ _ _ prf =>
    intros φ mset
    have h := Soundness _ _ prf
    simp [models, modelsEqPhi, evalInMagma] at *
    rw [h]; trivial
  case Cong₂ _ _ _ prf =>
    intros φ mset
    have h := Soundness _ _ prf
    simp [models, modelsEqPhi, evalInMagma] at *
    rw [h]; trivial
