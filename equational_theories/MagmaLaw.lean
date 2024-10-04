import equational_theories.FreeMagma
import Mathlib.Data.Set.Defs

set_option hygiene false

open FreeMagma

namespace Law

structure MagmaLaw (α : Type) where
  lhs : FreeMagma α
  rhs : FreeMagma α
deriving DecidableEq

infix:60 " ≃ " => MagmaLaw.mk

end Law

open Law

def substFreeMagma {α β} (t : FreeMagma α) (σ : α → FreeMagma β) : FreeMagma β :=
match t with
| .Leaf a => σ a
| t₁ ⋆ t₂ => substFreeMagma t₁ σ ⋆ substFreeMagma t₂ σ

infix:66 " ⬝ " => substFreeMagma

@[inline, simp]
def Ctx α := Set (MagmaLaw α)

-- FIXME: figure out how to remove this.
instance Ctx.Membership α : Membership (MagmaLaw α) (Ctx α) := ⟨ Set.instMembership.mem ⟩

instance {α : Type} : Singleton (MagmaLaw α) (Ctx α) := ⟨Set.singleton⟩

/-- Definition of derivability -/
local infix:50 " ⊢ " =>  derive

-- We keep this in type, because we're going to want to gather
-- the (finite!) set of required axioms later.
inductive derive {α} : Ctx α → MagmaLaw α → Type :=
  | Ax Γ E (h : E ∈ Γ) : Γ ⊢ E
  | Ref Γ t : Γ ⊢ (t ≃ t)
  | Sym Γ t u : Γ ⊢ (t ≃ u) → Γ ⊢ (u ≃ t)
  | Trans Γ t u v : Γ ⊢ (t ≃ u) → Γ ⊢ (u ≃ v) → Γ ⊢ (t ≃ v)
  -- This is not as polymorphic as it could be, shouldn't be an issue at the moment
  | Subst Γ t u σ : Γ ⊢ (t ≃ u) → Γ ⊢ (t ⬝ σ ≃ u ⬝ σ)
  | Cong Γ t₁ t₂ u₁ u₂ : Γ ⊢ (t₁ ≃ t₂) → Γ ⊢ (u₁ ≃ u₂) → Γ ⊢ (t₁ ⋆ u₁ ≃ t₂ ⋆ u₂)

/-- Definitions of entailment -/
def satisfiesPhi {α G : Type} [Magma G] (φ : α → G) (E : MagmaLaw α) : Prop :=
  E.lhs.evalInMagma φ = E.rhs.evalInMagma φ

abbrev satisfies {α : Type} (G : Type) [Magma G] (E : MagmaLaw α) := ∀ (φ : α → G), satisfiesPhi φ E

abbrev satisfiesSet {α : Type} (G : Type) [Magma G] (Γ : Set (MagmaLaw α)) : Prop :=
  ∀ E ∈ Γ, satisfies G E

abbrev models {α} (Γ : Ctx α) (E : MagmaLaw α) : Prop :=
  ∀ (G : Type)[Magma G], satisfiesSet G Γ → satisfies G E

/-- Notation for derivability and entailment -/
infix:50 " ⊧ " => (satisfies)

infix:50 " ⊧ " => (satisfiesSet)

infix:50 " ⊧ " => (models)

infix:50 " ⊢ " => (derive)

theorem satisfiesPhi.evalHom {α G : Type} [Magma G] (φ : α → G) (E : MagmaLaw α) (f : G →◇ G) :
    satisfiesPhi (f ∘ φ) E ↔ f (E.lhs.evalInMagma φ) = f (E.rhs.evalInMagma φ) := by
  rw [satisfiesPhi, FreeMagma.evalHom]
  rfl
