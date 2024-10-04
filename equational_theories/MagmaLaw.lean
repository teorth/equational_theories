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

def satisfies {α : Type} (G : Type) [Magma G] (E : MagmaLaw α) := ∀ (φ : α → G), satisfiesPhi φ E

def satisfiesSet {α : Type} (G : Type) [Magma G] (Γ : Set (MagmaLaw α)) : Prop :=
  ∀ E ∈ Γ, satisfies G E

def models {α} (Γ : Ctx α) (E : MagmaLaw α) : Prop :=
  ∀ (G : Type)[Magma G], satisfiesSet G Γ → satisfies G E

/-- Notation for derivability and entailment -/
infix:50 " ⊧ " => (satisfies)

infix:50 " ⊧ " => (satisfiesSet)

infix:50 " ⊧ " => (models)

infix:50 " ⊢ " => (derive)

namespace Law

def MagmaLaw.symm {α : Type} (l : MagmaLaw α) : MagmaLaw α := {lhs := l.rhs, rhs:=l.lhs}

@[simp]
theorem MagmaLaw.symm_symm {α : Type} (l : MagmaLaw α) : l.symm.symm = l := by
  simp [symm]

theorem satisfiesPhi_symm_law {α G : Type} [Magma G] (φ : α → G) (E : MagmaLaw α)
  (h : satisfiesPhi φ E) : satisfiesPhi φ E.symm := by
  simp [Law.MagmaLaw.symm, satisfiesPhi]
  exact h.symm

theorem satisfiesPhi_symm {α G : Type} [Magma G] (φ : α → G) (w₁ w₂ : FreeMagma α)
  (h : satisfiesPhi φ (w₁ ≃ w₂)) : satisfiesPhi φ (w₂ ≃ w₁) := Law.satisfiesPhi_symm_law φ (w₁ ≃ w₂) h

theorem satisfies_symm_law {α : Type} (G : Type) [Magma G] (E : MagmaLaw α)
  (h : G ⊧ E) :  G ⊧ E.symm := fun φ ↦ satisfiesPhi_symm_law φ E (h φ)

theorem satisfies_symm {α : Type} (G : Type) [Magma G] (w₁ w₂ : FreeMagma α)
  (h : G ⊧ w₁ ≃ w₂) :  G ⊧ w₂ ≃ w₁ := satisfies_symm_law G (w₁ ≃ w₂) h

def set_symm {α} (Γ : Set (MagmaLaw α)) : Set (MagmaLaw α) := { (γ.symm) | γ ∈ Γ}

theorem satisfiesSet_symm {α : Type} (G : Type) [Magma G] (Γ : Set (MagmaLaw α))
  (h :  G ⊧ Γ) : G ⊧ (set_symm Γ) := by
  simp [set_symm]
  intro E ⟨Esymm, ⟨hEsymm,hEsymmE⟩⟩
  rw [← hEsymmE]
  apply Law.satisfies_symm
  apply h
  exact hEsymm

theorem models_symm_law {α} (Γ : Ctx α) (E : MagmaLaw α) (h : Γ ⊧ E) : Γ   ⊧ E.symm :=
 fun G [Magma G] hsatisfiesSet ↦ satisfies_symm_law G E (h G hsatisfiesSet)

theorem models_symm {α} (Γ : Ctx α) (w₁ w₂ : FreeMagma α) (h : Γ ⊧ w₁ ≃ w₂) : Γ ⊧ w₂ ≃ w₁ :=
   Law.models_symm_law Γ (w₁ ≃ w₂) h

end Law
