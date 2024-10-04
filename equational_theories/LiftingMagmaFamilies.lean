import equational_theories.MagmaLaw
import equational_theories.Homomorphisms

open Law

class LiftingMagma (G : Type → Type) where
  instMagma {α} : Magma (G α)
  ι : ∀ {α}, α → G α
  lift : ∀ {α}, (α → G α) → (G α →◇ G α)
  lift_factors : ∀ {α}, ∀ f : α → G α, f = (lift f) ∘ ι

instance {G : Type → Type} [LiftingMagma G] {α : Type} : Magma (G α) := LiftingMagma.instMagma

theorem MagmaLaw.models_iff {α : Type} {G : Type → Type} (law : MagmaLaw α) [LiftingMagma G] :
    (satisfiesPhi (G := G α) LiftingMagma.ι law) ↔
    (G α ⊧ law) := by
  constructor
  · intro h
    intro f
    have := LiftingMagma.lift_factors f
    rw [this, satisfiesPhi.evalHom, h]
  · intro h
    apply h
