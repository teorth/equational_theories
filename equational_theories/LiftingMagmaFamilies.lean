import equational_theories.MagmaLaw
import equational_theories.Homomorphisms
import equational_theories.ForMathlib.Enum.Enum

open Law

class LiftingMagma (G : Type → Type) where
  instMagma {α} : Magma (G α)
  instMagmaDecidableEq {α} [DecidableEq α] : DecidableEq (G α)
  ι : ∀ {α}, α → G α
  lift : ∀ {α}, (α → G α) → (G α →◇ G α)
  lift_factors : ∀ {α}, ∀ f : α → G α, f = (lift f) ∘ ι

variable {α : Type} {G : Type → Type} [LiftingMagma G]

instance : Magma (G α) := LiftingMagma.instMagma

instance [DecidableEq α] : DecidableEq (G α) :=
  LiftingMagma.instMagmaDecidableEq

theorem MagmaLaw.models_iff_satisfies_ι (law : MagmaLaw α) :
    G α ⊧ law ↔ satisfiesPhi (G := G α) LiftingMagma.ι law := by
  constructor
  · intro h
    apply h
  · intro h
    intro f
    have := LiftingMagma.lift_factors f
    rw [this, satisfiesPhi.evalHom, h]

instance [DecidableEq α] (law : MagmaLaw α) : Decidable (G α ⊧ law) := by
  rw [MagmaLaw.models_iff_satisfies_ι, satisfiesPhi]
  infer_instance

section Instances

instance instMagmaList {α : Type _} : Magma (List α) where
  op := List.append

instance : LiftingMagma List where
  instMagma := instMagmaList
  instMagmaDecidableEq := inferInstance
  ι := fun a ↦ [a]
  lift f := {
    toFun := (List.bind · f),
    map_op' := by
      intro x y
      show (x ++ y).bind f = (x.bind f ++ y.bind f)
      rw [List.bind, List.bind, List.bind, ← List.join_append, List.map_append]
  }
  lift_factors := by
    intro α f
    funext x
    symm
    apply List.bind_singleton

end Instances
