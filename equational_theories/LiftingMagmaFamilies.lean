import equational_theories.MagmaLaw
import equational_theories.Homomorphisms
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finsupp.Defs
-- import Mathlib.Algebra.Free

open Law

class LiftingMagmaFamily (G : Type → Type) where
  instMagma (α) [DecidableEq α] : Magma (G α)
  instMagmaDecidableEq {α} [DecidableEq α] : DecidableEq (G α)
  ι : ∀ {α}, α → G α
  lift : ∀ {α} [DecidableEq α], (α → G α) → (G α →◇ G α)
  lift_factors : ∀ {α} [DecidableEq α], ∀ f : α → G α, f = (lift f) ∘ ι

variable {α : Type} [DecidableEq α] (G : Type → Type) [LiftingMagmaFamily G]

instance [LiftingMagmaFamily G] : Magma (G α) := LiftingMagmaFamily.instMagma α

instance [DecidableEq α] : DecidableEq (G α) :=
  LiftingMagmaFamily.instMagmaDecidableEq

theorem MagmaLaw.models_iff_satisfies_ι (law : MagmaLaw α) :
    G α ⊧ law ↔ satisfiesPhi (G := G α) LiftingMagmaFamily.ι law := by
  constructor
  · intro h
    apply h
  · intro h
    intro f
    have := LiftingMagmaFamily.lift_factors f
    rw [this, satisfiesPhi_evalHom, h]

instance instDecidableSatisfiesLaw [DecidableEq α] (law : MagmaLaw α) : Decidable (G α ⊧ law) := by
  rw [MagmaLaw.models_iff_satisfies_ι, satisfiesPhi]
  infer_instance

section Instances

instance instMagmaList {α : Type _} : Magma (List α) where
  op := List.append

instance : LiftingMagmaFamily (List ·) where
  instMagmaDecidableEq := inferInstance
  ι := fun a ↦ [a]
  lift f := {
    toFun := (List.bind · f),
    map_op' := by
      intro x y
      dsimp [Magma.op, List.bind]
      rw [← List.join_append, List.map_append]
  }
  lift_factors := by
    intro α _ f
    funext x
    symm
    apply List.bind_singleton

instance (priority := high) instMagmaMultiset (α : Type _) [DecidableEq α] : Magma (Multiset α) where
  op := (· + ·)

instance : LiftingMagmaFamily (Multiset ·) where
  instMagma := instMagmaMultiset
  instMagmaDecidableEq := inferInstance
  ι := fun a ↦ {a}
  lift f := {
    toFun := (Multiset.bind · f),
    map_op' := by
      intro _ _
      dsimp [Magma.op, Multiset.bind]
      rw [Multiset.map_add, Multiset.join_add]
    }
  lift_factors := by
    intro α _ f
    funext x
    symm
    apply Multiset.singleton_bind

def LeftProj (α : Type _) := α

instance (priority := low) leftProj (α : Type _) : Magma (LeftProj α) where
  op := fun a _ => a

instance instLiftingMagmaFamilyLeftProj : @LiftingMagmaFamily (LeftProj ·) where
  instMagma := (leftProj ·)
  instMagmaDecidableEq := inferInstance
  ι := id
  lift f := {
    toFun := f,
    map_op' := by
      intro x y
      rfl
  }
  lift_factors := by
    intro α _ f
    funext x
    rfl

def RightProj (α : Type _) := α

instance (priority := low+1) rightProj (α : Type _) : Magma (RightProj α) where
  op := fun _ a => a

instance instLiftingMagmaFamilyRightProj : @LiftingMagmaFamily (RightProj ·) where
  instMagma := (rightProj ·)
  instMagmaDecidableEq := inferInstance
  ι := id
  lift f := {
    toFun := f,
    map_op' := by
      intro x y
      rfl
  }
  lift_factors := by
    intro α _ f
    funext x
    rfl

-- TODO: Lifting family FreeMagma

end Instances
