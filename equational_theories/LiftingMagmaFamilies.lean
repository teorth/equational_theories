import equational_theories.MagmaLaw
import equational_theories.Homomorphisms
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finsupp.Defs
-- import Mathlib.Algebra.Free

open Law

class LiftingMagmaFamily (G : (α : Type) → [DecidableEq α] → Type) [∀ α [DecidableEq α], Magma (G α)] where
  instMagmaDecidableEq {α} [DecidableEq α] : DecidableEq (G α)
  ι : ∀ {α} [DecidableEq α], α → G α
  lift : ∀ {α} [DecidableEq α], (α → G α) → (G α →◇ G α)
  lift_factors : ∀ {α} [DecidableEq α], ∀ f : α → G α, f = (lift f) ∘ ι

variable {α : Type} [DecidableEq α] (G : (α : Type) → [DecidableEq α] → Type)
  [∀ α [DecidableEq α], Magma (G α)] [LiftingMagmaFamily G]

instance [DecidableEq α] : DecidableEq (G α) :=
  LiftingMagmaFamily.instMagmaDecidableEq

theorem MagmaLaw.models_iff_satisfies_ι (law : MagmaLaw α) :
    G α ⊧ law ↔ satisfiesPhi (G := G α) LiftingMagmaFamily.ι law := by
  constructor
  · intro h
    apply h
  · intro h f
    have := LiftingMagmaFamily.lift_factors f
    rw [this, satisfiesPhi_evalHom, h]

instance instDecidableSatisfies [DecidableEq α] (law : MagmaLaw α) : Decidable (G α ⊧ law) := by
  rw [MagmaLaw.models_iff_satisfies_ι, satisfiesPhi]
  infer_instance

set_option linter.unusedSectionVars false in
lemma proveNonimplication {law law' : NatMagmaLaw} {P P' : (G : Type _) → Prop}
  (models_law_iff : G Nat ⊧ law ↔ P (G Nat)) (models_law'_iff : G Nat ⊧ law' ↔ P' (G Nat))
  (hlaw : G Nat ⊧ law) (hlaw' : ¬(G Nat ⊧ law')) : ∃ (M : Type _) (_ : Magma M), P M ∧ ¬ (P' M) :=
  ⟨G Nat, inferInstance, models_law_iff.mp hlaw, ((not_iff_not).mpr models_law'_iff).mp hlaw'⟩

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

instance (priority := low) leftProj (α : Type _) : Magma α where
  op := fun a _ => a

instance instLiftingMagmaFamilyLeftProj : @LiftingMagmaFamily (Id ·) (leftProj ·) where
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

instance (priority := low) rightProj (α : Type _) : Magma α where
  op := fun _ a => a

instance instLiftingMagmaFamilyRightProj : @LiftingMagmaFamily (Id ·) (rightProj ·) where
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

instance instMagmaMultiset {α : Type _} [DecidableEq α] : Magma (Finset α) where
  op := Union.union

instance : LiftingMagmaFamily (Multiset ·) where
  instMagmaDecidableEq := inferInstance
  ι := fun a ↦ {a}
  lift f := {
    toFun := (Multiset.bind · f),
    map_op' := by
      intro _ _
      dsimp only [Magma.op]
    }
  lift_factors := by
    intro α _ f
    funext x
    symm
    apply Multiset.singleton_bind

-- TODO: Lifting family FreeMagma

end Instances
