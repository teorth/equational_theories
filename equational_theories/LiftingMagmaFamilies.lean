import equational_theories.MagmaLaw
import equational_theories.Homomorphisms
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finsupp.Defs
-- import Mathlib.Algebra.Free

open Law

class LiftingMagmaFamily (G : Type _ → Type _) where
  instMagma (α) [DecidableEq α] : Magma (G α)
  instMagmaDecidableEq {α} [DecidableEq α] : DecidableEq (G α)
  ι : ∀ {α}, α → G α
  lift : ∀ {α} [DecidableEq α], (α → G α) → (G α →◇ G α)
  lift_factors : ∀ {α} [DecidableEq α], ∀ f : α → G α, f = (lift f) ∘ ι

variable {α : Type _} [DecidableEq α] (G : Type → Type) [family : LiftingMagmaFamily G]

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

instance [DecidableEq α] (law : MagmaLaw α) :  Decidable (@satisfiesPhi α (G α) (LiftingMagmaFamily.instMagma α) LiftingMagmaFamily.ι law) :=
  inferInstanceAs <| Decidable (law.lhs ⬝ LiftingMagmaFamily.ι = law.rhs ⬝ LiftingMagmaFamily.ι)

instance instDecidableSatisfiesLaw [DecidableEq α] (law : MagmaLaw α) : Decidable (G α ⊧ law) :=
  decidable_of_decidable_of_iff (MagmaLaw.models_iff_satisfies_ι G law).symm

lemma LiftingMagmaFamily.establishNonimplication {law law' : MagmaLaw Nat} {P P' : (M : Type _) → [Magma M] → Prop}
  (hlaw_iff : ∀ (G : Type _) [Magma G], G ⊧ law ↔ P G) (hlaw'_iff : ∀ (G : Type _) [Magma G], G ⊧ law' ↔ P' G)
  (h : G ℕ ⊧ law := by decide) (h' : ¬ G ℕ ⊧ law' := by decide) :
    ∃ (G : Type) (_ : Magma G), P G ∧ ¬ P' G :=
  ⟨G ℕ, inferInstance, (hlaw_iff _).mp h, (not_iff_not.mpr (hlaw'_iff _)).mp h'⟩

section Instances

instance instMagmaList {α : Type _} : Magma (List α) where
  op := List.append

instance : LiftingMagmaFamily List where
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

instance : LiftingMagmaFamily Multiset where
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

instance instLiftingMagmaFamilyLeftProj : LiftingMagmaFamily LeftProj where
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

instance instLiftingMagmaFamilyRightProj : LiftingMagmaFamily RightProj where
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
