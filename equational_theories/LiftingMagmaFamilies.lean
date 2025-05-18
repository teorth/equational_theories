import equational_theories.MagmaLaw
import equational_theories.Homomorphisms
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Finset.Union
import equational_theories.Completeness

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
    G α ⊧ law ↔ satisfiesPhi (G := G α) LiftingMagmaFamily.ι law :=
  ⟨fun h ↦ h _, fun h f ↦ by rw [LiftingMagmaFamily.lift_factors f, satisfiesPhi_evalHom, h]⟩

instance [DecidableEq α] (law : MagmaLaw α) :  Decidable (@satisfiesPhi α (G α) (LiftingMagmaFamily.instMagma α) LiftingMagmaFamily.ι law) :=
  inferInstanceAs <| Decidable (law.lhs ⬝ LiftingMagmaFamily.ι = law.rhs ⬝ LiftingMagmaFamily.ι)

instance instDecidableSatisfiesLaw [DecidableEq α] (law : MagmaLaw α) : Decidable (G α ⊧ law) :=
  decidable_of_decidable_of_iff (MagmaLaw.models_iff_satisfies_ι G law).symm

lemma LiftingMagmaFamily.establishNonimplication {law law' : MagmaLaw Nat} {P P' : (M : Type _) → [Magma M] → Prop}
  (hlaw_iff : ∀ {G} [Magma G], G ⊧ law ↔ P G) (hlaw'_iff : ∀ {G} [Magma G], G ⊧ law' ↔ P' G)
  (h : G ℕ ⊧ law := by decide) (h' : ¬ G ℕ ⊧ law' := by decide) :
    ∃ (G : Type) (_ : Magma G), P G ∧ ¬ P' G :=
  ⟨G ℕ, inferInstance, hlaw_iff.mp h, (not_iff_not.mpr hlaw'_iff).mp h'⟩

section Instances

instance instMagmaList {α : Type _} : Magma (List α) where
  op := List.append

instance : LiftingMagmaFamily List where
  instMagma := fun α [DecidableEq α] ↦ instMagmaList
  instMagmaDecidableEq := inferInstance
  ι := fun a ↦ [a]
  lift f := {
    toFun := List.flatMap f,
    map_op' := by
      intro x y
      dsimp [Magma.op, List.flatMap]
      rw [← List.flatten_append, List.map_append]
  }
  lift_factors := by
    intro α _ f
    funext x
    exact (List.flatMap_singleton _ _).symm


instance (priority := high) instMagmaMultiset (α : Type _) [DecidableEq α] : Magma (Multiset α) where
  op := (· + ·)

instance : LiftingMagmaFamily Multiset where
  instMagma := instMagmaMultiset
  instMagmaDecidableEq := inferInstance
  ι := fun a ↦ {a}
  lift f := {
    toFun := (Multiset.bind · f),
    map_op' := by
      intros
      dsimp [Magma.op, Multiset.bind]
      rw [Multiset.map_add, Multiset.join_add]
    }
  lift_factors := by
    intros
    funext x
    exact (Multiset.singleton_bind _ _).symm

def LeftProj (α : Type _) := α

instance (priority := low) leftProj (α : Type _) : Magma (LeftProj α) where
  op := fun a _ => a

instance instLiftingMagmaFamilyLeftProj : LiftingMagmaFamily LeftProj where
  instMagma := (leftProj ·)
  instMagmaDecidableEq := inferInstance
  ι := id
  lift f := {
    toFun := f,
    map_op' := fun _ _ ↦ rfl
  }
  lift_factors := by intros; rfl

def RightProj (α : Type _) := α

instance (priority := low+1) rightProj (α : Type _) : Magma (RightProj α) where
  op := fun _ a ↦ a

instance instLiftingMagmaFamilyRightProj : LiftingMagmaFamily RightProj where
  instMagma := (rightProj ·)
  instMagmaDecidableEq := inferInstance
  ι := id
  lift f := {
    toFun := f,
    map_op' := fun _ _ ↦ rfl
  }
  lift_factors := by intros; rfl

instance instLiftingMagmaFamilyFreeMagmaWithLaws {α} (Γ : Ctx α)
    [∀ α [DecidableEq α], DecidableEq (FreeMagmaWithLaws α Γ)] : LiftingMagmaFamily (FreeMagmaWithLaws · Γ) where
  instMagma := inferInstance
  instMagmaDecidableEq := inferInstance
  ι := fun a ↦ embed Γ (.Leaf a)
  lift {α} _ f := FreeMagmaWithLaws.evalHom (G := FreeMagmaWithLaws α Γ) f (FreeMagmaWithLaws.isModel α Γ)
  lift_factors := by intros; ext; rfl

instance (priority := high) instMagmaFinset (α : Type _) [DecidableEq α] : Magma (Finset α) where
  op := (· ∪ ·)

instance : LiftingMagmaFamily Finset where
  instMagma := instMagmaFinset
  instMagmaDecidableEq := inferInstance
  ι := fun a ↦ {a}
  lift f := {
    toFun := (Finset.biUnion · f),
    map_op' := by
      intro x _
      dsimp [Magma.op]
      induction x using Finset.induction
      · simp
      · simp only [Finset.insert_union, Finset.biUnion_insert, Finset.union_assoc]
        congr
    }
  lift_factors := by
    intro α _ f
    funext x
    symm
    apply Finset.singleton_biUnion

-- TODO: Lifting family FreeMagma

end Instances
