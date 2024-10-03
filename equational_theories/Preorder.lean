import Mathlib.Order.Defs
import Mathlib.Data.Set.Basic
import equational_theories.Completeness

namespace MagmaLaw

variable {α : Type}

/--
A magma law `l₁` implies a law `l₂` if in any Magma `G` where `l₁` holds, `l₂` also holds.

We have to explicitly quantify the type `G` and the Magma instance `[Magma G]` instead of
using them as parameters so that the implication holds in any Magma `G`.
-/
def implies (l₁ l₂ : MagmaLaw α) := ∀ {G : Type} [Magma G],
  satisfies G l₁ → satisfies G l₂

instance : LE (MagmaLaw α) where
  le l₁ l₂ := l₁.implies l₂

theorem implies_refl (l : MagmaLaw α) : l ≤ l := fun {G} [Magma G] a ↦ a

theorem implies_trans {l₁ l₂ l₃ : MagmaLaw α} : l₁ ≤ l₂ → l₂ ≤ l₃ → l₁ ≤ l₃ := by
  intro h₁ h₂ G inst h
  dsimp only [satisfies, satisfiesPhi] at *
  exact h₂ (h₁ h)

instance : Preorder (MagmaLaw α) where
  le_refl := implies_refl
  le_trans := fun _ _ _ ↦ implies_trans

theorem implies_eq_singleton_models {l₁ l₂ : MagmaLaw α} : l₁ ≤ l₂ ↔ {l₁} ⊧ l₂ := by
  simp only [LE.le, implies, models, satisfiesSet, Ctx, Set.mem_singleton_iff, forall_eq]

end MagmaLaw
