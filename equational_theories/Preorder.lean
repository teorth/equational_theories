import Mathlib.Order.Defs
import Mathlib.Data.Set.Basic
import equational_theories.MagmaLaw

open Law

namespace Law.MagmaLaw

variable {α : Type}

/--
A magma law `l₁` implies a law `l₂` if in any Magma `G` where `l₁` holds, `l₂` also holds.

We have to explicitly quantify the type `G` and the Magma instance `[Magma G]` instead of
using them as parameters so that the implication holds in any Magma `G`.
-/
def implies (l₁ l₂ : MagmaLaw α) := ∀ {G : Type} [Magma G],
  satisfies G l₁ → satisfies G l₂


/--
If a law `l₁` implies a law `l₂`, then we say `l₁ ≤ l₂`.
-/
instance : LE (MagmaLaw α) where
  le l₁ l₂ := l₂.implies l₁

/--
A stronger law is smaller than a weaker law, because this corresponds to the inclusion of
the class of magmas that obey these laws:  the class of magmas that obey the stronger law is a
subset of the class of magmas that obey the weaker law.
-/
theorem implies_set {α} (l₁ l₂ : MagmaLaw α) (h : l₁.implies l₂) :
  { Sigma.mk G inst | @satisfies α G inst l₁ } ⊆ { Sigma.mk G inst | @satisfies α G inst l₂ } := by
  simp_all [Membership.mem, Set.Mem]
  intro ⟨G,inst⟩ h1
  exact h h1

theorem implies_refl (l : MagmaLaw α) : l ≤ l := fun {G} [Magma G] a ↦ a

theorem implies_trans {l₁ l₂ l₃ : MagmaLaw α} : l₁ ≤ l₂ → l₂ ≤ l₃ → l₁ ≤ l₃ := by
  intro h₁ h₂ G inst h
  dsimp only [satisfies, satisfiesPhi] at *
  exact h₁ (h₂ h)

instance : Preorder (MagmaLaw α) where
  le_refl := implies_refl
  le_trans := fun _ _ _ ↦ implies_trans

theorem implies_eq_singleton_models {l₁ l₂ : MagmaLaw α} : l₁ ≤ l₂ ↔ {l₂} ⊧ l₁ := by
  simp only [LE.le, implies, models, satisfiesSet, Ctx, Set.mem_singleton_iff, forall_eq]

end Law.MagmaLaw
