import Mathlib.Order.Defs
import equational_theories.MagmaLaw

namespace MagmaLaw

universe u
variable {α : Type u}

/--
A magma law `l₁` implies a law `l₂` if in any Magma `G` where `l₁` holds, `l₂` also holds.

We have to explicitly quantify the type `G` and the Magma instance `[Magma G]` instead of
using them as parameters so that the implication holds in any Magma `G`.
-/
def implies (l₁ l₂ : MagmaLaw α) := ∀ {G : Type u} [Magma G] {f : α → G},
   l₁.lhs.evalInMagma f = l₁.rhs.evalInMagma f → l₂.lhs.evalInMagma f = l₂.rhs.evalInMagma f

instance : LE (MagmaLaw α) where
  le l₁ l₂ := l₁.implies l₂

theorem implies_refl (l : MagmaLaw α) : l ≤ l := by
  intro G inst f h; exact h

theorem implies_trans {l₁ l₂ l₃ : MagmaLaw α} : l₁ ≤ l₂ → l₂ ≤ l₃ → l₁ ≤ l₃ := by
  intros h₁ h₂ G inst f h
  exact h₂ (h₁ h)

instance : Preorder (MagmaLaw α) where
  le_refl := implies_refl
  le_trans := fun _ _ _ => implies_trans

end MagmaLaw
