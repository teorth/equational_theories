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
  le l₁ l₂ := l₁.implies l₂

theorem implies_set {α} (l₁ l₂ : MagmaLaw α) (h : l₁.implies l₂) :
  { Sigma.mk G inst | @satisfies α G inst l₁ } ⊆ { Sigma.mk G inst | @satisfies α G inst l₂ } := by
  simp_all [Membership.mem, Set.Mem]
  intro ⟨G,inst⟩ h1
  exact h h1

/--
A stronger law is smaller than a weaker law, because this corresponds to the inclusion of
the class of magmas that obey these laws:  the class of magmas that obey the stronger law is a
subset of the class of magmas that obey the weaker law.
-/
theorem le_set {α} (l₁ l₂ : MagmaLaw α) (h : l₁ ≤ l₂) :
  { Sigma.mk G inst | @satisfies α G inst l₁ } ⊆ { Sigma.mk G inst | @satisfies α G inst l₂ } := by
  apply implies_set; exact h

/--
The law `0 ≃ 0` is the maximal element in the pre-order on magma laws (over ℕ).  -/
theorem Equation1_maximal (l : MagmaLaw ℕ) : l ≤ (0 ≃ 0) := by
  intro _ _ _ _
  simp_all only [satisfies, satisfiesPhi]

theorem Equation2_all_eq {G} [Magma G] (h : G ⊧ (0 ≃ 1 : MagmaLaw ℕ)) :
  ∀ (x y : G), x = y := by
  intro x y
  refine h (fun n => match n with
    | 0 => x
    | 1 => y
    | _ => x)

theorem Equation2_implies (l : MagmaLaw ℕ) : (0 ≃ 1).implies l := by
  intro G inst h φ
  have hG := Equation2_all_eq h
  simp [satisfies, satisfiesPhi, FreeMagma.evalInMagma]
  induction l.lhs <;> induction l.rhs <;>
    simp [FreeMagma.evalInMagma, hG] <;> aesop

/--
The law `0 ≃ 1` is the minimal element in the pre-order on magma laws (over ℕ).  -/
theorem Equation2_minimal (l : MagmaLaw ℕ) : (0 ≃ 1) ≤ l := by
  apply Equation2_implies

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

end Law.MagmaLaw
