import Mathlib.Order.Defs
import Mathlib.Data.Set.Basic
import equational_theories.MagmaLaw

open Law

namespace Law.MagmaLaw

variable {α : Type*}

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
    ({ ⟨G, _⟩ | G ⊧ l₁ } : Set (Σ G : Type, Magma G)) ⊆ { ⟨G, _⟩ | G ⊧ l₂ } :=
  fun ⟨_, _⟩ h1 ↦ h h1

/--
A stronger law is smaller than a weaker law, because this corresponds to the inclusion of
the class of magmas that obey these laws:  the class of magmas that obey the stronger law is a
subset of the class of magmas that obey the weaker law.
-/
theorem le_set {α} (l₁ l₂ : MagmaLaw α) (h : l₁ ≤ l₂) :
    ({ ⟨G, _⟩ | G ⊧ l₁ } : Set (Σ G : Type, Magma G)) ⊆ { ⟨G, _⟩ | G ⊧ l₂ } :=
  implies_set _ _ h

/--
The law `0 ≃ 0` is the maximal element in the pre-order on magma laws (over ℕ).  -/
theorem Equation1_maximal (l : MagmaLaw ℕ) : l ≤ (0 ≃ 0) :=
  fun _ _ ↦ rfl

theorem Equation2_all_eq {G} [Magma G] (h : G ⊧ (0 ≃ 1 : MagmaLaw ℕ)) :
    ∀ (x y : G), x = y := by
  refine fun x y ↦ h (fun n => match n with
    | 0 => x
    | 1 => y
    | _ => x)

theorem Equation2_implies (l : MagmaLaw ℕ) : (0 ≃ 1).implies l := by
  intro G inst h φ
  have hG := Equation2_all_eq h
  simp only [satisfiesPhi]
  induction l.lhs <;> induction l.rhs <;>
    simp only [FreeMagma.evalInMagma] <;> aesop

/--
The law `0 ≃ 1` is the minimal element in the pre-order on magma laws (over ℕ).  -/
theorem Equation2_minimal (l : MagmaLaw ℕ) : (0 ≃ 1) ≤ l := Equation2_implies _

theorem implies_refl (l : MagmaLaw α) : l ≤ l := fun {G} [Magma G] a ↦ a

theorem implies_trans {l₁ l₂ l₃ : MagmaLaw α} : l₁ ≤ l₂ → l₂ ≤ l₃ → l₁ ≤ l₃ :=
  fun h₁ h₂ _ _ h ↦ h₂ (h₁ h)

instance : Preorder (MagmaLaw α) where
  le_refl := implies_refl
  le_trans := fun _ _ _ ↦ implies_trans

theorem implies_eq_singleton_models {l₁ l₂ : MagmaLaw α} : l₁ ≤ l₂ ↔ {l₁} ⊧ l₂ := by
  simp only [LE.le, implies, models, satisfiesSet, Ctx, Set.mem_singleton_iff, forall_eq]

theorem Law.implies_fin_implies_nat {n : Nat} {l₁ l₂ : MagmaLaw (Fin n)}
    (h : l₁.implies l₂) : (l₁.map Fin.val).implies (l₂.map Fin.val) := by
  intro G inst hG
  rw [satisfies_fin_satisfies_nat G l₂]
  rw [satisfies_fin_satisfies_nat G l₁] at hG
  exact h hG

theorem Law.leq_fin_leq_nat {n : Nat} {l₁ l₂ : MagmaLaw (Fin n)} (h : l₁ ≤ l₂) :
    l₁.map Fin.val ≤ l₂.map Fin.val :=
  implies_fin_implies_nat h

end Law.MagmaLaw
