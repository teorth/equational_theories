/-
  Define the free commutative magma as the multisets with union.
  Prove

-/
import Mathlib.Data.Multiset.Basic
import equational_theories.FreeMagma
import equational_theories.Completeness


instance Multiset.isMagma {α} [DecidableEq α] : Magma (Multiset α) := { op := (. + .) }

@[simp]
def FreeMagma.count {α} [DecidableEq α] (w : FreeMagma α)(a : α) : ℕ :=
match w with
| .Leaf x => if a = x then 1 else 0
| .Fork w₁ w₂ => w₁.count a + w₂.count a

lemma Multiset.count_is_free_count {α} [DecidableEq α] (w : FreeMagma α)(a : α) :
  (evalInMagma (G := Multiset α) (λ x ↦ {x}) w).count a = w.count a :=
by
  cases w
  case Leaf x =>
    simp [evalInMagma]
    exact Multiset.count_singleton _ _
  case Fork w₁ w₁ =>
    simp [evalInMagma, Magma.op]
    repeat rw [Multiset.count_is_free_count]

def FreeMagma.SameCount {α} [DecidableEq α] (w₁ w₂ : FreeMagma α) :=
  ∀ a, w₁.count a = w₂.count a

open Law

#check (λ w₁ w₂ : FreeMagma ℕ ↦ w₁ ≃ w₂)

#check Multiset.ext

lemma Multiset.same_count_sat {α} [DecidableEq α] (w₁ w₂ : FreeMagma α) :
  FreeMagma.SameCount w₁ w₂ ↔ Multiset α ⊧ w₁ ≃ w₂ :=
by
  simp [FreeMagma.SameCount, satisfies, satisfiesPhi]
  constructor
  . intros
    rw [Multiset.ext]; intro
    -- FIXME: uh oh, this is true but does not follow forom the count_is_free count lemma.
    -- we need to generalize.
    sorry
  . intros h a
    have h := h (λ x ↦ {x})
    repeat rw [← Multiset.count_is_free_count]
    rw [h]

theorem CountIsPreserved {α} [DecidableEq α] (w₁ w₂ w₃ w₄ : FreeMagma α) :
  Set.singleton (w₁ ≃ w₂) ⊧ w₃ ≃ w₄ → FreeMagma.SameCount w₁ w₂ → FreeMagma.SameCount w₃ w₄ :=
by
  repeat rw [Multiset.same_count_sat]
  intros mod sat
  apply mod; simp [satisfiesSet, Set.singleton]; trivial
