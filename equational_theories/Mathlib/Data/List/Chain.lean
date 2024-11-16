import Mathlib.Data.List.Chain

namespace List

universe u

variable {α : Type u}

variable {R : α → α → Prop}

theorem chain'_iff_all_append_cons_cons {l : List α} : Chain' R l ↔
∀ {a b} {l₁ l₂}, l = l₁ ++ (a :: b :: l₂) → R a b := by
  constructor
  · exact fun h _ _ _ _ eq => (chain'_append_cons_cons.mp (eq ▸ h)).2.1
  · induction l with
  | nil => exact fun _ ↦ chain'_nil
  | cons head tail ih =>
    intro h
    cases tail with
    | nil => exact chain'_singleton head
    | cons head' tail =>
      rw [chain'_cons]
      constructor
      · apply h (nil_append _).symm
      · apply ih
        intro a b l₁ l₂ eq
        apply h (l₁ := head :: l₁) (l₂ := l₂)
        rw [eq]
        simp

end List
