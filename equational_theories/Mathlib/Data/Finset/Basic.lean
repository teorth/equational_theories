import Mathlib.Data.Finset.Basic

variable {α β : Type*} {f : α → β} {s : Finset α} {t : Set β} {t' : Finset β}

-- Mathlib PR: https://github.com/leanprover-community/mathlib4/pull/17976
instance [DecidablePred (· ∈ t)] : Decidable (Set.MapsTo f s t) :=
  inferInstanceAs (Decidable (∀ x ∈ s, f x ∈ t))

-- Mathlib PR: https://github.com/leanprover-community/mathlib4/pull/17976
-- The `DecidableEq` instance on `α` can be avoided.
instance [DecidableEq α] [DecidableEq β] : Decidable (Set.InjOn f s) :=
  inferInstanceAs (Decidable (∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y))

-- Mathlib PR: https://github.com/leanprover-community/mathlib4/pull/17976
instance [DecidableEq β] : Decidable (Set.SurjOn f s t') :=
  inferInstanceAs (Decidable (∀ x ∈ t', ∃ y ∈ s, f y = x))

-- Mathlib PR: https://github.com/leanprover-community/mathlib4/pull/17976
instance [DecidableEq α] [DecidableEq β] : Decidable (Set.BijOn f s t') :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
