import Mathlib.Data.Finset.Basic
import equational_theories.Mathlib.Data.Set.Function

variable {α β : Type*} {f : α → β} {s : Finset α} {t : Set β} {t' : Finset β}

instance [DecidablePred (· ∈ t)] : Decidable (Set.MapsTo f s t) :=
  inferInstanceAs (Decidable (∀ x ∈ s, f x ∈ t))

-- The `DecidableEq` instance on `α` can be avoided.
instance [DecidableEq α] [DecidableEq β] : Decidable (Set.InjOn f s) :=
  inferInstanceAs (Decidable (∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y))

instance [DecidableEq β] : Decidable (Set.SurjOn f s t') :=
  inferInstanceAs (Decidable (∀ x ∈ t', ∃ y ∈ s, f y = x))

instance [DecidableEq α] [DecidableEq β] : Decidable (Set.BijOn f s t') :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
