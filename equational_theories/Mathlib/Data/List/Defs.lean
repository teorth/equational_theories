import Mathlib.Data.List.Defs
import Mathlib.Data.List.Chain

namespace List

variable {α : Type*}
instance decidableChain {R : α → α → Prop} [DecidableRel R] (l : List α) :
    Decidable (IsChain R l) := by
  induction l with
  | nil => exact .isTrue .nil
  | cons a as ih => exact decidable_of_iff' _ List.isChain_cons
