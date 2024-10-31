import Mathlib.Data.List.Defs

namespace List

variable {α : Type*}
instance decidableChain_2 {R : α → α → Prop} [DecidableRel R] (a : α) (l : List α) :
    Decidable (Chain R a l) := by
  induction l generalizing a with
  | nil => exact .isTrue .nil
  | cons a as ih => exact decidable_of_iff' _ List.chain_cons

instance decidableChain'_2 {R : α → α → Prop} [DecidableRel R] (l : List α) :
    Decidable (Chain' R l) := by
  cases l <;> dsimp only [List.Chain'] <;> infer_instance
