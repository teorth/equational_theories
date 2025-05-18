import Mathlib.Data.List.Lemmas

namespace List

universe u

variable {α : Type u}

-- [DUPLICATE] PR: https://github.com/leanprover-community/mathlib4/pull/22511
-- theorem append_cancel_right_length {as bs bs' cs : List α}
-- (eq_length : bs.length = bs'.length) (h : as ++ bs = cs ++ bs') : (as = cs) := by
--  match as, cs with
--  | [], []       => rfl
--  | [], c::cs    => have aux := congrArg length h; simp +arith +decide [eq_length] at aux
--  | a::as, []    => have aux := congrArg length h; simp +arith +decide [eq_length] at aux
--  | a::as, c::cs => injection h with h₁ h₂; subst h₁; rw [append_cancel_right_length eq_length h₂]

@[deprecated (since := "2025-05-18")] alias append_cancel_right_length := List.append_inj_left'

-- [UPSTREAMED] PR: https://github.com/leanprover-community/mathlib4/pull/22510
-- theorem head?_flatten_replicate {n : ℕ} {as : List α} (h : n ≠ 0) :
-- ((List.replicate n as).flatten.head?) = as.head? := by
-- match n, as with
-- | 0, _ => exfalso; exact h rfl
-- | n+1, [] => simp
-- | n+1, h::_ => simp [replicate]

-- [UPSTREAMED] PR: https://github.com/leanprover-community/mathlib4/pull/22510
-- theorem getLast?_flatten_replicate  {n : ℕ} {as : List α} (h : n ≠ 0) :
-- ((List.replicate n as).flatten.getLast?) = as.getLast? := by
--   rw [← List.head?_reverse, ← List.head?_reverse,List.reverse_flatten, List.map_replicate,
--   List.reverse_replicate,head?_flatten_replicate h]
