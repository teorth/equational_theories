﻿-- This countermodel was automatically generated using Z3.
-- It refutes x ◇ (x ◇ y) = x ◇ (y ◇ x) -> x ◇ (y ◇ z) = x ◇ (z ◇ y)
import equational_theories.Magma
import equational_theories.Equations.All
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

inductive M :=
| M_val_2
| M_val_5
| M_val_1
| M_val_4
| M_val_3
| M_val_6
| M_val_0
deriving DecidableEq, Fintype

def m (x y : M) : M :=
match x, y with
| M.M_val_2, M.M_val_2 => M.M_val_6
| M.M_val_2, M.M_val_5 => M.M_val_6
| M.M_val_2, M.M_val_1 => M.M_val_5
| M.M_val_2, M.M_val_4 => M.M_val_6
| M.M_val_2, M.M_val_3 => M.M_val_6
| M.M_val_2, M.M_val_6 => M.M_val_6
| M.M_val_2, M.M_val_0 => M.M_val_6
| M.M_val_5, M.M_val_2 => M.M_val_6
| M.M_val_5, M.M_val_5 => M.M_val_6
| M.M_val_5, M.M_val_1 => M.M_val_6
| M.M_val_5, M.M_val_4 => M.M_val_6
| M.M_val_5, M.M_val_3 => M.M_val_6
| M.M_val_5, M.M_val_6 => M.M_val_6
| M.M_val_5, M.M_val_0 => M.M_val_6
| M.M_val_1, M.M_val_2 => M.M_val_3
| M.M_val_1, M.M_val_5 => M.M_val_6
| M.M_val_1, M.M_val_1 => M.M_val_6
| M.M_val_1, M.M_val_4 => M.M_val_3
| M.M_val_1, M.M_val_3 => M.M_val_6
| M.M_val_1, M.M_val_6 => M.M_val_3
| M.M_val_1, M.M_val_0 => M.M_val_6
| M.M_val_4, M.M_val_2 => M.M_val_6
| M.M_val_4, M.M_val_5 => M.M_val_6
| M.M_val_4, M.M_val_1 => M.M_val_5
| M.M_val_4, M.M_val_4 => M.M_val_6
| M.M_val_4, M.M_val_3 => M.M_val_6
| M.M_val_4, M.M_val_6 => M.M_val_6
| M.M_val_4, M.M_val_0 => M.M_val_6
| M.M_val_3, M.M_val_2 => M.M_val_6
| M.M_val_3, M.M_val_5 => M.M_val_6
| M.M_val_3, M.M_val_1 => M.M_val_6
| M.M_val_3, M.M_val_4 => M.M_val_6
| M.M_val_3, M.M_val_3 => M.M_val_6
| M.M_val_3, M.M_val_6 => M.M_val_6
| M.M_val_3, M.M_val_0 => M.M_val_6
| M.M_val_6, M.M_val_2 => M.M_val_6
| M.M_val_6, M.M_val_5 => M.M_val_6
| M.M_val_6, M.M_val_1 => M.M_val_5
| M.M_val_6, M.M_val_4 => M.M_val_6
| M.M_val_6, M.M_val_3 => M.M_val_6
| M.M_val_6, M.M_val_6 => M.M_val_6
| M.M_val_6, M.M_val_0 => M.M_val_6
| M.M_val_0, M.M_val_2 => M.M_val_6
| M.M_val_0, M.M_val_5 => M.M_val_6
| M.M_val_0, M.M_val_1 => M.M_val_6
| M.M_val_0, M.M_val_4 => M.M_val_6
| M.M_val_0, M.M_val_3 => M.M_val_4
| M.M_val_0, M.M_val_6 => M.M_val_6
| M.M_val_0, M.M_val_0 => M.M_val_6

instance M.Magma : Magma M := ⟨ m ⟩

@[equational_result]
theorem Equation4283_not_implies_Equation4358 :  ∃ (G: Type) (_: Magma G), Equation4283 G ∧ ¬ Equation4358 G :=
by exists M, M.Magma
