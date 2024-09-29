-- This countermodel was automatically generated using Z3.
import equational_theories.Magma
import equational_theories.AllEquations
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

inductive M :=
| M_val_8
| M_val_9
| M_val_3
| M_val_6
| M_val_7
| M_val_2
| M_val_5
| M_val_1
| M_val_4
| M_val_10
| M_val_11
| M_val_0
deriving DecidableEq, Fintype

def m (x y : M) : M :=
match x, y with
| M.M_val_8, M.M_val_8 => M.M_val_4
| M.M_val_8, M.M_val_9 => M.M_val_4
| M.M_val_8, M.M_val_3 => M.M_val_4
| M.M_val_8, M.M_val_6 => M.M_val_4
| M.M_val_8, M.M_val_7 => M.M_val_4
| M.M_val_8, M.M_val_2 => M.M_val_4
| M.M_val_8, M.M_val_5 => M.M_val_4
| M.M_val_8, M.M_val_1 => M.M_val_4
| M.M_val_8, M.M_val_4 => M.M_val_4
| M.M_val_8, M.M_val_10 => M.M_val_4
| M.M_val_8, M.M_val_11 => M.M_val_4
| M.M_val_8, M.M_val_0 => M.M_val_4
| M.M_val_9, M.M_val_8 => M.M_val_4
| M.M_val_9, M.M_val_9 => M.M_val_4
| M.M_val_9, M.M_val_3 => M.M_val_4
| M.M_val_9, M.M_val_6 => M.M_val_4
| M.M_val_9, M.M_val_7 => M.M_val_4
| M.M_val_9, M.M_val_2 => M.M_val_4
| M.M_val_9, M.M_val_5 => M.M_val_4
| M.M_val_9, M.M_val_1 => M.M_val_4
| M.M_val_9, M.M_val_4 => M.M_val_4
| M.M_val_9, M.M_val_10 => M.M_val_4
| M.M_val_9, M.M_val_11 => M.M_val_4
| M.M_val_9, M.M_val_0 => M.M_val_4
| M.M_val_3, M.M_val_8 => M.M_val_4
| M.M_val_3, M.M_val_9 => M.M_val_4
| M.M_val_3, M.M_val_3 => M.M_val_4
| M.M_val_3, M.M_val_6 => M.M_val_4
| M.M_val_3, M.M_val_7 => M.M_val_4
| M.M_val_3, M.M_val_2 => M.M_val_4
| M.M_val_3, M.M_val_5 => M.M_val_4
| M.M_val_3, M.M_val_1 => M.M_val_4
| M.M_val_3, M.M_val_4 => M.M_val_4
| M.M_val_3, M.M_val_10 => M.M_val_4
| M.M_val_3, M.M_val_11 => M.M_val_4
| M.M_val_3, M.M_val_0 => M.M_val_4
| M.M_val_6, M.M_val_8 => M.M_val_4
| M.M_val_6, M.M_val_9 => M.M_val_4
| M.M_val_6, M.M_val_3 => M.M_val_4
| M.M_val_6, M.M_val_6 => M.M_val_4
| M.M_val_6, M.M_val_7 => M.M_val_4
| M.M_val_6, M.M_val_2 => M.M_val_4
| M.M_val_6, M.M_val_5 => M.M_val_4
| M.M_val_6, M.M_val_1 => M.M_val_4
| M.M_val_6, M.M_val_4 => M.M_val_4
| M.M_val_6, M.M_val_10 => M.M_val_4
| M.M_val_6, M.M_val_11 => M.M_val_4
| M.M_val_6, M.M_val_0 => M.M_val_9
| M.M_val_7, M.M_val_8 => M.M_val_4
| M.M_val_7, M.M_val_9 => M.M_val_4
| M.M_val_7, M.M_val_3 => M.M_val_4
| M.M_val_7, M.M_val_6 => M.M_val_4
| M.M_val_7, M.M_val_7 => M.M_val_4
| M.M_val_7, M.M_val_2 => M.M_val_4
| M.M_val_7, M.M_val_5 => M.M_val_4
| M.M_val_7, M.M_val_1 => M.M_val_4
| M.M_val_7, M.M_val_4 => M.M_val_4
| M.M_val_7, M.M_val_10 => M.M_val_4
| M.M_val_7, M.M_val_11 => M.M_val_4
| M.M_val_7, M.M_val_0 => M.M_val_11
| M.M_val_2, M.M_val_8 => M.M_val_4
| M.M_val_2, M.M_val_9 => M.M_val_4
| M.M_val_2, M.M_val_3 => M.M_val_4
| M.M_val_2, M.M_val_6 => M.M_val_4
| M.M_val_2, M.M_val_7 => M.M_val_4
| M.M_val_2, M.M_val_2 => M.M_val_4
| M.M_val_2, M.M_val_5 => M.M_val_4
| M.M_val_2, M.M_val_1 => M.M_val_5
| M.M_val_2, M.M_val_4 => M.M_val_4
| M.M_val_2, M.M_val_10 => M.M_val_4
| M.M_val_2, M.M_val_11 => M.M_val_4
| M.M_val_2, M.M_val_0 => M.M_val_4
| M.M_val_5, M.M_val_8 => M.M_val_4
| M.M_val_5, M.M_val_9 => M.M_val_4
| M.M_val_5, M.M_val_3 => M.M_val_4
| M.M_val_5, M.M_val_6 => M.M_val_4
| M.M_val_5, M.M_val_7 => M.M_val_4
| M.M_val_5, M.M_val_2 => M.M_val_4
| M.M_val_5, M.M_val_5 => M.M_val_4
| M.M_val_5, M.M_val_1 => M.M_val_4
| M.M_val_5, M.M_val_4 => M.M_val_4
| M.M_val_5, M.M_val_10 => M.M_val_4
| M.M_val_5, M.M_val_11 => M.M_val_4
| M.M_val_5, M.M_val_0 => M.M_val_7
| M.M_val_1, M.M_val_8 => M.M_val_4
| M.M_val_1, M.M_val_9 => M.M_val_4
| M.M_val_1, M.M_val_3 => M.M_val_4
| M.M_val_1, M.M_val_6 => M.M_val_4
| M.M_val_1, M.M_val_7 => M.M_val_4
| M.M_val_1, M.M_val_2 => M.M_val_3
| M.M_val_1, M.M_val_5 => M.M_val_4
| M.M_val_1, M.M_val_1 => M.M_val_4
| M.M_val_1, M.M_val_4 => M.M_val_4
| M.M_val_1, M.M_val_10 => M.M_val_4
| M.M_val_1, M.M_val_11 => M.M_val_4
| M.M_val_1, M.M_val_0 => M.M_val_4
| M.M_val_4, M.M_val_8 => M.M_val_4
| M.M_val_4, M.M_val_9 => M.M_val_4
| M.M_val_4, M.M_val_3 => M.M_val_4
| M.M_val_4, M.M_val_6 => M.M_val_4
| M.M_val_4, M.M_val_7 => M.M_val_4
| M.M_val_4, M.M_val_2 => M.M_val_4
| M.M_val_4, M.M_val_5 => M.M_val_4
| M.M_val_4, M.M_val_1 => M.M_val_4
| M.M_val_4, M.M_val_4 => M.M_val_4
| M.M_val_4, M.M_val_10 => M.M_val_4
| M.M_val_4, M.M_val_11 => M.M_val_4
| M.M_val_4, M.M_val_0 => M.M_val_11
| M.M_val_10, M.M_val_8 => M.M_val_4
| M.M_val_10, M.M_val_9 => M.M_val_4
| M.M_val_10, M.M_val_3 => M.M_val_4
| M.M_val_10, M.M_val_6 => M.M_val_4
| M.M_val_10, M.M_val_7 => M.M_val_4
| M.M_val_10, M.M_val_2 => M.M_val_4
| M.M_val_10, M.M_val_5 => M.M_val_4
| M.M_val_10, M.M_val_1 => M.M_val_4
| M.M_val_10, M.M_val_4 => M.M_val_4
| M.M_val_10, M.M_val_10 => M.M_val_4
| M.M_val_10, M.M_val_11 => M.M_val_4
| M.M_val_10, M.M_val_0 => M.M_val_11
| M.M_val_11, M.M_val_8 => M.M_val_4
| M.M_val_11, M.M_val_9 => M.M_val_4
| M.M_val_11, M.M_val_3 => M.M_val_4
| M.M_val_11, M.M_val_6 => M.M_val_4
| M.M_val_11, M.M_val_7 => M.M_val_4
| M.M_val_11, M.M_val_2 => M.M_val_4
| M.M_val_11, M.M_val_5 => M.M_val_4
| M.M_val_11, M.M_val_1 => M.M_val_4
| M.M_val_11, M.M_val_4 => M.M_val_4
| M.M_val_11, M.M_val_10 => M.M_val_4
| M.M_val_11, M.M_val_11 => M.M_val_4
| M.M_val_11, M.M_val_0 => M.M_val_4
| M.M_val_0, M.M_val_8 => M.M_val_10
| M.M_val_0, M.M_val_9 => M.M_val_10
| M.M_val_0, M.M_val_3 => M.M_val_4
| M.M_val_0, M.M_val_6 => M.M_val_8
| M.M_val_0, M.M_val_7 => M.M_val_8
| M.M_val_0, M.M_val_2 => M.M_val_4
| M.M_val_0, M.M_val_5 => M.M_val_6
| M.M_val_0, M.M_val_1 => M.M_val_4
| M.M_val_0, M.M_val_4 => M.M_val_8
| M.M_val_0, M.M_val_10 => M.M_val_8
| M.M_val_0, M.M_val_11 => M.M_val_10
| M.M_val_0, M.M_val_0 => M.M_val_4

instance M.Magma : Magma M := ⟨ m ⟩

theorem Equation4283_not_implies_Equation4358 :  ∃ (G: Type) (_: Magma G), Equation4283 G ∧ ¬ Equation4358 G :=
by exists M, M.Magma
