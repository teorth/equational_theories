
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 1, 1, 1], [2, 3, 3, 3], [3, 0, 0, 0], [1, 2, 2, 2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 1, 1, 1], [2, 3, 3, 3], [3, 0, 0, 0], [1, 2, 2, 2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 1, 1, 1], [2, 3, 3, 3], [3, 0, 0, 0], [1, 2, 2, 2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 1, 1, 1], [2, 3, 3, 3], [3, 0, 0, 0], [1, 2, 2, 2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3056, 3068, 3319] [8, 151, 411, 1020, 1223, 1426, 1629, 1832, 2441, 2644, 3051, 3052, 3053, 3055, 3058, 3059, 3065, 3066, 3069, 3075, 3076, 3078, 3079, 3102, 3103, 3105, 3106, 3112, 3113, 3115, 3116, 3139, 3140, 3142, 3143, 3149, 3150, 3152, 3261, 3262, 3306, 3318, 3456, 3862, 4314] :=
    ⟨Fin 4, «FinitePoly [[0, 1, 1, 1], [2, 3, 3, 3], [3, 0, 0, 0], [1, 2, 2, 2]]», by decideFin!⟩
