
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 1, 3, 3], [3, 3, 0, 3], [0, 3, 1, 3], [0, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 1, 3, 3], [3, 3, 0, 3], [0, 3, 1, 3], [0, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 1, 3, 3], [3, 3, 0, 3], [0, 3, 1, 3], [0, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 1, 3, 3], [3, 3, 0, 3], [0, 3, 1, 3], [0, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2368, 2372, 2385, 2406, 2662, 4276] [2243, 2246, 2672, 2696, 3051, 3052, 3053, 3055, 3056, 3058, 3059, 3065, 3066, 3068, 3069, 3075, 3076, 3078, 3079, 3102, 3103, 3105, 3106, 3112, 3113, 3115, 3116, 3139, 3140, 3142, 3143, 3149, 3150] :=
    ⟨Fin 4, «FinitePoly [[3, 1, 3, 3], [3, 3, 0, 3], [0, 3, 1, 3], [0, 1, 2, 3]]», by decideFin!⟩
