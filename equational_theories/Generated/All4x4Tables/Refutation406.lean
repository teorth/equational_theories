
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0, 0, 3, 3], [3, 2, 2, 3], [1, 1, 2, 3], [0, 1, 2, 3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0, 0, 3, 3], [3, 2, 2, 3], [1, 1, 2, 3], [0, 1, 2, 3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0, 0, 3, 3], [3, 2, 2, 3], [1, 1, 2, 3], [0, 1, 2, 3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0, 0, 3, 3], [3, 2, 2, 3], [1, 1, 2, 3], [0, 1, 2, 3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2665, 2702, 3664] [29, 255, 326, 2649, 2652, 2672, 2736, 2847, 3055, 3058, 3075, 3078, 3309, 3319, 3509, 3512, 3674, 3684, 3715, 3722, 3725, 3759, 4067, 4073, 4121, 4131] :=
    ⟨Fin 4, «FinitePoly [[0, 0, 3, 3], [3, 2, 2, 3], [1, 1, 2, 3], [0, 1, 2, 3]]», by decideFin!⟩
