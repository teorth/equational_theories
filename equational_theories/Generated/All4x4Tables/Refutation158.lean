
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,0,1],[3,2,0,1],[2,3,1,0],[2,3,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,0,1],[3,2,0,1],[2,3,1,0],[2,3,1,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,0,1],[3,2,0,1],[2,3,1,0],[2,3,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,0,1],[3,2,0,1],[2,3,1,0],[2,3,1,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [528, 562, 2182] [107, 413, 416, 426, 476, 503, 614, 817, 1020, 1225, 1241, 1251, 1285, 1322, 1426, 1629, 1832, 2037, 2040, 2060, 2127, 2134, 3253, 3456, 3659, 3864, 3870, 3880, 3890, 3918, 3928, 3955, 4065, 4269, 4272, 4284, 4291, 4380, 4584, 4590, 4598, 4599, 4635] :=
    ⟨Fin 4, «FinitePoly [[3,2,0,1],[3,2,0,1],[2,3,1,0],[2,3,1,0]]», by decideFin!⟩
