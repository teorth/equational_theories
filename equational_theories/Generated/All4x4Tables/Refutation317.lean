
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,0,2],[3,1,1,1],[1,2,2,2],[3,3,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,0,2],[3,1,1,1],[1,2,2,2],[3,3,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,0,0,2],[3,1,1,1],[1,2,2,2],[3,3,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,0,2],[3,1,1,1],[1,2,2,2],[3,3,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1056] [99, 359, 818, 843, 1022, 1031, 1039, 1052, 1223, 1252, 1254, 3660, 3661, 3665, 3864, 3867, 4065, 4066, 4067, 4068, 4070, 4071, 4583, 4598, 4631] :=
    ⟨Fin 4, «FinitePoly [[1,0,0,2],[3,1,1,1],[1,2,2,2],[3,3,3,2]]», by decideFin!⟩
