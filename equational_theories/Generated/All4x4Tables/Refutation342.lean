
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,0,1],[2,2,1,2],[2,2,2,2],[2,1,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,0,1],[2,2,1,2],[2,2,2,2],[2,1,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,0,1],[2,2,1,2],[2,2,2,2],[2,1,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,0,1],[2,2,1,2],[2,2,2,2],[2,1,3,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [105, 1240, 1243, 1244, 1245, 1253, 1255, 1259, 1263] [107, 817, 1022, 1250, 1254, 1262, 3253, 3862] :=
    ⟨Fin 4, «FinitePoly [[3,1,0,1],[2,2,1,2],[2,2,2,2],[2,1,3,1]]», by decideFin!⟩
