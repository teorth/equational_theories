
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,0,3],[2,1,1,2],[2,2,2,2],[2,0,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,1,0,3],[2,1,1,2],[2,2,2,2],[2,0,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,1,0,3],[2,1,1,2],[2,2,2,2],[2,0,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,1,0,3],[2,1,1,2],[2,2,2,2],[2,0,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1240, 1250, 1254] [105, 108, 413, 426, 427, 429, 430, 437, 439, 817, 1035, 1038, 1046, 1048, 1049, 1226, 1234, 1241, 1245, 1252, 1259, 1260, 1266, 1834, 1847, 1850, 1851, 1860, 3255, 3316, 3318, 3726, 3727, 3865, 3925, 4076, 4131, 4269, 4314, 4598] :=
    ⟨Fin 4, «FinitePoly [[1,1,0,3],[2,1,1,2],[2,2,2,2],[2,0,3,2]]», by decideFin!⟩
