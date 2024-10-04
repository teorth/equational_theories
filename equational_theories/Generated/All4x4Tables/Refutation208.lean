
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,0,1],[2,1,1,2],[1,2,2,2],[1,3,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,0,1],[2,1,1,2],[1,2,2,2],[1,3,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,0,0,1],[2,1,1,2],[1,2,2,2],[1,3,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,0,1],[2,1,1,2],[1,2,2,2],[1,3,3,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [109, 111, 1257, 1265, 1271, 3322] [426, 427, 429, 430, 439, 832, 833, 836, 1035, 1038, 1048, 1238, 1834, 1847, 1850, 1851, 1860, 3306, 3318, 3660, 3661, 3665, 3724, 3864, 3865, 3867, 3925, 4065, 4269, 4314, 4583, 4631] :=
    ⟨Fin 4, «FinitePoly [[1,0,0,1],[2,1,1,2],[1,2,2,2],[1,3,3,1]]», by decideFin!⟩
