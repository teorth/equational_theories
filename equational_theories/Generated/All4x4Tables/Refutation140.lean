
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,0,1],[2,2,1,3],[2,2,2,2],[3,2,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,0,1],[2,2,1,3],[2,2,2,2],[3,2,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,0,1],[2,2,1,3],[2,2,2,2],[3,2,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,0,1],[2,2,1,3],[2,2,2,2],[3,2,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [371, 1068] [413, 426, 427, 429, 430, 437, 439, 832, 833, 836, 1035, 1038, 1045, 1048, 1231, 1238, 1239, 1834, 1847, 1851, 1860, 3255, 3306, 3316, 3318, 3724, 3865, 3887, 3925, 4073, 4081, 4131, 4269, 4314, 4673] :=
    ⟨Fin 4, «FinitePoly [[2,0,0,1],[2,2,1,3],[2,2,2,2],[3,2,3,2]]», by decideFin!⟩
