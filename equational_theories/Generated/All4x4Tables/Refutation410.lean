
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,3,1],[3,3,1,3],[0,0,3,0],[3,3,1,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,3,1],[3,3,1,3],[0,0,3,0],[3,3,1,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,3,1],[3,3,1,3],[0,0,3,0],[3,3,1,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,3,1],[3,3,1,3],[0,0,3,0],[3,3,1,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3910] [3253, 3721, 3724, 3725, 3865, 3887, 3915, 3925, 3928, 4065, 4269, 4293, 4314, 4583, 4588, 4591, 4598, 4606, 4608, 4631] :=
    ⟨Fin 4, «FinitePoly [[3,1,3,1],[3,3,1,3],[0,0,3,0],[3,3,1,3]]», by decideFin!⟩
