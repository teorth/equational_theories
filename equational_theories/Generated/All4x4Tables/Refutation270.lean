
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,2,3],[3,3,3,3],[1,1,0,0],[0,0,0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,2,3],[3,3,3,3],[1,1,0,0],[0,0,0,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,2,3],[3,3,3,3],[1,1,0,0],[0,0,0,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,2,3],[3,3,3,3],[1,1,0,0],[0,0,0,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3085] [2644, 3052, 3058, 3068, 3253, 3458, 3459, 3461, 3464, 3509, 3512, 3519, 3522, 3659, 4269, 4270, 4284, 4314, 4599, 4631] :=
    ⟨Fin 4, «FinitePoly [[3,2,2,3],[3,3,3,3],[1,1,0,0],[0,0,0,0]]», by decideFin!⟩
