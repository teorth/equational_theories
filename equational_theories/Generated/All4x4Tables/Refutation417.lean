
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,1,3],[3,0,1,0],[3,3,0,1],[1,0,3,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,1,3],[3,0,1,0],[3,3,0,1],[1,0,3,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,1,3],[3,0,1,0],[3,3,0,1],[1,0,3,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,1,3],[3,0,1,0],[3,3,0,1],[1,0,3,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3756] [43, 3253, 3456, 3588, 3591, 3601, 3607, 3761, 3794, 4065, 4098, 4118, 4127, 4131, 4165, 4273, 4320, 4380, 4605, 4612, 4656, 4684] :=
    ⟨Fin 4, «FinitePoly [[0,1,1,3],[3,0,1,0],[3,3,0,1],[1,0,3,0]]», by decideFin!⟩
