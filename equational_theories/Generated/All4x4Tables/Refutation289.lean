
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[0,0,1],[0,2,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0,0],[0,0,1],[0,2,0]]» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[0,0,1],[0,2,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0,0],[0,0,1],[0,2,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [325, 3483, 3493, 3885, 3889, 4410, 4417, 4495, 4616] [3259, 3271, 3318, 3461, 3475, 3519, 3667, 3675, 3868, 3880, 4269, 4273, 4283, 4291, 4314, 4320, 4321, 4433, 4435, 4443, 4445, 4629] :=
    ⟨Fin 3, «All4x4Tables [[0,0,0],[0,0,1],[0,2,0]]», Finite.of_fintype _, by decideFin!⟩
