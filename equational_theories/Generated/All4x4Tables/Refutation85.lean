
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2],[0,0,1],[0,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,1,2],[0,0,1],[0,1,0]]» : Magma (Fin 3) where
  op := finOpTable "[[0,1,2],[0,0,1],[0,1,0]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,1,2],[0,0,1],[0,1,0]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [316, 2389, 2558, 2836] [221, 2243, 2330, 2446, 2456, 2506, 2533, 3065, 3115, 3255, 3279, 3306, 3458, 3461, 3475, 3482, 3519, 3749, 4070, 4084, 4128, 4155, 4269, 4273, 4314, 4320, 4321, 4606, 4631, 4658] :=
    ⟨Fin 3, «All4x4Tables [[0,1,2],[0,0,1],[0,1,0]]», Finite.of_fintype _, by decideFin!⟩
