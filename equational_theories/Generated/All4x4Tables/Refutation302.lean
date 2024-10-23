
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,1,3],[3,1,2,3],[0,1,2,0],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,1,3],[3,1,2,3],[0,1,2,0],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,1,3],[3,1,2,3],[0,1,2,0],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,1,3],[3,1,2,3],[0,1,2,0],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2513, 2716] [2263, 2310, 2347, 2364, 2381, 2550, 2679, 3309, 3316, 3343, 3509, 3519, 3556, 3712, 3749, 3752, 3897, 3925, 3952, 3962, 4128, 4165, 4284, 4291, 4362, 4396, 4406, 4435, 4480, 4606] :=
    ⟨Fin 4, «FinitePoly [[0,3,1,3],[3,1,2,3],[0,1,2,0],[0,1,2,3]]», Finite.of_fintype _, by decideFin!⟩
