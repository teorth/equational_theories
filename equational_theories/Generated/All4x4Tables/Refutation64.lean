
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,2],[2,2,2],[0,1,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0,2],[2,2,2],[0,1,2]]» : Magma (Fin 3) where
  op := finOpTable "[[0,0,2],[2,2,2],[0,1,2]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0,2],[2,2,2],[0,1,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2322] [231, 1637, 1657, 1721, 1731, 2340, 2496, 2506, 2530, 2533, 2543, 2652, 2672, 2706, 2709, 2746, 3058, 3078, 3105, 3115, 3139, 3142, 3152, 3255, 3256, 3258, 3259, 3261, 3262, 3268, 3269, 3271, 3278, 3459, 3467, 3472, 3481, 3537, 3662, 3665, 3668, 3677, 3694, 3820, 4068, 4090, 4131, 4155, 4165, 4269, 4270, 4272, 4273, 4314, 4606, 4622] :=
    ⟨Fin 3, «All4x4Tables [[0,0,2],[2,2,2],[0,1,2]]», Finite.of_fintype _, by decideFin!⟩
