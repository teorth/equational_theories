
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,2,3],[3,3,3,3],[0,0,0,3],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,2,3],[3,3,3,3],[0,0,0,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,2,3],[3,3,3,3],[0,0,0,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,2,3],[3,3,3,3],[0,0,0,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [224] [231, 1637, 1657, 1721, 1731, 2340, 2496, 2506, 2533, 2543, 2652, 2672, 2706, 2709, 2746, 3058, 3078, 3105, 3115, 3139, 3142, 3152, 3255, 3256, 3258, 3259, 3261, 3262, 3268, 3271, 3278, 3459, 3467, 3481, 3509, 3677, 3694, 3820, 4090, 4131, 4155, 4165, 4269, 4270, 4272, 4314, 4362, 4606, 4622] :=
    ⟨Fin 4, «FinitePoly [[0,3,2,3],[3,3,3,3],[0,0,0,3],[0,1,2,3]]», by decideFin!⟩
