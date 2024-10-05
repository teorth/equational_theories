
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,1,3,3],[2,3,2,3],[0,2,1,3],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,1,3,3],[2,3,2,3],[0,2,1,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,1,3,3],[2,3,2,3],[0,2,1,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,1,3,3],[2,3,2,3],[0,2,1,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2303] [203, 323, 1631, 1637, 1644, 1647, 1657, 1721, 1731, 2240, 2246, 2266, 2340, 2446, 2466, 2496, 2506, 2533, 2543, 2652, 2672, 2709, 2746, 3058, 3152, 3258, 3268, 3278, 3458, 3464, 3509, 3659, 4090, 4165, 4272, 4622] :=
    ⟨Fin 4, «FinitePoly [[2,1,3,3],[2,3,2,3],[0,2,1,3],[0,1,2,3]]», by decideFin!⟩
