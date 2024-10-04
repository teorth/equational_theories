
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,2,3],[3,3,2,3],[0,1,0,3],[0,1,2,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,2,3],[3,3,2,3],[0,1,0,3],[0,1,2,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,2,3],[3,3,2,3],[0,1,0,3],[0,1,2,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,2,3],[3,3,2,3],[0,1,0,3],[0,1,2,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2300, 2712, 2774, 3180] [221, 231, 1637, 1657, 1718, 1721, 1731, 2293, 2318, 2330, 2340, 2364, 2496, 2506, 2533, 2543, 2652, 2662, 2672, 2739, 2746, 3058, 3115, 3139, 3152, 3258, 3268, 3278, 3509, 3659, 4090, 4155, 4272, 4320, 4606, 4622] :=
    ⟨Fin 4, «FinitePoly [[3,3,2,3],[3,3,2,3],[0,1,0,3],[0,1,2,2]]», by decideFin!⟩
