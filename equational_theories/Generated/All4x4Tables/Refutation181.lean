
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,1,3],[3,2,2,1],[1,1,2,3],[0,1,0,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,1,3],[3,2,2,1],[1,1,2,3],[0,1,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,1,3],[3,2,2,1],[1,1,2,3],[0,1,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,1,3],[3,2,2,1],[1,1,2,3],[0,1,0,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3105] [2530, 2533, 2588, 2646, 2659, 2672, 2696, 2709, 2736, 3052, 3065, 3078, 3115, 3142, 3264, 3519, 3749, 4128, 4155, 4606] :=
    ⟨Fin 4, «FinitePoly [[0,3,1,3],[3,2,2,1],[1,1,2,3],[0,1,0,3]]», by decideFin!⟩
