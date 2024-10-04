
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,2,3,4],[2,3,0,4,1],[1,0,4,2,3],[4,2,3,1,0],[3,4,1,0,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,2,3,4],[2,3,0,4,1],[1,0,4,2,3],[4,2,3,1,0],[3,4,1,0,2]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[0,1,2,3,4],[2,3,0,4,1],[1,0,4,2,3],[4,2,3,1,0],[3,4,1,0,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,2,3,4],[2,3,0,4,1],[1,0,4,2,3],[4,2,3,1,0],[3,4,1,0,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2592, 3201] [1629, 1718, 1731, 2238, 2327, 2340, 2449, 2466, 2496, 2530, 2644, 2699, 2706, 2733, 2746, 2847, 2949, 3058, 3075, 3105, 3139, 3456, 3659, 3712, 3759, 4065, 4118, 4165, 4226, 4320, 4622] :=
    ⟨Fin 5, «FinitePoly [[0,1,2,3,4],[2,3,0,4,1],[1,0,4,2,3],[4,2,3,1,0],[3,4,1,0,2]]», by decideFin!⟩
