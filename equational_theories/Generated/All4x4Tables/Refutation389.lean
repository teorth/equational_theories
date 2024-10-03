import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,2,2,1],[3,1,1,0],[0,1,1,3],[1,2,2,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,2,2,1],[3,1,1,0],[0,1,1,3],[1,2,2,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,2,2,1],[3,1,1,0],[0,1,1,3],[1,2,2,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,2,2,1],[3,1,1,0],[0,1,1,3],[1,2,2,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3488] [3664,3668,3672,3674,3678,3682,3694,3699,3704,3709] :=
    ⟨Fin 4, «FinitePoly [[1,2,2,1],[3,1,1,0],[0,1,1,3],[1,2,2,1]]», by decideFin!⟩
