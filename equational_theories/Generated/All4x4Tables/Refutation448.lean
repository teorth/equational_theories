
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,1,3],[1,2,2,0],[0,3,0,2],[2,1,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,1,3],[1,2,2,0],[0,3,0,2],[2,1,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,1,3],[1,2,2,0],[0,3,0,2],[2,1,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,1,3],[1,2,2,0],[0,3,0,2],[2,1,3,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [826] [8, 38, 47, 99, 151, 203, 620, 633, 833, 1426, 3050, 4130, 4399] :=
    ⟨Fin 4, «FinitePoly [[3,0,1,3],[1,2,2,0],[0,3,0,2],[2,1,3,1]]», by decideFin!⟩
