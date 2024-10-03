import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,2,3],[3,3,2,3],[0,1,0,0],[0,1,1,0]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,2,3],[3,3,2,3],[0,1,0,0],[0,1,1,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,2,3],[3,3,2,3],[0,1,0,0],[0,1,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,2,3],[3,3,2,3],[0,1,0,0],[0,1,1,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3061,3081,3089,3093,3097] [326,3309,3319,3509,3664,3712,4284] :=
    ⟨Fin 4, «FinitePoly [[3,2,2,3],[3,3,2,3],[0,1,0,0],[0,1,1,0]]», by decideFin!⟩
