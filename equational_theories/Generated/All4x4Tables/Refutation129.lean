import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,0,0,3],[1,1,1,1],[1,2,2,2],[3,3,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,0,0,3],[1,1,1,1],[1,2,2,2],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,0,0,3],[1,1,1,1],[1,2,2,2],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,0,0,3],[1,1,1,1],[1,2,2,2],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [325,3315,3317] [326,327,3318,3319,3320,3321,3322,3324,3519,3521,3522,3526,4314] :=
    ⟨Fin 4, «FinitePoly [[3,0,0,3],[1,1,1,1],[1,2,2,2],[3,3,3,3]]», by decideFin!⟩
