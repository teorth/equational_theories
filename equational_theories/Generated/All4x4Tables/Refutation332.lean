import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,1,1],[2,3,0,0],[2,2,3,2],[3,3,3,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,1,1],[2,3,0,0],[2,2,3,2],[3,3,3,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,1,1],[2,3,0,0],[2,2,3,2],[3,3,3,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,1,1],[2,3,0,0],[2,2,3,2],[3,3,3,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1853,1855] [3253,3255,3256,3306,3315,3316,3318,3319,3321,3322,3323,4070,4071,4072,4073,4076,4584,4598,4601,4631,4673] :=
    ⟨Fin 4, «FinitePoly [[3,3,1,1],[2,3,0,0],[2,2,3,2],[3,3,3,3]]», by decideFin!⟩
