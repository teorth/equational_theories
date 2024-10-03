import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,1,2,1],[3,3,2,3],[3,0,2,1],[0,0,2,0]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,1,2,1],[3,3,2,3],[3,0,2,1],[0,0,2,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,1,2,1],[3,3,2,3],[3,0,2,1],[0,0,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,1,2,1],[3,3,2,3],[3,0,2,1],[0,0,2,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2037,2056,3309] [2043,2046,3306,3308,3312,3316,3319,3322,3326,3330,3334,3338,3862,4065,4121,4131,4284,4287,4340,4360,4599] :=
    ⟨Fin 4, «FinitePoly [[1,1,2,1],[3,3,2,3],[3,0,2,1],[0,0,2,0]]», by decideFin!⟩
