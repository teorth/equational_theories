import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1,4,3],[3,4,2,0,1],[4,1,3,2,0],[2,3,0,1,4],[1,0,4,3,2]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,1,4,3],[3,4,2,0,1],[4,1,3,2,0],[2,3,0,1,4],[1,0,4,3,2]]» : Magma (Fin 5) where
  op := memoFinOp fun x y => [[0,2,1,4,3],[3,4,2,0,1],[4,1,3,2,0],[2,3,0,1,4],[1,0,4,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,1,4,3],[3,4,2,0,1],[4,1,3,2,0],[2,3,0,1,4],[1,0,4,3,2]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [430,1110] [255,429,473,562,1029,1038,1223,1241,1249,3271,3871,3954,4065,4636] :=
    ⟨Fin 5, «FinitePoly [[0,2,1,4,3],[3,4,2,0,1],[4,1,3,2,0],[2,3,0,1,4],[1,0,4,3,2]]», by decideFin!⟩
