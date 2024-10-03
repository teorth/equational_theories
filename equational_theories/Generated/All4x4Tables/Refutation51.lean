import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,0,3],[1,3,1,0],[2,0,1,0],[1,0,0,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,0,3],[1,3,1,0],[2,0,1,0],[1,0,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,0,0,3],[1,3,1,0],[2,0,1,0],[1,0,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,0,3],[1,3,1,0],[2,0,1,0],[1,0,0,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1063] [99,104,107,1022,1038,1041,1223,1228,1238,1241,1248,1258,3253,3255,3316,3659] :=
    ⟨Fin 4, «FinitePoly [[1,0,0,3],[1,3,1,0],[2,0,1,0],[1,0,0,3]]», by decideFin!⟩
