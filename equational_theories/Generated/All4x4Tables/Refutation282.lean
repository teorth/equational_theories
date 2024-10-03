import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,2,3],[1,0,2,3],[0,3,2,1],[1,0,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,2,3],[1,0,2,3],[0,3,2,1],[1,0,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,0,2,3],[1,0,2,3],[0,3,2,1],[1,0,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,2,3],[1,0,2,3],[0,3,2,1],[1,0,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [138,194,1096,1133,1150,1167,1202,1299,1336,1405,1742,1763,1797,1816,1912,1979,2000,2024,2182,2227] [429,473,562,3271,3346,3388,4320,4362] :=
    ⟨Fin 4, «FinitePoly [[1,0,2,3],[1,0,2,3],[0,3,2,1],[1,0,2,3]]», by decideFin!⟩
