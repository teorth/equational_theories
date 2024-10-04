
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,1,1],[3,3,0,0],[2,2,2,0],[2,1,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,1,1],[3,3,0,0],[2,2,2,0],[2,1,1,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,1,1],[3,3,0,0],[2,2,2,0],[2,1,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,1,1],[3,3,0,0],[2,2,2,0],[2,1,1,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1843] [151, 1629, 1664, 1668, 1672, 1847, 1850, 1857, 1860, 3253, 3330, 3334, 4065, 4118, 4121, 4128, 4131, 4269, 4284, 4360, 4599, 4631] :=
    ⟨Fin 4, «FinitePoly [[3,1,1,1],[3,3,0,0],[2,2,2,0],[2,1,1,1]]», by decideFin!⟩
