
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,3,1,1],[3,2,0,0],[1,1,1,1],[1,0,1,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,3,1,1],[3,2,0,0],[1,1,1,1],[1,0,1,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,3,1,1],[3,2,0,0],[1,1,1,1],[1,0,1,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,3,1,1],[3,2,0,0],[1,1,1,1],[1,0,1,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1446, 1867] [1435, 1629, 1840, 1850, 1860, 2035, 3253, 3459, 3462, 3465, 3862, 4073, 4121, 4284] :=
    ⟨Fin 4, «FinitePoly [[3,3,1,1],[3,2,0,0],[1,1,1,1],[1,0,1,0]]», by decideFin!⟩
