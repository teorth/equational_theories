
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,1,3,4,5],[5,1,2,4,5,5],[3,1,2,5,5,0],[0,1,1,3,4,5],[5,2,1,3,4,5],[0,2,1,3,4,5]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,1,3,4,5],[5,1,2,4,5,5],[3,1,2,5,5,0],[0,1,1,3,4,5],[5,2,1,3,4,5],[0,2,1,3,4,5]]» : Magma (Fin 6) where
  op := memoFinOp fun x y => [[0,1,1,3,4,5],[5,1,2,4,5,5],[3,1,2,5,5,0],[0,1,1,3,4,5],[5,2,1,3,4,5],[0,2,1,3,4,5]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,1,3,4,5],[5,1,2,4,5,5],[3,1,2,5,5,0],[0,1,1,3,4,5],[5,2,1,3,4,5],[0,2,1,3,4,5]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2381] [1055, 1958, 2364, 2584, 2669, 3897] :=
    ⟨Fin 6, «FinitePoly [[0,1,1,3,4,5],[5,1,2,4,5,5],[3,1,2,5,5,0],[0,1,1,3,4,5],[5,2,1,3,4,5],[0,2,1,3,4,5]]», by decideFin!⟩
