
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,0,1],[2,3,1,0],[2,3,1,0],[3,2,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,0,1],[2,3,1,0],[2,3,1,0],[3,2,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,0,1],[2,3,1,0],[2,3,1,0],[3,2,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,0,1],[2,3,1,0],[2,3,1,0],[3,2,0,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [528, 1171, 1949, 1996] [614, 817, 1223, 1426, 1629, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3659, 3862, 4622] :=
    ⟨Fin 4, «FinitePoly [[3,2,0,1],[2,3,1,0],[2,3,1,0],[3,2,0,1]]», by decideFin!⟩
