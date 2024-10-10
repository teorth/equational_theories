
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,2,0,1],[3,3,0,1],[3,2,1,1],[3,3,1,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,2,0,1],[3,3,0,1],[3,2,1,1],[3,3,1,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,2,0,1],[3,3,0,1],[3,2,1,1],[3,3,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,2,0,1],[3,3,0,1],[3,2,1,1],[3,3,1,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [422] [99, 151, 426, 429, 436, 1020, 1223, 1629, 1832, 2035, 3253, 3864, 3867, 3870, 3915, 3918, 3925, 3928, 4065, 4269, 4284, 4599, 4631] :=
    ⟨Fin 4, «FinitePoly [[3,2,0,1],[3,3,0,1],[3,2,1,1],[3,3,1,1]]», by decideFin!⟩
