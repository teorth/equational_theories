import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,0,3],[2,2,0,0],[0,2,0,3],[0,2,2,0]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,0,3],[2,2,0,0],[0,2,0,3],[0,2,2,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,0,3],[2,2,0,0],[0,2,0,3],[0,2,2,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,0,3],[2,2,0,0],[0,2,0,3],[0,2,2,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3265] [307,309,310,323,3256,3258,3261,3264,3266,3306,3456,3458,3459,3461,3464,3467,3509,3519,3522,3525,3529,3537,3659,3662,3664,3665,3668,3672,3712,4270,4341] :=
    ⟨Fin 4, «FinitePoly [[0,3,0,3],[2,2,0,0],[0,2,0,3],[0,2,2,0]]», by decideFin!⟩
