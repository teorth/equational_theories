
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3,1,0,1],[2,1,0,3],[2,0,1,1],[2,1,0,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3,1,0,1],[2,1,0,3],[2,0,1,1],[2,1,0,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3,1,0,1],[2,1,0,3],[2,0,1,1],[2,1,0,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3,1,0,1],[2,1,0,3],[2,0,1,1],[2,1,0,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1028, 1738] [1832, 3253, 3862, 4080, 4090, 4093, 4155, 4165, 4272, 4275, 4291, 4320, 4606, 4635] :=
    ⟨Fin 4, «FinitePoly [[3,1,0,1],[2,1,0,3],[2,0,1,1],[2,1,0,3]]», by decideFin!⟩
