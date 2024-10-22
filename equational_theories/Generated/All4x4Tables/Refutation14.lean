
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,1,0,1],[2,0,1,3],[2,2,2,0],[2,2,3,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,1,0,1],[2,0,1,3],[2,2,2,0],[2,2,3,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,1,0,1],[2,0,1,3],[2,2,2,0],[2,2,3,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,1,0,1],[2,0,1,3],[2,2,2,0],[2,2,3,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1046] [99, 413, 426, 427, 429, 430, 437, 439, 817, 1023, 1025, 1035, 1038, 1039, 1045, 1048, 1049, 1223, 1834, 1847, 1851, 1860, 3255, 3316, 3318, 3724, 3864, 3865, 3867, 3925, 4072, 4076, 4131, 4269, 4314, 4598, 4631] :=
    ⟨Fin 4, «FinitePoly [[0,1,0,1],[2,0,1,3],[2,2,2,0],[2,2,3,2]]», Finite.of_fintype _, by decideFin!⟩
