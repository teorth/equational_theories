
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,0,3],[1,1,1,1],[2,2,1,1],[2,3,0,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,0,3],[1,1,1,1],[2,2,1,1],[2,3,0,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,0,0,3],[1,1,1,1],[2,2,1,1],[2,3,0,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,0,3],[1,1,1,1],[2,2,1,1],[2,3,0,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [427, 1060] [105, 429, 430, 437, 439, 832, 833, 836, 1022, 1035, 1038, 1046, 1048, 1229, 1231, 1242, 1244, 1834, 1847, 3255, 3316, 3724, 3864, 3925, 4131, 4269] :=
    ⟨Fin 4, «FinitePoly [[1,0,0,3],[1,1,1,1],[2,2,1,1],[2,3,0,1]]», Finite.of_fintype _, by decideFin!⟩
