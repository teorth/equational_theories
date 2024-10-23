
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,1,1],[0,1,3,2],[0,1,2,3],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,1,1],[0,1,3,2],[0,1,2,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,1,1],[0,1,3,2],[0,1,2,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,1,1],[0,1,3,2],[0,1,2,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [2584, 2804, 2973, 4192, 4209] [208, 280, 323, 333, 619, 832, 1035, 1228, 1248, 1478, 1634, 1681, 1884, 2050, 2124, 2290, 2337, 2493, 2530, 2659, 2706, 2733, 2852, 2872, 2909, 2946, 3055, 3075, 3112, 3149, 3309, 3461, 3509, 3674, 3712, 3867, 3877, 4070, 4090, 4269, 4284, 4396, 4666] :=
    ⟨Fin 4, «FinitePoly [[0,3,1,1],[0,1,3,2],[0,1,2,3],[0,1,2,3]]», Finite.of_fintype _, by decideFin!⟩
