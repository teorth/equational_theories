
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,2,1,3],[2,0,3,1],[3,1,2,0],[1,3,0,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,2,1,3],[2,0,3,1],[3,1,2,0],[1,3,0,2]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,2,1,3],[2,0,3,1],[3,1,2,0],[1,3,0,2]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,2,1,3],[2,0,3,1],[3,1,2,0],[1,3,0,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [429, 633, 1452, 1793] [47, 99, 151, 211, 261, 413, 414, 416, 417, 419, 420, 426, 436, 437, 440, 619, 620, 622, 623, 629, 630, 632, 639, 640, 642, 643, 817, 1020, 1223, 1427, 1428, 1429, 1431, 1434, 1435, 1441, 1445, 1451, 1454, 1631, 1632, 1634, 1635, 1637, 1638, 1644, 1648, 1655, 1657, 1832, 2035, 2238, 2441, 2644, 2847, 3050, 3253, 3456, 3660, 3661, 3662, 3664, 3665, 3667, 3668, 3712, 3714, 3721, 3722, 3862, 4065, 4320, 4399, 4435, 4470, 4590] :=
    ⟨Fin 4, «FinitePoly [[0,2,1,3],[2,0,3,1],[3,1,2,0],[1,3,0,2]]», Finite.of_fintype _, by decideFin!⟩
