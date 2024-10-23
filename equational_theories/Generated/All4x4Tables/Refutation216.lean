
import Mathlib.Data.Finite.Basic
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,1],[2,1,2],[0,2,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,0,1],[2,1,2],[0,2,1]]» : Magma (Fin 3) where
  op := memoFinOp fun x y => [[0,0,1],[2,1,2],[0,2,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,0,1],[2,1,2],[0,2,1]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1682] [414, 427, 473, 477, 511, 513, 622, 632, 639, 667, 680, 707, 1023, 1109, 1122, 1239, 1278, 1289, 1429, 1451, 1488, 1515, 1519, 1637, 1645, 1658, 1731, 1857, 1861, 1885, 1887, 2038, 2041, 2043, 2124, 2128, 2137, 2254, 2267, 2293, 2338, 2444, 2530, 2855, 2872, 2900, 2947, 3056, 3079, 3105, 3116, 3139, 3150, 3662, 3665, 3667, 3675, 3677, 3684, 4270, 4283, 4398, 4405, 4442, 4482, 4622, 4635] :=
    ⟨Fin 3, «FinitePoly [[0,0,1],[2,1,2],[0,2,1]]», Finite.of_fintype _, by decideFin!⟩
