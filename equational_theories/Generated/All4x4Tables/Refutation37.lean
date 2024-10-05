
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,0,3,1],[3,1,1,3],[3,2,2,3],[1,3,3,1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,0,3,1],[3,1,1,3],[3,2,2,3],[1,3,3,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,0,3,1],[3,1,1,3],[3,2,2,3],[1,3,3,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,0,3,1],[3,1,1,3],[3,2,2,3],[1,3,3,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [417, 419, 620, 622, 1026, 1038, 1045, 1239, 1241, 1248, 3662, 3725] [99, 413, 414, 426, 427, 429, 436, 437, 440, 632, 639, 643, 817, 1023, 1039, 1046, 1048, 1049, 1229, 1238, 1242, 1251, 1252, 1442, 1451, 1629, 1832, 2035, 2244, 2256, 2444, 2449, 2459, 2466, 2644, 2847, 3050, 3253, 3459, 3462, 3464, 3509, 3663, 3665, 3667, 3712, 3714, 3721, 3862, 4065, 4270, 4283, 4314, 4396, 4398, 4433, 4583, 4598] :=
    ⟨Fin 4, «FinitePoly [[2,0,3,1],[3,1,1,3],[3,2,2,3],[1,3,3,1]]», by decideFin!⟩
