import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,3,1,1],[3,1,2,3],[0,3,2,1],[0,1,2,3]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[0,3,1,1],[3,1,2,3],[0,3,2,1],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[0,3,1,1],[3,1,2,3],[0,3,2,1],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[0,3,1,1],[3,1,2,3],[0,3,2,1],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [28,290,2347,2567,2804,2956,3024,3122,3159,3193,3210,3227] [208,238,333,632,642,653,669,679,690,703,713,723,825,845,860,872,879,909,916,947,960,1025,1055,1434,1444,1451,1491,1506,1518,1525,1560,1586,1647,1847,1958,2253,2263,2273,2300,2310,2364,2381,2398,2415,2446,2466,2476,2503,2513,2550,2584,2601,2618,2649,2679,2716,2753,2787,2821,3068,3346,3474,3484,3495,3546,3556,3566,3667,3687,3702,3752,3759,3790,3803,3867,3897,4128,4138,4165,4175,4209,4226,4243,4320,4362,4399,4409,4420,4435,4445,4456,4480,4490] :=
    ⟨Fin 4, «FinitePoly [[0,3,1,1],[3,1,2,3],[0,3,2,1],[0,1,2,3]]», by decideFin!⟩
