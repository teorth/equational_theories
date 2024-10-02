
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[3, 3, 2, 3], [3, 3, 3, 3], [1, 1, 1, 0], [0, 1, 0, 1]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[3, 3, 2, 3], [3, 3, 3, 3], [1, 1, 1, 0], [0, 1, 0, 1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[3, 3, 2, 3], [3, 3, 3, 3], [1, 1, 1, 0], [0, 1, 0, 1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[3, 3, 2, 3], [3, 3, 3, 3], [1, 1, 1, 0], [0, 1, 0, 1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [307, 2443, 3055, 3075, 3256] [8, 23, 151, 203, 309, 323, 326, 411, 614, 817, 1020, 1223, 1426, 1629, 1832, 2035, 2238, 2442, 2444, 2446, 2447, 2450, 2456, 2457, 2459, 2460, 2466, 2467, 2469, 2470, 2493, 2494, 2496, 2497, 2503, 2504, 2506, 2507, 2530, 2531, 2533, 2534, 2540, 2541, 2543, 2644, 2847, 3051, 3052, 3053, 3056, 3058, 3059, 3065, 3066, 3068, 3069, 3076, 3078, 3079, 3102, 3103, 3105, 3106, 3112, 3113, 3115, 3116, 3139, 3140, 3142, 3143, 3149, 3150, 3152, 3319, 3456, 3659, 3862, 4065, 4380] :=
    ⟨Fin 4, «FinitePoly [[3, 3, 2, 3], [3, 3, 3, 3], [1, 1, 1, 0], [0, 1, 0, 1]]», by decideFin!⟩
