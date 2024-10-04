
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,3,3],[3,2,1,3],[2,3,0,3],[0,1,2,3]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,3,3],[3,2,1,3],[2,3,0,3],[0,1,2,3]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,0,3,3],[3,2,1,3],[2,3,0,3],[0,1,2,3]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,3,3],[3,2,1,3],[2,3,0,3],[0,1,2,3]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [283, 2609] [47, 99, 151, 203, 263, 273, 280, 307, 413, 416, 419, 426, 429, 436, 439, 463, 466, 473, 476, 500, 503, 510, 513, 614, 817, 1022, 1025, 1028, 1035, 1038, 1045, 1048, 1072, 1075, 1082, 1085, 1109, 1112, 1119, 1122, 1223, 1426, 1629, 1834, 1837, 1840, 1847, 1850, 1857, 1860, 1884, 1887, 1894, 1897, 1921, 1924, 1931, 1934, 2035, 2238, 2443, 2446, 2449, 2456, 2459, 2466, 2496, 2503, 2506, 2530, 2533, 2540, 2644, 2847, 3050, 3255, 3258, 3261, 3268, 3271, 3278, 3281, 3309, 3316, 3343, 3346, 3353, 3456, 3659, 3864, 3867, 3870, 3877, 3880, 3887, 3890, 3918, 3925, 3928, 3952, 3955, 3962, 4065, 4269, 4272, 4275, 4284, 4291, 4320, 4380, 4584, 4587, 4590, 4599, 4606, 4635] :=
    ⟨Fin 4, «FinitePoly [[1,0,3,3],[3,2,1,3],[2,3,0,3],[0,1,2,3]]», by decideFin!⟩
