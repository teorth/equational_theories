import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,0,0,1],[3,1,3,0],[3,0,1,1],[1,3,1,1]]
-/
set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,0,0,1],[3,1,3,0],[3,0,1,1],[1,3,1,1]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[1,0,0,1],[3,1,3,0],[3,0,1,1],[1,3,1,1]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,0,0,1],[3,1,3,0],[3,0,1,1],[1,3,1,1]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [3714,3761,3823] [43,3253,3256,3259,3261,3269,3271,3278,3282,3286,3294,3297,3306,3308,3315,3319,3323,3331,3334,3342,3346,3350,3353,3355,3364,3370,3385,3388,3398,3404,3414,3417,3737,3748,3810,3862,3865,3870,3878,3887,3891,3895,3906,3915,3924,3928,3932,3943,3962,4007,4023,4275,4290,4297,4307,4369,4380,4435,4588,4598,4620,4647,4673] :=
    ⟨Fin 4, «FinitePoly [[1,0,0,1],[3,1,3,0],[3,0,1,1],[1,3,1,1]]», by decideFin!⟩
