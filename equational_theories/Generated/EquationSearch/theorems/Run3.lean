import equational_theories.Generated.SimpleRewrites
import equational_theories.Generated.Constant
import equational_theories.Generated.Singleton
import equational_theories.Generated.TrivialBruteforce
import equational_theories.Generated.FinitePoly
import equational_theories.Generated.EquationSearch.theorems.Run1
import equational_theories.Generated.EquationSearch.theorems.Run2
import equational_theories.Subgraph

namespace Run3
@[equational_result]
theorem Equation3282_implies_Equation3286 (G: Type _) [Magma G] (h: Equation3282 G) : Equation3286 G := by
  have eq3278 (x y : G) : x ◇ x = y ◇ (y ◇ (x ◇ x)) := by
    apply RewriteCombinations.Equation3282_implies_Equation3278 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteCombinations.Equation3282_implies_Equation3278 at h
    apply Apply.Equation3278_implies_Equation3253 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq3278]
  nth_rewrite 1 [eq3253]
  symm
  apply h
@[equational_result]
theorem Equation9_implies_Equation1224 (G: Type _) [Magma G] (h: Equation9 G) : Equation1224 G := by
  have eq4118 (x y : G) : x ◇ y = ((x ◇ x) ◇ x) ◇ y := by
    apply Run2.Equation9_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation23 at h
    apply RewriteHypothesis.Equation23_implies_Equation4118 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq4118]
  symm
  apply h
@[equational_result]
theorem Equation9_implies_Equation823 (G: Type _) [Magma G] (h: Equation9 G) : Equation823 G := by
  have eq3722 (x y : G) : x ◇ y = (x ◇ y) ◇ (x ◇ y) := by
    apply Run2.Equation9_implies_Equation3 at h
    apply Apply.Equation3_implies_Equation3722 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq3722]
  symm
  apply h
@[equational_result]
theorem Equation4094_implies_Equation4098 (G: Type _) [Magma G] (h: Equation4094 G) : Equation4098 G := by
  have eq4068 (x y : G) : x ◇ x = ((x ◇ x) ◇ y) ◇ y := by
    apply RewriteCombinations.Equation4094_implies_Equation4068 at h
    apply h
  have eq4065 (x : G) : x ◇ x = ((x ◇ x) ◇ x) ◇ x := by
    apply RewriteCombinations.Equation4094_implies_Equation4068 at h
    apply Apply.Equation4068_implies_Equation4065 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4068]
  nth_rewrite 1 [eq4065]
  symm
  apply h
@[equational_result]
theorem Equation4095_implies_Equation4098 (G: Type _) [Magma G] (h: Equation4095 G) : Equation4098 G := by
  have eq4068 (x y : G) : x ◇ x = ((x ◇ x) ◇ y) ◇ y := by
    apply Apply.Equation4095_implies_Equation4094 at h
    apply RewriteCombinations.Equation4094_implies_Equation4068 at h
    apply h
  have eq4066 (x y : G) : x ◇ x = ((x ◇ x) ◇ x) ◇ y := by
    apply Apply.Equation4095_implies_Equation4066 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4068]
  nth_rewrite 1 [eq4066]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3293_implies_Equation320 (G: Type _) [Magma G] (h: Equation3293 G) : Equation320 G := by
  have eq312 (x y : G) : x ◇ x = y ◇ (x ◇ x) := by
    apply RewriteCombinations.Equation3293_implies_Equation312 at h
    apply h
  have eq3258 (x y : G) : x ◇ x = x ◇ (y ◇ (x ◇ x)) := by
    apply RewriteCombinations.Equation3293_implies_Equation312 at h
    apply RewriteHypothesis.Equation312_implies_Equation3288 at h
    apply Apply.Equation3288_implies_Equation3258 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq312]
  nth_rewrite 1 [eq3258]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4097_implies_Equation369 (G: Type _) [Magma G] (h: Equation4097 G) : Equation369 G := by
  have eq360 (x y : G) : x ◇ x = (x ◇ x) ◇ y := by
    apply RewriteCombinations.Equation4097_implies_Equation360 at h
    apply h
  have eq4067 (x y : G) : x ◇ x = ((x ◇ x) ◇ y) ◇ x := by
    apply RewriteCombinations.Equation4097_implies_Equation360 at h
    apply RewriteHypothesis.Equation360_implies_Equation4069 at h
    apply Apply.Equation4069_implies_Equation4067 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq360]
  nth_rewrite 1 [eq4067]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4105_implies_Equation4098 (G: Type _) [Magma G] (h: Equation4105 G) : Equation4098 G := by
  have eq4068 (x y : G) : x ◇ x = ((x ◇ x) ◇ y) ◇ y := by
    apply Apply.Equation4105_implies_Equation4094 at h
    apply RewriteCombinations.Equation4094_implies_Equation4068 at h
    apply h
  have eq4070 (x y : G) : x ◇ x = ((x ◇ y) ◇ x) ◇ x := by
    apply Apply.Equation4105_implies_Equation4070 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4068]
  nth_rewrite 1 [eq4070]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4106_implies_Equation4098 (G: Type _) [Magma G] (h: Equation4106 G) : Equation4098 G := by
  have eq4068 (x y : G) : x ◇ x = ((x ◇ x) ◇ y) ◇ y := by
    apply Apply.Equation4106_implies_Equation4094 at h
    apply RewriteCombinations.Equation4094_implies_Equation4068 at h
    apply h
  have eq4071 (x y : G) : x ◇ x = ((x ◇ y) ◇ x) ◇ y := by
    apply Apply.Equation4106_implies_Equation4071 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4068]
  nth_rewrite 1 [eq4071]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3299_implies_Equation3293 (G: Type _) [Magma G] (h: Equation3299 G) : Equation3293 G := by
  have eq3258 (x y : G) : x ◇ x = x ◇ (y ◇ (x ◇ x)) := by
    apply Apply.Equation3299_implies_Equation3263 at h
    apply RewriteCombinations.Equation3263_implies_Equation310 at h
    apply RewriteHypothesis.Equation310_implies_Equation3266 at h
    apply Apply.Equation3266_implies_Equation3258 at h
    apply h
  have eq3263 (x y z : G) : x ◇ x = x ◇ (y ◇ (y ◇ z)) := by
    apply Apply.Equation3299_implies_Equation3263 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq3258]
  nth_rewrite 1 [eq3263]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4109_implies_Equation4098 (G: Type _) [Magma G] (h: Equation4109 G) : Equation4098 G := by
  have eq4068 (x y : G) : x ◇ x = ((x ◇ x) ◇ y) ◇ y := by
    apply Apply.Equation4109_implies_Equation4094 at h
    apply RewriteCombinations.Equation4094_implies_Equation4068 at h
    apply h
  have eq4073 (x y : G) : x ◇ x = ((x ◇ y) ◇ y) ◇ x := by
    apply Apply.Equation4109_implies_Equation4073 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4068]
  nth_rewrite 1 [eq4073]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4110_implies_Equation4098 (G: Type _) [Magma G] (h: Equation4110 G) : Equation4098 G := by
  have eq4068 (x y : G) : x ◇ x = ((x ◇ x) ◇ y) ◇ y := by
    apply Apply.Equation4110_implies_Equation4094 at h
    apply RewriteCombinations.Equation4094_implies_Equation4068 at h
    apply h
  have eq4074 (x y : G) : x ◇ x = ((x ◇ y) ◇ y) ◇ y := by
    apply Apply.Equation4110_implies_Equation4074 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4068]
  nth_rewrite 1 [eq4074]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4111_implies_Equation4097 (G: Type _) [Magma G] (h: Equation4111 G) : Equation4097 G := by
  have eq4067 (x y : G) : x ◇ x = ((x ◇ x) ◇ y) ◇ x := by
    apply Apply.Equation4111_implies_Equation4108 at h
    apply RewriteCombinations.Equation4108_implies_Equation367 at h
    apply RewriteHypothesis.Equation367_implies_Equation4096 at h
    apply Apply.Equation4096_implies_Equation4067 at h
    apply h
  have eq4075 (x y z : G) : x ◇ x = ((x ◇ y) ◇ y) ◇ z := by
    apply Apply.Equation4111_implies_Equation4075 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4067]
  nth_rewrite 1 [eq4075]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3344_implies_Equation3348 (G: Type _) [Magma G] (h: Equation3344 G) : Equation3348 G := by
  have eq4283 (x y : G) : x ◇ (x ◇ y) = x ◇ (y ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation3344_implies_Equation332 at h
    apply Run2.Equation332_implies_Equation387 at h
    apply Subgraph.Equation387_implies_Equation43 at h
    apply NthRewrites.Equation43_implies_Equation4358 at h
    apply Apply.Equation4358_implies_Equation4283 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4283]
  symm
  apply h
@[equational_result]
theorem Equation3344_implies_Equation3551 (G: Type _) [Magma G] (h: Equation3344 G) : Equation3551 G := by
  have eq4398 (x y : G) : x ◇ (x ◇ y) = (x ◇ y) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation3344_implies_Equation332 at h
    apply Run2.Equation332_implies_Equation387 at h
    apply Subgraph.Equation387_implies_Equation43 at h
    apply Apply.Equation43_implies_Equation4531 at h
    apply Apply.Equation4531_implies_Equation4398 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4398]
  symm
  apply h
@[equational_result]
theorem Equation28_implies_Equation166 (G: Type _) [Magma G] (h: Equation28 G) : Equation166 G := by
  have eq3674 (x y : G) : x ◇ x = (y ◇ x) ◇ (x ◇ x) := by
    apply Run2.Equation28_implies_Equation3674 at h
    apply h
  have eq364 (x y : G) : x ◇ x = (y ◇ x) ◇ x := by
    apply Run1.Equation28_implies_Equation364 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq3674]
  nth_rewrite 1 [eq364]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3371_implies_Equation3451 (G: Type _) [Magma G] (h: Equation3371 G) : Equation3451 G := by
  have eq3338 (x y z w : G) : x ◇ y = x ◇ (z ◇ (w ◇ y)) := by
    apply RewriteCombinations.Equation3371_implies_Equation3446 at h
    apply Apply.Equation3446_implies_Equation3422 at h
    apply RewriteCombinations.Equation3422_implies_Equation3401 at h
    apply Apply.Equation3401_implies_Equation3356 at h
    apply NthRewrites.Equation3356_implies_Equation3367 at h
    apply RewriteCombinations.Equation3367_implies_Equation3330 at h
    apply NthRewrites.Equation3330_implies_Equation3312 at h
    apply NthRewrites.Equation3312_implies_Equation3338 at h
    apply h
  have eq3343 (x y : G) : x ◇ y = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteCombinations.Equation3371_implies_Equation3446 at h
    apply Apply.Equation3446_implies_Equation3422 at h
    apply RewriteCombinations.Equation3422_implies_Equation3401 at h
    apply Run2.Equation3401_implies_Equation3375 at h
    apply Apply.Equation3375_implies_Equation3349 at h
    apply Apply.Equation3349_implies_Equation3343 at h
    apply h
  intro x y z w u
  symm
  nth_rewrite 1 [← eq3338]
  nth_rewrite 1 [eq3343]
  symm
  apply h
@[equational_result]
theorem Equation3384_implies_Equation3436 (G: Type _) [Magma G] (h: Equation3384 G) : Equation3436 G := by
  have eq3288 (x y z : G) : x ◇ x = y ◇ (z ◇ (x ◇ x)) := by
    apply NthRewrites.Equation3384_implies_Equation3431 at h
    apply Apply.Equation3431_implies_Equation3288 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq3288]
  nth_rewrite 1 [eq3288]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3392_implies_Equation3451 (G: Type _) [Magma G] (h: Equation3392 G) : Equation3451 G := by
  have eq45 (x y z : G) : x ◇ y = z ◇ y := by
    apply Run2.Equation3392_implies_Equation45 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [← eq45]
  apply h
@[equational_result]
theorem Equation3405_implies_Equation3451 (G: Type _) [Magma G] (h: Equation3405 G) : Equation3451 G := by
  have eq3338 (x y z w : G) : x ◇ y = x ◇ (z ◇ (w ◇ y)) := by
    apply RewriteCombinations.Equation3405_implies_Equation3401 at h
    apply Apply.Equation3401_implies_Equation3356 at h
    apply NthRewrites.Equation3356_implies_Equation3367 at h
    apply RewriteCombinations.Equation3367_implies_Equation3330 at h
    apply NthRewrites.Equation3330_implies_Equation3312 at h
    apply NthRewrites.Equation3312_implies_Equation3338 at h
    apply h
  have eq3316 (x y : G) : x ◇ y = x ◇ (y ◇ (x ◇ y)) := by
    apply RewriteCombinations.Equation3405_implies_Equation3401 at h
    apply Apply.Equation3401_implies_Equation3356 at h
    apply NthRewrites.Equation3356_implies_Equation3367 at h
    apply RewriteCombinations.Equation3367_implies_Equation3330 at h
    apply NthRewrites.Equation3330_implies_Equation3322 at h
    apply Apply.Equation3322_implies_Equation3316 at h
    apply h
  intro x y z w u
  symm
  nth_rewrite 1 [← eq3338]
  nth_rewrite 1 [eq3316]
  symm
  apply h
@[equational_result]
theorem Equation3418_implies_Equation3451 (G: Type _) [Magma G] (h: Equation3418 G) : Equation3451 G := by
  have eq3338 (x y z w : G) : x ◇ y = x ◇ (z ◇ (w ◇ y)) := by
    apply RewriteCombinations.Equation3418_implies_Equation3436 at h
    apply Run2.Equation3436_implies_Equation3446 at h
    apply Apply.Equation3446_implies_Equation3422 at h
    apply RewriteCombinations.Equation3422_implies_Equation3401 at h
    apply Apply.Equation3401_implies_Equation3356 at h
    apply NthRewrites.Equation3356_implies_Equation3367 at h
    apply RewriteCombinations.Equation3367_implies_Equation3330 at h
    apply NthRewrites.Equation3330_implies_Equation3312 at h
    apply NthRewrites.Equation3312_implies_Equation3338 at h
    apply h
  have eq3309 (x y : G) : x ◇ y = x ◇ (x ◇ (y ◇ y)) := by
    apply RewriteCombinations.Equation3418_implies_Equation3436 at h
    apply Run2.Equation3436_implies_Equation3446 at h
    apply Apply.Equation3446_implies_Equation3422 at h
    apply RewriteCombinations.Equation3422_implies_Equation3401 at h
    apply Apply.Equation3401_implies_Equation3356 at h
    apply NthRewrites.Equation3356_implies_Equation3367 at h
    apply RewriteCombinations.Equation3367_implies_Equation3330 at h
    apply Apply.Equation3330_implies_Equation3309 at h
    apply h
  intro x y z w u
  symm
  nth_rewrite 1 [← eq3338]
  nth_rewrite 1 [eq3309]
  symm
  apply h
@[equational_result]
theorem Equation3422_implies_Equation3451 (G: Type _) [Magma G] (h: Equation3422 G) : Equation3451 G := by
  have eq3338 (x y z w : G) : x ◇ y = x ◇ (z ◇ (w ◇ y)) := by
    apply RewriteCombinations.Equation3422_implies_Equation3401 at h
    apply Apply.Equation3401_implies_Equation3356 at h
    apply NthRewrites.Equation3356_implies_Equation3367 at h
    apply RewriteCombinations.Equation3367_implies_Equation3330 at h
    apply NthRewrites.Equation3330_implies_Equation3312 at h
    apply NthRewrites.Equation3312_implies_Equation3338 at h
    apply h
  have eq3306 (x y : G) : x ◇ y = x ◇ (x ◇ (x ◇ y)) := by
    apply NthRewrites.Equation3422_implies_Equation3388 at h
    apply NthRewrites.Equation3388_implies_Equation3334 at h
    apply Apply.Equation3334_implies_Equation3306 at h
    apply h
  intro x y z w u
  symm
  nth_rewrite 1 [← eq3338]
  nth_rewrite 1 [eq3306]
  symm
  apply h
@[equational_result]
theorem Equation3426_implies_Equation3451 (G: Type _) [Magma G] (h: Equation3426 G) : Equation3451 G := by
  have eq3338 (x y z w : G) : x ◇ y = x ◇ (z ◇ (w ◇ y)) := by
    apply Apply.Equation3426_implies_Equation3422 at h
    apply RewriteCombinations.Equation3422_implies_Equation3401 at h
    apply Apply.Equation3401_implies_Equation3356 at h
    apply NthRewrites.Equation3356_implies_Equation3367 at h
    apply RewriteCombinations.Equation3367_implies_Equation3330 at h
    apply NthRewrites.Equation3330_implies_Equation3312 at h
    apply NthRewrites.Equation3312_implies_Equation3338 at h
    apply h
  have eq3312 (x y z : G) : x ◇ y = x ◇ (x ◇ (z ◇ y)) := by
    apply Apply.Equation3426_implies_Equation3422 at h
    apply RewriteCombinations.Equation3422_implies_Equation3401 at h
    apply Apply.Equation3401_implies_Equation3356 at h
    apply NthRewrites.Equation3356_implies_Equation3367 at h
    apply RewriteCombinations.Equation3367_implies_Equation3330 at h
    apply NthRewrites.Equation3330_implies_Equation3312 at h
    apply h
  intro x y z w u
  symm
  nth_rewrite 1 [← eq3338]
  nth_rewrite 1 [eq3312]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3436_implies_Equation3451 (G: Type _) [Magma G] (h: Equation3436 G) : Equation3451 G := by
  have eq3338 (x y z w : G) : x ◇ y = x ◇ (z ◇ (w ◇ y)) := by
    apply Run2.Equation3436_implies_Equation3446 at h
    apply Apply.Equation3446_implies_Equation3422 at h
    apply RewriteCombinations.Equation3422_implies_Equation3401 at h
    apply Apply.Equation3401_implies_Equation3356 at h
    apply NthRewrites.Equation3356_implies_Equation3367 at h
    apply RewriteCombinations.Equation3367_implies_Equation3330 at h
    apply NthRewrites.Equation3330_implies_Equation3312 at h
    apply NthRewrites.Equation3312_implies_Equation3338 at h
    apply h
  have eq3330 (x y z : G) : x ◇ y = x ◇ (z ◇ (y ◇ y)) := by
    apply Run2.Equation3436_implies_Equation3446 at h
    apply Apply.Equation3446_implies_Equation3422 at h
    apply RewriteCombinations.Equation3422_implies_Equation3401 at h
    apply Apply.Equation3401_implies_Equation3356 at h
    apply NthRewrites.Equation3356_implies_Equation3367 at h
    apply RewriteCombinations.Equation3367_implies_Equation3330 at h
    apply h
  intro x y z w u
  symm
  nth_rewrite 1 [← eq3338]
  nth_rewrite 1 [eq3330]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3441_implies_Equation3451 (G: Type _) [Magma G] (h: Equation3441 G) : Equation3451 G := by
  have eq3338 (x y z w : G) : x ◇ y = x ◇ (z ◇ (w ◇ y)) := by
    apply Apply.Equation3441_implies_Equation3422 at h
    apply RewriteCombinations.Equation3422_implies_Equation3401 at h
    apply Apply.Equation3401_implies_Equation3356 at h
    apply NthRewrites.Equation3356_implies_Equation3367 at h
    apply RewriteCombinations.Equation3367_implies_Equation3330 at h
    apply NthRewrites.Equation3330_implies_Equation3312 at h
    apply NthRewrites.Equation3312_implies_Equation3338 at h
    apply h
  have eq3326 (x y z : G) : x ◇ y = x ◇ (z ◇ (x ◇ y)) := by
    apply Apply.Equation3441_implies_Equation3422 at h
    apply RewriteCombinations.Equation3422_implies_Equation3401 at h
    apply Apply.Equation3401_implies_Equation3356 at h
    apply NthRewrites.Equation3356_implies_Equation3367 at h
    apply RewriteCombinations.Equation3367_implies_Equation3330 at h
    apply NthRewrites.Equation3330_implies_Equation3326 at h
    apply h
  intro x y z w u
  symm
  nth_rewrite 1 [← eq3338]
  nth_rewrite 1 [eq3326]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3485_implies_Equation3500 (G: Type _) [Magma G] (h: Equation3485 G) : Equation3500 G := by
  have eq3472 (x y : G) : x ◇ x = y ◇ ((x ◇ x) ◇ y) := by
    apply RewriteCombinations.Equation3485_implies_Equation3472 at h
    apply h
  have eq3456 (x : G) : x ◇ x = x ◇ ((x ◇ x) ◇ x) := by
    apply RewriteCombinations.Equation3485_implies_Equation3472 at h
    apply Apply.Equation3472_implies_Equation3456 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq3472]
  nth_rewrite 1 [eq3456]
  symm
  apply h
@[equational_result]
theorem Equation3486_implies_Equation3500 (G: Type _) [Magma G] (h: Equation3486 G) : Equation3500 G := by
  have eq3472 (x y : G) : x ◇ x = y ◇ ((x ◇ x) ◇ y) := by
    apply Apply.Equation3486_implies_Equation3485 at h
    apply RewriteCombinations.Equation3485_implies_Equation3472 at h
    apply h
  have eq3457 (x y : G) : x ◇ x = x ◇ ((x ◇ x) ◇ y) := by
    apply Apply.Equation3486_implies_Equation3457 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq3472]
  nth_rewrite 1 [eq3457]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3488_implies_Equation3500 (G: Type _) [Magma G] (h: Equation3488 G) : Equation3500 G := by
  have eq3472 (x y : G) : x ◇ x = y ◇ ((x ◇ x) ◇ y) := by
    apply Apply.Equation3488_implies_Equation3485 at h
    apply RewriteCombinations.Equation3485_implies_Equation3472 at h
    apply h
  have eq3458 (x y : G) : x ◇ x = x ◇ ((x ◇ y) ◇ x) := by
    apply Apply.Equation3488_implies_Equation3458 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq3472]
  nth_rewrite 1 [eq3458]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3489_implies_Equation3500 (G: Type _) [Magma G] (h: Equation3489 G) : Equation3500 G := by
  have eq3472 (x y : G) : x ◇ x = y ◇ ((x ◇ x) ◇ y) := by
    apply Apply.Equation3489_implies_Equation3485 at h
    apply RewriteCombinations.Equation3485_implies_Equation3472 at h
    apply h
  have eq3459 (x y : G) : x ◇ x = x ◇ ((x ◇ y) ◇ y) := by
    apply Apply.Equation3489_implies_Equation3459 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq3472]
  nth_rewrite 1 [eq3459]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3496_implies_Equation3500 (G: Type _) [Magma G] (h: Equation3496 G) : Equation3500 G := by
  have eq3472 (x y : G) : x ◇ x = y ◇ ((x ◇ x) ◇ y) := by
    apply Apply.Equation3496_implies_Equation3485 at h
    apply RewriteCombinations.Equation3485_implies_Equation3472 at h
    apply h
  have eq3461 (x y : G) : x ◇ x = x ◇ ((y ◇ x) ◇ x) := by
    apply Apply.Equation3496_implies_Equation3461 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq3472]
  nth_rewrite 1 [eq3461]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3497_implies_Equation3500 (G: Type _) [Magma G] (h: Equation3497 G) : Equation3500 G := by
  have eq3472 (x y : G) : x ◇ x = y ◇ ((x ◇ x) ◇ y) := by
    apply Apply.Equation3497_implies_Equation3485 at h
    apply RewriteCombinations.Equation3485_implies_Equation3472 at h
    apply h
  have eq3462 (x y : G) : x ◇ x = x ◇ ((y ◇ x) ◇ y) := by
    apply Apply.Equation3497_implies_Equation3462 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq3472]
  nth_rewrite 1 [eq3462]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3501_implies_Equation3293 (G: Type _) [Magma G] (h: Equation3501 G) : Equation3293 G := by
  have eq3258 (x y : G) : x ◇ x = x ◇ (y ◇ (x ◇ x)) := by
    apply Apply.Equation3501_implies_Equation3471 at h
    apply NthRewrites.Equation3471_implies_Equation312 at h
    apply RewriteHypothesis.Equation312_implies_Equation3288 at h
    apply Apply.Equation3288_implies_Equation3258 at h
    apply h
  have eq3465 (x y : G) : x ◇ x = x ◇ ((y ◇ y) ◇ y) := by
    apply Apply.Equation3501_implies_Equation3465 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq3258]
  nth_rewrite 1 [eq3465]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3501_implies_Equation3500 (G: Type _) [Magma G] (h: Equation3501 G) : Equation3500 G := by
  have eq3472 (x y : G) : x ◇ x = y ◇ ((x ◇ x) ◇ y) := by
    apply Apply.Equation3501_implies_Equation3485 at h
    apply RewriteCombinations.Equation3485_implies_Equation3472 at h
    apply h
  have eq3465 (x y : G) : x ◇ x = x ◇ ((y ◇ y) ◇ y) := by
    apply Apply.Equation3501_implies_Equation3465 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq3472]
  nth_rewrite 1 [eq3465]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3567_implies_Equation3364 (G: Type _) [Magma G] (h: Equation3567 G) : Equation3364 G := by
  have eq4435 (x y : G) : x ◇ (y ◇ x) = (x ◇ y) ◇ x := by
    apply Run2.Equation3567_implies_Equation3370 at h
    apply Apply.Equation3370_implies_Equation3355 at h
    apply NthRewrites.Equation3355_implies_Equation4435 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq4435]
  symm
  apply h
@[equational_result]
theorem Equation3568_implies_Equation3581 (G: Type _) [Magma G] (h: Equation3568 G) : Equation3581 G := by
  have eq3565 (x y z : G) : x ◇ y = y ◇ ((z ◇ x) ◇ x) := by
    apply Apply.Equation3568_implies_Equation3565 at h
    apply h
  have eq3553 (x y z : G) : x ◇ y = y ◇ ((x ◇ z) ◇ z) := by
    apply Apply.Equation3568_implies_Equation3567 at h
    apply Run2.Equation3567_implies_Equation3370 at h
    apply NthRewrites.Equation3370_implies_Equation3553 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [eq3565]
  nth_rewrite 1 [← eq3553]
  apply h
@[equational_result]
theorem Equation3891_implies_Equation3906 (G: Type _) [Magma G] (h: Equation3891 G) : Equation3906 G := by
  have eq3878 (x y : G) : x ◇ x = (y ◇ (x ◇ x)) ◇ y := by
    apply RewriteCombinations.Equation3891_implies_Equation3878 at h
    apply h
  have eq3862 (x : G) : x ◇ x = (x ◇ (x ◇ x)) ◇ x := by
    apply RewriteCombinations.Equation3891_implies_Equation3878 at h
    apply Apply.Equation3878_implies_Equation3862 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq3878]
  nth_rewrite 1 [eq3862]
  symm
  apply h
@[equational_result]
theorem Equation3892_implies_Equation3906 (G: Type _) [Magma G] (h: Equation3892 G) : Equation3906 G := by
  have eq3878 (x y : G) : x ◇ x = (y ◇ (x ◇ x)) ◇ y := by
    apply Apply.Equation3892_implies_Equation3891 at h
    apply RewriteCombinations.Equation3891_implies_Equation3878 at h
    apply h
  have eq3863 (x y : G) : x ◇ x = (x ◇ (x ◇ x)) ◇ y := by
    apply Apply.Equation3892_implies_Equation3863 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq3878]
  nth_rewrite 1 [eq3863]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3892_implies_Equation4097 (G: Type _) [Magma G] (h: Equation3892 G) : Equation4097 G := by
  have eq4067 (x y : G) : x ◇ x = ((x ◇ x) ◇ y) ◇ x := by
    apply Apply.Equation3892_implies_Equation3863 at h
    apply NthRewrites.Equation3863_implies_Equation360 at h
    apply RewriteHypothesis.Equation360_implies_Equation4069 at h
    apply Apply.Equation4069_implies_Equation4067 at h
    apply h
  have eq3863 (x y : G) : x ◇ x = (x ◇ (x ◇ x)) ◇ y := by
    apply Apply.Equation3892_implies_Equation3863 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4067]
  nth_rewrite 1 [eq3863]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3894_implies_Equation3906 (G: Type _) [Magma G] (h: Equation3894 G) : Equation3906 G := by
  have eq3878 (x y : G) : x ◇ x = (y ◇ (x ◇ x)) ◇ y := by
    apply Apply.Equation3894_implies_Equation3891 at h
    apply RewriteCombinations.Equation3891_implies_Equation3878 at h
    apply h
  have eq3864 (x y : G) : x ◇ x = (x ◇ (x ◇ y)) ◇ x := by
    apply Apply.Equation3894_implies_Equation3864 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq3878]
  nth_rewrite 1 [eq3864]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3895_implies_Equation3906 (G: Type _) [Magma G] (h: Equation3895 G) : Equation3906 G := by
  have eq3878 (x y : G) : x ◇ x = (y ◇ (x ◇ x)) ◇ y := by
    apply Apply.Equation3895_implies_Equation3891 at h
    apply RewriteCombinations.Equation3891_implies_Equation3878 at h
    apply h
  have eq3865 (x y : G) : x ◇ x = (x ◇ (x ◇ y)) ◇ y := by
    apply Apply.Equation3895_implies_Equation3865 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq3878]
  nth_rewrite 1 [eq3865]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3902_implies_Equation3906 (G: Type _) [Magma G] (h: Equation3902 G) : Equation3906 G := by
  have eq3878 (x y : G) : x ◇ x = (y ◇ (x ◇ x)) ◇ y := by
    apply Apply.Equation3902_implies_Equation3891 at h
    apply RewriteCombinations.Equation3891_implies_Equation3878 at h
    apply h
  have eq3867 (x y : G) : x ◇ x = (x ◇ (y ◇ x)) ◇ x := by
    apply Apply.Equation3902_implies_Equation3867 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq3878]
  nth_rewrite 1 [eq3867]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3903_implies_Equation3906 (G: Type _) [Magma G] (h: Equation3903 G) : Equation3906 G := by
  have eq3878 (x y : G) : x ◇ x = (y ◇ (x ◇ x)) ◇ y := by
    apply Apply.Equation3903_implies_Equation3891 at h
    apply RewriteCombinations.Equation3891_implies_Equation3878 at h
    apply h
  have eq3868 (x y : G) : x ◇ x = (x ◇ (y ◇ x)) ◇ y := by
    apply Apply.Equation3903_implies_Equation3868 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq3878]
  nth_rewrite 1 [eq3868]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3907_implies_Equation3906 (G: Type _) [Magma G] (h: Equation3907 G) : Equation3906 G := by
  have eq3878 (x y : G) : x ◇ x = (y ◇ (x ◇ x)) ◇ y := by
    apply Apply.Equation3907_implies_Equation3891 at h
    apply RewriteCombinations.Equation3891_implies_Equation3878 at h
    apply h
  have eq3871 (x y : G) : x ◇ x = (x ◇ (y ◇ y)) ◇ y := by
    apply Apply.Equation3907_implies_Equation3871 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq3878]
  nth_rewrite 1 [eq3871]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation387_implies_Equation4343 (G: Type _) [Magma G] (h: Equation387 G) : Equation4343 G := by
  have eq4470 (x y : G) : x ◇ (y ◇ y) = (x ◇ x) ◇ y := by
    apply Run2.Equation387_implies_Equation4470 at h
    apply h
  have eq326 (x y : G) : x ◇ y = x ◇ (y ◇ y) := by
    apply RewriteHypothesis.Equation387_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation326 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [eq4470]
  symm
  nth_rewrite 1 [← eq326]
  apply h
@[equational_result]
theorem Equation387_implies_Equation332 (G: Type _) [Magma G] (h: Equation387 G) : Equation332 G := by
  have eq4470 (x y : G) : x ◇ (y ◇ y) = (x ◇ x) ◇ y := by
    apply Run2.Equation387_implies_Equation4470 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [eq4470]
  symm
  apply h
@[equational_result]
theorem Equation387_implies_Equation3342 (G: Type _) [Magma G] (h: Equation387 G) : Equation3342 G := by
  have eq3319 (x y : G) : x ◇ y = x ◇ (y ◇ (y ◇ y)) := by
    apply RewriteHypothesis.Equation387_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation326 at h
    apply RewriteHypothesis.Equation326_implies_Equation3319 at h
    apply h
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply RewriteHypothesis.Equation387_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation375 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq3319]
  nth_rewrite 1 [eq375]
  symm
  apply h
@[equational_result]
theorem Equation387_implies_Equation3545 (G: Type _) [Magma G] (h: Equation387 G) : Equation3545 G := by
  have eq3522 (x y : G) : x ◇ y = x ◇ ((y ◇ y) ◇ y) := by
    apply RewriteHypothesis.Equation387_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation326 at h
    apply NthRewrites.Equation326_implies_Equation3522 at h
    apply h
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply RewriteHypothesis.Equation387_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation375 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq3522]
  nth_rewrite 1 [eq375]
  symm
  apply h
@[equational_result]
theorem Equation387_implies_Equation3758 (G: Type _) [Magma G] (h: Equation387 G) : Equation3758 G := by
  have eq3715 (x y : G) : x ◇ y = (x ◇ x) ◇ (y ◇ y) := by
    apply RewriteHypothesis.Equation387_implies_Equation3715 at h
    apply h
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply RewriteHypothesis.Equation387_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation375 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq3715]
  nth_rewrite 1 [eq375]
  symm
  apply h
@[equational_result]
theorem Equation9_implies_Equation4395 (G: Type _) [Magma G] (h: Equation9 G) : Equation4395 G := by
  have eq4380 (x : G) : x ◇ (x ◇ x) = (x ◇ x) ◇ x := by
    apply Run2.Equation9_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation4470 at h
    apply Apply.Equation4470_implies_Equation4380 at h
    apply h
  have eq308 (x y : G) : x ◇ x = x ◇ (x ◇ y) := by
    apply Run1.Equation9_implies_Equation308 at h
    apply h
  have eq4268 (x y : G) : x ◇ (x ◇ x) = x ◇ (x ◇ y) := by
    apply Run1.Equation9_implies_Equation308 at h
    apply RewriteHypothesis.Equation308_implies_Equation4282 at h
    apply Apply.Equation4282_implies_Equation4268 at h
    apply h
  have eq3 (x : G) : x = x ◇ x := by
    apply Run2.Equation9_implies_Equation3 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq4380]
  symm
  nth_rewrite 1 [← eq308]
  symm
  nth_rewrite 1 [eq4268]
  symm
  nth_rewrite 1 [← eq3]
  apply h
  repeat assumption
@[equational_result]
theorem Equation9_implies_Equation2443 (G: Type _) [Magma G] (h: Equation9 G) : Equation2443 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply Run2.Equation9_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation375 at h
    apply h
  have eq3864 (x y : G) : x ◇ x = (x ◇ (x ◇ y)) ◇ x := by
    apply RewriteHypothesis.Equation9_implies_Equation3921 at h
    apply Apply.Equation3921_implies_Equation3864 at h
    apply h
  have eq308 (x y : G) : x ◇ x = x ◇ (x ◇ y) := by
    apply Run1.Equation9_implies_Equation308 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq375]
  nth_rewrite 1 [← eq3864]
  nth_rewrite 1 [eq308]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation28_implies_Equation1035 (G: Type _) [Magma G] (h: Equation28 G) : Equation1035 G := by
  have eq326 (x y : G) : x ◇ y = x ◇ (y ◇ y) := by
    apply Run1.Equation28_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation326 at h
    apply h
  have eq3461 (x y : G) : x ◇ x = x ◇ ((y ◇ x) ◇ x) := by
    apply RewriteHypothesis.Equation28_implies_Equation3533 at h
    apply Apply.Equation3533_implies_Equation3461 at h
    apply h
  have eq364 (x y : G) : x ◇ x = (y ◇ x) ◇ x := by
    apply Run1.Equation28_implies_Equation364 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq326]
  nth_rewrite 1 [← eq3461]
  nth_rewrite 1 [eq364]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation9_implies_Equation152 (G: Type _) [Magma G] (h: Equation9 G) : Equation152 G := by
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply Run1.Equation9_implies_Equation308 at h
    apply Apply.Equation308_implies_Equation307 at h
    apply h
  have eq3 (x : G) : x = x ◇ x := by
    apply Run2.Equation9_implies_Equation3 at h
    apply h
  have eq1833 (x y : G) : x = (x ◇ (x ◇ x)) ◇ (x ◇ y) := by
    apply RewriteHypothesis.Equation9_implies_Equation1839 at h
    apply Apply.Equation1839_implies_Equation1833 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation9_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation8 at h
    apply h
  have eq4268 (x y : G) : x ◇ (x ◇ x) = x ◇ (x ◇ y) := by
    apply Run1.Equation9_implies_Equation308 at h
    apply RewriteHypothesis.Equation308_implies_Equation4282 at h
    apply Apply.Equation4282_implies_Equation4268 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [eq307]
  symm
  nth_rewrite 1 [eq3 x]
  symm
  nth_rewrite 1 [← eq1833]
  nth_rewrite 1 [eq8 x]
  nth_rewrite 1 [eq4268]
  symm
  nth_rewrite 1 [← eq3]
  apply h
  repeat assumption
@[equational_result]
theorem Equation9_implies_Equation2036 (G: Type _) [Magma G] (h: Equation9 G) : Equation2036 G := by
  have eq4380 (x : G) : x ◇ (x ◇ x) = (x ◇ x) ◇ x := by
    apply Run2.Equation9_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation4470 at h
    apply Apply.Equation4470_implies_Equation4380 at h
    apply h
  have eq3 (x : G) : x = x ◇ x := by
    apply Run2.Equation9_implies_Equation3 at h
    apply h
  have eq1833 (x y : G) : x = (x ◇ (x ◇ x)) ◇ (x ◇ y) := by
    apply RewriteHypothesis.Equation9_implies_Equation1839 at h
    apply Apply.Equation1839_implies_Equation1833 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation9_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation8 at h
    apply h
  have eq4268 (x y : G) : x ◇ (x ◇ x) = x ◇ (x ◇ y) := by
    apply Run1.Equation9_implies_Equation308 at h
    apply RewriteHypothesis.Equation308_implies_Equation4282 at h
    apply Apply.Equation4282_implies_Equation4268 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq4380]
  symm
  nth_rewrite 1 [eq3 x]
  symm
  nth_rewrite 1 [← eq1833]
  nth_rewrite 1 [eq8 x]
  nth_rewrite 1 [eq4268]
  symm
  nth_rewrite 1 [← eq3]
  apply h
  repeat assumption
@[equational_result]
theorem Equation9_implies_Equation3660 (G: Type _) [Magma G] (h: Equation9 G) : Equation3660 G := by
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply Run1.Equation9_implies_Equation308 at h
    apply Apply.Equation308_implies_Equation307 at h
    apply h
  have eq1833 (x y : G) : x = (x ◇ (x ◇ x)) ◇ (x ◇ y) := by
    apply RewriteHypothesis.Equation9_implies_Equation1839 at h
    apply Apply.Equation1839_implies_Equation1833 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation9_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation8 at h
    apply h
  have eq4268 (x y : G) : x ◇ (x ◇ x) = x ◇ (x ◇ y) := by
    apply Run1.Equation9_implies_Equation308 at h
    apply RewriteHypothesis.Equation308_implies_Equation4282 at h
    apply Apply.Equation4282_implies_Equation4268 at h
    apply h
  have eq3 (x : G) : x = x ◇ x := by
    apply Run2.Equation9_implies_Equation3 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [eq307]
  nth_rewrite 1 [← eq1833]
  nth_rewrite 1 [eq8 x]
  nth_rewrite 1 [eq4268]
  symm
  nth_rewrite 1 [← eq3]
  apply h
  repeat assumption
@[equational_result]
theorem Equation28_implies_Equation1478 (G: Type _) [Magma G] (h: Equation28 G) : Equation1478 G := by
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run1.Equation28_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation8 at h
    apply h
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply Run1.Equation28_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply h
  have eq3674 (x y : G) : x ◇ x = (y ◇ x) ◇ (x ◇ x) := by
    apply Run2.Equation28_implies_Equation3674 at h
    apply h
  have eq364 (x y : G) : x ◇ x = (y ◇ x) ◇ x := by
    apply Run1.Equation28_implies_Equation364 at h
    apply h
  intro x y
  nth_rewrite 1 [eq8 x]
  symm
  nth_rewrite 1 [← eq307]
  nth_rewrite 1 [← eq3674]
  nth_rewrite 1 [eq364]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation48_implies_Equation3254 (G: Type _) [Magma G] (h: Equation48 G) : Equation3254 G := by
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation48_implies_Equation47 at h
    apply h
  have eq411 (x : G) : x = x ◇ (x ◇ (x ◇ (x ◇ x))) := by
    apply Apply.Equation48_implies_Equation415 at h
    apply Apply.Equation415_implies_Equation412 at h
    apply Apply.Equation412_implies_Equation411 at h
    apply h
  intro x y
  nth_rewrite 2 [eq47 x]
  nth_rewrite 1 [← eq411]
  apply h
@[equational_result]
theorem Equation51_implies_Equation3257 (G: Type _) [Magma G] (h: Equation51 G) : Equation3257 G := by
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation51_implies_Equation48 at h
    apply Apply.Equation48_implies_Equation47 at h
    apply h
  have eq411 (x : G) : x = x ◇ (x ◇ (x ◇ (x ◇ x))) := by
    apply Apply.Equation51_implies_Equation425 at h
    apply Apply.Equation425_implies_Equation415 at h
    apply Apply.Equation415_implies_Equation412 at h
    apply Apply.Equation412_implies_Equation411 at h
    apply h
  intro x y z
  nth_rewrite 2 [eq47 x]
  nth_rewrite 1 [← eq411]
  apply h
@[equational_result]
theorem Equation54_implies_Equation3260 (G: Type _) [Magma G] (h: Equation54 G) : Equation3260 G := by
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation54_implies_Equation48 at h
    apply Apply.Equation48_implies_Equation47 at h
    apply h
  have eq411 (x : G) : x = x ◇ (x ◇ (x ◇ (x ◇ x))) := by
    apply Apply.Equation54_implies_Equation435 at h
    apply Apply.Equation435_implies_Equation415 at h
    apply Apply.Equation415_implies_Equation412 at h
    apply Apply.Equation412_implies_Equation411 at h
    apply h
  intro x y z
  nth_rewrite 2 [eq47 x]
  nth_rewrite 1 [← eq411]
  apply h
@[equational_result]
theorem Equation67_implies_Equation3273 (G: Type _) [Magma G] (h: Equation67 G) : Equation3273 G := by
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation67_implies_Equation48 at h
    apply Apply.Equation48_implies_Equation47 at h
    apply h
  have eq411 (x : G) : x = x ◇ (x ◇ (x ◇ (x ◇ x))) := by
    apply Apply.Equation67_implies_Equation48 at h
    apply Apply.Equation48_implies_Equation415 at h
    apply Apply.Equation415_implies_Equation412 at h
    apply Apply.Equation412_implies_Equation411 at h
    apply h
  intro x y z
  nth_rewrite 2 [eq47 x]
  nth_rewrite 1 [← eq411]
  apply h
@[equational_result]
theorem Equation74_implies_Equation3280 (G: Type _) [Magma G] (h: Equation74 G) : Equation3280 G := by
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation74_implies_Equation48 at h
    apply Apply.Equation48_implies_Equation47 at h
    apply h
  have eq411 (x : G) : x = x ◇ (x ◇ (x ◇ (x ◇ x))) := by
    apply Apply.Equation74_implies_Equation48 at h
    apply Apply.Equation48_implies_Equation415 at h
    apply Apply.Equation415_implies_Equation412 at h
    apply Apply.Equation412_implies_Equation411 at h
    apply h
  intro x y z
  nth_rewrite 2 [eq47 x]
  nth_rewrite 1 [← eq411]
  apply h
@[equational_result]
theorem Equation270_implies_Equation4080 (G: Type _) [Magma G] (h: Equation270 G) : Equation4080 G := by
  have eq255 (x : G) : x = ((x ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation270_implies_Equation255 at h
    apply h
  have eq3050 (x : G) : x = (((x ◇ x) ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation270_implies_Equation3176 at h
    apply Apply.Equation3176_implies_Equation3065 at h
    apply Apply.Equation3065_implies_Equation3050 at h
    apply h
  intro x y
  nth_rewrite 1 [eq255 x]
  nth_rewrite 1 [← eq3050]
  apply h
@[equational_result]
theorem Equation292_implies_Equation4102 (G: Type _) [Magma G] (h: Equation292 G) : Equation4102 G := by
  have eq255 (x : G) : x = ((x ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation292_implies_Equation261 at h
    apply Apply.Equation261_implies_Equation255 at h
    apply h
  have eq3050 (x : G) : x = (((x ◇ x) ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation292_implies_Equation270 at h
    apply Apply.Equation270_implies_Equation3176 at h
    apply Apply.Equation3176_implies_Equation3065 at h
    apply Apply.Equation3065_implies_Equation3050 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq255 x]
  nth_rewrite 1 [← eq3050]
  apply h
@[equational_result]
theorem Equation298_implies_Equation4258 (G: Type _) [Magma G] (h: Equation298 G) : Equation4258 G := by
  have eq255 (x : G) : x = ((x ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation298_implies_Equation263 at h
    apply Apply.Equation263_implies_Equation255 at h
    apply h
  have eq3152 (x y : G) : x = (((y ◇ y) ◇ y) ◇ y) ◇ x := by
    apply Apply.Equation298_implies_Equation3242 at h
    apply Apply.Equation3242_implies_Equation3167 at h
    apply Apply.Equation3167_implies_Equation3152 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq255 x]
  nth_rewrite 1 [← eq3152]
  apply h
@[equational_result]
theorem Equation57_implies_Equation3336 (G: Type _) [Magma G] (h: Equation57 G) : Equation3336 G := by
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation57_implies_Equation48 at h
    apply Apply.Equation48_implies_Equation47 at h
    apply h
  have eq440 (x y : G) : x = x ◇ (y ◇ (y ◇ (y ◇ y))) := by
    apply Apply.Equation57_implies_Equation445 at h
    apply Apply.Equation445_implies_Equation441 at h
    apply Apply.Equation441_implies_Equation440 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq47 y]
  nth_rewrite 1 [← eq440]
  apply h
@[equational_result]
theorem Equation64_implies_Equation3403 (G: Type _) [Magma G] (h: Equation64 G) : Equation3403 G := by
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation64_implies_Equation48 at h
    apply Apply.Equation48_implies_Equation47 at h
    apply h
  have eq463 (x y : G) : x = y ◇ (x ◇ (x ◇ (x ◇ x))) := by
    apply Apply.Equation64_implies_Equation472 at h
    apply Apply.Equation472_implies_Equation465 at h
    apply Apply.Equation465_implies_Equation463 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq47 y]
  nth_rewrite 1 [← eq463]
  apply h
@[equational_result]
theorem Equation1791_implies_Equation98 (G: Type _) [Magma G] (h: Equation1791 G) : Equation98 G := by
  have eq3324 (x y z w : G) : x ◇ y = x ◇ (y ◇ (z ◇ w)) := by
    apply RewriteHypothesisAndGoal.Equation1791_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4186 at h
    apply Apply.Equation4186_implies_Equation4178 at h
    apply NthRewrites.Equation4178_implies_Equation327 at h
    apply Apply.Equation327_implies_Equation3324 at h
    apply h
  have eq3750 (x y z : G) : x ◇ y = (y ◇ x) ◇ (x ◇ z) := by
    apply RewriteHypothesisAndGoal.Equation1791_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3757 at h
    apply Apply.Equation3757_implies_Equation3750 at h
    apply h
  have eq377 (x y : G) : x ◇ y = (x ◇ y) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation1791_implies_Equation41 at h
    apply RewriteGoal.Equation41_implies_Equation3746 at h
    apply Apply.Equation3746_implies_Equation3741 at h
    apply RewriteCombinations.Equation3741_implies_Equation3950 at h
    apply Apply.Equation3950_implies_Equation3941 at h
    apply RewriteHypothesisAndGoal.Equation3941_implies_Equation3916 at h
    apply Apply.Equation3916_implies_Equation3914 at h
    apply RewriteCombinations.Equation3914_implies_Equation374 at h
    apply RewriteCombinations.Equation374_implies_Equation380 at h
    apply RewriteCombinations.Equation380_implies_Equation383 at h
    apply Apply.Equation383_implies_Equation379 at h
    apply Apply.Equation379_implies_Equation377 at h
    apply h
  intro x y z w u
  symm
  nth_rewrite 1 [← eq3324]
  nth_rewrite 1 [eq3750]
  nth_rewrite 3 [eq377]
  symm
  apply h
@[equational_result]
theorem Equation3344_implies_Equation3320 (G: Type _) [Magma G] (h: Equation3344 G) : Equation3320 G := by
  have eq43 (x y : G) : x ◇ y = y ◇ x := by
    apply RewriteHypothesisAndGoal.Equation3344_implies_Equation332 at h
    apply Run2.Equation332_implies_Equation387 at h
    apply Subgraph.Equation387_implies_Equation43 at h
    apply h
  intro x y z
  nth_rewrite 1 [h]
  nth_rewrite 1 [← h]
  nth_rewrite 1 [← eq43]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3356_implies_Equation3300 (G: Type _) [Magma G] (h: Equation3356 G) : Equation3300 G := by
  have eq3338 (x y z w : G) : x ◇ y = x ◇ (z ◇ (w ◇ y)) := by
    apply NthRewrites.Equation3356_implies_Equation3367 at h
    apply RewriteCombinations.Equation3367_implies_Equation3330 at h
    apply NthRewrites.Equation3330_implies_Equation3312 at h
    apply NthRewrites.Equation3312_implies_Equation3338 at h
    apply h
  have eq39 (x y : G) : x ◇ x = y ◇ x := by
    apply RewriteHypothesisAndGoal.Equation3356_implies_Equation45 at h
    apply Subgraph.Equation45_implies_Equation39 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq3338]
  nth_rewrite 1 [h]
  symm
  nth_rewrite 1 [eq39]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3715_implies_Equation4470 (G: Type _) [Magma G] (h: Equation3715 G) : Equation4470 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply NthRewrites.Equation3715_implies_Equation375 at h
    apply h
  have eq326 (x y : G) : x ◇ y = x ◇ (y ◇ y) := by
    apply NthRewrites.Equation3715_implies_Equation326 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq375]
  nth_rewrite 1 [h]
  symm
  nth_rewrite 1 [← eq326]
  apply h
@[equational_result]
theorem Equation3744_implies_Equation4476 (G: Type _) [Magma G] (h: Equation3744 G) : Equation4476 G := by
  have eq381 (x y z : G) : x ◇ y = (x ◇ z) ◇ y := by
    apply Subgraph.Equation3744_implies_Equation381 at h
    apply h
  have eq326 (x y : G) : x ◇ y = x ◇ (y ◇ y) := by
    apply Apply.Equation3744_implies_Equation3718 at h
    apply Apply.Equation3718_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation326 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq381]
  nth_rewrite 1 [h]
  symm
  nth_rewrite 1 [← eq326]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3758_implies_Equation4470 (G: Type _) [Magma G] (h: Equation3758 G) : Equation4470 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply NthRewrites.Equation3758_implies_Equation375 at h
    apply h
  have eq326 (x y : G) : x ◇ y = x ◇ (y ◇ y) := by
    apply NthRewrites.Equation3758_implies_Equation326 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq375]
  nth_rewrite 1 [h]
  symm
  nth_rewrite 1 [← eq326]
  apply h
@[equational_result]
theorem Equation3634_implies_Equation4396 (G: Type _) [Magma G] (h: Equation3634 G) : Equation4396 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply Apply.Equation3634_implies_Equation3566 at h
    apply NthRewrites.Equation3566_implies_Equation4243 at h
    apply Apply.Equation4243_implies_Equation4192 at h
    apply RewriteHypothesisAndGoal.Equation4192_implies_Equation375 at h
    apply h
  have eq3509 (x y : G) : x ◇ y = x ◇ ((x ◇ x) ◇ y) := by
    apply Apply.Equation3634_implies_Equation3529 at h
    apply Apply.Equation3529_implies_Equation3509 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq375]
  nth_rewrite 1 [h]
  symm
  nth_rewrite 2 [eq375]
  nth_rewrite 1 [← eq3509]
  apply h
  repeat assumption
@[equational_result]
theorem Equation48_implies_Equation3 (G: Type _) [Magma G] (h: Equation48 G) : Equation3 G := by
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation48_implies_Equation47 at h
    apply h
  have eq411 (x : G) : x = x ◇ (x ◇ (x ◇ (x ◇ x))) := by
    apply Apply.Equation48_implies_Equation415 at h
    apply Apply.Equation415_implies_Equation412 at h
    apply Apply.Equation412_implies_Equation411 at h
    apply h
  intro x
  symm
  nth_rewrite 2 [eq47 x]
  symm
  nth_rewrite 1 [eq47 x]
  symm
  nth_rewrite 1 [← eq411 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation64_implies_Equation5 (G: Type _) [Magma G] (h: Equation64 G) : Equation5 G := by
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation64_implies_Equation48 at h
    apply Apply.Equation48_implies_Equation47 at h
    apply h
  have eq463 (x y : G) : x = y ◇ (x ◇ (x ◇ (x ◇ x))) := by
    apply Apply.Equation64_implies_Equation472 at h
    apply Apply.Equation472_implies_Equation465 at h
    apply Apply.Equation465_implies_Equation463 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [eq47 x]
  symm
  nth_rewrite 1 [eq47 x]
  symm
  nth_rewrite 1 [← eq463]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation270_implies_Equation3 (G: Type _) [Magma G] (h: Equation270 G) : Equation3 G := by
  have eq255 (x : G) : x = ((x ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation270_implies_Equation255 at h
    apply h
  have eq3050 (x : G) : x = (((x ◇ x) ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation270_implies_Equation3176 at h
    apply Apply.Equation3176_implies_Equation3065 at h
    apply Apply.Equation3065_implies_Equation3050 at h
    apply h
  intro x
  symm
  nth_rewrite 1 [eq255 x]
  symm
  nth_rewrite 1 [eq255 x]
  symm
  nth_rewrite 1 [← eq3050]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq255]
  apply h
  repeat assumption
@[equational_result]
theorem Equation272_implies_Equation4 (G: Type _) [Magma G] (h: Equation272 G) : Equation4 G := by
  have eq255 (x : G) : x = ((x ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation272_implies_Equation256 at h
    apply Apply.Equation256_implies_Equation255 at h
    apply h
  have eq3051 (x y : G) : x = (((x ◇ x) ◇ x) ◇ x) ◇ y := by
    apply Apply.Equation272_implies_Equation3179 at h
    apply Apply.Equation3179_implies_Equation3067 at h
    apply Apply.Equation3067_implies_Equation3051 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [eq255 x]
  symm
  nth_rewrite 1 [eq255 x]
  symm
  nth_rewrite 1 [← eq3051]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq255]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1134 (G: Type _) [Magma G] (h: Equation953 G) : Equation1134 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1025 (x y : G) : x = x ◇ ((x ◇ (y ◇ x)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation110 at h
    apply Apply.Equation110_implies_Equation101 at h
    apply Apply.Equation101_implies_Equation1031 at h
    apply Apply.Equation1031_implies_Equation1025 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1025]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1138 (G: Type _) [Magma G] (h: Equation953 G) : Equation1138 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1028 (x y : G) : x = x ◇ ((x ◇ (y ◇ y)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation110 at h
    apply Apply.Equation110_implies_Equation101 at h
    apply Apply.Equation101_implies_Equation1031 at h
    apply Apply.Equation1031_implies_Equation1028 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1028]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1168 (G: Type _) [Magma G] (h: Equation953 G) : Equation1168 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1035 (x y : G) : x = x ◇ ((y ◇ (x ◇ x)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation110 at h
    apply Apply.Equation110_implies_Equation1067 at h
    apply Apply.Equation1067_implies_Equation1041 at h
    apply Apply.Equation1041_implies_Equation1035 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1035]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1172 (G: Type _) [Magma G] (h: Equation953 G) : Equation1172 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1038 (x y : G) : x = x ◇ ((y ◇ (x ◇ y)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation110 at h
    apply Apply.Equation110_implies_Equation1067 at h
    apply Apply.Equation1067_implies_Equation1041 at h
    apply Apply.Equation1041_implies_Equation1038 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1038]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1176 (G: Type _) [Magma G] (h: Equation953 G) : Equation1176 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1041 (x y z : G) : x = x ◇ ((y ◇ (x ◇ z)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation110 at h
    apply Apply.Equation110_implies_Equation1067 at h
    apply Apply.Equation1067_implies_Equation1041 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1041]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1185 (G: Type _) [Magma G] (h: Equation953 G) : Equation1185 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1045 (x y : G) : x = x ◇ ((y ◇ (y ◇ x)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation16 at h
    apply RewriteHypothesis.Equation16_implies_Equation1184 at h
    apply Apply.Equation1184_implies_Equation1045 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1045]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1189 (G: Type _) [Magma G] (h: Equation953 G) : Equation1189 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1048 (x y : G) : x = x ◇ ((y ◇ (y ◇ y)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation110 at h
    apply Apply.Equation110_implies_Equation1067 at h
    apply Apply.Equation1067_implies_Equation1051 at h
    apply Apply.Equation1051_implies_Equation1048 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1048]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1193 (G: Type _) [Magma G] (h: Equation953 G) : Equation1193 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1051 (x y z : G) : x = x ◇ ((y ◇ (y ◇ z)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation110 at h
    apply Apply.Equation110_implies_Equation1067 at h
    apply Apply.Equation1067_implies_Equation1051 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1051]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1203 (G: Type _) [Magma G] (h: Equation953 G) : Equation1203 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1055 (x y z : G) : x = x ◇ ((y ◇ (z ◇ x)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation110 at h
    apply Apply.Equation110_implies_Equation1067 at h
    apply Apply.Equation1067_implies_Equation1055 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1055]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1208 (G: Type _) [Magma G] (h: Equation953 G) : Equation1208 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1059 (x y z : G) : x = x ◇ ((y ◇ (z ◇ y)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation110 at h
    apply Apply.Equation110_implies_Equation1067 at h
    apply Apply.Equation1067_implies_Equation1059 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1059]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1213 (G: Type _) [Magma G] (h: Equation953 G) : Equation1213 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1063 (x y z : G) : x = x ◇ ((y ◇ (z ◇ z)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation110 at h
    apply Apply.Equation110_implies_Equation1067 at h
    apply Apply.Equation1067_implies_Equation1063 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1063]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1190 (G: Type _) [Magma G] (h: Equation953 G) : Equation1190 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1072 (x y : G) : x = y ◇ ((x ◇ (x ◇ x)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation146 at h
    apply Apply.Equation146_implies_Equation120 at h
    apply Apply.Equation120_implies_Equation1104 at h
    apply Apply.Equation1104_implies_Equation1078 at h
    apply Apply.Equation1078_implies_Equation1072 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1072]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1186 (G: Type _) [Magma G] (h: Equation953 G) : Equation1186 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1075 (x y : G) : x = y ◇ ((x ◇ (x ◇ y)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation16 at h
    apply RewriteHypothesis.Equation16_implies_Equation1184 at h
    apply Apply.Equation1184_implies_Equation1075 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1075]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1194 (G: Type _) [Magma G] (h: Equation953 G) : Equation1194 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1078 (x y z : G) : x = y ◇ ((x ◇ (x ◇ z)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation146 at h
    apply Apply.Equation146_implies_Equation120 at h
    apply Apply.Equation120_implies_Equation1104 at h
    apply Apply.Equation1104_implies_Equation1078 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1078]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1173 (G: Type _) [Magma G] (h: Equation953 G) : Equation1173 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1082 (x y : G) : x = y ◇ ((x ◇ (y ◇ x)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation146 at h
    apply Apply.Equation146_implies_Equation120 at h
    apply Apply.Equation120_implies_Equation1104 at h
    apply Apply.Equation1104_implies_Equation1088 at h
    apply Apply.Equation1088_implies_Equation1082 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1082]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1169 (G: Type _) [Magma G] (h: Equation953 G) : Equation1169 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1085 (x y : G) : x = y ◇ ((x ◇ (y ◇ y)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation146 at h
    apply Apply.Equation146_implies_Equation120 at h
    apply Apply.Equation120_implies_Equation1104 at h
    apply Apply.Equation1104_implies_Equation1088 at h
    apply Apply.Equation1088_implies_Equation1085 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1085]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1177 (G: Type _) [Magma G] (h: Equation953 G) : Equation1177 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1088 (x y z : G) : x = y ◇ ((x ◇ (y ◇ z)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation146 at h
    apply Apply.Equation146_implies_Equation120 at h
    apply Apply.Equation120_implies_Equation1104 at h
    apply Apply.Equation1104_implies_Equation1088 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1088]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1209 (G: Type _) [Magma G] (h: Equation953 G) : Equation1209 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1092 (x y z : G) : x = y ◇ ((x ◇ (z ◇ x)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation146 at h
    apply Apply.Equation146_implies_Equation120 at h
    apply Apply.Equation120_implies_Equation1104 at h
    apply Apply.Equation1104_implies_Equation1092 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1092]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1204 (G: Type _) [Magma G] (h: Equation953 G) : Equation1204 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1096 (x y z : G) : x = y ◇ ((x ◇ (z ◇ y)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation146 at h
    apply Apply.Equation146_implies_Equation120 at h
    apply Apply.Equation120_implies_Equation1104 at h
    apply Apply.Equation1104_implies_Equation1096 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1096]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1214 (G: Type _) [Magma G] (h: Equation953 G) : Equation1214 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1100 (x y z : G) : x = y ◇ ((x ◇ (z ◇ z)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation146 at h
    apply Apply.Equation146_implies_Equation120 at h
    apply Apply.Equation120_implies_Equation1104 at h
    apply Apply.Equation1104_implies_Equation1100 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1100]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1139 (G: Type _) [Magma G] (h: Equation953 G) : Equation1139 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1109 (x y : G) : x = y ◇ ((y ◇ (x ◇ x)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation146 at h
    apply Apply.Equation146_implies_Equation1217 at h
    apply Apply.Equation1217_implies_Equation1141 at h
    apply Apply.Equation1141_implies_Equation1115 at h
    apply Apply.Equation1115_implies_Equation1109 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1109]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1135 (G: Type _) [Magma G] (h: Equation953 G) : Equation1135 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1112 (x y : G) : x = y ◇ ((y ◇ (x ◇ y)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation146 at h
    apply Apply.Equation146_implies_Equation1217 at h
    apply Apply.Equation1217_implies_Equation1141 at h
    apply Apply.Equation1141_implies_Equation1115 at h
    apply Apply.Equation1115_implies_Equation1112 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1112]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1215 (G: Type _) [Magma G] (h: Equation953 G) : Equation1215 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1146 (x y z : G) : x = y ◇ ((z ◇ (x ◇ x)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation146 at h
    apply Apply.Equation146_implies_Equation1217 at h
    apply Apply.Equation1217_implies_Equation1158 at h
    apply Apply.Equation1158_implies_Equation1146 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1146]
  nth_rewrite 1 [h w]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1205 (G: Type _) [Magma G] (h: Equation953 G) : Equation1205 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1150 (x y z : G) : x = y ◇ ((z ◇ (x ◇ y)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation146 at h
    apply Apply.Equation146_implies_Equation1217 at h
    apply Apply.Equation1217_implies_Equation1158 at h
    apply Apply.Equation1158_implies_Equation1150 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1150]
  nth_rewrite 1 [h w]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1210 (G: Type _) [Magma G] (h: Equation953 G) : Equation1210 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1154 (x y z : G) : x = y ◇ ((z ◇ (x ◇ z)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation146 at h
    apply Apply.Equation146_implies_Equation1217 at h
    apply Apply.Equation1217_implies_Equation1158 at h
    apply Apply.Equation1158_implies_Equation1154 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1154]
  nth_rewrite 1 [h w]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1178 (G: Type _) [Magma G] (h: Equation953 G) : Equation1178 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1163 (x y z : G) : x = y ◇ ((z ◇ (y ◇ x)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation146 at h
    apply Apply.Equation146_implies_Equation1217 at h
    apply Apply.Equation1217_implies_Equation1175 at h
    apply Apply.Equation1175_implies_Equation1163 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1163]
  nth_rewrite 1 [h w]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1170 (G: Type _) [Magma G] (h: Equation953 G) : Equation1170 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1167 (x y z : G) : x = y ◇ ((z ◇ (y ◇ y)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation146 at h
    apply Apply.Equation146_implies_Equation1217 at h
    apply Apply.Equation1217_implies_Equation1175 at h
    apply Apply.Equation1175_implies_Equation1167 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1167]
  nth_rewrite 1 [h w]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1174 (G: Type _) [Magma G] (h: Equation953 G) : Equation1174 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1171 (x y z : G) : x = y ◇ ((z ◇ (y ◇ z)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation146 at h
    apply Apply.Equation146_implies_Equation1217 at h
    apply Apply.Equation1217_implies_Equation1175 at h
    apply Apply.Equation1175_implies_Equation1171 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1171]
  nth_rewrite 1 [h w]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1195 (G: Type _) [Magma G] (h: Equation953 G) : Equation1195 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1180 (x y z : G) : x = y ◇ ((z ◇ (z ◇ x)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation146 at h
    apply Apply.Equation146_implies_Equation1217 at h
    apply Apply.Equation1217_implies_Equation1192 at h
    apply Apply.Equation1192_implies_Equation1180 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1180]
  nth_rewrite 1 [h w]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1187 (G: Type _) [Magma G] (h: Equation953 G) : Equation1187 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1184 (x y z : G) : x = y ◇ ((z ◇ (z ◇ y)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation16 at h
    apply RewriteHypothesis.Equation16_implies_Equation1184 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1184]
  nth_rewrite 1 [h w]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation1191 (G: Type _) [Magma G] (h: Equation953 G) : Equation1191 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq1188 (x y z : G) : x = y ◇ ((z ◇ (z ◇ z)) ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation146 at h
    apply Apply.Equation146_implies_Equation1217 at h
    apply Apply.Equation1217_implies_Equation1192 at h
    apply Apply.Equation1192_implies_Equation1188 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq1188]
  nth_rewrite 1 [h w]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation954_implies_Equation988 (G: Type _) [Magma G] (h: Equation954 G) : Equation988 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Apply.Equation954_implies_Equation953 at h
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply Apply.Equation954_implies_Equation953 at h
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq871 (x y z : G) : x = y ◇ ((x ◇ x) ◇ (x ◇ z)) := by
    apply Apply.Equation954_implies_Equation871 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Apply.Equation954_implies_Equation953 at h
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq871]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation957_implies_Equation991 (G: Type _) [Magma G] (h: Equation957 G) : Equation991 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Apply.Equation957_implies_Equation953 at h
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply Apply.Equation957_implies_Equation953 at h
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq875 (x y z : G) : x = y ◇ ((x ◇ x) ◇ (z ◇ x)) := by
    apply Apply.Equation957_implies_Equation875 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Apply.Equation957_implies_Equation953 at h
    apply Run2.Equation953_implies_Equation19 at h
    apply Apply.Equation19_implies_Equation10 at h
    apply Apply.Equation10_implies_Equation8 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq10 x]
  nth_rewrite 1 [← eq4273]
  symm
  nth_rewrite 1 [← eq875]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3358_implies_Equation4118 (G: Type _) [Magma G] (h: Equation3358 G) : Equation4118 G := by
  have eq4380 (x : G) : x ◇ (x ◇ x) = (x ◇ x) ◇ x := by
    apply Apply.Equation3358_implies_Equation3355 at h
    apply NthRewrites.Equation3355_implies_Equation4435 at h
    apply Apply.Equation4435_implies_Equation4380 at h
    apply h
  have eq3352 (x y : G) : x ◇ y = y ◇ (y ◇ (x ◇ x)) := by
    apply Apply.Equation3358_implies_Equation3352 at h
    apply h
  have eq3915 (x y : G) : x ◇ y = (x ◇ (x ◇ x)) ◇ y := by
    apply NthRewrites.Equation3358_implies_Equation3947 at h
    apply Apply.Equation3947_implies_Equation3921 at h
    apply Apply.Equation3921_implies_Equation3915 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq4380]
  symm
  nth_rewrite 1 [eq3352]
  symm
  nth_rewrite 1 [← eq3915]
  nth_rewrite 1 [h]
  symm
  nth_rewrite 1 [← eq3352]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3358_implies_Equation4128 (G: Type _) [Magma G] (h: Equation3358 G) : Equation4128 G := by
  have eq4435 (x y : G) : x ◇ (y ◇ x) = (x ◇ y) ◇ x := by
    apply Apply.Equation3358_implies_Equation3355 at h
    apply NthRewrites.Equation3355_implies_Equation4435 at h
    apply h
  have eq3352 (x y : G) : x ◇ y = y ◇ (y ◇ (x ◇ x)) := by
    apply Apply.Equation3358_implies_Equation3352 at h
    apply h
  have eq3925 (x y : G) : x ◇ y = (x ◇ (y ◇ x)) ◇ y := by
    apply NthRewrites.Equation3358_implies_Equation3947 at h
    apply Apply.Equation3947_implies_Equation3931 at h
    apply Apply.Equation3931_implies_Equation3925 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq4435]
  symm
  nth_rewrite 1 [eq3352]
  symm
  nth_rewrite 1 [← eq3925]
  nth_rewrite 1 [h]
  symm
  nth_rewrite 1 [← eq3352]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3404_implies_Equation4118 (G: Type _) [Magma G] (h: Equation3404 G) : Equation4118 G := by
  have eq4380 (x : G) : x ◇ (x ◇ x) = (x ◇ x) ◇ x := by
    apply Apply.Equation3404_implies_Equation3355 at h
    apply NthRewrites.Equation3355_implies_Equation4435 at h
    apply Apply.Equation4435_implies_Equation4380 at h
    apply h
  have eq3315 (x y : G) : x ◇ y = x ◇ (y ◇ (x ◇ x)) := by
    apply Apply.Equation3404_implies_Equation3315 at h
    apply h
  have eq3915 (x y : G) : x ◇ y = (x ◇ (x ◇ x)) ◇ y := by
    apply NthRewrites.Equation3404_implies_Equation3943 at h
    apply Apply.Equation3943_implies_Equation3915 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq4380]
  symm
  nth_rewrite 1 [eq3315]
  symm
  nth_rewrite 1 [← eq3915]
  nth_rewrite 1 [h]
  symm
  nth_rewrite 1 [← eq3315]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3566_implies_Equation333 (G: Type _) [Magma G] (h: Equation3566 G) : Equation333 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply NthRewrites.Equation3566_implies_Equation4243 at h
    apply Apply.Equation4243_implies_Equation4192 at h
    apply RewriteHypothesisAndGoal.Equation4192_implies_Equation375 at h
    apply h
  have eq3546 (x y : G) : x ◇ y = y ◇ ((x ◇ x) ◇ y) := by
    apply Apply.Equation3566_implies_Equation3546 at h
    apply h
  intro x y
  symm
  nth_rewrite 2 [eq375]
  symm
  nth_rewrite 1 [eq375]
  symm
  nth_rewrite 1 [← eq3546]
  nth_rewrite 1 [h]
  symm
  nth_rewrite 1 [← eq375]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3634_implies_Equation343 (G: Type _) [Magma G] (h: Equation3634 G) : Equation343 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply Apply.Equation3634_implies_Equation3566 at h
    apply NthRewrites.Equation3566_implies_Equation4243 at h
    apply Apply.Equation4243_implies_Equation4192 at h
    apply RewriteHypothesisAndGoal.Equation4192_implies_Equation375 at h
    apply h
  have eq3583 (x y z : G) : x ◇ y = z ◇ ((x ◇ x) ◇ y) := by
    apply Apply.Equation3634_implies_Equation3583 at h
    apply h
  intro x y z
  symm
  nth_rewrite 2 [eq375]
  symm
  nth_rewrite 1 [eq375]
  symm
  nth_rewrite 1 [← eq3583]
  nth_rewrite 1 [h]
  symm
  nth_rewrite 1 [← eq375]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4013_implies_Equation3306 (G: Type _) [Magma G] (h: Equation4013 G) : Equation3306 G := by
  have eq4398 (x y : G) : x ◇ (x ◇ y) = (x ◇ y) ◇ x := by
    apply NthRewrites.Equation4013_implies_Equation4531 at h
    apply Apply.Equation4531_implies_Equation4398 at h
    apply h
  have eq3308 (x y : G) : x ◇ y = x ◇ (x ◇ (y ◇ x)) := by
    apply NthRewrites.Equation4013_implies_Equation3331 at h
    apply Apply.Equation3331_implies_Equation3308 at h
    apply h
  have eq3511 (x y : G) : x ◇ y = x ◇ ((x ◇ y) ◇ x) := by
    apply NthRewrites.Equation4013_implies_Equation3331 at h
    apply NthRewrites.Equation3331_implies_Equation3534 at h
    apply Apply.Equation3534_implies_Equation3511 at h
    apply h
  intro x y
  symm
  nth_rewrite 2 [eq4398]
  symm
  nth_rewrite 1 [eq3308]
  symm
  nth_rewrite 1 [← eq3511]
  nth_rewrite 1 [h]
  symm
  nth_rewrite 1 [← eq3308]
  apply h
  repeat assumption
@[equational_result]
theorem Equation9_implies_Equation1630 (G: Type _) [Magma G] (h: Equation9 G) : Equation1630 G := by
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run2.Equation9_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation8 at h
    apply h
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply Run2.Equation9_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation375 at h
    apply h
  have eq3 (x : G) : x = x ◇ x := by
    apply Run2.Equation9_implies_Equation3 at h
    apply h
  have eq1833 (x y : G) : x = (x ◇ (x ◇ x)) ◇ (x ◇ y) := by
    apply RewriteHypothesis.Equation9_implies_Equation1839 at h
    apply Apply.Equation1839_implies_Equation1833 at h
    apply h
  intro x y
  nth_rewrite 2 [eq8 x]
  symm
  nth_rewrite 1 [← eq375]
  nth_rewrite 4 [eq3 x]
  nth_rewrite 1 [← eq1833]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq8]
  apply h
@[equational_result]
theorem Equation71_implies_Equation6 (G: Type _) [Magma G] (h: Equation71 G) : Equation6 G := by
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation71_implies_Equation51 at h
    apply Apply.Equation51_implies_Equation48 at h
    apply Apply.Equation48_implies_Equation47 at h
    apply h
  have eq40 (x y : G) : x ◇ x = y ◇ y := by
    apply Apply.Equation71_implies_Equation1568 at h
    apply Apply.Equation1568_implies_Equation1565 at h
    apply RewriteHypothesisAndGoal.Equation1565_implies_Equation40 at h
    apply h
  have eq411 (x : G) : x = x ◇ (x ◇ (x ◇ (x ◇ x))) := by
    apply Apply.Equation71_implies_Equation499 at h
    apply Apply.Equation499_implies_Equation425 at h
    apply Apply.Equation425_implies_Equation415 at h
    apply Apply.Equation415_implies_Equation412 at h
    apply Apply.Equation412_implies_Equation411 at h
    apply h
  intro x y
  nth_rewrite 1 [eq47 x]
  symm
  nth_rewrite 1 [← eq40]
  nth_rewrite 4 [eq47 x]
  nth_rewrite 1 [← eq411]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation272_implies_Equation4193 (G: Type _) [Magma G] (h: Equation272 G) : Equation4193 G := by
  have eq255 (x : G) : x = ((x ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation272_implies_Equation256 at h
    apply Apply.Equation256_implies_Equation255 at h
    apply h
  have eq3051 (x y : G) : x = (((x ◇ x) ◇ x) ◇ x) ◇ y := by
    apply Apply.Equation272_implies_Equation3179 at h
    apply Apply.Equation3179_implies_Equation3067 at h
    apply Apply.Equation3067_implies_Equation3051 at h
    apply h
  have eq271 (x y : G) : x = ((y ◇ x) ◇ x) ◇ y := by
    apply Apply.Equation272_implies_Equation271 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq255 x]
  nth_rewrite 1 [← eq3051]
  nth_rewrite 1 [eq255 x]
  symm
  nth_rewrite 1 [← eq271]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq255]
  apply h
  repeat assumption
@[equational_result]
theorem Equation276_implies_Equation4067 (G: Type _) [Magma G] (h: Equation276 G) : Equation4067 G := by
  have eq255 (x : G) : x = ((x ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation276_implies_Equation257 at h
    apply Apply.Equation257_implies_Equation255 at h
    apply h
  have eq3050 (x : G) : x = (((x ◇ x) ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation276_implies_Equation270 at h
    apply Apply.Equation270_implies_Equation3176 at h
    apply Apply.Equation3176_implies_Equation3065 at h
    apply Apply.Equation3065_implies_Equation3050 at h
    apply h
  have eq257 (x y : G) : x = ((x ◇ x) ◇ y) ◇ x := by
    apply Apply.Equation276_implies_Equation257 at h
    apply h
  intro x y
  nth_rewrite 1 [eq255 x]
  nth_rewrite 1 [← eq3050]
  nth_rewrite 1 [eq255 x]
  symm
  nth_rewrite 1 [← eq257]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq255]
  apply h
  repeat assumption
@[equational_result]
theorem Equation276_implies_Equation4083 (G: Type _) [Magma G] (h: Equation276 G) : Equation4083 G := by
  have eq255 (x : G) : x = ((x ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation276_implies_Equation257 at h
    apply Apply.Equation257_implies_Equation255 at h
    apply h
  have eq3050 (x : G) : x = (((x ◇ x) ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation276_implies_Equation270 at h
    apply Apply.Equation270_implies_Equation3176 at h
    apply Apply.Equation3176_implies_Equation3065 at h
    apply Apply.Equation3065_implies_Equation3050 at h
    apply h
  have eq273 (x y : G) : x = ((y ◇ x) ◇ y) ◇ x := by
    apply Apply.Equation276_implies_Equation273 at h
    apply h
  intro x y
  nth_rewrite 1 [eq255 x]
  nth_rewrite 1 [← eq3050]
  nth_rewrite 1 [eq255 x]
  symm
  nth_rewrite 1 [← eq273]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq255]
  apply h
  repeat assumption
@[equational_result]
theorem Equation290_implies_Equation4070 (G: Type _) [Magma G] (h: Equation290 G) : Equation4070 G := by
  have eq255 (x : G) : x = ((x ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation290_implies_Equation260 at h
    apply Apply.Equation260_implies_Equation255 at h
    apply h
  have eq3050 (x : G) : x = (((x ◇ x) ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation290_implies_Equation270 at h
    apply Apply.Equation270_implies_Equation3176 at h
    apply Apply.Equation3176_implies_Equation3065 at h
    apply Apply.Equation3065_implies_Equation3050 at h
    apply h
  have eq260 (x y : G) : x = ((x ◇ y) ◇ x) ◇ x := by
    apply Apply.Equation290_implies_Equation260 at h
    apply h
  intro x y
  nth_rewrite 1 [eq255 x]
  nth_rewrite 1 [← eq3050]
  nth_rewrite 1 [eq255 x]
  symm
  nth_rewrite 1 [← eq260]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq255]
  apply h
  repeat assumption
@[equational_result]
theorem Equation290_implies_Equation4090 (G: Type _) [Magma G] (h: Equation290 G) : Equation4090 G := by
  have eq255 (x : G) : x = ((x ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation290_implies_Equation260 at h
    apply Apply.Equation260_implies_Equation255 at h
    apply h
  have eq3050 (x : G) : x = (((x ◇ x) ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation290_implies_Equation270 at h
    apply Apply.Equation270_implies_Equation3176 at h
    apply Apply.Equation3176_implies_Equation3065 at h
    apply Apply.Equation3065_implies_Equation3050 at h
    apply h
  have eq280 (x y : G) : x = ((y ◇ y) ◇ x) ◇ x := by
    apply Apply.Equation290_implies_Equation280 at h
    apply h
  intro x y
  nth_rewrite 1 [eq255 x]
  nth_rewrite 1 [← eq3050]
  nth_rewrite 1 [eq255 x]
  symm
  nth_rewrite 1 [← eq280]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq255]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1529 (G: Type _) [Magma G] (h: Equation591 G) : Equation1529 G := by
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  have eq3282 (x y : G) : x ◇ x = y ◇ (y ◇ (y ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply Run1.Equation314_implies_Equation317 at h
    apply Apply.Equation317_implies_Equation3287 at h
    apply Apply.Equation3287_implies_Equation3283 at h
    apply Apply.Equation3283_implies_Equation3282 at h
    apply h
  have eq1426 (x : G) : x = (x ◇ x) ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1473 at h
    apply Apply.Equation1473_implies_Equation1437 at h
    apply Apply.Equation1437_implies_Equation1428 at h
    apply Apply.Equation1428_implies_Equation1426 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  intro x y
  nth_rewrite 1 [eq47 x]
  nth_rewrite 1 [← eq3282]
  symm
  nth_rewrite 1 [← eq1426]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1532 (G: Type _) [Magma G] (h: Equation591 G) : Equation1532 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq1428 (x y : G) : x = (x ◇ x) ◇ (x ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1473 at h
    apply Apply.Equation1473_implies_Equation1437 at h
    apply Apply.Equation1437_implies_Equation1428 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq1428]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1540 (G: Type _) [Magma G] (h: Equation591 G) : Equation1540 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq1431 (x y : G) : x = (x ◇ x) ◇ (y ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1473 at h
    apply Apply.Equation1473_implies_Equation1437 at h
    apply Apply.Equation1437_implies_Equation1431 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq1431]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1544 (G: Type _) [Magma G] (h: Equation591 G) : Equation1544 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq1434 (x y : G) : x = (x ◇ x) ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1473 at h
    apply Apply.Equation1473_implies_Equation1437 at h
    apply Apply.Equation1437_implies_Equation1434 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq1434]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1574 (G: Type _) [Magma G] (h: Equation591 G) : Equation1574 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq1441 (x y : G) : x = (x ◇ y) ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1473 at h
    apply Apply.Equation1473_implies_Equation1447 at h
    apply Apply.Equation1447_implies_Equation1441 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq1441]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1578 (G: Type _) [Magma G] (h: Equation591 G) : Equation1578 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq1444 (x y : G) : x = (x ◇ y) ◇ (x ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1473 at h
    apply Apply.Equation1473_implies_Equation1447 at h
    apply Apply.Equation1447_implies_Equation1444 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq1444]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1591 (G: Type _) [Magma G] (h: Equation591 G) : Equation1591 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq1451 (x y : G) : x = (x ◇ y) ◇ (y ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1473 at h
    apply Apply.Equation1473_implies_Equation1457 at h
    apply Apply.Equation1457_implies_Equation1451 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq1451]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1595 (G: Type _) [Magma G] (h: Equation591 G) : Equation1595 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq1454 (x y : G) : x = (x ◇ y) ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1473 at h
    apply Apply.Equation1473_implies_Equation1457 at h
    apply Apply.Equation1457_implies_Equation1454 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq1454]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1596 (G: Type _) [Magma G] (h: Equation591 G) : Equation1596 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq1478 (x y : G) : x = (y ◇ x) ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1510 at h
    apply Apply.Equation1510_implies_Equation1484 at h
    apply Apply.Equation1484_implies_Equation1478 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq1478]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1592 (G: Type _) [Magma G] (h: Equation591 G) : Equation1592 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq1481 (x y : G) : x = (y ◇ x) ◇ (x ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1510 at h
    apply Apply.Equation1510_implies_Equation1484 at h
    apply Apply.Equation1484_implies_Equation1481 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq1481]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1579 (G: Type _) [Magma G] (h: Equation591 G) : Equation1579 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq1488 (x y : G) : x = (y ◇ x) ◇ (y ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1510 at h
    apply Apply.Equation1510_implies_Equation1494 at h
    apply Apply.Equation1494_implies_Equation1488 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq1488]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1575 (G: Type _) [Magma G] (h: Equation591 G) : Equation1575 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq1491 (x y : G) : x = (y ◇ x) ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1510 at h
    apply Apply.Equation1510_implies_Equation1494 at h
    apply Apply.Equation1494_implies_Equation1491 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq1491]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1545 (G: Type _) [Magma G] (h: Equation591 G) : Equation1545 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq1515 (x y : G) : x = (y ◇ y) ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1547 at h
    apply Apply.Equation1547_implies_Equation1521 at h
    apply Apply.Equation1521_implies_Equation1515 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq1515]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1541 (G: Type _) [Magma G] (h: Equation591 G) : Equation1541 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq1518 (x y : G) : x = (y ◇ y) ◇ (x ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1547 at h
    apply Apply.Equation1547_implies_Equation1521 at h
    apply Apply.Equation1521_implies_Equation1518 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq1518]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1533 (G: Type _) [Magma G] (h: Equation591 G) : Equation1533 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq1525 (x y : G) : x = (y ◇ y) ◇ (y ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1547 at h
    apply Apply.Equation1547_implies_Equation1531 at h
    apply Apply.Equation1531_implies_Equation1525 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq1525]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1530 (G: Type _) [Magma G] (h: Equation591 G) : Equation1530 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq1528 (x y : G) : x = (y ◇ y) ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1547 at h
    apply Apply.Equation1547_implies_Equation1531 at h
    apply Apply.Equation1531_implies_Equation1528 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq1528]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation181 (G: Type _) [Magma G] (h: Equation591 G) : Equation181 G := by
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  have eq3689 (x y z : G) : x ◇ x = (y ◇ y) ◇ (y ◇ z) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3693 at h
    apply Apply.Equation3693_implies_Equation3689 at h
    apply h
  have eq3255 (x y : G) : x ◇ x = x ◇ (x ◇ (y ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3361 at h
    apply Apply.Equation3361_implies_Equation3358 at h
    apply Apply.Equation3358_implies_Equation3255 at h
    apply h
  have eq49 (x y : G) : x = x ◇ (x ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq47 x]
  symm
  nth_rewrite 1 [← eq3689]
  nth_rewrite 1 [eq3255]
  nth_rewrite 1 [← eq49]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation191 (G: Type _) [Magma G] (h: Equation591 G) : Equation191 G := by
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  have eq3699 (x y z : G) : x ◇ x = (y ◇ z) ◇ (y ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3701 at h
    apply Apply.Equation3701_implies_Equation3699 at h
    apply h
  have eq3255 (x y : G) : x ◇ x = x ◇ (x ◇ (y ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3361 at h
    apply Apply.Equation3361_implies_Equation3358 at h
    apply Apply.Equation3358_implies_Equation3255 at h
    apply h
  have eq49 (x y : G) : x = x ◇ (x ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq47 x]
  symm
  nth_rewrite 1 [← eq3699]
  nth_rewrite 1 [eq3255]
  nth_rewrite 1 [← eq49]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation192 (G: Type _) [Magma G] (h: Equation591 G) : Equation192 G := by
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  have eq3700 (x y z : G) : x ◇ x = (y ◇ z) ◇ (y ◇ z) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation3497 at h
    apply Apply.Equation3497_implies_Equation3485 at h
    apply RewriteHypothesisAndGoal.Equation3485_implies_Equation40 at h
    apply Apply.Equation40_implies_Equation3700 at h
    apply h
  have eq3255 (x y : G) : x ◇ x = x ◇ (x ◇ (y ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3361 at h
    apply Apply.Equation3361_implies_Equation3358 at h
    apply Apply.Equation3358_implies_Equation3255 at h
    apply h
  have eq49 (x y : G) : x = x ◇ (x ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq47 x]
  symm
  nth_rewrite 1 [← eq3700]
  nth_rewrite 1 [eq3255]
  nth_rewrite 1 [← eq49]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation193 (G: Type _) [Magma G] (h: Equation591 G) : Equation193 G := by
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  have eq3701 (x y z w : G) : x ◇ x = (y ◇ z) ◇ (y ◇ w) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3701 at h
    apply h
  have eq3255 (x y : G) : x ◇ x = x ◇ (x ◇ (y ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3361 at h
    apply Apply.Equation3361_implies_Equation3358 at h
    apply Apply.Equation3358_implies_Equation3255 at h
    apply h
  have eq49 (x y : G) : x = x ◇ (x ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq47 x]
  symm
  nth_rewrite 1 [← eq3701]
  nth_rewrite 1 [eq3255]
  nth_rewrite 1 [← eq49]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation244 (G: Type _) [Magma G] (h: Equation591 G) : Equation244 G := by
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  have eq3903 (x y z : G) : x ◇ x = (y ◇ (z ◇ y)) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4176 at h
    apply NthRewrites.Equation4176_implies_Equation3903 at h
    apply h
  have eq3255 (x y : G) : x ◇ x = x ◇ (x ◇ (y ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3361 at h
    apply Apply.Equation3361_implies_Equation3358 at h
    apply Apply.Equation3358_implies_Equation3255 at h
    apply h
  have eq49 (x y : G) : x = x ◇ (x ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq47 x]
  symm
  nth_rewrite 1 [← eq3903]
  nth_rewrite 1 [eq3255]
  nth_rewrite 1 [← eq49]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1606_implies_Equation1935 (G: Type _) [Magma G] (h: Equation1606 G) : Equation1935 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Run2.Equation1606_implies_Equation1809 at h
    apply Apply.Equation1809_implies_Equation1791 at h
    apply Run2.Equation1791_implies_Equation194 at h
    apply Apply.Equation194_implies_Equation159 at h
    apply Apply.Equation159_implies_Equation151 at h
    apply h
  have eq3688 (x y : G) : x ◇ x = (y ◇ y) ◇ (y ◇ y) := by
    apply Run2.Equation1606_implies_Equation1809 at h
    apply Apply.Equation1809_implies_Equation1791 at h
    apply RewriteHypothesisAndGoal.Equation1791_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3757 at h
    apply Apply.Equation3757_implies_Equation3756 at h
    apply NthRewrites.Equation3756_implies_Equation3688 at h
    apply h
  have eq1832 (x : G) : x = (x ◇ (x ◇ x)) ◇ (x ◇ x) := by
    apply Run2.Equation1606_implies_Equation1809 at h
    apply Run2.Equation1809_implies_Equation198 at h
    apply Apply.Equation198_implies_Equation162 at h
    apply Apply.Equation162_implies_Equation156 at h
    apply Apply.Equation156_implies_Equation1867 at h
    apply Apply.Equation1867_implies_Equation1837 at h
    apply Apply.Equation1837_implies_Equation1832 at h
    apply h
  have eq3659 (x : G) : x ◇ x = (x ◇ x) ◇ (x ◇ x) := by
    apply Run2.Equation1606_implies_Equation1809 at h
    apply Apply.Equation1809_implies_Equation1791 at h
    apply RewriteHypothesisAndGoal.Equation1791_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply NthRewrites.Equation3269_implies_Equation3659 at h
    apply h
  intro x y
  nth_rewrite 1 [eq151 x]
  nth_rewrite 1 [← eq3688]
  symm
  nth_rewrite 1 [← eq1832]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [eq3659]
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1792_implies_Equation98 (G: Type _) [Magma G] (h: Equation1792 G) : Equation98 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation1792_implies_Equation1791 at h
    apply Run2.Equation1791_implies_Equation194 at h
    apply Apply.Equation194_implies_Equation159 at h
    apply Apply.Equation159_implies_Equation151 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply Apply.Equation1792_implies_Equation1791 at h
    apply RewriteHypothesisAndGoal.Equation1791_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply RewriteCombinations.Equation314_implies_Equation3291 at h
    apply Run1.Equation3291_implies_Equation3304 at h
    apply h
  have eq3667 (x y : G) : x ◇ x = (x ◇ y) ◇ (y ◇ x) := by
    apply Apply.Equation1792_implies_Equation1791 at h
    apply RewriteHypothesisAndGoal.Equation1791_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3780 at h
    apply Apply.Equation3780_implies_Equation3776 at h
    apply Apply.Equation3776_implies_Equation3667 at h
    apply h
  have eq159 (x y : G) : x = (x ◇ y) ◇ (y ◇ x) := by
    apply Apply.Equation1792_implies_Equation1791 at h
    apply Run2.Equation1791_implies_Equation194 at h
    apply Apply.Equation194_implies_Equation159 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3304]
  nth_rewrite 1 [eq3667]
  nth_rewrite 1 [← eq159]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1809_implies_Equation98 (G: Type _) [Magma G] (h: Equation1809 G) : Equation98 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation1809_implies_Equation1791 at h
    apply Run2.Equation1791_implies_Equation194 at h
    apply Apply.Equation194_implies_Equation159 at h
    apply Apply.Equation159_implies_Equation151 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply Apply.Equation1809_implies_Equation1791 at h
    apply RewriteHypothesisAndGoal.Equation1791_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply RewriteCombinations.Equation314_implies_Equation3291 at h
    apply Run1.Equation3291_implies_Equation3304 at h
    apply h
  have eq3661 (x y : G) : x ◇ x = (x ◇ x) ◇ (y ◇ x) := by
    apply Apply.Equation1809_implies_Equation1791 at h
    apply RewriteHypothesisAndGoal.Equation1791_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3757 at h
    apply Apply.Equation3757_implies_Equation3754 at h
    apply Apply.Equation3754_implies_Equation3661 at h
    apply h
  have eq153 (x y : G) : x = (x ◇ x) ◇ (y ◇ x) := by
    apply Run2.Equation1809_implies_Equation198 at h
    apply Apply.Equation198_implies_Equation162 at h
    apply Apply.Equation162_implies_Equation153 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3304]
  nth_rewrite 1 [eq3661]
  nth_rewrite 1 [← eq153]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1732 (G: Type _) [Magma G] (h: Equation591 G) : Equation1732 G := by
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  have eq3282 (x y : G) : x ◇ x = y ◇ (y ◇ (y ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply Run1.Equation314_implies_Equation317 at h
    apply Apply.Equation317_implies_Equation3287 at h
    apply Apply.Equation3287_implies_Equation3283 at h
    apply Apply.Equation3283_implies_Equation3282 at h
    apply h
  have eq4380 (x : G) : x ◇ (x ◇ x) = (x ◇ x) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation337 at h
    apply Apply.Equation337_implies_Equation335 at h
    apply NthRewrites.Equation335_implies_Equation4435 at h
    apply Apply.Equation4435_implies_Equation4380 at h
    apply h
  have eq1426 (x : G) : x = (x ◇ x) ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1473 at h
    apply Apply.Equation1473_implies_Equation1437 at h
    apply Apply.Equation1437_implies_Equation1428 at h
    apply Apply.Equation1428_implies_Equation1426 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  intro x y
  nth_rewrite 1 [eq47 x]
  nth_rewrite 1 [← eq3282]
  symm
  nth_rewrite 1 [← eq4380]
  nth_rewrite 1 [← eq1426]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1733 (G: Type _) [Magma G] (h: Equation591 G) : Equation1733 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq4433 (x y : G) : x ◇ (y ◇ x) = (x ◇ x) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4582 at h
    apply Apply.Equation4582_implies_Equation4578 at h
    apply Apply.Equation4578_implies_Equation4553 at h
    apply Apply.Equation4553_implies_Equation4439 at h
    apply Apply.Equation4439_implies_Equation4433 at h
    apply h
  have eq1428 (x y : G) : x = (x ◇ x) ◇ (x ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1473 at h
    apply Apply.Equation1473_implies_Equation1437 at h
    apply Apply.Equation1437_implies_Equation1428 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 y]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq4433]
  nth_rewrite 1 [← eq1428]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1735 (G: Type _) [Magma G] (h: Equation591 G) : Equation1735 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq4435 (x y : G) : x ◇ (y ◇ x) = (x ◇ y) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation337 at h
    apply Apply.Equation337_implies_Equation335 at h
    apply NthRewrites.Equation335_implies_Equation4435 at h
    apply h
  have eq1428 (x y : G) : x = (x ◇ x) ◇ (x ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1473 at h
    apply Apply.Equation1473_implies_Equation1437 at h
    apply Apply.Equation1437_implies_Equation1428 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq4435]
  nth_rewrite 1 [← eq1428]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1736 (G: Type _) [Magma G] (h: Equation591 G) : Equation1736 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq4436 (x y : G) : x ◇ (y ◇ x) = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3383 at h
    apply NthRewrites.Equation3383_implies_Equation4545 at h
    apply Apply.Equation4545_implies_Equation4436 at h
    apply h
  have eq1428 (x y : G) : x = (x ◇ x) ◇ (x ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1473 at h
    apply Apply.Equation1473_implies_Equation1437 at h
    apply Apply.Equation1437_implies_Equation1428 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq4436]
  nth_rewrite 1 [← eq1428]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1777 (G: Type _) [Magma G] (h: Equation591 G) : Equation1777 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq4380 (x : G) : x ◇ (x ◇ x) = (x ◇ x) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation337 at h
    apply Apply.Equation337_implies_Equation335 at h
    apply NthRewrites.Equation335_implies_Equation4435 at h
    apply Apply.Equation4435_implies_Equation4380 at h
    apply h
  have eq1441 (x y : G) : x = (x ◇ y) ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1473 at h
    apply Apply.Equation1473_implies_Equation1447 at h
    apply Apply.Equation1447_implies_Equation1441 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq4380]
  nth_rewrite 1 [← eq1441]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1778 (G: Type _) [Magma G] (h: Equation591 G) : Equation1778 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq4433 (x y : G) : x ◇ (y ◇ x) = (x ◇ x) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4582 at h
    apply Apply.Equation4582_implies_Equation4578 at h
    apply Apply.Equation4578_implies_Equation4553 at h
    apply Apply.Equation4553_implies_Equation4439 at h
    apply Apply.Equation4439_implies_Equation4433 at h
    apply h
  have eq1444 (x y : G) : x = (x ◇ y) ◇ (x ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1473 at h
    apply Apply.Equation1473_implies_Equation1447 at h
    apply Apply.Equation1447_implies_Equation1444 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq4433]
  nth_rewrite 1 [← eq1444]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1781 (G: Type _) [Magma G] (h: Equation591 G) : Equation1781 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq4435 (x y : G) : x ◇ (y ◇ x) = (x ◇ y) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation337 at h
    apply Apply.Equation337_implies_Equation335 at h
    apply NthRewrites.Equation335_implies_Equation4435 at h
    apply h
  have eq1444 (x y : G) : x = (x ◇ y) ◇ (x ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1473 at h
    apply Apply.Equation1473_implies_Equation1447 at h
    apply Apply.Equation1447_implies_Equation1444 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq4435]
  nth_rewrite 1 [← eq1444]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1782 (G: Type _) [Magma G] (h: Equation591 G) : Equation1782 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq4436 (x y : G) : x ◇ (y ◇ x) = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3383 at h
    apply NthRewrites.Equation3383_implies_Equation4545 at h
    apply Apply.Equation4545_implies_Equation4436 at h
    apply h
  have eq1444 (x y : G) : x = (x ◇ y) ◇ (x ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1473 at h
    apply Apply.Equation1473_implies_Equation1447 at h
    apply Apply.Equation1447_implies_Equation1444 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq4436]
  nth_rewrite 1 [← eq1444]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1799 (G: Type _) [Magma G] (h: Equation591 G) : Equation1799 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq4380 (x : G) : x ◇ (x ◇ x) = (x ◇ x) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation337 at h
    apply Apply.Equation337_implies_Equation335 at h
    apply NthRewrites.Equation335_implies_Equation4435 at h
    apply Apply.Equation4435_implies_Equation4380 at h
    apply h
  have eq1478 (x y : G) : x = (y ◇ x) ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1510 at h
    apply Apply.Equation1510_implies_Equation1484 at h
    apply Apply.Equation1484_implies_Equation1478 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq4380]
  nth_rewrite 1 [← eq1478]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1798 (G: Type _) [Magma G] (h: Equation591 G) : Equation1798 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq4433 (x y : G) : x ◇ (y ◇ x) = (x ◇ x) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4582 at h
    apply Apply.Equation4582_implies_Equation4578 at h
    apply Apply.Equation4578_implies_Equation4553 at h
    apply Apply.Equation4553_implies_Equation4439 at h
    apply Apply.Equation4439_implies_Equation4433 at h
    apply h
  have eq1481 (x y : G) : x = (y ◇ x) ◇ (x ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1510 at h
    apply Apply.Equation1510_implies_Equation1484 at h
    apply Apply.Equation1484_implies_Equation1481 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq4433]
  nth_rewrite 1 [← eq1481]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1795 (G: Type _) [Magma G] (h: Equation591 G) : Equation1795 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq4435 (x y : G) : x ◇ (y ◇ x) = (x ◇ y) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation337 at h
    apply Apply.Equation337_implies_Equation335 at h
    apply NthRewrites.Equation335_implies_Equation4435 at h
    apply h
  have eq1481 (x y : G) : x = (y ◇ x) ◇ (x ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1510 at h
    apply Apply.Equation1510_implies_Equation1484 at h
    apply Apply.Equation1484_implies_Equation1481 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq4435]
  nth_rewrite 1 [← eq1481]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1794 (G: Type _) [Magma G] (h: Equation591 G) : Equation1794 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq4436 (x y : G) : x ◇ (y ◇ x) = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3383 at h
    apply NthRewrites.Equation3383_implies_Equation4545 at h
    apply Apply.Equation4545_implies_Equation4436 at h
    apply h
  have eq1481 (x y : G) : x = (y ◇ x) ◇ (x ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1510 at h
    apply Apply.Equation1510_implies_Equation1484 at h
    apply Apply.Equation1484_implies_Equation1481 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq4436]
  nth_rewrite 1 [← eq1481]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1748 (G: Type _) [Magma G] (h: Equation591 G) : Equation1748 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq4380 (x : G) : x ◇ (x ◇ x) = (x ◇ x) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation337 at h
    apply Apply.Equation337_implies_Equation335 at h
    apply NthRewrites.Equation335_implies_Equation4435 at h
    apply Apply.Equation4435_implies_Equation4380 at h
    apply h
  have eq1515 (x y : G) : x = (y ◇ y) ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1547 at h
    apply Apply.Equation1547_implies_Equation1521 at h
    apply Apply.Equation1521_implies_Equation1515 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq4380]
  nth_rewrite 1 [← eq1515]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1747 (G: Type _) [Magma G] (h: Equation591 G) : Equation1747 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq4433 (x y : G) : x ◇ (y ◇ x) = (x ◇ x) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4582 at h
    apply Apply.Equation4582_implies_Equation4578 at h
    apply Apply.Equation4578_implies_Equation4553 at h
    apply Apply.Equation4553_implies_Equation4439 at h
    apply Apply.Equation4439_implies_Equation4433 at h
    apply h
  have eq1518 (x y : G) : x = (y ◇ y) ◇ (x ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1547 at h
    apply Apply.Equation1547_implies_Equation1521 at h
    apply Apply.Equation1521_implies_Equation1518 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 y]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq4433]
  nth_rewrite 1 [← eq1518]
  nth_rewrite 2 [h y]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1744 (G: Type _) [Magma G] (h: Equation591 G) : Equation1744 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq4435 (x y : G) : x ◇ (y ◇ x) = (x ◇ y) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation337 at h
    apply Apply.Equation337_implies_Equation335 at h
    apply NthRewrites.Equation335_implies_Equation4435 at h
    apply h
  have eq1518 (x y : G) : x = (y ◇ y) ◇ (x ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1547 at h
    apply Apply.Equation1547_implies_Equation1521 at h
    apply Apply.Equation1521_implies_Equation1518 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq4435]
  nth_rewrite 1 [← eq1518]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation1743 (G: Type _) [Magma G] (h: Equation591 G) : Equation1743 G := by
  have eq55 (x y : G) : x = x ◇ (y ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation55 at h
    apply h
  have eq3269 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply h
  have eq4436 (x y : G) : x ◇ (y ◇ x) = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3383 at h
    apply NthRewrites.Equation3383_implies_Equation4545 at h
    apply Apply.Equation4545_implies_Equation4436 at h
    apply h
  have eq1518 (x y : G) : x = (y ◇ y) ◇ (x ◇ (y ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1623 at h
    apply Apply.Equation1623_implies_Equation1547 at h
    apply Apply.Equation1547_implies_Equation1521 at h
    apply Apply.Equation1521_implies_Equation1518 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply Apply.Equation3398_implies_Equation3269 at h
    apply Apply.Equation3269_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Run2.Equation591_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation58 at h
    apply Apply.Equation58_implies_Equation49 at h
    apply Apply.Equation49_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq55 x]
  nth_rewrite 1 [← eq3269]
  symm
  nth_rewrite 1 [← eq4436]
  nth_rewrite 1 [← eq1518]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
