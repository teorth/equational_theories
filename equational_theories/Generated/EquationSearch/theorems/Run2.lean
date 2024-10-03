import equational_theories.Generated.SimpleRewrites
import equational_theories.Generated.Constant
import equational_theories.Generated.Singleton
import equational_theories.Generated.TrivialBruteforce
import equational_theories.Generated.FinitePoly
import equational_theories.Generated.EquationSearch.theorems.Run1
import equational_theories.Subgraph

namespace Run2
@[equational_result]
theorem Equation9_implies_Equation3 (G: Type _) [Magma G] (h: Equation9 G) : Equation3 G := by
  have eq308 (x y : G) : x ◇ x = x ◇ (x ◇ y) := by
    apply Run1.Equation9_implies_Equation308 at h
    apply h
  intro x
  symm
  nth_rewrite 1 [eq308]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation9_implies_Equation3457 (G: Type _) [Magma G] (h: Equation9 G) : Equation3457 G := by
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply Run1.Equation9_implies_Equation308 at h
    apply Apply.Equation308_implies_Equation307 at h
    apply h
  have eq3915 (x y : G) : x ◇ y = (x ◇ (x ◇ x)) ◇ y := by
    apply RewriteHypothesis.Equation9_implies_Equation3921 at h
    apply Apply.Equation3921_implies_Equation3915 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Apply.Equation9_implies_Equation8 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [eq307]
  symm
  symm
  nth_rewrite 1 [← eq3915]
  symm
  nth_rewrite 1 [eq307]
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation9_implies_Equation205 (G: Type _) [Magma G] (h: Equation9 G) : Equation205 G := by
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Apply.Equation9_implies_Equation8 at h
    apply h
  have eq3864 (x y : G) : x ◇ x = (x ◇ (x ◇ y)) ◇ x := by
    apply RewriteHypothesis.Equation9_implies_Equation3921 at h
    apply Apply.Equation3921_implies_Equation3864 at h
    apply h
  have eq308 (x y : G) : x ◇ x = x ◇ (x ◇ y) := by
    apply Run1.Equation9_implies_Equation308 at h
    apply h
  intro x y
  nth_rewrite 1 [eq8 x]
  symm
  nth_rewrite 1 [← eq3864]
  symm
  symm
  nth_rewrite 1 [eq308]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation9_implies_Equation100 (G: Type _) [Magma G] (h: Equation9 G) : Equation100 G := by
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply Run1.Equation9_implies_Equation308 at h
    apply Apply.Equation308_implies_Equation307 at h
    apply h
  have eq3915 (x y : G) : x ◇ y = (x ◇ (x ◇ x)) ◇ y := by
    apply RewriteHypothesis.Equation9_implies_Equation3921 at h
    apply Apply.Equation3921_implies_Equation3915 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [eq307]
  symm
  symm
  nth_rewrite 1 [← eq3915]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation12_implies_Equation4 (G: Type _) [Magma G] (h: Equation12 G) : Equation4 G := by
  have eq327 (x y z : G) : x ◇ y = x ◇ (y ◇ z) := by
    apply Run1.Equation12_implies_Equation331 at h
    apply Apply.Equation331_implies_Equation3542 at h
    apply SimpleRewrites.Equation3542_implies_Equation3538 at h
    apply SimpleRewrites.Equation3538_implies_Equation3508 at h
    apply RewriteHypothesisAndGoal.Equation3508_implies_Equation3341 at h
    apply Apply.Equation3341_implies_Equation3314 at h
    apply Apply.Equation3314_implies_Equation3307 at h
    apply SimpleRewrites.Equation3307_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply RewriteHypothesisAndGoal.Equation322_implies_Equation42 at h
    apply Apply.Equation42_implies_Equation327 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [eq327]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation13_implies_Equation16 (G: Type _) [Magma G] (h: Equation13 G) : Equation16 G := by
  have eq4275 (x y : G) : x ◇ (x ◇ x) = y ◇ (y ◇ x) := by
    apply Run1.Equation13_implies_Equation4304 at h
    apply RewriteCombinations.Equation4304_implies_Equation4307 at h
    apply Apply.Equation4307_implies_Equation4275 at h
    apply h
  have eq4272 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ x) := by
    apply Run1.Equation13_implies_Equation4304 at h
    apply Apply.Equation4304_implies_Equation4272 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq4275]
  symm
  symm
  nth_rewrite 1 [eq4272]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation28_implies_Equation4385 (G: Type _) [Magma G] (h: Equation28 G) : Equation4385 G := by
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Run1.Equation28_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation8 at h
    apply h
  intro x y
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation28_implies_Equation104 (G: Type _) [Magma G] (h: Equation28 G) : Equation104 G := by
  have eq3461 (x y : G) : x ◇ x = x ◇ ((y ◇ x) ◇ x) := by
    apply RewriteHypothesis.Equation28_implies_Equation3533 at h
    apply Apply.Equation3533_implies_Equation3461 at h
    apply h
  have eq364 (x y : G) : x ◇ x = (y ◇ x) ◇ x := by
    apply Run1.Equation28_implies_Equation364 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq3461]
  symm
  symm
  nth_rewrite 1 [eq364]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation28_implies_Equation3674 (G: Type _) [Magma G] (h: Equation28 G) : Equation3674 G := by
  have eq359 (x : G) : x ◇ x = (x ◇ x) ◇ x := by
    apply Run1.Equation28_implies_Equation364 at h
    apply Apply.Equation364_implies_Equation359 at h
    apply h
  have eq1681 (x y : G) : x = (y ◇ x) ◇ ((x ◇ x) ◇ x) := by
    apply RewriteHypothesis.Equation28_implies_Equation1701 at h
    apply Apply.Equation1701_implies_Equation1681 at h
    apply h
  have eq23 (x : G) : x = (x ◇ x) ◇ x := by
    apply Run1.Equation28_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation23 at h
    apply h
  have eq4587 (x y : G) : (x ◇ x) ◇ x = (y ◇ x) ◇ x := by
    apply Run1.Equation28_implies_Equation364 at h
    apply RewriteHypothesis.Equation364_implies_Equation4666 at h
    apply Apply.Equation4666_implies_Equation4587 at h
    apply h
  have eq3 (x : G) : x = x ◇ x := by
    apply Run1.Equation28_implies_Equation3 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [eq359]
  symm
  symm
  nth_rewrite 1 [← eq1681]
  symm
  symm
  nth_rewrite 1 [eq23 x]
  symm
  symm
  nth_rewrite 1 [eq4587]
  symm
  nth_rewrite 1 [← eq3]
  apply h
  repeat assumption
@[equational_result]
theorem Equation28_implies_Equation3877 (G: Type _) [Magma G] (h: Equation28 G) : Equation3877 G := by
  have eq359 (x : G) : x ◇ x = (x ◇ x) ◇ x := by
    apply Run1.Equation28_implies_Equation364 at h
    apply Apply.Equation364_implies_Equation359 at h
    apply h
  have eq2493 (x y : G) : x = (y ◇ ((x ◇ x) ◇ x)) ◇ x := by
    apply RewriteHypothesis.Equation28_implies_Equation2567 at h
    apply Apply.Equation2567_implies_Equation2493 at h
    apply h
  have eq23 (x : G) : x = (x ◇ x) ◇ x := by
    apply Run1.Equation28_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation23 at h
    apply h
  have eq4587 (x y : G) : (x ◇ x) ◇ x = (y ◇ x) ◇ x := by
    apply Run1.Equation28_implies_Equation364 at h
    apply RewriteHypothesis.Equation364_implies_Equation4666 at h
    apply Apply.Equation4666_implies_Equation4587 at h
    apply h
  have eq3 (x : G) : x = x ◇ x := by
    apply Run1.Equation28_implies_Equation3 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [eq359]
  symm
  symm
  nth_rewrite 1 [← eq2493]
  symm
  symm
  nth_rewrite 1 [eq23 x]
  symm
  symm
  nth_rewrite 1 [eq4587]
  symm
  nth_rewrite 1 [← eq3]
  apply h
  repeat assumption
@[equational_result]
theorem Equation29_implies_Equation1075 (G: Type _) [Magma G] (h: Equation29 G) : Equation1075 G := by
  have eq3917 (x y : G) : x ◇ y = (x ◇ (x ◇ y)) ◇ x := by
    apply Apply.Equation29_implies_Equation3994 at h
    apply Apply.Equation3994_implies_Equation3917 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply Run1.Equation29_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq4386 (x y : G) : x ◇ (x ◇ x) = (y ◇ x) ◇ y := by
    apply Run1.Equation29_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4386 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq3917]
  symm
  symm
  nth_rewrite 1 [← eq4273]
  symm
  symm
  nth_rewrite 1 [eq4386]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation29_implies_Equation1276 (G: Type _) [Magma G] (h: Equation29 G) : Equation1276 G := by
  have eq4118 (x y : G) : x ◇ y = ((x ◇ x) ◇ x) ◇ y := by
    apply Apply.Equation29_implies_Equation23 at h
    apply RewriteHypothesis.Equation23_implies_Equation4118 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply Run1.Equation29_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4446 at h
    apply RewriteGoal.Equation4446_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq4386 (x y : G) : x ◇ (x ◇ x) = (y ◇ x) ◇ y := by
    apply Run1.Equation29_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4386 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq4118]
  symm
  symm
  nth_rewrite 1 [← eq4273]
  symm
  symm
  nth_rewrite 1 [eq4386]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation34_implies_Equation5 (G: Type _) [Magma G] (h: Equation34 G) : Equation5 G := by
  have eq39 (x y : G) : x ◇ x = y ◇ x := by
    apply Run1.Equation34_implies_Equation407 at h
    apply Apply.Equation407_implies_Equation4253 at h
    apply SimpleRewrites.Equation4253_implies_Equation4234 at h
    apply SimpleRewrites.Equation4234_implies_Equation4168 at h
    apply RewriteHypothesisAndGoal.Equation4168_implies_Equation4060 at h
    apply Apply.Equation4060_implies_Equation4055 at h
    apply SimpleRewrites.Equation4055_implies_Equation4031 at h
    apply SimpleRewrites.Equation4031_implies_Equation3965 at h
    apply RewriteHypothesisAndGoal.Equation3965_implies_Equation391 at h
    apply Apply.Equation391_implies_Equation388 at h
    apply RewriteHypothesisAndGoal.Equation388_implies_Equation45 at h
    apply Subgraph.Equation45_implies_Equation39 at h
    apply h
  have eq370 (x y z : G) : x ◇ x = (y ◇ z) ◇ x := by
    apply Run1.Equation34_implies_Equation407 at h
    apply Apply.Equation407_implies_Equation4253 at h
    apply SimpleRewrites.Equation4253_implies_Equation4234 at h
    apply SimpleRewrites.Equation4234_implies_Equation4168 at h
    apply RewriteHypothesisAndGoal.Equation4168_implies_Equation4060 at h
    apply Apply.Equation4060_implies_Equation4055 at h
    apply SimpleRewrites.Equation4055_implies_Equation4031 at h
    apply SimpleRewrites.Equation4031_implies_Equation3965 at h
    apply RewriteHypothesisAndGoal.Equation3965_implies_Equation391 at h
    apply Apply.Equation391_implies_Equation388 at h
    apply RewriteHypothesisAndGoal.Equation388_implies_Equation45 at h
    apply Subgraph.Equation45_implies_Equation39 at h
    apply Apply.Equation39_implies_Equation370 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq39]
  symm
  symm
  nth_rewrite 1 [eq370]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation34_implies_Equation13 (G: Type _) [Magma G] (h: Equation34 G) : Equation13 G := by
  have eq4272 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ x) := by
    apply Run1.Equation34_implies_Equation407 at h
    apply Apply.Equation407_implies_Equation4253 at h
    apply SimpleRewrites.Equation4253_implies_Equation4234 at h
    apply SimpleRewrites.Equation4234_implies_Equation4168 at h
    apply RewriteHypothesisAndGoal.Equation4168_implies_Equation4060 at h
    apply Apply.Equation4060_implies_Equation4055 at h
    apply SimpleRewrites.Equation4055_implies_Equation4031 at h
    apply SimpleRewrites.Equation4031_implies_Equation3965 at h
    apply RewriteHypothesisAndGoal.Equation3965_implies_Equation391 at h
    apply Apply.Equation391_implies_Equation388 at h
    apply RewriteHypothesisAndGoal.Equation388_implies_Equation45 at h
    apply RewriteHypothesisAndGoal.Equation45_implies_Equation4278 at h
    apply RewriteCombinations.Equation4278_implies_Equation4304 at h
    apply Apply.Equation4304_implies_Equation4272 at h
    apply h
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply Apply.Equation34_implies_Equation28 at h
    apply Run1.Equation28_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply h
  have eq370 (x y z : G) : x ◇ x = (y ◇ z) ◇ x := by
    apply Run1.Equation34_implies_Equation407 at h
    apply Apply.Equation407_implies_Equation4253 at h
    apply SimpleRewrites.Equation4253_implies_Equation4234 at h
    apply SimpleRewrites.Equation4234_implies_Equation4168 at h
    apply RewriteHypothesisAndGoal.Equation4168_implies_Equation4060 at h
    apply Apply.Equation4060_implies_Equation4055 at h
    apply SimpleRewrites.Equation4055_implies_Equation4031 at h
    apply SimpleRewrites.Equation4031_implies_Equation3965 at h
    apply RewriteHypothesisAndGoal.Equation3965_implies_Equation391 at h
    apply Apply.Equation391_implies_Equation388 at h
    apply RewriteHypothesisAndGoal.Equation388_implies_Equation45 at h
    apply Subgraph.Equation45_implies_Equation39 at h
    apply Apply.Equation39_implies_Equation370 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq4272]
  symm
  symm
  nth_rewrite 1 [← eq307]
  symm
  symm
  nth_rewrite 1 [eq370]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation34_implies_Equation3824 (G: Type _) [Magma G] (h: Equation34 G) : Equation3824 G := by
  have eq39 (x y : G) : x ◇ x = y ◇ x := by
    apply Run1.Equation34_implies_Equation407 at h
    apply Apply.Equation407_implies_Equation4253 at h
    apply SimpleRewrites.Equation4253_implies_Equation4234 at h
    apply SimpleRewrites.Equation4234_implies_Equation4168 at h
    apply RewriteHypothesisAndGoal.Equation4168_implies_Equation4060 at h
    apply Apply.Equation4060_implies_Equation4055 at h
    apply SimpleRewrites.Equation4055_implies_Equation4031 at h
    apply SimpleRewrites.Equation4031_implies_Equation3965 at h
    apply RewriteHypothesisAndGoal.Equation3965_implies_Equation391 at h
    apply Apply.Equation391_implies_Equation388 at h
    apply RewriteHypothesisAndGoal.Equation388_implies_Equation45 at h
    apply Subgraph.Equation45_implies_Equation39 at h
    apply h
  have eq359 (x : G) : x ◇ x = (x ◇ x) ◇ x := by
    apply Apply.Equation34_implies_Equation28 at h
    apply Run1.Equation28_implies_Equation364 at h
    apply Apply.Equation364_implies_Equation359 at h
    apply h
  have eq3684 (x y : G) : x ◇ x = (y ◇ y) ◇ (x ◇ x) := by
    apply Apply.Equation34_implies_Equation31 at h
    apply Apply.Equation31_implies_Equation3820 at h
    apply Apply.Equation3820_implies_Equation3684 at h
    apply h
  have eq370 (x y z : G) : x ◇ x = (y ◇ z) ◇ x := by
    apply Run1.Equation34_implies_Equation407 at h
    apply Apply.Equation407_implies_Equation4253 at h
    apply SimpleRewrites.Equation4253_implies_Equation4234 at h
    apply SimpleRewrites.Equation4234_implies_Equation4168 at h
    apply RewriteHypothesisAndGoal.Equation4168_implies_Equation4060 at h
    apply Apply.Equation4060_implies_Equation4055 at h
    apply SimpleRewrites.Equation4055_implies_Equation4031 at h
    apply SimpleRewrites.Equation4031_implies_Equation3965 at h
    apply RewriteHypothesisAndGoal.Equation3965_implies_Equation391 at h
    apply Apply.Equation391_implies_Equation388 at h
    apply RewriteHypothesisAndGoal.Equation388_implies_Equation45 at h
    apply Subgraph.Equation45_implies_Equation39 at h
    apply Apply.Equation39_implies_Equation370 at h
    apply h
  have eq23 (x : G) : x = (x ◇ x) ◇ x := by
    apply Apply.Equation34_implies_Equation25 at h
    apply Apply.Equation25_implies_Equation23 at h
    apply h
  intro x y z
  nth_rewrite 1 [← eq39]
  nth_rewrite 1 [eq359]
  symm
  nth_rewrite 1 [← eq3684]
  symm
  symm
  nth_rewrite 1 [eq370]
  symm
  nth_rewrite 1 [← eq23]
  apply h
  repeat assumption
@[equational_result]
theorem Equation332_implies_Equation387 (G: Type _) [Magma G] (h: Equation332 G) : Equation387 G := by
  have eq4482 (x y : G) : x ◇ (y ◇ y) = (y ◇ y) ◇ x := by
    apply NthRewrites.Equation332_implies_Equation4482 at h
    apply h
  have eq4343 (x y : G) : x ◇ (y ◇ y) = y ◇ (x ◇ x) := by
    apply Run1.Equation332_implies_Equation4343 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq4482]
  symm
  symm
  nth_rewrite 1 [eq4343]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation372_implies_Equation369 (G: Type _) [Magma G] (h: Equation372 G) : Equation369 G := by
  have eq4612 (x y z : G) : (x ◇ x) ◇ y = (y ◇ z) ◇ z := by
    apply Run1.Equation372_implies_Equation4627 at h
    apply Apply.Equation4627_implies_Equation4612 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq4612]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation387_implies_Equation4470 (G: Type _) [Magma G] (h: Equation387 G) : Equation4470 G := by
  have eq4608 (x y : G) : (x ◇ x) ◇ y = (y ◇ y) ◇ x := by
    apply Run1.Equation387_implies_Equation4608 at h
    apply h
  have eq326 (x y : G) : x ◇ y = x ◇ (y ◇ y) := by
    apply RewriteHypothesis.Equation387_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation326 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [eq4608]
  symm
  nth_rewrite 1 [← eq326]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3401_implies_Equation3375 (G: Type _) [Magma G] (h: Equation3401 G) : Equation3375 G := by
  have eq39 (x y : G) : x ◇ x = y ◇ x := by
    apply Apply.Equation3401_implies_Equation3356 at h
    apply RewriteHypothesisAndGoal.Equation3356_implies_Equation45 at h
    apply Subgraph.Equation45_implies_Equation39 at h
    apply h
  have eq359 (x : G) : x ◇ x = (x ◇ x) ◇ x := by
    apply Apply.Equation3401_implies_Equation3356 at h
    apply RewriteHypothesisAndGoal.Equation3356_implies_Equation45 at h
    apply Apply.Equation45_implies_Equation381 at h
    apply Apply.Equation381_implies_Equation361 at h
    apply Apply.Equation361_implies_Equation359 at h
    apply h
  have eq3264 (x y z : G) : x ◇ x = x ◇ (y ◇ (z ◇ x)) := by
    apply Apply.Equation3401_implies_Equation3356 at h
    apply NthRewrites.Equation3356_implies_Equation3367 at h
    apply RewriteCombinations.Equation3367_implies_Equation3330 at h
    apply NthRewrites.Equation3330_implies_Equation3264 at h
    apply h
  have eq3268 (x y : G) : x ◇ x = y ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation3401_implies_Equation3356 at h
    apply RewriteCombinations.Equation3356_implies_Equation3359 at h
    apply RewriteCombinations.Equation3359_implies_Equation3274 at h
    apply Apply.Equation3274_implies_Equation3268 at h
    apply h
  have eq388 (x y : G) : x ◇ y = (y ◇ y) ◇ y := by
    apply Apply.Equation3401_implies_Equation3356 at h
    apply RewriteHypothesisAndGoal.Equation3356_implies_Equation45 at h
    apply Subgraph.Equation45_implies_Equation39 at h
    apply RewriteCombinations.Equation39_implies_Equation399 at h
    apply SimpleRewrites.Equation399_implies_Equation388 at h
    apply h
  intro x y z w
  nth_rewrite 1 [← eq39]
  nth_rewrite 1 [eq359]
  symm
  nth_rewrite 1 [← eq3264]
  symm
  symm
  nth_rewrite 1 [eq3268]
  symm
  nth_rewrite 1 [← eq388]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4017_implies_Equation4059 (G: Type _) [Magma G] (h: Equation4017 G) : Equation4059 G := by
  have eq3308 (x y : G) : x ◇ y = x ◇ (x ◇ (y ◇ x)) := by
    apply Apply.Equation4017_implies_Equation4013 at h
    apply NthRewrites.Equation4013_implies_Equation3331 at h
    apply Apply.Equation3331_implies_Equation3308 at h
    apply h
  have eq3255 (x y : G) : x ◇ x = x ◇ (x ◇ (y ◇ x)) := by
    apply Apply.Equation4017_implies_Equation3930 at h
    apply NthRewrites.Equation3930_implies_Equation3324 at h
    apply Apply.Equation3324_implies_Equation3257 at h
    apply Apply.Equation3257_implies_Equation3255 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3308]
  nth_rewrite 1 [← eq3255]
  nth_rewrite 1 [eq3255]
  nth_rewrite 1 [← eq3308]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4578_implies_Equation4431 (G: Type _) [Magma G] (h: Equation4578 G) : Equation4431 G := by
  have eq4268 (x y : G) : x ◇ (x ◇ x) = x ◇ (x ◇ y) := by
    apply Apply.Equation4578_implies_Equation4427 at h
    apply Apply.Equation4427_implies_Equation4401 at h
    apply Apply.Equation4401_implies_Equation4395 at h
    apply RewriteGoal.Equation4395_implies_Equation4282 at h
    apply Apply.Equation4282_implies_Equation4268 at h
    apply h
  have eq4271 (x y z : G) : x ◇ (x ◇ x) = x ◇ (y ◇ z) := by
    apply Apply.Equation4578_implies_Equation4536 at h
    apply Run1.Equation4536_implies_Equation4518 at h
    apply Apply.Equation4518_implies_Equation4506 at h
    apply RewriteGoal.Equation4506_implies_Equation4361 at h
    apply Apply.Equation4361_implies_Equation4289 at h
    apply SimpleRewrites.Equation4289_implies_Equation4271 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [← eq4268]
  nth_rewrite 1 [eq4271]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4578_implies_Equation4571 (G: Type _) [Magma G] (h: Equation4578 G) : Equation4571 G := by
  have eq4317 (x y z : G) : x ◇ (y ◇ x) = x ◇ (z ◇ y) := by
    apply Apply.Equation4578_implies_Equation4536 at h
    apply Run1.Equation4536_implies_Equation4518 at h
    apply Apply.Equation4518_implies_Equation4506 at h
    apply RewriteGoal.Equation4506_implies_Equation4361 at h
    apply Apply.Equation4361_implies_Equation4289 at h
    apply RewriteCombinations.Equation4289_implies_Equation4317 at h
    apply h
  have eq4687 (x y z w : G) : (x ◇ y) ◇ z = (z ◇ w) ◇ y := by
    apply Run1.Equation4578_implies_Equation4468 at h
    apply Apply.Equation4468_implies_Equation4394 at h
    apply Apply.Equation4394_implies_Equation4387 at h
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4617 at h
    apply Apply.Equation4617_implies_Equation4607 at h
    apply RewriteCombinations.Equation4607_implies_Equation4667 at h
    apply Apply.Equation4667_implies_Equation4665 at h
    apply RewriteCombinations.Equation4665_implies_Equation4668 at h
    apply RewriteGoal.Equation4668_implies_Equation4664 at h
    apply RewriteGoal.Equation4664_implies_Equation4662 at h
    apply RewriteGoal.Equation4662_implies_Equation4671 at h
    apply Apply.Equation4671_implies_Equation4596 at h
    apply RewriteCombinations.Equation4596_implies_Equation4644 at h
    apply RewriteCombinations.Equation4644_implies_Equation4694 at h
    apply SimpleRewrites.Equation4694_implies_Equation4688 at h
    apply Apply.Equation4688_implies_Equation4687 at h
    apply h
  have eq4315 (x y z : G) : x ◇ (y ◇ x) = x ◇ (y ◇ z) := by
    apply Apply.Equation4578_implies_Equation4519 at h
    apply Apply.Equation4519_implies_Equation4507 at h
    apply RewriteGoal.Equation4507_implies_Equation4357 at h
    apply Apply.Equation4357_implies_Equation4339 at h
    apply RewriteCombinations.Equation4339_implies_Equation4315 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [← eq4317]
  symm
  nth_rewrite 1 [eq4687]
  symm
  nth_rewrite 1 [eq4315]
  apply h
  repeat assumption
@[equational_result]
theorem Equation13_implies_Equation19 (G: Type _) [Magma G] (h: Equation13 G) : Equation19 G := by
  have eq4340 (x y z : G) : x ◇ (y ◇ y) = x ◇ (z ◇ y) := by
    apply RewriteHypothesis.Equation13_implies_Equation3330 at h
    apply NthRewrites.Equation3330_implies_Equation4340 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4340]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation28_implies_Equation218 (G: Type _) [Magma G] (h: Equation28 G) : Equation218 G := by
  have eq326 (x y : G) : x ◇ y = x ◇ (y ◇ y) := by
    apply Run1.Equation28_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation326 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq326]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation28_implies_Equation2290 (G: Type _) [Magma G] (h: Equation28 G) : Equation2290 G := by
  have eq3319 (x y : G) : x ◇ y = x ◇ (y ◇ (y ◇ y)) := by
    apply Run1.Equation28_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation8 at h
    apply RewriteHypothesis.Equation8_implies_Equation3319 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq3319]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation28_implies_Equation2706 (G: Type _) [Magma G] (h: Equation28 G) : Equation2706 G := by
  have eq3722 (x y : G) : x ◇ y = (x ◇ y) ◇ (x ◇ y) := by
    apply Run1.Equation28_implies_Equation3 at h
    apply Apply.Equation3_implies_Equation3722 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq3722]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation29_implies_Equation2331 (G: Type _) [Magma G] (h: Equation29 G) : Equation2331 G := by
  have eq3308 (x y : G) : x ◇ y = x ◇ (x ◇ (y ◇ x)) := by
    apply Subgraph.Equation29_implies_Equation14 at h
    apply RewriteHypothesis.Equation14_implies_Equation3331 at h
    apply Apply.Equation3331_implies_Equation3308 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq3308]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation29_implies_Equation2291 (G: Type _) [Magma G] (h: Equation29 G) : Equation2291 G := by
  have eq3319 (x y : G) : x ◇ y = x ◇ (y ◇ (y ◇ y)) := by
    apply Subgraph.Equation29_implies_Equation14 at h
    apply RewriteHypothesis.Equation14_implies_Equation3331 at h
    apply Apply.Equation3331_implies_Equation3319 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq3319]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation29_implies_Equation2947 (G: Type _) [Magma G] (h: Equation29 G) : Equation2947 G := by
  have eq3915 (x y : G) : x ◇ y = (x ◇ (x ◇ x)) ◇ y := by
    apply Subgraph.Equation29_implies_Equation14 at h
    apply Apply.Equation14_implies_Equation8 at h
    apply RewriteHypothesis.Equation8_implies_Equation3915 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq3915]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation316_implies_Equation320 (G: Type _) [Magma G] (h: Equation316 G) : Equation320 G := by
  have eq4270 (x y : G) : x ◇ (x ◇ x) = x ◇ (y ◇ y) := by
    apply RewriteCombinations.Equation316_implies_Equation4280 at h
    apply RewriteCombinations.Equation4280_implies_Equation4341 at h
    apply Apply.Equation4341_implies_Equation4270 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4270]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation317_implies_Equation320 (G: Type _) [Magma G] (h: Equation317 G) : Equation320 G := by
  have eq4284 (x y : G) : x ◇ (x ◇ y) = x ◇ (y ◇ y) := by
    apply RewriteCombinations.Equation317_implies_Equation4312 at h
    apply Apply.Equation4312_implies_Equation4288 at h
    apply Apply.Equation4288_implies_Equation4284 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4284]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation368_implies_Equation369 (G: Type _) [Magma G] (h: Equation368 G) : Equation369 G := by
  have eq4583 (x y : G) : (x ◇ x) ◇ x = (x ◇ x) ◇ y := by
    apply RewriteCombinations.Equation368_implies_Equation4592 at h
    apply RewriteCombinations.Equation4592_implies_Equation4597 at h
    apply Apply.Equation4597_implies_Equation4583 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4583]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation387_implies_Equation3964 (G: Type _) [Magma G] (h: Equation387 G) : Equation3964 G := by
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply RewriteHypothesis.Equation387_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq307]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation94 (G: Type _) [Magma G] (h: Equation591 G) : Equation94 G := by
  have eq325 (x y : G) : x ◇ y = x ◇ (y ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4186 at h
    apply Apply.Equation4186_implies_Equation4178 at h
    apply NthRewrites.Equation4178_implies_Equation327 at h
    apply Apply.Equation327_implies_Equation325 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq325 w]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation603 (G: Type _) [Magma G] (h: Equation591 G) : Equation603 G := by
  have eq4283 (x y : G) : x ◇ (x ◇ y) = x ◇ (y ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3424 at h
    apply Constant.Equation3424_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation387 at h
    apply Subgraph.Equation387_implies_Equation43 at h
    apply NthRewrites.Equation43_implies_Equation4358 at h
    apply Apply.Equation4358_implies_Equation4283 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4283]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation588 (G: Type _) [Magma G] (h: Equation591 G) : Equation588 G := by
  have eq4314 (x y : G) : x ◇ (y ◇ x) = x ◇ (y ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4177 at h
    apply Apply.Equation4177_implies_Equation4174 at h
    apply NthRewrites.Equation4174_implies_Equation4510 at h
    apply RewriteGoal.Equation4510_implies_Equation4357 at h
    apply Apply.Equation4357_implies_Equation4339 at h
    apply RewriteHypothesis.Equation4339_implies_Equation4314 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4314]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation591_implies_Equation794 (G: Type _) [Magma G] (h: Equation591 G) : Equation794 G := by
  have eq4435 (x y : G) : x ◇ (y ◇ x) = (x ◇ y) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation337 at h
    apply Apply.Equation337_implies_Equation335 at h
    apply NthRewrites.Equation335_implies_Equation4435 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4435]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation592_implies_Equation795 (G: Type _) [Magma G] (h: Equation592 G) : Equation795 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation592_implies_Equation591 at h
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w u
  symm
  nth_rewrite 1 [← eq4512]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation742_implies_Equation84 (G: Type _) [Magma G] (h: Equation742 G) : Equation84 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation742_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3792 at h
    apply Apply.Equation3792_implies_Equation3716 at h
    apply Apply.Equation3716_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation375 at h
    apply h
  intro x y z
  symm
  nth_rewrite 3 [eq375]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation743_implies_Equation85 (G: Type _) [Magma G] (h: Equation743 G) : Equation85 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply Apply.Equation743_implies_Equation742 at h
    apply RewriteHypothesisAndGoal.Equation742_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3792 at h
    apply Apply.Equation3792_implies_Equation3716 at h
    apply Apply.Equation3716_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation375 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 3 [eq375]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation743_implies_Equation755 (G: Type _) [Magma G] (h: Equation743 G) : Equation755 G := by
  have eq4599 (x y : G) : (x ◇ x) ◇ y = (x ◇ y) ◇ y := by
    apply Apply.Equation743_implies_Equation742 at h
    apply RewriteHypothesisAndGoal.Equation742_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4582 at h
    apply Apply.Equation4582_implies_Equation4431 at h
    apply Apply.Equation4431_implies_Equation4404 at h
    apply Apply.Equation4404_implies_Equation4402 at h
    apply RewriteHypothesis.Equation4402_implies_Equation4675 at h
    apply Apply.Equation4675_implies_Equation4655 at h
    apply RewriteHypothesis.Equation4655_implies_Equation4599 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4599]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation877_implies_Equation15 (G: Type _) [Magma G] (h: Equation877 G) : Equation15 G := by
  have eq3715 (x y : G) : x ◇ y = (x ◇ x) ◇ (y ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation877_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3792 at h
    apply Apply.Equation3792_implies_Equation3716 at h
    apply Apply.Equation3716_implies_Equation3715 at h
    apply h
  intro x y z
  symm
  nth_rewrite 2 [eq3715]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation899_implies_Equation15 (G: Type _) [Magma G] (h: Equation899 G) : Equation15 G := by
  have eq3725 (x y : G) : x ◇ y = (x ◇ y) ◇ (y ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation899_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3857 at h
    apply Apply.Equation3857_implies_Equation3852 at h
    apply Apply.Equation3852_implies_Equation3828 at h
    apply RewriteCombinations.Equation3828_implies_Equation3842 at h
    apply Apply.Equation3842_implies_Equation3773 at h
    apply Apply.Equation3773_implies_Equation3762 at h
    apply RewriteCombinations.Equation3762_implies_Equation3811 at h
    apply RewriteCombinations.Equation3811_implies_Equation3744 at h
    apply Apply.Equation3744_implies_Equation3728 at h
    apply Apply.Equation3728_implies_Equation3725 at h
    apply h
  intro x y z
  symm
  nth_rewrite 2 [eq3725]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation953_implies_Equation19 (G: Type _) [Magma G] (h: Equation953 G) : Equation19 G := by
  have eq3721 (x y : G) : x ◇ y = (x ◇ y) ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation953_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply NthRewrites.Equation3398_implies_Equation3810 at h
    apply Apply.Equation3810_implies_Equation3721 at h
    apply h
  intro x y z
  symm
  nth_rewrite 2 [eq3721]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1604_implies_Equation1807 (G: Type _) [Magma G] (h: Equation1604 G) : Equation1807 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation1604_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 2 [← eq4512]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1606_implies_Equation1809 (G: Type _) [Magma G] (h: Equation1606 G) : Equation1809 G := by
  have eq4435 (x y : G) : x ◇ (y ◇ x) = (x ◇ y) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation1606_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation337 at h
    apply Apply.Equation337_implies_Equation335 at h
    apply NthRewrites.Equation335_implies_Equation4435 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4435]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1607_implies_Equation1810 (G: Type _) [Magma G] (h: Equation1607 G) : Equation1810 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation1607_implies_Equation1604 at h
    apply RewriteHypothesisAndGoal.Equation1604_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w u
  symm
  nth_rewrite 2 [← eq4512]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1715_implies_Equation1712 (G: Type _) [Magma G] (h: Equation1715 G) : Equation1712 G := by
  have eq4598 (x y : G) : (x ◇ x) ◇ y = (x ◇ y) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation1715_implies_Equation371 at h
    apply RewriteCombinations.Equation371_implies_Equation4626 at h
    apply Apply.Equation4626_implies_Equation4601 at h
    apply Apply.Equation4601_implies_Equation4598 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4598]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1757_implies_Equation188 (G: Type _) [Magma G] (h: Equation1757 G) : Equation188 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation1757_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3792 at h
    apply Apply.Equation3792_implies_Equation3716 at h
    apply Apply.Equation3716_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation375 at h
    apply h
  intro x y z
  symm
  nth_rewrite 3 [eq375]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1758_implies_Equation189 (G: Type _) [Magma G] (h: Equation1758 G) : Equation189 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply Apply.Equation1758_implies_Equation1757 at h
    apply RewriteHypothesisAndGoal.Equation1757_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3792 at h
    apply Apply.Equation3792_implies_Equation3716 at h
    apply Apply.Equation3716_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation375 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 3 [eq375]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1791_implies_Equation194 (G: Type _) [Magma G] (h: Equation1791 G) : Equation194 G := by
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
  intro x y z
  symm
  nth_rewrite 3 [eq377]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1791_implies_Equation1594 (G: Type _) [Magma G] (h: Equation1791 G) : Equation1594 G := by
  have eq4398 (x y : G) : x ◇ (x ◇ y) = (x ◇ y) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation1791_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3376 at h
    apply Apply.Equation3376_implies_Equation3364 at h
    apply NthRewrites.Equation3364_implies_Equation4531 at h
    apply Apply.Equation4531_implies_Equation4398 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq4398]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1791_implies_Equation1588 (G: Type _) [Magma G] (h: Equation1791 G) : Equation1588 G := by
  have eq4435 (x y : G) : x ◇ (y ◇ x) = (x ◇ y) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation1791_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation337 at h
    apply Apply.Equation337_implies_Equation335 at h
    apply NthRewrites.Equation335_implies_Equation4435 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq4435]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1791_implies_Equation1586 (G: Type _) [Magma G] (h: Equation1791 G) : Equation1586 G := by
  have eq4472 (x y : G) : x ◇ (y ◇ y) = (x ◇ y) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation1791_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4177 at h
    apply Apply.Equation4177_implies_Equation4174 at h
    apply NthRewrites.Equation4174_implies_Equation4510 at h
    apply Apply.Equation4510_implies_Equation4472 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq4472]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1791_implies_Equation1797 (G: Type _) [Magma G] (h: Equation1791 G) : Equation1797 G := by
  have eq4598 (x y : G) : (x ◇ x) ◇ y = (x ◇ y) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation1791_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4582 at h
    apply Apply.Equation4582_implies_Equation4431 at h
    apply Apply.Equation4431_implies_Equation4404 at h
    apply Apply.Equation4404_implies_Equation4384 at h
    apply RewriteHypothesis.Equation4384_implies_Equation4676 at h
    apply Apply.Equation4676_implies_Equation4673 at h
    apply Apply.Equation4673_implies_Equation4598 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq4598]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1791_implies_Equation1789 (G: Type _) [Magma G] (h: Equation1791 G) : Equation1789 G := by
  have eq4629 (x y : G) : (x ◇ y) ◇ x = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation1791_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4163 at h
    apply Apply.Equation4163_implies_Equation4159 at h
    apply NthRewrites.Equation4159_implies_Equation4407 at h
    apply RewriteHypothesis.Equation4407_implies_Equation4672 at h
    apply Apply.Equation4672_implies_Equation4654 at h
    apply RewriteHypothesis.Equation4654_implies_Equation4629 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4629]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1792_implies_Equation1589 (G: Type _) [Magma G] (h: Equation1792 G) : Equation1589 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation1792_implies_Equation1791 at h
    apply RewriteHypothesisAndGoal.Equation1791_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 2 [eq4512]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1809_implies_Equation198 (G: Type _) [Magma G] (h: Equation1809 G) : Equation198 G := by
  have eq377 (x y : G) : x ◇ y = (x ◇ y) ◇ x := by
    apply Apply.Equation1809_implies_Equation1791 at h
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
  intro x y z w
  symm
  nth_rewrite 3 [eq377]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1809_implies_Equation1618 (G: Type _) [Magma G] (h: Equation1809 G) : Equation1618 G := by
  have eq4398 (x y : G) : x ◇ (x ◇ y) = (x ◇ y) ◇ x := by
    apply Apply.Equation1809_implies_Equation1791 at h
    apply RewriteHypothesisAndGoal.Equation1791_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3376 at h
    apply Apply.Equation3376_implies_Equation3364 at h
    apply NthRewrites.Equation3364_implies_Equation4531 at h
    apply Apply.Equation4531_implies_Equation4398 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4398]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1809_implies_Equation1606 (G: Type _) [Magma G] (h: Equation1809 G) : Equation1606 G := by
  have eq4435 (x y : G) : x ◇ (y ◇ x) = (x ◇ y) ◇ x := by
    apply Apply.Equation1809_implies_Equation1791 at h
    apply RewriteHypothesisAndGoal.Equation1791_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation337 at h
    apply Apply.Equation337_implies_Equation335 at h
    apply NthRewrites.Equation335_implies_Equation4435 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4435]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1809_implies_Equation1603 (G: Type _) [Magma G] (h: Equation1809 G) : Equation1603 G := by
  have eq4472 (x y : G) : x ◇ (y ◇ y) = (x ◇ y) ◇ x := by
    apply Apply.Equation1809_implies_Equation1791 at h
    apply RewriteHypothesisAndGoal.Equation1791_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4177 at h
    apply Apply.Equation4177_implies_Equation4174 at h
    apply NthRewrites.Equation4174_implies_Equation4510 at h
    apply Apply.Equation4510_implies_Equation4472 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4472]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1889_implies_Equation171 (G: Type _) [Magma G] (h: Equation1889 G) : Equation171 G := by
  have eq326 (x y : G) : x ◇ y = x ◇ (y ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation1889_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3792 at h
    apply Apply.Equation3792_implies_Equation3716 at h
    apply Apply.Equation3716_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation326 at h
    apply h
  intro x y z
  symm
  nth_rewrite 2 [eq326]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1892_implies_Equation1929 (G: Type _) [Magma G] (h: Equation1892 G) : Equation1929 G := by
  have eq4284 (x y : G) : x ◇ (x ◇ y) = x ◇ (y ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation1892_implies_Equation4356 at h
    apply Apply.Equation4356_implies_Equation4353 at h
    apply RewriteCombinations.Equation4353_implies_Equation4379 at h
    apply Apply.Equation4379_implies_Equation4375 at h
    apply Apply.Equation4375_implies_Equation4302 at h
    apply Apply.Equation4302_implies_Equation4292 at h
    apply RewriteCombinations.Equation4292_implies_Equation4298 at h
    apply SimpleRewrites.Equation4298_implies_Equation4295 at h
    apply RewriteGoal.Equation4295_implies_Equation4287 at h
    apply RewriteCombinations.Equation4287_implies_Equation4340 at h
    apply RewriteHypothesis.Equation4340_implies_Equation4284 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq4284]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1892_implies_Equation1902 (G: Type _) [Magma G] (h: Equation1892 G) : Equation1902 G := by
  have eq4314 (x y : G) : x ◇ (y ◇ x) = x ◇ (y ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation1892_implies_Equation4356 at h
    apply Apply.Equation4356_implies_Equation4353 at h
    apply RewriteCombinations.Equation4353_implies_Equation4379 at h
    apply Apply.Equation4379_implies_Equation4375 at h
    apply Apply.Equation4375_implies_Equation4302 at h
    apply Apply.Equation4302_implies_Equation4292 at h
    apply RewriteCombinations.Equation4292_implies_Equation4298 at h
    apply SimpleRewrites.Equation4298_implies_Equation4271 at h
    apply RewriteCombinations.Equation4271_implies_Equation4361 at h
    apply Apply.Equation4361_implies_Equation4289 at h
    apply RewriteCombinations.Equation4289_implies_Equation4318 at h
    apply Apply.Equation4318_implies_Equation4314 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq4314]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1892_implies_Equation2132 (G: Type _) [Magma G] (h: Equation1892 G) : Equation2132 G := by
  have eq4470 (x y : G) : x ◇ (y ◇ y) = (x ◇ x) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation1892_implies_Equation4505 at h
    apply Apply.Equation4505_implies_Equation4478 at h
    apply Apply.Equation4478_implies_Equation4471 at h
    apply Apply.Equation4471_implies_Equation4470 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4470]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1892_implies_Equation2105 (G: Type _) [Magma G] (h: Equation1892 G) : Equation2105 G := by
  have eq4472 (x y : G) : x ◇ (y ◇ y) = (x ◇ y) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation1892_implies_Equation4505 at h
    apply Apply.Equation4505_implies_Equation4478 at h
    apply Apply.Equation4478_implies_Equation4474 at h
    apply Apply.Equation4474_implies_Equation4472 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4472]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1892_implies_Equation2095 (G: Type _) [Magma G] (h: Equation1892 G) : Equation2095 G := by
  have eq4473 (x y : G) : x ◇ (y ◇ y) = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation1892_implies_Equation4505 at h
    apply Apply.Equation4505_implies_Equation4478 at h
    apply Apply.Equation4478_implies_Equation4474 at h
    apply Apply.Equation4474_implies_Equation4473 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4473]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1899_implies_Equation1889 (G: Type _) [Magma G] (h: Equation1899 G) : Equation1889 G := by
  have eq4314 (x y : G) : x ◇ (y ◇ x) = x ◇ (y ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation1899_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4177 at h
    apply Apply.Equation4177_implies_Equation4174 at h
    apply NthRewrites.Equation4174_implies_Equation4510 at h
    apply RewriteGoal.Equation4510_implies_Equation4357 at h
    apply Apply.Equation4357_implies_Equation4339 at h
    apply RewriteHypothesis.Equation4339_implies_Equation4314 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4314]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1903_implies_Equation2106 (G: Type _) [Magma G] (h: Equation1903 G) : Equation2106 G := by
  have eq4435 (x y : G) : x ◇ (y ◇ x) = (x ◇ y) ◇ x := by
    apply Apply.Equation1903_implies_Equation1899 at h
    apply RewriteHypothesisAndGoal.Equation1899_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation337 at h
    apply Apply.Equation337_implies_Equation335 at h
    apply NthRewrites.Equation335_implies_Equation4435 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4435]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1911_implies_Equation2114 (G: Type _) [Magma G] (h: Equation1911 G) : Equation2114 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation1911_implies_Equation1889 at h
    apply RewriteHypothesisAndGoal.Equation1889_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4512 y]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1915_implies_Equation2118 (G: Type _) [Magma G] (h: Equation1915 G) : Equation2118 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation1915_implies_Equation1899 at h
    apply RewriteHypothesisAndGoal.Equation1899_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4512 y]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1918_implies_Equation2121 (G: Type _) [Magma G] (h: Equation1918 G) : Equation2121 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation1918_implies_Equation4582 at h
    apply Subgraph.Equation4582_implies_Equation4522 at h
    apply Subgraph.Equation4522_implies_Equation4513 at h
    apply Subgraph.Equation4513_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4512 y]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1920_implies_Equation2123 (G: Type _) [Magma G] (h: Equation1920 G) : Equation2123 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation1920_implies_Equation1918 at h
    apply RewriteHypothesisAndGoal.Equation1918_implies_Equation4582 at h
    apply Subgraph.Equation4582_implies_Equation4522 at h
    apply Subgraph.Equation4522_implies_Equation4513 at h
    apply Subgraph.Equation4513_implies_Equation4512 at h
    apply h
  intro x y z w u
  symm
  nth_rewrite 2 [← eq4512]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1930_implies_Equation1893 (G: Type _) [Magma G] (h: Equation1930 G) : Equation1893 G := by
  have eq4284 (x y : G) : x ◇ (x ◇ y) = x ◇ (y ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation1930_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply Run1.Equation314_implies_Equation317 at h
    apply RewriteCombinations.Equation317_implies_Equation4312 at h
    apply Apply.Equation4312_implies_Equation4288 at h
    apply Apply.Equation4288_implies_Equation4284 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4284]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1969_implies_Equation2172 (G: Type _) [Magma G] (h: Equation1969 G) : Equation2172 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation1969_implies_Equation4582 at h
    apply Subgraph.Equation4582_implies_Equation4522 at h
    apply Subgraph.Equation4522_implies_Equation4513 at h
    apply Subgraph.Equation4513_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 2 [← eq4512]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1972_implies_Equation2175 (G: Type _) [Magma G] (h: Equation1972 G) : Equation2175 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation1972_implies_Equation4582 at h
    apply Subgraph.Equation4582_implies_Equation4522 at h
    apply Subgraph.Equation4522_implies_Equation4513 at h
    apply Subgraph.Equation4513_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 2 [← eq4512]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1978_implies_Equation1995 (G: Type _) [Magma G] (h: Equation1978 G) : Equation1995 G := by
  have eq4314 (x y : G) : x ◇ (y ◇ x) = x ◇ (y ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation1978_implies_Equation319 at h
    apply RewriteCombinations.Equation319_implies_Equation4337 at h
    apply Apply.Equation4337_implies_Equation4318 at h
    apply Apply.Equation4318_implies_Equation4314 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4314]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2106_implies_Equation1930 (G: Type _) [Magma G] (h: Equation2106 G) : Equation1930 G := by
  have eq4398 (x y : G) : x ◇ (x ◇ y) = (x ◇ y) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation2106_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3376 at h
    apply Apply.Equation3376_implies_Equation3364 at h
    apply NthRewrites.Equation3364_implies_Equation4531 at h
    apply Apply.Equation4531_implies_Equation4398 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4398]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2120_implies_Equation1917 (G: Type _) [Magma G] (h: Equation2120 G) : Equation1917 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation2120_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4512 y]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2177_implies_Equation1974 (G: Type _) [Magma G] (h: Equation2177 G) : Equation1974 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation2177_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w u
  symm
  nth_rewrite 1 [eq4512 y]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2298_implies_Equation2523 (G: Type _) [Magma G] (h: Equation2298 G) : Equation2523 G := by
  have eq4399 (x y : G) : x ◇ (x ◇ y) = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2298_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4582 at h
    apply Apply.Equation4582_implies_Equation4431 at h
    apply Apply.Equation4431_implies_Equation4404 at h
    apply Apply.Equation4404_implies_Equation4400 at h
    apply Apply.Equation4400_implies_Equation4399 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4399]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2312_implies_Equation2523 (G: Type _) [Magma G] (h: Equation2312 G) : Equation2523 G := by
  have eq4436 (x y : G) : x ◇ (y ◇ x) = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2312_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3383 at h
    apply NthRewrites.Equation3383_implies_Equation4545 at h
    apply Apply.Equation4545_implies_Equation4436 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4436]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2320_implies_Equation2523 (G: Type _) [Magma G] (h: Equation2320 G) : Equation2523 G := by
  have eq4473 (x y : G) : x ◇ (y ◇ y) = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2320_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply Apply.Equation4512_implies_Equation4473 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4473]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2324_implies_Equation2527 (G: Type _) [Magma G] (h: Equation2324 G) : Equation2527 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2324_implies_Equation2312 at h
    apply RewriteHypothesisAndGoal.Equation2312_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 2 [← eq4512]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2325_implies_Equation2528 (G: Type _) [Magma G] (h: Equation2325 G) : Equation2528 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2325_implies_Equation2298 at h
    apply RewriteHypothesisAndGoal.Equation2298_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 2 [← eq4512]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2329_implies_Equation30 (G: Type _) [Magma G] (h: Equation2329 G) : Equation30 G := by
  have eq3309 (x y : G) : x ◇ y = x ◇ (x ◇ (y ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation2329_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3857 at h
    apply Apply.Equation3857_implies_Equation3852 at h
    apply Apply.Equation3852_implies_Equation3828 at h
    apply RewriteCombinations.Equation3828_implies_Equation3842 at h
    apply Apply.Equation3842_implies_Equation3773 at h
    apply Apply.Equation3773_implies_Equation3762 at h
    apply RewriteCombinations.Equation3762_implies_Equation3811 at h
    apply RewriteCombinations.Equation3811_implies_Equation329 at h
    apply RewriteHypothesis.Equation329_implies_Equation3338 at h
    apply Apply.Equation3338_implies_Equation3330 at h
    apply Apply.Equation3330_implies_Equation3309 at h
    apply h
  intro x y z
  symm
  nth_rewrite 2 [eq3309]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2332_implies_Equation30 (G: Type _) [Magma G] (h: Equation2332 G) : Equation30 G := by
  have eq3308 (x y : G) : x ◇ y = x ◇ (x ◇ (y ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation2332_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3383 at h
    apply Apply.Equation3383_implies_Equation3308 at h
    apply h
  intro x y z
  symm
  nth_rewrite 2 [eq3308]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2339_implies_Equation30 (G: Type _) [Magma G] (h: Equation2339 G) : Equation30 G := by
  have eq3306 (x y : G) : x ◇ y = x ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation2339_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply NthRewrites.Equation3398_implies_Equation3810 at h
    apply NthRewrites.Equation3810_implies_Equation3334 at h
    apply Apply.Equation3334_implies_Equation3306 at h
    apply h
  intro x y z
  symm
  nth_rewrite 2 [eq3306]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2350_implies_Equation2553 (G: Type _) [Magma G] (h: Equation2350 G) : Equation2553 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2350_implies_Equation2329 at h
    apply RewriteHypothesisAndGoal.Equation2329_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 2 [← eq4512]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2366_implies_Equation2603 (G: Type _) [Magma G] (h: Equation2366 G) : Equation2603 G := by
  have eq4470 (x y : G) : x ◇ (y ◇ y) = (x ◇ x) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2366_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation334 at h
    apply Apply.Equation334_implies_Equation3351 at h
    apply Apply.Equation3351_implies_Equation3344 at h
    apply RewriteHypothesisAndGoal.Equation3344_implies_Equation332 at h
    apply Run1.Equation332_implies_Equation4470 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4470]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2374_implies_Equation2603 (G: Type _) [Magma G] (h: Equation2374 G) : Equation2603 G := by
  have eq4433 (x y : G) : x ◇ (y ◇ x) = (x ◇ x) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2374_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4582 at h
    apply Subgraph.Equation4582_implies_Equation4522 at h
    apply Apply.Equation4522_implies_Equation4441 at h
    apply Apply.Equation4441_implies_Equation4434 at h
    apply Apply.Equation4434_implies_Equation4433 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4433]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2378_implies_Equation2581 (G: Type _) [Magma G] (h: Equation2378 G) : Equation2581 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2378_implies_Equation2366 at h
    apply RewriteHypothesisAndGoal.Equation2366_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 2 [← eq4512]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2379_implies_Equation2582 (G: Type _) [Magma G] (h: Equation2379 G) : Equation2582 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2379_implies_Equation2298 at h
    apply RewriteHypothesisAndGoal.Equation2298_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 2 [← eq4512]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2400_implies_Equation2603 (G: Type _) [Magma G] (h: Equation2400 G) : Equation2603 G := by
  have eq4396 (x y : G) : x ◇ (x ◇ y) = (x ◇ x) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2400_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply Apply.Equation4512_implies_Equation4396 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4396]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2417_implies_Equation2620 (G: Type _) [Magma G] (h: Equation2417 G) : Equation2620 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2417_implies_Equation2366 at h
    apply RewriteHypothesisAndGoal.Equation2366_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4512 z]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2418_implies_Equation2621 (G: Type _) [Magma G] (h: Equation2418 G) : Equation2621 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2418_implies_Equation2312 at h
    apply RewriteHypothesisAndGoal.Equation2312_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4512 z]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2501_implies_Equation226 (G: Type _) [Magma G] (h: Equation2501 G) : Equation226 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2501_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation387 at h
    apply RewriteHypothesis.Equation387_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation375 at h
    apply h
  intro x y z
  symm
  nth_rewrite 3 [eq375]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2515_implies_Equation2501 (G: Type _) [Magma G] (h: Equation2515 G) : Equation2501 G := by
  have eq4598 (x y : G) : (x ◇ x) ◇ y = (x ◇ y) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation2515_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4582 at h
    apply Apply.Equation4582_implies_Equation4431 at h
    apply Apply.Equation4431_implies_Equation4404 at h
    apply Apply.Equation4404_implies_Equation4384 at h
    apply RewriteHypothesis.Equation4384_implies_Equation4676 at h
    apply Apply.Equation4676_implies_Equation4673 at h
    apply Apply.Equation4673_implies_Equation4598 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq4598]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2523_implies_Equation2515 (G: Type _) [Magma G] (h: Equation2523 G) : Equation2515 G := by
  have eq4629 (x y : G) : (x ◇ y) ◇ x = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2523_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4163 at h
    apply Apply.Equation4163_implies_Equation4159 at h
    apply NthRewrites.Equation4159_implies_Equation4407 at h
    apply RewriteHypothesis.Equation4407_implies_Equation4672 at h
    apply Apply.Equation4672_implies_Equation4654 at h
    apply RewriteHypothesis.Equation4654_implies_Equation4629 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq4629]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2527_implies_Equation2324 (G: Type _) [Magma G] (h: Equation2527 G) : Equation2324 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2527_implies_Equation2515 at h
    apply RewriteHypothesisAndGoal.Equation2515_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4512 x z]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2532_implies_Equation30 (G: Type _) [Magma G] (h: Equation2532 G) : Equation30 G := by
  have eq3512 (x y : G) : x ◇ y = x ◇ ((x ◇ y) ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation2532_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3383 at h
    apply NthRewrites.Equation3383_implies_Equation3587 at h
    apply Apply.Equation3587_implies_Equation3512 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq3512 y]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2535_implies_Equation30 (G: Type _) [Magma G] (h: Equation2535 G) : Equation30 G := by
  have eq3511 (x y : G) : x ◇ y = x ◇ ((x ◇ y) ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation2535_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3620 at h
    apply NthRewrites.Equation3620_implies_Equation3534 at h
    apply Apply.Equation3534_implies_Equation3511 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq3511 y]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2539_implies_Equation2336 (G: Type _) [Magma G] (h: Equation2539 G) : Equation2336 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2539_implies_Equation2532 at h
    apply RewriteHypothesisAndGoal.Equation2532_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 2 [eq4512]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2542_implies_Equation30 (G: Type _) [Magma G] (h: Equation2542 G) : Equation30 G := by
  have eq3509 (x y : G) : x ◇ y = x ◇ ((x ◇ x) ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation2542_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4176 at h
    apply NthRewrites.Equation4176_implies_Equation3537 at h
    apply Apply.Equation3537_implies_Equation3509 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq3509 y]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2569_implies_Equation240 (G: Type _) [Magma G] (h: Equation2569 G) : Equation240 G := by
  have eq378 (x y : G) : x ◇ y = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2569_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3857 at h
    apply Apply.Equation3857_implies_Equation3852 at h
    apply Apply.Equation3852_implies_Equation3828 at h
    apply RewriteCombinations.Equation3828_implies_Equation3842 at h
    apply Apply.Equation3842_implies_Equation3773 at h
    apply Apply.Equation3773_implies_Equation3762 at h
    apply RewriteCombinations.Equation3762_implies_Equation3811 at h
    apply RewriteCombinations.Equation3811_implies_Equation3744 at h
    apply Subgraph.Equation3744_implies_Equation381 at h
    apply Apply.Equation381_implies_Equation378 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq378 z]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2577_implies_Equation2569 (G: Type _) [Magma G] (h: Equation2577 G) : Equation2569 G := by
  have eq4629 (x y : G) : (x ◇ y) ◇ x = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2577_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4163 at h
    apply Apply.Equation4163_implies_Equation4159 at h
    apply NthRewrites.Equation4159_implies_Equation4407 at h
    apply RewriteHypothesis.Equation4407_implies_Equation4672 at h
    apply Apply.Equation4672_implies_Equation4654 at h
    apply RewriteHypothesis.Equation4654_implies_Equation4629 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4629]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2581_implies_Equation2378 (G: Type _) [Magma G] (h: Equation2581 G) : Equation2378 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2581_implies_Equation2569 at h
    apply RewriteHypothesisAndGoal.Equation2569_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4512 z]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2603_implies_Equation2577 (G: Type _) [Magma G] (h: Equation2603 G) : Equation2577 G := by
  have eq4598 (x y : G) : (x ◇ x) ◇ y = (x ◇ y) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation2603_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4582 at h
    apply Apply.Equation4582_implies_Equation4431 at h
    apply Apply.Equation4431_implies_Equation4404 at h
    apply Apply.Equation4404_implies_Equation4384 at h
    apply RewriteHypothesis.Equation4384_implies_Equation4676 at h
    apply Apply.Equation4676_implies_Equation4673 at h
    apply Apply.Equation4673_implies_Equation4598 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4598]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2620_implies_Equation2417 (G: Type _) [Magma G] (h: Equation2620 G) : Equation2417 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2620_implies_Equation2569 at h
    apply RewriteHypothesisAndGoal.Equation2569_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4512 z]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2711_implies_Equation30 (G: Type _) [Magma G] (h: Equation2711 G) : Equation30 G := by
  have eq3721 (x y : G) : x ◇ y = (x ◇ y) ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation2711_implies_Equation3849 at h
    apply Constant.Equation3849_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply NthRewrites.Equation3398_implies_Equation3810 at h
    apply Apply.Equation3810_implies_Equation3721 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq3721 y]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2735_implies_Equation30 (G: Type _) [Magma G] (h: Equation2735 G) : Equation30 G := by
  have eq3715 (x y : G) : x ◇ y = (x ◇ x) ◇ (y ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation2735_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation387 at h
    apply RewriteHypothesis.Equation387_implies_Equation3715 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq3715 y]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2738_implies_Equation30 (G: Type _) [Magma G] (h: Equation2738 G) : Equation30 G := by
  have eq3714 (x y : G) : x ◇ y = (x ◇ x) ◇ (y ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation2738_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3792 at h
    apply Apply.Equation3792_implies_Equation3716 at h
    apply Apply.Equation3716_implies_Equation3714 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq3714 y]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2745_implies_Equation30 (G: Type _) [Magma G] (h: Equation2745 G) : Equation30 G := by
  have eq3712 (x y : G) : x ◇ y = (x ◇ x) ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation2745_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3857 at h
    apply Apply.Equation3857_implies_Equation3852 at h
    apply Apply.Equation3852_implies_Equation3828 at h
    apply RewriteCombinations.Equation3828_implies_Equation3842 at h
    apply Apply.Equation3842_implies_Equation3773 at h
    apply Apply.Equation3773_implies_Equation3762 at h
    apply RewriteCombinations.Equation3762_implies_Equation3811 at h
    apply RewriteCombinations.Equation3811_implies_Equation3744 at h
    apply Apply.Equation3744_implies_Equation3718 at h
    apply Apply.Equation3718_implies_Equation3712 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq3712 y]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2904_implies_Equation30 (G: Type _) [Magma G] (h: Equation2904 G) : Equation30 G := by
  have eq3927 (x y : G) : x ◇ y = (x ◇ (y ◇ y)) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation2904_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4017 at h
    apply Apply.Equation4017_implies_Equation3930 at h
    apply Apply.Equation3930_implies_Equation3927 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq3927 y]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2908_implies_Equation2918 (G: Type _) [Magma G] (h: Equation2908 G) : Equation2918 G := by
  have eq4314 (x y : G) : x ◇ (y ◇ x) = x ◇ (y ◇ y) := by
    apply Apply.Equation2908_implies_Equation2904 at h
    apply RewriteHypothesisAndGoal.Equation2904_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4177 at h
    apply Apply.Equation4177_implies_Equation4174 at h
    apply NthRewrites.Equation4174_implies_Equation4510 at h
    apply RewriteGoal.Equation4510_implies_Equation4357 at h
    apply Apply.Equation4357_implies_Equation4339 at h
    apply RewriteHypothesis.Equation4339_implies_Equation4314 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4314]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2908_implies_Equation3148 (G: Type _) [Magma G] (h: Equation2908 G) : Equation3148 G := by
  have eq4470 (x y : G) : x ◇ (y ◇ y) = (x ◇ x) ◇ y := by
    apply Apply.Equation2908_implies_Equation2904 at h
    apply RewriteHypothesisAndGoal.Equation2904_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation334 at h
    apply Apply.Equation334_implies_Equation3351 at h
    apply Apply.Equation3351_implies_Equation3344 at h
    apply RewriteHypothesisAndGoal.Equation3344_implies_Equation332 at h
    apply Run1.Equation332_implies_Equation4470 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4470]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2933_implies_Equation3136 (G: Type _) [Magma G] (h: Equation2933 G) : Equation3136 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation2933_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4512 y]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2935_implies_Equation3138 (G: Type _) [Magma G] (h: Equation2935 G) : Equation3138 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2935_implies_Equation2933 at h
    apply RewriteHypothesisAndGoal.Equation2933_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w u
  symm
  nth_rewrite 1 [← eq4512 y]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2980_implies_Equation3183 (G: Type _) [Magma G] (h: Equation2980 G) : Equation3183 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2980_implies_Equation2904 at h
    apply RewriteHypothesisAndGoal.Equation2904_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4512 y]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2987_implies_Equation3190 (G: Type _) [Magma G] (h: Equation2987 G) : Equation3190 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation2987_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4512 y]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2989_implies_Equation3192 (G: Type _) [Magma G] (h: Equation2989 G) : Equation3192 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2989_implies_Equation2987 at h
    apply RewriteHypothesisAndGoal.Equation2987_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w u
  symm
  nth_rewrite 1 [← eq4512 y]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3110_implies_Equation3147 (G: Type _) [Magma G] (h: Equation3110 G) : Equation3147 G := by
  have eq4599 (x y : G) : (x ◇ x) ◇ y = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation3110_implies_Equation4671 at h
    apply RewriteHypothesis.Equation4671_implies_Equation4627 at h
    apply Apply.Equation4627_implies_Equation4603 at h
    apply Apply.Equation4603_implies_Equation4599 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq4599]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3110_implies_Equation3120 (G: Type _) [Magma G] (h: Equation3110 G) : Equation3120 G := by
  have eq4629 (x y : G) : (x ◇ y) ◇ x = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation3110_implies_Equation4671 at h
    apply Apply.Equation4671_implies_Equation4596 at h
    apply RewriteCombinations.Equation4596_implies_Equation4644 at h
    apply RewriteCombinations.Equation4644_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4628 at h
    apply Apply.Equation4628_implies_Equation4624 at h
    apply RewriteGoal.Equation4624_implies_Equation4621 at h
    apply SimpleRewrites.Equation4621_implies_Equation4600 at h
    apply RewriteCombinations.Equation4600_implies_Equation4657 at h
    apply RewriteCombinations.Equation4657_implies_Equation4676 at h
    apply Apply.Equation4676_implies_Equation4604 at h
    apply RewriteCombinations.Equation4604_implies_Equation4633 at h
    apply Apply.Equation4633_implies_Equation4629 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq4629]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3111_implies_Equation3148 (G: Type _) [Magma G] (h: Equation3111 G) : Equation3148 G := by
  have eq4599 (x y : G) : (x ◇ x) ◇ y = (x ◇ y) ◇ y := by
    apply Apply.Equation3111_implies_Equation3110 at h
    apply RewriteHypothesisAndGoal.Equation3110_implies_Equation4671 at h
    apply RewriteHypothesis.Equation4671_implies_Equation4627 at h
    apply Apply.Equation4627_implies_Equation4603 at h
    apply Apply.Equation4603_implies_Equation4599 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4599]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3121_implies_Equation3111 (G: Type _) [Magma G] (h: Equation3121 G) : Equation3111 G := by
  have eq4629 (x y : G) : (x ◇ y) ◇ x = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation3121_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4628 at h
    apply Apply.Equation4628_implies_Equation4624 at h
    apply RewriteGoal.Equation4624_implies_Equation4621 at h
    apply SimpleRewrites.Equation4621_implies_Equation4600 at h
    apply RewriteCombinations.Equation4600_implies_Equation4657 at h
    apply RewriteCombinations.Equation4657_implies_Equation4676 at h
    apply Apply.Equation4676_implies_Equation4604 at h
    apply RewriteCombinations.Equation4604_implies_Equation4633 at h
    apply Apply.Equation4633_implies_Equation4629 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4629]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3125_implies_Equation2922 (G: Type _) [Magma G] (h: Equation3125 G) : Equation2922 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation3125_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4512]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3129_implies_Equation2926 (G: Type _) [Magma G] (h: Equation3129 G) : Equation2926 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation3129_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4512]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3133_implies_Equation2930 (G: Type _) [Magma G] (h: Equation3133 G) : Equation2930 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation3133_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4512]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3136_implies_Equation2933 (G: Type _) [Magma G] (h: Equation3136 G) : Equation2933 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation3136_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4512]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3137_implies_Equation2934 (G: Type _) [Magma G] (h: Equation3137 G) : Equation2934 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation3137_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4512]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3148_implies_Equation3121 (G: Type _) [Magma G] (h: Equation3148 G) : Equation3121 G := by
  have eq4598 (x y : G) : (x ◇ x) ◇ y = (x ◇ y) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation3148_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4679 at h
    apply Apply.Equation4679_implies_Equation4598 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4598]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3162_implies_Equation293 (G: Type _) [Magma G] (h: Equation3162 G) : Equation293 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation3162_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation387 at h
    apply RewriteHypothesis.Equation387_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation375 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq375 y]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3187_implies_Equation2984 (G: Type _) [Magma G] (h: Equation3187 G) : Equation2984 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation3187_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4512]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3189_implies_Equation2986 (G: Type _) [Magma G] (h: Equation3189 G) : Equation2986 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation3189_implies_Equation4582 at h
    apply Subgraph.Equation4582_implies_Equation4522 at h
    apply Subgraph.Equation4522_implies_Equation4513 at h
    apply Subgraph.Equation4513_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4512]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3192_implies_Equation2989 (G: Type _) [Magma G] (h: Equation3192 G) : Equation2989 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation3192_implies_Equation3189 at h
    apply RewriteHypothesisAndGoal.Equation3189_implies_Equation4582 at h
    apply Subgraph.Equation4582_implies_Equation4522 at h
    apply Subgraph.Equation4522_implies_Equation4513 at h
    apply Subgraph.Equation4513_implies_Equation4512 at h
    apply h
  intro x y z w u
  symm
  nth_rewrite 1 [eq4512]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3213_implies_Equation3162 (G: Type _) [Magma G] (h: Equation3213 G) : Equation3162 G := by
  have eq4599 (x y : G) : (x ◇ x) ◇ y = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation3213_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4582 at h
    apply Apply.Equation4582_implies_Equation4431 at h
    apply Apply.Equation4431_implies_Equation4404 at h
    apply Apply.Equation4404_implies_Equation4402 at h
    apply RewriteHypothesis.Equation4402_implies_Equation4675 at h
    apply Apply.Equation4675_implies_Equation4655 at h
    apply RewriteHypothesis.Equation4655_implies_Equation4599 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4599]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3229_implies_Equation3026 (G: Type _) [Magma G] (h: Equation3229 G) : Equation3026 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation3229_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4512]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3364_implies_Equation3567 (G: Type _) [Magma G] (h: Equation3364 G) : Equation3567 G := by
  have eq4435 (x y : G) : x ◇ (y ◇ x) = (x ◇ y) ◇ x := by
    apply NthRewrites.Equation3364_implies_Equation3370 at h
    apply Apply.Equation3370_implies_Equation3355 at h
    apply NthRewrites.Equation3355_implies_Equation4435 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4435]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3392_implies_Equation45 (G: Type _) [Magma G] (h: Equation3392 G) : Equation45 G := by
  have eq3338 (x y z w : G) : x ◇ y = x ◇ (z ◇ (w ◇ y)) := by
    apply Apply.Equation3392_implies_Equation3312 at h
    apply NthRewrites.Equation3312_implies_Equation3338 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq3338]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3436_implies_Equation3446 (G: Type _) [Magma G] (h: Equation3436 G) : Equation3446 G := by
  have eq4284 (x y : G) : x ◇ (x ◇ y) = x ◇ (y ◇ y) := by
    apply Apply.Equation3436_implies_Equation3401 at h
    apply Apply.Equation3401_implies_Equation3356 at h
    apply NthRewrites.Equation3356_implies_Equation3367 at h
    apply RewriteCombinations.Equation3367_implies_Equation3330 at h
    apply NthRewrites.Equation3330_implies_Equation4340 at h
    apply RewriteHypothesis.Equation4340_implies_Equation4284 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4284]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3567_implies_Equation3370 (G: Type _) [Magma G] (h: Equation3567 G) : Equation3370 G := by
  have eq4398 (x y : G) : x ◇ (x ◇ y) = (x ◇ y) ◇ x := by
    apply NthRewrites.Equation3567_implies_Equation4531 at h
    apply Apply.Equation4531_implies_Equation4398 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq4398]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4159_implies_Equation4156 (G: Type _) [Magma G] (h: Equation4159 G) : Equation4156 G := by
  have eq4629 (x y : G) : (x ◇ y) ◇ x = (x ◇ y) ◇ y := by
    apply NthRewrites.Equation4159_implies_Equation4407 at h
    apply RewriteHypothesis.Equation4407_implies_Equation4672 at h
    apply Apply.Equation4672_implies_Equation4654 at h
    apply RewriteHypothesis.Equation4654_implies_Equation4629 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4629]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4197_implies_Equation3994 (G: Type _) [Magma G] (h: Equation4197 G) : Equation3994 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply NthRewrites.Equation4197_implies_Equation4512 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq4512]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4216_implies_Equation4013 (G: Type _) [Magma G] (h: Equation4216 G) : Equation4013 G := by
  have eq4435 (x y : G) : x ◇ (y ◇ x) = (x ◇ y) ◇ x := by
    apply NthRewrites.Equation4216_implies_Equation4182 at h
    apply Apply.Equation4182_implies_Equation4154 at h
    apply NthRewrites.Equation4154_implies_Equation4435 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq4435]
  symm
  apply h
  repeat assumption
