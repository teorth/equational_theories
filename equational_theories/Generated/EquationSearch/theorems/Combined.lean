import equational_theories.Generated.SimpleRewrites
import equational_theories.Generated.Constant
import equational_theories.Generated.Singleton
import equational_theories.Generated.TrivialBruteforce
import equational_theories.Generated.FinitePoly
import equational_theories.Generated.VampireProven
import equational_theories.Generated.MagmaEgg.small
import equational_theories.Subgraph

@[equational_result]
theorem Equation332_implies_Equation4343 (G: Type _) [Magma G] (h: Equation332 G) : Equation4343 G := by
  have eq326 (x y : G) : x ◇ y = x ◇ (y ◇ y) := by
    apply RewriteHypothesis.Equation332_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation326 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [← eq326]
  apply h
@[equational_result]
theorem Equation9_implies_Equation308 (G: Type _) [Magma G] (h: Equation9 G) : Equation308 G := by
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesis.Equation9_implies_Equation3320 at h
    apply Apply.Equation3320_implies_Equation3254 at h
    apply Apply.Equation3254_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesis.Equation9_implies_Equation1024 at h
    apply Apply.Equation1024_implies_Equation1021 at h
    apply Equation1021_implies_Equation47 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
@[equational_result]
theorem Equation24_implies_Equation27 (G: Type _) [Magma G] (h: Equation24 G) : Equation27 G := by
  have eq4602 (x y z : G) : (x ◇ x) ◇ y = (x ◇ z) ◇ y := by
    apply RewriteHypothesis.Equation24_implies_Equation4124 at h
    apply NthRewrites.Equation4124_implies_Equation4150 at h
    apply Apply.Equation4150_implies_Equation4142 at h
    apply RewriteHypothesisAndGoal.Equation4142_implies_Equation4655 at h
    apply RewriteCombinations.Equation4655_implies_Equation4602 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [← eq4602]
  symm
  apply h
@[equational_result]
theorem Equation29_implies_Equation4458 (G: Type _) [Magma G] (h: Equation29 G) : Equation4458 G := by
  have eq14 (x y : G) : x = y ◇ (x ◇ y) := by
    apply Subgraph.Equation29_implies_Equation14 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq14]
  apply h
@[equational_result]
theorem Equation171_implies_Equation85 (G: Type _) [Magma G] (h: Equation171 G) : Equation85 G := by
  have eq3291 (x y z w : G) : x ◇ x = y ◇ (z ◇ (x ◇ w)) := by
    apply RewriteHypothesisAndGoal.Equation171_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3434 at h
    apply SimpleRewrites.Equation3434_implies_Equation3291 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply RewriteHypothesisAndGoal.Equation171_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3796 at h
    apply Apply.Equation3796_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3291]
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation116 (G: Type _) [Magma G] (h: Equation171 G) : Equation116 G := by
  have eq3473 (x y z : G) : x ◇ x = y ◇ ((x ◇ x) ◇ z) := by
    apply RewriteHypothesisAndGoal.Equation171_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3602 at h
    apply Apply.Equation3602_implies_Equation3473 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply RewriteHypothesisAndGoal.Equation171_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3796 at h
    apply Apply.Equation3796_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3473]
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation278_implies_Equation305 (G: Type _) [Magma G] (h: Equation278 G) : Equation305 G := by
  have eq258 (x y : G) : x = ((x ◇ x) ◇ y) ◇ y := by
    apply Apply.Equation278_implies_Equation258 at h
    apply h
  have eq4599 (x y : G) : (x ◇ x) ◇ y = (x ◇ y) ◇ y := by
    apply Apply.Equation278_implies_Equation3191 at h
    apply Apply.Equation3191_implies_Equation3110 at h
    apply Equation3110_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation38 at h
    apply RewriteGoal.Equation38_implies_Equation4602 at h
    apply Apply.Equation4602_implies_Equation4599 at h
    apply h
  have eq270 (x y : G) : x = ((y ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation278_implies_Equation270 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq258 x]
  nth_rewrite 1 [eq4599 x]
  nth_rewrite 1 [← eq270]
  apply h
@[equational_result]
theorem Equation314_implies_Equation321 (G: Type _) [Magma G] (h: Equation314 G) : Equation321 G := by
  have eq40 (x y : G) : x ◇ x = y ◇ y := by
    apply RewriteCombinations.Equation314_implies_Equation3291 at h
    apply Apply.Equation3291_implies_Equation3289 at h
    apply NthRewrites.Equation3289_implies_Equation3699 at h
    apply RewriteHypothesisAndGoal.Equation3699_implies_Equation40 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [← eq40]
  apply h
@[equational_result]
theorem Equation314_implies_Equation311 (G: Type _) [Magma G] (h: Equation314 G) : Equation311 G := by
  have eq4362 (x y z : G) : x ◇ (y ◇ z) = y ◇ (x ◇ z) := by
    apply RewriteCombinations.Equation314_implies_Equation4349 at h
    apply SimpleRewrites.Equation4349_implies_Equation4348 at h
    apply RewriteGoal.Equation4348_implies_Equation4278 at h
    apply RewriteCombinations.Equation4278_implies_Equation4362 at h
    apply h
  intro x; repeat intro
  symm
  nth_rewrite 1 [eq4362]
  symm
  apply h
@[equational_result]
theorem Equation314_implies_Equation317 (G: Type _) [Magma G] (h: Equation314 G) : Equation317 G := by
  have eq4277 (x y z : G) : x ◇ (x ◇ x) = y ◇ (y ◇ z) := by
    apply RewriteHypothesis.Equation314_implies_Equation4375 at h
    apply Apply.Equation4375_implies_Equation4302 at h
    apply Apply.Equation4302_implies_Equation4301 at h
    apply NthRewrites.Equation4301_implies_Equation4277 at h
    apply h
  have eq4274 (x y z : G) : x ◇ (x ◇ x) = y ◇ (x ◇ z) := by
    apply RewriteCombinations.Equation314_implies_Equation4349 at h
    apply SimpleRewrites.Equation4349_implies_Equation4274 at h
    apply h
  intro x; repeat intro
  symm
  nth_rewrite 1 [← eq4277]
  nth_rewrite 1 [eq4274]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation314_implies_Equation318 (G: Type _) [Magma G] (h: Equation314 G) : Equation318 G := by
  have eq4278 (x y z : G) : x ◇ (x ◇ x) = y ◇ (z ◇ x) := by
    apply RewriteCombinations.Equation314_implies_Equation4349 at h
    apply SimpleRewrites.Equation4349_implies_Equation4348 at h
    apply RewriteGoal.Equation4348_implies_Equation4278 at h
    apply h
  have eq4274 (x y z : G) : x ◇ (x ◇ x) = y ◇ (x ◇ z) := by
    apply RewriteCombinations.Equation314_implies_Equation4349 at h
    apply SimpleRewrites.Equation4349_implies_Equation4274 at h
    apply h
  intro x; repeat intro
  symm
  nth_rewrite 1 [← eq4278]
  nth_rewrite 1 [eq4274]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation314_implies_Equation319 (G: Type _) [Magma G] (h: Equation314 G) : Equation319 G := by
  have eq4279 (x y z : G) : x ◇ (x ◇ x) = y ◇ (z ◇ y) := by
    apply Equation314_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation319 at h
    apply RewriteCombinations.Equation319_implies_Equation4337 at h
    apply RewriteHypothesis.Equation4337_implies_Equation4279 at h
    apply h
  have eq4274 (x y z : G) : x ◇ (x ◇ x) = y ◇ (x ◇ z) := by
    apply RewriteCombinations.Equation314_implies_Equation4349 at h
    apply SimpleRewrites.Equation4349_implies_Equation4274 at h
    apply h
  intro x; repeat intro
  symm
  nth_rewrite 1 [← eq4279]
  nth_rewrite 1 [eq4274]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation338_implies_Equation398 (G: Type _) [Magma G] (h: Equation338 G) : Equation398 G := by
  have eq4456 (x y z : G) : x ◇ (y ◇ x) = (z ◇ y) ◇ x := by
    apply NthRewrites.Equation338_implies_Equation4562 at h
    apply Apply.Equation4562_implies_Equation4456 at h
    apply h
  have eq4323 (x y z : G) : x ◇ (y ◇ x) = y ◇ (z ◇ x) := by
    apply NthRewrites.Equation338_implies_Equation3351 at h
    apply Apply.Equation3351_implies_Equation3349 at h
    apply Equation3349_implies_Equation3451 at h
    apply Apply.Equation3451_implies_Equation3392 at h
    apply RewriteHypothesisAndGoal.Equation3392_implies_Equation4278 at h
    apply RewriteCombinations.Equation4278_implies_Equation4323 at h
    apply h
  have eq332 (x y : G) : x ◇ y = y ◇ (x ◇ x) := by
    apply Apply.Equation338_implies_Equation332 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq332]
  symm
  nth_rewrite 1 [← eq4456]
  nth_rewrite 1 [eq4323]
  symm
  nth_rewrite 1 [← eq332]
  apply h
  repeat assumption
@[equational_result]
theorem Equation366_implies_Equation373 (G: Type _) [Magma G] (h: Equation366 G) : Equation373 G := by
  have eq40 (x y : G) : x ◇ x = y ◇ y := by
    apply RewriteCombinations.Equation366_implies_Equation4089 at h
    apply Apply.Equation4089_implies_Equation4087 at h
    apply NthRewrites.Equation4087_implies_Equation3691 at h
    apply RewriteHypothesisAndGoal.Equation3691_implies_Equation40 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [← eq40]
  apply h
@[equational_result]
theorem Equation366_implies_Equation363 (G: Type _) [Magma G] (h: Equation366 G) : Equation363 G := by
  have eq4677 (x y z : G) : (x ◇ y) ◇ z = (y ◇ x) ◇ z := by
    apply RewriteCombinations.Equation366_implies_Equation4624 at h
    apply SimpleRewrites.Equation4624_implies_Equation4593 at h
    apply RewriteCombinations.Equation4593_implies_Equation4693 at h
    apply Apply.Equation4693_implies_Equation4677 at h
    apply h
  intro x; repeat intro
  symm
  nth_rewrite 1 [eq4677]
  symm
  apply h
@[equational_result]
theorem Equation366_implies_Equation370 (G: Type _) [Magma G] (h: Equation366 G) : Equation370 G := by
  have eq4593 (x y z : G) : (x ◇ x) ◇ x = (y ◇ z) ◇ x := by
    apply RewriteCombinations.Equation366_implies_Equation4624 at h
    apply SimpleRewrites.Equation4624_implies_Equation4593 at h
    apply h
  have eq4589 (x y z : G) : (x ◇ x) ◇ x = (y ◇ x) ◇ z := by
    apply RewriteCombinations.Equation366_implies_Equation4624 at h
    apply RewriteGoal.Equation4624_implies_Equation4621 at h
    apply SimpleRewrites.Equation4621_implies_Equation4589 at h
    apply h
  intro x; repeat intro
  symm
  nth_rewrite 1 [← eq4593]
  nth_rewrite 1 [eq4589]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation366_implies_Equation371 (G: Type _) [Magma G] (h: Equation366 G) : Equation371 G := by
  have eq4594 (x y z : G) : (x ◇ x) ◇ x = (y ◇ z) ◇ y := by
    apply Equation366_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation371 at h
    apply RewriteCombinations.Equation371_implies_Equation4626 at h
    apply Apply.Equation4626_implies_Equation4594 at h
    apply h
  have eq4589 (x y z : G) : (x ◇ x) ◇ x = (y ◇ x) ◇ z := by
    apply RewriteCombinations.Equation366_implies_Equation4624 at h
    apply RewriteGoal.Equation4624_implies_Equation4621 at h
    apply SimpleRewrites.Equation4621_implies_Equation4589 at h
    apply h
  intro x; repeat intro
  symm
  nth_rewrite 1 [← eq4594]
  nth_rewrite 1 [eq4589]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation366_implies_Equation372 (G: Type _) [Magma G] (h: Equation366 G) : Equation372 G := by
  have eq4595 (x y z : G) : (x ◇ x) ◇ x = (y ◇ z) ◇ z := by
    apply RewriteCombinations.Equation366_implies_Equation4624 at h
    apply SimpleRewrites.Equation4624_implies_Equation4614 at h
    apply Equation4614_implies_Equation4627 at h
    apply Apply.Equation4627_implies_Equation4595 at h
    apply h
  have eq4589 (x y z : G) : (x ◇ x) ◇ x = (y ◇ x) ◇ z := by
    apply RewriteCombinations.Equation366_implies_Equation4624 at h
    apply RewriteGoal.Equation4624_implies_Equation4621 at h
    apply SimpleRewrites.Equation4621_implies_Equation4589 at h
    apply h
  intro x; repeat intro
  symm
  nth_rewrite 1 [← eq4595]
  nth_rewrite 1 [eq4589]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation372_implies_Equation4627 (G: Type _) [Magma G] (h: Equation372 G) : Equation4627 G := by
  have eq360 (x y : G) : x ◇ x = (x ◇ x) ◇ y := by
    apply Apply.Equation372_implies_Equation368 at h
    apply RewriteCombinations.Equation368_implies_Equation360 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [← eq360]
  apply h
@[equational_result]
theorem Equation387_implies_Equation4608 (G: Type _) [Magma G] (h: Equation387 G) : Equation4608 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply RewriteHypothesis.Equation387_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation375 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [← eq375]
  apply h
@[equational_result]
theorem Equation387_implies_Equation4470 (G: Type _) [Magma G] (h: Equation387 G) : Equation4470 G := by
  have eq4608 (x y : G) : (x ◇ x) ◇ y = (y ◇ y) ◇ x := by
    apply Equation387_implies_Equation4608 at h
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
@[equational_result]
theorem Equation2292_implies_Equation220 (G: Type _) [Magma G] (h: Equation2292 G) : Equation220 G := by
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation2292_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation387 at h
    apply RewriteHypothesis.Equation387_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply h
  intro x; repeat intro
  symm
  nth_rewrite 1 [eq307]
  symm
  apply h
@[equational_result]
theorem Equation2295_implies_Equation2508 (G: Type _) [Magma G] (h: Equation2295 G) : Equation2508 G := by
  have eq4399 (x y : G) : x ◇ (x ◇ y) = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2295_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation3744 at h
    apply Equation3744_implies_Equation4520 at h
    apply Apply.Equation4520_implies_Equation4402 at h
    apply Apply.Equation4402_implies_Equation4399 at h
    apply h
  intro x; repeat intro
  symm
  nth_rewrite 1 [← eq4399]
  symm
  apply h
@[equational_result]
theorem Equation2302_implies_Equation223 (G: Type _) [Magma G] (h: Equation2302 G) : Equation223 G := by
  have eq325 (x y : G) : x ◇ y = x ◇ (y ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation2302_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation346 at h
    apply Apply.Equation346_implies_Equation325 at h
    apply h
  repeat intro
  symm
  nth_rewrite 3 [eq325]
  symm
  apply h
@[equational_result]
theorem Equation2305_implies_Equation2302 (G: Type _) [Magma G] (h: Equation2305 G) : Equation2302 G := by
  have eq4314 (x y : G) : x ◇ (y ◇ x) = x ◇ (y ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation2305_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation334 at h
    apply RewriteHypothesis.Equation334_implies_Equation4357 at h
    apply Apply.Equation4357_implies_Equation4315 at h
    apply Apply.Equation4315_implies_Equation4314 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [eq4314]
  symm
  apply h
@[equational_result]
theorem Equation2495_implies_Equation2292 (G: Type _) [Magma G] (h: Equation2495 G) : Equation2292 G := by
  have eq4380 (x : G) : x ◇ (x ◇ x) = (x ◇ x) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation2495_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation387 at h
    apply Equation387_implies_Equation4470 at h
    apply Apply.Equation4470_implies_Equation4380 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [eq4380]
  symm
  apply h
@[equational_result]
theorem Equation2498_implies_Equation2305 (G: Type _) [Magma G] (h: Equation2498 G) : Equation2305 G := by
  have eq4470 (x y : G) : x ◇ (y ◇ y) = (x ◇ x) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2498_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation387 at h
    apply Equation387_implies_Equation4470 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [eq4470]
  symm
  apply h
@[equational_result]
theorem Equation2505_implies_Equation2498 (G: Type _) [Magma G] (h: Equation2505 G) : Equation2498 G := by
  have eq4598 (x y : G) : (x ◇ x) ◇ y = (x ◇ y) ◇ x := by
    apply Apply.Equation2505_implies_Equation2442 at h
    apply Equation2442_implies_Equation27 at h
    apply RewriteHypothesis.Equation27_implies_Equation4676 at h
    apply Apply.Equation4676_implies_Equation4673 at h
    apply Apply.Equation4673_implies_Equation4598 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [eq4598]
  symm
  apply h
@[equational_result]
theorem Equation2508_implies_Equation2505 (G: Type _) [Magma G] (h: Equation2508 G) : Equation2505 G := by
  have eq4629 (x y : G) : (x ◇ y) ◇ x = (x ◇ y) ◇ y := by
    apply Apply.Equation2508_implies_Equation2442 at h
    apply Equation2442_implies_Equation27 at h
    apply Apply.Equation27_implies_Equation4136 at h
    apply Apply.Equation4136_implies_Equation4132 at h
    apply NthRewrites.Equation4132_implies_Equation4654 at h
    apply RewriteHypothesis.Equation4654_implies_Equation4629 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [eq4629]
  symm
  apply h
@[equational_result]
theorem Equation3289_implies_Equation3301 (G: Type _) [Magma G] (h: Equation3289 G) : Equation3301 G := by
  have eq40 (x y : G) : x ◇ x = y ◇ y := by
    apply NthRewrites.Equation3289_implies_Equation3699 at h
    apply RewriteHypothesisAndGoal.Equation3699_implies_Equation40 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq40]
  apply h
@[equational_result]
theorem Equation3290_implies_Equation3302 (G: Type _) [Magma G] (h: Equation3290 G) : Equation3302 G := by
  have eq40 (x y : G) : x ◇ x = y ◇ y := by
    apply NthRewrites.Equation3290_implies_Equation320 at h
    apply Apply.Equation320_implies_Equation3709 at h
    apply Apply.Equation3709_implies_Equation3692 at h
    apply RewriteHypothesisAndGoal.Equation3692_implies_Equation40 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq40]
  apply h
@[equational_result]
theorem Equation3291_implies_Equation3304 (G: Type _) [Magma G] (h: Equation3291 G) : Equation3304 G := by
  have eq40 (x y : G) : x ◇ x = y ◇ y := by
    apply Apply.Equation3291_implies_Equation3289 at h
    apply NthRewrites.Equation3289_implies_Equation3699 at h
    apply RewriteHypothesisAndGoal.Equation3699_implies_Equation40 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq40]
  apply h
@[equational_result]
theorem Equation3332_implies_Equation3341 (G: Type _) [Magma G] (h: Equation3332 G) : Equation3341 G := by
  have eq3310 (x y z : G) : x ◇ y = x ◇ (x ◇ (y ◇ z)) := by
    apply Apply.Equation3332_implies_Equation3310 at h
    apply h
  have eq3312 (x y z : G) : x ◇ y = x ◇ (x ◇ (z ◇ y)) := by
    apply Apply.Equation3332_implies_Equation3330 at h
    apply NthRewrites.Equation3330_implies_Equation3312 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq3310]
  nth_rewrite 1 [← eq3312]
  apply h
@[equational_result]
theorem Equation3351_implies_Equation3378 (G: Type _) [Magma G] (h: Equation3351 G) : Equation3378 G := by
  have eq4622 (x y z : G) : (x ◇ x) ◇ y = (z ◇ z) ◇ y := by
    apply Apply.Equation3351_implies_Equation3350 at h
    apply NthRewrites.Equation3350_implies_Equation4590 at h
    apply RewriteCombinations.Equation4590_implies_Equation4622 at h
    apply h
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply Apply.Equation3351_implies_Equation3348 at h
    apply NthRewrites.Equation3348_implies_Equation395 at h
    apply SimpleRewrites.Equation395_implies_Equation375 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq375]
  nth_rewrite 1 [← eq4622]
  nth_rewrite 1 [← eq375]
  apply h
@[equational_result]
theorem Equation3362_implies_Equation3377 (G: Type _) [Magma G] (h: Equation3362 G) : Equation3377 G := by
  have eq45 (x y z : G) : x ◇ y = z ◇ y := by
    apply NthRewrites.Equation3362_implies_Equation403 at h
    apply SimpleRewrites.Equation403_implies_Equation388 at h
    apply RewriteHypothesisAndGoal.Equation388_implies_Equation45 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq45]
  apply h
@[equational_result]
theorem Equation3365_implies_Equation3439 (G: Type _) [Magma G] (h: Equation3365 G) : Equation3439 G := by
  have eq4327 (x y z : G) : x ◇ (y ◇ x) = z ◇ (x ◇ x) := by
    apply Apply.Equation3365_implies_Equation3354 at h
    apply Equation3354_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3395 at h
    apply Apply.Equation3395_implies_Equation3392 at h
    apply RewriteHypothesisAndGoal.Equation3392_implies_Equation4327 at h
    apply h
  have eq4314 (x y : G) : x ◇ (y ◇ x) = x ◇ (y ◇ y) := by
    apply Apply.Equation3365_implies_Equation3362 at h
    apply NthRewrites.Equation3362_implies_Equation4527 at h
    apply RewriteGoal.Equation4527_implies_Equation4357 at h
    apply Apply.Equation4357_implies_Equation4315 at h
    apply Apply.Equation4315_implies_Equation4314 at h
    apply h
  have eq326 (x y : G) : x ◇ y = x ◇ (y ◇ y) := by
    apply Apply.Equation3365_implies_Equation3344 at h
    apply RewriteHypothesisAndGoal.Equation3344_implies_Equation332 at h
    apply RewriteHypothesis.Equation332_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation326 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq326]
  nth_rewrite 1 [← eq4327]
  nth_rewrite 1 [eq4314]
  nth_rewrite 1 [← eq326]
  apply h
@[equational_result]
theorem Equation3374_implies_Equation3378 (G: Type _) [Magma G] (h: Equation3374 G) : Equation3378 G := by
  have eq45 (x y z : G) : x ◇ y = z ◇ y := by
    apply Apply.Equation3374_implies_Equation3362 at h
    apply NthRewrites.Equation3362_implies_Equation403 at h
    apply SimpleRewrites.Equation403_implies_Equation388 at h
    apply RewriteHypothesisAndGoal.Equation388_implies_Equation45 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq45]
  apply h
@[equational_result]
theorem Equation3386_implies_Equation3412 (G: Type _) [Magma G] (h: Equation3386 G) : Equation3412 G := by
  have eq3310 (x y z : G) : x ◇ y = x ◇ (x ◇ (y ◇ z)) := by
    apply Apply.Equation3386_implies_Equation3310 at h
    apply h
  have eq3414 (x y z : G) : x ◇ y = z ◇ (z ◇ (x ◇ y)) := by
    apply Apply.Equation3386_implies_Equation3384 at h
    apply NthRewrites.Equation3384_implies_Equation3431 at h
    apply Apply.Equation3431_implies_Equation3414 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq3310]
  nth_rewrite 1 [← eq3414]
  apply h
@[equational_result]
theorem Equation3764_implies_Equation3767 (G: Type _) [Magma G] (h: Equation3764 G) : Equation3767 G := by
  have eq45 (x y z : G) : x ◇ y = z ◇ y := by
    apply Equation3764_implies_Equation41 at h
    apply Subgraph.Equation41_implies_Equation39 at h
    apply Subgraph.Equation39_implies_Equation45 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq45]
  apply h
@[equational_result]
theorem Equation3768_implies_Equation3836 (G: Type _) [Magma G] (h: Equation3768 G) : Equation3836 G := by
  have eq42 (x y z : G) : x ◇ y = x ◇ z := by
    apply Equation3768_implies_Equation41 at h
    apply SimpleRewrites.Equation41_implies_Equation38 at h
    apply Subgraph.Equation38_implies_Equation42 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq42]
  apply h
@[equational_result]
theorem Equation3771_implies_Equation3840 (G: Type _) [Magma G] (h: Equation3771 G) : Equation3840 G := by
  have eq42 (x y z : G) : x ◇ y = x ◇ z := by
    apply Apply.Equation3771_implies_Equation3760 at h
    apply Equation3760_implies_Equation41 at h
    apply SimpleRewrites.Equation41_implies_Equation38 at h
    apply Subgraph.Equation38_implies_Equation42 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq42]
  apply h
@[equational_result]
theorem Equation3780_implies_Equation3856 (G: Type _) [Magma G] (h: Equation3780 G) : Equation3856 G := by
  have eq42 (x y z : G) : x ◇ y = x ◇ z := by
    apply Apply.Equation3780_implies_Equation3754 at h
    apply Equation3754_implies_Equation41 at h
    apply SimpleRewrites.Equation41_implies_Equation38 at h
    apply Subgraph.Equation38_implies_Equation42 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq42]
  apply h
@[equational_result]
theorem Equation3814_implies_Equation3818 (G: Type _) [Magma G] (h: Equation3814 G) : Equation3818 G := by
  have eq45 (x y z : G) : x ◇ y = z ◇ y := by
    apply Apply.Equation3814_implies_Equation3764 at h
    apply Equation3764_implies_Equation41 at h
    apply Subgraph.Equation41_implies_Equation39 at h
    apply Subgraph.Equation39_implies_Equation45 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq45]
  apply h
@[equational_result]
theorem Equation4085_implies_Equation4107 (G: Type _) [Magma G] (h: Equation4085 G) : Equation4107 G := by
  have eq40 (x y : G) : x ◇ x = y ◇ y := by
    apply NthRewrites.Equation4085_implies_Equation369 at h
    apply Apply.Equation369_implies_Equation3693 at h
    apply Apply.Equation3693_implies_Equation3689 at h
    apply RewriteHypothesisAndGoal.Equation3689_implies_Equation40 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq40]
  apply h
@[equational_result]
theorem Equation4087_implies_Equation4113 (G: Type _) [Magma G] (h: Equation4087 G) : Equation4113 G := by
  have eq40 (x y : G) : x ◇ x = y ◇ y := by
    apply NthRewrites.Equation4087_implies_Equation3691 at h
    apply RewriteHypothesisAndGoal.Equation3691_implies_Equation40 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq40]
  apply h
@[equational_result]
theorem Equation4089_implies_Equation4116 (G: Type _) [Magma G] (h: Equation4089 G) : Equation4116 G := by
  have eq40 (x y : G) : x ◇ x = y ◇ y := by
    apply Apply.Equation4089_implies_Equation4087 at h
    apply NthRewrites.Equation4087_implies_Equation3691 at h
    apply RewriteHypothesisAndGoal.Equation3691_implies_Equation40 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq40]
  apply h
@[equational_result]
theorem Equation4122_implies_Equation4126 (G: Type _) [Magma G] (h: Equation4122 G) : Equation4126 G := by
  have eq4069 (x y z : G) : x ◇ x = ((x ◇ x) ◇ y) ◇ z := by
    apply NthRewrites.Equation4122_implies_Equation4132 at h
    apply NthRewrites.Equation4132_implies_Equation4069 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [← eq4069]
  nth_rewrite 1 [eq4069]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4126_implies_Equation4079 (G: Type _) [Magma G] (h: Equation4126 G) : Equation4079 G := by
  have eq4136 (x y z w : G) : x ◇ y = ((x ◇ y) ◇ z) ◇ w := by
    apply Apply.Equation4126_implies_Equation4122 at h
    apply Equation4122_implies_Equation4153 at h
    apply Apply.Equation4153_implies_Equation4136 at h
    apply h
  have eq4122 (x y z : G) : x ◇ y = ((x ◇ x) ◇ y) ◇ z := by
    apply Apply.Equation4126_implies_Equation4122 at h
    apply h
  have eq38 (x y : G) : x ◇ x = x ◇ y := by
    apply Apply.Equation4126_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply Subgraph.Equation42_implies_Equation38 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [← eq4136]
  nth_rewrite 1 [eq4122]
  symm
  nth_rewrite 1 [eq38]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4126_implies_Equation4148 (G: Type _) [Magma G] (h: Equation4126 G) : Equation4148 G := by
  have eq4599 (x y : G) : (x ◇ x) ◇ y = (x ◇ y) ◇ y := by
    apply Apply.Equation4126_implies_Equation4124 at h
    apply NthRewrites.Equation4124_implies_Equation4150 at h
    apply Apply.Equation4150_implies_Equation4142 at h
    apply RewriteHypothesisAndGoal.Equation4142_implies_Equation4655 at h
    apply RewriteHypothesis.Equation4655_implies_Equation4599 at h
    apply h
  have eq322 (x y : G) : x ◇ y = x ◇ (x ◇ x) := by
    apply Apply.Equation4126_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply Apply.Equation42_implies_Equation3332 at h
    apply Equation3332_implies_Equation3341 at h
    apply Apply.Equation3341_implies_Equation3336 at h
    apply Apply.Equation3336_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq322]
  symm
  nth_rewrite 1 [← eq4599]
  symm
  nth_rewrite 1 [← eq322]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4140_implies_Equation4153 (G: Type _) [Magma G] (h: Equation4140 G) : Equation4153 G := by
  have eq4136 (x y z w : G) : x ◇ y = ((x ◇ y) ◇ z) ◇ w := by
    apply Apply.Equation4140_implies_Equation4129 at h
    apply NthRewrites.Equation4129_implies_Equation4136 at h
    apply h
  have eq4129 (x y z : G) : x ◇ y = ((x ◇ y) ◇ x) ◇ z := by
    apply Apply.Equation4140_implies_Equation4129 at h
    apply h
  have eq322 (x y : G) : x ◇ y = x ◇ (x ◇ x) := by
    apply Apply.Equation4140_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply Apply.Equation42_implies_Equation3332 at h
    apply Equation3332_implies_Equation3341 at h
    apply Apply.Equation3341_implies_Equation3336 at h
    apply Apply.Equation3336_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq322]
  symm
  nth_rewrite 1 [← eq4136]
  nth_rewrite 1 [eq4129]
  symm
  nth_rewrite 1 [← eq322]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4151_implies_Equation4149 (G: Type _) [Magma G] (h: Equation4151 G) : Equation4149 G := by
  have eq4133 (x y z : G) : x ◇ y = ((x ◇ y) ◇ z) ◇ x := by
    apply Apply.Equation4151_implies_Equation4147 at h
    apply RewriteCombinations.Equation4147_implies_Equation4148 at h
    apply Apply.Equation4148_implies_Equation4132 at h
    apply NthRewrites.Equation4132_implies_Equation4133 at h
    apply h
  have eq4134 (x y z : G) : x ◇ y = ((x ◇ y) ◇ z) ◇ y := by
    apply Apply.Equation4151_implies_Equation4134 at h
    apply h
  have eq38 (x y : G) : x ◇ x = x ◇ y := by
    apply Apply.Equation4151_implies_Equation4123 at h
    apply Apply.Equation4123_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply Subgraph.Equation42_implies_Equation38 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq38]
  symm
  nth_rewrite 1 [← eq4133]
  nth_rewrite 1 [eq4134]
  symm
  nth_rewrite 1 [eq38]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4152_implies_Equation4153 (G: Type _) [Magma G] (h: Equation4152 G) : Equation4153 G := by
  have eq4136 (x y z w : G) : x ◇ y = ((x ◇ y) ◇ z) ◇ w := by
    apply Apply.Equation4152_implies_Equation4125 at h
    apply RewriteCombinations.Equation4125_implies_Equation4126 at h
    apply Apply.Equation4126_implies_Equation4122 at h
    apply Equation4122_implies_Equation4153 at h
    apply Apply.Equation4153_implies_Equation4136 at h
    apply h
  have eq4135 (x y z : G) : x ◇ y = ((x ◇ y) ◇ z) ◇ z := by
    apply Apply.Equation4152_implies_Equation4135 at h
    apply h
  have eq322 (x y : G) : x ◇ y = x ◇ (x ◇ x) := by
    apply Apply.Equation4152_implies_Equation4125 at h
    apply Apply.Equation4125_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply Apply.Equation42_implies_Equation3332 at h
    apply Equation3332_implies_Equation3341 at h
    apply Apply.Equation3341_implies_Equation3336 at h
    apply Apply.Equation3336_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq322]
  symm
  nth_rewrite 1 [← eq4136]
  nth_rewrite 1 [eq4135]
  symm
  nth_rewrite 1 [← eq322]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4170_implies_Equation4237 (G: Type _) [Magma G] (h: Equation4170 G) : Equation4237 G := by
  have eq42 (x y z : G) : x ◇ y = x ◇ z := by
    apply NthRewrites.Equation4170_implies_Equation330 at h
    apply SimpleRewrites.Equation330_implies_Equation322 at h
    apply RewriteHypothesisAndGoal.Equation322_implies_Equation42 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq42]
  apply h
@[equational_result]
theorem Equation4186_implies_Equation4262 (G: Type _) [Magma G] (h: Equation4186 G) : Equation4262 G := by
  have eq42 (x y z : G) : x ◇ y = x ◇ z := by
    apply Apply.Equation4186_implies_Equation4160 at h
    apply NthRewrites.Equation4160_implies_Equation3329 at h
    apply Equation3329_implies_Equation38 at h
    apply Subgraph.Equation38_implies_Equation42 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq42]
  apply h
@[equational_result]
theorem Equation4198_implies_Equation4207 (G: Type _) [Magma G] (h: Equation4198 G) : Equation4207 G := by
  have eq42 (x y z : G) : x ◇ y = x ◇ z := by
    apply RewriteHypothesisAndGoal.Equation4198_implies_Equation376 at h
    apply Apply.Equation376_implies_Equation374 at h
    apply RewriteHypothesis.Equation374_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq42]
  apply h
@[equational_result]
theorem Equation4204_implies_Equation4263 (G: Type _) [Magma G] (h: Equation4204 G) : Equation4263 G := by
  have eq4622 (x y z : G) : (x ◇ x) ◇ y = (z ◇ z) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation4204_implies_Equation4625 at h
    apply Apply.Equation4625_implies_Equation4622 at h
    apply h
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply Apply.Equation4204_implies_Equation4192 at h
    apply RewriteHypothesisAndGoal.Equation4192_implies_Equation375 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq375]
  nth_rewrite 1 [← eq4622]
  nth_rewrite 1 [← eq375]
  apply h
@[equational_result]
theorem Equation4220_implies_Equation4262 (G: Type _) [Magma G] (h: Equation4220 G) : Equation4262 G := by
  have eq42 (x y z : G) : x ◇ y = x ◇ z := by
    apply RewriteHypothesisAndGoal.Equation4220_implies_Equation374 at h
    apply RewriteHypothesis.Equation374_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq42]
  apply h
@[equational_result]
theorem Equation4247_implies_Equation4262 (G: Type _) [Magma G] (h: Equation4247 G) : Equation4262 G := by
  have eq4341 (x y z : G) : x ◇ (y ◇ y) = x ◇ (z ◇ z) := by
    apply Apply.Equation4247_implies_Equation4229 at h
    apply NthRewrites.Equation4229_implies_Equation4270 at h
    apply RewriteCombinations.Equation4270_implies_Equation4341 at h
    apply h
  have eq326 (x y : G) : x ◇ y = x ◇ (y ◇ y) := by
    apply Apply.Equation4247_implies_Equation4178 at h
    apply NthRewrites.Equation4178_implies_Equation327 at h
    apply Apply.Equation327_implies_Equation326 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq326]
  nth_rewrite 1 [← eq4341]
  nth_rewrite 1 [← eq326]
  apply h
@[equational_result]
theorem Equation4301_implies_Equation4311 (G: Type _) [Magma G] (h: Equation4301 G) : Equation4311 G := by
  have eq4294 (x y z : G) : x ◇ (x ◇ y) = y ◇ (y ◇ z) := by
    apply NthRewrites.Equation4301_implies_Equation4277 at h
    apply RewriteCombinations.Equation4277_implies_Equation4294 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4294]
  apply h
@[equational_result]
theorem Equation4331_implies_Equation4337 (G: Type _) [Magma G] (h: Equation4331 G) : Equation4337 G := by
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesis.Equation4331_implies_Equation4273 at h
    apply h
  have eq4270 (x y : G) : x ◇ (x ◇ x) = x ◇ (y ◇ y) := by
    apply NthRewrites.Equation4331_implies_Equation4355 at h
    apply Apply.Equation4355_implies_Equation4280 at h
    apply Apply.Equation4280_implies_Equation4270 at h
    apply h
  have eq4314 (x y : G) : x ◇ (y ◇ x) = x ◇ (y ◇ y) := by
    apply Apply.Equation4331_implies_Equation4314 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4273]
  nth_rewrite 1 [eq4270]
  nth_rewrite 1 [← eq4314]
  apply h
@[equational_result]
theorem Equation4387_implies_Equation4384 (G: Type _) [Magma G] (h: Equation4387 G) : Equation4384 G := by
  have eq4677 (x y z : G) : (x ◇ y) ◇ z = (y ◇ x) ◇ z := by
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4667 at h
    apply Apply.Equation4667_implies_Equation4665 at h
    apply RewriteCombinations.Equation4665_implies_Equation4668 at h
    apply SimpleRewrites.Equation4668_implies_Equation4593 at h
    apply RewriteCombinations.Equation4593_implies_Equation4693 at h
    apply Apply.Equation4693_implies_Equation4677 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [eq4677]
  symm
  apply h
@[equational_result]
theorem Equation4387_implies_Equation4390 (G: Type _) [Magma G] (h: Equation4387 G) : Equation4390 G := by
  have eq4592 (x y z : G) : (x ◇ x) ◇ x = (y ◇ y) ◇ z := by
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4617 at h
    apply Apply.Equation4617_implies_Equation4614 at h
    apply Equation4614_implies_Equation4627 at h
    apply RewriteHypothesis.Equation4627_implies_Equation4592 at h
    apply h
  have eq4589 (x y z : G) : (x ◇ x) ◇ x = (y ◇ x) ◇ z := by
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4617 at h
    apply SimpleRewrites.Equation4617_implies_Equation4589 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [← eq4592]
  nth_rewrite 1 [eq4589]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4387_implies_Equation4391 (G: Type _) [Magma G] (h: Equation4387 G) : Equation4391 G := by
  have eq4593 (x y z : G) : (x ◇ x) ◇ x = (y ◇ z) ◇ x := by
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4667 at h
    apply Apply.Equation4667_implies_Equation4665 at h
    apply RewriteCombinations.Equation4665_implies_Equation4668 at h
    apply SimpleRewrites.Equation4668_implies_Equation4593 at h
    apply h
  have eq4589 (x y z : G) : (x ◇ x) ◇ x = (y ◇ x) ◇ z := by
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4617 at h
    apply SimpleRewrites.Equation4617_implies_Equation4589 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [← eq4593]
  nth_rewrite 1 [eq4589]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4387_implies_Equation4392 (G: Type _) [Magma G] (h: Equation4387 G) : Equation4392 G := by
  have eq4594 (x y z : G) : (x ◇ x) ◇ x = (y ◇ z) ◇ y := by
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4667 at h
    apply Apply.Equation4667_implies_Equation4665 at h
    apply RewriteCombinations.Equation4665_implies_Equation4668 at h
    apply RewriteCombinations.Equation4668_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4628 at h
    apply Apply.Equation4628_implies_Equation4596 at h
    apply Apply.Equation4596_implies_Equation4594 at h
    apply h
  have eq4589 (x y z : G) : (x ◇ x) ◇ x = (y ◇ x) ◇ z := by
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4617 at h
    apply SimpleRewrites.Equation4617_implies_Equation4589 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [← eq4594]
  nth_rewrite 1 [eq4589]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4387_implies_Equation4393 (G: Type _) [Magma G] (h: Equation4387 G) : Equation4393 G := by
  have eq4595 (x y z : G) : (x ◇ x) ◇ x = (y ◇ z) ◇ z := by
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4617 at h
    apply Apply.Equation4617_implies_Equation4614 at h
    apply Equation4614_implies_Equation4627 at h
    apply Apply.Equation4627_implies_Equation4595 at h
    apply h
  have eq4589 (x y z : G) : (x ◇ x) ◇ x = (y ◇ x) ◇ z := by
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4617 at h
    apply SimpleRewrites.Equation4617_implies_Equation4589 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [← eq4595]
  nth_rewrite 1 [eq4589]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4387_implies_Equation4394 (G: Type _) [Magma G] (h: Equation4387 G) : Equation4394 G := by
  have eq4596 (x y z w : G) : (x ◇ x) ◇ x = (y ◇ z) ◇ w := by
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4667 at h
    apply Apply.Equation4667_implies_Equation4665 at h
    apply RewriteCombinations.Equation4665_implies_Equation4668 at h
    apply RewriteCombinations.Equation4668_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4628 at h
    apply Apply.Equation4628_implies_Equation4596 at h
    apply h
  have eq4589 (x y z : G) : (x ◇ x) ◇ x = (y ◇ x) ◇ z := by
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4617 at h
    apply SimpleRewrites.Equation4617_implies_Equation4589 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [← eq4596]
  nth_rewrite 1 [eq4589]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4492_implies_Equation4505 (G: Type _) [Magma G] (h: Equation4492 G) : Equation4505 G := by
  have eq4591 (x y : G) : (x ◇ x) ◇ x = (y ◇ y) ◇ y := by
    apply Apply.Equation4492_implies_Equation4387 at h
    apply Equation4387_implies_Equation4390 at h
    apply Apply.Equation4390_implies_Equation4389 at h
    apply RewriteCombinations.Equation4389_implies_Equation4591 at h
    apply h
  have eq4469 (x y : G) : x ◇ (y ◇ y) = (x ◇ x) ◇ x := by
    apply Apply.Equation4492_implies_Equation4471 at h
    apply Apply.Equation4471_implies_Equation4469 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq4469]
  nth_rewrite 1 [← eq4591]
  nth_rewrite 1 [← eq4469]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4528_implies_Equation4575 (G: Type _) [Magma G] (h: Equation4528 G) : Equation4575 G := by
  have eq4359 (x y z w : G) : x ◇ (y ◇ z) = x ◇ (z ◇ w) := by
    apply RewriteCombinations.Equation4528_implies_Equation4506 at h
    apply RewriteGoal.Equation4506_implies_Equation4361 at h
    apply Apply.Equation4361_implies_Equation4359 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4359]
  apply h
@[equational_result]
theorem Equation4536_implies_Equation4580 (G: Type _) [Magma G] (h: Equation4536 G) : Equation4580 G := by
  have eq4359 (x y z w : G) : x ◇ (y ◇ z) = x ◇ (z ◇ w) := by
    apply Apply.Equation4536_implies_Equation4524 at h
    apply Equation4524_implies_Equation4365 at h
    apply RewriteHypothesis.Equation4365_implies_Equation4361 at h
    apply Apply.Equation4361_implies_Equation4359 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4359]
  apply h
@[equational_result]
theorem Equation4561_implies_Equation4566 (G: Type _) [Magma G] (h: Equation4561 G) : Equation4566 G := by
  have eq4507 (x y z : G) : x ◇ (y ◇ z) = (x ◇ x) ◇ y := by
    apply Apply.Equation4561_implies_Equation4509 at h
    apply Apply.Equation4509_implies_Equation4507 at h
    apply h
  have eq4590 (x y : G) : (x ◇ x) ◇ x = (y ◇ y) ◇ x := by
    apply Apply.Equation4561_implies_Equation4418 at h
    apply Apply.Equation4418_implies_Equation4387 at h
    apply Equation4387_implies_Equation4390 at h
    apply Apply.Equation4390_implies_Equation4388 at h
    apply RewriteHypothesis.Equation4388_implies_Equation4622 at h
    apply Apply.Equation4622_implies_Equation4590 at h
    apply h
  have eq4506 (x y z : G) : x ◇ (y ◇ z) = (x ◇ x) ◇ x := by
    apply Apply.Equation4561_implies_Equation4509 at h
    apply Apply.Equation4509_implies_Equation4506 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq4507]
  nth_rewrite 1 [← eq4590]
  nth_rewrite 1 [← eq4506]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4561_implies_Equation4522 (G: Type _) [Magma G] (h: Equation4561 G) : Equation4522 G := by
  have eq4677 (x y z : G) : (x ◇ y) ◇ z = (y ◇ x) ◇ z := by
    apply Apply.Equation4561_implies_Equation4418 at h
    apply Apply.Equation4418_implies_Equation4387 at h
    apply Equation4387_implies_Equation4391 at h
    apply RewriteHypothesis.Equation4391_implies_Equation4693 at h
    apply Apply.Equation4693_implies_Equation4677 at h
    apply h
  have eq4506 (x y z : G) : x ◇ (y ◇ z) = (x ◇ x) ◇ x := by
    apply Apply.Equation4561_implies_Equation4509 at h
    apply Apply.Equation4509_implies_Equation4506 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq4506]
  symm
  nth_rewrite 1 [eq4677]
  symm
  nth_rewrite 1 [← eq4506]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4563_implies_Equation4557 (G: Type _) [Magma G] (h: Equation4563 G) : Equation4557 G := by
  have eq4363 (x y z w : G) : x ◇ (y ◇ z) = y ◇ (x ◇ w) := by
    apply Apply.Equation4563_implies_Equation4545 at h
    apply Equation4545_implies_Equation4365 at h
    apply RewriteHypothesis.Equation4365_implies_Equation4363 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4363]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4563_implies_Equation4569 (G: Type _) [Magma G] (h: Equation4563 G) : Equation4569 G := by
  have eq4372 (x y z w : G) : x ◇ (y ◇ z) = z ◇ (w ◇ y) := by
    apply Apply.Equation4563_implies_Equation4545 at h
    apply Equation4545_implies_Equation4365 at h
    apply RewriteHypothesis.Equation4365_implies_Equation4377 at h
    apply RewriteHypothesis.Equation4377_implies_Equation4372 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4372]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4563_implies_Equation4467 (G: Type _) [Magma G] (h: Equation4563 G) : Equation4467 G := by
  have eq4316 (x y z : G) : x ◇ (y ◇ x) = x ◇ (z ◇ x) := by
    apply Apply.Equation4563_implies_Equation4457 at h
    apply Equation4457_implies_Equation4440 at h
    apply Apply.Equation4440_implies_Equation4432 at h
    apply RewriteGoal.Equation4432_implies_Equation4316 at h
    apply h
  have eq4315 (x y z : G) : x ◇ (y ◇ x) = x ◇ (y ◇ z) := by
    apply Apply.Equation4563_implies_Equation4511 at h
    apply RewriteGoal.Equation4511_implies_Equation4357 at h
    apply Apply.Equation4357_implies_Equation4315 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4316]
  nth_rewrite 1 [eq4315]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4563_implies_Equation4504 (G: Type _) [Magma G] (h: Equation4563 G) : Equation4504 G := by
  have eq4318 (x y z : G) : x ◇ (y ◇ x) = x ◇ (z ◇ z) := by
    apply Apply.Equation4563_implies_Equation4528 at h
    apply RewriteCombinations.Equation4528_implies_Equation4506 at h
    apply RewriteGoal.Equation4506_implies_Equation4361 at h
    apply Apply.Equation4361_implies_Equation4289 at h
    apply RewriteCombinations.Equation4289_implies_Equation4318 at h
    apply h
  have eq4315 (x y z : G) : x ◇ (y ◇ x) = x ◇ (y ◇ z) := by
    apply Apply.Equation4563_implies_Equation4511 at h
    apply RewriteGoal.Equation4511_implies_Equation4357 at h
    apply Apply.Equation4357_implies_Equation4315 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4318]
  nth_rewrite 1 [eq4315]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4563_implies_Equation4430 (G: Type _) [Magma G] (h: Equation4563 G) : Equation4430 G := by
  have eq4277 (x y z : G) : x ◇ (x ◇ x) = y ◇ (y ◇ z) := by
    apply Apply.Equation4563_implies_Equation4528 at h
    apply Equation4528_implies_Equation4575 at h
    apply RewriteHypothesisAndGoal.Equation4575_implies_Equation4281 at h
    apply Apply.Equation4281_implies_Equation4277 at h
    apply h
  have eq4380 (x : G) : x ◇ (x ◇ x) = (x ◇ x) ◇ x := by
    apply Apply.Equation4563_implies_Equation4415 at h
    apply Apply.Equation4415_implies_Equation4385 at h
    apply Apply.Equation4385_implies_Equation4380 at h
    apply h
  have eq4528 (x y z : G) : x ◇ (y ◇ z) = (y ◇ y) ◇ y := by
    apply Apply.Equation4563_implies_Equation4528 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4277]
  nth_rewrite 1 [eq4380]
  nth_rewrite 1 [← eq4528]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4563_implies_Equation4575 (G: Type _) [Magma G] (h: Equation4563 G) : Equation4575 G := by
  have eq4281 (x y z w : G) : x ◇ (x ◇ x) = y ◇ (z ◇ w) := by
    apply Apply.Equation4563_implies_Equation4528 at h
    apply Equation4528_implies_Equation4575 at h
    apply RewriteHypothesisAndGoal.Equation4575_implies_Equation4281 at h
    apply h
  have eq4587 (x y : G) : (x ◇ x) ◇ x = (y ◇ x) ◇ x := by
    apply Apply.Equation4563_implies_Equation4415 at h
    apply Apply.Equation4415_implies_Equation4385 at h
    apply RewriteHypothesis.Equation4385_implies_Equation4666 at h
    apply Apply.Equation4666_implies_Equation4587 at h
    apply h
  have eq4380 (x : G) : x ◇ (x ◇ x) = (x ◇ x) ◇ x := by
    apply Apply.Equation4563_implies_Equation4415 at h
    apply Apply.Equation4415_implies_Equation4385 at h
    apply Apply.Equation4385_implies_Equation4380 at h
    apply h
  have eq4528 (x y z : G) : x ◇ (y ◇ z) = (y ◇ y) ◇ y := by
    apply Apply.Equation4563_implies_Equation4528 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4281]
  symm
  nth_rewrite 1 [eq4587]
  symm
  nth_rewrite 1 [eq4380]
  nth_rewrite 1 [← eq4528]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4578_implies_Equation4468 (G: Type _) [Magma G] (h: Equation4578 G) : Equation4468 G := by
  have eq4316 (x y z : G) : x ◇ (y ◇ x) = x ◇ (z ◇ x) := by
    apply Apply.Equation4578_implies_Equation4465 at h
    apply Equation4465_implies_Equation4441 at h
    apply Apply.Equation4441_implies_Equation4434 at h
    apply Apply.Equation4434_implies_Equation4432 at h
    apply RewriteGoal.Equation4432_implies_Equation4316 at h
    apply h
  have eq4315 (x y z : G) : x ◇ (y ◇ x) = x ◇ (y ◇ z) := by
    apply Apply.Equation4578_implies_Equation4519 at h
    apply Apply.Equation4519_implies_Equation4507 at h
    apply RewriteGoal.Equation4507_implies_Equation4357 at h
    apply Apply.Equation4357_implies_Equation4315 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4316]
  nth_rewrite 1 [eq4315]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4578_implies_Equation4579 (G: Type _) [Magma G] (h: Equation4578 G) : Equation4579 G := by
  have eq4317 (x y z : G) : x ◇ (y ◇ x) = x ◇ (z ◇ y) := by
    apply Apply.Equation4578_implies_Equation4536 at h
    apply Apply.Equation4536_implies_Equation4524 at h
    apply Equation4524_implies_Equation4365 at h
    apply RewriteHypothesis.Equation4365_implies_Equation4313 at h
    apply Apply.Equation4313_implies_Equation4289 at h
    apply RewriteCombinations.Equation4289_implies_Equation4317 at h
    apply h
  have eq4315 (x y z : G) : x ◇ (y ◇ x) = x ◇ (y ◇ z) := by
    apply Apply.Equation4578_implies_Equation4519 at h
    apply Apply.Equation4519_implies_Equation4507 at h
    apply RewriteGoal.Equation4507_implies_Equation4357 at h
    apply Apply.Equation4357_implies_Equation4315 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4317]
  nth_rewrite 1 [eq4315]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4578_implies_Equation4505 (G: Type _) [Magma G] (h: Equation4578 G) : Equation4505 G := by
  have eq4318 (x y z : G) : x ◇ (y ◇ x) = x ◇ (z ◇ z) := by
    apply Apply.Equation4578_implies_Equation4563 at h
    apply Equation4563_implies_Equation4575 at h
    apply RewriteHypothesisAndGoal.Equation4575_implies_Equation4281 at h
    apply RewriteCombinations.Equation4281_implies_Equation4337 at h
    apply Apply.Equation4337_implies_Equation4318 at h
    apply h
  have eq4315 (x y z : G) : x ◇ (y ◇ x) = x ◇ (y ◇ z) := by
    apply Apply.Equation4578_implies_Equation4519 at h
    apply Apply.Equation4519_implies_Equation4507 at h
    apply RewriteGoal.Equation4507_implies_Equation4357 at h
    apply Apply.Equation4357_implies_Equation4315 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4318]
  nth_rewrite 1 [eq4315]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4616_implies_Equation4626 (G: Type _) [Magma G] (h: Equation4616 G) : Equation4626 G := by
  have eq4609 (x y z : G) : (x ◇ x) ◇ y = (y ◇ y) ◇ z := by
    apply NthRewrites.Equation4616_implies_Equation4623 at h
    apply Apply.Equation4623_implies_Equation4609 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4609]
  apply h
@[equational_result]
theorem Equation4646_implies_Equation4652 (G: Type _) [Magma G] (h: Equation4646 G) : Equation4652 G := by
  have eq4588 (x y : G) : (x ◇ x) ◇ x = (y ◇ x) ◇ y := by
    apply RewriteHypothesis.Equation4646_implies_Equation4588 at h
    apply h
  have eq4585 (x y : G) : (x ◇ x) ◇ x = (x ◇ y) ◇ y := by
    apply NthRewrites.Equation4646_implies_Equation4670 at h
    apply Apply.Equation4670_implies_Equation4595 at h
    apply Apply.Equation4595_implies_Equation4585 at h
    apply h
  have eq4629 (x y : G) : (x ◇ y) ◇ x = (x ◇ y) ◇ y := by
    apply Apply.Equation4646_implies_Equation4629 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4588]
  nth_rewrite 1 [eq4585]
  nth_rewrite 1 [← eq4629]
  apply h
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
    apply Equation9_implies_Equation308 at h
    apply h
  intro x y
  nth_rewrite 1 [eq8 x]
  symm
  nth_rewrite 1 [← eq3864]
  nth_rewrite 1 [eq308]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation9_implies_Equation100 (G: Type _) [Magma G] (h: Equation9 G) : Equation100 G := by
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply Equation9_implies_Equation308 at h
    apply Apply.Equation308_implies_Equation307 at h
    apply h
  have eq3915 (x y : G) : x ◇ y = (x ◇ (x ◇ x)) ◇ y := by
    apply RewriteHypothesis.Equation9_implies_Equation3921 at h
    apply Apply.Equation3921_implies_Equation3915 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [eq307]
  nth_rewrite 1 [← eq3915]
  symm
  apply h
@[equational_result]
theorem Equation28_implies_Equation104 (G: Type _) [Magma G] (h: Equation28 G) : Equation104 G := by
  have eq3461 (x y : G) : x ◇ x = x ◇ ((y ◇ x) ◇ x) := by
    apply RewriteHypothesis.Equation28_implies_Equation3533 at h
    apply Apply.Equation3533_implies_Equation3461 at h
    apply h
  have eq364 (x y : G) : x ◇ x = (y ◇ x) ◇ x := by
    apply RewriteHypothesis.Equation28_implies_Equation2567 at h
    apply Equation2567_implies_Equation364 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq3461]
  nth_rewrite 1 [eq364]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation34_implies_Equation3824 (G: Type _) [Magma G] (h: Equation34 G) : Equation3824 G := by
  have eq39 (x y : G) : x ◇ x = y ◇ x := by
    apply Apply.Equation34_implies_Equation250 at h
    apply Apply.Equation250_implies_Equation234 at h
    apply Apply.Equation234_implies_Equation2359 at h
    apply Apply.Equation2359_implies_Equation2343 at h
    apply Equation2343_implies_Equation5 at h
    apply Subgraph.Equation5_implies_Equation39 at h
    apply h
  have eq359 (x : G) : x ◇ x = (x ◇ x) ◇ x := by
    apply NthRewrites.Equation34_implies_Equation4243 at h
    apply Equation4243_implies_Equation364 at h
    apply Apply.Equation364_implies_Equation359 at h
    apply h
  have eq3684 (x y : G) : x ◇ x = (y ◇ y) ◇ (x ◇ x) := by
    apply Apply.Equation34_implies_Equation31 at h
    apply Apply.Equation31_implies_Equation3820 at h
    apply Apply.Equation3820_implies_Equation3684 at h
    apply h
  have eq370 (x y z : G) : x ◇ x = (y ◇ z) ◇ x := by
    apply Apply.Equation34_implies_Equation250 at h
    apply Apply.Equation250_implies_Equation234 at h
    apply Apply.Equation234_implies_Equation2359 at h
    apply Apply.Equation2359_implies_Equation2343 at h
    apply Equation2343_implies_Equation5 at h
    apply Subgraph.Equation5_implies_Equation39 at h
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
    apply Equation332_implies_Equation4343 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq4482]
  nth_rewrite 1 [eq4343]
  symm
  apply h
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
    apply Subgraph.Equation45_implies_Equation381 at h
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
    apply Apply.Equation3401_implies_Equation3268 at h
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
  nth_rewrite 1 [eq3268]
  symm
  nth_rewrite 1 [← eq388]
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
    apply Apply.Equation4578_implies_Equation4563 at h
    apply Equation4563_implies_Equation4575 at h
    apply RewriteHypothesisAndGoal.Equation4575_implies_Equation4281 at h
    apply Apply.Equation4281_implies_Equation4271 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [← eq4268]
  nth_rewrite 1 [eq4271]
  apply h
  repeat assumption
@[equational_result]
theorem Equation28_implies_Equation2706 (G: Type _) [Magma G] (h: Equation28 G) : Equation2706 G := by
  have eq3722 (x y : G) : x ◇ y = (x ◇ y) ◇ (x ◇ y) := by
    apply RewriteHypothesis.Equation28_implies_Equation2567 at h
    apply Equation2567_implies_Equation3122 at h
    apply Apply.Equation3122_implies_Equation3102 at h
    apply Equation3102_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation3722 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq3722]
  symm
  apply h
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
@[equational_result]
theorem Equation742_implies_Equation84 (G: Type _) [Magma G] (h: Equation742 G) : Equation84 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation742_implies_Equation41 at h
    apply Subgraph.Equation41_implies_Equation381 at h
    apply Apply.Equation381_implies_Equation375 at h
    apply h
  intro x y z
  symm
  nth_rewrite 3 [eq375]
  symm
  apply h
@[equational_result]
theorem Equation743_implies_Equation85 (G: Type _) [Magma G] (h: Equation743 G) : Equation85 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply Apply.Equation743_implies_Equation742 at h
    apply RewriteHypothesisAndGoal.Equation742_implies_Equation41 at h
    apply Subgraph.Equation41_implies_Equation381 at h
    apply Apply.Equation381_implies_Equation375 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 3 [eq375]
  symm
  apply h
@[equational_result]
theorem Equation877_implies_Equation15 (G: Type _) [Magma G] (h: Equation877 G) : Equation15 G := by
  have eq3715 (x y : G) : x ◇ y = (x ◇ x) ◇ (y ◇ y) := by
    apply Equation877_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation3715 at h
    apply h
  intro x y z
  symm
  nth_rewrite 2 [eq3715]
  symm
  apply h
@[equational_result]
theorem Equation899_implies_Equation15 (G: Type _) [Magma G] (h: Equation899 G) : Equation15 G := by
  have eq3725 (x y : G) : x ◇ y = (x ◇ y) ◇ (y ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation899_implies_Equation41 at h
    apply Subgraph.Equation41_implies_Equation3744 at h
    apply Apply.Equation3744_implies_Equation3728 at h
    apply Apply.Equation3728_implies_Equation3725 at h
    apply h
  intro x y z
  symm
  nth_rewrite 2 [eq3725]
  symm
  apply h
@[equational_result]
theorem Equation1604_implies_Equation1807 (G: Type _) [Magma G] (h: Equation1604 G) : Equation1807 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation1604_implies_Equation1553 at h
    apply Equation1553_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 2 [← eq4512]
  symm
  apply h
@[equational_result]
theorem Equation1607_implies_Equation1810 (G: Type _) [Magma G] (h: Equation1607 G) : Equation1810 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation1607_implies_Equation1572 at h
    apply Apply.Equation1572_implies_Equation1571 at h
    apply Subgraph.Equation1571_implies_Equation4512 at h
    apply h
  intro x y z w u
  symm
  nth_rewrite 2 [← eq4512]
  symm
  apply h
@[equational_result]
theorem Equation1757_implies_Equation188 (G: Type _) [Magma G] (h: Equation1757 G) : Equation188 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply Equation1757_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation375 at h
    apply h
  intro x y z
  symm
  nth_rewrite 3 [eq375]
  symm
  apply h
@[equational_result]
theorem Equation1758_implies_Equation189 (G: Type _) [Magma G] (h: Equation1758 G) : Equation189 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply Apply.Equation1758_implies_Equation1720 at h
    apply Equation1720_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation375 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 3 [eq375]
  symm
  apply h
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
@[equational_result]
theorem Equation1809_implies_Equation1606 (G: Type _) [Magma G] (h: Equation1809 G) : Equation1606 G := by
  have eq4435 (x y : G) : x ◇ (y ◇ x) = (x ◇ y) ◇ x := by
    apply Apply.Equation1809_implies_Equation1773 at h
    apply Equation1773_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation4512 at h
    apply Apply.Equation4512_implies_Equation4435 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4435]
  symm
  apply h
@[equational_result]
theorem Equation1889_implies_Equation171 (G: Type _) [Magma G] (h: Equation1889 G) : Equation171 G := by
  have eq326 (x y : G) : x ◇ y = x ◇ (y ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation1889_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3403 at h
    apply Apply.Equation3403_implies_Equation3320 at h
    apply Equation3320_implies_Equation326 at h
    apply h
  intro x y z
  symm
  nth_rewrite 2 [eq326]
  symm
  apply h
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
@[equational_result]
theorem Equation1899_implies_Equation1889 (G: Type _) [Magma G] (h: Equation1899 G) : Equation1889 G := by
  have eq4314 (x y : G) : x ◇ (y ◇ x) = x ◇ (y ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation1899_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation334 at h
    apply RewriteHypothesis.Equation334_implies_Equation4357 at h
    apply Apply.Equation4357_implies_Equation4315 at h
    apply Apply.Equation4315_implies_Equation4314 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4314]
  symm
  apply h
@[equational_result]
theorem Equation1903_implies_Equation2106 (G: Type _) [Magma G] (h: Equation1903 G) : Equation2106 G := by
  have eq4435 (x y : G) : x ◇ (y ◇ x) = (x ◇ y) ◇ x := by
    apply Apply.Equation1903_implies_Equation1896 at h
    apply Equation1896_implies_Equation776 at h
    apply Apply.Equation776_implies_Equation714 at h
    apply Equation714_implies_Equation4435 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4435]
  symm
  apply h
@[equational_result]
theorem Equation1911_implies_Equation2114 (G: Type _) [Magma G] (h: Equation1911 G) : Equation2114 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation1911_implies_Equation1909 at h
    apply Equation1909_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4512 y]
  symm
  apply h
@[equational_result]
theorem Equation1920_implies_Equation2123 (G: Type _) [Magma G] (h: Equation1920 G) : Equation2123 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation1920_implies_Equation1893 at h
    apply Apply.Equation1893_implies_Equation1891 at h
    apply Equation1891_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation4512 at h
    apply h
  intro x y z w u
  symm
  nth_rewrite 2 [← eq4512]
  symm
  apply h
@[equational_result]
theorem Equation1930_implies_Equation1893 (G: Type _) [Magma G] (h: Equation1930 G) : Equation1893 G := by
  have eq4284 (x y : G) : x ◇ (x ◇ y) = x ◇ (y ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation1930_implies_Equation41 at h
    apply Subgraph.Equation41_implies_Equation39 at h
    apply RewriteGoal.Equation39_implies_Equation4340 at h
    apply RewriteHypothesis.Equation4340_implies_Equation4284 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4284]
  symm
  apply h
@[equational_result]
theorem Equation1969_implies_Equation2172 (G: Type _) [Magma G] (h: Equation1969 G) : Equation2172 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation1969_implies_Equation1968 at h
    apply Equation1968_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 2 [← eq4512]
  symm
  apply h
@[equational_result]
theorem Equation1972_implies_Equation2175 (G: Type _) [Magma G] (h: Equation1972 G) : Equation2175 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation1972_implies_Equation1960 at h
    apply Equation1960_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 2 [← eq4512]
  symm
  apply h
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
@[equational_result]
theorem Equation2106_implies_Equation1930 (G: Type _) [Magma G] (h: Equation2106 G) : Equation1930 G := by
  have eq4398 (x y : G) : x ◇ (x ◇ y) = (x ◇ y) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation2106_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4176 at h
    apply Equation4176_implies_Equation4421 at h
    apply Apply.Equation4421_implies_Equation4398 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4398]
  symm
  apply h
@[equational_result]
theorem Equation2120_implies_Equation1917 (G: Type _) [Magma G] (h: Equation2120 G) : Equation1917 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2120_implies_Equation2094 at h
    apply Equation2094_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4512 y]
  symm
  apply h
@[equational_result]
theorem Equation2177_implies_Equation1974 (G: Type _) [Magma G] (h: Equation2177 G) : Equation1974 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation2177_implies_Equation41 at h
    apply Subgraph.Equation41_implies_Equation3744 at h
    apply Subgraph.Equation3744_implies_Equation4512 at h
    apply h
  intro x y z w u
  symm
  nth_rewrite 1 [eq4512 y]
  symm
  apply h
@[equational_result]
theorem Equation2298_implies_Equation2523 (G: Type _) [Magma G] (h: Equation2298 G) : Equation2523 G := by
  have eq4399 (x y : G) : x ◇ (x ◇ y) = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2298_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation3744 at h
    apply Equation3744_implies_Equation4520 at h
    apply Apply.Equation4520_implies_Equation4402 at h
    apply Apply.Equation4402_implies_Equation4399 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4399]
  symm
  apply h
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
@[equational_result]
theorem Equation2320_implies_Equation2523 (G: Type _) [Magma G] (h: Equation2320 G) : Equation2523 G := by
  have eq4473 (x y : G) : x ◇ (y ◇ y) = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2320_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation3744 at h
    apply Subgraph.Equation3744_implies_Equation4512 at h
    apply Apply.Equation4512_implies_Equation4473 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4473]
  symm
  apply h
@[equational_result]
theorem Equation2324_implies_Equation2527 (G: Type _) [Magma G] (h: Equation2324 G) : Equation2527 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2324_implies_Equation2312 at h
    apply RewriteHypothesisAndGoal.Equation2312_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation3744 at h
    apply Subgraph.Equation3744_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 2 [← eq4512]
  symm
  apply h
@[equational_result]
theorem Equation2325_implies_Equation2528 (G: Type _) [Magma G] (h: Equation2325 G) : Equation2528 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2325_implies_Equation2315 at h
    apply Equation2315_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 2 [← eq4512]
  symm
  apply h
@[equational_result]
theorem Equation2329_implies_Equation30 (G: Type _) [Magma G] (h: Equation2329 G) : Equation30 G := by
  have eq3309 (x y : G) : x ◇ y = x ◇ (x ◇ (y ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation2329_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3310 at h
    apply Apply.Equation3310_implies_Equation3309 at h
    apply h
  intro x y z
  symm
  nth_rewrite 2 [eq3309]
  symm
  apply h
@[equational_result]
theorem Equation2332_implies_Equation30 (G: Type _) [Magma G] (h: Equation2332 G) : Equation30 G := by
  have eq3308 (x y : G) : x ◇ y = x ◇ (x ◇ (y ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation2332_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4162 at h
    apply NthRewrites.Equation4162_implies_Equation3308 at h
    apply h
  intro x y z
  symm
  nth_rewrite 2 [eq3308]
  symm
  apply h
@[equational_result]
theorem Equation2339_implies_Equation30 (G: Type _) [Magma G] (h: Equation2339 G) : Equation30 G := by
  have eq3306 (x y : G) : x ◇ y = x ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation2339_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation3744 at h
    apply Apply.Equation3744_implies_Equation3740 at h
    apply Equation3740_implies_Equation3334 at h
    apply Apply.Equation3334_implies_Equation3306 at h
    apply h
  intro x y z
  symm
  nth_rewrite 2 [eq3306]
  symm
  apply h
@[equational_result]
theorem Equation2350_implies_Equation2553 (G: Type _) [Magma G] (h: Equation2350 G) : Equation2553 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2350_implies_Equation2348 at h
    apply Equation2348_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 2 [← eq4512]
  symm
  apply h
@[equational_result]
theorem Equation2366_implies_Equation2603 (G: Type _) [Magma G] (h: Equation2366 G) : Equation2603 G := by
  have eq4470 (x y : G) : x ◇ (y ◇ y) = (x ◇ x) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2366_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation387 at h
    apply Equation387_implies_Equation4470 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4470]
  symm
  apply h
@[equational_result]
theorem Equation2374_implies_Equation2603 (G: Type _) [Magma G] (h: Equation2374 G) : Equation2603 G := by
  have eq4433 (x y : G) : x ◇ (y ◇ x) = (x ◇ x) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2374_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4176 at h
    apply Equation4176_implies_Equation4461 at h
    apply Apply.Equation4461_implies_Equation4433 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4433]
  symm
  apply h
@[equational_result]
theorem Equation2378_implies_Equation2581 (G: Type _) [Magma G] (h: Equation2378 G) : Equation2581 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2378_implies_Equation2334 at h
    apply Equation2334_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 2 [← eq4512]
  symm
  apply h
@[equational_result]
theorem Equation2379_implies_Equation2582 (G: Type _) [Magma G] (h: Equation2379 G) : Equation2582 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2379_implies_Equation2369 at h
    apply Equation2369_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 2 [← eq4512]
  symm
  apply h
@[equational_result]
theorem Equation2400_implies_Equation2603 (G: Type _) [Magma G] (h: Equation2400 G) : Equation2603 G := by
  have eq4396 (x y : G) : x ◇ (x ◇ y) = (x ◇ x) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2400_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation3744 at h
    apply Subgraph.Equation3744_implies_Equation4512 at h
    apply Apply.Equation4512_implies_Equation4396 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4396]
  symm
  apply h
@[equational_result]
theorem Equation2417_implies_Equation2620 (G: Type _) [Magma G] (h: Equation2417 G) : Equation2620 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2417_implies_Equation2348 at h
    apply Equation2348_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4512 z]
  symm
  apply h
@[equational_result]
theorem Equation2501_implies_Equation226 (G: Type _) [Magma G] (h: Equation2501 G) : Equation226 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2501_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation381 at h
    apply Apply.Equation381_implies_Equation375 at h
    apply h
  intro x y z
  symm
  nth_rewrite 3 [eq375]
  symm
  apply h
@[equational_result]
theorem Equation2515_implies_Equation2501 (G: Type _) [Magma G] (h: Equation2515 G) : Equation2501 G := by
  have eq4598 (x y : G) : (x ◇ x) ◇ y = (x ◇ y) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation2515_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4176 at h
    apply Equation4176_implies_Equation4679 at h
    apply Apply.Equation4679_implies_Equation4598 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq4598]
  symm
  apply h
@[equational_result]
theorem Equation2523_implies_Equation2515 (G: Type _) [Magma G] (h: Equation2523 G) : Equation2515 G := by
  have eq4629 (x y : G) : (x ◇ y) ◇ x = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2523_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4215 at h
    apply Apply.Equation4215_implies_Equation4132 at h
    apply NthRewrites.Equation4132_implies_Equation4654 at h
    apply RewriteHypothesis.Equation4654_implies_Equation4629 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq4629]
  symm
  apply h
@[equational_result]
theorem Equation2527_implies_Equation2324 (G: Type _) [Magma G] (h: Equation2527 G) : Equation2324 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2527_implies_Equation2510 at h
    apply Equation2510_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4512 x z]
  symm
  apply h
@[equational_result]
theorem Equation2532_implies_Equation30 (G: Type _) [Magma G] (h: Equation2532 G) : Equation30 G := by
  have eq3512 (x y : G) : x ◇ y = x ◇ ((x ◇ y) ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation2532_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3623 at h
    apply Apply.Equation3623_implies_Equation3513 at h
    apply Apply.Equation3513_implies_Equation3512 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq3512 y]
  symm
  apply h
@[equational_result]
theorem Equation2535_implies_Equation30 (G: Type _) [Magma G] (h: Equation2535 G) : Equation30 G := by
  have eq3511 (x y : G) : x ◇ y = x ◇ ((x ◇ y) ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation2535_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3620 at h
    apply Apply.Equation3620_implies_Equation3511 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq3511 y]
  symm
  apply h
@[equational_result]
theorem Equation2539_implies_Equation2336 (G: Type _) [Magma G] (h: Equation2539 G) : Equation2336 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2539_implies_Equation2532 at h
    apply RewriteHypothesisAndGoal.Equation2532_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation3744 at h
    apply Subgraph.Equation3744_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 2 [eq4512]
  symm
  apply h
@[equational_result]
theorem Equation2542_implies_Equation30 (G: Type _) [Magma G] (h: Equation2542 G) : Equation30 G := by
  have eq3509 (x y : G) : x ◇ y = x ◇ ((x ◇ x) ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation2542_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation3744 at h
    apply Apply.Equation3744_implies_Equation3740 at h
    apply Equation3740_implies_Equation3537 at h
    apply Apply.Equation3537_implies_Equation3509 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq3509 y]
  symm
  apply h
@[equational_result]
theorem Equation2569_implies_Equation240 (G: Type _) [Magma G] (h: Equation2569 G) : Equation240 G := by
  have eq378 (x y : G) : x ◇ y = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2569_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation381 at h
    apply Apply.Equation381_implies_Equation378 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq378 z]
  symm
  apply h
@[equational_result]
theorem Equation2577_implies_Equation2569 (G: Type _) [Magma G] (h: Equation2577 G) : Equation2569 G := by
  have eq4629 (x y : G) : (x ◇ y) ◇ x = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2577_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4215 at h
    apply Apply.Equation4215_implies_Equation4132 at h
    apply NthRewrites.Equation4132_implies_Equation4654 at h
    apply RewriteHypothesis.Equation4654_implies_Equation4629 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4629]
  symm
  apply h
@[equational_result]
theorem Equation2603_implies_Equation2577 (G: Type _) [Magma G] (h: Equation2603 G) : Equation2577 G := by
  have eq4598 (x y : G) : (x ◇ x) ◇ y = (x ◇ y) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation2603_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4176 at h
    apply Equation4176_implies_Equation4679 at h
    apply Apply.Equation4679_implies_Equation4598 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4598]
  symm
  apply h
@[equational_result]
theorem Equation2620_implies_Equation2417 (G: Type _) [Magma G] (h: Equation2620 G) : Equation2417 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2620_implies_Equation2551 at h
    apply Equation2551_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4512 z]
  symm
  apply h
@[equational_result]
theorem Equation2711_implies_Equation30 (G: Type _) [Magma G] (h: Equation2711 G) : Equation30 G := by
  have eq3721 (x y : G) : x ◇ y = (x ◇ y) ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation2711_implies_Equation3849 at h
    apply RewriteHypothesisAndGoal.Equation3849_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3398 at h
    apply RewriteHypothesisAndGoal.Equation3398_implies_Equation3721 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq3721 y]
  symm
  apply h
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
@[equational_result]
theorem Equation2738_implies_Equation30 (G: Type _) [Magma G] (h: Equation2738 G) : Equation30 G := by
  have eq3714 (x y : G) : x ◇ y = (x ◇ x) ◇ (y ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation2738_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply Equation3404_implies_Equation4197 at h
    apply RewriteHypothesisAndGoal.Equation4197_implies_Equation3714 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq3714 y]
  symm
  apply h
@[equational_result]
theorem Equation2745_implies_Equation30 (G: Type _) [Magma G] (h: Equation2745 G) : Equation30 G := by
  have eq3712 (x y : G) : x ◇ y = (x ◇ x) ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation2745_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation3744 at h
    apply Apply.Equation3744_implies_Equation3718 at h
    apply Apply.Equation3718_implies_Equation3712 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq3712 y]
  symm
  apply h
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
@[equational_result]
theorem Equation2908_implies_Equation3148 (G: Type _) [Magma G] (h: Equation2908 G) : Equation3148 G := by
  have eq4470 (x y : G) : x ◇ (y ◇ y) = (x ◇ x) ◇ y := by
    apply Apply.Equation2908_implies_Equation2904 at h
    apply RewriteHypothesisAndGoal.Equation2904_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation387 at h
    apply Equation387_implies_Equation4470 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4470]
  symm
  apply h
@[equational_result]
theorem Equation2933_implies_Equation3136 (G: Type _) [Magma G] (h: Equation2933 G) : Equation3136 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2933_implies_Equation2905 at h
    apply Equation2905_implies_Equation5 at h
    apply Subgraph.Equation5_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4512 y]
  symm
  apply h
@[equational_result]
theorem Equation2935_implies_Equation3138 (G: Type _) [Magma G] (h: Equation2935 G) : Equation3138 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2935_implies_Equation2908 at h
    apply Apply.Equation2908_implies_Equation2905 at h
    apply Equation2905_implies_Equation5 at h
    apply Subgraph.Equation5_implies_Equation4512 at h
    apply h
  intro x y z w u
  symm
  nth_rewrite 1 [← eq4512 y]
  symm
  apply h
@[equational_result]
theorem Equation2987_implies_Equation3190 (G: Type _) [Magma G] (h: Equation2987 G) : Equation3190 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2987_implies_Equation2905 at h
    apply Equation2905_implies_Equation5 at h
    apply Subgraph.Equation5_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4512 y]
  symm
  apply h
@[equational_result]
theorem Equation2989_implies_Equation3192 (G: Type _) [Magma G] (h: Equation2989 G) : Equation3192 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2989_implies_Equation2908 at h
    apply Apply.Equation2908_implies_Equation2905 at h
    apply Equation2905_implies_Equation5 at h
    apply Subgraph.Equation5_implies_Equation4512 at h
    apply h
  intro x y z w u
  symm
  nth_rewrite 1 [← eq4512 y]
  symm
  apply h
@[equational_result]
theorem Equation3111_implies_Equation3148 (G: Type _) [Magma G] (h: Equation3111 G) : Equation3148 G := by
  have eq4599 (x y : G) : (x ◇ x) ◇ y = (x ◇ y) ◇ y := by
    apply Apply.Equation3111_implies_Equation3104 at h
    apply Equation3104_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation38 at h
    apply RewriteGoal.Equation38_implies_Equation4602 at h
    apply Apply.Equation4602_implies_Equation4599 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4599]
  symm
  apply h
@[equational_result]
theorem Equation3121_implies_Equation3111 (G: Type _) [Magma G] (h: Equation3121 G) : Equation3111 G := by
  have eq4629 (x y : G) : (x ◇ y) ◇ x = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation3121_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4628 at h
    apply Apply.Equation4628_implies_Equation4604 at h
    apply RewriteCombinations.Equation4604_implies_Equation4632 at h
    apply Apply.Equation4632_implies_Equation4629 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4629]
  symm
  apply h
@[equational_result]
theorem Equation3129_implies_Equation2926 (G: Type _) [Magma G] (h: Equation3129 G) : Equation2926 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation3129_implies_Equation3107 at h
    apply Equation3107_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4512]
  symm
  apply h
@[equational_result]
theorem Equation3137_implies_Equation2934 (G: Type _) [Magma G] (h: Equation3137 G) : Equation2934 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation3137_implies_Equation3110 at h
    apply Equation3110_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4512]
  symm
  apply h
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
@[equational_result]
theorem Equation3162_implies_Equation293 (G: Type _) [Magma G] (h: Equation3162 G) : Equation293 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply Apply.Equation3162_implies_Equation3159 at h
    apply Equation3159_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation375 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq375 y]
  symm
  apply h
@[equational_result]
theorem Equation3187_implies_Equation2984 (G: Type _) [Magma G] (h: Equation3187 G) : Equation2984 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation3187_implies_Equation3104 at h
    apply Equation3104_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4512]
  symm
  apply h
@[equational_result]
theorem Equation3189_implies_Equation2986 (G: Type _) [Magma G] (h: Equation3189 G) : Equation2986 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation3189_implies_Equation3146 at h
    apply Equation3146_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation4512 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4512]
  symm
  apply h
@[equational_result]
theorem Equation3213_implies_Equation3162 (G: Type _) [Magma G] (h: Equation3213 G) : Equation3162 G := by
  have eq4599 (x y : G) : (x ◇ x) ◇ y = (x ◇ y) ◇ y := by
    apply Apply.Equation3213_implies_Equation3104 at h
    apply Equation3104_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation38 at h
    apply RewriteGoal.Equation38_implies_Equation4602 at h
    apply Apply.Equation4602_implies_Equation4599 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4599]
  symm
  apply h
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
    apply Apply.Equation3436_implies_Equation3330 at h
    apply NthRewrites.Equation3330_implies_Equation4340 at h
    apply RewriteHypothesis.Equation4340_implies_Equation4284 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [eq4284]
  symm
  apply h
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
@[equational_result]
theorem Equation4159_implies_Equation4156 (G: Type _) [Magma G] (h: Equation4159 G) : Equation4156 G := by
  have eq4629 (x y : G) : (x ◇ y) ◇ x = (x ◇ y) ◇ y := by
    apply NthRewrites.Equation4159_implies_Equation4407 at h
    apply RewriteHypothesis.Equation4407_implies_Equation4672 at h
    apply Apply.Equation4672_implies_Equation4630 at h
    apply Apply.Equation4630_implies_Equation4629 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4629]
  symm
  apply h
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
@[equational_result]
theorem Equation9_implies_Equation1224 (G: Type _) [Magma G] (h: Equation9 G) : Equation1224 G := by
  have eq4118 (x y : G) : x ◇ y = ((x ◇ x) ◇ x) ◇ y := by
    apply Apply.Equation9_implies_Equation51 at h
    apply Apply.Equation51_implies_Equation425 at h
    apply Equation425_implies_Equation1630 at h
    apply Equation1630_implies_Equation23 at h
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
    apply Apply.Equation9_implies_Equation51 at h
    apply Apply.Equation51_implies_Equation425 at h
    apply Apply.Equation425_implies_Equation415 at h
    apply Apply.Equation415_implies_Equation412 at h
    apply Equation412_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation3722 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq3722]
  symm
  apply h
@[equational_result]
theorem Equation3293_implies_Equation320 (G: Type _) [Magma G] (h: Equation3293 G) : Equation320 G := by
  have eq312 (x y : G) : x ◇ x = y ◇ (x ◇ x) := by
    apply RewriteCombinations.Equation3293_implies_Equation312 at h
    apply h
  have eq3258 (x y : G) : x ◇ x = x ◇ (y ◇ (x ◇ x)) := by
    apply Apply.Equation3293_implies_Equation3258 at h
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
    apply Apply.Equation4097_implies_Equation4067 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq360]
  nth_rewrite 1 [eq4067]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3344_implies_Equation3348 (G: Type _) [Magma G] (h: Equation3344 G) : Equation3348 G := by
  have eq4283 (x y : G) : x ◇ (x ◇ y) = x ◇ (y ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation3344_implies_Equation332 at h
    apply Equation332_implies_Equation387 at h
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
theorem Equation3405_implies_Equation3451 (G: Type _) [Magma G] (h: Equation3405 G) : Equation3451 G := by
  have eq3338 (x y z w : G) : x ◇ y = x ◇ (z ◇ (w ◇ y)) := by
    apply Apply.Equation3405_implies_Equation3356 at h
    apply Equation3356_implies_Equation3451 at h
    apply Apply.Equation3451_implies_Equation3338 at h
    apply h
  have eq3316 (x y : G) : x ◇ y = x ◇ (y ◇ (x ◇ y)) := by
    apply Apply.Equation3405_implies_Equation3316 at h
    apply h
  intro x y z w u
  symm
  nth_rewrite 1 [← eq3338]
  nth_rewrite 1 [eq3316]
  symm
  apply h
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
theorem Equation3568_implies_Equation3581 (G: Type _) [Magma G] (h: Equation3568 G) : Equation3581 G := by
  have eq3565 (x y z : G) : x ◇ y = y ◇ ((z ◇ x) ◇ x) := by
    apply Apply.Equation3568_implies_Equation3565 at h
    apply h
  have eq3553 (x y z : G) : x ◇ y = y ◇ ((x ◇ z) ◇ z) := by
    apply Apply.Equation3568_implies_Equation3567 at h
    apply Equation3567_implies_Equation3370 at h
    apply NthRewrites.Equation3370_implies_Equation3553 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [eq3565]
  nth_rewrite 1 [← eq3553]
  apply h
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
    apply Equation387_implies_Equation4470 at h
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
    apply Apply.Equation9_implies_Equation51 at h
    apply Apply.Equation51_implies_Equation425 at h
    apply Apply.Equation425_implies_Equation421 at h
    apply Equation421_implies_Equation4395 at h
    apply Apply.Equation4395_implies_Equation4380 at h
    apply h
  have eq308 (x y : G) : x ◇ x = x ◇ (x ◇ y) := by
    apply Equation9_implies_Equation308 at h
    apply h
  have eq4268 (x y : G) : x ◇ (x ◇ x) = x ◇ (x ◇ y) := by
    apply RewriteHypothesis.Equation9_implies_Equation4282 at h
    apply Apply.Equation4282_implies_Equation4268 at h
    apply h
  have eq3 (x : G) : x = x ◇ x := by
    apply Apply.Equation9_implies_Equation51 at h
    apply Apply.Equation51_implies_Equation425 at h
    apply Apply.Equation425_implies_Equation415 at h
    apply Apply.Equation415_implies_Equation412 at h
    apply Equation412_implies_Equation3 at h
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
    apply Apply.Equation9_implies_Equation51 at h
    apply Apply.Equation51_implies_Equation425 at h
    apply Apply.Equation425_implies_Equation415 at h
    apply Apply.Equation415_implies_Equation412 at h
    apply Equation412_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation375 at h
    apply h
  have eq3864 (x y : G) : x ◇ x = (x ◇ (x ◇ y)) ◇ x := by
    apply RewriteHypothesis.Equation9_implies_Equation3921 at h
    apply Apply.Equation3921_implies_Equation3864 at h
    apply h
  have eq308 (x y : G) : x ◇ x = x ◇ (x ◇ y) := by
    apply Equation9_implies_Equation308 at h
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
theorem Equation9_implies_Equation152 (G: Type _) [Magma G] (h: Equation9 G) : Equation152 G := by
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply Equation9_implies_Equation308 at h
    apply Apply.Equation308_implies_Equation307 at h
    apply h
  have eq3 (x : G) : x = x ◇ x := by
    apply Apply.Equation9_implies_Equation51 at h
    apply Apply.Equation51_implies_Equation425 at h
    apply Apply.Equation425_implies_Equation415 at h
    apply Apply.Equation415_implies_Equation412 at h
    apply Equation412_implies_Equation3 at h
    apply h
  have eq1833 (x y : G) : x = (x ◇ (x ◇ x)) ◇ (x ◇ y) := by
    apply RewriteHypothesis.Equation9_implies_Equation1839 at h
    apply Apply.Equation1839_implies_Equation1833 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Apply.Equation9_implies_Equation8 at h
    apply h
  have eq4268 (x y : G) : x ◇ (x ◇ x) = x ◇ (x ◇ y) := by
    apply RewriteHypothesis.Equation9_implies_Equation4282 at h
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
    apply Equation9_implies_Equation4395 at h
    apply Apply.Equation4395_implies_Equation4380 at h
    apply h
  have eq3 (x : G) : x = x ◇ x := by
    apply Apply.Equation9_implies_Equation51 at h
    apply Apply.Equation51_implies_Equation425 at h
    apply Apply.Equation425_implies_Equation415 at h
    apply Apply.Equation415_implies_Equation412 at h
    apply Equation412_implies_Equation3 at h
    apply h
  have eq1833 (x y : G) : x = (x ◇ (x ◇ x)) ◇ (x ◇ y) := by
    apply RewriteHypothesis.Equation9_implies_Equation1839 at h
    apply Apply.Equation1839_implies_Equation1833 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Apply.Equation9_implies_Equation8 at h
    apply h
  have eq4268 (x y : G) : x ◇ (x ◇ x) = x ◇ (x ◇ y) := by
    apply RewriteHypothesis.Equation9_implies_Equation4282 at h
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
    apply Equation9_implies_Equation308 at h
    apply Apply.Equation308_implies_Equation307 at h
    apply h
  have eq1833 (x y : G) : x = (x ◇ (x ◇ x)) ◇ (x ◇ y) := by
    apply RewriteHypothesis.Equation9_implies_Equation1839 at h
    apply Apply.Equation1839_implies_Equation1833 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Apply.Equation9_implies_Equation8 at h
    apply h
  have eq4268 (x y : G) : x ◇ (x ◇ x) = x ◇ (x ◇ y) := by
    apply RewriteHypothesis.Equation9_implies_Equation4282 at h
    apply Apply.Equation4282_implies_Equation4268 at h
    apply h
  have eq3 (x : G) : x = x ◇ x := by
    apply Apply.Equation9_implies_Equation51 at h
    apply Apply.Equation51_implies_Equation425 at h
    apply Apply.Equation425_implies_Equation415 at h
    apply Apply.Equation415_implies_Equation412 at h
    apply Equation412_implies_Equation3 at h
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
theorem Equation3356_implies_Equation3300 (G: Type _) [Magma G] (h: Equation3356 G) : Equation3300 G := by
  have eq3338 (x y z w : G) : x ◇ y = x ◇ (z ◇ (w ◇ y)) := by
    apply Equation3356_implies_Equation3451 at h
    apply Apply.Equation3451_implies_Equation3338 at h
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
theorem Equation954_implies_Equation988 (G: Type _) [Magma G] (h: Equation954 G) : Equation988 G := by
  have eq10 (x y : G) : x = x ◇ (y ◇ x) := by
    apply Apply.Equation954_implies_Equation871 at h
    apply Equation871_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation4 at h
    apply Apply.Equation4_implies_Equation12 at h
    apply Apply.Equation12_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply Apply.Equation954_implies_Equation871 at h
    apply Equation871_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation14 at h
    apply RewriteHypothesis.Equation14_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq871 (x y z : G) : x = y ◇ ((x ◇ x) ◇ (x ◇ z)) := by
    apply Apply.Equation954_implies_Equation871 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Apply.Equation954_implies_Equation871 at h
    apply Equation871_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation8 at h
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
    apply Apply.Equation957_implies_Equation839 at h
    apply Equation839_implies_Equation1260 at h
    apply Equation1260_implies_Equation10 at h
    apply h
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply Apply.Equation957_implies_Equation953 at h
    apply Subgraph.Equation953_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation14 at h
    apply RewriteHypothesis.Equation14_implies_Equation4332 at h
    apply Apply.Equation4332_implies_Equation4273 at h
    apply h
  have eq875 (x y z : G) : x = y ◇ ((x ◇ x) ◇ (z ◇ x)) := by
    apply Apply.Equation957_implies_Equation875 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Apply.Equation957_implies_Equation953 at h
    apply Subgraph.Equation953_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation8 at h
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
theorem Equation9_implies_Equation1630 (G: Type _) [Magma G] (h: Equation9 G) : Equation1630 G := by
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Apply.Equation9_implies_Equation8 at h
    apply h
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply Apply.Equation9_implies_Equation51 at h
    apply Apply.Equation51_implies_Equation425 at h
    apply Apply.Equation425_implies_Equation415 at h
    apply Apply.Equation415_implies_Equation412 at h
    apply Equation412_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation375 at h
    apply h
  have eq3 (x : G) : x = x ◇ x := by
    apply Apply.Equation9_implies_Equation51 at h
    apply Apply.Equation51_implies_Equation425 at h
    apply Apply.Equation425_implies_Equation415 at h
    apply Apply.Equation415_implies_Equation412 at h
    apply Equation412_implies_Equation3 at h
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
theorem Equation591_implies_Equation1529 (G: Type _) [Magma G] (h: Equation591 G) : Equation1529 G := by
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation591_implies_Equation485 at h
    apply Equation485_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  have eq3282 (x y : G) : x ◇ x = y ◇ (y ◇ (y ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3381 at h
    apply RewriteHypothesis.Equation3381_implies_Equation3423 at h
    apply SimpleRewrites.Equation3423_implies_Equation3282 at h
    apply h
  have eq1426 (x : G) : x = (x ◇ x) ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation591_implies_Equation485 at h
    apply Equation485_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation1426 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3381 at h
    apply SimpleRewrites.Equation3381_implies_Equation3269 at h
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
theorem Equation591_implies_Equation244 (G: Type _) [Magma G] (h: Equation591 G) : Equation244 G := by
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation591_implies_Equation485 at h
    apply Equation485_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  have eq3903 (x y z : G) : x ◇ x = (y ◇ (z ◇ y)) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4052 at h
    apply SimpleRewrites.Equation4052_implies_Equation3903 at h
    apply h
  have eq3255 (x y : G) : x ◇ x = x ◇ (x ◇ (y ◇ x)) := by
    apply RewriteHypothesisAndGoal.Equation591_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3361 at h
    apply Apply.Equation3361_implies_Equation3257 at h
    apply Apply.Equation3257_implies_Equation3255 at h
    apply h
  have eq49 (x y : G) : x = x ◇ (x ◇ (y ◇ x)) := by
    apply Apply.Equation591_implies_Equation448 at h
    apply Equation448_implies_Equation441 at h
    apply Equation441_implies_Equation649 at h
    apply Equation649_implies_Equation58 at h
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
    apply Apply.Equation1606_implies_Equation1570 at h
    apply Equation1570_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation151 at h
    apply h
  have eq3688 (x y : G) : x ◇ x = (y ◇ y) ◇ (y ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation1606_implies_Equation41 at h
    apply RewriteHypothesis.Equation41_implies_Equation3829 at h
    apply SimpleRewrites.Equation3829_implies_Equation3688 at h
    apply h
  have eq1832 (x : G) : x = (x ◇ (x ◇ x)) ◇ (x ◇ x) := by
    apply Apply.Equation1606_implies_Equation1537 at h
    apply Equation1537_implies_Equation14 at h
    apply Subgraph.Equation14_implies_Equation8 at h
    apply RewriteHypothesis.Equation8_implies_Equation1832 at h
    apply h
  have eq3659 (x : G) : x ◇ x = (x ◇ x) ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation1606_implies_Equation41 at h
    apply Subgraph.Equation41_implies_Equation3722 at h
    apply Apply.Equation3722_implies_Equation3659 at h
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
theorem Equation48_implies_Equation615 (G: Type _) [Magma G] (h: Equation48 G) : Equation615 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply Apply.Equation48_implies_Equation415 at h
    apply Apply.Equation415_implies_Equation412 at h
    apply Equation412_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation375 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq375]
  symm
  apply h
@[equational_result]
theorem Equation57_implies_Equation61 (G: Type _) [Magma G] (h: Equation57 G) : Equation61 G := by
  have eq3267 (x y z w : G) : x ◇ x = x ◇ (y ◇ (z ◇ w)) := by
    apply Apply.Equation57_implies_Equation445 at h
    apply Apply.Equation445_implies_Equation441 at h
    apply Equation441_implies_Equation4 at h
    apply Subgraph.Equation4_implies_Equation42 at h
    apply Apply.Equation42_implies_Equation3332 at h
    apply Equation3332_implies_Equation3341 at h
    apply SimpleRewrites.Equation3341_implies_Equation3267 at h
    apply h
  have eq3263 (x y z : G) : x ◇ x = x ◇ (y ◇ (y ◇ z)) := by
    apply Apply.Equation57_implies_Equation445 at h
    apply Apply.Equation445_implies_Equation441 at h
    apply Equation441_implies_Equation4 at h
    apply Subgraph.Equation4_implies_Equation42 at h
    apply Apply.Equation42_implies_Equation3332 at h
    apply Equation3332_implies_Equation3341 at h
    apply SimpleRewrites.Equation3341_implies_Equation3267 at h
    apply Apply.Equation3267_implies_Equation3263 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq3267]
  nth_rewrite 1 [eq3263]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation64_implies_Equation98 (G: Type _) [Magma G] (h: Equation64 G) : Equation98 G := by
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply Apply.Equation64_implies_Equation1555 at h
    apply Apply.Equation1555_implies_Equation1517 at h
    apply Equation1517_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3455 at h
    apply SimpleRewrites.Equation3455_implies_Equation3304 at h
    apply h
  have eq3270 (x y z : G) : x ◇ x = y ◇ (x ◇ (x ◇ z)) := by
    apply Apply.Equation64_implies_Equation1555 at h
    apply Apply.Equation1555_implies_Equation1517 at h
    apply Equation1517_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3382 at h
    apply SimpleRewrites.Equation3382_implies_Equation3270 at h
    apply h
  intro x y z w u
  symm
  nth_rewrite 1 [← eq3304]
  nth_rewrite 1 [eq3270]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation270_implies_Equation2899 (G: Type _) [Magma G] (h: Equation270 G) : Equation2899 G := by
  have eq326 (x y : G) : x ◇ y = x ◇ (y ◇ y) := by
    apply Apply.Equation270_implies_Equation3176 at h
    apply Apply.Equation3176_implies_Equation3102 at h
    apply Equation3102_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq326]
  symm
  apply h
@[equational_result]
theorem Equation3344_implies_Equation4247 (G: Type _) [Magma G] (h: Equation3344 G) : Equation4247 G := by
  have eq4243 (x y z w : G) : x ◇ y = ((z ◇ w) ◇ x) ◇ y := by
    apply Equation3344_implies_Equation3348 at h
    apply NthRewrites.Equation3348_implies_Equation395 at h
    apply Apply.Equation395_implies_Equation4243 at h
    apply h
  have eq3320 (x y z : G) : x ◇ y = x ◇ (y ◇ (y ◇ z)) := by
    apply Equation3344_implies_Equation3348 at h
    apply Equation3348_implies_Equation4178 at h
    apply NthRewrites.Equation4178_implies_Equation327 at h
    apply Apply.Equation327_implies_Equation3324 at h
    apply Apply.Equation3324_implies_Equation3320 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4243]
  nth_rewrite 1 [eq3320]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation51_implies_Equation9 (G: Type _) [Magma G] (h: Equation51 G) : Equation9 G := by
  have eq326 (x y : G) : x ◇ y = x ◇ (y ◇ y) := by
    apply Apply.Equation51_implies_Equation425 at h
    apply Apply.Equation425_implies_Equation423 at h
    apply Equation423_implies_Equation3320 at h
    apply Equation3320_implies_Equation326 at h
    apply h
  have eq3256 (x y : G) : x ◇ x = x ◇ (x ◇ (y ◇ y)) := by
    apply Apply.Equation51_implies_Equation628 at h
    apply Apply.Equation628_implies_Equation627 at h
    apply Equation627_implies_Equation9 at h
    apply Equation9_implies_Equation308 at h
    apply Apply.Equation308_implies_Equation3257 at h
    apply Apply.Equation3257_implies_Equation3256 at h
    apply h
  have eq3257 (x y z : G) : x ◇ x = x ◇ (x ◇ (y ◇ z)) := by
    apply Apply.Equation51_implies_Equation628 at h
    apply Apply.Equation628_implies_Equation627 at h
    apply Equation627_implies_Equation9 at h
    apply Equation9_implies_Equation308 at h
    apply Apply.Equation308_implies_Equation3257 at h
    apply h
  intro x y
  symm
  nth_rewrite 2 [eq326]
  nth_rewrite 1 [← eq3256]
  nth_rewrite 1 [eq3257]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation54_implies_Equation631 (G: Type _) [Magma G] (h: Equation54 G) : Equation631 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply Apply.Equation54_implies_Equation435 at h
    apply Apply.Equation435_implies_Equation415 at h
    apply Apply.Equation415_implies_Equation412 at h
    apply Equation412_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation375 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq375]
  symm
  apply h
@[equational_result]
theorem Equation292_implies_Equation1123 (G: Type _) [Magma G] (h: Equation292 G) : Equation1123 G := by
  have eq23 (x : G) : x = (x ◇ x) ◇ x := by
    apply Apply.Equation292_implies_Equation3230 at h
    apply Apply.Equation3230_implies_Equation3124 at h
    apply Equation3124_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation23 at h
    apply h
  have eq4591 (x y : G) : (x ◇ x) ◇ x = (y ◇ y) ◇ y := by
    apply Apply.Equation292_implies_Equation3230 at h
    apply Apply.Equation3230_implies_Equation3124 at h
    apply Equation3124_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4251 at h
    apply SimpleRewrites.Equation4251_implies_Equation4103 at h
    apply Apply.Equation4103_implies_Equation4102 at h
    apply RewriteCombinations.Equation4102_implies_Equation4591 at h
    apply h
  have eq1020 (x : G) : x = x ◇ ((x ◇ (x ◇ x)) ◇ x) := by
    apply Apply.Equation292_implies_Equation3230 at h
    apply Apply.Equation3230_implies_Equation3124 at h
    apply Equation3124_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation8 at h
    apply RewriteHypothesis.Equation8_implies_Equation1020 at h
    apply h
  intro x y
  nth_rewrite 1 [eq23 x]
  nth_rewrite 1 [← eq4591]
  symm
  nth_rewrite 1 [← eq1020]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq23]
  apply h
  repeat assumption
@[equational_result]
theorem Equation67_implies_Equation920 (G: Type _) [Magma G] (h: Equation67 G) : Equation920 G := by
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Apply.Equation67_implies_Equation482 at h
    apply Apply.Equation482_implies_Equation475 at h
    apply Apply.Equation475_implies_Equation474 at h
    apply Equation474_implies_Equation8 at h
    apply h
  have eq4276 (x y : G) : x ◇ (x ◇ x) = y ◇ (y ◇ y) := by
    apply Apply.Equation67_implies_Equation482 at h
    apply Apply.Equation482_implies_Equation475 at h
    apply Equation475_implies_Equation750 at h
    apply Equation750_implies_Equation751 at h
    apply Equation751_implies_Equation2932 at h
    apply Apply.Equation2932_implies_Equation2920 at h
    apply Equation2920_implies_Equation1151 at h
    apply Equation1151_implies_Equation689 at h
    apply Apply.Equation689_implies_Equation688 at h
    apply Equation688_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3390 at h
    apply SimpleRewrites.Equation3390_implies_Equation3273 at h
    apply RewriteCombinations.Equation3273_implies_Equation4276 at h
    apply h
  have eq817 (x : G) : x = x ◇ ((x ◇ x) ◇ (x ◇ x)) := by
    apply Equation67_implies_Equation3144 at h
    apply Equation3144_implies_Equation1490 at h
    apply Equation1490_implies_Equation874 at h
    apply Apply.Equation874_implies_Equation818 at h
    apply Apply.Equation818_implies_Equation817 at h
    apply h
  intro x y
  nth_rewrite 1 [eq8 x]
  nth_rewrite 1 [← eq4276]
  symm
  nth_rewrite 1 [← eq817]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1973_implies_Equation1980 (G: Type _) [Magma G] (h: Equation1973 G) : Equation1980 G := by
  have eq1851 (x y : G) : x = (x ◇ (y ◇ x)) ◇ (y ◇ y) := by
    apply Apply.Equation1973_implies_Equation1855 at h
    apply Apply.Equation1855_implies_Equation1851 at h
    apply h
  have eq1894 (x y : G) : x = (y ◇ (x ◇ y)) ◇ (x ◇ x) := by
    apply Apply.Equation1973_implies_Equation1963 at h
    apply Equation1963_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation14 at h
    apply RewriteHypothesis.Equation14_implies_Equation1977 at h
    apply Apply.Equation1977_implies_Equation1894 at h
    apply h
  have eq1832 (x : G) : x = (x ◇ (x ◇ x)) ◇ (x ◇ x) := by
    apply Apply.Equation1973_implies_Equation1855 at h
    apply Apply.Equation1855_implies_Equation1835 at h
    apply Apply.Equation1835_implies_Equation1832 at h
    apply h
  have eq1847 (x y : G) : x = (x ◇ (y ◇ x)) ◇ (x ◇ x) := by
    apply Apply.Equation1973_implies_Equation1855 at h
    apply Apply.Equation1855_implies_Equation1847 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq1851 x]
  nth_rewrite 1 [← eq1894]
  nth_rewrite 1 [eq1832 y]
  symm
  nth_rewrite 1 [← eq1847]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq1832]
  apply h
@[equational_result]
theorem Equation1973_implies_Equation1985 (G: Type _) [Magma G] (h: Equation1973 G) : Equation1985 G := by
  have eq1851 (x y : G) : x = (x ◇ (y ◇ x)) ◇ (y ◇ y) := by
    apply Apply.Equation1973_implies_Equation1855 at h
    apply Apply.Equation1855_implies_Equation1851 at h
    apply h
  have eq1894 (x y : G) : x = (y ◇ (x ◇ y)) ◇ (x ◇ x) := by
    apply Apply.Equation1973_implies_Equation1963 at h
    apply Equation1963_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation14 at h
    apply RewriteHypothesis.Equation14_implies_Equation1977 at h
    apply Apply.Equation1977_implies_Equation1894 at h
    apply h
  have eq1832 (x : G) : x = (x ◇ (x ◇ x)) ◇ (x ◇ x) := by
    apply Apply.Equation1973_implies_Equation1855 at h
    apply Apply.Equation1855_implies_Equation1835 at h
    apply Apply.Equation1835_implies_Equation1832 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq1851 x]
  nth_rewrite 1 [← eq1894]
  nth_rewrite 1 [eq1832 y]
  symm
  nth_rewrite 1 [← eq1851]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq1832]
  apply h
@[equational_result]
theorem Equation1973_implies_Equation1990 (G: Type _) [Magma G] (h: Equation1973 G) : Equation1990 G := by
  have eq1851 (x y : G) : x = (x ◇ (y ◇ x)) ◇ (y ◇ y) := by
    apply Apply.Equation1973_implies_Equation1855 at h
    apply Apply.Equation1855_implies_Equation1851 at h
    apply h
  have eq1894 (x y : G) : x = (y ◇ (x ◇ y)) ◇ (x ◇ x) := by
    apply Equation1973_implies_Equation1985 at h
    apply SimpleRewrites.Equation1985_implies_Equation1894 at h
    apply h
  have eq1832 (x : G) : x = (x ◇ (x ◇ x)) ◇ (x ◇ x) := by
    apply Apply.Equation1973_implies_Equation1855 at h
    apply Apply.Equation1855_implies_Equation1835 at h
    apply Apply.Equation1835_implies_Equation1832 at h
    apply h
  have eq1855 (x y z : G) : x = (x ◇ (y ◇ x)) ◇ (z ◇ z) := by
    apply Apply.Equation1973_implies_Equation1855 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq1851 x]
  nth_rewrite 1 [← eq1894]
  nth_rewrite 1 [eq1832 y]
  symm
  nth_rewrite 1 [← eq1855]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq1832]
  apply h
@[equational_result]
theorem Equation4277_implies_Equation4308 (G: Type _) [Magma G] (h: Equation4277 G) : Equation4308 G := by
  intro x y z w
  nth_rewrite 1 [← h]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4258_implies_Equation45 (G: Type _) [Magma G] (h: Equation4258 G) : Equation45 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4253_implies_Equation45 (G: Type _) [Magma G] (h: Equation4253 G) : Equation45 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4234_implies_Equation45 (G: Type _) [Magma G] (h: Equation4234 G) : Equation45 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4230_implies_Equation45 (G: Type _) [Magma G] (h: Equation4230 G) : Equation45 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4217_implies_Equation45 (G: Type _) [Magma G] (h: Equation4217 G) : Equation45 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4213_implies_Equation45 (G: Type _) [Magma G] (h: Equation4213 G) : Equation45 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4183_implies_Equation45 (G: Type _) [Magma G] (h: Equation4183 G) : Equation45 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4179_implies_Equation45 (G: Type _) [Magma G] (h: Equation4179 G) : Equation45 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4149_implies_Equation42 (G: Type _) [Magma G] (h: Equation4149 G) : Equation42 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4055_implies_Equation45 (G: Type _) [Magma G] (h: Equation4055 G) : Equation45 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4050_implies_Equation45 (G: Type _) [Magma G] (h: Equation4050 G) : Equation45 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4045_implies_Equation45 (G: Type _) [Magma G] (h: Equation4045 G) : Equation45 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4031_implies_Equation45 (G: Type _) [Magma G] (h: Equation4031 G) : Equation45 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4027_implies_Equation45 (G: Type _) [Magma G] (h: Equation4027 G) : Equation45 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4014_implies_Equation45 (G: Type _) [Magma G] (h: Equation4014 G) : Equation45 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4010_implies_Equation45 (G: Type _) [Magma G] (h: Equation4010 G) : Equation45 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3980_implies_Equation45 (G: Type _) [Magma G] (h: Equation3980 G) : Equation45 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3976_implies_Equation45 (G: Type _) [Magma G] (h: Equation3976 G) : Equation45 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3906_implies_Equation40 (G: Type _) [Magma G] (h: Equation3906 G) : Equation40 G := by
  intro x y
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3700_implies_Equation40 (G: Type _) [Magma G] (h: Equation3700 G) : Equation40 G := by
  intro x y
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3539_implies_Equation42 (G: Type _) [Magma G] (h: Equation3539 G) : Equation42 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3528_implies_Equation42 (G: Type _) [Magma G] (h: Equation3528 G) : Equation42 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation399_implies_Equation45 (G: Type _) [Magma G] (h: Equation399 G) : Equation45 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation369_implies_Equation4623 (G: Type _) [Magma G] (h: Equation369 G) : Equation4623 G := by
  intro x y z w
  nth_rewrite 1 [← h]
  apply h
  repeat assumption
@[equational_result]
theorem Equation48_implies_Equation1427 (G: Type _) [Magma G] (h: Equation48 G) : Equation1427 G := by
  have eq3 (x : G) : x = x ◇ x := by
    apply Apply.Equation48_implies_Equation415 at h
    apply Apply.Equation415_implies_Equation412 at h
    apply Equation412_implies_Equation3 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq3]
  symm
  apply h
@[equational_result]
theorem Equation54_implies_Equation1433 (G: Type _) [Magma G] (h: Equation54 G) : Equation1433 G := by
  have eq3 (x : G) : x = x ◇ x := by
    apply Apply.Equation54_implies_Equation435 at h
    apply Apply.Equation435_implies_Equation415 at h
    apply Apply.Equation415_implies_Equation412 at h
    apply Equation412_implies_Equation3 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq3]
  symm
  apply h
@[equational_result]
theorem Equation9_implies_Equation2646 (G: Type _) [Magma G] (h: Equation9 G) : Equation2646 G := by
  have eq3 (x : G) : x = x ◇ x := by
    apply Apply.Equation9_implies_Equation51 at h
    apply Apply.Equation51_implies_Equation425 at h
    apply Apply.Equation425_implies_Equation415 at h
    apply Apply.Equation415_implies_Equation412 at h
    apply Equation412_implies_Equation3 at h
    apply h
  have eq3864 (x y : G) : x ◇ x = (x ◇ (x ◇ y)) ◇ x := by
    apply RewriteHypothesis.Equation9_implies_Equation3921 at h
    apply Apply.Equation3921_implies_Equation3864 at h
    apply h
  have eq308 (x y : G) : x ◇ x = x ◇ (x ◇ y) := by
    apply Equation9_implies_Equation308 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq3]
  nth_rewrite 1 [← eq3864]
  nth_rewrite 1 [eq308]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3191_implies_Equation3245 (G: Type _) [Magma G] (h: Equation3191 G) : Equation3245 G := by
  have eq3069 (x y : G) : x = (((x ◇ y) ◇ x) ◇ y) ◇ y := by
    apply Apply.Equation3191_implies_Equation3073 at h
    apply Apply.Equation3073_implies_Equation3069 at h
    apply h
  have eq3112 (x y : G) : x = (((y ◇ x) ◇ y) ◇ x) ◇ x := by
    apply Apply.Equation3191_implies_Equation3110 at h
    apply Equation3110_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation14 at h
    apply Subgraph.Equation14_implies_Equation29 at h
    apply RewriteHypothesis.Equation29_implies_Equation3195 at h
    apply Apply.Equation3195_implies_Equation3112 at h
    apply h
  have eq3050 (x : G) : x = (((x ◇ x) ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation3191_implies_Equation3073 at h
    apply Apply.Equation3073_implies_Equation3053 at h
    apply Apply.Equation3053_implies_Equation3050 at h
    apply h
  have eq3176 (x y z : G) : x = (((y ◇ z) ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation3191_implies_Equation3176 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3069 x]
  nth_rewrite 1 [← eq3112]
  nth_rewrite 1 [eq3050 w]
  symm
  nth_rewrite 1 [← eq3176]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq3050]
  apply h
@[equational_result]
theorem Equation2216_implies_Equation6 (G: Type _) [Magma G] (h: Equation2216 G) : Equation6 G := by
  have eq2035 (x : G) : x = ((x ◇ x) ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation2216_implies_Equation2073 at h
    apply Apply.Equation2073_implies_Equation2042 at h
    apply Apply.Equation2042_implies_Equation2036 at h
    apply Apply.Equation2036_implies_Equation2035 at h
    apply h
  have eq40 (x y : G) : x ◇ x = y ◇ y := by
    apply Apply.Equation2216_implies_Equation2147 at h
    apply Apply.Equation2147_implies_Equation2136 at h
    apply Equation2136_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation40 at h
    apply h
  have eq3660 (x y : G) : x ◇ x = (x ◇ x) ◇ (x ◇ y) := by
    apply Apply.Equation2216_implies_Equation2215 at h
    apply RewriteHypothesisAndGoal.Equation2215_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation363 at h
    apply Apply.Equation363_implies_Equation360 at h
    apply Apply.Equation360_implies_Equation3663 at h
    apply Apply.Equation3663_implies_Equation3660 at h
    apply h
  have eq359 (x : G) : x ◇ x = (x ◇ x) ◇ x := by
    apply Apply.Equation2216_implies_Equation2147 at h
    apply Apply.Equation2147_implies_Equation2136 at h
    apply Equation2136_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation387 at h
    apply Apply.Equation387_implies_Equation359 at h
    apply h
  have eq2036 (x y : G) : x = ((x ◇ x) ◇ x) ◇ (x ◇ y) := by
    apply Apply.Equation2216_implies_Equation2073 at h
    apply Apply.Equation2073_implies_Equation2042 at h
    apply Apply.Equation2042_implies_Equation2036 at h
    apply h
  intro x y
  nth_rewrite 1 [eq2035 x]
  symm
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3660]
  nth_rewrite 1 [eq359]
  nth_rewrite 1 [← eq2036]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq2035]
  apply h
@[equational_result]
theorem Equation2215_implies_Equation30 (G: Type _) [Magma G] (h: Equation2215 G) : Equation30 G := by
  have eq4589 (x y z : G) : (x ◇ x) ◇ x = (y ◇ x) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation2215_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation366 at h
    apply RewriteCombinations.Equation366_implies_Equation4624 at h
    apply RewriteGoal.Equation4624_implies_Equation4621 at h
    apply SimpleRewrites.Equation4621_implies_Equation4589 at h
    apply h
  have eq359 (x : G) : x ◇ x = (x ◇ x) ◇ x := by
    apply Apply.Equation2215_implies_Equation2179 at h
    apply Equation2179_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation387 at h
    apply Apply.Equation387_implies_Equation359 at h
    apply h
  have eq3659 (x : G) : x ◇ x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation2215_implies_Equation2146 at h
    apply RewriteHypothesisAndGoal.Equation2146_implies_Equation3688 at h
    apply SimpleRewrites.Equation3688_implies_Equation3659 at h
    apply h
  have eq2035 (x : G) : x = ((x ◇ x) ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation2215_implies_Equation2072 at h
    apply Apply.Equation2072_implies_Equation2041 at h
    apply Apply.Equation2041_implies_Equation2035 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4589]
  symm
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq359 x]
  nth_rewrite 1 [eq3659 x]
  nth_rewrite 1 [eq359 x]
  nth_rewrite 1 [← eq2035 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1978_implies_Equation84 (G: Type _) [Magma G] (h: Equation1978 G) : Equation84 G := by
  have eq1832 (x : G) : x = (x ◇ (x ◇ x)) ◇ (x ◇ x) := by
    apply Apply.Equation1978_implies_Equation1849 at h
    apply Apply.Equation1849_implies_Equation1833 at h
    apply Apply.Equation1833_implies_Equation1832 at h
    apply h
  have eq3290 (x y z : G) : x ◇ x = y ◇ (z ◇ (x ◇ z)) := by
    apply RewriteHypothesisAndGoal.Equation1978_implies_Equation319 at h
    apply RewriteHypothesis.Equation319_implies_Equation3302 at h
    apply Apply.Equation3302_implies_Equation3290 at h
    apply h
  have eq3659 (x : G) : x ◇ x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation1978_implies_Equation1933 at h
    apply Equation1933_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation3722 at h
    apply Apply.Equation3722_implies_Equation3659 at h
    apply h
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply Apply.Equation1978_implies_Equation1849 at h
    apply Equation1849_implies_Equation309 at h
    apply Apply.Equation309_implies_Equation307 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq1832 x]
  symm
  nth_rewrite 1 [← eq3290 x]
  nth_rewrite 1 [eq3659 x]
  symm
  nth_rewrite 1 [← eq1832 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [eq307 x]
  nth_rewrite 1 [← eq1832 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1995_implies_Equation174 (G: Type _) [Magma G] (h: Equation1995 G) : Equation174 G := by
  have eq3682 (x y z : G) : x ◇ x = (y ◇ x) ◇ (z ◇ z) := by
    apply RewriteHypothesisAndGoal.Equation1995_implies_Equation320 at h
    apply Apply.Equation320_implies_Equation3709 at h
    apply Apply.Equation3709_implies_Equation3682 at h
    apply h
  have eq3659 (x : G) : x ◇ x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation1995_implies_Equation1933 at h
    apply Equation1933_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation3722 at h
    apply Apply.Equation3722_implies_Equation3659 at h
    apply h
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation1995_implies_Equation320 at h
    apply Apply.Equation320_implies_Equation310 at h
    apply Apply.Equation310_implies_Equation307 at h
    apply h
  have eq1832 (x : G) : x = (x ◇ (x ◇ x)) ◇ (x ◇ x) := by
    apply Apply.Equation1995_implies_Equation1859 at h
    apply Apply.Equation1859_implies_Equation1833 at h
    apply Apply.Equation1833_implies_Equation1832 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq3682 x]
  symm
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [eq3659 x]
  nth_rewrite 1 [eq307 x]
  nth_rewrite 1 [← eq1832 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1995_implies_Equation70 (G: Type _) [Magma G] (h: Equation1995 G) : Equation70 G := by
  have eq1832 (x : G) : x = (x ◇ (x ◇ x)) ◇ (x ◇ x) := by
    apply Apply.Equation1995_implies_Equation1859 at h
    apply Apply.Equation1859_implies_Equation1833 at h
    apply Apply.Equation1833_implies_Equation1832 at h
    apply h
  have eq3276 (x y z : G) : x ◇ x = y ◇ (x ◇ (z ◇ z)) := by
    apply RewriteHypothesisAndGoal.Equation1995_implies_Equation320 at h
    apply RewriteCombinations.Equation320_implies_Equation3303 at h
    apply Apply.Equation3303_implies_Equation3276 at h
    apply h
  have eq3659 (x : G) : x ◇ x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation1995_implies_Equation1933 at h
    apply Equation1933_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation3722 at h
    apply Apply.Equation3722_implies_Equation3659 at h
    apply h
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation1995_implies_Equation320 at h
    apply Apply.Equation320_implies_Equation310 at h
    apply Apply.Equation310_implies_Equation307 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq1832 x]
  symm
  nth_rewrite 1 [← eq3276 x]
  nth_rewrite 1 [eq3659 x]
  symm
  nth_rewrite 1 [← eq1832 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [eq307 x]
  nth_rewrite 1 [← eq1832 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation270_implies_Equation2087 (G: Type _) [Magma G] (h: Equation270 G) : Equation2087 G := by
  have eq3 (x : G) : x = x ◇ x := by
    apply Apply.Equation270_implies_Equation3176 at h
    apply Apply.Equation3176_implies_Equation3102 at h
    apply Equation3102_implies_Equation3 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq3]
  symm
  apply h
@[equational_result]
theorem Equation48_implies_Equation818 (G: Type _) [Magma G] (h: Equation48 G) : Equation818 G := by
  have eq3 (x : G) : x = x ◇ x := by
    apply Apply.Equation48_implies_Equation415 at h
    apply Apply.Equation415_implies_Equation412 at h
    apply Equation412_implies_Equation3 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq3]
  symm
  apply h
@[equational_result]
theorem Equation2726_implies_Equation2839 (G: Type _) [Magma G] (h: Equation2726 G) : Equation2839 G := by
  have eq2653 (x y : G) : x = ((x ◇ x) ◇ (y ◇ y)) ◇ y := by
    apply Apply.Equation2726_implies_Equation2653 at h
    apply h
  have eq3715 (x y : G) : x ◇ y = (x ◇ x) ◇ (y ◇ y) := by
    apply Equation2726_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation3715 at h
    apply h
  have eq4587 (x y : G) : (x ◇ x) ◇ x = (y ◇ x) ◇ x := by
    apply Equation2726_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation39 at h
    apply Apply.Equation39_implies_Equation370 at h
    apply Apply.Equation370_implies_Equation364 at h
    apply RewriteHypothesis.Equation364_implies_Equation4666 at h
    apply Apply.Equation4666_implies_Equation4587 at h
    apply h
  have eq23 (x : G) : x = (x ◇ x) ◇ x := by
    apply Equation2726_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation23 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq2653 x]
  nth_rewrite 1 [← eq3715]
  nth_rewrite 1 [← eq4587]
  nth_rewrite 1 [← eq23]
  apply h
@[equational_result]
theorem Equation1514_implies_Equation1123 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1123 G := by
  have eq3 (x : G) : x = x ◇ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1493 at h
    apply Equation1493_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ◇ x = y ◇ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1493 at h
    apply Equation1493_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation1514_implies_Equation1440 at h
    apply Apply.Equation1440_implies_Equation1433 at h
    apply Equation1433_implies_Equation2261 at h
    apply Apply.Equation2261_implies_Equation2241 at h
    apply Equation2241_implies_Equation3253 at h
    apply h
  have eq1020 (x : G) : x = x ◇ ((x ◇ (x ◇ x)) ◇ x) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1493 at h
    apply Equation1493_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation8 at h
    apply RewriteHypothesis.Equation8_implies_Equation1020 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1493 at h
    apply Apply.Equation1493_implies_Equation1491 at h
    apply Equation1491_implies_Equation47 at h
    apply h
  intro x y
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1020]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1626 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1626 G := by
  have eq3 (x : G) : x = x ◇ x := by
    apply Equation1514_implies_Equation1123 at h
    apply Singleton.Equation1123_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ◇ x = y ◇ y := by
    apply Equation1514_implies_Equation1123 at h
    apply Singleton.Equation1123_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation1514_implies_Equation1440 at h
    apply Apply.Equation1440_implies_Equation1433 at h
    apply Equation1433_implies_Equation2261 at h
    apply Apply.Equation2261_implies_Equation2241 at h
    apply Equation2241_implies_Equation3253 at h
    apply h
  have eq1512 (x y z w : G) : x = (y ◇ x) ◇ (z ◇ (w ◇ z)) := by
    apply Apply.Equation1514_implies_Equation1512 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1493 at h
    apply Apply.Equation1493_implies_Equation1491 at h
    apply Equation1491_implies_Equation47 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1512]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1715_implies_Equation920 (G: Type _) [Magma G] (h: Equation1715 G) : Equation920 G := by
  have eq3 (x : G) : x = x ◇ x := by
    apply Apply.Equation1715_implies_Equation1711 at h
    apply Equation1711_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ◇ x = y ◇ y := by
    apply Apply.Equation1715_implies_Equation1711 at h
    apply Equation1711_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation1715_implies_Equation1687 at h
    apply Equation1687_implies_Equation3316 at h
    apply Apply.Equation3316_implies_Equation3253 at h
    apply h
  have eq817 (x : G) : x = x ◇ ((x ◇ x) ◇ (x ◇ x)) := by
    apply Apply.Equation1715_implies_Equation1703 at h
    apply Equation1703_implies_Equation2113 at h
    apply Apply.Equation2113_implies_Equation2101 at h
    apply Equation2101_implies_Equation817 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation1715_implies_Equation1711 at h
    apply Equation1711_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq817]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1712_implies_Equation920 (G: Type _) [Magma G] (h: Equation1712 G) : Equation920 G := by
  have eq3 (x : G) : x = x ◇ x := by
    apply Apply.Equation1712_implies_Equation1711 at h
    apply Equation1711_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ◇ x = y ◇ y := by
    apply Apply.Equation1712_implies_Equation1696 at h
    apply Equation1696_implies_Equation979 at h
    apply RewriteHypothesisAndGoal.Equation979_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation1712_implies_Equation1711 at h
    apply Equation1711_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation387 at h
    apply Equation387_implies_Equation3342 at h
    apply Apply.Equation3342_implies_Equation3253 at h
    apply h
  have eq817 (x : G) : x = x ◇ ((x ◇ x) ◇ (x ◇ x)) := by
    apply Apply.Equation1712_implies_Equation1696 at h
    apply Equation1696_implies_Equation979 at h
    apply Apply.Equation979_implies_Equation843 at h
    apply Apply.Equation843_implies_Equation817 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation1712_implies_Equation1711 at h
    apply Equation1711_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq817]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation74_implies_Equation1005 (G: Type _) [Magma G] (h: Equation74 G) : Equation1005 G := by
  have eq4 (x y : G) : x = x ◇ y := by
    apply Apply.Equation74_implies_Equation509 at h
    apply Apply.Equation509_implies_Equation502 at h
    apply Equation502_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation4 at h
    apply h
  have eq39 (x y : G) : x ◇ x = y ◇ x := by
    apply Apply.Equation74_implies_Equation509 at h
    apply Apply.Equation509_implies_Equation502 at h
    apply Equation502_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation39 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation74_implies_Equation48 at h
    apply Equation48_implies_Equation3254 at h
    apply Apply.Equation3254_implies_Equation3253 at h
    apply h
  have eq856 (x y z : G) : x = x ◇ ((y ◇ z) ◇ (y ◇ x)) := by
    apply Apply.Equation74_implies_Equation509 at h
    apply Apply.Equation509_implies_Equation502 at h
    apply Equation502_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation5 at h
    apply RewriteHypothesis.Equation5_implies_Equation94 at h
    apply Apply.Equation94_implies_Equation1014 at h
    apply Apply.Equation1014_implies_Equation1004 at h
    apply Apply.Equation1004_implies_Equation856 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation74_implies_Equation48 at h
    apply Apply.Equation48_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq4 x]
  nth_rewrite 1 [← eq39]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq856]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation74_implies_Equation1006 (G: Type _) [Magma G] (h: Equation74 G) : Equation1006 G := by
  have eq4 (x y : G) : x = x ◇ y := by
    apply Equation74_implies_Equation1005 at h
    apply Singleton.Equation1005_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation4 at h
    apply h
  have eq39 (x y : G) : x ◇ x = y ◇ x := by
    apply Equation74_implies_Equation1005 at h
    apply Singleton.Equation1005_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation39 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation74_implies_Equation48 at h
    apply Equation48_implies_Equation3254 at h
    apply Apply.Equation3254_implies_Equation3253 at h
    apply h
  have eq857 (x y z : G) : x = x ◇ ((y ◇ z) ◇ (y ◇ y)) := by
    apply Equation74_implies_Equation1005 at h
    apply Singleton.Equation1005_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation4 at h
    apply Apply.Equation4_implies_Equation12 at h
    apply Apply.Equation12_implies_Equation113 at h
    apply Apply.Equation113_implies_Equation868 at h
    apply Apply.Equation868_implies_Equation859 at h
    apply Apply.Equation859_implies_Equation857 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation74_implies_Equation48 at h
    apply Apply.Equation48_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq4 x]
  nth_rewrite 1 [← eq39]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq857]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation74_implies_Equation1007 (G: Type _) [Magma G] (h: Equation74 G) : Equation1007 G := by
  have eq4 (x y : G) : x = x ◇ y := by
    apply Equation74_implies_Equation1005 at h
    apply Singleton.Equation1005_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation4 at h
    apply h
  have eq39 (x y : G) : x ◇ x = y ◇ x := by
    apply Equation74_implies_Equation1005 at h
    apply Singleton.Equation1005_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation39 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation74_implies_Equation48 at h
    apply Equation48_implies_Equation3254 at h
    apply Apply.Equation3254_implies_Equation3253 at h
    apply h
  have eq858 (x y z : G) : x = x ◇ ((y ◇ z) ◇ (y ◇ z)) := by
    apply Apply.Equation74_implies_Equation509 at h
    apply Apply.Equation509_implies_Equation508 at h
    apply Equation508_implies_Equation914 at h
    apply Equation914_implies_Equation1053 at h
    apply Equation1053_implies_Equation11 at h
    apply Apply.Equation11_implies_Equation858 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation74_implies_Equation48 at h
    apply Apply.Equation48_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq4 x]
  nth_rewrite 1 [← eq39]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq858]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation74_implies_Equation1010 (G: Type _) [Magma G] (h: Equation74 G) : Equation1010 G := by
  have eq4 (x y : G) : x = x ◇ y := by
    apply Equation74_implies_Equation1005 at h
    apply Singleton.Equation1005_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation4 at h
    apply h
  have eq39 (x y : G) : x ◇ x = y ◇ x := by
    apply Equation74_implies_Equation1005 at h
    apply Singleton.Equation1005_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation39 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation74_implies_Equation48 at h
    apply Equation48_implies_Equation3254 at h
    apply Apply.Equation3254_implies_Equation3253 at h
    apply h
  have eq860 (x y z : G) : x = x ◇ ((y ◇ z) ◇ (z ◇ x)) := by
    apply Equation74_implies_Equation1006 at h
    apply SimpleRewrites.Equation1006_implies_Equation889 at h
    apply Apply.Equation889_implies_Equation869 at h
    apply Equation869_implies_Equation811 at h
    apply Apply.Equation811_implies_Equation661 at h
    apply Equation661_implies_Equation860 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation74_implies_Equation48 at h
    apply Apply.Equation48_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq4 x]
  nth_rewrite 1 [← eq39]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq860]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation74_implies_Equation1011 (G: Type _) [Magma G] (h: Equation74 G) : Equation1011 G := by
  have eq4 (x y : G) : x = x ◇ y := by
    apply Equation74_implies_Equation1005 at h
    apply Singleton.Equation1005_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation4 at h
    apply h
  have eq39 (x y : G) : x ◇ x = y ◇ x := by
    apply Equation74_implies_Equation1005 at h
    apply Singleton.Equation1005_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation39 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation74_implies_Equation48 at h
    apply Equation48_implies_Equation3254 at h
    apply Apply.Equation3254_implies_Equation3253 at h
    apply h
  have eq861 (x y z : G) : x = x ◇ ((y ◇ z) ◇ (z ◇ y)) := by
    apply Equation74_implies_Equation1005 at h
    apply RewriteHypothesisAndGoal.Equation1005_implies_Equation1003 at h
    apply Apply.Equation1003_implies_Equation1002 at h
    apply SimpleRewrites.Equation1002_implies_Equation895 at h
    apply Equation895_implies_Equation861 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation74_implies_Equation48 at h
    apply Apply.Equation48_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq4 x]
  nth_rewrite 1 [← eq39]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq861]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation74_implies_Equation1012 (G: Type _) [Magma G] (h: Equation74 G) : Equation1012 G := by
  have eq4 (x y : G) : x = x ◇ y := by
    apply Equation74_implies_Equation1005 at h
    apply Singleton.Equation1005_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation4 at h
    apply h
  have eq39 (x y : G) : x ◇ x = y ◇ x := by
    apply Equation74_implies_Equation1005 at h
    apply Singleton.Equation1005_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation39 at h
    apply h
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation74_implies_Equation48 at h
    apply Equation48_implies_Equation3254 at h
    apply Apply.Equation3254_implies_Equation3253 at h
    apply h
  have eq862 (x y z : G) : x = x ◇ ((y ◇ z) ◇ (z ◇ z)) := by
    apply Equation74_implies_Equation1006 at h
    apply SimpleRewrites.Equation1006_implies_Equation970 at h
    apply RewriteHypothesisAndGoal.Equation970_implies_Equation97 at h
    apply SimpleRewrites.Equation97_implies_Equation60 at h
    apply Apply.Equation60_implies_Equation867 at h
    apply Apply.Equation867_implies_Equation862 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation74_implies_Equation48 at h
    apply Apply.Equation48_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq4 x]
  nth_rewrite 1 [← eq39]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq862]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3125_implies_Equation3240 (G: Type _) [Magma G] (h: Equation3125 G) : Equation3240 G := by
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Apply.Equation3125_implies_Equation3104 at h
    apply Equation3104_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation8 at h
    apply h
  have eq4276 (x y : G) : x ◇ (x ◇ x) = y ◇ (y ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation3125_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3390 at h
    apply SimpleRewrites.Equation3390_implies_Equation3273 at h
    apply RewriteCombinations.Equation3273_implies_Equation4276 at h
    apply h
  have eq3124 (x y z : G) : x = (((y ◇ x) ◇ z) ◇ x) ◇ z := by
    apply Apply.Equation3125_implies_Equation3124 at h
    apply h
  have eq411 (x : G) : x = x ◇ (x ◇ (x ◇ (x ◇ x))) := by
    apply Apply.Equation3125_implies_Equation3104 at h
    apply Equation3104_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation8 at h
    apply RewriteHypothesis.Equation8_implies_Equation411 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq8 x]
  nth_rewrite 1 [← eq4276]
  nth_rewrite 1 [eq8 y]
  symm
  nth_rewrite 1 [← eq3124]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq411]
  apply h
  repeat assumption
@[equational_result]
theorem Equation276_implies_Equation2107 (G: Type _) [Magma G] (h: Equation276 G) : Equation2107 G := by
  have eq3 (x : G) : x = x ◇ x := by
    apply Apply.Equation276_implies_Equation270 at h
    apply Apply.Equation270_implies_Equation3176 at h
    apply Apply.Equation3176_implies_Equation3102 at h
    apply Equation3102_implies_Equation3 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq3]
  symm
  apply h
@[equational_result]
theorem Equation1604_implies_Equation1751 (G: Type _) [Magma G] (h: Equation1604 G) : Equation1751 G := by
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Apply.Equation1604_implies_Equation1553 at h
    apply Equation1553_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation8 at h
    apply h
  have eq4276 (x y : G) : x ◇ (x ◇ x) = y ◇ (y ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation1604_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3390 at h
    apply SimpleRewrites.Equation3390_implies_Equation3273 at h
    apply RewriteCombinations.Equation3273_implies_Equation4276 at h
    apply h
  have eq1739 (x y z : G) : x = (y ◇ y) ◇ ((z ◇ x) ◇ y) := by
    apply Equation1604_implies_Equation1807 at h
    apply Apply.Equation1807_implies_Equation1739 at h
    apply h
  have eq411 (x : G) : x = x ◇ (x ◇ (x ◇ (x ◇ x))) := by
    apply Apply.Equation1604_implies_Equation1553 at h
    apply Equation1553_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation8 at h
    apply RewriteHypothesis.Equation8_implies_Equation411 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq8 w]
  nth_rewrite 1 [← eq4276]
  nth_rewrite 1 [eq8 x]
  symm
  nth_rewrite 1 [← eq1739]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq411]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1604_implies_Equation1822 (G: Type _) [Magma G] (h: Equation1604 G) : Equation1822 G := by
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Apply.Equation1604_implies_Equation1553 at h
    apply Equation1553_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation8 at h
    apply h
  have eq4276 (x y : G) : x ◇ (x ◇ x) = y ◇ (y ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation1604_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3390 at h
    apply SimpleRewrites.Equation3390_implies_Equation3273 at h
    apply RewriteCombinations.Equation3273_implies_Equation4276 at h
    apply h
  have eq1756 (x y z : G) : x = (y ◇ z) ◇ ((x ◇ x) ◇ y) := by
    apply Equation1604_implies_Equation1807 at h
    apply Apply.Equation1807_implies_Equation1756 at h
    apply h
  have eq411 (x : G) : x = x ◇ (x ◇ (x ◇ (x ◇ x))) := by
    apply Apply.Equation1604_implies_Equation1553 at h
    apply Equation1553_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation8 at h
    apply RewriteHypothesis.Equation8_implies_Equation411 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq8 y]
  nth_rewrite 1 [← eq4276]
  nth_rewrite 1 [eq8 x]
  symm
  nth_rewrite 1 [← eq1756]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq411]
  apply h
@[equational_result]
theorem Equation1604_implies_Equation1785 (G: Type _) [Magma G] (h: Equation1604 G) : Equation1785 G := by
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Apply.Equation1604_implies_Equation1553 at h
    apply Equation1553_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation8 at h
    apply h
  have eq4276 (x y : G) : x ◇ (x ◇ x) = y ◇ (y ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation1604_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3390 at h
    apply SimpleRewrites.Equation3390_implies_Equation3273 at h
    apply RewriteCombinations.Equation3273_implies_Equation4276 at h
    apply h
  have eq1773 (x y z : G) : x = (y ◇ z) ◇ ((y ◇ x) ◇ y) := by
    apply Equation1604_implies_Equation1807 at h
    apply Apply.Equation1807_implies_Equation1773 at h
    apply h
  have eq411 (x : G) : x = x ◇ (x ◇ (x ◇ (x ◇ x))) := by
    apply Apply.Equation1604_implies_Equation1553 at h
    apply Equation1553_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation8 at h
    apply RewriteHypothesis.Equation8_implies_Equation411 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq8 w]
  nth_rewrite 1 [← eq4276]
  nth_rewrite 1 [eq8 x]
  symm
  nth_rewrite 1 [← eq1773]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq411]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1604_implies_Equation1802 (G: Type _) [Magma G] (h: Equation1604 G) : Equation1802 G := by
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Apply.Equation1604_implies_Equation1553 at h
    apply Equation1553_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation8 at h
    apply h
  have eq4276 (x y : G) : x ◇ (x ◇ x) = y ◇ (y ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation1604_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3390 at h
    apply SimpleRewrites.Equation3390_implies_Equation3273 at h
    apply RewriteCombinations.Equation3273_implies_Equation4276 at h
    apply h
  have eq1790 (x y z : G) : x = (y ◇ z) ◇ ((z ◇ x) ◇ y) := by
    apply Equation1604_implies_Equation1807 at h
    apply Apply.Equation1807_implies_Equation1790 at h
    apply h
  have eq411 (x : G) : x = x ◇ (x ◇ (x ◇ (x ◇ x))) := by
    apply Apply.Equation1604_implies_Equation1553 at h
    apply Equation1553_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation8 at h
    apply RewriteHypothesis.Equation8_implies_Equation411 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq8 w]
  nth_rewrite 1 [← eq4276]
  nth_rewrite 1 [eq8 x]
  symm
  nth_rewrite 1 [← eq1790]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq411]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1604_implies_Equation1827 (G: Type _) [Magma G] (h: Equation1604 G) : Equation1827 G := by
  have eq3 (x : G) : x = x ◇ x := by
    apply Apply.Equation1604_implies_Equation1553 at h
    apply Equation1553_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ◇ x = y ◇ y := by
    apply RewriteHypothesisAndGoal.Equation1604_implies_Equation41 at h
    apply Subgraph.Equation41_implies_Equation40 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation1604_implies_Equation1553 at h
    apply Equation1553_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  have eq1807 (x y z w : G) : x = (y ◇ z) ◇ ((w ◇ x) ◇ y) := by
    apply Equation1604_implies_Equation1807 at h
    apply h
  have eq411 (x : G) : x = x ◇ (x ◇ (x ◇ (x ◇ x))) := by
    apply Apply.Equation1604_implies_Equation1553 at h
    apply Equation1553_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation8 at h
    apply RewriteHypothesis.Equation8_implies_Equation411 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [eq3 y]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq47 x]
  symm
  nth_rewrite 1 [← eq1807]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq411]
  apply h
  repeat assumption
