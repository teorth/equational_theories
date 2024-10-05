import equational_theories.Generated.SimpleRewrites
import equational_theories.Generated.Constant
import equational_theories.Generated.Singleton
import equational_theories.Generated.TrivialBruteforce
import equational_theories.Generated.FinitePoly
import equational_theories.Subgraph
import equational_theories.Generated.SimpleRewrites
import equational_theories.Generated.Constant
import equational_theories.Generated.Singleton
import equational_theories.Generated.TrivialBruteforce
import equational_theories.Generated.FinitePoly
import equational_theories.Subgraph
import equational_theories.AllEquations
import Mathlib.Tactic

namespace Run1
@[equational_result]
theorem Equation9_implies_Equation308 (G: Type _) [Magma G] (h: Equation9 G) : Equation308 G := by
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesis.Equation9_implies_Equation3320 at h
    apply Apply.Equation3320_implies_Equation3254 at h
    apply Apply.Equation3254_implies_Equation3253 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation9_implies_Equation51 at h
    apply Apply.Equation51_implies_Equation48 at h
    apply Apply.Equation48_implies_Equation47 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq3253]
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation12_implies_Equation331 (G: Type _) [Magma G] (h: Equation12 G) : Equation331 G := by
  have eq3315 (x y : G) : x ◇ y = x ◇ (y ◇ (x ◇ x)) := by
    apply Apply.Equation12_implies_Equation11 at h
    apply RewriteHypothesis.Equation11_implies_Equation3323 at h
    apply Apply.Equation3323_implies_Equation3315 at h
    apply h
  have eq52 (x y : G) : x = x ◇ (y ◇ (x ◇ x)) := by
    apply Apply.Equation12_implies_Equation61 at h
    apply Apply.Equation61_implies_Equation54 at h
    apply Apply.Equation54_implies_Equation52 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq3315]
  nth_rewrite 1 [← eq52]
  apply h
  repeat assumption
@[equational_result]
theorem Equation13_implies_Equation4327 (G: Type _) [Magma G] (h: Equation13 G) : Equation4327 G := by
  have eq4269 (x y : G) : x ◇ (x ◇ x) = x ◇ (y ◇ x) := by
    apply RewriteHypothesis.Equation13_implies_Equation3330 at h
    apply NthRewrites.Equation3330_implies_Equation4340 at h
    apply RewriteCombinations.Equation4340_implies_Equation4360 at h
    apply Apply.Equation4360_implies_Equation4316 at h
    apply Apply.Equation4316_implies_Equation4269 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Apply.Equation13_implies_Equation8 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4269]
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation13_implies_Equation10 (G: Type _) [Magma G] (h: Equation13 G) : Equation10 G := by
  have eq4269 (x y : G) : x ◇ (x ◇ x) = x ◇ (y ◇ x) := by
    apply RewriteHypothesis.Equation13_implies_Equation3330 at h
    apply NthRewrites.Equation3330_implies_Equation4340 at h
    apply RewriteCombinations.Equation4340_implies_Equation4360 at h
    apply Apply.Equation4360_implies_Equation4316 at h
    apply Apply.Equation4316_implies_Equation4269 at h
    apply h
  have eq4272 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ x) := by
    apply RewriteHypothesis.Equation13_implies_Equation4351 at h
    apply Apply.Equation4351_implies_Equation4272 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [← eq4269]
  symm
  symm
  nth_rewrite 1 [eq4272]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation13_implies_Equation4304 (G: Type _) [Magma G] (h: Equation13 G) : Equation4304 G := by
  have eq4284 (x y : G) : x ◇ (x ◇ y) = x ◇ (y ◇ y) := by
    apply RewriteHypothesis.Equation13_implies_Equation3330 at h
    apply NthRewrites.Equation3330_implies_Equation4340 at h
    apply RewriteCombinations.Equation4340_implies_Equation4360 at h
    apply Apply.Equation4360_implies_Equation4287 at h
    apply Apply.Equation4287_implies_Equation4284 at h
    apply h
  have eq4272 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ x) := by
    apply RewriteHypothesis.Equation13_implies_Equation4351 at h
    apply Apply.Equation4351_implies_Equation4272 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Apply.Equation13_implies_Equation8 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq4284]
  nth_rewrite 1 [← eq4272]
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation14_implies_Equation680 (G: Type _) [Magma G] (h: Equation14 G) : Equation680 G := by
  have eq3522 (x y : G) : x ◇ y = x ◇ ((y ◇ y) ◇ y) := by
    apply RewriteHypothesis.Equation14_implies_Equation3331 at h
    apply NthRewrites.Equation3331_implies_Equation3534 at h
    apply Apply.Equation3534_implies_Equation3522 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [← eq3522]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation15_implies_Equation98 (G: Type _) [Magma G] (h: Equation15 G) : Equation98 G := by
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Apply.Equation15_implies_Equation13 at h
    apply Apply.Equation13_implies_Equation8 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply Apply.Equation15_implies_Equation189 at h
    apply Apply.Equation189_implies_Equation188 at h
    apply RewriteHypothesisAndGoal.Equation188_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq314 (x y z : G) : x ◇ x = y ◇ (x ◇ z) := by
    apply Apply.Equation15_implies_Equation189 at h
    apply Apply.Equation189_implies_Equation188 at h
    apply RewriteHypothesisAndGoal.Equation188_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Apply.Equation15_implies_Equation13 at h
    apply Apply.Equation13_implies_Equation8 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq8 x]
  symm
  nth_rewrite 1 [← eq3304]
  symm
  symm
  nth_rewrite 1 [eq314]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
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
  repeat assumption
@[equational_result]
theorem Equation28_implies_Equation364 (G: Type _) [Magma G] (h: Equation28 G) : Equation364 G := by
  have eq359 (x : G) : x ◇ x = (x ◇ x) ◇ x := by
    apply RewriteHypothesis.Equation28_implies_Equation4192 at h
    apply RewriteHypothesisAndGoal.Equation4192_implies_Equation375 at h
    apply Apply.Equation375_implies_Equation359 at h
    apply h
  have eq23 (x : G) : x = (x ◇ x) ◇ x := by
    apply Apply.Equation28_implies_Equation23 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq359]
  nth_rewrite 1 [← eq23]
  apply h
  repeat assumption
@[equational_result]
theorem Equation28_implies_Equation3 (G: Type _) [Magma G] (h: Equation28 G) : Equation3 G := by
  have eq359 (x : G) : x ◇ x = (x ◇ x) ◇ x := by
    apply RewriteHypothesis.Equation28_implies_Equation4192 at h
    apply RewriteHypothesisAndGoal.Equation4192_implies_Equation375 at h
    apply Apply.Equation375_implies_Equation359 at h
    apply h
  have eq4587 (x y : G) : (x ◇ x) ◇ x = (y ◇ x) ◇ x := by
    apply RewriteHypothesis.Equation28_implies_Equation4666 at h
    apply Apply.Equation4666_implies_Equation4587 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [eq359]
  symm
  symm
  nth_rewrite 1 [eq4587]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation29_implies_Equation4458 (G: Type _) [Magma G] (h: Equation29 G) : Equation4458 G := by
  have eq14 (x y : G) : x = y ◇ (x ◇ y) := by
    apply Subgraph.Equation29_implies_Equation14 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq14]
  apply h
  repeat assumption
@[equational_result]
theorem Equation29_implies_Equation2238 (G: Type _) [Magma G] (h: Equation29 G) : Equation2238 G := by
  have eq3253 (x : G) : x ◇ x = x ◇ (x ◇ (x ◇ x)) := by
    apply Subgraph.Equation29_implies_Equation14 at h
    apply RewriteHypothesis.Equation14_implies_Equation3331 at h
    apply Apply.Equation3331_implies_Equation3259 at h
    apply Apply.Equation3259_implies_Equation3253 at h
    apply h
  have eq4588 (x y : G) : (x ◇ x) ◇ x = (y ◇ x) ◇ y := by
    apply RewriteHypothesis.Equation29_implies_Equation4647 at h
    apply Apply.Equation4647_implies_Equation4588 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [← eq3253]
  symm
  symm
  nth_rewrite 1 [eq4588]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation30_implies_Equation98 (G: Type _) [Magma G] (h: Equation30 G) : Equation98 G := by
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Apply.Equation30_implies_Equation29 at h
    apply Subgraph.Equation29_implies_Equation14 at h
    apply Apply.Equation14_implies_Equation8 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply Apply.Equation30_implies_Equation175 at h
    apply Apply.Equation175_implies_Equation1514 at h
    apply Apply.Equation1514_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq366 (x y z : G) : x ◇ x = (y ◇ x) ◇ z := by
    apply Apply.Equation30_implies_Equation175 at h
    apply Apply.Equation175_implies_Equation1717 at h
    apply RewriteHypothesisAndGoal.Equation1717_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation366 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Apply.Equation30_implies_Equation29 at h
    apply Subgraph.Equation29_implies_Equation14 at h
    apply Apply.Equation14_implies_Equation8 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq8 x]
  symm
  nth_rewrite 1 [← eq3304]
  symm
  symm
  nth_rewrite 1 [eq366]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation34_implies_Equation407 (G: Type _) [Magma G] (h: Equation34 G) : Equation407 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply Apply.Equation34_implies_Equation28 at h
    apply RewriteHypothesis.Equation28_implies_Equation4192 at h
    apply RewriteHypothesisAndGoal.Equation4192_implies_Equation375 at h
    apply h
  have eq31 (x y : G) : x = (y ◇ y) ◇ x := by
    apply Apply.Equation34_implies_Equation31 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq375]
  nth_rewrite 1 [← eq31]
  apply h
  repeat assumption
@[equational_result]
theorem Equation84_implies_Equation98 (G: Type _) [Magma G] (h: Equation84 G) : Equation98 G := by
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation84_implies_Equation53 at h
    apply Apply.Equation53_implies_Equation47 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply Apply.Equation84_implies_Equation1606 at h
    apply RewriteHypothesisAndGoal.Equation1606_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq3290 (x y z : G) : x ◇ x = y ◇ (z ◇ (x ◇ z)) := by
    apply Apply.Equation84_implies_Equation1606 at h
    apply RewriteHypothesisAndGoal.Equation1606_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply RewriteCombinations.Equation314_implies_Equation3291 at h
    apply Apply.Equation3291_implies_Equation3290 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation84_implies_Equation53 at h
    apply Apply.Equation53_implies_Equation47 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq47 x]
  symm
  nth_rewrite 1 [← eq3304]
  symm
  symm
  nth_rewrite 1 [eq3290]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation85_implies_Equation98 (G: Type _) [Magma G] (h: Equation85 G) : Equation98 G := by
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation85_implies_Equation54 at h
    apply Apply.Equation54_implies_Equation48 at h
    apply Apply.Equation48_implies_Equation47 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply Apply.Equation85_implies_Equation1607 at h
    apply Apply.Equation1607_implies_Equation1604 at h
    apply RewriteHypothesisAndGoal.Equation1604_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq3291 (x y z w : G) : x ◇ x = y ◇ (z ◇ (x ◇ w)) := by
    apply Apply.Equation85_implies_Equation1607 at h
    apply Apply.Equation1607_implies_Equation1604 at h
    apply RewriteHypothesisAndGoal.Equation1604_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply RewriteCombinations.Equation314_implies_Equation3291 at h
    apply h
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation85_implies_Equation54 at h
    apply Apply.Equation54_implies_Equation48 at h
    apply Apply.Equation48_implies_Equation47 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq47 x]
  symm
  nth_rewrite 1 [← eq3304]
  symm
  symm
  nth_rewrite 1 [eq3291]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation116_implies_Equation98 (G: Type _) [Magma G] (h: Equation116 G) : Equation98 G := by
  have eq99 (x : G) : x = x ◇ ((x ◇ x) ◇ x) := by
    apply Apply.Equation116_implies_Equation100 at h
    apply Apply.Equation100_implies_Equation99 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply Apply.Equation116_implies_Equation1758 at h
    apply Apply.Equation1758_implies_Equation1757 at h
    apply RewriteHypothesisAndGoal.Equation1757_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq3473 (x y z : G) : x ◇ x = y ◇ ((x ◇ x) ◇ z) := by
    apply Apply.Equation116_implies_Equation1758 at h
    apply Apply.Equation1758_implies_Equation1757 at h
    apply RewriteHypothesisAndGoal.Equation1757_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply RewriteHypothesis.Equation314_implies_Equation3480 at h
    apply Apply.Equation3480_implies_Equation3473 at h
    apply h
  have eq99 (x : G) : x = x ◇ ((x ◇ x) ◇ x) := by
    apply Apply.Equation116_implies_Equation100 at h
    apply Apply.Equation100_implies_Equation99 at h
    apply h
  intro  x
  repeat intro
  nth_rewrite 1 [eq99 x]
  symm
  nth_rewrite 1 [← eq3304]
  symm
  symm
  nth_rewrite 1 [eq3473]
  symm
  nth_rewrite 1 [← eq99]
  apply h
  repeat assumption
@[equational_result]
theorem Equation123_implies_Equation98 (G: Type _) [Magma G] (h: Equation123 G) : Equation98 G := by
  have eq99 (x : G) : x = x ◇ ((x ◇ x) ◇ x) := by
    apply Apply.Equation123_implies_Equation103 at h
    apply Apply.Equation103_implies_Equation100 at h
    apply Apply.Equation100_implies_Equation99 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply Apply.Equation123_implies_Equation116 at h
    apply Apply.Equation116_implies_Equation1758 at h
    apply Apply.Equation1758_implies_Equation1757 at h
    apply RewriteHypothesisAndGoal.Equation1757_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq3480 (x y z w : G) : x ◇ x = y ◇ ((x ◇ z) ◇ w) := by
    apply Apply.Equation123_implies_Equation116 at h
    apply Apply.Equation116_implies_Equation1758 at h
    apply Apply.Equation1758_implies_Equation1757 at h
    apply RewriteHypothesisAndGoal.Equation1757_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply RewriteHypothesis.Equation314_implies_Equation3480 at h
    apply h
  have eq99 (x : G) : x = x ◇ ((x ◇ x) ◇ x) := by
    apply Apply.Equation123_implies_Equation103 at h
    apply Apply.Equation103_implies_Equation100 at h
    apply Apply.Equation100_implies_Equation99 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq99 x]
  symm
  nth_rewrite 1 [← eq3304]
  symm
  symm
  nth_rewrite 1 [eq3480]
  symm
  nth_rewrite 1 [← eq99]
  apply h
  repeat assumption
@[equational_result]
theorem Equation136_implies_Equation98 (G: Type _) [Magma G] (h: Equation136 G) : Equation98 G := by
  have eq99 (x : G) : x = x ◇ ((x ◇ x) ◇ x) := by
    apply Apply.Equation136_implies_Equation105 at h
    apply Apply.Equation105_implies_Equation99 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply Apply.Equation136_implies_Equation1809 at h
    apply Apply.Equation1809_implies_Equation1791 at h
    apply RewriteHypothesisAndGoal.Equation1791_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq3493 (x y z : G) : x ◇ x = y ◇ ((z ◇ x) ◇ z) := by
    apply Apply.Equation136_implies_Equation1809 at h
    apply Apply.Equation1809_implies_Equation1791 at h
    apply RewriteHypothesisAndGoal.Equation1791_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3507 at h
    apply Apply.Equation3507_implies_Equation3494 at h
    apply Apply.Equation3494_implies_Equation3493 at h
    apply h
  have eq99 (x : G) : x = x ◇ ((x ◇ x) ◇ x) := by
    apply Apply.Equation136_implies_Equation105 at h
    apply Apply.Equation105_implies_Equation99 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq99 x]
  symm
  nth_rewrite 1 [← eq3304]
  symm
  symm
  nth_rewrite 1 [eq3493]
  symm
  nth_rewrite 1 [← eq99]
  apply h
  repeat assumption
@[equational_result]
theorem Equation137_implies_Equation98 (G: Type _) [Magma G] (h: Equation137 G) : Equation98 G := by
  have eq99 (x : G) : x = x ◇ ((x ◇ x) ◇ x) := by
    apply Apply.Equation137_implies_Equation106 at h
    apply Apply.Equation106_implies_Equation100 at h
    apply Apply.Equation100_implies_Equation99 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply Apply.Equation137_implies_Equation116 at h
    apply Apply.Equation116_implies_Equation1758 at h
    apply Apply.Equation1758_implies_Equation1757 at h
    apply RewriteHypothesisAndGoal.Equation1757_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq3494 (x y z w : G) : x ◇ x = y ◇ ((z ◇ x) ◇ w) := by
    apply Apply.Equation137_implies_Equation116 at h
    apply Apply.Equation116_implies_Equation1758 at h
    apply Apply.Equation1758_implies_Equation1757 at h
    apply RewriteHypothesisAndGoal.Equation1757_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3507 at h
    apply Apply.Equation3507_implies_Equation3494 at h
    apply h
  have eq99 (x : G) : x = x ◇ ((x ◇ x) ◇ x) := by
    apply Apply.Equation137_implies_Equation106 at h
    apply Apply.Equation106_implies_Equation100 at h
    apply Apply.Equation100_implies_Equation99 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq99 x]
  symm
  nth_rewrite 1 [← eq3304]
  symm
  symm
  nth_rewrite 1 [eq3494]
  symm
  nth_rewrite 1 [← eq99]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation15 (G: Type _) [Magma G] (h: Equation171 G) : Equation15 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq314 (x y z : G) : x ◇ x = y ◇ (x ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq314]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation17 (G: Type _) [Magma G] (h: Equation171 G) : Equation17 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq316 (x y : G) : x ◇ x = y ◇ (y ◇ y) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation317 at h
    apply Apply.Equation317_implies_Equation316 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq316]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation18 (G: Type _) [Magma G] (h: Equation171 G) : Equation18 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq317 (x y z : G) : x ◇ x = y ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation317 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq317]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation29 (G: Type _) [Magma G] (h: Equation171 G) : Equation29 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq365 (x y : G) : x ◇ x = (y ◇ x) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation171_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4203 at h
    apply Apply.Equation4203_implies_Equation4199 at h
    apply RewriteCombinations.Equation4199_implies_Equation4202 at h
    apply NthRewrites.Equation4202_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation366 at h
    apply Apply.Equation366_implies_Equation365 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq365]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation30 (G: Type _) [Magma G] (h: Equation171 G) : Equation30 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq366 (x y z : G) : x ◇ x = (y ◇ x) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation171_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4203 at h
    apply Apply.Equation4203_implies_Equation4199 at h
    apply RewriteCombinations.Equation4199_implies_Equation4202 at h
    apply NthRewrites.Equation4202_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation366 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq366]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation71 (G: Type _) [Magma G] (h: Equation171 G) : Equation71 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3277 (x y z w : G) : x ◇ x = y ◇ (x ◇ (z ◇ w)) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply Apply.Equation314_implies_Equation3277 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3277]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation74 (G: Type _) [Magma G] (h: Equation171 G) : Equation74 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3280 (x y z : G) : x ◇ x = y ◇ (y ◇ (x ◇ z)) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply RewriteCombinations.Equation314_implies_Equation3291 at h
    apply Apply.Equation3291_implies_Equation3280 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3280]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation83 (G: Type _) [Magma G] (h: Equation171 G) : Equation83 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3289 (x y z : G) : x ◇ x = y ◇ (z ◇ (x ◇ y)) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply RewriteCombinations.Equation314_implies_Equation3291 at h
    apply Apply.Equation3291_implies_Equation3289 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3289]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation84 (G: Type _) [Magma G] (h: Equation171 G) : Equation84 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3290 (x y z : G) : x ◇ x = y ◇ (z ◇ (x ◇ z)) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply RewriteCombinations.Equation314_implies_Equation3291 at h
    apply Apply.Equation3291_implies_Equation3290 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3290]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation85 (G: Type _) [Magma G] (h: Equation171 G) : Equation85 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3291 (x y z w : G) : x ◇ x = y ◇ (z ◇ (x ◇ w)) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply RewriteCombinations.Equation314_implies_Equation3291 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
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
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation116 (G: Type _) [Magma G] (h: Equation171 G) : Equation116 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3473 (x y z : G) : x ◇ x = y ◇ ((x ◇ x) ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply RewriteHypothesis.Equation314_implies_Equation3480 at h
    apply Apply.Equation3480_implies_Equation3473 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
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
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation119 (G: Type _) [Magma G] (h: Equation171 G) : Equation119 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3476 (x y z : G) : x ◇ x = y ◇ ((x ◇ y) ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply RewriteHypothesis.Equation314_implies_Equation3480 at h
    apply Apply.Equation3480_implies_Equation3476 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3476]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation121 (G: Type _) [Magma G] (h: Equation171 G) : Equation121 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3478 (x y z : G) : x ◇ x = y ◇ ((x ◇ z) ◇ y) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply RewriteHypothesis.Equation314_implies_Equation3480 at h
    apply Apply.Equation3480_implies_Equation3478 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3478]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation122 (G: Type _) [Magma G] (h: Equation171 G) : Equation122 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3479 (x y z : G) : x ◇ x = y ◇ ((x ◇ z) ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply RewriteHypothesis.Equation314_implies_Equation3480 at h
    apply Apply.Equation3480_implies_Equation3479 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3479]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation123 (G: Type _) [Magma G] (h: Equation171 G) : Equation123 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3480 (x y z w : G) : x ◇ x = y ◇ ((x ◇ z) ◇ w) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply RewriteHypothesis.Equation314_implies_Equation3480 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3480]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation126 (G: Type _) [Magma G] (h: Equation171 G) : Equation126 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3483 (x y z : G) : x ◇ x = y ◇ ((y ◇ x) ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3507 at h
    apply Apply.Equation3507_implies_Equation3490 at h
    apply Apply.Equation3490_implies_Equation3483 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3483]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation128 (G: Type _) [Magma G] (h: Equation171 G) : Equation128 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3485 (x y : G) : x ◇ x = y ◇ ((y ◇ y) ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation171_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation3497 at h
    apply Apply.Equation3497_implies_Equation3485 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3485]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation129 (G: Type _) [Magma G] (h: Equation171 G) : Equation129 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3486 (x y z : G) : x ◇ x = y ◇ ((y ◇ y) ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3507 at h
    apply Apply.Equation3507_implies_Equation3490 at h
    apply Apply.Equation3490_implies_Equation3486 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3486]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation131 (G: Type _) [Magma G] (h: Equation171 G) : Equation131 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3488 (x y z : G) : x ◇ x = y ◇ ((y ◇ z) ◇ y) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation319 at h
    apply Apply.Equation319_implies_Equation3504 at h
    apply Apply.Equation3504_implies_Equation3488 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3488]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation132 (G: Type _) [Magma G] (h: Equation171 G) : Equation132 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3489 (x y z : G) : x ◇ x = y ◇ ((y ◇ z) ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3507 at h
    apply Apply.Equation3507_implies_Equation3490 at h
    apply Apply.Equation3490_implies_Equation3489 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3489]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation133 (G: Type _) [Magma G] (h: Equation171 G) : Equation133 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3490 (x y z w : G) : x ◇ x = y ◇ ((y ◇ z) ◇ w) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3507 at h
    apply Apply.Equation3507_implies_Equation3490 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3490]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation135 (G: Type _) [Magma G] (h: Equation171 G) : Equation135 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3492 (x y z : G) : x ◇ x = y ◇ ((z ◇ x) ◇ y) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation319 at h
    apply Apply.Equation319_implies_Equation3504 at h
    apply Apply.Equation3504_implies_Equation3492 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3492]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation136 (G: Type _) [Magma G] (h: Equation171 G) : Equation136 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3493 (x y z : G) : x ◇ x = y ◇ ((z ◇ x) ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3507 at h
    apply Apply.Equation3507_implies_Equation3494 at h
    apply Apply.Equation3494_implies_Equation3493 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3493]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation137 (G: Type _) [Magma G] (h: Equation171 G) : Equation137 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3494 (x y z w : G) : x ◇ x = y ◇ ((z ◇ x) ◇ w) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3507 at h
    apply Apply.Equation3507_implies_Equation3494 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x
  repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3494]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation139 (G: Type _) [Magma G] (h: Equation171 G) : Equation139 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3496 (x y z : G) : x ◇ x = y ◇ ((z ◇ y) ◇ y) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation319 at h
    apply Apply.Equation319_implies_Equation3504 at h
    apply Apply.Equation3504_implies_Equation3496 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3496]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation140 (G: Type _) [Magma G] (h: Equation171 G) : Equation140 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3497 (x y z : G) : x ◇ x = y ◇ ((z ◇ y) ◇ z) := by
    apply RewriteHypothesisAndGoal.Equation171_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3404 at h
    apply NthRewrites.Equation3404_implies_Equation3497 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3497]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation141 (G: Type _) [Magma G] (h: Equation171 G) : Equation141 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3498 (x y z w : G) : x ◇ x = y ◇ ((z ◇ y) ◇ w) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3507 at h
    apply Apply.Equation3507_implies_Equation3498 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3498]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation143 (G: Type _) [Magma G] (h: Equation171 G) : Equation143 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3500 (x y z : G) : x ◇ x = y ◇ ((z ◇ z) ◇ y) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation319 at h
    apply Apply.Equation319_implies_Equation3504 at h
    apply Apply.Equation3504_implies_Equation3500 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3500]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation144 (G: Type _) [Magma G] (h: Equation171 G) : Equation144 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3501 (x y z : G) : x ◇ x = y ◇ ((z ◇ z) ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3507 at h
    apply Apply.Equation3507_implies_Equation3502 at h
    apply Apply.Equation3502_implies_Equation3501 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3501]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation145 (G: Type _) [Magma G] (h: Equation171 G) : Equation145 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3502 (x y z w : G) : x ◇ x = y ◇ ((z ◇ z) ◇ w) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3507 at h
    apply Apply.Equation3507_implies_Equation3502 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3502]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation147 (G: Type _) [Magma G] (h: Equation171 G) : Equation147 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3504 (x y z w : G) : x ◇ x = y ◇ ((z ◇ w) ◇ y) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation319 at h
    apply Apply.Equation319_implies_Equation3504 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3504]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation148 (G: Type _) [Magma G] (h: Equation171 G) : Equation148 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3505 (x y z w : G) : x ◇ x = y ◇ ((z ◇ w) ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3507 at h
    apply Apply.Equation3507_implies_Equation3505 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3505]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation149 (G: Type _) [Magma G] (h: Equation171 G) : Equation149 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3506 (x y z w : G) : x ◇ x = y ◇ ((z ◇ w) ◇ w) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3507 at h
    apply Apply.Equation3507_implies_Equation3506 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3506]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation150 (G: Type _) [Magma G] (h: Equation171 G) : Equation150 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3507 (x y z w u : G) : x ◇ x = y ◇ ((z ◇ w) ◇ u) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3507 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3507]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation173 (G: Type _) [Magma G] (h: Equation171 G) : Equation173 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3681 (x y z : G) : x ◇ x = (y ◇ x) ◇ (z ◇ y) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3681 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3681]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation174 (G: Type _) [Magma G] (h: Equation171 G) : Equation174 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3682 (x y z : G) : x ◇ x = (y ◇ x) ◇ (z ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3682 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3682]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation175 (G: Type _) [Magma G] (h: Equation171 G) : Equation175 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3683 (x y z w : G) : x ◇ x = (y ◇ x) ◇ (z ◇ w) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3683]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation178 (G: Type _) [Magma G] (h: Equation171 G) : Equation178 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3686 (x y z : G) : x ◇ x = (y ◇ y) ◇ (x ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply Apply.Equation314_implies_Equation3697 at h
    apply Apply.Equation3697_implies_Equation3686 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3686]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation180 (G: Type _) [Magma G] (h: Equation171 G) : Equation180 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3688 (x y : G) : x ◇ x = (y ◇ y) ◇ (y ◇ y) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3688]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation183 (G: Type _) [Magma G] (h: Equation171 G) : Equation183 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3691 (x y z : G) : x ◇ x = (y ◇ y) ◇ (z ◇ y) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3693 at h
    apply Apply.Equation3693_implies_Equation3691 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3691]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation184 (G: Type _) [Magma G] (h: Equation171 G) : Equation184 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3692 (x y z : G) : x ◇ x = (y ◇ y) ◇ (z ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply NthRewrites.Equation40_implies_Equation3692 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3692]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation185 (G: Type _) [Magma G] (h: Equation171 G) : Equation185 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3693 (x y z w : G) : x ◇ x = (y ◇ y) ◇ (z ◇ w) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3693 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3693]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation187 (G: Type _) [Magma G] (h: Equation171 G) : Equation187 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3695 (x y z : G) : x ◇ x = (y ◇ z) ◇ (x ◇ y) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply Apply.Equation314_implies_Equation3697 at h
    apply Apply.Equation3697_implies_Equation3695 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3695]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation188 (G: Type _) [Magma G] (h: Equation171 G) : Equation188 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3696 (x y z : G) : x ◇ x = (y ◇ z) ◇ (x ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply Apply.Equation314_implies_Equation3697 at h
    apply Apply.Equation3697_implies_Equation3696 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3696]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation189 (G: Type _) [Magma G] (h: Equation171 G) : Equation189 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3697 (x y z w : G) : x ◇ x = (y ◇ z) ◇ (x ◇ w) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply Apply.Equation314_implies_Equation3697 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3697]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation195 (G: Type _) [Magma G] (h: Equation171 G) : Equation195 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3703 (x y z : G) : x ◇ x = (y ◇ z) ◇ (z ◇ y) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3705 at h
    apply Apply.Equation3705_implies_Equation3703 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3703]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation196 (G: Type _) [Magma G] (h: Equation171 G) : Equation196 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3704 (x y z : G) : x ◇ x = (y ◇ z) ◇ (z ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3705 at h
    apply Apply.Equation3705_implies_Equation3704 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3704]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation197 (G: Type _) [Magma G] (h: Equation171 G) : Equation197 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3705 (x y z w : G) : x ◇ x = (y ◇ z) ◇ (z ◇ w) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3705 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3705]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation199 (G: Type _) [Magma G] (h: Equation171 G) : Equation199 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3707 (x y z w : G) : x ◇ x = (y ◇ z) ◇ (w ◇ y) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3707 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3707]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation225 (G: Type _) [Magma G] (h: Equation171 G) : Equation225 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3884 (x y z : G) : x ◇ x = (y ◇ (x ◇ z)) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation171_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4203 at h
    apply Apply.Equation4203_implies_Equation4199 at h
    apply RewriteCombinations.Equation4199_implies_Equation4202 at h
    apply NthRewrites.Equation4202_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation371 at h
    apply Apply.Equation371_implies_Equation3910 at h
    apply Apply.Equation3910_implies_Equation3884 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3884]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation226 (G: Type _) [Magma G] (h: Equation171 G) : Equation226 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3885 (x y z : G) : x ◇ x = (y ◇ (x ◇ z)) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation171_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4203 at h
    apply Apply.Equation4203_implies_Equation4199 at h
    apply RewriteCombinations.Equation4199_implies_Equation4202 at h
    apply NthRewrites.Equation4202_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation3913 at h
    apply Apply.Equation3913_implies_Equation3886 at h
    apply Apply.Equation3886_implies_Equation3885 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3885]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation227 (G: Type _) [Magma G] (h: Equation171 G) : Equation227 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3886 (x y z w : G) : x ◇ x = (y ◇ (x ◇ z)) ◇ w := by
    apply RewriteHypothesisAndGoal.Equation171_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4203 at h
    apply Apply.Equation4203_implies_Equation4199 at h
    apply RewriteCombinations.Equation4199_implies_Equation4202 at h
    apply NthRewrites.Equation4202_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation3913 at h
    apply Apply.Equation3913_implies_Equation3886 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3886]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation230 (G: Type _) [Magma G] (h: Equation171 G) : Equation230 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3889 (x y z : G) : x ◇ x = (y ◇ (y ◇ x)) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation171_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4203 at h
    apply Apply.Equation4203_implies_Equation4199 at h
    apply RewriteCombinations.Equation4199_implies_Equation4202 at h
    apply NthRewrites.Equation4202_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation366 at h
    apply RewriteHypothesis.Equation366_implies_Equation3900 at h
    apply Apply.Equation3900_implies_Equation3889 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3889]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation239 (G: Type _) [Magma G] (h: Equation171 G) : Equation239 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3898 (x y z : G) : x ◇ x = (y ◇ (z ◇ x)) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation171_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4203 at h
    apply Apply.Equation4203_implies_Equation4199 at h
    apply RewriteCombinations.Equation4199_implies_Equation4202 at h
    apply NthRewrites.Equation4202_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation366 at h
    apply RewriteHypothesis.Equation366_implies_Equation3900 at h
    apply Apply.Equation3900_implies_Equation3898 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3898]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation240 (G: Type _) [Magma G] (h: Equation171 G) : Equation240 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3899 (x y z : G) : x ◇ x = (y ◇ (z ◇ x)) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation171_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4203 at h
    apply Apply.Equation4203_implies_Equation4199 at h
    apply RewriteCombinations.Equation4199_implies_Equation4202 at h
    apply NthRewrites.Equation4202_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation366 at h
    apply RewriteHypothesis.Equation366_implies_Equation3900 at h
    apply Apply.Equation3900_implies_Equation3899 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3899]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation241 (G: Type _) [Magma G] (h: Equation171 G) : Equation241 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3900 (x y z w : G) : x ◇ x = (y ◇ (z ◇ x)) ◇ w := by
    apply RewriteHypothesisAndGoal.Equation171_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4203 at h
    apply Apply.Equation4203_implies_Equation4199 at h
    apply RewriteCombinations.Equation4199_implies_Equation4202 at h
    apply NthRewrites.Equation4202_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation366 at h
    apply RewriteHypothesis.Equation366_implies_Equation3900 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3900]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation272 (G: Type _) [Magma G] (h: Equation171 G) : Equation272 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq4082 (x y z : G) : x ◇ x = ((y ◇ x) ◇ x) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation171_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4198 at h
    apply Apply.Equation4198_implies_Equation4082 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq4082]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation275 (G: Type _) [Magma G] (h: Equation171 G) : Equation275 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq4085 (x y z : G) : x ◇ x = ((y ◇ x) ◇ y) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation171_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4203 at h
    apply Apply.Equation4203_implies_Equation4199 at h
    apply RewriteCombinations.Equation4199_implies_Equation4202 at h
    apply NthRewrites.Equation4202_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation366 at h
    apply RewriteCombinations.Equation366_implies_Equation4089 at h
    apply Apply.Equation4089_implies_Equation4085 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq4085]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation277 (G: Type _) [Magma G] (h: Equation171 G) : Equation277 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq4087 (x y z : G) : x ◇ x = ((y ◇ x) ◇ z) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation171_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4203 at h
    apply Apply.Equation4203_implies_Equation4199 at h
    apply RewriteCombinations.Equation4199_implies_Equation4202 at h
    apply NthRewrites.Equation4202_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation366 at h
    apply RewriteCombinations.Equation366_implies_Equation4089 at h
    apply Apply.Equation4089_implies_Equation4087 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq4087]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation278 (G: Type _) [Magma G] (h: Equation171 G) : Equation278 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq4088 (x y z : G) : x ◇ x = ((y ◇ x) ◇ z) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation171_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4203 at h
    apply Apply.Equation4203_implies_Equation4199 at h
    apply RewriteCombinations.Equation4199_implies_Equation4202 at h
    apply NthRewrites.Equation4202_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation366 at h
    apply RewriteCombinations.Equation366_implies_Equation4089 at h
    apply Apply.Equation4089_implies_Equation4088 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq4088]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation279 (G: Type _) [Magma G] (h: Equation171 G) : Equation279 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq4089 (x y z w : G) : x ◇ x = ((y ◇ x) ◇ z) ◇ w := by
    apply RewriteHypothesisAndGoal.Equation171_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4203 at h
    apply Apply.Equation4203_implies_Equation4199 at h
    apply RewriteCombinations.Equation4199_implies_Equation4202 at h
    apply NthRewrites.Equation4202_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation366 at h
    apply RewriteCombinations.Equation366_implies_Equation4089 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq4089]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation282 (G: Type _) [Magma G] (h: Equation171 G) : Equation282 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq4092 (x y z : G) : x ◇ x = ((y ◇ y) ◇ x) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation171_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4203 at h
    apply Apply.Equation4203_implies_Equation4199 at h
    apply RewriteCombinations.Equation4199_implies_Equation4202 at h
    apply NthRewrites.Equation4202_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation366 at h
    apply Apply.Equation366_implies_Equation4103 at h
    apply Apply.Equation4103_implies_Equation4092 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq4092]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation291 (G: Type _) [Magma G] (h: Equation171 G) : Equation291 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq4101 (x y z : G) : x ◇ x = ((y ◇ z) ◇ x) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation171_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4203 at h
    apply Apply.Equation4203_implies_Equation4199 at h
    apply RewriteCombinations.Equation4199_implies_Equation4202 at h
    apply NthRewrites.Equation4202_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation366 at h
    apply Apply.Equation366_implies_Equation4103 at h
    apply Apply.Equation4103_implies_Equation4101 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq4101]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation292 (G: Type _) [Magma G] (h: Equation171 G) : Equation292 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq4102 (x y z : G) : x ◇ x = ((y ◇ z) ◇ x) ◇ z := by
    apply RewriteHypothesisAndGoal.Equation171_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4203 at h
    apply Apply.Equation4203_implies_Equation4199 at h
    apply RewriteCombinations.Equation4199_implies_Equation4202 at h
    apply NthRewrites.Equation4202_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation366 at h
    apply Apply.Equation366_implies_Equation4103 at h
    apply Apply.Equation4103_implies_Equation4102 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq4102]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation171_implies_Equation293 (G: Type _) [Magma G] (h: Equation171 G) : Equation293 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq4103 (x y z w : G) : x ◇ x = ((y ◇ z) ◇ x) ◇ w := by
    apply RewriteHypothesisAndGoal.Equation171_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4203 at h
    apply Apply.Equation4203_implies_Equation4199 at h
    apply RewriteCombinations.Equation4199_implies_Equation4202 at h
    apply NthRewrites.Equation4202_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation366 at h
    apply Apply.Equation366_implies_Equation4103 at h
    apply h
  have eq3679 (x y z : G) : x ◇ x = (y ◇ x) ◇ (y ◇ z) := by
    apply Apply.Equation171_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3683 at h
    apply Apply.Equation3683_implies_Equation3679 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation171_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq4103]
  symm
  symm
  nth_rewrite 1 [eq3679]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation175_implies_Equation98 (G: Type _) [Magma G] (h: Equation175 G) : Equation98 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation175_implies_Equation155 at h
    apply Apply.Equation155_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply Apply.Equation175_implies_Equation1514 at h
    apply Apply.Equation1514_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq3683 (x y z w : G) : x ◇ x = (y ◇ x) ◇ (z ◇ w) := by
    apply Apply.Equation175_implies_Equation1717 at h
    apply RewriteHypothesisAndGoal.Equation1717_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation366 at h
    apply Apply.Equation366_implies_Equation3683 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation175_implies_Equation155 at h
    apply Apply.Equation155_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3304]
  symm
  symm
  nth_rewrite 1 [eq3683]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation188_implies_Equation98 (G: Type _) [Magma G] (h: Equation188 G) : Equation98 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation188_implies_Equation157 at h
    apply Apply.Equation157_implies_Equation151 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply RewriteHypothesisAndGoal.Equation188_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq3696 (x y z : G) : x ◇ x = (y ◇ z) ◇ (x ◇ z) := by
    apply Apply.Equation188_implies_Equation2215 at h
    apply RewriteHypothesisAndGoal.Equation2215_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3697 at h
    apply Apply.Equation3697_implies_Equation3696 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation188_implies_Equation157 at h
    apply Apply.Equation157_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3304]
  symm
  symm
  nth_rewrite 1 [eq3696]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation189_implies_Equation98 (G: Type _) [Magma G] (h: Equation189 G) : Equation98 G := by
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation189_implies_Equation158 at h
    apply Apply.Equation158_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply Apply.Equation189_implies_Equation188 at h
    apply RewriteHypothesisAndGoal.Equation188_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq3697 (x y z w : G) : x ◇ x = (y ◇ z) ◇ (x ◇ w) := by
    apply Apply.Equation189_implies_Equation188 at h
    apply Apply.Equation188_implies_Equation2215 at h
    apply RewriteHypothesisAndGoal.Equation2215_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3697 at h
    apply h
  have eq151 (x : G) : x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation189_implies_Equation158 at h
    apply Apply.Equation158_implies_Equation152 at h
    apply Apply.Equation152_implies_Equation151 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq151 x]
  symm
  nth_rewrite 1 [← eq3304]
  symm
  symm
  nth_rewrite 1 [eq3697]
  symm
  nth_rewrite 1 [← eq151]
  apply h
  repeat assumption
@[equational_result]
theorem Equation220_implies_Equation98 (G: Type _) [Magma G] (h: Equation220 G) : Equation98 G := by
  have eq203 (x : G) : x = (x ◇ (x ◇ x)) ◇ x := by
    apply Apply.Equation220_implies_Equation204 at h
    apply Apply.Equation204_implies_Equation203 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply Apply.Equation220_implies_Equation1893 at h
    apply Apply.Equation1893_implies_Equation1889 at h
    apply RewriteHypothesisAndGoal.Equation1889_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq3879 (x y z : G) : x ◇ x = (y ◇ (x ◇ x)) ◇ z := by
    apply Apply.Equation220_implies_Equation1893 at h
    apply Apply.Equation1893_implies_Equation1889 at h
    apply RewriteHypothesisAndGoal.Equation1889_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4203 at h
    apply Apply.Equation4203_implies_Equation4199 at h
    apply RewriteCombinations.Equation4199_implies_Equation4202 at h
    apply NthRewrites.Equation4202_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation366 at h
    apply RewriteHypothesis.Equation366_implies_Equation3900 at h
    apply Apply.Equation3900_implies_Equation3879 at h
    apply h
  have eq203 (x : G) : x = (x ◇ (x ◇ x)) ◇ x := by
    apply Apply.Equation220_implies_Equation204 at h
    apply Apply.Equation204_implies_Equation203 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq203 x]
  symm
  nth_rewrite 1 [← eq3304]
  symm
  symm
  nth_rewrite 1 [eq3879]
  symm
  nth_rewrite 1 [← eq203]
  apply h
  repeat assumption
@[equational_result]
theorem Equation223_implies_Equation98 (G: Type _) [Magma G] (h: Equation223 G) : Equation98 G := by
  have eq203 (x : G) : x = (x ◇ (x ◇ x)) ◇ x := by
    apply Apply.Equation223_implies_Equation204 at h
    apply Apply.Equation204_implies_Equation203 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply Apply.Equation223_implies_Equation1903 at h
    apply Apply.Equation1903_implies_Equation1899 at h
    apply RewriteHypothesisAndGoal.Equation1899_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq3882 (x y z : G) : x ◇ x = (y ◇ (x ◇ y)) ◇ z := by
    apply Apply.Equation223_implies_Equation1903 at h
    apply Apply.Equation1903_implies_Equation1899 at h
    apply RewriteHypothesisAndGoal.Equation1899_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4203 at h
    apply Apply.Equation4203_implies_Equation4199 at h
    apply RewriteCombinations.Equation4199_implies_Equation4202 at h
    apply NthRewrites.Equation4202_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation3913 at h
    apply Apply.Equation3913_implies_Equation3886 at h
    apply Apply.Equation3886_implies_Equation3882 at h
    apply h
  have eq203 (x : G) : x = (x ◇ (x ◇ x)) ◇ x := by
    apply Apply.Equation223_implies_Equation204 at h
    apply Apply.Equation204_implies_Equation203 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq203 x]
  symm
  nth_rewrite 1 [← eq3304]
  symm
  symm
  nth_rewrite 1 [eq3882]
  symm
  nth_rewrite 1 [← eq203]
  apply h
  repeat assumption
@[equational_result]
theorem Equation226_implies_Equation98 (G: Type _) [Magma G] (h: Equation226 G) : Equation98 G := by
  have eq203 (x : G) : x = (x ◇ (x ◇ x)) ◇ x := by
    apply Apply.Equation226_implies_Equation206 at h
    apply Apply.Equation206_implies_Equation203 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply Apply.Equation226_implies_Equation2785 at h
    apply RewriteHypothesisAndGoal.Equation2785_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq3885 (x y z : G) : x ◇ x = (y ◇ (x ◇ z)) ◇ z := by
    apply Apply.Equation226_implies_Equation2785 at h
    apply RewriteHypothesisAndGoal.Equation2785_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4203 at h
    apply Apply.Equation4203_implies_Equation4199 at h
    apply RewriteCombinations.Equation4199_implies_Equation4202 at h
    apply NthRewrites.Equation4202_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation3913 at h
    apply Apply.Equation3913_implies_Equation3886 at h
    apply Apply.Equation3886_implies_Equation3885 at h
    apply h
  have eq203 (x : G) : x = (x ◇ (x ◇ x)) ◇ x := by
    apply Apply.Equation226_implies_Equation206 at h
    apply Apply.Equation206_implies_Equation203 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq203 x]
  symm
  nth_rewrite 1 [← eq3304]
  symm
  symm
  nth_rewrite 1 [eq3885]
  symm
  nth_rewrite 1 [← eq203]
  apply h
  repeat assumption
@[equational_result]
theorem Equation230_implies_Equation98 (G: Type _) [Magma G] (h: Equation230 G) : Equation98 G := by
  have eq203 (x : G) : x = (x ◇ (x ◇ x)) ◇ x := by
    apply Apply.Equation230_implies_Equation204 at h
    apply Apply.Equation204_implies_Equation203 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply Apply.Equation230_implies_Equation1930 at h
    apply RewriteHypothesisAndGoal.Equation1930_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq3889 (x y z : G) : x ◇ x = (y ◇ (y ◇ x)) ◇ z := by
    apply Apply.Equation230_implies_Equation1930 at h
    apply RewriteHypothesisAndGoal.Equation1930_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4203 at h
    apply Apply.Equation4203_implies_Equation4199 at h
    apply RewriteCombinations.Equation4199_implies_Equation4202 at h
    apply NthRewrites.Equation4202_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation366 at h
    apply RewriteHypothesis.Equation366_implies_Equation3900 at h
    apply Apply.Equation3900_implies_Equation3889 at h
    apply h
  have eq203 (x : G) : x = (x ◇ (x ◇ x)) ◇ x := by
    apply Apply.Equation230_implies_Equation204 at h
    apply Apply.Equation204_implies_Equation203 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq203 x]
  symm
  nth_rewrite 1 [← eq3304]
  symm
  symm
  nth_rewrite 1 [eq3889]
  symm
  nth_rewrite 1 [← eq203]
  apply h
  repeat assumption
@[equational_result]
theorem Equation240_implies_Equation98 (G: Type _) [Magma G] (h: Equation240 G) : Equation98 G := by
  have eq203 (x : G) : x = (x ◇ (x ◇ x)) ◇ x := by
    apply Apply.Equation240_implies_Equation209 at h
    apply Apply.Equation209_implies_Equation203 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply Apply.Equation240_implies_Equation2824 at h
    apply RewriteHypothesisAndGoal.Equation2824_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq3899 (x y z : G) : x ◇ x = (y ◇ (z ◇ x)) ◇ z := by
    apply Apply.Equation240_implies_Equation2824 at h
    apply RewriteHypothesisAndGoal.Equation2824_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4203 at h
    apply Apply.Equation4203_implies_Equation4199 at h
    apply RewriteCombinations.Equation4199_implies_Equation4202 at h
    apply NthRewrites.Equation4202_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation366 at h
    apply RewriteHypothesis.Equation366_implies_Equation3900 at h
    apply Apply.Equation3900_implies_Equation3899 at h
    apply h
  have eq203 (x : G) : x = (x ◇ (x ◇ x)) ◇ x := by
    apply Apply.Equation240_implies_Equation209 at h
    apply Apply.Equation209_implies_Equation203 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq203 x]
  symm
  nth_rewrite 1 [← eq3304]
  symm
  symm
  nth_rewrite 1 [eq3899]
  symm
  nth_rewrite 1 [← eq203]
  apply h
  repeat assumption
@[equational_result]
theorem Equation275_implies_Equation98 (G: Type _) [Magma G] (h: Equation275 G) : Equation98 G := by
  have eq255 (x : G) : x = ((x ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation275_implies_Equation256 at h
    apply Apply.Equation256_implies_Equation255 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply Apply.Equation275_implies_Equation2106 at h
    apply RewriteHypothesisAndGoal.Equation2106_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq4085 (x y z : G) : x ◇ x = ((y ◇ x) ◇ y) ◇ z := by
    apply Apply.Equation275_implies_Equation2106 at h
    apply RewriteHypothesisAndGoal.Equation2106_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4203 at h
    apply Apply.Equation4203_implies_Equation4199 at h
    apply RewriteCombinations.Equation4199_implies_Equation4202 at h
    apply NthRewrites.Equation4202_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation366 at h
    apply RewriteCombinations.Equation366_implies_Equation4089 at h
    apply Apply.Equation4089_implies_Equation4085 at h
    apply h
  have eq255 (x : G) : x = ((x ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation275_implies_Equation256 at h
    apply Apply.Equation256_implies_Equation255 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq255 x]
  symm
  nth_rewrite 1 [← eq3304]
  symm
  symm
  nth_rewrite 1 [eq4085]
  symm
  nth_rewrite 1 [← eq255]
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
    apply RewriteHypothesisAndGoal.Equation3110_implies_Equation4671 at h
    apply Apply.Equation4671_implies_Equation4668 at h
    apply RewriteCombinations.Equation4668_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4628 at h
    apply Apply.Equation4628_implies_Equation4627 at h
    apply Apply.Equation4627_implies_Equation4603 at h
    apply Apply.Equation4603_implies_Equation4599 at h
    apply h
  have eq270 (x y : G) : x = ((y ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation278_implies_Equation270 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq258 x]
  nth_rewrite 1 [eq4599 x]
  nth_rewrite 1 [← eq270]
  apply h
  repeat assumption
@[equational_result]
theorem Equation279_implies_Equation98 (G: Type _) [Magma G] (h: Equation279 G) : Equation98 G := by
  have eq255 (x : G) : x = ((x ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation279_implies_Equation259 at h
    apply Apply.Equation259_implies_Equation256 at h
    apply Apply.Equation256_implies_Equation255 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply Apply.Equation279_implies_Equation2123 at h
    apply Apply.Equation2123_implies_Equation2106 at h
    apply RewriteHypothesisAndGoal.Equation2106_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq4089 (x y z w : G) : x ◇ x = ((y ◇ x) ◇ z) ◇ w := by
    apply Apply.Equation279_implies_Equation2123 at h
    apply Apply.Equation2123_implies_Equation2106 at h
    apply RewriteHypothesisAndGoal.Equation2106_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4203 at h
    apply Apply.Equation4203_implies_Equation4199 at h
    apply RewriteCombinations.Equation4199_implies_Equation4202 at h
    apply NthRewrites.Equation4202_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation366 at h
    apply RewriteCombinations.Equation366_implies_Equation4089 at h
    apply h
  have eq255 (x : G) : x = ((x ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation279_implies_Equation259 at h
    apply Apply.Equation259_implies_Equation256 at h
    apply Apply.Equation256_implies_Equation255 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq255 x]
  symm
  nth_rewrite 1 [← eq3304]
  symm
  symm
  nth_rewrite 1 [eq4089]
  symm
  nth_rewrite 1 [← eq255]
  apply h
  repeat assumption
@[equational_result]
theorem Equation293_implies_Equation98 (G: Type _) [Magma G] (h: Equation293 G) : Equation98 G := by
  have eq255 (x : G) : x = ((x ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation293_implies_Equation262 at h
    apply Apply.Equation262_implies_Equation256 at h
    apply Apply.Equation256_implies_Equation255 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply Apply.Equation293_implies_Equation2177 at h
    apply RewriteHypothesisAndGoal.Equation2177_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq4103 (x y z w : G) : x ◇ x = ((y ◇ z) ◇ x) ◇ w := by
    apply Apply.Equation293_implies_Equation2177 at h
    apply RewriteHypothesisAndGoal.Equation2177_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4203 at h
    apply Apply.Equation4203_implies_Equation4199 at h
    apply RewriteCombinations.Equation4199_implies_Equation4202 at h
    apply NthRewrites.Equation4202_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation366 at h
    apply Apply.Equation366_implies_Equation4103 at h
    apply h
  have eq255 (x : G) : x = ((x ◇ x) ◇ x) ◇ x := by
    apply Apply.Equation293_implies_Equation262 at h
    apply Apply.Equation262_implies_Equation256 at h
    apply Apply.Equation256_implies_Equation255 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq255 x]
  symm
  nth_rewrite 1 [← eq3304]
  symm
  symm
  nth_rewrite 1 [eq4103]
  symm
  nth_rewrite 1 [← eq255]
  apply h
  repeat assumption
@[equational_result]
theorem Equation314_implies_Equation321 (G: Type _) [Magma G] (h: Equation314 G) : Equation321 G := by
  have eq40 (x y : G) : x ◇ x = y ◇ y := by
    apply RewriteCombinations.Equation314_implies_Equation3291 at h
    apply Apply.Equation3291_implies_Equation3289 at h
    apply NthRewrites.Equation3289_implies_Equation3699 at h
    apply SimpleRewrites.Equation3699_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [← eq40]
  apply h
  repeat assumption
@[equational_result]
theorem Equation314_implies_Equation311 (G: Type _) [Magma G] (h: Equation314 G) : Equation311 G := by
  have eq4362 (x y z : G) : x ◇ (y ◇ z) = y ◇ (x ◇ z) := by
    apply RewriteCombinations.Equation314_implies_Equation4349 at h
    apply RewriteCombinations.Equation4349_implies_Equation4379 at h
    apply Apply.Equation4379_implies_Equation4377 at h
    apply RewriteHypothesis.Equation4377_implies_Equation4372 at h
    apply RewriteHypothesis.Equation4372_implies_Equation4368 at h
    apply Apply.Equation4368_implies_Equation4366 at h
    apply RewriteHypothesis.Equation4366_implies_Equation4365 at h
    apply RewriteHypothesis.Equation4365_implies_Equation4375 at h
    apply Apply.Equation4375_implies_Equation4370 at h
    apply SimpleRewrites.Equation4370_implies_Equation4292 at h
    apply RewriteCombinations.Equation4292_implies_Equation4298 at h
    apply RewriteGoal.Equation4298_implies_Equation4313 at h
    apply Apply.Equation4313_implies_Equation4281 at h
    apply RewriteCombinations.Equation4281_implies_Equation4363 at h
    apply Apply.Equation4363_implies_Equation4362 at h
    apply h
  intro x; repeat intro
  symm
  nth_rewrite 1 [eq4362]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation314_implies_Equation317 (G: Type _) [Magma G] (h: Equation314 G) : Equation317 G := by
  have eq4277 (x y z : G) : x ◇ (x ◇ x) = y ◇ (y ◇ z) := by
    apply RewriteCombinations.Equation314_implies_Equation4349 at h
    apply RewriteCombinations.Equation4349_implies_Equation4379 at h
    apply Apply.Equation4379_implies_Equation4377 at h
    apply RewriteHypothesis.Equation4377_implies_Equation4372 at h
    apply RewriteHypothesis.Equation4372_implies_Equation4368 at h
    apply Apply.Equation4368_implies_Equation4366 at h
    apply RewriteHypothesis.Equation4366_implies_Equation4365 at h
    apply RewriteHypothesis.Equation4365_implies_Equation4375 at h
    apply Apply.Equation4375_implies_Equation4370 at h
    apply SimpleRewrites.Equation4370_implies_Equation4292 at h
    apply RewriteCombinations.Equation4292_implies_Equation4298 at h
    apply RewriteGoal.Equation4298_implies_Equation4313 at h
    apply Apply.Equation4313_implies_Equation4281 at h
    apply RewriteCombinations.Equation4281_implies_Equation4312 at h
    apply RewriteHypothesis.Equation4312_implies_Equation4277 at h
    apply h
  have eq4274 (x y z : G) : x ◇ (x ◇ x) = y ◇ (x ◇ z) := by
    apply RewriteCombinations.Equation314_implies_Equation4349 at h
    apply RewriteCombinations.Equation4349_implies_Equation4379 at h
    apply Apply.Equation4379_implies_Equation4377 at h
    apply RewriteHypothesis.Equation4377_implies_Equation4372 at h
    apply RewriteHypothesis.Equation4372_implies_Equation4368 at h
    apply Apply.Equation4368_implies_Equation4366 at h
    apply RewriteHypothesis.Equation4366_implies_Equation4365 at h
    apply RewriteHypothesis.Equation4365_implies_Equation4375 at h
    apply Apply.Equation4375_implies_Equation4370 at h
    apply SimpleRewrites.Equation4370_implies_Equation4292 at h
    apply RewriteCombinations.Equation4292_implies_Equation4298 at h
    apply RewriteGoal.Equation4298_implies_Equation4313 at h
    apply Apply.Equation4313_implies_Equation4281 at h
    apply Apply.Equation4281_implies_Equation4274 at h
    apply h
  intro x; repeat intro
  symm
  nth_rewrite 1 [← eq4277]
  symm
  symm
  nth_rewrite 1 [eq4274]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation314_implies_Equation318 (G: Type _) [Magma G] (h: Equation314 G) : Equation318 G := by
  have eq4278 (x y z : G) : x ◇ (x ◇ x) = y ◇ (z ◇ x) := by
    apply RewriteCombinations.Equation314_implies_Equation4349 at h
    apply RewriteCombinations.Equation4349_implies_Equation4379 at h
    apply Apply.Equation4379_implies_Equation4377 at h
    apply RewriteHypothesis.Equation4377_implies_Equation4372 at h
    apply RewriteHypothesis.Equation4372_implies_Equation4368 at h
    apply Apply.Equation4368_implies_Equation4366 at h
    apply RewriteHypothesis.Equation4366_implies_Equation4365 at h
    apply RewriteHypothesis.Equation4365_implies_Equation4375 at h
    apply Apply.Equation4375_implies_Equation4370 at h
    apply SimpleRewrites.Equation4370_implies_Equation4292 at h
    apply RewriteCombinations.Equation4292_implies_Equation4298 at h
    apply RewriteGoal.Equation4298_implies_Equation4313 at h
    apply Apply.Equation4313_implies_Equation4281 at h
    apply RewriteCombinations.Equation4281_implies_Equation4378 at h
    apply Apply.Equation4378_implies_Equation4354 at h
    apply SimpleRewrites.Equation4354_implies_Equation4278 at h
    apply h
  have eq4274 (x y z : G) : x ◇ (x ◇ x) = y ◇ (x ◇ z) := by
    apply RewriteCombinations.Equation314_implies_Equation4349 at h
    apply RewriteCombinations.Equation4349_implies_Equation4379 at h
    apply Apply.Equation4379_implies_Equation4377 at h
    apply RewriteHypothesis.Equation4377_implies_Equation4372 at h
    apply RewriteHypothesis.Equation4372_implies_Equation4368 at h
    apply Apply.Equation4368_implies_Equation4366 at h
    apply RewriteHypothesis.Equation4366_implies_Equation4365 at h
    apply RewriteHypothesis.Equation4365_implies_Equation4375 at h
    apply Apply.Equation4375_implies_Equation4370 at h
    apply SimpleRewrites.Equation4370_implies_Equation4292 at h
    apply RewriteCombinations.Equation4292_implies_Equation4298 at h
    apply RewriteGoal.Equation4298_implies_Equation4313 at h
    apply Apply.Equation4313_implies_Equation4281 at h
    apply Apply.Equation4281_implies_Equation4274 at h
    apply h
  intro x; repeat intro
  symm
  nth_rewrite 1 [← eq4278]
  symm
  symm
  nth_rewrite 1 [eq4274]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation314_implies_Equation319 (G: Type _) [Magma G] (h: Equation314 G) : Equation319 G := by
  have eq4279 (x y z : G) : x ◇ (x ◇ x) = y ◇ (z ◇ y) := by
    apply RewriteCombinations.Equation314_implies_Equation4349 at h
    apply RewriteCombinations.Equation4349_implies_Equation4379 at h
    apply Apply.Equation4379_implies_Equation4377 at h
    apply RewriteHypothesis.Equation4377_implies_Equation4372 at h
    apply RewriteHypothesis.Equation4372_implies_Equation4368 at h
    apply Apply.Equation4368_implies_Equation4366 at h
    apply RewriteHypothesis.Equation4366_implies_Equation4365 at h
    apply RewriteHypothesis.Equation4365_implies_Equation4375 at h
    apply Apply.Equation4375_implies_Equation4370 at h
    apply SimpleRewrites.Equation4370_implies_Equation4292 at h
    apply RewriteCombinations.Equation4292_implies_Equation4298 at h
    apply RewriteGoal.Equation4298_implies_Equation4313 at h
    apply Apply.Equation4313_implies_Equation4281 at h
    apply RewriteCombinations.Equation4281_implies_Equation4311 at h
    apply Apply.Equation4311_implies_Equation4279 at h
    apply h
  have eq4274 (x y z : G) : x ◇ (x ◇ x) = y ◇ (x ◇ z) := by
    apply RewriteCombinations.Equation314_implies_Equation4349 at h
    apply RewriteCombinations.Equation4349_implies_Equation4379 at h
    apply Apply.Equation4379_implies_Equation4377 at h
    apply RewriteHypothesis.Equation4377_implies_Equation4372 at h
    apply RewriteHypothesis.Equation4372_implies_Equation4368 at h
    apply Apply.Equation4368_implies_Equation4366 at h
    apply RewriteHypothesis.Equation4366_implies_Equation4365 at h
    apply RewriteHypothesis.Equation4365_implies_Equation4375 at h
    apply Apply.Equation4375_implies_Equation4370 at h
    apply SimpleRewrites.Equation4370_implies_Equation4292 at h
    apply RewriteCombinations.Equation4292_implies_Equation4298 at h
    apply RewriteGoal.Equation4298_implies_Equation4313 at h
    apply Apply.Equation4313_implies_Equation4281 at h
    apply Apply.Equation4281_implies_Equation4274 at h
    apply h
  intro x; repeat intro
  symm
  nth_rewrite 1 [← eq4279]
  symm
  symm
  nth_rewrite 1 [eq4274]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation332_implies_Equation4343 (G: Type _) [Magma G] (h: Equation332 G) : Equation4343 G := by
  have eq326 (x y : G) : x ◇ y = x ◇ (y ◇ y) := by
    apply RewriteHypothesis.Equation332_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation326 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [← eq326]
  apply h
  repeat assumption
@[equational_result]
theorem Equation332_implies_Equation3545 (G: Type _) [Magma G] (h: Equation332 G) : Equation3545 G := by
  have eq359 (x : G) : x ◇ x = (x ◇ x) ◇ x := by
    apply RewriteHypothesis.Equation332_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation375 at h
    apply Apply.Equation375_implies_Equation359 at h
    apply h
  intro x; repeat intro
  symm
  nth_rewrite 1 [← eq359]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation332_implies_Equation4470 (G: Type _) [Magma G] (h: Equation332 G) : Equation4470 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply RewriteHypothesis.Equation332_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation375 at h
    apply h
  have eq3342 (x y : G) : x ◇ y = y ◇ (x ◇ (x ◇ x)) := by
    apply RewriteHypothesis.Equation332_implies_Equation3342 at h
    apply h
  have eq326 (x y : G) : x ◇ y = x ◇ (y ◇ y) := by
    apply RewriteHypothesis.Equation332_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation326 at h
    apply h
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply RewriteHypothesis.Equation332_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply h
  intro x; repeat intro
  symm
  nth_rewrite 1 [← eq375]
  symm
  symm
  nth_rewrite 1 [eq3342]
  symm
  nth_rewrite 1 [← eq326]
  symm
  nth_rewrite 1 [← eq307]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation334_implies_Equation390 (G: Type _) [Magma G] (h: Equation334 G) : Equation390 G := by
  have eq332 (x y : G) : x ◇ y = y ◇ (x ◇ x) := by
    apply Apply.Equation334_implies_Equation3351 at h
    apply Apply.Equation3351_implies_Equation3344 at h
    apply RewriteHypothesisAndGoal.Equation3344_implies_Equation332 at h
    apply h
  have eq4531 (x y z : G) : x ◇ (y ◇ z) = (y ◇ z) ◇ x := by
    apply NthRewrites.Equation334_implies_Equation3365 at h
    apply Apply.Equation3365_implies_Equation3364 at h
    apply NthRewrites.Equation3364_implies_Equation4531 at h
    apply h
  have eq4362 (x y z : G) : x ◇ (y ◇ z) = y ◇ (x ◇ z) := by
    apply NthRewrites.Equation334_implies_Equation3365 at h
    apply Apply.Equation3365_implies_Equation3362 at h
    apply NthRewrites.Equation3362_implies_Equation403 at h
    apply RewriteHypothesis.Equation403_implies_Equation4238 at h
    apply SimpleRewrites.Equation4238_implies_Equation4234 at h
    apply SimpleRewrites.Equation4234_implies_Equation4168 at h
    apply RewriteHypothesisAndGoal.Equation4168_implies_Equation4060 at h
    apply Apply.Equation4060_implies_Equation4055 at h
    apply SimpleRewrites.Equation4055_implies_Equation4031 at h
    apply SimpleRewrites.Equation4031_implies_Equation3965 at h
    apply RewriteHypothesisAndGoal.Equation3965_implies_Equation391 at h
    apply Apply.Equation391_implies_Equation388 at h
    apply RewriteHypothesisAndGoal.Equation388_implies_Equation45 at h
    apply RewriteHypothesisAndGoal.Equation45_implies_Equation4278 at h
    apply RewriteCombinations.Equation4278_implies_Equation4362 at h
    apply h
  have eq332 (x y : G) : x ◇ y = y ◇ (x ◇ x) := by
    apply Apply.Equation334_implies_Equation3351 at h
    apply Apply.Equation3351_implies_Equation3344 at h
    apply RewriteHypothesisAndGoal.Equation3344_implies_Equation332 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq332]
  symm
  nth_rewrite 1 [← eq4531]
  symm
  symm
  nth_rewrite 1 [eq4362]
  symm
  nth_rewrite 1 [← eq332]
  apply h
  repeat assumption
@[equational_result]
theorem Equation338_implies_Equation398 (G: Type _) [Magma G] (h: Equation338 G) : Equation398 G := by
  have eq332 (x y : G) : x ◇ y = y ◇ (x ◇ x) := by
    apply NthRewrites.Equation338_implies_Equation3351 at h
    apply Apply.Equation3351_implies_Equation3344 at h
    apply RewriteHypothesisAndGoal.Equation3344_implies_Equation332 at h
    apply h
  have eq4456 (x y z : G) : x ◇ (y ◇ x) = (z ◇ y) ◇ x := by
    apply NthRewrites.Equation338_implies_Equation4562 at h
    apply Apply.Equation4562_implies_Equation4456 at h
    apply h
  have eq4323 (x y z : G) : x ◇ (y ◇ x) = y ◇ (z ◇ x) := by
    apply NthRewrites.Equation338_implies_Equation4263 at h
    apply SimpleRewrites.Equation4263_implies_Equation4253 at h
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
    apply RewriteCombinations.Equation4278_implies_Equation4323 at h
    apply h
  have eq332 (x y : G) : x ◇ y = y ◇ (x ◇ x) := by
    apply NthRewrites.Equation338_implies_Equation3351 at h
    apply Apply.Equation3351_implies_Equation3344 at h
    apply RewriteHypothesisAndGoal.Equation3344_implies_Equation332 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [eq332]
  symm
  nth_rewrite 1 [← eq4456]
  symm
  symm
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
    apply SimpleRewrites.Equation3691_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [← eq40]
  apply h
  repeat assumption
@[equational_result]
theorem Equation366_implies_Equation363 (G: Type _) [Magma G] (h: Equation366 G) : Equation363 G := by
  have eq4677 (x y z : G) : (x ◇ y) ◇ z = (y ◇ x) ◇ z := by
    apply RewriteCombinations.Equation366_implies_Equation4624 at h
    apply RewriteCombinations.Equation4624_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4678 at h
    apply Apply.Equation4678_implies_Equation4677 at h
    apply h
  intro x; repeat intro
  symm
  nth_rewrite 1 [eq4677]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation366_implies_Equation370 (G: Type _) [Magma G] (h: Equation366 G) : Equation370 G := by
  have eq4593 (x y z : G) : (x ◇ x) ◇ x = (y ◇ z) ◇ x := by
    apply RewriteCombinations.Equation366_implies_Equation4624 at h
    apply RewriteCombinations.Equation4624_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4693 at h
    apply Apply.Equation4693_implies_Equation4625 at h
    apply Apply.Equation4625_implies_Equation4593 at h
    apply h
  have eq4589 (x y z : G) : (x ◇ x) ◇ x = (y ◇ x) ◇ z := by
    apply RewriteCombinations.Equation366_implies_Equation4624 at h
    apply RewriteCombinations.Equation4624_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4628 at h
    apply Apply.Equation4628_implies_Equation4596 at h
    apply Apply.Equation4596_implies_Equation4589 at h
    apply h
  intro x; repeat intro
  symm
  nth_rewrite 1 [← eq4593]
  symm
  symm
  nth_rewrite 1 [eq4589]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation366_implies_Equation371 (G: Type _) [Magma G] (h: Equation366 G) : Equation371 G := by
  have eq4594 (x y z : G) : (x ◇ x) ◇ x = (y ◇ z) ◇ y := by
    apply RewriteCombinations.Equation366_implies_Equation4624 at h
    apply RewriteCombinations.Equation4624_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4628 at h
    apply Apply.Equation4628_implies_Equation4626 at h
    apply Apply.Equation4626_implies_Equation4594 at h
    apply h
  have eq4589 (x y z : G) : (x ◇ x) ◇ x = (y ◇ x) ◇ z := by
    apply RewriteCombinations.Equation366_implies_Equation4624 at h
    apply RewriteCombinations.Equation4624_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4628 at h
    apply Apply.Equation4628_implies_Equation4596 at h
    apply Apply.Equation4596_implies_Equation4589 at h
    apply h
  intro x; repeat intro
  symm
  nth_rewrite 1 [← eq4594]
  symm
  symm
  nth_rewrite 1 [eq4589]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation366_implies_Equation372 (G: Type _) [Magma G] (h: Equation366 G) : Equation372 G := by
  have eq4595 (x y z : G) : (x ◇ x) ◇ x = (y ◇ z) ◇ z := by
    apply RewriteCombinations.Equation366_implies_Equation4624 at h
    apply RewriteCombinations.Equation4624_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4628 at h
    apply Apply.Equation4628_implies_Equation4627 at h
    apply Apply.Equation4627_implies_Equation4595 at h
    apply h
  have eq4589 (x y z : G) : (x ◇ x) ◇ x = (y ◇ x) ◇ z := by
    apply RewriteCombinations.Equation366_implies_Equation4624 at h
    apply RewriteCombinations.Equation4624_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4628 at h
    apply Apply.Equation4628_implies_Equation4596 at h
    apply Apply.Equation4596_implies_Equation4589 at h
    apply h
  intro x; repeat intro
  symm
  nth_rewrite 1 [← eq4595]
  symm
  symm
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
  repeat assumption
@[equational_result]
theorem Equation387_implies_Equation4608 (G: Type _) [Magma G] (h: Equation387 G) : Equation4608 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply RewriteHypothesis.Equation387_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation375 at h
    apply h
  intro x; repeat intro
  nth_rewrite 1 [← eq375]
  apply h
  repeat assumption
@[equational_result]
theorem Equation2292_implies_Equation220 (G: Type _) [Magma G] (h: Equation2292 G) : Equation220 G := by
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation2292_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation334 at h
    apply Apply.Equation334_implies_Equation308 at h
    apply Apply.Equation308_implies_Equation307 at h
    apply h
  intro x; repeat intro
  symm
  nth_rewrite 1 [eq307]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2295_implies_Equation2508 (G: Type _) [Magma G] (h: Equation2295 G) : Equation2508 G := by
  have eq4399 (x y : G) : x ◇ (x ◇ y) = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2295_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation398 at h
    apply NthRewrites.Equation398_implies_Equation4220 at h
    apply RewriteHypothesisAndGoal.Equation4220_implies_Equation374 at h
    apply RewriteCombinations.Equation374_implies_Equation380 at h
    apply RewriteCombinations.Equation380_implies_Equation4522 at h
    apply Apply.Equation4522_implies_Equation4404 at h
    apply Apply.Equation4404_implies_Equation4400 at h
    apply Apply.Equation4400_implies_Equation4399 at h
    apply h
  intro x; repeat intro
  symm
  nth_rewrite 1 [← eq4399]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2302_implies_Equation223 (G: Type _) [Magma G] (h: Equation2302 G) : Equation223 G := by
  have eq325 (x y : G) : x ◇ y = x ◇ (y ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation2302_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4186 at h
    apply Apply.Equation4186_implies_Equation4178 at h
    apply NthRewrites.Equation4178_implies_Equation327 at h
    apply Apply.Equation327_implies_Equation325 at h
    apply h
  repeat intro
  symm
  nth_rewrite 3 [eq325]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2305_implies_Equation2302 (G: Type _) [Magma G] (h: Equation2305 G) : Equation2302 G := by
  have eq4314 (x y : G) : x ◇ (y ◇ x) = x ◇ (y ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation2305_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation338 at h
    apply NthRewrites.Equation338_implies_Equation4562 at h
    apply Apply.Equation4562_implies_Equation4510 at h
    apply RewriteGoal.Equation4510_implies_Equation4357 at h
    apply Apply.Equation4357_implies_Equation4339 at h
    apply RewriteHypothesis.Equation4339_implies_Equation4314 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [eq4314]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2309_implies_Equation2512 (G: Type _) [Magma G] (h: Equation2309 G) : Equation2512 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply Apply.Equation2309_implies_Equation2302 at h
    apply RewriteHypothesisAndGoal.Equation2302_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3386 at h
    apply Apply.Equation3386_implies_Equation3385 at h
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  repeat intro
  symm
  nth_rewrite 2 [← eq4512]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2495_implies_Equation2292 (G: Type _) [Magma G] (h: Equation2495 G) : Equation2292 G := by
  have eq4380 (x : G) : x ◇ (x ◇ x) = (x ◇ x) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation2495_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation338 at h
    apply Apply.Equation338_implies_Equation335 at h
    apply NthRewrites.Equation335_implies_Equation4435 at h
    apply Apply.Equation4435_implies_Equation4380 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [eq4380]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2498_implies_Equation2305 (G: Type _) [Magma G] (h: Equation2498 G) : Equation2305 G := by
  have eq4470 (x y : G) : x ◇ (y ◇ y) = (x ◇ x) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2498_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation398 at h
    apply NthRewrites.Equation398_implies_Equation4220 at h
    apply RewriteHypothesisAndGoal.Equation4220_implies_Equation374 at h
    apply RewriteCombinations.Equation374_implies_Equation380 at h
    apply RewriteCombinations.Equation380_implies_Equation4522 at h
    apply Apply.Equation4522_implies_Equation4478 at h
    apply Apply.Equation4478_implies_Equation4471 at h
    apply Apply.Equation4471_implies_Equation4470 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [eq4470]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2505_implies_Equation2498 (G: Type _) [Magma G] (h: Equation2505 G) : Equation2498 G := by
  have eq4598 (x y : G) : (x ◇ x) ◇ y = (x ◇ y) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation2505_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation398 at h
    apply NthRewrites.Equation398_implies_Equation4220 at h
    apply RewriteHypothesisAndGoal.Equation4220_implies_Equation374 at h
    apply RewriteCombinations.Equation374_implies_Equation380 at h
    apply RewriteCombinations.Equation380_implies_Equation363 at h
    apply RewriteHypothesis.Equation363_implies_Equation4676 at h
    apply Apply.Equation4676_implies_Equation4673 at h
    apply Apply.Equation4673_implies_Equation4598 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [eq4598]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation2508_implies_Equation2505 (G: Type _) [Magma G] (h: Equation2508 G) : Equation2505 G := by
  have eq4629 (x y : G) : (x ◇ y) ◇ x = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2508_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4198 at h
    apply Apply.Equation4198_implies_Equation4159 at h
    apply NthRewrites.Equation4159_implies_Equation4407 at h
    apply RewriteHypothesis.Equation4407_implies_Equation4672 at h
    apply Apply.Equation4672_implies_Equation4654 at h
    apply RewriteHypothesis.Equation4654_implies_Equation4629 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [eq4629]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3289_implies_Equation3301 (G: Type _) [Magma G] (h: Equation3289 G) : Equation3301 G := by
  have eq40 (x y : G) : x ◇ x = y ◇ y := by
    apply NthRewrites.Equation3289_implies_Equation3699 at h
    apply SimpleRewrites.Equation3699_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq40]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3290_implies_Equation3302 (G: Type _) [Magma G] (h: Equation3290 G) : Equation3302 G := by
  have eq40 (x y : G) : x ◇ x = y ◇ y := by
    apply NthRewrites.Equation3290_implies_Equation320 at h
    apply Apply.Equation320_implies_Equation316 at h
    apply RewriteHypothesis.Equation316_implies_Equation3298 at h
    apply Apply.Equation3298_implies_Equation3282 at h
    apply RewriteHypothesisAndGoal.Equation3282_implies_Equation40 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq40]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3291_implies_Equation3304 (G: Type _) [Magma G] (h: Equation3291 G) : Equation3304 G := by
  have eq40 (x y : G) : x ◇ x = y ◇ y := by
    apply Apply.Equation3291_implies_Equation3289 at h
    apply NthRewrites.Equation3289_implies_Equation3699 at h
    apply SimpleRewrites.Equation3699_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq40]
  apply h
  repeat assumption
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
  repeat assumption
@[equational_result]
theorem Equation3351_implies_Equation3378 (G: Type _) [Magma G] (h: Equation3351 G) : Equation3378 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply Apply.Equation3351_implies_Equation3344 at h
    apply RewriteHypothesisAndGoal.Equation3344_implies_Equation332 at h
    apply RewriteHypothesis.Equation332_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation375 at h
    apply h
  have eq4622 (x y z : G) : (x ◇ x) ◇ y = (z ◇ z) ◇ y := by
    apply Apply.Equation3351_implies_Equation3350 at h
    apply NthRewrites.Equation3350_implies_Equation4590 at h
    apply RewriteCombinations.Equation4590_implies_Equation4622 at h
    apply h
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply Apply.Equation3351_implies_Equation3344 at h
    apply RewriteHypothesisAndGoal.Equation3344_implies_Equation332 at h
    apply RewriteHypothesis.Equation332_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation375 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq375]
  nth_rewrite 1 [← eq4622]
  nth_rewrite 1 [← eq375]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3362_implies_Equation3377 (G: Type _) [Magma G] (h: Equation3362 G) : Equation3377 G := by
  have eq45 (x y z : G) : x ◇ y = z ◇ y := by
    apply NthRewrites.Equation3362_implies_Equation403 at h
    apply RewriteHypothesis.Equation403_implies_Equation4238 at h
    apply SimpleRewrites.Equation4238_implies_Equation4234 at h
    apply SimpleRewrites.Equation4234_implies_Equation4168 at h
    apply RewriteHypothesisAndGoal.Equation4168_implies_Equation4060 at h
    apply Apply.Equation4060_implies_Equation4055 at h
    apply SimpleRewrites.Equation4055_implies_Equation4031 at h
    apply SimpleRewrites.Equation4031_implies_Equation3965 at h
    apply RewriteHypothesisAndGoal.Equation3965_implies_Equation391 at h
    apply Apply.Equation391_implies_Equation388 at h
    apply RewriteHypothesisAndGoal.Equation388_implies_Equation45 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq45]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3365_implies_Equation3439 (G: Type _) [Magma G] (h: Equation3365 G) : Equation3439 G := by
  have eq326 (x y : G) : x ◇ y = x ◇ (y ◇ y) := by
    apply Apply.Equation3365_implies_Equation3344 at h
    apply RewriteHypothesisAndGoal.Equation3344_implies_Equation332 at h
    apply RewriteHypothesis.Equation332_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation326 at h
    apply h
  have eq4327 (x y z : G) : x ◇ (y ◇ x) = z ◇ (x ◇ x) := by
    apply Apply.Equation3365_implies_Equation3362 at h
    apply NthRewrites.Equation3362_implies_Equation403 at h
    apply RewriteHypothesis.Equation403_implies_Equation4238 at h
    apply SimpleRewrites.Equation4238_implies_Equation4234 at h
    apply SimpleRewrites.Equation4234_implies_Equation4168 at h
    apply RewriteHypothesisAndGoal.Equation4168_implies_Equation4060 at h
    apply Apply.Equation4060_implies_Equation4055 at h
    apply SimpleRewrites.Equation4055_implies_Equation4031 at h
    apply SimpleRewrites.Equation4031_implies_Equation3965 at h
    apply RewriteHypothesisAndGoal.Equation3965_implies_Equation391 at h
    apply Apply.Equation391_implies_Equation388 at h
    apply RewriteHypothesisAndGoal.Equation388_implies_Equation45 at h
    apply RewriteHypothesisAndGoal.Equation45_implies_Equation4278 at h
    apply RewriteCombinations.Equation4278_implies_Equation4327 at h
    apply h
  have eq4314 (x y : G) : x ◇ (y ◇ x) = x ◇ (y ◇ y) := by
    apply Apply.Equation3365_implies_Equation3362 at h
    apply NthRewrites.Equation3362_implies_Equation4527 at h
    apply RewriteGoal.Equation4527_implies_Equation4357 at h
    apply Apply.Equation4357_implies_Equation4339 at h
    apply RewriteHypothesis.Equation4339_implies_Equation4314 at h
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
  repeat assumption
@[equational_result]
theorem Equation3374_implies_Equation3378 (G: Type _) [Magma G] (h: Equation3374 G) : Equation3378 G := by
  have eq45 (x y z : G) : x ◇ y = z ◇ y := by
    apply Apply.Equation3374_implies_Equation3362 at h
    apply NthRewrites.Equation3362_implies_Equation403 at h
    apply RewriteHypothesis.Equation403_implies_Equation4238 at h
    apply SimpleRewrites.Equation4238_implies_Equation4234 at h
    apply SimpleRewrites.Equation4234_implies_Equation4168 at h
    apply RewriteHypothesisAndGoal.Equation4168_implies_Equation4060 at h
    apply Apply.Equation4060_implies_Equation4055 at h
    apply SimpleRewrites.Equation4055_implies_Equation4031 at h
    apply SimpleRewrites.Equation4031_implies_Equation3965 at h
    apply RewriteHypothesisAndGoal.Equation3965_implies_Equation391 at h
    apply Apply.Equation391_implies_Equation388 at h
    apply RewriteHypothesisAndGoal.Equation388_implies_Equation45 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq45]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3385_implies_Equation3588 (G: Type _) [Magma G] (h: Equation3385 G) : Equation3588 G := by
  have eq4512 (x y z : G) : x ◇ (y ◇ z) = (x ◇ y) ◇ z := by
    apply NthRewrites.Equation3385_implies_Equation4512 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [← eq4512]
  symm
  apply h
  repeat assumption
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
  repeat assumption
@[equational_result]
theorem Equation3764_implies_Equation3767 (G: Type _) [Magma G] (h: Equation3764 G) : Equation3767 G := by
  have eq45 (x y z : G) : x ◇ y = z ◇ y := by
    apply NthRewrites.Equation3764_implies_Equation4263 at h
    apply SimpleRewrites.Equation4263_implies_Equation4253 at h
    apply SimpleRewrites.Equation4253_implies_Equation4234 at h
    apply SimpleRewrites.Equation4234_implies_Equation4168 at h
    apply RewriteHypothesisAndGoal.Equation4168_implies_Equation4060 at h
    apply Apply.Equation4060_implies_Equation4055 at h
    apply SimpleRewrites.Equation4055_implies_Equation4031 at h
    apply SimpleRewrites.Equation4031_implies_Equation3965 at h
    apply RewriteHypothesisAndGoal.Equation3965_implies_Equation391 at h
    apply Apply.Equation391_implies_Equation388 at h
    apply RewriteHypothesisAndGoal.Equation388_implies_Equation45 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq45]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3768_implies_Equation3836 (G: Type _) [Magma G] (h: Equation3768 G) : Equation3836 G := by
  have eq42 (x y z : G) : x ◇ y = x ◇ z := by
    apply NthRewrites.Equation3768_implies_Equation3543 at h
    apply SimpleRewrites.Equation3543_implies_Equation3538 at h
    apply SimpleRewrites.Equation3538_implies_Equation3508 at h
    apply RewriteHypothesisAndGoal.Equation3508_implies_Equation3341 at h
    apply Apply.Equation3341_implies_Equation3314 at h
    apply Apply.Equation3314_implies_Equation3307 at h
    apply SimpleRewrites.Equation3307_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply RewriteHypothesisAndGoal.Equation322_implies_Equation42 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq42]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3771_implies_Equation3840 (G: Type _) [Magma G] (h: Equation3771 G) : Equation3840 G := by
  have eq42 (x y z : G) : x ◇ y = x ◇ z := by
    apply Apply.Equation3771_implies_Equation3768 at h
    apply NthRewrites.Equation3768_implies_Equation3543 at h
    apply SimpleRewrites.Equation3543_implies_Equation3538 at h
    apply SimpleRewrites.Equation3538_implies_Equation3508 at h
    apply RewriteHypothesisAndGoal.Equation3508_implies_Equation3341 at h
    apply Apply.Equation3341_implies_Equation3314 at h
    apply Apply.Equation3314_implies_Equation3307 at h
    apply SimpleRewrites.Equation3307_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply RewriteHypothesisAndGoal.Equation322_implies_Equation42 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq42]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3780_implies_Equation3856 (G: Type _) [Magma G] (h: Equation3780 G) : Equation3856 G := by
  have eq42 (x y z : G) : x ◇ y = x ◇ z := by
    apply Apply.Equation3780_implies_Equation3768 at h
    apply NthRewrites.Equation3768_implies_Equation3543 at h
    apply SimpleRewrites.Equation3543_implies_Equation3538 at h
    apply SimpleRewrites.Equation3538_implies_Equation3508 at h
    apply RewriteHypothesisAndGoal.Equation3508_implies_Equation3341 at h
    apply Apply.Equation3341_implies_Equation3314 at h
    apply Apply.Equation3314_implies_Equation3307 at h
    apply SimpleRewrites.Equation3307_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply RewriteHypothesisAndGoal.Equation322_implies_Equation42 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq42]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3814_implies_Equation3818 (G: Type _) [Magma G] (h: Equation3814 G) : Equation3818 G := by
  have eq45 (x y z : G) : x ◇ y = z ◇ y := by
    apply Apply.Equation3814_implies_Equation3764 at h
    apply NthRewrites.Equation3764_implies_Equation4263 at h
    apply SimpleRewrites.Equation4263_implies_Equation4253 at h
    apply SimpleRewrites.Equation4253_implies_Equation4234 at h
    apply SimpleRewrites.Equation4234_implies_Equation4168 at h
    apply RewriteHypothesisAndGoal.Equation4168_implies_Equation4060 at h
    apply Apply.Equation4060_implies_Equation4055 at h
    apply SimpleRewrites.Equation4055_implies_Equation4031 at h
    apply SimpleRewrites.Equation4031_implies_Equation3965 at h
    apply RewriteHypothesisAndGoal.Equation3965_implies_Equation391 at h
    apply Apply.Equation391_implies_Equation388 at h
    apply RewriteHypothesisAndGoal.Equation388_implies_Equation45 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq45]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4017_implies_Equation3909 (G: Type _) [Magma G] (h: Equation4017 G) : Equation3909 G := by
  have eq3255 (x y : G) : x ◇ x = x ◇ (x ◇ (y ◇ x)) := by
    apply Apply.Equation4017_implies_Equation3930 at h
    apply NthRewrites.Equation3930_implies_Equation3324 at h
    apply Apply.Equation3324_implies_Equation3257 at h
    apply Apply.Equation3257_implies_Equation3255 at h
    apply h
  have eq3308 (x y : G) : x ◇ y = x ◇ (x ◇ (y ◇ x)) := by
    apply Apply.Equation4017_implies_Equation4013 at h
    apply NthRewrites.Equation4013_implies_Equation3331 at h
    apply Apply.Equation3331_implies_Equation3308 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq3255]
  nth_rewrite 1 [← eq3308]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4085_implies_Equation4107 (G: Type _) [Magma G] (h: Equation4085 G) : Equation4107 G := by
  have eq40 (x y : G) : x ◇ x = y ◇ y := by
    apply NthRewrites.Equation4085_implies_Equation369 at h
    apply Apply.Equation369_implies_Equation368 at h
    apply RewriteHypothesis.Equation368_implies_Equation4095 at h
    apply Apply.Equation4095_implies_Equation4094 at h
    apply RewriteHypothesisAndGoal.Equation4094_implies_Equation40 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq40]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4087_implies_Equation4113 (G: Type _) [Magma G] (h: Equation4087 G) : Equation4113 G := by
  have eq40 (x y : G) : x ◇ x = y ◇ y := by
    apply NthRewrites.Equation4087_implies_Equation3691 at h
    apply SimpleRewrites.Equation3691_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq40]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4089_implies_Equation4116 (G: Type _) [Magma G] (h: Equation4089 G) : Equation4116 G := by
  have eq40 (x y : G) : x ◇ x = y ◇ y := by
    apply Apply.Equation4089_implies_Equation4087 at h
    apply NthRewrites.Equation4087_implies_Equation3691 at h
    apply SimpleRewrites.Equation3691_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq40]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4119_implies_Equation4153 (G: Type _) [Magma G] (h: Equation4119 G) : Equation4153 G := by
  have eq322 (x y : G) : x ◇ y = x ◇ (x ◇ x) := by
    apply Apply.Equation4119_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply Apply.Equation42_implies_Equation3544 at h
    apply SimpleRewrites.Equation3544_implies_Equation3517 at h
    apply SimpleRewrites.Equation3517_implies_Equation3510 at h
    apply Apply.Equation3510_implies_Equation3508 at h
    apply RewriteHypothesisAndGoal.Equation3508_implies_Equation3341 at h
    apply Apply.Equation3341_implies_Equation3314 at h
    apply Apply.Equation3314_implies_Equation3307 at h
    apply SimpleRewrites.Equation3307_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply h
  have eq4136 (x y z w : G) : x ◇ y = ((x ◇ y) ◇ z) ◇ w := by
    apply Apply.Equation4119_implies_Equation4117 at h
    apply NthRewrites.Equation4117_implies_Equation4123 at h
    apply RewriteCombinations.Equation4123_implies_Equation4126 at h
    apply Apply.Equation4126_implies_Equation4122 at h
    apply NthRewrites.Equation4122_implies_Equation4132 at h
    apply NthRewrites.Equation4132_implies_Equation4129 at h
    apply NthRewrites.Equation4129_implies_Equation4136 at h
    apply h
  have eq4118 (x y : G) : x ◇ y = ((x ◇ x) ◇ x) ◇ y := by
    apply Apply.Equation4119_implies_Equation4117 at h
    apply NthRewrites.Equation4117_implies_Equation4123 at h
    apply RewriteCombinations.Equation4123_implies_Equation4126 at h
    apply Apply.Equation4126_implies_Equation4124 at h
    apply NthRewrites.Equation4124_implies_Equation4150 at h
    apply Apply.Equation4150_implies_Equation4138 at h
    apply Apply.Equation4138_implies_Equation4118 at h
    apply h
  have eq322 (x y : G) : x ◇ y = x ◇ (x ◇ x) := by
    apply Apply.Equation4119_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply Apply.Equation42_implies_Equation3544 at h
    apply SimpleRewrites.Equation3544_implies_Equation3517 at h
    apply SimpleRewrites.Equation3517_implies_Equation3510 at h
    apply Apply.Equation3510_implies_Equation3508 at h
    apply RewriteHypothesisAndGoal.Equation3508_implies_Equation3341 at h
    apply Apply.Equation3341_implies_Equation3314 at h
    apply Apply.Equation3314_implies_Equation3307 at h
    apply SimpleRewrites.Equation3307_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq322]
  symm
  nth_rewrite 1 [← eq4136]
  symm
  symm
  nth_rewrite 1 [eq4118]
  symm
  nth_rewrite 1 [← eq322]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4122_implies_Equation4126 (G: Type _) [Magma G] (h: Equation4122 G) : Equation4126 G := by
  have eq4069 (x y z : G) : x ◇ x = ((x ◇ x) ◇ y) ◇ z := by
    apply NthRewrites.Equation4122_implies_Equation4132 at h
    apply NthRewrites.Equation4132_implies_Equation4069 at h
    apply h
  have eq4069 (x y z : G) : x ◇ x = ((x ◇ x) ◇ y) ◇ z := by
    apply NthRewrites.Equation4122_implies_Equation4132 at h
    apply NthRewrites.Equation4132_implies_Equation4069 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [← eq4069]
  symm
  symm
  nth_rewrite 1 [eq4069]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4126_implies_Equation4079 (G: Type _) [Magma G] (h: Equation4126 G) : Equation4079 G := by
  have eq4136 (x y z w : G) : x ◇ y = ((x ◇ y) ◇ z) ◇ w := by
    apply Apply.Equation4126_implies_Equation4122 at h
    apply NthRewrites.Equation4122_implies_Equation4132 at h
    apply NthRewrites.Equation4132_implies_Equation4129 at h
    apply NthRewrites.Equation4129_implies_Equation4136 at h
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
  symm
  symm
  nth_rewrite 1 [eq4122]
  symm
  nth_rewrite 1 [eq38]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4126_implies_Equation4148 (G: Type _) [Magma G] (h: Equation4126 G) : Equation4148 G := by
  have eq322 (x y : G) : x ◇ y = x ◇ (x ◇ x) := by
    apply Apply.Equation4126_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply Apply.Equation42_implies_Equation3544 at h
    apply SimpleRewrites.Equation3544_implies_Equation3517 at h
    apply SimpleRewrites.Equation3517_implies_Equation3510 at h
    apply Apply.Equation3510_implies_Equation3508 at h
    apply RewriteHypothesisAndGoal.Equation3508_implies_Equation3341 at h
    apply Apply.Equation3341_implies_Equation3314 at h
    apply Apply.Equation3314_implies_Equation3307 at h
    apply SimpleRewrites.Equation3307_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply h
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
    apply Apply.Equation42_implies_Equation3544 at h
    apply SimpleRewrites.Equation3544_implies_Equation3517 at h
    apply SimpleRewrites.Equation3517_implies_Equation3510 at h
    apply Apply.Equation3510_implies_Equation3508 at h
    apply RewriteHypothesisAndGoal.Equation3508_implies_Equation3341 at h
    apply Apply.Equation3341_implies_Equation3314 at h
    apply Apply.Equation3314_implies_Equation3307 at h
    apply SimpleRewrites.Equation3307_implies_Equation3305 at h
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
theorem Equation4126_implies_Equation4147 (G: Type _) [Magma G] (h: Equation4126 G) : Equation4147 G := by
  have eq322 (x y : G) : x ◇ y = x ◇ (x ◇ x) := by
    apply Apply.Equation4126_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply Apply.Equation42_implies_Equation3544 at h
    apply SimpleRewrites.Equation3544_implies_Equation3517 at h
    apply SimpleRewrites.Equation3517_implies_Equation3510 at h
    apply Apply.Equation3510_implies_Equation3508 at h
    apply RewriteHypothesisAndGoal.Equation3508_implies_Equation3341 at h
    apply Apply.Equation3341_implies_Equation3314 at h
    apply Apply.Equation3314_implies_Equation3307 at h
    apply SimpleRewrites.Equation3307_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply h
  have eq4131 (x y : G) : x ◇ y = ((x ◇ y) ◇ y) ◇ y := by
    apply Apply.Equation4126_implies_Equation4122 at h
    apply NthRewrites.Equation4122_implies_Equation4132 at h
    apply NthRewrites.Equation4132_implies_Equation4134 at h
    apply Apply.Equation4134_implies_Equation4131 at h
    apply h
  have eq4122 (x y z : G) : x ◇ y = ((x ◇ x) ◇ y) ◇ z := by
    apply Apply.Equation4126_implies_Equation4122 at h
    apply h
  have eq322 (x y : G) : x ◇ y = x ◇ (x ◇ x) := by
    apply Apply.Equation4126_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply Apply.Equation42_implies_Equation3544 at h
    apply SimpleRewrites.Equation3544_implies_Equation3517 at h
    apply SimpleRewrites.Equation3517_implies_Equation3510 at h
    apply Apply.Equation3510_implies_Equation3508 at h
    apply RewriteHypothesisAndGoal.Equation3508_implies_Equation3341 at h
    apply Apply.Equation3341_implies_Equation3314 at h
    apply Apply.Equation3314_implies_Equation3307 at h
    apply SimpleRewrites.Equation3307_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq322]
  symm
  nth_rewrite 1 [← eq4131]
  symm
  symm
  nth_rewrite 1 [eq4122]
  symm
  nth_rewrite 1 [← eq322]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4126_implies_Equation4152 (G: Type _) [Magma G] (h: Equation4126 G) : Equation4152 G := by
  have eq322 (x y : G) : x ◇ y = x ◇ (x ◇ x) := by
    apply Apply.Equation4126_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply Apply.Equation42_implies_Equation3544 at h
    apply SimpleRewrites.Equation3544_implies_Equation3517 at h
    apply SimpleRewrites.Equation3517_implies_Equation3510 at h
    apply Apply.Equation3510_implies_Equation3508 at h
    apply RewriteHypothesisAndGoal.Equation3508_implies_Equation3341 at h
    apply Apply.Equation3341_implies_Equation3314 at h
    apply Apply.Equation3314_implies_Equation3307 at h
    apply SimpleRewrites.Equation3307_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply h
  have eq4135 (x y z : G) : x ◇ y = ((x ◇ y) ◇ z) ◇ z := by
    apply Apply.Equation4126_implies_Equation4122 at h
    apply NthRewrites.Equation4122_implies_Equation4132 at h
    apply NthRewrites.Equation4132_implies_Equation4135 at h
    apply h
  have eq4122 (x y z : G) : x ◇ y = ((x ◇ x) ◇ y) ◇ z := by
    apply Apply.Equation4126_implies_Equation4122 at h
    apply h
  have eq322 (x y : G) : x ◇ y = x ◇ (x ◇ x) := by
    apply Apply.Equation4126_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply Apply.Equation42_implies_Equation3544 at h
    apply SimpleRewrites.Equation3544_implies_Equation3517 at h
    apply SimpleRewrites.Equation3517_implies_Equation3510 at h
    apply Apply.Equation3510_implies_Equation3508 at h
    apply RewriteHypothesisAndGoal.Equation3508_implies_Equation3341 at h
    apply Apply.Equation3341_implies_Equation3314 at h
    apply Apply.Equation3314_implies_Equation3307 at h
    apply SimpleRewrites.Equation3307_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq322]
  symm
  nth_rewrite 1 [← eq4135]
  symm
  symm
  nth_rewrite 1 [eq4122]
  symm
  nth_rewrite 1 [← eq322]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4139_implies_Equation4153 (G: Type _) [Magma G] (h: Equation4139 G) : Equation4153 G := by
  have eq322 (x y : G) : x ◇ y = x ◇ (x ◇ x) := by
    apply RewriteCombinations.Equation4139_implies_Equation4140 at h
    apply Apply.Equation4140_implies_Equation4137 at h
    apply RewriteCombinations.Equation4137_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply Apply.Equation42_implies_Equation3544 at h
    apply SimpleRewrites.Equation3544_implies_Equation3517 at h
    apply SimpleRewrites.Equation3517_implies_Equation3510 at h
    apply Apply.Equation3510_implies_Equation3508 at h
    apply RewriteHypothesisAndGoal.Equation3508_implies_Equation3341 at h
    apply Apply.Equation3341_implies_Equation3314 at h
    apply Apply.Equation3314_implies_Equation3307 at h
    apply SimpleRewrites.Equation3307_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply h
  have eq4136 (x y z w : G) : x ◇ y = ((x ◇ y) ◇ z) ◇ w := by
    apply RewriteCombinations.Equation4139_implies_Equation4140 at h
    apply Apply.Equation4140_implies_Equation4137 at h
    apply RewriteCombinations.Equation4137_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply NthRewrites.Equation4117_implies_Equation4123 at h
    apply RewriteCombinations.Equation4123_implies_Equation4126 at h
    apply Apply.Equation4126_implies_Equation4122 at h
    apply NthRewrites.Equation4122_implies_Equation4132 at h
    apply NthRewrites.Equation4132_implies_Equation4129 at h
    apply NthRewrites.Equation4129_implies_Equation4136 at h
    apply h
  have eq4128 (x y : G) : x ◇ y = ((x ◇ y) ◇ x) ◇ y := by
    apply RewriteCombinations.Equation4139_implies_Equation4140 at h
    apply Apply.Equation4140_implies_Equation4137 at h
    apply RewriteCombinations.Equation4137_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply NthRewrites.Equation4117_implies_Equation4123 at h
    apply RewriteCombinations.Equation4123_implies_Equation4126 at h
    apply Apply.Equation4126_implies_Equation4122 at h
    apply NthRewrites.Equation4122_implies_Equation4132 at h
    apply NthRewrites.Equation4132_implies_Equation4134 at h
    apply Apply.Equation4134_implies_Equation4128 at h
    apply h
  have eq322 (x y : G) : x ◇ y = x ◇ (x ◇ x) := by
    apply RewriteCombinations.Equation4139_implies_Equation4140 at h
    apply Apply.Equation4140_implies_Equation4137 at h
    apply RewriteCombinations.Equation4137_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply Apply.Equation42_implies_Equation3544 at h
    apply SimpleRewrites.Equation3544_implies_Equation3517 at h
    apply SimpleRewrites.Equation3517_implies_Equation3510 at h
    apply Apply.Equation3510_implies_Equation3508 at h
    apply RewriteHypothesisAndGoal.Equation3508_implies_Equation3341 at h
    apply Apply.Equation3341_implies_Equation3314 at h
    apply Apply.Equation3314_implies_Equation3307 at h
    apply SimpleRewrites.Equation3307_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq322]
  symm
  nth_rewrite 1 [← eq4136]
  symm
  symm
  nth_rewrite 1 [eq4128]
  symm
  nth_rewrite 1 [← eq322]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4140_implies_Equation4153 (G: Type _) [Magma G] (h: Equation4140 G) : Equation4153 G := by
  have eq322 (x y : G) : x ◇ y = x ◇ (x ◇ x) := by
    apply Apply.Equation4140_implies_Equation4137 at h
    apply RewriteCombinations.Equation4137_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply Apply.Equation42_implies_Equation3544 at h
    apply SimpleRewrites.Equation3544_implies_Equation3517 at h
    apply SimpleRewrites.Equation3517_implies_Equation3510 at h
    apply Apply.Equation3510_implies_Equation3508 at h
    apply RewriteHypothesisAndGoal.Equation3508_implies_Equation3341 at h
    apply Apply.Equation3341_implies_Equation3314 at h
    apply Apply.Equation3314_implies_Equation3307 at h
    apply SimpleRewrites.Equation3307_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply h
  have eq4136 (x y z w : G) : x ◇ y = ((x ◇ y) ◇ z) ◇ w := by
    apply Apply.Equation4140_implies_Equation4137 at h
    apply RewriteCombinations.Equation4137_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply NthRewrites.Equation4117_implies_Equation4123 at h
    apply RewriteCombinations.Equation4123_implies_Equation4126 at h
    apply Apply.Equation4126_implies_Equation4122 at h
    apply NthRewrites.Equation4122_implies_Equation4132 at h
    apply NthRewrites.Equation4132_implies_Equation4129 at h
    apply NthRewrites.Equation4129_implies_Equation4136 at h
    apply h
  have eq4129 (x y z : G) : x ◇ y = ((x ◇ y) ◇ x) ◇ z := by
    apply Apply.Equation4140_implies_Equation4137 at h
    apply RewriteCombinations.Equation4137_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply NthRewrites.Equation4117_implies_Equation4123 at h
    apply RewriteCombinations.Equation4123_implies_Equation4126 at h
    apply Apply.Equation4126_implies_Equation4122 at h
    apply NthRewrites.Equation4122_implies_Equation4132 at h
    apply NthRewrites.Equation4132_implies_Equation4129 at h
    apply h
  have eq322 (x y : G) : x ◇ y = x ◇ (x ◇ x) := by
    apply Apply.Equation4140_implies_Equation4137 at h
    apply RewriteCombinations.Equation4137_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply Apply.Equation42_implies_Equation3544 at h
    apply SimpleRewrites.Equation3544_implies_Equation3517 at h
    apply SimpleRewrites.Equation3517_implies_Equation3510 at h
    apply Apply.Equation3510_implies_Equation3508 at h
    apply RewriteHypothesisAndGoal.Equation3508_implies_Equation3341 at h
    apply Apply.Equation3341_implies_Equation3314 at h
    apply Apply.Equation3314_implies_Equation3307 at h
    apply SimpleRewrites.Equation3307_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq322]
  symm
  nth_rewrite 1 [← eq4136]
  symm
  symm
  nth_rewrite 1 [eq4129]
  symm
  nth_rewrite 1 [← eq322]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4144_implies_Equation4153 (G: Type _) [Magma G] (h: Equation4144 G) : Equation4153 G := by
  have eq4122 (x y z : G) : x ◇ y = ((x ◇ x) ◇ y) ◇ z := by
    apply Apply.Equation4144_implies_Equation4122 at h
    apply h
  have eq4124 (x y z : G) : x ◇ y = ((x ◇ x) ◇ z) ◇ y := by
    apply Apply.Equation4144_implies_Equation4142 at h
    apply NthRewrites.Equation4142_implies_Equation4124 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq4122]
  nth_rewrite 1 [← eq4124]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4147_implies_Equation4153 (G: Type _) [Magma G] (h: Equation4147 G) : Equation4153 G := by
  have eq322 (x y : G) : x ◇ y = x ◇ (x ◇ x) := by
    apply RewriteCombinations.Equation4147_implies_Equation4148 at h
    apply Apply.Equation4148_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply Apply.Equation42_implies_Equation3544 at h
    apply SimpleRewrites.Equation3544_implies_Equation3517 at h
    apply SimpleRewrites.Equation3517_implies_Equation3510 at h
    apply Apply.Equation3510_implies_Equation3508 at h
    apply RewriteHypothesisAndGoal.Equation3508_implies_Equation3341 at h
    apply Apply.Equation3341_implies_Equation3314 at h
    apply Apply.Equation3314_implies_Equation3307 at h
    apply SimpleRewrites.Equation3307_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply h
  have eq4136 (x y z w : G) : x ◇ y = ((x ◇ y) ◇ z) ◇ w := by
    apply RewriteCombinations.Equation4147_implies_Equation4148 at h
    apply Apply.Equation4148_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply NthRewrites.Equation4117_implies_Equation4123 at h
    apply RewriteCombinations.Equation4123_implies_Equation4126 at h
    apply Apply.Equation4126_implies_Equation4122 at h
    apply NthRewrites.Equation4122_implies_Equation4132 at h
    apply NthRewrites.Equation4132_implies_Equation4129 at h
    apply NthRewrites.Equation4129_implies_Equation4136 at h
    apply h
  have eq4131 (x y : G) : x ◇ y = ((x ◇ y) ◇ y) ◇ y := by
    apply NthRewrites.Equation4147_implies_Equation4143 at h
    apply NthRewrites.Equation4143_implies_Equation4135 at h
    apply Apply.Equation4135_implies_Equation4131 at h
    apply h
  have eq322 (x y : G) : x ◇ y = x ◇ (x ◇ x) := by
    apply RewriteCombinations.Equation4147_implies_Equation4148 at h
    apply Apply.Equation4148_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply Apply.Equation42_implies_Equation3544 at h
    apply SimpleRewrites.Equation3544_implies_Equation3517 at h
    apply SimpleRewrites.Equation3517_implies_Equation3510 at h
    apply Apply.Equation3510_implies_Equation3508 at h
    apply RewriteHypothesisAndGoal.Equation3508_implies_Equation3341 at h
    apply Apply.Equation3341_implies_Equation3314 at h
    apply Apply.Equation3314_implies_Equation3307 at h
    apply SimpleRewrites.Equation3307_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq322]
  symm
  nth_rewrite 1 [← eq4136]
  symm
  symm
  nth_rewrite 1 [eq4131]
  symm
  nth_rewrite 1 [← eq322]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4148_implies_Equation4153 (G: Type _) [Magma G] (h: Equation4148 G) : Equation4153 G := by
  have eq322 (x y : G) : x ◇ y = x ◇ (x ◇ x) := by
    apply Apply.Equation4148_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply Apply.Equation42_implies_Equation3544 at h
    apply SimpleRewrites.Equation3544_implies_Equation3517 at h
    apply SimpleRewrites.Equation3517_implies_Equation3510 at h
    apply Apply.Equation3510_implies_Equation3508 at h
    apply RewriteHypothesisAndGoal.Equation3508_implies_Equation3341 at h
    apply Apply.Equation3341_implies_Equation3314 at h
    apply Apply.Equation3314_implies_Equation3307 at h
    apply SimpleRewrites.Equation3307_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply h
  have eq4136 (x y z w : G) : x ◇ y = ((x ◇ y) ◇ z) ◇ w := by
    apply Apply.Equation4148_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply NthRewrites.Equation4117_implies_Equation4123 at h
    apply RewriteCombinations.Equation4123_implies_Equation4126 at h
    apply Apply.Equation4126_implies_Equation4122 at h
    apply NthRewrites.Equation4122_implies_Equation4132 at h
    apply NthRewrites.Equation4132_implies_Equation4129 at h
    apply NthRewrites.Equation4129_implies_Equation4136 at h
    apply h
  have eq4132 (x y z : G) : x ◇ y = ((x ◇ y) ◇ y) ◇ z := by
    apply Apply.Equation4148_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply NthRewrites.Equation4117_implies_Equation4123 at h
    apply RewriteCombinations.Equation4123_implies_Equation4126 at h
    apply Apply.Equation4126_implies_Equation4122 at h
    apply NthRewrites.Equation4122_implies_Equation4132 at h
    apply h
  have eq322 (x y : G) : x ◇ y = x ◇ (x ◇ x) := by
    apply Apply.Equation4148_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply Apply.Equation42_implies_Equation3544 at h
    apply SimpleRewrites.Equation3544_implies_Equation3517 at h
    apply SimpleRewrites.Equation3517_implies_Equation3510 at h
    apply Apply.Equation3510_implies_Equation3508 at h
    apply RewriteHypothesisAndGoal.Equation3508_implies_Equation3341 at h
    apply Apply.Equation3341_implies_Equation3314 at h
    apply Apply.Equation3314_implies_Equation3307 at h
    apply SimpleRewrites.Equation3307_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq322]
  symm
  nth_rewrite 1 [← eq4136]
  symm
  symm
  nth_rewrite 1 [eq4132]
  symm
  nth_rewrite 1 [← eq322]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4151_implies_Equation4149 (G: Type _) [Magma G] (h: Equation4151 G) : Equation4149 G := by
  have eq38 (x y : G) : x ◇ x = x ◇ y := by
    apply Apply.Equation4151_implies_Equation4147 at h
    apply RewriteCombinations.Equation4147_implies_Equation4148 at h
    apply Apply.Equation4148_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply Subgraph.Equation42_implies_Equation38 at h
    apply h
  have eq4133 (x y z : G) : x ◇ y = ((x ◇ y) ◇ z) ◇ x := by
    apply Apply.Equation4151_implies_Equation4147 at h
    apply RewriteCombinations.Equation4147_implies_Equation4148 at h
    apply Apply.Equation4148_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply NthRewrites.Equation4117_implies_Equation4123 at h
    apply RewriteCombinations.Equation4123_implies_Equation4126 at h
    apply Apply.Equation4126_implies_Equation4122 at h
    apply NthRewrites.Equation4122_implies_Equation4132 at h
    apply NthRewrites.Equation4132_implies_Equation4133 at h
    apply h
  have eq4134 (x y z : G) : x ◇ y = ((x ◇ y) ◇ z) ◇ y := by
    apply Apply.Equation4151_implies_Equation4147 at h
    apply RewriteCombinations.Equation4147_implies_Equation4148 at h
    apply Apply.Equation4148_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply NthRewrites.Equation4117_implies_Equation4123 at h
    apply RewriteCombinations.Equation4123_implies_Equation4126 at h
    apply Apply.Equation4126_implies_Equation4122 at h
    apply NthRewrites.Equation4122_implies_Equation4132 at h
    apply NthRewrites.Equation4132_implies_Equation4134 at h
    apply h
  have eq38 (x y : G) : x ◇ x = x ◇ y := by
    apply Apply.Equation4151_implies_Equation4147 at h
    apply RewriteCombinations.Equation4147_implies_Equation4148 at h
    apply Apply.Equation4148_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply Subgraph.Equation42_implies_Equation38 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq38]
  symm
  nth_rewrite 1 [← eq4133]
  symm
  symm
  nth_rewrite 1 [eq4134]
  symm
  nth_rewrite 1 [eq38]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4152_implies_Equation4153 (G: Type _) [Magma G] (h: Equation4152 G) : Equation4153 G := by
  have eq322 (x y : G) : x ◇ y = x ◇ (x ◇ x) := by
    apply Apply.Equation4152_implies_Equation4147 at h
    apply RewriteCombinations.Equation4147_implies_Equation4148 at h
    apply Apply.Equation4148_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply Apply.Equation42_implies_Equation3544 at h
    apply SimpleRewrites.Equation3544_implies_Equation3517 at h
    apply SimpleRewrites.Equation3517_implies_Equation3510 at h
    apply Apply.Equation3510_implies_Equation3508 at h
    apply RewriteHypothesisAndGoal.Equation3508_implies_Equation3341 at h
    apply Apply.Equation3341_implies_Equation3314 at h
    apply Apply.Equation3314_implies_Equation3307 at h
    apply SimpleRewrites.Equation3307_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply h
  have eq4136 (x y z w : G) : x ◇ y = ((x ◇ y) ◇ z) ◇ w := by
    apply Apply.Equation4152_implies_Equation4147 at h
    apply RewriteCombinations.Equation4147_implies_Equation4148 at h
    apply Apply.Equation4148_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply NthRewrites.Equation4117_implies_Equation4123 at h
    apply RewriteCombinations.Equation4123_implies_Equation4126 at h
    apply Apply.Equation4126_implies_Equation4122 at h
    apply NthRewrites.Equation4122_implies_Equation4132 at h
    apply NthRewrites.Equation4132_implies_Equation4129 at h
    apply NthRewrites.Equation4129_implies_Equation4136 at h
    apply h
  have eq4135 (x y z : G) : x ◇ y = ((x ◇ y) ◇ z) ◇ z := by
    apply Apply.Equation4152_implies_Equation4147 at h
    apply NthRewrites.Equation4147_implies_Equation4143 at h
    apply NthRewrites.Equation4143_implies_Equation4135 at h
    apply h
  have eq322 (x y : G) : x ◇ y = x ◇ (x ◇ x) := by
    apply Apply.Equation4152_implies_Equation4147 at h
    apply RewriteCombinations.Equation4147_implies_Equation4148 at h
    apply Apply.Equation4148_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply Apply.Equation42_implies_Equation3544 at h
    apply SimpleRewrites.Equation3544_implies_Equation3517 at h
    apply SimpleRewrites.Equation3517_implies_Equation3510 at h
    apply Apply.Equation3510_implies_Equation3508 at h
    apply RewriteHypothesisAndGoal.Equation3508_implies_Equation3341 at h
    apply Apply.Equation3341_implies_Equation3314 at h
    apply Apply.Equation3314_implies_Equation3307 at h
    apply SimpleRewrites.Equation3307_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq322]
  symm
  nth_rewrite 1 [← eq4136]
  symm
  symm
  nth_rewrite 1 [eq4135]
  symm
  nth_rewrite 1 [← eq322]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4170_implies_Equation4237 (G: Type _) [Magma G] (h: Equation4170 G) : Equation4237 G := by
  have eq42 (x y z : G) : x ◇ y = x ◇ z := by
    apply NthRewrites.Equation4170_implies_Equation330 at h
    apply RewriteHypothesis.Equation330_implies_Equation3340 at h
    apply Apply.Equation3340_implies_Equation3335 at h
    apply SimpleRewrites.Equation3335_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply RewriteHypothesisAndGoal.Equation322_implies_Equation42 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq42]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4186_implies_Equation4262 (G: Type _) [Magma G] (h: Equation4186 G) : Equation4262 G := by
  have eq42 (x y z : G) : x ◇ y = x ◇ z := by
    apply Apply.Equation4186_implies_Equation4170 at h
    apply NthRewrites.Equation4170_implies_Equation330 at h
    apply RewriteHypothesis.Equation330_implies_Equation3340 at h
    apply Apply.Equation3340_implies_Equation3335 at h
    apply SimpleRewrites.Equation3335_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply RewriteHypothesisAndGoal.Equation322_implies_Equation42 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq42]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4198_implies_Equation4207 (G: Type _) [Magma G] (h: Equation4198 G) : Equation4207 G := by
  have eq42 (x y z : G) : x ◇ y = x ◇ z := by
    apply RewriteHypothesisAndGoal.Equation4198_implies_Equation376 at h
    apply Apply.Equation376_implies_Equation374 at h
    apply RewriteCombinations.Equation374_implies_Equation380 at h
    apply RewriteCombinations.Equation380_implies_Equation4153 at h
    apply Apply.Equation4153_implies_Equation4149 at h
    apply Apply.Equation4149_implies_Equation4145 at h
    apply RewriteCombinations.Equation4145_implies_Equation4148 at h
    apply Apply.Equation4148_implies_Equation4119 at h
    apply Apply.Equation4119_implies_Equation4117 at h
    apply RewriteHypothesisAndGoal.Equation4117_implies_Equation42 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq42]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4204_implies_Equation4263 (G: Type _) [Magma G] (h: Equation4204 G) : Equation4263 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply Apply.Equation4204_implies_Equation4192 at h
    apply RewriteHypothesisAndGoal.Equation4192_implies_Equation375 at h
    apply h
  have eq4622 (x y z : G) : (x ◇ x) ◇ y = (z ◇ z) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation4204_implies_Equation4625 at h
    apply Apply.Equation4625_implies_Equation4611 at h
    apply RewriteHypothesis.Equation4611_implies_Equation4590 at h
    apply RewriteCombinations.Equation4590_implies_Equation4622 at h
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
  repeat assumption
@[equational_result]
theorem Equation4220_implies_Equation4262 (G: Type _) [Magma G] (h: Equation4220 G) : Equation4262 G := by
  have eq42 (x y z : G) : x ◇ y = x ◇ z := by
    apply Apply.Equation4220_implies_Equation4170 at h
    apply NthRewrites.Equation4170_implies_Equation330 at h
    apply RewriteHypothesis.Equation330_implies_Equation3340 at h
    apply Apply.Equation3340_implies_Equation3335 at h
    apply SimpleRewrites.Equation3335_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply RewriteHypothesisAndGoal.Equation322_implies_Equation42 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq42]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4247_implies_Equation4262 (G: Type _) [Magma G] (h: Equation4247 G) : Equation4262 G := by
  have eq326 (x y : G) : x ◇ y = x ◇ (y ◇ y) := by
    apply Apply.Equation4247_implies_Equation4178 at h
    apply NthRewrites.Equation4178_implies_Equation327 at h
    apply Apply.Equation327_implies_Equation326 at h
    apply h
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
  repeat assumption
@[equational_result]
theorem Equation4301_implies_Equation4311 (G: Type _) [Magma G] (h: Equation4301 G) : Equation4311 G := by
  have eq4294 (x y z : G) : x ◇ (x ◇ y) = y ◇ (y ◇ z) := by
    apply NthRewrites.Equation4301_implies_Equation4277 at h
    apply RewriteCombinations.Equation4277_implies_Equation4294 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4294]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4331_implies_Equation4337 (G: Type _) [Magma G] (h: Equation4331 G) : Equation4337 G := by
  have eq4273 (x y : G) : x ◇ (x ◇ x) = y ◇ (x ◇ y) := by
    apply RewriteHypothesis.Equation4331_implies_Equation4273 at h
    apply h
  have eq4270 (x y : G) : x ◇ (x ◇ x) = x ◇ (y ◇ y) := by
    apply NthRewrites.Equation4331_implies_Equation4355 at h
    apply Apply.Equation4355_implies_Equation4280 at h
    apply RewriteCombinations.Equation4280_implies_Equation4341 at h
    apply Apply.Equation4341_implies_Equation4270 at h
    apply h
  have eq4314 (x y : G) : x ◇ (y ◇ x) = x ◇ (y ◇ y) := by
    apply Apply.Equation4331_implies_Equation4314 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4273]
  nth_rewrite 1 [eq4270]
  nth_rewrite 1 [← eq4314]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4387_implies_Equation4384 (G: Type _) [Magma G] (h: Equation4387 G) : Equation4384 G := by
  have eq4677 (x y z : G) : (x ◇ y) ◇ z = (y ◇ x) ◇ z := by
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4667 at h
    apply Apply.Equation4667_implies_Equation4665 at h
    apply RewriteCombinations.Equation4665_implies_Equation4668 at h
    apply RewriteCombinations.Equation4668_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4678 at h
    apply Apply.Equation4678_implies_Equation4677 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [eq4677]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4387_implies_Equation4390 (G: Type _) [Magma G] (h: Equation4387 G) : Equation4390 G := by
  have eq4592 (x y z : G) : (x ◇ x) ◇ x = (y ◇ y) ◇ z := by
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4667 at h
    apply Apply.Equation4667_implies_Equation4665 at h
    apply RewriteCombinations.Equation4665_implies_Equation4668 at h
    apply RewriteCombinations.Equation4668_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4628 at h
    apply Apply.Equation4628_implies_Equation4627 at h
    apply RewriteHypothesis.Equation4627_implies_Equation4592 at h
    apply h
  have eq4589 (x y z : G) : (x ◇ x) ◇ x = (y ◇ x) ◇ z := by
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4667 at h
    apply Apply.Equation4667_implies_Equation4665 at h
    apply RewriteCombinations.Equation4665_implies_Equation4668 at h
    apply RewriteCombinations.Equation4668_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4628 at h
    apply Apply.Equation4628_implies_Equation4596 at h
    apply Apply.Equation4596_implies_Equation4589 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [← eq4592]
  symm
  symm
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
    apply RewriteCombinations.Equation4668_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4693 at h
    apply Apply.Equation4693_implies_Equation4625 at h
    apply Apply.Equation4625_implies_Equation4593 at h
    apply h
  have eq4589 (x y z : G) : (x ◇ x) ◇ x = (y ◇ x) ◇ z := by
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4667 at h
    apply Apply.Equation4667_implies_Equation4665 at h
    apply RewriteCombinations.Equation4665_implies_Equation4668 at h
    apply RewriteCombinations.Equation4668_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4628 at h
    apply Apply.Equation4628_implies_Equation4596 at h
    apply Apply.Equation4596_implies_Equation4589 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [← eq4593]
  symm
  symm
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
    apply Apply.Equation4628_implies_Equation4626 at h
    apply Apply.Equation4626_implies_Equation4594 at h
    apply h
  have eq4589 (x y z : G) : (x ◇ x) ◇ x = (y ◇ x) ◇ z := by
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4667 at h
    apply Apply.Equation4667_implies_Equation4665 at h
    apply RewriteCombinations.Equation4665_implies_Equation4668 at h
    apply RewriteCombinations.Equation4668_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4628 at h
    apply Apply.Equation4628_implies_Equation4596 at h
    apply Apply.Equation4596_implies_Equation4589 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [← eq4594]
  symm
  symm
  nth_rewrite 1 [eq4589]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4387_implies_Equation4393 (G: Type _) [Magma G] (h: Equation4387 G) : Equation4393 G := by
  have eq4595 (x y z : G) : (x ◇ x) ◇ x = (y ◇ z) ◇ z := by
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4667 at h
    apply Apply.Equation4667_implies_Equation4665 at h
    apply RewriteCombinations.Equation4665_implies_Equation4668 at h
    apply RewriteCombinations.Equation4668_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4628 at h
    apply Apply.Equation4628_implies_Equation4627 at h
    apply Apply.Equation4627_implies_Equation4595 at h
    apply h
  have eq4589 (x y z : G) : (x ◇ x) ◇ x = (y ◇ x) ◇ z := by
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4667 at h
    apply Apply.Equation4667_implies_Equation4665 at h
    apply RewriteCombinations.Equation4665_implies_Equation4668 at h
    apply RewriteCombinations.Equation4668_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4628 at h
    apply Apply.Equation4628_implies_Equation4596 at h
    apply Apply.Equation4596_implies_Equation4589 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [← eq4595]
  symm
  symm
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
    apply Apply.Equation4690_implies_Equation4667 at h
    apply Apply.Equation4667_implies_Equation4665 at h
    apply RewriteCombinations.Equation4665_implies_Equation4668 at h
    apply RewriteCombinations.Equation4668_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4628 at h
    apply Apply.Equation4628_implies_Equation4596 at h
    apply Apply.Equation4596_implies_Equation4589 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [← eq4596]
  symm
  symm
  nth_rewrite 1 [eq4589]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation4418_implies_Equation4414 (G: Type _) [Magma G] (h: Equation4418 G) : Equation4414 G := by
  have eq4396 (x y : G) : x ◇ (x ◇ y) = (x ◇ x) ◇ y := by
    apply Apply.Equation4418_implies_Equation4397 at h
    apply Apply.Equation4397_implies_Equation4396 at h
    apply h
  have eq4590 (x y : G) : (x ◇ x) ◇ x = (y ◇ y) ◇ x := by
    apply Apply.Equation4418_implies_Equation4387 at h
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4667 at h
    apply Apply.Equation4667_implies_Equation4665 at h
    apply RewriteCombinations.Equation4665_implies_Equation4668 at h
    apply RewriteCombinations.Equation4668_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4628 at h
    apply Apply.Equation4628_implies_Equation4626 at h
    apply Apply.Equation4626_implies_Equation4611 at h
    apply RewriteHypothesis.Equation4611_implies_Equation4590 at h
    apply h
  have eq4677 (x y z : G) : (x ◇ y) ◇ z = (y ◇ x) ◇ z := by
    apply Apply.Equation4418_implies_Equation4387 at h
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4667 at h
    apply Apply.Equation4667_implies_Equation4665 at h
    apply RewriteCombinations.Equation4665_implies_Equation4668 at h
    apply RewriteCombinations.Equation4668_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4678 at h
    apply Apply.Equation4678_implies_Equation4677 at h
    apply h
  have eq4395 (x y : G) : x ◇ (x ◇ y) = (x ◇ x) ◇ x := by
    apply Apply.Equation4418_implies_Equation4397 at h
    apply Apply.Equation4397_implies_Equation4395 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq4396]
  nth_rewrite 1 [← eq4590]
  symm
  nth_rewrite 1 [eq4677]
  symm
  nth_rewrite 1 [← eq4395]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4455_implies_Equation4468 (G: Type _) [Magma G] (h: Equation4455 G) : Equation4468 G := by
  have eq4432 (x y : G) : x ◇ (y ◇ x) = (x ◇ x) ◇ x := by
    apply Apply.Equation4455_implies_Equation4434 at h
    apply Apply.Equation4434_implies_Equation4432 at h
    apply h
  have eq4591 (x y : G) : (x ◇ x) ◇ x = (y ◇ y) ◇ y := by
    apply Apply.Equation4455_implies_Equation4387 at h
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4667 at h
    apply Apply.Equation4667_implies_Equation4665 at h
    apply RewriteCombinations.Equation4665_implies_Equation4668 at h
    apply RewriteCombinations.Equation4668_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4628 at h
    apply Apply.Equation4628_implies_Equation4626 at h
    apply Apply.Equation4626_implies_Equation4594 at h
    apply Apply.Equation4594_implies_Equation4591 at h
    apply h
  have eq4432 (x y : G) : x ◇ (y ◇ x) = (x ◇ x) ◇ x := by
    apply Apply.Equation4455_implies_Equation4434 at h
    apply Apply.Equation4434_implies_Equation4432 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq4432]
  nth_rewrite 1 [← eq4591]
  nth_rewrite 1 [← eq4432]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4492_implies_Equation4505 (G: Type _) [Magma G] (h: Equation4492 G) : Equation4505 G := by
  have eq4469 (x y : G) : x ◇ (y ◇ y) = (x ◇ x) ◇ x := by
    apply Apply.Equation4492_implies_Equation4471 at h
    apply Apply.Equation4471_implies_Equation4469 at h
    apply h
  have eq4591 (x y : G) : (x ◇ x) ◇ x = (y ◇ y) ◇ y := by
    apply Apply.Equation4492_implies_Equation4387 at h
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4667 at h
    apply Apply.Equation4667_implies_Equation4665 at h
    apply RewriteCombinations.Equation4665_implies_Equation4668 at h
    apply RewriteCombinations.Equation4668_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4628 at h
    apply Apply.Equation4628_implies_Equation4626 at h
    apply Apply.Equation4626_implies_Equation4594 at h
    apply Apply.Equation4594_implies_Equation4591 at h
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
  repeat assumption
@[equational_result]
theorem Equation4528_implies_Equation4550 (G: Type _) [Magma G] (h: Equation4528 G) : Equation4550 G := by
  have eq4372 (x y z w : G) : x ◇ (y ◇ z) = z ◇ (w ◇ y) := by
    apply RewriteGoal.Equation4528_implies_Equation4375 at h
    apply Apply.Equation4375_implies_Equation4370 at h
    apply SimpleRewrites.Equation4370_implies_Equation4292 at h
    apply RewriteCombinations.Equation4292_implies_Equation4298 at h
    apply RewriteGoal.Equation4298_implies_Equation4313 at h
    apply Apply.Equation4313_implies_Equation4281 at h
    apply RewriteCombinations.Equation4281_implies_Equation4373 at h
    apply Apply.Equation4373_implies_Equation4372 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4372]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4528_implies_Equation4462 (G: Type _) [Magma G] (h: Equation4528 G) : Equation4462 G := by
  have eq4316 (x y z : G) : x ◇ (y ◇ x) = x ◇ (z ◇ x) := by
    apply RewriteCombinations.Equation4528_implies_Equation4506 at h
    apply Apply.Equation4506_implies_Equation4432 at h
    apply RewriteGoal.Equation4432_implies_Equation4316 at h
    apply h
  have eq4315 (x y z : G) : x ◇ (y ◇ x) = x ◇ (y ◇ z) := by
    apply RewriteCombinations.Equation4528_implies_Equation4506 at h
    apply RewriteGoal.Equation4506_implies_Equation4361 at h
    apply Apply.Equation4361_implies_Equation4357 at h
    apply Apply.Equation4357_implies_Equation4339 at h
    apply RewriteCombinations.Equation4339_implies_Equation4315 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4316]
  nth_rewrite 1 [eq4315]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4528_implies_Equation4499 (G: Type _) [Magma G] (h: Equation4528 G) : Equation4499 G := by
  have eq4318 (x y z : G) : x ◇ (y ◇ x) = x ◇ (z ◇ z) := by
    apply RewriteCombinations.Equation4528_implies_Equation4506 at h
    apply RewriteGoal.Equation4506_implies_Equation4361 at h
    apply Apply.Equation4361_implies_Equation4289 at h
    apply RewriteCombinations.Equation4289_implies_Equation4318 at h
    apply h
  have eq4315 (x y z : G) : x ◇ (y ◇ x) = x ◇ (y ◇ z) := by
    apply RewriteCombinations.Equation4528_implies_Equation4506 at h
    apply RewriteGoal.Equation4506_implies_Equation4361 at h
    apply Apply.Equation4361_implies_Equation4357 at h
    apply Apply.Equation4357_implies_Equation4339 at h
    apply RewriteCombinations.Equation4339_implies_Equation4315 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4318]
  nth_rewrite 1 [eq4315]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4528_implies_Equation4425 (G: Type _) [Magma G] (h: Equation4528 G) : Equation4425 G := by
  have eq4277 (x y z : G) : x ◇ (x ◇ x) = y ◇ (y ◇ z) := by
    apply RewriteGoal.Equation4528_implies_Equation4375 at h
    apply Apply.Equation4375_implies_Equation4370 at h
    apply SimpleRewrites.Equation4370_implies_Equation4292 at h
    apply RewriteCombinations.Equation4292_implies_Equation4298 at h
    apply RewriteGoal.Equation4298_implies_Equation4313 at h
    apply Apply.Equation4313_implies_Equation4281 at h
    apply RewriteCombinations.Equation4281_implies_Equation4312 at h
    apply RewriteHypothesis.Equation4312_implies_Equation4277 at h
    apply h
  have eq4271 (x y z : G) : x ◇ (x ◇ x) = x ◇ (y ◇ z) := by
    apply RewriteCombinations.Equation4528_implies_Equation4506 at h
    apply RewriteGoal.Equation4506_implies_Equation4361 at h
    apply Apply.Equation4361_implies_Equation4289 at h
    apply SimpleRewrites.Equation4289_implies_Equation4271 at h
    apply h
  have eq4363 (x y z w : G) : x ◇ (y ◇ z) = y ◇ (x ◇ w) := by
    apply RewriteGoal.Equation4528_implies_Equation4375 at h
    apply Apply.Equation4375_implies_Equation4370 at h
    apply SimpleRewrites.Equation4370_implies_Equation4292 at h
    apply RewriteCombinations.Equation4292_implies_Equation4298 at h
    apply RewriteGoal.Equation4298_implies_Equation4313 at h
    apply Apply.Equation4313_implies_Equation4281 at h
    apply RewriteCombinations.Equation4281_implies_Equation4363 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4277]
  nth_rewrite 1 [eq4271]
  nth_rewrite 1 [← eq4363]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4536_implies_Equation4580 (G: Type _) [Magma G] (h: Equation4536 G) : Equation4580 G := by
  have eq4359 (x y z w : G) : x ◇ (y ◇ z) = x ◇ (z ◇ w) := by
    apply Apply.Equation4536_implies_Equation4528 at h
    apply RewriteCombinations.Equation4528_implies_Equation4506 at h
    apply RewriteGoal.Equation4506_implies_Equation4361 at h
    apply Apply.Equation4361_implies_Equation4359 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4359]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4536_implies_Equation4518 (G: Type _) [Magma G] (h: Equation4536 G) : Equation4518 G := by
  have eq4363 (x y z w : G) : x ◇ (y ◇ z) = y ◇ (x ◇ w) := by
    apply Apply.Equation4536_implies_Equation4528 at h
    apply RewriteGoal.Equation4528_implies_Equation4375 at h
    apply Apply.Equation4375_implies_Equation4370 at h
    apply SimpleRewrites.Equation4370_implies_Equation4292 at h
    apply RewriteCombinations.Equation4292_implies_Equation4298 at h
    apply RewriteGoal.Equation4298_implies_Equation4313 at h
    apply Apply.Equation4313_implies_Equation4281 at h
    apply RewriteCombinations.Equation4281_implies_Equation4363 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4363]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4536_implies_Equation4554 (G: Type _) [Magma G] (h: Equation4536 G) : Equation4554 G := by
  have eq4372 (x y z w : G) : x ◇ (y ◇ z) = z ◇ (w ◇ y) := by
    apply Apply.Equation4536_implies_Equation4528 at h
    apply RewriteGoal.Equation4528_implies_Equation4375 at h
    apply Apply.Equation4375_implies_Equation4370 at h
    apply SimpleRewrites.Equation4370_implies_Equation4292 at h
    apply RewriteCombinations.Equation4292_implies_Equation4298 at h
    apply RewriteGoal.Equation4298_implies_Equation4313 at h
    apply Apply.Equation4313_implies_Equation4281 at h
    apply RewriteCombinations.Equation4281_implies_Equation4373 at h
    apply Apply.Equation4373_implies_Equation4372 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4372]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4536_implies_Equation4466 (G: Type _) [Magma G] (h: Equation4536 G) : Equation4466 G := by
  have eq4316 (x y z : G) : x ◇ (y ◇ x) = x ◇ (z ◇ x) := by
    apply Apply.Equation4536_implies_Equation4528 at h
    apply RewriteCombinations.Equation4528_implies_Equation4506 at h
    apply Apply.Equation4506_implies_Equation4432 at h
    apply RewriteGoal.Equation4432_implies_Equation4316 at h
    apply h
  have eq4315 (x y z : G) : x ◇ (y ◇ x) = x ◇ (y ◇ z) := by
    apply Apply.Equation4536_implies_Equation4524 at h
    apply RewriteGoal.Equation4524_implies_Equation4357 at h
    apply Apply.Equation4357_implies_Equation4339 at h
    apply RewriteCombinations.Equation4339_implies_Equation4315 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4316]
  nth_rewrite 1 [eq4315]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4536_implies_Equation4503 (G: Type _) [Magma G] (h: Equation4536 G) : Equation4503 G := by
  have eq4318 (x y z : G) : x ◇ (y ◇ x) = x ◇ (z ◇ z) := by
    apply Apply.Equation4536_implies_Equation4528 at h
    apply RewriteCombinations.Equation4528_implies_Equation4506 at h
    apply RewriteGoal.Equation4506_implies_Equation4361 at h
    apply Apply.Equation4361_implies_Equation4289 at h
    apply RewriteCombinations.Equation4289_implies_Equation4318 at h
    apply h
  have eq4315 (x y z : G) : x ◇ (y ◇ x) = x ◇ (y ◇ z) := by
    apply Apply.Equation4536_implies_Equation4524 at h
    apply RewriteGoal.Equation4524_implies_Equation4357 at h
    apply Apply.Equation4357_implies_Equation4339 at h
    apply RewriteCombinations.Equation4339_implies_Equation4315 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4318]
  nth_rewrite 1 [eq4315]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4536_implies_Equation4429 (G: Type _) [Magma G] (h: Equation4536 G) : Equation4429 G := by
  have eq4277 (x y z : G) : x ◇ (x ◇ x) = y ◇ (y ◇ z) := by
    apply Apply.Equation4536_implies_Equation4528 at h
    apply RewriteGoal.Equation4528_implies_Equation4375 at h
    apply Apply.Equation4375_implies_Equation4370 at h
    apply SimpleRewrites.Equation4370_implies_Equation4292 at h
    apply RewriteCombinations.Equation4292_implies_Equation4298 at h
    apply RewriteGoal.Equation4298_implies_Equation4313 at h
    apply Apply.Equation4313_implies_Equation4281 at h
    apply RewriteCombinations.Equation4281_implies_Equation4312 at h
    apply RewriteHypothesis.Equation4312_implies_Equation4277 at h
    apply h
  have eq4382 (x y : G) : x ◇ (x ◇ x) = (x ◇ y) ◇ x := by
    apply Apply.Equation4536_implies_Equation4401 at h
    apply Apply.Equation4401_implies_Equation4382 at h
    apply h
  have eq4524 (x y z : G) : x ◇ (y ◇ z) = (y ◇ x) ◇ y := by
    apply Apply.Equation4536_implies_Equation4524 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4277]
  nth_rewrite 1 [eq4382]
  nth_rewrite 1 [← eq4524]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4536_implies_Equation4575 (G: Type _) [Magma G] (h: Equation4536 G) : Equation4575 G := by
  have eq4281 (x y z w : G) : x ◇ (x ◇ x) = y ◇ (z ◇ w) := by
    apply Apply.Equation4536_implies_Equation4528 at h
    apply RewriteGoal.Equation4528_implies_Equation4375 at h
    apply Apply.Equation4375_implies_Equation4370 at h
    apply SimpleRewrites.Equation4370_implies_Equation4292 at h
    apply RewriteCombinations.Equation4292_implies_Equation4298 at h
    apply RewriteGoal.Equation4298_implies_Equation4313 at h
    apply Apply.Equation4313_implies_Equation4281 at h
    apply h
  have eq4584 (x y : G) : (x ◇ x) ◇ x = (x ◇ y) ◇ x := by
    apply Apply.Equation4536_implies_Equation4401 at h
    apply Apply.Equation4401_implies_Equation4382 at h
    apply RewriteHypothesis.Equation4382_implies_Equation4631 at h
    apply Apply.Equation4631_implies_Equation4584 at h
    apply h
  have eq4382 (x y : G) : x ◇ (x ◇ x) = (x ◇ y) ◇ x := by
    apply Apply.Equation4536_implies_Equation4401 at h
    apply Apply.Equation4401_implies_Equation4382 at h
    apply h
  have eq4524 (x y z : G) : x ◇ (y ◇ z) = (y ◇ x) ◇ y := by
    apply Apply.Equation4536_implies_Equation4524 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4281]
  symm
  nth_rewrite 1 [eq4584]
  symm
  nth_rewrite 1 [eq4382]
  nth_rewrite 1 [← eq4524]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4561_implies_Equation4566 (G: Type _) [Magma G] (h: Equation4561 G) : Equation4566 G := by
  have eq4507 (x y z : G) : x ◇ (y ◇ z) = (x ◇ x) ◇ y := by
    apply Apply.Equation4561_implies_Equation4509 at h
    apply Apply.Equation4509_implies_Equation4507 at h
    apply h
  have eq4590 (x y : G) : (x ◇ x) ◇ x = (y ◇ y) ◇ x := by
    apply Apply.Equation4561_implies_Equation4418 at h
    apply Apply.Equation4418_implies_Equation4387 at h
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4667 at h
    apply Apply.Equation4667_implies_Equation4665 at h
    apply RewriteCombinations.Equation4665_implies_Equation4668 at h
    apply RewriteCombinations.Equation4668_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4628 at h
    apply Apply.Equation4628_implies_Equation4626 at h
    apply Apply.Equation4626_implies_Equation4611 at h
    apply RewriteHypothesis.Equation4611_implies_Equation4590 at h
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
theorem Equation4561_implies_Equation4431 (G: Type _) [Magma G] (h: Equation4561 G) : Equation4431 G := by
  have eq4395 (x y : G) : x ◇ (x ◇ y) = (x ◇ x) ◇ x := by
    apply Apply.Equation4561_implies_Equation4418 at h
    apply Apply.Equation4418_implies_Equation4397 at h
    apply Apply.Equation4397_implies_Equation4395 at h
    apply h
  have eq4591 (x y : G) : (x ◇ x) ◇ x = (y ◇ y) ◇ y := by
    apply Apply.Equation4561_implies_Equation4418 at h
    apply Apply.Equation4418_implies_Equation4387 at h
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4667 at h
    apply Apply.Equation4667_implies_Equation4665 at h
    apply RewriteCombinations.Equation4665_implies_Equation4668 at h
    apply RewriteCombinations.Equation4668_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4628 at h
    apply Apply.Equation4628_implies_Equation4626 at h
    apply Apply.Equation4626_implies_Equation4594 at h
    apply Apply.Equation4594_implies_Equation4591 at h
    apply h
  have eq4506 (x y z : G) : x ◇ (y ◇ z) = (x ◇ x) ◇ x := by
    apply Apply.Equation4561_implies_Equation4509 at h
    apply Apply.Equation4509_implies_Equation4506 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq4395]
  nth_rewrite 1 [← eq4591]
  nth_rewrite 1 [← eq4506]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4561_implies_Equation4522 (G: Type _) [Magma G] (h: Equation4561 G) : Equation4522 G := by
  have eq4506 (x y z : G) : x ◇ (y ◇ z) = (x ◇ x) ◇ x := by
    apply Apply.Equation4561_implies_Equation4509 at h
    apply Apply.Equation4509_implies_Equation4506 at h
    apply h
  have eq4677 (x y z : G) : (x ◇ y) ◇ z = (y ◇ x) ◇ z := by
    apply Apply.Equation4561_implies_Equation4418 at h
    apply Apply.Equation4418_implies_Equation4387 at h
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4667 at h
    apply Apply.Equation4667_implies_Equation4665 at h
    apply RewriteCombinations.Equation4665_implies_Equation4668 at h
    apply RewriteCombinations.Equation4668_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4678 at h
    apply Apply.Equation4678_implies_Equation4677 at h
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
theorem Equation4561_implies_Equation4577 (G: Type _) [Magma G] (h: Equation4561 G) : Equation4577 G := by
  have eq4593 (x y z : G) : (x ◇ x) ◇ x = (y ◇ z) ◇ x := by
    apply Apply.Equation4561_implies_Equation4418 at h
    apply Apply.Equation4418_implies_Equation4387 at h
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4667 at h
    apply Apply.Equation4667_implies_Equation4665 at h
    apply RewriteCombinations.Equation4665_implies_Equation4668 at h
    apply RewriteCombinations.Equation4668_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4693 at h
    apply Apply.Equation4693_implies_Equation4625 at h
    apply Apply.Equation4625_implies_Equation4593 at h
    apply h
  have eq4271 (x y z : G) : x ◇ (x ◇ x) = x ◇ (y ◇ z) := by
    apply Apply.Equation4561_implies_Equation4509 at h
    apply Apply.Equation4509_implies_Equation4506 at h
    apply RewriteGoal.Equation4506_implies_Equation4361 at h
    apply Apply.Equation4361_implies_Equation4289 at h
    apply SimpleRewrites.Equation4289_implies_Equation4271 at h
    apply h
  have eq4589 (x y z : G) : (x ◇ x) ◇ x = (y ◇ x) ◇ z := by
    apply Apply.Equation4561_implies_Equation4418 at h
    apply Apply.Equation4418_implies_Equation4387 at h
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4667 at h
    apply Apply.Equation4667_implies_Equation4665 at h
    apply RewriteCombinations.Equation4665_implies_Equation4668 at h
    apply RewriteCombinations.Equation4668_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4628 at h
    apply Apply.Equation4628_implies_Equation4596 at h
    apply Apply.Equation4596_implies_Equation4589 at h
    apply h
  have eq4271 (x y z : G) : x ◇ (x ◇ x) = x ◇ (y ◇ z) := by
    apply Apply.Equation4561_implies_Equation4509 at h
    apply Apply.Equation4509_implies_Equation4506 at h
    apply RewriteGoal.Equation4506_implies_Equation4361 at h
    apply Apply.Equation4361_implies_Equation4289 at h
    apply SimpleRewrites.Equation4289_implies_Equation4271 at h
    apply h
  repeat intro
  symm
  nth_rewrite 1 [← eq4593]
  symm
  nth_rewrite 1 [← eq4271]
  symm
  nth_rewrite 1 [eq4589]
  symm
  nth_rewrite 1 [eq4271]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4561_implies_Equation4539 (G: Type _) [Magma G] (h: Equation4561 G) : Equation4539 G := by
  have eq4507 (x y z : G) : x ◇ (y ◇ z) = (x ◇ x) ◇ y := by
    apply Apply.Equation4561_implies_Equation4509 at h
    apply Apply.Equation4509_implies_Equation4507 at h
    apply h
  have eq4590 (x y : G) : (x ◇ x) ◇ x = (y ◇ y) ◇ x := by
    apply Apply.Equation4561_implies_Equation4418 at h
    apply Apply.Equation4418_implies_Equation4387 at h
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4667 at h
    apply Apply.Equation4667_implies_Equation4665 at h
    apply RewriteCombinations.Equation4665_implies_Equation4668 at h
    apply RewriteCombinations.Equation4668_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4628 at h
    apply Apply.Equation4628_implies_Equation4626 at h
    apply Apply.Equation4626_implies_Equation4611 at h
    apply RewriteHypothesis.Equation4611_implies_Equation4590 at h
    apply h
  have eq4677 (x y z : G) : (x ◇ y) ◇ z = (y ◇ x) ◇ z := by
    apply Apply.Equation4561_implies_Equation4418 at h
    apply Apply.Equation4418_implies_Equation4387 at h
    apply RewriteHypothesis.Equation4387_implies_Equation4690 at h
    apply Apply.Equation4690_implies_Equation4667 at h
    apply Apply.Equation4667_implies_Equation4665 at h
    apply RewriteCombinations.Equation4665_implies_Equation4668 at h
    apply RewriteCombinations.Equation4668_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4678 at h
    apply Apply.Equation4678_implies_Equation4677 at h
    apply h
  have eq4506 (x y z : G) : x ◇ (y ◇ z) = (x ◇ x) ◇ x := by
    apply Apply.Equation4561_implies_Equation4509 at h
    apply Apply.Equation4509_implies_Equation4506 at h
    apply h
  repeat intro
  nth_rewrite 1 [eq4507]
  nth_rewrite 1 [← eq4590]
  symm
  nth_rewrite 1 [eq4677]
  symm
  nth_rewrite 1 [← eq4506]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4563_implies_Equation4581 (G: Type _) [Magma G] (h: Equation4563 G) : Equation4581 G := by
  have eq4359 (x y z w : G) : x ◇ (y ◇ z) = x ◇ (z ◇ w) := by
    apply Apply.Equation4563_implies_Equation4528 at h
    apply RewriteCombinations.Equation4528_implies_Equation4506 at h
    apply RewriteGoal.Equation4506_implies_Equation4361 at h
    apply Apply.Equation4361_implies_Equation4359 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4359]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4563_implies_Equation4557 (G: Type _) [Magma G] (h: Equation4563 G) : Equation4557 G := by
  have eq4363 (x y z w : G) : x ◇ (y ◇ z) = y ◇ (x ◇ w) := by
    apply Apply.Equation4563_implies_Equation4528 at h
    apply RewriteGoal.Equation4528_implies_Equation4375 at h
    apply Apply.Equation4375_implies_Equation4370 at h
    apply SimpleRewrites.Equation4370_implies_Equation4292 at h
    apply RewriteCombinations.Equation4292_implies_Equation4298 at h
    apply RewriteGoal.Equation4298_implies_Equation4313 at h
    apply Apply.Equation4313_implies_Equation4281 at h
    apply RewriteCombinations.Equation4281_implies_Equation4363 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4363]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4563_implies_Equation4569 (G: Type _) [Magma G] (h: Equation4563 G) : Equation4569 G := by
  have eq4372 (x y z w : G) : x ◇ (y ◇ z) = z ◇ (w ◇ y) := by
    apply Apply.Equation4563_implies_Equation4528 at h
    apply RewriteGoal.Equation4528_implies_Equation4375 at h
    apply Apply.Equation4375_implies_Equation4370 at h
    apply SimpleRewrites.Equation4370_implies_Equation4292 at h
    apply RewriteCombinations.Equation4292_implies_Equation4298 at h
    apply RewriteGoal.Equation4298_implies_Equation4313 at h
    apply Apply.Equation4313_implies_Equation4281 at h
    apply RewriteCombinations.Equation4281_implies_Equation4373 at h
    apply Apply.Equation4373_implies_Equation4372 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4372]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4563_implies_Equation4467 (G: Type _) [Magma G] (h: Equation4563 G) : Equation4467 G := by
  have eq4316 (x y z : G) : x ◇ (y ◇ x) = x ◇ (z ◇ x) := by
    apply Apply.Equation4563_implies_Equation4528 at h
    apply RewriteCombinations.Equation4528_implies_Equation4506 at h
    apply Apply.Equation4506_implies_Equation4432 at h
    apply RewriteGoal.Equation4432_implies_Equation4316 at h
    apply h
  have eq4315 (x y z : G) : x ◇ (y ◇ x) = x ◇ (y ◇ z) := by
    apply Apply.Equation4563_implies_Equation4511 at h
    apply RewriteGoal.Equation4511_implies_Equation4357 at h
    apply Apply.Equation4357_implies_Equation4339 at h
    apply RewriteCombinations.Equation4339_implies_Equation4315 at h
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
    apply Apply.Equation4357_implies_Equation4339 at h
    apply RewriteCombinations.Equation4339_implies_Equation4315 at h
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
    apply RewriteGoal.Equation4528_implies_Equation4375 at h
    apply Apply.Equation4375_implies_Equation4370 at h
    apply SimpleRewrites.Equation4370_implies_Equation4292 at h
    apply RewriteCombinations.Equation4292_implies_Equation4298 at h
    apply RewriteGoal.Equation4298_implies_Equation4313 at h
    apply Apply.Equation4313_implies_Equation4281 at h
    apply RewriteCombinations.Equation4281_implies_Equation4312 at h
    apply RewriteHypothesis.Equation4312_implies_Equation4277 at h
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
    apply RewriteGoal.Equation4528_implies_Equation4375 at h
    apply Apply.Equation4375_implies_Equation4370 at h
    apply SimpleRewrites.Equation4370_implies_Equation4292 at h
    apply RewriteCombinations.Equation4292_implies_Equation4298 at h
    apply RewriteGoal.Equation4298_implies_Equation4313 at h
    apply Apply.Equation4313_implies_Equation4281 at h
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
theorem Equation4573_implies_Equation4576 (G: Type _) [Magma G] (h: Equation4573 G) : Equation4576 G := by
  have eq4359 (x y z w : G) : x ◇ (y ◇ z) = x ◇ (z ◇ w) := by
    apply Apply.Equation4573_implies_Equation4528 at h
    apply RewriteCombinations.Equation4528_implies_Equation4506 at h
    apply RewriteGoal.Equation4506_implies_Equation4361 at h
    apply Apply.Equation4361_implies_Equation4359 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4359]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4578_implies_Equation4468 (G: Type _) [Magma G] (h: Equation4578 G) : Equation4468 G := by
  have eq4316 (x y z : G) : x ◇ (y ◇ x) = x ◇ (z ◇ x) := by
    apply Apply.Equation4578_implies_Equation4536 at h
    apply Apply.Equation4536_implies_Equation4528 at h
    apply RewriteCombinations.Equation4528_implies_Equation4506 at h
    apply Apply.Equation4506_implies_Equation4432 at h
    apply RewriteGoal.Equation4432_implies_Equation4316 at h
    apply h
  have eq4315 (x y z : G) : x ◇ (y ◇ x) = x ◇ (y ◇ z) := by
    apply Apply.Equation4578_implies_Equation4519 at h
    apply Apply.Equation4519_implies_Equation4507 at h
    apply RewriteGoal.Equation4507_implies_Equation4357 at h
    apply Apply.Equation4357_implies_Equation4339 at h
    apply RewriteCombinations.Equation4339_implies_Equation4315 at h
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
    apply Apply.Equation4536_implies_Equation4528 at h
    apply RewriteCombinations.Equation4528_implies_Equation4506 at h
    apply RewriteGoal.Equation4506_implies_Equation4361 at h
    apply Apply.Equation4361_implies_Equation4289 at h
    apply RewriteCombinations.Equation4289_implies_Equation4317 at h
    apply h
  have eq4315 (x y z : G) : x ◇ (y ◇ x) = x ◇ (y ◇ z) := by
    apply Apply.Equation4578_implies_Equation4519 at h
    apply Apply.Equation4519_implies_Equation4507 at h
    apply RewriteGoal.Equation4507_implies_Equation4357 at h
    apply Apply.Equation4357_implies_Equation4339 at h
    apply RewriteCombinations.Equation4339_implies_Equation4315 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4317]
  nth_rewrite 1 [eq4315]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4578_implies_Equation4505 (G: Type _) [Magma G] (h: Equation4578 G) : Equation4505 G := by
  have eq4318 (x y z : G) : x ◇ (y ◇ x) = x ◇ (z ◇ z) := by
    apply Apply.Equation4578_implies_Equation4536 at h
    apply Apply.Equation4536_implies_Equation4528 at h
    apply RewriteCombinations.Equation4528_implies_Equation4506 at h
    apply RewriteGoal.Equation4506_implies_Equation4361 at h
    apply Apply.Equation4361_implies_Equation4289 at h
    apply RewriteCombinations.Equation4289_implies_Equation4318 at h
    apply h
  have eq4315 (x y z : G) : x ◇ (y ◇ x) = x ◇ (y ◇ z) := by
    apply Apply.Equation4578_implies_Equation4519 at h
    apply Apply.Equation4519_implies_Equation4507 at h
    apply RewriteGoal.Equation4507_implies_Equation4357 at h
    apply Apply.Equation4357_implies_Equation4339 at h
    apply RewriteCombinations.Equation4339_implies_Equation4315 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4318]
  nth_rewrite 1 [eq4315]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4578_implies_Equation4581 (G: Type _) [Magma G] (h: Equation4578 G) : Equation4581 G := by
  have eq4319 (x y z w : G) : x ◇ (y ◇ x) = x ◇ (z ◇ w) := by
    apply Apply.Equation4578_implies_Equation4536 at h
    apply Apply.Equation4536_implies_Equation4528 at h
    apply RewriteCombinations.Equation4528_implies_Equation4506 at h
    apply RewriteGoal.Equation4506_implies_Equation4361 at h
    apply Apply.Equation4361_implies_Equation4319 at h
    apply h
  have eq4669 (x y z w : G) : (x ◇ y) ◇ y = (z ◇ w) ◇ y := by
    apply Apply.Equation4578_implies_Equation4427 at h
    apply Apply.Equation4427_implies_Equation4391 at h
    apply RewriteHypothesis.Equation4391_implies_Equation4693 at h
    apply Apply.Equation4693_implies_Equation4669 at h
    apply h
  have eq4315 (x y z : G) : x ◇ (y ◇ x) = x ◇ (y ◇ z) := by
    apply Apply.Equation4578_implies_Equation4519 at h
    apply Apply.Equation4519_implies_Equation4507 at h
    apply RewriteGoal.Equation4507_implies_Equation4357 at h
    apply Apply.Equation4357_implies_Equation4339 at h
    apply RewriteCombinations.Equation4339_implies_Equation4315 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4319]
  symm
  nth_rewrite 1 [eq4669]
  symm
  nth_rewrite 1 [eq4315]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4616_implies_Equation4626 (G: Type _) [Magma G] (h: Equation4616 G) : Equation4626 G := by
  have eq4609 (x y z : G) : (x ◇ x) ◇ y = (y ◇ y) ◇ z := by
    apply NthRewrites.Equation4616_implies_Equation4623 at h
    apply Apply.Equation4623_implies_Equation4592 at h
    apply RewriteCombinations.Equation4592_implies_Equation4609 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4609]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4646_implies_Equation4652 (G: Type _) [Magma G] (h: Equation4646 G) : Equation4652 G := by
  have eq4588 (x y : G) : (x ◇ x) ◇ x = (y ◇ x) ◇ y := by
    apply RewriteCombinations.Equation4646_implies_Equation4647 at h
    apply Apply.Equation4647_implies_Equation4588 at h
    apply h
  have eq4585 (x y : G) : (x ◇ x) ◇ x = (x ◇ y) ◇ y := by
    apply NthRewrites.Equation4646_implies_Equation4670 at h
    apply Apply.Equation4670_implies_Equation4595 at h
    apply RewriteCombinations.Equation4595_implies_Equation4656 at h
    apply Apply.Equation4656_implies_Equation4585 at h
    apply h
  have eq4629 (x y : G) : (x ◇ y) ◇ x = (x ◇ y) ◇ y := by
    apply Apply.Equation4646_implies_Equation4629 at h
    apply h
  repeat intro
  nth_rewrite 1 [← eq4588]
  nth_rewrite 1 [eq4585]
  nth_rewrite 1 [← eq4629]
  apply h
  repeat assumption
