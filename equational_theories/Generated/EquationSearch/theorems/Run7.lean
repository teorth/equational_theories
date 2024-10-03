import equational_theories.Generated.SimpleRewrites
import equational_theories.Generated.Constant
import equational_theories.Generated.Singleton
import equational_theories.Generated.TrivialBruteforce
import equational_theories.Generated.FinitePoly
import equational_theories.Generated.EquationSearch.theorems.Run1
import equational_theories.Generated.EquationSearch.theorems.Run2
import equational_theories.Generated.EquationSearch.theorems.Run3
import equational_theories.Generated.EquationSearch.theorems.Run4
import equational_theories.Generated.EquationSearch.theorems.Run5
import equational_theories.Generated.EquationSearch.theorems.Run6
import Mathlib.Tactic

namespace Run7
@[equational_result]
theorem Equation28_implies_Equation832 (G: Type _) [Magma G] (h: Equation28 G) : Equation832 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Run1.Equation28_implies_Equation3 at h
    apply h
  have eq3461 (x y : G) : x ∘ x = x ∘ ((y ∘ x) ∘ x) := by
    apply RewriteHypothesis.Equation28_implies_Equation3533 at h
    apply Apply.Equation3533_implies_Equation3461 at h
    apply h
  have eq364 (x y : G) : x ∘ x = (y ∘ x) ∘ x := by
    apply Run1.Equation28_implies_Equation364 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq3]
  nth_rewrite 1 [← eq3461]
  nth_rewrite 1 [eq364]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation69 (G: Type _) [Magma G] (h: Equation1514 G) : Equation69 G := by
  have eq3275 (x y z : G) : x ∘ x = y ∘ (x ∘ (z ∘ y)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply Apply.Equation314_implies_Equation3277 at h
    apply Apply.Equation3277_implies_Equation3275 at h
    apply h
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq3275]
  symm
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq3]
  apply h
  repeat assumption
@[equational_result]
theorem Equation979_implies_Equation11 (G: Type _) [Magma G] (h: Equation979 G) : Equation11 G := by
  have eq4270 (x y : G) : x ∘ (x ∘ x) = x ∘ (y ∘ y) := by
    apply RewriteHypothesisAndGoal.Equation979_implies_Equation40 at h
    apply RewriteHypothesis.Equation40_implies_Equation4341 at h
    apply Apply.Equation4341_implies_Equation4270 at h
    apply h
  have eq8 (x : G) : x = x ∘ (x ∘ x) := by
    apply Run6.Equation979_implies_Equation8 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq4270]
  symm
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation270_implies_Equation2087 (G: Type _) [Magma G] (h: Equation270 G) : Equation2087 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Run3.Equation270_implies_Equation3 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq3]
  symm
  apply h
@[equational_result]
theorem Equation276_implies_Equation101 (G: Type _) [Magma G] (h: Equation276 G) : Equation101 G := by
  have eq3458 (x y : G) : x ∘ x = x ∘ ((x ∘ y) ∘ x) := by
    apply Run6.Equation276_implies_Equation25 at h
    apply RewriteHypothesis.Equation25_implies_Equation3525 at h
    apply Apply.Equation3525_implies_Equation3458 at h
    apply h
  have eq4086 (x y z : G) : x ∘ x = ((y ∘ x) ∘ z) ∘ x := by
    apply Run4.Equation276_implies_Equation4086 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq3458]
  nth_rewrite 1 [eq4086]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation276_implies_Equation260 (G: Type _) [Magma G] (h: Equation276 G) : Equation260 G := by
  have eq4070 (x y : G) : x ∘ x = ((x ∘ y) ∘ x) ∘ x := by
    apply Run6.Equation276_implies_Equation361 at h
    apply RewriteHypothesis.Equation361_implies_Equation4070 at h
    apply h
  have eq4086 (x y z : G) : x ∘ x = ((y ∘ x) ∘ z) ∘ x := by
    apply Run4.Equation276_implies_Equation4086 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq4070]
  nth_rewrite 1 [eq4086]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation276_implies_Equation3664 (G: Type _) [Magma G] (h: Equation276 G) : Equation3664 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation276_implies_Equation270 at h
    apply Run3.Equation270_implies_Equation3 at h
    apply h
  have eq1644 (x y : G) : x = (x ∘ y) ∘ ((x ∘ x) ∘ x) := by
    apply Run6.Equation276_implies_Equation25 at h
    apply RewriteHypothesis.Equation25_implies_Equation1650 at h
    apply Apply.Equation1650_implies_Equation1644 at h
    apply h
  have eq4086 (x y z : G) : x ∘ x = ((y ∘ x) ∘ z) ∘ x := by
    apply Run4.Equation276_implies_Equation4086 at h
    apply h
  intro x y
  symm
  nth_rewrite 2 [eq3 x]
  nth_rewrite 1 [← eq1644]
  symm
  nth_rewrite 1 [eq4086]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation276_implies_Equation2662 (G: Type _) [Magma G] (h: Equation276 G) : Equation2662 G := by
  have eq3722 (x y : G) : x ∘ y = (x ∘ y) ∘ (x ∘ y) := by
    apply Apply.Equation276_implies_Equation270 at h
    apply Run3.Equation270_implies_Equation3 at h
    apply Apply.Equation3_implies_Equation3722 at h
    apply h
  have eq361 (x y : G) : x ∘ x = (x ∘ y) ∘ x := by
    apply Run6.Equation276_implies_Equation361 at h
    apply h
  have eq4086 (x y z : G) : x ∘ x = ((y ∘ x) ∘ z) ∘ x := by
    apply Run4.Equation276_implies_Equation4086 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq3722]
  nth_rewrite 1 [← eq361]
  nth_rewrite 1 [eq4086]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation48_implies_Equation818 (G: Type _) [Magma G] (h: Equation48 G) : Equation818 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Run3.Equation48_implies_Equation3 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq3]
  symm
  apply h
@[equational_result]
theorem Equation54_implies_Equation4 (G: Type _) [Magma G] (h: Equation54 G) : Equation4 G := by
  have eq3316 (x y : G) : x ∘ y = x ∘ (y ∘ (x ∘ y)) := by
    apply Run5.Equation54_implies_Equation10 at h
    apply RewriteHypothesis.Equation10_implies_Equation3322 at h
    apply Apply.Equation3322_implies_Equation3316 at h
    apply h
  have eq3259 (x y : G) : x ∘ x = x ∘ (y ∘ (x ∘ y)) := by
    apply Run3.Equation54_implies_Equation3260 at h
    apply Apply.Equation3260_implies_Equation3259 at h
    apply h
  have eq3260 (x y z : G) : x ∘ x = x ∘ (y ∘ (x ∘ z)) := by
    apply Run3.Equation54_implies_Equation3260 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [eq3316]
  nth_rewrite 1 [← eq3259]
  nth_rewrite 1 [eq3260]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1700_implies_Equation1426 (G: Type _) [Magma G] (h: Equation1700 G) : Equation1426 G := by
  have eq4380 (x : G) : x ∘ (x ∘ x) = (x ∘ x) ∘ x := by
    apply RewriteHypothesisAndGoal.Equation1700_implies_Equation4431 at h
    apply Apply.Equation4431_implies_Equation4394 at h
    apply Apply.Equation4394_implies_Equation4384 at h
    apply Apply.Equation4384_implies_Equation4381 at h
    apply Apply.Equation4381_implies_Equation4380 at h
    apply h
  have eq1629 (x : G) : x = (x ∘ x) ∘ ((x ∘ x) ∘ x) := by
    apply Apply.Equation1700_implies_Equation1633 at h
    apply Apply.Equation1633_implies_Equation1630 at h
    apply Apply.Equation1630_implies_Equation1629 at h
    apply h
  intro x
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [eq4380]
  nth_rewrite 1 [← eq1629]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1201_implies_Equation1223 (G: Type _) [Magma G] (h: Equation1201 G) : Equation1223 G := by
  have eq4380 (x : G) : x ∘ (x ∘ x) = (x ∘ x) ∘ x := by
    apply RewriteHypothesisAndGoal.Equation1201_implies_Equation4431 at h
    apply Apply.Equation4431_implies_Equation4394 at h
    apply Apply.Equation4394_implies_Equation4384 at h
    apply Apply.Equation4384_implies_Equation4381 at h
    apply Apply.Equation4381_implies_Equation4380 at h
    apply h
  have eq1020 (x : G) : x = x ∘ ((x ∘ (x ∘ x)) ∘ x) := by
    apply Apply.Equation1201_implies_Equation1058 at h
    apply Apply.Equation1058_implies_Equation1027 at h
    apply Apply.Equation1027_implies_Equation1021 at h
    apply Apply.Equation1021_implies_Equation1020 at h
    apply h
  intro x
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq4380]
  nth_rewrite 1 [← eq1020]
  apply h
  repeat assumption
@[equational_result]
theorem Equation2726_implies_Equation2839 (G: Type _) [Magma G] (h: Equation2726 G) : Equation2839 G := by
  have eq2653 (x y : G) : x = ((x ∘ x) ∘ (y ∘ y)) ∘ y := by
    apply Apply.Equation2726_implies_Equation2653 at h
    apply h
  have eq3715 (x y : G) : x ∘ y = (x ∘ x) ∘ (y ∘ y) := by
    apply RewriteHypothesisAndGoal.Equation2726_implies_Equation3762 at h
    apply RewriteCombinations.Equation3762_implies_Equation347 at h
    apply Apply.Equation347_implies_Equation3842 at h
    apply Apply.Equation3842_implies_Equation3736 at h
    apply Apply.Equation3736_implies_Equation3715 at h
    apply h
  have eq4587 (x y : G) : (x ∘ x) ∘ x = (y ∘ x) ∘ x := by
    apply RewriteHypothesisAndGoal.Equation2726_implies_Equation3762 at h
    apply RewriteCombinations.Equation3762_implies_Equation336 at h
    apply RewriteHypothesis.Equation336_implies_Equation4391 at h
    apply Apply.Equation4391_implies_Equation4385 at h
    apply RewriteHypothesis.Equation4385_implies_Equation4666 at h
    apply Apply.Equation4666_implies_Equation4587 at h
    apply h
  have eq23 (x : G) : x = (x ∘ x) ∘ x := by
    apply Run6.Equation2726_implies_Equation23 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq2653 x]
  nth_rewrite 1 [← eq3715]
  nth_rewrite 1 [← eq4587]
  nth_rewrite 1 [← eq23]
  apply h
@[equational_result]
theorem Equation276_implies_Equation1441 (G: Type _) [Magma G] (h: Equation276 G) : Equation1441 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation276_implies_Equation270 at h
    apply Run3.Equation270_implies_Equation3 at h
    apply h
  have eq4380 (x : G) : x ∘ (x ∘ x) = (x ∘ x) ∘ x := by
    apply Run6.Equation276_implies_Equation4382 at h
    apply Apply.Equation4382_implies_Equation4380 at h
    apply h
  have eq1644 (x y : G) : x = (x ∘ y) ∘ ((x ∘ x) ∘ x) := by
    apply Run6.Equation276_implies_Equation25 at h
    apply RewriteHypothesis.Equation25_implies_Equation1650 at h
    apply Apply.Equation1650_implies_Equation1644 at h
    apply h
  have eq4086 (x y z : G) : x ∘ x = ((y ∘ x) ∘ z) ∘ x := by
    apply Run4.Equation276_implies_Equation4086 at h
    apply h
  intro x y
  nth_rewrite 1 [eq3 x]
  symm
  nth_rewrite 1 [eq4380]
  nth_rewrite 1 [← eq1644]
  symm
  nth_rewrite 1 [eq4086]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation276_implies_Equation156 (G: Type _) [Magma G] (h: Equation276 G) : Equation156 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation276_implies_Equation270 at h
    apply Run3.Equation270_implies_Equation3 at h
    apply h
  have eq1644 (x y : G) : x = (x ∘ y) ∘ ((x ∘ x) ∘ x) := by
    apply Run6.Equation276_implies_Equation25 at h
    apply RewriteHypothesis.Equation25_implies_Equation1650 at h
    apply Apply.Equation1650_implies_Equation1644 at h
    apply h
  have eq4086 (x y z : G) : x ∘ x = ((y ∘ x) ∘ z) ∘ x := by
    apply Run4.Equation276_implies_Equation4086 at h
    apply h
  intro x y
  symm
  nth_rewrite 2 [eq3 x]
  symm
  nth_rewrite 1 [eq3 x]
  symm
  nth_rewrite 1 [← eq1644]
  symm
  nth_rewrite 1 [eq4086]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation276_implies_Equation4217 (G: Type _) [Magma G] (h: Equation276 G) : Equation4217 G := by
  have eq4128 (x y : G) : x ∘ y = ((x ∘ y) ∘ x) ∘ y := by
    apply Run6.Equation276_implies_Equation25 at h
    apply RewriteHypothesis.Equation25_implies_Equation4138 at h
    apply Apply.Equation4138_implies_Equation4128 at h
    apply h
  have eq273 (x y : G) : x = ((y ∘ x) ∘ y) ∘ x := by
    apply Apply.Equation276_implies_Equation273 at h
    apply h
  have eq4083 (x y : G) : x ∘ x = ((y ∘ x) ∘ y) ∘ x := by
    apply Run3.Equation276_implies_Equation4083 at h
    apply h
  have eq4086 (x y z : G) : x ∘ x = ((y ∘ x) ∘ z) ∘ x := by
    apply Run4.Equation276_implies_Equation4086 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq4128]
  nth_rewrite 1 [← eq273]
  symm
  nth_rewrite 1 [← eq4083]
  nth_rewrite 1 [eq4086]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1995_implies_Equation4469 (G: Type _) [Magma G] (h: Equation1995 G) : Equation4469 G := by
  have eq23 (x : G) : x = (x ∘ x) ∘ x := by
    apply Run6.Equation1995_implies_Equation23 at h
    apply h
  have eq2038 (x y : G) : x = ((x ∘ x) ∘ x) ∘ (y ∘ y) := by
    apply Run6.Equation1995_implies_Equation174 at h
    apply Apply.Equation174_implies_Equation2176 at h
    apply Apply.Equation2176_implies_Equation2058 at h
    apply Apply.Equation2058_implies_Equation2038 at h
    apply h
  intro x y
  nth_rewrite 1 [eq23 x]
  nth_rewrite 1 [← eq2038]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq23]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1995_implies_Equation3676 (G: Type _) [Magma G] (h: Equation1995 G) : Equation3676 G := by
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply RewriteHypothesisAndGoal.Equation1995_implies_Equation320 at h
    apply Apply.Equation320_implies_Equation310 at h
    apply Apply.Equation310_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq168 (x y z : G) : x = (y ∘ x) ∘ (x ∘ z) := by
    apply Run6.Equation1995_implies_Equation168 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Run6.Equation1995_implies_Equation70 at h
    apply Apply.Equation70_implies_Equation50 at h
    apply Apply.Equation50_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq168]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1497_implies_Equation98 (G: Type _) [Magma G] (h: Equation1497 G) : Equation98 G := by
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  have eq3304 (x y z w u : G) : x ∘ x = y ∘ (z ∘ (w ∘ u)) := by
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq3 (x : G) : x = x ∘ x := by
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [eq47 x]
  symm
  nth_rewrite 1 [← eq3304]
  nth_rewrite 1 [← eq3]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation181 (G: Type _) [Magma G] (h: Equation1514 G) : Equation181 G := by
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  have eq3689 (x y z : G) : x ∘ x = (y ∘ y) ∘ (y ∘ z) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3693 at h
    apply Apply.Equation3693_implies_Equation3689 at h
    apply h
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq47 x]
  symm
  nth_rewrite 1 [← eq3689]
  nth_rewrite 1 [← eq3]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation191 (G: Type _) [Magma G] (h: Equation1514 G) : Equation191 G := by
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  have eq3699 (x y z : G) : x ∘ x = (y ∘ z) ∘ (y ∘ y) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation320 at h
    apply Apply.Equation320_implies_Equation3709 at h
    apply Apply.Equation3709_implies_Equation3699 at h
    apply h
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq47 x]
  symm
  nth_rewrite 1 [← eq3699]
  nth_rewrite 1 [← eq3]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation192 (G: Type _) [Magma G] (h: Equation1514 G) : Equation192 G := by
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  have eq3700 (x y z : G) : x ∘ x = (y ∘ z) ∘ (y ∘ z) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply Apply.Equation40_implies_Equation3700 at h
    apply h
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq47 x]
  symm
  nth_rewrite 1 [← eq3700]
  nth_rewrite 1 [← eq3]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation193 (G: Type _) [Magma G] (h: Equation1514 G) : Equation193 G := by
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  have eq3701 (x y z w : G) : x ∘ x = (y ∘ z) ∘ (y ∘ w) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3710 at h
    apply Apply.Equation3710_implies_Equation3701 at h
    apply h
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq47 x]
  symm
  nth_rewrite 1 [← eq3701]
  nth_rewrite 1 [← eq3]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1123 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1123 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1020 (x : G) : x = x ∘ ((x ∘ (x ∘ x)) ∘ x) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation8 at h
    apply RewriteHypothesis.Equation8_implies_Equation1020 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
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
theorem Equation1514_implies_Equation1326 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1326 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1223 (x : G) : x = x ∘ (((x ∘ x) ∘ x) ∘ x) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation1223 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1223]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1529 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1529 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1426 (x : G) : x = (x ∘ x) ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation1426 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1426]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1530 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1530 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1427 (x y : G) : x = (x ∘ x) ∘ (x ∘ (x ∘ y)) := by
    apply Apply.Equation1514_implies_Equation1440 at h
    apply Apply.Equation1440_implies_Equation1430 at h
    apply Apply.Equation1430_implies_Equation1427 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1427]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1532 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1532 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1428 (x y : G) : x = (x ∘ x) ∘ (x ∘ (y ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1440 at h
    apply Apply.Equation1440_implies_Equation1430 at h
    apply Apply.Equation1430_implies_Equation1428 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1428]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1533 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1533 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1429 (x y : G) : x = (x ∘ x) ∘ (x ∘ (y ∘ y)) := by
    apply Apply.Equation1514_implies_Equation1440 at h
    apply Apply.Equation1440_implies_Equation1430 at h
    apply Apply.Equation1430_implies_Equation1429 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1429]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1534 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1534 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1430 (x y z : G) : x = (x ∘ x) ∘ (x ∘ (y ∘ z)) := by
    apply Apply.Equation1514_implies_Equation1440 at h
    apply Apply.Equation1440_implies_Equation1430 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1430]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1540 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1540 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1431 (x y : G) : x = (x ∘ x) ∘ (y ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1440 at h
    apply Apply.Equation1440_implies_Equation1433 at h
    apply Apply.Equation1433_implies_Equation1431 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1431]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1541 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1541 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1432 (x y : G) : x = (x ∘ x) ∘ (y ∘ (x ∘ y)) := by
    apply Apply.Equation1514_implies_Equation1440 at h
    apply Apply.Equation1440_implies_Equation1433 at h
    apply Apply.Equation1433_implies_Equation1432 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1432]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1542 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1542 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1433 (x y z : G) : x = (x ∘ x) ∘ (y ∘ (x ∘ z)) := by
    apply Apply.Equation1514_implies_Equation1440 at h
    apply Apply.Equation1440_implies_Equation1433 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1433]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1544 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1544 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1434 (x y : G) : x = (x ∘ x) ∘ (y ∘ (y ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1440 at h
    apply Apply.Equation1440_implies_Equation1436 at h
    apply Apply.Equation1436_implies_Equation1434 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1434]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1545 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1545 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1435 (x y : G) : x = (x ∘ x) ∘ (y ∘ (y ∘ y)) := by
    apply Apply.Equation1514_implies_Equation1440 at h
    apply Apply.Equation1440_implies_Equation1436 at h
    apply Apply.Equation1436_implies_Equation1435 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1435]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1546 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1546 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1436 (x y z : G) : x = (x ∘ x) ∘ (y ∘ (y ∘ z)) := by
    apply Apply.Equation1514_implies_Equation1440 at h
    apply Apply.Equation1440_implies_Equation1436 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1436]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1548 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1548 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1437 (x y z : G) : x = (x ∘ x) ∘ (y ∘ (z ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1440 at h
    apply Apply.Equation1440_implies_Equation1437 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1437]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1549 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1549 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1438 (x y z : G) : x = (x ∘ x) ∘ (y ∘ (z ∘ y)) := by
    apply Apply.Equation1514_implies_Equation1440 at h
    apply Apply.Equation1440_implies_Equation1438 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1438]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1550 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1550 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1439 (x y z : G) : x = (x ∘ x) ∘ (y ∘ (z ∘ z)) := by
    apply Apply.Equation1514_implies_Equation1440 at h
    apply Apply.Equation1440_implies_Equation1439 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1439]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1551 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1551 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1440 (x y z w : G) : x = (x ∘ x) ∘ (y ∘ (z ∘ w)) := by
    apply Apply.Equation1514_implies_Equation1440 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1440]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1596 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1596 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1478 (x y : G) : x = (y ∘ x) ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1487 at h
    apply Apply.Equation1487_implies_Equation1480 at h
    apply Apply.Equation1480_implies_Equation1478 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1478]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1595 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1595 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1479 (x y : G) : x = (y ∘ x) ∘ (x ∘ (x ∘ y)) := by
    apply Apply.Equation1514_implies_Equation1487 at h
    apply Apply.Equation1487_implies_Equation1480 at h
    apply Apply.Equation1480_implies_Equation1479 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1479]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1597 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1597 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1480 (x y z : G) : x = (y ∘ x) ∘ (x ∘ (x ∘ z)) := by
    apply Apply.Equation1514_implies_Equation1487 at h
    apply Apply.Equation1487_implies_Equation1480 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1480]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1592 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1592 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1481 (x y : G) : x = (y ∘ x) ∘ (x ∘ (y ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1487 at h
    apply Apply.Equation1487_implies_Equation1483 at h
    apply Apply.Equation1483_implies_Equation1481 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1481]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1591 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1591 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1482 (x y : G) : x = (y ∘ x) ∘ (x ∘ (y ∘ y)) := by
    apply Apply.Equation1514_implies_Equation1487 at h
    apply Apply.Equation1487_implies_Equation1483 at h
    apply Apply.Equation1483_implies_Equation1482 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1482]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1593 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1593 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1483 (x y z : G) : x = (y ∘ x) ∘ (x ∘ (y ∘ z)) := by
    apply Apply.Equation1514_implies_Equation1487 at h
    apply Apply.Equation1487_implies_Equation1483 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1483]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1600 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1600 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1484 (x y z : G) : x = (y ∘ x) ∘ (x ∘ (z ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1487 at h
    apply Apply.Equation1487_implies_Equation1484 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1484]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1599 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1599 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1485 (x y z : G) : x = (y ∘ x) ∘ (x ∘ (z ∘ y)) := by
    apply Apply.Equation1514_implies_Equation1487 at h
    apply Apply.Equation1487_implies_Equation1485 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1485]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1601 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1601 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1486 (x y z : G) : x = (y ∘ x) ∘ (x ∘ (z ∘ z)) := by
    apply Apply.Equation1514_implies_Equation1487 at h
    apply Apply.Equation1487_implies_Equation1486 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1486]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1602 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1602 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1487 (x y z w : G) : x = (y ∘ x) ∘ (x ∘ (z ∘ w)) := by
    apply Apply.Equation1514_implies_Equation1487 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1487]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1579 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1579 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1488 (x y : G) : x = (y ∘ x) ∘ (y ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1490 at h
    apply Apply.Equation1490_implies_Equation1488 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1488]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1578 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1578 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1489 (x y : G) : x = (y ∘ x) ∘ (y ∘ (x ∘ y)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1490 at h
    apply Apply.Equation1490_implies_Equation1489 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1489]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1580 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1580 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1490 (x y z : G) : x = (y ∘ x) ∘ (y ∘ (x ∘ z)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1490 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1490]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1575 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1575 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1491 (x y : G) : x = (y ∘ x) ∘ (y ∘ (y ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1493 at h
    apply Apply.Equation1493_implies_Equation1491 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1491]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1574 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1574 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1492 (x y : G) : x = (y ∘ x) ∘ (y ∘ (y ∘ y)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1493 at h
    apply Apply.Equation1493_implies_Equation1492 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1492]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1576 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1576 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1493 (x y z : G) : x = (y ∘ x) ∘ (y ∘ (y ∘ z)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1493 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1493]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1583 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1583 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1494 (x y z : G) : x = (y ∘ x) ∘ (y ∘ (z ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1494 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1494]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1582 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1582 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1495 (x y z : G) : x = (y ∘ x) ∘ (y ∘ (z ∘ y)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1495 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1495]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1584 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1584 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1496 (x y z : G) : x = (y ∘ x) ∘ (y ∘ (z ∘ z)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1496]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1585 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1585 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1497 (x y z w : G) : x = (y ∘ x) ∘ (y ∘ (z ∘ w)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1497]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1615 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1615 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1498 (x y z : G) : x = (y ∘ x) ∘ (z ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1501 at h
    apply Apply.Equation1501_implies_Equation1498 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1498]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1614 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1614 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1499 (x y z : G) : x = (y ∘ x) ∘ (z ∘ (x ∘ y)) := by
    apply Apply.Equation1514_implies_Equation1501 at h
    apply Apply.Equation1501_implies_Equation1499 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1499]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1616 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1616 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1500 (x y z : G) : x = (y ∘ x) ∘ (z ∘ (x ∘ z)) := by
    apply Apply.Equation1514_implies_Equation1501 at h
    apply Apply.Equation1501_implies_Equation1500 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1500]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1617 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1617 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1501 (x y z w : G) : x = (y ∘ x) ∘ (z ∘ (x ∘ w)) := by
    apply Apply.Equation1514_implies_Equation1501 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1501]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1610 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1610 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1502 (x y z : G) : x = (y ∘ x) ∘ (z ∘ (y ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1505 at h
    apply Apply.Equation1505_implies_Equation1502 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1502]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1609 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1609 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1503 (x y z : G) : x = (y ∘ x) ∘ (z ∘ (y ∘ y)) := by
    apply Apply.Equation1514_implies_Equation1505 at h
    apply Apply.Equation1505_implies_Equation1503 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1503]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1611 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1611 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1504 (x y z : G) : x = (y ∘ x) ∘ (z ∘ (y ∘ z)) := by
    apply Apply.Equation1514_implies_Equation1505 at h
    apply Apply.Equation1505_implies_Equation1504 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1504]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1612 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1612 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1505 (x y z w : G) : x = (y ∘ x) ∘ (z ∘ (y ∘ w)) := by
    apply Apply.Equation1514_implies_Equation1505 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1505]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1620 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1620 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1506 (x y z : G) : x = (y ∘ x) ∘ (z ∘ (z ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1509 at h
    apply Apply.Equation1509_implies_Equation1506 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1506]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1619 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1619 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1507 (x y z : G) : x = (y ∘ x) ∘ (z ∘ (z ∘ y)) := by
    apply Apply.Equation1514_implies_Equation1509 at h
    apply Apply.Equation1509_implies_Equation1507 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1507]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1621 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1621 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1508 (x y z : G) : x = (y ∘ x) ∘ (z ∘ (z ∘ z)) := by
    apply Apply.Equation1514_implies_Equation1509 at h
    apply Apply.Equation1509_implies_Equation1508 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1508]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1622 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1622 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1509 (x y z w : G) : x = (y ∘ x) ∘ (z ∘ (z ∘ w)) := by
    apply Apply.Equation1514_implies_Equation1509 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1509]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1625 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1625 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1510 (x y z w : G) : x = (y ∘ x) ∘ (z ∘ (w ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1510 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1510]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1624 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1624 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1511 (x y z w : G) : x = (y ∘ x) ∘ (z ∘ (w ∘ y)) := by
    apply Apply.Equation1514_implies_Equation1511 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1511]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1626 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1626 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1512 (x y z w : G) : x = (y ∘ x) ∘ (z ∘ (w ∘ z)) := by
    apply Apply.Equation1514_implies_Equation1512 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
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
theorem Equation1514_implies_Equation1627 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1627 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1513 (x y z w : G) : x = (y ∘ x) ∘ (z ∘ (w ∘ w)) := by
    apply Apply.Equation1514_implies_Equation1513 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1513]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1732 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1732 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1629 (x : G) : x = (x ∘ x) ∘ ((x ∘ x) ∘ x) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation23 at h
    apply RewriteHypothesis.Equation23_implies_Equation1629 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1629]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1514_implies_Equation1935 (G: Type _) [Magma G] (h: Equation1514 G) : Equation1935 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq1832 (x : G) : x = (x ∘ (x ∘ x)) ∘ (x ∘ x) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation8 at h
    apply RewriteHypothesis.Equation8_implies_Equation1832 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1514_implies_Equation1497 at h
    apply Run6.Equation1497_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  intro x y
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq40]
  nth_rewrite 1 [eq3253]
  symm
  nth_rewrite 1 [← eq1832]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1505_implies_Equation1428 (G: Type _) [Magma G] (h: Equation1505 G) : Equation1428 G := by
  have eq4283 (x y : G) : x ∘ (x ∘ y) = x ∘ (y ∘ x) := by
    apply RewriteHypothesisAndGoal.Equation1505_implies_Equation4338 at h
    apply Apply.Equation4338_implies_Equation4328 at h
    apply RewriteHypothesis.Equation4328_implies_Equation4283 at h
    apply h
  have eq1426 (x : G) : x = (x ∘ x) ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1505_implies_Equation1433 at h
    apply Apply.Equation1433_implies_Equation1427 at h
    apply Apply.Equation1427_implies_Equation1426 at h
    apply h
  have eq1427 (x y : G) : x = (x ∘ x) ∘ (x ∘ (x ∘ y)) := by
    apply Apply.Equation1505_implies_Equation1433 at h
    apply Apply.Equation1433_implies_Equation1427 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq4283 x]
  symm
  nth_rewrite 1 [eq1426 x]
  symm
  nth_rewrite 1 [← eq1427 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq1426 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1505_implies_Equation1429 (G: Type _) [Magma G] (h: Equation1505 G) : Equation1429 G := by
  have eq1426 (x : G) : x = (x ∘ x) ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1505_implies_Equation1433 at h
    apply Apply.Equation1433_implies_Equation1427 at h
    apply Apply.Equation1427_implies_Equation1426 at h
    apply h
  have eq4284 (x y : G) : x ∘ (x ∘ y) = x ∘ (y ∘ y) := by
    apply RewriteHypothesisAndGoal.Equation1505_implies_Equation4338 at h
    apply Apply.Equation4338_implies_Equation4281 at h
    apply Apply.Equation4281_implies_Equation4278 at h
    apply RewriteCombinations.Equation4278_implies_Equation4304 at h
    apply Apply.Equation4304_implies_Equation4284 at h
    apply h
  have eq1427 (x y : G) : x = (x ∘ x) ∘ (x ∘ (x ∘ y)) := by
    apply Apply.Equation1505_implies_Equation1433 at h
    apply Apply.Equation1433_implies_Equation1427 at h
    apply h
  intro x y
  nth_rewrite 1 [eq1426 x]
  symm
  nth_rewrite 1 [← eq4284 x]
  nth_rewrite 1 [← eq1427 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq1426 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1505_implies_Equation1479 (G: Type _) [Magma G] (h: Equation1505 G) : Equation1479 G := by
  have eq4283 (x y : G) : x ∘ (x ∘ y) = x ∘ (y ∘ x) := by
    apply RewriteHypothesisAndGoal.Equation1505_implies_Equation4338 at h
    apply Apply.Equation4338_implies_Equation4328 at h
    apply RewriteHypothesis.Equation4328_implies_Equation4283 at h
    apply h
  have eq1426 (x : G) : x = (x ∘ x) ∘ (x ∘ (x ∘ x)) := by
    apply Apply.Equation1505_implies_Equation1433 at h
    apply Apply.Equation1433_implies_Equation1427 at h
    apply Apply.Equation1427_implies_Equation1426 at h
    apply h
  have eq1481 (x y : G) : x = (y ∘ x) ∘ (x ∘ (y ∘ x)) := by
    apply Apply.Equation1505_implies_Equation1483 at h
    apply Apply.Equation1483_implies_Equation1481 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [eq4283 x]
  symm
  nth_rewrite 1 [eq1426 x]
  symm
  nth_rewrite 1 [← eq1481 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq1426 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1715_implies_Equation920 (G: Type _) [Magma G] (h: Equation1715 G) : Equation920 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Run2.Equation1715_implies_Equation1712 at h
    apply Run6.Equation1712_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply RewriteHypothesisAndGoal.Equation1715_implies_Equation371 at h
    apply Apply.Equation371_implies_Equation3910 at h
    apply Apply.Equation3910_implies_Equation3906 at h
    apply Run6.Equation3906_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Run2.Equation1715_implies_Equation1712 at h
    apply Run6.Equation1712_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq817 (x : G) : x = x ∘ ((x ∘ x) ∘ (x ∘ x)) := by
    apply Run2.Equation1715_implies_Equation1712 at h
    apply Run6.Equation1712_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation817 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Run2.Equation1715_implies_Equation1712 at h
    apply Run6.Equation1712_implies_Equation3 at h
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
  have eq3 (x : G) : x = x ∘ x := by
    apply Run6.Equation1712_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply RewriteHypothesisAndGoal.Equation1712_implies_Equation369 at h
    apply Apply.Equation369_implies_Equation3693 at h
    apply Apply.Equation3693_implies_Equation3689 at h
    apply RewriteHypothesisAndGoal.Equation3689_implies_Equation40 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Run6.Equation1712_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation326 at h
    apply Apply.Equation326_implies_Equation307 at h
    apply RewriteHypothesis.Equation307_implies_Equation3253 at h
    apply h
  have eq817 (x : G) : x = x ∘ ((x ∘ x) ∘ (x ∘ x)) := by
    apply Run6.Equation1712_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation817 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Run6.Equation1712_implies_Equation3 at h
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
theorem Equation979_implies_Equation13 (G: Type _) [Magma G] (h: Equation979 G) : Equation13 G := by
  have eq3659 (x : G) : x ∘ x = (x ∘ x) ∘ (x ∘ x) := by
    apply RewriteHypothesisAndGoal.Equation979_implies_Equation40 at h
    apply NthRewrites.Equation40_implies_Equation3662 at h
    apply Apply.Equation3662_implies_Equation3659 at h
    apply h
  have eq411 (x : G) : x = x ∘ (x ∘ (x ∘ (x ∘ x))) := by
    apply Run6.Equation979_implies_Equation8 at h
    apply RewriteHypothesis.Equation8_implies_Equation411 at h
    apply h
  have eq869 (x y : G) : x = y ∘ ((x ∘ x) ∘ (x ∘ x)) := by
    apply Apply.Equation979_implies_Equation869 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [eq3659]
  symm
  nth_rewrite 1 [eq411 x]
  symm
  nth_rewrite 1 [← eq869]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq411]
  apply h
  repeat assumption
@[equational_result]
theorem Equation2214_implies_Equation2050 (G: Type _) [Magma G] (h: Equation2214 G) : Equation2050 G := by
  have eq4598 (x y : G) : (x ∘ x) ∘ y = (x ∘ y) ∘ x := by
    apply RewriteHypothesisAndGoal.Equation2214_implies_Equation4653 at h
    apply Apply.Equation4653_implies_Equation4643 at h
    apply RewriteHypothesis.Equation4643_implies_Equation4598 at h
    apply h
  have eq2035 (x : G) : x = ((x ∘ x) ∘ x) ∘ (x ∘ x) := by
    apply Apply.Equation2214_implies_Equation2071 at h
    apply Apply.Equation2071_implies_Equation2040 at h
    apply Apply.Equation2040_implies_Equation2035 at h
    apply h
  have eq2040 (x y : G) : x = ((x ∘ x) ∘ y) ∘ (x ∘ x) := by
    apply Apply.Equation2214_implies_Equation2071 at h
    apply Apply.Equation2071_implies_Equation2040 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq4598]
  symm
  nth_rewrite 1 [eq2035 x]
  symm
  nth_rewrite 1 [← eq2040]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq2035]
  apply h
  repeat assumption
@[equational_result]
theorem Equation2214_implies_Equation2060 (G: Type _) [Magma G] (h: Equation2214 G) : Equation2060 G := by
  have eq2035 (x : G) : x = ((x ∘ x) ∘ x) ∘ (x ∘ x) := by
    apply Apply.Equation2214_implies_Equation2071 at h
    apply Apply.Equation2071_implies_Equation2040 at h
    apply Apply.Equation2040_implies_Equation2035 at h
    apply h
  have eq4599 (x y : G) : (x ∘ x) ∘ y = (x ∘ y) ∘ y := by
    apply RewriteHypothesisAndGoal.Equation2214_implies_Equation4653 at h
    apply Apply.Equation4653_implies_Equation4596 at h
    apply RewriteCombinations.Equation4596_implies_Equation4664 at h
    apply SimpleRewrites.Equation4664_implies_Equation4663 at h
    apply RewriteHypothesis.Equation4663_implies_Equation4599 at h
    apply h
  have eq2040 (x y : G) : x = ((x ∘ x) ∘ y) ∘ (x ∘ x) := by
    apply Apply.Equation2214_implies_Equation2071 at h
    apply Apply.Equation2071_implies_Equation2040 at h
    apply h
  intro x y
  nth_rewrite 1 [eq2035 x]
  symm
  nth_rewrite 1 [← eq4599]
  nth_rewrite 1 [← eq2040]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq2035]
  apply h
  repeat assumption
@[equational_result]
theorem Equation2214_implies_Equation2041 (G: Type _) [Magma G] (h: Equation2214 G) : Equation2041 G := by
  have eq4598 (x y : G) : (x ∘ x) ∘ y = (x ∘ y) ∘ x := by
    apply RewriteHypothesisAndGoal.Equation2214_implies_Equation4653 at h
    apply Apply.Equation4653_implies_Equation4643 at h
    apply RewriteHypothesis.Equation4643_implies_Equation4598 at h
    apply h
  have eq2035 (x : G) : x = ((x ∘ x) ∘ x) ∘ (x ∘ x) := by
    apply Apply.Equation2214_implies_Equation2071 at h
    apply Apply.Equation2071_implies_Equation2040 at h
    apply Apply.Equation2040_implies_Equation2035 at h
    apply h
  have eq2051 (x y : G) : x = ((x ∘ y) ∘ x) ∘ (x ∘ y) := by
    apply Apply.Equation2214_implies_Equation2071 at h
    apply Apply.Equation2071_implies_Equation2051 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [eq4598]
  symm
  nth_rewrite 1 [eq2035 x]
  symm
  nth_rewrite 1 [← eq2051]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq2035]
  apply h
  repeat assumption
@[equational_result]
theorem Equation74_implies_Equation1005 (G: Type _) [Magma G] (h: Equation74 G) : Equation1005 G := by
  have eq4 (x y : G) : x = x ∘ y := by
    apply Run5.Equation74_implies_Equation4 at h
    apply h
  have eq39 (x y : G) : x ∘ x = y ∘ x := by
    apply Run5.Equation74_implies_Equation3416 at h
    apply RewriteCombinations.Equation3416_implies_Equation3429 at h
    apply Constant.Equation3429_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation39 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Run3.Equation74_implies_Equation3280 at h
    apply Apply.Equation3280_implies_Equation3254 at h
    apply Apply.Equation3254_implies_Equation3253 at h
    apply h
  have eq856 (x y z : G) : x = x ∘ ((y ∘ z) ∘ (y ∘ x)) := by
    apply Run5.Equation74_implies_Equation4 at h
    apply Apply.Equation4_implies_Equation12 at h
    apply Apply.Equation12_implies_Equation113 at h
    apply Apply.Equation113_implies_Equation868 at h
    apply Apply.Equation868_implies_Equation859 at h
    apply Apply.Equation859_implies_Equation856 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
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
  have eq4 (x y : G) : x = x ∘ y := by
    apply Run5.Equation74_implies_Equation4 at h
    apply h
  have eq39 (x y : G) : x ∘ x = y ∘ x := by
    apply Run5.Equation74_implies_Equation3416 at h
    apply RewriteCombinations.Equation3416_implies_Equation3429 at h
    apply Constant.Equation3429_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation39 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Run3.Equation74_implies_Equation3280 at h
    apply Apply.Equation3280_implies_Equation3254 at h
    apply Apply.Equation3254_implies_Equation3253 at h
    apply h
  have eq857 (x y z : G) : x = x ∘ ((y ∘ z) ∘ (y ∘ y)) := by
    apply Run5.Equation74_implies_Equation4 at h
    apply Apply.Equation4_implies_Equation12 at h
    apply Apply.Equation12_implies_Equation113 at h
    apply Apply.Equation113_implies_Equation868 at h
    apply Apply.Equation868_implies_Equation859 at h
    apply Apply.Equation859_implies_Equation857 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
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
  have eq4 (x y : G) : x = x ∘ y := by
    apply Run5.Equation74_implies_Equation4 at h
    apply h
  have eq39 (x y : G) : x ∘ x = y ∘ x := by
    apply Run5.Equation74_implies_Equation3416 at h
    apply RewriteCombinations.Equation3416_implies_Equation3429 at h
    apply Constant.Equation3429_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation39 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Run3.Equation74_implies_Equation3280 at h
    apply Apply.Equation3280_implies_Equation3254 at h
    apply Apply.Equation3254_implies_Equation3253 at h
    apply h
  have eq858 (x y z : G) : x = x ∘ ((y ∘ z) ∘ (y ∘ z)) := by
    apply Run5.Equation74_implies_Equation4 at h
    apply Apply.Equation4_implies_Equation12 at h
    apply Apply.Equation12_implies_Equation11 at h
    apply Apply.Equation11_implies_Equation858 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
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
  have eq4 (x y : G) : x = x ∘ y := by
    apply Run5.Equation74_implies_Equation4 at h
    apply h
  have eq39 (x y : G) : x ∘ x = y ∘ x := by
    apply Run5.Equation74_implies_Equation3416 at h
    apply RewriteCombinations.Equation3416_implies_Equation3429 at h
    apply Constant.Equation3429_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation39 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Run3.Equation74_implies_Equation3280 at h
    apply Apply.Equation3280_implies_Equation3254 at h
    apply Apply.Equation3254_implies_Equation3253 at h
    apply h
  have eq860 (x y z : G) : x = x ∘ ((y ∘ z) ∘ (z ∘ x)) := by
    apply Run5.Equation74_implies_Equation4 at h
    apply Apply.Equation4_implies_Equation12 at h
    apply Apply.Equation12_implies_Equation113 at h
    apply Apply.Equation113_implies_Equation868 at h
    apply Apply.Equation868_implies_Equation863 at h
    apply Apply.Equation863_implies_Equation860 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
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
  have eq4 (x y : G) : x = x ∘ y := by
    apply Run5.Equation74_implies_Equation4 at h
    apply h
  have eq39 (x y : G) : x ∘ x = y ∘ x := by
    apply Run5.Equation74_implies_Equation3416 at h
    apply RewriteCombinations.Equation3416_implies_Equation3429 at h
    apply Constant.Equation3429_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation39 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Run3.Equation74_implies_Equation3280 at h
    apply Apply.Equation3280_implies_Equation3254 at h
    apply Apply.Equation3254_implies_Equation3253 at h
    apply h
  have eq861 (x y z : G) : x = x ∘ ((y ∘ z) ∘ (z ∘ y)) := by
    apply Run5.Equation74_implies_Equation4 at h
    apply Apply.Equation4_implies_Equation12 at h
    apply Apply.Equation12_implies_Equation113 at h
    apply Apply.Equation113_implies_Equation868 at h
    apply Apply.Equation868_implies_Equation863 at h
    apply Apply.Equation863_implies_Equation861 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
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
  have eq4 (x y : G) : x = x ∘ y := by
    apply Run5.Equation74_implies_Equation4 at h
    apply h
  have eq39 (x y : G) : x ∘ x = y ∘ x := by
    apply Run5.Equation74_implies_Equation3416 at h
    apply RewriteCombinations.Equation3416_implies_Equation3429 at h
    apply Constant.Equation3429_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation39 at h
    apply h
  have eq3253 (x : G) : x ∘ x = x ∘ (x ∘ (x ∘ x)) := by
    apply Run3.Equation74_implies_Equation3280 at h
    apply Apply.Equation3280_implies_Equation3254 at h
    apply Apply.Equation3254_implies_Equation3253 at h
    apply h
  have eq862 (x y z : G) : x = x ∘ ((y ∘ z) ∘ (z ∘ z)) := by
    apply Run5.Equation74_implies_Equation4 at h
    apply Apply.Equation4_implies_Equation12 at h
    apply Apply.Equation12_implies_Equation113 at h
    apply Apply.Equation113_implies_Equation868 at h
    apply Apply.Equation868_implies_Equation863 at h
    apply Apply.Equation863_implies_Equation862 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
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
theorem Equation3190_implies_Equation3062 (G: Type _) [Magma G] (h: Equation3190 G) : Equation3062 G := by
  have eq4598 (x y : G) : (x ∘ x) ∘ y = (x ∘ y) ∘ x := by
    apply RewriteHypothesisAndGoal.Equation3190_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4679 at h
    apply Apply.Equation4679_implies_Equation4598 at h
    apply h
  have eq3050 (x : G) : x = (((x ∘ x) ∘ x) ∘ x) ∘ x := by
    apply Apply.Equation3190_implies_Equation3072 at h
    apply Apply.Equation3072_implies_Equation3052 at h
    apply Apply.Equation3052_implies_Equation3050 at h
    apply h
  have eq3072 (x y z : G) : x = (((x ∘ y) ∘ x) ∘ z) ∘ y := by
    apply Apply.Equation3190_implies_Equation3072 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq4598 x]
  symm
  nth_rewrite 1 [eq3050 x]
  symm
  nth_rewrite 1 [← eq3072 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq3050 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3190_implies_Equation3082 (G: Type _) [Magma G] (h: Equation3190 G) : Equation3082 G := by
  have eq3050 (x : G) : x = (((x ∘ x) ∘ x) ∘ x) ∘ x := by
    apply Apply.Equation3190_implies_Equation3072 at h
    apply Apply.Equation3072_implies_Equation3052 at h
    apply Apply.Equation3052_implies_Equation3050 at h
    apply h
  have eq4629 (x y : G) : (x ∘ y) ∘ x = (x ∘ y) ∘ y := by
    apply RewriteHypothesisAndGoal.Equation3190_implies_Equation4694 at h
    apply Apply.Equation4694_implies_Equation4628 at h
    apply Apply.Equation4628_implies_Equation4604 at h
    apply RewriteCombinations.Equation4604_implies_Equation4632 at h
    apply Apply.Equation4632_implies_Equation4629 at h
    apply h
  have eq3072 (x y z : G) : x = (((x ∘ y) ∘ x) ∘ z) ∘ y := by
    apply Apply.Equation3190_implies_Equation3072 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq3050 x]
  symm
  nth_rewrite 1 [← eq4629 x]
  nth_rewrite 1 [← eq3072 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq3050 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3189_implies_Equation2858 (G: Type _) [Magma G] (h: Equation3189 G) : Equation2858 G := by
  have eq4283 (x y : G) : x ∘ (x ∘ y) = x ∘ (y ∘ x) := by
    apply RewriteHypothesisAndGoal.Equation3189_implies_Equation4379 at h
    apply Apply.Equation4379_implies_Equation4364 at h
    apply Apply.Equation4364_implies_Equation4283 at h
    apply h
  have eq2847 (x : G) : x = ((x ∘ (x ∘ x)) ∘ x) ∘ x := by
    apply Run2.Equation3189_implies_Equation2986 at h
    apply Apply.Equation2986_implies_Equation2868 at h
    apply Apply.Equation2868_implies_Equation2849 at h
    apply Apply.Equation2849_implies_Equation2847 at h
    apply h
  have eq2868 (x y z : G) : x = ((x ∘ (y ∘ x)) ∘ z) ∘ x := by
    apply Run2.Equation3189_implies_Equation2986 at h
    apply Apply.Equation2986_implies_Equation2868 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq4283 x]
  symm
  nth_rewrite 1 [eq2847 x]
  symm
  nth_rewrite 1 [← eq2868 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq2847 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3189_implies_Equation2878 (G: Type _) [Magma G] (h: Equation3189 G) : Equation2878 G := by
  have eq2847 (x : G) : x = ((x ∘ (x ∘ x)) ∘ x) ∘ x := by
    apply Run2.Equation3189_implies_Equation2986 at h
    apply Apply.Equation2986_implies_Equation2868 at h
    apply Apply.Equation2868_implies_Equation2849 at h
    apply Apply.Equation2849_implies_Equation2847 at h
    apply h
  have eq4314 (x y : G) : x ∘ (y ∘ x) = x ∘ (y ∘ y) := by
    apply RewriteHypothesisAndGoal.Equation3189_implies_Equation4379 at h
    apply Apply.Equation4379_implies_Equation4313 at h
    apply Apply.Equation4313_implies_Equation4281 at h
    apply RewriteCombinations.Equation4281_implies_Equation4350 at h
    apply RewriteHypothesis.Equation4350_implies_Equation4314 at h
    apply h
  have eq2868 (x y z : G) : x = ((x ∘ (y ∘ x)) ∘ z) ∘ x := by
    apply Run2.Equation3189_implies_Equation2986 at h
    apply Apply.Equation2986_implies_Equation2868 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq2847 x]
  symm
  nth_rewrite 1 [← eq4314 x]
  nth_rewrite 1 [← eq2868 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq2847 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3189_implies_Equation3061 (G: Type _) [Magma G] (h: Equation3189 G) : Equation3061 G := by
  have eq2847 (x : G) : x = ((x ∘ (x ∘ x)) ∘ x) ∘ x := by
    apply Run2.Equation3189_implies_Equation2986 at h
    apply Apply.Equation2986_implies_Equation2868 at h
    apply Apply.Equation2868_implies_Equation2849 at h
    apply Apply.Equation2849_implies_Equation2847 at h
    apply h
  have eq4433 (x y : G) : x ∘ (y ∘ x) = (x ∘ x) ∘ y := by
    apply RewriteHypothesisAndGoal.Equation3189_implies_Equation4582 at h
    apply Apply.Equation4582_implies_Equation4468 at h
    apply Apply.Equation4468_implies_Equation4441 at h
    apply Apply.Equation4441_implies_Equation4434 at h
    apply Apply.Equation4434_implies_Equation4433 at h
    apply h
  have eq2868 (x y z : G) : x = ((x ∘ (y ∘ x)) ∘ z) ∘ x := by
    apply Run2.Equation3189_implies_Equation2986 at h
    apply Apply.Equation2986_implies_Equation2868 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq2847 x]
  symm
  nth_rewrite 1 [← eq4433 x]
  nth_rewrite 1 [← eq2868 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq2847 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3189_implies_Equation3081 (G: Type _) [Magma G] (h: Equation3189 G) : Equation3081 G := by
  have eq2847 (x : G) : x = ((x ∘ (x ∘ x)) ∘ x) ∘ x := by
    apply Run2.Equation3189_implies_Equation2986 at h
    apply Apply.Equation2986_implies_Equation2868 at h
    apply Apply.Equation2868_implies_Equation2849 at h
    apply Apply.Equation2849_implies_Equation2847 at h
    apply h
  have eq4436 (x y : G) : x ∘ (y ∘ x) = (x ∘ y) ∘ y := by
    apply RewriteHypothesisAndGoal.Equation3189_implies_Equation4582 at h
    apply Apply.Equation4582_implies_Equation4468 at h
    apply Apply.Equation4468_implies_Equation4441 at h
    apply Apply.Equation4441_implies_Equation4437 at h
    apply Apply.Equation4437_implies_Equation4436 at h
    apply h
  have eq2868 (x y z : G) : x = ((x ∘ (y ∘ x)) ∘ z) ∘ x := by
    apply Run2.Equation3189_implies_Equation2986 at h
    apply Apply.Equation2986_implies_Equation2868 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq2847 x]
  symm
  nth_rewrite 1 [← eq4436 x]
  nth_rewrite 1 [← eq2868 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq2847 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3125_implies_Equation3240 (G: Type _) [Magma G] (h: Equation3125 G) : Equation3240 G := by
  have eq8 (x : G) : x = x ∘ (x ∘ x) := by
    apply Run6.Equation3125_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation8 at h
    apply h
  have eq4276 (x y : G) : x ∘ (x ∘ x) = y ∘ (y ∘ y) := by
    apply RewriteHypothesisAndGoal.Equation3125_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3390 at h
    apply SimpleRewrites.Equation3390_implies_Equation3273 at h
    apply RewriteCombinations.Equation3273_implies_Equation4276 at h
    apply h
  have eq3124 (x y z : G) : x = (((y ∘ x) ∘ z) ∘ x) ∘ z := by
    apply Apply.Equation3125_implies_Equation3124 at h
    apply h
  have eq411 (x : G) : x = x ∘ (x ∘ (x ∘ (x ∘ x))) := by
    apply Run6.Equation3125_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation8 at h
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
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation276_implies_Equation270 at h
    apply Run3.Equation270_implies_Equation3 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq3]
  symm
  apply h
@[equational_result]
theorem Equation1972_implies_Equation1844 (G: Type _) [Magma G] (h: Equation1972 G) : Equation1844 G := by
  have eq4283 (x y : G) : x ∘ (x ∘ y) = x ∘ (y ∘ x) := by
    apply RewriteHypothesisAndGoal.Equation1972_implies_Equation4379 at h
    apply Apply.Equation4379_implies_Equation4364 at h
    apply Apply.Equation4364_implies_Equation4283 at h
    apply h
  have eq1832 (x : G) : x = (x ∘ (x ∘ x)) ∘ (x ∘ x) := by
    apply Apply.Equation1972_implies_Equation1854 at h
    apply Apply.Equation1854_implies_Equation1834 at h
    apply Apply.Equation1834_implies_Equation1832 at h
    apply h
  have eq1854 (x y z : G) : x = (x ∘ (y ∘ x)) ∘ (z ∘ y) := by
    apply Apply.Equation1972_implies_Equation1854 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq4283 x]
  symm
  nth_rewrite 1 [eq1832 x]
  symm
  nth_rewrite 1 [← eq1854 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq1832 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1972_implies_Equation1864 (G: Type _) [Magma G] (h: Equation1972 G) : Equation1864 G := by
  have eq1832 (x : G) : x = (x ∘ (x ∘ x)) ∘ (x ∘ x) := by
    apply Apply.Equation1972_implies_Equation1854 at h
    apply Apply.Equation1854_implies_Equation1834 at h
    apply Apply.Equation1834_implies_Equation1832 at h
    apply h
  have eq4314 (x y : G) : x ∘ (y ∘ x) = x ∘ (y ∘ y) := by
    apply RewriteHypothesisAndGoal.Equation1972_implies_Equation4379 at h
    apply Apply.Equation4379_implies_Equation4313 at h
    apply Apply.Equation4313_implies_Equation4281 at h
    apply RewriteCombinations.Equation4281_implies_Equation4350 at h
    apply RewriteHypothesis.Equation4350_implies_Equation4314 at h
    apply h
  have eq1854 (x y z : G) : x = (x ∘ (y ∘ x)) ∘ (z ∘ y) := by
    apply Apply.Equation1972_implies_Equation1854 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq1832 x]
  symm
  nth_rewrite 1 [← eq4314 x]
  nth_rewrite 1 [← eq1854 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq1832 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1972_implies_Equation2047 (G: Type _) [Magma G] (h: Equation1972 G) : Equation2047 G := by
  have eq1832 (x : G) : x = (x ∘ (x ∘ x)) ∘ (x ∘ x) := by
    apply Apply.Equation1972_implies_Equation1854 at h
    apply Apply.Equation1854_implies_Equation1834 at h
    apply Apply.Equation1834_implies_Equation1832 at h
    apply h
  have eq4433 (x y : G) : x ∘ (y ∘ x) = (x ∘ x) ∘ y := by
    apply RewriteHypothesisAndGoal.Equation1972_implies_Equation4582 at h
    apply Apply.Equation4582_implies_Equation4468 at h
    apply Apply.Equation4468_implies_Equation4441 at h
    apply Apply.Equation4441_implies_Equation4434 at h
    apply Apply.Equation4434_implies_Equation4433 at h
    apply h
  have eq1854 (x y z : G) : x = (x ∘ (y ∘ x)) ∘ (z ∘ y) := by
    apply Apply.Equation1972_implies_Equation1854 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq1832 x]
  symm
  nth_rewrite 1 [← eq4433 x]
  nth_rewrite 1 [← eq1854 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq1832 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1972_implies_Equation2067 (G: Type _) [Magma G] (h: Equation1972 G) : Equation2067 G := by
  have eq1832 (x : G) : x = (x ∘ (x ∘ x)) ∘ (x ∘ x) := by
    apply Apply.Equation1972_implies_Equation1854 at h
    apply Apply.Equation1854_implies_Equation1834 at h
    apply Apply.Equation1834_implies_Equation1832 at h
    apply h
  have eq4436 (x y : G) : x ∘ (y ∘ x) = (x ∘ y) ∘ y := by
    apply RewriteHypothesisAndGoal.Equation1972_implies_Equation4582 at h
    apply Apply.Equation4582_implies_Equation4468 at h
    apply Apply.Equation4468_implies_Equation4441 at h
    apply Apply.Equation4441_implies_Equation4437 at h
    apply Apply.Equation4437_implies_Equation4436 at h
    apply h
  have eq1854 (x y z : G) : x = (x ∘ (y ∘ x)) ∘ (z ∘ y) := by
    apply Apply.Equation1972_implies_Equation1854 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq1832 x]
  symm
  nth_rewrite 1 [← eq4436 x]
  nth_rewrite 1 [← eq1854 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq1832 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1969_implies_Equation1842 (G: Type _) [Magma G] (h: Equation1969 G) : Equation1842 G := by
  have eq4283 (x y : G) : x ∘ (x ∘ y) = x ∘ (y ∘ x) := by
    apply RewriteHypothesisAndGoal.Equation1969_implies_Equation4379 at h
    apply Apply.Equation4379_implies_Equation4364 at h
    apply Apply.Equation4364_implies_Equation4283 at h
    apply h
  have eq1832 (x : G) : x = (x ∘ (x ∘ x)) ∘ (x ∘ x) := by
    apply Apply.Equation1969_implies_Equation1852 at h
    apply Apply.Equation1852_implies_Equation1833 at h
    apply Apply.Equation1833_implies_Equation1832 at h
    apply h
  have eq1852 (x y z : G) : x = (x ∘ (y ∘ x)) ∘ (y ∘ z) := by
    apply Apply.Equation1969_implies_Equation1852 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [eq4283 x]
  symm
  nth_rewrite 1 [eq1832 x]
  symm
  nth_rewrite 1 [← eq1852 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq1832 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1969_implies_Equation1862 (G: Type _) [Magma G] (h: Equation1969 G) : Equation1862 G := by
  have eq1832 (x : G) : x = (x ∘ (x ∘ x)) ∘ (x ∘ x) := by
    apply Apply.Equation1969_implies_Equation1852 at h
    apply Apply.Equation1852_implies_Equation1833 at h
    apply Apply.Equation1833_implies_Equation1832 at h
    apply h
  have eq4314 (x y : G) : x ∘ (y ∘ x) = x ∘ (y ∘ y) := by
    apply RewriteHypothesisAndGoal.Equation1969_implies_Equation4379 at h
    apply Apply.Equation4379_implies_Equation4313 at h
    apply Apply.Equation4313_implies_Equation4281 at h
    apply RewriteCombinations.Equation4281_implies_Equation4350 at h
    apply RewriteHypothesis.Equation4350_implies_Equation4314 at h
    apply h
  have eq1852 (x y z : G) : x = (x ∘ (y ∘ x)) ∘ (y ∘ z) := by
    apply Apply.Equation1969_implies_Equation1852 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq1832 x]
  symm
  nth_rewrite 1 [← eq4314 x]
  nth_rewrite 1 [← eq1852 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq1832 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1969_implies_Equation2045 (G: Type _) [Magma G] (h: Equation1969 G) : Equation2045 G := by
  have eq1832 (x : G) : x = (x ∘ (x ∘ x)) ∘ (x ∘ x) := by
    apply Apply.Equation1969_implies_Equation1852 at h
    apply Apply.Equation1852_implies_Equation1833 at h
    apply Apply.Equation1833_implies_Equation1832 at h
    apply h
  have eq4433 (x y : G) : x ∘ (y ∘ x) = (x ∘ x) ∘ y := by
    apply RewriteHypothesisAndGoal.Equation1969_implies_Equation4582 at h
    apply Apply.Equation4582_implies_Equation4468 at h
    apply Apply.Equation4468_implies_Equation4441 at h
    apply Apply.Equation4441_implies_Equation4434 at h
    apply Apply.Equation4434_implies_Equation4433 at h
    apply h
  have eq1852 (x y z : G) : x = (x ∘ (y ∘ x)) ∘ (y ∘ z) := by
    apply Apply.Equation1969_implies_Equation1852 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq1832 x]
  symm
  nth_rewrite 1 [← eq4433 x]
  nth_rewrite 1 [← eq1852 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq1832 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1969_implies_Equation2065 (G: Type _) [Magma G] (h: Equation1969 G) : Equation2065 G := by
  have eq1832 (x : G) : x = (x ∘ (x ∘ x)) ∘ (x ∘ x) := by
    apply Apply.Equation1969_implies_Equation1852 at h
    apply Apply.Equation1852_implies_Equation1833 at h
    apply Apply.Equation1833_implies_Equation1832 at h
    apply h
  have eq4436 (x y : G) : x ∘ (y ∘ x) = (x ∘ y) ∘ y := by
    apply RewriteHypothesisAndGoal.Equation1969_implies_Equation4582 at h
    apply Apply.Equation4582_implies_Equation4468 at h
    apply Apply.Equation4468_implies_Equation4441 at h
    apply Apply.Equation4441_implies_Equation4437 at h
    apply Apply.Equation4437_implies_Equation4436 at h
    apply h
  have eq1852 (x y z : G) : x = (x ∘ (y ∘ x)) ∘ (y ∘ z) := by
    apply Apply.Equation1969_implies_Equation1852 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq1832 x]
  symm
  nth_rewrite 1 [← eq4436 x]
  nth_rewrite 1 [← eq1852 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq1832 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1995_implies_Equation9 (G: Type _) [Magma G] (h: Equation1995 G) : Equation9 G := by
  have eq23 (x : G) : x = (x ∘ x) ∘ x := by
    apply Run6.Equation1995_implies_Equation23 at h
    apply h
  have eq203 (x : G) : x = (x ∘ (x ∘ x)) ∘ x := by
    apply Run6.Equation1995_implies_Equation203 at h
    apply h
  have eq2036 (x y : G) : x = ((x ∘ x) ∘ x) ∘ (x ∘ y) := by
    apply Run6.Equation1995_implies_Equation168 at h
    apply Apply.Equation168_implies_Equation2164 at h
    apply Apply.Equation2164_implies_Equation2052 at h
    apply Apply.Equation2052_implies_Equation2036 at h
    apply h
  have eq307 (x : G) : x ∘ x = x ∘ (x ∘ x) := by
    apply RewriteHypothesisAndGoal.Equation1995_implies_Equation320 at h
    apply Apply.Equation320_implies_Equation310 at h
    apply Apply.Equation310_implies_Equation307 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [eq23 x]
  symm
  nth_rewrite 1 [eq203 x]
  symm
  nth_rewrite 1 [← eq2036 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq307 x]
  nth_rewrite 1 [← eq23 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1995_implies_Equation11 (G: Type _) [Magma G] (h: Equation1995 G) : Equation11 G := by
  have eq23 (x : G) : x = (x ∘ x) ∘ x := by
    apply Run6.Equation1995_implies_Equation23 at h
    apply h
  have eq203 (x : G) : x = (x ∘ (x ∘ x)) ∘ x := by
    apply Run6.Equation1995_implies_Equation203 at h
    apply h
  have eq2038 (x y : G) : x = ((x ∘ x) ∘ x) ∘ (y ∘ y) := by
    apply Run6.Equation1995_implies_Equation174 at h
    apply Apply.Equation174_implies_Equation2176 at h
    apply Apply.Equation2176_implies_Equation2058 at h
    apply Apply.Equation2058_implies_Equation2038 at h
    apply h
  have eq307 (x : G) : x ∘ x = x ∘ (x ∘ x) := by
    apply RewriteHypothesisAndGoal.Equation1995_implies_Equation320 at h
    apply Apply.Equation320_implies_Equation310 at h
    apply Apply.Equation310_implies_Equation307 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [eq23 x]
  symm
  nth_rewrite 1 [eq203 x]
  symm
  nth_rewrite 1 [← eq2038 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq307 x]
  nth_rewrite 1 [← eq23 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1995_implies_Equation34 (G: Type _) [Magma G] (h: Equation1995 G) : Equation34 G := by
  have eq203 (x : G) : x = (x ∘ (x ∘ x)) ∘ x := by
    apply Run6.Equation1995_implies_Equation203 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Run6.Equation1995_implies_Equation70 at h
    apply Apply.Equation70_implies_Equation50 at h
    apply Apply.Equation50_implies_Equation47 at h
    apply h
  have eq307 (x : G) : x ∘ x = x ∘ (x ∘ x) := by
    apply RewriteHypothesisAndGoal.Equation1995_implies_Equation320 at h
    apply Apply.Equation320_implies_Equation310 at h
    apply Apply.Equation310_implies_Equation307 at h
    apply h
  have eq1552 (x y z : G) : x = (y ∘ z) ∘ (x ∘ (x ∘ x)) := by
    apply Run6.Equation1995_implies_Equation70 at h
    apply Apply.Equation70_implies_Equation1567 at h
    apply Apply.Equation1567_implies_Equation1552 at h
    apply h
  have eq23 (x : G) : x = (x ∘ x) ∘ x := by
    apply Run6.Equation1995_implies_Equation23 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq203 x]
  symm
  nth_rewrite 1 [eq47 x]
  nth_rewrite 1 [← eq307 x]
  nth_rewrite 1 [← eq1552 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq307 x]
  nth_rewrite 1 [← eq23 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1604_implies_Equation1751 (G: Type _) [Magma G] (h: Equation1604 G) : Equation1751 G := by
  have eq8 (x : G) : x = x ∘ (x ∘ x) := by
    apply Run6.Equation1604_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation8 at h
    apply h
  have eq4276 (x y : G) : x ∘ (x ∘ x) = y ∘ (y ∘ y) := by
    apply RewriteHypothesisAndGoal.Equation1604_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3390 at h
    apply SimpleRewrites.Equation3390_implies_Equation3273 at h
    apply RewriteCombinations.Equation3273_implies_Equation4276 at h
    apply h
  have eq1739 (x y z : G) : x = (y ∘ y) ∘ ((z ∘ x) ∘ y) := by
    apply Run2.Equation1604_implies_Equation1807 at h
    apply Apply.Equation1807_implies_Equation1739 at h
    apply h
  have eq411 (x : G) : x = x ∘ (x ∘ (x ∘ (x ∘ x))) := by
    apply Run6.Equation1604_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation8 at h
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
  have eq8 (x : G) : x = x ∘ (x ∘ x) := by
    apply Run6.Equation1604_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation8 at h
    apply h
  have eq4276 (x y : G) : x ∘ (x ∘ x) = y ∘ (y ∘ y) := by
    apply RewriteHypothesisAndGoal.Equation1604_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3390 at h
    apply SimpleRewrites.Equation3390_implies_Equation3273 at h
    apply RewriteCombinations.Equation3273_implies_Equation4276 at h
    apply h
  have eq1756 (x y z : G) : x = (y ∘ z) ∘ ((x ∘ x) ∘ y) := by
    apply Run2.Equation1604_implies_Equation1807 at h
    apply Apply.Equation1807_implies_Equation1756 at h
    apply h
  have eq411 (x : G) : x = x ∘ (x ∘ (x ∘ (x ∘ x))) := by
    apply Run6.Equation1604_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation8 at h
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
  have eq8 (x : G) : x = x ∘ (x ∘ x) := by
    apply Run6.Equation1604_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation8 at h
    apply h
  have eq4276 (x y : G) : x ∘ (x ∘ x) = y ∘ (y ∘ y) := by
    apply RewriteHypothesisAndGoal.Equation1604_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3390 at h
    apply SimpleRewrites.Equation3390_implies_Equation3273 at h
    apply RewriteCombinations.Equation3273_implies_Equation4276 at h
    apply h
  have eq1773 (x y z : G) : x = (y ∘ z) ∘ ((y ∘ x) ∘ y) := by
    apply Run2.Equation1604_implies_Equation1807 at h
    apply Apply.Equation1807_implies_Equation1773 at h
    apply h
  have eq411 (x : G) : x = x ∘ (x ∘ (x ∘ (x ∘ x))) := by
    apply Run6.Equation1604_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation8 at h
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
  have eq8 (x : G) : x = x ∘ (x ∘ x) := by
    apply Run6.Equation1604_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation8 at h
    apply h
  have eq4276 (x y : G) : x ∘ (x ∘ x) = y ∘ (y ∘ y) := by
    apply RewriteHypothesisAndGoal.Equation1604_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3390 at h
    apply SimpleRewrites.Equation3390_implies_Equation3273 at h
    apply RewriteCombinations.Equation3273_implies_Equation4276 at h
    apply h
  have eq1790 (x y z : G) : x = (y ∘ z) ∘ ((z ∘ x) ∘ y) := by
    apply Run2.Equation1604_implies_Equation1807 at h
    apply Apply.Equation1807_implies_Equation1790 at h
    apply h
  have eq411 (x : G) : x = x ∘ (x ∘ (x ∘ (x ∘ x))) := by
    apply Run6.Equation1604_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation8 at h
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
  have eq3 (x : G) : x = x ∘ x := by
    apply Run6.Equation1604_implies_Equation3 at h
    apply h
  have eq40 (x y : G) : x ∘ x = y ∘ y := by
    apply RewriteHypothesisAndGoal.Equation1604_implies_Equation41 at h
    apply Subgraph.Equation41_implies_Equation40 at h
    apply h
  have eq47 (x : G) : x = x ∘ (x ∘ (x ∘ x)) := by
    apply Run6.Equation1604_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  have eq1807 (x y z w : G) : x = (y ∘ z) ∘ ((w ∘ x) ∘ y) := by
    apply Run2.Equation1604_implies_Equation1807 at h
    apply h
  have eq411 (x : G) : x = x ∘ (x ∘ (x ∘ (x ∘ x))) := by
    apply Run6.Equation1604_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation8 at h
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
@[equational_result]
theorem Equation1918_implies_Equation1854 (G: Type _) [Magma G] (h: Equation1918 G) : Equation1854 G := by
  have eq4283 (x y : G) : x ∘ (x ∘ y) = x ∘ (y ∘ x) := by
    apply RewriteHypothesisAndGoal.Equation1918_implies_Equation4379 at h
    apply Apply.Equation4379_implies_Equation4364 at h
    apply Apply.Equation4364_implies_Equation4283 at h
    apply h
  have eq1832 (x : G) : x = (x ∘ (x ∘ x)) ∘ (x ∘ x) := by
    apply Apply.Equation1918_implies_Equation1844 at h
    apply Apply.Equation1844_implies_Equation1834 at h
    apply Apply.Equation1834_implies_Equation1832 at h
    apply h
  have eq1844 (x y z : G) : x = (x ∘ (x ∘ y)) ∘ (z ∘ y) := by
    apply Apply.Equation1918_implies_Equation1844 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4283 x]
  symm
  nth_rewrite 1 [eq1832 x]
  symm
  nth_rewrite 1 [← eq1844 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq1832 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1918_implies_Equation1864 (G: Type _) [Magma G] (h: Equation1918 G) : Equation1864 G := by
  have eq1832 (x : G) : x = (x ∘ (x ∘ x)) ∘ (x ∘ x) := by
    apply Apply.Equation1918_implies_Equation1844 at h
    apply Apply.Equation1844_implies_Equation1834 at h
    apply Apply.Equation1834_implies_Equation1832 at h
    apply h
  have eq4284 (x y : G) : x ∘ (x ∘ y) = x ∘ (y ∘ y) := by
    apply RewriteHypothesisAndGoal.Equation1918_implies_Equation4379 at h
    apply Apply.Equation4379_implies_Equation4313 at h
    apply Apply.Equation4313_implies_Equation4289 at h
    apply Apply.Equation4289_implies_Equation4285 at h
    apply Apply.Equation4285_implies_Equation4284 at h
    apply h
  have eq1844 (x y z : G) : x = (x ∘ (x ∘ y)) ∘ (z ∘ y) := by
    apply Apply.Equation1918_implies_Equation1844 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq1832 x]
  symm
  nth_rewrite 1 [← eq4284 x]
  nth_rewrite 1 [← eq1844 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq1832 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1918_implies_Equation2057 (G: Type _) [Magma G] (h: Equation1918 G) : Equation2057 G := by
  have eq1832 (x : G) : x = (x ∘ (x ∘ x)) ∘ (x ∘ x) := by
    apply Apply.Equation1918_implies_Equation1844 at h
    apply Apply.Equation1844_implies_Equation1834 at h
    apply Apply.Equation1834_implies_Equation1832 at h
    apply h
  have eq4398 (x y : G) : x ∘ (x ∘ y) = (x ∘ y) ∘ x := by
    apply RewriteHypothesisAndGoal.Equation1918_implies_Equation4582 at h
    apply Apply.Equation4582_implies_Equation4431 at h
    apply Apply.Equation4431_implies_Equation4404 at h
    apply Apply.Equation4404_implies_Equation4400 at h
    apply Apply.Equation4400_implies_Equation4398 at h
    apply h
  have eq1844 (x y z : G) : x = (x ∘ (x ∘ y)) ∘ (z ∘ y) := by
    apply Apply.Equation1918_implies_Equation1844 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq1832 x]
  symm
  nth_rewrite 1 [← eq4398 x]
  nth_rewrite 1 [← eq1844 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq1832 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1918_implies_Equation2067 (G: Type _) [Magma G] (h: Equation1918 G) : Equation2067 G := by
  have eq1832 (x : G) : x = (x ∘ (x ∘ x)) ∘ (x ∘ x) := by
    apply Apply.Equation1918_implies_Equation1844 at h
    apply Apply.Equation1844_implies_Equation1834 at h
    apply Apply.Equation1834_implies_Equation1832 at h
    apply h
  have eq4399 (x y : G) : x ∘ (x ∘ y) = (x ∘ y) ∘ y := by
    apply RewriteHypothesisAndGoal.Equation1918_implies_Equation4582 at h
    apply Apply.Equation4582_implies_Equation4431 at h
    apply Apply.Equation4431_implies_Equation4404 at h
    apply Apply.Equation4404_implies_Equation4400 at h
    apply Apply.Equation4400_implies_Equation4399 at h
    apply h
  have eq1844 (x y z : G) : x = (x ∘ (x ∘ y)) ∘ (z ∘ y) := by
    apply Apply.Equation1918_implies_Equation1844 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq1832 x]
  symm
  nth_rewrite 1 [← eq4399 x]
  nth_rewrite 1 [← eq1844 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq1832 x]
  apply h
  repeat assumption
