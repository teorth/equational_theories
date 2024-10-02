import equational_theories.Generated.SimpleRewrites
import equational_theories.Generated.Constant
import equational_theories.Generated.Singleton
import equational_theories.Generated.TrivialBruteforce
import equational_theories.Generated.FinitePoly
import equational_theories.Subgraph
import equational_theories.AllEquations
import equational_theories.Generated.EquationSearch.theorems.Run1
import equational_theories.Generated.EquationSearch.theorems.Run2
import equational_theories.Generated.EquationSearch.theorems.Run3
import equational_theories.Generated.EquationSearch.theorems.Run4
import Mathlib.Tactic

namespace Run5
@[equational_result]
theorem Equation14_implies_Equation620 (G: Type _) [Magma G] (h: Equation14 G) : Equation620 G := by
  have eq4435 (x y : G) : x ∘ (y ∘ x) = (x ∘ y) ∘ x := by
    apply Subgraph.Equation14_implies_Equation29 at h
    apply Run1.Equation29_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4435 at h
    apply h
  have eq417 (x y : G) : x = x ∘ (x ∘ (y ∘ (x ∘ y))) := by
    apply RewriteHypothesis.Equation14_implies_Equation489 at h
    apply Apply.Equation489_implies_Equation417 at h
    apply h
  intro x y
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq4435]
  nth_rewrite 1 [← eq417]
  apply h
  repeat assumption
@[equational_result]
theorem Equation14_implies_Equation1241 (G: Type _) [Magma G] (h: Equation14 G) : Equation1241 G := by
  have eq4435 (x y : G) : x ∘ (y ∘ x) = (x ∘ y) ∘ x := by
    apply Subgraph.Equation14_implies_Equation29 at h
    apply Run1.Equation29_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4435 at h
    apply h
  have eq1038 (x y : G) : x = x ∘ ((y ∘ (x ∘ y)) ∘ x) := by
    apply RewriteHypothesis.Equation14_implies_Equation1155 at h
    apply Apply.Equation1155_implies_Equation1038 at h
    apply h
  intro x y
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq4435]
  nth_rewrite 1 [← eq1038]
  apply h
  repeat assumption
@[equational_result]
theorem Equation14_implies_Equation1432 (G: Type _) [Magma G] (h: Equation14 G) : Equation1432 G := by
  have eq4435 (x y : G) : x ∘ (y ∘ x) = (x ∘ y) ∘ x := by
    apply Subgraph.Equation14_implies_Equation29 at h
    apply Run1.Equation29_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4435 at h
    apply h
  have eq1635 (x y : G) : x = (x ∘ x) ∘ ((y ∘ x) ∘ y) := by
    apply Subgraph.Equation14_implies_Equation29 at h
    apply RewriteHypothesis.Equation29_implies_Equation1707 at h
    apply Apply.Equation1707_implies_Equation1635 at h
    apply h
  intro x y
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [eq4435]
  nth_rewrite 1 [← eq1635]
  apply h
  repeat assumption
@[equational_result]
theorem Equation14_implies_Equation2256 (G: Type _) [Magma G] (h: Equation14 G) : Equation2256 G := by
  have eq4435 (x y : G) : x ∘ (y ∘ x) = (x ∘ y) ∘ x := by
    apply Subgraph.Equation14_implies_Equation29 at h
    apply Run1.Equation29_implies_Equation4458 at h
    apply Apply.Equation4458_implies_Equation4435 at h
    apply h
  have eq2459 (x y : G) : x = (x ∘ ((y ∘ x) ∘ y)) ∘ x := by
    apply Subgraph.Equation14_implies_Equation29 at h
    apply RewriteHypothesis.Equation29_implies_Equation2576 at h
    apply Apply.Equation2576_implies_Equation2459 at h
    apply h
  intro x y
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [eq4435]
  nth_rewrite 1 [← eq2459]
  apply h
  repeat assumption
@[equational_result]
theorem Equation51_implies_Equation9 (G: Type _) [Magma G] (h: Equation51 G) : Equation9 G := by
  have eq326 (x y : G) : x ∘ y = x ∘ (y ∘ y) := by
    apply Apply.Equation51_implies_Equation48 at h
    apply Run3.Equation48_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation326 at h
    apply h
  have eq3256 (x y : G) : x ∘ x = x ∘ (x ∘ (y ∘ y)) := by
    apply Run3.Equation51_implies_Equation3257 at h
    apply Apply.Equation3257_implies_Equation3256 at h
    apply h
  have eq3257 (x y z : G) : x ∘ x = x ∘ (x ∘ (y ∘ z)) := by
    apply Run3.Equation51_implies_Equation3257 at h
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
theorem Equation54_implies_Equation4432 (G: Type _) [Magma G] (h: Equation54 G) : Equation4432 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation54_implies_Equation48 at h
    apply Run3.Equation48_implies_Equation3 at h
    apply h
  have eq359 (x : G) : x ∘ x = (x ∘ x) ∘ x := by
    apply Apply.Equation54_implies_Equation48 at h
    apply Run3.Equation48_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation375 at h
    apply Apply.Equation375_implies_Equation359 at h
    apply h
  have eq52 (x y : G) : x = x ∘ (y ∘ (x ∘ x)) := by
    apply Apply.Equation54_implies_Equation52 at h
    apply h
  have eq3260 (x y z : G) : x ∘ x = x ∘ (y ∘ (x ∘ z)) := by
    apply Run3.Equation54_implies_Equation3260 at h
    apply h
  intro x y
  nth_rewrite 2 [eq3 x]
  symm
  nth_rewrite 1 [← eq359]
  symm
  nth_rewrite 1 [← eq52]
  symm
  nth_rewrite 1 [eq3260]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation54_implies_Equation10 (G: Type _) [Magma G] (h: Equation54 G) : Equation10 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation54_implies_Equation48 at h
    apply Run3.Equation48_implies_Equation3 at h
    apply h
  have eq3258 (x y : G) : x ∘ x = x ∘ (y ∘ (x ∘ x)) := by
    apply Run3.Equation54_implies_Equation3260 at h
    apply Apply.Equation3260_implies_Equation3258 at h
    apply h
  have eq3260 (x y z : G) : x ∘ x = x ∘ (y ∘ (x ∘ z)) := by
    apply Run3.Equation54_implies_Equation3260 at h
    apply h
  intro x y
  symm
  nth_rewrite 2 [eq3 x]
  nth_rewrite 1 [← eq3258]
  nth_rewrite 1 [eq3260]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation54_implies_Equation309 (G: Type _) [Magma G] (h: Equation54 G) : Equation309 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation54_implies_Equation48 at h
    apply Run3.Equation48_implies_Equation3 at h
    apply h
  have eq52 (x y : G) : x = x ∘ (y ∘ (x ∘ x)) := by
    apply Apply.Equation54_implies_Equation52 at h
    apply h
  intro x y
  symm
  nth_rewrite 2 [eq3 x]
  nth_rewrite 1 [← eq52]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq3]
  apply h
  repeat assumption
@[equational_result]
theorem Equation54_implies_Equation9 (G: Type _) [Magma G] (h: Equation54 G) : Equation9 G := by
  have eq3722 (x y : G) : x ∘ y = (x ∘ y) ∘ (x ∘ y) := by
    apply Apply.Equation54_implies_Equation48 at h
    apply Run3.Equation48_implies_Equation3 at h
    apply Apply.Equation3_implies_Equation3722 at h
    apply h
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation54_implies_Equation48 at h
    apply Run3.Equation48_implies_Equation3 at h
    apply h
  have eq823 (x y : G) : x = x ∘ ((x ∘ y) ∘ (x ∘ y)) := by
    apply Apply.Equation54_implies_Equation855 at h
    apply Apply.Equation855_implies_Equation824 at h
    apply Apply.Equation824_implies_Equation823 at h
    apply h
  intro x y
  symm
  nth_rewrite 2 [eq3722]
  symm
  nth_rewrite 1 [eq3 x]
  symm
  nth_rewrite 1 [← eq823]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq3]
  apply h
  repeat assumption
@[equational_result]
theorem Equation54_implies_Equation4286 (G: Type _) [Magma G] (h: Equation54 G) : Equation4286 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation54_implies_Equation48 at h
    apply Run3.Equation48_implies_Equation3 at h
    apply h
  have eq3722 (x y : G) : x ∘ y = (x ∘ y) ∘ (x ∘ y) := by
    apply Apply.Equation54_implies_Equation48 at h
    apply Run3.Equation48_implies_Equation3 at h
    apply Apply.Equation3_implies_Equation3722 at h
    apply h
  have eq3258 (x y : G) : x ∘ x = x ∘ (y ∘ (x ∘ x)) := by
    apply Run3.Equation54_implies_Equation3260 at h
    apply Apply.Equation3260_implies_Equation3258 at h
    apply h
  have eq823 (x y : G) : x = x ∘ ((x ∘ y) ∘ (x ∘ y)) := by
    apply Apply.Equation54_implies_Equation855 at h
    apply Apply.Equation855_implies_Equation824 at h
    apply Apply.Equation824_implies_Equation823 at h
    apply h
  have eq3260 (x y z : G) : x ∘ x = x ∘ (y ∘ (x ∘ z)) := by
    apply Run3.Equation54_implies_Equation3260 at h
    apply h
  intro x y z
  symm
  nth_rewrite 2 [eq3 x]
  symm
  nth_rewrite 2 [eq3722]
  symm
  nth_rewrite 1 [← eq3258]
  symm
  nth_rewrite 1 [← eq823]
  symm
  nth_rewrite 1 [eq3260]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation57_implies_Equation4 (G: Type _) [Magma G] (h: Equation57 G) : Equation4 G := by
  have eq3320 (x y z : G) : x ∘ y = x ∘ (y ∘ (y ∘ z)) := by
    apply Run3.Equation57_implies_Equation3336 at h
    apply Apply.Equation3336_implies_Equation3335 at h
    apply SimpleRewrites.Equation3335_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply RewriteHypothesisAndGoal.Equation322_implies_Equation42 at h
    apply Apply.Equation42_implies_Equation327 at h
    apply Apply.Equation327_implies_Equation3324 at h
    apply Apply.Equation3324_implies_Equation3320 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [eq3320]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation54_implies_Equation631 (G: Type _) [Magma G] (h: Equation54 G) : Equation631 G := by
  have eq375 (x y : G) : x ∘ y = (x ∘ x) ∘ y := by
    apply Apply.Equation54_implies_Equation48 at h
    apply Run3.Equation48_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation375 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq375]
  symm
  apply h
@[equational_result]
theorem Equation74_implies_Equation705 (G: Type _) [Magma G] (h: Equation74 G) : Equation705 G := by
  have eq375 (x y : G) : x ∘ y = (x ∘ x) ∘ y := by
    apply Apply.Equation74_implies_Equation48 at h
    apply Run3.Equation48_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation375 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq375]
  symm
  apply h
@[equational_result]
theorem Equation290_implies_Equation28 (G: Type _) [Magma G] (h: Equation290 G) : Equation28 G := by
  have eq375 (x y : G) : x ∘ y = (x ∘ x) ∘ y := by
    apply Apply.Equation290_implies_Equation270 at h
    apply Run3.Equation270_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation375 at h
    apply h
  have eq4090 (x y : G) : x ∘ x = ((y ∘ y) ∘ x) ∘ x := by
    apply Run4.Equation290_implies_Equation4100 at h
    apply Apply.Equation4100_implies_Equation4090 at h
    apply h
  have eq4100 (x y z : G) : x ∘ x = ((y ∘ z) ∘ x) ∘ x := by
    apply Run4.Equation290_implies_Equation4100 at h
    apply h
  intro x y
  symm
  nth_rewrite 2 [eq375]
  nth_rewrite 1 [← eq4090]
  nth_rewrite 1 [eq4100]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation292_implies_Equation1123 (G: Type _) [Magma G] (h: Equation292 G) : Equation1123 G := by
  have eq23 (x : G) : x = (x ∘ x) ∘ x := by
    apply Apply.Equation292_implies_Equation270 at h
    apply Run3.Equation270_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation23 at h
    apply h
  have eq4591 (x y : G) : (x ∘ x) ∘ x = (y ∘ y) ∘ y := by
    apply Run3.Equation292_implies_Equation4102 at h
    apply RewriteCombinations.Equation4102_implies_Equation4591 at h
    apply h
  have eq1020 (x : G) : x = x ∘ ((x ∘ (x ∘ x)) ∘ x) := by
    apply Apply.Equation292_implies_Equation270 at h
    apply Run3.Equation270_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation8 at h
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
theorem Equation292_implies_Equation1326 (G: Type _) [Magma G] (h: Equation292 G) : Equation1326 G := by
  have eq23 (x : G) : x = (x ∘ x) ∘ x := by
    apply Apply.Equation292_implies_Equation270 at h
    apply Run3.Equation270_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation23 at h
    apply h
  have eq4591 (x y : G) : (x ∘ x) ∘ x = (y ∘ y) ∘ y := by
    apply Run3.Equation292_implies_Equation4102 at h
    apply RewriteCombinations.Equation4102_implies_Equation4591 at h
    apply h
  have eq1223 (x : G) : x = x ∘ (((x ∘ x) ∘ x) ∘ x) := by
    apply Apply.Equation292_implies_Equation270 at h
    apply Run3.Equation270_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation1223 at h
    apply h
  intro x y
  nth_rewrite 1 [eq23 x]
  nth_rewrite 1 [← eq4591]
  symm
  nth_rewrite 1 [← eq1223]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq23]
  apply h
  repeat assumption
@[equational_result]
theorem Equation67_implies_Equation920 (G: Type _) [Magma G] (h: Equation67 G) : Equation920 G := by
  have eq8 (x : G) : x = x ∘ (x ∘ x) := by
    apply Apply.Equation67_implies_Equation48 at h
    apply Run3.Equation48_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation8 at h
    apply h
  have eq4276 (x y : G) : x ∘ (x ∘ x) = y ∘ (y ∘ y) := by
    apply Run3.Equation67_implies_Equation3273 at h
    apply RewriteCombinations.Equation3273_implies_Equation4276 at h
    apply h
  have eq817 (x : G) : x = x ∘ ((x ∘ x) ∘ (x ∘ x)) := by
    apply Apply.Equation67_implies_Equation48 at h
    apply Run3.Equation48_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation817 at h
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
theorem Equation3136_implies_Equation98 (G: Type _) [Magma G] (h: Equation3136 G) : Equation98 G := by
  have eq2847 (x : G) : x = ((x ∘ (x ∘ x)) ∘ x) ∘ x := by
    apply Run2.Equation3136_implies_Equation2933 at h
    apply Apply.Equation2933_implies_Equation2859 at h
    apply Apply.Equation2859_implies_Equation2849 at h
    apply Apply.Equation2849_implies_Equation2847 at h
    apply h
  have eq3304 (x y z w u : G) : x ∘ x = y ∘ (z ∘ (w ∘ u)) := by
    apply RewriteHypothesisAndGoal.Equation3136_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply RewriteCombinations.Equation314_implies_Equation3291 at h
    apply Run1.Equation3291_implies_Equation3304 at h
    apply h
  have eq4067 (x y : G) : x ∘ x = ((x ∘ x) ∘ y) ∘ x := by
    apply RewriteHypothesisAndGoal.Equation3136_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4186 at h
    apply Apply.Equation4186_implies_Equation4160 at h
    apply Apply.Equation4160_implies_Equation4067 at h
    apply h
  have eq307 (x : G) : x ∘ x = x ∘ (x ∘ x) := by
    apply RewriteHypothesisAndGoal.Equation3136_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation337 at h
    apply Apply.Equation337_implies_Equation335 at h
    apply Apply.Equation335_implies_Equation307 at h
    apply h
  have eq2849 (x y : G) : x = ((x ∘ (x ∘ x)) ∘ y) ∘ x := by
    apply Run2.Equation3136_implies_Equation2933 at h
    apply Apply.Equation2933_implies_Equation2859 at h
    apply Apply.Equation2859_implies_Equation2849 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [eq2847 x]
  symm
  nth_rewrite 1 [← eq3304]
  nth_rewrite 1 [eq4067]
  nth_rewrite 1 [eq307]
  nth_rewrite 1 [← eq2849]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq2847]
  apply h
  repeat assumption
@[equational_result]
theorem Equation74_implies_Equation3416 (G: Type _) [Magma G] (h: Equation74 G) : Equation3416 G := by
  have eq3722 (x y : G) : x ∘ y = (x ∘ y) ∘ (x ∘ y) := by
    apply Apply.Equation74_implies_Equation48 at h
    apply Run3.Equation48_implies_Equation3 at h
    apply Apply.Equation3_implies_Equation3722 at h
    apply h
  have eq3665 (x y : G) : x ∘ x = (x ∘ y) ∘ (x ∘ y) := by
    apply Run3.Equation74_implies_Equation3280 at h
    apply RewriteCombinations.Equation3280_implies_Equation3665 at h
    apply h
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation74_implies_Equation48 at h
    apply Run3.Equation48_implies_Equation3 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq3722]
  nth_rewrite 1 [← eq3665]
  nth_rewrite 1 [← eq3]
  apply h
@[equational_result]
theorem Equation74_implies_Equation4 (G: Type _) [Magma G] (h: Equation74 G) : Equation4 G := by
  have eq411 (x : G) : x = x ∘ (x ∘ (x ∘ (x ∘ x))) := by
    apply Apply.Equation74_implies_Equation48 at h
    apply Run3.Equation48_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation8 at h
    apply RewriteHypothesis.Equation8_implies_Equation411 at h
    apply h
  have eq3722 (x y : G) : x ∘ y = (x ∘ y) ∘ (x ∘ y) := by
    apply Apply.Equation74_implies_Equation48 at h
    apply Run3.Equation48_implies_Equation3 at h
    apply Apply.Equation3_implies_Equation3722 at h
    apply h
  have eq3665 (x y : G) : x ∘ x = (x ∘ y) ∘ (x ∘ y) := by
    apply Run3.Equation74_implies_Equation3280 at h
    apply RewriteCombinations.Equation3280_implies_Equation3665 at h
    apply h
  have eq3280 (x y z : G) : x ∘ x = y ∘ (y ∘ (x ∘ z)) := by
    apply Run3.Equation74_implies_Equation3280 at h
    apply h
  intro x y
  nth_rewrite 1 [eq411 x]
  symm
  nth_rewrite 1 [eq3722]
  nth_rewrite 1 [← eq3665]
  nth_rewrite 1 [eq3280]
  symm
  nth_rewrite 1 [← eq411]
  apply h
  repeat assumption
