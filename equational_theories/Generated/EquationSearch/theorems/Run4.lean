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
import Mathlib.Tactic

namespace Run4
@[equational_result]
theorem Equation48_implies_Equation615 (G: Type _) [Magma G] (h: Equation48 G) : Equation615 G := by
  have eq375 (x y : G) : x ∘ y = (x ∘ x) ∘ y := by
    apply Run3.Equation48_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation375 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq375]
  symm
  apply h
@[equational_result]
theorem Equation57_implies_Equation61 (G: Type _) [Magma G] (h: Equation57 G) : Equation61 G := by
  have eq3267 (x y z w : G) : x ∘ x = x ∘ (y ∘ (z ∘ w)) := by
    apply Run3.Equation57_implies_Equation3336 at h
    apply Apply.Equation3336_implies_Equation3335 at h
    apply SimpleRewrites.Equation3335_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply RewriteHypothesisAndGoal.Equation322_implies_Equation331 at h
    apply SimpleRewrites.Equation331_implies_Equation311 at h
    apply Apply.Equation311_implies_Equation3267 at h
    apply h
  have eq3263 (x y z : G) : x ∘ x = x ∘ (y ∘ (y ∘ z)) := by
    apply Run3.Equation57_implies_Equation3336 at h
    apply Apply.Equation3336_implies_Equation3335 at h
    apply SimpleRewrites.Equation3335_implies_Equation3305 at h
    apply RewriteHypothesisAndGoal.Equation3305_implies_Equation324 at h
    apply Apply.Equation324_implies_Equation322 at h
    apply RewriteHypothesisAndGoal.Equation322_implies_Equation331 at h
    apply SimpleRewrites.Equation331_implies_Equation311 at h
    apply Apply.Equation311_implies_Equation3267 at h
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
  have eq3304 (x y z w u : G) : x ∘ x = y ∘ (z ∘ (w ∘ u)) := by
    apply Run3.Equation64_implies_Equation3403 at h
    apply Apply.Equation3403_implies_Equation3402 at h
    apply RewriteCombinations.Equation3402_implies_Equation3357 at h
    apply RewriteCombinations.Equation3357_implies_Equation3400 at h
    apply NthRewrites.Equation3400_implies_Equation3586 at h
    apply NthRewrites.Equation3586_implies_Equation3841 at h
    apply NthRewrites.Equation3841_implies_Equation3861 at h
    apply Apply.Equation3861_implies_Equation3858 at h
    apply Constant.Equation3858_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply RewriteCombinations.Equation314_implies_Equation3291 at h
    apply Run1.Equation3291_implies_Equation3304 at h
    apply h
  have eq3270 (x y z : G) : x ∘ x = y ∘ (x ∘ (x ∘ z)) := by
    apply Run3.Equation64_implies_Equation3403 at h
    apply Apply.Equation3403_implies_Equation3402 at h
    apply RewriteCombinations.Equation3402_implies_Equation3357 at h
    apply RewriteCombinations.Equation3357_implies_Equation3400 at h
    apply NthRewrites.Equation3400_implies_Equation3586 at h
    apply NthRewrites.Equation3586_implies_Equation3841 at h
    apply NthRewrites.Equation3841_implies_Equation3861 at h
    apply Apply.Equation3861_implies_Equation3858 at h
    apply Constant.Equation3858_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply Run1.Equation314_implies_Equation317 at h
    apply RewriteHypothesis.Equation317_implies_Equation3299 at h
    apply Apply.Equation3299_implies_Equation3270 at h
    apply h
  intro x y z w u
  symm
  nth_rewrite 1 [← eq3304]
  nth_rewrite 1 [eq3270]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation67_implies_Equation681 (G: Type _) [Magma G] (h: Equation67 G) : Equation681 G := by
  have eq375 (x y : G) : x ∘ y = (x ∘ x) ∘ y := by
    apply Apply.Equation67_implies_Equation48 at h
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
theorem Equation270_implies_Equation2899 (G: Type _) [Magma G] (h: Equation270 G) : Equation2899 G := by
  have eq326 (x y : G) : x ∘ y = x ∘ (y ∘ y) := by
    apply Run3.Equation270_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation326 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq326]
  symm
  apply h
@[equational_result]
theorem Equation272_implies_Equation98 (G: Type _) [Magma G] (h: Equation272 G) : Equation98 G := by
  have eq3304 (x y z w u : G) : x ∘ x = y ∘ (z ∘ (w ∘ u)) := by
    apply Run3.Equation272_implies_Equation4193 at h
    apply RewriteCombinations.Equation4193_implies_Equation4191 at h
    apply RewriteCombinations.Equation4191_implies_Equation4156 at h
    apply NthRewrites.Equation4156_implies_Equation3956 at h
    apply NthRewrites.Equation3956_implies_Equation4267 at h
    apply Constant.Equation4267_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation314 at h
    apply RewriteCombinations.Equation314_implies_Equation3291 at h
    apply Run1.Equation3291_implies_Equation3304 at h
    apply h
  have eq4082 (x y z : G) : x ∘ x = ((y ∘ x) ∘ x) ∘ z := by
    apply Run3.Equation272_implies_Equation4193 at h
    apply RewriteCombinations.Equation4193_implies_Equation4191 at h
    apply RewriteCombinations.Equation4191_implies_Equation4156 at h
    apply NthRewrites.Equation4156_implies_Equation3956 at h
    apply NthRewrites.Equation3956_implies_Equation4267 at h
    apply Constant.Equation4267_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4203 at h
    apply Apply.Equation4203_implies_Equation4199 at h
    apply RewriteCombinations.Equation4199_implies_Equation4202 at h
    apply NthRewrites.Equation4202_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation366 at h
    apply Run1.Equation366_implies_Equation372 at h
    apply RewriteHypothesis.Equation372_implies_Equation4111 at h
    apply Apply.Equation4111_implies_Equation4082 at h
    apply h
  intro x y z w u
  symm
  nth_rewrite 1 [← eq3304]
  nth_rewrite 1 [eq4082]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation276_implies_Equation4086 (G: Type _) [Magma G] (h: Equation276 G) : Equation4086 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation276_implies_Equation270 at h
    apply Run3.Equation270_implies_Equation3 at h
    apply h
  intro x y z
  nth_rewrite 1 [← eq3]
  apply h
@[equational_result]
theorem Equation276_implies_Equation2905 (G: Type _) [Magma G] (h: Equation276 G) : Equation2905 G := by
  have eq326 (x y : G) : x ∘ y = x ∘ (y ∘ y) := by
    apply Apply.Equation276_implies_Equation270 at h
    apply Run3.Equation270_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation326 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq326]
  symm
  apply h
@[equational_result]
theorem Equation290_implies_Equation4100 (G: Type _) [Magma G] (h: Equation290 G) : Equation4100 G := by
  have eq3 (x : G) : x = x ∘ x := by
    apply Apply.Equation290_implies_Equation270 at h
    apply Run3.Equation270_implies_Equation3 at h
    apply h
  intro x y z
  nth_rewrite 1 [← eq3]
  apply h
@[equational_result]
theorem Equation292_implies_Equation3009 (G: Type _) [Magma G] (h: Equation292 G) : Equation3009 G := by
  have eq326 (x y : G) : x ∘ y = x ∘ (y ∘ y) := by
    apply Apply.Equation292_implies_Equation270 at h
    apply Run3.Equation270_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation3715 at h
    apply NthRewrites.Equation3715_implies_Equation326 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq326]
  symm
  apply h
@[equational_result]
theorem Equation298_implies_Equation5 (G: Type _) [Magma G] (h: Equation298 G) : Equation5 G := by
  have eq4146 (x y z : G) : x ∘ y = ((x ∘ z) ∘ z) ∘ y := by
    apply Run3.Equation298_implies_Equation4258 at h
    apply SimpleRewrites.Equation4258_implies_Equation4234 at h
    apply SimpleRewrites.Equation4234_implies_Equation4168 at h
    apply RewriteHypothesisAndGoal.Equation4168_implies_Equation4060 at h
    apply Apply.Equation4060_implies_Equation4055 at h
    apply SimpleRewrites.Equation4055_implies_Equation4031 at h
    apply SimpleRewrites.Equation4031_implies_Equation3965 at h
    apply RewriteHypothesisAndGoal.Equation3965_implies_Equation391 at h
    apply Apply.Equation391_implies_Equation388 at h
    apply RewriteHypothesisAndGoal.Equation388_implies_Equation45 at h
    apply Apply.Equation45_implies_Equation381 at h
    apply RewriteHypothesis.Equation381_implies_Equation4150 at h
    apply Apply.Equation4150_implies_Equation4146 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [eq4146]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3344_implies_Equation4178 (G: Type _) [Magma G] (h: Equation3344 G) : Equation4178 G := by
  have eq4138 (x y z : G) : x ∘ y = ((x ∘ z) ∘ x) ∘ y := by
    apply Run3.Equation3344_implies_Equation3348 at h
    apply NthRewrites.Equation3348_implies_Equation395 at h
    apply Apply.Equation395_implies_Equation4243 at h
    apply Apply.Equation4243_implies_Equation4138 at h
    apply h
  have eq3320 (x y z : G) : x ∘ y = x ∘ (y ∘ (y ∘ z)) := by
    apply Run3.Equation3344_implies_Equation3320 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4138]
  nth_rewrite 1 [eq3320]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3344_implies_Equation4212 (G: Type _) [Magma G] (h: Equation3344 G) : Equation4212 G := by
  have eq4192 (x y z : G) : x ∘ y = ((z ∘ x) ∘ x) ∘ y := by
    apply Run3.Equation3344_implies_Equation3348 at h
    apply NthRewrites.Equation3348_implies_Equation395 at h
    apply Apply.Equation395_implies_Equation4243 at h
    apply Apply.Equation4243_implies_Equation4192 at h
    apply h
  have eq3320 (x y z : G) : x ∘ y = x ∘ (y ∘ (y ∘ z)) := by
    apply Run3.Equation3344_implies_Equation3320 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4192]
  nth_rewrite 1 [eq3320]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3344_implies_Equation4195 (G: Type _) [Magma G] (h: Equation3344 G) : Equation4195 G := by
  have eq4209 (x y z : G) : x ∘ y = ((z ∘ y) ∘ x) ∘ y := by
    apply Run3.Equation3344_implies_Equation3348 at h
    apply NthRewrites.Equation3348_implies_Equation395 at h
    apply Apply.Equation395_implies_Equation4243 at h
    apply Apply.Equation4243_implies_Equation4209 at h
    apply h
  have eq3320 (x y z : G) : x ∘ y = x ∘ (y ∘ (y ∘ z)) := by
    apply Run3.Equation3344_implies_Equation3320 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4209]
  nth_rewrite 1 [eq3320]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3344_implies_Equation4229 (G: Type _) [Magma G] (h: Equation3344 G) : Equation4229 G := by
  have eq4226 (x y z : G) : x ∘ y = ((z ∘ z) ∘ x) ∘ y := by
    apply Run3.Equation3344_implies_Equation3348 at h
    apply NthRewrites.Equation3348_implies_Equation395 at h
    apply Apply.Equation395_implies_Equation4243 at h
    apply Apply.Equation4243_implies_Equation4226 at h
    apply h
  have eq3320 (x y z : G) : x ∘ y = x ∘ (y ∘ (y ∘ z)) := by
    apply Run3.Equation3344_implies_Equation3320 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq4226]
  nth_rewrite 1 [eq3320]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3344_implies_Equation4247 (G: Type _) [Magma G] (h: Equation3344 G) : Equation4247 G := by
  have eq4243 (x y z w : G) : x ∘ y = ((z ∘ w) ∘ x) ∘ y := by
    apply Run3.Equation3344_implies_Equation3348 at h
    apply NthRewrites.Equation3348_implies_Equation395 at h
    apply Apply.Equation395_implies_Equation4243 at h
    apply h
  have eq3320 (x y z : G) : x ∘ y = x ∘ (y ∘ (y ∘ z)) := by
    apply Run3.Equation3344_implies_Equation3320 at h
    apply h
  intro x y z w
  symm
  nth_rewrite 1 [← eq4243]
  nth_rewrite 1 [eq3320]
  symm
  apply h
  repeat assumption
