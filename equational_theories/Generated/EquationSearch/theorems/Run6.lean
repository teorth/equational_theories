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
import equational_theories.Generated.EquationSearch.theorems.Run5
import Mathlib.Tactic

namespace Run6
@[equational_result]
theorem Equation1973_implies_Equation1939 (G: Type _) [Magma G] (h: Equation1973 G) : Equation1939 G := by
  have eq1851 (x y : G) : x = (x ◇ (y ◇ x)) ◇ (y ◇ y) := by
    apply Apply.Equation1973_implies_Equation1855 at h
    apply Apply.Equation1855_implies_Equation1851 at h
    apply h
  have eq1894 (x y : G) : x = (y ◇ (x ◇ y)) ◇ (x ◇ x) := by
    apply Apply.Equation1973_implies_Equation1892 at h
    apply Run2.Equation1892_implies_Equation1902 at h
    apply Apply.Equation1902_implies_Equation1894 at h
    apply h
  have eq1832 (x : G) : x = (x ◇ (x ◇ x)) ◇ (x ◇ x) := by
    apply Apply.Equation1973_implies_Equation1855 at h
    apply Apply.Equation1855_implies_Equation1835 at h
    apply Apply.Equation1835_implies_Equation1832 at h
    apply h
  have eq1835 (x y : G) : x = (x ◇ (x ◇ x)) ◇ (y ◇ y) := by
    apply Apply.Equation1973_implies_Equation1855 at h
    apply Apply.Equation1855_implies_Equation1835 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq1851 x]
  nth_rewrite 1 [← eq1894]
  nth_rewrite 1 [eq1832 y]
  symm
  nth_rewrite 1 [← eq1835]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq1832]
  apply h
@[equational_result]
theorem Equation1973_implies_Equation1980 (G: Type _) [Magma G] (h: Equation1973 G) : Equation1980 G := by
  have eq1851 (x y : G) : x = (x ◇ (y ◇ x)) ◇ (y ◇ y) := by
    apply Apply.Equation1973_implies_Equation1855 at h
    apply Apply.Equation1855_implies_Equation1851 at h
    apply h
  have eq1894 (x y : G) : x = (y ◇ (x ◇ y)) ◇ (x ◇ x) := by
    apply Apply.Equation1973_implies_Equation1892 at h
    apply Run2.Equation1892_implies_Equation1902 at h
    apply Apply.Equation1902_implies_Equation1894 at h
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
    apply Apply.Equation1973_implies_Equation1892 at h
    apply Run2.Equation1892_implies_Equation1902 at h
    apply Apply.Equation1902_implies_Equation1894 at h
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
    apply Apply.Equation1973_implies_Equation1892 at h
    apply Run2.Equation1892_implies_Equation1902 at h
    apply Apply.Equation1902_implies_Equation1894 at h
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
theorem Equation1973_implies_Equation1951 (G: Type _) [Magma G] (h: Equation1973 G) : Equation1951 G := by
  have eq1851 (x y : G) : x = (x ◇ (y ◇ x)) ◇ (y ◇ y) := by
    apply Apply.Equation1973_implies_Equation1855 at h
    apply Apply.Equation1855_implies_Equation1851 at h
    apply h
  have eq1894 (x y : G) : x = (y ◇ (x ◇ y)) ◇ (x ◇ x) := by
    apply Apply.Equation1973_implies_Equation1892 at h
    apply Run2.Equation1892_implies_Equation1902 at h
    apply Apply.Equation1902_implies_Equation1894 at h
    apply h
  have eq1832 (x : G) : x = (x ◇ (x ◇ x)) ◇ (x ◇ x) := by
    apply Apply.Equation1973_implies_Equation1855 at h
    apply Apply.Equation1855_implies_Equation1835 at h
    apply Apply.Equation1835_implies_Equation1832 at h
    apply h
  have eq1921 (x y : G) : x = (y ◇ (y ◇ x)) ◇ (x ◇ x) := by
    apply Apply.Equation1973_implies_Equation1929 at h
    apply Apply.Equation1929_implies_Equation1921 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq1851 x]
  nth_rewrite 1 [← eq1894]
  nth_rewrite 1 [eq1832 y]
  symm
  nth_rewrite 1 [← eq1921]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq1832]
  apply h
@[equational_result]
theorem Equation1973_implies_Equation1946 (G: Type _) [Magma G] (h: Equation1973 G) : Equation1946 G := by
  have eq1851 (x y : G) : x = (x ◇ (y ◇ x)) ◇ (y ◇ y) := by
    apply Apply.Equation1973_implies_Equation1855 at h
    apply Apply.Equation1855_implies_Equation1851 at h
    apply h
  have eq1894 (x y : G) : x = (y ◇ (x ◇ y)) ◇ (x ◇ x) := by
    apply Apply.Equation1973_implies_Equation1892 at h
    apply Run2.Equation1892_implies_Equation1902 at h
    apply Apply.Equation1902_implies_Equation1894 at h
    apply h
  have eq1832 (x : G) : x = (x ◇ (x ◇ x)) ◇ (x ◇ x) := by
    apply Apply.Equation1973_implies_Equation1855 at h
    apply Apply.Equation1855_implies_Equation1835 at h
    apply Apply.Equation1835_implies_Equation1832 at h
    apply h
  have eq1925 (x y : G) : x = (y ◇ (y ◇ x)) ◇ (y ◇ y) := by
    apply Apply.Equation1973_implies_Equation1929 at h
    apply Apply.Equation1929_implies_Equation1925 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq1851 x]
  nth_rewrite 1 [← eq1894]
  nth_rewrite 1 [eq1832 y]
  symm
  nth_rewrite 1 [← eq1925]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq1832]
  apply h
@[equational_result]
theorem Equation1973_implies_Equation1956 (G: Type _) [Magma G] (h: Equation1973 G) : Equation1956 G := by
  have eq1851 (x y : G) : x = (x ◇ (y ◇ x)) ◇ (y ◇ y) := by
    apply Apply.Equation1973_implies_Equation1855 at h
    apply Apply.Equation1855_implies_Equation1851 at h
    apply h
  have eq1894 (x y : G) : x = (y ◇ (x ◇ y)) ◇ (x ◇ x) := by
    apply Apply.Equation1973_implies_Equation1892 at h
    apply Run2.Equation1892_implies_Equation1902 at h
    apply Apply.Equation1902_implies_Equation1894 at h
    apply h
  have eq1832 (x : G) : x = (x ◇ (x ◇ x)) ◇ (x ◇ x) := by
    apply Apply.Equation1973_implies_Equation1855 at h
    apply Apply.Equation1855_implies_Equation1835 at h
    apply Apply.Equation1835_implies_Equation1832 at h
    apply h
  have eq1929 (x y z : G) : x = (y ◇ (y ◇ x)) ◇ (z ◇ z) := by
    apply Apply.Equation1973_implies_Equation1929 at h
    apply h
  intro x y z w
  nth_rewrite 1 [eq1851 x]
  nth_rewrite 1 [← eq1894]
  nth_rewrite 1 [eq1832 y]
  symm
  nth_rewrite 1 [← eq1929]
  nth_rewrite 1 [h z]
  symm
  nth_rewrite 1 [← eq1832]
  apply h
@[equational_result]
theorem Equation4692_implies_Equation4690 (G: Type _) [Magma G] (h: Equation4692 G) : Equation4690 G := by
  intro x y z w u
  nth_rewrite 1 [← h]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4668_implies_Equation4693 (G: Type _) [Magma G] (h: Equation4668 G) : Equation4693 G := by
  intro x y z w u
  nth_rewrite 1 [← h]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4662_implies_Equation4676 (G: Type _) [Magma G] (h: Equation4662 G) : Equation4676 G := by
  intro x y z w u
  nth_rewrite 1 [← h]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4660_implies_Equation4675 (G: Type _) [Magma G] (h: Equation4660 G) : Equation4675 G := by
  intro x y z w
  nth_rewrite 1 [← h]
  apply h
@[equational_result]
theorem Equation4659_implies_Equation4672 (G: Type _) [Magma G] (h: Equation4659 G) : Equation4672 G := by
  intro x y z w
  nth_rewrite 1 [← h]
  apply h
@[equational_result]
theorem Equation4643_implies_Equation4689 (G: Type _) [Magma G] (h: Equation4643 G) : Equation4689 G := by
  intro x y z w
  nth_rewrite 1 [← h]
  apply h
@[equational_result]
theorem Equation4595_implies_Equation4670 (G: Type _) [Magma G] (h: Equation4595 G) : Equation4670 G := by
  intro x y z w
  nth_rewrite 1 [← h]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4594_implies_Equation4651 (G: Type _) [Magma G] (h: Equation4594 G) : Equation4651 G := by
  intro x y z w
  nth_rewrite 1 [← h]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4592_implies_Equation4623 (G: Type _) [Magma G] (h: Equation4592 G) : Equation4623 G := by
  intro x y z w
  nth_rewrite 1 [← h]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4377_implies_Equation4375 (G: Type _) [Magma G] (h: Equation4377 G) : Equation4375 G := by
  intro x y z w u
  nth_rewrite 1 [← h]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4354_implies_Equation4378 (G: Type _) [Magma G] (h: Equation4354 G) : Equation4378 G := by
  intro x y z w u
  nth_rewrite 1 [← h]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4322_implies_Equation4357 (G: Type _) [Magma G] (h: Equation4322 G) : Equation4357 G := by
  intro x y z w
  nth_rewrite 1 [← h]
  apply h
@[equational_result]
theorem Equation4303_implies_Equation4374 (G: Type _) [Magma G] (h: Equation4303 G) : Equation4374 G := by
  intro x y z w
  nth_rewrite 1 [← h]
  apply h
@[equational_result]
theorem Equation4298_implies_Equation4361 (G: Type _) [Magma G] (h: Equation4298 G) : Equation4361 G := by
  intro x y z w u
  nth_rewrite 1 [← h]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4295_implies_Equation4360 (G: Type _) [Magma G] (h: Equation4295 G) : Equation4360 G := by
  intro x y z w
  nth_rewrite 1 [← h]
  apply h
@[equational_result]
theorem Equation4280_implies_Equation4355 (G: Type _) [Magma G] (h: Equation4280 G) : Equation4355 G := by
  intro x y z w
  nth_rewrite 1 [← h]
  apply h
  repeat assumption
@[equational_result]
theorem Equation4279_implies_Equation4336 (G: Type _) [Magma G] (h: Equation4279 G) : Equation4336 G := by
  intro x y z w
  nth_rewrite 1 [← h]
  apply h
  repeat assumption
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
theorem Equation4248_implies_Equation45 (G: Type _) [Magma G] (h: Equation4248 G) : Equation45 G := by
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
theorem Equation4098_implies_Equation40 (G: Type _) [Magma G] (h: Equation4098 G) : Equation40 G := by
  intro x y
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
theorem Equation3543_implies_Equation42 (G: Type _) [Magma G] (h: Equation3543 G) : Equation42 G := by
  intro x y z
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
theorem Equation3538_implies_Equation42 (G: Type _) [Magma G] (h: Equation3538 G) : Equation42 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3536_implies_Equation42 (G: Type _) [Magma G] (h: Equation3536 G) : Equation42 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3531_implies_Equation42 (G: Type _) [Magma G] (h: Equation3531 G) : Equation42 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3530_implies_Equation42 (G: Type _) [Magma G] (h: Equation3530 G) : Equation42 G := by
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
theorem Equation3516_implies_Equation42 (G: Type _) [Magma G] (h: Equation3516 G) : Equation42 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3510_implies_Equation42 (G: Type _) [Magma G] (h: Equation3510 G) : Equation42 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3508_implies_Equation42 (G: Type _) [Magma G] (h: Equation3508 G) : Equation42 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
@[equational_result]
theorem Equation3500_implies_Equation40 (G: Type _) [Magma G] (h: Equation3500 G) : Equation40 G := by
  intro x y
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3339_implies_Equation42 (G: Type _) [Magma G] (h: Equation3339 G) : Equation42 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3337_implies_Equation42 (G: Type _) [Magma G] (h: Equation3337 G) : Equation42 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3335_implies_Equation42 (G: Type _) [Magma G] (h: Equation3335 G) : Equation42 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3333_implies_Equation42 (G: Type _) [Magma G] (h: Equation3333 G) : Equation42 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3327_implies_Equation42 (G: Type _) [Magma G] (h: Equation3327 G) : Equation42 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3325_implies_Equation42 (G: Type _) [Magma G] (h: Equation3325 G) : Equation42 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3313_implies_Equation42 (G: Type _) [Magma G] (h: Equation3313 G) : Equation42 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation3311_implies_Equation42 (G: Type _) [Magma G] (h: Equation3311 G) : Equation42 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation407_implies_Equation45 (G: Type _) [Magma G] (h: Equation407 G) : Equation45 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation403_implies_Equation45 (G: Type _) [Magma G] (h: Equation403 G) : Equation45 G := by
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
theorem Equation330_implies_Equation42 (G: Type _) [Magma G] (h: Equation330 G) : Equation42 G := by
  intro x y z
  symm
  nth_rewrite 1 [h]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation48_implies_Equation1427 (G: Type _) [Magma G] (h: Equation48 G) : Equation1427 G := by
  have eq3 (x : G) : x = x ◇ x := by
    apply Run3.Equation48_implies_Equation3 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq3]
  symm
  apply h
@[equational_result]
theorem Equation54_implies_Equation1433 (G: Type _) [Magma G] (h: Equation54 G) : Equation1433 G := by
  have eq3 (x : G) : x = x ◇ x := by
    apply Apply.Equation54_implies_Equation48 at h
    apply Run3.Equation48_implies_Equation3 at h
    apply h
  intro x y z
  symm
  nth_rewrite 1 [← eq3]
  symm
  apply h
@[equational_result]
theorem Equation9_implies_Equation2646 (G: Type _) [Magma G] (h: Equation9 G) : Equation2646 G := by
  have eq3 (x : G) : x = x ◇ x := by
    apply Run2.Equation9_implies_Equation3 at h
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
  nth_rewrite 1 [← eq3]
  nth_rewrite 1 [← eq3864]
  nth_rewrite 1 [eq308]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation1995_implies_Equation23 (G: Type _) [Magma G] (h: Equation1995 G) : Equation23 G := by
  have eq1832 (x : G) : x = (x ◇ (x ◇ x)) ◇ (x ◇ x) := by
    apply Apply.Equation1995_implies_Equation1859 at h
    apply Apply.Equation1859_implies_Equation1833 at h
    apply Apply.Equation1833_implies_Equation1832 at h
    apply h
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation1995_implies_Equation320 at h
    apply Apply.Equation320_implies_Equation310 at h
    apply Apply.Equation310_implies_Equation307 at h
    apply h
  have eq3659 (x : G) : x ◇ x = (x ◇ x) ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation1995_implies_Equation320 at h
    apply Apply.Equation320_implies_Equation312 at h
    apply Apply.Equation312_implies_Equation3694 at h
    apply Apply.Equation3694_implies_Equation3664 at h
    apply Apply.Equation3664_implies_Equation3659 at h
    apply h
  intro x
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 3 [eq1832 x]
  nth_rewrite 1 [← eq307]
  nth_rewrite 1 [eq307]
  nth_rewrite 1 [← eq3659]
  nth_rewrite 1 [← eq1832]
  apply h
  repeat assumption
@[equational_result]
theorem Equation2726_implies_Equation23 (G: Type _) [Magma G] (h: Equation2726 G) : Equation23 G := by
  have eq3659 (x : G) : x ◇ x = (x ◇ x) ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation2726_implies_Equation3762 at h
    apply Apply.Equation3762_implies_Equation3659 at h
    apply h
  have eq2644 (x : G) : x = ((x ◇ x) ◇ (x ◇ x)) ◇ x := by
    apply Apply.Equation2726_implies_Equation2653 at h
    apply Apply.Equation2653_implies_Equation2644 at h
    apply h
  intro x
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [eq3659]
  nth_rewrite 1 [← eq2644]
  apply h
  repeat assumption
@[equational_result]
theorem Equation2726_implies_Equation203 (G: Type _) [Magma G] (h: Equation2726 G) : Equation203 G := by
  have eq2644 (x : G) : x = ((x ◇ x) ◇ (x ◇ x)) ◇ x := by
    apply Apply.Equation2726_implies_Equation2653 at h
    apply Apply.Equation2653_implies_Equation2644 at h
    apply h
  have eq3659 (x : G) : x ◇ x = (x ◇ x) ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation2726_implies_Equation3762 at h
    apply Apply.Equation3762_implies_Equation3659 at h
    apply h
  have eq359 (x : G) : x ◇ x = (x ◇ x) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation2726_implies_Equation3762 at h
    apply RewriteHypothesisAndGoal.Equation3762_implies_Equation45 at h
    apply Apply.Equation45_implies_Equation381 at h
    apply Apply.Equation381_implies_Equation361 at h
    apply Apply.Equation361_implies_Equation359 at h
    apply h
  intro x
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [eq2644 x]
  nth_rewrite 1 [← eq3659]
  nth_rewrite 1 [← eq359]
  nth_rewrite 1 [← eq2644]
  apply h
  repeat assumption
@[equational_result]
theorem Equation2726_implies_Equation2847 (G: Type _) [Magma G] (h: Equation2726 G) : Equation2847 G := by
  have eq2644 (x : G) : x = ((x ◇ x) ◇ (x ◇ x)) ◇ x := by
    apply Apply.Equation2726_implies_Equation2653 at h
    apply Apply.Equation2653_implies_Equation2644 at h
    apply h
  have eq3659 (x : G) : x ◇ x = (x ◇ x) ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation2726_implies_Equation3762 at h
    apply Apply.Equation3762_implies_Equation3659 at h
    apply h
  have eq359 (x : G) : x ◇ x = (x ◇ x) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation2726_implies_Equation3762 at h
    apply RewriteHypothesisAndGoal.Equation3762_implies_Equation45 at h
    apply Apply.Equation45_implies_Equation381 at h
    apply Apply.Equation381_implies_Equation361 at h
    apply Apply.Equation361_implies_Equation359 at h
    apply h
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation2726_implies_Equation3762 at h
    apply RewriteCombinations.Equation3762_implies_Equation336 at h
    apply Apply.Equation336_implies_Equation307 at h
    apply h
  intro x
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 4 [eq2644 x]
  nth_rewrite 1 [← eq3659]
  nth_rewrite 1 [← eq359]
  nth_rewrite 1 [← eq307 x]
  nth_rewrite 1 [← eq2644]
  apply h
  repeat assumption
@[equational_result]
theorem Equation2726_implies_Equation2238 (G: Type _) [Magma G] (h: Equation2726 G) : Equation2238 G := by
  have eq2644 (x : G) : x = ((x ◇ x) ◇ (x ◇ x)) ◇ x := by
    apply Apply.Equation2726_implies_Equation2653 at h
    apply Apply.Equation2653_implies_Equation2644 at h
    apply h
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation2726_implies_Equation3762 at h
    apply RewriteCombinations.Equation3762_implies_Equation336 at h
    apply Apply.Equation336_implies_Equation307 at h
    apply h
  have eq3659 (x : G) : x ◇ x = (x ◇ x) ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation2726_implies_Equation3762 at h
    apply Apply.Equation3762_implies_Equation3659 at h
    apply h
  have eq359 (x : G) : x ◇ x = (x ◇ x) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation2726_implies_Equation3762 at h
    apply RewriteHypothesisAndGoal.Equation3762_implies_Equation45 at h
    apply Apply.Equation45_implies_Equation381 at h
    apply Apply.Equation381_implies_Equation361 at h
    apply Apply.Equation361_implies_Equation359 at h
    apply h
  intro x
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [eq2644 x]
  nth_rewrite 1 [← eq307]
  nth_rewrite 1 [← eq3659]
  nth_rewrite 1 [← eq359]
  nth_rewrite 1 [← eq2644]
  apply h
  repeat assumption
@[equational_result]
theorem Equation292_implies_Equation920 (G: Type _) [Magma G] (h: Equation292 G) : Equation920 G := by
  have eq23 (x : G) : x = (x ◇ x) ◇ x := by
    apply Run5.Equation292_implies_Equation1123 at h
    apply Singleton.Equation1123_implies_Equation2 at h
    apply Subgraph.Equation2_implies_Equation23 at h
    apply h
  have eq4591 (x y : G) : (x ◇ x) ◇ x = (y ◇ y) ◇ y := by
    apply Run3.Equation292_implies_Equation4102 at h
    apply RewriteCombinations.Equation4102_implies_Equation4591 at h
    apply h
  have eq817 (x : G) : x = x ◇ ((x ◇ x) ◇ (x ◇ x)) := by
    apply Apply.Equation292_implies_Equation270 at h
    apply Run3.Equation270_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation817 at h
    apply h
  intro x y
  nth_rewrite 1 [eq23 x]
  nth_rewrite 1 [← eq4591]
  symm
  nth_rewrite 1 [← eq817]
  nth_rewrite 1 [h y]
  symm
  nth_rewrite 1 [← eq23]
  apply h
  repeat assumption
@[equational_result]
theorem Equation979_implies_Equation8 (G: Type _) [Magma G] (h: Equation979 G) : Equation8 G := by
  have eq3659 (x : G) : x ◇ x = (x ◇ x) ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation979_implies_Equation40 at h
    apply NthRewrites.Equation40_implies_Equation3662 at h
    apply Apply.Equation3662_implies_Equation3659 at h
    apply h
  have eq817 (x : G) : x = x ◇ ((x ◇ x) ◇ (x ◇ x)) := by
    apply Apply.Equation979_implies_Equation843 at h
    apply Apply.Equation843_implies_Equation817 at h
    apply h
  intro x
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [eq3659]
  nth_rewrite 1 [← eq817]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1497_implies_Equation3 (G: Type _) [Magma G] (h: Equation1497 G) : Equation3 G := by
  have eq3254 (x y : G) : x ◇ x = x ◇ (x ◇ (x ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation311 at h
    apply Apply.Equation311_implies_Equation308 at h
    apply Apply.Equation308_implies_Equation3257 at h
    apply Apply.Equation3257_implies_Equation3254 at h
    apply h
  have eq1426 (x : G) : x = (x ◇ x) ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation1497_implies_Equation1430 at h
    apply Apply.Equation1430_implies_Equation1427 at h
    apply Apply.Equation1427_implies_Equation1426 at h
    apply h
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation1497_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation311 at h
    apply Apply.Equation311_implies_Equation308 at h
    apply Apply.Equation308_implies_Equation307 at h
    apply h
  have eq3659 (x : G) : x ◇ x = (x ◇ x) ◇ (x ◇ x) := by
    apply Apply.Equation1497_implies_Equation1496 at h
    apply RewriteHypothesisAndGoal.Equation1496_implies_Equation3688 at h
    apply SimpleRewrites.Equation3688_implies_Equation3659 at h
    apply h
  have eq1427 (x y : G) : x = (x ◇ x) ◇ (x ◇ (x ◇ y)) := by
    apply Apply.Equation1497_implies_Equation1430 at h
    apply Apply.Equation1430_implies_Equation1427 at h
    apply h
  intro x
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [eq3254]
  nth_rewrite 1 [eq1426 x]
  nth_rewrite 1 [← eq307]
  nth_rewrite 1 [← eq3659]
  nth_rewrite 1 [← eq1427]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1712_implies_Equation3 (G: Type _) [Magma G] (h: Equation1712 G) : Equation3 G := by
  have eq3660 (x y : G) : x ◇ x = (x ◇ x) ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation1712_implies_Equation369 at h
    apply Apply.Equation369_implies_Equation360 at h
    apply Apply.Equation360_implies_Equation3663 at h
    apply Apply.Equation3663_implies_Equation3660 at h
    apply h
  have eq1629 (x : G) : x = (x ◇ x) ◇ ((x ◇ x) ◇ x) := by
    apply Apply.Equation1712_implies_Equation1639 at h
    apply Apply.Equation1639_implies_Equation1630 at h
    apply Apply.Equation1630_implies_Equation1629 at h
    apply h
  have eq359 (x : G) : x ◇ x = (x ◇ x) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation1712_implies_Equation369 at h
    apply Apply.Equation369_implies_Equation360 at h
    apply Apply.Equation360_implies_Equation359 at h
    apply h
  have eq3659 (x : G) : x ◇ x = (x ◇ x) ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation1712_implies_Equation369 at h
    apply Apply.Equation369_implies_Equation360 at h
    apply Apply.Equation360_implies_Equation3663 at h
    apply Apply.Equation3663_implies_Equation3660 at h
    apply Apply.Equation3660_implies_Equation3659 at h
    apply h
  have eq1630 (x y : G) : x = (x ◇ x) ◇ ((x ◇ x) ◇ y) := by
    apply Apply.Equation1712_implies_Equation1639 at h
    apply Apply.Equation1639_implies_Equation1630 at h
    apply h
  intro x
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [eq3660]
  nth_rewrite 3 [eq1629 x]
  nth_rewrite 1 [← eq359]
  nth_rewrite 1 [← eq3659]
  nth_rewrite 1 [← eq1630]
  apply h
  repeat assumption
@[equational_result]
theorem Equation28_implies_Equation1884 (G: Type _) [Magma G] (h: Equation28 G) : Equation1884 G := by
  have eq3 (x : G) : x = x ◇ x := by
    apply Run1.Equation28_implies_Equation3 at h
    apply h
  have eq3674 (x y : G) : x ◇ x = (y ◇ x) ◇ (x ◇ x) := by
    apply Run2.Equation28_implies_Equation3674 at h
    apply h
  have eq364 (x y : G) : x ◇ x = (y ◇ x) ◇ x := by
    apply Run1.Equation28_implies_Equation364 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [← eq3]
  nth_rewrite 1 [← eq3674]
  nth_rewrite 1 [eq364]
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
    apply Run2.Equation3110_implies_Equation3120 at h
    apply Apply.Equation3120_implies_Equation3112 at h
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
theorem Equation276_implies_Equation25 (G: Type _) [Magma G] (h: Equation276 G) : Equation25 G := by
  have eq47 (x : G) : x = x ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation276_implies_Equation270 at h
    apply Run3.Equation270_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation47 at h
    apply h
  have eq3 (x : G) : x = x ◇ x := by
    apply Apply.Equation276_implies_Equation270 at h
    apply Run3.Equation270_implies_Equation3 at h
    apply h
  have eq257 (x y : G) : x = ((x ◇ x) ◇ y) ◇ x := by
    apply Apply.Equation276_implies_Equation257 at h
    apply h
  intro x y
  nth_rewrite 1 [eq47 x]
  symm
  nth_rewrite 1 [eq3 x]
  nth_rewrite 1 [← eq257]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq47]
  apply h
  repeat assumption
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
    apply Apply.Equation2147_implies_Equation2146 at h
    apply RewriteHypothesisAndGoal.Equation2146_implies_Equation3688 at h
    apply RewriteHypothesisAndGoal.Equation3688_implies_Equation40 at h
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
    apply Apply.Equation2216_implies_Equation2215 at h
    apply RewriteHypothesisAndGoal.Equation2215_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation363 at h
    apply Apply.Equation363_implies_Equation360 at h
    apply Apply.Equation360_implies_Equation359 at h
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
theorem Equation1995_implies_Equation168 (G: Type _) [Magma G] (h: Equation1995 G) : Equation168 G := by
  have eq1832 (x : G) : x = (x ◇ (x ◇ x)) ◇ (x ◇ x) := by
    apply Apply.Equation1995_implies_Equation1859 at h
    apply Apply.Equation1859_implies_Equation1833 at h
    apply Apply.Equation1833_implies_Equation1832 at h
    apply h
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation1995_implies_Equation320 at h
    apply Apply.Equation320_implies_Equation310 at h
    apply Apply.Equation310_implies_Equation307 at h
    apply h
  have eq3659 (x : G) : x ◇ x = (x ◇ x) ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation1995_implies_Equation320 at h
    apply Apply.Equation320_implies_Equation312 at h
    apply Apply.Equation312_implies_Equation3694 at h
    apply Apply.Equation3694_implies_Equation3664 at h
    apply Apply.Equation3664_implies_Equation3659 at h
    apply h
  have eq1886 (x y z : G) : x = (y ◇ (x ◇ x)) ◇ (x ◇ z) := by
    apply Apply.Equation1995_implies_Equation1886 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq1832 x]
  symm
  nth_rewrite 1 [eq1832 x]
  nth_rewrite 1 [← eq307]
  nth_rewrite 1 [← eq3659]
  nth_rewrite 1 [← eq1886]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq1832]
  apply h
  repeat assumption
@[equational_result]
theorem Equation2726_implies_Equation255 (G: Type _) [Magma G] (h: Equation2726 G) : Equation255 G := by
  have eq2644 (x : G) : x = ((x ◇ x) ◇ (x ◇ x)) ◇ x := by
    apply Apply.Equation2726_implies_Equation2653 at h
    apply Apply.Equation2653_implies_Equation2644 at h
    apply h
  have eq3659 (x : G) : x ◇ x = (x ◇ x) ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation2726_implies_Equation3762 at h
    apply Apply.Equation3762_implies_Equation3659 at h
    apply h
  have eq359 (x : G) : x ◇ x = (x ◇ x) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation2726_implies_Equation3762 at h
    apply RewriteHypothesisAndGoal.Equation3762_implies_Equation45 at h
    apply Apply.Equation45_implies_Equation381 at h
    apply Apply.Equation381_implies_Equation361 at h
    apply Apply.Equation361_implies_Equation359 at h
    apply h
  intro x
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 3 [eq2644 x]
  nth_rewrite 1 [← eq3659]
  nth_rewrite 1 [← eq359]
  nth_rewrite 1 [← eq2644]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1995_implies_Equation203 (G: Type _) [Magma G] (h: Equation1995 G) : Equation203 G := by
  have eq1832 (x : G) : x = (x ◇ (x ◇ x)) ◇ (x ◇ x) := by
    apply Apply.Equation1995_implies_Equation1859 at h
    apply Apply.Equation1859_implies_Equation1833 at h
    apply Apply.Equation1833_implies_Equation1832 at h
    apply h
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation1995_implies_Equation320 at h
    apply Apply.Equation320_implies_Equation310 at h
    apply Apply.Equation310_implies_Equation307 at h
    apply h
  have eq3659 (x : G) : x ◇ x = (x ◇ x) ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation1995_implies_Equation320 at h
    apply Apply.Equation320_implies_Equation312 at h
    apply Apply.Equation312_implies_Equation3694 at h
    apply Apply.Equation3694_implies_Equation3664 at h
    apply Apply.Equation3664_implies_Equation3659 at h
    apply h
  intro x
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 4 [eq1832 x]
  nth_rewrite 2 [← eq307]
  nth_rewrite 1 [← eq3659 x]
  nth_rewrite 1 [← eq1832]
  apply h
  repeat assumption
@[equational_result]
theorem Equation2120_implies_Equation3 (G: Type _) [Magma G] (h: Equation2120 G) : Equation3 G := by
  have eq3661 (x y : G) : x ◇ x = (x ◇ x) ◇ (y ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation2120_implies_Equation41 at h
    apply RewriteGoal.Equation41_implies_Equation3720 at h
    apply Apply.Equation3720_implies_Equation3663 at h
    apply Apply.Equation3663_implies_Equation3661 at h
    apply h
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation2120_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation334 at h
    apply Apply.Equation334_implies_Equation308 at h
    apply Apply.Equation308_implies_Equation307 at h
    apply h
  have eq1834 (x y : G) : x = (x ◇ (x ◇ x)) ◇ (y ◇ x) := by
    apply Run2.Equation2120_implies_Equation1917 at h
    apply Apply.Equation1917_implies_Equation1843 at h
    apply Apply.Equation1843_implies_Equation1834 at h
    apply h
  intro x
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [eq3661 x]
  nth_rewrite 1 [eq307 x]
  nth_rewrite 1 [← eq1834 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3125_implies_Equation3 (G: Type _) [Magma G] (h: Equation3125 G) : Equation3 G := by
  have eq4066 (x y : G) : x ◇ x = ((x ◇ x) ◇ x) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation3125_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4163 at h
    apply Apply.Equation4163_implies_Equation4069 at h
    apply Apply.Equation4069_implies_Equation4066 at h
    apply h
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation3125_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation387 at h
    apply Run3.Equation387_implies_Equation332 at h
    apply Apply.Equation332_implies_Equation307 at h
    apply h
  have eq2848 (x y : G) : x = ((x ◇ (x ◇ x)) ◇ x) ◇ y := by
    apply Run2.Equation3125_implies_Equation2922 at h
    apply Apply.Equation2922_implies_Equation2854 at h
    apply Apply.Equation2854_implies_Equation2848 at h
    apply h
  intro x
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [eq4066 x]
  nth_rewrite 1 [eq307 x]
  nth_rewrite 1 [← eq2848 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation1604_implies_Equation3 (G: Type _) [Magma G] (h: Equation1604 G) : Equation3 G := by
  have eq3664 (x y : G) : x ◇ x = (x ◇ y) ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation1604_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3437 at h
    apply RewriteHypothesisAndGoal.Equation3437_implies_Equation3731 at h
    apply Apply.Equation3731_implies_Equation3664 at h
    apply h
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation1604_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation334 at h
    apply Apply.Equation334_implies_Equation308 at h
    apply Apply.Equation308_implies_Equation307 at h
    apply h
  have eq1441 (x y : G) : x = (x ◇ y) ◇ (x ◇ (x ◇ x)) := by
    apply Apply.Equation1604_implies_Equation1461 at h
    apply Apply.Equation1461_implies_Equation1441 at h
    apply h
  intro x
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [eq3664 x]
  nth_rewrite 2 [eq307 x]
  nth_rewrite 1 [← eq1441 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation276_implies_Equation2040 (G: Type _) [Magma G] (h: Equation276 G) : Equation2040 G := by
  have eq3 (x : G) : x = x ◇ x := by
    apply Apply.Equation276_implies_Equation270 at h
    apply Run3.Equation270_implies_Equation3 at h
    apply h
  have eq4067 (x y : G) : x ◇ x = ((x ◇ x) ◇ y) ◇ x := by
    apply Run3.Equation276_implies_Equation4067 at h
    apply h
  have eq4086 (x y z : G) : x ◇ x = ((y ◇ x) ◇ z) ◇ x := by
    apply Run4.Equation276_implies_Equation4086 at h
    apply h
  intro x y
  symm
  nth_rewrite 2 [← eq3 x]
  nth_rewrite 1 [← eq4067 x]
  nth_rewrite 1 [eq4086]
  symm
  apply h
  repeat assumption
@[equational_result]
theorem Equation276_implies_Equation361 (G: Type _) [Magma G] (h: Equation276 G) : Equation361 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply Apply.Equation276_implies_Equation270 at h
    apply Run3.Equation270_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation375 at h
    apply h
  have eq257 (x y : G) : x = ((x ◇ x) ◇ y) ◇ x := by
    apply Apply.Equation276_implies_Equation257 at h
    apply h
  have eq3 (x : G) : x = x ◇ x := by
    apply Apply.Equation276_implies_Equation270 at h
    apply Run3.Equation270_implies_Equation3 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [eq375 x]
  nth_rewrite 1 [← eq257]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq3]
  apply h
  repeat assumption
@[equational_result]
theorem Equation276_implies_Equation4382 (G: Type _) [Magma G] (h: Equation276 G) : Equation4382 G := by
  have eq375 (x y : G) : x ◇ y = (x ◇ x) ◇ y := by
    apply Apply.Equation276_implies_Equation270 at h
    apply Run3.Equation270_implies_Equation3 at h
    apply RewriteHypothesis.Equation3_implies_Equation375 at h
    apply h
  have eq257 (x y : G) : x = ((x ◇ x) ◇ y) ◇ x := by
    apply Apply.Equation276_implies_Equation257 at h
    apply h
  have eq8 (x : G) : x = x ◇ (x ◇ x) := by
    apply Apply.Equation276_implies_Equation270 at h
    apply Run3.Equation270_implies_Equation3 at h
    apply Subgraph.Equation3_implies_Equation8 at h
    apply h
  intro x y
  symm
  nth_rewrite 1 [eq375 x]
  nth_rewrite 1 [← eq257]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq8]
  apply h
  repeat assumption
@[equational_result]
theorem Equation2987_implies_Equation98 (G: Type _) [Magma G] (h: Equation2987 G) : Equation98 G := by
  have eq2847 (x : G) : x = ((x ◇ (x ◇ x)) ◇ x) ◇ x := by
    apply Apply.Equation2987_implies_Equation2869 at h
    apply Apply.Equation2869_implies_Equation2849 at h
    apply Apply.Equation2849_implies_Equation2847 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply RewriteHypothesisAndGoal.Equation2987_implies_Equation46 at h
    apply Apply.Equation46_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq4067 (x y : G) : x ◇ x = ((x ◇ x) ◇ y) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation2987_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation39 at h
    apply RewriteCombinations.Equation39_implies_Equation4187 at h
    apply SimpleRewrites.Equation4187_implies_Equation4076 at h
    apply Apply.Equation4076_implies_Equation4067 at h
    apply h
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation2987_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation387 at h
    apply Run3.Equation387_implies_Equation332 at h
    apply Apply.Equation332_implies_Equation307 at h
    apply h
  have eq2849 (x y : G) : x = ((x ◇ (x ◇ x)) ◇ y) ◇ x := by
    apply Apply.Equation2987_implies_Equation2869 at h
    apply Apply.Equation2869_implies_Equation2849 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [eq2847 x]
  symm
  nth_rewrite 1 [← eq3304 x]
  nth_rewrite 1 [eq4067 x]
  nth_rewrite 1 [eq307 x]
  nth_rewrite 1 [← eq2849]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq2847]
  apply h
  repeat assumption
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
    apply RewriteHypothesisAndGoal.Equation2215_implies_Equation373 at h
    apply Apply.Equation373_implies_Equation363 at h
    apply Apply.Equation363_implies_Equation360 at h
    apply Apply.Equation360_implies_Equation359 at h
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
theorem Equation3187_implies_Equation98 (G: Type _) [Magma G] (h: Equation3187 G) : Equation98 G := by
  have eq2847 (x : G) : x = ((x ◇ (x ◇ x)) ◇ x) ◇ x := by
    apply Run2.Equation3187_implies_Equation2984 at h
    apply Apply.Equation2984_implies_Equation2867 at h
    apply Apply.Equation2867_implies_Equation2848 at h
    apply Apply.Equation2848_implies_Equation2847 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply RewriteHypothesisAndGoal.Equation3187_implies_Equation46 at h
    apply Apply.Equation46_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq4066 (x y : G) : x ◇ x = ((x ◇ x) ◇ x) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation3187_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4163 at h
    apply Apply.Equation4163_implies_Equation4069 at h
    apply Apply.Equation4069_implies_Equation4066 at h
    apply h
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation3187_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation387 at h
    apply Run3.Equation387_implies_Equation332 at h
    apply Apply.Equation332_implies_Equation307 at h
    apply h
  have eq2848 (x y : G) : x = ((x ◇ (x ◇ x)) ◇ x) ◇ y := by
    apply Run2.Equation3187_implies_Equation2984 at h
    apply Apply.Equation2984_implies_Equation2867 at h
    apply Apply.Equation2867_implies_Equation2848 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [eq2847 x]
  symm
  nth_rewrite 1 [← eq3304 x]
  nth_rewrite 1 [eq4066 x]
  nth_rewrite 1 [eq307 x]
  nth_rewrite 1 [← eq2848 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq2847]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3133_implies_Equation98 (G: Type _) [Magma G] (h: Equation3133 G) : Equation98 G := by
  have eq2847 (x : G) : x = ((x ◇ (x ◇ x)) ◇ x) ◇ x := by
    apply Run2.Equation3133_implies_Equation2930 at h
    apply Apply.Equation2930_implies_Equation2857 at h
    apply Apply.Equation2857_implies_Equation2848 at h
    apply Apply.Equation2848_implies_Equation2847 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply RewriteHypothesisAndGoal.Equation3133_implies_Equation46 at h
    apply Apply.Equation46_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq4066 (x y : G) : x ◇ x = ((x ◇ x) ◇ x) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation3133_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4163 at h
    apply Apply.Equation4163_implies_Equation4069 at h
    apply Apply.Equation4069_implies_Equation4066 at h
    apply h
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation3133_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation387 at h
    apply Run3.Equation387_implies_Equation332 at h
    apply Apply.Equation332_implies_Equation307 at h
    apply h
  have eq2848 (x y : G) : x = ((x ◇ (x ◇ x)) ◇ x) ◇ y := by
    apply Run2.Equation3133_implies_Equation2930 at h
    apply Apply.Equation2930_implies_Equation2857 at h
    apply Apply.Equation2857_implies_Equation2848 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [eq2847 x]
  symm
  nth_rewrite 1 [← eq3304]
  nth_rewrite 1 [eq4066]
  nth_rewrite 1 [eq307]
  nth_rewrite 1 [← eq2848 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq2847]
  apply h
  repeat assumption
@[equational_result]
theorem Equation2824_implies_Equation98 (G: Type _) [Magma G] (h: Equation2824 G) : Equation98 G := by
  have eq2644 (x : G) : x = ((x ◇ x) ◇ (x ◇ x)) ◇ x := by
    apply Apply.Equation2824_implies_Equation2681 at h
    apply Apply.Equation2681_implies_Equation2650 at h
    apply Apply.Equation2650_implies_Equation2644 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply RewriteHypothesisAndGoal.Equation2824_implies_Equation46 at h
    apply Apply.Equation46_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq362 (x y : G) : x ◇ x = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2824_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation392 at h
    apply SimpleRewrites.Equation392_implies_Equation362 at h
    apply h
  have eq3714 (x y : G) : x ◇ y = (x ◇ x) ◇ (y ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation2824_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteGoal.Equation41_implies_Equation3720 at h
    apply Apply.Equation3720_implies_Equation3716 at h
    apply Apply.Equation3716_implies_Equation3714 at h
    apply h
  have eq2650 (x y : G) : x = ((x ◇ x) ◇ (y ◇ x)) ◇ y := by
    apply Apply.Equation2824_implies_Equation2681 at h
    apply Apply.Equation2681_implies_Equation2650 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [eq2644 x]
  symm
  nth_rewrite 1 [← eq3304]
  nth_rewrite 1 [eq362]
  nth_rewrite 1 [eq3714 x]
  nth_rewrite 1 [← eq2650 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq2644 x]
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
    apply RewriteHypothesisAndGoal.Equation1978_implies_Equation319 at h
    apply Apply.Equation319_implies_Equation313 at h
    apply NthRewrites.Equation313_implies_Equation3678 at h
    apply Apply.Equation3678_implies_Equation3659 at h
    apply h
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation1978_implies_Equation319 at h
    apply Apply.Equation319_implies_Equation309 at h
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
    apply RewriteHypothesisAndGoal.Equation1995_implies_Equation320 at h
    apply Apply.Equation320_implies_Equation312 at h
    apply Apply.Equation312_implies_Equation3694 at h
    apply Apply.Equation3694_implies_Equation3664 at h
    apply Apply.Equation3664_implies_Equation3659 at h
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
    apply RewriteHypothesisAndGoal.Equation1995_implies_Equation320 at h
    apply Apply.Equation320_implies_Equation312 at h
    apply Apply.Equation312_implies_Equation3694 at h
    apply Apply.Equation3694_implies_Equation3664 at h
    apply Apply.Equation3664_implies_Equation3659 at h
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
theorem Equation2785_implies_Equation64 (G: Type _) [Magma G] (h: Equation2785 G) : Equation64 G := by
  have eq2644 (x : G) : x = ((x ◇ x) ◇ (x ◇ x)) ◇ x := by
    apply Apply.Equation2785_implies_Equation2667 at h
    apply Apply.Equation2667_implies_Equation2647 at h
    apply Apply.Equation2647_implies_Equation2644 at h
    apply h
  have eq3270 (x y z : G) : x ◇ x = y ◇ (x ◇ (x ◇ z)) := by
    apply RewriteHypothesisAndGoal.Equation2785_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3382 at h
    apply SimpleRewrites.Equation3382_implies_Equation3270 at h
    apply h
  have eq362 (x y : G) : x ◇ x = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2785_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation392 at h
    apply SimpleRewrites.Equation392_implies_Equation362 at h
    apply h
  have eq3712 (x y : G) : x ◇ y = (x ◇ x) ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation2785_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteGoal.Equation41_implies_Equation3720 at h
    apply Apply.Equation3720_implies_Equation3713 at h
    apply Apply.Equation3713_implies_Equation3712 at h
    apply h
  have eq2647 (x y : G) : x = ((x ◇ x) ◇ (x ◇ y)) ◇ y := by
    apply Apply.Equation2785_implies_Equation2667 at h
    apply Apply.Equation2667_implies_Equation2647 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq2644 x]
  symm
  nth_rewrite 1 [← eq3270 x]
  nth_rewrite 1 [eq362 x]
  nth_rewrite 1 [eq3712 x]
  nth_rewrite 1 [← eq2647 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq2644]
  apply h
  repeat assumption
@[equational_result]
theorem Equation2785_implies_Equation69 (G: Type _) [Magma G] (h: Equation2785 G) : Equation69 G := by
  have eq2644 (x : G) : x = ((x ◇ x) ◇ (x ◇ x)) ◇ x := by
    apply Apply.Equation2785_implies_Equation2667 at h
    apply Apply.Equation2667_implies_Equation2647 at h
    apply Apply.Equation2647_implies_Equation2644 at h
    apply h
  have eq3275 (x y z : G) : x ◇ x = y ◇ (x ◇ (z ◇ y)) := by
    apply RewriteHypothesisAndGoal.Equation2785_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation3393 at h
    apply SimpleRewrites.Equation3393_implies_Equation3275 at h
    apply h
  have eq362 (x y : G) : x ◇ x = (x ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation2785_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation392 at h
    apply SimpleRewrites.Equation392_implies_Equation362 at h
    apply h
  have eq3712 (x y : G) : x ◇ y = (x ◇ x) ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation2785_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteGoal.Equation41_implies_Equation3720 at h
    apply Apply.Equation3720_implies_Equation3713 at h
    apply Apply.Equation3713_implies_Equation3712 at h
    apply h
  have eq2647 (x y : G) : x = ((x ◇ x) ◇ (x ◇ y)) ◇ y := by
    apply Apply.Equation2785_implies_Equation2667 at h
    apply Apply.Equation2667_implies_Equation2647 at h
    apply h
  intro x y z
  nth_rewrite 1 [eq2644 x]
  symm
  nth_rewrite 1 [← eq3275 x]
  nth_rewrite 1 [eq362 x]
  nth_rewrite 1 [eq3712 x]
  nth_rewrite 1 [← eq2647 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq2644 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3137_implies_Equation98 (G: Type _) [Magma G] (h: Equation3137 G) : Equation98 G := by
  have eq2847 (x : G) : x = ((x ◇ (x ◇ x)) ◇ x) ◇ x := by
    apply Run2.Equation3137_implies_Equation2934 at h
    apply Apply.Equation2934_implies_Equation2860 at h
    apply Apply.Equation2860_implies_Equation2850 at h
    apply Apply.Equation2850_implies_Equation2847 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply RewriteHypothesisAndGoal.Equation3137_implies_Equation46 at h
    apply Apply.Equation46_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq4068 (x y : G) : x ◇ x = ((x ◇ x) ◇ y) ◇ y := by
    apply RewriteHypothesisAndGoal.Equation3137_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation41 at h
    apply RewriteCombinations.Equation41_implies_Equation4162 at h
    apply Apply.Equation4162_implies_Equation4068 at h
    apply h
  have eq307 (x : G) : x ◇ x = x ◇ (x ◇ x) := by
    apply RewriteHypothesisAndGoal.Equation3137_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation387 at h
    apply Run3.Equation387_implies_Equation332 at h
    apply Apply.Equation332_implies_Equation307 at h
    apply h
  have eq2850 (x y : G) : x = ((x ◇ (x ◇ x)) ◇ y) ◇ y := by
    apply Run2.Equation3137_implies_Equation2934 at h
    apply Apply.Equation2934_implies_Equation2860 at h
    apply Apply.Equation2860_implies_Equation2850 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [eq2847 x]
  symm
  nth_rewrite 1 [← eq3304 x]
  nth_rewrite 1 [eq4068 x]
  nth_rewrite 1 [eq307 x]
  nth_rewrite 1 [← eq2850 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq2847 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation3229_implies_Equation98 (G: Type _) [Magma G] (h: Equation3229 G) : Equation98 G := by
  have eq2847 (x : G) : x = ((x ◇ (x ◇ x)) ◇ x) ◇ x := by
    apply Run2.Equation3229_implies_Equation3026 at h
    apply Apply.Equation3026_implies_Equation2883 at h
    apply Apply.Equation2883_implies_Equation2852 at h
    apply Apply.Equation2852_implies_Equation2847 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply RewriteHypothesisAndGoal.Equation3229_implies_Equation46 at h
    apply Apply.Equation46_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq4070 (x y : G) : x ◇ x = ((x ◇ y) ◇ x) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation3229_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation39 at h
    apply RewriteCombinations.Equation39_implies_Equation4179 at h
    apply SimpleRewrites.Equation4179_implies_Equation4070 at h
    apply h
  have eq323 (x y : G) : x ◇ y = x ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation3229_implies_Equation46 at h
    apply Subgraph.Equation46_implies_Equation42 at h
    apply Apply.Equation42_implies_Equation329 at h
    apply Apply.Equation329_implies_Equation323 at h
    apply h
  have eq2852 (x y : G) : x = ((x ◇ (x ◇ y)) ◇ x) ◇ x := by
    apply Run2.Equation3229_implies_Equation3026 at h
    apply Apply.Equation3026_implies_Equation2883 at h
    apply Apply.Equation2883_implies_Equation2852 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [eq2847 x]
  symm
  nth_rewrite 1 [← eq3304 x]
  nth_rewrite 1 [eq4070 x]
  nth_rewrite 1 [eq323 x]
  nth_rewrite 1 [← eq2852 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq2847 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation2731_implies_Equation98 (G: Type _) [Magma G] (h: Equation2731 G) : Equation98 G := by
  have eq2644 (x : G) : x = ((x ◇ x) ◇ (x ◇ x)) ◇ x := by
    apply Apply.Equation2731_implies_Equation2657 at h
    apply Apply.Equation2657_implies_Equation2647 at h
    apply Apply.Equation2647_implies_Equation2644 at h
    apply h
  have eq3451 (x y z w u : G) : x ◇ y = z ◇ (w ◇ (u ◇ y)) := by
    apply Apply.Equation2731_implies_Equation2726 at h
    apply RewriteHypothesisAndGoal.Equation2726_implies_Equation3762 at h
    apply RewriteCombinations.Equation3762_implies_Equation3811 at h
    apply RewriteCombinations.Equation3811_implies_Equation3451 at h
    apply h
  have eq378 (x y : G) : x ◇ y = (x ◇ y) ◇ y := by
    apply Apply.Equation2731_implies_Equation2726 at h
    apply RewriteHypothesisAndGoal.Equation2726_implies_Equation3762 at h
    apply RewriteHypothesisAndGoal.Equation3762_implies_Equation45 at h
    apply Apply.Equation45_implies_Equation381 at h
    apply Apply.Equation381_implies_Equation378 at h
    apply h
  have eq3712 (x y : G) : x ◇ y = (x ◇ x) ◇ (x ◇ y) := by
    apply RewriteHypothesisAndGoal.Equation2731_implies_Equation355 at h
    apply Apply.Equation355_implies_Equation343 at h
    apply Apply.Equation343_implies_Equation3837 at h
    apply Apply.Equation3837_implies_Equation3732 at h
    apply Apply.Equation3732_implies_Equation3712 at h
    apply h
  have eq2647 (x y : G) : x = ((x ◇ x) ◇ (x ◇ y)) ◇ y := by
    apply Apply.Equation2731_implies_Equation2657 at h
    apply Apply.Equation2657_implies_Equation2647 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [eq2644 x]
  symm
  nth_rewrite 1 [← eq3451 x]
  nth_rewrite 1 [eq378 x]
  nth_rewrite 1 [eq3712 x]
  nth_rewrite 1 [← eq2647 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq2644 x]
  apply h
  repeat assumption
@[equational_result]
theorem Equation2730_implies_Equation98 (G: Type _) [Magma G] (h: Equation2730 G) : Equation98 G := by
  have eq2644 (x : G) : x = ((x ◇ x) ◇ (x ◇ x)) ◇ x := by
    apply Apply.Equation2730_implies_Equation2656 at h
    apply Apply.Equation2656_implies_Equation2646 at h
    apply Apply.Equation2646_implies_Equation2644 at h
    apply h
  have eq3304 (x y z w u : G) : x ◇ x = y ◇ (z ◇ (w ◇ u)) := by
    apply RewriteHypothesisAndGoal.Equation2730_implies_Equation393 at h
    apply RewriteCombinations.Equation393_implies_Equation4267 at h
    apply Constant.Equation4267_implies_Equation46 at h
    apply Apply.Equation46_implies_Equation358 at h
    apply SimpleRewrites.Equation358_implies_Equation321 at h
    apply Apply.Equation321_implies_Equation3304 at h
    apply h
  have eq361 (x y : G) : x ◇ x = (x ◇ y) ◇ x := by
    apply RewriteHypothesisAndGoal.Equation2730_implies_Equation393 at h
    apply SimpleRewrites.Equation393_implies_Equation363 at h
    apply Apply.Equation363_implies_Equation361 at h
    apply h
  have eq3712 (x y : G) : x ◇ y = (x ◇ x) ◇ (x ◇ y) := by
    apply Apply.Equation2730_implies_Equation2726 at h
    apply RewriteHypothesisAndGoal.Equation2726_implies_Equation3762 at h
    apply RewriteCombinations.Equation3762_implies_Equation3811 at h
    apply RewriteCombinations.Equation3811_implies_Equation3744 at h
    apply Apply.Equation3744_implies_Equation3718 at h
    apply Apply.Equation3718_implies_Equation3712 at h
    apply h
  have eq2646 (x y : G) : x = ((x ◇ x) ◇ (x ◇ y)) ◇ x := by
    apply Apply.Equation2730_implies_Equation2656 at h
    apply Apply.Equation2656_implies_Equation2646 at h
    apply h
  intro x y z w u
  nth_rewrite 1 [eq2644 x]
  symm
  nth_rewrite 1 [← eq3304 x]
  nth_rewrite 1 [eq361 x]
  nth_rewrite 1 [eq3712 x]
  nth_rewrite 1 [← eq2646 x]
  nth_rewrite 1 [h x]
  symm
  nth_rewrite 1 [← eq2644 x]
  apply h
  repeat assumption
