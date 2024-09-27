import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation437 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (y ∘ (x ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation640 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ ((y ∘ x) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation843 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ y) ∘ (x ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1046 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ (y ∘ x)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1249 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((y ∘ y) ∘ x) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1452 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (y ∘ (x ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1655 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ ((y ∘ x) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1858 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ y)) ∘ (x ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2061 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ y) ∘ (x ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2264 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ (y ∘ x))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2467 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((y ∘ y) ∘ x)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2670 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ (y ∘ x)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2873 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (y ∘ y)) ∘ x) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3076 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ y) ∘ y) ∘ x) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3279 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (y ∘ (x ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3482 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ ((y ∘ x) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3685 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ y) ∘ (x ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3888 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ (y ∘ x)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4091 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((y ∘ y) ∘ x) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4291 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = y ∘ (x ∘ y)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4406 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = (y ∘ x) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4606 (G: Type*) [Magma G] := ∀ x y : G, (x ∘ x) ∘ y = (y ∘ x) ∘ y
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation437 (G : Type*) [Magma G] (h : Equation613 G) : Equation437 G := λ x y => h x x y y x y
theorem Equation816_implies_Equation640 (G : Type*) [Magma G] (h : Equation816 G) : Equation640 G := λ x y => h x x y y x y
theorem Equation1019_implies_Equation843 (G : Type*) [Magma G] (h : Equation1019 G) : Equation843 G := λ x y => h x x y y x y
theorem Equation1222_implies_Equation1046 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1046 G := λ x y => h x x y y x y
theorem Equation1425_implies_Equation1249 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1249 G := λ x y => h x x y y x y
theorem Equation1628_implies_Equation1452 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1452 G := λ x y => h x x y y x y
theorem Equation1831_implies_Equation1655 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1655 G := λ x y => h x x y y x y
theorem Equation2034_implies_Equation1858 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1858 G := λ x y => h x x y y x y
theorem Equation2237_implies_Equation2061 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2061 G := λ x y => h x x y y x y
theorem Equation2440_implies_Equation2264 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2264 G := λ x y => h x x y y x y
theorem Equation2643_implies_Equation2467 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2467 G := λ x y => h x x y y x y
theorem Equation2846_implies_Equation2670 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2670 G := λ x y => h x x y y x y
theorem Equation3049_implies_Equation2873 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2873 G := λ x y => h x x y y x y
theorem Equation3252_implies_Equation3076 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3076 G := λ x y => h x x y y x y
theorem Equation3455_implies_Equation3279 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3279 G := λ x y => h x x y y x y
theorem Equation3658_implies_Equation3482 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3482 G := λ x y => h x x y y x y
theorem Equation3861_implies_Equation3685 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3685 G := λ x y => h x x y y x y
theorem Equation4064_implies_Equation3888 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3888 G := λ x y => h x x y y x y
theorem Equation4267_implies_Equation4091 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4091 G := λ x y => h x x y y x y
theorem Equation4379_implies_Equation4291 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4291 G := λ x y => h x x y y x y
theorem Equation4582_implies_Equation4406 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4406 G := λ x y => h x x y y x y
theorem Equation4694_implies_Equation4606 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4606 G := λ x y => h x x y y x y