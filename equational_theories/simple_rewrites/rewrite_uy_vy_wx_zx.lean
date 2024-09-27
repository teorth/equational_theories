import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation467 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (x ∘ (y ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation670 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((x ∘ y) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation873 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ x) ∘ (y ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1076 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (x ∘ y)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1279 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ x) ∘ y) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1482 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (x ∘ (y ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1685 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((x ∘ y) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1888 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ x)) ∘ (y ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2091 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ x) ∘ (y ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2294 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (x ∘ y))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2497 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ x) ∘ y)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2700 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (x ∘ y)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2903 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ x)) ∘ y) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3106 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ x) ∘ y) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3309 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (x ∘ (y ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3512 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((x ∘ y) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3715 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ x) ∘ (y ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3918 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (x ∘ y)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4121 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ x) ∘ y) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4314 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = x ∘ (y ∘ y)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4436 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (x ∘ y) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4629 (G: Type*) [Magma G] := ∀ x y : G, (x ∘ y) ∘ x = (x ∘ y) ∘ y
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation467 (G : Type*) [Magma G] (h : Equation613 G) : Equation467 G := λ x y => h x y x x y y
theorem Equation816_implies_Equation670 (G : Type*) [Magma G] (h : Equation816 G) : Equation670 G := λ x y => h x y x x y y
theorem Equation1019_implies_Equation873 (G : Type*) [Magma G] (h : Equation1019 G) : Equation873 G := λ x y => h x y x x y y
theorem Equation1222_implies_Equation1076 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1076 G := λ x y => h x y x x y y
theorem Equation1425_implies_Equation1279 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1279 G := λ x y => h x y x x y y
theorem Equation1628_implies_Equation1482 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1482 G := λ x y => h x y x x y y
theorem Equation1831_implies_Equation1685 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1685 G := λ x y => h x y x x y y
theorem Equation2034_implies_Equation1888 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1888 G := λ x y => h x y x x y y
theorem Equation2237_implies_Equation2091 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2091 G := λ x y => h x y x x y y
theorem Equation2440_implies_Equation2294 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2294 G := λ x y => h x y x x y y
theorem Equation2643_implies_Equation2497 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2497 G := λ x y => h x y x x y y
theorem Equation2846_implies_Equation2700 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2700 G := λ x y => h x y x x y y
theorem Equation3049_implies_Equation2903 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2903 G := λ x y => h x y x x y y
theorem Equation3252_implies_Equation3106 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3106 G := λ x y => h x y x x y y
theorem Equation3455_implies_Equation3309 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3309 G := λ x y => h x y x x y y
theorem Equation3658_implies_Equation3512 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3512 G := λ x y => h x y x x y y
theorem Equation3861_implies_Equation3715 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3715 G := λ x y => h x y x x y y
theorem Equation4064_implies_Equation3918 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3918 G := λ x y => h x y x x y y
theorem Equation4267_implies_Equation4121 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4121 G := λ x y => h x y x x y y
theorem Equation4379_implies_Equation4314 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4314 G := λ x y => h x y x x y y
theorem Equation4582_implies_Equation4436 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4436 G := λ x y => h x y x x y y
theorem Equation4694_implies_Equation4629 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4629 G := λ x y => h x y x x y y