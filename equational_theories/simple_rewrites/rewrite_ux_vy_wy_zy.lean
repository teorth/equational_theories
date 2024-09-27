import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation511 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (y ∘ (x ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation714 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ ((y ∘ x) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation917 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ y) ∘ (x ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1120 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ (y ∘ x)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1323 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((y ∘ y) ∘ x) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1526 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (y ∘ (x ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1729 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ ((y ∘ x) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1932 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ y)) ∘ (x ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2135 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ y) ∘ (x ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2338 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ (y ∘ x))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2541 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((y ∘ y) ∘ x)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2744 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ (y ∘ x)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2947 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (y ∘ y)) ∘ x) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3150 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ y) ∘ y) ∘ x) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3353 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (y ∘ (x ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3556 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ ((y ∘ x) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3759 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ y) ∘ (x ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3962 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ (y ∘ x)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4165 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((y ∘ y) ∘ x) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4480 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = (y ∘ x) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation511 (G : Type*) [Magma G] (h : Equation613 G) : Equation511 G := λ x y => h x y y y x y
theorem Equation816_implies_Equation714 (G : Type*) [Magma G] (h : Equation816 G) : Equation714 G := λ x y => h x y y y x y
theorem Equation1019_implies_Equation917 (G : Type*) [Magma G] (h : Equation1019 G) : Equation917 G := λ x y => h x y y y x y
theorem Equation1222_implies_Equation1120 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1120 G := λ x y => h x y y y x y
theorem Equation1425_implies_Equation1323 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1323 G := λ x y => h x y y y x y
theorem Equation1628_implies_Equation1526 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1526 G := λ x y => h x y y y x y
theorem Equation1831_implies_Equation1729 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1729 G := λ x y => h x y y y x y
theorem Equation2034_implies_Equation1932 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1932 G := λ x y => h x y y y x y
theorem Equation2237_implies_Equation2135 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2135 G := λ x y => h x y y y x y
theorem Equation2440_implies_Equation2338 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2338 G := λ x y => h x y y y x y
theorem Equation2643_implies_Equation2541 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2541 G := λ x y => h x y y y x y
theorem Equation2846_implies_Equation2744 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2744 G := λ x y => h x y y y x y
theorem Equation3049_implies_Equation2947 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2947 G := λ x y => h x y y y x y
theorem Equation3252_implies_Equation3150 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3150 G := λ x y => h x y y y x y
theorem Equation3455_implies_Equation3353 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3353 G := λ x y => h x y y y x y
theorem Equation3658_implies_Equation3556 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3556 G := λ x y => h x y y y x y
theorem Equation3861_implies_Equation3759 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3759 G := λ x y => h x y y y x y
theorem Equation4064_implies_Equation3962 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3962 G := λ x y => h x y y y x y
theorem Equation4267_implies_Equation4165 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4165 G := λ x y => h x y y y x y
theorem Equation4582_implies_Equation4480 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4480 G := λ x y => h x y y y x y