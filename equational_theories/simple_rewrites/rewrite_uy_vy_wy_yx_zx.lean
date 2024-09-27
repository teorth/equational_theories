import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation420 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (y ∘ (y ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation623 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ ((y ∘ y) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation826 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ y) ∘ (y ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1029 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ (y ∘ y)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1232 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((x ∘ y) ∘ y) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1435 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ (y ∘ (y ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1638 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ ((y ∘ y) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1841 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ y)) ∘ (y ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2044 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ y) ∘ (y ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2247 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ (y ∘ y))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2450 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((x ∘ y) ∘ y)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2653 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ (y ∘ y)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2856 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (x ∘ y)) ∘ y) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3059 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ x) ∘ y) ∘ y) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3262 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ (y ∘ (y ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3465 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ ((y ∘ y) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3668 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ y) ∘ (y ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3871 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ (y ∘ y)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4074 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((x ∘ y) ∘ y) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4276 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = y ∘ (y ∘ y)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4389 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = (y ∘ y) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4591 (G: Type*) [Magma G] := ∀ x y : G, (x ∘ x) ∘ x = (y ∘ y) ∘ y
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation420 (G : Type*) [Magma G] (h : Equation613 G) : Equation420 G := λ x y => h x x x y y y
theorem Equation816_implies_Equation623 (G : Type*) [Magma G] (h : Equation816 G) : Equation623 G := λ x y => h x x x y y y
theorem Equation1019_implies_Equation826 (G : Type*) [Magma G] (h : Equation1019 G) : Equation826 G := λ x y => h x x x y y y
theorem Equation1222_implies_Equation1029 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1029 G := λ x y => h x x x y y y
theorem Equation1425_implies_Equation1232 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1232 G := λ x y => h x x x y y y
theorem Equation1628_implies_Equation1435 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1435 G := λ x y => h x x x y y y
theorem Equation1831_implies_Equation1638 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1638 G := λ x y => h x x x y y y
theorem Equation2034_implies_Equation1841 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1841 G := λ x y => h x x x y y y
theorem Equation2237_implies_Equation2044 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2044 G := λ x y => h x x x y y y
theorem Equation2440_implies_Equation2247 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2247 G := λ x y => h x x x y y y
theorem Equation2643_implies_Equation2450 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2450 G := λ x y => h x x x y y y
theorem Equation2846_implies_Equation2653 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2653 G := λ x y => h x x x y y y
theorem Equation3049_implies_Equation2856 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2856 G := λ x y => h x x x y y y
theorem Equation3252_implies_Equation3059 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3059 G := λ x y => h x x x y y y
theorem Equation3455_implies_Equation3262 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3262 G := λ x y => h x x x y y y
theorem Equation3658_implies_Equation3465 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3465 G := λ x y => h x x x y y y
theorem Equation3861_implies_Equation3668 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3668 G := λ x y => h x x x y y y
theorem Equation4064_implies_Equation3871 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3871 G := λ x y => h x x x y y y
theorem Equation4267_implies_Equation4074 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4074 G := λ x y => h x x x y y y
theorem Equation4379_implies_Equation4276 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4276 G := λ x y => h x x x y y y
theorem Equation4582_implies_Equation4389 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4389 G := λ x y => h x x x y y y
theorem Equation4694_implies_Equation4591 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4591 G := λ x y => h x x x y y y