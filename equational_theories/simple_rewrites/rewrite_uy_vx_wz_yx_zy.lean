import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation450 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ (y ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation653 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((z ∘ y) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation856 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ (y ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1059 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (z ∘ y)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1262 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ z) ∘ y) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1465 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ (y ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1668 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((z ∘ y) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1871 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ (y ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2074 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ (y ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2277 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (z ∘ y))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2480 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ z) ∘ y)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2683 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (z ∘ y)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2886 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ z)) ∘ y) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3089 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ z) ∘ y) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3292 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ (y ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3495 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((z ∘ y) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3698 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ (y ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3901 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (z ∘ y)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4104 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ z) ∘ y) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4303 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = z ∘ (y ∘ x)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4419 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (z ∘ y) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4618 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (z ∘ y) ∘ x
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation450 (G : Type*) [Magma G] (h : Equation613 G) : Equation450 G := λ x y z => h x x y z y x
theorem Equation816_implies_Equation653 (G : Type*) [Magma G] (h : Equation816 G) : Equation653 G := λ x y z => h x x y z y x
theorem Equation1019_implies_Equation856 (G : Type*) [Magma G] (h : Equation1019 G) : Equation856 G := λ x y z => h x x y z y x
theorem Equation1222_implies_Equation1059 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1059 G := λ x y z => h x x y z y x
theorem Equation1425_implies_Equation1262 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1262 G := λ x y z => h x x y z y x
theorem Equation1628_implies_Equation1465 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1465 G := λ x y z => h x x y z y x
theorem Equation1831_implies_Equation1668 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1668 G := λ x y z => h x x y z y x
theorem Equation2034_implies_Equation1871 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1871 G := λ x y z => h x x y z y x
theorem Equation2237_implies_Equation2074 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2074 G := λ x y z => h x x y z y x
theorem Equation2440_implies_Equation2277 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2277 G := λ x y z => h x x y z y x
theorem Equation2643_implies_Equation2480 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2480 G := λ x y z => h x x y z y x
theorem Equation2846_implies_Equation2683 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2683 G := λ x y z => h x x y z y x
theorem Equation3049_implies_Equation2886 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2886 G := λ x y z => h x x y z y x
theorem Equation3252_implies_Equation3089 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3089 G := λ x y z => h x x y z y x
theorem Equation3455_implies_Equation3292 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3292 G := λ x y z => h x x y z y x
theorem Equation3658_implies_Equation3495 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3495 G := λ x y z => h x x y z y x
theorem Equation3861_implies_Equation3698 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3698 G := λ x y z => h x x y z y x
theorem Equation4064_implies_Equation3901 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3901 G := λ x y z => h x x y z y x
theorem Equation4267_implies_Equation4104 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4104 G := λ x y z => h x x y z y x
theorem Equation4379_implies_Equation4303 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4303 G := λ x y z => h x x y z y x
theorem Equation4582_implies_Equation4419 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4419 G := λ x y z => h x x y z y x
theorem Equation4694_implies_Equation4618 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4618 G := λ x y z => h x x y z y x