import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation480 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (y ∘ (z ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation683 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((y ∘ z) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation886 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ y) ∘ (z ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1089 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (y ∘ z)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1292 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ y) ∘ z) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1495 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (y ∘ (z ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1698 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((y ∘ z) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1901 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ y)) ∘ (z ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2104 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ y) ∘ (z ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2307 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (y ∘ z))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2510 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ y) ∘ z)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2713 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (y ∘ z)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2916 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ y)) ∘ z) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3119 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ y) ∘ z) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3322 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (y ∘ (z ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3525 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((y ∘ z) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3728 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ y) ∘ (z ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3931 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (y ∘ z)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4134 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ y) ∘ z) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4324 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = y ∘ (z ∘ y)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4449 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (y ∘ z) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4639 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (y ∘ z) ∘ y
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation480 (G : Type*) [Magma G] (h : Equation613 G) : Equation480 G := λ x y z => h x y x y z y
theorem Equation816_implies_Equation683 (G : Type*) [Magma G] (h : Equation816 G) : Equation683 G := λ x y z => h x y x y z y
theorem Equation1019_implies_Equation886 (G : Type*) [Magma G] (h : Equation1019 G) : Equation886 G := λ x y z => h x y x y z y
theorem Equation1222_implies_Equation1089 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1089 G := λ x y z => h x y x y z y
theorem Equation1425_implies_Equation1292 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1292 G := λ x y z => h x y x y z y
theorem Equation1628_implies_Equation1495 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1495 G := λ x y z => h x y x y z y
theorem Equation1831_implies_Equation1698 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1698 G := λ x y z => h x y x y z y
theorem Equation2034_implies_Equation1901 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1901 G := λ x y z => h x y x y z y
theorem Equation2237_implies_Equation2104 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2104 G := λ x y z => h x y x y z y
theorem Equation2440_implies_Equation2307 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2307 G := λ x y z => h x y x y z y
theorem Equation2643_implies_Equation2510 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2510 G := λ x y z => h x y x y z y
theorem Equation2846_implies_Equation2713 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2713 G := λ x y z => h x y x y z y
theorem Equation3049_implies_Equation2916 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2916 G := λ x y z => h x y x y z y
theorem Equation3252_implies_Equation3119 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3119 G := λ x y z => h x y x y z y
theorem Equation3455_implies_Equation3322 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3322 G := λ x y z => h x y x y z y
theorem Equation3658_implies_Equation3525 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3525 G := λ x y z => h x y x y z y
theorem Equation3861_implies_Equation3728 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3728 G := λ x y z => h x y x y z y
theorem Equation4064_implies_Equation3931 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3931 G := λ x y z => h x y x y z y
theorem Equation4267_implies_Equation4134 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4134 G := λ x y z => h x y x y z y
theorem Equation4379_implies_Equation4324 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4324 G := λ x y z => h x y x y z y
theorem Equation4582_implies_Equation4449 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4449 G := λ x y z => h x y x y z y
theorem Equation4694_implies_Equation4639 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4639 G := λ x y z => h x y x y z y