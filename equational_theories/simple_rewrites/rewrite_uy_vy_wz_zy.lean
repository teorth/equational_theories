import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation525 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ (y ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation728 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((z ∘ y) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation931 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ (y ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1134 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (z ∘ y)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1337 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ z) ∘ y) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1540 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ (y ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1743 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((z ∘ y) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1946 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ (y ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2149 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ (y ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2352 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (z ∘ y))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2555 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ z) ∘ y)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2758 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (z ∘ y)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2961 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ z)) ∘ y) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3164 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ z) ∘ y) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3367 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ (y ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3570 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((z ∘ y) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3773 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ (y ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3976 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (z ∘ y)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4179 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ z) ∘ y) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4351 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = z ∘ (y ∘ y)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4494 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (z ∘ y) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4666 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ y = (z ∘ y) ∘ y
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation525 (G : Type*) [Magma G] (h : Equation613 G) : Equation525 G := λ x y z => h x y y z y y
theorem Equation816_implies_Equation728 (G : Type*) [Magma G] (h : Equation816 G) : Equation728 G := λ x y z => h x y y z y y
theorem Equation1019_implies_Equation931 (G : Type*) [Magma G] (h : Equation1019 G) : Equation931 G := λ x y z => h x y y z y y
theorem Equation1222_implies_Equation1134 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1134 G := λ x y z => h x y y z y y
theorem Equation1425_implies_Equation1337 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1337 G := λ x y z => h x y y z y y
theorem Equation1628_implies_Equation1540 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1540 G := λ x y z => h x y y z y y
theorem Equation1831_implies_Equation1743 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1743 G := λ x y z => h x y y z y y
theorem Equation2034_implies_Equation1946 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1946 G := λ x y z => h x y y z y y
theorem Equation2237_implies_Equation2149 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2149 G := λ x y z => h x y y z y y
theorem Equation2440_implies_Equation2352 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2352 G := λ x y z => h x y y z y y
theorem Equation2643_implies_Equation2555 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2555 G := λ x y z => h x y y z y y
theorem Equation2846_implies_Equation2758 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2758 G := λ x y z => h x y y z y y
theorem Equation3049_implies_Equation2961 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2961 G := λ x y z => h x y y z y y
theorem Equation3252_implies_Equation3164 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3164 G := λ x y z => h x y y z y y
theorem Equation3455_implies_Equation3367 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3367 G := λ x y z => h x y y z y y
theorem Equation3658_implies_Equation3570 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3570 G := λ x y z => h x y y z y y
theorem Equation3861_implies_Equation3773 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3773 G := λ x y z => h x y y z y y
theorem Equation4064_implies_Equation3976 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3976 G := λ x y z => h x y y z y y
theorem Equation4267_implies_Equation4179 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4179 G := λ x y z => h x y y z y y
theorem Equation4379_implies_Equation4351 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4351 G := λ x y z => h x y y z y y
theorem Equation4582_implies_Equation4494 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4494 G := λ x y z => h x y y z y y
theorem Equation4694_implies_Equation4666 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4666 G := λ x y z => h x y y z y y