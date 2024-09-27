import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation558 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ (y ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation761 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((y ∘ y) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation964 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ (y ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1167 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (y ∘ y)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1370 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ y) ∘ y) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1573 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ (y ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1776 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((y ∘ y) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1979 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ (y ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2182 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ (y ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2385 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (y ∘ y))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2588 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ y) ∘ y)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2791 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (y ∘ y)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2994 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ y)) ∘ y) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3197 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ y) ∘ y) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3400 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ (y ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3603 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((y ∘ y) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3806 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ (y ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4009 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (y ∘ y)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4212 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ y) ∘ y) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4527 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (y ∘ y) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation558 (G : Type*) [Magma G] (h : Equation613 G) : Equation558 G := λ x y z => h x y z y y x
theorem Equation816_implies_Equation761 (G : Type*) [Magma G] (h : Equation816 G) : Equation761 G := λ x y z => h x y z y y x
theorem Equation1019_implies_Equation964 (G : Type*) [Magma G] (h : Equation1019 G) : Equation964 G := λ x y z => h x y z y y x
theorem Equation1222_implies_Equation1167 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1167 G := λ x y z => h x y z y y x
theorem Equation1425_implies_Equation1370 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1370 G := λ x y z => h x y z y y x
theorem Equation1628_implies_Equation1573 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1573 G := λ x y z => h x y z y y x
theorem Equation1831_implies_Equation1776 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1776 G := λ x y z => h x y z y y x
theorem Equation2034_implies_Equation1979 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1979 G := λ x y z => h x y z y y x
theorem Equation2237_implies_Equation2182 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2182 G := λ x y z => h x y z y y x
theorem Equation2440_implies_Equation2385 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2385 G := λ x y z => h x y z y y x
theorem Equation2643_implies_Equation2588 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2588 G := λ x y z => h x y z y y x
theorem Equation2846_implies_Equation2791 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2791 G := λ x y z => h x y z y y x
theorem Equation3049_implies_Equation2994 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2994 G := λ x y z => h x y z y y x
theorem Equation3252_implies_Equation3197 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3197 G := λ x y z => h x y z y y x
theorem Equation3455_implies_Equation3400 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3400 G := λ x y z => h x y z y y x
theorem Equation3658_implies_Equation3603 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3603 G := λ x y z => h x y z y y x
theorem Equation3861_implies_Equation3806 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3806 G := λ x y z => h x y z y y x
theorem Equation4064_implies_Equation4009 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4009 G := λ x y z => h x y z y y x
theorem Equation4267_implies_Equation4212 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4212 G := λ x y z => h x y z y y x
theorem Equation4582_implies_Equation4527 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4527 G := λ x y z => h x y z y y x