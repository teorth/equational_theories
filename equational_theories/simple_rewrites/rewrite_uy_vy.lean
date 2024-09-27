import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation594 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (y ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation797 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ y) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation1000 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (y ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1203 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ y)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1406 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ y) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1609 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (y ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1812 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ y) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation2015 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (y ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2218 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (y ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2421 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ y))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2624 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ y)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2827 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ y)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3030 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ y) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3233 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ y) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3436 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (y ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3639 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ y) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3842 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (y ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4045 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ y)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4248 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ y) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4563 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ y) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation594 (G : Type*) [Magma G] (h : Equation613 G) : Equation594 G := λ x y z w => h x y z w y y
theorem Equation816_implies_Equation797 (G : Type*) [Magma G] (h : Equation816 G) : Equation797 G := λ x y z w => h x y z w y y
theorem Equation1019_implies_Equation1000 (G : Type*) [Magma G] (h : Equation1019 G) : Equation1000 G := λ x y z w => h x y z w y y
theorem Equation1222_implies_Equation1203 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1203 G := λ x y z w => h x y z w y y
theorem Equation1425_implies_Equation1406 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1406 G := λ x y z w => h x y z w y y
theorem Equation1628_implies_Equation1609 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1609 G := λ x y z w => h x y z w y y
theorem Equation1831_implies_Equation1812 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1812 G := λ x y z w => h x y z w y y
theorem Equation2034_implies_Equation2015 (G : Type*) [Magma G] (h : Equation2034 G) : Equation2015 G := λ x y z w => h x y z w y y
theorem Equation2237_implies_Equation2218 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2218 G := λ x y z w => h x y z w y y
theorem Equation2440_implies_Equation2421 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2421 G := λ x y z w => h x y z w y y
theorem Equation2643_implies_Equation2624 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2624 G := λ x y z w => h x y z w y y
theorem Equation2846_implies_Equation2827 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2827 G := λ x y z w => h x y z w y y
theorem Equation3049_implies_Equation3030 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3030 G := λ x y z w => h x y z w y y
theorem Equation3252_implies_Equation3233 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3233 G := λ x y z w => h x y z w y y
theorem Equation3455_implies_Equation3436 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3436 G := λ x y z w => h x y z w y y
theorem Equation3658_implies_Equation3639 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3639 G := λ x y z w => h x y z w y y
theorem Equation3861_implies_Equation3842 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3842 G := λ x y z w => h x y z w y y
theorem Equation4064_implies_Equation4045 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4045 G := λ x y z w => h x y z w y y
theorem Equation4267_implies_Equation4248 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4248 G := λ x y z w => h x y z w y y
theorem Equation4582_implies_Equation4563 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4563 G := λ x y z w => h x y z w y y