import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation551 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (w ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation754 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ w) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation957 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (w ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1160 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1363 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ w) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1566 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (w ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1769 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1972 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2175 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2378 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2581 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2784 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2987 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3190 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3393 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (w ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3596 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ w) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3799 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (w ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4002 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ w)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4205 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ w) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4360 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = x ∘ (w ∘ z)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4520 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ w) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4675 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (x ∘ w) ∘ z
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation551 (G : Type*) [Magma G] (h : Equation613 G) : Equation551 G := λ x y z w => h x y z x w z
theorem Equation816_implies_Equation754 (G : Type*) [Magma G] (h : Equation816 G) : Equation754 G := λ x y z w => h x y z x w z
theorem Equation1019_implies_Equation957 (G : Type*) [Magma G] (h : Equation1019 G) : Equation957 G := λ x y z w => h x y z x w z
theorem Equation1222_implies_Equation1160 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1160 G := λ x y z w => h x y z x w z
theorem Equation1425_implies_Equation1363 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1363 G := λ x y z w => h x y z x w z
theorem Equation1628_implies_Equation1566 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1566 G := λ x y z w => h x y z x w z
theorem Equation1831_implies_Equation1769 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1769 G := λ x y z w => h x y z x w z
theorem Equation2034_implies_Equation1972 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1972 G := λ x y z w => h x y z x w z
theorem Equation2237_implies_Equation2175 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2175 G := λ x y z w => h x y z x w z
theorem Equation2440_implies_Equation2378 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2378 G := λ x y z w => h x y z x w z
theorem Equation2643_implies_Equation2581 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2581 G := λ x y z w => h x y z x w z
theorem Equation2846_implies_Equation2784 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2784 G := λ x y z w => h x y z x w z
theorem Equation3049_implies_Equation2987 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2987 G := λ x y z w => h x y z x w z
theorem Equation3252_implies_Equation3190 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3190 G := λ x y z w => h x y z x w z
theorem Equation3455_implies_Equation3393 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3393 G := λ x y z w => h x y z x w z
theorem Equation3658_implies_Equation3596 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3596 G := λ x y z w => h x y z x w z
theorem Equation3861_implies_Equation3799 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3799 G := λ x y z w => h x y z x w z
theorem Equation4064_implies_Equation4002 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4002 G := λ x y z w => h x y z x w z
theorem Equation4267_implies_Equation4205 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4205 G := λ x y z w => h x y z x w z
theorem Equation4379_implies_Equation4360 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4360 G := λ x y z w => h x y z x w z
theorem Equation4582_implies_Equation4520 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4520 G := λ x y z w => h x y z x w z
theorem Equation4694_implies_Equation4675 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4675 G := λ x y z w => h x y z x w z