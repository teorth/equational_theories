import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation568 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (w ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation771 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ w) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation974 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (w ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1177 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1380 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ w) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1583 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (w ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1786 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1989 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2192 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2395 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2598 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2801 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3004 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3207 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3410 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (w ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3613 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ w) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3816 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (w ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4019 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ w)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4222 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ w) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4367 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = y ∘ (w ∘ z)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4537 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ w) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4682 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (y ∘ w) ∘ z
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation568 (G : Type*) [Magma G] (h : Equation613 G) : Equation568 G := λ x y z w => h x y z y w z
theorem Equation816_implies_Equation771 (G : Type*) [Magma G] (h : Equation816 G) : Equation771 G := λ x y z w => h x y z y w z
theorem Equation1019_implies_Equation974 (G : Type*) [Magma G] (h : Equation1019 G) : Equation974 G := λ x y z w => h x y z y w z
theorem Equation1222_implies_Equation1177 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1177 G := λ x y z w => h x y z y w z
theorem Equation1425_implies_Equation1380 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1380 G := λ x y z w => h x y z y w z
theorem Equation1628_implies_Equation1583 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1583 G := λ x y z w => h x y z y w z
theorem Equation1831_implies_Equation1786 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1786 G := λ x y z w => h x y z y w z
theorem Equation2034_implies_Equation1989 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1989 G := λ x y z w => h x y z y w z
theorem Equation2237_implies_Equation2192 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2192 G := λ x y z w => h x y z y w z
theorem Equation2440_implies_Equation2395 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2395 G := λ x y z w => h x y z y w z
theorem Equation2643_implies_Equation2598 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2598 G := λ x y z w => h x y z y w z
theorem Equation2846_implies_Equation2801 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2801 G := λ x y z w => h x y z y w z
theorem Equation3049_implies_Equation3004 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3004 G := λ x y z w => h x y z y w z
theorem Equation3252_implies_Equation3207 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3207 G := λ x y z w => h x y z y w z
theorem Equation3455_implies_Equation3410 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3410 G := λ x y z w => h x y z y w z
theorem Equation3658_implies_Equation3613 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3613 G := λ x y z w => h x y z y w z
theorem Equation3861_implies_Equation3816 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3816 G := λ x y z w => h x y z y w z
theorem Equation4064_implies_Equation4019 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4019 G := λ x y z w => h x y z y w z
theorem Equation4267_implies_Equation4222 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4222 G := λ x y z w => h x y z y w z
theorem Equation4379_implies_Equation4367 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4367 G := λ x y z w => h x y z y w z
theorem Equation4582_implies_Equation4537 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4537 G := λ x y z w => h x y z y w z
theorem Equation4694_implies_Equation4682 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4682 G := λ x y z w => h x y z y w z