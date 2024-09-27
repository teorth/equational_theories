import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation566 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (w ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation769 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ w) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation972 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (w ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1175 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1378 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ w) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1581 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (w ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1784 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1987 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2190 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2393 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2596 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2799 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3002 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3205 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3408 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (w ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3611 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ w) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3814 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (w ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4017 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ w)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4220 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ w) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4366 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = y ∘ (w ∘ x)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4535 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ w) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4681 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (y ∘ w) ∘ x
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation566 (G : Type*) [Magma G] (h : Equation613 G) : Equation566 G := λ x y z w => h x y z y w x
theorem Equation816_implies_Equation769 (G : Type*) [Magma G] (h : Equation816 G) : Equation769 G := λ x y z w => h x y z y w x
theorem Equation1019_implies_Equation972 (G : Type*) [Magma G] (h : Equation1019 G) : Equation972 G := λ x y z w => h x y z y w x
theorem Equation1222_implies_Equation1175 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1175 G := λ x y z w => h x y z y w x
theorem Equation1425_implies_Equation1378 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1378 G := λ x y z w => h x y z y w x
theorem Equation1628_implies_Equation1581 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1581 G := λ x y z w => h x y z y w x
theorem Equation1831_implies_Equation1784 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1784 G := λ x y z w => h x y z y w x
theorem Equation2034_implies_Equation1987 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1987 G := λ x y z w => h x y z y w x
theorem Equation2237_implies_Equation2190 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2190 G := λ x y z w => h x y z y w x
theorem Equation2440_implies_Equation2393 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2393 G := λ x y z w => h x y z y w x
theorem Equation2643_implies_Equation2596 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2596 G := λ x y z w => h x y z y w x
theorem Equation2846_implies_Equation2799 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2799 G := λ x y z w => h x y z y w x
theorem Equation3049_implies_Equation3002 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3002 G := λ x y z w => h x y z y w x
theorem Equation3252_implies_Equation3205 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3205 G := λ x y z w => h x y z y w x
theorem Equation3455_implies_Equation3408 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3408 G := λ x y z w => h x y z y w x
theorem Equation3658_implies_Equation3611 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3611 G := λ x y z w => h x y z y w x
theorem Equation3861_implies_Equation3814 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3814 G := λ x y z w => h x y z y w x
theorem Equation4064_implies_Equation4017 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4017 G := λ x y z w => h x y z y w x
theorem Equation4267_implies_Equation4220 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4220 G := λ x y z w => h x y z y w x
theorem Equation4379_implies_Equation4366 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4366 G := λ x y z w => h x y z y w x
theorem Equation4582_implies_Equation4535 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4535 G := λ x y z w => h x y z y w x
theorem Equation4694_implies_Equation4681 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4681 G := λ x y z w => h x y z y w x