import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation584 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (w ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation787 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ w) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation990 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (w ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1193 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ w)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1396 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ w) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1599 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (w ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1802 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ w) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation2005 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (w ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2208 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (w ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2411 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ w))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2614 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ w)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2817 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ w)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3020 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ w) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3223 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ w) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3426 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (w ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3629 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ w) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3832 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (w ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4035 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ w)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4238 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ w) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4372 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = z ∘ (w ∘ y)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4553 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ w) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4687 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (z ∘ w) ∘ y
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation584 (G : Type*) [Magma G] (h : Equation613 G) : Equation584 G := λ x y z w => h x y z z w y
theorem Equation816_implies_Equation787 (G : Type*) [Magma G] (h : Equation816 G) : Equation787 G := λ x y z w => h x y z z w y
theorem Equation1019_implies_Equation990 (G : Type*) [Magma G] (h : Equation1019 G) : Equation990 G := λ x y z w => h x y z z w y
theorem Equation1222_implies_Equation1193 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1193 G := λ x y z w => h x y z z w y
theorem Equation1425_implies_Equation1396 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1396 G := λ x y z w => h x y z z w y
theorem Equation1628_implies_Equation1599 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1599 G := λ x y z w => h x y z z w y
theorem Equation1831_implies_Equation1802 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1802 G := λ x y z w => h x y z z w y
theorem Equation2034_implies_Equation2005 (G : Type*) [Magma G] (h : Equation2034 G) : Equation2005 G := λ x y z w => h x y z z w y
theorem Equation2237_implies_Equation2208 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2208 G := λ x y z w => h x y z z w y
theorem Equation2440_implies_Equation2411 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2411 G := λ x y z w => h x y z z w y
theorem Equation2643_implies_Equation2614 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2614 G := λ x y z w => h x y z z w y
theorem Equation2846_implies_Equation2817 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2817 G := λ x y z w => h x y z z w y
theorem Equation3049_implies_Equation3020 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3020 G := λ x y z w => h x y z z w y
theorem Equation3252_implies_Equation3223 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3223 G := λ x y z w => h x y z z w y
theorem Equation3455_implies_Equation3426 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3426 G := λ x y z w => h x y z z w y
theorem Equation3658_implies_Equation3629 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3629 G := λ x y z w => h x y z z w y
theorem Equation3861_implies_Equation3832 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3832 G := λ x y z w => h x y z z w y
theorem Equation4064_implies_Equation4035 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4035 G := λ x y z w => h x y z z w y
theorem Equation4267_implies_Equation4238 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4238 G := λ x y z w => h x y z z w y
theorem Equation4379_implies_Equation4372 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4372 G := λ x y z w => h x y z z w y
theorem Equation4582_implies_Equation4553 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4553 G := λ x y z w => h x y z z w y
theorem Equation4694_implies_Equation4687 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4687 G := λ x y z w => h x y z z w y