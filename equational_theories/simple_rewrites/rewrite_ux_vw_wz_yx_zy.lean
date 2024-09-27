import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation449 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (x ∘ w)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation652 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ x) ∘ w))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation855 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (x ∘ w))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1058 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ x)) ∘ w)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1261 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ x) ∘ w)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1464 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (x ∘ w))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1667 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ x) ∘ w)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1870 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (x ∘ w)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2073 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (x ∘ w)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2276 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ x))) ∘ w
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2479 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ x)) ∘ w
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2682 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ x)) ∘ w
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2885 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ x) ∘ w
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3088 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ x) ∘ w
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3291 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (x ∘ w))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3494 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ x) ∘ w)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3697 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (x ∘ w)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3900 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ x)) ∘ w
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4103 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ x) ∘ w
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4302 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (x ∘ w)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4418 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ x) ∘ w
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4617 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ x) ∘ w
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation449 (G : Type*) [Magma G] (h : Equation613 G) : Equation449 G := λ x y z w => h x x y z x w
theorem Equation816_implies_Equation652 (G : Type*) [Magma G] (h : Equation816 G) : Equation652 G := λ x y z w => h x x y z x w
theorem Equation1019_implies_Equation855 (G : Type*) [Magma G] (h : Equation1019 G) : Equation855 G := λ x y z w => h x x y z x w
theorem Equation1222_implies_Equation1058 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1058 G := λ x y z w => h x x y z x w
theorem Equation1425_implies_Equation1261 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1261 G := λ x y z w => h x x y z x w
theorem Equation1628_implies_Equation1464 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1464 G := λ x y z w => h x x y z x w
theorem Equation1831_implies_Equation1667 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1667 G := λ x y z w => h x x y z x w
theorem Equation2034_implies_Equation1870 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1870 G := λ x y z w => h x x y z x w
theorem Equation2237_implies_Equation2073 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2073 G := λ x y z w => h x x y z x w
theorem Equation2440_implies_Equation2276 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2276 G := λ x y z w => h x x y z x w
theorem Equation2643_implies_Equation2479 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2479 G := λ x y z w => h x x y z x w
theorem Equation2846_implies_Equation2682 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2682 G := λ x y z w => h x x y z x w
theorem Equation3049_implies_Equation2885 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2885 G := λ x y z w => h x x y z x w
theorem Equation3252_implies_Equation3088 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3088 G := λ x y z w => h x x y z x w
theorem Equation3455_implies_Equation3291 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3291 G := λ x y z w => h x x y z x w
theorem Equation3658_implies_Equation3494 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3494 G := λ x y z w => h x x y z x w
theorem Equation3861_implies_Equation3697 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3697 G := λ x y z w => h x x y z x w
theorem Equation4064_implies_Equation3900 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3900 G := λ x y z w => h x x y z x w
theorem Equation4267_implies_Equation4103 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4103 G := λ x y z w => h x x y z x w
theorem Equation4379_implies_Equation4302 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4302 G := λ x y z w => h x x y z x w
theorem Equation4582_implies_Equation4418 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4418 G := λ x y z w => h x x y z x w
theorem Equation4694_implies_Equation4617 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4617 G := λ x y z w => h x x y z x w