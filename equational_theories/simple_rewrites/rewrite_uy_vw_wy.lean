import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation561 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (y ∘ w)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation764 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ y) ∘ w))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation967 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (y ∘ w))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1170 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ y)) ∘ w)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1373 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ y) ∘ w)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1576 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (y ∘ w))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1779 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ y) ∘ w)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1982 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (y ∘ w)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2185 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (y ∘ w)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2388 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ y))) ∘ w
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2591 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ y)) ∘ w
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2794 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ y)) ∘ w
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2997 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ y) ∘ w
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3200 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ y) ∘ w
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3403 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (y ∘ w))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3606 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ y) ∘ w)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3809 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (y ∘ w)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4012 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ y)) ∘ w
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4215 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ y) ∘ w
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4530 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ y) ∘ w
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation561 (G : Type*) [Magma G] (h : Equation613 G) : Equation561 G := λ x y z w => h x y z y y w
theorem Equation816_implies_Equation764 (G : Type*) [Magma G] (h : Equation816 G) : Equation764 G := λ x y z w => h x y z y y w
theorem Equation1019_implies_Equation967 (G : Type*) [Magma G] (h : Equation1019 G) : Equation967 G := λ x y z w => h x y z y y w
theorem Equation1222_implies_Equation1170 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1170 G := λ x y z w => h x y z y y w
theorem Equation1425_implies_Equation1373 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1373 G := λ x y z w => h x y z y y w
theorem Equation1628_implies_Equation1576 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1576 G := λ x y z w => h x y z y y w
theorem Equation1831_implies_Equation1779 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1779 G := λ x y z w => h x y z y y w
theorem Equation2034_implies_Equation1982 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1982 G := λ x y z w => h x y z y y w
theorem Equation2237_implies_Equation2185 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2185 G := λ x y z w => h x y z y y w
theorem Equation2440_implies_Equation2388 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2388 G := λ x y z w => h x y z y y w
theorem Equation2643_implies_Equation2591 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2591 G := λ x y z w => h x y z y y w
theorem Equation2846_implies_Equation2794 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2794 G := λ x y z w => h x y z y y w
theorem Equation3049_implies_Equation2997 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2997 G := λ x y z w => h x y z y y w
theorem Equation3252_implies_Equation3200 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3200 G := λ x y z w => h x y z y y w
theorem Equation3455_implies_Equation3403 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3403 G := λ x y z w => h x y z y y w
theorem Equation3658_implies_Equation3606 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3606 G := λ x y z w => h x y z y y w
theorem Equation3861_implies_Equation3809 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3809 G := λ x y z w => h x y z y y w
theorem Equation4064_implies_Equation4012 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4012 G := λ x y z w => h x y z y y w
theorem Equation4267_implies_Equation4215 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4215 G := λ x y z w => h x y z y y w
theorem Equation4582_implies_Equation4530 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4530 G := λ x y z w => h x y z y y w