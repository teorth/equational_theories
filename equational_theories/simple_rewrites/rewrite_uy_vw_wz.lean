import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation578 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (y ∘ w)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation781 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ y) ∘ w))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation984 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (y ∘ w))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1187 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ y)) ∘ w)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1390 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ y) ∘ w)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1593 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (y ∘ w))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1796 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ y) ∘ w)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1999 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (y ∘ w)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2202 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (y ∘ w)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2405 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ y))) ∘ w
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2608 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ y)) ∘ w
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2811 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ y)) ∘ w
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3014 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ y) ∘ w
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3217 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ y) ∘ w
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3420 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (y ∘ w))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3623 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ y) ∘ w)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3826 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (y ∘ w)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4029 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ y)) ∘ w
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4232 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ y) ∘ w
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4370 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = z ∘ (y ∘ w)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4547 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ y) ∘ w
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4685 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (z ∘ y) ∘ w
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation578 (G : Type*) [Magma G] (h : Equation613 G) : Equation578 G := λ x y z w => h x y z z y w
theorem Equation816_implies_Equation781 (G : Type*) [Magma G] (h : Equation816 G) : Equation781 G := λ x y z w => h x y z z y w
theorem Equation1019_implies_Equation984 (G : Type*) [Magma G] (h : Equation1019 G) : Equation984 G := λ x y z w => h x y z z y w
theorem Equation1222_implies_Equation1187 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1187 G := λ x y z w => h x y z z y w
theorem Equation1425_implies_Equation1390 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1390 G := λ x y z w => h x y z z y w
theorem Equation1628_implies_Equation1593 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1593 G := λ x y z w => h x y z z y w
theorem Equation1831_implies_Equation1796 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1796 G := λ x y z w => h x y z z y w
theorem Equation2034_implies_Equation1999 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1999 G := λ x y z w => h x y z z y w
theorem Equation2237_implies_Equation2202 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2202 G := λ x y z w => h x y z z y w
theorem Equation2440_implies_Equation2405 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2405 G := λ x y z w => h x y z z y w
theorem Equation2643_implies_Equation2608 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2608 G := λ x y z w => h x y z z y w
theorem Equation2846_implies_Equation2811 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2811 G := λ x y z w => h x y z z y w
theorem Equation3049_implies_Equation3014 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3014 G := λ x y z w => h x y z z y w
theorem Equation3252_implies_Equation3217 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3217 G := λ x y z w => h x y z z y w
theorem Equation3455_implies_Equation3420 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3420 G := λ x y z w => h x y z z y w
theorem Equation3658_implies_Equation3623 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3623 G := λ x y z w => h x y z z y w
theorem Equation3861_implies_Equation3826 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3826 G := λ x y z w => h x y z z y w
theorem Equation4064_implies_Equation4029 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4029 G := λ x y z w => h x y z z y w
theorem Equation4267_implies_Equation4232 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4232 G := λ x y z w => h x y z z y w
theorem Equation4379_implies_Equation4370 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4370 G := λ x y z w => h x y z z y w
theorem Equation4582_implies_Equation4547 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4547 G := λ x y z w => h x y z z y w
theorem Equation4694_implies_Equation4685 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4685 G := λ x y z w => h x y z z y w