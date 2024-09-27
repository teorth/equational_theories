import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation585 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (w ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation788 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ w) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation991 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (w ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1194 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ w)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1397 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ w) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1600 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (w ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1803 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ w) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation2006 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (w ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2209 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (w ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2412 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ w))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2615 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ w)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2818 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ w)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3021 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ w) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3224 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ w) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3427 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (w ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3630 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ w) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3833 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (w ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4036 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ w)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4239 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ w) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4554 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ w) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation585 (G : Type*) [Magma G] (h : Equation613 G) : Equation585 G := λ x y z w => h x y z z w z
theorem Equation816_implies_Equation788 (G : Type*) [Magma G] (h : Equation816 G) : Equation788 G := λ x y z w => h x y z z w z
theorem Equation1019_implies_Equation991 (G : Type*) [Magma G] (h : Equation1019 G) : Equation991 G := λ x y z w => h x y z z w z
theorem Equation1222_implies_Equation1194 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1194 G := λ x y z w => h x y z z w z
theorem Equation1425_implies_Equation1397 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1397 G := λ x y z w => h x y z z w z
theorem Equation1628_implies_Equation1600 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1600 G := λ x y z w => h x y z z w z
theorem Equation1831_implies_Equation1803 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1803 G := λ x y z w => h x y z z w z
theorem Equation2034_implies_Equation2006 (G : Type*) [Magma G] (h : Equation2034 G) : Equation2006 G := λ x y z w => h x y z z w z
theorem Equation2237_implies_Equation2209 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2209 G := λ x y z w => h x y z z w z
theorem Equation2440_implies_Equation2412 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2412 G := λ x y z w => h x y z z w z
theorem Equation2643_implies_Equation2615 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2615 G := λ x y z w => h x y z z w z
theorem Equation2846_implies_Equation2818 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2818 G := λ x y z w => h x y z z w z
theorem Equation3049_implies_Equation3021 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3021 G := λ x y z w => h x y z z w z
theorem Equation3252_implies_Equation3224 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3224 G := λ x y z w => h x y z z w z
theorem Equation3455_implies_Equation3427 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3427 G := λ x y z w => h x y z z w z
theorem Equation3658_implies_Equation3630 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3630 G := λ x y z w => h x y z z w z
theorem Equation3861_implies_Equation3833 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3833 G := λ x y z w => h x y z z w z
theorem Equation4064_implies_Equation4036 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4036 G := λ x y z w => h x y z z w z
theorem Equation4267_implies_Equation4239 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4239 G := λ x y z w => h x y z z w z
theorem Equation4582_implies_Equation4554 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4554 G := λ x y z w => h x y z z w z