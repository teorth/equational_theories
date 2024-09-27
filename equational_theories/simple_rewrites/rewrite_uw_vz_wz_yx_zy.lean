import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation460 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (w ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation663 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ w) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation866 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (w ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1069 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1272 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ w) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1475 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (w ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1678 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1881 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2084 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2287 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2490 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2693 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2896 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3099 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3302 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (w ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3505 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ w) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3708 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (w ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3911 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ w)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4114 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ w) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4311 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (w ∘ z)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4429 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ w) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4626 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ w) ∘ z
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation460 (G : Type*) [Magma G] (h : Equation613 G) : Equation460 G := λ x y z w => h x x y z w z
theorem Equation816_implies_Equation663 (G : Type*) [Magma G] (h : Equation816 G) : Equation663 G := λ x y z w => h x x y z w z
theorem Equation1019_implies_Equation866 (G : Type*) [Magma G] (h : Equation1019 G) : Equation866 G := λ x y z w => h x x y z w z
theorem Equation1222_implies_Equation1069 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1069 G := λ x y z w => h x x y z w z
theorem Equation1425_implies_Equation1272 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1272 G := λ x y z w => h x x y z w z
theorem Equation1628_implies_Equation1475 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1475 G := λ x y z w => h x x y z w z
theorem Equation1831_implies_Equation1678 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1678 G := λ x y z w => h x x y z w z
theorem Equation2034_implies_Equation1881 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1881 G := λ x y z w => h x x y z w z
theorem Equation2237_implies_Equation2084 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2084 G := λ x y z w => h x x y z w z
theorem Equation2440_implies_Equation2287 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2287 G := λ x y z w => h x x y z w z
theorem Equation2643_implies_Equation2490 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2490 G := λ x y z w => h x x y z w z
theorem Equation2846_implies_Equation2693 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2693 G := λ x y z w => h x x y z w z
theorem Equation3049_implies_Equation2896 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2896 G := λ x y z w => h x x y z w z
theorem Equation3252_implies_Equation3099 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3099 G := λ x y z w => h x x y z w z
theorem Equation3455_implies_Equation3302 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3302 G := λ x y z w => h x x y z w z
theorem Equation3658_implies_Equation3505 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3505 G := λ x y z w => h x x y z w z
theorem Equation3861_implies_Equation3708 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3708 G := λ x y z w => h x x y z w z
theorem Equation4064_implies_Equation3911 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3911 G := λ x y z w => h x x y z w z
theorem Equation4267_implies_Equation4114 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4114 G := λ x y z w => h x x y z w z
theorem Equation4379_implies_Equation4311 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4311 G := λ x y z w => h x x y z w z
theorem Equation4582_implies_Equation4429 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4429 G := λ x y z w => h x x y z w z
theorem Equation4694_implies_Equation4626 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4626 G := λ x y z w => h x x y z w z