import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation496 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (w ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation699 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ w) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation902 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (w ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1105 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ w)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1308 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ w) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1511 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (w ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1714 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ w) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1917 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (w ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2120 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (w ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2323 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ w))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2526 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ w)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2729 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ w)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2932 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ w) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3135 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ w) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3338 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (w ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3541 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ w) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3744 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (w ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3947 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ w)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4150 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ w) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4335 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = z ∘ (w ∘ y)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4465 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ w) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4650 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ x = (z ∘ w) ∘ y
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation496 (G : Type*) [Magma G] (h : Equation613 G) : Equation496 G := λ x y z w => h x y x z w y
theorem Equation816_implies_Equation699 (G : Type*) [Magma G] (h : Equation816 G) : Equation699 G := λ x y z w => h x y x z w y
theorem Equation1019_implies_Equation902 (G : Type*) [Magma G] (h : Equation1019 G) : Equation902 G := λ x y z w => h x y x z w y
theorem Equation1222_implies_Equation1105 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1105 G := λ x y z w => h x y x z w y
theorem Equation1425_implies_Equation1308 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1308 G := λ x y z w => h x y x z w y
theorem Equation1628_implies_Equation1511 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1511 G := λ x y z w => h x y x z w y
theorem Equation1831_implies_Equation1714 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1714 G := λ x y z w => h x y x z w y
theorem Equation2034_implies_Equation1917 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1917 G := λ x y z w => h x y x z w y
theorem Equation2237_implies_Equation2120 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2120 G := λ x y z w => h x y x z w y
theorem Equation2440_implies_Equation2323 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2323 G := λ x y z w => h x y x z w y
theorem Equation2643_implies_Equation2526 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2526 G := λ x y z w => h x y x z w y
theorem Equation2846_implies_Equation2729 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2729 G := λ x y z w => h x y x z w y
theorem Equation3049_implies_Equation2932 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2932 G := λ x y z w => h x y x z w y
theorem Equation3252_implies_Equation3135 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3135 G := λ x y z w => h x y x z w y
theorem Equation3455_implies_Equation3338 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3338 G := λ x y z w => h x y x z w y
theorem Equation3658_implies_Equation3541 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3541 G := λ x y z w => h x y x z w y
theorem Equation3861_implies_Equation3744 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3744 G := λ x y z w => h x y x z w y
theorem Equation4064_implies_Equation3947 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3947 G := λ x y z w => h x y x z w y
theorem Equation4267_implies_Equation4150 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4150 G := λ x y z w => h x y x z w y
theorem Equation4379_implies_Equation4335 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4335 G := λ x y z w => h x y x z w y
theorem Equation4582_implies_Equation4465 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4465 G := λ x y z w => h x y x z w y
theorem Equation4694_implies_Equation4650 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4650 G := λ x y z w => h x y x z w y