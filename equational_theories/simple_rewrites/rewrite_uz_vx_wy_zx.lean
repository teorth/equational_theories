import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation479 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (y ∘ (z ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation682 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((y ∘ z) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation885 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ y) ∘ (z ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1088 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (y ∘ z)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1291 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ y) ∘ z) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1494 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (y ∘ (z ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1697 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((y ∘ z) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1900 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ y)) ∘ (z ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2103 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ y) ∘ (z ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2306 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (y ∘ z))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2509 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ y) ∘ z)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2712 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (y ∘ z)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2915 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ y)) ∘ z) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3118 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ y) ∘ z) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3321 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (y ∘ (z ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3524 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((y ∘ z) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3727 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ y) ∘ (z ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3930 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (y ∘ z)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4133 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ y) ∘ z) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4323 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = y ∘ (z ∘ x)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4448 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (y ∘ z) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4638 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (y ∘ z) ∘ x
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation479 (G : Type*) [Magma G] (h : Equation613 G) : Equation479 G := λ x y z => h x y x y z x
theorem Equation816_implies_Equation682 (G : Type*) [Magma G] (h : Equation816 G) : Equation682 G := λ x y z => h x y x y z x
theorem Equation1019_implies_Equation885 (G : Type*) [Magma G] (h : Equation1019 G) : Equation885 G := λ x y z => h x y x y z x
theorem Equation1222_implies_Equation1088 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1088 G := λ x y z => h x y x y z x
theorem Equation1425_implies_Equation1291 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1291 G := λ x y z => h x y x y z x
theorem Equation1628_implies_Equation1494 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1494 G := λ x y z => h x y x y z x
theorem Equation1831_implies_Equation1697 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1697 G := λ x y z => h x y x y z x
theorem Equation2034_implies_Equation1900 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1900 G := λ x y z => h x y x y z x
theorem Equation2237_implies_Equation2103 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2103 G := λ x y z => h x y x y z x
theorem Equation2440_implies_Equation2306 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2306 G := λ x y z => h x y x y z x
theorem Equation2643_implies_Equation2509 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2509 G := λ x y z => h x y x y z x
theorem Equation2846_implies_Equation2712 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2712 G := λ x y z => h x y x y z x
theorem Equation3049_implies_Equation2915 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2915 G := λ x y z => h x y x y z x
theorem Equation3252_implies_Equation3118 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3118 G := λ x y z => h x y x y z x
theorem Equation3455_implies_Equation3321 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3321 G := λ x y z => h x y x y z x
theorem Equation3658_implies_Equation3524 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3524 G := λ x y z => h x y x y z x
theorem Equation3861_implies_Equation3727 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3727 G := λ x y z => h x y x y z x
theorem Equation4064_implies_Equation3930 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3930 G := λ x y z => h x y x y z x
theorem Equation4267_implies_Equation4133 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4133 G := λ x y z => h x y x y z x
theorem Equation4379_implies_Equation4323 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4323 G := λ x y z => h x y x y z x
theorem Equation4582_implies_Equation4448 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4448 G := λ x y z => h x y x y z x
theorem Equation4694_implies_Equation4638 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4638 G := λ x y z => h x y x y z x