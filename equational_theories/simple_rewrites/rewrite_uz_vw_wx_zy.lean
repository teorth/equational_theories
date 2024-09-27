import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation509 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (x ∘ (z ∘ w)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation712 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((x ∘ z) ∘ w))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation915 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ x) ∘ (z ∘ w))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1118 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (x ∘ z)) ∘ w)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1321 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ x) ∘ z) ∘ w)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1524 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (x ∘ (z ∘ w))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1727 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((x ∘ z) ∘ w)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1930 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ x)) ∘ (z ∘ w)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2133 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ x) ∘ (z ∘ w)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2336 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (x ∘ z))) ∘ w
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2539 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ x) ∘ z)) ∘ w
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2742 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (x ∘ z)) ∘ w
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2945 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ x)) ∘ z) ∘ w
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3148 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ x) ∘ z) ∘ w
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3351 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (x ∘ (z ∘ w))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3554 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((x ∘ z) ∘ w)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3757 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ x) ∘ (z ∘ w)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3960 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (x ∘ z)) ∘ w
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4163 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ x) ∘ z) ∘ w
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4342 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = x ∘ (z ∘ w)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4478 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (x ∘ z) ∘ w
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4657 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ y = (x ∘ z) ∘ w
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation509 (G : Type*) [Magma G] (h : Equation613 G) : Equation509 G := λ x y z w => h x y y x z w
theorem Equation816_implies_Equation712 (G : Type*) [Magma G] (h : Equation816 G) : Equation712 G := λ x y z w => h x y y x z w
theorem Equation1019_implies_Equation915 (G : Type*) [Magma G] (h : Equation1019 G) : Equation915 G := λ x y z w => h x y y x z w
theorem Equation1222_implies_Equation1118 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1118 G := λ x y z w => h x y y x z w
theorem Equation1425_implies_Equation1321 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1321 G := λ x y z w => h x y y x z w
theorem Equation1628_implies_Equation1524 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1524 G := λ x y z w => h x y y x z w
theorem Equation1831_implies_Equation1727 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1727 G := λ x y z w => h x y y x z w
theorem Equation2034_implies_Equation1930 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1930 G := λ x y z w => h x y y x z w
theorem Equation2237_implies_Equation2133 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2133 G := λ x y z w => h x y y x z w
theorem Equation2440_implies_Equation2336 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2336 G := λ x y z w => h x y y x z w
theorem Equation2643_implies_Equation2539 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2539 G := λ x y z w => h x y y x z w
theorem Equation2846_implies_Equation2742 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2742 G := λ x y z w => h x y y x z w
theorem Equation3049_implies_Equation2945 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2945 G := λ x y z w => h x y y x z w
theorem Equation3252_implies_Equation3148 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3148 G := λ x y z w => h x y y x z w
theorem Equation3455_implies_Equation3351 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3351 G := λ x y z w => h x y y x z w
theorem Equation3658_implies_Equation3554 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3554 G := λ x y z w => h x y y x z w
theorem Equation3861_implies_Equation3757 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3757 G := λ x y z w => h x y y x z w
theorem Equation4064_implies_Equation3960 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3960 G := λ x y z w => h x y y x z w
theorem Equation4267_implies_Equation4163 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4163 G := λ x y z w => h x y y x z w
theorem Equation4379_implies_Equation4342 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4342 G := λ x y z w => h x y y x z w
theorem Equation4582_implies_Equation4478 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4478 G := λ x y z w => h x y y x z w
theorem Equation4694_implies_Equation4657 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4657 G := λ x y z w => h x y y x z w