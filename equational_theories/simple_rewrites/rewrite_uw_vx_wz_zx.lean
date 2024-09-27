import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation495 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (w ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation698 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ w) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation901 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (w ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1104 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ w)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1307 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ w) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1510 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (w ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1713 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ w) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1916 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (w ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2119 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (w ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2322 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ w))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2525 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ w)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2728 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ w)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2931 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ w) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3134 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ w) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3337 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (w ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3540 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ w) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3743 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (w ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3946 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ w)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4149 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ w) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4334 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = z ∘ (w ∘ x)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4464 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ w) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4649 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ x = (z ∘ w) ∘ x
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation495 (G : Type*) [Magma G] (h : Equation613 G) : Equation495 G := λ x y z w => h x y x z w x
theorem Equation816_implies_Equation698 (G : Type*) [Magma G] (h : Equation816 G) : Equation698 G := λ x y z w => h x y x z w x
theorem Equation1019_implies_Equation901 (G : Type*) [Magma G] (h : Equation1019 G) : Equation901 G := λ x y z w => h x y x z w x
theorem Equation1222_implies_Equation1104 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1104 G := λ x y z w => h x y x z w x
theorem Equation1425_implies_Equation1307 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1307 G := λ x y z w => h x y x z w x
theorem Equation1628_implies_Equation1510 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1510 G := λ x y z w => h x y x z w x
theorem Equation1831_implies_Equation1713 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1713 G := λ x y z w => h x y x z w x
theorem Equation2034_implies_Equation1916 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1916 G := λ x y z w => h x y x z w x
theorem Equation2237_implies_Equation2119 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2119 G := λ x y z w => h x y x z w x
theorem Equation2440_implies_Equation2322 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2322 G := λ x y z w => h x y x z w x
theorem Equation2643_implies_Equation2525 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2525 G := λ x y z w => h x y x z w x
theorem Equation2846_implies_Equation2728 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2728 G := λ x y z w => h x y x z w x
theorem Equation3049_implies_Equation2931 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2931 G := λ x y z w => h x y x z w x
theorem Equation3252_implies_Equation3134 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3134 G := λ x y z w => h x y x z w x
theorem Equation3455_implies_Equation3337 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3337 G := λ x y z w => h x y x z w x
theorem Equation3658_implies_Equation3540 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3540 G := λ x y z w => h x y x z w x
theorem Equation3861_implies_Equation3743 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3743 G := λ x y z w => h x y x z w x
theorem Equation4064_implies_Equation3946 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3946 G := λ x y z w => h x y x z w x
theorem Equation4267_implies_Equation4149 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4149 G := λ x y z w => h x y x z w x
theorem Equation4379_implies_Equation4334 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4334 G := λ x y z w => h x y x z w x
theorem Equation4582_implies_Equation4464 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4464 G := λ x y z w => h x y x z w x
theorem Equation4694_implies_Equation4649 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4649 G := λ x y z w => h x y x z w x