import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation539 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ (x ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation742 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((x ∘ x) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation945 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ (x ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1148 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (x ∘ x)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1351 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ x) ∘ x) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1554 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ (x ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1757 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((x ∘ x) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1960 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ (x ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2163 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ (x ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2366 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (x ∘ x))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2569 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ x) ∘ x)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2772 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (x ∘ x)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2975 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ x)) ∘ x) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3178 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ x) ∘ x) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3381 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ (x ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3584 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((x ∘ x) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3787 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ (x ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3990 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (x ∘ x)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4193 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ x) ∘ x) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4508 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ x) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation539 (G : Type*) [Magma G] (h : Equation613 G) : Equation539 G := λ x y z => h x y z x x z
theorem Equation816_implies_Equation742 (G : Type*) [Magma G] (h : Equation816 G) : Equation742 G := λ x y z => h x y z x x z
theorem Equation1019_implies_Equation945 (G : Type*) [Magma G] (h : Equation1019 G) : Equation945 G := λ x y z => h x y z x x z
theorem Equation1222_implies_Equation1148 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1148 G := λ x y z => h x y z x x z
theorem Equation1425_implies_Equation1351 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1351 G := λ x y z => h x y z x x z
theorem Equation1628_implies_Equation1554 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1554 G := λ x y z => h x y z x x z
theorem Equation1831_implies_Equation1757 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1757 G := λ x y z => h x y z x x z
theorem Equation2034_implies_Equation1960 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1960 G := λ x y z => h x y z x x z
theorem Equation2237_implies_Equation2163 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2163 G := λ x y z => h x y z x x z
theorem Equation2440_implies_Equation2366 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2366 G := λ x y z => h x y z x x z
theorem Equation2643_implies_Equation2569 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2569 G := λ x y z => h x y z x x z
theorem Equation2846_implies_Equation2772 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2772 G := λ x y z => h x y z x x z
theorem Equation3049_implies_Equation2975 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2975 G := λ x y z => h x y z x x z
theorem Equation3252_implies_Equation3178 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3178 G := λ x y z => h x y z x x z
theorem Equation3455_implies_Equation3381 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3381 G := λ x y z => h x y z x x z
theorem Equation3658_implies_Equation3584 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3584 G := λ x y z => h x y z x x z
theorem Equation3861_implies_Equation3787 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3787 G := λ x y z => h x y z x x z
theorem Equation4064_implies_Equation3990 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3990 G := λ x y z => h x y z x x z
theorem Equation4267_implies_Equation4193 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4193 G := λ x y z => h x y z x x z
theorem Equation4582_implies_Equation4508 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4508 G := λ x y z => h x y z x x z