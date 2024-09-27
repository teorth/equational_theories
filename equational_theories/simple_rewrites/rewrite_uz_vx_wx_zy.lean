import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation506 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (x ∘ (z ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation709 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((x ∘ z) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation912 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ x) ∘ (z ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1115 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (x ∘ z)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1318 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ x) ∘ z) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1521 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (x ∘ (z ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1724 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((x ∘ z) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1927 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ x)) ∘ (z ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2130 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ x) ∘ (z ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2333 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (x ∘ z))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2536 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ x) ∘ z)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2739 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (x ∘ z)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2942 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ x)) ∘ z) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3145 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ x) ∘ z) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3348 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (x ∘ (z ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3551 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((x ∘ z) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3754 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ x) ∘ (z ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3957 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (x ∘ z)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4160 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ x) ∘ z) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4475 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (x ∘ z) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation506 (G : Type*) [Magma G] (h : Equation613 G) : Equation506 G := λ x y z => h x y y x z x
theorem Equation816_implies_Equation709 (G : Type*) [Magma G] (h : Equation816 G) : Equation709 G := λ x y z => h x y y x z x
theorem Equation1019_implies_Equation912 (G : Type*) [Magma G] (h : Equation1019 G) : Equation912 G := λ x y z => h x y y x z x
theorem Equation1222_implies_Equation1115 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1115 G := λ x y z => h x y y x z x
theorem Equation1425_implies_Equation1318 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1318 G := λ x y z => h x y y x z x
theorem Equation1628_implies_Equation1521 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1521 G := λ x y z => h x y y x z x
theorem Equation1831_implies_Equation1724 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1724 G := λ x y z => h x y y x z x
theorem Equation2034_implies_Equation1927 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1927 G := λ x y z => h x y y x z x
theorem Equation2237_implies_Equation2130 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2130 G := λ x y z => h x y y x z x
theorem Equation2440_implies_Equation2333 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2333 G := λ x y z => h x y y x z x
theorem Equation2643_implies_Equation2536 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2536 G := λ x y z => h x y y x z x
theorem Equation2846_implies_Equation2739 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2739 G := λ x y z => h x y y x z x
theorem Equation3049_implies_Equation2942 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2942 G := λ x y z => h x y y x z x
theorem Equation3252_implies_Equation3145 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3145 G := λ x y z => h x y y x z x
theorem Equation3455_implies_Equation3348 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3348 G := λ x y z => h x y y x z x
theorem Equation3658_implies_Equation3551 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3551 G := λ x y z => h x y y x z x
theorem Equation3861_implies_Equation3754 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3754 G := λ x y z => h x y y x z x
theorem Equation4064_implies_Equation3957 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3957 G := λ x y z => h x y y x z x
theorem Equation4267_implies_Equation4160 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4160 G := λ x y z => h x y y x z x
theorem Equation4582_implies_Equation4475 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4475 G := λ x y z => h x y y x z x