import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation521 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ (x ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation724 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((z ∘ x) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation927 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ (x ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1130 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (z ∘ x)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1333 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ z) ∘ x) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1536 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ (x ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1739 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((z ∘ x) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1942 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ (x ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2145 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ (x ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2348 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (z ∘ x))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2551 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ z) ∘ x)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2754 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (z ∘ x)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2957 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ z)) ∘ x) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3160 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ z) ∘ x) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3363 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ (x ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3566 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((z ∘ x) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3769 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ (x ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3972 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (z ∘ x)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4175 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ z) ∘ x) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4348 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = z ∘ (x ∘ y)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4490 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (z ∘ x) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4663 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ y = (z ∘ x) ∘ y
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation521 (G : Type*) [Magma G] (h : Equation613 G) : Equation521 G := λ x y z => h x y y z x y
theorem Equation816_implies_Equation724 (G : Type*) [Magma G] (h : Equation816 G) : Equation724 G := λ x y z => h x y y z x y
theorem Equation1019_implies_Equation927 (G : Type*) [Magma G] (h : Equation1019 G) : Equation927 G := λ x y z => h x y y z x y
theorem Equation1222_implies_Equation1130 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1130 G := λ x y z => h x y y z x y
theorem Equation1425_implies_Equation1333 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1333 G := λ x y z => h x y y z x y
theorem Equation1628_implies_Equation1536 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1536 G := λ x y z => h x y y z x y
theorem Equation1831_implies_Equation1739 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1739 G := λ x y z => h x y y z x y
theorem Equation2034_implies_Equation1942 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1942 G := λ x y z => h x y y z x y
theorem Equation2237_implies_Equation2145 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2145 G := λ x y z => h x y y z x y
theorem Equation2440_implies_Equation2348 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2348 G := λ x y z => h x y y z x y
theorem Equation2643_implies_Equation2551 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2551 G := λ x y z => h x y y z x y
theorem Equation2846_implies_Equation2754 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2754 G := λ x y z => h x y y z x y
theorem Equation3049_implies_Equation2957 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2957 G := λ x y z => h x y y z x y
theorem Equation3252_implies_Equation3160 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3160 G := λ x y z => h x y y z x y
theorem Equation3455_implies_Equation3363 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3363 G := λ x y z => h x y y z x y
theorem Equation3658_implies_Equation3566 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3566 G := λ x y z => h x y y z x y
theorem Equation3861_implies_Equation3769 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3769 G := λ x y z => h x y y z x y
theorem Equation4064_implies_Equation3972 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3972 G := λ x y z => h x y y z x y
theorem Equation4267_implies_Equation4175 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4175 G := λ x y z => h x y y z x y
theorem Equation4379_implies_Equation4348 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4348 G := λ x y z => h x y y z x y
theorem Equation4582_implies_Equation4490 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4490 G := λ x y z => h x y y z x y
theorem Equation4694_implies_Equation4663 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4663 G := λ x y z => h x y y z x y