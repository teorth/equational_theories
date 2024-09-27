import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation516 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (y ∘ (z ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation719 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((y ∘ z) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation922 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ y) ∘ (z ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1125 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (y ∘ z)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1328 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ y) ∘ z) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1531 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (y ∘ (z ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1734 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((y ∘ z) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1937 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ y)) ∘ (z ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2140 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ y) ∘ (z ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2343 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (y ∘ z))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2546 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ y) ∘ z)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2749 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (y ∘ z)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2952 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ y)) ∘ z) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3155 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ y) ∘ z) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3358 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (y ∘ (z ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3561 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((y ∘ z) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3764 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ y) ∘ (z ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3967 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (y ∘ z)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4170 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ y) ∘ z) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4345 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = y ∘ (z ∘ x)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4485 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (y ∘ z) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4660 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ y = (y ∘ z) ∘ x
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation516 (G : Type*) [Magma G] (h : Equation613 G) : Equation516 G := λ x y z => h x y y y z x
theorem Equation816_implies_Equation719 (G : Type*) [Magma G] (h : Equation816 G) : Equation719 G := λ x y z => h x y y y z x
theorem Equation1019_implies_Equation922 (G : Type*) [Magma G] (h : Equation1019 G) : Equation922 G := λ x y z => h x y y y z x
theorem Equation1222_implies_Equation1125 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1125 G := λ x y z => h x y y y z x
theorem Equation1425_implies_Equation1328 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1328 G := λ x y z => h x y y y z x
theorem Equation1628_implies_Equation1531 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1531 G := λ x y z => h x y y y z x
theorem Equation1831_implies_Equation1734 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1734 G := λ x y z => h x y y y z x
theorem Equation2034_implies_Equation1937 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1937 G := λ x y z => h x y y y z x
theorem Equation2237_implies_Equation2140 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2140 G := λ x y z => h x y y y z x
theorem Equation2440_implies_Equation2343 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2343 G := λ x y z => h x y y y z x
theorem Equation2643_implies_Equation2546 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2546 G := λ x y z => h x y y y z x
theorem Equation2846_implies_Equation2749 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2749 G := λ x y z => h x y y y z x
theorem Equation3049_implies_Equation2952 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2952 G := λ x y z => h x y y y z x
theorem Equation3252_implies_Equation3155 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3155 G := λ x y z => h x y y y z x
theorem Equation3455_implies_Equation3358 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3358 G := λ x y z => h x y y y z x
theorem Equation3658_implies_Equation3561 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3561 G := λ x y z => h x y y y z x
theorem Equation3861_implies_Equation3764 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3764 G := λ x y z => h x y y y z x
theorem Equation4064_implies_Equation3967 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3967 G := λ x y z => h x y y y z x
theorem Equation4267_implies_Equation4170 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4170 G := λ x y z => h x y y y z x
theorem Equation4379_implies_Equation4345 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4345 G := λ x y z => h x y y y z x
theorem Equation4582_implies_Equation4485 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4485 G := λ x y z => h x y y y z x
theorem Equation4694_implies_Equation4660 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4660 G := λ x y z => h x y y y z x