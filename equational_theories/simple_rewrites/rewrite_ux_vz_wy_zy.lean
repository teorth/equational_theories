import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation512 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (y ∘ (x ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation715 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((y ∘ x) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation918 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ y) ∘ (x ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1121 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (y ∘ x)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1324 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ y) ∘ x) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1527 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (y ∘ (x ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1730 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((y ∘ x) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1933 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ y)) ∘ (x ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2136 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ y) ∘ (x ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2339 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (y ∘ x))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2542 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ y) ∘ x)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2745 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (y ∘ x)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2948 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ y)) ∘ x) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3151 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ y) ∘ x) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3354 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (y ∘ (x ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3557 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((y ∘ x) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3760 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ y) ∘ (x ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3963 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (y ∘ x)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4166 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ y) ∘ x) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4344 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = y ∘ (x ∘ z)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4481 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (y ∘ x) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4659 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ y = (y ∘ x) ∘ z
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation512 (G : Type*) [Magma G] (h : Equation613 G) : Equation512 G := λ x y z => h x y y y x z
theorem Equation816_implies_Equation715 (G : Type*) [Magma G] (h : Equation816 G) : Equation715 G := λ x y z => h x y y y x z
theorem Equation1019_implies_Equation918 (G : Type*) [Magma G] (h : Equation1019 G) : Equation918 G := λ x y z => h x y y y x z
theorem Equation1222_implies_Equation1121 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1121 G := λ x y z => h x y y y x z
theorem Equation1425_implies_Equation1324 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1324 G := λ x y z => h x y y y x z
theorem Equation1628_implies_Equation1527 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1527 G := λ x y z => h x y y y x z
theorem Equation1831_implies_Equation1730 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1730 G := λ x y z => h x y y y x z
theorem Equation2034_implies_Equation1933 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1933 G := λ x y z => h x y y y x z
theorem Equation2237_implies_Equation2136 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2136 G := λ x y z => h x y y y x z
theorem Equation2440_implies_Equation2339 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2339 G := λ x y z => h x y y y x z
theorem Equation2643_implies_Equation2542 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2542 G := λ x y z => h x y y y x z
theorem Equation2846_implies_Equation2745 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2745 G := λ x y z => h x y y y x z
theorem Equation3049_implies_Equation2948 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2948 G := λ x y z => h x y y y x z
theorem Equation3252_implies_Equation3151 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3151 G := λ x y z => h x y y y x z
theorem Equation3455_implies_Equation3354 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3354 G := λ x y z => h x y y y x z
theorem Equation3658_implies_Equation3557 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3557 G := λ x y z => h x y y y x z
theorem Equation3861_implies_Equation3760 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3760 G := λ x y z => h x y y y x z
theorem Equation4064_implies_Equation3963 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3963 G := λ x y z => h x y y y x z
theorem Equation4267_implies_Equation4166 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4166 G := λ x y z => h x y y y x z
theorem Equation4379_implies_Equation4344 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4344 G := λ x y z => h x y y y x z
theorem Equation4582_implies_Equation4481 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4481 G := λ x y z => h x y y y x z
theorem Equation4694_implies_Equation4659 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4659 G := λ x y z => h x y y y x z