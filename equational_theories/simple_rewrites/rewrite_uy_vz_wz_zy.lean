import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation526 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ (y ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation729 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((z ∘ y) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation932 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ (y ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1135 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (z ∘ y)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1338 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ z) ∘ y) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1541 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ (y ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1744 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((z ∘ y) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1947 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ (y ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2150 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ (y ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2353 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (z ∘ y))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2556 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ z) ∘ y)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2759 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (z ∘ y)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2962 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ z)) ∘ y) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3165 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ z) ∘ y) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3368 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ (y ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3571 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((z ∘ y) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3774 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ (y ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3977 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (z ∘ y)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4180 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ z) ∘ y) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4495 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (z ∘ y) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation526 (G : Type*) [Magma G] (h : Equation613 G) : Equation526 G := λ x y z => h x y y z y z
theorem Equation816_implies_Equation729 (G : Type*) [Magma G] (h : Equation816 G) : Equation729 G := λ x y z => h x y y z y z
theorem Equation1019_implies_Equation932 (G : Type*) [Magma G] (h : Equation1019 G) : Equation932 G := λ x y z => h x y y z y z
theorem Equation1222_implies_Equation1135 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1135 G := λ x y z => h x y y z y z
theorem Equation1425_implies_Equation1338 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1338 G := λ x y z => h x y y z y z
theorem Equation1628_implies_Equation1541 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1541 G := λ x y z => h x y y z y z
theorem Equation1831_implies_Equation1744 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1744 G := λ x y z => h x y y z y z
theorem Equation2034_implies_Equation1947 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1947 G := λ x y z => h x y y z y z
theorem Equation2237_implies_Equation2150 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2150 G := λ x y z => h x y y z y z
theorem Equation2440_implies_Equation2353 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2353 G := λ x y z => h x y y z y z
theorem Equation2643_implies_Equation2556 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2556 G := λ x y z => h x y y z y z
theorem Equation2846_implies_Equation2759 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2759 G := λ x y z => h x y y z y z
theorem Equation3049_implies_Equation2962 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2962 G := λ x y z => h x y y z y z
theorem Equation3252_implies_Equation3165 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3165 G := λ x y z => h x y y z y z
theorem Equation3455_implies_Equation3368 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3368 G := λ x y z => h x y y z y z
theorem Equation3658_implies_Equation3571 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3571 G := λ x y z => h x y y z y z
theorem Equation3861_implies_Equation3774 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3774 G := λ x y z => h x y y z y z
theorem Equation4064_implies_Equation3977 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3977 G := λ x y z => h x y y z y z
theorem Equation4267_implies_Equation4180 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4180 G := λ x y z => h x y y z y z
theorem Equation4582_implies_Equation4495 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4495 G := λ x y z => h x y y z y z