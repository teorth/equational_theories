import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation556 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ (x ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation759 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((y ∘ x) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation962 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ (x ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1165 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (y ∘ x)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1368 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ y) ∘ x) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1571 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ (x ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1774 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((y ∘ x) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1977 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ (x ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2180 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ (x ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2383 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (y ∘ x))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2586 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ y) ∘ x)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2789 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (y ∘ x)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2992 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ y)) ∘ x) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3195 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ y) ∘ x) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3398 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ (x ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3601 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((y ∘ x) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3804 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ (x ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4007 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (y ∘ x)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4210 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ y) ∘ x) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4362 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = y ∘ (x ∘ z)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4525 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (y ∘ x) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4677 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ z = (y ∘ x) ∘ z
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation556 (G : Type*) [Magma G] (h : Equation613 G) : Equation556 G := λ x y z => h x y z y x z
theorem Equation816_implies_Equation759 (G : Type*) [Magma G] (h : Equation816 G) : Equation759 G := λ x y z => h x y z y x z
theorem Equation1019_implies_Equation962 (G : Type*) [Magma G] (h : Equation1019 G) : Equation962 G := λ x y z => h x y z y x z
theorem Equation1222_implies_Equation1165 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1165 G := λ x y z => h x y z y x z
theorem Equation1425_implies_Equation1368 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1368 G := λ x y z => h x y z y x z
theorem Equation1628_implies_Equation1571 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1571 G := λ x y z => h x y z y x z
theorem Equation1831_implies_Equation1774 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1774 G := λ x y z => h x y z y x z
theorem Equation2034_implies_Equation1977 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1977 G := λ x y z => h x y z y x z
theorem Equation2237_implies_Equation2180 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2180 G := λ x y z => h x y z y x z
theorem Equation2440_implies_Equation2383 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2383 G := λ x y z => h x y z y x z
theorem Equation2643_implies_Equation2586 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2586 G := λ x y z => h x y z y x z
theorem Equation2846_implies_Equation2789 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2789 G := λ x y z => h x y z y x z
theorem Equation3049_implies_Equation2992 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2992 G := λ x y z => h x y z y x z
theorem Equation3252_implies_Equation3195 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3195 G := λ x y z => h x y z y x z
theorem Equation3455_implies_Equation3398 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3398 G := λ x y z => h x y z y x z
theorem Equation3658_implies_Equation3601 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3601 G := λ x y z => h x y z y x z
theorem Equation3861_implies_Equation3804 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3804 G := λ x y z => h x y z y x z
theorem Equation4064_implies_Equation4007 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4007 G := λ x y z => h x y z y x z
theorem Equation4267_implies_Equation4210 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4210 G := λ x y z => h x y z y x z
theorem Equation4379_implies_Equation4362 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4362 G := λ x y z => h x y z y x z
theorem Equation4582_implies_Equation4525 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4525 G := λ x y z => h x y z y x z
theorem Equation4694_implies_Equation4677 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4677 G := λ x y z => h x y z y x z