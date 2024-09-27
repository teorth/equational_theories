import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation424 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ (y ∘ (z ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation627 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ ((y ∘ z) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation830 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ y) ∘ (z ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1033 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ (y ∘ z)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1236 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((x ∘ y) ∘ z) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1439 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ (y ∘ (z ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1642 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ ((y ∘ z) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1845 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ y)) ∘ (z ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2048 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ y) ∘ (z ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2251 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ (y ∘ z))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2454 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((x ∘ y) ∘ z)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2657 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ (y ∘ z)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2860 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (x ∘ y)) ∘ z) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3063 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ x) ∘ y) ∘ z) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3266 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ (y ∘ (z ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3469 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ ((y ∘ z) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3672 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ y) ∘ (z ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3875 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ (y ∘ z)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4078 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((x ∘ y) ∘ z) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4280 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ x) = y ∘ (z ∘ z)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4393 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ x) = (y ∘ z) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4595 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ x = (y ∘ z) ∘ z
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation424 (G : Type*) [Magma G] (h : Equation613 G) : Equation424 G := λ x y z => h x x x y z z
theorem Equation816_implies_Equation627 (G : Type*) [Magma G] (h : Equation816 G) : Equation627 G := λ x y z => h x x x y z z
theorem Equation1019_implies_Equation830 (G : Type*) [Magma G] (h : Equation1019 G) : Equation830 G := λ x y z => h x x x y z z
theorem Equation1222_implies_Equation1033 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1033 G := λ x y z => h x x x y z z
theorem Equation1425_implies_Equation1236 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1236 G := λ x y z => h x x x y z z
theorem Equation1628_implies_Equation1439 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1439 G := λ x y z => h x x x y z z
theorem Equation1831_implies_Equation1642 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1642 G := λ x y z => h x x x y z z
theorem Equation2034_implies_Equation1845 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1845 G := λ x y z => h x x x y z z
theorem Equation2237_implies_Equation2048 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2048 G := λ x y z => h x x x y z z
theorem Equation2440_implies_Equation2251 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2251 G := λ x y z => h x x x y z z
theorem Equation2643_implies_Equation2454 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2454 G := λ x y z => h x x x y z z
theorem Equation2846_implies_Equation2657 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2657 G := λ x y z => h x x x y z z
theorem Equation3049_implies_Equation2860 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2860 G := λ x y z => h x x x y z z
theorem Equation3252_implies_Equation3063 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3063 G := λ x y z => h x x x y z z
theorem Equation3455_implies_Equation3266 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3266 G := λ x y z => h x x x y z z
theorem Equation3658_implies_Equation3469 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3469 G := λ x y z => h x x x y z z
theorem Equation3861_implies_Equation3672 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3672 G := λ x y z => h x x x y z z
theorem Equation4064_implies_Equation3875 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3875 G := λ x y z => h x x x y z z
theorem Equation4267_implies_Equation4078 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4078 G := λ x y z => h x x x y z z
theorem Equation4379_implies_Equation4280 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4280 G := λ x y z => h x x x y z z
theorem Equation4582_implies_Equation4393 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4393 G := λ x y z => h x x x y z z
theorem Equation4694_implies_Equation4595 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4595 G := λ x y z => h x x x y z z