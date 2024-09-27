import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation597 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (y ∘ u)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation800 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ y) ∘ u))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation1003 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (y ∘ u))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1206 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ y)) ∘ u)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1409 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ y) ∘ u)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1612 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (y ∘ u))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1815 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ y) ∘ u)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation2018 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (y ∘ u)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2221 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (y ∘ u)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2424 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ y))) ∘ u
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2627 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ y)) ∘ u
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2830 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ y)) ∘ u
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3033 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ y) ∘ u
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3236 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ y) ∘ u
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3439 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (y ∘ u))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3642 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ y) ∘ u)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3845 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (y ∘ u)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4048 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ y)) ∘ u
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4251 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ y) ∘ u
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4375 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = w ∘ (y ∘ u)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4566 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ y) ∘ u
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4690 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (w ∘ y) ∘ u
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation597 (G : Type*) [Magma G] (h : Equation613 G) : Equation597 G := λ x y z w u => h x y z w y u
theorem Equation816_implies_Equation800 (G : Type*) [Magma G] (h : Equation816 G) : Equation800 G := λ x y z w u => h x y z w y u
theorem Equation1019_implies_Equation1003 (G : Type*) [Magma G] (h : Equation1019 G) : Equation1003 G := λ x y z w u => h x y z w y u
theorem Equation1222_implies_Equation1206 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1206 G := λ x y z w u => h x y z w y u
theorem Equation1425_implies_Equation1409 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1409 G := λ x y z w u => h x y z w y u
theorem Equation1628_implies_Equation1612 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1612 G := λ x y z w u => h x y z w y u
theorem Equation1831_implies_Equation1815 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1815 G := λ x y z w u => h x y z w y u
theorem Equation2034_implies_Equation2018 (G : Type*) [Magma G] (h : Equation2034 G) : Equation2018 G := λ x y z w u => h x y z w y u
theorem Equation2237_implies_Equation2221 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2221 G := λ x y z w u => h x y z w y u
theorem Equation2440_implies_Equation2424 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2424 G := λ x y z w u => h x y z w y u
theorem Equation2643_implies_Equation2627 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2627 G := λ x y z w u => h x y z w y u
theorem Equation2846_implies_Equation2830 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2830 G := λ x y z w u => h x y z w y u
theorem Equation3049_implies_Equation3033 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3033 G := λ x y z w u => h x y z w y u
theorem Equation3252_implies_Equation3236 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3236 G := λ x y z w u => h x y z w y u
theorem Equation3455_implies_Equation3439 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3439 G := λ x y z w u => h x y z w y u
theorem Equation3658_implies_Equation3642 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3642 G := λ x y z w u => h x y z w y u
theorem Equation3861_implies_Equation3845 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3845 G := λ x y z w u => h x y z w y u
theorem Equation4064_implies_Equation4048 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4048 G := λ x y z w u => h x y z w y u
theorem Equation4267_implies_Equation4251 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4251 G := λ x y z w u => h x y z w y u
theorem Equation4379_implies_Equation4375 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4375 G := λ x y z w u => h x y z w y u
theorem Equation4582_implies_Equation4566 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4566 G := λ x y z w u => h x y z w y u
theorem Equation4694_implies_Equation4690 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4690 G := λ x y z w u => h x y z w y u