import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation612 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (u ∘ u)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation815 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ u) ∘ u))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation1018 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (u ∘ u))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1221 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ u)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1424 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ u) ∘ u)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1627 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (u ∘ u))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1830 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ u)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation2033 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ u)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2236 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ u)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2439 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ u
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2642 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ u
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2845 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ u
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3048 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ u
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3251 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ u
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3454 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (u ∘ u))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3657 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ u) ∘ u)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3860 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (u ∘ u)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4063 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ u)) ∘ u
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4266 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ u) ∘ u
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4581 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ u) ∘ u
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation612 (G : Type*) [Magma G] (h : Equation613 G) : Equation612 G := λ x y z w u => h x y z w u u
theorem Equation816_implies_Equation815 (G : Type*) [Magma G] (h : Equation816 G) : Equation815 G := λ x y z w u => h x y z w u u
theorem Equation1019_implies_Equation1018 (G : Type*) [Magma G] (h : Equation1019 G) : Equation1018 G := λ x y z w u => h x y z w u u
theorem Equation1222_implies_Equation1221 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1221 G := λ x y z w u => h x y z w u u
theorem Equation1425_implies_Equation1424 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1424 G := λ x y z w u => h x y z w u u
theorem Equation1628_implies_Equation1627 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1627 G := λ x y z w u => h x y z w u u
theorem Equation1831_implies_Equation1830 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1830 G := λ x y z w u => h x y z w u u
theorem Equation2034_implies_Equation2033 (G : Type*) [Magma G] (h : Equation2034 G) : Equation2033 G := λ x y z w u => h x y z w u u
theorem Equation2237_implies_Equation2236 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2236 G := λ x y z w u => h x y z w u u
theorem Equation2440_implies_Equation2439 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2439 G := λ x y z w u => h x y z w u u
theorem Equation2643_implies_Equation2642 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2642 G := λ x y z w u => h x y z w u u
theorem Equation2846_implies_Equation2845 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2845 G := λ x y z w u => h x y z w u u
theorem Equation3049_implies_Equation3048 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3048 G := λ x y z w u => h x y z w u u
theorem Equation3252_implies_Equation3251 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3251 G := λ x y z w u => h x y z w u u
theorem Equation3455_implies_Equation3454 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3454 G := λ x y z w u => h x y z w u u
theorem Equation3658_implies_Equation3657 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3657 G := λ x y z w u => h x y z w u u
theorem Equation3861_implies_Equation3860 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3860 G := λ x y z w u => h x y z w u u
theorem Equation4064_implies_Equation4063 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4063 G := λ x y z w u => h x y z w u u
theorem Equation4267_implies_Equation4266 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4266 G := λ x y z w u => h x y z w u u
theorem Equation4582_implies_Equation4581 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4581 G := λ x y z w u => h x y z w u u