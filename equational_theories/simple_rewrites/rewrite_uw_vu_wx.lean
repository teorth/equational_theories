import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation553 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (x ∘ (w ∘ u)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation756 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((x ∘ w) ∘ u))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation959 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ x) ∘ (w ∘ u))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1162 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ u)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1365 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ x) ∘ w) ∘ u)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1568 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (x ∘ (w ∘ u))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1771 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ u)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1974 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ u)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2177 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ u)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2380 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ u
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2583 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ u
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2786 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ u
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2989 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ u
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3192 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ u
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3395 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (x ∘ (w ∘ u))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3598 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((x ∘ w) ∘ u)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3801 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ x) ∘ (w ∘ u)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4004 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (x ∘ w)) ∘ u
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4207 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ x) ∘ w) ∘ u
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4361 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = x ∘ (w ∘ u)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4522 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (x ∘ w) ∘ u
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4676 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (x ∘ w) ∘ u
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation553 (G : Type*) [Magma G] (h : Equation613 G) : Equation553 G := λ x y z w u => h x y z x w u
theorem Equation816_implies_Equation756 (G : Type*) [Magma G] (h : Equation816 G) : Equation756 G := λ x y z w u => h x y z x w u
theorem Equation1019_implies_Equation959 (G : Type*) [Magma G] (h : Equation1019 G) : Equation959 G := λ x y z w u => h x y z x w u
theorem Equation1222_implies_Equation1162 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1162 G := λ x y z w u => h x y z x w u
theorem Equation1425_implies_Equation1365 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1365 G := λ x y z w u => h x y z x w u
theorem Equation1628_implies_Equation1568 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1568 G := λ x y z w u => h x y z x w u
theorem Equation1831_implies_Equation1771 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1771 G := λ x y z w u => h x y z x w u
theorem Equation2034_implies_Equation1974 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1974 G := λ x y z w u => h x y z x w u
theorem Equation2237_implies_Equation2177 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2177 G := λ x y z w u => h x y z x w u
theorem Equation2440_implies_Equation2380 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2380 G := λ x y z w u => h x y z x w u
theorem Equation2643_implies_Equation2583 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2583 G := λ x y z w u => h x y z x w u
theorem Equation2846_implies_Equation2786 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2786 G := λ x y z w u => h x y z x w u
theorem Equation3049_implies_Equation2989 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2989 G := λ x y z w u => h x y z x w u
theorem Equation3252_implies_Equation3192 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3192 G := λ x y z w u => h x y z x w u
theorem Equation3455_implies_Equation3395 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3395 G := λ x y z w u => h x y z x w u
theorem Equation3658_implies_Equation3598 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3598 G := λ x y z w u => h x y z x w u
theorem Equation3861_implies_Equation3801 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3801 G := λ x y z w u => h x y z x w u
theorem Equation4064_implies_Equation4004 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4004 G := λ x y z w u => h x y z x w u
theorem Equation4267_implies_Equation4207 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4207 G := λ x y z w u => h x y z x w u
theorem Equation4379_implies_Equation4361 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4361 G := λ x y z w u => h x y z x w u
theorem Equation4582_implies_Equation4522 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4522 G := λ x y z w u => h x y z x w u
theorem Equation4694_implies_Equation4676 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4676 G := λ x y z w u => h x y z x w u