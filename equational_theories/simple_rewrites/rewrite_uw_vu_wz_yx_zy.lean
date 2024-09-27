import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation462 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (y ∘ (z ∘ (w ∘ u)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation665 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (y ∘ ((z ∘ w) ∘ u))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation868 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ ((y ∘ z) ∘ (w ∘ u))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1071 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ u)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1274 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (((y ∘ z) ∘ w) ∘ u)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1477 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ y) ∘ (z ∘ (w ∘ u))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1680 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ u)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1883 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ u)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2086 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ u)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2289 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ u
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2492 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ u
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2695 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ u
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2898 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ u
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3101 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ u
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3304 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = y ∘ (z ∘ (w ∘ u))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3507 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = y ∘ ((z ∘ w) ∘ u)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3710 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = (y ∘ z) ∘ (w ∘ u)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3913 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = (y ∘ (z ∘ w)) ∘ u
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4116 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = ((y ∘ z) ∘ w) ∘ u
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4313 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (x ∘ y) = z ∘ (w ∘ u)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4431 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (x ∘ y) = (z ∘ w) ∘ u
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4628 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ x) ∘ y = (z ∘ w) ∘ u
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation462 (G : Type*) [Magma G] (h : Equation613 G) : Equation462 G := λ x y z w u => h x x y z w u
theorem Equation816_implies_Equation665 (G : Type*) [Magma G] (h : Equation816 G) : Equation665 G := λ x y z w u => h x x y z w u
theorem Equation1019_implies_Equation868 (G : Type*) [Magma G] (h : Equation1019 G) : Equation868 G := λ x y z w u => h x x y z w u
theorem Equation1222_implies_Equation1071 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1071 G := λ x y z w u => h x x y z w u
theorem Equation1425_implies_Equation1274 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1274 G := λ x y z w u => h x x y z w u
theorem Equation1628_implies_Equation1477 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1477 G := λ x y z w u => h x x y z w u
theorem Equation1831_implies_Equation1680 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1680 G := λ x y z w u => h x x y z w u
theorem Equation2034_implies_Equation1883 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1883 G := λ x y z w u => h x x y z w u
theorem Equation2237_implies_Equation2086 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2086 G := λ x y z w u => h x x y z w u
theorem Equation2440_implies_Equation2289 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2289 G := λ x y z w u => h x x y z w u
theorem Equation2643_implies_Equation2492 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2492 G := λ x y z w u => h x x y z w u
theorem Equation2846_implies_Equation2695 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2695 G := λ x y z w u => h x x y z w u
theorem Equation3049_implies_Equation2898 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2898 G := λ x y z w u => h x x y z w u
theorem Equation3252_implies_Equation3101 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3101 G := λ x y z w u => h x x y z w u
theorem Equation3455_implies_Equation3304 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3304 G := λ x y z w u => h x x y z w u
theorem Equation3658_implies_Equation3507 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3507 G := λ x y z w u => h x x y z w u
theorem Equation3861_implies_Equation3710 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3710 G := λ x y z w u => h x x y z w u
theorem Equation4064_implies_Equation3913 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3913 G := λ x y z w u => h x x y z w u
theorem Equation4267_implies_Equation4116 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4116 G := λ x y z w u => h x x y z w u
theorem Equation4379_implies_Equation4313 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4313 G := λ x y z w u => h x x y z w u
theorem Equation4582_implies_Equation4431 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4431 G := λ x y z w u => h x x y z w u
theorem Equation4694_implies_Equation4628 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4628 G := λ x y z w u => h x x y z w u