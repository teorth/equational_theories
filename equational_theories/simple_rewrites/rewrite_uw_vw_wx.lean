import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation552 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (w ∘ w)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation755 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ w) ∘ w))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation958 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (w ∘ w))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1161 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ w)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1364 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ w) ∘ w)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1567 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (w ∘ w))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1770 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ w)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1973 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ w)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2176 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ w)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2379 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ w
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2582 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ w
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2785 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ w
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2988 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ w
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3191 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ w
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3394 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (w ∘ w))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3597 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ w) ∘ w)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3800 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (w ∘ w)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4003 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ w)) ∘ w
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4206 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ w) ∘ w
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4521 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ w) ∘ w
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation552 (G : Type*) [Magma G] (h : Equation613 G) : Equation552 G := λ x y z w => h x y z x w w
theorem Equation816_implies_Equation755 (G : Type*) [Magma G] (h : Equation816 G) : Equation755 G := λ x y z w => h x y z x w w
theorem Equation1019_implies_Equation958 (G : Type*) [Magma G] (h : Equation1019 G) : Equation958 G := λ x y z w => h x y z x w w
theorem Equation1222_implies_Equation1161 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1161 G := λ x y z w => h x y z x w w
theorem Equation1425_implies_Equation1364 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1364 G := λ x y z w => h x y z x w w
theorem Equation1628_implies_Equation1567 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1567 G := λ x y z w => h x y z x w w
theorem Equation1831_implies_Equation1770 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1770 G := λ x y z w => h x y z x w w
theorem Equation2034_implies_Equation1973 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1973 G := λ x y z w => h x y z x w w
theorem Equation2237_implies_Equation2176 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2176 G := λ x y z w => h x y z x w w
theorem Equation2440_implies_Equation2379 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2379 G := λ x y z w => h x y z x w w
theorem Equation2643_implies_Equation2582 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2582 G := λ x y z w => h x y z x w w
theorem Equation2846_implies_Equation2785 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2785 G := λ x y z w => h x y z x w w
theorem Equation3049_implies_Equation2988 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2988 G := λ x y z w => h x y z x w w
theorem Equation3252_implies_Equation3191 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3191 G := λ x y z w => h x y z x w w
theorem Equation3455_implies_Equation3394 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3394 G := λ x y z w => h x y z x w w
theorem Equation3658_implies_Equation3597 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3597 G := λ x y z w => h x y z x w w
theorem Equation3861_implies_Equation3800 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3800 G := λ x y z w => h x y z x w w
theorem Equation4064_implies_Equation4003 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4003 G := λ x y z w => h x y z x w w
theorem Equation4267_implies_Equation4206 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4206 G := λ x y z w => h x y z x w w
theorem Equation4582_implies_Equation4521 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4521 G := λ x y z w => h x y z x w w