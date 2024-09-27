import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation550 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (w ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation753 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ w) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation956 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (w ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1159 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1362 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ w) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1565 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (w ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1768 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1971 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2174 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2377 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2580 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2783 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2986 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3189 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3392 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (w ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3595 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ w) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3798 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (w ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4001 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ w)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4204 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ w) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4519 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ w) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation550 (G : Type*) [Magma G] (h : Equation613 G) : Equation550 G := λ x y z w => h x y z x w y
theorem Equation816_implies_Equation753 (G : Type*) [Magma G] (h : Equation816 G) : Equation753 G := λ x y z w => h x y z x w y
theorem Equation1019_implies_Equation956 (G : Type*) [Magma G] (h : Equation1019 G) : Equation956 G := λ x y z w => h x y z x w y
theorem Equation1222_implies_Equation1159 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1159 G := λ x y z w => h x y z x w y
theorem Equation1425_implies_Equation1362 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1362 G := λ x y z w => h x y z x w y
theorem Equation1628_implies_Equation1565 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1565 G := λ x y z w => h x y z x w y
theorem Equation1831_implies_Equation1768 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1768 G := λ x y z w => h x y z x w y
theorem Equation2034_implies_Equation1971 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1971 G := λ x y z w => h x y z x w y
theorem Equation2237_implies_Equation2174 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2174 G := λ x y z w => h x y z x w y
theorem Equation2440_implies_Equation2377 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2377 G := λ x y z w => h x y z x w y
theorem Equation2643_implies_Equation2580 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2580 G := λ x y z w => h x y z x w y
theorem Equation2846_implies_Equation2783 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2783 G := λ x y z w => h x y z x w y
theorem Equation3049_implies_Equation2986 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2986 G := λ x y z w => h x y z x w y
theorem Equation3252_implies_Equation3189 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3189 G := λ x y z w => h x y z x w y
theorem Equation3455_implies_Equation3392 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3392 G := λ x y z w => h x y z x w y
theorem Equation3658_implies_Equation3595 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3595 G := λ x y z w => h x y z x w y
theorem Equation3861_implies_Equation3798 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3798 G := λ x y z w => h x y z x w y
theorem Equation4064_implies_Equation4001 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4001 G := λ x y z w => h x y z x w y
theorem Equation4267_implies_Equation4204 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4204 G := λ x y z w => h x y z x w y
theorem Equation4582_implies_Equation4519 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4519 G := λ x y z w => h x y z x w y