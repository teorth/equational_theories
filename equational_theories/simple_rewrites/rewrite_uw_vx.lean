import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation603 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (w ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation806 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ w) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation1009 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (w ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1212 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ w)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1415 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ w) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1618 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (w ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1821 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ w) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation2024 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (w ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2227 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (w ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2430 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ w))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2633 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ w)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2836 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ w)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3039 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ w) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3242 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ w) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3445 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (w ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3648 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ w) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3851 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (w ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4054 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ w)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4257 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ w) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4572 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ w) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation603 (G : Type*) [Magma G] (h : Equation613 G) : Equation603 G := λ x y z w => h x y z w w x
theorem Equation816_implies_Equation806 (G : Type*) [Magma G] (h : Equation816 G) : Equation806 G := λ x y z w => h x y z w w x
theorem Equation1019_implies_Equation1009 (G : Type*) [Magma G] (h : Equation1019 G) : Equation1009 G := λ x y z w => h x y z w w x
theorem Equation1222_implies_Equation1212 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1212 G := λ x y z w => h x y z w w x
theorem Equation1425_implies_Equation1415 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1415 G := λ x y z w => h x y z w w x
theorem Equation1628_implies_Equation1618 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1618 G := λ x y z w => h x y z w w x
theorem Equation1831_implies_Equation1821 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1821 G := λ x y z w => h x y z w w x
theorem Equation2034_implies_Equation2024 (G : Type*) [Magma G] (h : Equation2034 G) : Equation2024 G := λ x y z w => h x y z w w x
theorem Equation2237_implies_Equation2227 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2227 G := λ x y z w => h x y z w w x
theorem Equation2440_implies_Equation2430 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2430 G := λ x y z w => h x y z w w x
theorem Equation2643_implies_Equation2633 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2633 G := λ x y z w => h x y z w w x
theorem Equation2846_implies_Equation2836 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2836 G := λ x y z w => h x y z w w x
theorem Equation3049_implies_Equation3039 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3039 G := λ x y z w => h x y z w w x
theorem Equation3252_implies_Equation3242 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3242 G := λ x y z w => h x y z w w x
theorem Equation3455_implies_Equation3445 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3445 G := λ x y z w => h x y z w w x
theorem Equation3658_implies_Equation3648 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3648 G := λ x y z w => h x y z w w x
theorem Equation3861_implies_Equation3851 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3851 G := λ x y z w => h x y z w w x
theorem Equation4064_implies_Equation4054 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4054 G := λ x y z w => h x y z w w x
theorem Equation4267_implies_Equation4257 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4257 G := λ x y z w => h x y z w w x
theorem Equation4582_implies_Equation4572 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4572 G := λ x y z w => h x y z w w x