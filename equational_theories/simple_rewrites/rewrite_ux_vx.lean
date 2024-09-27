import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation588 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (x ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation791 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ x) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation994 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (x ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1197 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ x)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1400 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ x) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1603 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (x ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1806 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ x) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation2009 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (x ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2212 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (x ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2415 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ x))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2618 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ x)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2821 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ x)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3024 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ x) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3227 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ x) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3430 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (x ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3633 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ x) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3836 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (x ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4039 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ x)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4242 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ x) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4557 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ x) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation588 (G : Type*) [Magma G] (h : Equation613 G) : Equation588 G := λ x y z w => h x y z w x x
theorem Equation816_implies_Equation791 (G : Type*) [Magma G] (h : Equation816 G) : Equation791 G := λ x y z w => h x y z w x x
theorem Equation1019_implies_Equation994 (G : Type*) [Magma G] (h : Equation1019 G) : Equation994 G := λ x y z w => h x y z w x x
theorem Equation1222_implies_Equation1197 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1197 G := λ x y z w => h x y z w x x
theorem Equation1425_implies_Equation1400 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1400 G := λ x y z w => h x y z w x x
theorem Equation1628_implies_Equation1603 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1603 G := λ x y z w => h x y z w x x
theorem Equation1831_implies_Equation1806 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1806 G := λ x y z w => h x y z w x x
theorem Equation2034_implies_Equation2009 (G : Type*) [Magma G] (h : Equation2034 G) : Equation2009 G := λ x y z w => h x y z w x x
theorem Equation2237_implies_Equation2212 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2212 G := λ x y z w => h x y z w x x
theorem Equation2440_implies_Equation2415 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2415 G := λ x y z w => h x y z w x x
theorem Equation2643_implies_Equation2618 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2618 G := λ x y z w => h x y z w x x
theorem Equation2846_implies_Equation2821 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2821 G := λ x y z w => h x y z w x x
theorem Equation3049_implies_Equation3024 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3024 G := λ x y z w => h x y z w x x
theorem Equation3252_implies_Equation3227 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3227 G := λ x y z w => h x y z w x x
theorem Equation3455_implies_Equation3430 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3430 G := λ x y z w => h x y z w x x
theorem Equation3658_implies_Equation3633 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3633 G := λ x y z w => h x y z w x x
theorem Equation3861_implies_Equation3836 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3836 G := λ x y z w => h x y z w x x
theorem Equation4064_implies_Equation4039 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4039 G := λ x y z w => h x y z w x x
theorem Equation4267_implies_Equation4242 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4242 G := λ x y z w => h x y z w x x
theorem Equation4582_implies_Equation4557 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4557 G := λ x y z w => h x y z w x x