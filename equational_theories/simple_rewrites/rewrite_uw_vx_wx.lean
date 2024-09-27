import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation549 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (w ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation752 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ w) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation955 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (w ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1158 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1361 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ w) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1564 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (w ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1767 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1970 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2173 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2376 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2579 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2782 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2985 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3188 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3391 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (w ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3594 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ w) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3797 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (w ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4000 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ w)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4203 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ w) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4518 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ w) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation549 (G : Type*) [Magma G] (h : Equation613 G) : Equation549 G := λ x y z w => h x y z x w x
theorem Equation816_implies_Equation752 (G : Type*) [Magma G] (h : Equation816 G) : Equation752 G := λ x y z w => h x y z x w x
theorem Equation1019_implies_Equation955 (G : Type*) [Magma G] (h : Equation1019 G) : Equation955 G := λ x y z w => h x y z x w x
theorem Equation1222_implies_Equation1158 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1158 G := λ x y z w => h x y z x w x
theorem Equation1425_implies_Equation1361 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1361 G := λ x y z w => h x y z x w x
theorem Equation1628_implies_Equation1564 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1564 G := λ x y z w => h x y z x w x
theorem Equation1831_implies_Equation1767 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1767 G := λ x y z w => h x y z x w x
theorem Equation2034_implies_Equation1970 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1970 G := λ x y z w => h x y z x w x
theorem Equation2237_implies_Equation2173 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2173 G := λ x y z w => h x y z x w x
theorem Equation2440_implies_Equation2376 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2376 G := λ x y z w => h x y z x w x
theorem Equation2643_implies_Equation2579 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2579 G := λ x y z w => h x y z x w x
theorem Equation2846_implies_Equation2782 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2782 G := λ x y z w => h x y z x w x
theorem Equation3049_implies_Equation2985 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2985 G := λ x y z w => h x y z x w x
theorem Equation3252_implies_Equation3188 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3188 G := λ x y z w => h x y z x w x
theorem Equation3455_implies_Equation3391 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3391 G := λ x y z w => h x y z x w x
theorem Equation3658_implies_Equation3594 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3594 G := λ x y z w => h x y z x w x
theorem Equation3861_implies_Equation3797 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3797 G := λ x y z w => h x y z x w x
theorem Equation4064_implies_Equation4000 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4000 G := λ x y z w => h x y z x w x
theorem Equation4267_implies_Equation4203 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4203 G := λ x y z w => h x y z x w x
theorem Equation4582_implies_Equation4518 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4518 G := λ x y z w => h x y z x w x