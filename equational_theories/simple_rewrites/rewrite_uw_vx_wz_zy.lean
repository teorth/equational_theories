import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation532 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (w ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation735 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ w) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation938 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (w ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1141 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ w)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1344 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ w) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1547 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (w ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1750 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ w) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1953 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (w ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2156 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (w ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2359 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ w))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2562 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ w)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2765 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ w)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2968 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ w) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3171 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ w) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3374 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (w ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3577 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ w) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3780 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (w ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3983 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ w)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4186 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ w) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4353 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = z ∘ (w ∘ x)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4501 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ w) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4668 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ y = (z ∘ w) ∘ x
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation532 (G : Type*) [Magma G] (h : Equation613 G) : Equation532 G := λ x y z w => h x y y z w x
theorem Equation816_implies_Equation735 (G : Type*) [Magma G] (h : Equation816 G) : Equation735 G := λ x y z w => h x y y z w x
theorem Equation1019_implies_Equation938 (G : Type*) [Magma G] (h : Equation1019 G) : Equation938 G := λ x y z w => h x y y z w x
theorem Equation1222_implies_Equation1141 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1141 G := λ x y z w => h x y y z w x
theorem Equation1425_implies_Equation1344 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1344 G := λ x y z w => h x y y z w x
theorem Equation1628_implies_Equation1547 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1547 G := λ x y z w => h x y y z w x
theorem Equation1831_implies_Equation1750 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1750 G := λ x y z w => h x y y z w x
theorem Equation2034_implies_Equation1953 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1953 G := λ x y z w => h x y y z w x
theorem Equation2237_implies_Equation2156 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2156 G := λ x y z w => h x y y z w x
theorem Equation2440_implies_Equation2359 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2359 G := λ x y z w => h x y y z w x
theorem Equation2643_implies_Equation2562 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2562 G := λ x y z w => h x y y z w x
theorem Equation2846_implies_Equation2765 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2765 G := λ x y z w => h x y y z w x
theorem Equation3049_implies_Equation2968 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2968 G := λ x y z w => h x y y z w x
theorem Equation3252_implies_Equation3171 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3171 G := λ x y z w => h x y y z w x
theorem Equation3455_implies_Equation3374 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3374 G := λ x y z w => h x y y z w x
theorem Equation3658_implies_Equation3577 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3577 G := λ x y z w => h x y y z w x
theorem Equation3861_implies_Equation3780 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3780 G := λ x y z w => h x y y z w x
theorem Equation4064_implies_Equation3983 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3983 G := λ x y z w => h x y y z w x
theorem Equation4267_implies_Equation4186 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4186 G := λ x y z w => h x y y z w x
theorem Equation4379_implies_Equation4353 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4353 G := λ x y z w => h x y y z w x
theorem Equation4582_implies_Equation4501 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4501 G := λ x y z w => h x y y z w x
theorem Equation4694_implies_Equation4668 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4668 G := λ x y z w => h x y y z w x