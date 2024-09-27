import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation413 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (x ∘ (y ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation616 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ ((x ∘ y) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation819 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ x) ∘ (y ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1022 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ (x ∘ y)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1225 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((x ∘ x) ∘ y) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1428 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ (x ∘ (y ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1631 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ ((x ∘ y) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1834 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ x)) ∘ (y ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2037 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ x) ∘ (y ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2240 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ (x ∘ y))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2443 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((x ∘ x) ∘ y)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2646 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ (x ∘ y)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2849 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (x ∘ x)) ∘ y) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3052 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ x) ∘ x) ∘ y) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3255 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ (x ∘ (y ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3458 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ ((x ∘ y) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3661 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ x) ∘ (y ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3864 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ (x ∘ y)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4067 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((x ∘ x) ∘ y) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4269 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = x ∘ (y ∘ x)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4382 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = (x ∘ y) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4584 (G: Type*) [Magma G] := ∀ x y : G, (x ∘ x) ∘ x = (x ∘ y) ∘ x
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation413 (G : Type*) [Magma G] (h : Equation613 G) : Equation413 G := λ x y => h x x x x y x
theorem Equation816_implies_Equation616 (G : Type*) [Magma G] (h : Equation816 G) : Equation616 G := λ x y => h x x x x y x
theorem Equation1019_implies_Equation819 (G : Type*) [Magma G] (h : Equation1019 G) : Equation819 G := λ x y => h x x x x y x
theorem Equation1222_implies_Equation1022 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1022 G := λ x y => h x x x x y x
theorem Equation1425_implies_Equation1225 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1225 G := λ x y => h x x x x y x
theorem Equation1628_implies_Equation1428 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1428 G := λ x y => h x x x x y x
theorem Equation1831_implies_Equation1631 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1631 G := λ x y => h x x x x y x
theorem Equation2034_implies_Equation1834 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1834 G := λ x y => h x x x x y x
theorem Equation2237_implies_Equation2037 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2037 G := λ x y => h x x x x y x
theorem Equation2440_implies_Equation2240 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2240 G := λ x y => h x x x x y x
theorem Equation2643_implies_Equation2443 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2443 G := λ x y => h x x x x y x
theorem Equation2846_implies_Equation2646 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2646 G := λ x y => h x x x x y x
theorem Equation3049_implies_Equation2849 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2849 G := λ x y => h x x x x y x
theorem Equation3252_implies_Equation3052 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3052 G := λ x y => h x x x x y x
theorem Equation3455_implies_Equation3255 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3255 G := λ x y => h x x x x y x
theorem Equation3658_implies_Equation3458 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3458 G := λ x y => h x x x x y x
theorem Equation3861_implies_Equation3661 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3661 G := λ x y => h x x x x y x
theorem Equation4064_implies_Equation3864 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3864 G := λ x y => h x x x x y x
theorem Equation4267_implies_Equation4067 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4067 G := λ x y => h x x x x y x
theorem Equation4379_implies_Equation4269 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4269 G := λ x y => h x x x x y x
theorem Equation4582_implies_Equation4382 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4382 G := λ x y => h x x x x y x
theorem Equation4694_implies_Equation4584 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4584 G := λ x y => h x x x x y x