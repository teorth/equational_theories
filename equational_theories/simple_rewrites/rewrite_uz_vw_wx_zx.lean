import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation472 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (x ∘ (z ∘ w)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation675 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((x ∘ z) ∘ w))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation878 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ x) ∘ (z ∘ w))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1081 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (x ∘ z)) ∘ w)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1284 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ x) ∘ z) ∘ w)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1487 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (x ∘ (z ∘ w))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1690 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((x ∘ z) ∘ w)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1893 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ x)) ∘ (z ∘ w)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2096 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ x) ∘ (z ∘ w)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2299 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (x ∘ z))) ∘ w
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2502 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ x) ∘ z)) ∘ w
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2705 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (x ∘ z)) ∘ w
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2908 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ x)) ∘ z) ∘ w
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3111 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ x) ∘ z) ∘ w
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3314 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (x ∘ (z ∘ w))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3517 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((x ∘ z) ∘ w)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3720 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ x) ∘ (z ∘ w)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3923 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (x ∘ z)) ∘ w
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4126 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ x) ∘ z) ∘ w
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4319 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = x ∘ (z ∘ w)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4441 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (x ∘ z) ∘ w
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4634 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ x = (x ∘ z) ∘ w
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation472 (G : Type*) [Magma G] (h : Equation613 G) : Equation472 G := λ x y z w => h x y x x z w
theorem Equation816_implies_Equation675 (G : Type*) [Magma G] (h : Equation816 G) : Equation675 G := λ x y z w => h x y x x z w
theorem Equation1019_implies_Equation878 (G : Type*) [Magma G] (h : Equation1019 G) : Equation878 G := λ x y z w => h x y x x z w
theorem Equation1222_implies_Equation1081 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1081 G := λ x y z w => h x y x x z w
theorem Equation1425_implies_Equation1284 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1284 G := λ x y z w => h x y x x z w
theorem Equation1628_implies_Equation1487 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1487 G := λ x y z w => h x y x x z w
theorem Equation1831_implies_Equation1690 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1690 G := λ x y z w => h x y x x z w
theorem Equation2034_implies_Equation1893 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1893 G := λ x y z w => h x y x x z w
theorem Equation2237_implies_Equation2096 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2096 G := λ x y z w => h x y x x z w
theorem Equation2440_implies_Equation2299 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2299 G := λ x y z w => h x y x x z w
theorem Equation2643_implies_Equation2502 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2502 G := λ x y z w => h x y x x z w
theorem Equation2846_implies_Equation2705 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2705 G := λ x y z w => h x y x x z w
theorem Equation3049_implies_Equation2908 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2908 G := λ x y z w => h x y x x z w
theorem Equation3252_implies_Equation3111 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3111 G := λ x y z w => h x y x x z w
theorem Equation3455_implies_Equation3314 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3314 G := λ x y z w => h x y x x z w
theorem Equation3658_implies_Equation3517 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3517 G := λ x y z w => h x y x x z w
theorem Equation3861_implies_Equation3720 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3720 G := λ x y z w => h x y x x z w
theorem Equation4064_implies_Equation3923 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3923 G := λ x y z w => h x y x x z w
theorem Equation4267_implies_Equation4126 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4126 G := λ x y z w => h x y x x z w
theorem Equation4379_implies_Equation4319 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4319 G := λ x y z w => h x y x x z w
theorem Equation4582_implies_Equation4441 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4441 G := λ x y z w => h x y x x z w
theorem Equation4694_implies_Equation4634 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4634 G := λ x y z w => h x y x x z w