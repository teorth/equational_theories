import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation453 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (y ∘ w)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation656 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ y) ∘ w))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation859 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (y ∘ w))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1062 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ y)) ∘ w)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1265 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ y) ∘ w)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1468 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (y ∘ w))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1671 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ y) ∘ w)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1874 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (y ∘ w)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2077 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (y ∘ w)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2280 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ y))) ∘ w
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2483 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ y)) ∘ w
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2686 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ y)) ∘ w
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2889 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ y) ∘ w
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3092 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ y) ∘ w
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3295 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (y ∘ w))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3498 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ y) ∘ w)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3701 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (y ∘ w)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3904 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ y)) ∘ w
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4107 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ y) ∘ w
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4306 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (y ∘ w)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4422 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ y) ∘ w
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4621 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ y) ∘ w
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation453 (G : Type*) [Magma G] (h : Equation613 G) : Equation453 G := λ x y z w => h x x y z y w
theorem Equation816_implies_Equation656 (G : Type*) [Magma G] (h : Equation816 G) : Equation656 G := λ x y z w => h x x y z y w
theorem Equation1019_implies_Equation859 (G : Type*) [Magma G] (h : Equation1019 G) : Equation859 G := λ x y z w => h x x y z y w
theorem Equation1222_implies_Equation1062 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1062 G := λ x y z w => h x x y z y w
theorem Equation1425_implies_Equation1265 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1265 G := λ x y z w => h x x y z y w
theorem Equation1628_implies_Equation1468 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1468 G := λ x y z w => h x x y z y w
theorem Equation1831_implies_Equation1671 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1671 G := λ x y z w => h x x y z y w
theorem Equation2034_implies_Equation1874 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1874 G := λ x y z w => h x x y z y w
theorem Equation2237_implies_Equation2077 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2077 G := λ x y z w => h x x y z y w
theorem Equation2440_implies_Equation2280 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2280 G := λ x y z w => h x x y z y w
theorem Equation2643_implies_Equation2483 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2483 G := λ x y z w => h x x y z y w
theorem Equation2846_implies_Equation2686 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2686 G := λ x y z w => h x x y z y w
theorem Equation3049_implies_Equation2889 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2889 G := λ x y z w => h x x y z y w
theorem Equation3252_implies_Equation3092 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3092 G := λ x y z w => h x x y z y w
theorem Equation3455_implies_Equation3295 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3295 G := λ x y z w => h x x y z y w
theorem Equation3658_implies_Equation3498 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3498 G := λ x y z w => h x x y z y w
theorem Equation3861_implies_Equation3701 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3701 G := λ x y z w => h x x y z y w
theorem Equation4064_implies_Equation3904 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3904 G := λ x y z w => h x x y z y w
theorem Equation4267_implies_Equation4107 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4107 G := λ x y z w => h x x y z y w
theorem Equation4379_implies_Equation4306 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4306 G := λ x y z w => h x x y z y w
theorem Equation4582_implies_Equation4422 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4422 G := λ x y z w => h x x y z y w
theorem Equation4694_implies_Equation4621 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4621 G := λ x y z w => h x x y z y w