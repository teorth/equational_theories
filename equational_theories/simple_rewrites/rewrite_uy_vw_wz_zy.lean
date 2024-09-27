import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation527 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (y ∘ w)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation730 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ y) ∘ w))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation933 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (y ∘ w))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1136 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ y)) ∘ w)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1339 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ y) ∘ w)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1542 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (y ∘ w))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1745 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ y) ∘ w)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1948 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (y ∘ w)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2151 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (y ∘ w)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2354 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ y))) ∘ w
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2557 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ y)) ∘ w
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2760 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ y)) ∘ w
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2963 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ y) ∘ w
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3166 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ y) ∘ w
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3369 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (y ∘ w))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3572 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ y) ∘ w)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3775 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (y ∘ w)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3978 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ y)) ∘ w
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4181 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ y) ∘ w
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4352 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = z ∘ (y ∘ w)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4496 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ y) ∘ w
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4667 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ y = (z ∘ y) ∘ w
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation527 (G : Type*) [Magma G] (h : Equation613 G) : Equation527 G := λ x y z w => h x y y z y w
theorem Equation816_implies_Equation730 (G : Type*) [Magma G] (h : Equation816 G) : Equation730 G := λ x y z w => h x y y z y w
theorem Equation1019_implies_Equation933 (G : Type*) [Magma G] (h : Equation1019 G) : Equation933 G := λ x y z w => h x y y z y w
theorem Equation1222_implies_Equation1136 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1136 G := λ x y z w => h x y y z y w
theorem Equation1425_implies_Equation1339 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1339 G := λ x y z w => h x y y z y w
theorem Equation1628_implies_Equation1542 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1542 G := λ x y z w => h x y y z y w
theorem Equation1831_implies_Equation1745 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1745 G := λ x y z w => h x y y z y w
theorem Equation2034_implies_Equation1948 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1948 G := λ x y z w => h x y y z y w
theorem Equation2237_implies_Equation2151 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2151 G := λ x y z w => h x y y z y w
theorem Equation2440_implies_Equation2354 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2354 G := λ x y z w => h x y y z y w
theorem Equation2643_implies_Equation2557 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2557 G := λ x y z w => h x y y z y w
theorem Equation2846_implies_Equation2760 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2760 G := λ x y z w => h x y y z y w
theorem Equation3049_implies_Equation2963 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2963 G := λ x y z w => h x y y z y w
theorem Equation3252_implies_Equation3166 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3166 G := λ x y z w => h x y y z y w
theorem Equation3455_implies_Equation3369 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3369 G := λ x y z w => h x y y z y w
theorem Equation3658_implies_Equation3572 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3572 G := λ x y z w => h x y y z y w
theorem Equation3861_implies_Equation3775 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3775 G := λ x y z w => h x y y z y w
theorem Equation4064_implies_Equation3978 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3978 G := λ x y z w => h x y y z y w
theorem Equation4267_implies_Equation4181 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4181 G := λ x y z w => h x y y z y w
theorem Equation4379_implies_Equation4352 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4352 G := λ x y z w => h x y y z y w
theorem Equation4582_implies_Equation4496 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4496 G := λ x y z w => h x y y z y w
theorem Equation4694_implies_Equation4667 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4667 G := λ x y z w => h x y y z y w