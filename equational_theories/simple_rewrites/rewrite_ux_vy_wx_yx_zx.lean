import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation412 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (x ∘ (x ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation615 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ ((x ∘ x) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation818 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ x) ∘ (x ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1021 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ (x ∘ x)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1224 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((x ∘ x) ∘ x) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1427 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ (x ∘ (x ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1630 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ ((x ∘ x) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1833 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ x)) ∘ (x ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2036 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ x) ∘ (x ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2239 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ (x ∘ x))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2442 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((x ∘ x) ∘ x)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2645 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ (x ∘ x)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2848 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (x ∘ x)) ∘ x) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3051 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ x) ∘ x) ∘ x) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3254 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ (x ∘ (x ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3457 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ ((x ∘ x) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3660 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ x) ∘ (x ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3863 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ (x ∘ x)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4066 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((x ∘ x) ∘ x) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4268 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = x ∘ (x ∘ y)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4381 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = (x ∘ x) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4583 (G: Type*) [Magma G] := ∀ x y : G, (x ∘ x) ∘ x = (x ∘ x) ∘ y
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation412 (G : Type*) [Magma G] (h : Equation613 G) : Equation412 G := λ x y => h x x x x x y
theorem Equation816_implies_Equation615 (G : Type*) [Magma G] (h : Equation816 G) : Equation615 G := λ x y => h x x x x x y
theorem Equation1019_implies_Equation818 (G : Type*) [Magma G] (h : Equation1019 G) : Equation818 G := λ x y => h x x x x x y
theorem Equation1222_implies_Equation1021 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1021 G := λ x y => h x x x x x y
theorem Equation1425_implies_Equation1224 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1224 G := λ x y => h x x x x x y
theorem Equation1628_implies_Equation1427 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1427 G := λ x y => h x x x x x y
theorem Equation1831_implies_Equation1630 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1630 G := λ x y => h x x x x x y
theorem Equation2034_implies_Equation1833 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1833 G := λ x y => h x x x x x y
theorem Equation2237_implies_Equation2036 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2036 G := λ x y => h x x x x x y
theorem Equation2440_implies_Equation2239 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2239 G := λ x y => h x x x x x y
theorem Equation2643_implies_Equation2442 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2442 G := λ x y => h x x x x x y
theorem Equation2846_implies_Equation2645 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2645 G := λ x y => h x x x x x y
theorem Equation3049_implies_Equation2848 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2848 G := λ x y => h x x x x x y
theorem Equation3252_implies_Equation3051 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3051 G := λ x y => h x x x x x y
theorem Equation3455_implies_Equation3254 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3254 G := λ x y => h x x x x x y
theorem Equation3658_implies_Equation3457 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3457 G := λ x y => h x x x x x y
theorem Equation3861_implies_Equation3660 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3660 G := λ x y => h x x x x x y
theorem Equation4064_implies_Equation3863 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3863 G := λ x y => h x x x x x y
theorem Equation4267_implies_Equation4066 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4066 G := λ x y => h x x x x x y
theorem Equation4379_implies_Equation4268 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4268 G := λ x y => h x x x x x y
theorem Equation4582_implies_Equation4381 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4381 G := λ x y => h x x x x x y
theorem Equation4694_implies_Equation4583 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4583 G := λ x y => h x x x x x y