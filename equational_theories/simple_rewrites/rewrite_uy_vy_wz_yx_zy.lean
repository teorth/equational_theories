import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation451 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ (y ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation654 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((z ∘ y) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation857 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ (y ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1060 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (z ∘ y)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1263 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ z) ∘ y) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1466 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ (y ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1669 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((z ∘ y) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1872 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ (y ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2075 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ (y ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2278 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (z ∘ y))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2481 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ z) ∘ y)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2684 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (z ∘ y)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2887 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ z)) ∘ y) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3090 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ z) ∘ y) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3293 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ (y ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3496 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((z ∘ y) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3699 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ (y ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3902 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (z ∘ y)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4105 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ z) ∘ y) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4304 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = z ∘ (y ∘ y)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4420 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (z ∘ y) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4619 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (z ∘ y) ∘ y
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation451 (G : Type*) [Magma G] (h : Equation613 G) : Equation451 G := λ x y z => h x x y z y y
theorem Equation816_implies_Equation654 (G : Type*) [Magma G] (h : Equation816 G) : Equation654 G := λ x y z => h x x y z y y
theorem Equation1019_implies_Equation857 (G : Type*) [Magma G] (h : Equation1019 G) : Equation857 G := λ x y z => h x x y z y y
theorem Equation1222_implies_Equation1060 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1060 G := λ x y z => h x x y z y y
theorem Equation1425_implies_Equation1263 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1263 G := λ x y z => h x x y z y y
theorem Equation1628_implies_Equation1466 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1466 G := λ x y z => h x x y z y y
theorem Equation1831_implies_Equation1669 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1669 G := λ x y z => h x x y z y y
theorem Equation2034_implies_Equation1872 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1872 G := λ x y z => h x x y z y y
theorem Equation2237_implies_Equation2075 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2075 G := λ x y z => h x x y z y y
theorem Equation2440_implies_Equation2278 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2278 G := λ x y z => h x x y z y y
theorem Equation2643_implies_Equation2481 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2481 G := λ x y z => h x x y z y y
theorem Equation2846_implies_Equation2684 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2684 G := λ x y z => h x x y z y y
theorem Equation3049_implies_Equation2887 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2887 G := λ x y z => h x x y z y y
theorem Equation3252_implies_Equation3090 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3090 G := λ x y z => h x x y z y y
theorem Equation3455_implies_Equation3293 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3293 G := λ x y z => h x x y z y y
theorem Equation3658_implies_Equation3496 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3496 G := λ x y z => h x x y z y y
theorem Equation3861_implies_Equation3699 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3699 G := λ x y z => h x x y z y y
theorem Equation4064_implies_Equation3902 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3902 G := λ x y z => h x x y z y y
theorem Equation4267_implies_Equation4105 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4105 G := λ x y z => h x x y z y y
theorem Equation4379_implies_Equation4304 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4304 G := λ x y z => h x x y z y y
theorem Equation4582_implies_Equation4420 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4420 G := λ x y z => h x x y z y y
theorem Equation4694_implies_Equation4619 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4619 G := λ x y z => h x x y z y y