import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation423 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ (y ∘ (z ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation626 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ ((y ∘ z) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation829 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ y) ∘ (z ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1032 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ (y ∘ z)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1235 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((x ∘ y) ∘ z) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1438 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ (y ∘ (z ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1641 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ ((y ∘ z) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1844 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ y)) ∘ (z ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2047 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ y) ∘ (z ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2250 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ (y ∘ z))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2453 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((x ∘ y) ∘ z)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2656 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ (y ∘ z)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2859 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (x ∘ y)) ∘ z) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3062 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ x) ∘ y) ∘ z) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3265 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ (y ∘ (z ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3468 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ ((y ∘ z) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3671 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ y) ∘ (z ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3874 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ (y ∘ z)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4077 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((x ∘ y) ∘ z) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4279 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ x) = y ∘ (z ∘ y)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4392 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ x) = (y ∘ z) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4594 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ x = (y ∘ z) ∘ y
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation423 (G : Type*) [Magma G] (h : Equation613 G) : Equation423 G := λ x y z => h x x x y z y
theorem Equation816_implies_Equation626 (G : Type*) [Magma G] (h : Equation816 G) : Equation626 G := λ x y z => h x x x y z y
theorem Equation1019_implies_Equation829 (G : Type*) [Magma G] (h : Equation1019 G) : Equation829 G := λ x y z => h x x x y z y
theorem Equation1222_implies_Equation1032 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1032 G := λ x y z => h x x x y z y
theorem Equation1425_implies_Equation1235 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1235 G := λ x y z => h x x x y z y
theorem Equation1628_implies_Equation1438 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1438 G := λ x y z => h x x x y z y
theorem Equation1831_implies_Equation1641 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1641 G := λ x y z => h x x x y z y
theorem Equation2034_implies_Equation1844 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1844 G := λ x y z => h x x x y z y
theorem Equation2237_implies_Equation2047 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2047 G := λ x y z => h x x x y z y
theorem Equation2440_implies_Equation2250 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2250 G := λ x y z => h x x x y z y
theorem Equation2643_implies_Equation2453 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2453 G := λ x y z => h x x x y z y
theorem Equation2846_implies_Equation2656 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2656 G := λ x y z => h x x x y z y
theorem Equation3049_implies_Equation2859 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2859 G := λ x y z => h x x x y z y
theorem Equation3252_implies_Equation3062 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3062 G := λ x y z => h x x x y z y
theorem Equation3455_implies_Equation3265 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3265 G := λ x y z => h x x x y z y
theorem Equation3658_implies_Equation3468 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3468 G := λ x y z => h x x x y z y
theorem Equation3861_implies_Equation3671 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3671 G := λ x y z => h x x x y z y
theorem Equation4064_implies_Equation3874 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3874 G := λ x y z => h x x x y z y
theorem Equation4267_implies_Equation4077 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4077 G := λ x y z => h x x x y z y
theorem Equation4379_implies_Equation4279 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4279 G := λ x y z => h x x x y z y
theorem Equation4582_implies_Equation4392 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4392 G := λ x y z => h x x x y z y
theorem Equation4694_implies_Equation4594 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4594 G := λ x y z => h x x x y z y