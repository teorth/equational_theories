import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation422 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ (y ∘ (z ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation625 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ ((y ∘ z) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation828 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ y) ∘ (z ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1031 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ (y ∘ z)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1234 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((x ∘ y) ∘ z) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1437 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ (y ∘ (z ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1640 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ ((y ∘ z) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1843 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ y)) ∘ (z ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2046 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ y) ∘ (z ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2249 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ (y ∘ z))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2452 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((x ∘ y) ∘ z)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2655 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ (y ∘ z)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2858 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (x ∘ y)) ∘ z) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3061 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ x) ∘ y) ∘ z) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3264 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ (y ∘ (z ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3467 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ ((y ∘ z) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3670 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ y) ∘ (z ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3873 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ (y ∘ z)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4076 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((x ∘ y) ∘ z) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4278 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ x) = y ∘ (z ∘ x)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4391 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ x) = (y ∘ z) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4593 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ x = (y ∘ z) ∘ x
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation422 (G : Type*) [Magma G] (h : Equation613 G) : Equation422 G := λ x y z => h x x x y z x
theorem Equation816_implies_Equation625 (G : Type*) [Magma G] (h : Equation816 G) : Equation625 G := λ x y z => h x x x y z x
theorem Equation1019_implies_Equation828 (G : Type*) [Magma G] (h : Equation1019 G) : Equation828 G := λ x y z => h x x x y z x
theorem Equation1222_implies_Equation1031 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1031 G := λ x y z => h x x x y z x
theorem Equation1425_implies_Equation1234 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1234 G := λ x y z => h x x x y z x
theorem Equation1628_implies_Equation1437 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1437 G := λ x y z => h x x x y z x
theorem Equation1831_implies_Equation1640 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1640 G := λ x y z => h x x x y z x
theorem Equation2034_implies_Equation1843 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1843 G := λ x y z => h x x x y z x
theorem Equation2237_implies_Equation2046 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2046 G := λ x y z => h x x x y z x
theorem Equation2440_implies_Equation2249 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2249 G := λ x y z => h x x x y z x
theorem Equation2643_implies_Equation2452 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2452 G := λ x y z => h x x x y z x
theorem Equation2846_implies_Equation2655 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2655 G := λ x y z => h x x x y z x
theorem Equation3049_implies_Equation2858 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2858 G := λ x y z => h x x x y z x
theorem Equation3252_implies_Equation3061 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3061 G := λ x y z => h x x x y z x
theorem Equation3455_implies_Equation3264 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3264 G := λ x y z => h x x x y z x
theorem Equation3658_implies_Equation3467 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3467 G := λ x y z => h x x x y z x
theorem Equation3861_implies_Equation3670 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3670 G := λ x y z => h x x x y z x
theorem Equation4064_implies_Equation3873 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3873 G := λ x y z => h x x x y z x
theorem Equation4267_implies_Equation4076 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4076 G := λ x y z => h x x x y z x
theorem Equation4379_implies_Equation4278 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4278 G := λ x y z => h x x x y z x
theorem Equation4582_implies_Equation4391 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4391 G := λ x y z => h x x x y z x
theorem Equation4694_implies_Equation4593 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4593 G := λ x y z => h x x x y z x