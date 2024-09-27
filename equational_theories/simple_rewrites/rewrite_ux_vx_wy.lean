import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation554 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ (x ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation757 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((y ∘ x) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation960 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ (x ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1163 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (y ∘ x)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1366 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ y) ∘ x) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1569 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ (x ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1772 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((y ∘ x) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1975 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ (x ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2178 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ (x ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2381 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (y ∘ x))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2584 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ y) ∘ x)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2787 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (y ∘ x)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2990 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ y)) ∘ x) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3193 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ y) ∘ x) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3396 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ (x ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3599 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((y ∘ x) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3802 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ (x ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4005 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (y ∘ x)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4208 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ y) ∘ x) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4523 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (y ∘ x) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation554 (G : Type*) [Magma G] (h : Equation613 G) : Equation554 G := λ x y z => h x y z y x x
theorem Equation816_implies_Equation757 (G : Type*) [Magma G] (h : Equation816 G) : Equation757 G := λ x y z => h x y z y x x
theorem Equation1019_implies_Equation960 (G : Type*) [Magma G] (h : Equation1019 G) : Equation960 G := λ x y z => h x y z y x x
theorem Equation1222_implies_Equation1163 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1163 G := λ x y z => h x y z y x x
theorem Equation1425_implies_Equation1366 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1366 G := λ x y z => h x y z y x x
theorem Equation1628_implies_Equation1569 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1569 G := λ x y z => h x y z y x x
theorem Equation1831_implies_Equation1772 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1772 G := λ x y z => h x y z y x x
theorem Equation2034_implies_Equation1975 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1975 G := λ x y z => h x y z y x x
theorem Equation2237_implies_Equation2178 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2178 G := λ x y z => h x y z y x x
theorem Equation2440_implies_Equation2381 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2381 G := λ x y z => h x y z y x x
theorem Equation2643_implies_Equation2584 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2584 G := λ x y z => h x y z y x x
theorem Equation2846_implies_Equation2787 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2787 G := λ x y z => h x y z y x x
theorem Equation3049_implies_Equation2990 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2990 G := λ x y z => h x y z y x x
theorem Equation3252_implies_Equation3193 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3193 G := λ x y z => h x y z y x x
theorem Equation3455_implies_Equation3396 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3396 G := λ x y z => h x y z y x x
theorem Equation3658_implies_Equation3599 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3599 G := λ x y z => h x y z y x x
theorem Equation3861_implies_Equation3802 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3802 G := λ x y z => h x y z y x x
theorem Equation4064_implies_Equation4005 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4005 G := λ x y z => h x y z y x x
theorem Equation4267_implies_Equation4208 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4208 G := λ x y z => h x y z y x x
theorem Equation4582_implies_Equation4523 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4523 G := λ x y z => h x y z y x x