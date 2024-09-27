import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation468 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (x ∘ (y ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation671 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((x ∘ y) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation874 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ x) ∘ (y ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1077 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (x ∘ y)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1280 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ x) ∘ y) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1483 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (x ∘ (y ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1686 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((x ∘ y) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1889 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ x)) ∘ (y ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2092 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ x) ∘ (y ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2295 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (x ∘ y))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2498 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ x) ∘ y)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2701 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (x ∘ y)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2904 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ x)) ∘ y) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3107 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ x) ∘ y) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3310 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (x ∘ (y ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3513 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((x ∘ y) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3716 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ x) ∘ (y ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3919 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (x ∘ y)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4122 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ x) ∘ y) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4315 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = x ∘ (y ∘ z)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4437 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (x ∘ y) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4630 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (x ∘ y) ∘ z
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation468 (G : Type*) [Magma G] (h : Equation613 G) : Equation468 G := λ x y z => h x y x x y z
theorem Equation816_implies_Equation671 (G : Type*) [Magma G] (h : Equation816 G) : Equation671 G := λ x y z => h x y x x y z
theorem Equation1019_implies_Equation874 (G : Type*) [Magma G] (h : Equation1019 G) : Equation874 G := λ x y z => h x y x x y z
theorem Equation1222_implies_Equation1077 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1077 G := λ x y z => h x y x x y z
theorem Equation1425_implies_Equation1280 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1280 G := λ x y z => h x y x x y z
theorem Equation1628_implies_Equation1483 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1483 G := λ x y z => h x y x x y z
theorem Equation1831_implies_Equation1686 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1686 G := λ x y z => h x y x x y z
theorem Equation2034_implies_Equation1889 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1889 G := λ x y z => h x y x x y z
theorem Equation2237_implies_Equation2092 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2092 G := λ x y z => h x y x x y z
theorem Equation2440_implies_Equation2295 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2295 G := λ x y z => h x y x x y z
theorem Equation2643_implies_Equation2498 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2498 G := λ x y z => h x y x x y z
theorem Equation2846_implies_Equation2701 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2701 G := λ x y z => h x y x x y z
theorem Equation3049_implies_Equation2904 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2904 G := λ x y z => h x y x x y z
theorem Equation3252_implies_Equation3107 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3107 G := λ x y z => h x y x x y z
theorem Equation3455_implies_Equation3310 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3310 G := λ x y z => h x y x x y z
theorem Equation3658_implies_Equation3513 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3513 G := λ x y z => h x y x x y z
theorem Equation3861_implies_Equation3716 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3716 G := λ x y z => h x y x x y z
theorem Equation4064_implies_Equation3919 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3919 G := λ x y z => h x y x x y z
theorem Equation4267_implies_Equation4122 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4122 G := λ x y z => h x y x x y z
theorem Equation4379_implies_Equation4315 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4315 G := λ x y z => h x y x x y z
theorem Equation4582_implies_Equation4437 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4437 G := λ x y z => h x y x x y z
theorem Equation4694_implies_Equation4630 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4630 G := λ x y z => h x y x x y z