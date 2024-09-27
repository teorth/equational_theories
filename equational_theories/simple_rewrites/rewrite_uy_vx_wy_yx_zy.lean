import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation439 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (y ∘ (y ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation642 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ ((y ∘ y) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation845 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ y) ∘ (y ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1048 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ (y ∘ y)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1251 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((y ∘ y) ∘ y) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1454 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (y ∘ (y ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1657 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ ((y ∘ y) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1860 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ y)) ∘ (y ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2063 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ y) ∘ (y ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2266 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ (y ∘ y))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2469 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((y ∘ y) ∘ y)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2672 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ (y ∘ y)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2875 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (y ∘ y)) ∘ y) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3078 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ y) ∘ y) ∘ y) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3281 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (y ∘ (y ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3484 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ ((y ∘ y) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3687 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ y) ∘ (y ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3890 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ (y ∘ y)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4093 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((y ∘ y) ∘ y) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4293 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = y ∘ (y ∘ x)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4408 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = (y ∘ y) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4608 (G: Type*) [Magma G] := ∀ x y : G, (x ∘ x) ∘ y = (y ∘ y) ∘ x
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation439 (G : Type*) [Magma G] (h : Equation613 G) : Equation439 G := λ x y => h x x y y y x
theorem Equation816_implies_Equation642 (G : Type*) [Magma G] (h : Equation816 G) : Equation642 G := λ x y => h x x y y y x
theorem Equation1019_implies_Equation845 (G : Type*) [Magma G] (h : Equation1019 G) : Equation845 G := λ x y => h x x y y y x
theorem Equation1222_implies_Equation1048 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1048 G := λ x y => h x x y y y x
theorem Equation1425_implies_Equation1251 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1251 G := λ x y => h x x y y y x
theorem Equation1628_implies_Equation1454 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1454 G := λ x y => h x x y y y x
theorem Equation1831_implies_Equation1657 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1657 G := λ x y => h x x y y y x
theorem Equation2034_implies_Equation1860 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1860 G := λ x y => h x x y y y x
theorem Equation2237_implies_Equation2063 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2063 G := λ x y => h x x y y y x
theorem Equation2440_implies_Equation2266 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2266 G := λ x y => h x x y y y x
theorem Equation2643_implies_Equation2469 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2469 G := λ x y => h x x y y y x
theorem Equation2846_implies_Equation2672 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2672 G := λ x y => h x x y y y x
theorem Equation3049_implies_Equation2875 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2875 G := λ x y => h x x y y y x
theorem Equation3252_implies_Equation3078 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3078 G := λ x y => h x x y y y x
theorem Equation3455_implies_Equation3281 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3281 G := λ x y => h x x y y y x
theorem Equation3658_implies_Equation3484 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3484 G := λ x y => h x x y y y x
theorem Equation3861_implies_Equation3687 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3687 G := λ x y => h x x y y y x
theorem Equation4064_implies_Equation3890 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3890 G := λ x y => h x x y y y x
theorem Equation4267_implies_Equation4093 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4093 G := λ x y => h x x y y y x
theorem Equation4379_implies_Equation4293 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4293 G := λ x y => h x x y y y x
theorem Equation4582_implies_Equation4408 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4408 G := λ x y => h x x y y y x
theorem Equation4694_implies_Equation4608 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4608 G := λ x y => h x x y y y x