import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation483 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ (x ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation686 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((z ∘ x) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation889 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ (x ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1092 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (z ∘ x)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1295 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ z) ∘ x) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1498 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ (x ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1701 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((z ∘ x) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1904 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ (x ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2107 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ (x ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2310 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (z ∘ x))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2513 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ z) ∘ x)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2716 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (z ∘ x)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2919 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ z)) ∘ x) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3122 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ z) ∘ x) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3325 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ (x ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3528 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((z ∘ x) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3731 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ (x ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3934 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (z ∘ x)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4137 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ z) ∘ x) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4327 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = z ∘ (x ∘ x)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4452 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (z ∘ x) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4642 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (z ∘ x) ∘ x
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation483 (G : Type*) [Magma G] (h : Equation613 G) : Equation483 G := λ x y z => h x y x z x x
theorem Equation816_implies_Equation686 (G : Type*) [Magma G] (h : Equation816 G) : Equation686 G := λ x y z => h x y x z x x
theorem Equation1019_implies_Equation889 (G : Type*) [Magma G] (h : Equation1019 G) : Equation889 G := λ x y z => h x y x z x x
theorem Equation1222_implies_Equation1092 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1092 G := λ x y z => h x y x z x x
theorem Equation1425_implies_Equation1295 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1295 G := λ x y z => h x y x z x x
theorem Equation1628_implies_Equation1498 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1498 G := λ x y z => h x y x z x x
theorem Equation1831_implies_Equation1701 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1701 G := λ x y z => h x y x z x x
theorem Equation2034_implies_Equation1904 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1904 G := λ x y z => h x y x z x x
theorem Equation2237_implies_Equation2107 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2107 G := λ x y z => h x y x z x x
theorem Equation2440_implies_Equation2310 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2310 G := λ x y z => h x y x z x x
theorem Equation2643_implies_Equation2513 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2513 G := λ x y z => h x y x z x x
theorem Equation2846_implies_Equation2716 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2716 G := λ x y z => h x y x z x x
theorem Equation3049_implies_Equation2919 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2919 G := λ x y z => h x y x z x x
theorem Equation3252_implies_Equation3122 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3122 G := λ x y z => h x y x z x x
theorem Equation3455_implies_Equation3325 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3325 G := λ x y z => h x y x z x x
theorem Equation3658_implies_Equation3528 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3528 G := λ x y z => h x y x z x x
theorem Equation3861_implies_Equation3731 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3731 G := λ x y z => h x y x z x x
theorem Equation4064_implies_Equation3934 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3934 G := λ x y z => h x y x z x x
theorem Equation4267_implies_Equation4137 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4137 G := λ x y z => h x y x z x x
theorem Equation4379_implies_Equation4327 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4327 G := λ x y z => h x y x z x x
theorem Equation4582_implies_Equation4452 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4452 G := λ x y z => h x y x z x x
theorem Equation4694_implies_Equation4642 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4642 G := λ x y z => h x y x z x x