import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation431 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (x ∘ (y ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation634 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((x ∘ y) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation837 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ x) ∘ (y ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1040 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (x ∘ y)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1243 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ x) ∘ y) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1446 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (x ∘ (y ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1649 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((x ∘ y) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1852 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ x)) ∘ (y ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2055 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ x) ∘ (y ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2258 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (x ∘ y))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2461 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ x) ∘ y)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2664 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (x ∘ y)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2867 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ x)) ∘ y) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3070 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ x) ∘ y) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3273 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (x ∘ (y ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3476 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((x ∘ y) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3679 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ x) ∘ (y ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3882 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (x ∘ y)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4085 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ x) ∘ y) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4285 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = x ∘ (y ∘ z)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4400 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (x ∘ y) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4600 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (x ∘ y) ∘ z
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation431 (G : Type*) [Magma G] (h : Equation613 G) : Equation431 G := λ x y z => h x x y x y z
theorem Equation816_implies_Equation634 (G : Type*) [Magma G] (h : Equation816 G) : Equation634 G := λ x y z => h x x y x y z
theorem Equation1019_implies_Equation837 (G : Type*) [Magma G] (h : Equation1019 G) : Equation837 G := λ x y z => h x x y x y z
theorem Equation1222_implies_Equation1040 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1040 G := λ x y z => h x x y x y z
theorem Equation1425_implies_Equation1243 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1243 G := λ x y z => h x x y x y z
theorem Equation1628_implies_Equation1446 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1446 G := λ x y z => h x x y x y z
theorem Equation1831_implies_Equation1649 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1649 G := λ x y z => h x x y x y z
theorem Equation2034_implies_Equation1852 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1852 G := λ x y z => h x x y x y z
theorem Equation2237_implies_Equation2055 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2055 G := λ x y z => h x x y x y z
theorem Equation2440_implies_Equation2258 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2258 G := λ x y z => h x x y x y z
theorem Equation2643_implies_Equation2461 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2461 G := λ x y z => h x x y x y z
theorem Equation2846_implies_Equation2664 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2664 G := λ x y z => h x x y x y z
theorem Equation3049_implies_Equation2867 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2867 G := λ x y z => h x x y x y z
theorem Equation3252_implies_Equation3070 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3070 G := λ x y z => h x x y x y z
theorem Equation3455_implies_Equation3273 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3273 G := λ x y z => h x x y x y z
theorem Equation3658_implies_Equation3476 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3476 G := λ x y z => h x x y x y z
theorem Equation3861_implies_Equation3679 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3679 G := λ x y z => h x x y x y z
theorem Equation4064_implies_Equation3882 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3882 G := λ x y z => h x x y x y z
theorem Equation4267_implies_Equation4085 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4085 G := λ x y z => h x x y x y z
theorem Equation4379_implies_Equation4285 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4285 G := λ x y z => h x x y x y z
theorem Equation4582_implies_Equation4400 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4400 G := λ x y z => h x x y x y z
theorem Equation4694_implies_Equation4600 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4600 G := λ x y z => h x x y x y z