import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation469 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (x ∘ (z ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation672 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((x ∘ z) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation875 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ x) ∘ (z ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1078 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (x ∘ z)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1281 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ x) ∘ z) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1484 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (x ∘ (z ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1687 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((x ∘ z) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1890 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ x)) ∘ (z ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2093 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ x) ∘ (z ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2296 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (x ∘ z))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2499 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ x) ∘ z)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2702 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (x ∘ z)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2905 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ x)) ∘ z) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3108 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ x) ∘ z) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3311 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (x ∘ (z ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3514 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((x ∘ z) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3717 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ x) ∘ (z ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3920 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (x ∘ z)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4123 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ x) ∘ z) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4316 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = x ∘ (z ∘ x)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4438 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (x ∘ z) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4631 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (x ∘ z) ∘ x
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation469 (G : Type*) [Magma G] (h : Equation613 G) : Equation469 G := λ x y z => h x y x x z x
theorem Equation816_implies_Equation672 (G : Type*) [Magma G] (h : Equation816 G) : Equation672 G := λ x y z => h x y x x z x
theorem Equation1019_implies_Equation875 (G : Type*) [Magma G] (h : Equation1019 G) : Equation875 G := λ x y z => h x y x x z x
theorem Equation1222_implies_Equation1078 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1078 G := λ x y z => h x y x x z x
theorem Equation1425_implies_Equation1281 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1281 G := λ x y z => h x y x x z x
theorem Equation1628_implies_Equation1484 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1484 G := λ x y z => h x y x x z x
theorem Equation1831_implies_Equation1687 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1687 G := λ x y z => h x y x x z x
theorem Equation2034_implies_Equation1890 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1890 G := λ x y z => h x y x x z x
theorem Equation2237_implies_Equation2093 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2093 G := λ x y z => h x y x x z x
theorem Equation2440_implies_Equation2296 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2296 G := λ x y z => h x y x x z x
theorem Equation2643_implies_Equation2499 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2499 G := λ x y z => h x y x x z x
theorem Equation2846_implies_Equation2702 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2702 G := λ x y z => h x y x x z x
theorem Equation3049_implies_Equation2905 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2905 G := λ x y z => h x y x x z x
theorem Equation3252_implies_Equation3108 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3108 G := λ x y z => h x y x x z x
theorem Equation3455_implies_Equation3311 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3311 G := λ x y z => h x y x x z x
theorem Equation3658_implies_Equation3514 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3514 G := λ x y z => h x y x x z x
theorem Equation3861_implies_Equation3717 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3717 G := λ x y z => h x y x x z x
theorem Equation4064_implies_Equation3920 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3920 G := λ x y z => h x y x x z x
theorem Equation4267_implies_Equation4123 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4123 G := λ x y z => h x y x x z x
theorem Equation4379_implies_Equation4316 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4316 G := λ x y z => h x y x x z x
theorem Equation4582_implies_Equation4438 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4438 G := λ x y z => h x y x x z x
theorem Equation4694_implies_Equation4631 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4631 G := λ x y z => h x y x x z x