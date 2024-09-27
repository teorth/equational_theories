import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation428 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (x ∘ (x ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation631 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((x ∘ x) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation834 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ x) ∘ (x ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1037 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (x ∘ x)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1240 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ x) ∘ x) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1443 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (x ∘ (x ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1646 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((x ∘ x) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1849 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ x)) ∘ (x ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2052 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ x) ∘ (x ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2255 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (x ∘ x))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2458 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ x) ∘ x)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2661 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (x ∘ x)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2864 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ x)) ∘ x) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3067 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ x) ∘ x) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3270 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (x ∘ (x ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3473 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((x ∘ x) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3676 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ x) ∘ (x ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3879 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (x ∘ x)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4082 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ x) ∘ x) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4282 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = x ∘ (x ∘ z)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4397 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (x ∘ x) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4597 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (x ∘ x) ∘ z
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation428 (G : Type*) [Magma G] (h : Equation613 G) : Equation428 G := λ x y z => h x x y x x z
theorem Equation816_implies_Equation631 (G : Type*) [Magma G] (h : Equation816 G) : Equation631 G := λ x y z => h x x y x x z
theorem Equation1019_implies_Equation834 (G : Type*) [Magma G] (h : Equation1019 G) : Equation834 G := λ x y z => h x x y x x z
theorem Equation1222_implies_Equation1037 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1037 G := λ x y z => h x x y x x z
theorem Equation1425_implies_Equation1240 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1240 G := λ x y z => h x x y x x z
theorem Equation1628_implies_Equation1443 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1443 G := λ x y z => h x x y x x z
theorem Equation1831_implies_Equation1646 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1646 G := λ x y z => h x x y x x z
theorem Equation2034_implies_Equation1849 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1849 G := λ x y z => h x x y x x z
theorem Equation2237_implies_Equation2052 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2052 G := λ x y z => h x x y x x z
theorem Equation2440_implies_Equation2255 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2255 G := λ x y z => h x x y x x z
theorem Equation2643_implies_Equation2458 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2458 G := λ x y z => h x x y x x z
theorem Equation2846_implies_Equation2661 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2661 G := λ x y z => h x x y x x z
theorem Equation3049_implies_Equation2864 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2864 G := λ x y z => h x x y x x z
theorem Equation3252_implies_Equation3067 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3067 G := λ x y z => h x x y x x z
theorem Equation3455_implies_Equation3270 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3270 G := λ x y z => h x x y x x z
theorem Equation3658_implies_Equation3473 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3473 G := λ x y z => h x x y x x z
theorem Equation3861_implies_Equation3676 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3676 G := λ x y z => h x x y x x z
theorem Equation4064_implies_Equation3879 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3879 G := λ x y z => h x x y x x z
theorem Equation4267_implies_Equation4082 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4082 G := λ x y z => h x x y x x z
theorem Equation4379_implies_Equation4282 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4282 G := λ x y z => h x x y x x z
theorem Equation4582_implies_Equation4397 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4397 G := λ x y z => h x x y x x z
theorem Equation4694_implies_Equation4597 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4597 G := λ x y z => h x x y x x z