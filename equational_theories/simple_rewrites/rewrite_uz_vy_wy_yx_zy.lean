import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation443 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (y ∘ (z ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation646 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((y ∘ z) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation849 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ y) ∘ (z ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1052 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (y ∘ z)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1255 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ y) ∘ z) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1458 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (y ∘ (z ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1661 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((y ∘ z) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1864 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ y)) ∘ (z ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2067 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ y) ∘ (z ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2270 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (y ∘ z))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2473 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ y) ∘ z)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2676 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (y ∘ z)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2879 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ y)) ∘ z) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3082 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ y) ∘ z) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3285 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (y ∘ (z ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3488 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((y ∘ z) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3691 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ y) ∘ (z ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3894 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (y ∘ z)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4097 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ y) ∘ z) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4296 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = y ∘ (z ∘ y)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4412 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (y ∘ z) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4611 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (y ∘ z) ∘ y
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation443 (G : Type*) [Magma G] (h : Equation613 G) : Equation443 G := λ x y z => h x x y y z y
theorem Equation816_implies_Equation646 (G : Type*) [Magma G] (h : Equation816 G) : Equation646 G := λ x y z => h x x y y z y
theorem Equation1019_implies_Equation849 (G : Type*) [Magma G] (h : Equation1019 G) : Equation849 G := λ x y z => h x x y y z y
theorem Equation1222_implies_Equation1052 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1052 G := λ x y z => h x x y y z y
theorem Equation1425_implies_Equation1255 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1255 G := λ x y z => h x x y y z y
theorem Equation1628_implies_Equation1458 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1458 G := λ x y z => h x x y y z y
theorem Equation1831_implies_Equation1661 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1661 G := λ x y z => h x x y y z y
theorem Equation2034_implies_Equation1864 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1864 G := λ x y z => h x x y y z y
theorem Equation2237_implies_Equation2067 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2067 G := λ x y z => h x x y y z y
theorem Equation2440_implies_Equation2270 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2270 G := λ x y z => h x x y y z y
theorem Equation2643_implies_Equation2473 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2473 G := λ x y z => h x x y y z y
theorem Equation2846_implies_Equation2676 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2676 G := λ x y z => h x x y y z y
theorem Equation3049_implies_Equation2879 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2879 G := λ x y z => h x x y y z y
theorem Equation3252_implies_Equation3082 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3082 G := λ x y z => h x x y y z y
theorem Equation3455_implies_Equation3285 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3285 G := λ x y z => h x x y y z y
theorem Equation3658_implies_Equation3488 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3488 G := λ x y z => h x x y y z y
theorem Equation3861_implies_Equation3691 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3691 G := λ x y z => h x x y y z y
theorem Equation4064_implies_Equation3894 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3894 G := λ x y z => h x x y y z y
theorem Equation4267_implies_Equation4097 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4097 G := λ x y z => h x x y y z y
theorem Equation4379_implies_Equation4296 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4296 G := λ x y z => h x x y y z y
theorem Equation4582_implies_Equation4412 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4412 G := λ x y z => h x x y y z y
theorem Equation4694_implies_Equation4611 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4611 G := λ x y z => h x x y y z y