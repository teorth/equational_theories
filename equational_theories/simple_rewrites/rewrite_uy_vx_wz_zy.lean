import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation524 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ (y ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation727 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((z ∘ y) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation930 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ (y ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1133 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (z ∘ y)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1336 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ z) ∘ y) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1539 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ (y ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1742 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((z ∘ y) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1945 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ (y ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2148 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ (y ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2351 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (z ∘ y))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2554 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ z) ∘ y)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2757 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (z ∘ y)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2960 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ z)) ∘ y) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3163 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ z) ∘ y) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3366 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ (y ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3569 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((z ∘ y) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3772 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ (y ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3975 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (z ∘ y)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4178 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ z) ∘ y) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4350 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = z ∘ (y ∘ x)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4493 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (z ∘ y) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4665 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ y = (z ∘ y) ∘ x
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation524 (G : Type*) [Magma G] (h : Equation613 G) : Equation524 G := λ x y z => h x y y z y x
theorem Equation816_implies_Equation727 (G : Type*) [Magma G] (h : Equation816 G) : Equation727 G := λ x y z => h x y y z y x
theorem Equation1019_implies_Equation930 (G : Type*) [Magma G] (h : Equation1019 G) : Equation930 G := λ x y z => h x y y z y x
theorem Equation1222_implies_Equation1133 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1133 G := λ x y z => h x y y z y x
theorem Equation1425_implies_Equation1336 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1336 G := λ x y z => h x y y z y x
theorem Equation1628_implies_Equation1539 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1539 G := λ x y z => h x y y z y x
theorem Equation1831_implies_Equation1742 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1742 G := λ x y z => h x y y z y x
theorem Equation2034_implies_Equation1945 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1945 G := λ x y z => h x y y z y x
theorem Equation2237_implies_Equation2148 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2148 G := λ x y z => h x y y z y x
theorem Equation2440_implies_Equation2351 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2351 G := λ x y z => h x y y z y x
theorem Equation2643_implies_Equation2554 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2554 G := λ x y z => h x y y z y x
theorem Equation2846_implies_Equation2757 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2757 G := λ x y z => h x y y z y x
theorem Equation3049_implies_Equation2960 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2960 G := λ x y z => h x y y z y x
theorem Equation3252_implies_Equation3163 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3163 G := λ x y z => h x y y z y x
theorem Equation3455_implies_Equation3366 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3366 G := λ x y z => h x y y z y x
theorem Equation3658_implies_Equation3569 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3569 G := λ x y z => h x y y z y x
theorem Equation3861_implies_Equation3772 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3772 G := λ x y z => h x y y z y x
theorem Equation4064_implies_Equation3975 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3975 G := λ x y z => h x y y z y x
theorem Equation4267_implies_Equation4178 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4178 G := λ x y z => h x y y z y x
theorem Equation4379_implies_Equation4350 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4350 G := λ x y z => h x y y z y x
theorem Equation4582_implies_Equation4493 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4493 G := λ x y z => h x y y z y x
theorem Equation4694_implies_Equation4665 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4665 G := λ x y z => h x y y z y x