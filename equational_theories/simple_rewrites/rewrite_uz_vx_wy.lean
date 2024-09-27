import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation562 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ (z ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation765 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((y ∘ z) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation968 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ (z ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1171 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (y ∘ z)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1374 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ y) ∘ z) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1577 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ (z ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1780 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((y ∘ z) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1983 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ (z ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2186 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ (z ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2389 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (y ∘ z))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2592 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ y) ∘ z)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2795 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (y ∘ z)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2998 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ y)) ∘ z) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3201 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ y) ∘ z) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3404 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ (z ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3607 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((y ∘ z) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3810 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ (z ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4013 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (y ∘ z)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4216 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ y) ∘ z) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4364 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = y ∘ (z ∘ x)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4531 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (y ∘ z) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4679 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ z = (y ∘ z) ∘ x
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation562 (G : Type*) [Magma G] (h : Equation613 G) : Equation562 G := λ x y z => h x y z y z x
theorem Equation816_implies_Equation765 (G : Type*) [Magma G] (h : Equation816 G) : Equation765 G := λ x y z => h x y z y z x
theorem Equation1019_implies_Equation968 (G : Type*) [Magma G] (h : Equation1019 G) : Equation968 G := λ x y z => h x y z y z x
theorem Equation1222_implies_Equation1171 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1171 G := λ x y z => h x y z y z x
theorem Equation1425_implies_Equation1374 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1374 G := λ x y z => h x y z y z x
theorem Equation1628_implies_Equation1577 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1577 G := λ x y z => h x y z y z x
theorem Equation1831_implies_Equation1780 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1780 G := λ x y z => h x y z y z x
theorem Equation2034_implies_Equation1983 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1983 G := λ x y z => h x y z y z x
theorem Equation2237_implies_Equation2186 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2186 G := λ x y z => h x y z y z x
theorem Equation2440_implies_Equation2389 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2389 G := λ x y z => h x y z y z x
theorem Equation2643_implies_Equation2592 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2592 G := λ x y z => h x y z y z x
theorem Equation2846_implies_Equation2795 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2795 G := λ x y z => h x y z y z x
theorem Equation3049_implies_Equation2998 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2998 G := λ x y z => h x y z y z x
theorem Equation3252_implies_Equation3201 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3201 G := λ x y z => h x y z y z x
theorem Equation3455_implies_Equation3404 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3404 G := λ x y z => h x y z y z x
theorem Equation3658_implies_Equation3607 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3607 G := λ x y z => h x y z y z x
theorem Equation3861_implies_Equation3810 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3810 G := λ x y z => h x y z y z x
theorem Equation4064_implies_Equation4013 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4013 G := λ x y z => h x y z y z x
theorem Equation4267_implies_Equation4216 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4216 G := λ x y z => h x y z y z x
theorem Equation4379_implies_Equation4364 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4364 G := λ x y z => h x y z y z x
theorem Equation4582_implies_Equation4531 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4531 G := λ x y z => h x y z y z x
theorem Equation4694_implies_Equation4679 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4679 G := λ x y z => h x y z y z x