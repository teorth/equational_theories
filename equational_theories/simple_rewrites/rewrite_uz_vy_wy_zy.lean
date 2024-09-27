import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation517 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (y ∘ (z ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation720 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((y ∘ z) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation923 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ y) ∘ (z ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1126 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (y ∘ z)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1329 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ y) ∘ z) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1532 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (y ∘ (z ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1735 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((y ∘ z) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1938 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ y)) ∘ (z ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2141 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ y) ∘ (z ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2344 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (y ∘ z))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2547 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ y) ∘ z)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2750 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (y ∘ z)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2953 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ y)) ∘ z) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3156 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ y) ∘ z) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3359 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (y ∘ (z ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3562 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((y ∘ z) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3765 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ y) ∘ (z ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3968 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (y ∘ z)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4171 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ y) ∘ z) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4486 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (y ∘ z) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation517 (G : Type*) [Magma G] (h : Equation613 G) : Equation517 G := λ x y z => h x y y y z y
theorem Equation816_implies_Equation720 (G : Type*) [Magma G] (h : Equation816 G) : Equation720 G := λ x y z => h x y y y z y
theorem Equation1019_implies_Equation923 (G : Type*) [Magma G] (h : Equation1019 G) : Equation923 G := λ x y z => h x y y y z y
theorem Equation1222_implies_Equation1126 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1126 G := λ x y z => h x y y y z y
theorem Equation1425_implies_Equation1329 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1329 G := λ x y z => h x y y y z y
theorem Equation1628_implies_Equation1532 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1532 G := λ x y z => h x y y y z y
theorem Equation1831_implies_Equation1735 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1735 G := λ x y z => h x y y y z y
theorem Equation2034_implies_Equation1938 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1938 G := λ x y z => h x y y y z y
theorem Equation2237_implies_Equation2141 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2141 G := λ x y z => h x y y y z y
theorem Equation2440_implies_Equation2344 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2344 G := λ x y z => h x y y y z y
theorem Equation2643_implies_Equation2547 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2547 G := λ x y z => h x y y y z y
theorem Equation2846_implies_Equation2750 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2750 G := λ x y z => h x y y y z y
theorem Equation3049_implies_Equation2953 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2953 G := λ x y z => h x y y y z y
theorem Equation3252_implies_Equation3156 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3156 G := λ x y z => h x y y y z y
theorem Equation3455_implies_Equation3359 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3359 G := λ x y z => h x y y y z y
theorem Equation3658_implies_Equation3562 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3562 G := λ x y z => h x y y y z y
theorem Equation3861_implies_Equation3765 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3765 G := λ x y z => h x y y y z y
theorem Equation4064_implies_Equation3968 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3968 G := λ x y z => h x y y y z y
theorem Equation4267_implies_Equation4171 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4171 G := λ x y z => h x y y y z y
theorem Equation4582_implies_Equation4486 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4486 G := λ x y z => h x y y y z y