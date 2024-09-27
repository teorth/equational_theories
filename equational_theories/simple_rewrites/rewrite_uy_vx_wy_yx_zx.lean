import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation419 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (y ∘ (y ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation622 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ ((y ∘ y) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation825 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ y) ∘ (y ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1028 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ (y ∘ y)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1231 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((x ∘ y) ∘ y) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1434 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ (y ∘ (y ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1637 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ ((y ∘ y) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1840 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ y)) ∘ (y ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2043 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ y) ∘ (y ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2246 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ (y ∘ y))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2449 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((x ∘ y) ∘ y)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2652 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ (y ∘ y)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2855 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (x ∘ y)) ∘ y) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3058 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ x) ∘ y) ∘ y) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3261 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ (y ∘ (y ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3464 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ ((y ∘ y) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3667 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ y) ∘ (y ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3870 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ (y ∘ y)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4073 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((x ∘ y) ∘ y) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4275 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = y ∘ (y ∘ x)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4388 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = (y ∘ y) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4590 (G: Type*) [Magma G] := ∀ x y : G, (x ∘ x) ∘ x = (y ∘ y) ∘ x
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation419 (G : Type*) [Magma G] (h : Equation613 G) : Equation419 G := λ x y => h x x x y y x
theorem Equation816_implies_Equation622 (G : Type*) [Magma G] (h : Equation816 G) : Equation622 G := λ x y => h x x x y y x
theorem Equation1019_implies_Equation825 (G : Type*) [Magma G] (h : Equation1019 G) : Equation825 G := λ x y => h x x x y y x
theorem Equation1222_implies_Equation1028 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1028 G := λ x y => h x x x y y x
theorem Equation1425_implies_Equation1231 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1231 G := λ x y => h x x x y y x
theorem Equation1628_implies_Equation1434 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1434 G := λ x y => h x x x y y x
theorem Equation1831_implies_Equation1637 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1637 G := λ x y => h x x x y y x
theorem Equation2034_implies_Equation1840 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1840 G := λ x y => h x x x y y x
theorem Equation2237_implies_Equation2043 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2043 G := λ x y => h x x x y y x
theorem Equation2440_implies_Equation2246 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2246 G := λ x y => h x x x y y x
theorem Equation2643_implies_Equation2449 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2449 G := λ x y => h x x x y y x
theorem Equation2846_implies_Equation2652 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2652 G := λ x y => h x x x y y x
theorem Equation3049_implies_Equation2855 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2855 G := λ x y => h x x x y y x
theorem Equation3252_implies_Equation3058 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3058 G := λ x y => h x x x y y x
theorem Equation3455_implies_Equation3261 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3261 G := λ x y => h x x x y y x
theorem Equation3658_implies_Equation3464 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3464 G := λ x y => h x x x y y x
theorem Equation3861_implies_Equation3667 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3667 G := λ x y => h x x x y y x
theorem Equation4064_implies_Equation3870 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3870 G := λ x y => h x x x y y x
theorem Equation4267_implies_Equation4073 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4073 G := λ x y => h x x x y y x
theorem Equation4379_implies_Equation4275 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4275 G := λ x y => h x x x y y x
theorem Equation4582_implies_Equation4388 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4388 G := λ x y => h x x x y y x
theorem Equation4694_implies_Equation4590 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4590 G := λ x y => h x x x y y x