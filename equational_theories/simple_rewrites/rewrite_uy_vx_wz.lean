import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation575 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (y ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation778 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ y) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation981 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (y ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1184 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ y)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1387 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ y) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1590 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (y ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1793 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ y) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1996 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (y ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2199 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (y ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2402 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ y))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2605 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ y)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2808 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ y)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3011 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ y) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3214 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ y) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3417 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (y ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3620 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ y) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3823 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (y ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4026 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ y)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4229 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ y) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4369 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = z ∘ (y ∘ x)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4544 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ y) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4684 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ z = (z ∘ y) ∘ x
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation575 (G : Type*) [Magma G] (h : Equation613 G) : Equation575 G := λ x y z => h x y z z y x
theorem Equation816_implies_Equation778 (G : Type*) [Magma G] (h : Equation816 G) : Equation778 G := λ x y z => h x y z z y x
theorem Equation1019_implies_Equation981 (G : Type*) [Magma G] (h : Equation1019 G) : Equation981 G := λ x y z => h x y z z y x
theorem Equation1222_implies_Equation1184 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1184 G := λ x y z => h x y z z y x
theorem Equation1425_implies_Equation1387 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1387 G := λ x y z => h x y z z y x
theorem Equation1628_implies_Equation1590 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1590 G := λ x y z => h x y z z y x
theorem Equation1831_implies_Equation1793 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1793 G := λ x y z => h x y z z y x
theorem Equation2034_implies_Equation1996 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1996 G := λ x y z => h x y z z y x
theorem Equation2237_implies_Equation2199 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2199 G := λ x y z => h x y z z y x
theorem Equation2440_implies_Equation2402 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2402 G := λ x y z => h x y z z y x
theorem Equation2643_implies_Equation2605 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2605 G := λ x y z => h x y z z y x
theorem Equation2846_implies_Equation2808 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2808 G := λ x y z => h x y z z y x
theorem Equation3049_implies_Equation3011 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3011 G := λ x y z => h x y z z y x
theorem Equation3252_implies_Equation3214 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3214 G := λ x y z => h x y z z y x
theorem Equation3455_implies_Equation3417 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3417 G := λ x y z => h x y z z y x
theorem Equation3658_implies_Equation3620 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3620 G := λ x y z => h x y z z y x
theorem Equation3861_implies_Equation3823 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3823 G := λ x y z => h x y z z y x
theorem Equation4064_implies_Equation4026 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4026 G := λ x y z => h x y z z y x
theorem Equation4267_implies_Equation4229 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4229 G := λ x y z => h x y z z y x
theorem Equation4379_implies_Equation4369 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4369 G := λ x y z => h x y z z y x
theorem Equation4582_implies_Equation4544 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4544 G := λ x y z => h x y z z y x
theorem Equation4694_implies_Equation4684 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4684 G := λ x y z => h x y z z y x