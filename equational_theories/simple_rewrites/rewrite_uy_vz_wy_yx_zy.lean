import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation441 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (y ∘ (y ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation644 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((y ∘ y) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation847 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ y) ∘ (y ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1050 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (y ∘ y)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1253 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ y) ∘ y) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1456 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (y ∘ (y ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1659 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((y ∘ y) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1862 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ y)) ∘ (y ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2065 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ y) ∘ (y ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2268 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (y ∘ y))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2471 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ y) ∘ y)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2674 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (y ∘ y)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2877 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ y)) ∘ y) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3080 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ y) ∘ y) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3283 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (y ∘ (y ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3486 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((y ∘ y) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3689 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ y) ∘ (y ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3892 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (y ∘ y)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4095 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ y) ∘ y) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4294 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = y ∘ (y ∘ z)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4410 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (y ∘ y) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4609 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (y ∘ y) ∘ z
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation441 (G : Type*) [Magma G] (h : Equation613 G) : Equation441 G := λ x y z => h x x y y y z
theorem Equation816_implies_Equation644 (G : Type*) [Magma G] (h : Equation816 G) : Equation644 G := λ x y z => h x x y y y z
theorem Equation1019_implies_Equation847 (G : Type*) [Magma G] (h : Equation1019 G) : Equation847 G := λ x y z => h x x y y y z
theorem Equation1222_implies_Equation1050 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1050 G := λ x y z => h x x y y y z
theorem Equation1425_implies_Equation1253 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1253 G := λ x y z => h x x y y y z
theorem Equation1628_implies_Equation1456 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1456 G := λ x y z => h x x y y y z
theorem Equation1831_implies_Equation1659 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1659 G := λ x y z => h x x y y y z
theorem Equation2034_implies_Equation1862 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1862 G := λ x y z => h x x y y y z
theorem Equation2237_implies_Equation2065 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2065 G := λ x y z => h x x y y y z
theorem Equation2440_implies_Equation2268 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2268 G := λ x y z => h x x y y y z
theorem Equation2643_implies_Equation2471 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2471 G := λ x y z => h x x y y y z
theorem Equation2846_implies_Equation2674 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2674 G := λ x y z => h x x y y y z
theorem Equation3049_implies_Equation2877 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2877 G := λ x y z => h x x y y y z
theorem Equation3252_implies_Equation3080 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3080 G := λ x y z => h x x y y y z
theorem Equation3455_implies_Equation3283 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3283 G := λ x y z => h x x y y y z
theorem Equation3658_implies_Equation3486 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3486 G := λ x y z => h x x y y y z
theorem Equation3861_implies_Equation3689 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3689 G := λ x y z => h x x y y y z
theorem Equation4064_implies_Equation3892 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3892 G := λ x y z => h x x y y y z
theorem Equation4267_implies_Equation4095 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4095 G := λ x y z => h x x y y y z
theorem Equation4379_implies_Equation4294 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4294 G := λ x y z => h x x y y y z
theorem Equation4582_implies_Equation4410 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4410 G := λ x y z => h x x y y y z
theorem Equation4694_implies_Equation4609 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4609 G := λ x y z => h x x y y y z