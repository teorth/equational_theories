import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation471 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (x ∘ (z ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation674 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((x ∘ z) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation877 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ x) ∘ (z ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1080 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (x ∘ z)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1283 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ x) ∘ z) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1486 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (x ∘ (z ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1689 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((x ∘ z) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1892 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ x)) ∘ (z ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2095 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ x) ∘ (z ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2298 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (x ∘ z))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2501 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ x) ∘ z)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2704 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (x ∘ z)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2907 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ x)) ∘ z) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3110 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ x) ∘ z) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3313 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (x ∘ (z ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3516 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((x ∘ z) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3719 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ x) ∘ (z ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3922 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (x ∘ z)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4125 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ x) ∘ z) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4318 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = x ∘ (z ∘ z)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4440 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (x ∘ z) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4633 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (x ∘ z) ∘ z
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation471 (G : Type*) [Magma G] (h : Equation613 G) : Equation471 G := λ x y z => h x y x x z z
theorem Equation816_implies_Equation674 (G : Type*) [Magma G] (h : Equation816 G) : Equation674 G := λ x y z => h x y x x z z
theorem Equation1019_implies_Equation877 (G : Type*) [Magma G] (h : Equation1019 G) : Equation877 G := λ x y z => h x y x x z z
theorem Equation1222_implies_Equation1080 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1080 G := λ x y z => h x y x x z z
theorem Equation1425_implies_Equation1283 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1283 G := λ x y z => h x y x x z z
theorem Equation1628_implies_Equation1486 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1486 G := λ x y z => h x y x x z z
theorem Equation1831_implies_Equation1689 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1689 G := λ x y z => h x y x x z z
theorem Equation2034_implies_Equation1892 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1892 G := λ x y z => h x y x x z z
theorem Equation2237_implies_Equation2095 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2095 G := λ x y z => h x y x x z z
theorem Equation2440_implies_Equation2298 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2298 G := λ x y z => h x y x x z z
theorem Equation2643_implies_Equation2501 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2501 G := λ x y z => h x y x x z z
theorem Equation2846_implies_Equation2704 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2704 G := λ x y z => h x y x x z z
theorem Equation3049_implies_Equation2907 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2907 G := λ x y z => h x y x x z z
theorem Equation3252_implies_Equation3110 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3110 G := λ x y z => h x y x x z z
theorem Equation3455_implies_Equation3313 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3313 G := λ x y z => h x y x x z z
theorem Equation3658_implies_Equation3516 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3516 G := λ x y z => h x y x x z z
theorem Equation3861_implies_Equation3719 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3719 G := λ x y z => h x y x x z z
theorem Equation4064_implies_Equation3922 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3922 G := λ x y z => h x y x x z z
theorem Equation4267_implies_Equation4125 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4125 G := λ x y z => h x y x x z z
theorem Equation4379_implies_Equation4318 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4318 G := λ x y z => h x y x x z z
theorem Equation4582_implies_Equation4440 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4440 G := λ x y z => h x y x x z z
theorem Equation4694_implies_Equation4633 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4633 G := λ x y z => h x y x x z z