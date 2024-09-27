import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation481 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (y ∘ (z ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation684 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((y ∘ z) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation887 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ y) ∘ (z ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1090 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (y ∘ z)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1293 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ y) ∘ z) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1496 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (y ∘ (z ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1699 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((y ∘ z) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1902 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ y)) ∘ (z ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2105 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ y) ∘ (z ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2308 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (y ∘ z))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2511 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ y) ∘ z)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2714 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (y ∘ z)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2917 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ y)) ∘ z) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3120 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ y) ∘ z) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3323 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (y ∘ (z ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3526 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((y ∘ z) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3729 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ y) ∘ (z ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3932 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (y ∘ z)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4135 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ y) ∘ z) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4325 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = y ∘ (z ∘ z)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4450 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (y ∘ z) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4640 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (y ∘ z) ∘ z
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation481 (G : Type*) [Magma G] (h : Equation613 G) : Equation481 G := λ x y z => h x y x y z z
theorem Equation816_implies_Equation684 (G : Type*) [Magma G] (h : Equation816 G) : Equation684 G := λ x y z => h x y x y z z
theorem Equation1019_implies_Equation887 (G : Type*) [Magma G] (h : Equation1019 G) : Equation887 G := λ x y z => h x y x y z z
theorem Equation1222_implies_Equation1090 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1090 G := λ x y z => h x y x y z z
theorem Equation1425_implies_Equation1293 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1293 G := λ x y z => h x y x y z z
theorem Equation1628_implies_Equation1496 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1496 G := λ x y z => h x y x y z z
theorem Equation1831_implies_Equation1699 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1699 G := λ x y z => h x y x y z z
theorem Equation2034_implies_Equation1902 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1902 G := λ x y z => h x y x y z z
theorem Equation2237_implies_Equation2105 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2105 G := λ x y z => h x y x y z z
theorem Equation2440_implies_Equation2308 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2308 G := λ x y z => h x y x y z z
theorem Equation2643_implies_Equation2511 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2511 G := λ x y z => h x y x y z z
theorem Equation2846_implies_Equation2714 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2714 G := λ x y z => h x y x y z z
theorem Equation3049_implies_Equation2917 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2917 G := λ x y z => h x y x y z z
theorem Equation3252_implies_Equation3120 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3120 G := λ x y z => h x y x y z z
theorem Equation3455_implies_Equation3323 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3323 G := λ x y z => h x y x y z z
theorem Equation3658_implies_Equation3526 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3526 G := λ x y z => h x y x y z z
theorem Equation3861_implies_Equation3729 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3729 G := λ x y z => h x y x y z z
theorem Equation4064_implies_Equation3932 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3932 G := λ x y z => h x y x y z z
theorem Equation4267_implies_Equation4135 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4135 G := λ x y z => h x y x y z z
theorem Equation4379_implies_Equation4325 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4325 G := λ x y z => h x y x y z z
theorem Equation4582_implies_Equation4450 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4450 G := λ x y z => h x y x y z z
theorem Equation4694_implies_Equation4640 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4640 G := λ x y z => h x y x y z z