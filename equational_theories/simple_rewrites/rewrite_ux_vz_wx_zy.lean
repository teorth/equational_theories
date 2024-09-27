import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation502 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (x ∘ (x ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation705 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((x ∘ x) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation908 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ x) ∘ (x ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1111 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (x ∘ x)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1314 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ x) ∘ x) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1517 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (x ∘ (x ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1720 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((x ∘ x) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1923 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ x)) ∘ (x ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2126 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ x) ∘ (x ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2329 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (x ∘ x))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2532 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ x) ∘ x)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2735 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (x ∘ x)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2938 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ x)) ∘ x) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3141 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ x) ∘ x) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3344 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (x ∘ (x ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3547 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((x ∘ x) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3750 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ x) ∘ (x ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3953 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (x ∘ x)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4156 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ x) ∘ x) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4471 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (x ∘ x) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation502 (G : Type*) [Magma G] (h : Equation613 G) : Equation502 G := λ x y z => h x y y x x z
theorem Equation816_implies_Equation705 (G : Type*) [Magma G] (h : Equation816 G) : Equation705 G := λ x y z => h x y y x x z
theorem Equation1019_implies_Equation908 (G : Type*) [Magma G] (h : Equation1019 G) : Equation908 G := λ x y z => h x y y x x z
theorem Equation1222_implies_Equation1111 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1111 G := λ x y z => h x y y x x z
theorem Equation1425_implies_Equation1314 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1314 G := λ x y z => h x y y x x z
theorem Equation1628_implies_Equation1517 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1517 G := λ x y z => h x y y x x z
theorem Equation1831_implies_Equation1720 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1720 G := λ x y z => h x y y x x z
theorem Equation2034_implies_Equation1923 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1923 G := λ x y z => h x y y x x z
theorem Equation2237_implies_Equation2126 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2126 G := λ x y z => h x y y x x z
theorem Equation2440_implies_Equation2329 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2329 G := λ x y z => h x y y x x z
theorem Equation2643_implies_Equation2532 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2532 G := λ x y z => h x y y x x z
theorem Equation2846_implies_Equation2735 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2735 G := λ x y z => h x y y x x z
theorem Equation3049_implies_Equation2938 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2938 G := λ x y z => h x y y x x z
theorem Equation3252_implies_Equation3141 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3141 G := λ x y z => h x y y x x z
theorem Equation3455_implies_Equation3344 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3344 G := λ x y z => h x y y x x z
theorem Equation3658_implies_Equation3547 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3547 G := λ x y z => h x y y x x z
theorem Equation3861_implies_Equation3750 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3750 G := λ x y z => h x y y x x z
theorem Equation4064_implies_Equation3953 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3953 G := λ x y z => h x y y x x z
theorem Equation4267_implies_Equation4156 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4156 G := λ x y z => h x y y x x z
theorem Equation4582_implies_Equation4471 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4471 G := λ x y z => h x y y x x z