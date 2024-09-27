import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation447 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ (x ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation650 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((z ∘ x) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation853 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ (x ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1056 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (z ∘ x)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1259 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ z) ∘ x) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1462 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ (x ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1665 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((z ∘ x) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1868 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ (x ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2071 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ (x ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2274 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (z ∘ x))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2477 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ z) ∘ x)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2680 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (z ∘ x)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2883 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ z)) ∘ x) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3086 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ z) ∘ x) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3289 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ (x ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3492 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((z ∘ x) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3695 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ (x ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3898 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (z ∘ x)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4101 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ z) ∘ x) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4300 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = z ∘ (x ∘ y)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4416 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (z ∘ x) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4615 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (z ∘ x) ∘ y
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation447 (G : Type*) [Magma G] (h : Equation613 G) : Equation447 G := λ x y z => h x x y z x y
theorem Equation816_implies_Equation650 (G : Type*) [Magma G] (h : Equation816 G) : Equation650 G := λ x y z => h x x y z x y
theorem Equation1019_implies_Equation853 (G : Type*) [Magma G] (h : Equation1019 G) : Equation853 G := λ x y z => h x x y z x y
theorem Equation1222_implies_Equation1056 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1056 G := λ x y z => h x x y z x y
theorem Equation1425_implies_Equation1259 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1259 G := λ x y z => h x x y z x y
theorem Equation1628_implies_Equation1462 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1462 G := λ x y z => h x x y z x y
theorem Equation1831_implies_Equation1665 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1665 G := λ x y z => h x x y z x y
theorem Equation2034_implies_Equation1868 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1868 G := λ x y z => h x x y z x y
theorem Equation2237_implies_Equation2071 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2071 G := λ x y z => h x x y z x y
theorem Equation2440_implies_Equation2274 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2274 G := λ x y z => h x x y z x y
theorem Equation2643_implies_Equation2477 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2477 G := λ x y z => h x x y z x y
theorem Equation2846_implies_Equation2680 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2680 G := λ x y z => h x x y z x y
theorem Equation3049_implies_Equation2883 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2883 G := λ x y z => h x x y z x y
theorem Equation3252_implies_Equation3086 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3086 G := λ x y z => h x x y z x y
theorem Equation3455_implies_Equation3289 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3289 G := λ x y z => h x x y z x y
theorem Equation3658_implies_Equation3492 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3492 G := λ x y z => h x x y z x y
theorem Equation3861_implies_Equation3695 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3695 G := λ x y z => h x x y z x y
theorem Equation4064_implies_Equation3898 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3898 G := λ x y z => h x x y z x y
theorem Equation4267_implies_Equation4101 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4101 G := λ x y z => h x x y z x y
theorem Equation4379_implies_Equation4300 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4300 G := λ x y z => h x x y z x y
theorem Equation4582_implies_Equation4416 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4416 G := λ x y z => h x x y z x y
theorem Equation4694_implies_Equation4615 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4615 G := λ x y z => h x x y z x y