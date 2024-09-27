import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation415 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ (x ∘ (y ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation618 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ ((x ∘ y) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation821 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ x) ∘ (y ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1024 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ (x ∘ y)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1227 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((x ∘ x) ∘ y) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1430 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ (x ∘ (y ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1633 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ ((x ∘ y) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1836 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ x)) ∘ (y ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2039 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ x) ∘ (y ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2242 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ (x ∘ y))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2445 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((x ∘ x) ∘ y)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2648 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ (x ∘ y)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2851 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (x ∘ x)) ∘ y) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3054 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ x) ∘ x) ∘ y) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3257 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ (x ∘ (y ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3460 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ ((x ∘ y) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3663 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ x) ∘ (y ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3866 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ (x ∘ y)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4069 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((x ∘ x) ∘ y) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4271 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ x) = x ∘ (y ∘ z)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4384 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ x) = (x ∘ y) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4586 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ x = (x ∘ y) ∘ z
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation415 (G : Type*) [Magma G] (h : Equation613 G) : Equation415 G := λ x y z => h x x x x y z
theorem Equation816_implies_Equation618 (G : Type*) [Magma G] (h : Equation816 G) : Equation618 G := λ x y z => h x x x x y z
theorem Equation1019_implies_Equation821 (G : Type*) [Magma G] (h : Equation1019 G) : Equation821 G := λ x y z => h x x x x y z
theorem Equation1222_implies_Equation1024 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1024 G := λ x y z => h x x x x y z
theorem Equation1425_implies_Equation1227 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1227 G := λ x y z => h x x x x y z
theorem Equation1628_implies_Equation1430 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1430 G := λ x y z => h x x x x y z
theorem Equation1831_implies_Equation1633 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1633 G := λ x y z => h x x x x y z
theorem Equation2034_implies_Equation1836 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1836 G := λ x y z => h x x x x y z
theorem Equation2237_implies_Equation2039 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2039 G := λ x y z => h x x x x y z
theorem Equation2440_implies_Equation2242 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2242 G := λ x y z => h x x x x y z
theorem Equation2643_implies_Equation2445 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2445 G := λ x y z => h x x x x y z
theorem Equation2846_implies_Equation2648 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2648 G := λ x y z => h x x x x y z
theorem Equation3049_implies_Equation2851 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2851 G := λ x y z => h x x x x y z
theorem Equation3252_implies_Equation3054 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3054 G := λ x y z => h x x x x y z
theorem Equation3455_implies_Equation3257 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3257 G := λ x y z => h x x x x y z
theorem Equation3658_implies_Equation3460 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3460 G := λ x y z => h x x x x y z
theorem Equation3861_implies_Equation3663 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3663 G := λ x y z => h x x x x y z
theorem Equation4064_implies_Equation3866 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3866 G := λ x y z => h x x x x y z
theorem Equation4267_implies_Equation4069 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4069 G := λ x y z => h x x x x y z
theorem Equation4379_implies_Equation4271 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4271 G := λ x y z => h x x x x y z
theorem Equation4582_implies_Equation4384 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4384 G := λ x y z => h x x x x y z
theorem Equation4694_implies_Equation4586 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4586 G := λ x y z => h x x x x y z