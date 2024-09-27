import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation543 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ (y ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation746 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((x ∘ y) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation949 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ (y ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1152 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (x ∘ y)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1355 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ x) ∘ y) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1558 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ (y ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1761 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((x ∘ y) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1964 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ (y ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2167 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ (y ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2370 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (x ∘ y))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2573 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ x) ∘ y)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2776 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (x ∘ y)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2979 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ x)) ∘ y) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3182 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ x) ∘ y) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3385 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ (y ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3588 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((x ∘ y) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3791 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ (y ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3994 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (x ∘ y)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4197 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ x) ∘ y) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4512 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ y) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation543 (G : Type*) [Magma G] (h : Equation613 G) : Equation543 G := λ x y z => h x y z x y z
theorem Equation816_implies_Equation746 (G : Type*) [Magma G] (h : Equation816 G) : Equation746 G := λ x y z => h x y z x y z
theorem Equation1019_implies_Equation949 (G : Type*) [Magma G] (h : Equation1019 G) : Equation949 G := λ x y z => h x y z x y z
theorem Equation1222_implies_Equation1152 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1152 G := λ x y z => h x y z x y z
theorem Equation1425_implies_Equation1355 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1355 G := λ x y z => h x y z x y z
theorem Equation1628_implies_Equation1558 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1558 G := λ x y z => h x y z x y z
theorem Equation1831_implies_Equation1761 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1761 G := λ x y z => h x y z x y z
theorem Equation2034_implies_Equation1964 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1964 G := λ x y z => h x y z x y z
theorem Equation2237_implies_Equation2167 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2167 G := λ x y z => h x y z x y z
theorem Equation2440_implies_Equation2370 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2370 G := λ x y z => h x y z x y z
theorem Equation2643_implies_Equation2573 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2573 G := λ x y z => h x y z x y z
theorem Equation2846_implies_Equation2776 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2776 G := λ x y z => h x y z x y z
theorem Equation3049_implies_Equation2979 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2979 G := λ x y z => h x y z x y z
theorem Equation3252_implies_Equation3182 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3182 G := λ x y z => h x y z x y z
theorem Equation3455_implies_Equation3385 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3385 G := λ x y z => h x y z x y z
theorem Equation3658_implies_Equation3588 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3588 G := λ x y z => h x y z x y z
theorem Equation3861_implies_Equation3791 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3791 G := λ x y z => h x y z x y z
theorem Equation4064_implies_Equation3994 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3994 G := λ x y z => h x y z x y z
theorem Equation4267_implies_Equation4197 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4197 G := λ x y z => h x y z x y z
theorem Equation4582_implies_Equation4512 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4512 G := λ x y z => h x y z x y z