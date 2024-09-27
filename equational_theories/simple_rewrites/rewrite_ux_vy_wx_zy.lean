import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation501 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (x ∘ (x ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation704 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ ((x ∘ x) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation907 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ x) ∘ (x ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1110 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ (x ∘ x)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1313 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((y ∘ x) ∘ x) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1516 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (x ∘ (x ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1719 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ ((x ∘ x) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1922 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ x)) ∘ (x ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2125 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ x) ∘ (x ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2328 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ (x ∘ x))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2531 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((y ∘ x) ∘ x)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2734 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ (x ∘ x)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2937 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (y ∘ x)) ∘ x) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3140 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ y) ∘ x) ∘ x) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3343 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (x ∘ (x ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3546 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ ((x ∘ x) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3749 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ x) ∘ (x ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3952 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ (x ∘ x)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4155 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((y ∘ x) ∘ x) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4470 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = (x ∘ x) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation501 (G : Type*) [Magma G] (h : Equation613 G) : Equation501 G := λ x y => h x y y x x y
theorem Equation816_implies_Equation704 (G : Type*) [Magma G] (h : Equation816 G) : Equation704 G := λ x y => h x y y x x y
theorem Equation1019_implies_Equation907 (G : Type*) [Magma G] (h : Equation1019 G) : Equation907 G := λ x y => h x y y x x y
theorem Equation1222_implies_Equation1110 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1110 G := λ x y => h x y y x x y
theorem Equation1425_implies_Equation1313 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1313 G := λ x y => h x y y x x y
theorem Equation1628_implies_Equation1516 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1516 G := λ x y => h x y y x x y
theorem Equation1831_implies_Equation1719 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1719 G := λ x y => h x y y x x y
theorem Equation2034_implies_Equation1922 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1922 G := λ x y => h x y y x x y
theorem Equation2237_implies_Equation2125 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2125 G := λ x y => h x y y x x y
theorem Equation2440_implies_Equation2328 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2328 G := λ x y => h x y y x x y
theorem Equation2643_implies_Equation2531 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2531 G := λ x y => h x y y x x y
theorem Equation2846_implies_Equation2734 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2734 G := λ x y => h x y y x x y
theorem Equation3049_implies_Equation2937 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2937 G := λ x y => h x y y x x y
theorem Equation3252_implies_Equation3140 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3140 G := λ x y => h x y y x x y
theorem Equation3455_implies_Equation3343 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3343 G := λ x y => h x y y x x y
theorem Equation3658_implies_Equation3546 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3546 G := λ x y => h x y y x x y
theorem Equation3861_implies_Equation3749 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3749 G := λ x y => h x y y x x y
theorem Equation4064_implies_Equation3952 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3952 G := λ x y => h x y y x x y
theorem Equation4267_implies_Equation4155 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4155 G := λ x y => h x y y x x y
theorem Equation4582_implies_Equation4470 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4470 G := λ x y => h x y y x x y