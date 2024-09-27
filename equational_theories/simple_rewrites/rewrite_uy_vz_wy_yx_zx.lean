import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation421 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ (y ∘ (y ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation624 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ ((y ∘ y) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation827 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ y) ∘ (y ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1030 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ (y ∘ y)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1233 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((x ∘ y) ∘ y) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1436 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ (y ∘ (y ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1639 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ ((y ∘ y) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1842 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ y)) ∘ (y ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2045 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ y) ∘ (y ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2248 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ (y ∘ y))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2451 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((x ∘ y) ∘ y)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2654 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ (y ∘ y)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2857 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (x ∘ y)) ∘ y) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3060 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ x) ∘ y) ∘ y) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3263 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ (y ∘ (y ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3466 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ ((y ∘ y) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3669 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ y) ∘ (y ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3872 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ (y ∘ y)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4075 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((x ∘ y) ∘ y) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4277 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ x) = y ∘ (y ∘ z)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4390 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ x) = (y ∘ y) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4592 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ x = (y ∘ y) ∘ z
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation421 (G : Type*) [Magma G] (h : Equation613 G) : Equation421 G := λ x y z => h x x x y y z
theorem Equation816_implies_Equation624 (G : Type*) [Magma G] (h : Equation816 G) : Equation624 G := λ x y z => h x x x y y z
theorem Equation1019_implies_Equation827 (G : Type*) [Magma G] (h : Equation1019 G) : Equation827 G := λ x y z => h x x x y y z
theorem Equation1222_implies_Equation1030 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1030 G := λ x y z => h x x x y y z
theorem Equation1425_implies_Equation1233 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1233 G := λ x y z => h x x x y y z
theorem Equation1628_implies_Equation1436 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1436 G := λ x y z => h x x x y y z
theorem Equation1831_implies_Equation1639 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1639 G := λ x y z => h x x x y y z
theorem Equation2034_implies_Equation1842 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1842 G := λ x y z => h x x x y y z
theorem Equation2237_implies_Equation2045 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2045 G := λ x y z => h x x x y y z
theorem Equation2440_implies_Equation2248 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2248 G := λ x y z => h x x x y y z
theorem Equation2643_implies_Equation2451 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2451 G := λ x y z => h x x x y y z
theorem Equation2846_implies_Equation2654 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2654 G := λ x y z => h x x x y y z
theorem Equation3049_implies_Equation2857 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2857 G := λ x y z => h x x x y y z
theorem Equation3252_implies_Equation3060 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3060 G := λ x y z => h x x x y y z
theorem Equation3455_implies_Equation3263 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3263 G := λ x y z => h x x x y y z
theorem Equation3658_implies_Equation3466 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3466 G := λ x y z => h x x x y y z
theorem Equation3861_implies_Equation3669 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3669 G := λ x y z => h x x x y y z
theorem Equation4064_implies_Equation3872 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3872 G := λ x y z => h x x x y y z
theorem Equation4267_implies_Equation4075 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4075 G := λ x y z => h x x x y y z
theorem Equation4379_implies_Equation4277 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4277 G := λ x y z => h x x x y y z
theorem Equation4582_implies_Equation4390 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4390 G := λ x y z => h x x x y y z
theorem Equation4694_implies_Equation4592 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4592 G := λ x y z => h x x x y y z