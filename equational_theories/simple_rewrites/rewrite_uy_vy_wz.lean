import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation576 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (y ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation779 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ y) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation982 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (y ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1185 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ y)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1388 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ y) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1591 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (y ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1794 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ y) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1997 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (y ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2200 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (y ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2403 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ y))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2606 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ y)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2809 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ y)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3012 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ y) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3215 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ y) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3418 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (y ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3621 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ y) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3824 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (y ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4027 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ y)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4230 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ y) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4545 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ y) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation576 (G : Type*) [Magma G] (h : Equation613 G) : Equation576 G := λ x y z => h x y z z y y
theorem Equation816_implies_Equation779 (G : Type*) [Magma G] (h : Equation816 G) : Equation779 G := λ x y z => h x y z z y y
theorem Equation1019_implies_Equation982 (G : Type*) [Magma G] (h : Equation1019 G) : Equation982 G := λ x y z => h x y z z y y
theorem Equation1222_implies_Equation1185 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1185 G := λ x y z => h x y z z y y
theorem Equation1425_implies_Equation1388 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1388 G := λ x y z => h x y z z y y
theorem Equation1628_implies_Equation1591 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1591 G := λ x y z => h x y z z y y
theorem Equation1831_implies_Equation1794 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1794 G := λ x y z => h x y z z y y
theorem Equation2034_implies_Equation1997 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1997 G := λ x y z => h x y z z y y
theorem Equation2237_implies_Equation2200 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2200 G := λ x y z => h x y z z y y
theorem Equation2440_implies_Equation2403 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2403 G := λ x y z => h x y z z y y
theorem Equation2643_implies_Equation2606 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2606 G := λ x y z => h x y z z y y
theorem Equation2846_implies_Equation2809 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2809 G := λ x y z => h x y z z y y
theorem Equation3049_implies_Equation3012 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3012 G := λ x y z => h x y z z y y
theorem Equation3252_implies_Equation3215 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3215 G := λ x y z => h x y z z y y
theorem Equation3455_implies_Equation3418 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3418 G := λ x y z => h x y z z y y
theorem Equation3658_implies_Equation3621 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3621 G := λ x y z => h x y z z y y
theorem Equation3861_implies_Equation3824 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3824 G := λ x y z => h x y z z y y
theorem Equation4064_implies_Equation4027 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4027 G := λ x y z => h x y z z y y
theorem Equation4267_implies_Equation4230 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4230 G := λ x y z => h x y z z y y
theorem Equation4582_implies_Equation4545 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4545 G := λ x y z => h x y z z y y