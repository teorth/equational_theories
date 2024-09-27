import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation540 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (x ∘ w)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation743 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ x) ∘ w))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation946 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (x ∘ w))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1149 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ x)) ∘ w)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1352 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ x) ∘ w)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1555 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (x ∘ w))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1758 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ x) ∘ w)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1961 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (x ∘ w)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2164 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (x ∘ w)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2367 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ x))) ∘ w
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2570 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ x)) ∘ w
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2773 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ x)) ∘ w
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2976 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ x) ∘ w
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3179 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ x) ∘ w
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3382 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (x ∘ w))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3585 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ x) ∘ w)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3788 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (x ∘ w)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3991 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ x)) ∘ w
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4194 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ x) ∘ w
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4509 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ x) ∘ w
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation540 (G : Type*) [Magma G] (h : Equation613 G) : Equation540 G := λ x y z w => h x y z x x w
theorem Equation816_implies_Equation743 (G : Type*) [Magma G] (h : Equation816 G) : Equation743 G := λ x y z w => h x y z x x w
theorem Equation1019_implies_Equation946 (G : Type*) [Magma G] (h : Equation1019 G) : Equation946 G := λ x y z w => h x y z x x w
theorem Equation1222_implies_Equation1149 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1149 G := λ x y z w => h x y z x x w
theorem Equation1425_implies_Equation1352 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1352 G := λ x y z w => h x y z x x w
theorem Equation1628_implies_Equation1555 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1555 G := λ x y z w => h x y z x x w
theorem Equation1831_implies_Equation1758 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1758 G := λ x y z w => h x y z x x w
theorem Equation2034_implies_Equation1961 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1961 G := λ x y z w => h x y z x x w
theorem Equation2237_implies_Equation2164 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2164 G := λ x y z w => h x y z x x w
theorem Equation2440_implies_Equation2367 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2367 G := λ x y z w => h x y z x x w
theorem Equation2643_implies_Equation2570 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2570 G := λ x y z w => h x y z x x w
theorem Equation2846_implies_Equation2773 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2773 G := λ x y z w => h x y z x x w
theorem Equation3049_implies_Equation2976 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2976 G := λ x y z w => h x y z x x w
theorem Equation3252_implies_Equation3179 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3179 G := λ x y z w => h x y z x x w
theorem Equation3455_implies_Equation3382 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3382 G := λ x y z w => h x y z x x w
theorem Equation3658_implies_Equation3585 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3585 G := λ x y z w => h x y z x x w
theorem Equation3861_implies_Equation3788 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3788 G := λ x y z w => h x y z x x w
theorem Equation4064_implies_Equation3991 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3991 G := λ x y z w => h x y z x x w
theorem Equation4267_implies_Equation4194 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4194 G := λ x y z w => h x y z x x w
theorem Equation4582_implies_Equation4509 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4509 G := λ x y z w => h x y z x x w