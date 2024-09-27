import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation572 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (x ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation775 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ x) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation978 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (x ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1181 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ x)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1384 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ x) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1587 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (x ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1790 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ x) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1993 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (x ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2196 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (x ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2399 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ x))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2602 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ x)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2805 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ x)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3008 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ x) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3211 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ x) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3414 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (x ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3617 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ x) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3820 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (x ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4023 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ x)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4226 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ x) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4541 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ x) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation572 (G : Type*) [Magma G] (h : Equation613 G) : Equation572 G := λ x y z => h x y z z x y
theorem Equation816_implies_Equation775 (G : Type*) [Magma G] (h : Equation816 G) : Equation775 G := λ x y z => h x y z z x y
theorem Equation1019_implies_Equation978 (G : Type*) [Magma G] (h : Equation1019 G) : Equation978 G := λ x y z => h x y z z x y
theorem Equation1222_implies_Equation1181 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1181 G := λ x y z => h x y z z x y
theorem Equation1425_implies_Equation1384 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1384 G := λ x y z => h x y z z x y
theorem Equation1628_implies_Equation1587 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1587 G := λ x y z => h x y z z x y
theorem Equation1831_implies_Equation1790 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1790 G := λ x y z => h x y z z x y
theorem Equation2034_implies_Equation1993 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1993 G := λ x y z => h x y z z x y
theorem Equation2237_implies_Equation2196 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2196 G := λ x y z => h x y z z x y
theorem Equation2440_implies_Equation2399 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2399 G := λ x y z => h x y z z x y
theorem Equation2643_implies_Equation2602 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2602 G := λ x y z => h x y z z x y
theorem Equation2846_implies_Equation2805 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2805 G := λ x y z => h x y z z x y
theorem Equation3049_implies_Equation3008 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3008 G := λ x y z => h x y z z x y
theorem Equation3252_implies_Equation3211 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3211 G := λ x y z => h x y z z x y
theorem Equation3455_implies_Equation3414 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3414 G := λ x y z => h x y z z x y
theorem Equation3658_implies_Equation3617 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3617 G := λ x y z => h x y z z x y
theorem Equation3861_implies_Equation3820 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3820 G := λ x y z => h x y z z x y
theorem Equation4064_implies_Equation4023 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4023 G := λ x y z => h x y z z x y
theorem Equation4267_implies_Equation4226 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4226 G := λ x y z => h x y z z x y
theorem Equation4582_implies_Equation4541 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4541 G := λ x y z => h x y z z x y