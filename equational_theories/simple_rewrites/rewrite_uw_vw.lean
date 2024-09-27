import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation606 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (w ∘ w)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation809 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ w) ∘ w))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation1012 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (w ∘ w))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1215 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ w)) ∘ w)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1418 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ w) ∘ w)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1621 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (w ∘ w))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1824 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ w) ∘ w)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation2027 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (w ∘ w)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2230 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (w ∘ w)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2433 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ w))) ∘ w
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2636 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ w)) ∘ w
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2839 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ w)) ∘ w
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3042 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ w) ∘ w
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3245 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ w) ∘ w
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3448 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (w ∘ w))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3651 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ w) ∘ w)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3854 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (w ∘ w)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4057 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ w)) ∘ w
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4260 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ w) ∘ w
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4575 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ w) ∘ w
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation606 (G : Type*) [Magma G] (h : Equation613 G) : Equation606 G := λ x y z w => h x y z w w w
theorem Equation816_implies_Equation809 (G : Type*) [Magma G] (h : Equation816 G) : Equation809 G := λ x y z w => h x y z w w w
theorem Equation1019_implies_Equation1012 (G : Type*) [Magma G] (h : Equation1019 G) : Equation1012 G := λ x y z w => h x y z w w w
theorem Equation1222_implies_Equation1215 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1215 G := λ x y z w => h x y z w w w
theorem Equation1425_implies_Equation1418 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1418 G := λ x y z w => h x y z w w w
theorem Equation1628_implies_Equation1621 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1621 G := λ x y z w => h x y z w w w
theorem Equation1831_implies_Equation1824 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1824 G := λ x y z w => h x y z w w w
theorem Equation2034_implies_Equation2027 (G : Type*) [Magma G] (h : Equation2034 G) : Equation2027 G := λ x y z w => h x y z w w w
theorem Equation2237_implies_Equation2230 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2230 G := λ x y z w => h x y z w w w
theorem Equation2440_implies_Equation2433 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2433 G := λ x y z w => h x y z w w w
theorem Equation2643_implies_Equation2636 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2636 G := λ x y z w => h x y z w w w
theorem Equation2846_implies_Equation2839 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2839 G := λ x y z w => h x y z w w w
theorem Equation3049_implies_Equation3042 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3042 G := λ x y z w => h x y z w w w
theorem Equation3252_implies_Equation3245 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3245 G := λ x y z w => h x y z w w w
theorem Equation3455_implies_Equation3448 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3448 G := λ x y z w => h x y z w w w
theorem Equation3658_implies_Equation3651 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3651 G := λ x y z w => h x y z w w w
theorem Equation3861_implies_Equation3854 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3854 G := λ x y z w => h x y z w w w
theorem Equation4064_implies_Equation4057 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4057 G := λ x y z w => h x y z w w w
theorem Equation4267_implies_Equation4260 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4260 G := λ x y z w => h x y z w w w
theorem Equation4582_implies_Equation4575 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4575 G := λ x y z w => h x y z w w w