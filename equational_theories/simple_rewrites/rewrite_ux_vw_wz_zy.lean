import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation523 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (x ∘ w)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation726 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ x) ∘ w))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation929 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (x ∘ w))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1132 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ x)) ∘ w)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1335 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ x) ∘ w)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1538 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (x ∘ w))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1741 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ x) ∘ w)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1944 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (x ∘ w)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2147 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (x ∘ w)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2350 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ x))) ∘ w
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2553 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ x)) ∘ w
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2756 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ x)) ∘ w
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2959 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ x) ∘ w
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3162 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ x) ∘ w
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3365 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (x ∘ w))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3568 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ x) ∘ w)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3771 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (x ∘ w)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3974 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ x)) ∘ w
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4177 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ x) ∘ w
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4349 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = z ∘ (x ∘ w)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4492 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ x) ∘ w
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4664 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ y = (z ∘ x) ∘ w
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation523 (G : Type*) [Magma G] (h : Equation613 G) : Equation523 G := λ x y z w => h x y y z x w
theorem Equation816_implies_Equation726 (G : Type*) [Magma G] (h : Equation816 G) : Equation726 G := λ x y z w => h x y y z x w
theorem Equation1019_implies_Equation929 (G : Type*) [Magma G] (h : Equation1019 G) : Equation929 G := λ x y z w => h x y y z x w
theorem Equation1222_implies_Equation1132 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1132 G := λ x y z w => h x y y z x w
theorem Equation1425_implies_Equation1335 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1335 G := λ x y z w => h x y y z x w
theorem Equation1628_implies_Equation1538 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1538 G := λ x y z w => h x y y z x w
theorem Equation1831_implies_Equation1741 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1741 G := λ x y z w => h x y y z x w
theorem Equation2034_implies_Equation1944 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1944 G := λ x y z w => h x y y z x w
theorem Equation2237_implies_Equation2147 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2147 G := λ x y z w => h x y y z x w
theorem Equation2440_implies_Equation2350 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2350 G := λ x y z w => h x y y z x w
theorem Equation2643_implies_Equation2553 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2553 G := λ x y z w => h x y y z x w
theorem Equation2846_implies_Equation2756 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2756 G := λ x y z w => h x y y z x w
theorem Equation3049_implies_Equation2959 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2959 G := λ x y z w => h x y y z x w
theorem Equation3252_implies_Equation3162 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3162 G := λ x y z w => h x y y z x w
theorem Equation3455_implies_Equation3365 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3365 G := λ x y z w => h x y y z x w
theorem Equation3658_implies_Equation3568 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3568 G := λ x y z w => h x y y z x w
theorem Equation3861_implies_Equation3771 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3771 G := λ x y z w => h x y y z x w
theorem Equation4064_implies_Equation3974 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3974 G := λ x y z w => h x y y z x w
theorem Equation4267_implies_Equation4177 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4177 G := λ x y z w => h x y y z x w
theorem Equation4379_implies_Equation4349 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4349 G := λ x y z w => h x y y z x w
theorem Equation4582_implies_Equation4492 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4492 G := λ x y z w => h x y y z x w
theorem Equation4694_implies_Equation4664 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4664 G := λ x y z w => h x y y z x w