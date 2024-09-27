import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation498 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (w ∘ w)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation701 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ w) ∘ w))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation904 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (w ∘ w))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1107 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ w)) ∘ w)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1310 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ w) ∘ w)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1513 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (w ∘ w))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1716 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ w) ∘ w)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1919 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (w ∘ w)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2122 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (w ∘ w)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2325 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ w))) ∘ w
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2528 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ w)) ∘ w
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2731 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ w)) ∘ w
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2934 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ w) ∘ w
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3137 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ w) ∘ w
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3340 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (w ∘ w))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3543 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ w) ∘ w)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3746 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (w ∘ w)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3949 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ w)) ∘ w
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4152 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ w) ∘ w
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4337 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = z ∘ (w ∘ w)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4467 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ w) ∘ w
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4652 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ x = (z ∘ w) ∘ w
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation498 (G : Type*) [Magma G] (h : Equation613 G) : Equation498 G := λ x y z w => h x y x z w w
theorem Equation816_implies_Equation701 (G : Type*) [Magma G] (h : Equation816 G) : Equation701 G := λ x y z w => h x y x z w w
theorem Equation1019_implies_Equation904 (G : Type*) [Magma G] (h : Equation1019 G) : Equation904 G := λ x y z w => h x y x z w w
theorem Equation1222_implies_Equation1107 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1107 G := λ x y z w => h x y x z w w
theorem Equation1425_implies_Equation1310 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1310 G := λ x y z w => h x y x z w w
theorem Equation1628_implies_Equation1513 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1513 G := λ x y z w => h x y x z w w
theorem Equation1831_implies_Equation1716 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1716 G := λ x y z w => h x y x z w w
theorem Equation2034_implies_Equation1919 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1919 G := λ x y z w => h x y x z w w
theorem Equation2237_implies_Equation2122 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2122 G := λ x y z w => h x y x z w w
theorem Equation2440_implies_Equation2325 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2325 G := λ x y z w => h x y x z w w
theorem Equation2643_implies_Equation2528 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2528 G := λ x y z w => h x y x z w w
theorem Equation2846_implies_Equation2731 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2731 G := λ x y z w => h x y x z w w
theorem Equation3049_implies_Equation2934 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2934 G := λ x y z w => h x y x z w w
theorem Equation3252_implies_Equation3137 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3137 G := λ x y z w => h x y x z w w
theorem Equation3455_implies_Equation3340 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3340 G := λ x y z w => h x y x z w w
theorem Equation3658_implies_Equation3543 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3543 G := λ x y z w => h x y x z w w
theorem Equation3861_implies_Equation3746 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3746 G := λ x y z w => h x y x z w w
theorem Equation4064_implies_Equation3949 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3949 G := λ x y z w => h x y x z w w
theorem Equation4267_implies_Equation4152 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4152 G := λ x y z w => h x y x z w w
theorem Equation4379_implies_Equation4337 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4337 G := λ x y z w => h x y x z w w
theorem Equation4582_implies_Equation4467 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4467 G := λ x y z w => h x y x z w w
theorem Equation4694_implies_Equation4652 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4652 G := λ x y z w => h x y x z w w