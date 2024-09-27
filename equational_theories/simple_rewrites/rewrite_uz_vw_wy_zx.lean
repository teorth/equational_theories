import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation482 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (y ∘ (z ∘ w)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation685 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((y ∘ z) ∘ w))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation888 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ y) ∘ (z ∘ w))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1091 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (y ∘ z)) ∘ w)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1294 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ y) ∘ z) ∘ w)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1497 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (y ∘ (z ∘ w))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1700 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((y ∘ z) ∘ w)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1903 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ y)) ∘ (z ∘ w)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2106 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ y) ∘ (z ∘ w)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2309 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (y ∘ z))) ∘ w
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2512 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ y) ∘ z)) ∘ w
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2715 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (y ∘ z)) ∘ w
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2918 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ y)) ∘ z) ∘ w
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3121 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ y) ∘ z) ∘ w
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3324 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (y ∘ (z ∘ w))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3527 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((y ∘ z) ∘ w)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3730 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ y) ∘ (z ∘ w)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3933 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (y ∘ z)) ∘ w
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4136 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ y) ∘ z) ∘ w
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4326 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = y ∘ (z ∘ w)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4451 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (y ∘ z) ∘ w
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4641 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ x = (y ∘ z) ∘ w
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation482 (G : Type*) [Magma G] (h : Equation613 G) : Equation482 G := λ x y z w => h x y x y z w
theorem Equation816_implies_Equation685 (G : Type*) [Magma G] (h : Equation816 G) : Equation685 G := λ x y z w => h x y x y z w
theorem Equation1019_implies_Equation888 (G : Type*) [Magma G] (h : Equation1019 G) : Equation888 G := λ x y z w => h x y x y z w
theorem Equation1222_implies_Equation1091 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1091 G := λ x y z w => h x y x y z w
theorem Equation1425_implies_Equation1294 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1294 G := λ x y z w => h x y x y z w
theorem Equation1628_implies_Equation1497 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1497 G := λ x y z w => h x y x y z w
theorem Equation1831_implies_Equation1700 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1700 G := λ x y z w => h x y x y z w
theorem Equation2034_implies_Equation1903 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1903 G := λ x y z w => h x y x y z w
theorem Equation2237_implies_Equation2106 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2106 G := λ x y z w => h x y x y z w
theorem Equation2440_implies_Equation2309 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2309 G := λ x y z w => h x y x y z w
theorem Equation2643_implies_Equation2512 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2512 G := λ x y z w => h x y x y z w
theorem Equation2846_implies_Equation2715 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2715 G := λ x y z w => h x y x y z w
theorem Equation3049_implies_Equation2918 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2918 G := λ x y z w => h x y x y z w
theorem Equation3252_implies_Equation3121 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3121 G := λ x y z w => h x y x y z w
theorem Equation3455_implies_Equation3324 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3324 G := λ x y z w => h x y x y z w
theorem Equation3658_implies_Equation3527 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3527 G := λ x y z w => h x y x y z w
theorem Equation3861_implies_Equation3730 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3730 G := λ x y z w => h x y x y z w
theorem Equation4064_implies_Equation3933 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3933 G := λ x y z w => h x y x y z w
theorem Equation4267_implies_Equation4136 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4136 G := λ x y z w => h x y x y z w
theorem Equation4379_implies_Equation4326 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4326 G := λ x y z w => h x y x y z w
theorem Equation4582_implies_Equation4451 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4451 G := λ x y z w => h x y x y z w
theorem Equation4694_implies_Equation4641 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4641 G := λ x y z w => h x y x y z w