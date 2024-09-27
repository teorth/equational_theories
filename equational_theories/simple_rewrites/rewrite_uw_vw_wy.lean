import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation569 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (w ∘ w)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation772 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ w) ∘ w))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation975 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (w ∘ w))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1178 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ w)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1381 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ w) ∘ w)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1584 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (w ∘ w))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1787 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ w)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1990 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ w)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2193 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ w)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2396 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ w
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2599 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ w
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2802 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ w
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3005 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ w
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3208 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ w
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3411 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (w ∘ w))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3614 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ w) ∘ w)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3817 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (w ∘ w)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4020 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ w)) ∘ w
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4223 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ w) ∘ w
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4538 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ w) ∘ w
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation569 (G : Type*) [Magma G] (h : Equation613 G) : Equation569 G := λ x y z w => h x y z y w w
theorem Equation816_implies_Equation772 (G : Type*) [Magma G] (h : Equation816 G) : Equation772 G := λ x y z w => h x y z y w w
theorem Equation1019_implies_Equation975 (G : Type*) [Magma G] (h : Equation1019 G) : Equation975 G := λ x y z w => h x y z y w w
theorem Equation1222_implies_Equation1178 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1178 G := λ x y z w => h x y z y w w
theorem Equation1425_implies_Equation1381 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1381 G := λ x y z w => h x y z y w w
theorem Equation1628_implies_Equation1584 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1584 G := λ x y z w => h x y z y w w
theorem Equation1831_implies_Equation1787 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1787 G := λ x y z w => h x y z y w w
theorem Equation2034_implies_Equation1990 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1990 G := λ x y z w => h x y z y w w
theorem Equation2237_implies_Equation2193 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2193 G := λ x y z w => h x y z y w w
theorem Equation2440_implies_Equation2396 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2396 G := λ x y z w => h x y z y w w
theorem Equation2643_implies_Equation2599 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2599 G := λ x y z w => h x y z y w w
theorem Equation2846_implies_Equation2802 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2802 G := λ x y z w => h x y z y w w
theorem Equation3049_implies_Equation3005 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3005 G := λ x y z w => h x y z y w w
theorem Equation3252_implies_Equation3208 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3208 G := λ x y z w => h x y z y w w
theorem Equation3455_implies_Equation3411 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3411 G := λ x y z w => h x y z y w w
theorem Equation3658_implies_Equation3614 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3614 G := λ x y z w => h x y z y w w
theorem Equation3861_implies_Equation3817 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3817 G := λ x y z w => h x y z y w w
theorem Equation4064_implies_Equation4020 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4020 G := λ x y z w => h x y z y w w
theorem Equation4267_implies_Equation4223 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4223 G := λ x y z w => h x y z y w w
theorem Equation4582_implies_Equation4538 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4538 G := λ x y z w => h x y z y w w