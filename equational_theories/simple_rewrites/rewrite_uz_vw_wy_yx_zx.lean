import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation425 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (x ∘ (y ∘ (z ∘ w)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation628 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (x ∘ ((y ∘ z) ∘ w))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation831 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((x ∘ y) ∘ (z ∘ w))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1034 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((x ∘ (y ∘ z)) ∘ w)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1237 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((x ∘ y) ∘ z) ∘ w)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1440 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ x) ∘ (y ∘ (z ∘ w))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1643 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ x) ∘ ((y ∘ z) ∘ w)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1846 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (x ∘ y)) ∘ (z ∘ w)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2049 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ x) ∘ y) ∘ (z ∘ w)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2252 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (x ∘ (y ∘ z))) ∘ w
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2455 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((x ∘ y) ∘ z)) ∘ w
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2658 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ x) ∘ (y ∘ z)) ∘ w
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2861 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (x ∘ y)) ∘ z) ∘ w
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3064 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ x) ∘ y) ∘ z) ∘ w
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3267 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = x ∘ (y ∘ (z ∘ w))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3470 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = x ∘ ((y ∘ z) ∘ w)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3673 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (x ∘ y) ∘ (z ∘ w)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3876 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (x ∘ (y ∘ z)) ∘ w
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4079 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((x ∘ y) ∘ z) ∘ w
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4281 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ x) = y ∘ (z ∘ w)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4394 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ x) = (y ∘ z) ∘ w
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4596 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ x = (y ∘ z) ∘ w
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation425 (G : Type*) [Magma G] (h : Equation613 G) : Equation425 G := λ x y z w => h x x x y z w
theorem Equation816_implies_Equation628 (G : Type*) [Magma G] (h : Equation816 G) : Equation628 G := λ x y z w => h x x x y z w
theorem Equation1019_implies_Equation831 (G : Type*) [Magma G] (h : Equation1019 G) : Equation831 G := λ x y z w => h x x x y z w
theorem Equation1222_implies_Equation1034 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1034 G := λ x y z w => h x x x y z w
theorem Equation1425_implies_Equation1237 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1237 G := λ x y z w => h x x x y z w
theorem Equation1628_implies_Equation1440 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1440 G := λ x y z w => h x x x y z w
theorem Equation1831_implies_Equation1643 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1643 G := λ x y z w => h x x x y z w
theorem Equation2034_implies_Equation1846 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1846 G := λ x y z w => h x x x y z w
theorem Equation2237_implies_Equation2049 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2049 G := λ x y z w => h x x x y z w
theorem Equation2440_implies_Equation2252 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2252 G := λ x y z w => h x x x y z w
theorem Equation2643_implies_Equation2455 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2455 G := λ x y z w => h x x x y z w
theorem Equation2846_implies_Equation2658 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2658 G := λ x y z w => h x x x y z w
theorem Equation3049_implies_Equation2861 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2861 G := λ x y z w => h x x x y z w
theorem Equation3252_implies_Equation3064 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3064 G := λ x y z w => h x x x y z w
theorem Equation3455_implies_Equation3267 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3267 G := λ x y z w => h x x x y z w
theorem Equation3658_implies_Equation3470 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3470 G := λ x y z w => h x x x y z w
theorem Equation3861_implies_Equation3673 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3673 G := λ x y z w => h x x x y z w
theorem Equation4064_implies_Equation3876 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3876 G := λ x y z w => h x x x y z w
theorem Equation4267_implies_Equation4079 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4079 G := λ x y z w => h x x x y z w
theorem Equation4379_implies_Equation4281 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4281 G := λ x y z w => h x x x y z w
theorem Equation4582_implies_Equation4394 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4394 G := λ x y z w => h x x x y z w
theorem Equation4694_implies_Equation4596 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4596 G := λ x y z w => h x x x y z w