import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation445 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (y ∘ (z ∘ w)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation648 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((y ∘ z) ∘ w))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation851 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ y) ∘ (z ∘ w))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1054 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (y ∘ z)) ∘ w)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1257 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ y) ∘ z) ∘ w)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1460 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (y ∘ (z ∘ w))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1663 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((y ∘ z) ∘ w)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1866 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ y)) ∘ (z ∘ w)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2069 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ y) ∘ (z ∘ w)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2272 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (y ∘ z))) ∘ w
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2475 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ y) ∘ z)) ∘ w
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2678 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (y ∘ z)) ∘ w
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2881 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ y)) ∘ z) ∘ w
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3084 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ y) ∘ z) ∘ w
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3287 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (y ∘ (z ∘ w))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3490 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((y ∘ z) ∘ w)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3693 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ y) ∘ (z ∘ w)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3896 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (y ∘ z)) ∘ w
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4099 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ y) ∘ z) ∘ w
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4298 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = y ∘ (z ∘ w)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4414 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (y ∘ z) ∘ w
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4613 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (y ∘ z) ∘ w
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation445 (G : Type*) [Magma G] (h : Equation613 G) : Equation445 G := λ x y z w => h x x y y z w
theorem Equation816_implies_Equation648 (G : Type*) [Magma G] (h : Equation816 G) : Equation648 G := λ x y z w => h x x y y z w
theorem Equation1019_implies_Equation851 (G : Type*) [Magma G] (h : Equation1019 G) : Equation851 G := λ x y z w => h x x y y z w
theorem Equation1222_implies_Equation1054 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1054 G := λ x y z w => h x x y y z w
theorem Equation1425_implies_Equation1257 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1257 G := λ x y z w => h x x y y z w
theorem Equation1628_implies_Equation1460 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1460 G := λ x y z w => h x x y y z w
theorem Equation1831_implies_Equation1663 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1663 G := λ x y z w => h x x y y z w
theorem Equation2034_implies_Equation1866 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1866 G := λ x y z w => h x x y y z w
theorem Equation2237_implies_Equation2069 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2069 G := λ x y z w => h x x y y z w
theorem Equation2440_implies_Equation2272 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2272 G := λ x y z w => h x x y y z w
theorem Equation2643_implies_Equation2475 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2475 G := λ x y z w => h x x y y z w
theorem Equation2846_implies_Equation2678 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2678 G := λ x y z w => h x x y y z w
theorem Equation3049_implies_Equation2881 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2881 G := λ x y z w => h x x y y z w
theorem Equation3252_implies_Equation3084 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3084 G := λ x y z w => h x x y y z w
theorem Equation3455_implies_Equation3287 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3287 G := λ x y z w => h x x y y z w
theorem Equation3658_implies_Equation3490 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3490 G := λ x y z w => h x x y y z w
theorem Equation3861_implies_Equation3693 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3693 G := λ x y z w => h x x y y z w
theorem Equation4064_implies_Equation3896 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3896 G := λ x y z w => h x x y y z w
theorem Equation4267_implies_Equation4099 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4099 G := λ x y z w => h x x y y z w
theorem Equation4379_implies_Equation4298 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4298 G := λ x y z w => h x x y y z w
theorem Equation4582_implies_Equation4414 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4414 G := λ x y z w => h x x y y z w
theorem Equation4694_implies_Equation4613 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4613 G := λ x y z w => h x x y y z w