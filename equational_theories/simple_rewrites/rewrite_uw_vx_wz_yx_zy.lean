import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation458 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (w ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation661 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ w) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation864 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (w ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1067 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1270 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ w) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1473 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (w ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1676 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1879 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2082 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2285 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2488 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2691 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2894 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3097 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3300 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (w ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3503 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ w) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3706 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (w ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3909 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ w)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4112 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ w) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4309 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (w ∘ x)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4427 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ w) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4624 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ w) ∘ x
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation458 (G : Type*) [Magma G] (h : Equation613 G) : Equation458 G := λ x y z w => h x x y z w x
theorem Equation816_implies_Equation661 (G : Type*) [Magma G] (h : Equation816 G) : Equation661 G := λ x y z w => h x x y z w x
theorem Equation1019_implies_Equation864 (G : Type*) [Magma G] (h : Equation1019 G) : Equation864 G := λ x y z w => h x x y z w x
theorem Equation1222_implies_Equation1067 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1067 G := λ x y z w => h x x y z w x
theorem Equation1425_implies_Equation1270 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1270 G := λ x y z w => h x x y z w x
theorem Equation1628_implies_Equation1473 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1473 G := λ x y z w => h x x y z w x
theorem Equation1831_implies_Equation1676 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1676 G := λ x y z w => h x x y z w x
theorem Equation2034_implies_Equation1879 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1879 G := λ x y z w => h x x y z w x
theorem Equation2237_implies_Equation2082 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2082 G := λ x y z w => h x x y z w x
theorem Equation2440_implies_Equation2285 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2285 G := λ x y z w => h x x y z w x
theorem Equation2643_implies_Equation2488 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2488 G := λ x y z w => h x x y z w x
theorem Equation2846_implies_Equation2691 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2691 G := λ x y z w => h x x y z w x
theorem Equation3049_implies_Equation2894 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2894 G := λ x y z w => h x x y z w x
theorem Equation3252_implies_Equation3097 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3097 G := λ x y z w => h x x y z w x
theorem Equation3455_implies_Equation3300 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3300 G := λ x y z w => h x x y z w x
theorem Equation3658_implies_Equation3503 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3503 G := λ x y z w => h x x y z w x
theorem Equation3861_implies_Equation3706 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3706 G := λ x y z w => h x x y z w x
theorem Equation4064_implies_Equation3909 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3909 G := λ x y z w => h x x y z w x
theorem Equation4267_implies_Equation4112 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4112 G := λ x y z w => h x x y z w x
theorem Equation4379_implies_Equation4309 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4309 G := λ x y z w => h x x y z w x
theorem Equation4582_implies_Equation4427 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4427 G := λ x y z w => h x x y z w x
theorem Equation4694_implies_Equation4624 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4624 G := λ x y z w => h x x y z w x