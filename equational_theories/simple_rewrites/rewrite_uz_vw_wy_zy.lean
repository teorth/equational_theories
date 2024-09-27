import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation519 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (y ∘ (z ∘ w)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation722 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((y ∘ z) ∘ w))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation925 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ y) ∘ (z ∘ w))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1128 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (y ∘ z)) ∘ w)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1331 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ y) ∘ z) ∘ w)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1534 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (y ∘ (z ∘ w))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1737 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((y ∘ z) ∘ w)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1940 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ y)) ∘ (z ∘ w)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2143 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ y) ∘ (z ∘ w)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2346 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (y ∘ z))) ∘ w
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2549 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ y) ∘ z)) ∘ w
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2752 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (y ∘ z)) ∘ w
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2955 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ y)) ∘ z) ∘ w
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3158 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ y) ∘ z) ∘ w
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3361 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (y ∘ (z ∘ w))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3564 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((y ∘ z) ∘ w)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3767 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ y) ∘ (z ∘ w)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3970 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (y ∘ z)) ∘ w
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4173 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ y) ∘ z) ∘ w
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4347 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = y ∘ (z ∘ w)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4488 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (y ∘ z) ∘ w
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4662 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ y = (y ∘ z) ∘ w
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation519 (G : Type*) [Magma G] (h : Equation613 G) : Equation519 G := λ x y z w => h x y y y z w
theorem Equation816_implies_Equation722 (G : Type*) [Magma G] (h : Equation816 G) : Equation722 G := λ x y z w => h x y y y z w
theorem Equation1019_implies_Equation925 (G : Type*) [Magma G] (h : Equation1019 G) : Equation925 G := λ x y z w => h x y y y z w
theorem Equation1222_implies_Equation1128 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1128 G := λ x y z w => h x y y y z w
theorem Equation1425_implies_Equation1331 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1331 G := λ x y z w => h x y y y z w
theorem Equation1628_implies_Equation1534 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1534 G := λ x y z w => h x y y y z w
theorem Equation1831_implies_Equation1737 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1737 G := λ x y z w => h x y y y z w
theorem Equation2034_implies_Equation1940 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1940 G := λ x y z w => h x y y y z w
theorem Equation2237_implies_Equation2143 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2143 G := λ x y z w => h x y y y z w
theorem Equation2440_implies_Equation2346 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2346 G := λ x y z w => h x y y y z w
theorem Equation2643_implies_Equation2549 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2549 G := λ x y z w => h x y y y z w
theorem Equation2846_implies_Equation2752 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2752 G := λ x y z w => h x y y y z w
theorem Equation3049_implies_Equation2955 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2955 G := λ x y z w => h x y y y z w
theorem Equation3252_implies_Equation3158 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3158 G := λ x y z w => h x y y y z w
theorem Equation3455_implies_Equation3361 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3361 G := λ x y z w => h x y y y z w
theorem Equation3658_implies_Equation3564 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3564 G := λ x y z w => h x y y y z w
theorem Equation3861_implies_Equation3767 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3767 G := λ x y z w => h x y y y z w
theorem Equation4064_implies_Equation3970 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3970 G := λ x y z w => h x y y y z w
theorem Equation4267_implies_Equation4173 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4173 G := λ x y z w => h x y y y z w
theorem Equation4379_implies_Equation4347 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4347 G := λ x y z w => h x y y y z w
theorem Equation4582_implies_Equation4488 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4488 G := λ x y z w => h x y y y z w
theorem Equation4694_implies_Equation4662 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4662 G := λ x y z w => h x y y y z w