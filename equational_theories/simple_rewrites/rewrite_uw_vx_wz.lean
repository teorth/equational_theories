import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation583 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (w ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation786 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ w) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation989 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (w ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1192 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ w)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1395 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ w) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1598 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (w ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1801 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ w) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation2004 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (w ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2207 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (w ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2410 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ w))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2613 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ w)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2816 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ w)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3019 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ w) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3222 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ w) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3425 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (w ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3628 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ w) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3831 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (w ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4034 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ w)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4237 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ w) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4371 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = z ∘ (w ∘ x)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4552 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ w) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4686 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (z ∘ w) ∘ x
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation583 (G : Type*) [Magma G] (h : Equation613 G) : Equation583 G := λ x y z w => h x y z z w x
theorem Equation816_implies_Equation786 (G : Type*) [Magma G] (h : Equation816 G) : Equation786 G := λ x y z w => h x y z z w x
theorem Equation1019_implies_Equation989 (G : Type*) [Magma G] (h : Equation1019 G) : Equation989 G := λ x y z w => h x y z z w x
theorem Equation1222_implies_Equation1192 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1192 G := λ x y z w => h x y z z w x
theorem Equation1425_implies_Equation1395 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1395 G := λ x y z w => h x y z z w x
theorem Equation1628_implies_Equation1598 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1598 G := λ x y z w => h x y z z w x
theorem Equation1831_implies_Equation1801 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1801 G := λ x y z w => h x y z z w x
theorem Equation2034_implies_Equation2004 (G : Type*) [Magma G] (h : Equation2034 G) : Equation2004 G := λ x y z w => h x y z z w x
theorem Equation2237_implies_Equation2207 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2207 G := λ x y z w => h x y z z w x
theorem Equation2440_implies_Equation2410 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2410 G := λ x y z w => h x y z z w x
theorem Equation2643_implies_Equation2613 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2613 G := λ x y z w => h x y z z w x
theorem Equation2846_implies_Equation2816 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2816 G := λ x y z w => h x y z z w x
theorem Equation3049_implies_Equation3019 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3019 G := λ x y z w => h x y z z w x
theorem Equation3252_implies_Equation3222 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3222 G := λ x y z w => h x y z z w x
theorem Equation3455_implies_Equation3425 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3425 G := λ x y z w => h x y z z w x
theorem Equation3658_implies_Equation3628 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3628 G := λ x y z w => h x y z z w x
theorem Equation3861_implies_Equation3831 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3831 G := λ x y z w => h x y z z w x
theorem Equation4064_implies_Equation4034 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4034 G := λ x y z w => h x y z z w x
theorem Equation4267_implies_Equation4237 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4237 G := λ x y z w => h x y z z w x
theorem Equation4379_implies_Equation4371 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4371 G := λ x y z w => h x y z z w x
theorem Equation4582_implies_Equation4552 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4552 G := λ x y z w => h x y z z w x
theorem Equation4694_implies_Equation4686 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4686 G := λ x y z w => h x y z z w x