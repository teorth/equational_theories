import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation564 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ (z ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation767 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((y ∘ z) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation970 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ (z ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1173 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (y ∘ z)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1376 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ y) ∘ z) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1579 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ (z ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1782 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((y ∘ z) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1985 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ (z ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2188 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ (z ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2391 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (y ∘ z))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2594 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ y) ∘ z)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2797 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (y ∘ z)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3000 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ y)) ∘ z) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3203 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ y) ∘ z) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3406 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ (z ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3609 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((y ∘ z) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3812 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ (z ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4015 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (y ∘ z)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4218 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ y) ∘ z) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4533 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (y ∘ z) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation564 (G : Type*) [Magma G] (h : Equation613 G) : Equation564 G := λ x y z => h x y z y z z
theorem Equation816_implies_Equation767 (G : Type*) [Magma G] (h : Equation816 G) : Equation767 G := λ x y z => h x y z y z z
theorem Equation1019_implies_Equation970 (G : Type*) [Magma G] (h : Equation1019 G) : Equation970 G := λ x y z => h x y z y z z
theorem Equation1222_implies_Equation1173 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1173 G := λ x y z => h x y z y z z
theorem Equation1425_implies_Equation1376 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1376 G := λ x y z => h x y z y z z
theorem Equation1628_implies_Equation1579 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1579 G := λ x y z => h x y z y z z
theorem Equation1831_implies_Equation1782 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1782 G := λ x y z => h x y z y z z
theorem Equation2034_implies_Equation1985 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1985 G := λ x y z => h x y z y z z
theorem Equation2237_implies_Equation2188 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2188 G := λ x y z => h x y z y z z
theorem Equation2440_implies_Equation2391 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2391 G := λ x y z => h x y z y z z
theorem Equation2643_implies_Equation2594 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2594 G := λ x y z => h x y z y z z
theorem Equation2846_implies_Equation2797 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2797 G := λ x y z => h x y z y z z
theorem Equation3049_implies_Equation3000 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3000 G := λ x y z => h x y z y z z
theorem Equation3252_implies_Equation3203 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3203 G := λ x y z => h x y z y z z
theorem Equation3455_implies_Equation3406 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3406 G := λ x y z => h x y z y z z
theorem Equation3658_implies_Equation3609 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3609 G := λ x y z => h x y z y z z
theorem Equation3861_implies_Equation3812 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3812 G := λ x y z => h x y z y z z
theorem Equation4064_implies_Equation4015 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4015 G := λ x y z => h x y z y z z
theorem Equation4267_implies_Equation4218 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4218 G := λ x y z => h x y z y z z
theorem Equation4582_implies_Equation4533 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4533 G := λ x y z => h x y z y z z