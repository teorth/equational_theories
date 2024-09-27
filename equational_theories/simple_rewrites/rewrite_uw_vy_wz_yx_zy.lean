import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation459 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (w ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation662 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ w) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation865 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (w ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1068 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1271 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ w) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1474 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (w ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1677 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1880 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2083 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2286 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2489 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2692 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2895 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3098 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3301 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (w ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3504 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ w) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3707 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (w ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3910 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ w)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4113 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ w) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4310 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (w ∘ y)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4428 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ w) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4625 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ w) ∘ y
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation459 (G : Type*) [Magma G] (h : Equation613 G) : Equation459 G := λ x y z w => h x x y z w y
theorem Equation816_implies_Equation662 (G : Type*) [Magma G] (h : Equation816 G) : Equation662 G := λ x y z w => h x x y z w y
theorem Equation1019_implies_Equation865 (G : Type*) [Magma G] (h : Equation1019 G) : Equation865 G := λ x y z w => h x x y z w y
theorem Equation1222_implies_Equation1068 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1068 G := λ x y z w => h x x y z w y
theorem Equation1425_implies_Equation1271 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1271 G := λ x y z w => h x x y z w y
theorem Equation1628_implies_Equation1474 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1474 G := λ x y z w => h x x y z w y
theorem Equation1831_implies_Equation1677 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1677 G := λ x y z w => h x x y z w y
theorem Equation2034_implies_Equation1880 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1880 G := λ x y z w => h x x y z w y
theorem Equation2237_implies_Equation2083 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2083 G := λ x y z w => h x x y z w y
theorem Equation2440_implies_Equation2286 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2286 G := λ x y z w => h x x y z w y
theorem Equation2643_implies_Equation2489 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2489 G := λ x y z w => h x x y z w y
theorem Equation2846_implies_Equation2692 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2692 G := λ x y z w => h x x y z w y
theorem Equation3049_implies_Equation2895 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2895 G := λ x y z w => h x x y z w y
theorem Equation3252_implies_Equation3098 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3098 G := λ x y z w => h x x y z w y
theorem Equation3455_implies_Equation3301 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3301 G := λ x y z w => h x x y z w y
theorem Equation3658_implies_Equation3504 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3504 G := λ x y z w => h x x y z w y
theorem Equation3861_implies_Equation3707 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3707 G := λ x y z w => h x x y z w y
theorem Equation4064_implies_Equation3910 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3910 G := λ x y z w => h x x y z w y
theorem Equation4267_implies_Equation4113 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4113 G := λ x y z w => h x x y z w y
theorem Equation4379_implies_Equation4310 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4310 G := λ x y z w => h x x y z w y
theorem Equation4582_implies_Equation4428 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4428 G := λ x y z w => h x x y z w y
theorem Equation4694_implies_Equation4625 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4625 G := λ x y z w => h x x y z w y