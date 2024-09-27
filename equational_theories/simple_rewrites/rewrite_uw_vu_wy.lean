import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation570 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (y ∘ (w ∘ u)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation773 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((y ∘ w) ∘ u))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation976 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ y) ∘ (w ∘ u))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1179 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ u)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1382 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ y) ∘ w) ∘ u)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1585 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (y ∘ (w ∘ u))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1788 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ u)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1991 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ u)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2194 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ u)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2397 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ u
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2600 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ u
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2803 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ u
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3006 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ u
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3209 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ u
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3412 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (y ∘ (w ∘ u))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3615 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((y ∘ w) ∘ u)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3818 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ y) ∘ (w ∘ u)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4021 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (y ∘ w)) ∘ u
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4224 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ y) ∘ w) ∘ u
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4368 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = y ∘ (w ∘ u)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4539 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (y ∘ w) ∘ u
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4683 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (y ∘ w) ∘ u
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation570 (G : Type*) [Magma G] (h : Equation613 G) : Equation570 G := λ x y z w u => h x y z y w u
theorem Equation816_implies_Equation773 (G : Type*) [Magma G] (h : Equation816 G) : Equation773 G := λ x y z w u => h x y z y w u
theorem Equation1019_implies_Equation976 (G : Type*) [Magma G] (h : Equation1019 G) : Equation976 G := λ x y z w u => h x y z y w u
theorem Equation1222_implies_Equation1179 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1179 G := λ x y z w u => h x y z y w u
theorem Equation1425_implies_Equation1382 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1382 G := λ x y z w u => h x y z y w u
theorem Equation1628_implies_Equation1585 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1585 G := λ x y z w u => h x y z y w u
theorem Equation1831_implies_Equation1788 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1788 G := λ x y z w u => h x y z y w u
theorem Equation2034_implies_Equation1991 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1991 G := λ x y z w u => h x y z y w u
theorem Equation2237_implies_Equation2194 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2194 G := λ x y z w u => h x y z y w u
theorem Equation2440_implies_Equation2397 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2397 G := λ x y z w u => h x y z y w u
theorem Equation2643_implies_Equation2600 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2600 G := λ x y z w u => h x y z y w u
theorem Equation2846_implies_Equation2803 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2803 G := λ x y z w u => h x y z y w u
theorem Equation3049_implies_Equation3006 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3006 G := λ x y z w u => h x y z y w u
theorem Equation3252_implies_Equation3209 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3209 G := λ x y z w u => h x y z y w u
theorem Equation3455_implies_Equation3412 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3412 G := λ x y z w u => h x y z y w u
theorem Equation3658_implies_Equation3615 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3615 G := λ x y z w u => h x y z y w u
theorem Equation3861_implies_Equation3818 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3818 G := λ x y z w u => h x y z y w u
theorem Equation4064_implies_Equation4021 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4021 G := λ x y z w u => h x y z y w u
theorem Equation4267_implies_Equation4224 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4224 G := λ x y z w u => h x y z y w u
theorem Equation4379_implies_Equation4368 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4368 G := λ x y z w u => h x y z y w u
theorem Equation4582_implies_Equation4539 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4539 G := λ x y z w u => h x y z y w u
theorem Equation4694_implies_Equation4683 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4683 G := λ x y z w u => h x y z y w u