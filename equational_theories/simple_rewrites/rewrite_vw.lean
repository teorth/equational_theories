import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation611 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (u ∘ w)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation814 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ u) ∘ w))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation1017 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (u ∘ w))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1220 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ w)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1423 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ u) ∘ w)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1626 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (u ∘ w))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1829 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ w)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation2032 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ w)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2235 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ w)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2438 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ w
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2641 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ w
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2844 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ w
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3047 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ w
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3250 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ w
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3453 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (u ∘ w))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3656 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ u) ∘ w)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3859 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (u ∘ w)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4062 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ u)) ∘ w
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4265 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ u) ∘ w
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4580 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ u) ∘ w
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation611 (G : Type*) [Magma G] (h : Equation613 G) : Equation611 G := λ x y z w u => h x y z w u w
theorem Equation816_implies_Equation814 (G : Type*) [Magma G] (h : Equation816 G) : Equation814 G := λ x y z w u => h x y z w u w
theorem Equation1019_implies_Equation1017 (G : Type*) [Magma G] (h : Equation1019 G) : Equation1017 G := λ x y z w u => h x y z w u w
theorem Equation1222_implies_Equation1220 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1220 G := λ x y z w u => h x y z w u w
theorem Equation1425_implies_Equation1423 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1423 G := λ x y z w u => h x y z w u w
theorem Equation1628_implies_Equation1626 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1626 G := λ x y z w u => h x y z w u w
theorem Equation1831_implies_Equation1829 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1829 G := λ x y z w u => h x y z w u w
theorem Equation2034_implies_Equation2032 (G : Type*) [Magma G] (h : Equation2034 G) : Equation2032 G := λ x y z w u => h x y z w u w
theorem Equation2237_implies_Equation2235 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2235 G := λ x y z w u => h x y z w u w
theorem Equation2440_implies_Equation2438 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2438 G := λ x y z w u => h x y z w u w
theorem Equation2643_implies_Equation2641 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2641 G := λ x y z w u => h x y z w u w
theorem Equation2846_implies_Equation2844 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2844 G := λ x y z w u => h x y z w u w
theorem Equation3049_implies_Equation3047 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3047 G := λ x y z w u => h x y z w u w
theorem Equation3252_implies_Equation3250 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3250 G := λ x y z w u => h x y z w u w
theorem Equation3455_implies_Equation3453 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3453 G := λ x y z w u => h x y z w u w
theorem Equation3658_implies_Equation3656 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3656 G := λ x y z w u => h x y z w u w
theorem Equation3861_implies_Equation3859 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3859 G := λ x y z w u => h x y z w u w
theorem Equation4064_implies_Equation4062 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4062 G := λ x y z w u => h x y z w u w
theorem Equation4267_implies_Equation4265 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4265 G := λ x y z w u => h x y z w u w
theorem Equation4582_implies_Equation4580 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4580 G := λ x y z w u => h x y z w u w