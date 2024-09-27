import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation592 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (x ∘ u)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation795 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ x) ∘ u))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation998 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (x ∘ u))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1201 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ x)) ∘ u)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1404 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ x) ∘ u)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1607 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (x ∘ u))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1810 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ x) ∘ u)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation2013 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (x ∘ u)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2216 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (x ∘ u)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2419 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ x))) ∘ u
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2622 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ x)) ∘ u
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2825 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ x)) ∘ u
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3028 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ x) ∘ u
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3231 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ x) ∘ u
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3434 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (x ∘ u))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3637 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ x) ∘ u)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3840 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (x ∘ u)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4043 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ x)) ∘ u
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4246 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ x) ∘ u
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4561 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ x) ∘ u
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation592 (G : Type*) [Magma G] (h : Equation613 G) : Equation592 G := λ x y z w u => h x y z w x u
theorem Equation816_implies_Equation795 (G : Type*) [Magma G] (h : Equation816 G) : Equation795 G := λ x y z w u => h x y z w x u
theorem Equation1019_implies_Equation998 (G : Type*) [Magma G] (h : Equation1019 G) : Equation998 G := λ x y z w u => h x y z w x u
theorem Equation1222_implies_Equation1201 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1201 G := λ x y z w u => h x y z w x u
theorem Equation1425_implies_Equation1404 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1404 G := λ x y z w u => h x y z w x u
theorem Equation1628_implies_Equation1607 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1607 G := λ x y z w u => h x y z w x u
theorem Equation1831_implies_Equation1810 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1810 G := λ x y z w u => h x y z w x u
theorem Equation2034_implies_Equation2013 (G : Type*) [Magma G] (h : Equation2034 G) : Equation2013 G := λ x y z w u => h x y z w x u
theorem Equation2237_implies_Equation2216 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2216 G := λ x y z w u => h x y z w x u
theorem Equation2440_implies_Equation2419 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2419 G := λ x y z w u => h x y z w x u
theorem Equation2643_implies_Equation2622 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2622 G := λ x y z w u => h x y z w x u
theorem Equation2846_implies_Equation2825 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2825 G := λ x y z w u => h x y z w x u
theorem Equation3049_implies_Equation3028 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3028 G := λ x y z w u => h x y z w x u
theorem Equation3252_implies_Equation3231 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3231 G := λ x y z w u => h x y z w x u
theorem Equation3455_implies_Equation3434 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3434 G := λ x y z w u => h x y z w x u
theorem Equation3658_implies_Equation3637 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3637 G := λ x y z w u => h x y z w x u
theorem Equation3861_implies_Equation3840 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3840 G := λ x y z w u => h x y z w x u
theorem Equation4064_implies_Equation4043 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4043 G := λ x y z w u => h x y z w x u
theorem Equation4267_implies_Equation4246 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4246 G := λ x y z w u => h x y z w x u
theorem Equation4582_implies_Equation4561 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4561 G := λ x y z w u => h x y z w x u