import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation545 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ (z ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation748 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((x ∘ z) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation951 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ (z ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1154 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (x ∘ z)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1357 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ x) ∘ z) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1560 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ (z ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1763 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((x ∘ z) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1966 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ (z ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2169 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ (z ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2372 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (x ∘ z))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2575 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ x) ∘ z)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2778 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (x ∘ z)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2981 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ x)) ∘ z) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3184 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ x) ∘ z) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3387 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ (z ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3590 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((x ∘ z) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3793 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ (z ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3996 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (x ∘ z)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4199 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ x) ∘ z) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4514 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ z) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation545 (G : Type*) [Magma G] (h : Equation613 G) : Equation545 G := λ x y z => h x y z x z x
theorem Equation816_implies_Equation748 (G : Type*) [Magma G] (h : Equation816 G) : Equation748 G := λ x y z => h x y z x z x
theorem Equation1019_implies_Equation951 (G : Type*) [Magma G] (h : Equation1019 G) : Equation951 G := λ x y z => h x y z x z x
theorem Equation1222_implies_Equation1154 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1154 G := λ x y z => h x y z x z x
theorem Equation1425_implies_Equation1357 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1357 G := λ x y z => h x y z x z x
theorem Equation1628_implies_Equation1560 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1560 G := λ x y z => h x y z x z x
theorem Equation1831_implies_Equation1763 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1763 G := λ x y z => h x y z x z x
theorem Equation2034_implies_Equation1966 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1966 G := λ x y z => h x y z x z x
theorem Equation2237_implies_Equation2169 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2169 G := λ x y z => h x y z x z x
theorem Equation2440_implies_Equation2372 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2372 G := λ x y z => h x y z x z x
theorem Equation2643_implies_Equation2575 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2575 G := λ x y z => h x y z x z x
theorem Equation2846_implies_Equation2778 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2778 G := λ x y z => h x y z x z x
theorem Equation3049_implies_Equation2981 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2981 G := λ x y z => h x y z x z x
theorem Equation3252_implies_Equation3184 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3184 G := λ x y z => h x y z x z x
theorem Equation3455_implies_Equation3387 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3387 G := λ x y z => h x y z x z x
theorem Equation3658_implies_Equation3590 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3590 G := λ x y z => h x y z x z x
theorem Equation3861_implies_Equation3793 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3793 G := λ x y z => h x y z x z x
theorem Equation4064_implies_Equation3996 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3996 G := λ x y z => h x y z x z x
theorem Equation4267_implies_Equation4199 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4199 G := λ x y z => h x y z x z x
theorem Equation4582_implies_Equation4514 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4514 G := λ x y z => h x y z x z x