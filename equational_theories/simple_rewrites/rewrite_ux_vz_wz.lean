import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation573 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (x ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation776 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ x) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation979 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (x ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1182 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ x)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1385 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ x) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1588 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (x ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1791 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ x) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1994 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (x ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2197 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (x ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2400 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ x))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2603 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ x)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2806 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ x)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3009 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ x) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3212 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ x) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3415 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (x ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3618 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ x) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3821 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (x ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4024 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ x)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4227 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ x) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4542 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ x) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation573 (G : Type*) [Magma G] (h : Equation613 G) : Equation573 G := λ x y z => h x y z z x z
theorem Equation816_implies_Equation776 (G : Type*) [Magma G] (h : Equation816 G) : Equation776 G := λ x y z => h x y z z x z
theorem Equation1019_implies_Equation979 (G : Type*) [Magma G] (h : Equation1019 G) : Equation979 G := λ x y z => h x y z z x z
theorem Equation1222_implies_Equation1182 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1182 G := λ x y z => h x y z z x z
theorem Equation1425_implies_Equation1385 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1385 G := λ x y z => h x y z z x z
theorem Equation1628_implies_Equation1588 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1588 G := λ x y z => h x y z z x z
theorem Equation1831_implies_Equation1791 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1791 G := λ x y z => h x y z z x z
theorem Equation2034_implies_Equation1994 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1994 G := λ x y z => h x y z z x z
theorem Equation2237_implies_Equation2197 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2197 G := λ x y z => h x y z z x z
theorem Equation2440_implies_Equation2400 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2400 G := λ x y z => h x y z z x z
theorem Equation2643_implies_Equation2603 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2603 G := λ x y z => h x y z z x z
theorem Equation2846_implies_Equation2806 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2806 G := λ x y z => h x y z z x z
theorem Equation3049_implies_Equation3009 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3009 G := λ x y z => h x y z z x z
theorem Equation3252_implies_Equation3212 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3212 G := λ x y z => h x y z z x z
theorem Equation3455_implies_Equation3415 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3415 G := λ x y z => h x y z z x z
theorem Equation3658_implies_Equation3618 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3618 G := λ x y z => h x y z z x z
theorem Equation3861_implies_Equation3821 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3821 G := λ x y z => h x y z z x z
theorem Equation4064_implies_Equation4024 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4024 G := λ x y z => h x y z z x z
theorem Equation4267_implies_Equation4227 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4227 G := λ x y z => h x y z z x z
theorem Equation4582_implies_Equation4542 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4542 G := λ x y z => h x y z z x z