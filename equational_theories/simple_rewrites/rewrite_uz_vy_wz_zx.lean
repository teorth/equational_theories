import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation492 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ (z ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation695 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((z ∘ z) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation898 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ (z ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1101 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (z ∘ z)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1304 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ z) ∘ z) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1507 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ (z ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1710 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((z ∘ z) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1913 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ (z ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2116 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ (z ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2319 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (z ∘ z))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2522 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ z) ∘ z)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2725 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (z ∘ z)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2928 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ z)) ∘ z) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3131 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ z) ∘ z) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3334 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ (z ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3537 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((z ∘ z) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3740 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ (z ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3943 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (z ∘ z)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4146 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ z) ∘ z) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4461 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (z ∘ z) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation492 (G : Type*) [Magma G] (h : Equation613 G) : Equation492 G := λ x y z => h x y x z z y
theorem Equation816_implies_Equation695 (G : Type*) [Magma G] (h : Equation816 G) : Equation695 G := λ x y z => h x y x z z y
theorem Equation1019_implies_Equation898 (G : Type*) [Magma G] (h : Equation1019 G) : Equation898 G := λ x y z => h x y x z z y
theorem Equation1222_implies_Equation1101 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1101 G := λ x y z => h x y x z z y
theorem Equation1425_implies_Equation1304 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1304 G := λ x y z => h x y x z z y
theorem Equation1628_implies_Equation1507 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1507 G := λ x y z => h x y x z z y
theorem Equation1831_implies_Equation1710 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1710 G := λ x y z => h x y x z z y
theorem Equation2034_implies_Equation1913 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1913 G := λ x y z => h x y x z z y
theorem Equation2237_implies_Equation2116 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2116 G := λ x y z => h x y x z z y
theorem Equation2440_implies_Equation2319 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2319 G := λ x y z => h x y x z z y
theorem Equation2643_implies_Equation2522 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2522 G := λ x y z => h x y x z z y
theorem Equation2846_implies_Equation2725 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2725 G := λ x y z => h x y x z z y
theorem Equation3049_implies_Equation2928 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2928 G := λ x y z => h x y x z z y
theorem Equation3252_implies_Equation3131 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3131 G := λ x y z => h x y x z z y
theorem Equation3455_implies_Equation3334 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3334 G := λ x y z => h x y x z z y
theorem Equation3658_implies_Equation3537 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3537 G := λ x y z => h x y x z z y
theorem Equation3861_implies_Equation3740 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3740 G := λ x y z => h x y x z z y
theorem Equation4064_implies_Equation3943 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3943 G := λ x y z => h x y x z z y
theorem Equation4267_implies_Equation4146 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4146 G := λ x y z => h x y x z z y
theorem Equation4582_implies_Equation4461 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4461 G := λ x y z => h x y x z z y