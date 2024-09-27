import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation522 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ (x ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation725 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((z ∘ x) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation928 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ (x ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1131 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (z ∘ x)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1334 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ z) ∘ x) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1537 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ (x ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1740 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((z ∘ x) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1943 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ (x ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2146 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ (x ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2349 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (z ∘ x))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2552 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ z) ∘ x)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2755 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (z ∘ x)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2958 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ z)) ∘ x) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3161 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ z) ∘ x) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3364 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ (x ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3567 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((z ∘ x) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3770 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ (x ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3973 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (z ∘ x)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4176 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ z) ∘ x) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4491 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (z ∘ x) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation522 (G : Type*) [Magma G] (h : Equation613 G) : Equation522 G := λ x y z => h x y y z x z
theorem Equation816_implies_Equation725 (G : Type*) [Magma G] (h : Equation816 G) : Equation725 G := λ x y z => h x y y z x z
theorem Equation1019_implies_Equation928 (G : Type*) [Magma G] (h : Equation1019 G) : Equation928 G := λ x y z => h x y y z x z
theorem Equation1222_implies_Equation1131 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1131 G := λ x y z => h x y y z x z
theorem Equation1425_implies_Equation1334 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1334 G := λ x y z => h x y y z x z
theorem Equation1628_implies_Equation1537 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1537 G := λ x y z => h x y y z x z
theorem Equation1831_implies_Equation1740 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1740 G := λ x y z => h x y y z x z
theorem Equation2034_implies_Equation1943 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1943 G := λ x y z => h x y y z x z
theorem Equation2237_implies_Equation2146 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2146 G := λ x y z => h x y y z x z
theorem Equation2440_implies_Equation2349 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2349 G := λ x y z => h x y y z x z
theorem Equation2643_implies_Equation2552 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2552 G := λ x y z => h x y y z x z
theorem Equation2846_implies_Equation2755 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2755 G := λ x y z => h x y y z x z
theorem Equation3049_implies_Equation2958 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2958 G := λ x y z => h x y y z x z
theorem Equation3252_implies_Equation3161 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3161 G := λ x y z => h x y y z x z
theorem Equation3455_implies_Equation3364 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3364 G := λ x y z => h x y y z x z
theorem Equation3658_implies_Equation3567 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3567 G := λ x y z => h x y y z x z
theorem Equation3861_implies_Equation3770 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3770 G := λ x y z => h x y y z x z
theorem Equation4064_implies_Equation3973 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3973 G := λ x y z => h x y y z x z
theorem Equation4267_implies_Equation4176 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4176 G := λ x y z => h x y y z x z
theorem Equation4582_implies_Equation4491 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4491 G := λ x y z => h x y y z x z