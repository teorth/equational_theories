import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation530 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ (z ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation733 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((z ∘ z) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation936 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ (z ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1139 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (z ∘ z)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1342 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ z) ∘ z) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1545 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ (z ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1748 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((z ∘ z) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1951 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ (z ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2154 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ (z ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2357 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (z ∘ z))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2560 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ z) ∘ z)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2763 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (z ∘ z)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2966 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ z)) ∘ z) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3169 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ z) ∘ z) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3372 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ (z ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3575 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((z ∘ z) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3778 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ (z ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3981 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (z ∘ z)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4184 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ z) ∘ z) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4499 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (z ∘ z) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation530 (G : Type*) [Magma G] (h : Equation613 G) : Equation530 G := λ x y z => h x y y z z z
theorem Equation816_implies_Equation733 (G : Type*) [Magma G] (h : Equation816 G) : Equation733 G := λ x y z => h x y y z z z
theorem Equation1019_implies_Equation936 (G : Type*) [Magma G] (h : Equation1019 G) : Equation936 G := λ x y z => h x y y z z z
theorem Equation1222_implies_Equation1139 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1139 G := λ x y z => h x y y z z z
theorem Equation1425_implies_Equation1342 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1342 G := λ x y z => h x y y z z z
theorem Equation1628_implies_Equation1545 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1545 G := λ x y z => h x y y z z z
theorem Equation1831_implies_Equation1748 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1748 G := λ x y z => h x y y z z z
theorem Equation2034_implies_Equation1951 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1951 G := λ x y z => h x y y z z z
theorem Equation2237_implies_Equation2154 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2154 G := λ x y z => h x y y z z z
theorem Equation2440_implies_Equation2357 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2357 G := λ x y z => h x y y z z z
theorem Equation2643_implies_Equation2560 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2560 G := λ x y z => h x y y z z z
theorem Equation2846_implies_Equation2763 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2763 G := λ x y z => h x y y z z z
theorem Equation3049_implies_Equation2966 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2966 G := λ x y z => h x y y z z z
theorem Equation3252_implies_Equation3169 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3169 G := λ x y z => h x y y z z z
theorem Equation3455_implies_Equation3372 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3372 G := λ x y z => h x y y z z z
theorem Equation3658_implies_Equation3575 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3575 G := λ x y z => h x y y z z z
theorem Equation3861_implies_Equation3778 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3778 G := λ x y z => h x y y z z z
theorem Equation4064_implies_Equation3981 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3981 G := λ x y z => h x y y z z z
theorem Equation4267_implies_Equation4184 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4184 G := λ x y z => h x y y z z z
theorem Equation4582_implies_Equation4499 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4499 G := λ x y z => h x y y z z z