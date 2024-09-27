import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation515 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (y ∘ (y ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation718 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((y ∘ y) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation921 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ y) ∘ (y ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1124 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (y ∘ y)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1327 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ y) ∘ y) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1530 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (y ∘ (y ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1733 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((y ∘ y) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1936 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ y)) ∘ (y ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2139 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ y) ∘ (y ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2342 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (y ∘ y))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2545 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ y) ∘ y)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2748 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (y ∘ y)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2951 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ y)) ∘ y) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3154 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ y) ∘ y) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3357 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (y ∘ (y ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3560 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((y ∘ y) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3763 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ y) ∘ (y ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3966 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (y ∘ y)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4169 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ y) ∘ y) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4484 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (y ∘ y) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation515 (G : Type*) [Magma G] (h : Equation613 G) : Equation515 G := λ x y z => h x y y y y z
theorem Equation816_implies_Equation718 (G : Type*) [Magma G] (h : Equation816 G) : Equation718 G := λ x y z => h x y y y y z
theorem Equation1019_implies_Equation921 (G : Type*) [Magma G] (h : Equation1019 G) : Equation921 G := λ x y z => h x y y y y z
theorem Equation1222_implies_Equation1124 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1124 G := λ x y z => h x y y y y z
theorem Equation1425_implies_Equation1327 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1327 G := λ x y z => h x y y y y z
theorem Equation1628_implies_Equation1530 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1530 G := λ x y z => h x y y y y z
theorem Equation1831_implies_Equation1733 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1733 G := λ x y z => h x y y y y z
theorem Equation2034_implies_Equation1936 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1936 G := λ x y z => h x y y y y z
theorem Equation2237_implies_Equation2139 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2139 G := λ x y z => h x y y y y z
theorem Equation2440_implies_Equation2342 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2342 G := λ x y z => h x y y y y z
theorem Equation2643_implies_Equation2545 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2545 G := λ x y z => h x y y y y z
theorem Equation2846_implies_Equation2748 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2748 G := λ x y z => h x y y y y z
theorem Equation3049_implies_Equation2951 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2951 G := λ x y z => h x y y y y z
theorem Equation3252_implies_Equation3154 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3154 G := λ x y z => h x y y y y z
theorem Equation3455_implies_Equation3357 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3357 G := λ x y z => h x y y y y z
theorem Equation3658_implies_Equation3560 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3560 G := λ x y z => h x y y y y z
theorem Equation3861_implies_Equation3763 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3763 G := λ x y z => h x y y y y z
theorem Equation4064_implies_Equation3966 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3966 G := λ x y z => h x y y y y z
theorem Equation4267_implies_Equation4169 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4169 G := λ x y z => h x y y y y z
theorem Equation4582_implies_Equation4484 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4484 G := λ x y z => h x y y y y z