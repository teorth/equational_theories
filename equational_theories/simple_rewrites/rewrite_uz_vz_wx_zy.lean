import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation508 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (x ∘ (z ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation711 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((x ∘ z) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation914 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ x) ∘ (z ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1117 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (x ∘ z)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1320 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ x) ∘ z) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1523 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (x ∘ (z ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1726 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((x ∘ z) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1929 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ x)) ∘ (z ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2132 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ x) ∘ (z ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2335 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (x ∘ z))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2538 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ x) ∘ z)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2741 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (x ∘ z)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2944 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ x)) ∘ z) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3147 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ x) ∘ z) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3350 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (x ∘ (z ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3553 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((x ∘ z) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3756 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ x) ∘ (z ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3959 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (x ∘ z)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4162 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ x) ∘ z) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4341 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = x ∘ (z ∘ z)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4477 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (x ∘ z) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4656 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ y = (x ∘ z) ∘ z
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation508 (G : Type*) [Magma G] (h : Equation613 G) : Equation508 G := λ x y z => h x y y x z z
theorem Equation816_implies_Equation711 (G : Type*) [Magma G] (h : Equation816 G) : Equation711 G := λ x y z => h x y y x z z
theorem Equation1019_implies_Equation914 (G : Type*) [Magma G] (h : Equation1019 G) : Equation914 G := λ x y z => h x y y x z z
theorem Equation1222_implies_Equation1117 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1117 G := λ x y z => h x y y x z z
theorem Equation1425_implies_Equation1320 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1320 G := λ x y z => h x y y x z z
theorem Equation1628_implies_Equation1523 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1523 G := λ x y z => h x y y x z z
theorem Equation1831_implies_Equation1726 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1726 G := λ x y z => h x y y x z z
theorem Equation2034_implies_Equation1929 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1929 G := λ x y z => h x y y x z z
theorem Equation2237_implies_Equation2132 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2132 G := λ x y z => h x y y x z z
theorem Equation2440_implies_Equation2335 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2335 G := λ x y z => h x y y x z z
theorem Equation2643_implies_Equation2538 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2538 G := λ x y z => h x y y x z z
theorem Equation2846_implies_Equation2741 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2741 G := λ x y z => h x y y x z z
theorem Equation3049_implies_Equation2944 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2944 G := λ x y z => h x y y x z z
theorem Equation3252_implies_Equation3147 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3147 G := λ x y z => h x y y x z z
theorem Equation3455_implies_Equation3350 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3350 G := λ x y z => h x y y x z z
theorem Equation3658_implies_Equation3553 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3553 G := λ x y z => h x y y x z z
theorem Equation3861_implies_Equation3756 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3756 G := λ x y z => h x y y x z z
theorem Equation4064_implies_Equation3959 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3959 G := λ x y z => h x y y x z z
theorem Equation4267_implies_Equation4162 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4162 G := λ x y z => h x y y x z z
theorem Equation4379_implies_Equation4341 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4341 G := λ x y z => h x y y x z z
theorem Equation4582_implies_Equation4477 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4477 G := λ x y z => h x y y x z z
theorem Equation4694_implies_Equation4656 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4656 G := λ x y z => h x y y x z z