import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation478 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (y ∘ (y ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation681 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((y ∘ y) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation884 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ y) ∘ (y ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1087 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (y ∘ y)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1290 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ y) ∘ y) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1493 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (y ∘ (y ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1696 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((y ∘ y) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1899 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ y)) ∘ (y ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2102 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ y) ∘ (y ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2305 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (y ∘ y))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2508 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ y) ∘ y)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2711 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (y ∘ y)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2914 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ y)) ∘ y) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3117 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ y) ∘ y) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3320 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (y ∘ (y ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3523 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((y ∘ y) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3726 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ y) ∘ (y ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3929 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (y ∘ y)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4132 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ y) ∘ y) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4447 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (y ∘ y) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation478 (G : Type*) [Magma G] (h : Equation613 G) : Equation478 G := λ x y z => h x y x y y z
theorem Equation816_implies_Equation681 (G : Type*) [Magma G] (h : Equation816 G) : Equation681 G := λ x y z => h x y x y y z
theorem Equation1019_implies_Equation884 (G : Type*) [Magma G] (h : Equation1019 G) : Equation884 G := λ x y z => h x y x y y z
theorem Equation1222_implies_Equation1087 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1087 G := λ x y z => h x y x y y z
theorem Equation1425_implies_Equation1290 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1290 G := λ x y z => h x y x y y z
theorem Equation1628_implies_Equation1493 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1493 G := λ x y z => h x y x y y z
theorem Equation1831_implies_Equation1696 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1696 G := λ x y z => h x y x y y z
theorem Equation2034_implies_Equation1899 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1899 G := λ x y z => h x y x y y z
theorem Equation2237_implies_Equation2102 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2102 G := λ x y z => h x y x y y z
theorem Equation2440_implies_Equation2305 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2305 G := λ x y z => h x y x y y z
theorem Equation2643_implies_Equation2508 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2508 G := λ x y z => h x y x y y z
theorem Equation2846_implies_Equation2711 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2711 G := λ x y z => h x y x y y z
theorem Equation3049_implies_Equation2914 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2914 G := λ x y z => h x y x y y z
theorem Equation3252_implies_Equation3117 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3117 G := λ x y z => h x y x y y z
theorem Equation3455_implies_Equation3320 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3320 G := λ x y z => h x y x y y z
theorem Equation3658_implies_Equation3523 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3523 G := λ x y z => h x y x y y z
theorem Equation3861_implies_Equation3726 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3726 G := λ x y z => h x y x y y z
theorem Equation4064_implies_Equation3929 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3929 G := λ x y z => h x y x y y z
theorem Equation4267_implies_Equation4132 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4132 G := λ x y z => h x y x y y z
theorem Equation4582_implies_Equation4447 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4447 G := λ x y z => h x y x y y z