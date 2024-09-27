import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation463 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (x ∘ (x ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation666 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((x ∘ x) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation869 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ x) ∘ (x ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1072 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (x ∘ x)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1275 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ x) ∘ x) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1478 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (x ∘ (x ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1681 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((x ∘ x) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1884 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ x)) ∘ (x ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2087 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ x) ∘ (x ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2290 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (x ∘ x))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2493 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ x) ∘ x)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2696 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (x ∘ x)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2899 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ x)) ∘ x) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3102 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ x) ∘ x) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3305 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (x ∘ (x ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3508 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((x ∘ x) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3711 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ x) ∘ (x ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3914 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (x ∘ x)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4117 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ x) ∘ x) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4432 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (x ∘ x) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation463 (G : Type*) [Magma G] (h : Equation613 G) : Equation463 G := λ x y => h x y x x x x
theorem Equation816_implies_Equation666 (G : Type*) [Magma G] (h : Equation816 G) : Equation666 G := λ x y => h x y x x x x
theorem Equation1019_implies_Equation869 (G : Type*) [Magma G] (h : Equation1019 G) : Equation869 G := λ x y => h x y x x x x
theorem Equation1222_implies_Equation1072 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1072 G := λ x y => h x y x x x x
theorem Equation1425_implies_Equation1275 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1275 G := λ x y => h x y x x x x
theorem Equation1628_implies_Equation1478 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1478 G := λ x y => h x y x x x x
theorem Equation1831_implies_Equation1681 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1681 G := λ x y => h x y x x x x
theorem Equation2034_implies_Equation1884 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1884 G := λ x y => h x y x x x x
theorem Equation2237_implies_Equation2087 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2087 G := λ x y => h x y x x x x
theorem Equation2440_implies_Equation2290 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2290 G := λ x y => h x y x x x x
theorem Equation2643_implies_Equation2493 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2493 G := λ x y => h x y x x x x
theorem Equation2846_implies_Equation2696 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2696 G := λ x y => h x y x x x x
theorem Equation3049_implies_Equation2899 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2899 G := λ x y => h x y x x x x
theorem Equation3252_implies_Equation3102 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3102 G := λ x y => h x y x x x x
theorem Equation3455_implies_Equation3305 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3305 G := λ x y => h x y x x x x
theorem Equation3658_implies_Equation3508 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3508 G := λ x y => h x y x x x x
theorem Equation3861_implies_Equation3711 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3711 G := λ x y => h x y x x x x
theorem Equation4064_implies_Equation3914 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3914 G := λ x y => h x y x x x x
theorem Equation4267_implies_Equation4117 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4117 G := λ x y => h x y x x x x
theorem Equation4582_implies_Equation4432 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4432 G := λ x y => h x y x x x x