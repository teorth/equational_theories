import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation493 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ (z ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation696 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((z ∘ z) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation899 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ (z ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1102 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (z ∘ z)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1305 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ z) ∘ z) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1508 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ (z ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1711 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((z ∘ z) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1914 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ (z ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2117 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ (z ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2320 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (z ∘ z))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2523 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ z) ∘ z)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2726 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (z ∘ z)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2929 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ z)) ∘ z) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3132 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ z) ∘ z) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3335 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ (z ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3538 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((z ∘ z) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3741 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ (z ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3944 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (z ∘ z)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4147 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ z) ∘ z) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4462 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (z ∘ z) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation493 (G : Type*) [Magma G] (h : Equation613 G) : Equation493 G := λ x y z => h x y x z z z
theorem Equation816_implies_Equation696 (G : Type*) [Magma G] (h : Equation816 G) : Equation696 G := λ x y z => h x y x z z z
theorem Equation1019_implies_Equation899 (G : Type*) [Magma G] (h : Equation1019 G) : Equation899 G := λ x y z => h x y x z z z
theorem Equation1222_implies_Equation1102 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1102 G := λ x y z => h x y x z z z
theorem Equation1425_implies_Equation1305 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1305 G := λ x y z => h x y x z z z
theorem Equation1628_implies_Equation1508 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1508 G := λ x y z => h x y x z z z
theorem Equation1831_implies_Equation1711 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1711 G := λ x y z => h x y x z z z
theorem Equation2034_implies_Equation1914 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1914 G := λ x y z => h x y x z z z
theorem Equation2237_implies_Equation2117 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2117 G := λ x y z => h x y x z z z
theorem Equation2440_implies_Equation2320 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2320 G := λ x y z => h x y x z z z
theorem Equation2643_implies_Equation2523 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2523 G := λ x y z => h x y x z z z
theorem Equation2846_implies_Equation2726 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2726 G := λ x y z => h x y x z z z
theorem Equation3049_implies_Equation2929 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2929 G := λ x y z => h x y x z z z
theorem Equation3252_implies_Equation3132 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3132 G := λ x y z => h x y x z z z
theorem Equation3455_implies_Equation3335 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3335 G := λ x y z => h x y x z z z
theorem Equation3658_implies_Equation3538 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3538 G := λ x y z => h x y x z z z
theorem Equation3861_implies_Equation3741 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3741 G := λ x y z => h x y x z z z
theorem Equation4064_implies_Equation3944 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3944 G := λ x y z => h x y x z z z
theorem Equation4267_implies_Equation4147 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4147 G := λ x y z => h x y x z z z
theorem Equation4582_implies_Equation4462 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4462 G := λ x y z => h x y x z z z