import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation470 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (x ∘ (z ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation673 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((x ∘ z) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation876 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ x) ∘ (z ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1079 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (x ∘ z)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1282 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ x) ∘ z) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1485 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (x ∘ (z ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1688 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((x ∘ z) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1891 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ x)) ∘ (z ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2094 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ x) ∘ (z ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2297 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (x ∘ z))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2500 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ x) ∘ z)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2703 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (x ∘ z)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2906 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ x)) ∘ z) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3109 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ x) ∘ z) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3312 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (x ∘ (z ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3515 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((x ∘ z) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3718 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ x) ∘ (z ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3921 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (x ∘ z)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4124 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ x) ∘ z) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4317 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = x ∘ (z ∘ y)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4439 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (x ∘ z) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4632 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (x ∘ z) ∘ y
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation470 (G : Type*) [Magma G] (h : Equation613 G) : Equation470 G := λ x y z => h x y x x z y
theorem Equation816_implies_Equation673 (G : Type*) [Magma G] (h : Equation816 G) : Equation673 G := λ x y z => h x y x x z y
theorem Equation1019_implies_Equation876 (G : Type*) [Magma G] (h : Equation1019 G) : Equation876 G := λ x y z => h x y x x z y
theorem Equation1222_implies_Equation1079 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1079 G := λ x y z => h x y x x z y
theorem Equation1425_implies_Equation1282 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1282 G := λ x y z => h x y x x z y
theorem Equation1628_implies_Equation1485 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1485 G := λ x y z => h x y x x z y
theorem Equation1831_implies_Equation1688 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1688 G := λ x y z => h x y x x z y
theorem Equation2034_implies_Equation1891 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1891 G := λ x y z => h x y x x z y
theorem Equation2237_implies_Equation2094 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2094 G := λ x y z => h x y x x z y
theorem Equation2440_implies_Equation2297 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2297 G := λ x y z => h x y x x z y
theorem Equation2643_implies_Equation2500 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2500 G := λ x y z => h x y x x z y
theorem Equation2846_implies_Equation2703 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2703 G := λ x y z => h x y x x z y
theorem Equation3049_implies_Equation2906 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2906 G := λ x y z => h x y x x z y
theorem Equation3252_implies_Equation3109 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3109 G := λ x y z => h x y x x z y
theorem Equation3455_implies_Equation3312 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3312 G := λ x y z => h x y x x z y
theorem Equation3658_implies_Equation3515 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3515 G := λ x y z => h x y x x z y
theorem Equation3861_implies_Equation3718 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3718 G := λ x y z => h x y x x z y
theorem Equation4064_implies_Equation3921 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3921 G := λ x y z => h x y x x z y
theorem Equation4267_implies_Equation4124 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4124 G := λ x y z => h x y x x z y
theorem Equation4379_implies_Equation4317 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4317 G := λ x y z => h x y x x z y
theorem Equation4582_implies_Equation4439 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4439 G := λ x y z => h x y x x z y
theorem Equation4694_implies_Equation4632 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4632 G := λ x y z => h x y x x z y