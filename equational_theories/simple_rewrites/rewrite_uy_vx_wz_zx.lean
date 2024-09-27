import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation487 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ (y ∘ x)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation690 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((z ∘ y) ∘ x))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation893 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ (y ∘ x))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1096 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (z ∘ y)) ∘ x)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1299 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ z) ∘ y) ∘ x)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1502 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ (y ∘ x))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1705 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((z ∘ y) ∘ x)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1908 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ (y ∘ x)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2111 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ (y ∘ x)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2314 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (z ∘ y))) ∘ x
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2517 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ z) ∘ y)) ∘ x
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2720 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (z ∘ y)) ∘ x
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2923 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ z)) ∘ y) ∘ x
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3126 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ z) ∘ y) ∘ x
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3329 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ (y ∘ x))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3532 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((z ∘ y) ∘ x)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3735 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ (y ∘ x)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3938 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (z ∘ y)) ∘ x
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4141 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ z) ∘ y) ∘ x
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4330 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = z ∘ (y ∘ x)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4456 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (z ∘ y) ∘ x
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4645 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (z ∘ y) ∘ x
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation487 (G : Type*) [Magma G] (h : Equation613 G) : Equation487 G := λ x y z => h x y x z y x
theorem Equation816_implies_Equation690 (G : Type*) [Magma G] (h : Equation816 G) : Equation690 G := λ x y z => h x y x z y x
theorem Equation1019_implies_Equation893 (G : Type*) [Magma G] (h : Equation1019 G) : Equation893 G := λ x y z => h x y x z y x
theorem Equation1222_implies_Equation1096 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1096 G := λ x y z => h x y x z y x
theorem Equation1425_implies_Equation1299 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1299 G := λ x y z => h x y x z y x
theorem Equation1628_implies_Equation1502 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1502 G := λ x y z => h x y x z y x
theorem Equation1831_implies_Equation1705 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1705 G := λ x y z => h x y x z y x
theorem Equation2034_implies_Equation1908 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1908 G := λ x y z => h x y x z y x
theorem Equation2237_implies_Equation2111 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2111 G := λ x y z => h x y x z y x
theorem Equation2440_implies_Equation2314 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2314 G := λ x y z => h x y x z y x
theorem Equation2643_implies_Equation2517 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2517 G := λ x y z => h x y x z y x
theorem Equation2846_implies_Equation2720 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2720 G := λ x y z => h x y x z y x
theorem Equation3049_implies_Equation2923 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2923 G := λ x y z => h x y x z y x
theorem Equation3252_implies_Equation3126 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3126 G := λ x y z => h x y x z y x
theorem Equation3455_implies_Equation3329 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3329 G := λ x y z => h x y x z y x
theorem Equation3658_implies_Equation3532 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3532 G := λ x y z => h x y x z y x
theorem Equation3861_implies_Equation3735 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3735 G := λ x y z => h x y x z y x
theorem Equation4064_implies_Equation3938 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3938 G := λ x y z => h x y x z y x
theorem Equation4267_implies_Equation4141 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4141 G := λ x y z => h x y x z y x
theorem Equation4379_implies_Equation4330 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4330 G := λ x y z => h x y x z y x
theorem Equation4582_implies_Equation4456 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4456 G := λ x y z => h x y x z y x
theorem Equation4694_implies_Equation4645 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4645 G := λ x y z => h x y x z y x