import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation577 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (y ∘ z)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation780 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ y) ∘ z))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation983 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (y ∘ z))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1186 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ y)) ∘ z)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1389 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ y) ∘ z)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1592 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (y ∘ z))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1795 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ y) ∘ z)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1998 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (y ∘ z)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2201 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (y ∘ z)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2404 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ y))) ∘ z
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2607 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ y)) ∘ z
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2810 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ y)) ∘ z
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation3013 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ y) ∘ z
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3216 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ y) ∘ z
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3419 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (y ∘ z))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3622 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ y) ∘ z)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3825 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (y ∘ z)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation4028 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ y)) ∘ z
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4231 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ y) ∘ z
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4546 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ y) ∘ z
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation577 (G : Type*) [Magma G] (h : Equation613 G) : Equation577 G := λ x y z => h x y z z y z
theorem Equation816_implies_Equation780 (G : Type*) [Magma G] (h : Equation816 G) : Equation780 G := λ x y z => h x y z z y z
theorem Equation1019_implies_Equation983 (G : Type*) [Magma G] (h : Equation1019 G) : Equation983 G := λ x y z => h x y z z y z
theorem Equation1222_implies_Equation1186 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1186 G := λ x y z => h x y z z y z
theorem Equation1425_implies_Equation1389 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1389 G := λ x y z => h x y z z y z
theorem Equation1628_implies_Equation1592 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1592 G := λ x y z => h x y z z y z
theorem Equation1831_implies_Equation1795 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1795 G := λ x y z => h x y z z y z
theorem Equation2034_implies_Equation1998 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1998 G := λ x y z => h x y z z y z
theorem Equation2237_implies_Equation2201 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2201 G := λ x y z => h x y z z y z
theorem Equation2440_implies_Equation2404 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2404 G := λ x y z => h x y z z y z
theorem Equation2643_implies_Equation2607 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2607 G := λ x y z => h x y z z y z
theorem Equation2846_implies_Equation2810 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2810 G := λ x y z => h x y z z y z
theorem Equation3049_implies_Equation3013 (G : Type*) [Magma G] (h : Equation3049 G) : Equation3013 G := λ x y z => h x y z z y z
theorem Equation3252_implies_Equation3216 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3216 G := λ x y z => h x y z z y z
theorem Equation3455_implies_Equation3419 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3419 G := λ x y z => h x y z z y z
theorem Equation3658_implies_Equation3622 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3622 G := λ x y z => h x y z z y z
theorem Equation3861_implies_Equation3825 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3825 G := λ x y z => h x y z z y z
theorem Equation4064_implies_Equation4028 (G : Type*) [Magma G] (h : Equation4064 G) : Equation4028 G := λ x y z => h x y z z y z
theorem Equation4267_implies_Equation4231 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4231 G := λ x y z => h x y z z y z
theorem Equation4582_implies_Equation4546 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4546 G := λ x y z => h x y z z y z