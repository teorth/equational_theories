import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation514 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (y ∘ (y ∘ y)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation717 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ ((y ∘ y) ∘ y))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation920 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ y) ∘ (y ∘ y))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1123 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ (y ∘ y)) ∘ y)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1326 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((y ∘ y) ∘ y) ∘ y)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1529 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (y ∘ (y ∘ y))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1732 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ ((y ∘ y) ∘ y)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1935 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ y)) ∘ (y ∘ y)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2138 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ y) ∘ (y ∘ y)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2341 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ (y ∘ y))) ∘ y
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2544 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((y ∘ y) ∘ y)) ∘ y
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2747 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ (y ∘ y)) ∘ y
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2950 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (y ∘ y)) ∘ y) ∘ y
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3153 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ y) ∘ y) ∘ y) ∘ y
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3356 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (y ∘ (y ∘ y))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3559 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ ((y ∘ y) ∘ y)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3762 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ y) ∘ (y ∘ y)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3965 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ (y ∘ y)) ∘ y
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4168 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((y ∘ y) ∘ y) ∘ y
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4483 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = (y ∘ y) ∘ y
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
theorem Equation613_implies_Equation514 (G : Type*) [Magma G] (h : Equation613 G) : Equation514 G := λ x y => h x y y y y y
theorem Equation816_implies_Equation717 (G : Type*) [Magma G] (h : Equation816 G) : Equation717 G := λ x y => h x y y y y y
theorem Equation1019_implies_Equation920 (G : Type*) [Magma G] (h : Equation1019 G) : Equation920 G := λ x y => h x y y y y y
theorem Equation1222_implies_Equation1123 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1123 G := λ x y => h x y y y y y
theorem Equation1425_implies_Equation1326 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1326 G := λ x y => h x y y y y y
theorem Equation1628_implies_Equation1529 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1529 G := λ x y => h x y y y y y
theorem Equation1831_implies_Equation1732 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1732 G := λ x y => h x y y y y y
theorem Equation2034_implies_Equation1935 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1935 G := λ x y => h x y y y y y
theorem Equation2237_implies_Equation2138 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2138 G := λ x y => h x y y y y y
theorem Equation2440_implies_Equation2341 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2341 G := λ x y => h x y y y y y
theorem Equation2643_implies_Equation2544 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2544 G := λ x y => h x y y y y y
theorem Equation2846_implies_Equation2747 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2747 G := λ x y => h x y y y y y
theorem Equation3049_implies_Equation2950 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2950 G := λ x y => h x y y y y y
theorem Equation3252_implies_Equation3153 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3153 G := λ x y => h x y y y y y
theorem Equation3455_implies_Equation3356 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3356 G := λ x y => h x y y y y y
theorem Equation3658_implies_Equation3559 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3559 G := λ x y => h x y y y y y
theorem Equation3861_implies_Equation3762 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3762 G := λ x y => h x y y y y y
theorem Equation4064_implies_Equation3965 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3965 G := λ x y => h x y y y y y
theorem Equation4267_implies_Equation4168 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4168 G := λ x y => h x y y y y y
theorem Equation4582_implies_Equation4483 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4483 G := λ x y => h x y y y y y