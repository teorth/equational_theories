import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation535 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (w ∘ w)))
def Equation613 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
def Equation738 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ w) ∘ w))
def Equation816 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
def Equation941 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (w ∘ w))
def Equation1019 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
def Equation1144 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ w)) ∘ w)
def Equation1222 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
def Equation1347 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ w) ∘ w)
def Equation1425 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
def Equation1550 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (w ∘ w))
def Equation1628 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
def Equation1753 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ w) ∘ w)
def Equation1831 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
def Equation1956 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (w ∘ w)
def Equation2034 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
def Equation2159 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (w ∘ w)
def Equation2237 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
def Equation2362 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ w))) ∘ w
def Equation2440 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
def Equation2565 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ w)) ∘ w
def Equation2643 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
def Equation2768 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ w)) ∘ w
def Equation2846 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
def Equation2971 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ w) ∘ w
def Equation3049 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
def Equation3174 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ w) ∘ w
def Equation3252 (G: Type*) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
def Equation3377 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (w ∘ w))
def Equation3455 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
def Equation3580 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ w) ∘ w)
def Equation3658 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
def Equation3783 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (w ∘ w)
def Equation3861 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
def Equation3986 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ w)) ∘ w
def Equation4064 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
def Equation4189 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ w) ∘ w
def Equation4267 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
def Equation4355 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = z ∘ (w ∘ w)
def Equation4379 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
def Equation4504 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ w) ∘ w
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
def Equation4670 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ y = (z ∘ w) ∘ w
def Equation4694 (G: Type*) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
theorem Equation613_implies_Equation535 (G : Type*) [Magma G] (h : Equation613 G) : Equation535 G := λ x y z w => h x y y z w w
theorem Equation816_implies_Equation738 (G : Type*) [Magma G] (h : Equation816 G) : Equation738 G := λ x y z w => h x y y z w w
theorem Equation1019_implies_Equation941 (G : Type*) [Magma G] (h : Equation1019 G) : Equation941 G := λ x y z w => h x y y z w w
theorem Equation1222_implies_Equation1144 (G : Type*) [Magma G] (h : Equation1222 G) : Equation1144 G := λ x y z w => h x y y z w w
theorem Equation1425_implies_Equation1347 (G : Type*) [Magma G] (h : Equation1425 G) : Equation1347 G := λ x y z w => h x y y z w w
theorem Equation1628_implies_Equation1550 (G : Type*) [Magma G] (h : Equation1628 G) : Equation1550 G := λ x y z w => h x y y z w w
theorem Equation1831_implies_Equation1753 (G : Type*) [Magma G] (h : Equation1831 G) : Equation1753 G := λ x y z w => h x y y z w w
theorem Equation2034_implies_Equation1956 (G : Type*) [Magma G] (h : Equation2034 G) : Equation1956 G := λ x y z w => h x y y z w w
theorem Equation2237_implies_Equation2159 (G : Type*) [Magma G] (h : Equation2237 G) : Equation2159 G := λ x y z w => h x y y z w w
theorem Equation2440_implies_Equation2362 (G : Type*) [Magma G] (h : Equation2440 G) : Equation2362 G := λ x y z w => h x y y z w w
theorem Equation2643_implies_Equation2565 (G : Type*) [Magma G] (h : Equation2643 G) : Equation2565 G := λ x y z w => h x y y z w w
theorem Equation2846_implies_Equation2768 (G : Type*) [Magma G] (h : Equation2846 G) : Equation2768 G := λ x y z w => h x y y z w w
theorem Equation3049_implies_Equation2971 (G : Type*) [Magma G] (h : Equation3049 G) : Equation2971 G := λ x y z w => h x y y z w w
theorem Equation3252_implies_Equation3174 (G : Type*) [Magma G] (h : Equation3252 G) : Equation3174 G := λ x y z w => h x y y z w w
theorem Equation3455_implies_Equation3377 (G : Type*) [Magma G] (h : Equation3455 G) : Equation3377 G := λ x y z w => h x y y z w w
theorem Equation3658_implies_Equation3580 (G : Type*) [Magma G] (h : Equation3658 G) : Equation3580 G := λ x y z w => h x y y z w w
theorem Equation3861_implies_Equation3783 (G : Type*) [Magma G] (h : Equation3861 G) : Equation3783 G := λ x y z w => h x y y z w w
theorem Equation4064_implies_Equation3986 (G : Type*) [Magma G] (h : Equation4064 G) : Equation3986 G := λ x y z w => h x y y z w w
theorem Equation4267_implies_Equation4189 (G : Type*) [Magma G] (h : Equation4267 G) : Equation4189 G := λ x y z w => h x y y z w w
theorem Equation4379_implies_Equation4355 (G : Type*) [Magma G] (h : Equation4379 G) : Equation4355 G := λ x y z w => h x y y z w w
theorem Equation4582_implies_Equation4504 (G : Type*) [Magma G] (h : Equation4582 G) : Equation4504 G := λ x y z w => h x y y z w w
theorem Equation4694_implies_Equation4670 (G : Type*) [Magma G] (h : Equation4694 G) : Equation4670 G := λ x y z w => h x y y z w w