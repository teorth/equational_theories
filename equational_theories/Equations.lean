import equational_theories.Magma
import Mathlib.Tactic

/- List of equational laws being studied -/

/-- The reflexive law -/
def Equation1 (G: Type*) [Magma G] := ∀ x : G, x = x

/-- The singleton law -/
def Equation2 (G: Type*) [Magma G] := ∀ x y : G, x = y

/-- The idempotence law -/
def Equation3 (G: Type*) [Magma G] := ∀ x : G, x = x ∘ x

/-- The left absorption law -/
def Equation4 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ y

/-- The right absorption law -/
def Equation5 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ x

@[inherit_doc Equation2]
def Equation6 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ y

@[inherit_doc Equation2]
def Equation7 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ z

def Equation8 (G: Type*) [Magma G] := ∀ x : G, x = x ∘ (x ∘ x)

/-- value of multiplication is independent of right argument -/
def Equation38 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ y

/-- value of multiplication is independent of left argument; dual of 38 -/
def Equation39 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ x

/-- all squares are the same -/
def Equation40 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ y

/-- all products are the same -/
def Equation41 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ z

@[inherit_doc Equation38]
def Equation42 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ z

/-- The commutative law -/
def Equation43 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ x

/-- The constant law -/
def Equation46 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ w

/-- The central groupoid law -/
def Equation168 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (x ∘ z)

def Equation387 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ y) ∘ x

/-- The associative law -/
def Equation4512 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ y) ∘ z

def Equation4513 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ y) ∘ w

def Equation4522 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (x ∘ w) ∘ u

/-- all products of three values are the same, regardless bracketing -/
def Equation4582 (G: Type*) [Magma G] := ∀ x y z w u v: G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
