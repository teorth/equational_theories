import equational_theories.Magma
import Mathlib.Tactic

/- List of equational laws being studied -/
inductive Equation: Type :=
| e1 | e2 | e3 | e4 | e5 | e6 | e7 | e8 | e38 | e39
| e40 | e41 | e42 | e43 | e46 | e168 | e387 | e4512 | e4513 | e4522 | e4582

def Equation.interp (G: Type*) [Magma G] (e: Equation): Prop :=
  match e with
  /- The reflexive law -/
  | .e1 => ∀ x : G, x = x
  /- The singleton law -/
  | .e2 => ∀ x y : G, x = y
  | .e3 => ∀ x : G, x = x ∘ x
  /- The left absorption law -/
  | .e4 => ∀ x y : G, x = x ∘ y
  /- The right absorption law -/
  | .e5 => ∀ x y : G, x = y ∘ x
  | .e6 => ∀ x y : G, x = y ∘ y
  | .e7 => ∀ x y z : G, x = y ∘ z
  | .e8 => ∀ x : G, x = x ∘ (x ∘ x)
  | .e38 => ∀ x y : G, x ∘ x = x ∘ y
  | .e39 => ∀ x y : G, x ∘ x = y ∘ x
  | .e40 => ∀ x y : G, x ∘ x = y ∘ y
  | .e41 => ∀ x y z : G, x ∘ x = y ∘ z
  | .e42 => ∀ x y z : G, x ∘ y = x ∘ z
  | _ => False

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
