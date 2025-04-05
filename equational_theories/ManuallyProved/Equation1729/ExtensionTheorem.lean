import equational_theories.Mathlib.Order.Greedy
import equational_theories.FreshGenerator
import equational_theories.Equations.All
import equational_theories.FactsSyntax

import Mathlib.Tactic

namespace Eq1729

set_option autoImplicit true
#print Equation1729
#print Equation817
#print Magma





def injective (f : α → β) := ∀ x₁ x₂ : α, f x₁ = f x₂ → x₁ = x₂

def surjective (f : α → β) := ∀ y : β, ∃ x : α, f x = y

def bijective (f : α → β) := surjective f ∧ injective f

structure Invertible (f : α → β) where
  bij : bijective f
  inv : β → α
  inv_left : inv ∘ f = id
  inv_right : f ∘ inv = id

-- Tiny helper lemmas
lemma invmap_left (f : α → α) (finv : Invertible f) : ∀ x : α, finv.inv (f x) = x := by
  intro x
  simp_rw[←Function.comp_apply, finv.inv_left, id]

lemma invmap_right (f : α → α) (finv : Invertible f) : ∀ x : α, f (finv.inv x) = x := by
  intro x
  simp_rw [←Function.comp_apply, finv.inv_right, id]

/- This structure contains the pieces needed for extending an eq1729 obeying magma
to one that does not obey 817
-/

#print Sum

def extend_sum_inl (f : α → β) (γ : Type) : α → Sum β γ :=
  fun (x : α) => .inl (f x)

def extend_sum_inr (f : α → γ) (β : Type) : α → Sum β γ :=
  fun (x : α) => .inr (f x)



def combine (f : α → β) (g : γ → β) : Sum α γ → β :=
  fun x =>
    match x with
    | .inl xl => f xl
    | .inr xr => g xr

def extend_sum_both (f : α → β) (g : δ → γ) : Sum α δ → Sum β γ :=
  let f₁ := extend_sum_inl f γ
  let g₁ := extend_sum_inr g β
  combine f₁ g₁


def is_left_extension_of (f' : α → γ) (f : α ⊕ β → γ) : Prop :=
  ∀ x : α, f' x = f (.inl x)

def is_right_extension_of (f' : β → γ) (f : α ⊕ β → γ) : Prop :=
  ∀ x : β, f' x = f (.inr x)

structure ExtOps (SM N : Type) [Magma SM] where
  -- The extended magma
  -- EM : SM ⊕ N  -- it seems unnecesary to specify an element of SM ⊕ N, and this component caused problems in applications

  -- The squaring map on `SM`. In the blueprint this is `S`
  S : SM → SM
  L : SM → SM → SM
  R : SM → SM → SM

  -- A complement squaring map from `N` to `SM`. Since we don't have a
  -- magma operation for `N` yet, we will wait for the magma operation construction
  -- to prove a theorem that with the resulting magma operation `sqN` acts
  -- as a squaring function. In the blueprint this is `S'`
  S' : N → SM

  -- `rest_of_the_map` is a function that will serve as part of our binary operation
  -- which deals with the situation where both operands come from `N`.
  -- In the blueprint this is `◇'`
  rest_map : N → N → Sum SM N

  L' : SM → N → N

  R' : SM → N → N




structure ExtOpsWithProps (SM N : Type) [Magma SM] extends (ExtOps SM N) where

  -- Properties of functions on the small magma `SM`
  squaring_prop_SM : ∀ x : SM, S x = x ◇ x
  left_map_SM : ∀ x y : SM, L x y = x ◇ y
  right_map_SM : ∀ x y : SM, R x y = y ◇ x

  -- `sqN` extends `sqM`. This fairly trivial from type theory
  sqN_extends_sqM : is_right_extension_of S' (combine S S')

  L_inv : (a : SM) → Invertible (L a)
  -- The left mult operation is invertible
  L'_inv : (a : SM) → Invertible (L' a)

  R_inv : (a : SM) → Invertible (R a)
  -- The right mult operation is invertible
  R'_inv : (a : SM) →  Invertible (R' a)

  -- The small magma `SM` satisfies equation 1729
  SM_sat_1729 : Equation1729 SM

  axiom_1 : ∀ a : SM, (L' (S a)) ∘ (R' a) ∘ L' a = id

  axiom_21 : ∀ a b : SM, ∀ y : N, a ≠ b → R' a y ≠ R' b y
  axiom_22 : ∀ a : SM, ∀ x, R' a x ≠ x

  -- axiom 3
  axiom_3 : ∀ x y, ∀ a, R' a x = y → (L' (S' y) (L' ((R_inv (S' x)).inv a) y)) = x
  -- axiom 4
  axiom_4 : ∀ x : N, (L' (S' x) (L' (S' x) x)) = x

  -- restmap axioms

  -- axiom 5 the squaring property of `S'`
  axiom_5 : ∀ x, rest_map x x = .inl (S' x)

  -- axiom 6
  axiom_6 : ∀ y : N, ∀ a : SM,
    rest_map (R' a y) y = Sum.inl ((L_inv (S' y)).inv a)



def operation {SM N : Type}
  [Magma SM] (E : ExtOps SM N) (a b : SM ⊕ N) : SM ⊕ N :=
  match a,b with
  | .inl a, .inl b => .inl (a ◇ b)
  | .inl a, .inr b => .inr <| E.L' a b
  | .inr a, .inl b => .inr <| E.R' b a
  | .inr a, .inr b => E.rest_map a b

instance extMagmaInst {SM N : Type}
  [Magma SM] (E : ExtOpsWithProps SM N) : Magma (SM ⊕ N) where
  op := operation E.toExtOps


lemma ExtMagma_sat_eq1729 {SM N : Type} [Magma SM]
  (E : ExtOpsWithProps SM N)
  : @Equation1729 (SM ⊕ N) (extMagmaInst E) := by
  unfold Equation1729
  intro x y
  cases hx : x <;> cases hy : y <;> simp [Magma.op, operation]
  case inl.inl =>
    rw [←E.SM_sat_1729]
  case inl.inr a x =>
    symm
    simp[E.axiom_5, E.axiom_6]
    rw[←E.right_map_SM]
    sorry
  case inr.inl x b =>
    rw [←E.squaring_prop_SM]
    sorry
  case inr.inr x y =>
    rw[E.axiom_5]

    sorry



lemma ExtMagma_unsat_eq817 {SM N : Type} [Magma SM]
  (E : ExtOpsWithProps SM N)
  : ¬ @Equation817 (SM ⊕ N) (extMagmaInst E) := by
  intro H

  simp_all [Equation1729]
  cases H with
  | intro left right =>
      revert left
      conv =>
        lhs
        rhs
        simp [Magma.op, operation]
      conv =>
      intro left
      revert right
      conv =>
        lhs
        rhs
        rhs
        simp [Magma.op, operation, E.axiom_5, E.squaring_prop_SM]
      intro left right
      have h1 := E.axiom_22
      have h2 := E.axiom_21
      clear right



      sorry


end Eq1729
