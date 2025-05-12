import equational_theories.Mathlib.Order.Greedy
import equational_theories.FreshGenerator
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic

namespace Eq1729

set_option autoImplicit true
set_option relaxedAutoImplicit true

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
  -- The squaring map on `SM`. In the blueprint this is `S`
  S : SM → SM
  L : SM → Equiv SM SM
  R : SM → Equiv SM SM
  -- A complement squaring map from `N` to `SM`. Since we don't have a
  -- magma operation for `N` yet, we will wait for the magma operation construction
  -- to prove a theorem that with the resulting magma operation `sqN` acts
  -- as a squaring function. In the blueprint this is `S'`
  S' : N → SM
  -- `rest_of_the_map` is a function that will serve as part of our binary operation
  -- which deals with the situation where both operands come from `N`.
  -- In the blueprint this is `◇'`
  rest_map : N → N → SM ⊕ N
  L' : SM → Equiv N N
  R' : SM → Equiv N N

structure ExtOpsWithProps (SM N : Type) [Magma SM] extends (ExtOps SM N) where
  -- Properties of functions on the small magma `SM`
  squaring_prop_SM : ∀ x : SM, S x = x ◇ x
  left_map_SM : ∀ x y : SM, L x y = x ◇ y
  right_map_SM : ∀ x y : SM, R x y = y ◇ x
  -- The small magma `SM` satisfies equation 1729
  SM_sat_1729 : Equation1729 SM
  axiom_1 : ∀ a, ∀ x, (L' a) x = ( (R' a).symm ∘ (L' (S a)).symm) x
  axiom_21 : ∀ a b : SM, ∀ y : N, a ≠ b → R' a y ≠ R' b y
  axiom_22 : ∀ a : SM, ∀ x, R' a x ≠ x
  -- Axiom 3
  -- axiom_3 : ∀ x y, ∀ a, R' a x = y → ((L' (S' y)) (L' ((R a).symm (S' x)) y)) = x
  axiom_3 : ∀ x y, ∀ a, R' a x = y → ((L' (S' y)) (L' ((L (S' x)).symm a) y)) = x
  -- Axiom 4
  axiom_4 : ∀ x : N, L' (S' x) (L' (S' x) x) = x
  -- Restmap axioms
  -- Axiom 5 the squaring property of `S'`
  axiom_5 : ∀ x, rest_map x x = .inl (S' x)
  -- Axiom 6
  axiom_6 : ∀ y : N, ∀ a : SM,
    rest_map (R' a y) y = .inl ((L (S' y)).symm a)
  axiom_7 : ∀ x y : N, ¬ x = y -- The condition for axiom 5 doesn't hold
    → ¬(∃ a : SM, x = R' a y)  -- The condition for axiom 6 doesn't hold
    → (∃ z, rest_map x y = .inr z ∧ rest_map z x =  (Sum.inr <| (L' (S' x)).symm y))

lemma axiom_1_alt [Magma SM] (E : ExtOpsWithProps SM N) :
  ∀ a, ∀ x, ((E.L' (E.S a)) ∘ (E.R' a) ∘ (E.L' a)) x = x := by
  intro a x
  simp [E.axiom_1 a x]

def operation {SM N : Type}
  [Magma SM] (E : ExtOpsWithProps SM N) (a b : SM ⊕ N) : SM ⊕ N :=
  match a,b with
  | .inl a, .inl b => .inl (a ◇ b)
  | .inl a, .inr b => .inr <| E.L' a b
  | .inr a, .inl b => .inr <| E.R' b a
  | .inr a, .inr b => E.rest_map a b

instance extMagmaInst {SM N : Type}
  [Magma SM] (E : ExtOpsWithProps SM N) : Magma (SM ⊕ N) where
  op := operation E

lemma Equiv_symm_inv : ∀ e : Equiv α β, e.symm.toFun = e.invFun := fun _ ↦ rfl

lemma ExtMagma_sat_eq1729 {SM N : Type} [Magma SM] [Inhabited SM] [Inhabited N]
  (E : ExtOpsWithProps SM N)
  : @Equation1729 (SM ⊕ N) (extMagmaInst E) := by
  intro x y
  cases hx : x
  <;> cases hy : y
  <;> simp only [Magma.op, operation]
  case inl.inl => simp [← E.SM_sat_1729]
  case inl.inr a z => simp [E.axiom_5, E.axiom_6, Sum.inl.injEq, ← E.left_map_SM]
    -- Note: axiom 1 weas not needed here. Unlike what the blueprint says.
  case inr.inl z a =>
    rw [← E.squaring_prop_SM]
    nth_rw 1 [← axiom_1_alt E a z]
    simp only [Function.comp_apply]
  case inr.inr x' y' =>
    by_cases hxy' : (y' = x') <;> simp_all [hxy', E.axiom_5]
    · rw [E.axiom_4]
    · by_cases ha2 : ∃ a, y' = E.R' a x'
      case pos =>
        obtain ⟨a, h2⟩ := ha2
        simp only [h2, E.axiom_6, Sum.inr.injEq]
        nth_rw 1 [← h2, ← h2]
        exact (E.axiom_3 _ _ _ (h2.symm)).symm
      case neg =>
        have := E.axiom_7 y' x' (fun hxy ↦ hxy' hxy) ha2
        aesop

lemma ExtMagma_unsat_eq817 {SM N : Type} [Magma SM]
  (E : ExtOpsWithProps SM N) [Inhabited N] [Inhabited SM]
  : ¬ @Equation817 (SM ⊕ N) (extMagmaInst E) := by
  intro H
  simp_all only [Sum.forall]
  cases H with
  | intro left right =>
      revert left
      conv => lhs; rhs; simp
      conv => left
      revert right
      conv => lhs; rhs; rhs; simp [Magma.op, operation, E.axiom_5, E.squaring_prop_SM]
      intro left _
      let x : N := Inhabited.default
      have h1 := E.axiom_22 ((E.S' x ◇ E.S' x)) x
      specialize left x
      injection left with left
      exact h1 left.symm

end Eq1729
