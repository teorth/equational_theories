import equational_theories.EquationalResult
import equational_theories.Equations.All
import equational_theories.Mathlib.Order.Greedy
import Mathlib.GroupTheory.FreeGroup.Basic

instance (α : Type*) [DecidableEq α] [Encodable α] : Encodable (FreeGroup α) where
  encode x := Encodable.encode x.toWord
  decode n := Encodable.decode n |>.map FreeGroup.mk
  encodek x := by simp; exact x.mk_toWord

instance (α : Type*) [DecidableEq α] [Countable α] : Countable (FreeGroup α) := by
  haveI := Encodable.ofCountable α
  infer_instance

-- This has got to be in Mathlib somewhere
theorem relToFun {α : Type*} (R : α → α → Prop) (hd : ∀ x, ∃ y, R x y) (hf : ∀ x y z, R x y → R x z → y = z) :
    ∃ f : α → α, ∀ x y, f x = y ↔ R x y := by
  use fun x => (hd x).choose
  intro x y
  constructor
  · intro h; simp [←h, (hd x).choose_spec]
  · apply hf x _ y (hd x).choose_spec

namespace Eq879

abbrev G := FreeGroup Nat

def func_eq879  (f : G → G) := ∀ x, f (f (f 1 * (f x)⁻¹) * f x * x⁻¹) = x⁻¹
def func_eq4065 (f : G → G) := 1 = f ((f 1)⁻¹ * (f ((f 1)⁻¹))⁻¹) * f ((f 1)⁻¹)

structure PartialSolution where
  E : G → G → Prop
  x₁ : G
  support : Finset G
  mem_1 : ∀ a b, E a b → a ∈ support
  mem_2 : ∀ a b, E a b → b ∈ support
  isFun : ∀ a b c, E a b → E a c → b = c
  atOne : E 1 x₁
  cond4 : ∀ a b, E a b → ¬E (x₁ * a) (x₁ * b)
  cond5 : ∀ a a' b c, E a b → E a' b → E (x₁ * a) c → E (x₁ * a') c → a = a'
  cond6 : ∀ a b c, E a b → E (x₁ * b⁻¹) c → E (c * b * a⁻¹) a⁻¹

instance : Preorder PartialSolution where
  le s t := ∀ a b, s.E a b → t.E a b
  le_refl := by simp
  le_trans := by simp_all

def PartialSolution.dom (sol : PartialSolution) : Set G :=
  { x | ∃ y, sol.E x y }

-- The heart of the proof, Lemma 1.1 in
--    https://leanprover.zulipchat.com/user_uploads/3121/-Y2DILKZP-OuhxcU0HS-EHge/Equation879.pdf
def extend (sol : PartialSolution) (x : G) : { sol' // sol ≤ sol' ∧ x ∈ sol'.dom } :=
  sorry

theorem exists_full_solution (seed : PartialSolution) :
    ∃ f : G → G, func_eq879 f ∧ ∀ a b, seed.E a b → f a = b := by
  have ⟨c, hc, _, _, h3⟩ := exists_greedy_chain
    (fun x => { sol : PartialSolution | x ∈ sol.dom })
    (fun sol x => let ⟨sol', h⟩ := extend sol x; ⟨sol', by simp [h]⟩)
    seed

  let E a b := ∃ sol ∈ c, sol.E a b
  have hdom : ∀ x, ∃ y, E x y := by intro x; choose sol _ y _ using h3 x; use y, sol
  have isFun : ∀ x y z, E x y → E x z → y = z := by
    intro x y z ⟨sxy, hsxy, hxy⟩ ⟨sxz, hsxz, hxz⟩
    have ⟨s, sy, sz⟩ : ∃ s, sxy ≤ s ∧ sxz ≤ s := by
      cases hc.total hsxy hsxz; use sxz; use sxy
    exact s.isFun x y z (sy x y hxy) (sz x z hxz)
  let ⟨f, hf⟩ := relToFun E hdom isFun

  have : func_eq879 f := by
    suffices h : ∀ x y z, f x = y → f (f 1 * y⁻¹) = z → f (z * y * x⁻¹) = x⁻¹ by simp [func_eq879, h]
    simp [hf]
    intro x y z ⟨sxy, hsxy, hxy⟩ ⟨swz, hswz, hwz⟩
    have ⟨s, hs, hsab, hswz⟩ : ∃ s ∈ c, sxy ≤ s ∧ swz ≤ s := by
      cases hc.total hsxy hswz; use swz; use sxy
    have : f 1 = s.x₁ := by simp [hf]; use s, hs, s.atOne
    rw [this] at hwz
    have _ := s.cond6 x y z (hsab _ _ hxy) (hswz _ _ hwz)
    use s

  have (a b : G) (h : seed.E a b) : f a = b := by simp [hf]; use seed

  use f

def g₁ : G := FreeGroup.of 1
def g₂ : G := FreeGroup.of 2
def g₃ : G := FreeGroup.of 3

def seed : PartialSolution where
  E a b := (a, b) ∈ ({(1, g₁), (g₁ * g₁, 1), (g₁⁻¹, g₂), (g₁⁻¹ * g₂⁻¹, g₃)} : Finset _)
  x₁ := g₁
  support := {1, g₁, g₁ * g₁, g₁⁻¹, g₂, g₁⁻¹ * g₂⁻¹, g₃}
  mem_1 := by aesop
  mem_2 := by aesop
  isFun := by aesop; repeat contradiction
  atOne := by simp
  cond4 := by sorry
  cond5 := by sorry
  cond6 := by sorry

-- @[equational_result]
theorem Equation879_not_implies_Equation4065 :
    ∃ (G: Type) (_: Magma G), Equation879 G ∧ ¬ Equation4065 G := by

  let ⟨f, h879, h⟩ := exists_full_solution seed
  use G, {op := fun x y => f (y * x⁻¹) * x}

  have values : f 1 = g₁ ∧ f g₁⁻¹ = g₂ ∧ f (g₁⁻¹ * g₂⁻¹) = g₃ := by
    repeat first | constructor | apply h; simp [seed]
  have h4065 : ¬func_eq4065 f := by simp [func_eq4065, values]; decide

  constructor
  · intro x y
    have h := congrArg (· * y) <| h879 (y * x⁻¹)
    simp_all [mul_assoc]
  · by_contra h
    let h := congrArg (· * (f 1)⁻¹) <| h 1
    simp [mul_assoc] at h
    contradiction
