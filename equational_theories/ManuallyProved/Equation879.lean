import equational_theories.EquationalResult
import equational_theories.Equations.All
import equational_theories.Mathlib.Order.Greedy
import Mathlib.GroupTheory.FreeGroup.Basic

-- Formalization of
--    https://leanprover.zulipchat.com/user_uploads/3121/-Y2DILKZP-OuhxcU0HS-EHge/Equation879.pdf

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

theorem le_x₁ (sol sol' : PartialSolution) (h : sol ≤ sol') : sol.x₁ = sol'.x₁ :=
  sol'.isFun _ _ _ (h _ _ sol.atOne) sol'.atOne

def PartialSolution.dom (sol : PartialSolution) : Set G :=
  { x | ∃ y, sol.E x y }

def PartialSolution.satisfies_func_eq879 (sol : PartialSolution) (x : G) :=
  ∃ y z, sol.E x y ∧ sol.E (sol.x₁ * y⁻¹) z -- ∧ sol.E (z * y * x⁻¹) x⁻¹

theorem satisfies_func_eq879_dom (sol : PartialSolution) (x : G) (h : sol.satisfies_func_eq879 x) : x ∈ sol.dom := by
  choose y _ _ _ using h
  use y

def extend_case1 (sol : PartialSolution) (a : G) (h : a ∈ sol.dom) :
    { sol' // sol ≤ sol' ∧ sol'.satisfies_func_eq879 a ∧ ∃ b, sol'.E a b ∧ (sol'.x₁ * b⁻¹) ∈ sol'.dom } := by
  sorry

def extend (sol : PartialSolution) (a : G) : { sol' // sol ≤ sol' ∧ sol'.satisfies_func_eq879 a } := by
  by_cases h : a ∈ sol.dom
  · have ⟨sol', _, _, _⟩ := extend_case1 sol a h
    use sol'
  · by_cases h2 : ∃ z, sol.E z (a⁻¹ * sol.x₁)
    · choose z hz using h2
      have ⟨sol', hle, _, hdom⟩ := extend_case1 sol z ⟨_, hz⟩
      have ⟨sol'', hle', _, _⟩ := extend_case1 sol' a <| by
        choose b hzb hbdom using hdom
        rw [le_x₁ _ _ hle] at hz
        apply hle at hz
        have ha : a = sol'.x₁ * b⁻¹ := by
          simp [congrArg (a * · * b⁻¹),
                sol'.isFun z b _ hzb hz]
        simp [hbdom, ha]
      have : sol ≤ sol'' := le_trans hle hle'
      use sol''
    · sorry

theorem exists_full_solution (seed : PartialSolution) :
    ∃ f : G → G, func_eq879 f ∧ ∀ a b, seed.E a b → f a = b := by
  have ⟨c, hc, _, _, h3⟩ := exists_greedy_chain
    (fun a => { sol : PartialSolution | sol.satisfies_func_eq879 a })
    (fun sol a => let ⟨sol', h⟩ := extend sol a; ⟨sol', by simp [h]⟩)
    seed

  let E a b := ∃ sol ∈ c, sol.E a b
  have hdom : ∀ a, ∃ b, E a b := by
    intro a
    choose sol _ b heq using h3 a
    have : sol.E a b := heq.choose_spec.1
    use b, sol
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
