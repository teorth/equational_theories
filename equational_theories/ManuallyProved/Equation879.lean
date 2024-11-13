import equational_theories.EquationalResult
import equational_theories.Equations.All
import equational_theories.Mathlib.Order.Greedy
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Rel
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Order.Defs
import Mathlib.Tactic.ITauto

-- These two should go in Mathlib

instance (α : Type*) [DecidableEq α] [Encodable α] : Encodable (FreeGroup α) where
  encode x := Encodable.encode x.toWord
  decode n := Encodable.decode n |>.map FreeGroup.mk
  encodek x := by simp; exact x.mk_toWord

instance (α : Type*) [DecidableEq α] [Countable α] : Countable (FreeGroup α) := by
  haveI := Encodable.ofCountable α
  infer_instance

def G := FreeGroup Nat

-- TODO: figure out why these need to be declared here
instance : Group G := FreeGroup.instGroup
instance : DecidableEq G := FreeGroup.instDecidableEq
instance : Countable G := instCountableFreeGroupOfDecidableEq_equational_theories Nat

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

-- The heart of the proof, Lemma 1.1 in
--    https://leanprover.zulipchat.com/user_uploads/3121/-Y2DILKZP-OuhxcU0HS-EHge/Equation879.pdf
def extend (sol : PartialSolution) (x : G) : { sol' // sol ≤ sol' ∧ ∃ y, sol'.E x y } :=
  sorry

theorem exists_full_solution (seed : PartialSolution) :
    ∃ f : G → G, func_eq879 f ∧ ∀ a b, seed.E a b → f a = b := by
  have ⟨c, hc, h1, _, h3⟩ := exists_greedy_chain
    (fun x => {sol : PartialSolution | ∃ y, sol.E x y})
    (fun sol x => let ⟨sol', h⟩ := extend sol x; ⟨sol', by simp [h]⟩)
    seed
  let E a b := ∃ sol ∈ c, sol.E a b

  have isFun : ∀ x y z, E x y → E x z → y = z := by
    intro x y z ⟨sxy, hsxy, hxy⟩ ⟨sxz, hsxz, hxz⟩
    have : ∃ s, sxy ≤ s ∧ sxz ≤ s := by
      cases hc.total hsxy hsxz; use sxz; use sxy
    let ⟨s, sy, sz⟩ := this
    exact s.isFun x y z (sy x y hxy) (sz x z hxz)

  have hdom x : ∃ y, E x y := by choose step _ y _ using h3 x; use y, step
  let f x := (hdom x).choose
  have hf {x y} : E x y → f x = y := isFun x (f x) y (hdom x).choose_spec
  have hf' {x y} (fxy : f x = y) : E x y := by
    let ⟨s, _, h⟩ := (hdom x).choose_spec
    unfold f at fxy
    rw [fxy] at h
    use s

  have cond6 : ∀ x y z, E x y → E (f 1 * y⁻¹) z → E (z * y * x⁻¹) x⁻¹ := by
    intro x y z ⟨sxy, hsxy, hxy⟩ ⟨swz, hswz, hwz⟩
    have : ∃ s ∈ c, sxy ≤ s ∧ swz ≤ s := by
      cases hc.total hsxy hswz; use swz; use sxy
    let ⟨s, hs, hsab, hswz⟩ := this
    have : f 1 = s.x₁ := by apply hf; use s, hs, s.atOne
    rw [this] at hwz
    have c6 := s.cond6 x y z (hsab _ _ hxy) (hswz _ _ hwz)
    use s

  have : func_eq879 f := by
    intro x
    apply hf
    apply cond6 x (f x) (f (f 1 * (f x)⁻¹))
    repeat simp [hf']

  have : ∀ a b, seed.E a b → f a = b := by
    intro a b h
    apply hf
    use seed

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
    repeat first
    | constructor
    | apply h; simp [seed]
  have h4065 : ¬func_eq4065 f := by simp [func_eq4065, values]; decide

  constructor
  · intro x y
    have h := congrArg (· * y) <| h879 (y * x⁻¹)
    simp_all [mul_assoc]
  · by_contra h
    let h := congrArg (· * (f 1)⁻¹) <| h 1
    simp [mul_assoc] at h
    contradiction
