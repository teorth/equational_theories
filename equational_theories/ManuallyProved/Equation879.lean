import equational_theories.EquationalResult
import equational_theories.Equations.All
import equational_theories.Mathlib.Order.Greedy
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Tactic.Group

-- Formalization of
--    https://leanprover.zulipchat.com/user_uploads/3121/-Y2DILKZP-OuhxcU0HS-EHge/Equation879.pdf

instance (α : Type*) [DecidableEq α] [Encodable α] : Encodable (FreeGroup α) where
  encode x := Encodable.encode x.toWord
  decode n := Encodable.decode n |>.map FreeGroup.mk
  encodek x := by simp; exact x.mk_toWord

instance (α : Type*) [DecidableEq α] [Countable α] : Countable (FreeGroup α) := by
  haveI := Encodable.ofCountable α
  infer_instance

instance (α : Type*) [DecidableEq α] [Nonempty α] : Infinite (FreeGroup α) :=
  let a := Nonempty.some (by assumption)
  Infinite.of_injective (FreeGroup.of a ^ ·) <| by
    intro _ _ h
    apply congrArg FreeGroup.norm at h
    simp [FreeGroup.norm_of_pow] at h
    exact h

theorem toWord_prod {α} [DecidableEq α] {x y : FreeGroup α} :
    (x * y).toWord = FreeGroup.reduce (x.toWord ++ y.toWord) := by
  rcases x
  rcases y
  simp [FreeGroup.prod_mk]
  exact FreeGroup.reduce.eq_of_red (FreeGroup.Red.append_append FreeGroup.reduce.red FreeGroup.reduce.red)

def generatorNames {α} [DecidableEq α] (x : FreeGroup α) : Finset α :=
  (x.toWord.map Prod.fst).toFinset

def FreeGroup.generators {α} [DecidableEq α] (x : FreeGroup α) : Finset (FreeGroup α) :=
  (generatorNames x).map ⟨FreeGroup.of, FreeGroup.of_injective⟩

def finset_generators {α} [DecidableEq α] (A : Finset (FreeGroup α)) : Finset (FreeGroup α) :=
  A.biUnion FreeGroup.generators

theorem generators_of {α} [DecidableEq α] (g : α) : (FreeGroup.of g).generators = {FreeGroup.of g} := by
  aesop

theorem generators_mul {α} [DecidableEq α] (a b : FreeGroup α) :
    (a * b).generators ⊆ a.generators ∪ b.generators := by
  simp [FreeGroup.generators, generatorNames]
  rw [←Finset.map_union, ←List.toFinset_append, ←List.map_append, toWord_prod]
  rw [Finset.map_subset_map]
  sorry

theorem generators_inv {α} [DecidableEq α] (a : FreeGroup α) :
    a⁻¹.generators = a.generators := by
  rw [FreeGroup.generators, generatorNames, FreeGroup.toWord_inv, FreeGroup.invRev]
  aesop

theorem generators_closure {α} [DecidableEq α] (A : Finset (FreeGroup α))
    (x : FreeGroup α) (h : x ∈ Subgroup.closure A) : x.generators ⊆ finset_generators A := by
  induction h using Subgroup.closure_induction with
  | mem a ha => intro _ _; simp [finset_generators]; have := ha.out; use a
  | one => simp [FreeGroup.generators, generatorNames]
  | mul _ _ _ _ iha ihb =>
    exact subset_trans (generators_mul _ _) (Finset.union_subset iha ihb)
  | inv _ _ ih => rw [generators_inv]; exact ih

-- TODO: make this computable for well-ordered α
noncomputable def freshGenerator {α} [DecidableEq α] [Infinite α] (A : Finset (FreeGroup α)) : FreeGroup α :=
  let existsFreshName := Finset.exists_not_mem (A.biUnion generatorNames)
  FreeGroup.of (existsFreshName.choose)

-- Should be a standard tactic but I can't find it
-- theorem inferNeg {α : Type} {x y : α} (p : α → Prop) (hx : p x) (hy : ¬p y) : ¬ (x = y) := by
--   by_contra hc
--   rw [hc] at hx
--   exact hy hx

@[simp]
theorem freshGenerator_not_mem' {α} [DecidableEq α] [Infinite α] (A : Finset (FreeGroup α)) :
    freshGenerator A ∉ finset_generators A := by
  simp [finset_generators, Finset.mem_biUnion, freshGenerator, FreeGroup.generators]
  intro x hx y hy
  simp [FreeGroup.of_injective, Function.Injective.eq_iff]
  have spec := (Finset.exists_not_mem (A.biUnion generatorNames)).choose_spec
  aesop

theorem freshGenerator_generators {α} [DecidableEq α] [Infinite α] (A : Finset (FreeGroup α)) :
    (freshGenerator A).generators = { freshGenerator A } := by
  simp [freshGenerator, generators_of]

@[simp]
theorem freshGenerator_not_in_span {α} [DecidableEq α] [Infinite α] (A : Finset (FreeGroup α)) :
    freshGenerator A ∉ Subgroup.closure A := by
  intro h
  apply generators_closure at h
  simp [freshGenerator_generators] at h
  exact freshGenerator_not_mem' _ h

-- TODO: do we need this?
@[simp]
theorem freshGenerator_not_in_span' {α} [DecidableEq α] [Infinite α] (A : Finset (FreeGroup α))
    (x : FreeGroup α) (h : x ∈ Subgroup.closure A) : freshGenerator A ∉ x.generators := by
  sorry

@[simp]
theorem Subgroup.subset_closure' {α} [Group α] {k : Set α} : ∀ x ∈ k, x ∈ Subgroup.closure k := Subgroup.subset_closure

@[simp]
theorem freshGenerator_not_mem {α} [DecidableEq α] [Infinite α] (A : Finset (FreeGroup α)) :
    freshGenerator A ∉ A := by
  apply mt (Subgroup.subset_closure' _)
  exact freshGenerator_not_in_span A

theorem closure_subset {G} [Group G] {A B : Set G} (h : A ⊆ B) (x : G) (hx : x ∈ Subgroup.closure A) : x ∈ Subgroup.closure B := by
  simp [Subgroup.closure] at *
  intro p hB
  apply hx p (subset_trans h hB)

-- This has got to be in Mathlib somewhere
theorem relToFun {α : Type*} (R : α → α → Prop) (hd : ∀ x, ∃ y, R x y) (hf : ∀ x y z, R x y → R x z → y = z) :
    ∃ f : α → α, ∀ x y, f x = y ↔ R x y := by
  use fun x => (hd x).choose
  intro x y
  constructor
  · intro h; simp [←h, (hd x).choose_spec]
  · exact hf x _ y (hd x).choose_spec

theorem eq_contr {α : Type*} {p : α → Prop} {x y : α} (hx : p x) (hy : ¬p y) : x ≠ y := by
  by_contra hc
  rw [hc] at hx
  exact hy hx

namespace Eq879

abbrev G := FreeGroup Nat

structure PartialFunction where
  E : G → G → Prop
  support : Finset G
  support_1 : ∀ {a b}, E a b → a ∈ support
  support_2 : ∀ {a b}, E a b → b ∈ support
  coherence : ∀ {a b c}, E a b → E a c → b = c
  x₁ : G
  cond3 : E 1 x₁

instance : Preorder PartialFunction where
  le f g := ∀ a b, f.E a b → g.E a b
  le_refl := by simp
  le_trans := by simp_all

def PartialFunction.dom (f : PartialFunction) : Set G :=
  { a | ∃ b, f.E a b }

def PartialFunction.im (f : PartialFunction) : Set G :=
  { b | ∃ a, f.E a b }

@[simp]
theorem mem_dom (f : PartialFunction) : ∀ a, a ∈ f.dom ↔ ∃ b, f.E a b := by simp [PartialFunction.dom]

@[simp]
theorem mem_im (f : PartialFunction) : ∀ b, b ∈ f.im ↔ ∃ a, f.E a b := by simp [PartialFunction.im]

@[simp]
theorem le_E {f f' : PartialFunction} {a b : G} (h : f ≤ f') : f.E a b → f'.E a b := by
  simp [instPreorderPartialFunction] at h
  apply h

theorem le_x₁ {f f' : PartialFunction} (h : f ≤ f') : f.x₁ = f'.x₁ :=
  f'.coherence (h _ _ f.cond3) f'.cond3

@[simp]
theorem dom_subset_support (f : PartialFunction) : f.dom ⊆ f.support :=
  fun _ ⟨_, h⟩ => f.support_1 h

@[simp]
theorem im_subset_support (f : PartialFunction) : f.im ⊆ f.support :=
  fun _ ⟨_, h⟩ => f.support_2 h

@[simp]
theorem x₁_mem_im (f : PartialFunction) : f.x₁ ∈ f.im :=
  ⟨1, f.cond3⟩

def PartialFunction.extend (f : PartialFunction) (a b : G) (ha : a ∉ f.dom) : PartialFunction :=
  let E x y := f.E x y ∨ x = a ∧ y = b
  let support := f.support ∪ {a, b}
  have support_1 {x y} (h : E x y) : x ∈ support := by
    simp [support]
    cases h; apply f.support_1 at h; tauto; tauto
  have support_2 {x y} (h : E x y) : y ∈ support := by
    -- cases h; repeat simp_all [support, f.support_2]
    simp [support]
    cases h with
    | inl h => simp [f.support_2 h]
    | inr => tauto
  have coherence {x y z} : E x y → E x z → y = z := by
    by_cases x = a
    · simp_all [E, PartialFunction.dom]
    · simp_all [E]; apply f.coherence
  ⟨E, support, support_1, support_2, coherence, f.x₁, by simp [E, f.cond3]⟩

@[simp]
theorem extend_le (f : PartialFunction) (a b : G) (ha : a ∉ f.dom) :
    f ≤ f.extend a b ha := by
  simp [PartialFunction.extend]
  tauto

def func_eq879  (f : G → G) := ∀ x, f (f (f 1 * (f x)⁻¹) * f x * x⁻¹) = x⁻¹
def func_eq4065 (f : G → G) := 1 = f ((f 1)⁻¹ * (f ((f 1)⁻¹))⁻¹) * f ((f 1)⁻¹)

def cond4 (f : PartialFunction) :=
  ∀ a b, f.E a b → ¬f.E (f.x₁ * a) (f.x₁ * b)
def cond5 (f : PartialFunction) :=
  ∀ a a' b c, f.E a b → f.E a' b → f.E (f.x₁ * a) c → f.E (f.x₁ * a') c → a = a'
def cond6 (f : PartialFunction) :=
  ∀ a b c, f.E a b → f.E (f.x₁ * b⁻¹) c → f.E (c * b * a⁻¹) a⁻¹

structure PartialSolution extends PartialFunction where
  cond4 : ∀ a b, E a b → ¬E (x₁ * a) (x₁ * b)
  cond5 : ∀ a a' b c, E a b → E a' b → E (x₁ * a) c → E (x₁ * a') c → a = a'
  cond6 : ∀ a b c, E a b → E (x₁ * b⁻¹) c → E (c * b * a⁻¹) a⁻¹

instance : Coe PartialSolution PartialFunction where
  coe := PartialSolution.toPartialFunction

def PartialFunction.toSolution (f : PartialFunction) (h4 : cond4 f) (h5 : cond5 f) (h6 : cond6 f) : PartialSolution :=
  ⟨f, h4, h5, h6⟩

def satisfies_func_eq879 (f : PartialFunction) (x : G) :=
  ∃ y z, f.E x y ∧ f.E (f.x₁ * y⁻¹) z -- ∧ f.E (z * y * x⁻¹) x⁻¹

@[simp]
def x₁_in_closure (f : PartialFunction) : f.x₁ ∈ Subgroup.closure f.support :=
  Subgroup.subset_closure (f.support_2 f.cond3)

@[simp]
def closure_mul_mem_not_mem {G : Type} [Group G] {A : Set G} {x y : G} (hx : x ∈ Subgroup.closure A) (hy : y ∉ Subgroup.closure A) : x * y ∉ Subgroup.closure A := by
  apply mt (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx))
  group
  exact hy

def cond4_extend_with_fresh (f : PartialFunction) (h4 : cond4 f) (a b : G) (ha : a ∉ f.dom)
    (hb : b ∉ Subgroup.closure f.support) : cond4 (f.extend a b ha) := by
  intro x y h'
  simp [PartialFunction.extend]
  constructor
  · cases h'
    · apply h4; assumption
    · apply mt f.support_2
      apply mt (Subgroup.subset_closure' _)
      -- apply closure_mul_mem_not_mem (x₁_in_closure f)
      apply mt (Subgroup.mul_mem _ (Subgroup.inv_mem _ (x₁_in_closure f)))
      group
      simp_all
  · cases h'
    · suffices h : f.x₁ * y ≠ b by simp [h]
      apply eq_contr _ hb
      apply Subgroup.mul_mem
      exact x₁_in_closure f
      apply Subgroup.subset_closure
      apply f.support_2
      assumption
    · simp_all
      by_contra hc
      unfold cond4 at h4
      rw [hc] at h4
      simp at h4
      exact h4 _ _ f.cond3

def cond5_extend_with_fresh (f : PartialFunction) (h5 : cond5 f) (a b : G) (ha : a ∉ f.dom)
    (hb : b ∉ f.im) : cond5 (f.extend a b ha) := by
  intro x x' y z h1 h2 h3 h4
  have : ∀ x, ¬f.E x b := by tauto
  simp [PartialFunction.extend] at h1 h2 h3 h4
  by_cases y = b
  · simp_all
  by_cases z = b
  · simp_all
    apply congrArg (f.x₁⁻¹ * ·) at h3
    apply congrArg (f.x₁⁻¹ * ·) at h4
    simp_all
  simp_all
  exact h5 _ _ _ _ h1 h2 h3 h4

theorem Subgroup.closure_mono' {h k : Set G} (h' : h ⊆ k) : ∀ x ∈ Subgroup.closure h, x ∈ Subgroup.closure k := Subgroup.closure_mono h'

def cond6_extend_with_fresh (f : PartialFunction) (h6 : cond6 f) (a b : G) (ha : a ∉ f.dom)
    (hb : b ∉ Subgroup.closure (f.support ∪ {a}))
    (h_for_cond6 : a⁻¹ * f.x₁ ∉ f.im) : cond6 (f.extend a b ha) := by
  intro x y z h1 h2
  have hb' : b ∉ Subgroup.closure f.support := mt (Subgroup.closure_mono' Set.subset_union_left _) hb
  by_cases h3 : y = b
  · simp [h3, PartialFunction.extend, hb] at h1 h2
    cases h2 with
    | inl h2 =>
      let h2 := Subgroup.mul_mem _ (Subgroup.inv_mem _ (x₁_in_closure f)) (Subgroup.subset_closure (f.support_1 h2))
      simp at h2
      tauto
    | inr h2 =>
      exfalso
      have h2 := congrArg (a⁻¹ * · * b) h2.1
      group at h2
      apply eq_contr _ hb h2
      apply Subgroup.mul_mem
      · simp
      · apply Subgroup.subset_closure; left; exact f.support_2 f.cond3
  by_cases h4 : z = b
  · exfalso
    simp [PartialFunction.extend, h4] at h1 h2
    cases h2; apply hb'; apply Subgroup.subset_closure; apply f.support_2; assumption
    rename_i h2
    apply congrArg (·⁻¹ * f.x₁) at h2
    simp at h2
    refine eq_contr ?_ h_for_cond6 h2
    tauto
  simp [PartialFunction.extend, h3, h4, hb] at h1 h2
  suffices f.E (z * y * x⁻¹) x⁻¹ by tauto
  exact h6 x y z h1 h2

instance : Preorder PartialSolution where
  le f g := ∀ a b, f.E a b → g.E a b
  le_refl := by simp
  le_trans := by simp_all

noncomputable def extend_with_fresh_generator (sol : PartialSolution) (a : G) (h : a ∉ sol.dom)
    (h_for_cond6 : a⁻¹ * sol.x₁ ∉ sol.im) :
    { sol' // sol ≤ sol' ∧ a ∈ sol'.dom } := by
  let b := freshGenerator (sol.support ∪ {a})
  have b_subgroup2 : b ∉ Subgroup.closure (sol.support ∪ {a}) := by
    have : sol.support.toSet ∪ {a} = (sol.support ∪ {a}).toSet := by simp
    rw [this]
    apply freshGenerator_not_in_span
  have b_subgroup : b ∉ Subgroup.closure sol.support :=
    mt (Subgroup.closure_mono' Set.subset_union_left _) b_subgroup2
  have b_im : b ∉ sol.im := by
    have : b ∉ sol.support ∪ {a} := freshGenerator_not_mem _
    have : b ∉ sol.support := by simp_all [this]
    have : b ∉ sol.im := Set.not_mem_subset (im_subset_support sol) this
    assumption
  let sol' := (sol.extend a b h).toSolution
    (h4 := cond4_extend_with_fresh sol sol.cond4 a b h b_subgroup)
    (h5 := cond5_extend_with_fresh sol sol.cond5 a b h b_im)
    (h6 := cond6_extend_with_fresh sol sol.cond6 a b h b_subgroup2 h_for_cond6)
  have : sol ≤ sol' := by tauto
  have : a ∈ sol'.dom := by use b; tauto
  use sol'

def PartialSolution.extend_case1 (sol : PartialSolution) (a : G) (h : a ∈ sol.dom) :
    { sol' // sol ≤ sol' ∧ satisfies_func_eq879 sol' a ∧ ∃ b, sol'.E a b ∧ (sol'.x₁ * b⁻¹) ∈ sol'.dom } := by
  sorry

noncomputable def PartialSolution.extend (sol : PartialSolution) (a : G) :
    { sol' // sol ≤ sol' ∧ satisfies_func_eq879 (sol' : PartialFunction) a } := by
  by_cases h : a ∈ sol.dom
  · have ⟨sol', _, _, _⟩ := sol.extend_case1 a h
    use sol'
  · by_cases h2 : ∃ z, sol.E z (a⁻¹ * sol.x₁)
    · choose z hz using h2
      have ⟨sol', hle, _, hdom⟩ := sol.extend_case1 z ⟨_, hz⟩
      suffices ha : a ∈ sol'.dom by
        have ⟨sol'', hle', _, _⟩ := sol'.extend_case1 a ha
        have : sol ≤ sol'' := le_trans hle hle'
        use sol''
      choose b hzb hbdom using hdom
      rw [le_x₁ hle] at hz
      apply hle at hz
      have ha : a = sol'.x₁ * b⁻¹ := by
        simp [congrArg (a * · * b⁻¹),
              sol'.coherence hzb hz]
      simp [hbdom, ha]
    · have ⟨sol', hle, ha⟩ := extend_with_fresh_generator sol a h h2
      have ⟨sol'', hle', _, _⟩ := sol'.extend_case1 a ha
      have : sol ≤ sol'' := le_trans hle hle'
      use sol''

theorem exists_full_solution (seed : PartialSolution) :
    ∃ f : G → G, func_eq879 f ∧ ∀ a b, seed.E a b → f a = b := by
  have ⟨c, hc, _, _, h3⟩ := exists_greedy_chain
    (fun a => { sol : PartialSolution | satisfies_func_eq879 sol.toPartialFunction a })
    (fun sol a => let ⟨sol', h⟩ := sol.extend a; ⟨sol', by simp [h]⟩)
    seed

  let E a b := ∃ sol ∈ c, sol.E a b
  have hdom : ∀ a, ∃ b, E a b := by
    intro a
    choose sol _ b heq using h3 a
    have : sol.E a b := heq.choose_spec.1
    use b, sol
  have coherence : ∀ x y z, E x y → E x z → y = z := by
    intro x y z ⟨sxy, hsxy, hxy⟩ ⟨sxz, hsxz, hxz⟩
    have ⟨s, sy, sz⟩ : ∃ s, sxy ≤ s ∧ sxz ≤ s := by
      cases hc.total hsxy hsxz; use sxz; use sxy
    exact s.coherence (sy x y hxy) (sz x z hxz)
  let ⟨f, hf⟩ := relToFun E hdom coherence

  have : func_eq879 f := by
    suffices h : ∀ x y z, f x = y → f (f 1 * y⁻¹) = z → f (z * y * x⁻¹) = x⁻¹ by simp [func_eq879, h]
    simp [hf]
    intro x y z ⟨sxy, hsxy, hxy⟩ ⟨swz, hswz, hwz⟩
    have ⟨s, hs, hsab, hswz⟩ : ∃ s ∈ c, sxy ≤ s ∧ swz ≤ s := by
      cases hc.total hsxy hswz; use swz; use sxy
    have : f 1 = s.x₁ := by simp [hf]; use s, hs, s.cond3
    rw [this] at hwz
    have := s.cond6 x y z (hsab _ _ hxy) (hswz _ _ hwz)
    use s

  have (a b : G) (h : seed.E a b) : f a = b := by simp [hf]; use seed

  use f

def g₁ : G := FreeGroup.of 1
def g₂ : G := FreeGroup.of 2
def g₃ : G := FreeGroup.of 3

def seed' : PartialFunction where
  E a b := (a, b) ∈ ({(1, g₁), (g₁ * g₁, 1), (g₁⁻¹, g₂), (g₁⁻¹ * g₂⁻¹, g₃)} : Finset _)
  support := {1, g₁, g₁ * g₁, g₁⁻¹, g₂, g₁⁻¹ * g₂⁻¹, g₃}
  support_1 := by aesop
  support_2 := by aesop
  coherence := by aesop; repeat contradiction
  x₁ := g₁
  cond3 := by aesop

def seed := seed'.toSolution
  (h4 := by
    simp [seed', cond4]
    intro a b h
    cases h; swap; rename_i h; cases h; swap; rename_i h; cases h;
    repeat rename_i h; rw [h.1, h.2]; tauto)
  (h5 := by
    simp [seed', cond5]
    intro a a' b c h1 h2 h3 h4
    cases h1; swap; rename_i h; cases h; swap; rename_i h; cases h;
    repeat {
      rename_i h; rw [h.2] at h2; rw [h.1] at h3; rw [h.1]
      cases h2; swap; rename_i h; cases h; swap; rename_i h; cases h;
      all_goals rename_i h; rw [h.1] at h4; rw [h.1]
      repeat {
        cases h3; swap; rename_i h; cases h; swap; rename_i h; cases h;
        repeat rename_i h; rw [h.2] at h4; tauto
      }
    }
  )
  (h6 := by
    simp [seed', cond6]
    intro a b c h1 h2
    cases h1; swap; rename_i h; cases h; swap; rename_i h; cases h;
    repeat {
      rename_i h; rw [h.1, h.2]; rw [h.2] at h2
      cases h2; swap; rename_i h; cases h; swap; rename_i h; cases h;
      rename_i h; rw [h.2]; tauto
      rename_i h; rw [h.2]; tauto
      rename_i h; rw [h.2]; tauto
      rename_i h; rw [h.2]; tauto
    })

@[equational_result]
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

end Eq879
