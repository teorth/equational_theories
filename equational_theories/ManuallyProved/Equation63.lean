import equational_theories.Mathlib.Order.Greedy
import Mathlib.Data.Finset.Order
import Mathlib.Data.Rel
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring

import equational_theories.FreshGenerator
import equational_theories.Equations.All
import equational_theories.FactsSyntax


namespace Eq63

/- Follows
https://teorth.github.io/equational_theories/blueprint/infinite-magma-constructions-chapter.html#a0000000233
 -/

private abbrev G := FreeGroup Nat


namespace Greedy
noncomputable section
open FreshGenerator

-- The functional forms of equations 63 and 1692 (for translation-invariant magmas)
def thomson (f : G → G) := ∀ x, f (x⁻¹ * f (f x)) = x⁻¹
def thompson (f : G → G) := ∀ x, f x * f (f ((f x)⁻¹)) = x


private abbrev g₁ := FreeGroup.of 1
private abbrev g₂ := FreeGroup.of 2
private abbrev g₃ := FreeGroup.of 3
private abbrev g₄ := FreeGroup.of 4
private abbrev g₅ := FreeGroup.of 5
private abbrev g₆ := FreeGroup.of 6

structure OK (E : Rel G G) : Prop where
  finite : Set.Finite {(x, y) : G × G | E x y}
  func {x y y'} : E x y → E x y' → y = y'
  base : E 1 g₁ ∧ E g₁ g₂ ∧ E g₂⁻¹ (g₁ * g₂) ∧ E (g₁ * g₂) (g₂⁻¹ * g₁)
  eq63 {x y z} : E x y → E y z → E (x⁻¹ * z) x⁻¹
  aux1 {x} : E x 1 → x = g₂
  aux2 {x} : ¬E x x⁻¹
  aux3 {x x' y z} : E x y → E x' y → E x⁻¹ z → x' = x * z → x' = x
  aux4 {x x' y z z'} : E x y → E x' y → E x⁻¹ z → E x'⁻¹ z' → x' * z' = x * z → x = x'

abbrev PartialSolution := {E : Rel G G // OK E}

class Extension where
  E : Rel G G
  ok : OK E
  d : G
  not_def {y} : ¬E d y

namespace Extension

variable [Extension]


def old : Finset G :=
  insert d <| ok.finite.toFinset.biUnion fun (a, b) => {a, b}

theorem mem_old {a b x}
    (h1 : E a b) (h2 : x ∈ ({a, b} : Finset G)) : x ∈ old := by
  refine Finset.mem_insert_of_mem ?_
  simp only [old, Finset.mem_biUnion, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Prod.exists]
  exact ⟨_, _, h1, h2⟩

def c := FreeGroup.of (freshGeneratorName old)

def project (x : G) : ℤ := Multiplicative.toAdd <| FreshGenerator.projectFresh old x

@[simp] theorem project_1 : project 1 = 0 := by simp [project]
@[simp] theorem project_mul {x y} : project (x * y) = project x + project y := by simp [project]
@[simp] theorem project_inv {x} : project x⁻¹ = -project x := by simp [project]

@[simp] theorem project_c : project c = 1 := by
  simp [project, c, ←FreshGenerator.freshGenerator.eq_1]
  rfl

@[simp] theorem project_d : project d = 0 := FreshGenerator.projectFresh_old (by simp [old])

@[local aesop safe destruct]
theorem project_E {x y} (h : E x y) : project x = 0 ∧ project y = 0 := by
  constructor <;> (apply FreshGenerator.projectFresh_old; apply mem_old h; simp)

theorem aux3' {x x' z} : E x d → E x' d → E x⁻¹ z → x' ≠ x * z := by
  intro h1 h2 h3 h4
  simp only [ok.aux3 h1 h2 h3 h4, left_eq_mul] at h4
  have := inv_eq_iff_eq_inv.1 $ ok.aux1 (h4 ▸ h3)
  rw [this] at h1
  have values : E g₂⁻¹ (g₁ * g₂) ∧ E (g₁ * g₂) (g₂⁻¹ * g₁) := by simp [ok.base]
  exact not_def $ ok.func h1 values.left ▸ values.right

@[mk_iff]
inductive Next : G → G → Prop
  | base {a b} : E a b → Next a b
  | new {a b} : a = d → b = c → Next a b
  | fromH {h a b} : E h d → a = h⁻¹ * c → b = h⁻¹ → Next a b
  | fromH' {h f a b} : E h d → E h⁻¹ f → a = c⁻¹ * h * f → b = c⁻¹ * h → Next a b

theorem inv_in_E_means_d {x y z} : Next x y → Next x⁻¹ z → x = d ∨ x = d⁻¹ ∨ E x y ∧ E x⁻¹ z
  | .base _, .base _ | .new rfl rfl, _ => by tauto
  | _, .new h _ => by rw [inv_eq_iff_eq_inv] at h; tauto
  | .fromH _ rfl rfl, .fromH' _ _ he _ => by
    simp only [mul_inv_rev, inv_inv, mul_assoc, mul_right_inj] at he
    solve_by_elim [aux3']
  | .fromH' _ _ rfl rfl, .fromH _ he _ => by
    apply_fun Inv.inv at he
    simp only [mul_assoc, mul_inv_rev, inv_inv, mul_right_inj] at he
    solve_by_elim [aux3']
  | .base hb, .fromH _ he _ | .base hb, .fromH' _ _ he _ | .fromH _ he _, .base _
  | .fromH .., .fromH _ he _ | .fromH' _ _ he _, .base _ | .fromH' _ _ rfl rfl, .fromH' _ _ he rfl => by
    apply_fun project at he
    aesop

theorem next_d_is_c {y} : Next d y → y = c
  | .base hb => False.elim $ not_def hb
  | .new _ h => h
  | .fromH _ he _ | .fromH' _ _ he _ => by apply_fun project at he; aesop

theorem prev_c_is_d {x} : Next x c → x = d
  | .base _ => by aesop
  | .new h _ => h
  | .fromH _ _ he | .fromH' _ _ _ he => by apply_fun project at he; aesop

def next_finite : Set.Finite {(x, y) : G × G | Next x y} := by
  simp [next_iff, Set.setOf_or]
  split_ands
  · exact ok.finite
  · simp [← Prod.mk.injEq]
  · apply Set.Finite.subset (ok.finite.image fun (x, y) => (x⁻¹ * c, x⁻¹))
    intro (a, b) ⟨x, h⟩
    simp only [Set.mem_image, Set.mem_setOf_eq, Prod.mk.injEq, Prod.exists, exists_and_right] at *
    use x; simp [h]
    use d; simp [h]
  · apply Set.Finite.subset ((ok.finite.prod ok.finite).image fun ((x, _), (_, y)) => (c⁻¹ * x * y, c⁻¹ * x))
    intro (a, b) ⟨x, h1, y, h2, h3, h4⟩
    simp only [Set.mem_image, Set.mem_prod, Set.mem_setOf_eq, Prod.mk.injEq, Prod.exists] at *
    exact ⟨x, d, x⁻¹, y, by simp [*]⟩

def next_func {x y y'} : Next x y → Next x y' → y = y'
  | .base hb, .base hb' => ok.func hb hb'
  | .new rfl rfl, .new rfl rfl => rfl
  | .fromH h1 h2 h3, .fromH h1' h2' h3' => by
    rw [h2', mul_left_inj, inv_inj] at h2
    exact h3' ▸ h2 ▸ h3
  | .base hb, .new rfl rfl | .new rfl rfl, .base hb => (not_def hb).elim
  | .base .., .fromH _ he _ | .fromH _ he _, .base ..| .new .., .fromH _ he _ | .fromH _ he _, .new ..
  | .base .., .fromH' _ _ he _ | .new .., .fromH' _ _ he _ | .fromH .., .fromH' _ _ he _
  | .fromH' _ _ he _, .base .. | .fromH' _ _ he _, .new .. | .fromH' _ _ he _, .fromH .. => by
    apply_fun project at he
    aesop
  | .fromH' h1 h2 h3 rfl, .fromH' h1' h2' rfl rfl => by
    simp only [mul_assoc, mul_right_inj] at h3
    simp [ok.aux4 h1 h1' h2 h2' h3]

def next_base : Next 1 g₁ ∧ Next g₁ g₂ ∧ Next g₂⁻¹ (g₁ * g₂) ∧ Next (g₁ * g₂) (g₂⁻¹ * g₁) := by
  simp [Next.base, ok.base]

def next_eq63 {x y z} : Next x y → Next y z → Next (x⁻¹ * z) x⁻¹
  | .base hb, .base hb' => .base $ ok.eq63 hb hb'
  | .base hb, .new rfl rfl => .fromH hb rfl rfl
  | .fromH h rfl h', .base hb => by apply Next.fromH' h (h' ▸ hb); group
  | .fromH h rfl h', .new rfl rfl => False.elim $ ok.aux2 (h' ▸ h)
  | .new rfl rfl, .fromH h1 h2 rfl => by
    exfalso
    apply congr_arg (c * ·⁻¹) at h2; simp at h2
    have values : E 1 g₁ ∧ E g₁ g₂ := by simp [ok.base]
    exact not_def $ ok.func (h2 ▸ h1) values.left ▸ values.right
  | .fromH' _ _ rfl rfl, .fromH' _ _ he rfl => by
    simp only [mul_assoc, mul_right_inj] at he
    solve_by_elim [aux3']
  | .base .., .fromH .. | .base .., .fromH' .. | .new .., .base .. | .fromH' .., .base .. => by aesop
  | .new .., .new he _ | .new .., .fromH' _ _ he _ | .fromH _ _ he, .fromH ..
  | .fromH _ _ he, .fromH' .. | .fromH' .., .new he _ | .fromH' .., .fromH _ he _ => by
    apply_fun project at he
    aesop

def next_aux1 {x} : Next x 1 → x = g₂
  | .base hb => ok.aux1 hb
  | .new rfl h => by apply_fun project at h; simp at h
  | .fromH h1 rfl h2 => by
    exfalso
    have values : E 1 g₁ ∧ E g₁ g₂ := by simp [ok.base]
    have := ok.func values.left $ inv_eq_one.1 h2.symm ▸ h1
    exact not_def (this ▸ values.right)
  | .fromH' _ _ rfl he => by
    apply_fun project at he
    aesop

def next_aux2 {x} : ¬Next x x⁻¹
  | .base hb => ok.aux2 hb
  | .new _ he | .fromH _ he _ | .fromH' _ _ _ he => by
    apply_fun project at he
    aesop

def next_aux3 {x x' y z} : Next x y → Next x' y → Next x⁻¹ z → x' = x * z → x' = x := by
  intro h1 h2 h3 h4
  match inv_in_E_means_d h1 h3 with
  | .inl h => exact h ▸ prev_c_is_d $ (next_d_is_c (h ▸ h1)) ▸ h2
  | .inr (.inl h) =>
    have h5 := next_d_is_c (inv_eq_iff_eq_inv.2 h ▸ h3)
    match h2 with
    | .fromH h6 rfl rfl =>
      simp [h, h5] at h4
      simp [h4, not_def] at h6
    | .base .. | .new .. | .fromH' .. =>
      apply_fun project at h4
      aesop
  | .inr (.inr ⟨h5, h6⟩) =>
    match h2 with
    | .base h7 => exact ok.aux3 h5 h7 h6 h4
    | .new .. | .fromH .. | .fromH' .. =>
      apply_fun project at h4
      aesop

def next_aux4 {x x' y z z'} : Next x y → Next x' y → Next x⁻¹ z → Next x'⁻¹ z' → x' * z' = x * z → x = x' := by
  intro h1 h2 h3 h4 h5
  match inv_in_E_means_d h1 h3 with
  | .inl h => exact h ▸ prev_c_is_d (next_d_is_c (h ▸ h1) ▸ h2) |>.symm
  | .inr (.inl h) =>
    rw [h] at h1 h3 h5
    rw [inv_inv] at h3
    rw [next_d_is_c h3] at h5
    match h4 with
    | .new h' rfl => exact h ▸ inv_eq_iff_eq_inv.2 h'.symm
    | .base h6 | .fromH _ h6 rfl | .fromH' _ _ h6 rfl =>
      apply_fun project at h5
      try apply_fun project at h6
      aesop
  | .inr (.inr ⟨h6, h7⟩) =>
    rw [next_func (.base h6) h1] at h6
    rw [next_func (.base h7) h3] at h7
    match h2, h4 with
    | .base hb, .base hb' => exact ok.aux4 h6 hb h7 hb' h5
    | .new rfl rfl, _ => exact prev_c_is_d (.base h6)
    | .base hb, .fromH _ h8 rfl | .base hb, .fromH' _ _ h8 _ | _, .new h8 rfl =>
      apply_fun project at h5 h8
      aesop
    | .fromH .., .base .. | .fromH .., .fromH .. =>
      apply_fun project at h5
      aesop
    | .fromH h8 rfl rfl, .fromH' h9 h10 h11 rfl =>
      simp [mul_assoc] at h11
      solve_by_elim [aux3']
    | .fromH' h8 h9 rfl rfl, _ => aesop


def next : PartialSolution :=
  ⟨Next, next_finite, fun {_} => next_func, next_base, next_eq63, next_aux1, next_aux2, next_aux3, next_aux4⟩

end Extension

theorem exists_extension (seed : PartialSolution) :
    ∃ f : G → G,
    thomson f ∧
    (∀ {x y}, seed.1 x y → f x = y) := by
  classical
  have ⟨c, hc, h1, h2, h3⟩ := exists_greedy_chain (a := seed)
    (task := fun x : _  => {e | ∃ y, e.1 x y}) fun ⟨E, ok⟩ d => by
      if h : ∃ y, E d y then exact ⟨_, le_rfl, h⟩ else
      let E1 : Extension := { E, ok, d, not_def := fun h' => h ⟨_, h'⟩ }
      exact ⟨E1.next, fun _ _ => (.base ·), _, .new rfl rfl⟩
  choose e he f hf using h3
  refine ⟨f, fun x => ?_, fun {x y} h => ?_,⟩
  · let S : Finset G := {x, f x, x⁻¹ * f (f x)}
    have ⟨⟨e, he⟩, le⟩ := hc.directed.finset_le (hι := ⟨⟨_, h1⟩⟩)
      (S.image fun a => ⟨e a, he a⟩)
    replace le a ha := Finset.forall_image.mp le a ha _ _ (hf a)
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, S] at le
    obtain ⟨fx, ffx, fffxmx⟩ := le
    exact e.2.func fffxmx (e.2.eq63 fx ffx)
  · exact (e ..).2.func (h2 _ (he x) _ _ h) (hf ..) |>.symm

end
end Greedy

open Greedy

def seed' : List (G × G) := [
  (1, g₁), (g₁, g₂), (g₂, 1), (g₁⁻¹, g₁⁻¹), (g₂⁻¹ * g₁, g₂⁻¹), (g₂⁻¹, g₁ * g₂),
  (g₁⁻¹ * g₂ * g₁ * g₂, g₁⁻¹ * g₂), (g₁ * g₂, g₂⁻¹ * g₁), (g₂⁻¹ * g₁⁻¹ * g₂⁻¹, g₂⁻¹ * g₁⁻¹),
  (g₃, g₄⁻¹), (g₄, g₃), (g₄⁻¹^2, g₄⁻¹),
]
def seed : Rel G G := fun x y => (x, y) ∈ seed'

theorem seed_ok : OK seed where
  finite := List.finite_toSet seed'
  func h1 h2 := by
    suffices ∀ a ∈ seed', ∀ b ∈ seed', a.1 = b.1 → a.2 = b.2 from this _ h1 _ h2 rfl
    decide
  base := by simp [seed, seed']
  eq63 h1 h2 := by
    suffices ∀ a ∈ seed', ∀ b ∈ seed', b.1 = a.2 → (a.1⁻¹ * b.2, a.1⁻¹) ∈ seed' from this _ h1 _ h2 rfl
    decide
  aux1 h := by
    suffices ∀ a ∈ seed', a.2 = 1 → a.1 = g₂ from this _ h rfl
    decide
  aux2 h := by
    suffices ∀ a ∈ seed', a.2 ≠ a.1⁻¹ from this _ h rfl
    decide
  aux3 h1 h2 h3 h4 := by
    suffices ∀ a ∈ seed', ∀ b ∈ seed', ∀ c ∈ seed', b.2 = a.2 → c.1 = a.1⁻¹ → b.1 = a.1 * c.2 → b.1 = a.1
      from this _ h1 _ h2 _ h3 rfl rfl h4
    decide
  aux4 h1 h2 h3 h4 h5 := by
    suffices ∀ a ∈ seed', ∀ b ∈ seed', ∀ c ∈ seed', ∀ d ∈ seed', b.2 = a.2 → c.1 = a.1⁻¹ → d.1 = b.1⁻¹ → b.1 * d.2 = a.1 * c.2 → a.1 = b.1
      from this _ h1 _ h2 _ h3 _ h4 rfl rfl rfl h5
    decide

@[equational_result]
theorem Equation63_not_implies_Equation1692 :
    ∃ (G: Type) (_: Magma G), Equation63 G ∧ ¬ Equation1692 G := by
  let ⟨f, h63, hf⟩ := exists_extension ⟨seed, seed_ok⟩
  use G, {op := fun x y => x * f (x⁻¹ * y)}
  have values : f g₃ = g₄⁻¹ ∧ f g₄ = g₃ := by
    repeat first | constructor | apply hf; simp [seed]
  have h1692 : ¬thompson f :=
    by rw [thompson, not_forall]; use g₃; simp only [values, inv_inv]; decide
  constructor
  · intro x y
    group
    have := congr_arg (y * ·) $ h63 (x⁻¹ * y)
    group at this
    exact this.symm
  · have ⟨x, h⟩ := Classical.exists_not_of_not_forall h1692
    simp only [not_forall]
    use x, 1; simp
    exact (h ·.symm)

end Eq63
