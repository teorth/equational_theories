import equational_theories.Mathlib.Data.List.Defs
import equational_theories.Mathlib.Order.Greedy
import Mathlib.Data.Finset.Order
import Mathlib.Data.List.AList
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Functor
import Mathlib.GroupTheory.FreeGroup.Basic

import equational_theories.FreshGenerator
import equational_theories.Equations.All
import equational_theories.FactsSyntax



namespace Eq1518

private abbrev A := FreeGroup Nat

/- Follows https://leanprover.zulipchat.com/user_uploads/3121/euHPpWREgokUUJA6B_2UtHGs/Equation1518-corrected.pdf
-/

namespace Greedy
noncomputable section
open FreshGenerator

private abbrev x₁ := FreeGroup.of 1
private abbrev x₂ := FreeGroup.of 2
private abbrev x₃ := FreeGroup.of 3
private abbrev x₄ := FreeGroup.of 4


abbrev PreExtension := A → Set A

abbrev fromList (S : List (A × A)) : PreExtension := fun a => {b | (a, b) ∈ S}

def E0List : List (A × A) := [(1, x₁), (x₁, x₂), (x₂ * x₁⁻¹, x₁⁻¹), (x₁⁻¹, 1),
  (x₂ * x₁⁻¹ * x₁⁻¹, x₁⁻¹ * x₁⁻¹), (x₁^2, x₃), (x₃ * x₁^(-2 : ℤ), x₁⁻¹)]

abbrev E0 := fromList E0List

structure PreExtension.OK (E : PreExtension) : Prop where
  finite : Set.Finite {x : A × A | x.2 ∈ E x.1}
  func {a} : Set.Subsingleton (E a)
  base {a b} : (b ∈ E0 a) → b ∈ E a
  eq1518 {a b c} : b ∈ E a → c ∈ E (b * a⁻¹) → a * x₁⁻¹ ∈ E (c * a * x₁⁻¹)
  aux {a} : x₁ ∈ E a → ∃ c, c ∈ E (x₁ * a⁻¹)

abbrev Extension := {E : PreExtension // E.OK}

class Extension1 where
  E : PreExtension
  ok : E.OK
  d : A
  not_def {c} : c ∉ E d

namespace Extension1
variable [Extension1]
def old : Finset A :=
  insert d <| ok.finite.toFinset.biUnion fun (a, b) => {a, b}

theorem mem_old {a b x}
    (h1 : b ∈ E a) (h2 : x ∈ ({a, b} : Finset A)) : x ∈ old := by
  refine Finset.mem_insert_of_mem ?_
  simp only [old, Finset.mem_biUnion, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Prod.exists]
  exact ⟨_, _, h1, h2⟩

@[local aesop safe forward]
theorem old_dom {a b} (h : b ∈ E a) : a ∈ old := mem_old h (by simp)
@[local aesop safe forward]
theorem old_im {a b} (h : b ∈ E a) : b ∈ old := mem_old h (by simp)
@[local aesop safe forward]
theorem old_d : d ∈ old := Finset.mem_insert_self ..
@[local aesop safe forward]
theorem old_x₁ : x₁ ∈ old := by
  apply old_im
  apply ok.base (a:= 1)
  decide


def c := freshGenerator old

@[local aesop norm simp]
theorem forgetOld_c : forgetOld old c = c := forgetOld_fresh

attribute [local aesop norm simp] forgetOld_old
attribute [local aesop norm simp] MonoidHom.map_mul

@[local aesop safe destruct]
theorem c_ne_1 : c = 1 → False := by unfold c freshGenerator ; simp

@[local aesop safe destruct]
theorem c_ne_1' : 1 = c → False := fun h => c_ne_1 h.symm

-- There should be a simple direct proof, but we can also use the cyclic one
@[local aesop safe destruct]
theorem c_ne_c_inv : c = c⁻¹ → False := FreeGroup.ne_inv_of_ne_one c_ne_1

@[local aesop safe destruct]
theorem c_ne_c_inv' : c⁻¹ = c → False := fun h => c_ne_c_inv h.symm

@[mk_iff]
inductive Relevant : A → A → Prop
  | mk {a b} : b ∈ E a → d = b * a⁻¹ → Relevant a b

theorem Relevant.ne_sx1 : ∀ {a b}, Relevant a b → a ≠ x₁^2
  | _, b, .mk h q, rfl => by
    have : b = x₃ := ok.func h (ok.base (by decide))
    apply this ▸ q ▸ not_def
    apply ok.base (b := x₁⁻¹) (by decide)

theorem Relevant.ne_x1 : ∀ {a b}, Relevant a b → b ≠ x₁
  | _, _, .mk h q, rfl => by
    obtain ⟨c, h2⟩ := ok.aux h
    exact (q ▸ not_def) h2

@[mk_iff]
inductive Next : A → A → Prop
  | base {a b} : b ∈ E a → Next a b
  | new {a b} : a = d → b = c → Next a b
  | extra {a b e f} : Relevant a b → e = c * a * x₁⁻¹ → f = a * x₁⁻¹ →  Next e f -- Nicer for pattern matching

abbrev next : PreExtension := fun a => {b | Next a b}

theorem next_func : ∀ {a}, (next a).Subsingleton
  | _, _, .base hb, _, .base hb' => ok.func hb hb'
  | _, _, .new rfl rfl, _, .new rfl rfl=> rfl
  | _, _, .base hb, _,  .new rfl rfl | _, _,  .new rfl rfl, _, .base hb => (not_def hb).elim
  | _, _, .base hb, _, .extra (.mk h q) he rfl | _, _, .extra (.mk h q) he rfl, _, .base hb
  | _, _, .new rfl rfl, _, .extra (.mk h q) he hf | _, _, .extra (.mk h q) he hf, _, .new rfl rfl => by
    exfalso
    apply_fun forgetOld old at he
    aesop
  | _, _, .extra (.mk h1 q1) he1 rfl, _, .extra (.mk h2 q2) he2 rfl => by
    rw [he1] at he2
    simp only [mul_left_inj, mul_right_inj] at he2
    simp [he2]

theorem next_eq1518 {a b c'} : b ∈ next a → c' ∈ next (b * a⁻¹) → a * x₁⁻¹ ∈ next (c' * a * x₁⁻¹)
  | .base h1, .base h2 => .base $ ok.eq1518 h1 h2
  | .base h1, .new e rfl => .extra ⟨h1, e.symm⟩ rfl rfl
  | .new rfl rfl, .base he => by
    exfalso
    have : forgetOld old (c * d⁻¹) = 1 := forgetOld_old (old_dom he)
    aesop
  | .new rfl rfl, .extra (.mk h q) he rfl => by
    rw [q] at he
    simp only [mul_inv_rev, inv_inv, mul_assoc, mul_right_inj, inv_inj] at he
    rw [he] at h
    exfalso
    exact Relevant.ne_x1 ⟨h, he ▸ q⟩ rfl
  | .extra (.mk h1 q1) rfl rfl, .base h2 => by
    group at h2
    have : forgetOld old (c^(-1 : ℤ)) = 1 := forgetOld_old (old_dom h2)
    aesop
  | .base h1, .extra (.mk h q) he rfl
  | .new rfl rfl, .new he rfl
  | .extra (.mk h1 q1) rfl rfl, .new he rfl
  | .extra (.mk h1 q1) rfl rfl, .extra (.mk h2 q2) he rfl => by
    exfalso
    apply_fun forgetOld old at he
    aesop

theorem next_aux {a} : x₁ ∈ next a → ∃ c, c ∈ next (x₁ * a⁻¹)
  | .base h => by
    obtain ⟨c, h⟩ := ok.aux h
    exact ⟨c, .base h⟩
  | .new rfl he => by
    exfalso
    apply_fun forgetOld old at he
    aesop
  | .extra h rfl he => by
    apply_fun (fun g => g * x₁) at he
    exfalso
    apply Relevant.ne_sx1 h
    group at *
    rw [← he]
    rfl

theorem next_ok : next.OK where
  finite := by
    have : {(a, b) | Relevant a b}.Finite := .subset ok.finite (fun _ (.mk h _) => h)
    refine (ok.finite.union <| (.insert (d, c)
    (this.map fun (a,_) => ((c * a * x₁⁻¹),(a * x₁⁻¹))))).subset fun (x,y) hx => ?_
    simp only [Set.mem_setOf_eq] at hx
    match hx with
    | .extra h rfl rfl =>
      simp only [Set.union_insert, Set.mem_insert_iff, Prod.mk.injEq, Set.mem_union,
        Set.mem_setOf_eq]
      right
      right
      simp only [Set.fmap_eq_image, Set.mem_image, Set.mem_setOf_eq, Prod.mk.injEq, mul_left_inj,
        mul_right_inj, and_self, Prod.exists, exists_and_right, exists_eq_right]
      exact ⟨_, h⟩
    | .new rfl rfl => tauto
    | .base h => simp [h]
  func {a} := next_func
  base := Next.base ∘ ok.base
  eq1518 {a b} := next_eq1518
  aux {a} := next_aux

end Extension1


variable (e₀ : Extension)

theorem exists_extension :
    ∃ op : A → A,
    (∀ x, op (op (op x * x⁻¹)*x*(op 1)⁻¹) = x * (op 1)⁻¹) ∧
    (∀ {x y}, y ∈ e₀.1 x → y = op x) := by
  classical
  have ⟨c, hc, h1, h2, h3⟩ := exists_greedy_chain (a := e₀)
    (task := fun x : _  => {e | (e.1 x).Nonempty}) fun ⟨E, ok⟩ d => by
      if h : (E d).Nonempty then exact ⟨_, le_rfl, h⟩ else
      let E1 : Extension1 := { E, ok, d, not_def := fun h' => h ⟨_, h'⟩ }
      exact ⟨⟨E1.next, E1.next_ok⟩, fun _ _ => (.base ·), _, .new rfl rfl⟩
  simp only [Subtype.exists, Prod.forall] at h3
  classical
  choose f hf1 hf2 op hop using h3
  refine ⟨op, fun x => ?_, fun {x y} h => ?_,⟩
  · let S : Finset A := {x, op x * x⁻¹, 1, op (op x * x⁻¹)*x*(op 1)⁻¹}
    have ⟨⟨e, he⟩, le⟩ := hc.directed.finset_le (hι := ⟨⟨_, h1⟩⟩)
      (S.image fun a => ⟨⟨f a, hf1 a⟩, hf2 a⟩)
    replace le a ha := Finset.forall_image.1 le a ha _ (hop a)
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, S] at le
    obtain ⟨opx, opopxxinv, op1, opfinal⟩ := le
    have eq : op 1 = x₁ := e.2.func op1 (e.2.base (by decide))
    exact e.2.func opfinal (eq.symm ▸ e.2.eq1518 opx opopxxinv)
  · exact (hf1 ..).func (h2 _ (hf2 x) _ h) (hop ..)


def GreedyMagma (_ : Extension) := A

def f (e₀ : Extension) : A → A := (exists_extension e₀).choose

theorem f_eq1518 (e₀ : Extension) : (∀ x, f e₀ (f e₀ (f e₀ x * x⁻¹)*x*(f e₀ 1)⁻¹) = x * (f e₀ 1)⁻¹) :=
  (exists_extension e₀).choose_spec.1

theorem f_base (e₀ : Extension) :∀ {x y: GreedyMagma e₀}, y ∈ e₀.1 x → y = f e₀ x :=
  (exists_extension e₀).choose_spec.2

def op (e₀ : Extension) (x y : A) : A := f e₀ (y*x⁻¹) * x

noncomputable instance instMagma : Magma (GreedyMagma e₀) where
  op x y:= op e₀ x y

theorem eq1518 : Equation1518 (GreedyMagma e₀) := by
  intro x y
  repeat rw [Magma.op, instMagma]
  simp only
  repeat rw [op]
  unfold GreedyMagma at *
  have := f_eq1518 e₀ (x * y⁻¹)
  symm
  apply_fun (fun g => g * (x * y⁻¹ * (f e₀ 1)⁻¹)⁻¹) at this
  apply eq_of_mul_inv_eq_one
  group at *
  assumption

theorem fromList_ok {S : List (A × A)}
    (func : ∀ a ∈ S, ∀ b ∈ S, a.1 = b.1 → a.2 = b.2 := by decide)
    (base : ∀ a ∈ E0List, a ∈ S := by decide)
    (eq1518 : ∀ a ∈ S, ∀ b ∈ S, b.1 = a.2 * a.1⁻¹ → (b.2*a.1* x₁⁻¹, a.1*x₁⁻¹) ∈ S := by decide)
    (aux : ∀ a ∈ S, a.2 = x₁ → ∃ b ∈ S, b.1 = x₁ * a.1⁻¹ := by decide) :
    (fromList S).OK where
  finite := List.finite_toSet S
  base h := base _ h
  func h1 _ h2 := func _ h1 _ h2 rfl
  eq1518 h1 h2 := eq1518 _ h1 _ h2 rfl
  aux h := let ⟨(_, c), h1, h2⟩ := aux _ h rfl ; ⟨c, h2 ▸ h1⟩



theorem fromList_eval {e : Extension} {S : List (A × A)} (hS : e.1 = fromList S)
    (a b : A) (h : (a, b) ∈ S := by decide) : f e a = b :=
  (f_base e (hS ▸ h)).symm

end
end Greedy

open Greedy

@[equational_result]
theorem not_47_614 : ∃ (G : Type) (_ : Magma G), Facts G [1518] [47, 614] := by
  have ⟨e, he⟩ : ∃ e : Extension, e.1 = fromList
    (E0List ++ [(x₂, x₄)]) :=
    ⟨⟨_, fromList_ok⟩, rfl⟩
  refine ⟨GreedyMagma e, inferInstance, eq1518 e, fun h => ?_, fun h => ?_⟩
  · have := h (1 : A)
    repeat rw [Magma.op, instMagma] at this
    simp only at this
    repeat rw [op] at this
    group at this
    rw [fromList_eval he 1 x₁, fromList_eval he x₁ x₂, fromList_eval he x₂ x₄] at this
    apply Ne.elim _ this
    unfold GreedyMagma -- changes the inequality type, so that decide works
    decide
  · have := h (1 : A)
    repeat rw [Magma.op, instMagma] at this
    simp only at this
    repeat rw [op] at this
    group at this
    rw [fromList_eval he 1 x₁, fromList_eval he (x₁^(-1)) 1,
        fromList_eval he (1 * x₁) x₂, fromList_eval he x₂ x₄] at this
    apply Ne.elim _ this
    unfold GreedyMagma
    decide

@[equational_result]
theorem not_817 : ∃ (G : Type) (_ : Magma G), Facts G [1518] [817] := by
  have ⟨e, he⟩ : ∃ e : Extension, e.1 = fromList
    E0List :=
    ⟨⟨_, fromList_ok⟩, rfl⟩
  refine ⟨GreedyMagma e, inferInstance, eq1518 e, fun h => ?_⟩
  · have := h (1 : A)
    repeat rw [Magma.op, instMagma] at this
    simp only at this
    repeat rw [op] at this
    group at this
    rw [fromList_eval he 1 x₁, fromList_eval he (x₁ * x₁) x₃] at this
    apply Ne.elim _ this
    unfold GreedyMagma
    decide

@[equational_result]
theorem not_3862 : ∃ (G : Type) (_ : Magma G), Facts G [1518] [3862] := by
  have ⟨e, he⟩ : ∃ e : Extension, e.1 = fromList
    (E0List ++ [(x₂⁻¹, x₄),(x₄*x₂*x₁^(-2 : ℤ),x₂*x₁^(-2 : ℤ)),(x₄*x₂*x₁^(-3 : ℤ),x₂*x₁^(-3 : ℤ))]) :=
    ⟨⟨_, fromList_ok⟩, rfl⟩
  refine ⟨GreedyMagma e, inferInstance, eq1518 e, fun h => ?_⟩
  · have := h (1 : A)
    repeat rw [Magma.op, instMagma] at this
    simp only at this
    repeat rw [op] at this
    group at this
    rw [fromList_eval he 1 x₁, fromList_eval he x₁ x₂, fromList_eval he (x₂ ^ (-1)) x₄] at this
    apply Ne.elim _ this
    unfold GreedyMagma
    decide



end Eq1518
