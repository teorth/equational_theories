import equational_theories.Mathlib.Data.List.Defs
import equational_theories.Mathlib.Order.Greedy
import Mathlib.Data.Finset.Order
import Mathlib.Data.List.AList
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Functor
import Mathlib.Tactic.DeriveFintype
import Mathlib.GroupTheory.FreeGroup.Basic

import equational_theories.FreshGenerator
import equational_theories.Equations.All
import equational_theories.FactsSyntax

import Mathlib.Data.FinEnum

namespace Eq1722
section TranslationInvariant
private abbrev A := FreeGroup Nat

/- Follows
https://leanprover.zulipchat.com/user_uploads/3121/VR_KgPk0rQaGpgjsi24OECXm/1526.pdf
-/

namespace Greedy
noncomputable section
open FreshGenerator

private abbrev x₁ := FreeGroup.of 1
private abbrev x₂ := FreeGroup.of 2
private abbrev x₃ := FreeGroup.of 3
private abbrev x₄ := FreeGroup.of 4
private abbrev x₅ := FreeGroup.of 5
private abbrev x₆ := FreeGroup.of 6

abbrev PreExtension := A → Set A

abbrev fromList (S : List (A × A)) : PreExtension := fun a => {b | (a, b) ∈ S}

def E0List : List (A × A) := [(1,x₁),(x₁⁻¹,x₂),(x₂,x₁⁻¹),(x₁⁻¹*x₂⁻¹,x₁*x₂⁻¹),(x₁,1),(x₁^(-2 : ℤ),x₁^(-2 : ℤ))]

abbrev E0 := fromList E0List

structure PreExtension.OK (E : PreExtension) : Prop where
  finite : Set.Finite {x : A × A | x.2 ∈ E x.1}
  func {a} : Set.Subsingleton (E a)
  base {a b} : (b ∈ E0 a) → b ∈ E a
  eq1722 {a b c} : b ∈ E a → c ∈ E (a * b⁻¹) → a⁻¹ * x₁⁻¹ ∈ E (c * b * a⁻¹ * x₁⁻¹)
  aux {a b c d} : b ∈ E a → d ∈ E c → a * b⁻¹ = c * d⁻¹ → a = c -- b = d follows from func

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

inductive Relevant : A → Prop
  | mk {a b} : b ∈ E a → d = a * b⁻¹ → Relevant a

theorem Relevant.unique {a a'} : Relevant a → Relevant a' → a = a'
  | .mk h1 q1, .mk h2 q2 => ok.aux h1 h2 (q2 ▸ q1.symm)

theorem Relevant.ne_x1inv {a} : Relevant a → x₁⁻¹ ≠ a
  | .mk h q, rfl => by
    have b_eq_x2 := ok.func h $ ok.base (b:=x₂) (by decide)
    exact ((b_eq_x2 ▸  q) ▸ not_def) (ok.base (b:= x₁*x₂⁻¹) (by decide))

@[mk_iff]
inductive Next : A → A → Prop
  | base {a b} : b ∈ E a → Next a b
  | new {a b} : a = d → b = c → Next a b
  | extra {a e f} : Relevant a → e = c * d⁻¹ * x₁⁻¹ → f = a⁻¹ * x₁⁻¹ →  Next e f -- Nicer for pattern matching



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
  | _, _, .extra h1 _ rfl, _, .extra h2 _ rfl => by rw [h1.unique h2]



theorem next_eq1722 {a b c} : b ∈ next a → c ∈ next (a * b⁻¹) → a⁻¹ * x₁⁻¹ ∈ next (c * b * a⁻¹ * x₁⁻¹)
  | .base h1, .base h2 => .base $ ok.eq1722 h1 h2
  | .base h1, .new e rfl => by
    refine (.extra ⟨h1, e.symm⟩ ?_ rfl)
    rw [← e]
    group
  | .new rfl rfl, .base he => by
    exfalso
    have := forgetOld_old (old_dom he)
    aesop
  | .extra (.mk h1 q1) rfl rfl, .base h2 => by
    group at h2
    have := forgetOld_old (old_dom h2)
    aesop
  | .base h1, .extra (.mk h q) he rfl
  | .new rfl rfl, .new he rfl
  | .new rfl rfl, .extra (.mk h q) he rfl
  | .extra (.mk h1 q1) rfl rfl, .new he rfl => by
    exfalso
    apply_fun forgetOld old at he
    aesop
  | .extra h rfl rfl, .extra (.mk h2 q2) he rfl => by
    simp only [mul_inv_rev, inv_inv, mul_right_eq_self] at he
    apply_fun (fun g => x₁⁻¹ * g) at he
    simp only [inv_mul_cancel_left, mul_one] at he
    exact (h.ne_x1inv he.symm).elim

theorem next_aux {a b c d} : b ∈ next a → d ∈ next c → a * b⁻¹ = c * d⁻¹ → a = c
  | .base h1, .base h2, e => ok.aux h1 h2 e
  | .new rfl _, .new rfl _, _ => rfl
  | .base h, .new rfl rfl, he  | .new rfl rfl, .base h, he
  | .base h, .extra (.mk h1 q) rfl rfl, he | .extra (.mk h1 q) rfl rfl, .base h, he
  | .new rfl rfl, .extra (.mk h1 q) rfl rfl, he | .extra (.mk h1 q) rfl rfl, .new rfl rfl, he => by
    exfalso
    apply_fun forgetOld old at he
    aesop
  | .extra h1 rfl rfl, .extra h2 rfl rfl, he => by rw [h1.unique h2] at he


theorem next_ok : next.OK where
  finite := by
    have : {a | Relevant a}.Subsingleton := fun _ h1 _ h2 => h1.unique h2
    refine (ok.finite.union <| (.insert (d, c)
    (this.finite.map fun a => ((c *d⁻¹* x₁⁻¹),(a⁻¹ * x₁⁻¹))))).subset fun (x,y) hx => ?_
    simp only [Set.mem_setOf_eq] at hx
    match hx with
    | .extra h rfl rfl =>
      simp only [Set.union_insert, Set.mem_insert_iff, Prod.mk.injEq, Set.mem_union,
        Set.mem_setOf_eq]
      right
      right
      simp only [Set.fmap_eq_image, Set.mem_image, Set.mem_setOf_eq, Prod.mk.injEq, mul_left_inj,
        mul_right_inj, and_self, Prod.exists, exists_and_right, exists_eq_right]
      exact ⟨_, h, True.intro, rfl⟩
    | .new rfl rfl => tauto
    | .base h => simp [h]
  func {a} := next_func
  base := Next.base ∘ ok.base
  eq1722 {a b} := next_eq1722
  aux {a b c d} := next_aux

end Extension1

variable (e₀ : Extension)

theorem exists_extension :
    ∃ op : A → A,
    (∀ x, op (op (x * (op x)⁻¹) * op x * x⁻¹*(op 1)⁻¹) = x⁻¹ * (op 1)⁻¹) ∧
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
  · let S : Finset A := {x, x * (op x)⁻¹, 1, op (x * (op x)⁻¹)*(op x)*x⁻¹*(op 1)⁻¹}
    have ⟨⟨e, he⟩, le⟩ := hc.directed.finset_le (hι := ⟨⟨_, h1⟩⟩)
      (S.image fun a => ⟨⟨f a, hf1 a⟩, hf2 a⟩)
    replace le a ha := Finset.forall_image.1 le a ha _ (hop a)
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, S] at le
    obtain ⟨opx, opopxxinv, op1, opfinal⟩ := le
    have eq : op 1 = x₁ := e.2.func op1 (e.2.base (by decide))
    exact e.2.func opfinal (eq.symm ▸ e.2.eq1722 opx opopxxinv)
  · exact (hf1 ..).func (h2 _ (hf2 x) _ h) (hop ..)



def GreedyMagma (_ : Extension) := A

def f (e₀ : Extension) : A → A := (exists_extension e₀).choose

theorem f_eq1722 (e₀ : Extension) : (∀ x, f e₀ (f e₀ (x*(f e₀ x)⁻¹)* (f e₀ x)*x⁻¹*(f e₀ 1)⁻¹) = x⁻¹ * (f e₀ 1)⁻¹) :=
  (exists_extension e₀).choose_spec.1

theorem f_base (e₀ : Extension) :∀ {x y: GreedyMagma e₀}, y ∈ e₀.1 x → y = f e₀ x :=
  (exists_extension e₀).choose_spec.2

def op (e₀ : Extension) (x y : A) : A := f e₀ (y*x⁻¹) * x

noncomputable instance instMagma : Magma (GreedyMagma e₀) where
  op x y:= op e₀ x y

theorem eq1722 : Equation1722 (GreedyMagma e₀) := by
  intro x y
  repeat rw [Magma.op, instMagma]
  simp only
  repeat rw [op]
  unfold GreedyMagma at *
  have := f_eq1722 e₀ (y * x⁻¹)
  symm
  apply_fun (fun g => g * (x * y⁻¹ * (f e₀ 1)⁻¹)⁻¹) at this
  apply eq_of_mul_inv_eq_one
  group at *
  assumption

theorem fromList_ok {S : List (A × A)}
    (func : ∀ a ∈ S, ∀ b ∈ S, a.1 = b.1 → a.2 = b.2 := by decide)
    (base : ∀ a ∈ E0List, a ∈ S := by decide)
    (eq1722 : ∀ a ∈ S, ∀ b ∈ S, b.1 = a.1 * a.2⁻¹ → (b.2*a.2*a.1⁻¹*x₁⁻¹, a.1⁻¹*x₁⁻¹) ∈ S := by decide)
    (aux : ∀ a ∈ S, ∀ b ∈ S, a.1*a.2⁻¹ = b.1*b.2⁻¹ → a.1 = b.1 := by decide) :
    (fromList S).OK where
  finite := List.finite_toSet S
  base h := base _ h
  func h1 _ h2 := func _ h1 _ h2 rfl
  eq1722 h1 h2 := eq1722 _ h1 _ h2 rfl
  aux h1 h2 h3 := aux _ h1 _ h2 h3

theorem fromList_eval {e : Extension} {S : List (A × A)} (hS : e.1 = fromList S)
    (a b : A) (h : (a, b) ∈ S := by decide) : f e a = b :=
  (f_base e (hS ▸ h)).symm

end
end Greedy

open Greedy

@[equational_result]
theorem not_2737 : ∃ (G : Type) (_ : Magma G), Facts G [1722] [2737] := by
  have ⟨e, he⟩ : ∃ e : Extension, e.1 = fromList
    (E0List ++ [(x₃⁻¹, x₄), (x₄*x₃*x₁⁻¹,x₅),(x₁⁻¹*x₅⁻¹,x₆)]) :=
    ⟨⟨_, fromList_ok⟩, rfl⟩
  refine ⟨GreedyMagma e, inferInstance, eq1722 e, fun h => ?_⟩
  · have := h (x₃) (1 : A)
    repeat rw [Magma.op, instMagma] at this
    simp only at this
    repeat rw [op] at this
    group at this
    rw [fromList_eval he 1 x₁, fromList_eval he (x₃^(-1)) x₄,
    fromList_eval he (x₄*x₃*x₁^(-1)) x₅, fromList_eval he (x₁^(-1)*x₅^(-1)) x₆] at this
    apply Ne.elim _ this
    unfold GreedyMagma -- changes the inequality type, so that decide works
    decide


@[equational_result]
theorem not_3143 : ∃ (G : Type) (_ : Magma G), Facts G [1722] [3143] := by
  have ⟨e, he⟩ : ∃ e : Extension, e.1 = fromList
    (E0List ++ [(x₃*x₁⁻¹, x₄),(x₁⁻¹*x₄⁻¹,x₅),(x₁⁻¹*x₄⁻¹*x₅⁻¹,x₆),(x₆*x₅*x₄,x₄)]) :=
    ⟨⟨_, fromList_ok⟩, rfl⟩
  refine ⟨GreedyMagma e, inferInstance, eq1722 e, fun h => ?_⟩
  · have := h (x₃) (1 : A)
    repeat rw [Magma.op, instMagma] at this
    simp only at this
    repeat rw [op] at this
    group at this
    rw [fromList_eval he 1 x₁, fromList_eval he (x₃*x₁^(-1)) x₄,
    fromList_eval he (x₁^(-1)*x₄^(-1)) x₅, fromList_eval he (x₁^(-1)*x₄^(-1)*x₅^(-1)) x₆] at this
    apply Ne.elim _ this
    unfold GreedyMagma -- changes the inequality type, so that decide works
    decide
end TranslationInvariant
namespace Greedy2
noncomputable section

--TODO: find better name
def adjoinFresh' {F : Type} [fE: FinEnum F]: ℕ ≃ ℕ ⊕ F where
  toFun n := if h: n < fE.card then .inr $ fE.equiv.symm ⟨n,h⟩ else .inl $ n - fE.card
  invFun a := match a with
  | .inl n => n + fE.card
  | .inr f => fE.equiv f
  left_inv n := by
    simp only
    split
    case h_1 h =>
      split at h
      · injection h
      · injection h
        omega
    case h_2 h =>
      split at h
      · injection h with h
        rw [← h]
        simp
      · injection h
  right_inv a := by cases a <;> simp

def adjoinFresh {F : Type} (e : ℕ ≃ ℕ ⊕ F) (m : ℕ) : ℕ ≃ ℕ ⊕ F where
  toFun n := if n < m then .inl n else match e (n - m) with
    | .inl k => .inl (k + m)
    | .inr c => .inr c
  invFun
    | .inl k => if k < m then k else e.symm (.inl (k-m)) + m
    | .inr c => e.symm (.inr c) + m
  left_inv n := by
    dsimp
    by_cases h : n < m
    · simp [h]
    · simp [h]
      split
      cases h' : e (n -m)
      next k' eq' k'' =>
        rw [h'] at eq'
        simp only [Sum.inl.injEq] at eq'
        rw [← eq']
        have  : ¬ k'' + m < m := by omega
        simp only [this, ↓reduceIte, Nat.add_sub_cancel]
        rw [← h']
        simp only [Equiv.symm_apply_apply]
        omega
      · simp_all
      next h' =>
        split at h'
        · simp_all
        next h'' =>
          rw [← h',← h'']
          simp only [Equiv.symm_apply_apply]
          omega
  right_inv a := by
    cases a
    case inl n =>
      simp only
      by_cases h : n < m
      · simp [h]
      · simp only [h, ↓reduceIte, Nat.add_sub_cancel, Equiv.apply_symm_apply]
        have : ¬ (e.symm (Sum.inl (n - m)) + m < m) := by omega
        simp only [this, ↓reduceIte, Sum.inl.injEq]
        omega
    case inr => simp

theorem adjoinFresh_fixed {F : Type} {e : ℕ ≃ ℕ ⊕ F} {m k: ℕ} (h : k  < m) :
  adjoinFresh e m k = .inl k := by unfold adjoinFresh ; simp [h]

theorem adjoinFresh_fixed' {F : Type} {e : ℕ ≃ ℕ ⊕ F} {m k: ℕ} (h : k  < m) :
  (adjoinFresh e m).symm (.inl k) = k := by unfold adjoinFresh ; simp [h]

abbrev PreExtension (α : Type) := α → α → Set α

structure PreExtension.OK {α : Type} (E : PreExtension α) : Prop where
  finite : Set.Finite {x : (α × α) × α | x.2 ∈ E x.1.1 x.1.2}
  func {x y} : Set.Subsingleton (E x y)
  eq1722 {x y xy xyy} : xy ∈ E x y → xyy ∈ E xy y → ∃yy, yy ∈ E y y ∧ x ∈ E yy xyy
  law2 {x y z xy zy} : xy ∈ E x y → zy ∈ E z y → xy = zy → x = z
  law3 {x xx} : xx ∈ E x x → ∃ xxx, ∃ xxxx, xxx ∈ E xx x ∧ xxxx ∈ E xxx x
  law4 {x z zx} : zx ∈ E z x → zx = x → ∃ xx, xx ∈ E x x

private abbrev Equiv.movePreExtension {α β : Type} (e : α ≃ β) (E : PreExtension β) : PreExtension α :=
  fun a b => { c | e c ∈ E (e a) (e b) }

def Equiv.movePreExtensionOK {α β : Type} (e : α ≃ β) (E : PreExtension β) (ok : E.OK) :
  (Equiv.movePreExtension e E).OK where
  finite := by
    apply ok.finite.of_equiv
    constructor
    case toFun =>
      refine fun ⟨((a,b),c),h⟩ => ⟨((e.symm a, e.symm b),e.symm c),?_⟩
      simp_all
    case invFun =>
      refine fun ⟨((a,b),c),h⟩ => ⟨((e a, e b),e c),?_⟩
      simp_all
    case left_inv =>
      refine fun ⟨((a,b),c),h⟩ => ?_
      simp_all
    case right_inv =>
      refine fun ⟨((a,b),c),h⟩ => ?_
      simp_all
  func {x y} z z_mem z' z'_mem := by
    have := ok.func z_mem z'_mem
    simpa
  eq1722 xy_mem xyy_mem := by
    obtain ⟨yy, yy_mem, eq⟩ := ok.eq1722 xy_mem xyy_mem
    exact ⟨e.symm yy, by simpa using yy_mem, by simpa using eq⟩
  law2 xy_mem zy_mem eq := by simpa using ok.law2 xy_mem zy_mem (by simpa using eq)
  law3 xx_mem := by
    obtain ⟨xxx, xxxx, h⟩ := ok.law3 xx_mem
    exact ⟨e.symm xxx, e.symm xxxx, by simpa using h⟩
  law4 zx_mem eq := by
    obtain ⟨xx, xx_mem⟩ := ok.law4 zx_mem (by simpa using eq)
    exact ⟨e.symm xx, by simpa using xx_mem⟩


abbrev Extension α:= {E : PreExtension α // E.OK}

class ExtensionBase where
  E : PreExtension ℕ
  ok : E.OK
  a : ℕ
  b : ℕ
  not_def {c} : c ∉ E a b

namespace ExtensionBase
variable [ExtensionBase]

-- Not show how to call this
structure FreshSolution (F : Type) (E' : PreExtension (ℕ ⊕ F)) : Prop where
  base {a b c} : c ∈ E a b → (.inl c) ∈ E' (.inl a) (.inl b)
  ok : E'.OK
  ab_def : (E' (.inl a) (.inl b)).Nonempty

abbrev FreshExtension (F : Type) := {E' : PreExtension (ℕ ⊕ F) // FreshSolution F E'}

scoped infix:80 " ◯ " => E
def dom : Finset ℕ :=
  insert a <| insert b <| ok.finite.toFinset.biUnion fun ((a, b), c) => {a, b, c}

theorem mem_dom {a b c x}
    (h1 : c ∈ a ◯ b) (h2 : x ∈ ({a, b, c} : Finset ℕ)) : x ∈ dom := by
  refine Finset.mem_insert_of_mem <| Finset.mem_insert_of_mem ?_
  simp only [dom, Finset.mem_biUnion, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Prod.exists]
  exact ⟨_, _, _, h1, h2⟩

@[scoped aesop safe forward]
theorem dom_l {a b c} (h : c ∈ a ◯ b) : a ∈ dom := mem_dom h (by simp)
@[scoped aesop safe forward]
theorem dom_r {a b c} (h : c ∈ a ◯ b) : b ∈ dom := mem_dom h (by simp)
@[scoped aesop safe forward]
theorem dom_o {a b c} (h : c ∈ a ◯ b) : c ∈ dom := mem_dom h (by simp)
@[scoped aesop safe forward]
theorem dom_a : a ∈ dom := Finset.mem_insert_self ..
@[scoped aesop safe forward]
theorem dom_b : b ∈ dom := Finset.mem_insert_of_mem <| Finset.mem_insert_self ..

def dom_bound := dom.sup id + 1

theorem lt_dom_bound {x} (h : x ∈ dom) : x < dom_bound := Nat.lt_succ.2 <| dom.le_sup (f := id) h

namespace FreshExtension

variable {F : Type} [FinEnum F] (E' : FreshExtension F)

def adjoin : PreExtension ℕ :=
  Equiv.movePreExtension (adjoinFresh adjoinFresh' dom_bound) E'.1

theorem adjoin_ok : E'.adjoin.OK :=
  Equiv.movePreExtensionOK (adjoinFresh adjoinFresh' dom_bound) E'.1 E'.2.ok

theorem adjoin_le : E ≤ E'.adjoin := by
  intro a b c h
  unfold adjoin Equiv.movePreExtension
  simp only [Set.mem_setOf_eq]
  unfold adjoinFresh
  simp only [Equiv.coe_fn_mk, lt_dom_bound (dom_l h), ↓reduceIte, lt_dom_bound (dom_r h),
    lt_dom_bound (dom_o h)]
  exact E'.2.base h

theorem adjoin_ab_def :
  E'.adjoin ∈ { e : (PreExtension ℕ) | Nonempty (e a b)} := by
  obtain ⟨c, c_mem⟩ := E'.2.ab_def
  use ((adjoinFresh adjoinFresh' dom_bound).symm c)
  unfold adjoin Equiv.movePreExtension
  simp only [Set.mem_setOf_eq, Equiv.apply_symm_apply]
  unfold adjoinFresh
  simp [lt_dom_bound dom_a, lt_dom_bound dom_b, c_mem]

end FreshExtension
end ExtensionBase
class Extension1 extends ExtensionBase where
  b_eq_a : b = a

namespace Extension1
variable [Extension1]
inductive F
  | ai : Fin 4 → F -- indexed shifted by 1
  | b₀ : F
  | bi : Fin 4 → F -- same
  deriving DecidableEq, Fintype
open F
instance : FinEnum F := FinEnum.ofList [ai 0, ai 1, ai 2, ai 3, b₀, bi 0, bi 1, bi 2, bi 3] (by decide)

open ExtensionBase
--unfold constructors to get better pattern matching
@[scoped aesop unsafe 50% [constructors]]
inductive Next : ℕ ⊕ F → ℕ ⊕ F → ℕ ⊕ F → Prop
  | base {x y z} : z ∈ x ◯ y → Next (.inl x) (.inl y) (.inl z)
  | new : Next (.inl a) (.inl a) (.inr $ ai 0)
  | sq_0 : Next (.inr $ ai 0) (.inr $ ai 0) (.inr $ ai 1)
  | sq_1 : Next (.inr $ ai 1) (.inr $ ai 1) (.inr $ ai 2)
  | sq_2 : Next (.inr $ ai 2) (.inr $ ai 2) (.inr $ ai 3)
  | sq_3 : Next (.inr $ ai 3) (.inr $ ai 3) (.inr $ ai 0)
  | extra1_base : Next (.inr $ ai 0) (.inl a) (.inr b₀)
  | extra1_0 : Next (.inr $ ai 1) (.inr $ ai 0) (.inr $ bi 0)
  | extra1_1 : Next (.inr $ ai 2) (.inr $ ai 1) (.inr $ bi 1)
  | extra1_2 : Next (.inr $ ai 3) (.inr $ ai 2) (.inr $ bi 2)
  | extra1_3 : Next (.inr $ ai 0) (.inr $ ai 3) (.inr $ bi 3)
  | extra2_base : Next (.inr b₀) (.inl a) (.inr $ ai 1)
  | extra2_0 : Next (.inr $ bi 0) (.inr $ ai 0) (.inr $ ai 2)
  | extra2_1 : Next (.inr $ bi 1) (.inr $ ai 1) (.inr $ ai 3)
  | extra2_2 : Next (.inr $ bi 2) (.inr $ ai 2) (.inr $ ai 0)
  | extra2_3 : Next (.inr $ bi 3) (.inr $ ai 3) (.inr $ ai 1)
  | extra3_0 : Next (.inr $ ai 2) (.inr $ ai 0) (.inr $ ai 0)
  | extra3_1 : Next (.inr $ ai 3) (.inr $ ai 1) (.inr $ ai 1)
  | extra3_2 : Next (.inr $ ai 0) (.inr $ ai 2) (.inr $ ai 2)
  | extra3_3 : Next (.inr $ ai 1) (.inr $ ai 3) (.inr $ ai 3)
  | extra4_0 : Next (.inr $ ai 0) (.inr $ ai 1) (.inr $ ai 0)
  | extra4_1 : Next (.inr $ ai 1) (.inr $ ai 2) (.inr $ ai 1)
  | extra4_2 : Next (.inr $ ai 2) (.inr $ ai 3) (.inr $ ai 2)
  | extra4_3 : Next (.inr $ ai 3) (.inr $ ai 0) (.inr $ ai 3)
  | extra5_base : Next (.inr $ ai 0) (.inr b₀) (.inl a)
  | extra5_0 : Next (.inr $ ai 1) (.inr $ bi 0) (.inr $ ai 0)
  | extra5_1 : Next (.inr $ ai 2) (.inr $ bi 1) (.inr $ ai 1)
  | extra5_2 : Next (.inr $ ai 3) (.inr $ bi 2) (.inr $ ai 2)
  | extra5_3 : Next (.inr $ ai 0) (.inr $ bi 3) (.inr $ ai 3)

@[scoped aesop safe destruct]
theorem not_def' {c} : c ∉ E a a := b_eq_a ▸ not_def (c:= c)

abbrev next : PreExtension (ℕ ⊕ F) := fun a b => {c | Next a b c}

theorem next_func : ∀ {x y}, Set.Subsingleton (next x y) := by
  intro x y z z_mem z' z'_mem
  cases z_mem <;>
  cases z'_mem <;> try rfl
  case base.base x y z z_mem z' z'_mem =>
    congr
    exact ok.func z_mem z'_mem
  all_goals exfalso ; apply not_def' ; assumption

theorem next_law2 {x y z xy zy} : xy ∈ next x y → zy ∈ next z y → xy = zy → x = z := by
  intro xy_mem zy_mem eq
  rw [eq] at xy_mem
  cases xy_mem <;> cases zy_mem
  case base.base xy_mem _ zy_mem =>
    simp only [Sum.inl.injEq]
    exact ok.law2 xy_mem zy_mem rfl
  all_goals rfl

theorem next_law3 {x xx} : xx ∈ next x x → ∃ xxx, ∃ xxxx, xxx ∈ next xx x ∧ xxxx ∈ next xxx x := by
  intro xx_mem
  cases xx_mem
  case base h =>
    obtain ⟨xxx, xxxx, xxx_mem, eq⟩ := ok.law3 h
    exact ⟨.inl xxx, .inl xxxx, .base xxx_mem, .base eq⟩
  all_goals simp_all
  all_goals aesop

theorem next_eq1722 {x y xy xyy} : xy ∈ next x y → xyy ∈ next xy y → ∃yy, yy ∈ next y y ∧ x ∈ next yy xyy := by
  intro xy_mem xyy_mem
  cases xy_mem <;> cases xyy_mem
  case base.base xy_mem _ xyy_mem =>
    obtain ⟨yy, yy_mem, eq⟩ := ok.eq1722 xy_mem xyy_mem
    exact ⟨.inl yy, .base yy_mem, .base eq⟩
  case base.new h =>
    obtain ⟨xx, xx_mem⟩ := (ok.law4 h rfl)
    exact (not_def' xx_mem).elim
  all_goals aesop

theorem next_law4 {x z zx} : zx ∈ next z x → zx = x → ∃ xx, xx ∈ next x x := by
  intro zx_mem eq
  rw [eq] at zx_mem
  cases zx_mem
  case base h =>
    obtain ⟨xx, xx_mem⟩ := (ok.law4 h rfl)
    exact ⟨.inl xx, .base xx_mem⟩
  all_goals aesop

def domFresh : Finset (ℕ ⊕F )  := Finset.image (.inl) dom ∪ Finset.image (.inr) Finset.univ

theorem next_ok : next.OK where
  finite := by
    apply Set.Finite.subset (s := ((domFresh ×ˢ domFresh) ×ˢ domFresh).toSet) (Finset.finite_toSet _)
    refine fun ((x,y),z) hx => ?_
    unfold domFresh
    simp at hx ⊢; cases hx with
    | base h => simp [dom_o h, dom_l h, dom_r h]
    | _ => simp [dom_a, dom_b]
  func {x y xy} hxy {xy'} hxy' := next_func hxy hxy'
  law2 := next_law2
  eq1722 := next_eq1722
  law3 := next_law3
  law4 := next_law4

def next_freshSolution : FreshSolution F Next where
  base := Next.base
  ok := next_ok
  ab_def := ⟨.inr (ai 0), b_eq_a ▸ Next.new⟩

end Extension1
class Extension2 extends ExtensionBase where
   a_ne_b : a ≠ b
   bb : ℕ
   bb_mem : bb ∈ E b b

namespace Extension2
variable [Extension2]
open ExtensionBase
attribute [scoped aesop safe destruct] a_ne_b

@[scoped aesop safe destruct]
theorem a_ne_bbb : a ∉ bb ◯ b := by
  intro h
  obtain ⟨bbb,bbbb,bbb_mem,eq⟩ := ok.law3 bb_mem
  obtain a_eq_bbb := ok.func h bbb_mem
  exact not_def (a_eq_bbb ▸ eq)

inductive Relevant : ℕ → Prop
  | mk {d} : a ∈ d ◯ b → Relevant d

theorem Relevant.unique {d d'} : Relevant d → Relevant d' → d = d'
  | .mk h1, .mk h2  => ok.law2 h1 h2 rfl

theorem Relevant.ne_bb {d} : Relevant d → bb ≠ d
  | .mk h, rfl => a_ne_bbb h

inductive Next : ℕ ⊕ Unit → ℕ ⊕ Unit → ℕ ⊕ Unit → Prop
  | base {x y z} : z ∈ x ◯ y → Next (.inl x) (.inl y) (.inl z)
  | new : Next (.inl a) (.inl b) (.inr ())
  | extra {d} : Relevant d → Next (.inl bb) (.inr ()) (.inl d)

abbrev next : PreExtension (ℕ ⊕ Unit) := fun a b => {c | Next a b c}

theorem next_func : ∀ {x y}, Set.Subsingleton (next x y) := by
  intro x y z z_mem z' z'_mem
  cases z_mem
    <;> generalize ha : a = a' at *
    <;> generalize hb : b = b' at *
    <;> generalize hbb : bb = bb' at *
    <;> cases z'_mem <;> try rfl
  case base.base x y z z_mem z' z'_mem =>
    congr
    exact ok.func z_mem z'_mem
  case extra.extra =>
    simp only [Sum.inl.injEq]
    apply Relevant.unique <;> assumption
  all_goals rw [← ha, ← hb, ← hbb] at *
  all_goals exfalso ; apply not_def ; assumption

theorem next_law2 {x y z xy zy} : xy ∈ next x y → zy ∈ next z y → xy = zy → x = z := by
  intro xy_mem zy_mem eq
  rw [eq] at xy_mem
  cases xy_mem <;> cases zy_mem
  case base.base xy_mem _ zy_mem =>
    simp only [Sum.inl.injEq]
    exact ok.law2 xy_mem zy_mem rfl
  all_goals rfl

-- better for pattern matching
theorem next_law3' {x y xx} : x = y → xx ∈ next x y → ∃ xxx, ∃ xxxx, xxx ∈ next xx x ∧ xxxx ∈ next xxx x := by
  intro x_eq_y xx_mem
  cases xx_mem
  case base h =>
    simp only [Sum.inl.injEq] at x_eq_y
    rw [← x_eq_y] at h
    obtain ⟨xxx, xxxx, xxx_mem, eq⟩ := ok.law3 h
    exact ⟨.inl xxx, .inl xxxx, .base xxx_mem, .base eq⟩
  all_goals simp_all
  all_goals aesop

theorem next_eq1722 {x y xy xyy} : xy ∈ next x y → xyy ∈ next xy y → ∃yy, yy ∈ next y y ∧ x ∈ next yy xyy := by
  intro xy_mem xyy_mem
  cases xy_mem <;> cases xyy_mem
  case base.base xy_mem _ xyy_mem =>
    obtain ⟨yy, yy_mem, eq⟩ := ok.eq1722 xy_mem xyy_mem
    exact ⟨.inl yy, .base yy_mem, .base eq⟩
  case base.new h =>
    exact ⟨.inl bb, .base bb_mem, .extra (.mk h)⟩
  case extra.extra h =>
    exact (h.ne_bb rfl).elim

theorem next_law4 {x z zx} : zx ∈ next z x → zx = x → ∃ xx, xx ∈ next x x := by
  intro zx_mem eq
  rw [eq] at zx_mem
  cases zx_mem
  case base h =>
    obtain ⟨xx, xx_mem⟩ := (ok.law4 h rfl)
    exact ⟨.inl xx, .base xx_mem⟩

def domFresh : Finset (ℕ ⊕ Unit)  := Finset.image (.inl) dom ∪ Finset.image (.inr) Finset.univ

theorem next_ok : next.OK where
  finite := by
    apply Set.Finite.subset (s := ((domFresh ×ˢ domFresh) ×ˢ domFresh).toSet) (Finset.finite_toSet _)
    refine fun ((x,y),z) hx => ?_
    unfold domFresh
    simp at hx ⊢; cases hx with
    | base h => simp [dom_o h, dom_l h, dom_r h]
    | new => simp [dom_a, dom_b]
    | extra h => simp [dom_l h.1, dom_o bb_mem]
  func {x y xy} hxy {xy'} hxy' := next_func hxy hxy'
  law2 := next_law2
  eq1722 := next_eq1722
  law3 := next_law3' rfl
  law4 := next_law4

def next_freshSolution : FreshSolution Unit Next where
  base := Next.base
  ok := next_ok
  ab_def := ⟨.inr (), Next.new⟩

end Extension2
open ExtensionBase

theorem liftS : ∀ (E : Extension ℕ) (a: ℕ),
  ∃ E' : Extension ℕ, E ≤ E' ∧ E' ∈ {e : Extension ℕ  | (e.1 a a).Nonempty} := fun ⟨E, ok⟩ a => by
  if h : (E a a).Nonempty then exact ⟨_, le_rfl, h⟩ else
  let E1 : Extension1 :=
    { E, ok, a, b := a, not_def := (fun h' => h ⟨_, h'⟩), b_eq_a := rfl }
  let FE : FreshExtension _ := ⟨_, E1.next_freshSolution⟩
  exact ⟨⟨FE.adjoin,FE.adjoin_ok⟩,FE.adjoin_le, by simpa using FE.adjoin_ab_def⟩

theorem lift : ∀ (E : Extension ℕ) (a b : ℕ),
  ∃ E' : Extension ℕ, E ≤ E' ∧ E' ∈ {e : Extension ℕ | (e.1 a b).Nonempty} := fun ⟨E, ok⟩ a b => by
  if h : (E a b).Nonempty then exact ⟨_, le_rfl, h⟩ else
  if b_eq_a : b = a then exact b_eq_a ▸ liftS ⟨E,ok⟩ a else
  obtain ⟨E',le,⟨bb, bb_mem⟩⟩ := liftS ⟨E, ok⟩ b
  if h' : (E'.1 a b).Nonempty then exact ⟨E',le, h'⟩ else
  let E2 : Extension2 :=
    { E:= E'.1, ok:= E'.2, a, b, not_def := (fun h'' => h' ⟨_, h''⟩), bb, bb_mem, a_ne_b := by tauto }
  let FE : FreshExtension _ := ⟨_, E2.next_freshSolution⟩
  exact ⟨⟨FE.adjoin,FE.adjoin_ok⟩,le_trans le FE.adjoin_le, by simpa using FE.adjoin_ab_def⟩


variable (e₀ : Extension ℕ)

theorem exists_extension :
    ∃ op : ℕ → ℕ → ℕ,
    (∀ x y, x = op (op y y) (op (op x y) y)) ∧
    (∀ {x y z}, z ∈ e₀.1 x y → z = op x y) := by
  classical
  have ⟨c, hc, h1, h2, h3⟩ := exists_greedy_chain (a := e₀)
    (task := fun x : _ × _ => {e | (e.1 x.1 x.2).Nonempty}) fun ⟨E, ok⟩ ⟨a, b⟩ => by
      apply lift
  simp only [Subtype.exists, Prod.forall] at h3
  classical
  choose f hf1 hf2 op hop using h3
  refine ⟨op, fun x y => ?_, fun {x y z} H => ?_⟩
  · let S : Finset _ := {(y,y), (x, y), (op x y, y), (op y y, op (op x y) y)}
    have ⟨⟨e, he⟩, le⟩ := hc.directed.finset_le (hι := ⟨⟨_, h1⟩⟩)
      (S.image fun (a, b) => ⟨⟨f a b, hf1 a b⟩, hf2 a b⟩)
    replace le a ha := Finset.forall_image.1 le a ha _ _ (hop a.1 a.2)
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, S] at le
    obtain ⟨yy, xy, xyy, final⟩ := le
    obtain ⟨yy', yy'_def, eq⟩ := (e.2.eq1722 xy xyy)
    exact e.2.func eq ((e.2.func yy yy'_def) ▸ final)
  · exact (hf1 ..).func (h2 _ (hf2 x y) _ _ H) (hop ..)

def GreedyMagma (_ : Extension ℕ) := ℕ

instance (n) : OfNat (GreedyMagma e₀) n := inferInstanceAs (OfNat Nat n)

noncomputable instance instMagma : Magma (GreedyMagma e₀) where
  op := (exists_extension e₀).choose

theorem Extension.eq1722 : Equation1722 (GreedyMagma e₀) :=
  (exists_extension e₀).choose_spec.1


theorem Extension.base : ∀ {x y z : GreedyMagma e₀}, z ∈ e₀.1 x y → z = x ◇ y :=
  (exists_extension e₀).choose_spec.2

def fromList (S : List ((Nat × Nat) × Nat)) : PreExtension ℕ := fun a b => {c | ((a, b), c) ∈ S}

theorem fromList_ok {S : List ((Nat ×ₗ Nat) × Nat)}
    (sorted : S.Chain' (fun a b => a.1 < b.1) := by decide)
    (eq1722 : ∀ a ∈ S, ∀ b ∈ S, a.1.2 = b.1.2 → a.2 = b.1.1 →
      ∃ c ∈ S, ∃ d ∈ S, c.1.1 = a.1.2 ∧ c.1.2 = a.1.2 ∧ d.1.1 = c.2 ∧ d.1.2 = b.2 ∧ d.2 = a.1.1 := by decide)
    (law2 : ∀ a ∈ S, ∀ b ∈ S, a.1.2 = b.1.2 → a.2 = b.2 → a.1.1 = b.1.1 := by decide)
    (law3 : ∀ a ∈ S, a.1.1 = a.1.2 → ∃ b ∈ S, ∃ c ∈ S, b.1.1 = a.2 ∧ b.1.2 = a.1.1 ∧ c.1.1 = b.2 ∧ c.1.2 = a.1.1 := by decide)
    (law4 : ∀ a ∈ S, a.1.2 = a.2 → ∃ b ∈ S, b.1.1 = a.1.2 ∧ b.1.2 = a.1.2 := by decide) :
    (fromList S).OK where
  finite := List.finite_toSet S
  func h1 _ h2 := Decidable.by_contra fun h =>
    have : IsTrans ((ℕ ×ₗ ℕ) × ℕ) (·.1 < ·.1) := ⟨fun _ _ _ => lt_trans⟩
    (List.chain'_iff_pairwise.1 sorted) |>.imp (fun h => h.ne)
      |>.forall (fun _ _ => (·.symm)) h1 h2 (by rintro ⟨⟩; exact h rfl) rfl
  eq1722 h1 h2 := by
    obtain ⟨⟨⟨y, y'⟩,yy⟩, yy_mem, ⟨⟨yy', xyy⟩,x⟩, eq_mem, y_def,
    y'_def, yy'_def, xyy_def, x_def⟩ := eq1722 _ h1 _ h2 rfl rfl
    simp only at yy_mem eq_mem y_def y'_def yy_mem yy'_def xyy_def x_def
    exists yy
    rewrite [y_def, y'_def] at yy_mem
    use yy_mem
    use yy'_def ▸xyy_def ▸ x_def ▸ eq_mem
  law2 h h' eq := law2 _ h _ h' (by simp [eq]) (by simpa)
  law3 h := by
    obtain ⟨⟨⟨x,x'⟩, xxx⟩, xxx_mem, ⟨⟨_, _⟩, _⟩, xxxx_mem, rfl, rfl, rfl, rfl⟩ := law3 _ h rfl
    exact ⟨_, ⟨_,  xxx_mem, xxxx_mem⟩⟩
  law4 h eq := by
    obtain ⟨⟨⟨_, _⟩,_⟩, xx_mem, rfl, h⟩ := law4 _ h (by simp [eq])
    simp only at eq h
    rw [←eq]
    exact ⟨_, eq.symm ▸ (h ▸ xx_mem)⟩

theorem fromList_eval {e : Extension ℕ} {S : List ((Nat × Nat) × Nat)} (hS : e.1 = fromList S)
    (a b c : Nat) (h : ((a, b), c) ∈ S := by decide) :
    haveI : Magma Nat := instMagma e; a ◇ b = c :=
  (Extension.base e (hS ▸ h)).symm

end
end Greedy2
open Greedy2
def seed : List ((Nat × Nat) × Nat) := [
  ((0,0),1),
  ((0,1),2),
  ((1,0),2),
  ((1,1),3),
  ((1,2),0),
  ((1,3),1),
  ((1,4),2),
  ((2,0),3),
  ((2,1),4),
  ((3,0),4),
  ((3,1),1),
  ((3,3),3),
  ((3,4),0),
]

@[equational_result]
theorem not_1832_2644_3050 : ∃ (G : Type) (_ : Magma G), Facts G [1722] [1832,2644,3050] := by
  have ⟨e, he⟩ : ∃ e : Extension ℕ, e.1 = fromList seed :=
    ⟨⟨_, fromList_ok⟩, rfl⟩
  refine ⟨GreedyMagma e, inferInstance, e.eq1722, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := h 0
    rw [fromList_eval he 0 0 1,fromList_eval he 0 1 2,fromList_eval he 2 1 4] at this
    apply Ne.elim _ this
    unfold GreedyMagma
    simp
  · have := h 0
    rw [fromList_eval he 0 0 1,fromList_eval he 1 1 3,fromList_eval he 3 0 4] at this
    apply Ne.elim _ this
    unfold GreedyMagma
    simp
  · have := h 0
    rw [fromList_eval he 0 0 1,fromList_eval he 1 0 2,fromList_eval he 2 0 3,fromList_eval he 3 0 4] at this
    apply Ne.elim _ this
    unfold GreedyMagma
    simp
end Eq1722
