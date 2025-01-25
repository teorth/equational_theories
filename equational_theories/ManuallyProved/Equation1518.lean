import equational_theories.Mathlib.Data.List.Defs
import equational_theories.Mathlib.Order.Greedy
import Mathlib.Data.Finset.Order
import Mathlib.Data.List.AList
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Functor
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.DeriveFintype

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

namespace Finite

abbrev J := 5

abbrev O := ZMod 7

inductive K where
  | special
  | nonIdem (s : Bool)
  | reg (k : O) (j : ZMod J) (s : Bool)
  deriving Fintype

def K.flip : K → K
  | .special => .special
  | .nonIdem s => .nonIdem !s
  | .reg k j s => .reg k j !s

structure G where
  kind : K
  i : ZMod 6
  deriving Fintype

def G.flip : G → G
  | ⟨k, i⟩ => ⟨k.flip, i⟩

def G.shift : G → ZMod 6 → G
  | ⟨k, i⟩, j => ⟨k, i + j⟩

@[simp] theorem shift_zero (g : G) : g.shift 0 = g := by simp [G.shift]
@[simp] theorem shift_add (g : G) (i j) : (g.shift i).shift j = g.shift (i + j) := by
  simp [G.shift, add_assoc]

theorem eq_shift (g : G) (i) : ∃ g' : G, g = g'.shift i := ⟨g.shift (-i), by simp⟩
theorem shift_eq_self {g : G} {i} (H : g.shift i = g) : i = 0 := by
  simpa [G.shift] using congr_arg (·.2) H

def K.isIdem : K → Bool
  | .nonIdem _ => false
  | _ => true

def G.sq : G → G
  | ⟨.nonIdem s, k⟩ => ⟨.nonIdem s, k + 1⟩
  | g => g

theorem G.sq_n {g : G} (n) (H : sq g = g) : sq^[n] g = g := by induction n <;> simp [H, *]

theorem G.sq_6 (g : G) : sq^[6] g = g := by
  obtain h | ⟨s, k, rfl⟩ : sq g = g ∨ ∃ s k, g = ⟨.nonIdem s, k⟩ := by unfold sq; split <;> simp
  · exact G.sq_n _ h
  · simp [sq, add_assoc]; rfl

inductive MkCycle : (cycle : ZMod 6 → G) → (y : G) → G → G → G → Prop
  | zero {cycle z} : MkCycle cycle z z (cycle 0) (cycle 1)
  | succ {cycle z a b c} : MkCycle (fun x => cycle (x - 1)) z.sq a b c → MkCycle cycle z a b c

theorem MkCycle.inv {cycle k a b c} (H : MkCycle cycle k a b c) :
    ∃ i : ZMod 6, a = G.sq^[i.1] k ∧ b = cycle (-i) ∧ c = cycle (1 - i) := by
  induction H with
  | zero => exact ⟨0, rfl, rfl, rfl⟩
  | @succ _ z _ _ _ _ ih =>
    obtain ⟨i, rfl, rfl, rfl⟩ := ih
    refine ⟨i + 1, ?_, by simp [sub_eq_add_neg, add_comm]⟩
    obtain hi | rfl := Fin.lt_or_eq_of_le (Fin.le_last i)
    · simp [Fin.val_add_one_of_lt hi]
    · simpa using G.sq_6 z

theorem MkCycle.inv' {cycle k a b c} (H : MkCycle cycle k a b c) :
    ∃ i : ZMod 6, a = G.sq^[(-i).1] k ∧ b = cycle i ∧ c = cycle (i + 1) := by
  obtain ⟨i, rfl, rfl, rfl⟩ := H.inv
  exact ⟨-i, by simp [sub_eq_neg_add]⟩

inductive IsReflectingPair' : O → O → ZMod J → Prop
  | zm : IsReflectingPair' 0 (-1) 1
  | zp : IsReflectingPair' 0 1 1
  | p1 : IsReflectingPair' 1 2 0
  | p2 : IsReflectingPair' 2 3 0
  | p3 : IsReflectingPair' 3 1 0
  | m1 : IsReflectingPair' (-1) (-3) 0
  | m2 : IsReflectingPair' (-2) (-1) 0
  | m3 : IsReflectingPair' (-3) (-2) 0

inductive IsReflectingPair : K → K → K → Prop
  | mk {a b c j s} : IsReflectingPair' a b c →
    IsReflectingPair (.reg a j s) (.reg b j s) (.reg (-b) (j + c) s)

def cycle1' (s : Bool) : Fin 6 → K
  | 0 => .nonIdem s
  | 1 => .reg (-1) 0 s
  | 2 => .reg 1 1 s
  | 3 => .reg 0 0 s
  | 4 => .reg (-1) 1 s
  | 5 => .reg 1 0 s
def cycle1 (s : Bool) (i : ZMod 6) : G := ⟨cycle1' s i, 0⟩

theorem cycle1'_inj {i i' s s'} (h1 : cycle1' s i = cycle1' s' i') : (i, s) = (i', s') := by
  fin_cases i <;> fin_cases i' <;> cases h1 <;> rfl

theorem cycle1_inj' {i i' m s s'} (h1 : (cycle1 s i).shift m = cycle1 s' i') :
    (i, s, m) = (i', s', 0) := by
  simp [cycle1, G.shift] at h1; cases cycle1'_inj h1.1; cases h1.2; rfl

def Is05 (i : Fin 6) : Prop := i = 0 ∨ i = 5

inductive ToCycle1 (s : Bool) : G → Prop
  | ni2 : ToCycle1 s ⟨.nonIdem s, 2⟩
  | ni3 : ToCycle1 s ⟨.nonIdem s, 3⟩
  | ni05 {i} : Is05 i → ToCycle1 s ⟨.nonIdem (!s), i⟩
  | r1 : ToCycle1 s ⟨.reg (-1) 0 (!s), 1⟩
  | r5 : ToCycle1 s ⟨.reg 1 0 (!s), 5⟩
  | sp {i} : ¬Is05 i → ToCycle1 s ⟨.special, i⟩

def cycle2 (s : Bool) : ZMod 6 → G
  | 0 => ⟨.nonIdem (!s), 0⟩
  | 1 => ⟨.nonIdem s, 1⟩
  | 2 => ⟨.reg 1 0 (!s), 0⟩
  | 3 => ⟨.reg 1 0 s, 1⟩
  | 4 => ⟨.reg (-1) 0 (!s), 0⟩
  | 5 => ⟨.reg (-1) 0 s, 1⟩

def K.split_sign : K → K × Bool
  | .special => (.special, false)
  | .nonIdem s => (.nonIdem false, s)
  | .reg k j s => (.reg k j false, s)

theorem cycle2_inj {i i' s s'} (h1 : cycle2 s i = cycle2 s' i') : (i, s) = (i', s') := by
  have h2 := congr_arg (·.1.split_sign.1) h1
  have h3 := congr_arg (·.2) h1
  fin_cases i <;> fin_cases i' <;> cases h3 <;> cases h2 <;>
  · have := congr_arg (·.1.split_sign.2) h1
    try replace := Bool.not_inj this
    cases this; rfl

inductive ToCycle3 : Bool → ZMod 6 → Prop
  | _0 : ToCycle3 true 0
  | _1 : ToCycle3 true 1
  | _3 : ToCycle3 false 3
  | _4 : ToCycle3 false 4

def cycle3 : ZMod 6 → G
  | 0 => ⟨.nonIdem true, 0⟩
  | 1 => ⟨.nonIdem true, 1⟩
  | 2 => ⟨.special, 0⟩
  | 3 => ⟨.nonIdem false, 0⟩
  | 4 => ⟨.nonIdem false, 1⟩
  | 5 => ⟨.special, 0⟩

def cycle4' : ZMod 6 → O
  | 0 => -1
  | 1 => 1
  | 2 => -2
  | 3 => 2
  | 4 => -3
  | 5 => 3
def cycle4 (j : ZMod J) (s : Bool) (i : ZMod 6) : G := ⟨.reg (cycle4' i) j s, 0⟩

theorem cycle4'_inj {i i'} (h1 : cycle4' i = cycle4' i') : i = i' := by
  fin_cases i <;> fin_cases i' <;> cases h1 <;> rfl

theorem cycle4_inj' {j j' s s' i i' m} (h1 : (cycle4 j s i).shift m = cycle4 j' s' i') :
    (j, s, i, m) = (j', s', i', 0) := by
  simp [cycle4, G.shift] at h1; simp [h1, cycle4'_inj h1.1.1]

inductive ToCycle4 (j : ZMod J) (s : Bool) : G → Prop
  | _0 : ToCycle4 j s ⟨.nonIdem s, 0⟩
  | _1 : ToCycle4 j s ⟨.reg 0 (j-1) s, 0⟩
  | _2 : ToCycle4 j s ⟨.reg 1 j (!s), 1⟩
  | _3 : ToCycle4 j s ⟨.reg (-1) j (!s), (-1)⟩

def cycle5' (j : ZMod J) (s : Bool) : ZMod 6 → K
  | 0 => .nonIdem s
  | 1 => .reg (-1) j s
  | 2 => .reg 1 (j+1) s
  | 3 => .reg 0 j s
  | 4 => .reg (-1) (j+1) s
  | 5 => .reg 1 j s
def cycle5 (j : ZMod J) (s : Bool) (i : ZMod 6) : G := ⟨cycle5' j s i, 0⟩

def K.split_j : K → K × ZMod J
  | .special => (.special, 0)
  | .nonIdem s => (.nonIdem s, 0)
  | .reg k j s => (.reg k 0 s, j)

theorem cycle5'_inj {j s s' i i'} (h1 : cycle5' j s i = cycle5' j s' i') :
    (s, i) = (s', i') := by
  have h2 := congr_arg (·.split_j.1) h1
  have : (1 : ZMod J) ≠ 0 := nofun
  fin_cases i <;> fin_cases i' <;> cases h2 <;> first | rfl | simp [cycle5', this] at h1

theorem cycle5_inj' {j s s' i i' m} (h1 : (cycle5 j s i).shift m = cycle5 j s' i') :
    (s, i, m) = (s', i', 0) := by
  simp [cycle5, G.shift] at h1; cases cycle5'_inj h1.1; simp [h1]

def ToCycle5 (k : O) : Prop := k = 1 ∨ k = -1

inductive IsCycle : (ZMod 6 → G) → G → Prop
  | cycle1 {s k} : ToCycle1 s k → IsCycle (cycle1 s) k
  | cycle2 {s} : IsCycle (cycle2 s) ⟨.special, 0⟩
  | cycle3 {s i} : ToCycle3 s i → IsCycle cycle3 ⟨.nonIdem s, i⟩
  | cycle4 {j s k} : ToCycle4 j s k → IsCycle (cycle4 j s) k
  | cycle5 {j s k} : ToCycle5 k → IsCycle (cycle5 j s) ⟨.reg k (j - 1) s, 0⟩

inductive Seed : G → G → G → Prop
  | shift1 {k} : k.isIdem → Seed ⟨k, 1⟩ ⟨k, 2⟩ ⟨k, 0⟩
  | shift2 {k} : k.isIdem → Seed ⟨k, 1⟩ ⟨k, 0⟩ ⟨k, 2⟩
  | unshift {x y} : x.1.isIdem → y.1.isIdem → Seed x y ⟨y.1, y.2 - 1⟩
  | reflectL {x y z} : IsReflectingPair x y z → Seed ⟨z, 0⟩ ⟨x, 0⟩ ⟨y, 0⟩
  | reflectR {x y z} : IsReflectingPair x y z → Seed ⟨z, 0⟩ ⟨y, 0⟩ ⟨x, 0⟩
  | cycle {cycle k a b c} : IsCycle cycle k → MkCycle cycle k a b c → Seed a b c

abbrev PreExtension := G → G → Set G

inductive Shift (E : G → G → G → Prop) : G → G → G → Prop
  | mk {a b c i} : E a b c → Shift E (a.shift i) (b.shift i) (c.shift i)

theorem Shift.id {E a b c} : E a b c → Shift E a b c := by simpa using Shift.mk (i := 0)

theorem Shift.shift {E a b c i} : Shift E a b c → Shift E (a.shift i) (b.shift i) (c.shift i) := by
  rintro ⟨⟩; simp; constructor; assumption

theorem Shift.shift_iff {E a b c i} :
    Shift E (a.shift i) (b.shift i) (c.shift i) ↔ Shift E a b c :=
  ⟨fun H => by simpa using H.shift (i := -i), Shift.shift⟩

theorem Shift.idem {E a b c} : Shift (Shift E) a b c ↔ Shift E a b c :=
  ⟨fun ⟨H⟩ => H.shift, fun H => (Shift.shift_iff (i := 0)).1 ⟨H⟩⟩

structure PreExtension.OK (E : PreExtension) : Prop where
  func {a b c c'} : c ∈ E a b → c' ∈ E a b → c = c'
  shift {a b c} : Shift E a b c → c ∈ E a b

structure Task where
  i : ZMod 6
  j : ZMod J
  s : Bool
  k : O
  t : Bool
  deriving Fintype

def Task.base (T : Task) : G := ⟨.reg T.k (T.j - 3) T.t, T.i⟩
def Task.cycle (T : Task) : Fin 6 → G := cycle5 T.j T.s

theorem Task.sq_n_base (T : Task) (n) : G.sq^[n] T.base = T.base := G.sq_n _ rfl

def Task.Done (E : PreExtension) (T : Task) : Prop :=
  {x | E T.base (T.cycle 0) x}.Nonempty

class Extension1 where
  E : PreExtension
  ok : E.OK
  T : Task
  not_done : ¬T.Done E

namespace Extension1
variable [Extension1]
local infix:80 " ◯ " => E

def next : PreExtension := fun a b => {c | c ∈ a ◯ b ∨ Shift (MkCycle T.cycle T.base) a b c}

theorem next_ok : next.OK where
  func {x y u v} hu hv := by
    have {x y u v}
        (hu : Shift (MkCycle T.cycle T.base) x y u) (hv : v ∈ x ◯ y) : u = v := by
      obtain @⟨x, y, u, i, hu⟩ := hu
      obtain ⟨v, rfl⟩ := eq_shift v i
      replace hv := ok.shift (Shift.shift_iff.1 (Shift.id hv)); congr
      obtain ⟨i', rfl, rfl, rfl⟩ := hu.inv'; clear hu
      rw [Task.sq_n_base] at hv
      sorry
    obtain hu | hu := hu <;> obtain hv | hv := hv
    · exact ok.func hu hv
    · exact (this hv hu).symm
    · exact this hu hv
    · obtain @⟨x, y, v, i, hv⟩ := hv
      obtain ⟨u, rfl⟩ := eq_shift u i
      rw [Shift.shift_iff] at hu; congr
      obtain @⟨x, y, u, i, hu⟩ := hu
      obtain ⟨i₁, rfl, rfl, rfl⟩ := hu.inv'
      obtain ⟨i₂, ex, ey, rfl⟩ := hv.inv'; clear hu hv
      cases shift_eq_self (by simpa [Task.sq_n_base] using ex)
      cases cycle5_inj' ey; simp
  shift := by
    rintro _ _ _ ⟨H | H⟩
    · exact .inl (ok.shift ⟨H⟩)
    · exact .inr (.shift H)

end Extension1

abbrev Extension := {E : PreExtension // E.OK}

def seed : Extension where
  val a b := {c | Shift Seed a b c}
  property := {
    func := sorry
    shift := Shift.idem.1
  }

theorem exists_extension : ∃ E : Extension, seed ≤ E ∧ ∀ T : Task, T.Done E := by
  have ⟨c, hc, h1, _, h3⟩ := exists_greedy_chain (a := seed)
    (task := fun T => {e | Task.Done e.1 T}) fun ⟨E, ok⟩ T => by
      if h : T.Done E then exact ⟨_, le_rfl, h⟩ else
      let E1 : Extension1 := { E, ok, T, not_done := h }
      exact ⟨⟨E1.next, E1.next_ok⟩, fun _ _ _ => (.inl ·), _, .inr (.id .zero)⟩
  refine ⟨⟨sSup (Subtype.val '' c), ?_, ?_⟩, ?_, fun T => ?_⟩
  · rintro x y u v
      ⟨_, ⟨⟨_, ⟨_, _, he₁, rfl⟩, rfl⟩, rfl⟩, hu⟩ ⟨_, ⟨⟨_, ⟨_, _, he₂, rfl⟩, rfl⟩, rfl⟩, hv⟩
    dsimp at hu hv
    have ⟨e, _, ee₁, ee₂⟩ := hc.directedOn _ he₁ _ he₂
    exact e.2.func (ee₁ _ _ hu) (ee₂ _ _ hv)
  · rintro _ _ _ ⟨⟨_, ⟨⟨_, ⟨_, e, he, rfl⟩, rfl⟩, rfl⟩, hu⟩⟩
    exact le_sSup (s := Subtype.val '' c) ⟨_, he, rfl⟩ _ _ (e.2.shift ⟨hu⟩)
  · exact le_sSup (s := Subtype.val '' c) ⟨_, h1, rfl⟩
  · have ⟨e, he, z, hz⟩ := h3 T
    exact ⟨z, le_sSup (s := Subtype.val '' c) ⟨_, he, rfl⟩ _ _ hz⟩

end Finite

end Eq1518
