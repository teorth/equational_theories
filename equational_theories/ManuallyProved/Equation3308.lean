import Mathlib.Data.Finset.Order
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Set.Basic

import equational_theories.Mathlib.Data.List.Defs
import equational_theories.Mathlib.Order.Greedy

import equational_theories.Equations.All
import equational_theories.FactsSyntax

namespace Refutation_3308

namespace Greedy
noncomputable section
inductive Fresh
  | c₀ : Fresh
  | c₁ : Fresh
  | c₂ : Fresh
  | c₃ : Fresh
  | c₄ : Fresh
  | c₅ : Fresh
  | c₆ : Fresh
  | c₇ : Fresh
  | c₈ : Fresh
  | c₉ : Fresh
  deriving DecidableEq, Fintype
open Fresh
private abbrev A := ℕ ⊕ Fresh

def adjoinFresh': ℕ ≃ A where
  toFun n := match n with
    | 0 => .inr c₀
    | 1 => .inr c₁
    | 2 => .inr c₂
    | 3 => .inr c₃
    | 4 => .inr c₄
    | 5 => .inr c₅
    | 6 => .inr c₆
    | 7 => .inr c₇
    | 8 => .inr c₈
    | 9 => .inr c₉
    | k + 10 => .inl k
  invFun
    | .inl n => n + 10
    | .inr c₀ => 0
    | .inr c₁ => 1
    | .inr c₂ => 2
    | .inr c₃ => 3
    | .inr c₄ => 4
    | .inr c₅ => 5
    | .inr c₆ => 6
    | .inr c₇ => 7
    | .inr c₈ => 8
    | .inr c₉ => 9
  left_inv n := match n with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => rfl
    | k + 10 => rfl
  right_inv a := by
    cases a
    case inl => rfl
    case inr a => cases a <;> rfl

def adjoinFresh (m : ℕ) : ℕ ≃ A where
  toFun n := if n < m then .inl n else match adjoinFresh' (n - m) with
    | .inl k => .inl (k + m)
    | .inr c => .inr c
  invFun
    | .inl k => if k < m then k else adjoinFresh'.symm (.inl (k-m)) + m
    | .inr c => adjoinFresh'.symm (.inr c) + m
  left_inv n := by
    dsimp
    by_cases h : n < m
    · simp [h]
    · simp [h]
      split
      cases h' : adjoinFresh' (n -m)
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
        have : ¬ (adjoinFresh'.symm (Sum.inl (n - m)) + m < m) := by omega
        simp only [this, ↓reduceIte, Sum.inl.injEq]
        omega
    case inr => simp

abbrev PreExtension (α : Type) := α → α → Set α

structure PreExtension.OK {α : Type} (E : PreExtension α) : Prop where
  finite : Set.Finite {x : (α × α) × α | x.2 ∈ E x.1.1 x.1.2}
  func {x y} : Set.Subsingleton (E x y)
  eq3308 {x y xy yx} : xy ∈ E x y → yx ∈ E y x → ∃ xyx ∈ E x yx, xy ∈ E x xyx
  not_left {x y z} : z ∈ E x y → x ≠ z
  not_right {x y z} : z ∈ E x y → y ≠ z
  right_cancel {x x' y xy} : xy ∈ E x y → xy ∈ E x' y → x = x'
  law3 {x y xy yxy} : xy ∈ E x y → yxy ∈ E y xy → ∃ yx, yx ∈ E y x
  law3' {x y xy xyy} : xy ∈ E x y → xyy ∈ E xy y → ∃ yx, yx ∈ E y x
  law5 {x y w z} : z ∈ E x y → y ∈ E w z → y ≠ z → ∃ yx, yx ∈ E y x

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
  eq3308 xy_mem yx_mem := by
    obtain ⟨xyx, xyx_mem, eq⟩ := ok.eq3308 xy_mem yx_mem
    exact ⟨e.symm xyx, by simpa using xyx_mem, by simpa using eq⟩
  not_left xy_mem h := ok.not_left xy_mem (by simpa using h)
  not_right xy_mem h := ok.not_right xy_mem (by simpa using h)
  right_cancel xy_mem xy_mem' := by simpa using ok.right_cancel xy_mem xy_mem'
  law3 xy_mem yxy_mem := by
    obtain ⟨yx, yx_mem⟩ := ok.law3 xy_mem yxy_mem
    exact ⟨e.symm yx, by simpa using yx_mem⟩
  law3' xy_mem xyy_mem := by
    obtain ⟨yx, yx_mem⟩ := ok.law3' xy_mem xyy_mem
    exact ⟨e.symm yx, by simpa using yx_mem⟩
  law5 xy_mem wz_mem ineq := by
    obtain ⟨yx, yx_mem⟩ := ok.law5 xy_mem wz_mem (by simpa using ineq)
    exact ⟨e.symm yx, by simpa using yx_mem⟩

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
structure FreshSolution (E' : PreExtension A) : Prop where
  base {a b c} : c ∈ E a b → (.inl c) ∈ E' (.inl a) (.inl b)
  ok : E'.OK
  ab_def : (.inr .c₀) ∈ E' (.inl a) (.inl b)

abbrev FreshExtension:= {E' : PreExtension A // FreshSolution E'}

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

variable (E' : FreshExtension)

def adjoin (E' : FreshExtension) : PreExtension ℕ :=
  Equiv.movePreExtension (adjoinFresh dom_bound) E'.1

theorem adjoin_ok (E' : FreshExtension) : E'.adjoin.OK :=
  Equiv.movePreExtensionOK (adjoinFresh dom_bound) E'.1 E'.2.ok

theorem adjoin_le (E' : FreshExtension) : E ≤ E'.adjoin := by
  intro a b c h
  unfold adjoin Equiv.movePreExtension
  simp only [Set.mem_setOf_eq]
  unfold adjoinFresh
  simp only [Equiv.coe_fn_mk, lt_dom_bound (dom_l h), ↓reduceIte, lt_dom_bound (dom_r h),
    lt_dom_bound (dom_o h)]
  exact E'.2.base h

theorem adjoin_ab_def (E' : FreshExtension) :
  E'.adjoin ∈ { e : (PreExtension ℕ) | Nonempty (e a b)} := by
  exists ((adjoinFresh dom_bound).symm (.inr .c₀))
  unfold adjoin Equiv.movePreExtension
  simp only [Set.mem_setOf_eq, Equiv.apply_symm_apply]
  unfold adjoinFresh
  simp [lt_dom_bound dom_a, lt_dom_bound dom_b]
  exact E'.2.ab_def
end FreshExtension


attribute [scoped aesop safe destruct] not_def
attribute [scoped aesop safe forward] ok
attribute [scoped aesop safe forward] PreExtension.OK.func
attribute [scoped aesop safe forward] PreExtension.OK.eq3308
attribute [scoped aesop safe destruct] PreExtension.OK.not_right
attribute [scoped aesop safe destruct] PreExtension.OK.not_left

end ExtensionBase
class Extension1 extends ExtensionBase where
  b_eq_a : b = a

namespace Extension1
variable [Extension1]



open ExtensionBase
@[scoped aesop unsafe 50% [constructors]]
inductive Next : A → A → A → Prop
  | base {x y z} : z ∈ x ◯ y → Next (.inl x) (.inl y) (.inl z)
  | new : Next (.inl a) (.inl a) (.inr c₀)
  | extra0 : Next (.inl a) (.inr c₀) (.inr c₁)
  | extra1 : Next (.inl a) (.inr c₁) (.inr c₀)
  | extra2 : Next (.inr c₀) (.inl a) (.inr c₂)
  | extra3 : Next (.inl a) (.inr c₂) (.inr c₃)
  | extra4 : Next (.inl a) (.inr c₃) (.inr c₁)
  | extra5 : Next (.inr c₀) (.inr c₁) (.inr c₄)
  | extra6 : Next (.inr c₀) (.inr c₄) (.inr c₂)
  | extra7 : Next (.inr c₁) (.inl a) (.inr c₅)
  | extra8 : Next (.inl a) (.inr c₅) (.inr c₆)
  | extra9 : Next (.inl a) (.inr c₆) (.inr c₀)
  | extra10 : Next (.inr c₁) (.inr c₀) (.inr c₇)
  | extra11 : Next (.inr c₁) (.inr c₇) (.inr c₅)
  | extra12 : Next (.inr c₁) (.inr c₄) (.inr c₈)
  | extra13 : Next (.inr c₁) (.inr c₈) (.inr c₇)
  | extra14 : Next (.inr c₀) (.inr c₇) (.inr c₉)
  | extra15 : Next (.inr c₀) (.inr c₉) (.inr c₄)

@[scoped aesop safe destruct]
theorem not_def' {c} : c ∉ E a a := b_eq_a ▸ not_def (c:= c)

abbrev next : PreExtension A := fun a b => {c | Next a b c}

theorem next_func : ∀ {x y}, Set.Subsingleton (next x y) := by
  intro x y z z_mem z' z'_mem
  cases z_mem <;> cases z'_mem <;> try rfl
  case base.base x y z z_mem z' z'_mem =>
    congr
    exact ok.func z_mem z'_mem
  all_goals exfalso ; apply not_def' ; assumption


theorem next_eq3308 {x y xy yx} : xy ∈ next x y → yx ∈ next y x → ∃ xyx ∈ next x yx,
  xy ∈ next x xyx := by
  intro xy_mem yx_mem
  cases xy_mem <;> cases yx_mem
  case base.base xy_mem yx yx_mem =>
    obtain ⟨xyx, xyx_mem, eq⟩ := ok.eq3308 xy_mem yx_mem
    exact ⟨.inl xyx, .base xyx_mem, .base eq⟩
  all_goals aesop

theorem next_not_left {x y z} : z ∈ next x y → x ≠ z := by
  intro xy_mem h
  rw [h] at xy_mem
  cases xy_mem
  case base xy_mem =>
    exact ok.not_left xy_mem rfl

theorem next_not_right {x y z} : z ∈ next x y → y ≠ z := by
  intro xy_mem h
  rw [h] at xy_mem
  cases xy_mem
  case base xy_mem =>
    exact ok.not_right xy_mem rfl

theorem next_law3 {x y xy yxy} : xy ∈ next x y → yxy ∈ next y xy → ∃ yx, yx ∈ next y x := by
  intro xy_mem yxy_mem
  cases xy_mem <;> cases yxy_mem
  case base.base xy_mem _ yxy_mem =>
    obtain ⟨yx, yx_mem⟩ := ok.law3 xy_mem yxy_mem
    exact ⟨.inl yx, .base yx_mem⟩
  case base.new _ c =>
    exfalso
    exact ok.not_right c rfl
  all_goals aesop

theorem next_law3' {x y xy xyy} : xy ∈ next x y → xyy ∈ next xy y → ∃ yx, yx ∈ next y x := by
  intro xy_mem xyy_mem
  cases xy_mem <;> cases xyy_mem
  case base.base xy_mem _ xyy_mem =>
    obtain ⟨yx, yx_mem⟩ := ok.law3' xy_mem xyy_mem
    exact ⟨.inl yx, .base yx_mem⟩
  case base.new _ c =>
    exfalso
    exact ok.not_right c rfl
  all_goals aesop

theorem next_right_cancel {x x' y xy} : xy ∈ next x y → xy ∈ next x' y → x = x' := by
  intro xy_mem xy_mem'
  cases xy_mem <;> cases xy_mem'
  case base.base xy_mem _ xy_mem' =>
    congr
    exact ok.right_cancel xy_mem xy_mem'
  all_goals rfl

theorem next_law5 {x y w z} : z ∈ next x y → y ∈ next w z → y ≠ z → ∃ yx, yx ∈ next y x := by
  intro xy_mem wz_mem
  cases xy_mem <;> cases wz_mem
  case base.base xy_mem _ wz_mem =>
    intro h
    obtain ⟨yx, yx_mem⟩ := ok.law5 xy_mem wz_mem (by simpa using h)
    exact ⟨.inl yx, .base yx_mem⟩
  all_goals aesop

def domFresh : Finset A := Finset.image (.inl) dom ∪ Finset.image (.inr) Finset.univ

theorem next_ok : next.OK where
  finite := by
    apply Set.Finite.subset (s := ((domFresh ×ˢ domFresh) ×ˢ domFresh).toSet) (Finset.finite_toSet _)
    refine fun ((x,y),z) hx => ?_
    unfold domFresh
    simp at hx ⊢; cases hx with
    | base h => simp [dom_o h, dom_l h, dom_r h]
    | _ => simp [dom_a]
  func {x y xy} hxy {xy'} hxy' := next_func hxy hxy'
  eq3308 := next_eq3308
  not_left := next_not_left
  not_right := next_not_right
  law3 := next_law3
  law3' := next_law3'
  right_cancel := next_right_cancel
  law5 := next_law5

def next_freshSolution : FreshSolution Next where
  base := Next.base
  ok := next_ok
  ab_def := b_eq_a ▸ Next.new


end Extension1
class Extension2 extends ExtensionBase where
  a_ne_b : a ≠ b
  d : ℕ
  ba_def : d ∈ E b a

namespace Extension2
variable [Extension2]
--attribute [scoped aesop safe forward] ba_def
open ExtensionBase
@[scoped aesop safe forward]
theorem dom_d : d ∈ dom := dom_o ba_def

@[scoped aesop safe destruct]
theorem b_ne_a (h : b = a) : False :=  a_ne_b h.symm

@[scoped aesop safe destruct]
theorem a_ne_b' (h : a = b) : False :=  a_ne_b h

@[scoped aesop safe destruct]
theorem d_ne_a (h : d = a) : False :=  ok.not_right (h ▸ ba_def) rfl

@[scoped aesop safe destruct]
theorem a_ne_d (h : a = d) : False :=  ok.not_right (h ▸ ba_def) rfl

@[scoped aesop safe destruct]
theorem d_ne_b (h : d = b) : False :=  ok.not_left (h ▸ ba_def) rfl

@[scoped aesop safe destruct]
theorem b_ne_d (h : b = d) : False :=  ok.not_left (h ▸ ba_def) rfl

@[scoped aesop safe destruct]
theorem ad_not_def {x} (h : x ∈ a ◯ d) : False := by
  obtain ⟨x, ab_def⟩ := ok.law3 ba_def h
  exact not_def ab_def

@[scoped aesop safe destruct]
theorem da_not_def {x} (h : x ∈ d ◯ a) : False := by
  obtain ⟨x, ab_def⟩ := ok.law3' ba_def h
  exact not_def ab_def

open ExtensionBase
@[scoped aesop unsafe 50% [constructors]]
inductive Next : A → A → A → Prop
  | base {x y z} : z ∈ x ◯ y → Next (.inl x) (.inl y) (.inl z)
  | new :  Next (.inl a) (.inl b) (.inr c₀)
  | extra0 : Next (.inl b) (.inr c₀) (.inr c₁)
  | extra1 : Next (.inl b) (.inr c₁) (.inl d)
  | extra2 : Next (.inl a) (.inl d) (.inr c₂)
  | extra3 : Next (.inl a) (.inr c₂) (.inr c₀)

abbrev next : PreExtension A := fun a b => {c | Next a b c}

theorem next_func : ∀ {x y}, Set.Subsingleton (next x y) := by
  intro x y z z_mem z' z'_mem
  cases z_mem
    <;> generalize ha : a = a' at *
    <;> generalize hb : b = b' at *
    <;> generalize hd : d = d' at *
    <;> cases z'_mem
    <;> aesop

theorem next_eq3308 {x y xy yx} : xy ∈ next x y → yx ∈ next y x → ∃ xyx ∈ next x yx,
  xy ∈ next x xyx := by
  intro xy_mem yx_mem
  cases xy_mem
    <;> generalize ha : a = a' at *
    <;> generalize hb : b = b' at *
    <;> generalize hd : d = d' at *
    <;> cases yx_mem
  case new.new =>
    exact (a_ne_b ha).elim
  case new.extra2 =>
    exact (a_ne_b hb.symm).elim
  case extra2.new =>
    exact (a_ne_b ha).elim
  case extra2.extra2 =>
    exact (a_ne_d ha).elim
  all_goals
    rw [← ha, ← hb, ← hd] at *
    clear a' b' d' ha hb hd
  case base.base xy_mem yx yx_mem =>
    obtain ⟨xyx, xyx_mem, eq⟩ := ok.eq3308 xy_mem yx_mem
    exact ⟨.inl xyx, .base xyx_mem, .base eq⟩
  case base.new yx yx_mem =>
    have yx_eq_d := ok.func yx_mem ba_def
    exact ⟨.inr c₁, .extra0, yx_eq_d ▸ .extra1⟩
  case new.base yx yx_mem =>
    have yx_eq_d := ok.func yx_mem ba_def
    exact ⟨.inr c₂, yx_eq_d ▸ .extra2, .extra3⟩
  case extra2.base | base.extra2 =>
    exfalso
    apply da_not_def
    assumption

theorem next_not_left {x y z} : z ∈ next x y → x ≠ z := by
  intro xy_mem
  cases xy_mem
  case base h =>
    intro eq
    simp only [Sum.inl.injEq] at eq
    exact ok.not_left h eq
  all_goals aesop

theorem next_not_right {x y z} : z ∈ next x y → y ≠ z := by
  intro xy_mem
  cases xy_mem
  case base h =>
    intro eq
    simp only [Sum.inl.injEq] at eq
    exact ok.not_right h eq
  all_goals aesop

theorem next_law3 {x y xy yxy} : xy ∈ next x y → yxy ∈ next y xy → ∃ yx, yx ∈ next y x := by
  intro xy_mem yxy_mem
  cases xy_mem
    <;> generalize ha : a = a' at *
    <;> generalize hb : b = b' at *
    <;> generalize hd : d = d' at *
    <;> cases yxy_mem
  case extra2.extra3 =>
    exact (d_ne_a hd).elim
  all_goals
    rw [← ha, ← hb, ← hd] at *
    clear a' d' ha hb hd
    try clear b'
  case base.base xy_mem _ yxy_mem =>
    obtain ⟨yx, yx_mem⟩ := ok.law3 xy_mem yxy_mem
    exact ⟨.inl yx, .base yx_mem⟩
  case base.new h =>
    obtain ⟨yx, yx_mem⟩ := ok.law3' h ba_def
    exact ⟨.inl yx, .base yx_mem⟩
  case base.extra2 x h =>
    have x_eq_b : x = b := ok.right_cancel h ba_def
    rw [x_eq_b]
    exact ⟨.inr c₀, .new⟩
  case new.extra0 =>
    exact ⟨.inl d, .base ba_def⟩


theorem next_law3' {x y xy xyy} : xy ∈ next x y → xyy ∈ next xy y → ∃ yx, yx ∈ next y x := by
  intro xy_mem xyy_mem
  cases xy_mem
    <;> generalize ha : a = a' at *
    <;> generalize hb : b = b' at *
    <;> generalize hd : d = d' at *
    <;> cases xyy_mem
  case extra1.extra1 =>
    exact (d_ne_b hd).elim
  all_goals
    rw [← ha, ← hb, ← hd] at *
    clear a' b' d' ha hb hd
  case base.base xy_mem _ xyy_mem =>
    obtain ⟨yx, yx_mem⟩ := ok.law3' xy_mem xyy_mem
    exact ⟨.inl yx, .base yx_mem⟩
  case base.new h =>
    obtain ⟨yx, yx_mem⟩ := ok.law3 h ba_def
    exact ⟨.inl yx, .base yx_mem⟩
  case base.extra2 h =>
    obtain ⟨yx, yx_mem⟩ := ok.law5 h ba_def d_ne_a
    exact ⟨.inl yx, .base yx_mem⟩

theorem next_right_cancel {x x' y xy} : xy ∈ next x y → xy ∈ next x' y → x = x' := by
  intro xy_mem xy_mem'
  cases xy_mem
    <;> generalize ha : a = a' at *
    <;> generalize hb : b = b' at *
    <;> generalize hd : d = d' at *
    <;> cases xy_mem'
  case base.base xy_mem _ xy_mem' =>
    congr
    exact ok.right_cancel xy_mem xy_mem'
  all_goals rw [← ha, ← hb, ← hd] at *

theorem next_law5 {x y w z} : z ∈ next x y → y ∈ next w z → y ≠ z → ∃ yx, yx ∈ next y x := by
  intro xy_mem wz_mem
  cases xy_mem
    <;> generalize ha : a = a' at *
    <;> generalize hb : b = b' at *
    <;> generalize hd : d = d' at *
    <;> cases wz_mem
  case base.base xy_mem _ wz_mem =>
    intro h
    obtain ⟨yx, yx_mem⟩ := ok.law5 xy_mem wz_mem (by simpa using h)
    exact ⟨.inl yx, .base yx_mem⟩

def domFresh : Finset A := Finset.image (.inl) dom ∪ Finset.image (.inr) Finset.univ

theorem next_ok : next.OK where
  finite := by
    apply Set.Finite.subset (s := ((domFresh ×ˢ domFresh) ×ˢ domFresh).toSet) (Finset.finite_toSet _)
    refine fun ((x,y),z) hx => ?_
    unfold domFresh
    simp at hx ⊢; cases hx with
    | base h => simp [dom_o h, dom_l h, dom_r h]
    | _ => simp [dom_a, dom_b, dom_d]
  func {x y xy} hxy {xy'} hxy' := next_func hxy hxy'
  eq3308 := next_eq3308
  not_left := next_not_left
  not_right := next_not_right
  law3 := next_law3
  law3' := next_law3'
  right_cancel := next_right_cancel
  law5 := next_law5

def next_freshSolution : FreshSolution Next where
  base := Next.base
  ok := next_ok
  ab_def := Next.new

end Extension2

class Extension3 extends ExtensionBase where
  a_ne_b : a ≠ b
  ba_not_def {d} : d ∉ E b a
  a_not_im_b {d} : a ∉ E d b
  b_not_im_a {d} : b ∉ E d a


namespace Extension3
variable [Extension3]
open ExtensionBase

@[scoped aesop safe destruct]
theorem b_ne_a (h : b = a) : False :=  a_ne_b h.symm

@[scoped aesop safe destruct]
theorem a_ne_b' (h : a = b) : False :=  a_ne_b h

attribute [scoped aesop safe destruct] ba_not_def
attribute [scoped aesop safe destruct] a_not_im_b
attribute [scoped aesop safe destruct] b_not_im_a



@[scoped aesop unsafe 50% [constructors]]
inductive Next : A → A → A → Prop
  | base {x y z} : z ∈ x ◯ y → Next (.inl x) (.inl y) (.inl z)
  | new :  Next (.inl a) (.inl b) (.inr c₀)
  | extra0 : Next (.inl b) (.inr c₀) (.inr c₁)
  | extra1 : Next (.inl b) (.inr c₁) (.inr c₂)
  | extra2 : Next (.inl b) (.inl a) (.inr c₂)
  | extra3 : Next (.inl a) (.inr c₂) (.inr c₃)
  | extra4 : Next (.inl a) (.inr c₃) (.inr c₀)

abbrev next : PreExtension A := fun a b => {c | Next a b c}

theorem next_func : ∀ {x y}, Set.Subsingleton (next x y) := by
  intro x y z z_mem z' z'_mem
  cases z_mem
    <;> generalize ha : a = a' at *
    <;> generalize hb : b = b' at *
    <;> cases z'_mem
    <;> aesop

theorem next_eq3308 {x y xy yx} : xy ∈ next x y → yx ∈ next y x → ∃ xyx ∈ next x yx,
  xy ∈ next x xyx := by
  intro xy_mem yx_mem
  cases xy_mem
    <;> generalize ha : a = a' at *
    <;> generalize hb : b = b' at *
    <;> cases yx_mem
  case new.new | extra2.extra2 =>
    exact (a_ne_b ha).elim
  all_goals
    rw [← ha, ← hb] at *
    clear ha hb
    try clear a'
    try clear b'
    aesop


theorem next_not_left {x y z} : z ∈ next x y → x ≠ z := by
  intro xy_mem
  cases xy_mem
  case base h =>
    intro eq
    simp only [Sum.inl.injEq] at eq
    exact ok.not_left h eq
  all_goals aesop

theorem next_not_right {x y z} : z ∈ next x y → y ≠ z := by
  intro xy_mem
  cases xy_mem
  case base h =>
    intro eq
    simp only [Sum.inl.injEq] at eq
    exact ok.not_right h eq
  all_goals aesop

theorem next_law3 {x y xy yxy} : xy ∈ next x y → yxy ∈ next y xy → ∃ yx, yx ∈ next y x := by
  intro xy_mem yxy_mem
  cases xy_mem
    <;> generalize ha : a = a' at *
    <;> generalize hb : b = b' at *
    <;> cases yxy_mem
  all_goals
    rw [← ha, ← hb] at *
    clear ha hb
    try clear a'
    try clear b'
  case base.base xy_mem _ yxy_mem =>
    obtain ⟨yx, yx_mem⟩ := ok.law3 xy_mem yxy_mem
    exact ⟨.inl yx, .base yx_mem⟩
  all_goals aesop



theorem next_law3' {x y xy xyy} : xy ∈ next x y → xyy ∈ next xy y → ∃ yx, yx ∈ next y x := by
  intro xy_mem xyy_mem
  cases xy_mem
    <;> generalize ha : a = a' at *
    <;> generalize hb : b = b' at *
    <;> cases xyy_mem
  all_goals
    rw [← ha, ← hb] at *
    clear ha hb
    try clear a'
    try clear b'
  case base.base xy_mem _ xyy_mem =>
    obtain ⟨yx, yx_mem⟩ := ok.law3' xy_mem xyy_mem
    exact ⟨.inl yx, .base yx_mem⟩
  all_goals aesop

theorem next_right_cancel {x x' y xy} : xy ∈ next x y → xy ∈ next x' y → x = x' := by
  intro xy_mem xy_mem'
  cases xy_mem
    <;> generalize ha : a = a' at *
    <;> generalize hb : b = b' at *
    <;> cases xy_mem'
  case base.base xy_mem _ xy_mem' =>
    congr
    exact ok.right_cancel xy_mem xy_mem'
  all_goals rw [← ha, ← hb] at *

theorem next_law5 {x y w z} : z ∈ next x y → y ∈ next w z → y ≠ z → ∃ yx, yx ∈ next y x := by
  intro xy_mem wz_mem
  cases xy_mem
    <;> generalize ha : a = a' at *
    <;> generalize hb : b = b' at *
    <;> cases wz_mem
  case base.base xy_mem _ wz_mem =>
    intro h
    obtain ⟨yx, yx_mem⟩ := ok.law5 xy_mem wz_mem (by simpa using h)
    exact ⟨.inl yx, .base yx_mem⟩

def domFresh : Finset A := Finset.image (.inl) dom ∪ Finset.image (.inr) Finset.univ

theorem next_ok : next.OK where
  finite := by
    apply Set.Finite.subset (s := ((domFresh ×ˢ domFresh) ×ˢ domFresh).toSet) (Finset.finite_toSet _)
    refine fun ((x,y),z) hx => ?_
    unfold domFresh
    simp at hx ⊢; cases hx with
    | base h => simp [dom_o h, dom_l h, dom_r h]
    | _ => simp [dom_a, dom_b]
  func {x y xy} hxy {xy'} hxy' := next_func hxy hxy'
  eq3308 := next_eq3308
  not_left := next_not_left
  not_right := next_not_right
  law3 := next_law3
  law3' := next_law3'
  right_cancel := next_right_cancel
  law5 := next_law5

def next_freshSolution : FreshSolution Next where
  base := Next.base
  ok := next_ok
  ab_def := Next.new

end Extension3
open ExtensionBase

theorem lift2 : ∀ (E : Extension ℕ) (a b : ℕ), (E.1 b a).Nonempty →
  ∃ E' : Extension ℕ, E ≤ E' ∧ E' ∈ {e : Extension ℕ  | (e.1 a b).Nonempty} := fun ⟨E, ok⟩ a b s => by
  if h : (E a b).Nonempty then exact ⟨_, le_rfl, h⟩ else
  if b_eq_a : b = a then exact ⟨_, le_rfl, b_eq_a ▸ s⟩ else
    let d := s.choose
    let ba_def := s.choose_spec
    let E2 : Extension2 :=
      { E, ok, a, b, not_def := (fun h' => h ⟨_, h'⟩), a_ne_b := by tauto, d, ba_def }
    let FE : FreshExtension := ⟨_, E2.next_freshSolution⟩
    exact ⟨⟨FE.adjoin,FE.adjoin_ok⟩,FE.adjoin_le, by simpa using FE.adjoin_ab_def⟩

theorem lift : ∀ (E : Extension ℕ) (a b : ℕ),
  ∃ E' : Extension ℕ, E ≤ E' ∧ E' ∈ {e : Extension ℕ | (e.1 a b).Nonempty} := fun ⟨E, ok⟩ a b => by
  if h : (E a b).Nonempty then exact ⟨_, le_rfl, h⟩ else
  if b_eq_a : b = a then
    let E1 : Extension1 := { E, ok, a, b, not_def := (fun h' => h ⟨_, h'⟩), b_eq_a }
    let FE : FreshExtension := ⟨_, E1.next_freshSolution⟩
    exact ⟨⟨FE.adjoin,FE.adjoin_ok⟩,FE.adjoin_le, by simpa using FE.adjoin_ab_def⟩
  else if h' : (E b a).Nonempty then
    apply lift2 ; assumption
  else if a_im_b : ∃ x, a ∈ E x b then
    rcases a_im_b with ⟨x, xb_def⟩
    obtain ⟨E',le,⟨y, bx_def⟩⟩ := lift2 ⟨E, ok⟩ b x ⟨a, xb_def⟩
    obtain ⟨ba, ba_def, _⟩ := E'.2.eq3308 bx_def (le _ _ xb_def)
    obtain ⟨E'',le',⟨ab, ab_def⟩⟩ := lift2 E' a b ⟨ba, ba_def⟩
    exact ⟨E'', le_trans le le', ⟨ab, ab_def⟩⟩
  else if b_im_a : ∃ x, b ∈ E x a then
    rcases b_im_a with ⟨x, xa_def⟩
    obtain ⟨E',le,⟨y, ax_def⟩⟩ := lift2 ⟨E, ok⟩ a x ⟨b, xa_def⟩
    obtain ⟨ab, ab_def, _⟩ := E'.2.eq3308 ax_def (le _ _ xa_def)
    exact ⟨E',le,⟨ab, ab_def⟩⟩
  else
    let E3 : Extension3 :=
    { E, ok, a, b, not_def := (fun h' => h ⟨_, h'⟩),
      a_ne_b := by tauto, ba_not_def := by tauto, a_not_im_b := by tauto, b_not_im_a := by tauto}
    let FE : FreshExtension := ⟨_, E3.next_freshSolution⟩
    exact ⟨⟨FE.adjoin,FE.adjoin_ok⟩,FE.adjoin_le, by simpa using FE.adjoin_ab_def⟩


variable (e₀ : Extension ℕ)

theorem exists_extension :
    ∃ op : ℕ → ℕ → ℕ,
    (∀ x y, op x y= op x (op x (op y x))) ∧
    (∀ {x y z}, z ∈ e₀.1 x y → z = op x y) := by
  classical
  have ⟨c, hc, h1, h2, h3⟩ := exists_greedy_chain (a := e₀)
    (task := fun x : _ × _ => {e | (e.1 x.1 x.2).Nonempty}) fun ⟨E, ok⟩ ⟨a, b⟩ => by
      apply lift
  simp only [Subtype.exists, Prod.forall] at h3
  classical
  choose f hf1 hf2 op hop using h3
  refine ⟨op, fun x y => ?_, fun {x y z} H => ?_⟩
  · let S : Finset _ := {(x,y), (y,x), (x, op y x), (x, op x (op y x))}
    have ⟨⟨e, he⟩, le⟩ := hc.directed.finset_le (hι := ⟨⟨_, h1⟩⟩)
      (S.image fun (a, b) => ⟨⟨f a b, hf1 a b⟩, hf2 a b⟩)
    replace le a ha := Finset.forall_image.1 le a ha _ _ (hop a.1 a.2)
    simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, S] at le
    obtain ⟨xy, yx, xyx, xxyx⟩ := le
    obtain ⟨xyx', xyx'_def, eq⟩ := (e.2.eq3308 xy yx)
    exact e.2.func eq (e.2.func xyx'_def xyx ▸ xxyx)
  · exact (hf1 ..).func (h2 _ (hf2 x y) _ _ H) (hop ..)

def GreedyMagma (_ : Extension ℕ) := ℕ

instance (n) : OfNat (GreedyMagma e₀) n := inferInstanceAs (OfNat Nat n)

noncomputable instance instMagma : Magma (GreedyMagma e₀) where
  op := (exists_extension e₀).choose

theorem Extension.eq3308 : Equation3308 (GreedyMagma e₀) :=
  (exists_extension e₀).choose_spec.1


theorem Extension.base : ∀ {x y z : GreedyMagma e₀}, z ∈ e₀.1 x y → z = x ◇ y :=
  (exists_extension e₀).choose_spec.2

def fromList (S : List ((Nat × Nat) × Nat)) : PreExtension ℕ := fun a b => {c | ((a, b), c) ∈ S}

theorem fromList_ok {S : List ((Nat ×ₗ Nat) × Nat)}
    (sorted : S.Chain' (fun a b => a.1 < b.1) := by decide)
    (eq3308 : ∀ a ∈ S, ∀ b ∈ S, a.1.1 = b.1.2 → a.1.2 = b.1.1 → ∃ c ∈ S, c.1.1 = a.1.1 ∧ c.1.2 = b.2
    ∧ ∃ d ∈ S, d.1.1 = a.1.1 ∧ d.1.2 = c.2 ∧ d.2 = a.2 := by decide)
    (not_left : ∀ a ∈ S, a.1.1 ≠ a.2 := by decide)
    (not_right : ∀ a ∈ S, a.1.2 ≠ a.2 := by decide)
    (right_cancel : ∀ a ∈ S, ∀ b ∈ S, a.1.2 = b.1.2 → a.2 = b.2 → a.1.1 = b.1.1 := by decide)
    (law3 : ∀ a ∈ S, ∀ b ∈ S, b.1.1 = a.1.2 -> b.1.2 = a.2 →
    ∃ c ∈ S, a.1.1 = c.1.2 ∧ a.1.2 = c.1.1 := by decide)
    (law3' : ∀ a ∈ S, ∀ b ∈ S, b.1.1 = a.2 -> b.1.2 = a.1.2 →
    ∃ c ∈ S, a.1.1 = c.1.2 ∧ a.1.2 = c.1.1 := by decide)
    (law5 : ∀ a ∈ S, ∀ b ∈ S, a.2 = b.1.2 → a.1.2 = b.2 → a.1.2 ≠ b.1.2 →
    ∃ c ∈ S, a.1.1 = c.1.2 ∧ a.1.2 = c.1.1 := by decide) :
    (fromList S).OK where
  finite := List.finite_toSet S
  func h1 _ h2 := Decidable.by_contra fun h =>
    have : IsTrans ((ℕ ×ₗ ℕ) × ℕ) (·.1 < ·.1) := ⟨fun _ _ _ => lt_trans⟩
    (List.chain'_iff_pairwise.1 sorted) |>.imp (fun h => h.ne)
      |>.forall (fun _ _ => (·.symm)) h1 h2 (by rintro ⟨⟩; exact h rfl) rfl
  eq3308 h1 h2 := by
    obtain ⟨⟨⟨x, y⟩,xyx⟩, xyx_mem, xyx_def1, xyx_def2,
    ⟨⟨x', xyx'⟩,xy'⟩, xy'_mem, xy'_def1, xy'_def2, xy'_def3⟩ := eq3308 _ h1 _ h2 rfl rfl
    simp only at xyx_def1 xyx_def2 xy'_def1 xy'_def2 xy'_def3
    exists xyx
    use xyx_def2 ▸ xyx_def1 ▸ xyx_mem
    use xy'_def1 ▸ xy'_def2 ▸ xy'_def3 ▸ xy'_mem
  not_left h := not_left _ h
  not_right h := not_right _ h
  right_cancel h h':= right_cancel _ h _ h' rfl rfl
  law3 h h':= by
    obtain ⟨⟨⟨y, x⟩,yx⟩, yx_mem, yx_def1, yx_def2⟩ := law3 _ h _ h' rfl rfl
    simp only at yx_def1 yx_def2
    exact ⟨yx, yx_def1 ▸ yx_def2 ▸ yx_mem⟩
  law3' h h':= by
    obtain ⟨⟨⟨y, x⟩,yx⟩, yx_mem, yx_def1, yx_def2⟩ := law3' _ h _ h' rfl rfl
    simp only at yx_def1 yx_def2
    exact ⟨yx, yx_def1 ▸ yx_def2 ▸ yx_mem⟩
  law5 h h' ineq := by
    obtain ⟨⟨⟨y, x⟩,yx⟩, yx_mem, yx_def1, yx_def2⟩ := law5 _ h _ h' rfl rfl ineq
    simp only at yx_def1 yx_def2
    exact ⟨yx, yx_def1 ▸ yx_def2 ▸ yx_mem⟩

theorem fromList_eval {e : Extension ℕ} {S : List ((Nat × Nat) × Nat)} (hS : e.1 = fromList S)
    (a b c : Nat) (h : ((a, b), c) ∈ S := by decide) :
    haveI : Magma Nat := instMagma e; a ◇ b = c :=
  (Extension.base e (hS ▸ h)).symm

end
end Greedy

open Greedy
def seed : List ((Nat × Nat) × Nat) := [
  ((0,0),1),
  ((0,1),3),
  ((0,2),4),
  ((0,3),1),
  ((0,4),3),
  ((1,0),2),
  ((1,2),5),
  ((1,3),5),
  ((1,5),2),
  ((2,1),5),
  ((2,5),1),
  ((3,0),4),
  ((3,1),0),
  ((3,4),0),
  ((3,5),4),
  ((4,0),3),
  ((4,3),0),
  ((5,1),2),
  ((5,2),1)
]

@[equational_result]
theorem not_3456_3511 : ∃ (G : Type) (_ : Magma G), Facts G [3308] [3456,3511] := by
  have ⟨e, he⟩ : ∃ e : Extension ℕ, e.1 = fromList seed :=
    ⟨⟨_, fromList_ok⟩, rfl⟩
  refine ⟨GreedyMagma e, inferInstance, e.eq3308, fun h => ?_, fun h => ?_⟩
  · have := h 0
    rw [fromList_eval he 0 0 1,fromList_eval he 1 0 2,fromList_eval he 0 2 4] at this
    apply Ne.elim _ this
    unfold GreedyMagma
    simp
  · have := h 0 0
    rw [fromList_eval he 0 0 1,fromList_eval he 1 0 2,fromList_eval he 0 2 4] at this
    apply Ne.elim _ this
    unfold GreedyMagma
    simp
