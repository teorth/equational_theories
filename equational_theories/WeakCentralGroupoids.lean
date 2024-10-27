import equational_theories.Mathlib.Order.Greedy
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.PFun
import Mathlib.Order.Part
import Mathlib.Tactic.DeriveFintype

class WeakCentralGroupoid (G : Type*) extends Magma G where
  /-- equation 1485 -/
  eqn (x y z : G) : (y ◇ x) ◇ (x ◇ (z ◇ y)) = x

class RelaxedVeryWeakCentralGroupoid (G : Type*) extends Magma G where
  Path : G → G → Prop
  IsGood : G → G → G → Prop
  op_isGood (x y : G) : IsGood x (x ◇ y) y
  isGood_path {x y z : G} : IsGood x y z → Path x y ∧ Path y z

class RelaxedVeryWeakCentralGroupoid.IsWeak (G : Type*)
    [RelaxedVeryWeakCentralGroupoid G] : Prop where
  isGood_five {a b c d e : G} : IsGood a b c → IsGood c d e → Path e a → IsGood b c d

def RelaxedVeryWeakCentralGroupoid.IsStrict (G : Type*) [RelaxedVeryWeakCentralGroupoid G] : Prop :=
  ∀ {{x y z : G}}, IsGood x y z → y = x ◇ z

namespace WeakCentralGroupoid

variable {G : Type*} [WeakCentralGroupoid G]

theorem eqn1485 : Equation1485 G := fun _ _ _ => (eqn ..).symm

  /-- equation 2162 -/
theorem dual_eqn (x y z : G) : ((y ◇ z) ◇ x) ◇ (x ◇ y) = x := by
  conv in _ ◇ y => rw [← eqn y, eqn z z z]
  apply eqn

def Path (x y : G) : Prop := ∃ z, x = z ◇ y

theorem Path.def' {x y : G} : Path x y ↔ ∃ z, x ◇ z = y := by
  constructor <;> rintro ⟨z, rfl⟩
  · exact ⟨_, by rw [← eqn z z z, dual_eqn]⟩
  · exact ⟨_, by rw [← eqn z z z, eqn]⟩

def IsGood (x y z : G) : Prop := y = x ◇ z

theorem isGood_five {a b c d e : G} : IsGood a b c → IsGood c d e → Path e a → IsGood b c d := by
  rintro rfl rfl ⟨_, rfl⟩; exact (eqn ..).symm

variable (G) in
instance toRelaxed : RelaxedVeryWeakCentralGroupoid G where
  Path := Path
  IsGood := IsGood
  isGood_path := fun h => ⟨Path.def'.2 ⟨_, h.symm⟩, ⟨_, h⟩⟩
  op_isGood _ _ := rfl

instance : (toRelaxed G).IsWeak where
  isGood_five := isGood_five

variable (G) in
theorem toRelaxed.isStrict : (toRelaxed G).IsStrict := by
  rintro _ _ _ rfl; rfl

end WeakCentralGroupoid

namespace RelaxedWeakCentralGroupoid
open RelaxedVeryWeakCentralGroupoid

def strictify {G : Type*} [inst : RelaxedVeryWeakCentralGroupoid G] [inst.IsWeak]
    (H : IsStrict G) : WeakCentralGroupoid G where
  eqn _ _ _ := .symm <| H <|
    IsWeak.isGood_five (op_isGood ..) (op_isGood ..) ((isGood_path (op_isGood ..)).2)

end RelaxedWeakCentralGroupoid

namespace RelaxedVeryWeakCentralGroupoid
namespace Greedy
universe u
variable {G : Type u} [RelaxedVeryWeakCentralGroupoid G]

variable (G) in
def ExtBase := G × Nat

instance [Countable G] : Countable (ExtBase G) := inferInstanceAs (Countable (_ × _))

variable (G) in
abbrev PreExtension := Finset (ExtBase G × ExtBase G)

def PreExtension.induced (E : PreExtension G) (x y : ExtBase G) : Set (ExtBase G) :=
  {z | IsGood x.1 z.1 y.1 ∧ (x, z) ∈ E ∧ (z, y) ∈ E}

theorem PreExtension.induced_mono {E E' : PreExtension G} (H : E ≤ E') {x y : ExtBase G} :
    E.induced x y ⊆ E'.induced x y :=
  fun _ ⟨h1, h2, h3⟩ => ⟨h1, H h2, H h3⟩

structure PreExtension.OK (E : PreExtension G) : Prop where
  path x y : (x, y) ∈ E → Path x.1 y.1
  consistent x y : Set.Subsingleton (E.induced x y)

variable (G) in
abbrev Extension := {E : PreExtension G // E.OK}

theorem Extension.next (E : Extension G) (a b) :
    ∃ E' : Extension G, E ≤ E' ∧ (E'.1.induced a b).Nonempty := by
  classical if h : (E.1.induced a b).Nonempty then exact ⟨_, le_rfl, h⟩ else
  let ⟨l, hl⟩ := Infinite.exists_not_mem_finset <|
    (insert a <| insert b <| E.1.image (·.1) ∪ E.1.image (·.2)).image (·.2)
  let c : ExtBase G := (a.1 ◇ b.1, l)
  refine ⟨⟨insert (a, c) (insert (c, b) E.1), ?_, fun x y z hz w hw => ?_⟩,
    fun _ => (by simp [·]), c, op_isGood .., by simp⟩
  · simp only [Finset.mem_insert, Prod.mk.injEq, or_imp, and_imp, forall_and,
      forall_eq_apply_imp_iff, forall_eq]
    exact have ⟨h1, h2⟩ := (isGood_path (op_isGood ..)); ⟨h1, h2, E.2.1⟩
  · simp only [PreExtension.induced, Finset.mem_insert, Set.mem_setOf_eq] at hz hw
    have ⟨hl1, hl2, hl3⟩ : a ≠ c ∧ b ≠ c ∧ ∀ {x y} (h : (x, y) ∈ E.1), x ≠ c ∧ y ≠ c := by
      simp only [Finset.image_insert, Finset.mem_insert, Finset.mem_image, Finset.mem_union,
        Prod.exists, exists_and_right, exists_eq_right, not_or, not_exists, not_and, or_imp,
        forall_exists_index, forall_and] at hl
      exact ⟨mt (congrArg (·.2)) (Ne.symm hl.1), mt (congrArg (·.2)) (Ne.symm hl.2.1),
        fun h => ⟨fun e => hl.2.2.1 _ _ h (e ▸ rfl), fun e => hl.2.2.2 _ _ h (e ▸ rfl)⟩⟩
    clear_value c; clear l hl
    obtain ⟨hz1, ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | hz2, hz3⟩ := hz <;> obtain ⟨hw1, ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | hw2, hw3⟩ := hw
    · rfl
    · cases hl1 rfl
    · obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | hz3 := hz3
      · cases hl1 rfl
      · obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | hw3 := hw3
        · cases hl2 rfl
        · cases (hl3 hw2).2 rfl
        · cases h ⟨_, hw1, hw2, hw3⟩
      · cases (hl3 hz3).1 rfl
    · cases hl1 rfl
    · rfl
    · cases (hl3 hw2).1 rfl
    · obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | hw3 := hw3
      · cases hl1 rfl
      · obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | hz3 := hz3
        · cases hl2 rfl
        · cases (hl3 hz2).2 rfl
        · cases h ⟨_, hz1, hz2, hz3⟩
      · cases (hl3 hw3).1 rfl
    · cases (hl3 hz2).1 rfl
    · obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | hz3 := hz3
      · obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | hw3 := hw3
        · rfl
        · cases hl2 rfl
        · cases (hl3 hw3).2 rfl
      · cases (hl3 hz2).2 rfl
      · obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | hw3 := hw3
        · cases (hl3 hz3).2 rfl
        · cases (hl3 hw2).2 rfl
        · exact E.2.2 _ _ ⟨hz1, hz2, hz3⟩ ⟨hw1, hw2, hw3⟩

variable [Countable G]

variable (e₀ : Extension G)

theorem exists_extension :
    ∃ op : ExtBase G → ExtBase G → ExtBase G, ∃ E : ExtBase G → ExtBase G → Prop,
    (∀ a b c, c = op a b ↔ IsGood a.1 c.1 b.1 ∧ E a c ∧ E c b) ∧
    (∀ a b, (a, b) ∈ e₀.1 → E a b) ∧
    (∀ a b, E a b → Path a.1 b.1) := by
  have ⟨c, hc, h1, _, h3⟩ := exists_greedy_chain
    (task := fun x : _ × _ => {e | (e.1.induced x.1 x.2).Nonempty}) (fun E ⟨a, b⟩ => E.next a b) e₀
  simp only [Subtype.exists, Prod.forall] at h3
  choose f hf1 hf2 op hop using h3
  refine ⟨op, fun a b => ∃ e ∈ c, (a, b) ∈ e.1, ?_, fun a b H => ⟨_, h1, H⟩, ?_⟩
  · refine fun a b c => ⟨fun H => ?_, fun ⟨h1, ⟨i, hi, h2⟩, ⟨j, hj, h3⟩⟩ => ?_⟩
    · exact let ⟨h1, h2, h3⟩ := hop a b; H ▸ ⟨h1, ⟨_, hf2 _ _, h2⟩, ⟨_, hf2 _ _, h3⟩⟩
    · have ⟨k, hk, ik, jk⟩ := hc.directedOn _ hi _ hj
      have ⟨l, _, kl, fl⟩ := hc.directedOn _ hk _ (hf2 a b)
      exact l.2.2 _ _ ⟨h1, le_trans ik kl h2, le_trans jk kl h3⟩ ((f ..).induced_mono fl (hop a b))
  · exact fun a b ⟨i, _, hi⟩ => i.2.1 a b hi

def GreedyMagma (_ : Extension G) := ExtBase G

noncomputable instance : Magma (GreedyMagma e₀) where
  op := (exists_extension e₀).choose

noncomputable def Extension.edge : GreedyMagma e₀ → GreedyMagma e₀ → Prop :=
  (exists_extension e₀).choose_spec.choose

theorem Extension.induced' : ∀ a b c, c = a ◇ b ↔ IsGood a.1 c.1 b.1 ∧ e₀.edge a c ∧ e₀.edge c b :=
  (exists_extension e₀).choose_spec.choose_spec.1

theorem Extension.induced : ∀ {a b c}, c = a ◇ b ↔ IsGood a.1 c.1 b.1 ∧ e₀.edge a c ∧ e₀.edge c b :=
  @(e₀.induced')

theorem Extension.base : ∀ {a b}, (a, b) ∈ e₀.1 → e₀.edge a b :=
  @(exists_extension e₀).choose_spec.choose_spec.2.1

theorem Extension.path : ∀ {a b}, e₀.edge a b → Path a.1 b.1 :=
  @(exists_extension e₀).choose_spec.choose_spec.2.2

noncomputable instance [RelaxedVeryWeakCentralGroupoid.IsWeak G] :
    WeakCentralGroupoid (GreedyMagma e₀) where
  eqn _ _ _ := by
    refine .symm <| e₀.induced.2 ⟨?_, ?_⟩
    · exact IsWeak.isGood_five
        (e₀.induced.1 rfl).1 (e₀.induced.1 rfl).1 (e₀.path (e₀.induced.1 rfl).2.2)
    · exact ⟨(e₀.induced.1 rfl).2.2, (e₀.induced.1 rfl).2.1⟩

end Greedy

end RelaxedVeryWeakCentralGroupoid

namespace Refutation_1485

inductive G0 where
  | A
  | B (i : Bool)
  | C (i : Bool)
  deriving Fintype

inductive Path : G0 → G0 → Prop where
  | aa : Path .A .A
  | ab {i} : Path .A (.B i)
  | ba {i} : Path (.B i) .A
  | bc {i} : Path (.B i) (.C !i)
  | cb {i} : Path (.C i) (.B i)
  | cc {i j} : Path (.C i) (.C j)

def Path.bc' {i} : Path (.B !i) (.C i) := by simpa using bc (i := !i)

inductive IsGood' : Bool → Bool → Bool → Prop where
  | mk {i} : IsGood' i (!i) i

theorem isGood'_iff {i j k} : IsGood' i j k ↔ k = i ∧ j = !i :=
  ⟨fun ⟨⟩ => by simp, by rintro ⟨rfl, rfl⟩; constructor⟩

instance {i j k} : Decidable (IsGood' i j k) := decidable_of_iff' _ isGood'_iff

inductive IsBad : G0 → G0 → G0 → Prop where
  | mk {i j k} : ¬IsGood' i j k → IsBad (.C i) (.C j) (.C k)

def IsGood (a b c : G0) : Prop :=
  Path a b ∧ Path b c ∧ ¬IsBad a b c

theorem IsGood.mk' {i j k} (h : IsGood' i j k) : IsGood (.C i) (.C j) (.C k) :=
  ⟨.cc, .cc, fun ⟨h'⟩ => h' h⟩

theorem anti_3457 : ∃ x y z w, IsGood x z x ∧ IsGood z w y ∧ ¬IsGood x z w :=
  ⟨.C true, .B false, .C false, .C false, .mk' ⟨⟩, ⟨.cc, .cb, nofun⟩, (·.2.2 ⟨nofun⟩)⟩

def mod2 (i j : Bool) : {k // i = (j ^^ k)} :=
  ⟨i != j, by revert i j; decide⟩

def isGood_exists : ∀ x y : G0, {z // IsGood x z y}
  | .A, .A => ⟨.A, .aa, .aa, nofun⟩
  | .A, .B j => ⟨.A, .aa, .ab, nofun⟩
  | .A, .C j => ⟨.B !j, .ab, .bc', nofun⟩
  | .B i, .A => ⟨.A, .ba, .aa, nofun⟩
  | .B i, .B j => ⟨.A, .ba, .ab, nofun⟩
  | .B i, .C j => ⟨.C !i, .bc, .cc, nofun⟩
  | .C i, .A => ⟨.B i, .cb, .ba, nofun⟩
  | .C i, .B j => ⟨.C j, .cc, .cb, nofun⟩
  | .C i, .C j => match i, mod2 i j with
    | _, ⟨false, rfl⟩ => ⟨.C !j, .cc, .cc, fun ⟨h⟩ => h (by simp; constructor)⟩
    | _, ⟨true, rfl⟩ => ⟨.B _, .cb, by simpa using Path.bc', nofun⟩

instance : RelaxedVeryWeakCentralGroupoid G0 where
  op x y := (isGood_exists x y).1
  Path := Path
  IsGood := IsGood
  op_isGood x y := (isGood_exists x y).2
  isGood_path := fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩

instance : RelaxedVeryWeakCentralGroupoid.IsWeak G0 where
  isGood_five := fun ⟨ab, bc, abc⟩ ⟨cd, de, cde⟩ ea => by
    use bc, cd; rintro @⟨i, j, k, ijk⟩
    rename_i a e x1 x2; clear bc cd x1 x2
    match (generalizing := true) ab, de, ea with
    | .bc, .cc, .cb => exact cde ⟨fun ⟨⟩ => ijk (by simpa using IsGood'.mk (i := !j))⟩
    | .cc, .cb, .bc => exact abc ⟨fun ⟨⟩ => ijk (by simpa using IsGood'.mk (i := k))⟩
    | .cc (i := u) (j := w), .cc (i := v) (j := v'), .cc =>
      if abc' : IsGood' u w j then ?_ else exact abc ⟨abc'⟩
      if cde' : IsGood' j v v' then ?_ else exact cde ⟨cde'⟩
      cases abc'; cases cde'; exact ijk (by simpa using IsGood'.mk (i := !j))

open RelaxedVeryWeakCentralGroupoid Greedy

@[equational_result]
theorem not_3457 : ∃ (G : Type) (_ : Magma G), Facts G [1485] [3457] := by
  have ⟨x,y,z,w, h1, h2, h3⟩ : ∃ x y z w, IsGood x z x ∧ IsGood z w y ∧ ¬IsGood x z w :=
    ⟨.C true, .B false, .C false, .C false, .mk' ⟨⟩, ⟨.cc, .cb, nofun⟩, (·.2.2 ⟨nofun⟩)⟩
  classical
  let e : Extension G0 := by
    refine let S := {((x,0),(z,2)),((z,2),(x,0)),((z,2),(w,3)),((w,3),(y,1))}; ⟨S, ?_, ?_⟩
    · simp [or_imp, forall_and, isGood_path h1, isGood_path h2, S]
    · intro a b
      let f : ℕ → ExtBase G0 | 1 => (w, 3) | 2 => (x, 0) | _ => (z, 2)
      refine Set.subsingleton_of_forall_eq (a := f b.2) fun u ⟨hu1, hu2, hu3⟩ => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton, S] at hu2 hu3
      obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := hu3 <;> rfl
  refine ⟨GreedyMagma e, inferInstance, WeakCentralGroupoid.eqn1485, fun h => ?_⟩
  have := h (x, 0) (y, 1)
  rw [← (e.induced' (x,0) (x,0) (z,2)).2 ⟨h1, e.base (by simp), e.base (by simp)⟩,
      ← (e.induced' (z,2) (y,1) (w,3)).2 ⟨h2, e.base (by simp), e.base (by simp)⟩] at this
  exact h3 (e.induced.1 this).1

@[equational_result]
theorem not_3511 : ∃ (G : Type) (_ : Magma G), Facts G [1485] [3511] := by
  have ⟨x,y,z,w, h1, h2, h3⟩ : ∃ x y z w, IsGood x z y ∧ IsGood z w x ∧ ¬IsGood x z w :=
    ⟨.C true, .B true, .C true, .C false, ⟨.cc, .cb, nofun⟩, .mk' ⟨⟩, (·.2.2 ⟨nofun⟩)⟩
  classical
  let e : Extension G0 := by
    refine let S := {((x,0),(z,2)),((z,2),(y,1)),((z,2),(w,3)),((w,3),(x,0))}; ⟨S, ?_, ?_⟩
    · simp [or_imp, forall_and, isGood_path h1, isGood_path h2, S]
    · intro a b
      let f : ℕ → ExtBase G0 | 0 => (w, 3) | 2 => (x, 0) | _ => (z, 2)
      refine Set.subsingleton_of_forall_eq (a := f b.2) fun u ⟨hu1, hu2, hu3⟩ => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton, S] at hu2 hu3
      obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := hu3 <;> rfl
  refine ⟨GreedyMagma e, inferInstance, WeakCentralGroupoid.eqn1485, fun h => ?_⟩
  have := h (x, 0) (y, 1)
  rw [← (e.induced' (x,0) (y,1) (z,2)).2 ⟨h1, e.base (by simp), e.base (by simp)⟩,
      ← (e.induced' (z,2) (x,0) (w,3)).2 ⟨h2, e.base (by simp), e.base (by simp)⟩] at this
  exact h3 (e.induced.1 this).1

@[equational_result]
theorem not_2087_2124 : ∃ (G : Type) (_ : Magma G), Facts G [1485] [2087, 2124] := by
  have ⟨x,y,z,w,v, h1, h2, h3, h4, h5⟩ : ∃ x y z w v,
      IsGood y z x ∧ IsGood y z y ∧ IsGood z w x ∧ IsGood x v x ∧ ¬IsGood w x v :=
    ⟨.C true, .A, .B false, .C true, .C false,
      ⟨.ab, .bc, nofun⟩, ⟨.ab, .ba, nofun⟩, ⟨.bc, .cc, nofun⟩, .mk' ⟨⟩, (·.2.2 ⟨nofun⟩)⟩
  classical
  let e : Extension G0 := by
    refine let S := {
      ((y,1),(z,2)),((z,2),(x,0)),((z,2),(y,1)),((z,2),(w,3)),
      ((w,3),(x,0)),((x,0),(v,4)),((v,4),(x,0))}; ⟨S, ?_, ?_⟩
    · simp [or_imp, forall_and, isGood_path h1, isGood_path h2, isGood_path h3, isGood_path h4, S]
    · intro a b
      let f : ℕ → ℕ → ExtBase G0
        | 2, 0 => (w, 3)
        | 2, 2 => (y, 1)
        | 1, _ => (z, 2)
        | 0, _ => (v, 4)
        | _, _ => (x, 0)
      refine Set.subsingleton_of_forall_eq (a := f a.2 b.2) fun u ⟨hu1, hu2, hu3⟩ => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton, S] at hu2 hu3
      obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := hu2 <;> (try rfl) <;>
      obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := hu3 <;> rfl
  refine ⟨GreedyMagma e, inferInstance, WeakCentralGroupoid.eqn1485, fun h => ?_, fun h => ?_⟩
  · have := h (x, 0) (y, 1)
    rw [← (e.induced' (y,1) (x,0) (z,2)).2 ⟨h1, e.base (by simp), e.base (by simp)⟩,
        ← (e.induced' (z,2) (x,0) (w,3)).2 ⟨h3, e.base (by simp), e.base (by simp)⟩,
        ← (e.induced' (x,0) (x,0) (v,4)).2 ⟨h4, e.base (by simp), e.base (by simp)⟩] at this
    exact h5 (e.induced.1 this).1
  · have := h (x, 0) (y, 1)
    rw [← (e.induced' (y,1) (y,1) (z,2)).2 ⟨h2, e.base (by simp), e.base (by simp)⟩,
        ← (e.induced' (z,2) (x,0) (w,3)).2 ⟨h3, e.base (by simp), e.base (by simp)⟩,
        ← (e.induced' (x,0) (x,0) (v,4)).2 ⟨h4, e.base (by simp), e.base (by simp)⟩] at this
    exact h5 (e.induced.1 this).1
