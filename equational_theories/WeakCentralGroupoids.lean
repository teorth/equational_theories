import equational_theories.Mathlib.Order.Greedy
import equational_theories.Equations.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.PFun
import Mathlib.Order.Part
import Mathlib.Order.Zorn

class WeakCentralGroupoid (G : Type*) extends Magma G where
  /-- equation 1485 -/
  eqn (x y z : G) : (y ◇ x) ◇ (x ◇ (z ◇ y)) = x

class RelaxedWeakCentralGroupoid (G : Type*) extends Magma G where
  Path : G → G → Prop
  IsGood : G → G → G → Prop
  op_isGood (x y : G) : IsGood x (x ◇ y) y
  isGood_path {x y z : G} : IsGood x y z → Path x y ∧ Path y z
  isGood_left {x y : G} : Path x y → ∃ z, IsGood z x y
  isGood_right {x y : G} : Path x y → ∃ z, IsGood x y z
  isGood_five {a b c d e : G} : IsGood a b c → IsGood c d e → Path e a → IsGood b c d

def RelaxedWeakCentralGroupoid.IsStrict (G : Type*) [RelaxedWeakCentralGroupoid G] : Prop :=
  ∀ {{x y z : G}}, IsGood x y z → y = x ◇ z

namespace WeakCentralGroupoid

variable {G : Type*} [WeakCentralGroupoid G]

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
def toRelaxed : RelaxedWeakCentralGroupoid G where
  Path := Path
  IsGood := IsGood
  isGood_path := fun h => ⟨Path.def'.2 ⟨_, h.symm⟩, ⟨_, h⟩⟩
  op_isGood _ _ := rfl
    -- ⟨⟨⟨x ◇ y, rfl⟩⟩, fun ⟨z, (h : _ = _)⟩ => by simp [h]⟩
  isGood_left h := h
  isGood_right h := (Path.def'.1 h).imp fun _ h => h.symm
  isGood_five := isGood_five

variable (G) in
theorem toRelaxed.isStrict : (toRelaxed G).IsStrict := by rintro _ _ _ rfl; rfl

end WeakCentralGroupoid

namespace RelaxedWeakCentralGroupoid
universe u
variable {G : Type u} [RelaxedWeakCentralGroupoid G]

def strictify (H : IsStrict G) : WeakCentralGroupoid G where
  eqn _ _ _ := .symm <| H <|
    isGood_five (op_isGood ..) (op_isGood ..) ((isGood_path (op_isGood ..)).2)

namespace Greedy

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

variable (G) in
structure GreedyArgs where
  [ct : Countable G]
  e₀ : Extension G
  H E x y : ∃ E' : Extension G, E ≤ E' ∧ (E'.1.induced x y).Nonempty

variable (A : GreedyArgs G)

private theorem exists_extension :
    ∃ op : ExtBase G → ExtBase G → ExtBase G, ∃ E : ExtBase G → ExtBase G → Prop,
    (∀ a b c, c = op a b ↔ IsGood a.1 c.1 b.1 ∧ E a c ∧ E c b) ∧
    (∀ a b, (a, b) ∈ A.e₀.1 → E a b) ∧
    (∀ a b, E a b → Path a.1 b.1) := by
  obtain ⟨e₀, H⟩ := A
  have ⟨c, hc, h1, _, h3⟩ := exists_greedy_chain
    (task := fun x : ExtBase G × ExtBase G => {e : Extension G | (e.1.induced x.1 x.2).Nonempty})
    (fun a ⟨b1, b2⟩ => H a b1 b2) e₀
  simp only [Subtype.exists, Prod.forall] at h3
  choose f hf1 hf2 op hop using h3
  refine ⟨op, fun a b => ∃ e ∈ c, (a, b) ∈ e.1, ?_, fun a b H => ⟨_, h1, H⟩, ?_⟩
  · refine fun a b c => ⟨fun H => ?_, fun ⟨h1, ⟨i, hi, h2⟩, ⟨j, hj, h3⟩⟩ => ?_⟩
    · exact let ⟨h1, h2, h3⟩ := hop a b; H ▸ ⟨h1, ⟨_, hf2 _ _, h2⟩, ⟨_, hf2 _ _, h3⟩⟩
    · have ⟨k, hk, ik, jk⟩ := hc.directedOn _ hi _ hj
      have ⟨l, _, kl, fl⟩ := hc.directedOn _ hk _ (hf2 a b)
      exact l.2.2 _ _ ⟨h1, le_trans ik kl h2, le_trans jk kl h3⟩ ((f ..).induced_mono fl (hop a b))
  · exact fun a b ⟨i, _, hi⟩ => i.2.1 a b hi

def GreedyMagma (_ : GreedyArgs G) := ExtBase G

noncomputable instance : Magma (GreedyMagma A) where
  op := (exists_extension A).choose

noncomputable def GreedyArgs.edge : GreedyMagma A → GreedyMagma A → Prop :=
  (exists_extension A).choose_spec.choose

theorem GreedyArgs.induced :
    ∀ {a b c}, c = a ◇ b ↔ IsGood a.1 c.1 b.1 ∧ A.edge a c ∧ A.edge c b :=
  @(exists_extension A).choose_spec.choose_spec.1

theorem GreedyArgs.base : ∀ {a b}, (a, b) ∈ A.e₀.1 → A.edge a b :=
  @(exists_extension A).choose_spec.choose_spec.2.1

theorem GreedyArgs.path : ∀ {a b}, A.edge a b → Path a.1 b.1 :=
  @(exists_extension A).choose_spec.choose_spec.2.2

noncomputable instance : WeakCentralGroupoid (GreedyMagma A) where
  eqn _ _ _ := by
    refine .symm <| A.induced.2 ⟨?_, ?_⟩
    · exact isGood_five (A.induced.1 rfl).1 (A.induced.1 rfl).1 (A.path (A.induced.1 rfl).2.2)
    · exact ⟨(A.induced.1 rfl).2.2, (A.induced.1 rfl).2.1⟩

end Greedy

end RelaxedWeakCentralGroupoid

namespace Refutation_1485

inductive G0 where
  | A
  | B (i : Bool)
  | C (i : Bool)

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

theorem anti_2087_and_anti_2124 : ∃ x y z w u,
    IsGood y z x ∧ IsGood y z y ∧ IsGood z w x ∧ IsGood x u x ∧ ¬IsGood w x u :=
  ⟨.C true, .A, .B false, .C true, .C false,
    ⟨.ab, .bc, nofun⟩, ⟨.ab, .ba, nofun⟩, ⟨.bc, .cc, nofun⟩, .mk' ⟨⟩, (·.2.2 ⟨nofun⟩)⟩

theorem anti_2124 : ∃ x y z w, IsGood x z y ∧ IsGood z w x ∧ ¬IsGood x z w :=
  ⟨.C true, .B true, .C true, .C false, ⟨.cc, .cb, nofun⟩, .mk' ⟨⟩, (·.2.2 ⟨nofun⟩)⟩

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

instance : RelaxedWeakCentralGroupoid G0 where
  op x y := (isGood_exists x y).1
  Path := Path
  IsGood := IsGood
  op_isGood x y := (isGood_exists x y).2
  isGood_path := fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩
  isGood_left
    | .aa => ⟨_, .aa, .aa, nofun⟩
    | .ab => ⟨_, .aa, .ab, nofun⟩
    | .ba => ⟨_, .ab, .ba, nofun⟩
    | .bc => ⟨_, .ab, .bc, nofun⟩
    | .cb => ⟨_, .bc', .cb, nofun⟩
    | .cc => ⟨_, .bc', .cc, nofun⟩
  isGood_right
    | .aa => ⟨_, .aa, .aa, nofun⟩
    | .ab => ⟨_, .ab, .ba, nofun⟩
    | .ba => ⟨_, .ba, .aa, nofun⟩
    | .bc => ⟨_, .bc, .cb, nofun⟩
    | .cb => ⟨_, .cb, .ba, nofun⟩
    | .cc => ⟨_, .cc, .cb, nofun⟩
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
