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
variable (G : Type u) [RelaxedWeakCentralGroupoid G]

def strictify (H : IsStrict G) : WeakCentralGroupoid G where
  eqn _ _ _ := .symm <| H <|
    isGood_five (op_isGood ..) (op_isGood ..) ((isGood_path (op_isGood ..)).2)

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
