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

namespace Refutation_1485_1483

inductive G0 where
  | hub
  | mid (i : Fin 3)
  | spoke (i : Fin 3)

inductive Path : G0 → G0 → Prop where
  | hm {i} : Path .hub (.mid i)
  | mh {i} : Path (.mid i) .hub
  | mm {i} : Path (.mid i) (.mid (i+1))
  | ms {i} : Path (.mid i) (.spoke i)
  | sm {i} : Path (.spoke i) (.mid i)
  | ss i : Path (.spoke (i+1)) (.spoke i)
  | rfl {i} : Path (.spoke i) (.spoke i)

inductive IsBad : G0 → G0 → G0 → Prop where
  | mk {i j k} : IsBad (.mid i) (.mid j) (.mid k)

def IsGood (a b c : G0) : Prop :=
  Path a b ∧ Path b c ∧ ¬IsBad a b c

theorem anti_1483 : ∃ a b c d e, IsGood a b c ∧ IsGood c d e ∧ Path a e ∧ ¬IsGood b c d :=
  ⟨.spoke 0, .mid 0, .mid 1, .mid 2, .spoke 2, ⟨.sm, .mm, nofun⟩, ⟨.mm, .ms, nofun⟩,
    .ss (i := 2), fun h => h.2.2 .mk⟩

def mod3 (i j : Fin 3) : {k // i = j+k} :=
  ⟨i - j, (add_sub_cancel ..).symm⟩

def mod3' (i j : Fin 3) : i = j ⊕' i = j+1 ⊕' i+1 = j :=
  match mod3 i j with
  | ⟨0, e⟩ => .inl (add_zero j ▸ e)
  | ⟨1, e⟩ => .inr <| .inl e
  | ⟨2, e⟩ => .inr <| .inr <| by rw [e, add_assoc]; apply add_zero

def isGood_exists : ∀ x y : G0, {z // IsGood x z y}
  | .hub, .hub => ⟨.mid 0, .hm, .mh, nofun⟩
  | .hub, .mid j => ⟨.mid (j-1), .hm, by simpa using Path.mm (i := j - 1), nofun⟩
  | .hub, .spoke j => ⟨_, .hm, .ms, nofun⟩
  | .mid i, .hub => ⟨_, .mm, .mh, nofun⟩
  | .mid i, .mid j => ⟨_, .mh, .hm, nofun⟩
  | .mid i, .spoke j => match i, j, mod3' i j with
    | _, i, .inl rfl => ⟨_, .ms, .rfl, nofun⟩
    | _, i, .inr <| .inl rfl => ⟨_, .ms, .ss _, nofun⟩
    | i, _, .inr <| .inr rfl => ⟨_, .mm, .ms, nofun⟩
  | .spoke i, .hub => ⟨_, .sm, .mh, nofun⟩
  | .spoke i, .mid j => match i, j, mod3' i j with
    | _, i, .inl rfl => ⟨_, .rfl, .sm, nofun⟩
    | _, i, .inr <| .inl rfl => ⟨_, .ss _, .sm, nofun⟩
    | i, _, .inr <| .inr rfl => ⟨_, .sm, .mm, nofun⟩
  | .spoke i, .spoke j => match i, mod3 i j with
    | _, ⟨0, rfl⟩ => ⟨_, (add_zero j).symm ▸ .rfl, .rfl, nofun⟩
    | _, ⟨1, rfl⟩ => ⟨_, .ss _, .rfl, nofun⟩
    | _, ⟨2, rfl⟩ => ⟨_, add_assoc j 1 1 ▸ .ss _, .ss _, nofun⟩

instance : RelaxedWeakCentralGroupoid G0 where
  op x y := (isGood_exists x y).1
  Path := Path
  IsGood := IsGood
  op_isGood x y := (isGood_exists x y).2
  isGood_path := fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩
  isGood_left
    | .hm => ⟨.mid 0, .mh, .hm, nofun⟩
    | .mh => ⟨_, .hm, .mh, nofun⟩
    | .mm => ⟨_, .hm, .mm, nofun⟩
    | .ms => ⟨_, .hm, .ms, nofun⟩
    | .sm => ⟨_, .ms, .sm, nofun⟩
    | .ss i => ⟨_, .ms, .ss i, nofun⟩
    | .rfl => ⟨_, .rfl, .rfl, nofun⟩
  isGood_right
    | .hm => ⟨_, .hm, .mh, nofun⟩
    | .mh => ⟨.mid 0, .mh, .hm, nofun⟩
    | .mm => ⟨_, .mm, .mh, nofun⟩
    | .ms => ⟨_, .ms, .sm, nofun⟩
    | .sm => ⟨_, .sm, .mh, nofun⟩
    | .ss i => ⟨_, .ss i, .sm, nofun⟩
    | .rfl => ⟨_, .rfl, .sm, nofun⟩
  isGood_five := fun ⟨ab, bc, abc⟩ ⟨cd, de, cde⟩ ea => by
    use bc, cd; rintro @⟨i⟩; cases bc; cases cd
    generalize eq : i+1+1 = k at de
    match ea with
    | .hm | .mm | .sm => nomatch abc ⟨⟩
    | .mh | .ms => nomatch cde ⟨⟩
    | .ss j | .rfl (i := j) => cases ab; cases de; simp [add_assoc] at eq
