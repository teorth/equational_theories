import equational_theories.ConfluenceSystem

open FreeMagma Confluence
variable {α: Type}

namespace rw115

variable [DecidableEq α]

rule_system rules {x y: FreeMagma α}
| y ⋆ ((x ⋆ x) ⋆ y) => x
| ((y ⋆ y) ⋆ (x ⋆ x)) ⋆ y => x

theorem comp2 {x y : FreeMagma α} (hx: NF rules x):
    rules (y ⋆ rules (x ⋆ x ⋆ y)) = x := by
  generalize h: rules (x ⋆ x ⋆ y) = e
  simp only [rules.elim] at h
  separate
  · apply rules.eq2
  · apply rw_eq_self_of_NF rules hx
  · apply rules.eq1

theorem comp3 {x y : FreeMagma α} (hx: NF rules x):
    rules (y ⋆ rules (rules (x ⋆ x) ⋆ y)) = x := by
  generalize h: rules (x ⋆ x) = e
  simp only [rules.elim] at h
  separate
  exact comp2 hx

@[equational_result]
theorem «Facts» :
  ∃ (G : Type) (_ : Magma G), Facts G [115] [2707, 4273, 4332] := by
  use ConfMagma (@rules Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp only [Magma.op, bu, hx, hy, buFixed_rw_op]
    symm
    congr! 1
    apply comp3 ((NF_iff_buFixed rules).mpr hx)
  all_goals refute

end rw115

namespace rw680

variable [DecidableEq α]

rule_system rules {x y: FreeMagma α}
| (x ⋆ (y ⋆ ((x ⋆ x) ⋆ x))) => y
| (((x ⋆ x) ⋆ x) ⋆ (((x ⋆ x) ⋆ x) ⋆ ((x ⋆ x) ⋆ x))) => x

theorem comp1_2 {x y : FreeMagma α}:
    rules (y ⋆ rules (x ⋆ (y ⋆ y ⋆ y))) = x := by
  generalize h: rules (x ⋆ (y ⋆ y ⋆ y)) = e
  simp only [rules.elim] at h
  separate
  · apply rules.eq2
  · apply rules.eq1

theorem comp1_3 {x y : FreeMagma α}:
    rules (y ⋆ rules (x ⋆ rules (y ⋆ y ⋆ y))) = x := by
  generalize h: rules (y ⋆ y ⋆ y) = e
  simp only [rules.elim] at h
  separate
  apply comp1_2

theorem comp1_4 {x y : FreeMagma α}:
    rules (y ⋆ rules (x ⋆ rules (rules (y ⋆ y) ⋆ y))) = x := by
  generalize h: rules (y ⋆ y) = e
  simp only [rules.elim] at h
  separate
  apply comp1_3

@[equational_result]
theorem «Facts» :
  ∃ (G : Type) (_ : Magma G), Facts G [680] [1629, 1695, 1832, 2847, 2947] := by
  use ConfMagma (@rules Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp (disch := bufixed) only [Magma.op, bu, hx, hy, buFixed_rw_op]
    symm
    congr! 1
    apply comp1_4
  all_goals refute

end rw680

namespace rw1276
variable [DecidableEq α]

rule_system rules {x y: FreeMagma α}
| (x ⋆ (((y ⋆ y) ⋆ y) ⋆ x)) => y
| ((((x ⋆ x) ⋆ x) ⋆ ((y ⋆ y) ⋆ y)) ⋆ x) => y

theorem comp1_2 {x y : FreeMagma α}:
    rules (y ⋆ rules (x ⋆ x ⋆ x ⋆ y)) = x := by
  generalize h: rules (x ⋆ x ⋆ x ⋆ y) = e
  simp only [rules.elim] at h
  separate
  · apply rules.eq2
  · apply rules.eq1

theorem comp1_3 {x y : FreeMagma α}:
    rules (y ⋆ rules (rules (x ⋆ x ⋆ x) ⋆ y)) = x := by
  generalize h: rules (x ⋆ x ⋆ x) = e
  simp only [rules.elim] at h
  separate
  apply comp1_2

theorem comp1_4 {x y : FreeMagma α}:
    rules (y ⋆ rules (rules (rules (x ⋆ x) ⋆ x) ⋆ y)) = x := by
  generalize h: rules (x ⋆ x) = e
  simp only [rules.elim] at h
  separate
  apply comp1_3

@[equational_result]
theorem «Facts» :
  ∃ (G : Type) (_ : Magma G), Facts G [1276] [4273, 4332] := by
  use ConfMagma (@rules Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp (disch := bufixed) only [Magma.op, bu, hx, hy, buFixed_rw_op]
    symm
    congr! 1
    apply comp1_4
  all_goals refute

end rw1276

namespace rw1431
variable [DecidableEq α]

rule_system rules {x y: FreeMagma α}
| ((x ⋆ x) ⋆ (y ⋆ (x ⋆ x))) => x
| (((x ⋆ x) ⋆ (x ⋆ x)) ⋆ x) => (x ⋆ x)

theorem comp1_2 {x y : FreeMagma α}:
    rules ((x ⋆ x) ⋆ rules (y ⋆ (x ⋆ x))) = x := by
  generalize h: rules (y ⋆ (x ⋆ x)) = e
  simp only [rules.elim] at h
  separate
  · apply rules.eq2
  · apply rules.eq1
  · apply rules.eq1

theorem comp1_4 {x y : FreeMagma α}:
    rules (rules (x ⋆ x) ⋆ rules (y ⋆ rules (x ⋆ x))) = x := by
  generalize h: rules (x ⋆ x) = e
  simp only [rules.elim] at h
  separate
  apply comp1_2

@[equational_result]
theorem «Facts» :
  ∃ (G : Type) (_ : Magma G), Facts G [1431] [1428, 4269, 4316] := by
  use ConfMagma (@rules Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp (disch := bufixed) only [Magma.op, bu, hx, hy, buFixed_rw_op]
    symm
    congr! 1
    apply comp1_4
  all_goals refute

end rw1431

namespace rw1519
variable [DecidableEq α]

rule_system rules {x y: FreeMagma α}
| ((x ⋆ x) ⋆ (y ⋆ (x ⋆ x))) => y
| (((x ⋆ x) ⋆ (x ⋆ x)) ⋆ (x ⋆ x)) => (x ⋆ x)

theorem comp1_2 {x y : FreeMagma α} (hx: NF rules x):
    rules (y ⋆ y ⋆ rules (x ⋆ (y ⋆ y))) = x := by
  generalize h: rules (x ⋆ (y ⋆ y)) = e
  simp only [rules.elim] at h
  separate
  · apply rules.eq2
  · apply hx.top
  · apply rules.eq1

theorem comp1_4 {x y : FreeMagma α} (hx: NF rules x):
    rules (rules (y ⋆ y) ⋆ rules (x ⋆ rules (y ⋆ y))) = x := by
  generalize h: rules (y ⋆ y) = e
  simp only [rules.elim] at h
  separate
  apply comp1_2 hx

@[equational_result]
theorem «Facts» :
  ∃ (G : Type) (_ : Magma G), Facts G [1519] [2035, 2128] := by
  use ConfMagma (@rules Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp (disch := bufixed) only [Magma.op, bu, hx, hy, buFixed_rw_op]
    symm
    congr! 1
    apply comp1_4  ((NF_iff_buFixed rules).mpr hx)
  all_goals refute

end rw1519

namespace rw1523

variable [Inhabited α] [DecidableEq α]

rule_system rules {x y z: FreeMagma α} -IsProj
| (y ⋆ y) ⋆ (x ⋆ (y ⋆ y)) => x
| x ⋆ x => default ⋆ default

instance: IsProjOrNF (rules : FreeMagma α → _) where
  proj_or_nf := by
    intro x
    generalize h: rules x = e
    simp only [rules.elim] at h
    separate
    · left
      subterm
    · right
      simp only [NF, Everywhere, and_self_left]
      constructor
      · simp [rules, rules.rule1, rules.rule2]
      · apply rules.eq2
    · left
      rfl

theorem comp1_2 {x : FreeMagma α}:
    rules (default ⋆ default ⋆ rules (x ⋆ (default ⋆ default))) = x := by
  generalize h: rules (x ⋆ (default ⋆ default)) = e
  simp only [rules.elim] at h
  separate
  · apply rules.eq2
  · apply rules.eq1

theorem comp1_4 {x y z : FreeMagma α}:
    rules (rules (y ⋆ y) ⋆ rules (x ⋆ rules (z ⋆ z))) = x := by
  simp [rules.eq2]
  apply comp1_2

@[equational_result]
theorem «Facts» :
  ∃ (G : Type) (_ : Magma G), Facts G [1523] [2035, 2038, 2124, 2128, 2132] := by
  use ConfMagma (@rules Nat _ _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
    simp (disch := bufixed) only [Magma.op, bu, hx, hy, hz, buFixed_rw_op]
    symm
    congr! 1
    apply comp1_4
  all_goals refute

end rw1523

namespace rw1630
variable [DecidableEq α]

rule_system rules {x y: FreeMagma α}
| ((x ⋆ x) ⋆ ((x ⋆ x) ⋆ y)) => x
| ((x ⋆ x) ⋆ x) => x

theorem comp1_2 {x y : FreeMagma α}:
    rules (x ⋆ x ⋆ rules (x ⋆ x ⋆ y)) = x := by
  generalize h: rules (x ⋆ x ⋆ y) = e
  simp only [rules.elim] at h
  separate
  · apply rules.eq2
  · apply rules.eq2
  · apply rules.eq1

theorem comp1_4 {x y : FreeMagma α}:
    rules (rules (x ⋆ x) ⋆ rules (rules (x ⋆ x) ⋆ y)) = x := by
  generalize h: rules (x ⋆ x) = e
  simp only [rules.elim] at h
  separate
  apply comp1_2

@[equational_result]
theorem «Facts» :
  ∃ (G : Type) (_ : Magma G), Facts G [1630] [4268, 4282] := by
  use ConfMagma (@rules Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    simp (disch := bufixed) only [Magma.op, bu, hx, hy, buFixed_rw_op]
    symm
    congr! 1
    apply comp1_4
  all_goals refute

end rw1630

namespace rw3588

variable [DecidableEq α]

rule_system rules {x y z w: FreeMagma α}
| z ⋆ ((x ⋆ y) ⋆ z) => x ⋆ y
| ((z ⋆ w) ⋆ (x ⋆ y)) ⋆ (z ⋆ w) => x ⋆ y

theorem comp2 {x y z : FreeMagma α} (hxy: NF rules (x ⋆ y)):
    rules (z ⋆ rules (x ⋆ y ⋆ z)) = x ⋆ y := by
  generalize h: rules (x ⋆ y ⋆ z) = e
  simp only [rules.elim] at h
  separate
  · apply rules.eq2
  · apply rw_eq_self_of_NF rules hxy
  · apply rules.eq1

theorem comp3 {x y z : FreeMagma α} (hx: NF rules x) (hy: NF rules y):
    rules (z ⋆ rules (rules (x ⋆ y) ⋆ z)) = rules (x ⋆ y) := by
  generalize h: rules (x ⋆ y) = e
  simp only [rules.elim] at h
  separate
  all_goals apply comp2
  · apply Everywhere.left hy
  · apply Everywhere.right hx
  · rw [NF, Everywhere]
    refine ⟨hx, hy, ?_⟩
    simp only [rules.elim]
    right
    constructorm* _ ∧ _
    all_goals trivial

@[equational_result]
theorem «Facts» :
  ∃ (G : Type) (_ : Magma G), Facts G [3588] [3862, 3878, 3917, 3955] := by
  use ConfMagma (@rules Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
    simp only [Magma.op, bu, hx, hy, hz, buFixed_rw_op]
    symm
    congr! 1
    apply comp3 ((NF_iff_buFixed rules).mpr hx) ((NF_iff_buFixed rules).mpr hy)
  all_goals refute

end rw3588
