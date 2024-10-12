import equational_theories.ConfluenceSystem

open FreeMagma Confluence
variable {α: Type} [DecidableEq α]

namespace rw1443

rule_system rules {x y z: FreeMagma α}
| ((x ⋆ y) ⋆ (x ⋆ (x ⋆ z))) => x
| (x ⋆ ((x ⋆ y) ⋆ x)) => (x ⋆ y)
| (x ⋆ ((x ⋆ y) ⋆ ((x ⋆ y) ⋆ z))) => (x ⋆ y)
| (((x ⋆ y) ⋆ z) ⋆ ((x ⋆ y) ⋆ x)) => (x ⋆ y)

theorem comp1_2 {x y z : FreeMagma α}:
    rules (rules (x ⋆ y) ⋆ (x ⋆ (x ⋆ z))) = x := by
  generalize h: rules (x ⋆ y) = e
  simp only [rules.elim] at h
  separate
  · apply rules.eq3
  · apply rules.eq1
  · apply rules.eq1
  · apply rules.eq3
  · apply rules.eq1

theorem comp1_3 {x y z : FreeMagma α}:
    rules (rules (x ⋆ y) ⋆ rules (x ⋆ (x ⋆ z))) = x := by
  generalize h: rules (x ⋆ (x ⋆ z)) = e
  simp only [rules.elim] at h
  separate
  · apply comp1_2

theorem comp4_2 {x y z : FreeMagma α}:
    rules (rules (x ⋆ y ⋆ z) ⋆ (x ⋆ y ⋆ x)) = x ⋆ y := by
  generalize h: rules (x ⋆ y ⋆ z) = e
  simp only [rules.elim] at h
  separate
  · apply rules.eq2
  · apply rules.eq4
  · apply rules.eq4
  · apply rules.eq2
  · apply rules.eq4

theorem comp4_3 {x y z : FreeMagma α}:
    rules (rules (x ⋆ y ⋆ z) ⋆ rules (x ⋆ y ⋆ x)) = x ⋆ y := by
  generalize h: rules (x ⋆ y ⋆ x) = e
  simp only [rules.elim] at h
  separate
  apply comp4_2

theorem comp1_4 {x y z : FreeMagma α}:
    rules (rules (x ⋆ y) ⋆ rules (x ⋆ rules (x ⋆ z))) = x := by
  generalize h: rules (x ⋆ z) = e
  simp only [rules.elim] at h
  separate
  · apply comp4_3
  · apply comp1_3
  · apply comp1_3
  · apply comp4_3
  · apply comp1_3

@[equational_result]
theorem «Facts» :
  ∃ (G : Type) (_ : Magma G), Facts G [1443] [23, 1629, 1630, 2441, 3050, 3055, 3522, 4065, 4067, 4118, 4268, 4282] := by
  use ConfMagma (@rules Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
    simp (disch := bufixed) only [Magma.op, bu, hx, hy, hz, buFixed_rw_op]
    symm
    congr! 1
    apply comp1_4
  all_goals refute

end rw1443

namespace rw1633

rule_system rules {x y z: FreeMagma α}
| ((x ⋆ x) ⋆ ((x ⋆ y) ⋆ z)) => x
| ((x ⋆ x) ⋆ x) => x
| (((x ⋆ x) ⋆ (x ⋆ x)) ⋆ (x ⋆ y)) => (x ⋆ x)
| ((((x ⋆ x) ⋆ (x ⋆ x)) ⋆ ((x ⋆ x) ⋆ (x ⋆ x))) ⋆ x) => ((x ⋆ x) ⋆ (x ⋆ x))

theorem comp1_2 {x y z : FreeMagma α}:
    rules (x ⋆ x ⋆ rules (x ⋆ y ⋆ z)) = x := by
  generalize h: rules (x ⋆ y ⋆ z) = e
  simp only [rules.elim] at h
  separate
  · apply rules.eq2
  · apply rules.eq2
  · apply rules.eq2
  · apply rules.eq2
  · apply rules.eq1

theorem comp3_2 {x y : FreeMagma α}:
    rules (x ⋆ x ⋆ (x ⋆ x) ⋆ rules (x ⋆ y)) = x ⋆ x := by
  generalize h: rules (x ⋆ y) = e
  simp only [rules.elim] at h
  separate
  · apply rules.eq4
  · apply rules.eq4
  · apply rules.eq4
  · apply rules.eq4
  · apply rules.eq3

theorem comp1_3 {x y z : FreeMagma α}:
    rules (x ⋆ x ⋆ rules (rules (x ⋆ y) ⋆ z)) = x := by
  generalize h: rules (x ⋆ y) = e
  simp only [rules.elim] at h
  separate
  · apply comp3_2
  · apply comp3_2
  · apply comp3_2
  · apply comp3_2
  · apply comp1_2

theorem comp1_4 {x y z : FreeMagma α}:
    rules (rules (x ⋆ x) ⋆ rules (rules (x ⋆ y) ⋆ z)) = x := by
  generalize h: rules (x ⋆ x) = e
  simp only [rules.elim] at h
  separate
  apply comp1_3

@[equational_result]
theorem «Facts» :
  ∃ (G : Type) (_ : Magma G), Facts G [1633] [4268, 4282] := by
  use ConfMagma (@rules Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
    simp (disch := bufixed) only [Magma.op, bu, hx, hy, hz, buFixed_rw_op]
    symm
    congr! 1
    apply comp1_4
  all_goals refute

end rw1633

namespace rw2126

rule_system rules {x y z w: FreeMagma α}
| y ⋆ y ⋆ x ⋆ (x ⋆ z) => x
| x ⋆ x ⋆ (x ⋆ x ⋆ y ⋆ z) => x ⋆ x ⋆ y
| x ⋆ x ⋆ (y ⋆ y ⋆ z) ⋆ z => y ⋆ y ⋆ z
| (x ⋆ x ⋆ y) ⋆ (x ⋆ x ⋆ y ⋆ z ⋆ w) => x ⋆ x ⋆ y ⋆ z

theorem comp1_2 {x y z : FreeMagma α}:
    rules (y ⋆ y ⋆ x ⋆ rules (x ⋆ z)) = x := by
  generalize h: rules (x ⋆ z) = e
  simp only [rules.elim] at h
  separate
  · apply rules.eq3
  · apply rules.eq1
  · apply rules.eq3
  · apply rules.eq1
  · apply rules.eq1

theorem comp2_2 {x y z : FreeMagma α} (hxxy: NF rules (x ⋆ x ⋆ y)):
    rules (x ⋆ x ⋆ rules (x ⋆ x ⋆ y ⋆ z)) = x ⋆ x ⋆ y := by
  generalize h: rules (x ⋆ x ⋆ y ⋆ z) = e
  simp only [rules.elim] at h
  separate
  · apply hxxy.top
  · apply rules.eq2
  · apply hxxy.top
  · apply rules.eq2
  · apply rules.eq2

theorem comp4_2 {x y z w : FreeMagma α} (hxxyz: NF rules (x ⋆ x ⋆ y ⋆ z)):
    rules (((x ⋆ x) ⋆ y) ⋆ rules ((((x ⋆ x) ⋆ y) ⋆ z) ⋆ w)) = (((x ⋆ x) ⋆ y) ⋆ z) := by
  generalize h: rules ((((x ⋆ x) ⋆ y) ⋆ z) ⋆ w) = e
  simp only [rules.elim] at h
  separate
  · apply hxxyz.top
  · apply rules.eq4
  · apply hxxyz.top
  · apply rules.eq2
  · apply rules.eq4

theorem comp1_3 {x y z : FreeMagma α} (hx: NF rules x):
    rules (rules (y ⋆ y ⋆ x) ⋆ rules (x ⋆ z)) = x := by
  generalize h: rules (y ⋆ y ⋆ x) = e
  simp only [rules.elim] at h
  separate
  · apply comp2_2 hx
  · apply comp4_2 hx
  · apply comp1_2
  · apply comp4_2 hx
  · apply comp1_2

theorem comp1_4 {x y z : FreeMagma α} (hx: NF rules x):
    rules (rules (rules (y ⋆ y) ⋆ x) ⋆ rules (x ⋆ z)) = x := by
  generalize h: rules (y ⋆ y) = e
  simp only [rules.elim] at h
  separate
  all_goals apply comp1_3 hx

@[equational_result]
theorem «Facts» :
  ∃ (G : Type) (_ : Magma G), Facts G [2126] [151, 152, 167, 168, 1426, 1427, 1428, 1429, 1430, 1478, 1479, 1480, 1481, 1482, 1483, 1484, 1485, 1486, 2050, 2051, 2052, 2087, 2088, 2089, 2161, 2162, 2163, 3456, 3457, 3511, 3512, 3513, 3862, 3877, 3918, 3955, 3993] := by
  use ConfMagma (@rules Nat _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
    simp only [Magma.op, bu, hx, hy, hz, buFixed_rw_op]
    symm
    congr! 1
    apply comp1_4 ((NF_iff_buFixed rules).mpr hx)
  all_goals refute

end rw2126
