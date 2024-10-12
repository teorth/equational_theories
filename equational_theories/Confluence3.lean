import equational_theories.ConfluenceSystem

open FreeMagma Confluence
variable {α: Type}

namespace rw481

variable [Inhabited α] [DecidableEq α]

rule_system rules {x y z: FreeMagma α} -IsProj
| y ⋆ (x ⋆ (y ⋆ (z ⋆ z))) => x
| (z ⋆ z) ⋆ (x ⋆ (z ⋆ z)) => x
| x ⋆ x => default ⋆ default

instance: IsProjOrNF (rules : FreeMagma α → _) where
  proj_or_nf := by
    intro x
    generalize h: rules x = e
    simp only [rules.elim] at h
    separate
    · left
      subterm
    · left
      subterm
    · right
      simp only [NF, Everywhere, and_self_left]
      constructor
      · simp [rules, rules.rule1, rules.rule2, rules.rule3]
      · apply rules.eq3
    · left
      rfl

theorem comp1_2 {x y : FreeMagma α} (hx: NF rules x):
    rules (y ⋆ rules (x ⋆ (y ⋆ (default ⋆ default)))) = x := by
  generalize h: rules (x ⋆ (y ⋆ (default ⋆ default))) = e
  simp only [rules.elim] at h
  separate
  · apply rules.eq3
  · apply hx.top
  · apply rules.eq1

theorem comp2_2 {x : FreeMagma α} (hx: NF rules x):
    rules (default ⋆ default ⋆ rules (x ⋆ (default ⋆ default))) = x := by
  generalize h: rules (x ⋆ (default ⋆ default)) = e
  simp only [rules.elim] at h
  separate
  · apply rules.eq3
  · apply rules.eq2

theorem comp1_3 {x y : FreeMagma α} (hx: NF rules x):
    rules (y ⋆ rules (x ⋆ rules (y ⋆ (default ⋆ default)))) = x := by
  generalize h: rules (y ⋆ (default ⋆ default)) = e
  simp only [rules.elim] at h
  separate
  · apply comp2_2 hx
  · apply comp1_2 hx

theorem comp1_4 {x y z : FreeMagma α} (hx: NF rules x):
    rules (y ⋆ rules (x ⋆ rules (y ⋆ rules (z ⋆ z)))) = x := by
  generalize h: rules (z ⋆ z) = e
  simp only [rules.elim] at h
  separate
  · apply comp1_3 hx
  · exfalso
    simp_all only [Fork.injEq, not_exists, not_and, exists_eq', not_true_eq_false]

@[equational_result]
theorem «Facts» :
  ∃ (G : Type) (_ : Magma G), Facts G [481] [1488, 1492, 1496, 2035, 2038, 2041, 2124, 2128, 2132, 2135, 3050, 3056, 3139, 3150, 3161] := by
  use ConfMagma (@rules Nat _ _), inferInstance
  repeat' apply And.intro
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
    simp (disch := bufixed) only [Magma.op, bu, hx, hy, hz, buFixed_rw_op]
    symm
    congr! 1
    apply comp1_4 ((NF_iff_buFixed rules).mpr hx)
  all_goals refute

end rw481
