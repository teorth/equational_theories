import Mathlib.Tactic
import equational_theories.Magma
import equational_theories.AllEquations
import Mathlib.Data.Fin.Basic

set_option linter.unusedTactic false


theorem Equation1_not_implies_Equation2 : ∃ (G: Type) (_: Magma G), Equation1 G ∧ ¬ Equation2 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation1_not_implies_Equation3 : ∃ (G: Type) (_: Magma G), Equation1 G ∧ ¬ Equation3 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1
    simp [hG] at h

theorem Equation1_not_implies_Equation4 : ∃ (G: Type) (_: Magma G), Equation1 G ∧ ¬ Equation4 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation1_not_implies_Equation5 : ∃ (G: Type) (_: Magma G), Equation1 G ∧ ¬ Equation5 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation1_not_implies_Equation6 : ∃ (G: Type) (_: Magma G), Equation1 G ∧ ¬ Equation6 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation1_not_implies_Equation7 : ∃ (G: Type) (_: Magma G), Equation1 G ∧ ¬ Equation7 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 0
    simp [hG] at h

theorem Equation1_not_implies_Equation8 : ∃ (G: Type) (_: Magma G), Equation1 G ∧ ¬ Equation8 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1
    simp [hG] at h

theorem Equation1_not_implies_Equation38 : ∃ (G: Type) (_: Magma G), Equation1 G ∧ ¬ Equation38 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation1_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation1 G ∧ ¬ Equation39 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation1_not_implies_Equation40 : ∃ (G: Type) (_: Magma G), Equation1 G ∧ ¬ Equation40 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation1_not_implies_Equation41 : ∃ (G: Type) (_: Magma G), Equation1 G ∧ ¬ Equation41 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1 1
    simp [hG] at h

theorem Equation1_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation1 G ∧ ¬ Equation42 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 1
    simp [hG] at h

theorem Equation1_not_implies_Equation43 : ∃ (G: Type) (_: Magma G), Equation1 G ∧ ¬ Equation43 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 || x=1 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation1_not_implies_Equation46 : ∃ (G: Type) (_: Magma G), Equation1 G ∧ ¬ Equation46 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 1 1
    simp [hG] at h

theorem Equation1_not_implies_Equation168 : ∃ (G: Type) (_: Magma G), Equation1 G ∧ ¬ Equation168 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 0
    simp [hG] at h

theorem Equation1_not_implies_Equation387 : ∃ (G: Type) (_: Magma G), Equation1 G ∧ ¬ Equation387 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 || x=1 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation1_not_implies_Equation4512 : ∃ (G: Type) (_: Magma G), Equation1 G ∧ ¬ Equation4512 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 || x=1 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 1
    simp [hG] at h

theorem Equation1_not_implies_Equation4513 : ∃ (G: Type) (_: Magma G), Equation1 G ∧ ¬ Equation4513 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 1 0 1
    simp [hG] at h

theorem Equation1_not_implies_Equation4552 : ∃ (G: Type) (_: Magma G), Equation1 G ∧ ¬ Equation4552 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 1 1
    simp [hG] at h

theorem Equation1_not_implies_Equation4582 : ∃ (G: Type) (_: Magma G), Equation1 G ∧ ¬ Equation4582 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0 1 1 1
    simp [hG] at h

theorem Equation3_not_implies_Equation2 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation2 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation3_not_implies_Equation4 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation4 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation3_not_implies_Equation5 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation5 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation3_not_implies_Equation6 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation6 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation3_not_implies_Equation7 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation7 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1 1
    simp [hG] at h

theorem Equation3_not_implies_Equation38 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation38 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation3_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation39 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation3_not_implies_Equation40 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation40 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation3_not_implies_Equation41 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation41 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1 1
    simp [hG] at h

theorem Equation3_not_implies_Equation43 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation43 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation3_not_implies_Equation46 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation46 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 1 1
    simp [hG] at h

theorem Equation3_not_implies_Equation168 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation168 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 0
    simp [hG] at h

theorem Equation3_not_implies_Equation387 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation387 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation3_not_implies_Equation4513 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation4513 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 1 0 1
    simp [hG] at h

theorem Equation3_not_implies_Equation4552 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation4552 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 1 1
    simp [hG] at h

theorem Equation3_not_implies_Equation4582 : ∃ (G: Type) (_: Magma G), Equation3 G ∧ ¬ Equation4582 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0 1 1 1
    simp [hG] at h

theorem Equation387_not_implies_Equation2 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation2 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation387_not_implies_Equation3 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation3 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1
    simp [hG] at h

theorem Equation387_not_implies_Equation4 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation4 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation387_not_implies_Equation5 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation5 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation387_not_implies_Equation6 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation6 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation387_not_implies_Equation7 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation7 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 0
    simp [hG] at h

theorem Equation387_not_implies_Equation8 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation8 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1
    simp [hG] at h

theorem Equation387_not_implies_Equation38 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation38 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation387_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation39 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation387_not_implies_Equation41 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation41 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1 1
    simp [hG] at h

theorem Equation387_not_implies_Equation46 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation46 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 1 1
    simp [hG] at h

theorem Equation387_not_implies_Equation168 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation168 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 0
    simp [hG] at h

theorem Equation387_not_implies_Equation4513 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation4513 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 1 0 1
    simp [hG] at h

theorem Equation387_not_implies_Equation4552 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation4552 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 1 1
    simp [hG] at h

theorem Equation387_not_implies_Equation4582 : ∃ (G: Type) (_: Magma G), Equation387 G ∧ ¬ Equation4582 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0 1 1 1
    simp [hG] at h

theorem Equation4_not_implies_Equation2 : ∃ (G: Type) (_: Magma G), Equation4 G ∧ ¬ Equation2 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation4_not_implies_Equation5 : ∃ (G: Type) (_: Magma G), Equation4 G ∧ ¬ Equation5 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation4_not_implies_Equation6 : ∃ (G: Type) (_: Magma G), Equation4 G ∧ ¬ Equation6 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation4_not_implies_Equation7 : ∃ (G: Type) (_: Magma G), Equation4 G ∧ ¬ Equation7 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1 0
    simp [hG] at h

theorem Equation4_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation4 G ∧ ¬ Equation39 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation4_not_implies_Equation41 : ∃ (G: Type) (_: Magma G), Equation4 G ∧ ¬ Equation41 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1 0
    simp [hG] at h

theorem Equation4_not_implies_Equation46 : ∃ (G: Type) (_: Magma G), Equation4 G ∧ ¬ Equation46 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 1 0
    simp [hG] at h

theorem Equation4_not_implies_Equation168 : ∃ (G: Type) (_: Magma G), Equation4 G ∧ ¬ Equation168 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1 0
    simp [hG] at h

theorem Equation4_not_implies_Equation387 : ∃ (G: Type) (_: Magma G), Equation4 G ∧ ¬ Equation387 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation5_not_implies_Equation2 : ∃ (G: Type) (_: Magma G), Equation5 G ∧ ¬ Equation2 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation5_not_implies_Equation4 : ∃ (G: Type) (_: Magma G), Equation5 G ∧ ¬ Equation4 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation5_not_implies_Equation6 : ∃ (G: Type) (_: Magma G), Equation5 G ∧ ¬ Equation6 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation5_not_implies_Equation7 : ∃ (G: Type) (_: Magma G), Equation5 G ∧ ¬ Equation7 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 1
    simp [hG] at h

theorem Equation5_not_implies_Equation38 : ∃ (G: Type) (_: Magma G), Equation5 G ∧ ¬ Equation38 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation5_not_implies_Equation40 : ∃ (G: Type) (_: Magma G), Equation5 G ∧ ¬ Equation40 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation5_not_implies_Equation41 : ∃ (G: Type) (_: Magma G), Equation5 G ∧ ¬ Equation41 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 1
    simp [hG] at h

theorem Equation5_not_implies_Equation46 : ∃ (G: Type) (_: Magma G), Equation5 G ∧ ¬ Equation46 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0 1
    simp [hG] at h

theorem Equation5_not_implies_Equation168 : ∃ (G: Type) (_: Magma G), Equation5 G ∧ ¬ Equation168 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 1
    simp [hG] at h

theorem Equation5_not_implies_Equation387 : ∃ (G: Type) (_: Magma G), Equation5 G ∧ ¬ Equation387 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation5_not_implies_Equation4552 : ∃ (G: Type) (_: Magma G), Equation5 G ∧ ¬ Equation4552 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 1 0
    simp [hG] at h

theorem Equation5_not_implies_Equation4582 : ∃ (G: Type) (_: Magma G), Equation5 G ∧ ¬ Equation4582 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0 0 0 1
    simp [hG] at h

theorem Equation8_not_implies_Equation2 : ∃ (G: Type) (_: Magma G), Equation8 G ∧ ¬ Equation2 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation8_not_implies_Equation4 : ∃ (G: Type) (_: Magma G), Equation8 G ∧ ¬ Equation4 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation8_not_implies_Equation5 : ∃ (G: Type) (_: Magma G), Equation8 G ∧ ¬ Equation5 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation8_not_implies_Equation6 : ∃ (G: Type) (_: Magma G), Equation8 G ∧ ¬ Equation6 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation8_not_implies_Equation7 : ∃ (G: Type) (_: Magma G), Equation8 G ∧ ¬ Equation7 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1 1
    simp [hG] at h

theorem Equation8_not_implies_Equation38 : ∃ (G: Type) (_: Magma G), Equation8 G ∧ ¬ Equation38 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation8_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation8 G ∧ ¬ Equation39 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation8_not_implies_Equation40 : ∃ (G: Type) (_: Magma G), Equation8 G ∧ ¬ Equation40 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation8_not_implies_Equation41 : ∃ (G: Type) (_: Magma G), Equation8 G ∧ ¬ Equation41 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1 1
    simp [hG] at h

theorem Equation8_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation8 G ∧ ¬ Equation42 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 1
    simp [hG] at h

theorem Equation8_not_implies_Equation43 : ∃ (G: Type) (_: Magma G), Equation8 G ∧ ¬ Equation43 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation8_not_implies_Equation46 : ∃ (G: Type) (_: Magma G), Equation8 G ∧ ¬ Equation46 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 1 1
    simp [hG] at h

theorem Equation8_not_implies_Equation168 : ∃ (G: Type) (_: Magma G), Equation8 G ∧ ¬ Equation168 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 0
    simp [hG] at h

theorem Equation8_not_implies_Equation387 : ∃ (G: Type) (_: Magma G), Equation8 G ∧ ¬ Equation387 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation8_not_implies_Equation4512 : ∃ (G: Type) (_: Magma G), Equation8 G ∧ ¬ Equation4512 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 1
    simp [hG] at h

theorem Equation8_not_implies_Equation4513 : ∃ (G: Type) (_: Magma G), Equation8 G ∧ ¬ Equation4513 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 1 0 1
    simp [hG] at h

theorem Equation8_not_implies_Equation4552 : ∃ (G: Type) (_: Magma G), Equation8 G ∧ ¬ Equation4552 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 1 1
    simp [hG] at h

theorem Equation8_not_implies_Equation4582 : ∃ (G: Type) (_: Magma G), Equation8 G ∧ ¬ Equation4582 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x
    fin_cases x <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0 1 1 1
    simp [hG] at h

theorem Equation4512_not_implies_Equation2 : ∃ (G: Type) (_: Magma G), Equation4512 G ∧ ¬ Equation2 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation4512_not_implies_Equation3 : ∃ (G: Type) (_: Magma G), Equation4512 G ∧ ¬ Equation3 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1
    simp [hG] at h

theorem Equation4512_not_implies_Equation4 : ∃ (G: Type) (_: Magma G), Equation4512 G ∧ ¬ Equation4 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation4512_not_implies_Equation5 : ∃ (G: Type) (_: Magma G), Equation4512 G ∧ ¬ Equation5 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation4512_not_implies_Equation6 : ∃ (G: Type) (_: Magma G), Equation4512 G ∧ ¬ Equation6 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation4512_not_implies_Equation7 : ∃ (G: Type) (_: Magma G), Equation4512 G ∧ ¬ Equation7 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 0
    simp [hG] at h

theorem Equation4512_not_implies_Equation8 : ∃ (G: Type) (_: Magma G), Equation4512 G ∧ ¬ Equation8 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1
    simp [hG] at h

theorem Equation4512_not_implies_Equation38 : ∃ (G: Type) (_: Magma G), Equation4512 G ∧ ¬ Equation38 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation4512_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation4512 G ∧ ¬ Equation39 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation4512_not_implies_Equation40 : ∃ (G: Type) (_: Magma G), Equation4512 G ∧ ¬ Equation40 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation4512_not_implies_Equation41 : ∃ (G: Type) (_: Magma G), Equation4512 G ∧ ¬ Equation41 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1 1
    simp [hG] at h

theorem Equation4512_not_implies_Equation43 : ∃ (G: Type) (_: Magma G), Equation4512 G ∧ ¬ Equation43 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation4512_not_implies_Equation46 : ∃ (G: Type) (_: Magma G), Equation4512 G ∧ ¬ Equation46 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 1 1
    simp [hG] at h

theorem Equation4512_not_implies_Equation168 : ∃ (G: Type) (_: Magma G), Equation4512 G ∧ ¬ Equation168 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 0
    simp [hG] at h

theorem Equation4512_not_implies_Equation387 : ∃ (G: Type) (_: Magma G), Equation4512 G ∧ ¬ Equation387 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation4512_not_implies_Equation4552 : ∃ (G: Type) (_: Magma G), Equation4512 G ∧ ¬ Equation4552 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 1 1
    simp [hG] at h

theorem Equation4512_not_implies_Equation4582 : ∃ (G: Type) (_: Magma G), Equation4512 G ∧ ¬ Equation4582 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0 1 1 1
    simp [hG] at h

theorem Equation4513_not_implies_Equation2 : ∃ (G: Type) (_: Magma G), Equation4513 G ∧ ¬ Equation2 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation4513_not_implies_Equation3 : ∃ (G: Type) (_: Magma G), Equation4513 G ∧ ¬ Equation3 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1
    simp [hG] at h

theorem Equation4513_not_implies_Equation4 : ∃ (G: Type) (_: Magma G), Equation4513 G ∧ ¬ Equation4 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation4513_not_implies_Equation5 : ∃ (G: Type) (_: Magma G), Equation4513 G ∧ ¬ Equation5 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation4513_not_implies_Equation6 : ∃ (G: Type) (_: Magma G), Equation4513 G ∧ ¬ Equation6 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation4513_not_implies_Equation7 : ∃ (G: Type) (_: Magma G), Equation4513 G ∧ ¬ Equation7 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 0
    simp [hG] at h

theorem Equation4513_not_implies_Equation8 : ∃ (G: Type) (_: Magma G), Equation4513 G ∧ ¬ Equation8 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1
    simp [hG] at h

theorem Equation4513_not_implies_Equation38 : ∃ (G: Type) (_: Magma G), Equation4513 G ∧ ¬ Equation38 G := by
  let G := Fin 3
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 0
        | 0, 2 => 0
        | 1, 0 => 0
        | 1, 1 => 0
        | 1, 2 => 0
        | 2, 0 => 0
        | 2, 1 => 0
        | 2, 2 => 1
  }
  refine ⟨G, hG, ?eq4513, ?neq38⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 2 0
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation4513_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation4513 G ∧ ¬ Equation39 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation4513_not_implies_Equation40 : ∃ (G: Type) (_: Magma G), Equation4513 G ∧ ¬ Equation40 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation4513_not_implies_Equation41 : ∃ (G: Type) (_: Magma G), Equation4513 G ∧ ¬ Equation41 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1 0
    simp [hG] at h

theorem Equation4513_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation4513 G ∧ ¬ Equation42 G := by
  let G := Fin 3
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 0
        | 0, 2 => 0
        | 1, 0 => 0
        | 1, 1 => 0
        | 1, 2 => 0
        | 2, 0 => 0
        | 2, 1 => 0
        | 2, 2 => 1
  }
  refine ⟨G, hG, ?eq4513, ?neq42⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 2 0 2
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation4513_not_implies_Equation43 : ∃ (G: Type) (_: Magma G), Equation4513 G ∧ ¬ Equation43 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation4513_not_implies_Equation46 : ∃ (G: Type) (_: Magma G), Equation4513 G ∧ ¬ Equation46 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 1 0
    simp [hG] at h

theorem Equation4513_not_implies_Equation168 : ∃ (G: Type) (_: Magma G), Equation4513 G ∧ ¬ Equation168 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 0
    simp [hG] at h

theorem Equation4513_not_implies_Equation387 : ∃ (G: Type) (_: Magma G), Equation4513 G ∧ ¬ Equation387 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation4513_not_implies_Equation4582 : ∃ (G: Type) (_: Magma G), Equation4513 G ∧ ¬ Equation4582 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0 1 0 0
    simp [hG] at h

theorem Equation38_not_implies_Equation2 : ∃ (G: Type) (_: Magma G), Equation38 G ∧ ¬ Equation2 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation38_not_implies_Equation3 : ∃ (G: Type) (_: Magma G), Equation38 G ∧ ¬ Equation3 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1
    simp [hG] at h

theorem Equation38_not_implies_Equation4 : ∃ (G: Type) (_: Magma G), Equation38 G ∧ ¬ Equation4 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation38_not_implies_Equation5 : ∃ (G: Type) (_: Magma G), Equation38 G ∧ ¬ Equation5 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation38_not_implies_Equation6 : ∃ (G: Type) (_: Magma G), Equation38 G ∧ ¬ Equation6 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation38_not_implies_Equation7 : ∃ (G: Type) (_: Magma G), Equation38 G ∧ ¬ Equation7 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 0
    simp [hG] at h

theorem Equation38_not_implies_Equation8 : ∃ (G: Type) (_: Magma G), Equation38 G ∧ ¬ Equation8 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1
    simp [hG] at h

theorem Equation38_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation38 G ∧ ¬ Equation39 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation38_not_implies_Equation40 : ∃ (G: Type) (_: Magma G), Equation38 G ∧ ¬ Equation40 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation38_not_implies_Equation41 : ∃ (G: Type) (_: Magma G), Equation38 G ∧ ¬ Equation41 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1 0
    simp [hG] at h

theorem Equation38_not_implies_Equation43 : ∃ (G: Type) (_: Magma G), Equation38 G ∧ ¬ Equation43 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation38_not_implies_Equation46 : ∃ (G: Type) (_: Magma G), Equation38 G ∧ ¬ Equation46 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 1 0
    simp [hG] at h

theorem Equation38_not_implies_Equation168 : ∃ (G: Type) (_: Magma G), Equation38 G ∧ ¬ Equation168 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 0
    simp [hG] at h

theorem Equation38_not_implies_Equation387 : ∃ (G: Type) (_: Magma G), Equation38 G ∧ ¬ Equation387 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation38_not_implies_Equation4512 : ∃ (G: Type) (_: Magma G), Equation38 G ∧ ¬ Equation4512 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=1 && y=0 || x=1 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0
    simp [hG] at h

theorem Equation38_not_implies_Equation4513 : ∃ (G: Type) (_: Magma G), Equation38 G ∧ ¬ Equation4513 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=1 && y=0 || x=1 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0 0
    simp [hG] at h

theorem Equation38_not_implies_Equation4552 : ∃ (G: Type) (_: Magma G), Equation38 G ∧ ¬ Equation4552 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 1 0
    simp [hG] at h

theorem Equation38_not_implies_Equation4582 : ∃ (G: Type) (_: Magma G), Equation38 G ∧ ¬ Equation4582 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0 1 0 0
    simp [hG] at h

theorem Equation39_not_implies_Equation2 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation2 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation39_not_implies_Equation3 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation3 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1
    simp [hG] at h

theorem Equation39_not_implies_Equation4 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation4 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation39_not_implies_Equation5 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation5 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation39_not_implies_Equation6 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation6 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation39_not_implies_Equation7 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation7 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 0
    simp [hG] at h

theorem Equation39_not_implies_Equation38 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation38 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation39_not_implies_Equation40 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation40 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation39_not_implies_Equation41 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation41 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 1
    simp [hG] at h

theorem Equation39_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation42 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 1
    simp [hG] at h

theorem Equation39_not_implies_Equation43 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation43 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation39_not_implies_Equation46 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation46 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0 1
    simp [hG] at h

theorem Equation39_not_implies_Equation168 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation168 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 0
    simp [hG] at h

theorem Equation39_not_implies_Equation387 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation387 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation39_not_implies_Equation4512 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation4512 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=1 || x=1 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0
    simp [hG] at h

theorem Equation39_not_implies_Equation4513 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation4513 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0 1
    simp [hG] at h

theorem Equation39_not_implies_Equation4552 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation4552 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 1 0
    simp [hG] at h

theorem Equation39_not_implies_Equation4582 : ∃ (G: Type) (_: Magma G), Equation39 G ∧ ¬ Equation4582 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0 0 0 1
    simp [hG] at h

theorem Equation40_not_implies_Equation2 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation2 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation40_not_implies_Equation4 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation4 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation40_not_implies_Equation5 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation5 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation40_not_implies_Equation6 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation6 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation40_not_implies_Equation7 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation7 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 0
    simp [hG] at h

theorem Equation40_not_implies_Equation8 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation8 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1
    simp [hG] at h

theorem Equation40_not_implies_Equation38 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation38 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 || x=1 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation40_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation39 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 || x=1 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation40_not_implies_Equation41 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation41 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 || x=1 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 1
    simp [hG] at h

theorem Equation40_not_implies_Equation46 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation46 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 || x=1 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0 1
    simp [hG] at h

theorem Equation40_not_implies_Equation168 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation168 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 0
    simp [hG] at h

theorem Equation40_not_implies_Equation387 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation387 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 || x=1 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation40_not_implies_Equation4513 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation4513 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 || x=1 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0 1
    simp [hG] at h

theorem Equation40_not_implies_Equation4552 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation4552 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 || x=1 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 1 0
    simp [hG] at h

theorem Equation40_not_implies_Equation4582 : ∃ (G: Type) (_: Magma G), Equation40 G ∧ ¬ Equation4582 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=1 && y=0 || x=1 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0 0 0 1
    simp [hG] at h

theorem Equation41_not_implies_Equation2 : ∃ (G: Type) (_: Magma G), Equation41 G ∧ ¬ Equation2 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation41_not_implies_Equation3 : ∃ (G: Type) (_: Magma G), Equation41 G ∧ ¬ Equation3 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1
    simp [hG] at h

theorem Equation41_not_implies_Equation4 : ∃ (G: Type) (_: Magma G), Equation41 G ∧ ¬ Equation4 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation41_not_implies_Equation5 : ∃ (G: Type) (_: Magma G), Equation41 G ∧ ¬ Equation5 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation41_not_implies_Equation6 : ∃ (G: Type) (_: Magma G), Equation41 G ∧ ¬ Equation6 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation41_not_implies_Equation7 : ∃ (G: Type) (_: Magma G), Equation41 G ∧ ¬ Equation7 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 0
    simp [hG] at h

theorem Equation41_not_implies_Equation8 : ∃ (G: Type) (_: Magma G), Equation41 G ∧ ¬ Equation8 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1
    simp [hG] at h

theorem Equation41_not_implies_Equation168 : ∃ (G: Type) (_: Magma G), Equation41 G ∧ ¬ Equation168 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 0
    simp [hG] at h

theorem Equation42_not_implies_Equation2 : ∃ (G: Type) (_: Magma G), Equation42 G ∧ ¬ Equation2 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation42_not_implies_Equation3 : ∃ (G: Type) (_: Magma G), Equation42 G ∧ ¬ Equation3 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1
    simp [hG] at h

theorem Equation42_not_implies_Equation4 : ∃ (G: Type) (_: Magma G), Equation42 G ∧ ¬ Equation4 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation42_not_implies_Equation5 : ∃ (G: Type) (_: Magma G), Equation42 G ∧ ¬ Equation5 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation42_not_implies_Equation6 : ∃ (G: Type) (_: Magma G), Equation42 G ∧ ¬ Equation6 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation42_not_implies_Equation7 : ∃ (G: Type) (_: Magma G), Equation42 G ∧ ¬ Equation7 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 0
    simp [hG] at h

theorem Equation42_not_implies_Equation8 : ∃ (G: Type) (_: Magma G), Equation42 G ∧ ¬ Equation8 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1
    simp [hG] at h

theorem Equation42_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation42 G ∧ ¬ Equation39 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation42_not_implies_Equation40 : ∃ (G: Type) (_: Magma G), Equation42 G ∧ ¬ Equation40 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation42_not_implies_Equation41 : ∃ (G: Type) (_: Magma G), Equation42 G ∧ ¬ Equation41 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1 0
    simp [hG] at h

theorem Equation42_not_implies_Equation46 : ∃ (G: Type) (_: Magma G), Equation42 G ∧ ¬ Equation46 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 1 0
    simp [hG] at h

theorem Equation42_not_implies_Equation168 : ∃ (G: Type) (_: Magma G), Equation42 G ∧ ¬ Equation168 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 0
    simp [hG] at h

theorem Equation42_not_implies_Equation387 : ∃ (G: Type) (_: Magma G), Equation42 G ∧ ¬ Equation387 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation42_not_implies_Equation4513 : ∃ (G: Type) (_: Magma G), Equation42 G ∧ ¬ Equation4513 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=1 && y=0 || x=1 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0 0
    simp [hG] at h

theorem Equation42_not_implies_Equation4552 : ∃ (G: Type) (_: Magma G), Equation42 G ∧ ¬ Equation4552 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 1 0
    simp [hG] at h

theorem Equation42_not_implies_Equation4582 : ∃ (G: Type) (_: Magma G), Equation42 G ∧ ¬ Equation4582 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0 1 0 0
    simp [hG] at h

theorem Equation43_not_implies_Equation2 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation2 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation43_not_implies_Equation4 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation4 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation43_not_implies_Equation5 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation5 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation43_not_implies_Equation6 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation6 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation43_not_implies_Equation7 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation7 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 0
    simp [hG] at h

theorem Equation43_not_implies_Equation8 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation8 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1
    simp [hG] at h

theorem Equation43_not_implies_Equation38 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation38 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation43_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation39 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation43_not_implies_Equation40 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation40 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation43_not_implies_Equation41 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation41 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1 1
    simp [hG] at h

theorem Equation43_not_implies_Equation46 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation46 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 1 1
    simp [hG] at h

theorem Equation43_not_implies_Equation168 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation168 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 0
    simp [hG] at h

theorem Equation43_not_implies_Equation4513 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation4513 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 1 0 1
    simp [hG] at h

theorem Equation43_not_implies_Equation4552 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation4552 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 1 1
    simp [hG] at h

theorem Equation43_not_implies_Equation4582 : ∃ (G: Type) (_: Magma G), Equation43 G ∧ ¬ Equation4582 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ if x=0 && y=0 || x=0 && y=1 || x=1 && y=0 then 0 else 1 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y
    fin_cases x <;>
    fin_cases y <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0 1 1 1
    simp [hG] at h

theorem Equation168_not_implies_Equation2 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation2 G := by
  let G := Fin 4
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 2
        | 0, 2 => 0
        | 0, 3 => 2
        | 1, 0 => 0
        | 1, 1 => 2
        | 1, 2 => 0
        | 1, 3 => 2
        | 2, 0 => 1
        | 2, 1 => 3
        | 2, 2 => 1
        | 2, 3 => 3
        | 3, 0 => 1
        | 3, 1 => 3
        | 3, 2 => 1
        | 3, 3 => 3
  }
  refine ⟨G, hG, ?eq168, ?neq2⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation168_not_implies_Equation3 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation3 G := by
  let G := Fin 4
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 2
        | 0, 2 => 0
        | 0, 3 => 2
        | 1, 0 => 0
        | 1, 1 => 2
        | 1, 2 => 0
        | 1, 3 => 2
        | 2, 0 => 1
        | 2, 1 => 3
        | 2, 2 => 1
        | 2, 3 => 3
        | 3, 0 => 1
        | 3, 1 => 3
        | 3, 2 => 1
        | 3, 3 => 3
  }
  refine ⟨G, hG, ?eq168, ?neq3⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation168_not_implies_Equation4 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation4 G := by
  let G := Fin 4
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 2
        | 0, 2 => 0
        | 0, 3 => 2
        | 1, 0 => 0
        | 1, 1 => 2
        | 1, 2 => 0
        | 1, 3 => 2
        | 2, 0 => 1
        | 2, 1 => 3
        | 2, 2 => 1
        | 2, 3 => 3
        | 3, 0 => 1
        | 3, 1 => 3
        | 3, 2 => 1
        | 3, 3 => 3
  }
  refine ⟨G, hG, ?eq168, ?neq4⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation168_not_implies_Equation5 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation5 G := by
  let G := Fin 4
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 2
        | 0, 2 => 0
        | 0, 3 => 2
        | 1, 0 => 0
        | 1, 1 => 2
        | 1, 2 => 0
        | 1, 3 => 2
        | 2, 0 => 1
        | 2, 1 => 3
        | 2, 2 => 1
        | 2, 3 => 3
        | 3, 0 => 1
        | 3, 1 => 3
        | 3, 2 => 1
        | 3, 3 => 3
  }
  refine ⟨G, hG, ?eq168, ?neq5⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 2
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation168_not_implies_Equation6 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation6 G := by
  let G := Fin 4
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 2
        | 0, 2 => 0
        | 0, 3 => 2
        | 1, 0 => 0
        | 1, 1 => 2
        | 1, 2 => 0
        | 1, 3 => 2
        | 2, 0 => 1
        | 2, 1 => 3
        | 2, 2 => 1
        | 2, 3 => 3
        | 3, 0 => 1
        | 3, 1 => 3
        | 3, 2 => 1
        | 3, 3 => 3
  }
  refine ⟨G, hG, ?eq168, ?neq6⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation168_not_implies_Equation7 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation7 G := by
  let G := Fin 4
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 2
        | 0, 2 => 0
        | 0, 3 => 2
        | 1, 0 => 0
        | 1, 1 => 2
        | 1, 2 => 0
        | 1, 3 => 2
        | 2, 0 => 1
        | 2, 1 => 3
        | 2, 2 => 1
        | 2, 3 => 3
        | 3, 0 => 1
        | 3, 1 => 3
        | 3, 2 => 1
        | 3, 3 => 3
  }
  refine ⟨G, hG, ?eq168, ?neq7⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 1
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation168_not_implies_Equation38 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation38 G := by
  let G := Fin 4
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 2
        | 0, 2 => 0
        | 0, 3 => 2
        | 1, 0 => 0
        | 1, 1 => 2
        | 1, 2 => 0
        | 1, 3 => 2
        | 2, 0 => 1
        | 2, 1 => 3
        | 2, 2 => 1
        | 2, 3 => 3
        | 3, 0 => 1
        | 3, 1 => 3
        | 3, 2 => 1
        | 3, 3 => 3
  }
  refine ⟨G, hG, ?eq168, ?neq38⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation168_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation39 G := by
  let G := Fin 4
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 2
        | 0, 2 => 0
        | 0, 3 => 2
        | 1, 0 => 0
        | 1, 1 => 2
        | 1, 2 => 0
        | 1, 3 => 2
        | 2, 0 => 1
        | 2, 1 => 3
        | 2, 2 => 1
        | 2, 3 => 3
        | 3, 0 => 1
        | 3, 1 => 3
        | 3, 2 => 1
        | 3, 3 => 3
  }
  refine ⟨G, hG, ?eq168, ?neq39⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 2
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation168_not_implies_Equation40 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation40 G := by
  let G := Fin 4
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 2
        | 0, 2 => 0
        | 0, 3 => 2
        | 1, 0 => 0
        | 1, 1 => 2
        | 1, 2 => 0
        | 1, 3 => 2
        | 2, 0 => 1
        | 2, 1 => 3
        | 2, 2 => 1
        | 2, 3 => 3
        | 3, 0 => 1
        | 3, 1 => 3
        | 3, 2 => 1
        | 3, 3 => 3
  }
  refine ⟨G, hG, ?eq168, ?neq40⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation168_not_implies_Equation41 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation41 G := by
  let G := Fin 4
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 2
        | 0, 2 => 0
        | 0, 3 => 2
        | 1, 0 => 0
        | 1, 1 => 2
        | 1, 2 => 0
        | 1, 3 => 2
        | 2, 0 => 1
        | 2, 1 => 3
        | 2, 2 => 1
        | 2, 3 => 3
        | 3, 0 => 1
        | 3, 1 => 3
        | 3, 2 => 1
        | 3, 3 => 3
  }
  refine ⟨G, hG, ?eq168, ?neq41⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 1
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation168_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation42 G := by
  let G := Fin 4
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 2
        | 0, 2 => 0
        | 0, 3 => 2
        | 1, 0 => 0
        | 1, 1 => 2
        | 1, 2 => 0
        | 1, 3 => 2
        | 2, 0 => 1
        | 2, 1 => 3
        | 2, 2 => 1
        | 2, 3 => 3
        | 3, 0 => 1
        | 3, 1 => 3
        | 3, 2 => 1
        | 3, 3 => 3
  }
  refine ⟨G, hG, ?eq168, ?neq42⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 1
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation168_not_implies_Equation43 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation43 G := by
  let G := Fin 4
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 2
        | 0, 2 => 0
        | 0, 3 => 2
        | 1, 0 => 0
        | 1, 1 => 2
        | 1, 2 => 0
        | 1, 3 => 2
        | 2, 0 => 1
        | 2, 1 => 3
        | 2, 2 => 1
        | 2, 3 => 3
        | 3, 0 => 1
        | 3, 1 => 3
        | 3, 2 => 1
        | 3, 3 => 3
  }
  refine ⟨G, hG, ?eq168, ?neq43⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation168_not_implies_Equation46 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation46 G := by
  let G := Fin 4
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 2
        | 0, 2 => 0
        | 0, 3 => 2
        | 1, 0 => 0
        | 1, 1 => 2
        | 1, 2 => 0
        | 1, 3 => 2
        | 2, 0 => 1
        | 2, 1 => 3
        | 2, 2 => 1
        | 2, 3 => 3
        | 3, 0 => 1
        | 3, 1 => 3
        | 3, 2 => 1
        | 3, 3 => 3
  }
  refine ⟨G, hG, ?eq168, ?neq46⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0 1
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation168_not_implies_Equation387 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation387 G := by
  let G := Fin 4
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 2
        | 0, 2 => 0
        | 0, 3 => 2
        | 1, 0 => 0
        | 1, 1 => 2
        | 1, 2 => 0
        | 1, 3 => 2
        | 2, 0 => 1
        | 2, 1 => 3
        | 2, 2 => 1
        | 2, 3 => 3
        | 3, 0 => 1
        | 3, 1 => 3
        | 3, 2 => 1
        | 3, 3 => 3
  }
  refine ⟨G, hG, ?eq168, ?neq387⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation168_not_implies_Equation4512 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation4512 G := by
  let G := Fin 4
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 2
        | 0, 2 => 0
        | 0, 3 => 2
        | 1, 0 => 0
        | 1, 1 => 2
        | 1, 2 => 0
        | 1, 3 => 2
        | 2, 0 => 1
        | 2, 1 => 3
        | 2, 2 => 1
        | 2, 3 => 3
        | 3, 0 => 1
        | 3, 1 => 3
        | 3, 2 => 1
        | 3, 3 => 3
  }
  refine ⟨G, hG, ?eq168, ?neq4512⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 1
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation168_not_implies_Equation4513 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation4513 G := by
  let G := Fin 4
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 2
        | 0, 2 => 0
        | 0, 3 => 2
        | 1, 0 => 0
        | 1, 1 => 2
        | 1, 2 => 0
        | 1, 3 => 2
        | 2, 0 => 1
        | 2, 1 => 3
        | 2, 2 => 1
        | 2, 3 => 3
        | 3, 0 => 1
        | 3, 1 => 3
        | 3, 2 => 1
        | 3, 3 => 3
  }
  refine ⟨G, hG, ?eq168, ?neq4513⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0 1
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation168_not_implies_Equation4552 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation4552 G := by
  let G := Fin 4
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 2
        | 0, 2 => 0
        | 0, 3 => 2
        | 1, 0 => 0
        | 1, 1 => 2
        | 1, 2 => 0
        | 1, 3 => 2
        | 2, 0 => 1
        | 2, 1 => 3
        | 2, 2 => 1
        | 2, 3 => 3
        | 3, 0 => 1
        | 3, 1 => 3
        | 3, 2 => 1
        | 3, 3 => 3
  }
  refine ⟨G, hG, ?eq168, ?neq4552⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0 1
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation168_not_implies_Equation4582 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation4582 G := by
  let G := Fin 4
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 2
        | 0, 2 => 0
        | 0, 3 => 2
        | 1, 0 => 0
        | 1, 1 => 2
        | 1, 2 => 0
        | 1, 3 => 2
        | 2, 0 => 1
        | 2, 1 => 3
        | 2, 2 => 1
        | 2, 3 => 3
        | 3, 0 => 1
        | 3, 1 => 3
        | 3, 2 => 1
        | 3, 3 => 3
  }
  refine ⟨G, hG, ?eq168, ?neq4582⟩
  ·
    intro x y z
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0 0 0 1
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation46_not_implies_Equation2 : ∃ (G: Type) (_: Magma G), Equation46 G ∧ ¬ Equation2 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation46_not_implies_Equation5 : ∃ (G: Type) (_: Magma G), Equation46 G ∧ ¬ Equation5 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation46_not_implies_Equation6 : ∃ (G: Type) (_: Magma G), Equation46 G ∧ ¬ Equation6 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation46_not_implies_Equation7 : ∃ (G: Type) (_: Magma G), Equation46 G ∧ ¬ Equation7 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 0
    simp [hG] at h

theorem Equation46_not_implies_Equation8 : ∃ (G: Type) (_: Magma G), Equation46 G ∧ ¬ Equation8 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1
    simp [hG] at h

theorem Equation46_not_implies_Equation168 : ∃ (G: Type) (_: Magma G), Equation46 G ∧ ¬ Equation168 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 0
    simp [hG] at h

theorem Equation4552_not_implies_Equation2 : ∃ (G: Type) (_: Magma G), Equation4552 G ∧ ¬ Equation2 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation4552_not_implies_Equation3 : ∃ (G: Type) (_: Magma G), Equation4552 G ∧ ¬ Equation3 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1
    simp [hG] at h

theorem Equation4552_not_implies_Equation4 : ∃ (G: Type) (_: Magma G), Equation4552 G ∧ ¬ Equation4 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation4552_not_implies_Equation5 : ∃ (G: Type) (_: Magma G), Equation4552 G ∧ ¬ Equation5 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation4552_not_implies_Equation6 : ∃ (G: Type) (_: Magma G), Equation4552 G ∧ ¬ Equation6 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation4552_not_implies_Equation7 : ∃ (G: Type) (_: Magma G), Equation4552 G ∧ ¬ Equation7 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 0
    simp [hG] at h

theorem Equation4552_not_implies_Equation8 : ∃ (G: Type) (_: Magma G), Equation4552 G ∧ ¬ Equation8 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1
    simp [hG] at h

theorem Equation4552_not_implies_Equation38 : ∃ (G: Type) (_: Magma G), Equation4552 G ∧ ¬ Equation38 G := by
  let G := Fin 3
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 0
        | 0, 2 => 0
        | 1, 0 => 0
        | 1, 1 => 0
        | 1, 2 => 0
        | 2, 0 => 0
        | 2, 1 => 0
        | 2, 2 => 1
  }
  refine ⟨G, hG, ?eq4552, ?neq38⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 2 0
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation4552_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation4552 G ∧ ¬ Equation39 G := by
  let G := Fin 3
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 0
        | 0, 2 => 0
        | 1, 0 => 0
        | 1, 1 => 0
        | 1, 2 => 0
        | 2, 0 => 0
        | 2, 1 => 0
        | 2, 2 => 1
  }
  refine ⟨G, hG, ?eq4552, ?neq39⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 2 0
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation4552_not_implies_Equation40 : ∃ (G: Type) (_: Magma G), Equation4552 G ∧ ¬ Equation40 G := by
  let G := Fin 3
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 0
        | 0, 2 => 0
        | 1, 0 => 0
        | 1, 1 => 0
        | 1, 2 => 0
        | 2, 0 => 0
        | 2, 1 => 0
        | 2, 2 => 1
  }
  refine ⟨G, hG, ?eq4552, ?neq40⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 2
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation4552_not_implies_Equation41 : ∃ (G: Type) (_: Magma G), Equation4552 G ∧ ¬ Equation41 G := by
  let G := Fin 3
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 0
        | 0, 2 => 0
        | 1, 0 => 0
        | 1, 1 => 0
        | 1, 2 => 0
        | 2, 0 => 0
        | 2, 1 => 0
        | 2, 2 => 1
  }
  refine ⟨G, hG, ?eq4552, ?neq41⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 2 2
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation4552_not_implies_Equation42 : ∃ (G: Type) (_: Magma G), Equation4552 G ∧ ¬ Equation42 G := by
  let G := Fin 3
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 0
        | 0, 2 => 0
        | 1, 0 => 0
        | 1, 1 => 0
        | 1, 2 => 0
        | 2, 0 => 0
        | 2, 1 => 0
        | 2, 2 => 1
  }
  refine ⟨G, hG, ?eq4552, ?neq42⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 2 0 2
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation4552_not_implies_Equation43 : ∃ (G: Type) (_: Magma G), Equation4552 G ∧ ¬ Equation43 G := by
  let G := Fin 4
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 0
        | 0, 2 => 0
        | 0, 3 => 0
        | 1, 0 => 0
        | 1, 1 => 0
        | 1, 2 => 3
        | 1, 3 => 0
        | 2, 0 => 0
        | 2, 1 => 0
        | 2, 2 => 0
        | 2, 3 => 0
        | 3, 0 => 0
        | 3, 1 => 0
        | 3, 2 => 0
        | 3, 3 => 0
  }
  refine ⟨G, hG, ?eq4552, ?neq43⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 2
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation4552_not_implies_Equation46 : ∃ (G: Type) (_: Magma G), Equation4552 G ∧ ¬ Equation46 G := by
  let G := Fin 3
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 0
        | 0, 2 => 0
        | 1, 0 => 0
        | 1, 1 => 0
        | 1, 2 => 0
        | 2, 0 => 0
        | 2, 1 => 0
        | 2, 2 => 1
  }
  refine ⟨G, hG, ?eq4552, ?neq46⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 2 2 0 0
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation4552_not_implies_Equation168 : ∃ (G: Type) (_: Magma G), Equation4552 G ∧ ¬ Equation168 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0 0
    simp [hG] at h

theorem Equation4552_not_implies_Equation387 : ∃ (G: Type) (_: Magma G), Equation4552 G ∧ ¬ Equation387 G := by
  let G := Fin 3
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 0
        | 0, 2 => 0
        | 1, 0 => 0
        | 1, 1 => 0
        | 1, 2 => 0
        | 2, 0 => 0
        | 2, 1 => 0
        | 2, 2 => 1
  }
  refine ⟨G, hG, ?eq4552, ?neq387⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 2 2
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation4552_not_implies_Equation4582 : ∃ (G: Type) (_: Magma G), Equation4552 G ∧ ¬ Equation4582 G := by
  let G := Fin 3
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 0
        | 0, 1 => 0
        | 0, 2 => 1
        | 1, 0 => 0
        | 1, 1 => 0
        | 1, 2 => 1
        | 2, 0 => 1
        | 2, 1 => 1
        | 2, 2 => 0
  }
  refine ⟨G, hG, ?eq4552, ?neq4582⟩
  ·
    intro x y z w
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 2 0 0 0 0 0
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation4582_not_implies_Equation2 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation2 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w u v
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    fin_cases u <;>
    fin_cases v <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h

theorem Equation4582_not_implies_Equation3 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation3 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w u v
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    fin_cases u <;>
    fin_cases v <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1
    simp [hG] at h

theorem Equation4582_not_implies_Equation4 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation4 G := by
  let G := Fin 2
  let hG : Magma G := { op := fun x y ↦ 0 }
  refine ⟨G, hG, ?eq51, ?neq62⟩
  ·
    intro x y z w u v
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    fin_cases u <;>
    fin_cases v <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 0
    simp [hG] at h

theorem Equation4582_not_implies_Equation5 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation5 G := by
  let G := Fin 6
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 4
        | 0, 1 => 4
        | 0, 2 => 2
        | 0, 3 => 4
        | 0, 4 => 2
        | 0, 5 => 4
        | 1, 0 => 4
        | 1, 1 => 4
        | 1, 2 => 2
        | 1, 3 => 4
        | 1, 4 => 2
        | 1, 5 => 4
        | 2, 0 => 2
        | 2, 1 => 2
        | 2, 2 => 2
        | 2, 3 => 2
        | 2, 4 => 2
        | 2, 5 => 2
        | 3, 0 => 4
        | 3, 1 => 2
        | 3, 2 => 2
        | 3, 3 => 4
        | 3, 4 => 2
        | 3, 5 => 4
        | 4, 0 => 2
        | 4, 1 => 2
        | 4, 2 => 2
        | 4, 3 => 2
        | 4, 4 => 2
        | 4, 5 => 2
        | 5, 0 => 4
        | 5, 1 => 4
        | 5, 2 => 2
        | 5, 3 => 4
        | 5, 4 => 2
        | 5, 5 => 4
  }
  refine ⟨G, hG, ?eq4582, ?neq5⟩
  ·
    intro x y z w u v
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    fin_cases u <;>
    fin_cases v <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation4582_not_implies_Equation6 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation6 G := by
  let G := Fin 6
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 2
        | 0, 1 => 2
        | 0, 2 => 2
        | 0, 3 => 2
        | 0, 4 => 2
        | 0, 5 => 2
        | 1, 0 => 2
        | 1, 1 => 2
        | 1, 2 => 2
        | 1, 3 => 2
        | 1, 4 => 2
        | 1, 5 => 2
        | 2, 0 => 2
        | 2, 1 => 2
        | 2, 2 => 2
        | 2, 3 => 2
        | 2, 4 => 2
        | 2, 5 => 2
        | 3, 0 => 2
        | 3, 1 => 2
        | 3, 2 => 2
        | 3, 3 => 1
        | 3, 4 => 1
        | 3, 5 => 0
        | 4, 0 => 2
        | 4, 1 => 2
        | 4, 2 => 2
        | 4, 3 => 2
        | 4, 4 => 2
        | 4, 5 => 2
        | 5, 0 => 2
        | 5, 1 => 2
        | 5, 2 => 2
        | 5, 3 => 0
        | 5, 4 => 2
        | 5, 5 => 0
  }
  refine ⟨G, hG, ?eq4582, ?neq6⟩
  ·
    intro x y z w u v
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    fin_cases u <;>
    fin_cases v <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation4582_not_implies_Equation7 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation7 G := by
  let G := Fin 6
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 5
        | 0, 1 => 1
        | 0, 2 => 5
        | 0, 3 => 5
        | 0, 4 => 5
        | 0, 5 => 1
        | 1, 0 => 1
        | 1, 1 => 1
        | 1, 2 => 1
        | 1, 3 => 1
        | 1, 4 => 1
        | 1, 5 => 1
        | 2, 0 => 5
        | 2, 1 => 1
        | 2, 2 => 5
        | 2, 3 => 1
        | 2, 4 => 5
        | 2, 5 => 1
        | 3, 0 => 5
        | 3, 1 => 1
        | 3, 2 => 1
        | 3, 3 => 5
        | 3, 4 => 5
        | 3, 5 => 1
        | 4, 0 => 5
        | 4, 1 => 1
        | 4, 2 => 5
        | 4, 3 => 5
        | 4, 4 => 5
        | 4, 5 => 1
        | 5, 0 => 1
        | 5, 1 => 1
        | 5, 2 => 1
        | 5, 3 => 1
        | 5, 4 => 1
        | 5, 5 => 1
  }
  refine ⟨G, hG, ?eq4582, ?neq7⟩
  ·
    intro x y z w u v
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    fin_cases u <;>
    fin_cases v <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation4582_not_implies_Equation8 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation8 G := by
  let G := Fin 6
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 4
        | 0, 1 => 1
        | 0, 2 => 4
        | 0, 3 => 1
        | 0, 4 => 1
        | 0, 5 => 1
        | 1, 0 => 1
        | 1, 1 => 1
        | 1, 2 => 1
        | 1, 3 => 1
        | 1, 4 => 1
        | 1, 5 => 1
        | 2, 0 => 3
        | 2, 1 => 1
        | 2, 2 => 3
        | 2, 3 => 1
        | 2, 4 => 1
        | 2, 5 => 3
        | 3, 0 => 1
        | 3, 1 => 1
        | 3, 2 => 1
        | 3, 3 => 1
        | 3, 4 => 1
        | 3, 5 => 1
        | 4, 0 => 1
        | 4, 1 => 1
        | 4, 2 => 1
        | 4, 3 => 1
        | 4, 4 => 1
        | 4, 5 => 1
        | 5, 0 => 4
        | 5, 1 => 1
        | 5, 2 => 4
        | 5, 3 => 1
        | 5, 4 => 1
        | 5, 5 => 4
  }
  refine ⟨G, hG, ?eq4582, ?neq8⟩
  ·
    intro x y z w u v
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    fin_cases u <;>
    fin_cases v <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation4582_not_implies_Equation38 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation38 G := by
  let G := Fin 6
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 1
        | 0, 1 => 5
        | 0, 2 => 5
        | 0, 3 => 5
        | 0, 4 => 5
        | 0, 5 => 5
        | 1, 0 => 5
        | 1, 1 => 5
        | 1, 2 => 5
        | 1, 3 => 5
        | 1, 4 => 5
        | 1, 5 => 5
        | 2, 0 => 5
        | 2, 1 => 5
        | 2, 2 => 5
        | 2, 3 => 4
        | 2, 4 => 5
        | 2, 5 => 5
        | 3, 0 => 4
        | 3, 1 => 5
        | 3, 2 => 5
        | 3, 3 => 4
        | 3, 4 => 5
        | 3, 5 => 5
        | 4, 0 => 5
        | 4, 1 => 5
        | 4, 2 => 5
        | 4, 3 => 5
        | 4, 4 => 5
        | 4, 5 => 5
        | 5, 0 => 5
        | 5, 1 => 5
        | 5, 2 => 5
        | 5, 3 => 5
        | 5, 4 => 5
        | 5, 5 => 5
  }
  refine ⟨G, hG, ?eq4582, ?neq38⟩
  ·
    intro x y z w u v
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    fin_cases u <;>
    fin_cases v <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 1
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation4582_not_implies_Equation39 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation39 G := by
  let G := Fin 6
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 5
        | 0, 1 => 5
        | 0, 2 => 5
        | 0, 3 => 5
        | 0, 4 => 5
        | 0, 5 => 5
        | 1, 0 => 5
        | 1, 1 => 5
        | 1, 2 => 5
        | 1, 3 => 5
        | 1, 4 => 5
        | 1, 5 => 5
        | 2, 0 => 5
        | 2, 1 => 5
        | 2, 2 => 0
        | 2, 3 => 5
        | 2, 4 => 5
        | 2, 5 => 5
        | 3, 0 => 5
        | 3, 1 => 5
        | 3, 2 => 5
        | 3, 3 => 5
        | 3, 4 => 5
        | 3, 5 => 5
        | 4, 0 => 5
        | 4, 1 => 5
        | 4, 2 => 5
        | 4, 3 => 5
        | 4, 4 => 1
        | 4, 5 => 5
        | 5, 0 => 5
        | 5, 1 => 5
        | 5, 2 => 5
        | 5, 3 => 5
        | 5, 4 => 5
        | 5, 5 => 5
  }
  refine ⟨G, hG, ?eq4582, ?neq39⟩
  ·
    intro x y z w u v
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    fin_cases u <;>
    fin_cases v <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 2 0
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation4582_not_implies_Equation41 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation41 G := by
  let G := Fin 6
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 5
        | 0, 1 => 5
        | 0, 2 => 5
        | 0, 3 => 5
        | 0, 4 => 5
        | 0, 5 => 5
        | 1, 0 => 5
        | 1, 1 => 5
        | 1, 2 => 5
        | 1, 3 => 5
        | 1, 4 => 5
        | 1, 5 => 5
        | 2, 0 => 5
        | 2, 1 => 5
        | 2, 2 => 5
        | 2, 3 => 5
        | 2, 4 => 5
        | 2, 5 => 5
        | 3, 0 => 5
        | 3, 1 => 5
        | 3, 2 => 5
        | 3, 3 => 4
        | 3, 4 => 5
        | 3, 5 => 5
        | 4, 0 => 5
        | 4, 1 => 5
        | 4, 2 => 5
        | 4, 3 => 5
        | 4, 4 => 5
        | 4, 5 => 5
        | 5, 0 => 5
        | 5, 1 => 5
        | 5, 2 => 5
        | 5, 3 => 5
        | 5, 4 => 5
        | 5, 5 => 5
  }
  refine ⟨G, hG, ?eq4582, ?neq41⟩
  ·
    intro x y z w u v
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    fin_cases u <;>
    fin_cases v <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 3 3
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation4582_not_implies_Equation46 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation46 G := by
  let G := Fin 6
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 4
        | 0, 1 => 4
        | 0, 2 => 4
        | 0, 3 => 4
        | 0, 4 => 4
        | 0, 5 => 4
        | 1, 0 => 4
        | 1, 1 => 4
        | 1, 2 => 4
        | 1, 3 => 4
        | 1, 4 => 4
        | 1, 5 => 4
        | 2, 0 => 4
        | 2, 1 => 4
        | 2, 2 => 1
        | 2, 3 => 4
        | 2, 4 => 4
        | 2, 5 => 4
        | 3, 0 => 4
        | 3, 1 => 4
        | 3, 2 => 4
        | 3, 3 => 4
        | 3, 4 => 4
        | 3, 5 => 4
        | 4, 0 => 4
        | 4, 1 => 4
        | 4, 2 => 4
        | 4, 3 => 4
        | 4, 4 => 4
        | 4, 5 => 4
        | 5, 0 => 4
        | 5, 1 => 4
        | 5, 2 => 4
        | 5, 3 => 4
        | 5, 4 => 4
        | 5, 5 => 0
  }
  refine ⟨G, hG, ?eq4582, ?neq46⟩
  ·
    intro x y z w u v
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    fin_cases u <;>
    fin_cases v <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 2 2
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation4582_not_implies_Equation168 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation168 G := by
  let G := Fin 6
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 2
        | 0, 1 => 2
        | 0, 2 => 2
        | 0, 3 => 2
        | 0, 4 => 2
        | 0, 5 => 3
        | 1, 0 => 3
        | 1, 1 => 3
        | 1, 2 => 2
        | 1, 3 => 2
        | 1, 4 => 3
        | 1, 5 => 2
        | 2, 0 => 2
        | 2, 1 => 2
        | 2, 2 => 2
        | 2, 3 => 2
        | 2, 4 => 2
        | 2, 5 => 2
        | 3, 0 => 2
        | 3, 1 => 2
        | 3, 2 => 2
        | 3, 3 => 2
        | 3, 4 => 2
        | 3, 5 => 2
        | 4, 0 => 3
        | 4, 1 => 2
        | 4, 2 => 2
        | 4, 3 => 2
        | 4, 4 => 2
        | 4, 5 => 3
        | 5, 0 => 3
        | 5, 1 => 3
        | 5, 2 => 2
        | 5, 3 => 2
        | 5, 4 => 3
        | 5, 5 => 2
  }
  refine ⟨G, hG, ?eq4582, ?neq168⟩
  ·
    intro x y z w u v
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    fin_cases u <;>
    fin_cases v <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 0 0 0
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }

theorem Equation4582_not_implies_Equation387 : ∃ (G: Type) (_: Magma G), Equation4582 G ∧ ¬ Equation387 G := by
  let G := Fin 6
  let hG : Magma G := {
      op := fun x y ↦ match x, y with
        | 0, 0 => 5
        | 0, 1 => 5
        | 0, 2 => 5
        | 0, 3 => 5
        | 0, 4 => 5
        | 0, 5 => 5
        | 1, 0 => 5
        | 1, 1 => 2
        | 1, 2 => 5
        | 1, 3 => 5
        | 1, 4 => 5
        | 1, 5 => 5
        | 2, 0 => 5
        | 2, 1 => 5
        | 2, 2 => 5
        | 2, 3 => 5
        | 2, 4 => 5
        | 2, 5 => 5
        | 3, 0 => 5
        | 3, 1 => 5
        | 3, 2 => 5
        | 3, 3 => 5
        | 3, 4 => 5
        | 3, 5 => 5
        | 4, 0 => 5
        | 4, 1 => 5
        | 4, 2 => 5
        | 4, 3 => 5
        | 4, 4 => 5
        | 4, 5 => 5
        | 5, 0 => 5
        | 5, 1 => 5
        | 5, 2 => 5
        | 5, 3 => 5
        | 5, 4 => 5
        | 5, 5 => 5
  }
  refine ⟨G, hG, ?eq4582, ?neq387⟩
  ·
    intro x y z w u v
    fin_cases x <;>
    fin_cases y <;>
    fin_cases z <;>
    fin_cases w <;>
    fin_cases u <;>
    fin_cases v <;>
    all_goals simp [hG]
  ·
    intro h
    specialize h 1 1
    simp [hG] at h
    try { exact Fin.ne_of_val_ne (by decide) h }
