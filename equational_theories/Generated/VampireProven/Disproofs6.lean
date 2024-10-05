import equational_theories.AllEquations
import equational_theories.MemoFinOp
import equational_theories.DecideBang

@[equational_result]
theorem Equation3342_not_implies_Equation4635 : ∃ (G: Type) (_: Magma G), Equation3342 G ∧ ¬ Equation4635 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 2, 1, 5, 0, 3], [1, 5, 5, 4, 3, 2], [2, 5, 5, 3, 4, 1], [0, 3, 4, 2, 2, 5], [5, 4, 3, 2, 2, 0], [3, 1, 2, 0, 5, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3352_not_implies_Equation3862 : ∃ (G: Type) (_: Magma G), Equation3352 G ∧ ¬ Equation3862 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[1, 2, 1, 0, 3, 0, 0], [1, 5, 5, 1, 3, 2, 1], [0, 1, 4, 4, 3, 5, 3], [1, 5, 4, 6, 2, 0, 3], [2, 2, 3, 2, 2, 2, 3], [2, 5, 0, 5, 3, 0, 5], [1, 5, 3, 3, 3, 0, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation335_not_implies_Equation3722 : ∃ (G: Type) (_: Magma G), Equation335 G ∧ ¬ Equation3722 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 4, 4, 1], [4, 1, 0, 0, 2], [1, 4, 3, 3, 0], [1, 4, 3, 3, 0], [2, 0, 1, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3355_not_implies_Equation4131 : ∃ (G: Type) (_: Magma G), Equation3355 G ∧ ¬ Equation4131 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 2, 5, 5, 1, 4], [4, 1, 0, 2, 3, 4], [1, 3, 2, 5, 4, 0], [1, 4, 1, 3, 5, 2], [5, 0, 4, 1, 4, 3], [2, 2, 3, 4, 0, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3527_not_implies_Equation4314 : ∃ (G: Type) (_: Magma G), Equation3527 G ∧ ¬ Equation4314 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 4, 4, 4, 4], [0, 3, 3, 3, 3], [0, 0, 0, 0, 0], [3, 3, 3, 3, 3], [0, 0, 0, 0, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3535_not_implies_Equation4282 : ∃ (G: Type) (_: Magma G), Equation3535 G ∧ ¬ Equation4282 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 3, 3, 2, 2], [2, 1, 1, 2, 2], [4, 3, 3, 4, 4], [2, 1, 1, 2, 2], [4, 3, 3, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3535_not_implies_Equation4314 : ∃ (G: Type) (_: Magma G), Equation3535 G ∧ ¬ Equation4314 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 3, 3, 3, 2], [2, 0, 0, 0, 2], [4, 0, 0, 0, 4], [2, 3, 3, 3, 2], [4, 0, 0, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3545_not_implies_Equation3253 : ∃ (G: Type) (_: Magma G), Equation3545 G ∧ ¬ Equation3253 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[1, 2, 0, 5, 1, 7, 0, 3, 4], [4, 5, 0, 1, 2, 6, 5, 8, 5], [1, 4, 1, 7, 0, 3, 2, 5, 0], [7, 6, 3, 0, 5, 0, 8, 7, 1], [0, 0, 1, 3, 1, 5, 4, 7, 2], [3, 8, 5, 7, 7, 0, 1, 0, 6], [2, 5, 4, 6, 0, 8, 5, 1, 5], [5, 1, 7, 0, 3, 7, 6, 0, 8], [0, 5, 2, 8, 4, 1, 5, 6, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3545_not_implies_Equation3522 : ∃ (G: Type) (_: Magma G), Equation3545 G ∧ ¬ Equation3522 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[4, 1, 4, 3, 0, 2], [3, 2, 1, 2, 4, 5], [4, 3, 4, 1, 2, 0], [1, 2, 3, 2, 5, 4], [2, 5, 0, 4, 3, 3], [0, 4, 2, 5, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3545_not_implies_Equation3915 : ∃ (G: Type) (_: Magma G), Equation3545 G ∧ ¬ Equation3915 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[1, 2, 5, 1, 6, 4, 5, 3, 0], [3, 5, 0, 2, 1, 8, 7, 5, 2], [1, 3, 1, 5, 4, 5, 6, 0, 2], [5, 0, 1, 1, 5, 6, 4, 2, 3], [4, 8, 5, 6, 3, 3, 7, 1, 7], [5, 7, 6, 4, 7, 3, 3, 8, 1], [6, 1, 4, 5, 3, 7, 3, 7, 8], [0, 2, 2, 3, 7, 1, 8, 5, 5], [2, 5, 3, 0, 8, 7, 1, 2, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3545_not_implies_Equation3964 : ∃ (G: Type) (_: Magma G), Equation3545 G ∧ ¬ Equation3964 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[5, 1, 5, 3, 2, 0], [3, 2, 1, 2, 4, 5], [5, 3, 5, 1, 0, 2], [1, 2, 3, 2, 5, 4], [0, 5, 2, 4, 3, 3], [2, 4, 0, 5, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3545_not_implies_Equation4065 : ∃ (G: Type) (_: Magma G), Equation3545 G ∧ ¬ Equation4065 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[1, 5, 1, 4, 6, 3, 3, 2, 0], [2, 3, 5, 8, 7, 0, 1, 3, 3], [3, 0, 1, 3, 4, 1, 6, 5, 2], [6, 7, 4, 0, 0, 3, 6, 8, 1], [3, 1, 6, 6, 0, 4, 0, 7, 8], [1, 2, 3, 6, 3, 1, 4, 0, 5], [4, 8, 3, 0, 6, 6, 0, 1, 7], [0, 3, 2, 1, 8, 5, 7, 3, 3], [5, 3, 0, 7, 1, 2, 8, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3545_not_implies_Equation4283 : ∃ (G: Type) (_: Magma G), Equation3545 G ∧ ¬ Equation4283 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 1, 2, 0, 5, 3], [2, 5, 5, 4, 3, 1], [1, 5, 5, 3, 4, 2], [5, 3, 4, 1, 1, 0], [0, 4, 3, 1, 1, 5], [3, 2, 1, 5, 0, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3545_not_implies_Equation4380 : ∃ (G: Type) (_: Magma G), Equation3545 G ∧ ¬ Equation4380 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 0, 1, 3, 4, 2], [2, 4, 0, 5, 1, 4], [1, 2, 1, 4, 3, 0], [4, 1, 3, 2, 2, 5], [3, 5, 4, 2, 2, 1], [0, 4, 2, 1, 5, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3545_not_implies_Equation4635 : ∃ (G: Type) (_: Magma G), Equation3545 G ∧ ¬ Equation4635 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[4, 1, 2, 4, 0, 3], [2, 3, 3, 1, 4, 5], [1, 3, 3, 2, 5, 4], [4, 2, 1, 4, 3, 0], [3, 5, 4, 0, 2, 2], [0, 4, 5, 3, 2, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3546_not_implies_Equation4065 : ∃ (G: Type) (_: Magma G), Equation3546 G ∧ ¬ Equation4065 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 2, 1, 1, 2], [2, 3, 3, 2, 4], [2, 3, 4, 1, 4], [1, 2, 1, 1, 2], [1, 2, 4, 2, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3583_not_implies_Equation4128 : ∃ (G: Type) (_: Magma G), Equation3583 G ∧ ¬ Equation4128 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 2, 3, 4], [2, 3, 2, 3, 4], [3, 3, 2, 3, 4], [2, 3, 2, 3, 4], [4, 2, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3600_not_implies_Equation4155 : ∃ (G: Type) (_: Magma G), Equation3600 G ∧ ¬ Equation4155 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 2, 3, 4], [3, 4, 2, 3, 4], [3, 3, 2, 3, 4], [4, 2, 2, 3, 4], [4, 4, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation365_not_implies_Equation4091 : ∃ (G: Type) (_: Magma G), Equation365 G ∧ ¬ Equation4091 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 4, 2, 4, 3, 3], [5, 3, 5, 3, 0, 2], [2, 4, 2, 4, 3, 3], [4, 3, 4, 3, 2, 0], [3, 0, 3, 2, 4, 4], [1, 2, 1, 0, 5, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3671_not_implies_Equation3660 : ∃ (G: Type) (_: Magma G), Equation3671 G ∧ ¬ Equation3660 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 3, 2, 2, 2], [4, 4, 4, 4, 4], [2, 3, 2, 0, 2], [2, 3, 2, 2, 2], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3671_not_implies_Equation3664 : ∃ (G: Type) (_: Magma G), Equation3671 G ∧ ¬ Equation3664 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 3, 2, 2, 2], [4, 4, 4, 4, 4], [2, 0, 2, 2, 2], [2, 3, 0, 2, 2], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3698_not_implies_Equation3661 : ∃ (G: Type) (_: Magma G), Equation3698 G ∧ ¬ Equation3661 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 4, 2, 2, 4], [3, 4, 3, 0, 4], [2, 4, 2, 0, 4], [2, 4, 2, 2, 4], [2, 4, 2, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3698_not_implies_Equation3674 : ∃ (G: Type) (_: Magma G), Equation3698 G ∧ ¬ Equation3674 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 4, 3, 2, 4], [0, 4, 3, 0, 4], [2, 4, 2, 2, 4], [2, 4, 2, 2, 4], [2, 4, 2, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation384_not_implies_Equation3722 : ∃ (G: Type) (_: Magma G), Equation384 G ∧ ¬ Equation3722 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 4, 0, 1], [4, 1, 0, 1, 2], [1, 4, 3, 3, 0], [0, 1, 3, 3, 4], [2, 0, 1, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3926_not_implies_Equation3318 : ∃ (G: Type) (_: Magma G), Equation3926 G ∧ ¬ Equation3318 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 4, 2, 4], [3, 4, 3, 4, 4], [2, 2, 2, 2, 2], [3, 3, 3, 3, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3927_not_implies_Equation3253 : ∃ (G: Type) (_: Magma G), Equation3927 G ∧ ¬ Equation3253 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 2, 2, 1, 1], [2, 3, 3, 2, 2], [1, 3, 4, 1, 2], [1, 2, 1, 1, 2], [2, 2, 2, 2, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3929_not_implies_Equation3316 : ∃ (G: Type) (_: Magma G), Equation3929 G ∧ ¬ Equation3316 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 2, 2, 4, 2], [3, 4, 3, 2, 4], [2, 2, 2, 2, 2], [3, 3, 3, 3, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3951_not_implies_Equation3253 : ∃ (G: Type) (_: Magma G), Equation3951 G ∧ ¬ Equation3253 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 3, 5, 2, 1], [5, 4, 5, 1, 4, 2], [1, 5, 3, 2, 2, 1], [5, 1, 2, 3, 3, 5], [2, 4, 2, 3, 4, 5], [3, 2, 1, 5, 5, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3964_not_implies_Equation3253 : ∃ (G: Type) (_: Magma G), Equation3964 G ∧ ¬ Equation3253 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[1, 2, 0, 6, 4, 5, 1, 7, 0], [6, 4, 0, 4, 8, 1, 2, 3, 4], [1, 6, 1, 0, 7, 4, 0, 5, 2], [0, 4, 2, 4, 1, 3, 6, 8, 4], [7, 3, 5, 8, 2, 8, 4, 2, 1], [4, 8, 7, 1, 2, 2, 5, 8, 3], [0, 0, 1, 2, 5, 7, 1, 4, 6], [5, 1, 4, 3, 8, 2, 7, 2, 8], [2, 4, 6, 4, 3, 8, 0, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3964_not_implies_Equation3522 : ∃ (G: Type) (_: Magma G), Equation3964 G ∧ ¬ Equation3522 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[2, 1, 1, 0, 4, 7, 6, 2, 8], [2, 2, 7, 1, 6, 0, 8, 1, 4], [7, 0, 8, 6, 5, 8, 2, 1, 3], [1, 7, 8, 8, 2, 6, 3, 0, 5], [6, 8, 2, 3, 1, 5, 1, 4, 6], [0, 1, 6, 8, 3, 8, 5, 7, 2], [8, 4, 3, 5, 6, 2, 1, 6, 1], [1, 2, 0, 7, 8, 1, 4, 2, 6], [4, 6, 5, 2, 1, 3, 6, 8, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3964_not_implies_Equation3545 : ∃ (G: Type) (_: Magma G), Equation3964 G ∧ ¬ Equation3545 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 0, 3, 2, 4, 5], [3, 5, 5, 0, 1, 2], [0, 5, 5, 3, 2, 1], [2, 3, 0, 2, 5, 4], [5, 2, 1, 4, 0, 0], [4, 1, 2, 5, 0, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3964_not_implies_Equation3915 : ∃ (G: Type) (_: Magma G), Equation3964 G ∧ ¬ Equation3915 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 1, 4, 3, 0], [0, 4, 2, 1, 5, 4], [1, 0, 1, 3, 4, 2], [3, 5, 4, 2, 2, 1], [4, 1, 3, 2, 2, 5], [2, 4, 0, 5, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3964_not_implies_Equation4065 : ∃ (G: Type) (_: Magma G), Equation3964 G ∧ ¬ Equation4065 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[1, 4, 1, 7, 2, 3, 0, 5, 2], [2, 3, 4, 6, 0, 8, 1, 1, 3], [2, 0, 1, 5, 1, 7, 2, 3, 4], [3, 8, 7, 2, 5, 2, 1, 1, 6], [1, 2, 2, 3, 1, 5, 4, 7, 0], [5, 1, 3, 1, 7, 2, 6, 2, 8], [4, 3, 0, 8, 2, 1, 3, 6, 1], [7, 6, 5, 2, 3, 1, 8, 2, 1], [0, 1, 2, 1, 4, 6, 3, 8, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3964_not_implies_Equation4283 : ∃ (G: Type) (_: Magma G), Equation3964 G ∧ ¬ Equation4283 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[4, 2, 1, 0, 5, 4], [1, 5, 5, 4, 3, 2], [2, 5, 5, 3, 4, 1], [5, 3, 4, 2, 2, 0], [0, 4, 3, 2, 2, 5], [4, 1, 2, 5, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3964_not_implies_Equation4380 : ∃ (G: Type) (_: Magma G), Equation3964 G ∧ ¬ Equation4380 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 1, 5, 0, 3], [0, 3, 2, 4, 3, 1], [1, 0, 1, 3, 2, 5], [3, 1, 5, 2, 4, 2], [2, 3, 0, 1, 3, 4], [5, 4, 3, 2, 1, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3964_not_implies_Equation4635 : ∃ (G: Type) (_: Magma G), Equation3964 G ∧ ¬ Equation4635 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[4, 2, 1, 0, 5, 4], [1, 5, 5, 3, 4, 2], [2, 5, 5, 4, 3, 1], [5, 4, 3, 1, 1, 0], [0, 3, 4, 1, 1, 5], [4, 1, 2, 5, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4001_not_implies_Equation4606 : ∃ (G: Type) (_: Magma G), Equation4001 G ∧ ¬ Equation4606 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 3, 1, 3, 1], [2, 2, 4, 2, 4], [1, 3, 1, 3, 1], [1, 3, 1, 3, 1], [2, 2, 4, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4001_not_implies_Equation4666 : ∃ (G: Type) (_: Magma G), Equation4001 G ∧ ¬ Equation4666 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 2, 2, 1, 1], [3, 4, 4, 3, 3], [2, 2, 2, 1, 1], [3, 4, 4, 3, 3], [2, 2, 2, 1, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4040_not_implies_Equation4606 : ∃ (G: Type) (_: Magma G), Equation4040 G ∧ ¬ Equation4606 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 3, 2, 1, 1], [1, 4, 2, 1, 1], [2, 3, 2, 1, 1], [2, 3, 2, 1, 1], [2, 3, 2, 1, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4082_not_implies_Equation4070 : ∃ (G: Type) (_: Magma G), Equation4082 G ∧ ¬ Equation4070 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 2, 1, 1, 1], [1, 1, 1, 1, 1], [3, 4, 1, 1, 0], [4, 4, 0, 1, 4], [1, 1, 1, 1, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4082_not_implies_Equation4084 : ∃ (G: Type) (_: Magma G), Equation4082 G ∧ ¬ Equation4084 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 0, 0, 0, 0], [2, 0, 0, 0, 0], [4, 3, 0, 1, 4], [0, 4, 0, 0, 4], [0, 0, 0, 0, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4102_not_implies_Equation4070 : ∃ (G: Type) (_: Magma G), Equation4102 G ∧ ¬ Equation4070 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 2, 1, 1, 2], [1, 1, 1, 1, 1], [3, 1, 1, 1, 1], [4, 1, 1, 1, 1], [1, 0, 0, 0, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4102_not_implies_Equation4084 : ∃ (G: Type) (_: Magma G), Equation4102 G ∧ ¬ Equation4084 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 0, 0, 0, 0], [2, 0, 0, 0, 4], [0, 3, 0, 0, 4], [0, 4, 0, 0, 0], [0, 0, 0, 0, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4114_not_implies_Equation4073 : ∃ (G: Type) (_: Magma G), Equation4114 G ∧ ¬ Equation4073 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 3, 2, 2, 2], [4, 2, 2, 2, 4], [2, 2, 2, 2, 2], [2, 1, 2, 2, 2], [2, 2, 2, 2, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4114_not_implies_Equation4081 : ∃ (G: Type) (_: Magma G), Equation4114 G ∧ ¬ Equation4081 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 0, 0, 0, 0], [2, 0, 0, 0, 0], [3, 0, 0, 0, 0], [0, 4, 0, 0, 0], [0, 0, 1, 0, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation412_not_implies_Equation1427 : ∃ (G: Type) (_: Magma G), Equation412 G ∧ ¬ Equation1427 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 4, 0], [1, 1, 1, 1, 3], [4, 4, 2, 4, 2], [3, 0, 0, 3, 3], [1, 4, 1, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation412_not_implies_Equation2240 : ∃ (G: Type) (_: Magma G), Equation412 G ∧ ¬ Equation2240 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 4, 0], [4, 1, 4, 4, 1], [4, 4, 2, 4, 2], [2, 2, 3, 3, 2], [4, 2, 4, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation412_not_implies_Equation3254 : ∃ (G: Type) (_: Magma G), Equation412 G ∧ ¬ Equation3254 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 4, 0], [4, 1, 4, 4, 1], [1, 2, 2, 2, 3], [1, 3, 1, 3, 2], [4, 0, 3, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation412_not_implies_Equation413 : ∃ (G: Type) (_: Magma G), Equation412 G ∧ ¬ Equation413 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 3, 1, 4, 0], [2, 1, 1, 0, 0], [1, 2, 2, 4, 1], [2, 4, 3, 3, 2], [2, 2, 4, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation412_not_implies_Equation414 : ∃ (G: Type) (_: Magma G), Equation412 G ∧ ¬ Equation414 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 4, 0], [4, 1, 3, 4, 1], [1, 2, 2, 2, 1], [3, 0, 0, 3, 0], [1, 4, 0, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation412_not_implies_Equation615 : ∃ (G: Type) (_: Magma G), Equation412 G ∧ ¬ Equation615 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 4, 0], [3, 1, 3, 1, 1], [1, 2, 2, 1, 3], [4, 4, 4, 3, 3], [3, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation412_not_implies_Equation818 : ∃ (G: Type) (_: Magma G), Equation412 G ∧ ¬ Equation818 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 4, 0], [2, 1, 1, 0, 3], [1, 2, 2, 0, 1], [4, 4, 4, 3, 3], [1, 4, 0, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4154_not_implies_Equation3306 : ∃ (G: Type) (_: Magma G), Equation4154 G ∧ ¬ Equation3306 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 2, 3, 4, 1, 5], [4, 1, 0, 2, 5, 2], [1, 5, 2, 0, 4, 3], [2, 4, 5, 3, 0, 4], [3, 0, 4, 5, 4, 1], [5, 4, 1, 2, 3, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4167_not_implies_Equation3342 : ∃ (G: Type) (_: Magma G), Equation4167 G ∧ ¬ Equation3342 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 0, 1, 5, 2, 3], [2, 5, 0, 4, 5, 1], [1, 2, 1, 3, 0, 5], [3, 1, 5, 0, 4, 0], [0, 5, 2, 1, 5, 4], [5, 4, 3, 0, 1, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4167_not_implies_Equation3456 : ∃ (G: Type) (_: Magma G), Equation4167 G ∧ ¬ Equation3456 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[1, 0, 0, 5, 3, 4, 7, 1, 2], [2, 3, 7, 1, 6, 8, 3, 0, 3], [1, 2, 1, 3, 4, 5, 0, 0, 7], [3, 6, 4, 0, 0, 4, 8, 5, 1], [4, 8, 5, 4, 0, 0, 1, 3, 6], [5, 1, 3, 0, 4, 0, 6, 4, 8], [0, 3, 2, 6, 8, 1, 3, 7, 3], [0, 7, 1, 4, 5, 3, 2, 1, 0], [7, 3, 0, 8, 1, 6, 3, 2, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4167_not_implies_Equation3964 : ∃ (G: Type) (_: Magma G), Equation4167 G ∧ ¬ Equation3964 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 0, 5, 1, 3, 2], [3, 2, 1, 0, 2, 4], [2, 4, 0, 5, 1, 0], [1, 3, 2, 1, 0, 5], [0, 2, 4, 3, 2, 1], [5, 1, 0, 2, 4, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4167_not_implies_Equation4118 : ∃ (G: Type) (_: Magma G), Equation4167 G ∧ ¬ Equation4118 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 0, 1, 4, 3, 2], [2, 3, 0, 1, 5, 3], [1, 2, 1, 3, 4, 0], [3, 5, 4, 0, 0, 1], [4, 1, 3, 0, 0, 5], [0, 3, 2, 5, 1, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4167_not_implies_Equation4283 : ∃ (G: Type) (_: Magma G), Equation4167 G ∧ ¬ Equation4283 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[4, 1, 2, 4, 0, 3], [2, 3, 3, 1, 5, 4], [1, 3, 3, 2, 4, 5], [4, 2, 1, 4, 3, 0], [3, 4, 5, 0, 1, 1], [0, 5, 4, 3, 1, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4167_not_implies_Equation4380 : ∃ (G: Type) (_: Magma G), Equation4167 G ∧ ¬ Equation4380 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 0, 1, 4, 3, 2], [2, 4, 0, 5, 1, 4], [1, 2, 1, 3, 4, 0], [3, 1, 4, 0, 0, 5], [4, 5, 3, 0, 0, 1], [0, 4, 2, 1, 5, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4167_not_implies_Equation4635 : ∃ (G: Type) (_: Magma G), Equation4167 G ∧ ¬ Equation4635 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[4, 1, 2, 4, 0, 3], [2, 3, 3, 1, 5, 4], [1, 3, 3, 2, 4, 5], [4, 2, 1, 4, 3, 0], [3, 4, 5, 0, 1, 1], [0, 5, 4, 3, 1, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4175_not_implies_Equation4090 : ∃ (G: Type) (_: Magma G), Equation4175 G ∧ ¬ Equation4090 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 4, 2, 4, 4], [3, 1, 4, 3, 4], [2, 1, 2, 4, 4], [0, 4, 2, 3, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4175_not_implies_Equation4118 : ∃ (G: Type) (_: Magma G), Equation4175 G ∧ ¬ Equation4118 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 2, 3, 2], [4, 1, 2, 2, 4], [0, 1, 2, 3, 4], [3, 1, 2, 3, 2], [0, 2, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4175_not_implies_Equation4128 : ∃ (G: Type) (_: Magma G), Equation4175 G ∧ ¬ Equation4128 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 2, 3, 3], [3, 4, 3, 3, 4], [3, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 4, 3, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4175_not_implies_Equation4606 : ∃ (G: Type) (_: Magma G), Equation4175 G ∧ ¬ Equation4606 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 3, 2, 3, 2], [3, 3, 2, 3, 2], [0, 1, 2, 3, 4], [0, 4, 2, 3, 4], [3, 3, 2, 3, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation1021 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation1021 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 4, 4, 0], [3, 1, 3, 1, 3], [3, 2, 2, 2, 3], [3, 2, 3, 3, 2], [3, 4, 3, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation1022 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation1022 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 0, 3], [4, 1, 4, 4, 1], [2, 4, 2, 4, 2], [4, 4, 4, 3, 3], [4, 4, 0, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation1023 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation1023 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 0, 3], [4, 1, 4, 4, 1], [4, 2, 2, 4, 2], [3, 4, 3, 3, 3], [4, 3, 3, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation1224 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation1224 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 4, 4, 0], [3, 1, 3, 1, 3], [3, 2, 2, 2, 3], [3, 0, 0, 3, 0], [3, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation1429 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation1429 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 4, 0, 0], [3, 1, 3, 1, 0], [2, 0, 2, 0, 0], [3, 0, 3, 3, 0], [2, 2, 4, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation1630 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation1630 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 0, 0], [4, 1, 4, 4, 1], [4, 2, 2, 4, 2], [3, 0, 0, 3, 0], [4, 4, 3, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation1833 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation1833 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 4, 0, 0], [3, 1, 3, 1, 3], [2, 2, 2, 1, 2], [4, 4, 4, 3, 3], [3, 4, 3, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation1837 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation1837 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 0, 0], [4, 1, 4, 4, 1], [2, 2, 2, 0, 1], [2, 3, 3, 3, 1], [3, 3, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation1838 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation1838 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 0, 3], [4, 1, 4, 4, 1], [2, 2, 2, 0, 1], [2, 3, 3, 3, 1], [2, 2, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation2036 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation2036 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 0, 0], [4, 1, 4, 4, 1], [4, 4, 2, 4, 2], [3, 2, 3, 3, 2], [4, 4, 0, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation2246 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation2246 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 0, 0], [4, 1, 4, 4, 1], [4, 4, 2, 4, 2], [3, 2, 3, 3, 2], [4, 4, 3, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation2443 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation2443 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 0, 3], [4, 1, 4, 4, 1], [4, 4, 2, 4, 2], [2, 2, 3, 3, 2], [4, 2, 4, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation2646 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation2646 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 0, 0], [4, 1, 4, 4, 1], [3, 2, 2, 2, 1], [3, 2, 0, 3, 0], [4, 0, 0, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation2852 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation2852 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 0, 3], [4, 1, 4, 4, 1], [4, 2, 2, 4, 2], [4, 4, 4, 3, 3], [3, 4, 3, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation3256 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation3256 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 4, 4, 0], [3, 1, 3, 1, 3], [3, 2, 2, 2, 3], [3, 2, 3, 3, 0], [4, 2, 4, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation3318 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation3318 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 2, 1], [3, 1, 1, 4, 1], [3, 3, 2, 2, 2], [3, 3, 0, 3, 3], [3, 3, 3, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation3457 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation3457 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 0, 0], [4, 1, 4, 4, 1], [2, 2, 2, 0, 0], [3, 3, 0, 3, 0], [2, 2, 4, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation3660 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation3660 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 0, 0], [4, 1, 4, 4, 1], [3, 2, 2, 2, 1], [3, 0, 3, 3, 0], [2, 2, 4, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation3864 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation3864 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 0, 0], [4, 1, 4, 4, 1], [4, 2, 2, 4, 2], [3, 2, 3, 3, 2], [4, 0, 0, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation3918 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation3918 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 0, 0], [4, 1, 4, 4, 1], [4, 2, 2, 4, 2], [2, 0, 3, 3, 2], [3, 4, 3, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation419 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation419 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 3, 4, 4, 0], [2, 1, 1, 2, 2], [2, 2, 2, 0, 0], [2, 3, 3, 3, 2], [4, 4, 1, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation420 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation420 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 4, 4, 0], [3, 1, 3, 1, 3], [3, 3, 2, 2, 3], [3, 3, 3, 3, 3], [4, 4, 0, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation4282 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation4282 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 4, 0, 2, 2], [3, 1, 3, 1, 3], [3, 2, 2, 2, 3], [3, 3, 0, 3, 3], [2, 2, 4, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation50 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation50 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 0, 0], [4, 1, 4, 4, 1], [4, 4, 2, 4, 2], [4, 4, 4, 3, 3], [4, 0, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation617 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation617 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 4, 2], [1, 1, 0, 0, 1], [2, 3, 2, 2, 0], [1, 3, 1, 3, 1], [1, 4, 1, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation620 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation620 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 0, 4, 2, 0], [2, 1, 1, 1, 1], [2, 3, 2, 2, 0], [1, 3, 1, 3, 1], [2, 2, 4, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation623 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation623 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 4, 0, 0], [3, 1, 3, 1, 3], [2, 2, 2, 0, 0], [3, 3, 3, 3, 3], [4, 2, 4, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation820 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation820 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 4, 4, 0], [3, 1, 3, 1, 3], [2, 2, 2, 1, 0], [3, 2, 3, 3, 2], [4, 3, 0, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation418_not_implies_Equation823 : ∃ (G: Type) (_: Magma G), Equation418 G ∧ ¬ Equation823 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 0, 3], [2, 1, 4, 4, 1], [2, 2, 2, 4, 2], [3, 3, 4, 3, 3], [3, 3, 3, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation428_not_implies_Equation3723 : ∃ (G: Type) (_: Magma G), Equation428 G ∧ ¬ Equation3723 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 3, 4, 0, 0], [3, 1, 1, 1, 1], [4, 2, 2, 1, 2], [3, 3, 1, 3, 1], [4, 4, 4, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation428_not_implies_Equation824 : ∃ (G: Type) (_: Magma G), Equation428 G ∧ ¬ Equation824 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 3, 4, 0, 0], [4, 1, 3, 1, 1], [4, 4, 2, 2, 2], [3, 3, 3, 3, 1], [4, 4, 4, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation428_not_implies_Equation837 : ∃ (G: Type) (_: Magma G), Equation428 G ∧ ¬ Equation837 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 3, 0, 0, 2], [3, 1, 4, 1, 1], [2, 4, 2, 0, 2], [3, 3, 0, 3, 1], [2, 4, 4, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation433_not_implies_Equation1023 : ∃ (G: Type) (_: Magma G), Equation433 G ∧ ¬ Equation1023 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 0, 0, 4, 0], [1, 4, 4, 1, 1], [2, 3, 4, 2, 2], [4, 3, 3, 4, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation433_not_implies_Equation1224 : ∃ (G: Type) (_: Magma G), Equation433 G ∧ ¬ Equation1224 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 0, 0, 4, 0], [1, 4, 4, 1, 1], [2, 3, 4, 2, 2], [4, 3, 3, 4, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation433_not_implies_Equation1226 : ∃ (G: Type) (_: Magma G), Equation433 G ∧ ¬ Equation1226 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 0, 0, 4, 0], [1, 4, 4, 1, 1], [2, 3, 4, 2, 2], [4, 3, 3, 4, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation433_not_implies_Equation1249 : ∃ (G: Type) (_: Magma G), Equation433 G ∧ ¬ Equation1249 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 0, 4, 0, 0], [1, 2, 1, 4, 1], [3, 2, 4, 2, 2], [3, 2, 3, 4, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation433_not_implies_Equation3315 : ∃ (G: Type) (_: Magma G), Equation433 G ∧ ¬ Equation3315 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 2, 0, 0, 5, 0], [3, 2, 1, 4, 3, 1], [2, 2, 5, 2, 2, 2], [3, 2, 3, 5, 3, 3], [3, 5, 4, 4, 5, 4], [5, 5, 5, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation433_not_implies_Equation3870 : ∃ (G: Type) (_: Magma G), Equation433 G ∧ ¬ Equation3870 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 0, 0, 4, 0], [1, 3, 1, 1, 1], [2, 2, 4, 2, 2], [4, 3, 3, 4, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation433_not_implies_Equation439 : ∃ (G: Type) (_: Magma G), Equation433 G ∧ ¬ Equation439 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 3, 0, 4, 3], [2, 3, 1, 1, 2], [2, 2, 2, 2, 2], [2, 3, 3, 2, 3], [2, 3, 4, 4, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation433_not_implies_Equation818 : ∃ (G: Type) (_: Magma G), Equation433 G ∧ ¬ Equation818 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 3, 0, 1, 5, 0], [2, 5, 4, 1, 2, 1], [2, 3, 5, 1, 2, 2], [2, 3, 4, 5, 2, 3], [5, 3, 4, 1, 5, 4], [5, 5, 5, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation433_not_implies_Equation819 : ∃ (G: Type) (_: Magma G), Equation433 G ∧ ¬ Equation819 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 0, 0, 4, 0], [1, 4, 4, 1, 1], [2, 3, 4, 2, 2], [4, 3, 3, 4, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation433_not_implies_Equation820 : ∃ (G: Type) (_: Magma G), Equation433 G ∧ ¬ Equation820 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 4, 0, 0, 1, 0], [5, 3, 1, 1, 1, 1], [2, 2, 5, 4, 2, 2], [3, 3, 5, 4, 3, 3], [5, 4, 4, 4, 5, 4], [5, 5, 5, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation433_not_implies_Equation836 : ∃ (G: Type) (_: Magma G), Equation433 G ∧ ¬ Equation836 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 0, 1, 0], [2, 2, 1, 1, 1], [2, 2, 3, 2, 2], [4, 3, 3, 4, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation434_not_implies_Equation1023 : ∃ (G: Type) (_: Magma G), Equation434 G ∧ ¬ Equation1023 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 4, 0], [4, 4, 1, 2, 1], [4, 2, 4, 2, 2], [4, 2, 3, 4, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4364_not_implies_Equation4358 : ∃ (G: Type) (_: Magma G), Equation4364 G ∧ ¬ Equation4358 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[1, 4, 1, 3, 5, 3, 4, 5], [7, 5, 3, 3, 3, 3, 3, 3], [6, 4, 6, 3, 3, 3, 4, 5], [5, 3, 5, 3, 3, 3, 3, 3], [5, 3, 5, 3, 3, 3, 3, 3], [5, 3, 5, 3, 3, 3, 3, 3], [7, 5, 3, 3, 3, 3, 3, 3], [5, 3, 5, 3, 3, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4364_not_implies_Equation4362 : ∃ (G: Type) (_: Magma G), Equation4364 G ∧ ¬ Equation4362 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[7, 3, 4, 3, 3, 3, 3, 5], [6, 3, 3, 3, 5, 3, 3, 3], [6, 7, 7, 3, 5, 3, 5, 3], [3, 3, 3, 3, 3, 3, 3, 3], [3, 5, 5, 3, 3, 3, 3, 3], [3, 3, 3, 3, 3, 3, 3, 3], [3, 3, 3, 3, 3, 3, 3, 3], [3, 3, 3, 3, 3, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4364_not_implies_Equation4369 : ∃ (G: Type) (_: Magma G), Equation4364 G ∧ ¬ Equation4369 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[6, 6, 3, 4, 5, 5, 3, 4], [2, 2, 3, 5, 5, 5, 3, 4], [7, 4, 5, 5, 5, 5, 4, 5], [5, 5, 5, 5, 5, 5, 5, 5], [5, 5, 5, 5, 5, 5, 5, 5], [4, 5, 5, 5, 5, 5, 5, 5], [7, 4, 5, 5, 5, 5, 4, 5], [5, 5, 5, 5, 5, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4431_not_implies_Equation4283 : ∃ (G: Type) (_: Magma G), Equation4431 G ∧ ¬ Equation4283 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 3, 3, 2], [4, 2, 3, 3, 3], [3, 3, 3, 3, 3], [3, 3, 3, 3, 3], [3, 3, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4431_not_implies_Equation4284 : ∃ (G: Type) (_: Magma G), Equation4431 G ∧ ¬ Equation4284 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 3, 3, 2], [2, 4, 3, 3, 3], [3, 3, 3, 3, 3], [3, 3, 3, 3, 3], [3, 3, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4431_not_implies_Equation4290 : ∃ (G: Type) (_: Magma G), Equation4431 G ∧ ¬ Equation4290 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 2, 3, 3, 2], [3, 3, 4, 3, 3], [3, 3, 3, 3, 3], [3, 3, 3, 3, 3], [3, 3, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4431_not_implies_Equation4291 : ∃ (G: Type) (_: Magma G), Equation4431 G ∧ ¬ Equation4291 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 3, 3, 2], [3, 3, 4, 3, 3], [3, 3, 3, 3, 3], [3, 3, 3, 3, 3], [3, 3, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4431_not_implies_Equation4314 : ∃ (G: Type) (_: Magma G), Equation4431 G ∧ ¬ Equation4314 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 4, 3, 4, 4], [2, 4, 4, 2, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4431_not_implies_Equation4316 : ∃ (G: Type) (_: Magma G), Equation4431 G ∧ ¬ Equation4316 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 4, 4, 2, 4], [3, 4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4431_not_implies_Equation4320 : ∃ (G: Type) (_: Magma G), Equation4431 G ∧ ¬ Equation4320 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 3, 3, 4, 4], [2, 3, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4431_not_implies_Equation4321 : ∃ (G: Type) (_: Magma G), Equation4431 G ∧ ¬ Equation4321 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 4, 3, 4, 4], [2, 2, 4, 2, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4431_not_implies_Equation4332 : ∃ (G: Type) (_: Magma G), Equation4431 G ∧ ¬ Equation4332 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 4, 4, 2, 4], [3, 4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4431_not_implies_Equation4341 : ∃ (G: Type) (_: Magma G), Equation4431 G ∧ ¬ Equation4341 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 3, 3, 4, 4], [3, 2, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4431_not_implies_Equation4343 : ∃ (G: Type) (_: Magma G), Equation4431 G ∧ ¬ Equation4343 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 3, 3, 4, 4], [3, 2, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4431_not_implies_Equation4351 : ∃ (G: Type) (_: Magma G), Equation4431 G ∧ ¬ Equation4351 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 4, 4, 2, 4], [4, 3, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4431_not_implies_Equation4433 : ∃ (G: Type) (_: Magma G), Equation4431 G ∧ ¬ Equation4433 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 3, 3, 4, 4], [2, 4, 4, 2, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4431_not_implies_Equation4435 : ∃ (G: Type) (_: Magma G), Equation4431 G ∧ ¬ Equation4435 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 4, 3, 4, 4], [2, 3, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

