import equational_theories.AllEquations
import equational_theories.MemoFinOp
import equational_theories.DecideBang

@[equational_result]
theorem Equation4164_not_implies_Equation4380 : ∃ (G: Type) (_: Magma G), Equation4164 G ∧ ¬ Equation4380 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[1, 1, 0, 1, 2, 2, 1], [2, 5, 1, 5, 2, 5, 5], [1, 5, 4, 4, 3, 0, 3], [0, 1, 4, 6, 2, 5, 3], [3, 3, 3, 2, 2, 3, 3], [0, 2, 5, 0, 2, 0, 0], [0, 1, 3, 3, 3, 5, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4164_not_implies_Equation4479 : ∃ (G: Type) (_: Magma G), Equation4164 G ∧ ¬ Equation4479 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[1, 1, 0, 2, 2, 1, 1], [2, 4, 1, 2, 4, 4, 4], [1, 4, 3, 5, 0, 3, 5], [5, 5, 5, 2, 5, 2, 5], [0, 2, 4, 2, 0, 0, 0], [0, 1, 3, 2, 4, 6, 5], [0, 1, 5, 5, 4, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4164_not_implies_Equation4435 : ∃ (G: Type) (_: Magma G), Equation4164 G ∧ ¬ Equation4435 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 3, 3, 0, 0, 3], [2, 5, 5, 5, 2, 2], [3, 5, 4, 0, 2, 1], [0, 5, 0, 0, 0, 1], [0, 2, 2, 0, 2, 2], [2, 2, 1, 1, 2, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4164_not_implies_Equation3862 : ∃ (G: Type) (_: Magma G), Equation4164 G ∧ ¬ Equation3862 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[1, 1, 0, 2, 1, 2, 1], [2, 5, 1, 2, 5, 5, 5], [1, 5, 3, 4, 3, 0, 4], [4, 4, 4, 2, 2, 4, 4], [0, 1, 3, 2, 6, 5, 4], [0, 2, 5, 2, 0, 0, 0], [0, 1, 4, 4, 4, 5, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4164_not_implies_Equation3456 : ∃ (G: Type) (_: Magma G), Equation4164 G ∧ ¬ Equation3456 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[1, 1, 0, 2, 1, 2, 1], [2, 5, 1, 2, 5, 5, 5], [1, 5, 3, 4, 3, 0, 4], [4, 4, 4, 2, 2, 4, 4], [0, 1, 3, 2, 6, 5, 4], [0, 2, 5, 2, 0, 0, 0], [0, 1, 4, 4, 4, 5, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4084_not_implies_Equation3659 : ∃ (G: Type) (_: Magma G), Equation4084 G ∧ ¬ Equation3659 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 4, 4, 4, 3, 2], [0, 2, 4, 2, 4, 5], [0, 3, 2, 2, 2, 5], [5, 2, 2, 2, 1, 0], [5, 1, 1, 1, 2, 0], [2, 4, 4, 4, 3, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3961_not_implies_Equation3659 : ∃ (G: Type) (_: Magma G), Equation3961 G ∧ ¬ Equation3659 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[1, 5, 4, 1, 3, 6, 2], [3, 0, 5, 6, 2, 0, 4], [6, 4, 0, 5, 0, 1, 3], [4, 0, 6, 0, 5, 2, 1], [2, 6, 1, 0, 2, 3, 5], [1, 2, 3, 4, 6, 1, 0], [5, 3, 0, 2, 1, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3961_not_implies_Equation3456 : ∃ (G: Type) (_: Magma G), Equation3961 G ∧ ¬ Equation3456 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[1, 6, 3, 4, 5, 3, 2], [2, 1, 2, 1, 1, 5, 1], [6, 2, 2, 2, 5, 6, 4], [5, 1, 2, 3, 3, 5, 1], [3, 1, 6, 3, 4, 4, 6], [4, 5, 4, 5, 4, 5, 5], [1, 1, 5, 1, 6, 5, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3558_not_implies_Equation4065 : ∃ (G: Type) (_: Magma G), Equation3558 G ∧ ¬ Equation4065 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 4, 1, 4, 3, 2], [2, 5, 4, 1, 4, 1], [3, 4, 3, 2, 1, 2], [4, 1, 2, 3, 4, 5], [3, 4, 1, 4, 3, 2], [4, 1, 2, 5, 2, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3555_not_implies_Equation3659 : ∃ (G: Type) (_: Magma G), Equation3555 G ∧ ¬ Equation3659 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[1, 4, 1, 5, 3, 6, 2], [2, 0, 5, 6, 0, 3, 4], [6, 0, 2, 4, 5, 1, 3], [4, 5, 6, 3, 2, 0, 1], [1, 6, 3, 0, 2, 2, 5], [3, 2, 4, 1, 6, 0, 0], [5, 3, 0, 2, 1, 4, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3279_not_implies_Equation3659 : ∃ (G: Type) (_: Magma G), Equation3279 G ∧ ¬ Equation3659 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 0, 0, 4, 2, 0], [3, 2, 1, 1, 5, 2], [3, 2, 2, 1, 5, 1], [3, 3, 2, 2, 5, 1], [2, 1, 4, 4, 1, 0], [3, 2, 2, 1, 5, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3076_not_implies_Equation3522 : ∃ (G: Type) (_: Magma G), Equation3076 G ∧ ¬ Equation3522 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[0, 0, 6, 4, 0, 6, 0], [2, 2, 2, 2, 2, 2, 2], [3, 3, 3, 3, 3, 3, 3], [5, 5, 5, 5, 5, 5, 5], [4, 4, 0, 6, 4, 0, 4], [1, 1, 1, 1, 1, 1, 1], [6, 6, 4, 0, 6, 4, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3069_not_implies_Equation3522 : ∃ (G: Type) (_: Magma G), Equation3069 G ∧ ¬ Equation3522 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[0, 2, 0, 2, 0, 0, 5], [3, 3, 3, 3, 3, 3, 3], [2, 5, 2, 5, 2, 2, 0], [4, 4, 4, 4, 4, 4, 4], [6, 6, 6, 6, 6, 6, 6], [5, 0, 5, 0, 5, 5, 2], [1, 1, 1, 1, 1, 1, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2866_not_implies_Equation2035 : ∃ (G: Type) (_: Magma G), Equation2866 G ∧ ¬ Equation2035 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[1, 5, 3, 7, 2, 4, 6, 0], [2, 0, 7, 3, 1, 6, 4, 5], [4, 3, 5, 0, 6, 1, 2, 7], [5, 1, 4, 6, 0, 3, 7, 2], [3, 4, 1, 2, 7, 5, 0, 6], [6, 7, 0, 5, 4, 2, 1, 3], [0, 2, 6, 4, 5, 7, 3, 1], [7, 6, 2, 1, 3, 0, 5, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2853_not_implies_Equation3456 : ∃ (G: Type) (_: Magma G), Equation2853 G ∧ ¬ Equation3456 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[1, 2, 3, 6, 3, 6, 1, 2], [2, 5, 6, 5, 6, 3, 2, 3], [7, 4, 5, 0, 5, 0, 7, 4], [6, 7, 2, 7, 2, 1, 6, 1], [3, 6, 1, 2, 1, 2, 3, 6], [4, 3, 0, 3, 0, 5, 4, 7], [5, 0, 7, 4, 7, 4, 5, 0], [0, 1, 4, 1, 4, 7, 0, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2853_not_implies_Equation3253 : ∃ (G: Type) (_: Magma G), Equation2853 G ∧ ¬ Equation3253 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[1, 2, 3, 4, 1, 3, 4, 2], [2, 1, 4, 7, 2, 4, 1, 7], [7, 5, 6, 0, 7, 6, 0, 5], [4, 3, 2, 6, 4, 2, 3, 6], [6, 0, 7, 5, 6, 7, 5, 0], [3, 4, 1, 2, 3, 1, 2, 4], [5, 6, 0, 3, 5, 0, 6, 3], [0, 7, 5, 1, 0, 5, 7, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2853_not_implies_Equation2035 : ∃ (G: Type) (_: Magma G), Equation2853 G ∧ ¬ Equation2035 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[1, 2, 4, 4, 5, 1, 5, 2], [2, 1, 5, 5, 1, 2, 7, 7], [7, 3, 6, 6, 0, 7, 0, 3], [4, 5, 1, 1, 2, 4, 2, 5], [5, 6, 2, 2, 7, 5, 6, 4], [6, 0, 7, 7, 3, 6, 3, 0], [3, 4, 0, 0, 6, 3, 4, 6], [0, 7, 3, 3, 4, 0, 1, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2734_not_implies_Equation4273 : ∃ (G: Type) (_: Magma G), Equation2734 G ∧ ¬ Equation4273 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[2, 3, 1, 6, 0, 4, 5, 7], [7, 0, 6, 2, 4, 3, 1, 5], [3, 1, 5, 7, 2, 0, 4, 6], [1, 7, 3, 4, 6, 5, 0, 2], [5, 2, 4, 0, 7, 1, 6, 3], [0, 5, 7, 1, 3, 6, 2, 4], [4, 6, 2, 5, 1, 7, 3, 0], [6, 4, 0, 3, 5, 2, 7, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2734_not_implies_Equation99 : ∃ (G: Type) (_: Magma G), Equation2734 G ∧ ¬ Equation99 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[1, 7, 3, 4, 5, 0, 6, 2], [2, 4, 6, 5, 0, 1, 3, 7], [7, 1, 5, 0, 3, 4, 2, 6], [3, 0, 2, 6, 1, 7, 5, 4], [0, 3, 1, 7, 2, 6, 4, 5], [5, 6, 7, 2, 4, 3, 0, 1], [4, 2, 0, 1, 6, 5, 7, 3], [6, 5, 4, 3, 7, 2, 1, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2734_not_implies_Equation115 : ∃ (G: Type) (_: Magma G), Equation2734 G ∧ ¬ Equation115 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[2, 1, 4, 6, 3, 7, 5, 0], [5, 4, 3, 0, 6, 1, 2, 7], [6, 2, 5, 1, 4, 0, 7, 3], [3, 6, 2, 7, 1, 4, 0, 5], [1, 3, 7, 5, 0, 2, 6, 4], [0, 5, 6, 2, 7, 3, 4, 1], [4, 7, 0, 3, 5, 6, 1, 2], [7, 0, 1, 4, 2, 5, 3, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2734_not_implies_Equation2707 : ∃ (G: Type) (_: Magma G), Equation2734 G ∧ ¬ Equation2707 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[5, 3, 6, 7, 4, 2, 1, 0], [2, 4, 3, 1, 7, 0, 6, 5], [4, 1, 0, 5, 6, 7, 3, 2], [0, 2, 7, 6, 3, 1, 5, 4], [3, 5, 1, 4, 2, 6, 0, 7], [1, 7, 2, 0, 5, 3, 4, 6], [6, 0, 4, 2, 1, 5, 7, 3], [7, 6, 5, 3, 0, 4, 2, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2504_not_implies_Equation4065 : ∃ (G: Type) (_: Magma G), Equation2504 G ∧ ¬ Equation4065 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[1, 5, 6, 3, 7, 2, 4, 0], [2, 4, 3, 6, 0, 1, 5, 7], [3, 7, 2, 1, 5, 6, 0, 4], [5, 1, 0, 7, 3, 4, 2, 6], [4, 2, 7, 0, 6, 5, 1, 3], [7, 3, 4, 5, 1, 0, 6, 2], [0, 6, 5, 4, 2, 7, 3, 1], [6, 0, 1, 2, 4, 3, 7, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2504_not_implies_Equation4118 : ∃ (G: Type) (_: Magma G), Equation2504 G ∧ ¬ Equation4118 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[3, 2, 7, 5, 0, 1, 6, 4], [6, 1, 0, 4, 7, 2, 3, 5], [0, 5, 6, 2, 3, 4, 7, 1], [1, 6, 5, 7, 4, 3, 2, 0], [2, 3, 4, 0, 5, 6, 1, 7], [4, 7, 2, 6, 1, 0, 5, 3], [5, 0, 1, 3, 2, 7, 4, 6], [7, 4, 3, 1, 6, 5, 0, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2504_not_implies_Equation3456 : ∃ (G: Type) (_: Magma G), Equation2504 G ∧ ¬ Equation3456 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[1, 4, 3, 5, 2, 7, 6, 0], [2, 5, 6, 4, 1, 0, 3, 7], [6, 7, 2, 0, 3, 4, 1, 5], [0, 3, 4, 6, 7, 2, 5, 1], [7, 6, 5, 3, 0, 1, 4, 2], [5, 2, 7, 1, 4, 3, 0, 6], [4, 1, 0, 2, 5, 6, 7, 3], [3, 0, 1, 7, 6, 5, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2504_not_implies_Equation3522 : ∃ (G: Type) (_: Magma G), Equation2504 G ∧ ¬ Equation3522 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[5, 2, 6, 3, 1, 7, 0, 4], [0, 3, 4, 2, 7, 1, 5, 6], [2, 5, 1, 0, 6, 4, 3, 7], [7, 4, 3, 6, 0, 5, 1, 2], [3, 0, 7, 5, 4, 6, 2, 1], [4, 7, 0, 1, 3, 2, 6, 5], [1, 6, 2, 4, 5, 0, 7, 3], [6, 1, 5, 7, 2, 3, 4, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2504_not_implies_Equation3050 : ∃ (G: Type) (_: Magma G), Equation2504 G ∧ ¬ Equation3050 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[1, 4, 5, 3, 2, 6, 7, 0], [2, 6, 3, 5, 1, 4, 0, 7], [3, 7, 2, 1, 5, 0, 4, 6], [4, 1, 0, 7, 6, 2, 3, 5], [7, 3, 6, 4, 0, 5, 1, 2], [0, 5, 4, 6, 7, 3, 2, 1], [6, 2, 7, 0, 4, 1, 5, 3], [5, 0, 1, 2, 3, 7, 6, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2504_not_implies_Equation1629 : ∃ (G: Type) (_: Magma G), Equation2504 G ∧ ¬ Equation1629 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[1, 5, 6, 3, 7, 2, 4, 0], [2, 4, 3, 6, 0, 1, 5, 7], [3, 7, 2, 1, 5, 6, 0, 4], [5, 1, 0, 7, 3, 4, 2, 6], [4, 2, 7, 0, 6, 5, 1, 3], [7, 3, 4, 5, 1, 0, 6, 2], [0, 6, 5, 4, 2, 7, 3, 1], [6, 0, 1, 2, 4, 3, 7, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2504_not_implies_Equation47 : ∃ (G: Type) (_: Magma G), Equation2504 G ∧ ¬ Equation47 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[1, 2, 3, 7, 4, 6, 0, 5], [3, 5, 1, 4, 7, 0, 6, 2], [6, 4, 0, 5, 2, 1, 3, 7], [4, 6, 7, 3, 1, 2, 5, 0], [2, 1, 5, 0, 6, 4, 7, 3], [5, 3, 2, 6, 0, 7, 4, 1], [7, 0, 4, 1, 3, 5, 2, 6], [0, 7, 6, 2, 5, 3, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2504_not_implies_Equation23 : ∃ (G: Type) (_: Magma G), Equation2504 G ∧ ¬ Equation23 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[1, 3, 5, 2, 6, 4, 0, 7], [2, 4, 7, 1, 0, 3, 6, 5], [7, 6, 2, 5, 3, 0, 4, 1], [6, 7, 4, 0, 1, 5, 2, 3], [4, 2, 6, 3, 5, 1, 7, 0], [0, 5, 3, 6, 2, 7, 1, 4], [5, 0, 1, 7, 4, 6, 3, 2], [3, 1, 0, 4, 7, 2, 5, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2467_not_implies_Equation3050 : ∃ (G: Type) (_: Magma G), Equation2467 G ∧ ¬ Equation3050 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[1, 6, 2, 0, 5, 3, 4], [2, 4, 5, 3, 0, 6, 1], [0, 2, 3, 4, 6, 1, 5], [5, 1, 0, 6, 3, 4, 2], [4, 3, 1, 5, 2, 0, 6], [6, 0, 4, 2, 1, 5, 3], [3, 5, 6, 1, 4, 2, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2467_not_implies_Equation3079 : ∃ (G: Type) (_: Magma G), Equation2467 G ∧ ¬ Equation3079 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 3, 3, 3], [1, 4, 1, 1, 4], [2, 3, 2, 2, 0], [0, 0, 0, 0, 2], [4, 1, 4, 4, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2126_not_implies_Equation4606 : ∃ (G: Type) (_: Magma G), Equation2126 G ∧ ¬ Equation4606 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[2, 8, 7, 2, 8, 8, 2, 7, 7], [1, 1, 0, 6, 6, 6, 1, 0, 0], [3, 3, 0, 6, 6, 6, 3, 0, 0], [1, 1, 0, 6, 6, 6, 1, 0, 0], [3, 3, 5, 4, 4, 4, 3, 5, 5], [2, 8, 7, 2, 8, 8, 2, 7, 7], [3, 3, 5, 4, 4, 4, 3, 5, 5], [2, 8, 7, 2, 8, 8, 2, 7, 7], [1, 1, 5, 4, 4, 4, 1, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2126_not_implies_Equation4314 : ∃ (G: Type) (_: Magma G), Equation2126 G ∧ ¬ Equation4314 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[2, 7, 3, 3, 2, 7, 2, 3, 7], [2, 4, 3, 3, 2, 4, 2, 3, 4], [6, 4, 0, 0, 6, 4, 6, 0, 4], [2, 7, 3, 3, 2, 7, 2, 3, 7], [8, 5, 1, 1, 1, 5, 8, 8, 5], [8, 5, 1, 1, 1, 5, 8, 8, 5], [6, 4, 0, 0, 6, 4, 6, 0, 4], [8, 5, 1, 1, 1, 5, 8, 8, 5], [6, 7, 0, 0, 6, 7, 6, 0, 7]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2126_not_implies_Equation3522 : ∃ (G: Type) (_: Magma G), Equation2126 G ∧ ¬ Equation3522 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[0, 2, 0, 6, 6, 6, 0, 2, 2], [3, 3, 3, 4, 5, 5, 4, 4, 5], [8, 8, 8, 1, 1, 1, 7, 7, 7], [0, 2, 0, 1, 1, 1, 0, 2, 2], [3, 3, 3, 6, 6, 6, 7, 7, 7], [8, 8, 8, 4, 5, 5, 4, 4, 5], [3, 3, 3, 4, 5, 5, 4, 4, 5], [8, 8, 8, 6, 6, 6, 7, 7, 7], [0, 2, 0, 1, 1, 1, 0, 2, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2126_not_implies_Equation3521 : ∃ (G: Type) (_: Magma G), Equation2126 G ∧ ¬ Equation3521 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[0, 2, 0, 4, 0, 2, 4, 4, 2], [3, 1, 7, 1, 7, 7, 3, 1, 3], [5, 1, 5, 1, 5, 8, 8, 1, 8], [0, 6, 0, 6, 0, 8, 8, 6, 8], [3, 6, 7, 6, 7, 7, 3, 6, 3], [0, 2, 0, 4, 0, 2, 4, 4, 2], [3, 1, 7, 1, 7, 7, 3, 1, 3], [5, 2, 5, 4, 5, 2, 4, 4, 2], [5, 6, 5, 6, 5, 8, 8, 6, 8]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2126_not_implies_Equation3462 : ∃ (G: Type) (_: Magma G), Equation2126 G ∧ ¬ Equation3462 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[2, 3, 7, 7, 3, 2, 2, 7, 3], [1, 1, 0, 0, 5, 1, 5, 0, 5], [6, 6, 0, 0, 5, 6, 5, 0, 5], [1, 1, 8, 8, 4, 1, 4, 8, 4], [6, 6, 8, 8, 4, 6, 4, 8, 4], [6, 6, 8, 8, 4, 6, 4, 8, 4], [1, 1, 0, 0, 5, 1, 5, 0, 5], [2, 3, 7, 7, 3, 2, 2, 7, 3], [2, 3, 7, 7, 3, 2, 2, 7, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2126_not_implies_Equation3461 : ∃ (G: Type) (_: Magma G), Equation2126 G ∧ ¬ Equation3461 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[2, 4, 4, 1, 4, 1, 2, 2, 1], [3, 5, 3, 8, 5, 8, 3, 5, 8], [7, 0, 0, 6, 0, 6, 7, 7, 6], [2, 0, 0, 6, 0, 6, 2, 2, 6], [2, 4, 4, 1, 4, 1, 2, 2, 1], [7, 4, 4, 1, 4, 1, 7, 7, 1], [3, 5, 3, 8, 5, 8, 3, 5, 8], [7, 0, 0, 6, 0, 6, 7, 7, 6], [3, 5, 3, 8, 5, 8, 3, 5, 8]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2089_not_implies_Equation4268 : ∃ (G: Type) (_: Magma G), Equation2089 G ∧ ¬ Equation4268 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 1, 3, 1, 2], [3, 1, 3, 1, 3], [4, 0, 0, 0, 4], [2, 0, 0, 0, 2], [4, 0, 0, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2052_not_implies_Equation4314 : ∃ (G: Type) (_: Magma G), Equation2052 G ∧ ¬ Equation4314 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 0, 3, 0, 0], [2, 1, 1, 2, 2], [0, 4, 4, 0, 4], [2, 2, 2, 2, 2], [1, 1, 1, 1, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1922_not_implies_Equation4065 : ∃ (G: Type) (_: Magma G), Equation1922 G ∧ ¬ Equation4065 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 3, 5, 1, 2, 2], [2, 4, 1, 0, 5, 1], [3, 2, 4, 2, 3, 0], [5, 0, 3, 4, 2, 3], [5, 1, 2, 3, 5, 5], [1, 5, 0, 5, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1841_not_implies_Equation2238 : ∃ (G: Type) (_: Magma G), Equation1841 G ∧ ¬ Equation2238 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 3, 1, 3, 2], [5, 5, 0, 4, 0, 4], [0, 0, 4, 5, 4, 5], [4, 4, 5, 0, 5, 0], [3, 1, 2, 3, 2, 1], [2, 3, 1, 2, 1, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2447_not_implies_Equation3253 : ∃ (G: Type) (_: Magma G), Equation2447 G ∧ ¬ Equation3253 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 3, 2, 2, 4], [5, 1, 2, 3, 3, 0], [3, 0, 4, 0, 0, 1], [2, 3, 0, 1, 1, 5], [0, 4, 5, 4, 4, 2], [4, 5, 1, 5, 5, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1685_not_implies_Equation3253 : ∃ (G: Type) (_: Magma G), Equation1685 G ∧ ¬ Equation3253 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 3, 5, 1, 1], [3, 4, 2, 0, 1, 5], [5, 1, 4, 3, 2, 0], [1, 0, 2, 4, 3, 5], [3, 2, 1, 5, 2, 3], [2, 1, 0, 3, 5, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1682_not_implies_Equation1832 : ∃ (G: Type) (_: Magma G), Equation1682 G ∧ ¬ Equation1832 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 2, 4, 0, 3], [0, 3, 4, 1, 3], [3, 2, 2, 0, 1], [4, 1, 4, 3, 0], [2, 0, 2, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1662_not_implies_Equation4585 : ∃ (G: Type) (_: Magma G), Equation1662 G ∧ ¬ Equation4585 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[1, 3, 3, 1, 3, 3, 1, 1], [2, 0, 0, 4, 0, 0, 2, 2], [3, 5, 1, 7, 1, 1, 3, 3], [0, 4, 2, 0, 2, 2, 0, 0], [7, 1, 5, 3, 5, 5, 7, 7], [4, 6, 6, 2, 6, 6, 4, 4], [5, 7, 7, 5, 7, 7, 5, 5], [6, 2, 4, 6, 4, 4, 6, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1662_not_implies_Equation3050 : ∃ (G: Type) (_: Magma G), Equation1662 G ∧ ¬ Equation3050 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[1, 5, 5, 1, 1, 1, 5, 5], [2, 0, 0, 2, 2, 2, 0, 0], [3, 1, 1, 3, 3, 3, 1, 1], [4, 2, 2, 4, 4, 4, 2, 2], [7, 3, 3, 7, 7, 7, 3, 3], [0, 6, 6, 0, 0, 0, 6, 6], [5, 7, 7, 5, 5, 5, 7, 7], [6, 4, 4, 6, 6, 6, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1662_not_implies_Equation3079 : ∃ (G: Type) (_: Magma G), Equation1662 G ∧ ¬ Equation3079 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[2, 2, 2, 7, 7, 2, 7, 7], [6, 6, 6, 5, 5, 6, 5, 5], [3, 3, 3, 0, 0, 3, 0, 0], [4, 4, 4, 2, 2, 4, 2, 2], [5, 5, 5, 3, 3, 5, 3, 3], [1, 1, 1, 4, 4, 1, 4, 4], [7, 7, 7, 1, 1, 7, 1, 1], [0, 0, 0, 6, 6, 0, 6, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1662_not_implies_Equation3075 : ∃ (G: Type) (_: Magma G), Equation1662 G ∧ ¬ Equation3075 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[2, 2, 2, 3, 3, 3, 5, 2], [4, 7, 4, 7, 7, 7, 4, 4], [5, 3, 5, 0, 0, 0, 0, 5], [0, 5, 0, 5, 5, 5, 2, 0], [6, 1, 6, 1, 1, 1, 6, 6], [3, 0, 3, 2, 2, 2, 3, 3], [7, 4, 7, 4, 4, 4, 7, 7], [1, 6, 1, 6, 6, 6, 1, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1662_not_implies_Equation3066 : ∃ (G: Type) (_: Magma G), Equation1662 G ∧ ¬ Equation3066 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[5, 2, 2, 5, 5, 5, 2, 1], [0, 6, 6, 3, 3, 3, 6, 7], [3, 7, 7, 0, 0, 0, 7, 6], [4, 1, 1, 4, 4, 4, 1, 2], [6, 3, 3, 6, 6, 6, 3, 3], [7, 0, 0, 7, 7, 7, 0, 0], [2, 4, 4, 1, 1, 1, 4, 4], [1, 5, 5, 2, 2, 2, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1662_not_implies_Equation3058 : ∃ (G: Type) (_: Magma G), Equation1662 G ∧ ¬ Equation3058 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[2, 1, 1, 5, 5, 5, 1, 5], [4, 7, 7, 0, 0, 0, 7, 6], [7, 3, 3, 6, 6, 6, 3, 0], [6, 4, 4, 2, 2, 2, 4, 4], [3, 6, 6, 3, 3, 3, 6, 1], [0, 0, 0, 7, 7, 7, 0, 7], [1, 2, 2, 4, 4, 4, 2, 3], [5, 5, 5, 1, 1, 1, 5, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1662_not_implies_Equation3053 : ∃ (G: Type) (_: Magma G), Equation1662 G ∧ ¬ Equation3053 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[2, 2, 6, 6, 2, 6, 2, 6], [7, 4, 3, 4, 7, 3, 4, 4], [3, 3, 0, 0, 3, 0, 3, 0], [6, 1, 2, 2, 6, 2, 1, 2], [1, 5, 1, 5, 1, 1, 5, 5], [4, 7, 4, 7, 4, 4, 7, 7], [0, 0, 7, 3, 0, 7, 0, 3], [5, 6, 5, 1, 5, 5, 6, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1486_not_implies_Equation4606 : ∃ (G: Type) (_: Magma G), Equation1486 G ∧ ¬ Equation4606 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[2, 2, 5, 8, 2, 5, 8, 8, 5], [3, 1, 3, 1, 6, 6, 1, 6, 3], [4, 1, 0, 1, 4, 0, 1, 4, 0], [2, 2, 0, 8, 2, 0, 8, 8, 0], [4, 7, 0, 7, 4, 0, 7, 4, 0], [2, 2, 5, 8, 2, 5, 8, 8, 5], [4, 7, 5, 7, 4, 5, 7, 4, 5], [3, 1, 3, 1, 6, 6, 1, 6, 3], [3, 7, 3, 7, 6, 6, 7, 6, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1486_not_implies_Equation4314 : ∃ (G: Type) (_: Magma G), Equation1486 G ∧ ¬ Equation4314 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[0, 5, 3, 0, 5, 0, 3, 5, 3], [0, 2, 3, 0, 2, 0, 3, 2, 3], [1, 7, 1, 1, 7, 4, 4, 7, 4], [6, 2, 6, 6, 2, 8, 8, 2, 8], [6, 5, 6, 6, 5, 8, 8, 5, 8], [1, 7, 1, 1, 7, 4, 4, 7, 4], [0, 2, 3, 0, 2, 0, 3, 2, 3], [1, 7, 1, 1, 7, 4, 4, 7, 4], [6, 5, 6, 6, 5, 8, 8, 5, 8]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1486_not_implies_Equation4268 : ∃ (G: Type) (_: Magma G), Equation1486 G ∧ ¬ Equation4268 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[2, 1, 3, 3, 2, 1, 1, 3, 2], [5, 1, 5, 6, 5, 1, 1, 6, 6], [8, 0, 0, 0, 8, 4, 4, 4, 8], [2, 7, 3, 3, 2, 7, 7, 3, 2], [5, 7, 5, 6, 5, 7, 7, 6, 6], [2, 0, 0, 0, 2, 4, 4, 4, 2], [8, 7, 3, 3, 8, 7, 7, 3, 8], [5, 1, 5, 6, 5, 1, 1, 6, 6], [8, 0, 0, 0, 8, 4, 4, 4, 8]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1486_not_implies_Equation3952 : ∃ (G: Type) (_: Magma G), Equation1486 G ∧ ¬ Equation3952 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[3, 2, 7, 7, 3, 2, 2, 7, 3], [3, 1, 6, 1, 3, 6, 1, 6, 3], [5, 1, 6, 1, 5, 6, 1, 6, 5], [8, 4, 0, 0, 8, 4, 4, 0, 8], [5, 1, 6, 1, 5, 6, 1, 6, 5], [8, 4, 0, 0, 8, 4, 4, 0, 8], [5, 2, 7, 7, 5, 2, 2, 7, 5], [3, 2, 7, 7, 3, 2, 2, 7, 3], [8, 4, 0, 0, 8, 4, 4, 0, 8]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1486_not_implies_Equation3915 : ∃ (G: Type) (_: Magma G), Equation1486 G ∧ ¬ Equation3915 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[2, 1, 3, 1, 3, 2, 1, 3, 2], [6, 1, 3, 1, 3, 6, 1, 3, 6], [8, 0, 0, 0, 5, 5, 8, 8, 5], [2, 4, 4, 4, 7, 2, 7, 7, 2], [2, 1, 3, 1, 3, 2, 1, 3, 2], [8, 4, 4, 4, 5, 5, 8, 8, 5], [8, 0, 0, 0, 5, 5, 8, 8, 5], [6, 4, 4, 4, 7, 6, 7, 7, 6], [6, 0, 0, 0, 7, 6, 7, 7, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1486_not_implies_Equation3880 : ∃ (G: Type) (_: Magma G), Equation1486 G ∧ ¬ Equation3880 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[0, 2, 0, 2, 5, 0, 2, 5, 5], [6, 6, 3, 7, 3, 3, 7, 7, 6], [6, 6, 3, 1, 3, 3, 1, 1, 6], [4, 2, 4, 2, 5, 4, 2, 5, 5], [0, 2, 0, 2, 5, 0, 2, 5, 5], [4, 8, 4, 7, 8, 4, 7, 7, 8], [0, 8, 0, 1, 8, 0, 1, 1, 8], [6, 6, 3, 7, 3, 3, 7, 7, 6], [4, 8, 4, 1, 8, 4, 1, 1, 8]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1486_not_implies_Equation3864 : ∃ (G: Type) (_: Magma G), Equation1486 G ∧ ¬ Equation3864 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[1, 2, 3, 2, 3, 3, 1, 1, 2], [6, 0, 0, 0, 6, 7, 7, 6, 7], [1, 8, 3, 8, 3, 3, 1, 1, 8], [4, 2, 5, 2, 4, 5, 5, 4, 2], [4, 0, 0, 0, 4, 7, 7, 4, 7], [6, 2, 5, 2, 6, 5, 5, 6, 2], [4, 0, 0, 0, 4, 7, 7, 4, 7], [6, 8, 5, 8, 6, 5, 5, 6, 8], [1, 8, 3, 8, 3, 3, 1, 1, 8]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1485_not_implies_Equation4606 : ∃ (G: Type) (_: Magma G), Equation1485 G ∧ ¬ Equation4606 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[2, 4, 0, 2, 5, 0, 5, 4], [0, 3, 0, 3, 0, 0, 3, 3], [0, 3, 0, 3, 0, 0, 3, 3], [1, 3, 6, 1, 7, 6, 7, 3], [1, 3, 0, 1, 7, 0, 7, 3], [4, 4, 6, 4, 6, 6, 6, 4], [2, 4, 6, 2, 5, 6, 5, 4], [4, 4, 6, 4, 6, 6, 6, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1485_not_implies_Equation4314 : ∃ (G: Type) (_: Magma G), Equation1485 G ∧ ¬ Equation4314 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[2, 5, 0, 4, 0, 2, 4, 5], [0, 3, 0, 3, 0, 0, 3, 3], [0, 5, 0, 5, 0, 0, 5, 5], [1, 3, 6, 1, 6, 7, 7, 3], [6, 3, 6, 3, 6, 6, 3, 3], [1, 3, 6, 1, 6, 7, 7, 3], [2, 5, 0, 4, 0, 2, 4, 5], [6, 5, 6, 5, 6, 6, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1485_not_implies_Equation3952 : ∃ (G: Type) (_: Magma G), Equation1485 G ∧ ¬ Equation3952 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[2, 0, 0, 1, 5, 1, 2, 5], [5, 3, 3, 3, 5, 5, 3, 5], [0, 0, 0, 6, 6, 0, 6, 6], [2, 3, 3, 1, 6, 1, 2, 6], [0, 0, 0, 6, 6, 0, 6, 6], [4, 0, 0, 7, 5, 7, 4, 5], [4, 3, 3, 7, 6, 7, 4, 6], [5, 3, 3, 3, 5, 5, 3, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1485_not_implies_Equation3880 : ∃ (G: Type) (_: Magma G), Equation1485 G ∧ ¬ Equation3880 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[2, 3, 0, 2, 6, 3, 0, 6], [4, 7, 7, 4, 7, 4, 4, 7], [0, 3, 0, 0, 3, 3, 0, 3], [5, 7, 7, 5, 1, 4, 4, 1], [5, 3, 0, 5, 6, 3, 0, 6], [0, 3, 0, 0, 3, 3, 0, 3], [4, 7, 7, 4, 7, 4, 4, 7], [2, 7, 7, 2, 1, 4, 4, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1485_not_implies_Equation3521 : ∃ (G: Type) (_: Magma G), Equation1485 G ∧ ¬ Equation3521 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[6, 0, 1, 4, 6, 1, 0, 4], [2, 2, 5, 2, 2, 5, 5, 5], [3, 0, 1, 4, 3, 1, 0, 4], [0, 0, 4, 4, 0, 4, 0, 4], [3, 2, 7, 2, 3, 7, 5, 5], [6, 2, 7, 2, 6, 7, 5, 5], [0, 0, 4, 4, 0, 4, 0, 4], [2, 2, 5, 2, 2, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1485_not_implies_Equation3462 : ∃ (G: Type) (_: Magma G), Equation1485 G ∧ ¬ Equation3462 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[2, 4, 2, 4, 2, 4, 2, 4], [1, 3, 0, 1, 0, 3, 5, 5], [2, 6, 0, 4, 0, 6, 2, 4], [1, 1, 5, 1, 5, 1, 5, 5], [1, 3, 7, 1, 7, 3, 5, 5], [2, 6, 7, 4, 7, 6, 2, 4], [1, 1, 5, 1, 5, 1, 5, 5], [2, 4, 2, 4, 2, 4, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1483_not_implies_Equation4606 : ∃ (G: Type) (_: Magma G), Equation1483 G ∧ ¬ Equation4606 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[2, 5, 6, 2, 3, 6, 5, 3], [4, 4, 0, 7, 1, 0, 7, 1], [3, 3, 0, 0, 3, 0, 0, 3], [4, 4, 0, 7, 1, 0, 7, 1], [1, 1, 0, 0, 1, 0, 0, 1], [1, 1, 6, 6, 1, 6, 6, 1], [2, 5, 6, 2, 3, 6, 5, 3], [3, 3, 6, 6, 3, 6, 6, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1483_not_implies_Equation4314 : ∃ (G: Type) (_: Magma G), Equation1483 G ∧ ¬ Equation4314 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[2, 4, 2, 4, 2, 4, 2, 4], [2, 3, 2, 3, 2, 3, 2, 3], [2, 4, 0, 6, 0, 6, 2, 4], [5, 3, 1, 1, 7, 7, 5, 3], [5, 3, 1, 1, 7, 7, 5, 3], [2, 4, 0, 6, 0, 6, 2, 4], [5, 3, 5, 3, 5, 3, 5, 3], [5, 4, 5, 4, 5, 4, 5, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1483_not_implies_Equation3952 : ∃ (G: Type) (_: Magma G), Equation1483 G ∧ ¬ Equation3952 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[3, 2, 3, 2, 2, 2, 3, 3], [3, 4, 5, 4, 1, 1, 5, 3], [3, 4, 5, 4, 1, 1, 5, 3], [6, 7, 0, 0, 2, 2, 7, 6], [3, 1, 3, 1, 1, 1, 3, 3], [6, 2, 6, 2, 2, 2, 6, 6], [6, 7, 0, 0, 2, 2, 7, 6], [6, 1, 6, 1, 1, 1, 6, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1483_not_implies_Equation3880 : ∃ (G: Type) (_: Magma G), Equation1483 G ∧ ¬ Equation3880 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[2, 3, 5, 1, 3, 1, 5, 2], [5, 3, 5, 3, 3, 3, 5, 5], [7, 0, 0, 0, 7, 0, 7, 7], [4, 3, 5, 1, 3, 1, 5, 4], [7, 0, 0, 0, 7, 0, 7, 7], [2, 0, 0, 6, 7, 6, 7, 2], [5, 3, 5, 3, 3, 3, 5, 5], [4, 0, 0, 6, 7, 6, 7, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1483_not_implies_Equation3877 : ∃ (G: Type) (_: Magma G), Equation1483 G ∧ ¬ Equation3877 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[2, 2, 6, 2, 2, 6, 6, 6], [3, 2, 3, 3, 2, 2, 3, 2], [3, 7, 4, 1, 2, 6, 0, 5], [3, 2, 0, 3, 2, 6, 0, 6], [2, 2, 2, 2, 2, 2, 2, 2], [2, 7, 7, 7, 2, 2, 2, 7], [2, 7, 5, 7, 2, 6, 6, 5], [3, 7, 1, 1, 2, 2, 3, 7]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1483_not_implies_Equation3521 : ∃ (G: Type) (_: Magma G), Equation1483 G ∧ ¬ Equation3521 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[4, 2, 0, 1, 0, 4, 1, 2], [3, 3, 7, 5, 7, 6, 5, 6], [7, 7, 7, 1, 7, 1, 1, 1], [0, 0, 0, 1, 0, 1, 1, 1], [0, 0, 0, 5, 0, 5, 5, 5], [3, 3, 7, 5, 7, 6, 5, 6], [7, 7, 7, 5, 7, 5, 5, 5], [4, 2, 0, 1, 0, 4, 1, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1483_not_implies_Equation3462 : ∃ (G: Type) (_: Magma G), Equation1483 G ∧ ¬ Equation3462 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[2, 2, 5, 2, 5, 5, 2, 5], [3, 6, 7, 6, 3, 7, 1, 1], [3, 6, 0, 6, 3, 0, 1, 1], [2, 4, 0, 4, 5, 0, 2, 5], [3, 1, 3, 1, 3, 3, 1, 1], [2, 4, 7, 4, 5, 7, 2, 5], [3, 1, 3, 1, 3, 3, 1, 1], [2, 2, 5, 2, 5, 5, 2, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1483_not_implies_Equation3457 : ∃ (G: Type) (_: Magma G), Equation1483 G ∧ ¬ Equation3457 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[0, 2, 3, 0, 6, 6, 3, 2], [4, 1, 0, 0, 1, 6, 4, 6], [1, 7, 2, 6, 1, 6, 7, 2], [6, 2, 2, 6, 6, 6, 2, 2], [0, 6, 0, 0, 6, 6, 0, 6], [6, 6, 6, 6, 6, 6, 6, 6], [4, 7, 3, 0, 1, 6, 5, 2], [1, 1, 6, 6, 1, 6, 1, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1483_not_implies_Equation2124 : ∃ (G: Type) (_: Magma G), Equation1483 G ∧ ¬ Equation2124 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[0, 6, 1, 4, 6, 4, 0, 1], [2, 1, 7, 2, 7, 4, 4, 1], [3, 0, 2, 2, 3, 4, 0, 4], [0, 0, 4, 4, 0, 4, 0, 4], [3, 6, 7, 2, 5, 4, 0, 1], [4, 4, 4, 4, 4, 4, 4, 4], [4, 1, 1, 4, 1, 4, 4, 1], [2, 4, 2, 2, 2, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1483_not_implies_Equation2088 : ∃ (G: Type) (_: Magma G), Equation1483 G ∧ ¬ Equation2088 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[6, 4, 1, 2, 5, 7, 0, 3], [2, 1, 1, 2, 0, 3, 0, 3], [3, 0, 0, 3, 0, 3, 0, 3], [7, 5, 0, 3, 5, 7, 0, 3], [1, 1, 1, 1, 0, 0, 0, 0], [4, 4, 1, 1, 5, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [5, 5, 0, 0, 5, 5, 0, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1483_not_implies_Equation2050 : ∃ (G: Type) (_: Magma G), Equation1483 G ∧ ¬ Equation2050 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[0, 2, 0, 2, 3, 1, 1, 3], [6, 1, 3, 5, 6, 1, 5, 3], [3, 1, 3, 1, 3, 1, 1, 3], [4, 2, 0, 7, 6, 1, 5, 3], [0, 0, 0, 0, 3, 3, 3, 3], [6, 3, 3, 6, 6, 3, 6, 3], [4, 0, 0, 4, 6, 3, 6, 3], [3, 3, 3, 3, 3, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1483_not_implies_Equation1479 : ∃ (G: Type) (_: Magma G), Equation1483 G ∧ ¬ Equation1479 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[0, 3, 1, 0, 6, 1, 3, 6], [2, 1, 5, 6, 2, 1, 5, 6], [4, 0, 2, 0, 2, 6, 4, 6], [6, 1, 1, 6, 6, 1, 1, 6], [0, 0, 6, 0, 6, 6, 0, 6], [2, 6, 2, 6, 2, 6, 2, 6], [4, 3, 5, 0, 2, 1, 7, 6], [6, 6, 6, 6, 6, 6, 6, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1483_not_implies_Equation1429 : ∃ (G: Type) (_: Magma G), Equation1483 G ∧ ¬ Equation1429 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[0, 2, 3, 0, 7, 2, 7, 3], [6, 1, 0, 0, 7, 7, 1, 6], [1, 5, 2, 7, 7, 2, 1, 5], [7, 2, 2, 7, 7, 2, 7, 2], [7, 7, 7, 7, 7, 7, 7, 7], [1, 1, 7, 7, 7, 7, 1, 1], [0, 7, 0, 0, 7, 7, 7, 0], [6, 5, 3, 0, 7, 2, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1483_not_implies_Equation1428 : ∃ (G: Type) (_: Magma G), Equation1483 G ∧ ¬ Equation1428 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[0, 3, 1, 0, 7, 1, 7, 3], [2, 5, 6, 0, 7, 1, 4, 3], [0, 0, 1, 0, 1, 1, 1, 0], [1, 7, 1, 1, 7, 1, 7, 7], [6, 6, 6, 1, 1, 1, 6, 1], [1, 1, 1, 1, 1, 1, 1, 1], [2, 2, 6, 0, 1, 1, 6, 0], [6, 4, 6, 1, 7, 1, 4, 7]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1483_not_implies_Equation1485 : ∃ (G: Type) (_: Magma G), Equation1483 G ∧ ¬ Equation1485 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[2, 2, 7, 2, 2, 7, 7, 7], [3, 2, 3, 3, 2, 2, 2, 3], [3, 5, 4, 1, 2, 6, 7, 0], [3, 2, 0, 3, 2, 7, 7, 0], [2, 2, 2, 2, 2, 2, 2, 2], [3, 5, 1, 1, 2, 5, 2, 3], [2, 5, 5, 5, 2, 5, 2, 2], [2, 5, 6, 5, 2, 6, 7, 7]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1483_not_implies_Equation151 : ∃ (G: Type) (_: Magma G), Equation1483 G ∧ ¬ Equation151 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[1, 7, 1, 7, 1, 7, 1, 7], [6, 2, 1, 5, 3, 7, 4, 0], [1, 1, 1, 1, 1, 1, 1, 1], [6, 4, 1, 3, 3, 1, 4, 6], [6, 6, 1, 1, 1, 1, 6, 6], [1, 3, 1, 3, 3, 1, 3, 1], [6, 0, 1, 7, 1, 7, 6, 0], [1, 5, 1, 5, 3, 7, 3, 7]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1483_not_implies_Equation166 : ∃ (G: Type) (_: Magma G), Equation1483 G ∧ ¬ Equation166 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[0, 5, 1, 6, 1, 0, 5, 6], [2, 1, 4, 2, 1, 6, 4, 6], [3, 0, 2, 2, 6, 0, 3, 6], [0, 0, 6, 6, 6, 0, 0, 6], [2, 6, 2, 2, 6, 6, 2, 6], [6, 1, 1, 6, 1, 6, 1, 6], [3, 5, 4, 2, 1, 0, 7, 6], [6, 6, 6, 6, 6, 6, 6, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1483_not_implies_Equation152 : ∃ (G: Type) (_: Magma G), Equation1483 G ∧ ¬ Equation152 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[1, 3, 1, 3, 1, 1, 3, 3], [5, 2, 1, 0, 7, 4, 3, 6], [1, 1, 1, 1, 1, 1, 1, 1], [1, 6, 1, 3, 7, 7, 3, 6], [5, 5, 1, 5, 1, 5, 1, 1], [5, 0, 1, 0, 1, 5, 3, 3], [1, 7, 1, 1, 7, 7, 1, 7], [5, 4, 1, 5, 7, 4, 1, 7]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1480_not_implies_Equation4587 : ∃ (G: Type) (_: Magma G), Equation1480 G ∧ ¬ Equation4587 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 4, 1, 4, 4], [2, 0, 2, 2, 0], [3, 3, 2, 2, 0], [1, 0, 1, 2, 0], [3, 3, 1, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1082_not_implies_Equation4065 : ∃ (G: Type) (_: Magma G), Equation1082 G ∧ ¬ Equation4065 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 5, 3, 2, 0, 4], [2, 1, 0, 3, 4, 5], [3, 2, 4, 0, 5, 1], [2, 1, 0, 5, 4, 3], [2, 4, 0, 3, 1, 5], [4, 0, 1, 3, 2, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1184_not_implies_Equation4275 : ∃ (G: Type) (_: Magma G), Equation1184 G ∧ ¬ Equation4275 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[2, 4, 3, 7, 6, 1, 5, 0], [3, 7, 1, 4, 5, 0, 2, 6], [2, 4, 3, 7, 6, 1, 5, 0], [7, 5, 0, 2, 1, 6, 4, 3], [7, 5, 0, 2, 1, 6, 4, 3], [2, 4, 3, 7, 6, 1, 5, 0], [5, 2, 6, 0, 3, 4, 7, 1], [7, 5, 0, 2, 1, 6, 4, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1184_not_implies_Equation411 : ∃ (G: Type) (_: Magma G), Equation1184 G ∧ ¬ Equation411 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[1, 2, 3, 4, 6, 7, 5, 0], [7, 0, 1, 2, 3, 6, 4, 5], [7, 0, 1, 2, 3, 6, 4, 5], [1, 2, 3, 4, 6, 7, 5, 0], [1, 2, 3, 4, 6, 7, 5, 0], [7, 0, 1, 2, 3, 6, 4, 5], [7, 0, 1, 2, 3, 6, 4, 5], [1, 2, 3, 4, 6, 7, 5, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1184_not_implies_Equation513 : ∃ (G: Type) (_: Magma G), Equation1184 G ∧ ¬ Equation513 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[2, 0, 3, 4, 5, 6, 7, 1], [2, 0, 3, 4, 5, 6, 7, 1], [1, 7, 0, 2, 3, 4, 5, 6], [1, 7, 0, 2, 3, 4, 5, 6], [2, 0, 3, 4, 5, 6, 7, 1], [2, 0, 3, 4, 5, 6, 7, 1], [1, 7, 0, 2, 3, 4, 5, 6], [1, 7, 0, 2, 3, 4, 5, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1184_not_implies_Equation466 : ∃ (G: Type) (_: Magma G), Equation1184 G ∧ ¬ Equation466 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[4, 6, 3, 0, 2, 7, 5, 1], [2, 7, 3, 4, 0, 1, 5, 6], [3, 7, 4, 2, 0, 6, 1, 5], [3, 7, 4, 2, 0, 6, 1, 5], [4, 6, 3, 0, 2, 7, 5, 1], [4, 5, 0, 2, 3, 6, 7, 1], [4, 5, 0, 2, 3, 6, 7, 1], [2, 7, 3, 4, 0, 1, 5, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1184_not_implies_Equation436 : ∃ (G: Type) (_: Magma G), Equation1184 G ∧ ¬ Equation436 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[2, 3, 7, 4, 6, 0, 1, 5], [1, 7, 0, 4, 6, 3, 5, 2], [2, 0, 7, 5, 3, 6, 4, 1], [1, 7, 0, 4, 6, 3, 5, 2], [2, 0, 7, 5, 3, 6, 4, 1], [1, 7, 0, 4, 6, 3, 5, 2], [2, 0, 7, 5, 3, 6, 4, 1], [5, 6, 0, 1, 3, 7, 4, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1184_not_implies_Equation419 : ∃ (G: Type) (_: Magma G), Equation1184 G ∧ ¬ Equation419 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[5, 4, 0, 1, 7, 6, 2, 3], [2, 6, 3, 4, 0, 1, 7, 5], [2, 3, 6, 7, 1, 0, 5, 4], [2, 3, 6, 7, 1, 0, 5, 4], [5, 4, 0, 1, 7, 6, 2, 3], [5, 4, 0, 1, 7, 6, 2, 3], [2, 3, 6, 7, 1, 0, 5, 4], [4, 5, 0, 2, 3, 7, 1, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1184_not_implies_Equation500 : ∃ (G: Type) (_: Magma G), Equation1184 G ∧ ¬ Equation500 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[2, 0, 3, 1, 6, 7, 5, 4], [3, 7, 6, 4, 5, 0, 1, 2], [5, 6, 7, 0, 3, 4, 2, 1], [1, 3, 0, 2, 7, 6, 4, 5], [1, 3, 0, 2, 7, 6, 4, 5], [2, 0, 3, 1, 6, 7, 5, 4], [1, 3, 0, 2, 7, 6, 4, 5], [2, 0, 3, 1, 6, 7, 5, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation873_not_implies_Equation4588 : ∃ (G: Type) (_: Magma G), Equation873 G ∧ ¬ Equation4588 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[2, 4, 7, 5, 0, 6, 1, 3], [0, 5, 2, 1, 7, 4, 3, 6], [3, 1, 4, 6, 5, 0, 2, 7], [7, 2, 3, 0, 4, 1, 6, 5], [1, 3, 0, 7, 6, 2, 5, 4], [5, 7, 6, 4, 1, 3, 0, 2], [4, 6, 1, 3, 2, 5, 7, 0], [6, 0, 5, 2, 3, 7, 4, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation873_not_implies_Equation203 : ∃ (G: Type) (_: Magma G), Equation873 G ∧ ¬ Equation203 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[1, 2, 7, 6, 3, 0, 5, 4], [7, 5, 0, 1, 4, 2, 6, 3], [3, 4, 6, 5, 2, 7, 0, 1], [0, 6, 4, 2, 5, 1, 3, 7], [4, 3, 1, 0, 7, 6, 2, 5], [6, 0, 5, 4, 1, 3, 7, 2], [2, 1, 3, 7, 0, 5, 4, 6], [5, 7, 2, 3, 6, 4, 1, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation873_not_implies_Equation219 : ∃ (G: Type) (_: Magma G), Equation873 G ∧ ¬ Equation219 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[2, 3, 5, 0, 7, 6, 4, 1], [5, 4, 2, 3, 0, 7, 1, 6], [6, 1, 3, 5, 4, 0, 7, 2], [1, 6, 0, 7, 2, 3, 5, 4], [4, 5, 7, 1, 6, 2, 3, 0], [7, 0, 4, 6, 5, 1, 2, 3], [3, 2, 6, 4, 1, 5, 0, 7], [0, 7, 1, 2, 3, 4, 6, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation873_not_implies_Equation880 : ∃ (G: Type) (_: Magma G), Equation873 G ∧ ¬ Equation880 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[4, 2, 7, 1, 6, 3, 5, 0], [7, 6, 1, 3, 2, 5, 0, 4], [0, 5, 3, 7, 4, 2, 1, 6], [3, 0, 6, 5, 1, 7, 4, 2], [5, 4, 2, 0, 7, 1, 6, 3], [6, 1, 4, 2, 5, 0, 3, 7], [1, 7, 0, 6, 3, 4, 2, 5], [2, 3, 5, 4, 0, 6, 7, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation676_not_implies_Equation4065 : ∃ (G: Type) (_: Magma G), Equation676 G ∧ ¬ Equation4065 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[1, 2, 5, 7, 3, 0, 4, 6], [2, 3, 4, 6, 7, 5, 1, 0], [3, 7, 6, 2, 1, 4, 0, 5], [7, 3, 0, 6, 2, 5, 1, 4], [3, 7, 6, 2, 1, 4, 0, 5], [2, 3, 4, 6, 7, 5, 1, 0], [7, 3, 0, 6, 2, 5, 1, 4], [1, 2, 5, 7, 3, 0, 4, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation676_not_implies_Equation3862 : ∃ (G: Type) (_: Magma G), Equation676 G ∧ ¬ Equation3862 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[1, 2, 5, 7, 6, 0, 3, 4], [2, 5, 6, 3, 4, 1, 7, 0], [3, 7, 4, 2, 0, 6, 1, 5], [7, 3, 0, 1, 4, 5, 2, 6], [7, 3, 0, 1, 4, 5, 2, 6], [2, 1, 6, 3, 4, 5, 7, 0], [3, 7, 4, 2, 0, 6, 1, 5], [1, 2, 5, 7, 6, 0, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation676_not_implies_Equation1426 : ∃ (G: Type) (_: Magma G), Equation676 G ∧ ¬ Equation1426 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[1, 2, 6, 4, 7, 3, 0, 5], [2, 1, 3, 7, 5, 4, 6, 0], [4, 7, 5, 1, 2, 0, 3, 6], [4, 7, 5, 1, 2, 0, 3, 6], [7, 6, 0, 2, 5, 4, 1, 3], [7, 6, 0, 2, 4, 5, 1, 3], [2, 6, 3, 7, 5, 4, 1, 0], [1, 2, 6, 4, 7, 3, 0, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation667_not_implies_Equation4380 : ∃ (G: Type) (_: Magma G), Equation667 G ∧ ¬ Equation4380 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[1, 2, 5, 6, 4, 3, 0], [3, 0, 6, 4, 2, 5, 1], [0, 4, 3, 5, 6, 1, 2], [5, 1, 4, 2, 0, 6, 3], [2, 6, 1, 3, 5, 0, 4], [6, 3, 2, 0, 1, 4, 5], [4, 5, 0, 1, 3, 2, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation667_not_implies_Equation3050 : ∃ (G: Type) (_: Magma G), Equation667 G ∧ ¬ Equation3050 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[1, 6, 4, 2, 0, 5, 3], [2, 0, 5, 3, 1, 6, 4], [3, 1, 6, 4, 2, 0, 5], [4, 2, 0, 5, 3, 1, 6], [5, 3, 1, 6, 4, 2, 0], [6, 4, 2, 0, 5, 3, 1], [0, 5, 3, 1, 6, 4, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation667_not_implies_Equation2847 : ∃ (G: Type) (_: Magma G), Equation667 G ∧ ¬ Equation2847 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[1, 2, 4, 3, 5, 6, 0], [5, 0, 6, 2, 4, 3, 1], [0, 3, 5, 6, 1, 4, 2], [2, 6, 1, 4, 0, 5, 3], [6, 5, 2, 1, 3, 0, 4], [4, 1, 3, 0, 6, 2, 5], [3, 4, 0, 5, 2, 1, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation667_not_implies_Equation411 : ∃ (G: Type) (_: Magma G), Equation667 G ∧ ¬ Equation411 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[1, 2, 3, 4, 6, 5, 0], [4, 0, 6, 3, 5, 2, 1], [0, 5, 4, 1, 3, 6, 2], [6, 4, 2, 5, 0, 1, 3], [3, 1, 5, 6, 2, 0, 4], [2, 6, 1, 0, 4, 3, 5], [5, 3, 0, 2, 1, 4, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1885_not_implies_Equation1629 : ∃ (G: Type) (_: Magma G), Equation1885 G ∧ ¬ Equation1629 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 0, 3, 4, 2], [2, 3, 2, 1, 0], [4, 4, 2, 4, 2], [0, 1, 0, 3, 2], [3, 3, 1, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3059_not_implies_Equation3522 : ∃ (G: Type) (_: Magma G), Equation3059 G ∧ ¬ Equation3522 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[0, 2, 0, 2, 0, 0, 2], [3, 3, 3, 3, 3, 3, 3], [2, 5, 2, 5, 2, 2, 5], [4, 4, 4, 4, 4, 4, 4], [6, 6, 6, 6, 6, 6, 6], [5, 0, 5, 0, 5, 5, 0], [1, 1, 1, 1, 1, 1, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation168_not_implies_Equation4606 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation4606 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[2, 2, 7, 2, 8, 8, 8, 7, 7], [4, 4, 4, 6, 5, 5, 5, 6, 6], [3, 3, 0, 3, 1, 1, 1, 0, 0], [3, 3, 0, 3, 1, 1, 1, 0, 0], [2, 2, 0, 2, 1, 1, 1, 0, 0], [4, 4, 4, 6, 5, 5, 5, 6, 6], [3, 3, 7, 3, 8, 8, 8, 7, 7], [2, 2, 7, 2, 8, 8, 8, 7, 7], [4, 4, 4, 6, 5, 5, 5, 6, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation168_not_implies_Equation4587 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation4587 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[2, 2, 7, 2, 8, 8, 8, 7, 7], [3, 3, 6, 5, 3, 5, 5, 6, 6], [3, 3, 0, 1, 3, 1, 1, 0, 0], [4, 4, 0, 1, 4, 1, 1, 0, 0], [4, 4, 0, 1, 4, 1, 1, 0, 0], [3, 3, 6, 5, 3, 5, 5, 6, 6], [2, 2, 7, 2, 8, 8, 8, 7, 7], [2, 2, 7, 2, 8, 8, 8, 7, 7], [4, 4, 6, 5, 4, 5, 5, 6, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation168_not_implies_Equation4615 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation4615 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[3, 7, 8, 7, 3, 8, 8, 7, 3], [2, 5, 2, 6, 5, 2, 5, 6, 6], [2, 5, 2, 0, 5, 2, 5, 0, 0], [4, 4, 8, 0, 4, 8, 8, 0, 0], [4, 4, 1, 0, 4, 1, 1, 0, 0], [4, 4, 1, 6, 4, 1, 1, 6, 6], [3, 7, 8, 7, 3, 8, 8, 7, 3], [3, 7, 1, 7, 3, 1, 1, 7, 3], [2, 5, 2, 6, 5, 2, 5, 6, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation168_not_implies_Equation4314 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation4314 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[3, 7, 3, 5, 5, 5, 3, 7, 7], [2, 4, 2, 5, 5, 5, 2, 4, 4], [2, 6, 2, 0, 6, 0, 2, 0, 6], [2, 6, 2, 0, 6, 0, 2, 0, 6], [8, 7, 1, 8, 1, 1, 8, 7, 7], [3, 4, 3, 5, 5, 5, 3, 4, 4], [8, 4, 1, 8, 1, 1, 8, 4, 4], [8, 7, 1, 8, 1, 1, 8, 7, 7], [3, 6, 3, 0, 6, 0, 3, 0, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation168_not_implies_Equation4268 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation4268 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[2, 3, 1, 3, 2, 1, 2, 1, 3], [2, 5, 5, 5, 2, 7, 2, 7, 7], [6, 0, 0, 0, 6, 4, 6, 4, 4], [8, 3, 1, 3, 8, 1, 8, 1, 3], [8, 5, 5, 5, 8, 7, 8, 7, 7], [2, 3, 1, 3, 2, 1, 2, 1, 3], [6, 0, 0, 0, 6, 4, 6, 4, 4], [8, 5, 5, 5, 8, 7, 8, 7, 7], [6, 0, 0, 0, 6, 4, 6, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation168_not_implies_Equation4315 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation4315 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[3, 3, 7, 5, 5, 5, 7, 3, 7], [1, 1, 4, 0, 1, 0, 4, 0, 4], [8, 8, 2, 6, 8, 6, 2, 6, 2], [1, 1, 7, 0, 1, 0, 7, 0, 7], [8, 8, 2, 6, 8, 6, 2, 6, 2], [3, 3, 4, 5, 5, 5, 4, 3, 4], [3, 3, 7, 5, 5, 5, 7, 3, 7], [8, 8, 2, 6, 8, 6, 2, 6, 2], [1, 1, 4, 0, 1, 0, 4, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation168_not_implies_Equation3952 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation3952 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[0, 2, 0, 7, 7, 2, 7, 0, 2], [3, 4, 6, 6, 3, 4, 6, 3, 4], [8, 8, 8, 1, 1, 5, 1, 5, 5], [0, 4, 0, 7, 7, 4, 7, 0, 4], [8, 8, 8, 1, 1, 5, 1, 5, 5], [8, 8, 8, 7, 7, 5, 7, 5, 5], [3, 2, 6, 6, 3, 2, 6, 3, 2], [3, 4, 6, 6, 3, 4, 6, 3, 4], [0, 2, 0, 1, 1, 2, 1, 0, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation168_not_implies_Equation3915 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation3915 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[3, 2, 8, 2, 2, 3, 3, 8, 8], [3, 2, 8, 2, 2, 3, 3, 8, 8], [3, 4, 1, 1, 4, 3, 3, 4, 1], [5, 6, 0, 0, 5, 6, 6, 5, 0], [7, 4, 1, 1, 4, 7, 7, 4, 1], [7, 4, 0, 0, 4, 7, 7, 4, 0], [5, 6, 1, 1, 5, 6, 6, 5, 1], [5, 6, 0, 0, 5, 6, 6, 5, 0], [7, 2, 8, 2, 2, 7, 7, 8, 8]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation168_not_implies_Equation3880 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation3880 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[2, 1, 8, 1, 2, 2, 8, 8, 1], [3, 1, 8, 1, 3, 3, 8, 8, 1], [5, 0, 0, 4, 5, 5, 4, 4, 0], [5, 0, 0, 4, 5, 5, 4, 4, 0], [3, 6, 6, 7, 3, 3, 7, 7, 6], [5, 0, 0, 4, 5, 5, 4, 4, 0], [2, 1, 8, 1, 2, 2, 8, 8, 1], [3, 6, 6, 7, 3, 3, 7, 7, 6], [2, 6, 6, 7, 2, 2, 7, 7, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation168_not_implies_Equation3997 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation3997 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[1, 2, 7, 2, 1, 7, 1, 2, 7], [4, 0, 0, 6, 6, 6, 4, 0, 4], [1, 3, 7, 3, 1, 7, 1, 3, 7], [1, 3, 7, 3, 1, 7, 1, 3, 7], [8, 0, 0, 6, 6, 6, 8, 0, 8], [4, 2, 5, 2, 5, 5, 4, 2, 4], [4, 3, 5, 3, 5, 5, 4, 3, 4], [8, 2, 5, 2, 5, 5, 8, 2, 8], [8, 0, 0, 6, 6, 6, 8, 0, 8]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation168_not_implies_Equation3989 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation3989 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[4, 3, 8, 4, 8, 4, 3, 3, 8], [4, 1, 6, 4, 1, 4, 1, 6, 6], [7, 1, 6, 7, 1, 7, 1, 6, 6], [7, 1, 6, 7, 1, 7, 1, 6, 6], [5, 3, 5, 0, 0, 5, 3, 3, 0], [5, 2, 5, 0, 0, 5, 2, 2, 0], [7, 2, 8, 7, 8, 7, 2, 2, 8], [5, 3, 5, 0, 0, 5, 3, 3, 0], [4, 2, 8, 4, 8, 4, 2, 2, 8]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation168_not_implies_Equation3864 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation3864 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[2, 3, 5, 2, 2, 5, 3, 5, 3], [4, 7, 6, 6, 4, 6, 7, 4, 7], [4, 3, 0, 0, 4, 0, 3, 4, 3], [8, 8, 6, 6, 1, 6, 1, 1, 8], [4, 7, 0, 0, 4, 0, 7, 4, 7], [2, 7, 5, 2, 2, 5, 7, 5, 7], [2, 3, 5, 2, 2, 5, 3, 5, 3], [8, 8, 6, 6, 1, 6, 1, 1, 8], [8, 8, 0, 0, 1, 0, 1, 1, 8]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation168_not_implies_Equation3921 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation3921 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[3, 3, 1, 7, 3, 1, 7, 7, 1], [8, 8, 5, 2, 8, 5, 2, 2, 5], [3, 3, 6, 7, 3, 6, 7, 7, 6], [4, 0, 1, 0, 4, 1, 4, 0, 1], [4, 0, 6, 0, 4, 6, 4, 0, 6], [8, 8, 5, 2, 8, 5, 2, 2, 5], [8, 8, 5, 2, 8, 5, 2, 2, 5], [3, 3, 6, 7, 3, 6, 7, 7, 6], [4, 0, 1, 0, 4, 1, 4, 0, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation168_not_implies_Equation3883 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation3883 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[3, 2, 2, 2, 1, 3, 1, 3, 1], [8, 8, 4, 8, 6, 4, 4, 6, 6], [3, 2, 2, 2, 1, 3, 1, 3, 1], [5, 0, 0, 0, 7, 5, 5, 7, 7], [5, 2, 2, 2, 6, 5, 5, 6, 6], [5, 0, 0, 0, 6, 5, 5, 6, 6], [8, 8, 4, 8, 7, 4, 4, 7, 7], [8, 8, 4, 8, 7, 4, 4, 7, 7], [3, 0, 0, 0, 1, 3, 1, 3, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation168_not_implies_Equation3958 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation3958 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[2, 2, 3, 3, 8, 8, 2, 8, 3], [7, 1, 7, 4, 1, 4, 4, 1, 7], [6, 1, 0, 0, 1, 6, 6, 1, 0], [2, 2, 3, 3, 8, 8, 2, 8, 3], [6, 5, 3, 3, 5, 6, 6, 5, 3], [7, 1, 7, 4, 1, 4, 4, 1, 7], [6, 5, 0, 0, 5, 6, 6, 5, 0], [2, 2, 0, 0, 8, 8, 2, 8, 0], [7, 5, 7, 4, 5, 4, 4, 5, 7]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation168_not_implies_Equation3522 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation3522 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[1, 2, 3, 3, 1, 2, 1, 2, 3], [6, 0, 0, 0, 6, 4, 6, 4, 4], [1, 7, 5, 5, 1, 7, 1, 7, 5], [8, 2, 3, 3, 8, 2, 8, 2, 3], [8, 7, 5, 5, 8, 7, 8, 7, 5], [8, 2, 3, 3, 8, 2, 8, 2, 3], [6, 0, 0, 0, 6, 4, 6, 4, 4], [1, 7, 5, 5, 1, 7, 1, 7, 5], [6, 0, 0, 0, 6, 4, 6, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation168_not_implies_Equation3521 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation3521 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[5, 2, 2, 8, 5, 2, 8, 8, 5], [7, 3, 6, 7, 3, 6, 3, 7, 6], [5, 2, 2, 1, 5, 2, 1, 1, 5], [4, 4, 6, 1, 4, 6, 1, 1, 6], [4, 4, 0, 1, 4, 0, 1, 1, 0], [4, 4, 0, 8, 4, 0, 8, 8, 0], [5, 2, 2, 8, 5, 2, 8, 8, 5], [7, 3, 0, 7, 3, 0, 3, 7, 0], [7, 3, 6, 7, 3, 6, 3, 7, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation168_not_implies_Equation3462 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation3462 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[2, 3, 5, 5, 3, 5, 3, 2, 2], [1, 1, 0, 0, 1, 0, 4, 4, 4], [8, 8, 0, 0, 8, 0, 7, 7, 7], [1, 1, 6, 6, 1, 6, 4, 4, 4], [8, 8, 6, 6, 8, 6, 7, 7, 7], [2, 3, 5, 5, 3, 5, 3, 2, 2], [2, 3, 5, 5, 3, 5, 3, 2, 2], [8, 8, 6, 6, 8, 6, 7, 7, 7], [1, 1, 0, 0, 1, 0, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation168_not_implies_Equation3534 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation3534 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[4, 3, 4, 1, 1, 3, 3, 1, 4], [4, 3, 4, 7, 7, 3, 3, 7, 4], [5, 0, 8, 0, 0, 5, 8, 8, 5], [5, 6, 6, 1, 1, 5, 6, 1, 5], [2, 0, 8, 0, 0, 2, 8, 8, 2], [5, 0, 8, 0, 0, 5, 8, 8, 5], [2, 6, 6, 1, 1, 2, 6, 1, 2], [4, 3, 4, 7, 7, 3, 3, 7, 4], [2, 6, 6, 7, 7, 2, 6, 7, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation168_not_implies_Equation3461 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation3461 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[2, 3, 5, 5, 2, 5, 3, 3, 2], [1, 1, 0, 0, 6, 0, 1, 6, 6], [8, 8, 0, 0, 4, 0, 8, 4, 4], [1, 1, 7, 7, 6, 7, 1, 6, 6], [8, 8, 7, 7, 4, 7, 8, 4, 4], [2, 3, 5, 5, 2, 5, 3, 3, 2], [8, 8, 7, 7, 4, 7, 8, 4, 4], [2, 3, 5, 5, 2, 5, 3, 3, 2], [1, 1, 0, 0, 6, 0, 1, 6, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation168_not_implies_Equation3533 : ∃ (G: Type) (_: Magma G), Equation168 G ∧ ¬ Equation3533 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[2, 3, 3, 3, 2, 2, 5, 5, 5], [7, 8, 8, 8, 7, 7, 6, 6, 6], [4, 4, 0, 0, 4, 0, 5, 5, 5], [2, 3, 3, 3, 2, 2, 1, 1, 1], [4, 4, 0, 0, 4, 0, 1, 1, 1], [7, 8, 8, 8, 7, 7, 6, 6, 6], [7, 8, 8, 8, 7, 7, 6, 6, 6], [4, 4, 0, 0, 4, 0, 5, 5, 5], [2, 3, 3, 3, 2, 2, 1, 1, 1]][x.val]![y.val]!⟩, by decideFin!⟩

