import equational_theories.AllEquations
import equational_theories.MemoFinOp
import equational_theories.DecideBang

@[equational_result]
theorem Equation690_not_implies_Equation632 : ∃ (G: Type) (_: Magma G), Equation690 G ∧ ¬ Equation632 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 2, 5, 4, 0, 1], [3, 2, 5, 0, 4, 1], [0, 2, 5, 4, 3, 1], [3, 2, 5, 4, 0, 1], [3, 2, 5, 4, 0, 1], [4, 2, 5, 3, 0, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation690_not_implies_Equation642 : ∃ (G: Type) (_: Magma G), Equation690 G ∧ ¬ Equation642 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 2, 0, 4, 5, 1], [1, 2, 5, 4, 0, 3], [3, 4, 5, 2, 0, 1], [1, 2, 5, 4, 0, 3], [3, 4, 5, 2, 0, 1], [3, 2, 0, 4, 5, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation690_not_implies_Equation817 : ∃ (G: Type) (_: Magma G), Equation690 G ∧ ¬ Equation817 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 3, 4, 5, 0], [4, 2, 0, 1, 5, 3], [1, 5, 0, 4, 2, 3], [1, 2, 3, 4, 5, 0], [4, 2, 0, 1, 5, 3], [1, 5, 0, 4, 2, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation723_not_implies_Equation3897 : ∃ (G: Type) (_: Magma G), Equation723 G ∧ ¬ Equation3897 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 1, 2, 3, 4], [0, 1, 2, 4, 3], [3, 1, 2, 0, 4], [0, 1, 2, 3, 4], [1, 0, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation727_not_implies_Equation3862 : ∃ (G: Type) (_: Magma G), Equation727 G ∧ ¬ Equation3862 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[1, 2, 4, 8, 3, 0, 7, 5, 6], [7, 5, 0, 2, 1, 6, 3, 8, 4], [3, 8, 6, 5, 7, 4, 1, 2, 0], [7, 5, 0, 2, 1, 6, 3, 8, 4], [1, 2, 4, 8, 3, 0, 7, 5, 6], [3, 8, 6, 5, 7, 4, 1, 2, 0], [1, 2, 4, 8, 3, 0, 7, 5, 6], [7, 5, 0, 2, 1, 6, 3, 8, 4], [3, 8, 6, 5, 7, 4, 1, 2, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation727_not_implies_Equation4065 : ∃ (G: Type) (_: Magma G), Equation727 G ∧ ¬ Equation4065 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[1, 5, 4, 8, 0, 6, 7, 3, 2], [2, 4, 3, 6, 8, 0, 1, 5, 7], [2, 4, 3, 6, 8, 0, 1, 5, 7], [7, 3, 5, 0, 6, 8, 2, 4, 1], [7, 3, 5, 0, 6, 8, 2, 4, 1], [7, 3, 5, 0, 6, 8, 2, 4, 1], [1, 5, 4, 8, 0, 6, 7, 3, 2], [2, 4, 3, 6, 8, 0, 1, 5, 7], [1, 5, 4, 8, 0, 6, 7, 3, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation727_not_implies_Equation4320 : ∃ (G: Type) (_: Magma G), Equation727 G ∧ ¬ Equation4320 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 1, 3, 0, 4], [0, 1, 3, 4, 2], [2, 1, 3, 0, 4], [2, 1, 3, 0, 4], [2, 1, 3, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation727_not_implies_Equation47 : ∃ (G: Type) (_: Magma G), Equation727 G ∧ ¬ Equation47 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[1, 2, 3, 4, 7, 0, 8, 6, 5], [8, 5, 0, 1, 2, 6, 4, 3, 7], [4, 7, 6, 8, 5, 3, 1, 0, 2], [1, 2, 3, 4, 7, 0, 8, 6, 5], [8, 5, 0, 1, 2, 6, 4, 3, 7], [4, 7, 6, 8, 5, 3, 1, 0, 2], [1, 2, 3, 4, 7, 0, 8, 6, 5], [4, 7, 6, 8, 5, 3, 1, 0, 2], [8, 5, 0, 1, 2, 6, 4, 3, 7]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation731_not_implies_Equation3862 : ∃ (G: Type) (_: Magma G), Equation731 G ∧ ¬ Equation3862 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 5, 0, 3, 4], [4, 3, 0, 5, 2, 1], [3, 4, 1, 2, 5, 0], [4, 3, 0, 5, 2, 1], [5, 0, 3, 4, 1, 2], [4, 3, 0, 5, 2, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation731_not_implies_Equation4065 : ∃ (G: Type) (_: Magma G), Equation731 G ∧ ¬ Equation4065 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 5, 3, 0, 2, 4], [2, 3, 5, 4, 1, 0], [3, 2, 4, 5, 0, 1], [2, 3, 5, 4, 1, 0], [2, 3, 5, 4, 1, 0], [1, 5, 3, 0, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation826_not_implies_Equation614 : ∃ (G: Type) (_: Magma G), Equation826 G ∧ ¬ Equation614 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 2, 4, 3, 0], [0, 4, 1, 2, 3], [2, 0, 3, 1, 4], [4, 3, 2, 0, 1], [3, 1, 0, 4, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation827_not_implies_Equation616 : ∃ (G: Type) (_: Magma G), Equation827 G ∧ ¬ Equation616 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 2, 5, 4, 5, 0], [4, 1, 4, 4, 1, 1], [3, 5, 2, 2, 5, 2], [2, 2, 3, 3, 3, 3], [4, 2, 5, 5, 4, 4], [2, 2, 5, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation828_not_implies_Equation4065 : ∃ (G: Type) (_: Magma G), Equation828 G ∧ ¬ Equation4065 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 3, 3, 0, 2], [2, 3, 3, 4, 1], [2, 3, 3, 4, 2], [1, 3, 3, 4, 1], [2, 3, 3, 4, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation829_not_implies_Equation825 : ∃ (G: Type) (_: Magma G), Equation829 G ∧ ¬ Equation825 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 0, 2], [3, 1, 1, 1, 2], [2, 2, 2, 4, 2], [3, 2, 3, 3, 2], [4, 2, 4, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation831_not_implies_Equation1231 : ∃ (G: Type) (_: Magma G), Equation831 G ∧ ¬ Equation1231 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 0, 2], [1, 1, 1, 4, 1], [2, 3, 2, 2, 2], [4, 3, 3, 3, 3], [1, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation834_not_implies_Equation1020 : ∃ (G: Type) (_: Magma G), Equation834 G ∧ ¬ Equation1020 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[1, 2, 4, 4, 0, 0, 0, 2], [4, 6, 4, 1, 6, 1, 1, 1], [1, 3, 2, 2, 7, 2, 3, 3], [1, 3, 3, 3, 7, 3, 3, 3], [4, 5, 5, 2, 4, 4, 4, 2], [5, 5, 5, 5, 5, 0, 7, 3], [6, 6, 4, 6, 6, 0, 6, 6], [1, 7, 4, 7, 6, 4, 7, 7]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation834_not_implies_Equation107 : ∃ (G: Type) (_: Magma G), Equation834 G ∧ ¬ Equation107 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 3, 3, 0, 0], [2, 1, 1, 1, 2], [4, 2, 2, 4, 2], [3, 3, 1, 3, 1], [4, 0, 4, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation834_not_implies_Equation1225 : ∃ (G: Type) (_: Magma G), Equation834 G ∧ ¬ Equation1225 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 0, 0, 2, 2, 0], [1, 1, 5, 5, 1, 1], [2, 3, 2, 2, 3, 2], [4, 4, 3, 3, 3, 4], [1, 4, 1, 4, 4, 1], [5, 5, 5, 2, 2, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation834_not_implies_Equation1241 : ∃ (G: Type) (_: Magma G), Equation834 G ∧ ¬ Equation1241 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 0, 3, 0, 0, 2], [1, 0, 1, 1, 5, 0], [3, 2, 3, 4, 2, 2], [3, 3, 4, 4, 1, 3], [4, 5, 4, 1, 5, 4], [2, 0, 5, 5, 5, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation834_not_implies_Equation1251 : ∃ (G: Type) (_: Magma G), Equation834 G ∧ ¬ Equation1251 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 4, 4, 0, 0], [2, 1, 1, 2, 1], [3, 2, 2, 2, 3], [3, 0, 3, 3, 0], [4, 4, 1, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation834_not_implies_Equation1832 : ∃ (G: Type) (_: Magma G), Equation834 G ∧ ¬ Equation1832 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 0, 0, 1, 0], [2, 3, 3, 1, 1, 1], [2, 3, 3, 5, 2, 2], [3, 3, 5, 5, 3, 4], [1, 4, 4, 4, 0, 0], [5, 5, 5, 4, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation834_not_implies_Equation3253 : ∃ (G: Type) (_: Magma G), Equation834 G ∧ ¬ Equation3253 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 0, 1, 0, 0], [2, 4, 4, 1, 1, 1], [2, 4, 5, 2, 5, 2], [1, 3, 3, 0, 3, 0], [4, 4, 5, 4, 3, 3], [5, 5, 5, 0, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation834_not_implies_Equation3862 : ∃ (G: Type) (_: Magma G), Equation834 G ∧ ¬ Equation3862 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 0, 1, 0, 0], [2, 2, 4, 1, 1, 1], [2, 4, 5, 2, 5, 2], [1, 3, 3, 1, 3, 0], [4, 4, 5, 4, 3, 3], [5, 5, 5, 0, 3, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation834_not_implies_Equation4065 : ∃ (G: Type) (_: Magma G), Equation834 G ∧ ¬ Equation4065 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 0, 0, 0, 1], [2, 2, 4, 1, 1, 1], [2, 4, 4, 2, 3, 2], [3, 3, 3, 0, 5, 0], [4, 4, 3, 5, 5, 4], [1, 5, 5, 0, 5, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation834_not_implies_Equation411 : ∃ (G: Type) (_: Magma G), Equation834 G ∧ ¬ Equation411 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 0, 1, 0, 0], [2, 2, 5, 1, 1, 1], [2, 5, 4, 2, 2, 4], [1, 3, 3, 0, 0, 3], [4, 4, 4, 0, 3, 3], [5, 5, 4, 5, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation834_not_implies_Equation4316 : ∃ (G: Type) (_: Magma G), Equation834 G ∧ ¬ Equation4316 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 2, 0], [3, 1, 1, 1, 3], [2, 2, 2, 1, 1], [4, 3, 4, 3, 3], [4, 0, 0, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation837_not_implies_Equation1020 : ∃ (G: Type) (_: Magma G), Equation837 G ∧ ¬ Equation1020 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 2, 1, 1, 0], [4, 4, 4, 1, 1], [3, 3, 3, 3, 2], [4, 3, 4, 4, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation837_not_implies_Equation1223 : ∃ (G: Type) (_: Magma G), Equation837 G ∧ ¬ Equation1223 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[1, 1, 0, 4, 1, 0, 0], [2, 6, 1, 6, 2, 1, 1], [3, 2, 5, 5, 2, 5, 2], [3, 2, 5, 5, 2, 5, 3], [6, 6, 4, 6, 6, 4, 4], [5, 5, 6, 6, 5, 6, 5], [6, 6, 6, 6, 6, 6, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation838_not_implies_Equation4065 : ∃ (G: Type) (_: Magma G), Equation838 G ∧ ¬ Equation4065 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 2, 0, 1, 0], [2, 2, 4, 1, 1], [2, 2, 4, 2, 3], [1, 2, 3, 1, 3], [1, 4, 4, 1, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation854_not_implies_Equation3255 : ∃ (G: Type) (_: Magma G), Equation854 G ∧ ¬ Equation3255 G :=
  ⟨Fin 11, ⟨memoFinOp fun x y => [[2, 3, 0, 4, 0, 10, 0, 10, 0, 7, 7], [1, 5, 6, 1, 8, 1, 8, 8, 6, 1, 6], [2, 9, 6, 2, 2, 2, 2, 2, 9, 2, 6], [2, 3, 3, 2, 3, 9, 3, 9, 3, 7, 7], [4, 5, 4, 4, 8, 4, 5, 8, 4, 4, 4], [2, 5, 5, 2, 5, 9, 5, 2, 5, 5, 5], [6, 5, 6, 6, 8, 6, 5, 8, 6, 6, 6], [4, 3, 7, 4, 5, 4, 5, 8, 7, 7, 7], [8, 9, 6, 8, 8, 8, 8, 8, 9, 8, 6], [2, 9, 9, 2, 9, 9, 9, 9, 9, 4, 4], [2, 9, 9, 2, 10, 10, 10, 10, 9, 2, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation854_not_implies_Equation3867 : ∃ (G: Type) (_: Magma G), Equation854 G ∧ ¬ Equation3867 G :=
  ⟨Fin 11, ⟨memoFinOp fun x y => [[2, 3, 0, 2, 0, 10, 10, 5, 0, 0, 5], [1, 6, 8, 1, 9, 8, 1, 1, 9, 8, 9], [2, 6, 8, 2, 2, 8, 2, 2, 2, 6, 2], [4, 3, 3, 2, 0, 7, 7, 5, 3, 3, 5], [4, 3, 4, 1, 9, 10, 4, 1, 3, 4, 9], [2, 6, 6, 2, 5, 8, 2, 5, 5, 6, 5], [2, 6, 6, 2, 6, 8, 7, 6, 6, 6, 6], [4, 7, 7, 9, 0, 7, 7, 9, 7, 7, 2], [8, 6, 8, 8, 9, 8, 8, 8, 7, 8, 9], [9, 6, 8, 9, 9, 8, 9, 9, 9, 6, 9], [4, 7, 10, 1, 0, 10, 10, 1, 7, 10, 9]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation856_not_implies_Equation4131 : ∃ (G: Type) (_: Magma G), Equation856 G ∧ ¬ Equation4131 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[0, 2, 2, 3, 2, 2, 2], [0, 6, 1, 1, 6, 1, 5], [0, 3, 2, 2, 2, 2, 2], [0, 3, 3, 3, 3, 3, 3], [0, 6, 4, 4, 6, 4, 5], [0, 6, 5, 5, 6, 4, 5], [0, 6, 6, 6, 6, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation856_not_implies_Equation616 : ∃ (G: Type) (_: Magma G), Equation856 G ∧ ¬ Equation616 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 1, 0, 0, 3], [2, 1, 2, 2, 2], [2, 1, 2, 2, 2], [4, 1, 3, 0, 3], [4, 1, 4, 0, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation856_not_implies_Equation629 : ∃ (G: Type) (_: Magma G), Equation856 G ∧ ¬ Equation629 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 2, 3, 0, 2, 0], [5, 1, 1, 1, 1, 5], [2, 2, 3, 4, 2, 2], [2, 3, 3, 4, 2, 3], [2, 4, 3, 4, 2, 4], [5, 1, 5, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation856_not_implies_Equation632 : ∃ (G: Type) (_: Magma G), Equation856 G ∧ ¬ Equation632 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 1, 0, 4], [0, 1, 1, 4, 4], [3, 2, 2, 3, 3], [3, 2, 2, 3, 3], [0, 1, 1, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation856_not_implies_Equation639 : ∃ (G: Type) (_: Magma G), Equation856 G ∧ ¬ Equation639 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[0, 4, 4, 0, 4, 0, 0], [2, 2, 3, 1, 1, 3, 2], [3, 2, 3, 6, 2, 3, 2], [3, 2, 3, 6, 3, 3, 5], [0, 4, 4, 4, 4, 4, 4], [5, 5, 3, 6, 5, 3, 5], [6, 5, 3, 6, 6, 3, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation856_not_implies_Equation642 : ∃ (G: Type) (_: Magma G), Equation856 G ∧ ¬ Equation642 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 4, 0, 5, 0, 0], [1, 2, 3, 1, 3, 0], [3, 2, 3, 5, 3, 2], [3, 4, 3, 5, 3, 0], [1, 4, 3, 5, 3, 4], [1, 5, 3, 5, 3, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation856_not_implies_Equation832 : ∃ (G: Type) (_: Magma G), Equation856 G ∧ ¬ Equation832 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 2, 2, 0, 0, 0], [1, 4, 1, 4, 5, 1], [0, 0, 2, 2, 2, 2], [3, 4, 3, 4, 5, 3], [4, 4, 4, 4, 5, 3], [5, 4, 5, 4, 5, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation856_not_implies_Equation842 : ∃ (G: Type) (_: Magma G), Equation856 G ∧ ¬ Equation842 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 2, 5, 2, 0, 0], [4, 1, 1, 1, 4, 1], [2, 2, 5, 2, 2, 3], [2, 3, 5, 2, 3, 3], [4, 1, 4, 4, 4, 4], [2, 5, 5, 2, 5, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation860_not_implies_Equation4065 : ∃ (G: Type) (_: Magma G), Equation860 G ∧ ¬ Equation4065 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 3, 4, 0, 5, 2], [2, 3, 4, 5, 0, 1], [2, 3, 4, 5, 0, 1], [1, 4, 3, 5, 0, 2], [1, 4, 3, 5, 0, 2], [1, 3, 4, 0, 5, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation860_not_implies_Equation47 : ∃ (G: Type) (_: Magma G), Equation860 G ∧ ¬ Equation47 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 3, 4, 5, 0], [4, 5, 3, 1, 2, 0], [4, 2, 0, 1, 5, 3], [1, 2, 3, 4, 5, 0], [4, 5, 3, 1, 2, 0], [4, 2, 0, 1, 5, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation860_not_implies_Equation614 : ∃ (G: Type) (_: Magma G), Equation860 G ∧ ¬ Equation614 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 5, 3, 4, 2, 0], [2, 5, 3, 0, 1, 4], [2, 5, 3, 0, 1, 4], [1, 3, 5, 0, 2, 4], [1, 5, 3, 4, 2, 0], [1, 3, 5, 0, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation880_not_implies_Equation3050 : ∃ (G: Type) (_: Magma G), Equation880 G ∧ ¬ Equation3050 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[1, 5, 6, 3, 0, 2, 4], [2, 4, 3, 1, 6, 5, 0], [3, 2, 0, 6, 4, 1, 5], [4, 6, 2, 5, 1, 0, 3], [5, 0, 1, 2, 3, 4, 6], [0, 3, 5, 4, 2, 6, 1], [6, 1, 4, 0, 5, 3, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation880_not_implies_Equation614 : ∃ (G: Type) (_: Magma G), Equation880 G ∧ ¬ Equation614 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[1, 5, 3, 4, 0, 2, 6], [2, 4, 6, 0, 3, 5, 1], [6, 2, 0, 5, 4, 1, 3], [3, 1, 4, 2, 5, 6, 0], [5, 0, 1, 3, 6, 4, 2], [0, 6, 5, 1, 2, 3, 4], [4, 3, 2, 6, 1, 0, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation906_not_implies_Equation3915 : ∃ (G: Type) (_: Magma G), Equation906 G ∧ ¬ Equation3915 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 1, 3, 0, 4], [2, 1, 3, 0, 4], [2, 4, 3, 0, 1], [2, 4, 3, 0, 1], [2, 4, 3, 0, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation910_not_implies_Equation1861 : ∃ (G: Type) (_: Magma G), Equation910 G ∧ ¬ Equation1861 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[5, 6, 3, 2, 4, 0, 1], [3, 2, 6, 4, 0, 1, 5], [6, 1, 5, 3, 4, 2, 0], [0, 1, 4, 5, 2, 3, 6], [2, 3, 0, 1, 5, 4, 6], [0, 1, 2, 3, 6, 5, 4], [3, 5, 1, 4, 0, 6, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation910_not_implies_Equation513 : ∃ (G: Type) (_: Magma G), Equation910 G ∧ ¬ Equation513 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[0, 2, 5, 6, 3, 1, 4], [2, 1, 3, 0, 6, 4, 5], [5, 3, 2, 4, 1, 6, 0], [6, 0, 4, 3, 5, 2, 1], [3, 6, 1, 5, 4, 0, 2], [1, 4, 6, 2, 0, 5, 3], [4, 5, 0, 1, 2, 3, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation916_not_implies_Equation3887 : ∃ (G: Type) (_: Magma G), Equation916 G ∧ ¬ Equation3887 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[2, 6, 5, 4, 1, 0, 3], [2, 6, 3, 5, 1, 0, 4], [2, 3, 5, 6, 1, 0, 4], [4, 0, 1, 3, 5, 6, 2], [2, 6, 5, 0, 1, 3, 4], [2, 6, 5, 1, 3, 0, 4], [3, 6, 5, 2, 1, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation947_not_implies_Equation1518 : ∃ (G: Type) (_: Magma G), Equation947 G ∧ ¬ Equation1518 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 1, 4], [0, 2, 3, 1, 4], [4, 2, 3, 1, 0], [0, 2, 3, 1, 4], [0, 2, 3, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation947_not_implies_Equation1525 : ∃ (G: Type) (_: Magma G), Equation947 G ∧ ¬ Equation1525 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 1, 4], [0, 2, 3, 1, 4], [4, 2, 3, 1, 0], [0, 2, 3, 1, 4], [0, 2, 3, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation947_not_implies_Equation3915 : ∃ (G: Type) (_: Magma G), Equation947 G ∧ ¬ Equation3915 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 1, 4, 0], [3, 1, 2, 4, 0], [3, 1, 2, 4, 0], [3, 1, 2, 4, 0], [3, 1, 2, 4, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation947_not_implies_Equation3962 : ∃ (G: Type) (_: Magma G), Equation947 G ∧ ¬ Equation3962 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 1, 4, 0], [3, 1, 2, 4, 0], [3, 1, 2, 4, 0], [3, 1, 2, 4, 0], [3, 1, 2, 4, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation947_not_implies_Equation4118 : ∃ (G: Type) (_: Magma G), Equation947 G ∧ ¬ Equation4118 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 1, 4, 3, 0], [2, 1, 4, 3, 0], [2, 3, 4, 1, 0], [2, 1, 4, 3, 0], [2, 1, 4, 3, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation947_not_implies_Equation4155 : ∃ (G: Type) (_: Magma G), Equation947 G ∧ ¬ Equation4155 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 1, 4, 0], [3, 1, 2, 4, 0], [3, 1, 2, 4, 0], [3, 1, 2, 4, 0], [3, 1, 2, 4, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation947_not_implies_Equation4362 : ∃ (G: Type) (_: Magma G), Equation947 G ∧ ¬ Equation4362 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 1, 2, 4, 3], [0, 1, 3, 2, 4], [1, 0, 2, 3, 4], [1, 0, 2, 3, 4], [1, 0, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation947_not_implies_Equation642 : ∃ (G: Type) (_: Magma G), Equation947 G ∧ ¬ Equation642 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 4, 3, 1], [0, 2, 4, 3, 1], [3, 2, 4, 0, 1], [0, 2, 4, 3, 1], [0, 2, 4, 3, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation947_not_implies_Equation679 : ∃ (G: Type) (_: Magma G), Equation947 G ∧ ¬ Equation679 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 1, 4], [4, 2, 3, 1, 0], [0, 2, 3, 1, 4], [4, 2, 3, 1, 0], [0, 2, 3, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation947_not_implies_Equation845 : ∃ (G: Type) (_: Magma G), Equation947 G ∧ ¬ Equation845 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 4, 3, 1], [3, 2, 4, 0, 1], [0, 2, 4, 3, 1], [0, 2, 4, 3, 1], [0, 2, 4, 3, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation960_not_implies_Equation1434 : ∃ (G: Type) (_: Magma G), Equation960 G ∧ ¬ Equation1434 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 3, 4, 5, 0, 1], [2, 3, 0, 5, 4, 1], [2, 3, 4, 5, 0, 1], [4, 3, 2, 5, 0, 1], [2, 3, 4, 5, 0, 1], [0, 3, 4, 5, 2, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation960_not_implies_Equation1451 : ∃ (G: Type) (_: Magma G), Equation960 G ∧ ¬ Equation1451 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 2, 5, 4, 0, 1], [3, 2, 5, 0, 4, 1], [4, 2, 5, 3, 0, 1], [3, 2, 5, 4, 0, 1], [3, 2, 5, 4, 0, 1], [0, 2, 5, 4, 3, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation960_not_implies_Equation1491 : ∃ (G: Type) (_: Magma G), Equation960 G ∧ ¬ Equation1491 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 5, 0, 2, 1, 4], [2, 5, 0, 3, 1, 4], [3, 5, 0, 2, 1, 4], [3, 5, 0, 2, 1, 4], [3, 5, 2, 0, 1, 4], [0, 5, 3, 2, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation960_not_implies_Equation1525 : ∃ (G: Type) (_: Magma G), Equation960 G ∧ ¬ Equation1525 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 2, 5, 4, 0, 1], [4, 2, 5, 3, 0, 1], [0, 2, 5, 4, 3, 1], [3, 2, 5, 4, 0, 1], [3, 2, 5, 4, 0, 1], [3, 2, 5, 0, 4, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation960_not_implies_Equation3915 : ∃ (G: Type) (_: Magma G), Equation960 G ∧ ¬ Equation3915 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 2, 1, 4, 0, 5], [3, 2, 5, 4, 0, 1], [3, 2, 5, 4, 0, 1], [3, 5, 2, 4, 0, 1], [3, 1, 5, 4, 0, 2], [3, 2, 5, 4, 0, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation960_not_implies_Equation3925 : ∃ (G: Type) (_: Magma G), Equation960 G ∧ ¬ Equation3925 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 2, 1, 4, 0, 5], [3, 5, 1, 4, 0, 2], [3, 5, 1, 4, 0, 2], [3, 1, 5, 4, 0, 2], [3, 5, 2, 4, 0, 1], [3, 5, 1, 4, 0, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation960_not_implies_Equation3952 : ∃ (G: Type) (_: Magma G), Equation960 G ∧ ¬ Equation3952 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 2, 1, 4, 0, 5], [3, 5, 1, 4, 0, 2], [3, 5, 1, 4, 0, 2], [3, 1, 5, 4, 0, 2], [3, 5, 2, 4, 0, 1], [3, 5, 1, 4, 0, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation960_not_implies_Equation3962 : ∃ (G: Type) (_: Magma G), Equation960 G ∧ ¬ Equation3962 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 2, 1, 4, 0, 5], [3, 2, 5, 4, 0, 1], [3, 2, 5, 4, 0, 1], [3, 5, 2, 4, 0, 1], [3, 1, 5, 4, 0, 2], [3, 2, 5, 4, 0, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation960_not_implies_Equation4118 : ∃ (G: Type) (_: Magma G), Equation960 G ∧ ¬ Equation4118 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 1, 5, 4, 3, 0], [2, 3, 5, 4, 1, 0], [2, 3, 5, 1, 4, 0], [2, 3, 5, 4, 1, 0], [2, 3, 5, 4, 1, 0], [2, 4, 5, 3, 1, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation960_not_implies_Equation4128 : ∃ (G: Type) (_: Magma G), Equation960 G ∧ ¬ Equation4128 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 1, 4, 5, 0, 3], [2, 3, 4, 5, 0, 1], [2, 3, 4, 1, 0, 5], [2, 3, 4, 5, 0, 1], [2, 5, 4, 3, 0, 1], [2, 3, 4, 5, 0, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation960_not_implies_Equation4155 : ∃ (G: Type) (_: Magma G), Equation960 G ∧ ¬ Equation4155 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 2, 1, 5, 4, 0], [3, 4, 1, 5, 2, 0], [3, 4, 1, 5, 2, 0], [3, 1, 4, 5, 2, 0], [3, 4, 1, 5, 2, 0], [3, 4, 2, 5, 1, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation960_not_implies_Equation4165 : ∃ (G: Type) (_: Magma G), Equation960 G ∧ ¬ Equation4165 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[4, 2, 1, 3, 5, 0], [4, 3, 1, 2, 5, 0], [4, 3, 1, 2, 5, 0], [4, 3, 1, 2, 5, 0], [4, 1, 3, 2, 5, 0], [4, 3, 2, 1, 5, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation960_not_implies_Equation4307 : ∃ (G: Type) (_: Magma G), Equation960 G ∧ ¬ Equation4307 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[4, 2, 1, 0, 3, 5], [4, 2, 5, 0, 3, 1], [4, 2, 5, 0, 3, 1], [4, 1, 5, 0, 3, 2], [4, 5, 2, 0, 3, 1], [4, 2, 5, 0, 3, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation960_not_implies_Equation4320 : ∃ (G: Type) (_: Magma G), Equation960 G ∧ ¬ Equation4320 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 4, 0, 2, 5, 1], [2, 4, 0, 3, 5, 1], [3, 4, 0, 2, 5, 1], [3, 4, 0, 2, 5, 1], [0, 4, 3, 2, 5, 1], [3, 4, 2, 0, 5, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation960_not_implies_Equation55 : ∃ (G: Type) (_: Magma G), Equation960 G ∧ ¬ Equation55 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 3, 4, 5, 0, 1], [2, 3, 0, 5, 4, 1], [2, 3, 4, 5, 0, 1], [4, 3, 2, 5, 0, 1], [2, 3, 4, 5, 0, 1], [0, 3, 4, 5, 2, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation960_not_implies_Equation65 : ∃ (G: Type) (_: Magma G), Equation960 G ∧ ¬ Equation65 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[4, 5, 0, 1, 2, 3], [2, 5, 0, 1, 4, 3], [4, 5, 0, 1, 2, 3], [4, 5, 2, 1, 0, 3], [4, 5, 0, 1, 2, 3], [0, 5, 4, 1, 2, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation960_not_implies_Equation669 : ∃ (G: Type) (_: Magma G), Equation960 G ∧ ¬ Equation669 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[4, 2, 5, 0, 3, 1], [4, 2, 5, 3, 0, 1], [3, 2, 5, 0, 4, 1], [4, 2, 5, 0, 3, 1], [4, 2, 5, 0, 3, 1], [0, 2, 5, 4, 3, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation960_not_implies_Equation679 : ∃ (G: Type) (_: Magma G), Equation960 G ∧ ¬ Equation679 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 2, 5, 4, 0, 1], [0, 2, 5, 4, 3, 1], [3, 2, 5, 0, 4, 1], [3, 2, 5, 4, 0, 1], [3, 2, 5, 4, 0, 1], [4, 2, 5, 3, 0, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation960_not_implies_Equation713 : ∃ (G: Type) (_: Magma G), Equation960 G ∧ ¬ Equation713 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 4, 3, 0, 5, 1], [2, 4, 0, 3, 5, 1], [2, 4, 3, 0, 5, 1], [2, 4, 3, 0, 5, 1], [3, 4, 2, 0, 5, 1], [0, 4, 3, 2, 5, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation960_not_implies_Equation825 : ∃ (G: Type) (_: Magma G), Equation960 G ∧ ¬ Equation825 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[4, 2, 5, 0, 3, 1], [3, 2, 5, 0, 4, 1], [0, 2, 5, 4, 3, 1], [4, 2, 5, 0, 3, 1], [4, 2, 5, 0, 3, 1], [4, 2, 5, 3, 0, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation960_not_implies_Equation845 : ∃ (G: Type) (_: Magma G), Equation960 G ∧ ¬ Equation845 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[4, 2, 5, 0, 3, 1], [3, 2, 5, 0, 4, 1], [0, 2, 5, 4, 3, 1], [4, 2, 5, 0, 3, 1], [4, 2, 5, 0, 3, 1], [4, 2, 5, 3, 0, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation960_not_implies_Equation872 : ∃ (G: Type) (_: Magma G), Equation960 G ∧ ¬ Equation872 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 4, 3, 0, 5, 1], [2, 4, 0, 3, 5, 1], [2, 4, 3, 0, 5, 1], [2, 4, 3, 0, 5, 1], [3, 4, 2, 0, 5, 1], [0, 4, 3, 2, 5, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation978_not_implies_Equation1848 : ∃ (G: Type) (_: Magma G), Equation978 G ∧ ¬ Equation1848 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[5, 3, 1, 2, 7, 0, 6, 4], [2, 5, 4, 3, 0, 1, 7, 6], [4, 7, 5, 1, 6, 2, 0, 3], [6, 4, 0, 5, 1, 3, 2, 7], [0, 2, 7, 6, 5, 4, 3, 1], [7, 6, 2, 4, 3, 5, 1, 0], [1, 0, 3, 7, 4, 6, 5, 2], [3, 1, 6, 0, 2, 7, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation978_not_implies_Equation466 : ∃ (G: Type) (_: Magma G), Equation978 G ∧ ¬ Equation466 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[6, 5, 3, 2, 4, 7, 0, 1], [2, 6, 4, 7, 0, 3, 1, 5], [0, 3, 6, 5, 7, 1, 2, 4], [7, 4, 1, 6, 2, 5, 3, 0], [5, 7, 2, 1, 6, 0, 4, 3], [1, 2, 0, 4, 3, 6, 5, 7], [3, 1, 7, 0, 5, 4, 6, 2], [4, 0, 5, 3, 1, 2, 7, 6]][x.val]![y.val]!⟩, by decideFin!⟩

