import equational_theories.AllEquations
import equational_theories.MemoFinOp
import equational_theories.DecideBang

@[equational_result]
theorem Equation1027_not_implies_Equation1028 : ∃ (G: Type) (_: Magma G), Equation1027 G ∧ ¬ Equation1028 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 4, 0], [3, 1, 1, 1, 1], [3, 2, 2, 2, 3], [3, 2, 3, 3, 3], [4, 4, 0, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1027_not_implies_Equation1225 : ∃ (G: Type) (_: Magma G), Equation1027 G ∧ ¬ Equation1225 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 4, 0], [4, 1, 3, 1, 1], [3, 2, 2, 2, 2], [3, 3, 3, 3, 3], [2, 2, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1027_not_implies_Equation1631 : ∃ (G: Type) (_: Magma G), Equation1027 G ∧ ¬ Equation1631 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 4, 0], [4, 1, 3, 1, 1], [3, 3, 2, 2, 2], [4, 3, 3, 3, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1027_not_implies_Equation2446 : ∃ (G: Type) (_: Magma G), Equation1027 G ∧ ¬ Equation2446 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 4, 0], [4, 1, 1, 4, 1], [3, 4, 2, 2, 2], [2, 2, 3, 3, 3], [2, 2, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1027_not_implies_Equation3458 : ∃ (G: Type) (_: Magma G), Equation1027 G ∧ ¬ Equation3458 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 4, 0], [3, 1, 1, 1, 1], [3, 2, 2, 2, 3], [2, 3, 3, 3, 2], [2, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1027_not_implies_Equation822 : ∃ (G: Type) (_: Magma G), Equation1027 G ∧ ¬ Equation822 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 4, 0], [2, 1, 1, 1, 1], [3, 3, 2, 2, 3], [3, 3, 3, 3, 3], [4, 4, 4, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1030_not_implies_Equation1232 : ∃ (G: Type) (_: Magma G), Equation1030 G ∧ ¬ Equation1232 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 0, 2], [3, 1, 3, 1, 1], [2, 3, 2, 2, 2], [4, 4, 4, 3, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1032_not_implies_Equation616 : ∃ (G: Type) (_: Magma G), Equation1032 G ∧ ¬ Equation616 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 2, 0, 4, 5, 0], [1, 1, 0, 0, 1, 0], [3, 2, 2, 2, 2, 4], [3, 3, 1, 3, 3, 4], [4, 4, 0, 0, 4, 1], [2, 2, 5, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1033_not_implies_Equation1026 : ∃ (G: Type) (_: Magma G), Equation1033 G ∧ ¬ Equation1026 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 0, 3, 0, 1], [2, 1, 1, 1, 1], [3, 4, 2, 2, 2], [3, 4, 3, 3, 3], [3, 4, 3, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1033_not_implies_Equation1028 : ∃ (G: Type) (_: Magma G), Equation1033 G ∧ ¬ Equation1028 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 4, 0], [4, 1, 4, 1, 1], [3, 2, 2, 2, 2], [4, 4, 4, 3, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1033_not_implies_Equation1225 : ∃ (G: Type) (_: Magma G), Equation1033 G ∧ ¬ Equation1225 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 4, 0], [3, 1, 1, 1, 3], [3, 2, 2, 2, 3], [2, 3, 3, 3, 2], [2, 2, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1033_not_implies_Equation1631 : ∃ (G: Type) (_: Magma G), Equation1033 G ∧ ¬ Equation1631 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 4, 0], [4, 1, 1, 4, 1], [3, 2, 2, 2, 2], [4, 3, 1, 3, 3], [4, 4, 1, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1033_not_implies_Equation2446 : ∃ (G: Type) (_: Magma G), Equation1033 G ∧ ¬ Equation2446 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 4, 0], [3, 1, 3, 1, 1], [3, 2, 2, 2, 2], [4, 3, 1, 3, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1033_not_implies_Equation3458 : ∃ (G: Type) (_: Magma G), Equation1033 G ∧ ¬ Equation3458 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 4, 0], [4, 1, 1, 1, 1], [3, 4, 2, 2, 2], [4, 4, 3, 3, 3], [2, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1033_not_implies_Equation822 : ∃ (G: Type) (_: Magma G), Equation1033 G ∧ ¬ Equation822 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 4, 0], [4, 1, 4, 1, 1], [3, 4, 2, 2, 2], [4, 4, 4, 3, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1034_not_implies_Equation1229 : ∃ (G: Type) (_: Magma G), Equation1034 G ∧ ¬ Equation1229 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 0, 2], [1, 1, 4, 1, 1], [3, 3, 2, 2, 2], [4, 4, 4, 3, 3], [3, 4, 3, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1037_not_implies_Equation3931 : ∃ (G: Type) (_: Magma G), Equation1037 G ∧ ¬ Equation3931 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 3, 3, 0, 5, 0], [5, 1, 4, 1, 1, 1], [5, 4, 2, 2, 2, 2], [3, 3, 3, 3, 3, 3], [5, 4, 4, 4, 4, 4], [5, 5, 5, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1037_not_implies_Equation4673 : ∃ (G: Type) (_: Magma G), Equation1037 G ∧ ¬ Equation4673 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 3, 4, 0, 0], [3, 1, 1, 1, 1], [3, 2, 2, 2, 2], [3, 3, 3, 3, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1043_not_implies_Equation1046 : ∃ (G: Type) (_: Magma G), Equation1043 G ∧ ¬ Equation1046 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 0, 1, 0], [2, 4, 0, 1, 1], [2, 3, 4, 1, 2], [2, 3, 0, 4, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1043_not_implies_Equation105 : ∃ (G: Type) (_: Magma G), Equation1043 G ∧ ¬ Equation105 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 0, 1, 0], [2, 4, 0, 1, 1], [2, 3, 4, 1, 2], [2, 3, 0, 4, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1043_not_implies_Equation1229 : ∃ (G: Type) (_: Magma G), Equation1043 G ∧ ¬ Equation1229 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 1, 0, 0], [3, 4, 1, 0, 1], [3, 2, 4, 0, 2], [3, 2, 1, 4, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1043_not_implies_Equation1239 : ∃ (G: Type) (_: Magma G), Equation1043 G ∧ ¬ Equation1239 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 0, 1, 0], [2, 4, 0, 1, 1], [2, 3, 4, 1, 2], [2, 3, 0, 4, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1043_not_implies_Equation1242 : ∃ (G: Type) (_: Magma G), Equation1043 G ∧ ¬ Equation1242 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 0, 1, 0], [2, 4, 0, 1, 1], [2, 3, 4, 1, 2], [2, 3, 0, 4, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1043_not_implies_Equation3318 : ∃ (G: Type) (_: Magma G), Equation1043 G ∧ ¬ Equation3318 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 1, 0, 0], [3, 4, 1, 0, 1], [3, 2, 4, 0, 2], [3, 2, 1, 4, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1043_not_implies_Equation3724 : ∃ (G: Type) (_: Magma G), Equation1043 G ∧ ¬ Equation3724 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 1, 0, 0], [3, 4, 1, 0, 1], [3, 2, 4, 0, 2], [3, 2, 1, 4, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1043_not_implies_Equation3864 : ∃ (G: Type) (_: Magma G), Equation1043 G ∧ ¬ Equation3864 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 3, 0, 1, 0], [4, 2, 1, 1, 0], [2, 2, 2, 2, 2], [4, 3, 3, 2, 0], [4, 3, 4, 1, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1043_not_implies_Equation833 : ∃ (G: Type) (_: Magma G), Equation1043 G ∧ ¬ Equation833 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 0, 1, 0], [2, 4, 0, 1, 1], [2, 3, 4, 1, 2], [2, 3, 0, 4, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1061_not_implies_Equation1832 : ∃ (G: Type) (_: Magma G), Equation1061 G ∧ ¬ Equation1832 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 2, 3, 0, 4], [4, 0, 2, 1, 3], [3, 1, 4, 2, 0], [2, 4, 0, 3, 1], [0, 3, 1, 4, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1061_not_implies_Equation817 : ∃ (G: Type) (_: Magma G), Equation1061 G ∧ ¬ Equation817 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 2, 3, 0, 4], [4, 0, 2, 1, 3], [3, 1, 4, 2, 0], [2, 4, 0, 3, 1], [0, 3, 1, 4, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1101_not_implies_Equation1684 : ∃ (G: Type) (_: Magma G), Equation1101 G ∧ ¬ Equation1684 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[5, 3, 4, 6, 0, 7, 2, 1], [2, 5, 6, 7, 3, 4, 1, 0], [6, 0, 5, 1, 7, 2, 4, 3], [3, 2, 0, 5, 1, 6, 7, 4], [7, 6, 3, 4, 5, 1, 0, 2], [0, 1, 2, 3, 4, 5, 6, 7], [1, 4, 7, 0, 2, 3, 5, 6], [4, 7, 1, 2, 6, 0, 3, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1101_not_implies_Equation3066 : ∃ (G: Type) (_: Magma G), Equation1101 G ∧ ¬ Equation3066 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[4, 2, 6, 0, 7, 1, 3, 5], [5, 4, 7, 6, 1, 2, 0, 3], [2, 3, 4, 5, 6, 0, 7, 1], [7, 0, 3, 4, 5, 6, 1, 2], [0, 1, 2, 3, 4, 5, 6, 7], [6, 7, 1, 2, 3, 4, 5, 0], [1, 5, 0, 7, 2, 3, 4, 6], [3, 6, 5, 1, 0, 7, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1119_not_implies_Equation4118 : ∃ (G: Type) (_: Magma G), Equation1119 G ∧ ¬ Equation4118 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[2, 1, 0, 4, 5, 6, 3], [2, 1, 0, 4, 5, 6, 3], [2, 3, 0, 6, 1, 5, 4], [2, 5, 0, 3, 6, 4, 1], [2, 6, 0, 1, 4, 3, 5], [2, 3, 0, 6, 1, 5, 4], [2, 4, 0, 5, 3, 1, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1233_not_implies_Equation1025 : ∃ (G: Type) (_: Magma G), Equation1233 G ∧ ¬ Equation1025 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 4, 0], [1, 1, 1, 1, 1], [3, 4, 2, 2, 2], [4, 3, 4, 3, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1233_not_implies_Equation1026 : ∃ (G: Type) (_: Magma G), Equation1233 G ∧ ¬ Equation1026 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 0, 3, 0, 5, 0], [2, 1, 1, 1, 1, 1], [3, 4, 2, 2, 2, 2], [4, 4, 5, 3, 3, 3], [4, 4, 4, 4, 4, 4], [3, 3, 3, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1233_not_implies_Equation1028 : ∃ (G: Type) (_: Magma G), Equation1233 G ∧ ¬ Equation1028 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 4, 0], [3, 1, 1, 1, 1], [3, 4, 2, 2, 2], [3, 3, 3, 3, 3], [2, 2, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1233_not_implies_Equation1225 : ∃ (G: Type) (_: Magma G), Equation1233 G ∧ ¬ Equation1225 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 4, 0], [2, 1, 1, 1, 3], [3, 4, 2, 2, 2], [3, 3, 3, 3, 3], [4, 2, 4, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1233_not_implies_Equation1229 : ∃ (G: Type) (_: Magma G), Equation1233 G ∧ ¬ Equation1229 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 0, 2], [1, 1, 3, 1, 1], [3, 2, 2, 2, 2], [3, 4, 4, 3, 3], [4, 3, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1233_not_implies_Equation1631 : ∃ (G: Type) (_: Magma G), Equation1233 G ∧ ¬ Equation1631 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 4, 0], [4, 1, 1, 1, 1], [3, 4, 2, 2, 2], [4, 3, 3, 3, 3], [2, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1233_not_implies_Equation2446 : ∃ (G: Type) (_: Magma G), Equation1233 G ∧ ¬ Equation2446 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 4, 0], [4, 1, 4, 1, 1], [3, 4, 2, 2, 2], [2, 3, 3, 3, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1233_not_implies_Equation3458 : ∃ (G: Type) (_: Magma G), Equation1233 G ∧ ¬ Equation3458 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 4, 0], [4, 1, 4, 4, 1], [3, 4, 2, 2, 2], [3, 3, 3, 3, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1233_not_implies_Equation822 : ∃ (G: Type) (_: Magma G), Equation1233 G ∧ ¬ Equation822 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 4, 0], [2, 1, 1, 1, 3], [3, 4, 2, 2, 2], [2, 3, 3, 3, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1233_not_implies_Equation825 : ∃ (G: Type) (_: Magma G), Equation1233 G ∧ ¬ Equation825 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 0, 3], [3, 1, 3, 1, 3], [2, 0, 2, 4, 2], [3, 3, 3, 3, 3], [4, 0, 4, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1235_not_implies_Equation1026 : ∃ (G: Type) (_: Magma G), Equation1235 G ∧ ¬ Equation1026 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 5, 3, 0, 5, 0], [2, 1, 1, 1, 1, 2], [3, 4, 2, 2, 2, 3], [3, 4, 3, 3, 3, 3], [4, 3, 3, 4, 4, 3], [5, 0, 0, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1235_not_implies_Equation1227 : ∃ (G: Type) (_: Magma G), Equation1235 G ∧ ¬ Equation1227 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 3, 5, 0, 5, 0], [1, 1, 3, 1, 1, 3], [2, 5, 2, 2, 2, 2], [3, 3, 4, 3, 3, 3], [4, 5, 4, 4, 4, 4], [5, 0, 0, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1235_not_implies_Equation1231 : ∃ (G: Type) (_: Magma G), Equation1235 G ∧ ¬ Equation1231 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 0, 2], [1, 1, 1, 0, 0], [3, 3, 2, 2, 2], [4, 2, 3, 3, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1235_not_implies_Equation1633 : ∃ (G: Type) (_: Magma G), Equation1235 G ∧ ¬ Equation1633 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 3, 5, 0, 5, 0], [1, 1, 5, 5, 5, 1], [4, 4, 2, 2, 2, 4], [3, 3, 4, 3, 3, 3], [4, 3, 3, 4, 4, 3], [5, 5, 0, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1235_not_implies_Equation2452 : ∃ (G: Type) (_: Magma G), Equation1235 G ∧ ¬ Equation2452 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 3, 5, 0, 5, 0], [1, 1, 1, 1, 2, 2], [1, 2, 2, 2, 2, 1], [3, 5, 4, 3, 3, 3], [4, 3, 0, 4, 4, 4], [5, 0, 0, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1235_not_implies_Equation3460 : ∃ (G: Type) (_: Magma G), Equation1235 G ∧ ¬ Equation3460 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 3, 5, 0, 5, 0], [4, 1, 4, 1, 1, 4], [2, 5, 2, 5, 5, 2], [3, 5, 4, 3, 3, 3], [4, 3, 3, 4, 4, 4], [5, 5, 5, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1235_not_implies_Equation825 : ∃ (G: Type) (_: Magma G), Equation1235 G ∧ ¬ Equation825 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 2, 0, 5, 5, 0], [3, 1, 1, 1, 1, 4], [2, 5, 2, 4, 2, 2], [4, 3, 3, 3, 3, 4], [2, 2, 4, 4, 4, 4], [5, 5, 5, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1236_not_implies_Equation825 : ∃ (G: Type) (_: Magma G), Equation1236 G ∧ ¬ Equation825 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 0, 2], [3, 1, 3, 1, 1], [2, 0, 2, 4, 2], [4, 4, 4, 3, 3], [4, 4, 4, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation124_not_implies_Equation1109 : ∃ (G: Type) (_: Magma G), Equation124 G ∧ ¬ Equation1109 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[2, 1, 0, 5, 3, 4, 6], [4, 1, 3, 6, 5, 0, 2], [2, 6, 0, 1, 4, 5, 3], [4, 2, 6, 3, 5, 0, 1], [5, 2, 6, 0, 4, 3, 1], [3, 2, 6, 4, 0, 5, 1], [4, 3, 1, 2, 5, 0, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation124_not_implies_Equation1322 : ∃ (G: Type) (_: Magma G), Equation124 G ∧ ¬ Equation1322 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 2, 1, 5, 3, 4], [4, 2, 1, 3, 5, 0], [3, 2, 1, 4, 0, 5], [4, 2, 1, 3, 5, 0], [5, 2, 1, 0, 4, 3], [3, 2, 1, 4, 0, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation124_not_implies_Equation1728 : ∃ (G: Type) (_: Magma G), Equation124 G ∧ ¬ Equation1728 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 2, 1, 5, 3, 4], [3, 2, 1, 4, 0, 5], [4, 2, 1, 3, 5, 0], [4, 2, 1, 3, 5, 0], [5, 2, 1, 0, 4, 3], [3, 2, 1, 4, 0, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation124_not_implies_Equation4118 : ∃ (G: Type) (_: Magma G), Equation124 G ∧ ¬ Equation4118 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 2, 4, 0, 1, 5], [3, 1, 5, 0, 2, 4], [3, 4, 2, 0, 5, 1], [3, 1, 5, 0, 2, 4], [3, 5, 1, 0, 4, 2], [3, 2, 4, 0, 1, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1259_not_implies_Equation1242 : ∃ (G: Type) (_: Magma G), Equation1259 G ∧ ¬ Equation1242 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 0, 3, 2], [0, 4, 1, 1, 0], [2, 3, 2, 2, 2], [2, 2, 3, 3, 3], [4, 2, 4, 4, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1312_not_implies_Equation1122 : ∃ (G: Type) (_: Magma G), Equation1312 G ∧ ¬ Equation1122 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 4, 1, 0, 5, 2], [2, 1, 3, 4, 0, 5], [5, 0, 4, 1, 2, 3], [0, 2, 5, 3, 1, 4], [1, 3, 2, 5, 4, 0], [4, 5, 0, 2, 3, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1353_not_implies_Equation2035 : ∃ (G: Type) (_: Magma G), Equation1353 G ∧ ¬ Equation2035 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 3, 0, 4, 5, 2], [2, 0, 5, 1, 3, 4], [2, 3, 5, 1, 0, 4], [1, 3, 0, 4, 5, 2], [1, 0, 5, 2, 3, 4], [4, 0, 3, 1, 5, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1353_not_implies_Equation3862 : ∃ (G: Type) (_: Magma G), Equation1353 G ∧ ¬ Equation3862 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 4, 5, 0, 3], [3, 0, 1, 5, 2, 4], [3, 2, 4, 0, 5, 1], [4, 0, 1, 5, 2, 3], [4, 5, 1, 0, 2, 3], [1, 2, 4, 5, 0, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1353_not_implies_Equation99 : ∃ (G: Type) (_: Magma G), Equation1353 G ∧ ¬ Equation99 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 5, 3, 2, 0, 4], [2, 0, 3, 4, 5, 1], [4, 0, 3, 2, 5, 1], [1, 5, 3, 2, 0, 4], [4, 3, 0, 2, 5, 1], [2, 5, 0, 1, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1370_not_implies_Equation99 : ∃ (G: Type) (_: Magma G), Equation1370 G ∧ ¬ Equation99 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 4, 3, 5, 2, 0], [2, 3, 4, 5, 1, 0], [5, 0, 4, 2, 1, 3], [1, 4, 3, 5, 2, 0], [5, 4, 0, 1, 2, 3], [5, 0, 4, 2, 1, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1023 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1023 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 1, 0], [3, 4, 0, 2, 1], [1, 3, 4, 0, 2], [2, 0, 1, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1045 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1045 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 1, 2, 0], [2, 4, 3, 0, 1], [3, 0, 4, 1, 2], [1, 2, 0, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1082 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1082 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 1, 2, 0], [2, 4, 3, 0, 1], [3, 0, 4, 1, 2], [1, 2, 0, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1109 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1109 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 4, 0, 1, 3], [3, 2, 1, 4, 0], [0, 1, 2, 3, 4], [4, 0, 3, 2, 1], [1, 3, 4, 0, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1122 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1122 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 4, 0, 1, 3], [3, 2, 1, 4, 0], [0, 1, 2, 3, 4], [4, 0, 3, 2, 1], [1, 3, 4, 0, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1231 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1231 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 1, 0], [3, 4, 0, 2, 1], [1, 3, 4, 0, 2], [2, 0, 1, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1239 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1239 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 1, 2, 0], [2, 4, 3, 0, 1], [3, 0, 4, 1, 2], [1, 2, 0, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1278 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1278 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 4, 0, 1, 3], [3, 2, 1, 4, 0], [0, 1, 2, 3, 4], [4, 0, 3, 2, 1], [1, 3, 4, 0, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1285 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1285 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 1, 0], [3, 4, 0, 2, 1], [1, 3, 4, 0, 2], [2, 0, 1, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1289 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1289 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 1, 0], [3, 4, 0, 2, 1], [1, 3, 4, 0, 2], [2, 0, 1, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1312 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1312 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 1, 2, 0], [2, 4, 3, 0, 1], [3, 0, 4, 1, 2], [1, 2, 0, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1325 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1325 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 4, 0, 1, 3], [3, 2, 1, 4, 0], [0, 1, 2, 3, 4], [4, 0, 3, 2, 1], [1, 3, 4, 0, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1434 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1434 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 4, 0, 1, 3], [3, 2, 1, 4, 0], [0, 1, 2, 3, 4], [4, 0, 3, 2, 1], [1, 3, 4, 0, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1444 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1444 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 1, 0], [3, 4, 0, 2, 1], [1, 3, 4, 0, 2], [2, 0, 1, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1451 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1451 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 4, 0, 1], [4, 3, 0, 1, 2], [1, 4, 3, 2, 0], [0, 1, 2, 3, 4], [2, 0, 1, 4, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1455 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1455 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 4, 0, 1], [4, 3, 0, 1, 2], [1, 4, 3, 2, 0], [0, 1, 2, 3, 4], [2, 0, 1, 4, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1479 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1479 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 1, 2, 0], [2, 4, 3, 0, 1], [3, 0, 4, 1, 2], [1, 2, 0, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1632 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1632 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 3, 0, 4, 1], [4, 2, 1, 0, 3], [0, 1, 2, 3, 4], [1, 4, 3, 2, 0], [3, 0, 4, 1, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1645 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1645 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 4, 0, 1], [4, 3, 0, 1, 2], [1, 4, 3, 2, 0], [0, 1, 2, 3, 4], [2, 0, 1, 4, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1654 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1654 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 1, 0], [3, 4, 0, 2, 1], [1, 3, 4, 0, 2], [2, 0, 1, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1658 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1658 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 4, 0, 1], [4, 3, 0, 1, 2], [1, 4, 3, 2, 0], [0, 1, 2, 3, 4], [2, 0, 1, 4, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1691 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1691 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 1, 2, 0], [2, 4, 3, 0, 1], [3, 0, 4, 1, 2], [1, 2, 0, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1722 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1722 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 3, 0, 4, 1], [4, 2, 1, 0, 3], [0, 1, 2, 3, 4], [1, 4, 3, 2, 0], [3, 0, 4, 1, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1838 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1838 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 1, 0], [3, 4, 0, 2, 1], [1, 3, 4, 0, 2], [2, 0, 1, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1840 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1840 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 1, 0], [3, 4, 0, 2, 1], [1, 3, 4, 0, 2], [2, 0, 1, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1887 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1887 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 4, 0, 1, 3], [3, 2, 1, 4, 0], [0, 1, 2, 3, 4], [4, 0, 3, 2, 1], [1, 3, 4, 0, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1921 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1921 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 1, 2, 0], [2, 4, 3, 0, 1], [3, 0, 4, 1, 2], [1, 2, 0, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation1925 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation1925 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 1, 2, 0], [2, 4, 3, 0, 1], [3, 0, 4, 1, 2], [1, 2, 0, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation2043 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation2043 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 4, 0, 1, 3], [3, 2, 1, 4, 0], [0, 1, 2, 3, 4], [4, 0, 3, 2, 1], [1, 3, 4, 0, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation2053 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation2053 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 1, 0], [3, 4, 0, 2, 1], [1, 3, 4, 0, 2], [2, 0, 1, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation2060 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation2060 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 1, 0], [3, 4, 0, 2, 1], [1, 3, 4, 0, 2], [2, 0, 1, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation2064 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation2064 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 1, 0], [3, 4, 0, 2, 1], [1, 3, 4, 0, 2], [2, 0, 1, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation2088 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation2088 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 1, 2, 0], [2, 4, 3, 0, 1], [3, 0, 4, 1, 2], [1, 2, 0, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation2241 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation2241 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 1, 0], [3, 4, 0, 2, 1], [1, 3, 4, 0, 2], [2, 0, 1, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation2244 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation2244 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 1, 2, 0], [2, 4, 3, 0, 1], [3, 0, 4, 1, 2], [1, 2, 0, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation2254 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation2254 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 3, 0, 4, 1], [4, 2, 1, 0, 3], [0, 1, 2, 3, 4], [1, 4, 3, 2, 0], [3, 0, 4, 1, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation2263 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation2263 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 1, 2, 0], [2, 4, 3, 0, 1], [3, 0, 4, 1, 2], [1, 2, 0, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation2293 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation2293 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 1, 0], [3, 4, 0, 2, 1], [1, 3, 4, 0, 2], [2, 0, 1, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation2338 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation2338 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 1, 2, 0], [2, 4, 3, 0, 1], [3, 0, 4, 1, 2], [1, 2, 0, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation2444 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation2444 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 3, 0, 4, 1], [4, 2, 1, 0, 3], [0, 1, 2, 3, 4], [1, 4, 3, 2, 0], [3, 0, 4, 1, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation2447 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation2447 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 1, 0], [3, 4, 0, 2, 1], [1, 3, 4, 0, 2], [2, 0, 1, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation2449 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation2449 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 1, 0], [3, 4, 0, 2, 1], [1, 3, 4, 0, 2], [2, 0, 1, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation2530 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation2530 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 1, 2, 0], [2, 4, 3, 0, 1], [3, 0, 4, 1, 2], [1, 2, 0, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation2647 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation2647 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 3, 0, 4, 1], [4, 2, 1, 0, 3], [0, 1, 2, 3, 4], [1, 4, 3, 2, 0], [3, 0, 4, 1, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation2660 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation2660 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 4, 0, 1], [4, 3, 0, 1, 2], [1, 4, 3, 2, 0], [0, 1, 2, 3, 4], [2, 0, 1, 4, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation2669 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation2669 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 1, 0], [3, 4, 0, 2, 1], [1, 3, 4, 0, 2], [2, 0, 1, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation2699 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation2699 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 1, 2, 0], [2, 4, 3, 0, 1], [3, 0, 4, 1, 2], [1, 2, 0, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation2853 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation2853 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 1, 0], [3, 4, 0, 2, 1], [1, 3, 4, 0, 2], [2, 0, 1, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation2855 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation2855 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 1, 0], [3, 4, 0, 2, 1], [1, 3, 4, 0, 2], [2, 0, 1, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation2936 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation2936 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 1, 2, 0], [2, 4, 3, 0, 1], [3, 0, 4, 1, 2], [1, 2, 0, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation3075 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation3075 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 1, 0], [3, 4, 0, 2, 1], [1, 3, 4, 0, 2], [2, 0, 1, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation3079 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation3079 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 1, 0], [3, 4, 0, 2, 1], [1, 3, 4, 0, 2], [2, 0, 1, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation3103 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation3103 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 1, 2, 0], [2, 4, 3, 0, 1], [3, 0, 4, 1, 2], [1, 2, 0, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation3105 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation3105 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 1, 2, 0], [2, 4, 3, 0, 1], [3, 0, 4, 1, 2], [1, 2, 0, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation3116 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation3116 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 1, 2, 0], [2, 4, 3, 0, 1], [3, 0, 4, 1, 2], [1, 2, 0, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation3143 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation3143 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 3, 0, 4, 1], [4, 2, 1, 0, 3], [0, 1, 2, 3, 4], [1, 4, 3, 2, 0], [3, 0, 4, 1, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation3261 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation3261 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 4, 0, 1, 3], [3, 2, 1, 4, 0], [0, 1, 2, 3, 4], [4, 0, 3, 2, 1], [1, 3, 4, 0, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation3269 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation3269 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 3, 0, 4, 1], [4, 2, 1, 0, 3], [0, 1, 2, 3, 4], [1, 4, 3, 2, 0], [3, 0, 4, 1, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation3306 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation3306 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 1, 0], [3, 4, 0, 2, 1], [1, 3, 4, 0, 2], [2, 0, 1, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation3342 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation3342 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 4, 0, 1], [4, 3, 0, 1, 2], [1, 4, 3, 2, 0], [0, 1, 2, 3, 4], [2, 0, 1, 4, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation3346 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation3346 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 4, 0, 1], [4, 3, 0, 1, 2], [1, 4, 3, 2, 0], [0, 1, 2, 3, 4], [2, 0, 1, 4, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation3353 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation3353 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 1, 0], [3, 4, 0, 2, 1], [1, 3, 4, 0, 2], [2, 0, 1, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation3355 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation3355 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 1, 0], [3, 4, 0, 2, 1], [1, 3, 4, 0, 2], [2, 0, 1, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation3459 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation3459 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 3, 0, 4, 1], [4, 2, 1, 0, 3], [0, 1, 2, 3, 4], [1, 4, 3, 2, 0], [3, 0, 4, 1, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1384_not_implies_Equation3481 : ∃ (G: Type) (_: Magma G), Equation1384 G ∧ ¬ Equation3481 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 4, 0, 1, 3], [3, 2, 1, 4, 0], [0, 1, 2, 3, 4], [4, 0, 3, 2, 1], [1, 3, 4, 0, 2]][x.val]![y.val]!⟩, by decideFin!⟩

