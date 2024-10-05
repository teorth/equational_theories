import equational_theories.AllEquations
import equational_theories.MemoFinOp
import equational_theories.DecideBang

@[equational_result]
theorem Equation1868_not_implies_Equation4067 : ∃ (G: Type) (_: Magma G), Equation1868 G ∧ ¬ Equation4067 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 2, 2, 2, 2, 2], [3, 3, 3, 3, 5, 3], [5, 3, 0, 4, 5, 4], [1, 1, 1, 1, 2, 1], [2, 5, 5, 2, 5, 2], [2, 4, 4, 1, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1869_not_implies_Equation1435 : ∃ (G: Type) (_: Magma G), Equation1869 G ∧ ¬ Equation1435 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 2, 2, 2, 2, 2], [3, 3, 3, 4, 3, 4], [5, 0, 0, 0, 5, 0], [1, 1, 1, 1, 1, 1], [5, 5, 5, 1, 5, 1], [2, 4, 4, 4, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1869_not_implies_Equation1638 : ∃ (G: Type) (_: Magma G), Equation1869 G ∧ ¬ Equation1638 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 3, 3, 2, 2, 2], [3, 3, 3, 3, 3, 3], [4, 0, 0, 0, 0, 4], [1, 0, 0, 1, 1, 1], [2, 5, 5, 5, 5, 2], [4, 4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1869_not_implies_Equation3261 : ∃ (G: Type) (_: Magma G), Equation1869 G ∧ ¬ Equation3261 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 2, 5, 2, 5, 2], [3, 3, 3, 4, 3, 4], [3, 3, 0, 0, 0, 0], [2, 2, 1, 1, 1, 1], [5, 5, 5, 1, 5, 1], [4, 4, 0, 4, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1869_not_implies_Equation3262 : ∃ (G: Type) (_: Magma G), Equation1869 G ∧ ¬ Equation3262 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 2, 5, 2, 5, 2], [3, 3, 3, 4, 3, 4], [3, 3, 0, 0, 0, 0], [2, 2, 1, 1, 1, 1], [5, 5, 5, 1, 5, 1], [4, 4, 0, 4, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1869_not_implies_Equation3462 : ∃ (G: Type) (_: Magma G), Equation1869 G ∧ ¬ Equation3462 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 2, 5, 2, 5, 2], [3, 3, 3, 3, 3, 3], [0, 0, 0, 0, 0, 0], [1, 4, 1, 1, 1, 4], [5, 3, 5, 5, 5, 3], [4, 4, 0, 4, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1869_not_implies_Equation3465 : ∃ (G: Type) (_: Magma G), Equation1869 G ∧ ¬ Equation3465 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 2, 4, 2, 2, 4], [3, 3, 3, 5, 5, 3], [3, 3, 0, 0, 0, 0], [2, 2, 1, 1, 1, 1], [5, 5, 0, 5, 5, 0], [4, 4, 4, 1, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1869_not_implies_Equation3518 : ∃ (G: Type) (_: Magma G), Equation1869 G ∧ ¬ Equation3518 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 2, 4, 2, 2, 4], [3, 3, 3, 3, 3, 3], [3, 3, 0, 0, 0, 0], [2, 3, 1, 1, 1, 1], [5, 5, 0, 5, 5, 4], [4, 4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1869_not_implies_Equation3521 : ∃ (G: Type) (_: Magma G), Equation1869 G ∧ ¬ Equation3521 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 2, 4, 2, 2, 4], [3, 3, 3, 5, 5, 3], [3, 3, 0, 0, 0, 0], [2, 2, 1, 1, 1, 1], [5, 5, 0, 5, 5, 0], [4, 4, 4, 1, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1869_not_implies_Equation4314 : ∃ (G: Type) (_: Magma G), Equation1869 G ∧ ¬ Equation4314 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 2, 3, 2, 2, 3], [2, 4, 4, 4, 1, 1], [3, 0, 0, 0, 1, 3], [2, 5, 0, 5, 2, 3], [1, 1, 1, 1, 1, 1], [3, 3, 3, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1888_not_implies_Equation1629 : ∃ (G: Type) (_: Magma G), Equation1888 G ∧ ¬ Equation1629 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 2, 0, 4, 3], [2, 4, 3, 0, 1], [3, 0, 2, 1, 4], [0, 1, 4, 3, 2], [4, 3, 1, 2, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1904_not_implies_Equation1038 : ∃ (G: Type) (_: Magma G), Equation1904 G ∧ ¬ Equation1038 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 3, 0], [3, 2, 1, 3, 0], [4, 2, 1, 3, 3], [4, 2, 1, 3, 0], [4, 3, 1, 3, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1904_not_implies_Equation1225 : ∃ (G: Type) (_: Magma G), Equation1904 G ∧ ¬ Equation1225 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 4, 0, 1, 4], [2, 3, 4, 1, 4], [2, 3, 0, 4, 4], [4, 3, 0, 1, 4], [2, 3, 0, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1904_not_implies_Equation1644 : ∃ (G: Type) (_: Magma G), Equation1904 G ∧ ¬ Equation1644 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 4, 0, 4], [4, 2, 1, 0, 4], [3, 2, 1, 4, 4], [3, 4, 1, 0, 4], [3, 2, 1, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1904_not_implies_Equation1654 : ∃ (G: Type) (_: Magma G), Equation1904 G ∧ ¬ Equation1654 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 3, 0], [3, 2, 1, 3, 0], [4, 2, 1, 3, 3], [4, 2, 1, 3, 0], [4, 3, 1, 3, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1904_not_implies_Equation1857 : ∃ (G: Type) (_: Magma G), Equation1904 G ∧ ¬ Equation1857 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 4, 1, 0, 4], [3, 2, 1, 4, 4], [4, 2, 1, 0, 4], [3, 2, 4, 0, 4], [3, 2, 1, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1904_not_implies_Equation3306 : ∃ (G: Type) (_: Magma G), Equation1904 G ∧ ¬ Equation3306 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 3, 0], [3, 2, 1, 3, 0], [4, 2, 1, 3, 3], [4, 2, 1, 3, 0], [4, 3, 1, 3, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1904_not_implies_Equation3343 : ∃ (G: Type) (_: Magma G), Equation1904 G ∧ ¬ Equation3343 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 3, 0], [3, 2, 1, 3, 0], [4, 2, 1, 3, 3], [4, 2, 1, 3, 0], [4, 3, 1, 3, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1904_not_implies_Equation3880 : ∃ (G: Type) (_: Magma G), Equation1904 G ∧ ¬ Equation3880 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 3, 0, 4, 4], [4, 3, 0, 1, 4], [2, 4, 0, 1, 4], [2, 3, 4, 1, 4], [2, 3, 0, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1904_not_implies_Equation4067 : ∃ (G: Type) (_: Magma G), Equation1904 G ∧ ¬ Equation4067 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 4, 0, 1, 4], [2, 3, 4, 1, 4], [2, 3, 0, 4, 4], [4, 3, 0, 1, 4], [2, 3, 0, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1904_not_implies_Equation4118 : ∃ (G: Type) (_: Magma G), Equation1904 G ∧ ¬ Equation4118 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 4, 0, 4], [4, 2, 1, 0, 4], [3, 2, 1, 4, 4], [3, 4, 1, 0, 4], [3, 2, 1, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1904_not_implies_Equation4128 : ∃ (G: Type) (_: Magma G), Equation1904 G ∧ ¬ Equation4128 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 2, 0, 4], [2, 1, 2, 4, 4], [3, 1, 2, 0, 4], [3, 4, 2, 0, 4], [3, 1, 2, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1904_not_implies_Equation4155 : ∃ (G: Type) (_: Magma G), Equation1904 G ∧ ¬ Equation4155 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 2, 0, 4], [2, 1, 2, 2, 4], [3, 1, 2, 0, 4], [3, 4, 2, 0, 4], [3, 1, 2, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1904_not_implies_Equation4291 : ∃ (G: Type) (_: Magma G), Equation1904 G ∧ ¬ Equation4291 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 3, 0], [3, 2, 1, 3, 0], [4, 2, 1, 3, 3], [4, 2, 1, 3, 0], [4, 3, 1, 3, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1924_not_implies_Equation1109 : ∃ (G: Type) (_: Magma G), Equation1924 G ∧ ¬ Equation1109 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[2, 6, 0, 3, 1, 5, 4], [4, 1, 3, 5, 6, 2, 0], [2, 1, 0, 6, 4, 3, 5], [1, 4, 5, 3, 0, 6, 2], [6, 0, 3, 5, 4, 2, 1], [1, 4, 6, 2, 0, 5, 3], [1, 4, 3, 5, 0, 2, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1924_not_implies_Equation4118 : ∃ (G: Type) (_: Magma G), Equation1924 G ∧ ¬ Equation4118 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 1, 0, 4, 5, 3], [2, 1, 0, 4, 5, 3], [2, 3, 0, 5, 4, 1], [2, 5, 0, 3, 1, 4], [2, 3, 0, 5, 4, 1], [2, 4, 0, 1, 3, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1993_not_implies_Equation1020 : ∃ (G: Type) (_: Magma G), Equation1993 G ∧ ¬ Equation1020 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 2, 4, 3, 0], [2, 1, 0, 4, 3], [3, 0, 1, 2, 4], [0, 4, 3, 1, 2], [4, 3, 2, 0, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1993_not_implies_Equation1223 : ∃ (G: Type) (_: Magma G), Equation1993 G ∧ ¬ Equation1223 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 2, 4, 3, 0], [2, 1, 0, 4, 3], [3, 0, 1, 2, 4], [0, 4, 3, 1, 2], [4, 3, 2, 0, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1993_not_implies_Equation2238 : ∃ (G: Type) (_: Magma G), Equation1993 G ∧ ¬ Equation2238 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 2, 3, 0, 4], [2, 1, 0, 4, 3], [4, 0, 1, 3, 2], [3, 4, 2, 1, 0], [0, 3, 4, 2, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1993_not_implies_Equation2441 : ∃ (G: Type) (_: Magma G), Equation1993 G ∧ ¬ Equation2441 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 2, 3, 0, 4], [2, 1, 0, 4, 3], [4, 0, 1, 3, 2], [3, 4, 2, 1, 0], [0, 3, 4, 2, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1993_not_implies_Equation2865 : ∃ (G: Type) (_: Magma G), Equation1993 G ∧ ¬ Equation2865 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 0, 2, 4, 1], [1, 3, 0, 2, 4], [0, 4, 3, 1, 2], [4, 2, 1, 3, 0], [2, 1, 4, 0, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1993_not_implies_Equation2940 : ∃ (G: Type) (_: Magma G), Equation1993 G ∧ ¬ Equation2940 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 1, 0, 4, 2], [0, 3, 4, 2, 1], [2, 0, 3, 1, 4], [4, 2, 1, 3, 0], [1, 4, 2, 0, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1993_not_implies_Equation3068 : ∃ (G: Type) (_: Magma G), Equation1993 G ∧ ¬ Equation3068 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 0, 1, 4], [4, 3, 2, 0, 1], [2, 1, 3, 4, 0], [1, 0, 4, 3, 2], [0, 4, 1, 2, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1993_not_implies_Equation429 : ∃ (G: Type) (_: Magma G), Equation1993 G ∧ ¬ Equation429 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 4, 2, 1, 0], [2, 3, 1, 0, 4], [0, 2, 3, 4, 1], [1, 0, 4, 3, 2], [4, 1, 0, 2, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1993_not_implies_Equation4435 : ∃ (G: Type) (_: Magma G), Equation1993 G ∧ ¬ Equation4435 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 0, 2, 4, 1], [1, 3, 0, 2, 4], [0, 4, 3, 1, 2], [4, 2, 1, 3, 0], [2, 1, 4, 0, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1993_not_implies_Equation632 : ∃ (G: Type) (_: Magma G), Equation1993 G ∧ ¬ Equation632 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 1, 0, 4, 2], [0, 3, 4, 2, 1], [2, 0, 3, 1, 4], [4, 2, 1, 3, 0], [1, 4, 2, 0, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation1993_not_implies_Equation707 : ∃ (G: Type) (_: Magma G), Equation1993 G ∧ ¬ Equation707 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 0, 2, 4, 1], [1, 3, 0, 2, 4], [0, 4, 3, 1, 2], [4, 2, 1, 3, 0], [2, 1, 4, 0, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2045_not_implies_Equation2060 : ∃ (G: Type) (_: Magma G), Equation2045 G ∧ ¬ Equation2060 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 2, 2, 0, 2, 4], [3, 3, 3, 3, 3, 3], [4, 0, 4, 4, 4, 2], [5, 5, 5, 5, 5, 5], [0, 4, 0, 2, 0, 0], [1, 1, 1, 1, 1, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2045_not_implies_Equation255 : ∃ (G: Type) (_: Magma G), Equation2045 G ∧ ¬ Equation255 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 5, 1, 5, 1], [2, 4, 4, 2, 4, 4], [3, 0, 3, 3, 3, 0], [5, 5, 1, 5, 1, 5], [0, 3, 0, 0, 0, 3], [4, 2, 2, 4, 2, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2045_not_implies_Equation2644 : ∃ (G: Type) (_: Magma G), Equation2045 G ∧ ¬ Equation2644 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 4, 1, 1, 4, 1], [2, 2, 5, 2, 2, 5], [3, 0, 0, 3, 0, 0], [4, 1, 4, 4, 1, 4], [5, 5, 2, 5, 5, 2], [0, 3, 3, 0, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2045_not_implies_Equation2847 : ∃ (G: Type) (_: Magma G), Equation2045 G ∧ ¬ Equation2847 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 4, 1, 1, 4], [2, 5, 5, 2, 5, 5], [3, 0, 3, 3, 0, 3], [4, 4, 1, 4, 4, 1], [5, 2, 2, 5, 2, 2], [0, 3, 0, 0, 3, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2045_not_implies_Equation3253 : ∃ (G: Type) (_: Magma G), Equation2045 G ∧ ¬ Equation3253 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 2, 1, 1, 1], [5, 5, 5, 5, 4, 4], [4, 4, 4, 4, 5, 5], [2, 1, 1, 2, 2, 2], [0, 3, 3, 0, 3, 3], [3, 0, 0, 3, 0, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2045_not_implies_Equation3456 : ∃ (G: Type) (_: Magma G), Equation2045 G ∧ ¬ Equation3456 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 3, 3, 3, 3, 1], [2, 4, 2, 4, 2, 2], [0, 0, 5, 0, 5, 0], [4, 2, 4, 2, 4, 4], [5, 5, 0, 5, 0, 5], [3, 1, 1, 1, 1, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2045_not_implies_Equation4598 : ∃ (G: Type) (_: Magma G), Equation2045 G ∧ ¬ Equation4598 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 3, 1, 3, 1, 1], [2, 2, 4, 2, 4, 2], [5, 0, 0, 0, 0, 5], [4, 4, 2, 4, 2, 4], [0, 5, 5, 5, 5, 0], [3, 1, 3, 1, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2045_not_implies_Equation4656 : ∃ (G: Type) (_: Magma G), Equation2045 G ∧ ¬ Equation4656 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 2, 2, 5, 0, 2], [4, 4, 4, 4, 4, 4], [5, 0, 5, 2, 5, 5], [1, 1, 1, 1, 1, 1], [3, 3, 3, 3, 3, 3], [0, 5, 0, 0, 2, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2061_not_implies_Equation2660 : ∃ (G: Type) (_: Magma G), Equation2061 G ∧ ¬ Equation2660 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[3, 2, 3, 3, 3, 3, 3], [1, 1, 1, 1, 1, 1, 1], [6, 4, 2, 2, 5, 2, 2], [4, 6, 4, 4, 4, 4, 4], [0, 5, 0, 0, 0, 0, 0], [5, 3, 5, 6, 2, 5, 5], [2, 0, 6, 5, 6, 6, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation206_not_implies_Equation1841 : ∃ (G: Type) (_: Magma G), Equation206 G ∧ ¬ Equation1841 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 2, 3, 5, 3, 2], [4, 4, 4, 4, 4, 4], [5, 3, 2, 0, 2, 3], [2, 0, 5, 3, 5, 0], [1, 1, 1, 1, 1, 1], [3, 5, 0, 2, 0, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation206_not_implies_Equation2247 : ∃ (G: Type) (_: Magma G), Equation206 G ∧ ¬ Equation2247 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 4, 3, 4, 5, 3], [2, 2, 2, 2, 2, 2], [1, 1, 1, 1, 1, 1], [5, 3, 4, 3, 0, 4], [3, 5, 0, 5, 4, 0], [4, 0, 5, 0, 3, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation206_not_implies_Equation2444 : ∃ (G: Type) (_: Magma G), Equation206 G ∧ ¬ Equation2444 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[2, 4, 2, 4, 5, 1, 4], [5, 1, 6, 2, 0, 4, 3], [0, 3, 0, 6, 3, 3, 1], [3, 6, 1, 3, 6, 6, 2], [1, 5, 4, 5, 4, 0, 5], [4, 0, 5, 0, 1, 5, 0], [6, 2, 3, 1, 2, 2, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation206_not_implies_Equation3319 : ∃ (G: Type) (_: Magma G), Equation206 G ∧ ¬ Equation3319 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 2, 5, 0, 2, 4], [3, 3, 3, 3, 3, 3], [4, 5, 2, 2, 5, 0], [1, 1, 1, 1, 1, 1], [5, 4, 0, 4, 4, 2], [2, 0, 4, 5, 0, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2066_not_implies_Equation2040 : ∃ (G: Type) (_: Magma G), Equation2066 G ∧ ¬ Equation2040 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 4, 0, 2, 4, 0], [2, 1, 3, 2, 1, 3], [2, 1, 0, 2, 1, 0], [5, 1, 3, 5, 1, 3], [5, 4, 0, 5, 4, 0], [5, 4, 3, 5, 4, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2066_not_implies_Equation2043 : ∃ (G: Type) (_: Magma G), Equation2066 G ∧ ¬ Equation2043 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 1, 0, 1, 0, 2], [4, 1, 0, 1, 0, 4], [2, 3, 0, 3, 0, 2], [2, 3, 5, 3, 5, 2], [4, 1, 5, 1, 5, 4], [4, 3, 5, 3, 5, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2066_not_implies_Equation2050 : ∃ (G: Type) (_: Magma G), Equation2066 G ∧ ¬ Equation2050 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 1, 0, 0, 3, 1], [2, 1, 0, 0, 2, 1], [2, 1, 4, 4, 2, 1], [3, 5, 0, 0, 3, 5], [2, 5, 4, 4, 2, 5], [3, 5, 4, 4, 3, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2066_not_implies_Equation2053 : ∃ (G: Type) (_: Magma G), Equation2066 G ∧ ¬ Equation2053 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[5, 1, 0, 5, 1, 0], [2, 1, 0, 2, 1, 0], [2, 1, 3, 2, 1, 3], [2, 4, 3, 2, 4, 3], [5, 4, 3, 5, 4, 3], [5, 4, 0, 5, 4, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2066_not_implies_Equation4599 : ∃ (G: Type) (_: Magma G), Equation2066 G ∧ ¬ Equation4599 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 2, 2, 0, 3, 0], [3, 1, 1, 4, 3, 4], [5, 2, 2, 0, 5, 0], [3, 1, 1, 0, 3, 0], [5, 1, 1, 4, 5, 4], [5, 2, 2, 4, 5, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2066_not_implies_Equation4631 : ∃ (G: Type) (_: Magma G), Equation2066 G ∧ ¬ Equation4631 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 1, 0, 0, 1, 3], [2, 1, 0, 0, 1, 2], [2, 1, 5, 5, 1, 2], [3, 4, 0, 0, 4, 3], [3, 4, 5, 5, 4, 3], [2, 4, 5, 5, 4, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2070_not_implies_Equation3253 : ∃ (G: Type) (_: Magma G), Equation2070 G ∧ ¬ Equation3253 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 2, 2, 1, 2], [4, 4, 4, 3, 4, 3], [4, 4, 3, 3, 3, 3], [0, 0, 5, 5, 0, 0], [0, 0, 5, 0, 0, 0], [1, 2, 2, 2, 1, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2074_not_implies_Equation3255 : ∃ (G: Type) (_: Magma G), Equation2074 G ∧ ¬ Equation3255 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 1, 2, 1, 1, 2], [3, 3, 5, 5, 5, 3], [3, 3, 5, 5, 5, 3], [0, 4, 0, 0, 4, 4], [2, 1, 2, 1, 1, 2], [0, 4, 0, 0, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2074_not_implies_Equation4316 : ∃ (G: Type) (_: Magma G), Equation2074 G ∧ ¬ Equation4316 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 5, 1, 5, 5, 1], [2, 2, 2, 3, 3, 3], [4, 0, 0, 4, 0, 4], [4, 0, 0, 4, 0, 4], [1, 5, 1, 5, 5, 1], [2, 2, 2, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2082_not_implies_Equation3319 : ∃ (G: Type) (_: Magma G), Equation2082 G ∧ ¬ Equation3319 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 2, 4, 4, 2, 4], [3, 0, 0, 0, 3, 3], [1, 1, 1, 5, 5, 5], [2, 2, 4, 4, 2, 4], [1, 1, 1, 5, 5, 5], [3, 0, 0, 0, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2093_not_implies_Equation3952 : ∃ (G: Type) (_: Magma G), Equation2093 G ∧ ¬ Equation3952 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 1, 0, 3], [4, 2, 1, 4, 3], [1, 2, 1, 4, 3], [4, 0, 1, 4, 3], [4, 0, 1, 0, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2127_not_implies_Equation1629 : ∃ (G: Type) (_: Magma G), Equation2127 G ∧ ¬ Equation1629 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 1, 3, 2, 1], [2, 4, 3, 2, 1], [3, 0, 3, 0, 1], [2, 0, 0, 2, 1], [3, 1, 0, 0, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2227_not_implies_Equation411 : ∃ (G: Type) (_: Magma G), Equation2227 G ∧ ¬ Equation411 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 3, 4, 5, 0], [5, 0, 1, 2, 3, 4], [1, 2, 3, 4, 5, 0], [5, 0, 1, 2, 3, 4], [1, 2, 3, 4, 5, 0], [5, 0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2227_not_implies_Equation4307 : ∃ (G: Type) (_: Magma G), Equation2227 G ∧ ¬ Equation4307 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 1, 2, 0], [4, 2, 1, 3, 0], [4, 2, 1, 3, 0], [4, 2, 1, 3, 0], [4, 2, 3, 1, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2260_not_implies_Equation1426 : ∃ (G: Type) (_: Magma G), Equation2260 G ∧ ¬ Equation1426 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 4, 1, 4, 4], [3, 0, 3, 3, 0, 3], [5, 5, 5, 0, 5, 5], [4, 1, 1, 4, 1, 1], [0, 3, 0, 5, 3, 0], [2, 4, 2, 2, 2, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2260_not_implies_Equation203 : ∃ (G: Type) (_: Magma G), Equation2260 G ∧ ¬ Equation203 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 5, 5, 1, 5], [4, 0, 4, 4, 4, 0], [3, 3, 3, 3, 0, 3], [2, 5, 2, 2, 2, 2], [5, 1, 1, 1, 5, 1], [0, 4, 0, 0, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2260_not_implies_Equation3456 : ∃ (G: Type) (_: Magma G), Equation2260 G ∧ ¬ Equation3456 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 3, 3, 3, 1, 3], [2, 0, 4, 0, 4, 4], [5, 5, 5, 1, 5, 5], [0, 4, 0, 4, 0, 0], [3, 1, 1, 5, 3, 1], [4, 2, 2, 2, 2, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2270_not_implies_Equation203 : ∃ (G: Type) (_: Magma G), Equation2270 G ∧ ¬ Equation203 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 5, 1, 5, 5], [4, 4, 0, 4, 4, 0], [3, 3, 4, 3, 0, 4], [5, 5, 2, 5, 2, 2], [2, 1, 1, 2, 1, 1], [0, 0, 3, 0, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2314_not_implies_Equation2330 : ∃ (G: Type) (_: Magma G), Equation2314 G ∧ ¬ Equation2330 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 2, 4, 3, 3], [4, 2, 3, 2, 3], [4, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 2, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2347_not_implies_Equation2669 : ∃ (G: Type) (_: Magma G), Equation2347 G ∧ ¬ Equation2669 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 2, 4, 3], [3, 1, 3, 3, 4], [0, 1, 2, 4, 3], [0, 1, 2, 3, 4], [2, 1, 3, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2381_not_implies_Equation1055 : ∃ (G: Type) (_: Magma G), Equation2381 G ∧ ¬ Equation1055 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 1, 1, 3, 4, 5], [5, 1, 2, 4, 5, 5], [3, 1, 2, 5, 5, 0], [0, 1, 1, 3, 4, 5], [5, 2, 1, 3, 4, 5], [0, 2, 1, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2381_not_implies_Equation1958 : ∃ (G: Type) (_: Magma G), Equation2381 G ∧ ¬ Equation1958 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 4, 3, 3, 4, 5], [5, 1, 2, 4, 5, 0], [3, 3, 2, 3, 5, 0], [0, 1, 2, 3, 4, 5], [5, 1, 2, 3, 4, 5], [0, 1, 3, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2381_not_implies_Equation2263 : ∃ (G: Type) (_: Magma G), Equation2381 G ∧ ¬ Equation2263 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 1, 2, 4, 1], [2, 1, 3, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 1], [2, 2, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2381_not_implies_Equation2364 : ∃ (G: Type) (_: Magma G), Equation2381 G ∧ ¬ Equation2364 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 1, 2, 3, 4, 5], [5, 1, 3, 4, 0, 5], [3, 0, 2, 3, 5, 5], [0, 1, 2, 3, 5, 5], [5, 0, 2, 3, 4, 5], [0, 1, 3, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2381_not_implies_Equation2503 : ∃ (G: Type) (_: Magma G), Equation2381 G ∧ ¬ Equation2503 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 2, 5, 5, 5, 5], [5, 1, 5, 4, 5, 5], [3, 1, 2, 5, 5, 5], [0, 1, 5, 3, 5, 5], [5, 1, 5, 3, 4, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2381_not_implies_Equation2669 : ∃ (G: Type) (_: Magma G), Equation2381 G ∧ ¬ Equation2669 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 2, 3, 3, 3, 5], [3, 1, 3, 3, 3, 5], [5, 1, 2, 4, 3, 5], [0, 1, 2, 3, 4, 5], [5, 1, 2, 3, 4, 5], [0, 1, 3, 3, 3, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2381_not_implies_Equation3897 : ∃ (G: Type) (_: Magma G), Equation2381 G ∧ ¬ Equation3897 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 5, 2, 3, 3, 5], [5, 1, 4, 4, 3, 5], [3, 5, 2, 5, 3, 5], [0, 5, 2, 3, 4, 5], [5, 5, 2, 3, 4, 5], [0, 1, 4, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation238_not_implies_Equation2300 : ∃ (G: Type) (_: Magma G), Equation238 G ∧ ¬ Equation2300 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 1, 3, 4, 4], [2, 1, 2, 4, 4], [0, 1, 2, 4, 4], [0, 1, 2, 3, 4], [2, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation238_not_implies_Equation2337 : ∃ (G: Type) (_: Magma G), Equation238 G ∧ ¬ Equation2337 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 1, 2, 4, 4], [2, 1, 3, 4, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [2, 0, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2398_not_implies_Equation1025 : ∃ (G: Type) (_: Magma G), Equation2398 G ∧ ¬ Equation1025 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 2, 4], [2, 1, 4, 3, 2], [0, 1, 2, 3, 4], [4, 1, 2, 3, 4], [0, 3, 2, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2398_not_implies_Equation1847 : ∃ (G: Type) (_: Magma G), Equation2398 G ∧ ¬ Equation1847 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 2, 2], [2, 1, 4, 2, 4], [0, 1, 2, 3, 4], [4, 1, 2, 3, 4], [0, 3, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2398_not_implies_Equation2253 : ∃ (G: Type) (_: Magma G), Equation2398 G ∧ ¬ Equation2253 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 1, 3, 2, 4], [2, 1, 4, 3, 2], [0, 1, 2, 3, 4], [4, 1, 2, 3, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2398_not_implies_Equation2300 : ∃ (G: Type) (_: Magma G), Equation2398 G ∧ ¬ Equation2300 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 1, 3, 2, 4], [2, 1, 2, 4, 3], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [2, 2, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2398_not_implies_Equation2446 : ∃ (G: Type) (_: Magma G), Equation2398 G ∧ ¬ Equation2446 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 1, 3, 2, 4], [2, 1, 4, 2, 4], [0, 1, 2, 3, 4], [4, 1, 2, 3, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2398_not_implies_Equation2466 : ∃ (G: Type) (_: Magma G), Equation2398 G ∧ ¬ Equation2466 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 3, 3, 2, 4], [2, 1, 4, 2, 4], [0, 1, 2, 3, 4], [4, 1, 2, 3, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2398_not_implies_Equation2503 : ∃ (G: Type) (_: Magma G), Equation2398 G ∧ ¬ Equation2503 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 2, 2, 3, 4, 5], [5, 1, 2, 4, 3, 0], [3, 1, 2, 0, 5, 5], [0, 2, 2, 3, 4, 5], [5, 2, 2, 3, 4, 0], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2398_not_implies_Equation2649 : ∃ (G: Type) (_: Magma G), Equation2398 G ∧ ¬ Equation2649 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 4, 3, 4, 4], [2, 1, 4, 3, 4], [0, 1, 2, 1, 4], [4, 4, 2, 3, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2398_not_implies_Equation2669 : ∃ (G: Type) (_: Magma G), Equation2398 G ∧ ¬ Equation2669 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 2, 3, 4], [3, 1, 3, 0, 0], [0, 1, 2, 4, 3], [0, 1, 2, 3, 4], [2, 2, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2398_not_implies_Equation3867 : ∃ (G: Type) (_: Magma G), Equation2398 G ∧ ¬ Equation3867 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 1, 3, 2, 4], [2, 1, 4, 3, 2], [0, 1, 2, 3, 4], [4, 0, 2, 3, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2450_not_implies_Equation2254 : ∃ (G: Type) (_: Magma G), Equation2450 G ∧ ¬ Equation2254 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 2, 5, 4, 3, 2], [1, 1, 1, 1, 1, 1], [4, 3, 2, 5, 0, 3], [2, 4, 0, 3, 5, 4], [5, 0, 3, 2, 4, 0], [3, 5, 4, 0, 2, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2450_not_implies_Equation3306 : ∃ (G: Type) (_: Magma G), Equation2450 G ∧ ¬ Equation3306 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[0, 2, 3, 4, 5, 6, 1], [6, 1, 0, 5, 3, 2, 4], [1, 5, 2, 0, 6, 4, 3], [2, 4, 6, 3, 0, 1, 5], [3, 6, 5, 1, 4, 0, 2], [4, 3, 1, 6, 2, 5, 0], [5, 0, 4, 2, 1, 3, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2499_not_implies_Equation3529 : ∃ (G: Type) (_: Magma G), Equation2499 G ∧ ¬ Equation3529 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 3, 3, 3, 4, 5], [5, 1, 3, 3, 3, 5], [4, 3, 2, 3, 4, 3], [0, 1, 2, 3, 4, 5], [0, 5, 2, 3, 4, 5], [0, 1, 3, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2499_not_implies_Equation4362 : ∃ (G: Type) (_: Magma G), Equation2499 G ∧ ¬ Equation4362 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 4, 4, 3, 4], [4, 1, 3, 3, 4], [4, 3, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2507_not_implies_Equation2338 : ∃ (G: Type) (_: Magma G), Equation2507 G ∧ ¬ Equation2338 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[5, 6, 7, 3, 8, 0, 1, 2, 4], [2, 1, 0, 6, 5, 4, 3, 8, 7], [8, 3, 2, 1, 6, 7, 4, 5, 0], [3, 4, 8, 0, 1, 5, 7, 6, 2], [1, 0, 6, 7, 4, 8, 2, 3, 5], [0, 2, 1, 5, 7, 3, 8, 4, 6], [7, 5, 4, 8, 2, 1, 6, 0, 3], [4, 8, 3, 2, 0, 6, 5, 7, 1], [6, 7, 5, 4, 3, 2, 0, 1, 8]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2507_not_implies_Equation3079 : ∃ (G: Type) (_: Magma G), Equation2507 G ∧ ¬ Equation3079 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[5, 2, 1, 3, 8, 0, 7, 6, 4], [4, 7, 5, 6, 0, 2, 3, 1, 8], [8, 3, 4, 1, 2, 7, 6, 5, 0], [3, 4, 7, 0, 1, 5, 8, 2, 6], [7, 5, 2, 8, 6, 1, 4, 0, 3], [0, 6, 8, 5, 7, 3, 1, 4, 2], [1, 0, 6, 7, 4, 8, 2, 3, 5], [2, 1, 0, 4, 3, 6, 5, 8, 7], [6, 8, 3, 2, 5, 4, 0, 7, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2507_not_implies_Equation4283 : ∃ (G: Type) (_: Magma G), Equation2507 G ∧ ¬ Equation4283 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[6, 2, 1, 4, 3, 8, 0, 7, 5], [3, 4, 6, 0, 1, 5, 2, 8, 7], [4, 7, 3, 2, 0, 6, 5, 1, 8], [5, 6, 2, 8, 7, 0, 1, 4, 3], [8, 1, 7, 6, 5, 4, 3, 2, 0], [2, 5, 0, 7, 4, 1, 8, 3, 6], [0, 8, 4, 5, 2, 3, 7, 6, 1], [7, 3, 5, 1, 8, 2, 6, 0, 4], [1, 0, 8, 3, 6, 7, 4, 5, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2507_not_implies_Equation4482 : ∃ (G: Type) (_: Magma G), Equation2507 G ∧ ¬ Equation4482 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[0, 6, 3, 2, 7, 8, 1, 4, 5], [3, 2, 1, 0, 8, 6, 5, 7, 4], [4, 1, 7, 5, 0, 3, 8, 2, 6], [7, 5, 8, 4, 3, 1, 6, 0, 2], [1, 0, 5, 3, 6, 2, 4, 8, 7], [8, 4, 6, 7, 1, 5, 2, 3, 0], [2, 8, 0, 6, 4, 7, 3, 5, 1], [6, 7, 2, 8, 5, 4, 0, 1, 3], [5, 3, 4, 1, 2, 0, 7, 6, 8]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2507_not_implies_Equation707 : ∃ (G: Type) (_: Magma G), Equation2507 G ∧ ¬ Equation707 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[0, 2, 1, 5, 8, 3, 7, 6, 4], [6, 7, 5, 4, 3, 2, 0, 1, 8], [7, 3, 6, 1, 4, 8, 2, 0, 5], [5, 6, 8, 3, 7, 0, 1, 4, 2], [1, 0, 4, 8, 2, 7, 6, 5, 3], [3, 4, 7, 0, 1, 5, 8, 2, 6], [8, 5, 2, 7, 6, 1, 4, 3, 0], [4, 1, 3, 2, 0, 6, 5, 8, 7], [2, 8, 0, 6, 5, 4, 3, 7, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2513_not_implies_Equation1025 : ∃ (G: Type) (_: Magma G), Equation2513 G ∧ ¬ Equation1025 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 4, 4], [2, 1, 2, 4, 4], [0, 1, 2, 4, 4], [4, 4, 2, 3, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2513_not_implies_Equation1847 : ∃ (G: Type) (_: Magma G), Equation2513 G ∧ ¬ Equation1847 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 4, 2], [2, 1, 2, 4, 4], [0, 1, 2, 3, 4], [4, 2, 2, 3, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2513_not_implies_Equation2253 : ∃ (G: Type) (_: Magma G), Equation2513 G ∧ ¬ Equation2253 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 3, 2], [2, 1, 2, 3, 2], [0, 1, 2, 3, 4], [4, 4, 2, 3, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2513_not_implies_Equation2466 : ∃ (G: Type) (_: Magma G), Equation2513 G ∧ ¬ Equation2466 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 3, 3, 3, 4], [2, 1, 2, 4, 4], [0, 1, 2, 3, 4], [4, 1, 2, 3, 4], [0, 2, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2513_not_implies_Equation2649 : ∃ (G: Type) (_: Magma G), Equation2513 G ∧ ¬ Equation2649 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 4, 4], [2, 1, 2, 4, 4], [0, 1, 2, 4, 4], [4, 2, 2, 3, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2513_not_implies_Equation3867 : ∃ (G: Type) (_: Magma G), Equation2513 G ∧ ¬ Equation3867 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 3, 2], [2, 1, 2, 4, 2], [0, 1, 2, 3, 4], [4, 2, 2, 3, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2536_not_implies_Equation221 : ∃ (G: Type) (_: Magma G), Equation2536 G ∧ ¬ Equation221 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 2, 2, 4], [3, 4, 3, 3, 4], [0, 0, 4, 0, 4], [1, 1, 1, 4, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2536_not_implies_Equation2293 : ∃ (G: Type) (_: Magma G), Equation2536 G ∧ ¬ Equation2293 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 2, 2, 4], [3, 4, 3, 3, 4], [0, 0, 4, 0, 4], [1, 1, 1, 4, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2536_not_implies_Equation2300 : ∃ (G: Type) (_: Magma G), Equation2536 G ∧ ¬ Equation2300 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 3, 3, 4], [2, 4, 2, 2, 4], [1, 1, 4, 1, 4], [0, 0, 0, 4, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2536_not_implies_Equation2330 : ∃ (G: Type) (_: Magma G), Equation2536 G ∧ ¬ Equation2330 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 2, 2, 4], [3, 4, 3, 3, 4], [0, 0, 4, 0, 4], [1, 1, 1, 4, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2536_not_implies_Equation2506 : ∃ (G: Type) (_: Magma G), Equation2536 G ∧ ¬ Equation2506 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 2, 2, 4], [3, 4, 3, 3, 4], [0, 0, 4, 0, 4], [1, 1, 1, 4, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2536_not_implies_Equation2699 : ∃ (G: Type) (_: Magma G), Equation2536 G ∧ ¬ Equation2699 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 3, 3, 4], [2, 4, 2, 2, 4], [1, 1, 4, 1, 4], [0, 0, 0, 4, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2536_not_implies_Equation3461 : ∃ (G: Type) (_: Magma G), Equation2536 G ∧ ¬ Equation3461 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 4, 2, 2, 4], [3, 4, 2, 3, 4], [0, 1, 2, 3, 4], [1, 1, 2, 2, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2536_not_implies_Equation3749 : ∃ (G: Type) (_: Magma G), Equation2536 G ∧ ¬ Equation3749 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 2, 2, 4], [3, 4, 3, 3, 4], [0, 0, 4, 0, 4], [1, 1, 1, 4, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2536_not_implies_Equation4155 : ∃ (G: Type) (_: Magma G), Equation2536 G ∧ ¬ Equation4155 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 2, 2, 4], [3, 4, 3, 3, 4], [0, 0, 4, 0, 4], [1, 1, 1, 4, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2550_not_implies_Equation1025 : ∃ (G: Type) (_: Magma G), Equation2550 G ∧ ¬ Equation1025 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 3, 4], [2, 1, 2, 2, 0], [0, 1, 2, 3, 4], [4, 1, 2, 3, 0], [0, 2, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2550_not_implies_Equation1847 : ∃ (G: Type) (_: Magma G), Equation2550 G ∧ ¬ Equation1847 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 4, 3, 4, 4], [2, 1, 2, 3, 2], [0, 1, 2, 1, 4], [4, 4, 2, 3, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2550_not_implies_Equation2253 : ∃ (G: Type) (_: Magma G), Equation2550 G ∧ ¬ Equation2253 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 4, 3, 3, 4], [2, 1, 2, 2, 4], [0, 4, 2, 3, 4], [4, 4, 2, 3, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2550_not_implies_Equation2466 : ∃ (G: Type) (_: Magma G), Equation2550 G ∧ ¬ Equation2466 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 4, 3, 3, 4], [2, 1, 2, 3, 4], [0, 4, 2, 4, 1], [4, 1, 2, 3, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2550_not_implies_Equation2503 : ∃ (G: Type) (_: Magma G), Equation2550 G ∧ ¬ Equation2503 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 3, 3, 3], [0, 1, 3, 4, 3], [3, 1, 2, 3, 3], [0, 1, 2, 3, 4], [1, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2550_not_implies_Equation2649 : ∃ (G: Type) (_: Magma G), Equation2550 G ∧ ¬ Equation2649 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 4, 3, 4, 4], [2, 1, 4, 2, 4], [0, 4, 2, 3, 4], [4, 4, 2, 3, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2550_not_implies_Equation3867 : ∃ (G: Type) (_: Magma G), Equation2550 G ∧ ¬ Equation3867 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 3, 3, 3, 4], [2, 1, 2, 3, 4], [0, 1, 2, 1, 1], [4, 1, 2, 3, 4], [0, 3, 2, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2584_not_implies_Equation2862 : ∃ (G: Type) (_: Magma G), Equation2584 G ∧ ¬ Equation2862 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 4, 3, 3, 4, 2], [2, 1, 2, 4, 4, 2], [0, 1, 2, 4, 0, 5], [4, 1, 2, 3, 0, 5], [5, 1, 2, 3, 4, 2], [0, 1, 3, 4, 0, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2592_not_implies_Equation1629 : ∃ (G: Type) (_: Magma G), Equation2592 G ∧ ¬ Equation1629 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 3, 4, 1, 2], [2, 4, 3, 2, 1], [4, 2, 1, 4, 3], [1, 0, 4, 4, 3], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2592_not_implies_Equation2644 : ∃ (G: Type) (_: Magma G), Equation2592 G ∧ ¬ Equation2644 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 4, 3, 2, 0], [2, 0, 1, 4, 3], [3, 2, 4, 0, 1], [0, 1, 2, 3, 4], [4, 3, 0, 1, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2647_not_implies_Equation3522 : ∃ (G: Type) (_: Magma G), Equation2647 G ∧ ¬ Equation3522 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 0, 0, 4, 4], [2, 2, 2, 2, 2], [3, 3, 3, 3, 3], [1, 1, 1, 1, 1], [4, 4, 4, 0, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2653_not_implies_Equation3459 : ∃ (G: Type) (_: Magma G), Equation2653 G ∧ ¬ Equation3459 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[0, 2, 6, 1, 5, 3, 4], [5, 5, 1, 6, 0, 5, 5], [4, 3, 4, 4, 4, 2, 0], [2, 0, 2, 2, 2, 4, 3], [3, 4, 3, 3, 3, 0, 2], [6, 6, 0, 5, 1, 6, 6], [1, 1, 5, 0, 6, 1, 1]][x.val]![y.val]!⟩, by decideFin!⟩

