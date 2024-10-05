import equational_theories.AllEquations
import equational_theories.MemoFinOp
import equational_theories.DecideBang

@[equational_result]
theorem Equation2939_not_implies_Equation4380 : ∃ (G: Type) (_: Magma G), Equation2939 G ∧ ¬ Equation4380 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 2, 0, 0, 4], [3, 1, 4, 4, 0], [4, 0, 2, 3, 1], [4, 0, 2, 3, 1], [0, 4, 1, 1, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2939_not_implies_Equation47 : ∃ (G: Type) (_: Magma G), Equation2939 G ∧ ¬ Equation47 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 2, 3, 0, 4], [3, 4, 2, 1, 0], [4, 1, 0, 2, 3], [2, 0, 4, 3, 1], [0, 3, 1, 4, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2939_not_implies_Equation99 : ∃ (G: Type) (_: Magma G), Equation2939 G ∧ ¬ Equation99 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 2, 3, 1, 4], [2, 1, 4, 3, 0], [4, 3, 2, 4, 1], [3, 1, 0, 2, 4], [0, 4, 1, 3, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2990_not_implies_Equation3253 : ∃ (G: Type) (_: Magma G), Equation2990 G ∧ ¬ Equation3253 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 2, 2, 1, 4], [3, 1, 2, 4, 0], [3, 1, 2, 4, 0], [0, 2, 2, 1, 2], [1, 1, 2, 3, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2990_not_implies_Equation3456 : ∃ (G: Type) (_: Magma G), Equation2990 G ∧ ¬ Equation3456 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 3, 3, 1, 4], [2, 1, 4, 3, 0], [0, 3, 3, 1, 3], [2, 1, 4, 3, 0], [3, 3, 2, 1, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2990_not_implies_Equation3674 : ∃ (G: Type) (_: Magma G), Equation2990 G ∧ ¬ Equation3674 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 3, 3, 2, 4], [0, 2, 3, 2, 2], [1, 4, 2, 3, 0], [1, 4, 2, 3, 0], [3, 1, 2, 2, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation1020 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation1020 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 1, 3, 3, 5], [2, 4, 2, 3, 4, 4], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 5, 2, 0, 0, 3], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation1223 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation1223 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 1, 4, 4, 2], [2, 3, 4, 3, 0, 3], [0, 1, 2, 3, 4, 5], [0, 5, 4, 0, 0, 2], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation1426 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation1426 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 4, 4, 5, 2], [5, 3, 2, 3, 5, 3], [5, 5, 3, 0, 0, 4], [0, 5, 4, 0, 0, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation151 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation151 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 4, 4, 4, 3], [5, 2, 2, 4, 4, 2], [0, 5, 0, 1, 0, 5], [5, 1, 0, 1, 1, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation1629 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation1629 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 4, 1, 2, 5, 3], [2, 4, 2, 2, 3, 3], [0, 1, 2, 3, 4, 5], [1, 5, 1, 0, 5, 5], [2, 5, 5, 0, 3, 3], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation1832 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation1832 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 4, 1, 5, 3], [5, 2, 2, 4, 5, 2], [3, 5, 0, 4, 0, 4], [5, 2, 4, 1, 1, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation203 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation203 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 1, 4, 4, 4], [2, 3, 2, 3, 0, 3], [0, 1, 2, 3, 4, 5], [0, 5, 1, 0, 0, 4], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation2035 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation2035 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 5, 2, 2, 3], [2, 5, 2, 4, 2, 4], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 3, 1, 3, 0, 3], [2, 3, 2, 0, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation2238 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation2238 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 2, 1, 5, 5], [3, 2, 2, 3, 5, 2], [3, 5, 4, 4, 4, 5], [0, 1, 2, 3, 4, 5], [0, 1, 3, 5, 0, 0], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation2441 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation2441 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 1, 2, 5, 3], [2, 3, 2, 3, 5, 3], [0, 1, 2, 3, 4, 5], [0, 5, 4, 0, 5, 5], [1, 5, 2, 2, 0, 3], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation2644 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation2644 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 3, 3, 5, 1], [5, 2, 2, 4, 5, 5], [1, 3, 4, 4, 4, 5], [0, 1, 2, 3, 4, 5], [0, 3, 3, 5, 0, 1], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation2849 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation2849 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 3, 3, 5, 1], [5, 2, 2, 4, 5, 3], [1, 3, 4, 0, 0, 5], [0, 1, 2, 3, 4, 5], [0, 3, 3, 3, 0, 1], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation2852 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation2852 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 2, 2, 3, 5, 1], [5, 4, 0, 2, 4, 5], [0, 1, 2, 3, 4, 5], [5, 1, 4, 1, 5, 5], [0, 2, 2, 2, 0, 3], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation2855 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation2855 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[4, 2, 2, 1, 4, 1], [3, 4, 0, 3, 4, 3], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [3, 2, 5, 1, 5, 5], [5, 1, 3, 1, 2, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation2865 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation2865 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[4, 3, 2, 3, 4, 4], [2, 4, 5, 0, 4, 5], [5, 1, 1, 5, 3, 1], [0, 1, 2, 3, 4, 5], [5, 3, 2, 2, 2, 3], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation2872 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation2872 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 3, 3, 5, 1], [5, 2, 2, 3, 2, 3], [0, 4, 0, 0, 5, 3], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation2875 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation2875 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[4, 5, 3, 5, 4, 4], [4, 2, 2, 5, 3, 2], [0, 5, 0, 0, 3, 5], [0, 1, 2, 3, 4, 5], [5, 5, 2, 1, 2, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation2899 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation2899 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 3, 2, 5, 2, 4], [0, 5, 3, 5, 2, 5], [4, 1, 1, 5, 3, 4], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 3, 3, 4, 2, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation2902 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation2902 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 3, 2, 5, 5, 2], [2, 4, 3, 0, 0, 3], [5, 1, 1, 4, 5, 3], [0, 1, 2, 3, 4, 5], [0, 3, 3, 5, 0, 2], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation2909 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation2909 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 3, 3, 5, 1], [5, 2, 2, 0, 2, 4], [0, 4, 0, 0, 5, 3], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation2939 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation2939 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 1, 5, 4, 4], [2, 3, 2, 3, 3, 4], [0, 1, 2, 3, 4, 5], [0, 4, 2, 0, 5, 0], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation2946 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation2946 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 4, 4, 3, 3, 3], [0, 1, 2, 3, 4, 5], [1, 4, 4, 3, 4, 3], [0, 1, 2, 3, 4, 5], [1, 1, 1, 0, 5, 5], [1, 1, 2, 2, 3, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation3050 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation3050 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 1, 3, 3, 3], [2, 4, 5, 3, 4, 4], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 5, 1, 0, 0, 2], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation3253 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation3253 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 3, 5, 3, 2], [5, 2, 3, 5, 3, 4], [5, 4, 3, 3, 3, 4], [0, 4, 4, 0, 5, 1], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation3456 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation3456 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 3, 5, 2, 4], [2, 4, 3, 5, 4, 4], [0, 1, 2, 3, 4, 5], [2, 4, 2, 1, 2, 4], [0, 5, 3, 5, 0, 2], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation3659 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation3659 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 4, 1, 4, 3], [5, 2, 2, 4, 4, 2], [3, 5, 0, 4, 0, 4], [5, 2, 4, 1, 1, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation3862 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation3862 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 5, 2, 5, 5], [3, 2, 2, 2, 0, 5], [3, 3, 4, 3, 4, 0], [0, 1, 2, 3, 4, 5], [0, 1, 5, 2, 0, 0], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation4065 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation4065 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 1, 2, 3, 3], [2, 4, 5, 0, 4, 4], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 5, 1, 0, 0, 3], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation411 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation411 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 3, 3, 4, 1], [5, 2, 2, 3, 2, 4], [0, 4, 0, 0, 3, 4], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation4284 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation4284 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 3, 5, 4, 1], [5, 2, 2, 4, 2, 3], [0, 4, 0, 0, 4, 3], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation4291 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation4291 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 2, 2, 3, 2, 3], [0, 0, 0, 4, 2, 4], [0, 1, 2, 3, 4, 5], [5, 1, 0, 1, 1, 4], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation4307 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation4307 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 3, 3, 3, 1], [5, 2, 2, 0, 2, 4], [0, 4, 0, 0, 3, 4], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation4316 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation4316 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 5, 2, 4, 4, 4], [0, 1, 2, 3, 4, 5], [1, 3, 3, 3, 0, 4], [0, 1, 1, 0, 0, 3], [0, 1, 2, 3, 4, 5], [1, 4, 2, 0, 0, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation4320 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation4320 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 3, 1, 3, 4, 2], [2, 3, 4, 3, 5, 2], [0, 1, 2, 3, 4, 5], [2, 4, 2, 5, 5, 5], [0, 1, 2, 3, 4, 5], [1, 4, 1, 4, 2, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation4351 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation4351 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 3, 3, 4, 1], [5, 2, 2, 3, 2, 4], [0, 4, 0, 0, 5, 3], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation4380 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation4380 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 5, 2, 5, 5], [3, 2, 2, 4, 5, 5], [3, 3, 4, 3, 4, 0], [0, 1, 2, 3, 4, 5], [1, 3, 5, 3, 0, 0], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation4599 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation4599 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 4, 2, 4, 4], [3, 2, 2, 5, 4, 4], [3, 3, 5, 4, 0, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [1, 3, 4, 3, 0, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation4606 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation4606 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 3, 2, 3, 1, 2], [0, 0, 4, 0, 4, 3], [5, 1, 1, 4, 1, 3], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation4622 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation4622 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 4, 2, 3, 3, 2], [0, 0, 3, 3, 0, 4], [5, 1, 1, 1, 3, 4], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation4631 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation4631 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 3, 2, 3, 4, 4], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [1, 1, 5, 5, 2, 5], [0, 1, 2, 3, 4, 5], [0, 3, 1, 2, 0, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation4635 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation4635 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 1, 5, 4, 2], [2, 3, 4, 3, 3, 2], [0, 1, 2, 3, 4, 5], [0, 4, 5, 0, 4, 0], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation4666 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation4666 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 4, 3, 5, 1], [5, 2, 2, 2, 0, 4], [0, 3, 0, 3, 0, 4], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation47 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation47 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 2, 4, 1, 5], [4, 2, 2, 4, 5, 3], [0, 5, 3, 3, 1, 3], [0, 5, 5, 0, 1, 4], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation614 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation614 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 1, 4, 4, 5], [2, 3, 5, 3, 0, 3], [0, 1, 2, 3, 4, 5], [0, 5, 2, 0, 0, 4], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation817 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation817 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 1, 3, 3, 3, 1], [5, 2, 2, 0, 2, 3], [0, 4, 0, 0, 4, 3], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation2994_not_implies_Equation99 : ∃ (G: Type) (_: Magma G), Equation2994 G ∧ ¬ Equation99 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 4, 3, 5, 5, 5], [2, 4, 4, 5, 4, 5], [0, 1, 2, 3, 4, 5], [2, 1, 2, 1, 5, 0], [2, 2, 2, 3, 3, 0], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3059_not_implies_Equation3319 : ∃ (G: Type) (_: Magma G), Equation3059 G ∧ ¬ Equation3319 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 4, 0], [3, 3, 3, 3, 3], [2, 4, 2, 0, 2], [1, 1, 1, 1, 1], [4, 0, 4, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3097_not_implies_Equation3456 : ∃ (G: Type) (_: Magma G), Equation3097 G ∧ ¬ Equation3456 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 1, 3, 3, 3], [2, 2, 2, 2, 2], [4, 4, 4, 4, 4], [2, 2, 2, 2, 2], [0, 0, 0, 0, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3097_not_implies_Equation4631 : ∃ (G: Type) (_: Magma G), Equation3097 G ∧ ¬ Equation4631 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 3, 4, 3, 4, 4], [0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1], [2, 5, 2, 5, 5, 5], [5, 5, 2, 5, 5, 5], [1, 1, 1, 1, 1, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3102_not_implies_Equation1238 : ∃ (G: Type) (_: Magma G), Equation3102 G ∧ ¬ Equation1238 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 4, 1, 4, 4], [2, 1, 2, 3, 3], [3, 4, 2, 4, 3], [4, 4, 4, 3, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3102_not_implies_Equation2087 : ∃ (G: Type) (_: Magma G), Equation3102 G ∧ ¬ Equation2087 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 1, 4, 1], [2, 1, 2, 4, 4], [3, 1, 2, 4, 1], [4, 2, 0, 3, 4], [0, 2, 1, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3102_not_implies_Equation2696 : ∃ (G: Type) (_: Magma G), Equation3102 G ∧ ¬ Equation2696 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 4, 4, 2, 3], [2, 1, 2, 4, 2], [3, 4, 2, 3, 4], [4, 4, 1, 3, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3102_not_implies_Equation2899 : ∃ (G: Type) (_: Magma G), Equation3102 G ∧ ¬ Equation2899 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 1, 2, 1, 4], [2, 1, 2, 3, 0], [3, 0, 2, 4, 0], [4, 1, 0, 3, 0], [0, 0, 0, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3102_not_implies_Equation3065 : ∃ (G: Type) (_: Magma G), Equation3102 G ∧ ¬ Equation3065 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 4, 2, 2], [4, 1, 4, 4, 4], [3, 1, 2, 3, 4], [1, 1, 4, 3, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3102_not_implies_Equation3139 : ∃ (G: Type) (_: Magma G), Equation3102 G ∧ ¬ Equation3139 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 1, 2, 4, 3], [2, 1, 0, 2, 4], [3, 0, 2, 3, 3], [4, 0, 4, 3, 4], [0, 0, 0, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3102_not_implies_Equation4080 : ∃ (G: Type) (_: Magma G), Equation3102 G ∧ ¬ Equation4080 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 1, 4, 1, 2], [2, 1, 4, 3, 4], [3, 1, 2, 4, 4], [4, 4, 4, 3, 4], [0, 0, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3108_not_implies_Equation2716 : ∃ (G: Type) (_: Magma G), Equation3108 G ∧ ¬ Equation2716 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 3, 4, 3, 4], [3, 1, 2, 3, 4], [4, 1, 2, 1, 4], [0, 1, 1, 3, 1], [0, 1, 2, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3108_not_implies_Equation2778 : ∃ (G: Type) (_: Magma G), Equation3108 G ∧ ¬ Equation2778 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 1, 4, 3, 4], [0, 1, 3, 3, 4], [3, 4, 2, 3, 4], [0, 1, 2, 3, 2], [0, 1, 2, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3108_not_implies_Equation3803 : ∃ (G: Type) (_: Magma G), Equation3108 G ∧ ¬ Equation3803 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 3, 2, 3, 4], [4, 1, 4, 3, 4], [0, 4, 2, 0, 4], [0, 1, 0, 3, 1], [0, 1, 2, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation1035 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation1035 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 4, 2, 3, 4], [2, 1, 2, 2, 3], [3, 4, 2, 0, 0], [0, 4, 0, 3, 4], [3, 1, 1, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation1248 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation1248 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 4, 4, 3, 4], [2, 1, 4, 0, 2], [3, 4, 2, 0, 4], [0, 4, 4, 3, 4], [3, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation1478 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation1478 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 3, 3, 2, 2], [2, 1, 2, 2, 4], [4, 3, 2, 3, 4], [4, 1, 2, 3, 2], [0, 3, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation1634 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation1634 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 2, 3, 3], [2, 1, 2, 3, 3], [3, 4, 2, 3, 4], [0, 4, 0, 3, 4], [3, 1, 1, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation1681 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation1681 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 3, 2, 4, 3], [2, 1, 2, 4, 4], [4, 3, 2, 4, 3], [0, 1, 1, 3, 4], [0, 3, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation1691 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation1691 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 4, 4, 4, 3], [2, 1, 2, 4, 4], [3, 4, 2, 4, 3], [0, 4, 4, 3, 4], [3, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation1884 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation1884 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 4, 2, 2, 2], [2, 1, 2, 2, 4], [3, 4, 2, 3, 4], [0, 0, 0, 3, 2], [0, 1, 2, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation2124 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation2124 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 4, 4, 4, 4], [2, 1, 2, 4, 3], [3, 4, 2, 4, 3], [0, 4, 2, 3, 4], [3, 1, 1, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation2290 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation2290 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 3, 2, 3, 2], [2, 1, 4, 3, 4], [4, 3, 2, 4, 4], [0, 1, 0, 3, 4], [0, 3, 0, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation2456 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation2456 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 4, 2, 4, 4], [2, 1, 2, 3, 2], [3, 4, 2, 4, 4], [0, 4, 0, 3, 0], [3, 1, 1, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation2493 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation2493 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 3, 3, 3, 3], [2, 1, 2, 3, 3], [4, 3, 2, 0, 3], [4, 1, 2, 3, 4], [0, 3, 3, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation2530 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation2530 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 4, 2, 2, 3], [2, 1, 2, 2, 2], [3, 4, 2, 3, 4], [0, 4, 0, 3, 4], [0, 1, 2, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation2706 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation2706 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 4, 2, 2, 3], [2, 1, 2, 3, 4], [3, 4, 2, 3, 4], [0, 4, 0, 3, 4], [0, 1, 0, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation2733 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation2733 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 4, 4, 3, 3], [2, 1, 2, 0, 4], [3, 4, 2, 0, 3], [0, 4, 4, 3, 4], [0, 1, 2, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation280 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation280 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 4, 3, 3, 4], [2, 1, 2, 0, 2], [3, 4, 2, 0, 4], [0, 4, 2, 3, 2], [0, 1, 1, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation2909 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation2909 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 2, 1, 1], [2, 1, 3, 3, 4], [0, 1, 2, 1, 1], [4, 1, 2, 3, 1], [2, 2, 2, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation2936 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation2936 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 4, 2, 1, 4], [2, 1, 3, 3, 0], [0, 4, 2, 1, 0], [4, 4, 2, 3, 4], [2, 1, 0, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation2946 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation2946 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 3, 3, 3, 3], [2, 1, 3, 2, 3], [4, 3, 2, 3, 3], [4, 1, 2, 3, 4], [0, 3, 3, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation3075 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation3075 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 2, 3, 3], [3, 1, 0, 0, 0], [0, 1, 2, 0, 3], [4, 2, 0, 3, 4], [0, 0, 0, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation3149 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation3149 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 4, 3, 3, 3], [2, 1, 3, 2, 3], [3, 4, 2, 3, 3], [0, 4, 2, 3, 4], [0, 1, 2, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation3461 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation3461 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 4, 4, 3, 4], [2, 1, 4, 0, 0], [3, 4, 2, 4, 0], [0, 4, 2, 3, 0], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation3512 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation3512 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 1, 3, 3], [4, 1, 2, 3, 3], [4, 3, 2, 1, 3], [4, 1, 1, 3, 4], [0, 3, 1, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation3674 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation3674 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 4, 2, 2, 2], [2, 1, 2, 2, 4], [3, 4, 2, 3, 4], [0, 0, 0, 3, 2], [0, 1, 1, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation3877 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation3877 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 2, 4, 2], [2, 1, 2, 4, 4], [3, 4, 2, 4, 4], [0, 4, 0, 3, 4], [3, 1, 1, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation4090 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation4090 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 3, 4, 3, 3], [2, 1, 4, 2, 3], [4, 3, 2, 3, 3], [4, 1, 4, 3, 4], [0, 3, 2, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation4155 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation4155 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 2, 2, 3], [3, 1, 0, 3, 3], [0, 1, 2, 3, 3], [4, 2, 0, 3, 4], [0, 0, 0, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation4666 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation4666 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 3, 3, 2, 1], [2, 1, 3, 2, 4], [0, 4, 2, 3, 1], [2, 4, 2, 3, 1], [2, 1, 3, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation619 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation619 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 4, 4, 2, 4], [2, 1, 4, 2, 4], [3, 4, 2, 3, 3], [0, 4, 4, 3, 4], [3, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3122_not_implies_Equation832 : ∃ (G: Type) (_: Magma G), Equation3122 G ∧ ¬ Equation832 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 4, 2, 3, 4], [2, 1, 2, 0, 0], [3, 4, 2, 0, 0], [0, 4, 0, 3, 4], [0, 1, 0, 0, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation313_not_implies_Equation3272 : ∃ (G: Type) (_: Magma G), Equation313 G ∧ ¬ Equation3272 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 5, 3, 2, 4, 2], [5, 2, 2, 4, 3, 0], [3, 1, 2, 0, 3, 0], [2, 4, 0, 3, 2, 5], [0, 5, 3, 2, 0, 2], [2, 4, 0, 3, 2, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3145_not_implies_Equation2530 : ∃ (G: Type) (_: Magma G), Equation3145 G ∧ ¬ Equation2530 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 4, 4, 4, 4], [2, 4, 2, 3, 4], [3, 1, 4, 3, 4], [4, 1, 2, 4, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3180_not_implies_Equation2290 : ∃ (G: Type) (_: Magma G), Equation3180 G ∧ ¬ Equation2290 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 1, 2, 2, 4], [0, 4, 3, 3, 4], [0, 4, 4, 3, 4], [4, 1, 2, 4, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3180_not_implies_Equation2303 : ∃ (G: Type) (_: Magma G), Equation3180 G ∧ ¬ Equation2303 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 1, 3, 3, 4], [0, 2, 2, 2, 4], [4, 1, 4, 3, 4], [0, 4, 2, 4, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3180_not_implies_Equation2327 : ∃ (G: Type) (_: Magma G), Equation3180 G ∧ ¬ Equation2327 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 1, 2, 2, 4], [0, 4, 3, 3, 4], [0, 4, 4, 3, 4], [4, 1, 2, 4, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3180_not_implies_Equation2530 : ∃ (G: Type) (_: Magma G), Equation3180 G ∧ ¬ Equation2530 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 4, 4, 4, 4], [2, 4, 2, 2, 4], [3, 1, 4, 3, 4], [2, 4, 2, 4, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3180_not_implies_Equation2659 : ∃ (G: Type) (_: Magma G), Equation3180 G ∧ ¬ Equation2659 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 1, 2, 4, 4], [0, 4, 3, 3, 4], [0, 4, 4, 3, 4], [4, 1, 2, 4, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3180_not_implies_Equation2696 : ∃ (G: Type) (_: Magma G), Equation3180 G ∧ ¬ Equation2696 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 3, 3, 3, 3, 5], [2, 5, 2, 2, 2, 5], [1, 1, 5, 1, 1, 5], [0, 4, 4, 5, 4, 5], [5, 3, 3, 3, 5, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3180_not_implies_Equation2733 : ∃ (G: Type) (_: Magma G), Equation3180 G ∧ ¬ Equation2733 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 3, 2, 3, 5, 5], [4, 2, 2, 3, 4, 5], [0, 1, 5, 4, 4, 5], [0, 1, 5, 5, 4, 5], [1, 1, 2, 3, 5, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3180_not_implies_Equation2736 : ∃ (G: Type) (_: Magma G), Equation3180 G ∧ ¬ Equation2736 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 2, 4, 4], [3, 2, 2, 3, 4], [0, 1, 3, 3, 4], [1, 1, 2, 4, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3180_not_implies_Equation3078 : ∃ (G: Type) (_: Magma G), Equation3180 G ∧ ¬ Equation3078 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 2, 2, 2, 2], [3, 3, 2, 3, 2], [0, 1, 2, 3, 4], [4, 1, 2, 2, 4], [3, 2, 2, 3, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3180_not_implies_Equation3464 : ∃ (G: Type) (_: Magma G), Equation3180 G ∧ ¬ Equation3464 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 1, 2, 4, 4], [0, 3, 4, 3, 4], [0, 4, 4, 3, 4], [4, 1, 2, 4, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3180_not_implies_Equation4165 : ∃ (G: Type) (_: Magma G), Equation3180 G ∧ ¬ Equation4165 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[5, 2, 2, 5, 5, 5], [3, 3, 2, 3, 5, 5], [0, 1, 5, 3, 4, 5], [4, 1, 2, 5, 4, 5], [3, 5, 2, 3, 2, 5], [0, 1, 2, 3, 4, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3197_not_implies_Equation2644 : ∃ (G: Type) (_: Magma G), Equation3197 G ∧ ¬ Equation2644 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 3, 3, 1, 3], [4, 0, 4, 0, 4], [0, 1, 2, 3, 4], [4, 2, 2, 2, 4], [2, 3, 2, 3, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3197_not_implies_Equation3456 : ∃ (G: Type) (_: Magma G), Equation3197 G ∧ ¬ Equation3456 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 1, 3, 1, 1], [2, 4, 2, 0, 4], [4, 1, 4, 3, 4], [2, 4, 2, 4, 4], [0, 1, 2, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3270_not_implies_Equation3255 : ∃ (G: Type) (_: Magma G), Equation3270 G ∧ ¬ Equation3255 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 1, 3, 4, 1], [2, 1, 1, 1, 1], [2, 1, 1, 1, 1], [1, 1, 1, 1, 1], [4, 1, 1, 1, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3270_not_implies_Equation3279 : ∃ (G: Type) (_: Magma G), Equation3270 G ∧ ¬ Equation3279 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 3, 2, 2, 2], [4, 2, 2, 0, 2], [1, 2, 2, 2, 2], [2, 2, 2, 2, 2], [2, 2, 2, 2, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3295_not_implies_Equation3255 : ∃ (G: Type) (_: Magma G), Equation3295 G ∧ ¬ Equation3255 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 3, 2, 4, 2], [1, 2, 2, 2, 2], [3, 3, 2, 2, 2], [3, 3, 2, 2, 2], [2, 4, 2, 2, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3295_not_implies_Equation3261 : ∃ (G: Type) (_: Magma G), Equation3295 G ∧ ¬ Equation3261 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 1, 4, 4, 1], [2, 1, 3, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 0], [1, 1, 1, 1, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3295_not_implies_Equation3269 : ∃ (G: Type) (_: Magma G), Equation3295 G ∧ ¬ Equation3269 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 3, 2, 4, 2], [2, 2, 2, 0, 0], [2, 2, 2, 2, 2], [2, 2, 2, 2, 2], [2, 2, 2, 2, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3295_not_implies_Equation3279 : ∃ (G: Type) (_: Magma G), Equation3295 G ∧ ¬ Equation3279 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 0, 0], [0, 0, 3, 4, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3321_not_implies_Equation3256 : ∃ (G: Type) (_: Magma G), Equation3321 G ∧ ¬ Equation3256 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 3, 2, 0, 0], [4, 1, 1, 4, 1], [2, 4, 2, 2, 2], [4, 3, 4, 3, 3], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3321_not_implies_Equation3316 : ∃ (G: Type) (_: Magma G), Equation3321 G ∧ ¬ Equation3316 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 0, 0, 4], [3, 1, 3, 1, 1], [3, 2, 2, 2, 3], [3, 3, 3, 3, 3], [4, 3, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3321_not_implies_Equation3319 : ∃ (G: Type) (_: Magma G), Equation3321 G ∧ ¬ Equation3319 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[0, 2, 0, 0, 2], [4, 3, 1, 3, 1], [2, 2, 2, 2, 2], [2, 3, 3, 3, 3], [4, 2, 4, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3321_not_implies_Equation4314 : ∃ (G: Type) (_: Magma G), Equation3321 G ∧ ¬ Equation4314 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 4, 0, 3, 0], [2, 1, 1, 1, 2], [2, 2, 2, 2, 2], [3, 2, 3, 3, 3], [2, 4, 4, 2, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3342_not_implies_Equation3319 : ∃ (G: Type) (_: Magma G), Equation3342 G ∧ ¬ Equation3319 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[5, 1, 2, 0, 5, 4], [2, 0, 0, 3, 1, 5], [1, 0, 0, 5, 2, 3], [4, 5, 3, 1, 0, 1], [5, 2, 1, 4, 5, 0], [0, 3, 5, 1, 4, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3342_not_implies_Equation3545 : ∃ (G: Type) (_: Magma G), Equation3342 G ∧ ¬ Equation3545 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 2, 1, 4, 3, 0], [1, 4, 4, 3, 2, 5], [2, 4, 4, 5, 1, 3], [0, 5, 3, 1, 4, 1], [3, 1, 2, 0, 3, 4], [4, 3, 5, 1, 0, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3342_not_implies_Equation3862 : ∃ (G: Type) (_: Magma G), Equation3342 G ∧ ¬ Equation3862 G :=
  ⟨Fin 9, ⟨memoFinOp fun x y => [[1, 2, 1, 0, 6, 4, 5, 8, 3], [0, 4, 2, 4, 3, 1, 7, 7, 8], [3, 8, 1, 2, 5, 6, 4, 0, 1], [8, 7, 0, 4, 7, 3, 1, 4, 2], [4, 1, 6, 3, 8, 8, 4, 7, 5], [5, 7, 4, 1, 4, 8, 8, 3, 6], [6, 3, 5, 7, 8, 4, 8, 1, 4], [2, 4, 8, 7, 1, 7, 3, 4, 0], [1, 0, 3, 8, 4, 5, 6, 2, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3342_not_implies_Equation4167 : ∃ (G: Type) (_: Magma G), Equation3342 G ∧ ¬ Equation4167 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[4, 2, 1, 4, 3, 0], [1, 3, 3, 2, 4, 5], [2, 3, 3, 1, 5, 4], [4, 1, 2, 4, 0, 3], [0, 5, 4, 3, 1, 1], [3, 4, 5, 0, 1, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3342_not_implies_Equation4283 : ∃ (G: Type) (_: Magma G), Equation3342 G ∧ ¬ Equation4283 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 1, 2, 4, 3, 0], [2, 0, 0, 3, 1, 5], [1, 0, 0, 5, 2, 3], [0, 5, 3, 1, 4, 1], [3, 2, 1, 0, 3, 4], [4, 3, 5, 1, 0, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation3342_not_implies_Equation4380 : ∃ (G: Type) (_: Magma G), Equation3342 G ∧ ¬ Equation4380 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 1, 5, 0, 3], [0, 3, 2, 4, 3, 1], [1, 0, 1, 3, 2, 5], [3, 1, 5, 2, 4, 2], [2, 3, 0, 1, 3, 4], [5, 4, 3, 2, 1, 2]][x.val]![y.val]!⟩, by decideFin!⟩

