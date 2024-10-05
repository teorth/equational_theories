import equational_theories.AllEquations
import equational_theories.MemoFinOp
import equational_theories.DecideBang

@[equational_result]
theorem Equation4431_not_implies_Equation4436 : ∃ (G: Type) (_: Magma G), Equation4431 G ∧ ¬ Equation4436 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 4, 3, 4, 4], [2, 4, 4, 2, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4431_not_implies_Equation4442 : ∃ (G: Type) (_: Magma G), Equation4431 G ∧ ¬ Equation4442 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 3, 3, 4, 4], [2, 2, 4, 2, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4431_not_implies_Equation4443 : ∃ (G: Type) (_: Magma G), Equation4431 G ∧ ¬ Equation4443 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 3, 3, 4, 4], [2, 2, 4, 2, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4431_not_implies_Equation4445 : ∃ (G: Type) (_: Magma G), Equation4431 G ∧ ¬ Equation4445 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 3, 3, 4, 4], [2, 3, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4431_not_implies_Equation4470 : ∃ (G: Type) (_: Magma G), Equation4431 G ∧ ¬ Equation4470 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 3, 3, 4, 4], [4, 2, 4, 2, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4431_not_implies_Equation4472 : ∃ (G: Type) (_: Magma G), Equation4431 G ∧ ¬ Equation4472 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 3, 3, 4, 4], [2, 2, 4, 2, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4431_not_implies_Equation4473 : ∃ (G: Type) (_: Magma G), Equation4431 G ∧ ¬ Equation4473 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 4, 3, 4, 4], [3, 2, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4431_not_implies_Equation4479 : ∃ (G: Type) (_: Magma G), Equation4431 G ∧ ¬ Equation4479 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 3, 3, 4, 4], [3, 2, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4431_not_implies_Equation4480 : ∃ (G: Type) (_: Magma G), Equation4431 G ∧ ¬ Equation4480 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 4, 3, 4, 4], [3, 2, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4431_not_implies_Equation4482 : ∃ (G: Type) (_: Magma G), Equation4431 G ∧ ¬ Equation4482 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 3, 3, 4, 4], [2, 2, 4, 2, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation443_not_implies_Equation3862 : ∃ (G: Type) (_: Magma G), Equation443 G ∧ ¬ Equation3862 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 2, 4, 2, 0], [3, 4, 1, 1, 1], [3, 2, 4, 2, 2], [3, 3, 3, 4, 3], [3, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation443_not_implies_Equation817 : ∃ (G: Type) (_: Magma G), Equation443 G ∧ ¬ Equation817 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 3, 0, 2, 3], [4, 0, 1, 4, 2], [4, 3, 2, 2, 2], [1, 3, 3, 2, 3], [4, 0, 4, 4, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4538_not_implies_Equation4396 : ∃ (G: Type) (_: Magma G), Equation4538 G ∧ ¬ Equation4396 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 3, 3], [4, 3, 3, 3, 3], [4, 3, 3, 3, 3], [3, 3, 3, 3, 3], [3, 2, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4538_not_implies_Equation4398 : ∃ (G: Type) (_: Magma G), Equation4538 G ∧ ¬ Equation4398 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 3, 3, 3], [3, 3, 3, 3, 3], [4, 3, 3, 3, 3], [3, 3, 3, 3, 3], [3, 3, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4538_not_implies_Equation4406 : ∃ (G: Type) (_: Magma G), Equation4538 G ∧ ¬ Equation4406 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 3, 3, 3], [4, 3, 3, 3, 3], [3, 3, 3, 3, 3], [3, 3, 3, 3, 3], [3, 2, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4538_not_implies_Equation4408 : ∃ (G: Type) (_: Magma G), Equation4538 G ∧ ¬ Equation4408 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 3, 3], [4, 2, 3, 3, 3], [4, 3, 3, 3, 3], [3, 3, 3, 3, 3], [3, 2, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4538_not_implies_Equation4433 : ∃ (G: Type) (_: Magma G), Equation4538 G ∧ ¬ Equation4433 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 3, 3], [2, 3, 3, 3, 3], [3, 3, 3, 3, 3], [3, 3, 3, 3, 3], [3, 2, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4538_not_implies_Equation4435 : ∃ (G: Type) (_: Magma G), Equation4538 G ∧ ¬ Equation4435 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 4, 3, 3, 3], [2, 4, 3, 3, 3], [3, 4, 3, 3, 3], [3, 3, 3, 3, 3], [2, 3, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4538_not_implies_Equation4443 : ∃ (G: Type) (_: Magma G), Equation4538 G ∧ ¬ Equation4443 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 3, 3, 3, 3], [2, 3, 3, 3, 3], [3, 4, 3, 3, 3], [3, 3, 3, 3, 3], [2, 3, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4538_not_implies_Equation4445 : ∃ (G: Type) (_: Magma G), Equation4538 G ∧ ¬ Equation4445 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 4, 3, 3, 3], [2, 4, 3, 3, 3], [3, 4, 3, 3, 3], [3, 3, 3, 3, 3], [2, 3, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4538_not_implies_Equation4470 : ∃ (G: Type) (_: Magma G), Equation4538 G ∧ ¬ Equation4470 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 2, 3, 3, 3], [3, 2, 3, 3, 3], [4, 3, 3, 3, 3], [3, 3, 3, 3, 3], [3, 2, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4538_not_implies_Equation4472 : ∃ (G: Type) (_: Magma G), Equation4538 G ∧ ¬ Equation4472 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 3, 3, 3], [4, 2, 3, 3, 3], [4, 3, 3, 3, 3], [3, 3, 3, 3, 3], [3, 3, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4538_not_implies_Equation4480 : ∃ (G: Type) (_: Magma G), Equation4538 G ∧ ¬ Equation4480 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 3, 3, 3], [4, 2, 3, 3, 3], [3, 3, 3, 3, 3], [3, 3, 3, 3, 3], [3, 2, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4538_not_implies_Equation4482 : ∃ (G: Type) (_: Magma G), Equation4538 G ∧ ¬ Equation4482 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 3, 3, 3, 3], [4, 2, 3, 3, 3], [4, 3, 3, 3, 3], [3, 3, 3, 3, 3], [3, 2, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4538_not_implies_Equation4597 : ∃ (G: Type) (_: Magma G), Equation4538 G ∧ ¬ Equation4597 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 4, 4, 4, 4], [3, 3, 4, 4, 4], [4, 3, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4538_not_implies_Equation4598 : ∃ (G: Type) (_: Magma G), Equation4538 G ∧ ¬ Equation4598 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 4, 4, 4, 4], [3, 3, 4, 4, 4], [4, 3, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4538_not_implies_Equation4599 : ∃ (G: Type) (_: Magma G), Equation4538 G ∧ ¬ Equation4599 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 4, 4, 4, 4], [3, 3, 4, 4, 4], [4, 3, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4538_not_implies_Equation4605 : ∃ (G: Type) (_: Magma G), Equation4538 G ∧ ¬ Equation4605 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 4, 4, 4, 4], [3, 3, 4, 4, 4], [4, 3, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4538_not_implies_Equation4606 : ∃ (G: Type) (_: Magma G), Equation4538 G ∧ ¬ Equation4606 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 4, 4, 4, 4], [3, 3, 4, 4, 4], [4, 3, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4538_not_implies_Equation4608 : ∃ (G: Type) (_: Magma G), Equation4538 G ∧ ¬ Equation4608 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 4, 4, 4, 4], [3, 3, 4, 4, 4], [4, 3, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4538_not_implies_Equation4622 : ∃ (G: Type) (_: Magma G), Equation4538 G ∧ ¬ Equation4622 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 2, 2, 2, 2], [2, 3, 2, 2, 2], [2, 2, 2, 2, 2], [4, 2, 2, 2, 2], [2, 3, 2, 2, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4538_not_implies_Equation4629 : ∃ (G: Type) (_: Magma G), Equation4538 G ∧ ¬ Equation4629 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 4, 4, 4], [3, 3, 4, 4, 4], [3, 4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4538_not_implies_Equation4631 : ∃ (G: Type) (_: Magma G), Equation4538 G ∧ ¬ Equation4631 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 1, 3, 1, 1], [1, 1, 1, 1, 1], [4, 1, 1, 1, 1], [4, 1, 1, 1, 1], [1, 1, 1, 1, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4538_not_implies_Equation4635 : ∃ (G: Type) (_: Magma G), Equation4538 G ∧ ¬ Equation4635 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 4, 4, 4], [3, 3, 4, 4, 4], [3, 4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4538_not_implies_Equation4636 : ∃ (G: Type) (_: Magma G), Equation4538 G ∧ ¬ Equation4636 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[3, 2, 4, 4, 4], [3, 3, 4, 4, 4], [3, 4, 4, 4, 4], [4, 4, 4, 4, 4], [4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4538_not_implies_Equation4647 : ∃ (G: Type) (_: Magma G), Equation4538 G ∧ ¬ Equation4647 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 2, 2, 2, 2], [3, 2, 2, 2, 2], [2, 2, 2, 2, 2], [2, 4, 2, 2, 2], [2, 2, 2, 2, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4541_not_implies_Equation4283 : ∃ (G: Type) (_: Magma G), Equation4541 G ∧ ¬ Equation4283 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 2, 3, 5, 5, 5], [4, 3, 5, 5, 5, 5], [5, 5, 5, 5, 5, 5], [5, 5, 5, 5, 5, 5], [3, 5, 5, 5, 5, 5], [5, 5, 5, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4541_not_implies_Equation4290 : ∃ (G: Type) (_: Magma G), Equation4541 G ∧ ¬ Equation4290 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[4, 2, 3, 3, 5, 3], [3, 3, 3, 3, 5, 3], [5, 3, 3, 3, 3, 3], [3, 3, 3, 3, 3, 3], [5, 3, 3, 3, 3, 3], [3, 3, 3, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4541_not_implies_Equation4320 : ∃ (G: Type) (_: Magma G), Equation4541 G ∧ ¬ Equation4320 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 5, 2, 2, 2, 2], [2, 4, 2, 4, 2, 2], [2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2], [4, 2, 2, 2, 2, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4541_not_implies_Equation4396 : ∃ (G: Type) (_: Magma G), Equation4541 G ∧ ¬ Equation4396 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 2, 3, 4, 4, 4], [5, 4, 4, 4, 4, 3], [4, 3, 4, 4, 4, 4], [4, 4, 4, 4, 4, 4], [4, 4, 4, 4, 4, 4], [3, 4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4541_not_implies_Equation4398 : ∃ (G: Type) (_: Magma G), Equation4541 G ∧ ¬ Equation4398 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[4, 2, 3, 4, 4, 4], [5, 4, 4, 4, 4, 4], [4, 4, 4, 4, 4, 4], [4, 4, 4, 4, 4, 4], [4, 4, 4, 4, 4, 4], [3, 4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4541_not_implies_Equation4435 : ∃ (G: Type) (_: Magma G), Equation4541 G ∧ ¬ Equation4435 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 4, 3, 5, 3, 5], [2, 4, 5, 5, 5, 5], [3, 3, 5, 5, 5, 5], [5, 5, 5, 5, 5, 5], [5, 5, 5, 5, 5, 5], [5, 5, 5, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4541_not_implies_Equation4442 : ∃ (G: Type) (_: Magma G), Equation4541 G ∧ ¬ Equation4442 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[4, 5, 3, 3, 3, 4], [2, 3, 3, 3, 3, 3], [4, 3, 3, 3, 3, 3], [3, 3, 3, 3, 3, 3], [3, 3, 3, 3, 3, 3], [3, 3, 3, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4541_not_implies_Equation4473 : ∃ (G: Type) (_: Magma G), Equation4541 G ∧ ¬ Equation4473 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[5, 4, 3, 3, 3, 3], [5, 2, 3, 3, 3, 2], [3, 3, 3, 3, 3, 3], [3, 3, 3, 3, 3, 3], [2, 2, 3, 3, 3, 3], [3, 3, 3, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4541_not_implies_Equation4482 : ∃ (G: Type) (_: Magma G), Equation4541 G ∧ ¬ Equation4482 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 5, 3, 3, 3, 4], [2, 2, 3, 3, 3, 4], [4, 3, 3, 3, 3, 3], [3, 3, 3, 3, 3, 3], [3, 3, 3, 3, 3, 3], [3, 3, 3, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4541_not_implies_Equation4598 : ∃ (G: Type) (_: Magma G), Equation4541 G ∧ ¬ Equation4598 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 2, 4, 3, 3, 3], [5, 5, 4, 3, 3, 3], [4, 3, 3, 3, 3, 3], [3, 3, 3, 3, 3, 3], [3, 3, 3, 3, 3, 3], [4, 3, 3, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4541_not_implies_Equation4605 : ∃ (G: Type) (_: Magma G), Equation4541 G ∧ ¬ Equation4605 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 5, 3, 3, 3, 2], [4, 2, 3, 3, 3, 3], [3, 3, 3, 3, 3, 3], [3, 3, 3, 3, 3, 3], [2, 3, 3, 3, 3, 3], [3, 3, 3, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4541_not_implies_Equation4635 : ∃ (G: Type) (_: Magma G), Equation4541 G ∧ ¬ Equation4635 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[5, 2, 4, 4, 4, 4], [3, 3, 4, 4, 4, 3], [3, 4, 4, 4, 4, 4], [4, 4, 4, 4, 4, 4], [4, 4, 4, 4, 4, 4], [4, 4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation458_not_implies_Equation3862 : ∃ (G: Type) (_: Magma G), Equation458 G ∧ ¬ Equation3862 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 2, 4, 2, 0], [1, 2, 4, 2, 0], [3, 2, 4, 2, 0], [3, 2, 4, 2, 0], [3, 2, 4, 2, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation458_not_implies_Equation4316 : ∃ (G: Type) (_: Magma G), Equation458 G ∧ ¬ Equation4316 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 3, 4, 5, 5, 0], [1, 4, 4, 5, 5, 0], [2, 4, 4, 5, 5, 0], [1, 3, 3, 5, 5, 0], [2, 4, 4, 5, 5, 0], [2, 3, 4, 5, 5, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4679_not_implies_Equation4673 : ∃ (G: Type) (_: Magma G), Equation4679 G ∧ ¬ Equation4673 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[7, 3, 1, 3, 4, 3, 3, 3], [5, 3, 5, 4, 4, 4, 4, 3], [7, 6, 1, 4, 4, 3, 3, 6], [4, 4, 4, 4, 4, 4, 4, 4], [4, 4, 4, 4, 4, 4, 4, 4], [4, 4, 3, 4, 4, 4, 4, 4], [3, 4, 3, 4, 4, 4, 4, 4], [5, 4, 5, 4, 4, 4, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4679_not_implies_Equation4677 : ∃ (G: Type) (_: Magma G), Equation4679 G ∧ ¬ Equation4677 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[4, 2, 5, 5, 5, 5, 5, 5], [4, 2, 6, 5, 6, 5, 5, 5], [7, 7, 3, 5, 3, 5, 5, 5], [5, 5, 5, 5, 5, 5, 5, 5], [7, 7, 5, 5, 5, 5, 5, 5], [5, 5, 5, 5, 5, 5, 5, 5], [3, 3, 5, 5, 5, 5, 5, 5], [5, 3, 5, 5, 5, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation4679_not_implies_Equation4684 : ∃ (G: Type) (_: Magma G), Equation4679 G ∧ ¬ Equation4684 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[1, 3, 6, 3, 3, 3, 3, 3], [7, 3, 3, 3, 3, 3, 3, 3], [7, 4, 4, 3, 3, 3, 3, 3], [3, 3, 3, 3, 3, 3, 3, 3], [5, 3, 3, 3, 3, 3, 3, 3], [3, 3, 3, 3, 3, 3, 3, 3], [3, 5, 5, 3, 3, 3, 3, 3], [3, 3, 5, 3, 3, 3, 3, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation510_not_implies_Equation3915 : ∃ (G: Type) (_: Magma G), Equation510 G ∧ ¬ Equation3915 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[2, 1, 3, 5, 4, 0, 6], [2, 1, 3, 5, 4, 0, 6], [2, 1, 3, 5, 4, 0, 6], [2, 4, 3, 5, 6, 0, 1], [2, 1, 3, 5, 4, 0, 6], [2, 4, 3, 5, 6, 0, 1], [2, 1, 3, 5, 4, 0, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation510_not_implies_Equation4118 : ∃ (G: Type) (_: Magma G), Equation510 G ∧ ¬ Equation4118 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 1, 0, 3, 4], [2, 1, 0, 3, 4], [2, 4, 0, 1, 3], [2, 1, 0, 3, 4], [2, 1, 0, 3, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation621_not_implies_Equation3659 : ∃ (G: Type) (_: Magma G), Equation621 G ∧ ¬ Equation3659 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 3, 3, 0, 3], [2, 2, 4, 4, 1], [2, 2, 2, 2, 2], [2, 3, 3, 3, 2], [2, 3, 3, 4, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation626_not_implies_Equation3660 : ∃ (G: Type) (_: Magma G), Equation626 G ∧ ¬ Equation3660 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[2, 0, 1, 1, 2], [3, 3, 4, 4, 1], [3, 3, 2, 2, 2], [2, 2, 3, 3, 2], [4, 3, 0, 0, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation626_not_implies_Equation3862 : ∃ (G: Type) (_: Magma G), Equation626 G ∧ ¬ Equation3862 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 2, 0, 2, 3], [1, 1, 1, 1, 1], [3, 4, 1, 4, 2], [1, 3, 3, 3, 1], [4, 0, 3, 0, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation626_not_implies_Equation4065 : ∃ (G: Type) (_: Magma G), Equation626 G ∧ ¬ Equation4065 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 3, 3, 0, 2], [2, 1, 1, 1, 2], [2, 2, 2, 1, 1], [2, 4, 4, 2, 3], [4, 0, 0, 1, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation633_not_implies_Equation1426 : ∃ (G: Type) (_: Magma G), Equation633 G ∧ ¬ Equation1426 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 2, 4, 1, 0], [2, 1, 3, 2, 4], [3, 4, 2, 0, 1], [1, 2, 4, 1, 3], [4, 3, 1, 4, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation633_not_implies_Equation203 : ∃ (G: Type) (_: Magma G), Equation633 G ∧ ¬ Equation203 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 2, 0, 0, 3], [4, 1, 3, 2, 0], [2, 3, 1, 4, 2], [3, 4, 2, 3, 1], [0, 2, 4, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation645_not_implies_Equation4131 : ∃ (G: Type) (_: Magma G), Equation645 G ∧ ¬ Equation4131 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 2, 5, 5, 0, 5], [4, 1, 2, 1, 4, 1], [4, 3, 2, 3, 4, 2], [4, 3, 2, 3, 4, 3], [4, 3, 2, 3, 4, 4], [0, 5, 5, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation645_not_implies_Equation629 : ∃ (G: Type) (_: Magma G), Equation645 G ∧ ¬ Equation629 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 3, 2, 3, 0, 0], [2, 1, 5, 1, 4, 5], [4, 3, 2, 3, 4, 2], [4, 3, 2, 3, 4, 3], [4, 3, 2, 3, 4, 4], [5, 1, 5, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation645_not_implies_Equation832 : ∃ (G: Type) (_: Magma G), Equation645 G ∧ ¬ Equation832 G :=
  ⟨Fin 8, ⟨memoFinOp fun x y => [[0, 4, 4, 4, 4, 0, 0, 0], [2, 1, 5, 7, 1, 5, 1, 7], [3, 6, 2, 7, 2, 2, 6, 7], [6, 6, 5, 3, 3, 5, 6, 3], [0, 4, 4, 4, 4, 4, 4, 4], [5, 6, 5, 3, 5, 5, 6, 3], [6, 6, 2, 7, 6, 5, 6, 7], [7, 6, 2, 7, 7, 2, 6, 7]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation645_not_implies_Equation835 : ∃ (G: Type) (_: Magma G), Equation645 G ∧ ¬ Equation835 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 4, 2, 0, 4, 0], [2, 1, 5, 5, 1, 5], [3, 4, 2, 3, 4, 2], [3, 4, 2, 3, 4, 3], [3, 4, 2, 3, 4, 0], [5, 1, 5, 5, 1, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation645_not_implies_Equation842 : ∃ (G: Type) (_: Magma G), Equation645 G ∧ ¬ Equation842 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[0, 3, 2, 3, 0, 0], [2, 1, 5, 1, 5, 5], [4, 3, 2, 3, 4, 2], [4, 3, 2, 3, 4, 3], [4, 3, 2, 3, 4, 4], [5, 1, 5, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation645_not_implies_Equation845 : ∃ (G: Type) (_: Magma G), Equation645 G ∧ ¬ Equation845 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[0, 2, 5, 0, 4, 6, 2], [3, 2, 5, 3, 4, 1, 2], [0, 2, 5, 4, 4, 6, 2], [3, 2, 5, 3, 3, 6, 2], [0, 2, 5, 4, 4, 6, 2], [0, 2, 5, 0, 4, 1, 2], [0, 2, 5, 4, 4, 6, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation1020 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation1020 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 0, 0, 1, 0], [1, 3, 1, 5, 5, 1], [1, 2, 2, 5, 1, 2], [5, 3, 3, 0, 0, 3], [2, 2, 4, 3, 0, 4], [5, 4, 5, 0, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation1223 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation1223 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 0, 0, 1, 0], [1, 3, 1, 5, 5, 1], [1, 5, 2, 5, 1, 2], [5, 3, 3, 0, 3, 3], [2, 2, 4, 2, 3, 4], [2, 4, 5, 0, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation1426 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation1426 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 0, 0, 0, 0], [1, 3, 1, 5, 1, 1], [1, 5, 2, 5, 2, 2], [4, 3, 3, 0, 3, 3], [4, 4, 4, 0, 4, 4], [2, 3, 5, 2, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation151 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation151 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 5, 5, 1, 0, 0], [2, 2, 5, 5, 1, 1], [4, 3, 3, 4, 2, 2], [4, 4, 0, 0, 3, 3], [4, 5, 0, 1, 4, 4], [2, 2, 5, 4, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation1629 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation1629 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 5, 0, 0, 0, 0], [1, 2, 4, 1, 1, 1], [3, 2, 0, 2, 2, 2], [5, 3, 0, 3, 3, 3], [2, 2, 4, 4, 4, 4], [1, 3, 3, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation1832 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation1832 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 0, 0, 0, 0], [1, 3, 1, 5, 1, 1], [1, 2, 2, 1, 2, 2], [4, 3, 3, 0, 3, 3], [2, 0, 4, 0, 4, 4], [3, 3, 5, 2, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation203 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation203 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 0, 0, 0, 0], [1, 3, 1, 5, 1, 1], [1, 2, 2, 4, 2, 2], [4, 3, 3, 0, 3, 3], [4, 4, 4, 0, 4, 4], [4, 3, 5, 2, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation2035 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation2035 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 5, 5, 0, 0, 0], [2, 4, 5, 1, 5, 1], [3, 2, 4, 2, 3, 2], [5, 5, 0, 3, 0, 3], [3, 4, 0, 4, 0, 4], [2, 4, 3, 5, 3, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation2238 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation2238 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 0, 0, 0, 0], [1, 3, 1, 5, 5, 1], [1, 5, 2, 2, 1, 2], [5, 3, 3, 0, 5, 3], [2, 2, 4, 2, 0, 4], [2, 4, 5, 4, 2, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation2441 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation2441 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 0, 0, 2, 0], [1, 3, 1, 5, 1, 1], [1, 5, 2, 4, 5, 2], [4, 3, 3, 4, 2, 3], [5, 5, 4, 4, 1, 4], [5, 3, 5, 5, 0, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation255 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation255 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 5, 0, 0, 0, 0], [1, 2, 4, 1, 1, 1], [3, 2, 0, 2, 2, 2], [3, 3, 0, 3, 3, 3], [5, 2, 5, 4, 4, 4], [1, 4, 4, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation2644 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation2644 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 5, 0, 0, 0, 0], [1, 2, 4, 1, 1, 1], [3, 2, 0, 2, 2, 2], [4, 0, 0, 3, 3, 3], [5, 2, 5, 4, 4, 4], [1, 3, 3, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation2847 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation2847 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 0, 0, 0, 0], [1, 4, 1, 1, 5, 1], [1, 3, 2, 2, 3, 2], [3, 3, 3, 3, 0, 3], [3, 4, 4, 4, 0, 4], [4, 4, 5, 5, 3, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation3050 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation3050 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 5, 0, 0, 0, 0], [1, 4, 1, 1, 3, 1], [2, 2, 2, 2, 0, 2], [5, 4, 3, 3, 5, 3], [2, 4, 4, 4, 0, 4], [1, 3, 5, 5, 3, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation3253 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation3253 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 0, 0, 0, 0], [1, 4, 1, 1, 5, 1], [1, 3, 2, 2, 5, 2], [3, 0, 3, 3, 0, 3], [3, 4, 4, 4, 0, 4], [3, 4, 5, 5, 3, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation3456 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation3456 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 0, 0, 0, 0], [1, 4, 1, 1, 5, 1], [1, 5, 2, 2, 3, 2], [3, 2, 3, 3, 0, 3], [3, 4, 4, 4, 0, 4], [2, 4, 5, 5, 2, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation3659 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation3659 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 4, 0, 0, 0, 0], [1, 2, 3, 1, 1, 1], [5, 2, 0, 2, 2, 2], [4, 2, 3, 3, 3, 3], [1, 5, 4, 4, 4, 4], [4, 4, 0, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation3862 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation3862 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 0, 2, 0, 0], [3, 4, 1, 2, 2, 1], [3, 4, 2, 5, 5, 2], [5, 3, 3, 4, 5, 3], [5, 4, 4, 0, 0, 4], [5, 0, 5, 0, 0, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation4065 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation4065 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 5, 5, 0, 0, 0], [2, 2, 4, 4, 1, 1], [2, 2, 3, 4, 2, 2], [5, 5, 3, 0, 3, 3], [3, 3, 3, 4, 4, 4], [1, 4, 4, 1, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation411 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation411 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 0, 0, 0, 0], [1, 3, 1, 5, 1, 1], [1, 4, 2, 2, 2, 2], [4, 3, 3, 0, 3, 3], [4, 0, 4, 0, 4, 4], [2, 3, 5, 2, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation4282 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation4282 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 0, 5, 0, 0, 0], [4, 0, 1, 1, 1, 1], [2, 3, 1, 2, 2, 2], [3, 3, 1, 3, 3, 3], [4, 0, 4, 4, 4, 4], [2, 4, 3, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation4283 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation4283 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 0, 5, 0, 0, 0], [3, 0, 1, 1, 1, 1], [2, 4, 1, 2, 2, 2], [3, 0, 0, 3, 3, 3], [4, 5, 1, 4, 4, 4], [2, 3, 4, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation4284 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation4284 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[4, 1, 3, 0, 3, 0], [2, 2, 3, 1, 1, 1], [5, 2, 4, 2, 5, 2], [4, 2, 5, 3, 5, 3], [4, 5, 4, 4, 1, 4], [3, 3, 0, 5, 1, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation4314 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation4314 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 4, 0, 4, 0, 0], [2, 3, 5, 5, 1, 1], [5, 2, 0, 2, 2, 2], [3, 2, 4, 2, 3, 3], [1, 5, 5, 2, 4, 4], [4, 3, 0, 4, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation4316 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation4316 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 0, 5, 0, 0, 0], [3, 0, 1, 1, 1, 1], [2, 4, 1, 2, 2, 2], [3, 0, 3, 3, 3, 3], [4, 4, 1, 4, 4, 4], [2, 3, 3, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation4341 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation4341 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 0, 5, 0, 0, 0], [1, 1, 4, 1, 1, 1], [2, 2, 4, 2, 1, 2], [3, 3, 0, 3, 0, 3], [3, 4, 4, 4, 0, 4], [2, 5, 1, 5, 3, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation4380 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation4380 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 0, 0, 0, 0], [1, 3, 1, 5, 1, 1], [1, 5, 2, 5, 2, 2], [4, 3, 3, 0, 3, 3], [4, 0, 4, 0, 4, 4], [2, 3, 5, 2, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation4597 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation4597 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 0, 5, 0, 0, 0], [4, 0, 1, 1, 1, 1], [2, 3, 1, 2, 2, 2], [3, 3, 1, 3, 3, 3], [4, 0, 0, 4, 4, 4], [2, 3, 3, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation4598 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation4598 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 2, 4, 4, 0, 0], [2, 2, 5, 0, 1, 1], [3, 2, 3, 4, 2, 2], [5, 5, 3, 1, 3, 3], [3, 4, 3, 5, 4, 4], [4, 2, 4, 0, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation4599 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation4599 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 0, 5, 0, 0, 0], [4, 0, 1, 1, 1, 1], [2, 3, 1, 2, 2, 2], [1, 3, 1, 3, 3, 3], [3, 0, 0, 4, 4, 4], [2, 4, 4, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation4629 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation4629 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 0, 5, 0, 0, 0], [1, 1, 4, 1, 1, 1], [2, 2, 4, 2, 1, 2], [1, 3, 3, 3, 0, 3], [3, 4, 4, 4, 0, 4], [2, 5, 3, 5, 1, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation4631 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation4631 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 3, 3, 0, 0, 3], [2, 2, 3, 1, 1, 1], [4, 2, 5, 2, 2, 4], [5, 2, 4, 3, 3, 4], [4, 3, 0, 4, 4, 0], [4, 4, 5, 5, 5, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation4656 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation4656 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 0, 5, 0, 0, 0], [4, 0, 1, 1, 1, 1], [2, 3, 1, 2, 2, 2], [4, 3, 1, 3, 3, 3], [4, 0, 0, 4, 4, 4], [2, 3, 3, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation615 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation615 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 4, 4, 0, 0, 0], [2, 2, 5, 5, 1, 1], [2, 3, 3, 4, 2, 2], [5, 5, 3, 0, 3, 3], [1, 4, 3, 4, 4, 4], [4, 2, 5, 0, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation619 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation619 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[4, 0, 0, 0, 5, 0], [2, 0, 1, 1, 1, 1], [3, 0, 2, 2, 2, 2], [5, 5, 3, 3, 1, 3], [4, 3, 4, 4, 1, 4], [4, 3, 5, 5, 3, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation620 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation620 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 0, 0, 5, 0, 0], [2, 1, 1, 1, 0, 1], [1, 2, 2, 4, 2, 2], [3, 3, 3, 4, 2, 3], [1, 4, 4, 4, 0, 4], [3, 5, 5, 2, 1, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation622 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation622 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 5, 0, 0, 0, 0], [1, 2, 4, 1, 1, 1], [3, 2, 0, 2, 2, 2], [4, 4, 0, 3, 3, 3], [2, 2, 5, 4, 4, 4], [1, 4, 4, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation623 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation623 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 5, 0, 0, 0, 0], [1, 2, 3, 1, 1, 1], [4, 2, 0, 2, 2, 2], [3, 2, 3, 3, 3, 3], [4, 5, 0, 4, 4, 4], [1, 4, 4, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation629 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation629 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 0, 3, 0, 3, 0], [1, 1, 0, 1, 0, 0], [2, 2, 4, 2, 3, 2], [4, 3, 4, 3, 1, 3], [1, 4, 4, 4, 5, 1], [1, 5, 0, 5, 5, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation630 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation630 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 0, 5, 0, 0, 0], [1, 1, 0, 1, 0, 1], [2, 2, 4, 2, 3, 2], [4, 3, 4, 3, 5, 3], [1, 4, 4, 4, 0, 4], [2, 5, 3, 5, 3, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation632 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation632 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 2, 4, 0, 0, 0], [3, 3, 1, 4, 1, 1], [2, 5, 1, 2, 2, 2], [5, 3, 5, 0, 3, 3], [2, 3, 4, 5, 4, 4], [4, 4, 1, 0, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation633 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation633 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[4, 2, 4, 0, 5, 0], [5, 0, 5, 1, 1, 1], [4, 3, 4, 2, 3, 2], [1, 5, 1, 3, 1, 3], [4, 3, 4, 4, 1, 4], [4, 2, 5, 5, 3, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation639 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation639 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 3, 0, 5, 0, 0], [2, 4, 1, 1, 2, 1], [2, 0, 2, 4, 2, 2], [3, 2, 3, 1, 2, 3], [5, 4, 4, 5, 0, 4], [3, 2, 5, 2, 3, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation642 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation642 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 3, 3, 0, 0, 0], [2, 2, 5, 1, 5, 1], [3, 4, 4, 2, 3, 2], [1, 5, 4, 3, 5, 3], [5, 4, 4, 4, 0, 4], [5, 2, 5, 5, 0, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation817 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation817 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 5, 1, 0, 5, 0], [1, 2, 5, 1, 1, 1], [3, 2, 4, 2, 3, 2], [3, 3, 0, 3, 0, 3], [3, 3, 4, 4, 1, 4], [4, 2, 3, 5, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation646_not_implies_Equation99 : ∃ (G: Type) (_: Magma G), Equation646 G ∧ ¬ Equation99 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 0, 0, 0, 0], [1, 3, 1, 5, 1, 1], [1, 5, 2, 5, 2, 2], [4, 3, 3, 0, 3, 3], [4, 0, 4, 0, 4, 4], [4, 3, 5, 4, 5, 5]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation653_not_implies_Equation4065 : ∃ (G: Type) (_: Magma G), Equation653 G ∧ ¬ Equation4065 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 4, 5, 2, 0, 0], [2, 2, 5, 1, 3, 1], [2, 2, 5, 2, 3, 1], [2, 4, 5, 2, 3, 3], [2, 4, 4, 2, 3, 1], [2, 4, 5, 2, 5, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation653_not_implies_Equation47 : ∃ (G: Type) (_: Magma G), Equation653 G ∧ ¬ Equation47 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[1, 2, 3, 5, 5, 0, 1], [4, 2, 3, 1, 5, 6, 1], [4, 2, 3, 5, 5, 2, 1], [4, 2, 3, 5, 5, 6, 3], [4, 2, 4, 1, 5, 6, 4], [4, 5, 3, 5, 5, 6, 1], [4, 2, 6, 5, 5, 6, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation653_not_implies_Equation817 : ∃ (G: Type) (_: Magma G), Equation653 G ∧ ¬ Equation817 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 4, 3, 0, 0], [1, 2, 3, 1, 0], [2, 2, 3, 1, 0], [2, 4, 3, 1, 3], [2, 4, 4, 1, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation657_not_implies_Equation619 : ∃ (G: Type) (_: Magma G), Equation657 G ∧ ¬ Equation619 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[4, 1, 0, 2, 3], [1, 2, 0, 2, 1], [3, 2, 4, 2, 3], [3, 2, 4, 2, 3], [3, 2, 4, 2, 3]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation65_not_implies_Equation872 : ∃ (G: Type) (_: Magma G), Equation65 G ∧ ¬ Equation872 G :=
  ⟨Fin 7, ⟨memoFinOp fun x y => [[2, 1, 4, 5, 0, 3, 6], [3, 1, 5, 4, 6, 0, 2], [2, 1, 4, 3, 0, 6, 5], [2, 1, 4, 3, 0, 5, 6], [2, 1, 4, 6, 0, 5, 3], [2, 1, 4, 3, 0, 5, 6], [2, 1, 4, 3, 0, 5, 6]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation661_not_implies_Equation4316 : ∃ (G: Type) (_: Magma G), Equation661 G ∧ ¬ Equation4316 G :=
  ⟨Fin 5, ⟨memoFinOp fun x y => [[1, 3, 4, 0, 0], [1, 4, 3, 0, 0], [2, 4, 4, 0, 0], [2, 3, 3, 0, 0], [2, 4, 4, 0, 0]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation690_not_implies_Equation1426 : ∃ (G: Type) (_: Magma G), Equation690 G ∧ ¬ Equation1426 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 0, 5, 3, 4], [1, 4, 3, 5, 0, 2], [5, 4, 0, 1, 3, 2], [1, 2, 0, 5, 3, 4], [5, 4, 0, 1, 3, 2], [1, 4, 3, 5, 0, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation690_not_implies_Equation3862 : ∃ (G: Type) (_: Magma G), Equation690 G ∧ ¬ Equation3862 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 0, 5, 3, 4], [1, 5, 4, 2, 3, 0], [3, 5, 0, 2, 1, 4], [1, 5, 4, 2, 3, 0], [1, 2, 0, 5, 3, 4], [3, 5, 0, 2, 1, 4]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation690_not_implies_Equation4065 : ∃ (G: Type) (_: Magma G), Equation690 G ∧ ¬ Equation4065 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 4, 3, 0, 5, 2], [2, 4, 3, 5, 0, 1], [2, 4, 3, 5, 0, 1], [1, 3, 4, 5, 0, 2], [1, 3, 4, 5, 0, 2], [1, 4, 3, 0, 5, 2]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation690_not_implies_Equation4307 : ∃ (G: Type) (_: Magma G), Equation690 G ∧ ¬ Equation4307 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[3, 1, 5, 4, 0, 2], [3, 2, 5, 4, 0, 1], [3, 2, 5, 4, 0, 1], [3, 5, 2, 4, 0, 1], [3, 2, 1, 4, 0, 5], [3, 2, 5, 4, 0, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation690_not_implies_Equation4320 : ∃ (G: Type) (_: Magma G), Equation690 G ∧ ¬ Equation4320 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[2, 4, 3, 0, 5, 1], [0, 4, 3, 2, 5, 1], [2, 4, 3, 0, 5, 1], [2, 4, 3, 0, 5, 1], [3, 4, 2, 0, 5, 1], [2, 4, 0, 3, 5, 1]][x.val]![y.val]!⟩, by decideFin!⟩

@[equational_result]
theorem Equation690_not_implies_Equation47 : ∃ (G: Type) (_: Magma G), Equation690 G ∧ ¬ Equation47 G :=
  ⟨Fin 6, ⟨memoFinOp fun x y => [[1, 2, 3, 4, 5, 0], [4, 2, 0, 1, 5, 3], [1, 5, 0, 4, 2, 3], [1, 2, 3, 4, 5, 0], [4, 2, 0, 1, 5, 3], [1, 5, 0, 4, 2, 3]][x.val]![y.val]!⟩, by decideFin!⟩

