import Mathlib.Tactic
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import equational_theories.EquationalResult

namespace Z3Counterexamples

/-
Found with the following Z3 spec:
```
(declare-fun op ((_ BitVec 3) (_ BitVec 3)) (_ BitVec 3))

(assert (forall ((x (_ BitVec 3)) (y (_ BitVec 3)) (z (_ BitVec 3)))
                         (= x (op x (op (op y x) (op x z))))))

(declare-const x (_ BitVec 3))
(declare-const y (_ BitVec 3))
(assert (not (= x (op x (op y x)))))

(check-sat)
(get-model)
```
-/

def f_834_10 : Fin 8 → Fin 8 →  Fin 8
| 0b010, 0b101 => ⟨0b110, by omega⟩
| 0b101, 0b110 => ⟨0b111, by omega⟩
| 0b101, 0b101 => ⟨0b000, by omega⟩
| 0b101, 0b100 => ⟨0b101, by omega⟩
| 0b110, 0b110 => ⟨0b000, by omega⟩
| 0b110, 0b101 => ⟨0b000, by omega⟩
| 0b101, 0b010 => ⟨0b110, by omega⟩
| 0b010, 0b010 => ⟨0b101, by omega⟩
| 0b110, 0b010 => ⟨0b110, by omega⟩
| 0b110, 0b111 => ⟨0b000, by omega⟩
| 0b111, 0b100 => ⟨0b001, by omega⟩
| 0b101, 0b000 => ⟨0b101, by omega⟩
| 0b010, 0b111 => ⟨0b010, by omega⟩
| 0b111, 0b010 => ⟨0b111, by omega⟩
| 0b000, 0b100 => ⟨0b001, by omega⟩
| 0b010, 0b100 => ⟨0b010, by omega⟩
| 0b100, 0b111 => ⟨0b011, by omega⟩
| 0b010, 0b011 => ⟨0b110, by omega⟩
| 0b000, 0b010 => ⟨0b000, by omega⟩
| 0b100, 0b100 => ⟨0b011, by omega⟩
| 0b100, 0b110 => ⟨0b100, by omega⟩
| 0b110, 0b001 => ⟨0b110, by omega⟩
| 0b111, 0b000 => ⟨0b100, by omega⟩
| 0b011, 0b100 => ⟨0b011, by omega⟩
| 0b000, 0b000 => ⟨0b100, by omega⟩
| 0b000, 0b101 => ⟨0b000, by omega⟩
| 0b000, 0b111 => ⟨0b001, by omega⟩
| 0b000, 0b110 => ⟨0b100, by omega⟩
| 0b110, 0b100 => ⟨0b110, by omega⟩
| 0b101, 0b001 => ⟨0b101, by omega⟩
| 0b111, 0b001 => ⟨0b111, by omega⟩
| 0b100, 0b001 => ⟨0b011, by omega⟩
| 0b001, 0b100 => ⟨0b010, by omega⟩
| 0b001, 0b001 => ⟨0b001, by omega⟩
| 0b001, 0b110 => ⟨0b001, by omega⟩
| 0b011, 0b001 => ⟨0b010, by omega⟩
| 0b001, 0b101 => ⟨0b001, by omega⟩
| 0b001, 0b111 => ⟨0b001, by omega⟩
| 0b111, 0b110 => ⟨0b100, by omega⟩
| 0b000, 0b001 => ⟨0b001, by omega⟩
| 0b100, 0b010 => ⟨0b100, by omega⟩
| 0b010, 0b000 => ⟨0b010, by omega⟩
| 0b001, 0b010 => ⟨0b001, by omega⟩
| 0b111, 0b101 => ⟨0b100, by omega⟩
| 0b100, 0b000 => ⟨0b011, by omega⟩
| 0b010, 0b001 => ⟨0b010, by omega⟩
| 0b001, 0b000 => ⟨0b011, by omega⟩
| 0b100, 0b011 => ⟨0b100, by omega⟩
| 0b110, 0b000 => ⟨0b100, by omega⟩
| 0b010, 0b110 => ⟨0b010, by omega⟩
| 0b110, 0b011 => ⟨0b110, by omega⟩
| 0b000, 0b011 => ⟨0b000, by omega⟩
| 0b001, 0b011 => ⟨0b010, by omega⟩
| 0b011, 0b010 => ⟨0b101, by omega⟩
| 0b100, 0b101 => ⟨0b100, by omega⟩
| 0b011, 0b111 => ⟨0b011, by omega⟩
| 0b011, 0b011 => ⟨0b010, by omega⟩
| 0b111, 0b011 => ⟨0b111, by omega⟩
| 0b101, 0b111 => ⟨0b000, by omega⟩
| 0b111, 0b111 => ⟨0b001, by omega⟩
| 0b101, 0b011 => ⟨0b101, by omega⟩
| 0b011, 0b000 => ⟨0b011, by omega⟩
| 0b011, 0b101 => ⟨0b011, by omega⟩
| 0b011, 0b110 => ⟨0b011, by omega⟩

@[equational_result]
theorem Equation834_not_implies_Equation10 : ∃ (G: Type) (_: Magma G), Equation834 G ∧ ¬ Equation10 G :=
  ⟨Fin 8, ⟨f_834_10⟩, by decide⟩
