import Mathlib.Tactic
import equational_theories.Equations.All
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

def matrix_834_10 : List (List (Fin 8)) :=
  [[4, 1, 0, 0, 1, 0, 4, 1],
   [3, 1, 1, 2, 2, 1, 1, 1],
   [2, 2, 5, 6, 2, 6, 2, 2],
   [3, 2, 5, 2, 3, 3, 3, 3],
   [3, 3, 4, 4, 3, 4, 4, 3],
   [5, 5, 6, 5, 5, 0, 7, 0],
   [4, 6, 6, 6, 6, 0, 0, 0],
   [4, 7, 7, 7, 1, 4, 4, 1]]

def Magma834_10 : Magma (Fin 8)
  where op := fun x y => (matrix_834_10.get! x.val).get! y.val

-- TODO use calculate_facts to find more places where this magma helps.

@[equational_result]
theorem Equation834_not_implies_Equation10 : ∃ (G: Type) (_: Magma G), Facts G [834] [10] :=
  ⟨Fin 8, Magma834_10, by decide!⟩

-- dual of the above
def Magma_2702_25 : Magma (Fin 8)
  where op := fun x y => (matrix_834_10.get! y.val).get! x.val

@[equational_result]
theorem Equation2702_not_implies_Equation25 : ∃ (G: Type) (_: Magma G), Facts G [2702] [25] :=
  ⟨Fin 8, Magma_2702_25, by decide!⟩


def matrix_1460_3050 : List (List (Fin 8)) :=
  [[7,1,1,7,7,1,7,1],
   [0,6,6,0,0,6,0,6],
   [6,4,4,6,6,4,6,4],
   [5,7,7,5,5,7,5,7],
   [2,5,5,2,2,5,2,5],
   [4,3,3,4,4,3,4,3],
   [1,2,2,1,1,2,1,2],
   [3,0,0,3,3,0,3,0]]

def Magma_1460_3050 : Magma (Fin 8)
  where op := fun x y => (matrix_1460_3050.get! x.val).get! y.val

@[equational_result]
theorem Equation1460_not_implies_Equation3050 : ∃ (G: Type) (_: Magma G), Facts G [1460] [3050] :=
  ⟨Fin 8, Magma_1460_3050, by decide!⟩

-- dual of the above
def Magma_2227_411 : Magma (Fin 8)
  where op := fun x y => (matrix_1460_3050.get! y.val).get! x.val

@[equational_result]
theorem Equation2227_not_implies_Equation411 : ∃ (G: Type) (_: Magma G), Facts G [2227] [411] :=
  ⟨Fin 8, Magma_2227_411, by decide!⟩
