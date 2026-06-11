
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

namespace MemoFinOp

open Lean Meta Elab Term

elab "jsonify_op_table" str:str :term => do
  return toExpr (("[[" ++ (str.getString.trimAscii |>.replace " " "," |>.replace "\n" "],[" ) ++ "]]")
      |>.replace ",0" "," |>.replace "[0" "[")

/--
modification of `finOpTable` to allow whitespace, instead of comma/bracket, delimited arrays.
This is convenient because it lets us copy-paste the table straight from the ICARM website, e.g.
https://eq677.icarm.cloud/magma/e549b5f8492c9b6b5ad530e3aa4f39c6e23d08645ebd1b36a3c2de2a5a23bac5/table.txt
-/
elab "finOpTable_spaces" str:str :term => do
  let matrix ← parseData
    (("[[" ++ (str.getString.trimAscii |>.replace " " "," |>.replace "\n" "],[" ) ++ "]]")
      |>.replace ",0" "," |>.replace "[0" "[")
  guard <| matrix.length < 256
  guard <| matrix.all (·.length == matrix.length)
  let table := toExpr (matrix.map rowToNat)
  let istable := mkApp2 (mkConst ``IsTable) (mkLit (.natVal matrix.length)) table
  let mv ← mkFreshExprMVar istable
  discard <| withCurrHeartbeats <| Tactic.run mv.mvarId! do Lean.Elab.Tactic.evalTactic (← `(tactic| decide +kernel))
  return mkApp3 (mkConst ``extractWrapper) (mkLit (.natVal matrix.length)) table (← instantiateMVars mv)

end MemoFinOp

/-!
Unique 677 magma on 5 elements, up to isomorphism.
Linear magma over Z/5Z (the prime field F_5): x ◇ y = 2x + 4y (mod 5). --dwrensha
https://eq677.icarm.cloud/magma/e549b5f8492c9b6b5ad530e3aa4f39c6e23d08645ebd1b36a3c2de2a5a23bac5
-/
@[implicit_reducible]
def SmallMagma_677_5 : Magma (Fin 5) where
  op := finOpTable_spaces "
00 04 03 02 01
03 01 04 00 02
01 00 02 04 03
04 02 01 03 00
02 03 00 01 04"

/--
Using the magma to prove some facts. In this case the magma is actually identical to
`Generated/FinitePoly/Refutation420.lean`, so we don't gain any new facts, but this is sort of a
demo usage. This is also the same magma as in `Generated/FinSearch/theorems/Refutation2.lean`,
although that theorem doesn't seem to list all the equations it applies to.
-/
@[equational_result]
theorem SmallMagma_677_5_facts : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G
    [677, 833, 845, 883]
    [2036, 2037, 2038, 2040, 2041, 2043, 2044] :=
  ⟨Fin 5, SmallMagma_677_5, Finite.of_fintype _, by decideFin!⟩

/-!
One of two 677 magmas on 7 elements, up to isomorphism.
Linear magma over Z/7Z (the prime field F_7): x ◇ y = 4x + y (mod 7). --dwrensha
https://eq677.icarm.cloud/magma/7981e2df4cc5c795ad295ab69f55b88db1cecb20c1d1ac4df4d7aa42b92757f1
-/
@[implicit_reducible]
def SmallMagma_677_7_1 : Magma (Fin 7) where
  op := finOpTable_spaces "
05 06 03 01 00 02 04
03 00 06 04 02 01 05
02 04 01 06 05 03 00
04 03 05 02 06 00 01
01 05 04 00 03 06 02
06 02 00 05 01 04 03
00 01 02 03 04 05 06 "

/--
Same as the facts in `Generated/All4x4Tables/Refutation12.lean`, so we just give some abbreviated
facts here.
-/
@[equational_result]
theorem SmallMagma_677_7_1_facts : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G
    [677, 907, 1489, 1516]
    [47, 99, 151, 203] :=
  ⟨Fin 7, SmallMagma_677_7_1, Finite.of_fintype _, by decideFin!⟩

/-!
One of two 677 magmas on 7 elements, up to isomorphism.
Linear magma over Z/7Z (the prime field F_7): x ◇ y = 4x + 3y (mod 7). --dwrensha
https://eq677.icarm.cloud/magma/baf8b55c9a489d3c0ce2405b9167b3a08aada73c1917019843910c3cbab0f48d
-/
@[implicit_reducible]
def SmallMagma_677_7_2 : Magma (Fin 7) where
  op := finOpTable_spaces "
06 03 00 04 02 05 01
05 06 02 00 01 04 03
02 00 06 03 05 01 04
01 02 05 06 04 03 00
00 04 03 01 06 02 05
03 01 04 05 00 06 02
04 05 01 02 03 00 06"

/--
This is the first magma that wasn't already in the Lean project otherwise. All of its individual
implications were already known, but it seems worth recording. The first list (equations it satisfies)
is complete, the latter (equations it refutes) is not.
-/
@[equational_result]
theorem SmallMagma_677_7_2_facts :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G
    [677, 1, 40, 255, 264, 614, 622, 633, 669, 3659, 3662, 3665, 3677, 3684, 3688, 3692, 3700, 3724, 4270, 4293, 4341, 4590, 4622, 4636]
    [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23] :=
  ⟨Fin 7, SmallMagma_677_7_2, Finite.of_fintype _, by decideFin!⟩

/-!
Unique 677 magma on 9 elements, up to isomorphism.
Linear magma over Z/9Z (the prime field F_9): x ◇ y = x + 3y (mod 9). --dwrensha
https://eq677.icarm.cloud/magma/2925dc18176c3a094e546f32ddfbde1b795255106b00f6076737cdc6da05a538
-/
@[implicit_reducible]
def SmallMagma_677_9 : Magma (Fin 9) where
  op := finOpTable_spaces "
01 05 02 06 07 04 08 03 00
06 03 08 00 05 02 04 07 01
08 01 07 04 00 03 05 06 02
07 02 06 05 04 01 00 08 03
02 00 03 08 06 05 07 01 04
03 04 01 07 08 00 06 02 05
00 07 04 01 03 08 02 05 06
05 08 00 03 02 06 01 04 07
04 06 05 02 01 07 03 00 08"

/--
The first list (equations it satisfies) is complete, the latter (equations it refutes) is not.
-/
@[equational_result]
theorem SmallMagma_677_9_facts : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G
    [677, 1, 255, 264, 614, 643, 679, 4293, 4598, 4673]
    [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23] :=
  ⟨Fin 9, SmallMagma_677_9, Finite.of_fintype _, by decideFin!⟩

/-!
One of four 677 magmas on 11 elements, up to isomorphism.
Linear magma over Z/11Z (the prime field F_11): x ◇ y = 6x + 6y (mod 11).
https://eq677.icarm.cloud/magma/9878faa9b07066f62fc077f7c99df5b1f6f079c61c0cd7e7f5bbdb9bc181adbc
-/
@[implicit_reducible]
def SmallMagma_677_11_1 : Magma (Fin 11) where
  op := finOpTable_spaces "00 10 09 07 08 04 05 02 01 06 03
10 01 06 08 05 09 03 04 07 00 02
09 06 02 10 01 03 07 05 00 04 08
07 08 10 03 02 00 04 06 05 01 09
08 05 01 02 04 10 09 00 03 07 06
04 09 03 00 10 05 01 08 06 02 07
05 03 07 04 09 01 06 10 02 08 00
02 04 05 06 00 08 10 07 09 03 01
01 07 00 05 03 06 02 09 08 10 04
06 00 04 01 07 02 08 03 10 09 05
03 02 08 09 06 07 00 01 04 05 10"

/--
This is isomorphic to the magma given in `Generated/All4x4Tables/Refutation41.lean`.
At the moment we just give some abbreviated facts here, but the list there is not complete
either. This is the last 677 magma that appears elsewhere in the Lean repo; all others on
the ICARM database are new.
-/
@[equational_result]
theorem SmallMagma_677_11_1_facts : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G
    [677, 1, 3, 8, 23, 43, 47, 99, 151, 203, 255, 307, 326, 359, 375, 411, 614, 670]
    [2, 4, 5, 6, 7, 9, 10] :=
  ⟨Fin 11, SmallMagma_677_11_1, Finite.of_fintype _, by decideFin!⟩

/-!
One of four 677 magmas on 11 elements, up to isomorphism.
Linear magma over Z/11Z (the prime field F_11): x ◇ y = 5x + 7y (mod 11).
https://eq677.icarm.cloud/magma/abfd8e025ce71b705594dbbe1465dc1c7328d12d30e12d07906d7138f9d583bc
-/
@[implicit_reducible]
def SmallMagma_677_11_2 : Magma (Fin 11) where
  op := finOpTable_spaces "00 02 10 05 07 09 01 08 06 04 03
10 01 09 06 00 04 07 05 03 08 02
03 08 02 10 06 01 05 00 09 07 04
09 07 04 03 10 08 00 06 02 05 01
08 10 05 01 04 06 09 02 07 03 00
04 00 08 02 09 05 10 03 01 06 07
02 05 01 09 03 07 06 10 04 00 08
06 04 03 00 05 02 08 07 10 01 09
01 06 07 04 02 00 03 09 08 10 05
07 03 00 08 01 10 02 04 05 09 06
05 09 06 07 08 03 04 01 00 02 10"
/--
Neither list of facts is complete.
-/
@[equational_result]
theorem SmallMagma_677_11_2_facts : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G
    [677, 1, 3, 8, 23, 47, 99, 151, 203, 255, 271, 307, 326]
    [2, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22] :=
  ⟨Fin 11, SmallMagma_677_11_2, Finite.of_fintype _, by decideFin!⟩

/-!
One of four 677 magmas on 11 elements, up to isomorphism.
Linear magma over Z/11Z (the prime field F_11): x ◇ y = 10x + 2y (mod 11).
https://eq677.icarm.cloud/magma/15fbff501c8b89769a455d502d124c300eee5410941b1d2c6635f2cbb99c8e39
-/
@[implicit_reducible]
def SmallMagma_677_11_3 : Magma (Fin 11) where
  op := finOpTable_spaces "00 10 06 09 01 07 04 08 03 02 05
03 01 10 07 00 02 08 05 09 04 06
05 04 02 10 08 01 03 09 06 00 07
01 06 05 03 10 09 02 04 00 07 08
08 02 07 06 04 10 00 03 05 01 09
02 09 03 08 07 05 10 01 04 06 00
07 03 00 04 09 08 06 10 02 05 01
06 08 04 01 05 00 09 07 10 03 02
04 07 09 05 02 06 01 00 08 10 03
10 05 08 00 06 03 07 02 01 09 04
09 00 01 02 03 04 05 06 07 08 10"

/--
Neither list of facts is complete.
-/
@[equational_result]
theorem SmallMagma_677_11_3_facts : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G
    [677, 1, 3, 8, 23, 26, 47, 99, 102, 151]
    [2, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22] :=
  ⟨Fin 11, SmallMagma_677_11_3, Finite.of_fintype _, by decideFin!⟩

/-!
One of four 677 magmas on 11 elements, up to isomorphism.
Linear magma over Z/11Z (the prime field F_11): x ◇ y = 4x + 8y (mod 11).
https://eq677.icarm.cloud/magma/ca58a4a9ddeee171fc40b5c556a5095e4a2c63eee13557dcdf190986f06d14c3
-/
@[implicit_reducible]
def SmallMagma_677_11_4 : Magma (Fin 11) where
  op := finOpTable_spaces "00 08 10 09 03 07 02 01 06 05 04
10 01 08 02 07 00 04 05 09 06 03
09 04 02 10 05 06 08 03 00 07 01
01 06 05 03 10 08 07 09 04 02 00
07 10 00 06 04 03 09 08 05 01 02
06 02 09 00 01 05 10 04 07 03 08
03 00 07 05 02 04 06 10 01 08 09
02 03 04 08 06 09 01 07 10 00 05
04 07 03 01 09 02 05 00 08 10 06
08 05 01 04 00 10 03 06 02 09 07
05 09 06 07 08 01 00 02 03 04 10"

/--
Neither list of facts is complete.
-/
@[equational_result]
theorem SmallMagma_677_11_4_facts : ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G
    [677, 1, 3, 8, 23, 47, 99, 124, 151, 203, 206, 255, 307, 326, 359, 375]
    [2, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22] :=
  ⟨Fin 11, SmallMagma_677_11_4, Finite.of_fintype _, by decideFin!⟩
