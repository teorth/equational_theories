import equational_theories.Asterix
import equational_theories.Confluence1
import equational_theories.Confluence4
import equational_theories.EndToEnd.Load
import equational_theories.Generated.All4x4Tables.Refutation103
import equational_theories.Generated.All4x4Tables.Refutation117
import equational_theories.Generated.All4x4Tables.Refutation12
import equational_theories.Generated.All4x4Tables.Refutation122
import equational_theories.Generated.All4x4Tables.Refutation13
import equational_theories.Generated.All4x4Tables.Refutation138
import equational_theories.Generated.All4x4Tables.Refutation164
import equational_theories.Generated.All4x4Tables.Refutation17
import equational_theories.Generated.All4x4Tables.Refutation174
import equational_theories.Generated.All4x4Tables.Refutation180
import equational_theories.Generated.All4x4Tables.Refutation19
import equational_theories.Generated.All4x4Tables.Refutation213
import equational_theories.Generated.All4x4Tables.Refutation215
import equational_theories.Generated.All4x4Tables.Refutation230
import equational_theories.Generated.All4x4Tables.Refutation254
import equational_theories.Generated.All4x4Tables.Refutation27
import equational_theories.Generated.All4x4Tables.Refutation271
import equational_theories.Generated.All4x4Tables.Refutation28
import equational_theories.Generated.All4x4Tables.Refutation29
import equational_theories.Generated.All4x4Tables.Refutation303
import equational_theories.Generated.All4x4Tables.Refutation317
import equational_theories.Generated.All4x4Tables.Refutation32
import equational_theories.Generated.All4x4Tables.Refutation326
import equational_theories.Generated.All4x4Tables.Refutation340
import equational_theories.Generated.All4x4Tables.Refutation351
import equational_theories.Generated.All4x4Tables.Refutation379
import equational_theories.Generated.All4x4Tables.Refutation382
import equational_theories.Generated.All4x4Tables.Refutation387
import equational_theories.Generated.All4x4Tables.Refutation389
import equational_theories.Generated.All4x4Tables.Refutation42
import equational_theories.Generated.All4x4Tables.Refutation466
import equational_theories.Generated.All4x4Tables.Refutation488
import equational_theories.Generated.All4x4Tables.Refutation5
import equational_theories.Generated.All4x4Tables.Refutation51
import equational_theories.Generated.All4x4Tables.Refutation511
import equational_theories.Generated.All4x4Tables.Refutation523
import equational_theories.Generated.All4x4Tables.Refutation525
import equational_theories.Generated.All4x4Tables.Refutation54
import equational_theories.Generated.All4x4Tables.Refutation540
import equational_theories.Generated.All4x4Tables.Refutation551
import equational_theories.Generated.All4x4Tables.Refutation6
import equational_theories.Generated.All4x4Tables.Refutation645
import equational_theories.Generated.All4x4Tables.Refutation656
import equational_theories.Generated.All4x4Tables.Refutation664
import equational_theories.Generated.All4x4Tables.Refutation674
import equational_theories.Generated.All4x4Tables.Refutation71
import equational_theories.Generated.All4x4Tables.Refutation758
import equational_theories.Generated.All4x4Tables.Refutation778
import equational_theories.Generated.All4x4Tables.Refutation790
import equational_theories.Generated.All4x4Tables.Refutation845
import equational_theories.Generated.All4x4Tables.Refutation846
import equational_theories.Generated.All4x4Tables.Refutation852
import equational_theories.Generated.All4x4Tables.Refutation866
import equational_theories.Generated.All4x4Tables.Refutation905
import equational_theories.Generated.All4x4Tables.Refutation92
import equational_theories.Generated.All4x4Tables.Refutation920
import equational_theories.Generated.All4x4Tables.Refutation95
import equational_theories.Generated.EndToEndCertificate.DualTable
import equational_theories.Generated.FinSearch.theorems.Refutation0
import equational_theories.Generated.FinSearch.theorems.Refutation1
import equational_theories.Generated.FinSearch.theorems.Refutation4
import equational_theories.Generated.FinitePoly.Refutation112
import equational_theories.Generated.FinitePoly.Refutation150
import equational_theories.Generated.FinitePoly.Refutation218
import equational_theories.Generated.FinitePoly.Refutation268
import equational_theories.Generated.FinitePoly.Refutation286
import equational_theories.Generated.FinitePoly.Refutation314
import equational_theories.Generated.FinitePoly.Refutation326
import equational_theories.Generated.FinitePoly.Refutation330
import equational_theories.Generated.FinitePoly.Refutation346
import equational_theories.Generated.FinitePoly.Refutation356
import equational_theories.Generated.FinitePoly.Refutation364
import equational_theories.Generated.FinitePoly.Refutation374
import equational_theories.Generated.FinitePoly.Refutation394
import equational_theories.Generated.FinitePoly.Refutation400
import equational_theories.Generated.FinitePoly.Refutation404
import equational_theories.Generated.FinitePoly.Refutation422
import equational_theories.Generated.FinitePoly.Refutation46
import equational_theories.Generated.FinitePoly.Refutation476
import equational_theories.Generated.FinitePoly.Refutation550
import equational_theories.Generated.FinitePoly.Refutation620
import equational_theories.Generated.FinitePoly.Refutation636
import equational_theories.Generated.FinitePoly.Refutation664
import equational_theories.Generated.FinitePoly.Refutation690
import equational_theories.Generated.FinitePoly.Refutation78
import equational_theories.Generated.Greedy.Eq511
import equational_theories.LinearOps
import equational_theories.ManuallyProved.Equation1076
import equational_theories.ManuallyProved.Equation1289
import equational_theories.ManuallyProved.Equation63

/-! Generated by equational_theories/Generated/EndToEndCertificate/src/generate.py. Do not edit. -/

/-! `neg` entries 0-119, where an entry is one model witness with its magma.

The data itself is in `json/neg.json`, shared by every shard; the
number after the path is that file's FNV-1a hash, checked on every elaboration
because Lake cannot track a file read during one.

`RArray` indices are *relative*: `.branch p l r` sends index `n` to `l` when
`n < p`, and to `r` at `n - p` (see `RArray.get`). So the numbers after `.branch`
are left-subtree **sizes**, not indices, and every subtree -- including this
shard -- is indexed from 0. Add 0 to get an index into `neg`.
-/

namespace EndToEnd

set_option maxRecDepth 20000 in
def neg0 : RArray NegFact :=
  loadNegTable% "json/neg.json" 6517078778232025408
    entries 0 to 120

end EndToEnd
