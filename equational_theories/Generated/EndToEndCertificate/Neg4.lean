import equational_theories.Confluence1
import equational_theories.Confluence2
import equational_theories.EndToEnd.Load
import equational_theories.Generated.All4x4Tables.Refutation131
import equational_theories.Generated.All4x4Tables.Refutation133
import equational_theories.Generated.All4x4Tables.Refutation17
import equational_theories.Generated.All4x4Tables.Refutation178
import equational_theories.Generated.All4x4Tables.Refutation2
import equational_theories.Generated.All4x4Tables.Refutation206
import equational_theories.Generated.All4x4Tables.Refutation224
import equational_theories.Generated.All4x4Tables.Refutation239
import equational_theories.Generated.All4x4Tables.Refutation28
import equational_theories.Generated.All4x4Tables.Refutation280
import equational_theories.Generated.All4x4Tables.Refutation313
import equational_theories.Generated.All4x4Tables.Refutation321
import equational_theories.Generated.All4x4Tables.Refutation323
import equational_theories.Generated.All4x4Tables.Refutation33
import equational_theories.Generated.All4x4Tables.Refutation335
import equational_theories.Generated.All4x4Tables.Refutation35
import equational_theories.Generated.All4x4Tables.Refutation353
import equational_theories.Generated.All4x4Tables.Refutation414
import equational_theories.Generated.All4x4Tables.Refutation429
import equational_theories.Generated.All4x4Tables.Refutation432
import equational_theories.Generated.All4x4Tables.Refutation437
import equational_theories.Generated.All4x4Tables.Refutation440
import equational_theories.Generated.All4x4Tables.Refutation441
import equational_theories.Generated.All4x4Tables.Refutation448
import equational_theories.Generated.All4x4Tables.Refutation479
import equational_theories.Generated.All4x4Tables.Refutation493
import equational_theories.Generated.All4x4Tables.Refutation503
import equational_theories.Generated.All4x4Tables.Refutation523
import equational_theories.Generated.All4x4Tables.Refutation528
import equational_theories.Generated.All4x4Tables.Refutation534
import equational_theories.Generated.All4x4Tables.Refutation539
import equational_theories.Generated.All4x4Tables.Refutation560
import equational_theories.Generated.All4x4Tables.Refutation624
import equational_theories.Generated.All4x4Tables.Refutation647
import equational_theories.Generated.All4x4Tables.Refutation66
import equational_theories.Generated.All4x4Tables.Refutation661
import equational_theories.Generated.All4x4Tables.Refutation673
import equational_theories.Generated.All4x4Tables.Refutation676
import equational_theories.Generated.All4x4Tables.Refutation685
import equational_theories.Generated.All4x4Tables.Refutation688
import equational_theories.Generated.All4x4Tables.Refutation690
import equational_theories.Generated.All4x4Tables.Refutation691
import equational_theories.Generated.All4x4Tables.Refutation696
import equational_theories.Generated.All4x4Tables.Refutation697
import equational_theories.Generated.All4x4Tables.Refutation699
import equational_theories.Generated.All4x4Tables.Refutation701
import equational_theories.Generated.All4x4Tables.Refutation703
import equational_theories.Generated.All4x4Tables.Refutation705
import equational_theories.Generated.All4x4Tables.Refutation706
import equational_theories.Generated.All4x4Tables.Refutation714
import equational_theories.Generated.All4x4Tables.Refutation717
import equational_theories.Generated.All4x4Tables.Refutation758
import equational_theories.Generated.All4x4Tables.Refutation786
import equational_theories.Generated.All4x4Tables.Refutation81
import equational_theories.Generated.All4x4Tables.Refutation860
import equational_theories.Generated.All4x4Tables.Refutation878
import equational_theories.Generated.All4x4Tables.Refutation88
import equational_theories.Generated.All4x4Tables.Refutation882
import equational_theories.Generated.All4x4Tables.Refutation883
import equational_theories.Generated.All4x4Tables.Refutation894
import equational_theories.Generated.All4x4Tables.Refutation897
import equational_theories.Generated.All4x4Tables.Refutation904
import equational_theories.Generated.All4x4Tables.Refutation906
import equational_theories.Generated.All4x4Tables.Refutation91
import equational_theories.Generated.All4x4Tables.Refutation912
import equational_theories.Generated.All4x4Tables.Refutation917
import equational_theories.Generated.All4x4Tables.Refutation919
import equational_theories.Generated.All4x4Tables.Refutation930
import equational_theories.Generated.EndToEndCertificate.DualTable
import equational_theories.Generated.Greedy.Eq1112
import equational_theories.Generated.Greedy.Eq1648
import equational_theories.Generated.Greedy.Eq511
import equational_theories.Generated.Greedy.Eq883
import equational_theories.Generated.Greedy.Eq906
import equational_theories.LinearOps
import equational_theories.ManuallyProved.Equation1289
import equational_theories.ManuallyProved.Equation1323
import equational_theories.ManuallyProved.Equation1437
import equational_theories.ManuallyProved.Equation1447
import equational_theories.ManuallyProved.Equation1526
import equational_theories.ManuallyProved.Equation1648
import equational_theories.ManuallyProved.Equation1659
import equational_theories.ManuallyProved.Equation1692
import equational_theories.ManuallyProved.Equation1722
import equational_theories.ManuallyProved.Equation1729
import equational_theories.ManuallyProved.Equation917
import equational_theories.ThreeC2

/-! Generated by equational_theories/Generated/EndToEndCertificate/src/generate.py. Do not edit. -/

/-! `neg` entries 480-599, where an entry is one model witness with its magma.

The data itself is in `json/neg.json`, shared by every shard; the
number after the path is that file's FNV-1a hash, checked on every elaboration
because Lake cannot track a file read during one.

`RArray` indices are *relative*: `.branch p l r` sends index `n` to `l` when
`n < p`, and to `r` at `n - p` (see `RArray.get`). So the numbers after `.branch`
are left-subtree **sizes**, not indices, and every subtree -- including this
shard -- is indexed from 0. Add 480 to get an index into `neg`.
-/

namespace EndToEnd

set_option maxRecDepth 20000 in
def neg4 : RArray NegFact :=
  loadNegTable% "json/neg.json" 6517078778232025408
    entries 480 to 600

end EndToEnd
