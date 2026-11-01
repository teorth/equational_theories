import equational_theories.Confluence1
import equational_theories.Confluence2
import equational_theories.Confluence3
import equational_theories.Confluence4
import equational_theories.EndToEnd.Load
import equational_theories.Generated.All4x4Tables.Refutation0
import equational_theories.Generated.All4x4Tables.Refutation118
import equational_theories.Generated.All4x4Tables.Refutation123
import equational_theories.Generated.All4x4Tables.Refutation137
import equational_theories.Generated.All4x4Tables.Refutation203
import equational_theories.Generated.All4x4Tables.Refutation24
import equational_theories.Generated.All4x4Tables.Refutation245
import equational_theories.Generated.All4x4Tables.Refutation249
import equational_theories.Generated.All4x4Tables.Refutation257
import equational_theories.Generated.All4x4Tables.Refutation309
import equational_theories.Generated.All4x4Tables.Refutation311
import equational_theories.Generated.All4x4Tables.Refutation313
import equational_theories.Generated.All4x4Tables.Refutation33
import equational_theories.Generated.All4x4Tables.Refutation336
import equational_theories.Generated.All4x4Tables.Refutation344
import equational_theories.Generated.All4x4Tables.Refutation35
import equational_theories.Generated.All4x4Tables.Refutation362
import equational_theories.Generated.All4x4Tables.Refutation387
import equational_theories.Generated.All4x4Tables.Refutation39
import equational_theories.Generated.All4x4Tables.Refutation412
import equational_theories.Generated.All4x4Tables.Refutation414
import equational_theories.Generated.All4x4Tables.Refutation430
import equational_theories.Generated.All4x4Tables.Refutation435
import equational_theories.Generated.All4x4Tables.Refutation441
import equational_theories.Generated.All4x4Tables.Refutation445
import equational_theories.Generated.All4x4Tables.Refutation476
import equational_theories.Generated.All4x4Tables.Refutation507
import equational_theories.Generated.All4x4Tables.Refutation511
import equational_theories.Generated.All4x4Tables.Refutation516
import equational_theories.Generated.All4x4Tables.Refutation534
import equational_theories.Generated.All4x4Tables.Refutation536
import equational_theories.Generated.All4x4Tables.Refutation537
import equational_theories.Generated.All4x4Tables.Refutation538
import equational_theories.Generated.All4x4Tables.Refutation545
import equational_theories.Generated.All4x4Tables.Refutation561
import equational_theories.Generated.All4x4Tables.Refutation577
import equational_theories.Generated.All4x4Tables.Refutation596
import equational_theories.Generated.All4x4Tables.Refutation620
import equational_theories.Generated.All4x4Tables.Refutation625
import equational_theories.Generated.All4x4Tables.Refutation637
import equational_theories.Generated.All4x4Tables.Refutation64
import equational_theories.Generated.All4x4Tables.Refutation660
import equational_theories.Generated.All4x4Tables.Refutation661
import equational_theories.Generated.All4x4Tables.Refutation673
import equational_theories.Generated.All4x4Tables.Refutation674
import equational_theories.Generated.All4x4Tables.Refutation676
import equational_theories.Generated.All4x4Tables.Refutation688
import equational_theories.Generated.All4x4Tables.Refutation690
import equational_theories.Generated.All4x4Tables.Refutation709
import equational_theories.Generated.All4x4Tables.Refutation785
import equational_theories.Generated.All4x4Tables.Refutation797
import equational_theories.Generated.All4x4Tables.Refutation802
import equational_theories.Generated.All4x4Tables.Refutation804
import equational_theories.Generated.All4x4Tables.Refutation805
import equational_theories.Generated.All4x4Tables.Refutation806
import equational_theories.Generated.All4x4Tables.Refutation807
import equational_theories.Generated.All4x4Tables.Refutation810
import equational_theories.Generated.All4x4Tables.Refutation812
import equational_theories.Generated.All4x4Tables.Refutation838
import equational_theories.Generated.All4x4Tables.Refutation839
import equational_theories.Generated.All4x4Tables.Refutation84
import equational_theories.Generated.All4x4Tables.Refutation882
import equational_theories.Generated.All4x4Tables.Refutation883
import equational_theories.Generated.All4x4Tables.Refutation886
import equational_theories.Generated.All4x4Tables.Refutation888
import equational_theories.Generated.All4x4Tables.Refutation890
import equational_theories.Generated.All4x4Tables.Refutation906
import equational_theories.Generated.All4x4Tables.Refutation92
import equational_theories.Generated.All4x4Tables.Refutation97
import equational_theories.Generated.EndToEndCertificate.DualTable
import equational_theories.Generated.Greedy.Eq707
import equational_theories.Generated.Greedy.Eq883
import equational_theories.ManuallyProved.Equation1117
import equational_theories.ManuallyProved.Equation1323
import equational_theories.ManuallyProved.Equation1526
import equational_theories.ManuallyProved.Equation1692
import equational_theories.ManuallyProved.Equation1729
import equational_theories.ManuallyProved.Equation917
import equational_theories.Subgraph

/-! Generated by equational_theories/Generated/EndToEndCertificate/src/generate.py. Do not edit. -/

/-! `neg` entries 360-479, where an entry is one model witness with its magma.

The data itself is in `json/neg.json`, shared by every shard; the
number after the path is that file's FNV-1a hash, checked on every elaboration
because Lake cannot track a file read during one.

`RArray` indices are *relative*: `.branch p l r` sends index `n` to `l` when
`n < p`, and to `r` at `n - p` (see `RArray.get`). So the numbers after `.branch`
are left-subtree **sizes**, not indices, and every subtree -- including this
shard -- is indexed from 0. Add 360 to get an index into `neg`.
-/

namespace EndToEnd

set_option maxRecDepth 20000 in
def neg3 : RArray NegFact :=
  loadNegTable% "json/neg.json" 6517078778232025408
    entries 360 to 480

end EndToEnd
