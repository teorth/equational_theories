import equational_theories.Confluence1
import equational_theories.Confluence2
import equational_theories.Confluence4
import equational_theories.EndToEnd.Load
import equational_theories.Generated.All4x4Tables.Refutation123
import equational_theories.Generated.All4x4Tables.Refutation141
import equational_theories.Generated.All4x4Tables.Refutation16
import equational_theories.Generated.All4x4Tables.Refutation20
import equational_theories.Generated.All4x4Tables.Refutation208
import equational_theories.Generated.All4x4Tables.Refutation215
import equational_theories.Generated.All4x4Tables.Refutation216
import equational_theories.Generated.All4x4Tables.Refutation236
import equational_theories.Generated.All4x4Tables.Refutation269
import equational_theories.Generated.All4x4Tables.Refutation270
import equational_theories.Generated.All4x4Tables.Refutation288
import equational_theories.Generated.All4x4Tables.Refutation294
import equational_theories.Generated.All4x4Tables.Refutation306
import equational_theories.Generated.All4x4Tables.Refutation312
import equational_theories.Generated.All4x4Tables.Refutation32
import equational_theories.Generated.All4x4Tables.Refutation360
import equational_theories.Generated.All4x4Tables.Refutation370
import equational_theories.Generated.All4x4Tables.Refutation373
import equational_theories.Generated.All4x4Tables.Refutation374
import equational_theories.Generated.All4x4Tables.Refutation376
import equational_theories.Generated.All4x4Tables.Refutation382
import equational_theories.Generated.All4x4Tables.Refutation413
import equational_theories.Generated.All4x4Tables.Refutation43
import equational_theories.Generated.All4x4Tables.Refutation440
import equational_theories.Generated.All4x4Tables.Refutation461
import equational_theories.Generated.All4x4Tables.Refutation466
import equational_theories.Generated.All4x4Tables.Refutation474
import equational_theories.Generated.All4x4Tables.Refutation475
import equational_theories.Generated.All4x4Tables.Refutation482
import equational_theories.Generated.All4x4Tables.Refutation483
import equational_theories.Generated.All4x4Tables.Refutation484
import equational_theories.Generated.All4x4Tables.Refutation491
import equational_theories.Generated.All4x4Tables.Refutation501
import equational_theories.Generated.All4x4Tables.Refutation520
import equational_theories.Generated.All4x4Tables.Refutation526
import equational_theories.Generated.All4x4Tables.Refutation530
import equational_theories.Generated.All4x4Tables.Refutation533
import equational_theories.Generated.All4x4Tables.Refutation548
import equational_theories.Generated.All4x4Tables.Refutation55
import equational_theories.Generated.All4x4Tables.Refutation578
import equational_theories.Generated.All4x4Tables.Refutation594
import equational_theories.Generated.All4x4Tables.Refutation595
import equational_theories.Generated.All4x4Tables.Refutation603
import equational_theories.Generated.All4x4Tables.Refutation606
import equational_theories.Generated.All4x4Tables.Refutation634
import equational_theories.Generated.All4x4Tables.Refutation645
import equational_theories.Generated.All4x4Tables.Refutation656
import equational_theories.Generated.All4x4Tables.Refutation669
import equational_theories.Generated.All4x4Tables.Refutation69
import equational_theories.Generated.All4x4Tables.Refutation694
import equational_theories.Generated.All4x4Tables.Refutation696
import equational_theories.Generated.All4x4Tables.Refutation7
import equational_theories.Generated.All4x4Tables.Refutation701
import equational_theories.Generated.All4x4Tables.Refutation712
import equational_theories.Generated.All4x4Tables.Refutation720
import equational_theories.Generated.All4x4Tables.Refutation737
import equational_theories.Generated.All4x4Tables.Refutation753
import equational_theories.Generated.All4x4Tables.Refutation761
import equational_theories.Generated.All4x4Tables.Refutation775
import equational_theories.Generated.All4x4Tables.Refutation777
import equational_theories.Generated.All4x4Tables.Refutation778
import equational_theories.Generated.All4x4Tables.Refutation787
import equational_theories.Generated.All4x4Tables.Refutation789
import equational_theories.Generated.All4x4Tables.Refutation790
import equational_theories.Generated.All4x4Tables.Refutation824
import equational_theories.Generated.All4x4Tables.Refutation830
import equational_theories.Generated.All4x4Tables.Refutation840
import equational_theories.Generated.All4x4Tables.Refutation843
import equational_theories.Generated.All4x4Tables.Refutation845
import equational_theories.Generated.All4x4Tables.Refutation846
import equational_theories.Generated.All4x4Tables.Refutation863
import equational_theories.Generated.All4x4Tables.Refutation880
import equational_theories.Generated.All4x4Tables.Refutation895
import equational_theories.Generated.All4x4Tables.Refutation896
import equational_theories.Generated.All4x4Tables.Refutation909
import equational_theories.Generated.All4x4Tables.Refutation91
import equational_theories.Generated.All4x4Tables.Refutation921
import equational_theories.Generated.All4x4Tables.Refutation925
import equational_theories.Generated.All4x4Tables.Refutation932
import equational_theories.Generated.All4x4Tables.Refutation935
import equational_theories.Generated.EndToEndCertificate.DualTable
import equational_theories.Generated.Greedy.Eq118
import equational_theories.Generated.Greedy.Eq476
import equational_theories.LinearOps
import equational_theories.ManuallyProved.Equation1076
import equational_theories.ManuallyProved.Equation1516
import equational_theories.ManuallyProved.Equation1661
import equational_theories.ManuallyProved.Equation73
import equational_theories.ManuallyProved.Equation854
import equational_theories.Obelix
import equational_theories.ThreeC2

/-! Generated by equational_theories/Generated/EndToEndCertificate/src/generate.py. Do not edit. -/

/-! `neg` entries 600-719, where an entry is one model witness with its magma.

The data itself is in `json/neg.json`, shared by every shard; the
number after the path is that file's FNV-1a hash, checked on every elaboration
because Lake cannot track a file read during one.

`RArray` indices are *relative*: `.branch p l r` sends index `n` to `l` when
`n < p`, and to `r` at `n - p` (see `RArray.get`). So the numbers after `.branch`
are left-subtree **sizes**, not indices, and every subtree -- including this
shard -- is indexed from 0. Add 600 to get an index into `neg`.
-/

namespace EndToEnd

set_option maxRecDepth 20000 in
def neg5 : RArray NegFact :=
  loadNegTable% "json/neg.json" 6517078778232025408
    entries 600 to 720

end EndToEnd
