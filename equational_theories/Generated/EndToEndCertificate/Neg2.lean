import equational_theories.Confluence2
import equational_theories.EndToEnd.Load
import equational_theories.Generated.All4x4Tables.Refutation105
import equational_theories.Generated.All4x4Tables.Refutation106
import equational_theories.Generated.All4x4Tables.Refutation126
import equational_theories.Generated.All4x4Tables.Refutation130
import equational_theories.Generated.All4x4Tables.Refutation132
import equational_theories.Generated.All4x4Tables.Refutation136
import equational_theories.Generated.All4x4Tables.Refutation153
import equational_theories.Generated.All4x4Tables.Refutation159
import equational_theories.Generated.All4x4Tables.Refutation163
import equational_theories.Generated.All4x4Tables.Refutation181
import equational_theories.Generated.All4x4Tables.Refutation194
import equational_theories.Generated.All4x4Tables.Refutation195
import equational_theories.Generated.All4x4Tables.Refutation232
import equational_theories.Generated.All4x4Tables.Refutation244
import equational_theories.Generated.All4x4Tables.Refutation272
import equational_theories.Generated.All4x4Tables.Refutation276
import equational_theories.Generated.All4x4Tables.Refutation284
import equational_theories.Generated.All4x4Tables.Refutation296
import equational_theories.Generated.All4x4Tables.Refutation299
import equational_theories.Generated.All4x4Tables.Refutation300
import equational_theories.Generated.All4x4Tables.Refutation307
import equational_theories.Generated.All4x4Tables.Refutation309
import equational_theories.Generated.All4x4Tables.Refutation346
import equational_theories.Generated.All4x4Tables.Refutation355
import equational_theories.Generated.All4x4Tables.Refutation369
import equational_theories.Generated.All4x4Tables.Refutation371
import equational_theories.Generated.All4x4Tables.Refutation377
import equational_theories.Generated.All4x4Tables.Refutation378
import equational_theories.Generated.All4x4Tables.Refutation385
import equational_theories.Generated.All4x4Tables.Refutation389
import equational_theories.Generated.All4x4Tables.Refutation394
import equational_theories.Generated.All4x4Tables.Refutation40
import equational_theories.Generated.All4x4Tables.Refutation417
import equational_theories.Generated.All4x4Tables.Refutation433
import equational_theories.Generated.All4x4Tables.Refutation434
import equational_theories.Generated.All4x4Tables.Refutation443
import equational_theories.Generated.All4x4Tables.Refutation457
import equational_theories.Generated.All4x4Tables.Refutation46
import equational_theories.Generated.All4x4Tables.Refutation462
import equational_theories.Generated.All4x4Tables.Refutation47
import equational_theories.Generated.All4x4Tables.Refutation471
import equational_theories.Generated.All4x4Tables.Refutation492
import equational_theories.Generated.All4x4Tables.Refutation504
import equational_theories.Generated.All4x4Tables.Refutation505
import equational_theories.Generated.All4x4Tables.Refutation510
import equational_theories.Generated.All4x4Tables.Refutation516
import equational_theories.Generated.All4x4Tables.Refutation521
import equational_theories.Generated.All4x4Tables.Refutation537
import equational_theories.Generated.All4x4Tables.Refutation552
import equational_theories.Generated.All4x4Tables.Refutation57
import equational_theories.Generated.All4x4Tables.Refutation579
import equational_theories.Generated.All4x4Tables.Refutation589
import equational_theories.Generated.All4x4Tables.Refutation597
import equational_theories.Generated.All4x4Tables.Refutation598
import equational_theories.Generated.All4x4Tables.Refutation599
import equational_theories.Generated.All4x4Tables.Refutation608
import equational_theories.Generated.All4x4Tables.Refutation618
import equational_theories.Generated.All4x4Tables.Refutation672
import equational_theories.Generated.All4x4Tables.Refutation675
import equational_theories.Generated.All4x4Tables.Refutation716
import equational_theories.Generated.All4x4Tables.Refutation791
import equational_theories.Generated.All4x4Tables.Refutation794
import equational_theories.Generated.All4x4Tables.Refutation799
import equational_theories.Generated.All4x4Tables.Refutation800
import equational_theories.Generated.All4x4Tables.Refutation802
import equational_theories.Generated.All4x4Tables.Refutation806
import equational_theories.Generated.All4x4Tables.Refutation807
import equational_theories.Generated.All4x4Tables.Refutation813
import equational_theories.Generated.All4x4Tables.Refutation815
import equational_theories.Generated.All4x4Tables.Refutation818
import equational_theories.Generated.All4x4Tables.Refutation82
import equational_theories.Generated.All4x4Tables.Refutation820
import equational_theories.Generated.All4x4Tables.Refutation821
import equational_theories.Generated.All4x4Tables.Refutation833
import equational_theories.Generated.All4x4Tables.Refutation834
import equational_theories.Generated.All4x4Tables.Refutation84
import equational_theories.Generated.All4x4Tables.Refutation842
import equational_theories.Generated.All4x4Tables.Refutation881
import equational_theories.Generated.All4x4Tables.Refutation884
import equational_theories.Generated.All4x4Tables.Refutation886
import equational_theories.Generated.All4x4Tables.Refutation922
import equational_theories.Generated.EndToEndCertificate.DualTable
import equational_theories.Generated.FinitePoly.Refutation364
import equational_theories.Generated.FinitePoly.Refutation424
import equational_theories.ManuallyProved.Equation3308
import equational_theories.ManuallyProved.Equation3342

/-! Generated by equational_theories/Generated/EndToEndCertificate/src/generate.py. Do not edit. -/

/-! `neg` entries 240-359, where an entry is one model witness with its magma.

The data itself is in `json/neg.json`, shared by every shard; the
number after the path is that file's FNV-1a hash, checked on every elaboration
because Lake cannot track a file read during one.

`RArray` indices are *relative*: `.branch p l r` sends index `n` to `l` when
`n < p`, and to `r` at `n - p` (see `RArray.get`). So the numbers after `.branch`
are left-subtree **sizes**, not indices, and every subtree -- including this
shard -- is indexed from 0. Add 240 to get an index into `neg`.
-/

namespace EndToEnd

set_option maxRecDepth 20000 in
def neg2 : RArray NegFact :=
  loadNegTable% "json/neg.json" 6517078778232025408
    entries 240 to 360

end EndToEnd
