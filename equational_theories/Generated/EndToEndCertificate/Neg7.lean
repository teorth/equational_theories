import equational_theories.Asterix
import equational_theories.Confluence2
import equational_theories.EndToEnd.Load
import equational_theories.Generated.All4x4Tables.Refutation11
import equational_theories.Generated.All4x4Tables.Refutation126
import equational_theories.Generated.All4x4Tables.Refutation141
import equational_theories.Generated.All4x4Tables.Refutation168
import equational_theories.Generated.All4x4Tables.Refutation208
import equational_theories.Generated.All4x4Tables.Refutation216
import equational_theories.Generated.All4x4Tables.Refutation267
import equational_theories.Generated.All4x4Tables.Refutation270
import equational_theories.Generated.All4x4Tables.Refutation306
import equational_theories.Generated.All4x4Tables.Refutation333
import equational_theories.Generated.All4x4Tables.Refutation339
import equational_theories.Generated.All4x4Tables.Refutation342
import equational_theories.Generated.All4x4Tables.Refutation349
import equational_theories.Generated.All4x4Tables.Refutation352
import equational_theories.Generated.All4x4Tables.Refutation374
import equational_theories.Generated.All4x4Tables.Refutation376
import equational_theories.Generated.All4x4Tables.Refutation380
import equational_theories.Generated.All4x4Tables.Refutation383
import equational_theories.Generated.All4x4Tables.Refutation399
import equational_theories.Generated.All4x4Tables.Refutation41
import equational_theories.Generated.All4x4Tables.Refutation413
import equational_theories.Generated.All4x4Tables.Refutation417
import equational_theories.Generated.All4x4Tables.Refutation444
import equational_theories.Generated.All4x4Tables.Refutation484
import equational_theories.Generated.All4x4Tables.Refutation491
import equational_theories.Generated.All4x4Tables.Refutation499
import equational_theories.Generated.All4x4Tables.Refutation501
import equational_theories.Generated.All4x4Tables.Refutation515
import equational_theories.Generated.All4x4Tables.Refutation519
import equational_theories.Generated.All4x4Tables.Refutation520
import equational_theories.Generated.All4x4Tables.Refutation526
import equational_theories.Generated.All4x4Tables.Refutation533
import equational_theories.Generated.All4x4Tables.Refutation565
import equational_theories.Generated.All4x4Tables.Refutation586
import equational_theories.Generated.All4x4Tables.Refutation603
import equational_theories.Generated.All4x4Tables.Refutation609
import equational_theories.Generated.All4x4Tables.Refutation625
import equational_theories.Generated.All4x4Tables.Refutation634
import equational_theories.Generated.All4x4Tables.Refutation649
import equational_theories.Generated.All4x4Tables.Refutation655
import equational_theories.Generated.All4x4Tables.Refutation657
import equational_theories.Generated.All4x4Tables.Refutation659
import equational_theories.Generated.All4x4Tables.Refutation665
import equational_theories.Generated.All4x4Tables.Refutation667
import equational_theories.Generated.All4x4Tables.Refutation684
import equational_theories.Generated.All4x4Tables.Refutation712
import equational_theories.Generated.All4x4Tables.Refutation720
import equational_theories.Generated.All4x4Tables.Refutation721
import equational_theories.Generated.All4x4Tables.Refutation722
import equational_theories.Generated.All4x4Tables.Refutation724
import equational_theories.Generated.All4x4Tables.Refutation725
import equational_theories.Generated.All4x4Tables.Refutation728
import equational_theories.Generated.All4x4Tables.Refutation737
import equational_theories.Generated.All4x4Tables.Refutation740
import equational_theories.Generated.All4x4Tables.Refutation753
import equational_theories.Generated.All4x4Tables.Refutation759
import equational_theories.Generated.All4x4Tables.Refutation760
import equational_theories.Generated.All4x4Tables.Refutation761
import equational_theories.Generated.All4x4Tables.Refutation763
import equational_theories.Generated.All4x4Tables.Refutation765
import equational_theories.Generated.All4x4Tables.Refutation771
import equational_theories.Generated.All4x4Tables.Refutation787
import equational_theories.Generated.All4x4Tables.Refutation789
import equational_theories.Generated.All4x4Tables.Refutation825
import equational_theories.Generated.All4x4Tables.Refutation826
import equational_theories.Generated.All4x4Tables.Refutation830
import equational_theories.Generated.All4x4Tables.Refutation854
import equational_theories.Generated.All4x4Tables.Refutation857
import equational_theories.Generated.All4x4Tables.Refutation858
import equational_theories.Generated.All4x4Tables.Refutation859
import equational_theories.Generated.All4x4Tables.Refutation862
import equational_theories.Generated.All4x4Tables.Refutation867
import equational_theories.Generated.All4x4Tables.Refutation893
import equational_theories.Generated.All4x4Tables.Refutation895
import equational_theories.Generated.All4x4Tables.Refutation905
import equational_theories.Generated.All4x4Tables.Refutation921
import equational_theories.Generated.All4x4Tables.Refutation925
import equational_theories.Generated.All4x4Tables.Refutation932
import equational_theories.Generated.All4x4Tables.Refutation939
import equational_theories.Generated.EndToEndCertificate.DualTable
import equational_theories.Generated.Greedy.Eq118
import equational_theories.Generated.Greedy.Eq677
import equational_theories.LinearOps
import equational_theories.ManuallyProved.Equation63
import equational_theories.ManuallyProved.Equation713
import equational_theories.ManuallyProved.Equation73
import equational_theories.ManuallyProved.Equation854
import equational_theories.Obelix

/-! Generated by equational_theories/Generated/EndToEndCertificate/src/generate.py. Do not edit. -/

/-! `neg` entries 840-945, where an entry is one model witness with its magma.

The data itself is in `json/neg.json`, shared by every shard; the
number after the path is that file's FNV-1a hash, checked on every elaboration
because Lake cannot track a file read during one.

`RArray` indices are *relative*: `.branch p l r` sends index `n` to `l` when
`n < p`, and to `r` at `n - p` (see `RArray.get`). So the numbers after `.branch`
are left-subtree **sizes**, not indices, and every subtree -- including this
shard -- is indexed from 0. Add 840 to get an index into `neg`.
-/

namespace EndToEnd

set_option maxRecDepth 20000 in
def neg7 : RArray NegFact :=
  loadNegTable% "json/neg.json" 6517078778232025408
    entries 840 to 946

end EndToEnd
