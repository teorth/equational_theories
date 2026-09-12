import equational_theories.Confluence4
import equational_theories.EndToEnd.Load
import equational_theories.Generated.All4x4Tables.Refutation131
import equational_theories.Generated.All4x4Tables.Refutation133
import equational_theories.Generated.All4x4Tables.Refutation168
import equational_theories.Generated.All4x4Tables.Refutation2
import equational_theories.Generated.All4x4Tables.Refutation239
import equational_theories.Generated.All4x4Tables.Refutation269
import equational_theories.Generated.All4x4Tables.Refutation280
import equational_theories.Generated.All4x4Tables.Refutation288
import equational_theories.Generated.All4x4Tables.Refutation326
import equational_theories.Generated.All4x4Tables.Refutation337
import equational_theories.Generated.All4x4Tables.Refutation339
import equational_theories.Generated.All4x4Tables.Refutation342
import equational_theories.Generated.All4x4Tables.Refutation349
import equational_theories.Generated.All4x4Tables.Refutation373
import equational_theories.Generated.All4x4Tables.Refutation379
import equational_theories.Generated.All4x4Tables.Refutation380
import equational_theories.Generated.All4x4Tables.Refutation390
import equational_theories.Generated.All4x4Tables.Refutation395
import equational_theories.Generated.All4x4Tables.Refutation399
import equational_theories.Generated.All4x4Tables.Refutation415
import equational_theories.Generated.All4x4Tables.Refutation444
import equational_theories.Generated.All4x4Tables.Refutation461
import equational_theories.Generated.All4x4Tables.Refutation467
import equational_theories.Generated.All4x4Tables.Refutation479
import equational_theories.Generated.All4x4Tables.Refutation493
import equational_theories.Generated.All4x4Tables.Refutation499
import equational_theories.Generated.All4x4Tables.Refutation515
import equational_theories.Generated.All4x4Tables.Refutation519
import equational_theories.Generated.All4x4Tables.Refutation530
import equational_theories.Generated.All4x4Tables.Refutation554
import equational_theories.Generated.All4x4Tables.Refutation556
import equational_theories.Generated.All4x4Tables.Refutation560
import equational_theories.Generated.All4x4Tables.Refutation565
import equational_theories.Generated.All4x4Tables.Refutation586
import equational_theories.Generated.All4x4Tables.Refutation595
import equational_theories.Generated.All4x4Tables.Refutation624
import equational_theories.Generated.All4x4Tables.Refutation638
import equational_theories.Generated.All4x4Tables.Refutation649
import equational_theories.Generated.All4x4Tables.Refutation650
import equational_theories.Generated.All4x4Tables.Refutation655
import equational_theories.Generated.All4x4Tables.Refutation657
import equational_theories.Generated.All4x4Tables.Refutation659
import equational_theories.Generated.All4x4Tables.Refutation664
import equational_theories.Generated.All4x4Tables.Refutation665
import equational_theories.Generated.All4x4Tables.Refutation667
import equational_theories.Generated.All4x4Tables.Refutation669
import equational_theories.Generated.All4x4Tables.Refutation685
import equational_theories.Generated.All4x4Tables.Refutation691
import equational_theories.Generated.All4x4Tables.Refutation697
import equational_theories.Generated.All4x4Tables.Refutation699
import equational_theories.Generated.All4x4Tables.Refutation705
import equational_theories.Generated.All4x4Tables.Refutation706
import equational_theories.Generated.All4x4Tables.Refutation710
import equational_theories.Generated.All4x4Tables.Refutation714
import equational_theories.Generated.All4x4Tables.Refutation716
import equational_theories.Generated.All4x4Tables.Refutation717
import equational_theories.Generated.All4x4Tables.Refutation721
import equational_theories.Generated.All4x4Tables.Refutation722
import equational_theories.Generated.All4x4Tables.Refutation724
import equational_theories.Generated.All4x4Tables.Refutation725
import equational_theories.Generated.All4x4Tables.Refutation728
import equational_theories.Generated.All4x4Tables.Refutation742
import equational_theories.Generated.All4x4Tables.Refutation746
import equational_theories.Generated.All4x4Tables.Refutation750
import equational_theories.Generated.All4x4Tables.Refutation759
import equational_theories.Generated.All4x4Tables.Refutation760
import equational_theories.Generated.All4x4Tables.Refutation767
import equational_theories.Generated.All4x4Tables.Refutation771
import equational_theories.Generated.All4x4Tables.Refutation775
import equational_theories.Generated.All4x4Tables.Refutation777
import equational_theories.Generated.All4x4Tables.Refutation822
import equational_theories.Generated.All4x4Tables.Refutation823
import equational_theories.Generated.All4x4Tables.Refutation825
import equational_theories.Generated.All4x4Tables.Refutation826
import equational_theories.Generated.All4x4Tables.Refutation843
import equational_theories.Generated.All4x4Tables.Refutation851
import equational_theories.Generated.All4x4Tables.Refutation854
import equational_theories.Generated.All4x4Tables.Refutation862
import equational_theories.Generated.All4x4Tables.Refutation867
import equational_theories.Generated.All4x4Tables.Refutation871
import equational_theories.Generated.All4x4Tables.Refutation872
import equational_theories.Generated.All4x4Tables.Refutation88
import equational_theories.Generated.All4x4Tables.Refutation917
import equational_theories.Generated.All4x4Tables.Refutation935
import equational_theories.Generated.EndToEndCertificate.DualTable
import equational_theories.Generated.Greedy.Eq1112
import equational_theories.Generated.Greedy.Eq1648
import equational_theories.Generated.Greedy.Eq476
import equational_theories.ManuallyProved.Equation1437
import equational_theories.ManuallyProved.Equation1447
import equational_theories.ManuallyProved.Equation1648
import equational_theories.ManuallyProved.Equation1659
import equational_theories.ManuallyProved.Equation1661
import equational_theories.ManuallyProved.Equation1701
import equational_theories.ThreeC2

/-! Generated by equational_theories/Generated/EndToEndCertificate/src/generate.py. Do not edit. -/

/-! `neg` entries 720-839, where an entry is one model witness with its magma.

The data itself is in `json/neg.json`, shared by every shard; the
number after the path is that file's FNV-1a hash, checked on every elaboration
because Lake cannot track a file read during one.

`RArray` indices are *relative*: `.branch p l r` sends index `n` to `l` when
`n < p`, and to `r` at `n - p` (see `RArray.get`). So the numbers after `.branch`
are left-subtree **sizes**, not indices, and every subtree -- including this
shard -- is indexed from 0. Add 720 to get an index into `neg`.
-/

namespace EndToEnd

set_option maxRecDepth 20000 in
def neg6 : RArray NegFact :=
  loadNegTable% "json/neg.json" 6517078778232025408
    entries 720 to 840

end EndToEnd
