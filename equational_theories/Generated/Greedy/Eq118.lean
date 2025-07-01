import equational_theories.Equations.All
import equational_theories.Generated.Greedy.OrLemmas
import equational_theories.Superposition
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Pairing

namespace Eq118

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (old_4 : (∀ X0 X1 X2, ¬ old X0 X0 X1 ∨ ¬ old X1 X0 X2 ∨ old X0 X1 X2)) (old_8 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X3 = X0)) (old_10 : (∀ X0 X1 X2, ¬ old X0 X0 X1 ∨ ¬ old X0 X1 X2 ∨ old X1 X0 X2)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), b = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z b a ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b b a ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), b = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b b a ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), old a a b ∨ ¬sP4 X Y Z) (rule_def_5_0 : ∀ (X Y Z : G), c = X ∨ ¬sP5 X Y Z) (rule_def_5_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP5 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), old a a b ∨ ¬sP5 X Y Z) (rule_def_6_0 : ∀ (X Y Z : G), a = X ∨ ¬sP6 X Y Z) (rule_def_6_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP6 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), old b b a ∨ ¬sP6 X Y Z) (rule_def_6_3 : ∀ (X Y Z : G), old Z a b ∨ ¬sP6 X Y Z) (rule_def_7_0 : ∀ (X Y Z : G), a = b ∨ ¬sP7 X Y Z) (rule_def_7_1 : ∀ (X Y Z : G), c = X ∨ ¬sP7 X Y Z) (rule_def_7_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP7 X Y Z) (rule_def_7_3 : ∀ (X Y Z : G), old Z b b ∨ ¬sP7 X Y Z) (rule_def_8_0 : ∀ (X Y Z : G), b = X ∨ ¬sP8 X Y Z) (rule_def_8_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP8 X Y Z) (rule_def_8_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP8 X Y Z) (rule_def_8_3 : ∀ (X Y Z : G), old a a b ∨ ¬sP8 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq216 : (sP8 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 188,189
  have eq217 : (sP8 sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) := resolve new_imp preserve_1 -- resolution 188,190
  have eq235 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (old a a b) := resolve eq216 rule_def_8_3 -- resolution 216,186
  have eq236 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ c = sk2 := resolve eq216 rule_def_8_2 -- resolution 216,185
  have eq237 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ a = sk1 := resolve eq216 rule_def_8_1 -- resolution 216,184
  have eq238 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ b = sk0 := resolve eq216 rule_def_8_0 -- resolution 216,183
  have eq239 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (old a a b) := resolve eq235 rule_def_4_3 -- subsumption resolution 235,166
  have eq240 : (sP7 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (old a a b) := resolve eq239 rule_def_5_3 -- subsumption resolution 239,171
  have eq241 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ c = sk2 := resolve eq236 rule_def_3_2 -- subsumption resolution 236,160
  have eq242 : (sP7 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ c = sk2 := resolve eq241 rule_def_0_2 -- subsumption resolution 241,147
  have eq243 : (sP6 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ a = sk1 := resolve eq237 rule_def_5_1 -- subsumption resolution 237,169
  have eq244 : (sP7 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ a = sk1 := resolve eq243 rule_def_3_1 -- subsumption resolution 243,159
  have eq245 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ b = sk0 := resolve eq238 rule_def_3_0 -- subsumption resolution 238,158
  have eq246 : (sP7 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ b = sk0 := resolve eq245 rule_def_1_0 -- subsumption resolution 245,149
  have eq252 : (sP6 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ (old a a b) := resolve eq217 rule_def_8_3 -- resolution 217,186
  have eq253 : (sP6 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ c = sk3 := resolve eq217 rule_def_8_2 -- resolution 217,185
  have eq254 : (sP6 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ a = sk1 := resolve eq217 rule_def_8_1 -- resolution 217,184
  have eq255 : (sP6 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ b = sk0 := resolve eq217 rule_def_8_0 -- resolution 217,183
  have eq256 : (sP6 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ (old a a b) := resolve eq252 rule_def_4_3 -- subsumption resolution 252,166
  have eq257 : (sP7 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (old a a b) := resolve eq256 rule_def_5_3 -- subsumption resolution 256,171
  have eq258 : (sP6 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ c = sk3 := resolve eq253 rule_def_3_2 -- subsumption resolution 253,160
  have eq259 : (sP7 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ c = sk3 := resolve eq258 rule_def_0_2 -- subsumption resolution 258,147
  have eq260 : (sP6 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ a = sk1 := resolve eq254 rule_def_5_1 -- subsumption resolution 254,169
  have eq261 : (sP7 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ a = sk1 := resolve eq260 rule_def_3_1 -- subsumption resolution 260,159
  have eq262 : (sP6 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ b = sk0 := resolve eq255 rule_def_3_0 -- subsumption resolution 255,158
  have eq263 : (sP7 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ b = sk0 := resolve eq262 rule_def_1_0 -- subsumption resolution 262,149
  have eq279 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 := resolve eq242 rule_def_7_1 -- resolution 242,179
  have eq282 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 := resolve eq279 rule_def_5_0 -- subsumption resolution 279,168
  have eq283 : (sP6 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 := resolve eq282 rule_def_2_0 -- subsumption resolution 282,153
  have eq288 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 := resolve eq244 rule_def_7_2 -- resolution 244,180
  have eq290 : (sP6 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk1 ∨ a = b := resolve eq244 rule_def_7_0 -- resolution 244,178
  have eq291 : (sP4 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 := resolve eq288 rule_def_2_1 -- subsumption resolution 288,154
  have eq292 : (sP6 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 := resolve eq291 rule_def_0_1 -- subsumption resolution 291,146
  have eq298 : (sP6 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ b = sk0 ∨ (old sk2 b b) := resolve eq246 rule_def_7_3 -- resolution 246,181
  have eq299 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 := resolve eq246 rule_def_7_2 -- resolution 246,180
  have eq302 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 := resolve eq299 rule_def_2_1 -- subsumption resolution 299,154
  have eq303 : (sP6 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 := resolve eq302 rule_def_0_1 -- subsumption resolution 302,146
  have eq308 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq283 rule_def_6_1 -- resolution 283,174
  have eq310 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq308 rule_def_4_1 -- subsumption resolution 308,164
  have eq311 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq310 rule_def_1_1 -- subsumption resolution 310,150
  have eq315 : (sP5 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk0 := resolve eq259 rule_def_7_1 -- resolution 259,179
  have eq318 : (sP4 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk0 := resolve eq315 rule_def_5_0 -- subsumption resolution 315,168
  have eq319 : (sP6 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk0 := resolve eq318 rule_def_2_0 -- subsumption resolution 318,153
  have eq320 (X0 : G) : ¬(old sk0 sk1 X0) ∨ c = sk0 ∨ c = sk1 ∨ sk2 = X0 ∨ c = sk2 := resolve eq311 old_0 -- resolution 311,132
  have eq330 : (sP4 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ a = sk1 ∨ b = sk1 := resolve eq261 rule_def_7_2 -- resolution 261,180
  have eq332 : (sP6 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ a = sk1 ∨ a = b := resolve eq261 rule_def_7_0 -- resolution 261,178
  have eq333 : (sP4 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ a = sk1 ∨ b = sk1 := resolve eq330 rule_def_2_1 -- subsumption resolution 330,154
  have eq334 : (sP6 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ a = sk1 ∨ b = sk1 := resolve eq333 rule_def_0_1 -- subsumption resolution 333,146
  have eq338 : (sP6 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ b = sk0 ∨ (old sk3 b b) := resolve eq263 rule_def_7_3 -- resolution 263,181
  have eq339 : (sP5 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ b = sk0 ∨ b = sk1 := resolve eq263 rule_def_7_2 -- resolution 263,180
  have eq340 : (sP5 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ b = sk0 ∨ c = sk0 := resolve eq263 rule_def_7_1 -- resolution 263,179
  have eq342 : (sP5 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ b = sk0 ∨ b = sk1 := resolve eq339 rule_def_2_1 -- subsumption resolution 339,154
  have eq343 : (sP6 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ b = sk0 ∨ b = sk1 := resolve eq342 rule_def_0_1 -- subsumption resolution 342,146
  have eq344 : (sP4 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ b = sk0 ∨ c = sk0 := resolve eq340 rule_def_5_0 -- subsumption resolution 340,168
  have eq345 : (sP6 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk0 ∨ c = sk0 := resolve eq344 rule_def_2_0 -- subsumption resolution 344,153
  have eq349 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 := resolve eq240 rule_def_7_2 -- resolution 240,180
  have eq350 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (old a a b) ∨ c = sk0 := resolve eq240 rule_def_7_1 -- resolution 240,179
  have eq352 : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 := resolve eq349 rule_def_2_1 -- subsumption resolution 349,154
  have eq353 : (sP6 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 := resolve eq352 rule_def_0_1 -- subsumption resolution 352,146
  have eq354 : (sP6 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (old a a b) ∨ c = sk0 := resolve eq350 rule_def_2_0 -- subsumption resolution 350,153
  have eq359 : (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (old a a b) ∨ b = sk1 := resolve eq257 rule_def_7_2 -- resolution 257,180
  have eq360 : (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (old a a b) ∨ c = sk0 := resolve eq257 rule_def_7_1 -- resolution 257,179
  have eq362 : (sP3 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (old a a b) ∨ b = sk1 := resolve eq359 rule_def_2_1 -- subsumption resolution 359,154
  have eq363 : (sP6 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (old a a b) ∨ b = sk1 := resolve eq362 rule_def_0_1 -- subsumption resolution 362,146
  have eq364 : (sP6 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (old a a b) ∨ c = sk0 := resolve eq360 rule_def_2_0 -- subsumption resolution 360,153
  have eq378 : (sP4 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ (old sk2 a b) := resolve eq292 rule_def_6_3 -- resolution 292,176
  have eq380 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 := resolve eq292 rule_def_6_1 -- resolution 292,174
  have eq382 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 := resolve eq380 rule_def_4_1 -- subsumption resolution 380,164
  have eq383 : (old sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 := resolve eq382 rule_def_1_1 -- subsumption resolution 382,150
  have eq387 (X0 : G) : ¬(old sk0 sk1 X0) ∨ b = sk1 ∨ c = sk1 ∨ sk2 = X0 ∨ a = sk1 := resolve eq383 old_0 -- resolution 383,132
  have eq398 : (sP5 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 ∨ (old sk2 a b) := resolve eq303 rule_def_6_3 -- resolution 303,176
  have eq401 : (sP4 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 ∨ a = sk0 := resolve eq303 rule_def_6_0 -- resolution 303,173
  have eq403 : (sP5 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 ∨ a = sk0 := resolve eq401 rule_def_4_0 -- subsumption resolution 401,163
  have eq432 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 := resolve eq319 rule_def_6_1 -- resolution 319,174
  have eq434 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 := resolve eq432 rule_def_4_1 -- subsumption resolution 432,164
  have eq435 : (old sk0 sk1 sk3) ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 := resolve eq434 rule_def_1_1 -- subsumption resolution 434,150
  have eq438 : c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk0 ∨ c = sk1 ∨ sk2 = sk3 ∨ c = sk2 := resolve eq435 eq320 -- resolution 435,320
  have eq448 : c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ sk2 = sk3 ∨ c = sk2 := resolve eq438 rfl -- duplicate literal removal 438
  have eq451 : c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := resolve eq448 preserve_2 -- subsumption resolution 448,191
  have eq452 : (sP4 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ a = sk1 ∨ b = sk1 ∨ (old sk3 a b) := resolve eq334 rule_def_6_3 -- resolution 334,176
  have eq454 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 := resolve eq334 rule_def_6_1 -- resolution 334,174
  have eq456 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 := resolve eq454 rule_def_4_1 -- subsumption resolution 454,164
  have eq457 : (old sk0 sk1 sk3) ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 := resolve eq456 rule_def_1_1 -- subsumption resolution 456,150
  have eq463 : (sP7 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ a = sk1 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := Or.assoc8 (eq451.imp_left (fun h : c = sk3 ↦ superpose h eq261)) -- superposition 261,451, 451 into 261, unify on (0).2 in 451 and (0).3 in 261
  have eq478 : (sP7 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ a = sk1 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := resolve eq463 p4XY -- subsumption resolution 463,129
  have eq479 : (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ a = sk1 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := resolve eq478 rule_def_7_1 -- subsumption resolution 478,179
  have eq480 : (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ a = sk1 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := resolve eq479 rule_def_6_1 -- subsumption resolution 479,174
  have eq481 : (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ a = sk1 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := resolve eq480 rule_def_4_1 -- subsumption resolution 480,164
  have eq482 : (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ a = sk1 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := resolve eq481 rule_def_2_0 -- subsumption resolution 481,153
  have eq483 : (sP0 sk0 sk1 c) ∨ a = sk1 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := resolve eq482 rule_def_1_1 -- subsumption resolution 482,150
  have eq494 : (sP5 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk0 ∨ b = sk1 ∨ (old sk3 a b) := resolve eq343 rule_def_6_3 -- resolution 343,176
  have eq497 : (sP4 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ b = sk0 ∨ b = sk1 ∨ a = sk0 := resolve eq343 rule_def_6_0 -- resolution 343,173
  have eq498 : (sP6 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ b = sk0 ∨ b = sk1 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := Or.assoc6 (eq451.imp_left (fun h : c = sk3 ↦ superpose h eq343)) -- superposition 343,451, 451 into 343, unify on (0).2 in 451 and (0).3 in 343
  have eq500 : (sP5 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk0 ∨ b = sk1 ∨ a = sk0 := resolve eq497 rule_def_4_0 -- subsumption resolution 497,163
  have eq501 : (sP6 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ b = sk0 ∨ b = sk1 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := resolve eq498 p4XY -- subsumption resolution 498,129
  have eq502 : (sP4 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ b = sk0 ∨ b = sk1 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := resolve eq501 rule_def_6_1 -- subsumption resolution 501,174
  have eq503 : (sP4 sk0 sk1 c) ∨ b = sk0 ∨ b = sk1 ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := resolve eq502 rule_def_5_0 -- subsumption resolution 502,168
  have eq504 : c = sk2 ∨ b = sk1 ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq503 rule_def_4_1 -- subsumption resolution 503,164
  have eq505 : a = sk1 ∨ b = sk1 ∨ c = sk1 ∨ b = sk1 ∨ c = sk1 ∨ sk2 = sk3 ∨ a = sk1 := resolve eq457 eq387 -- resolution 457,387
  have eq519 : a = sk1 ∨ b = sk1 ∨ c = sk1 ∨ sk2 = sk3 := resolve eq505 rfl -- duplicate literal removal 505
  have eq520 : b = sk1 ∨ a = sk1 ∨ c = sk1 := resolve eq519 preserve_2 -- subsumption resolution 519,191
  have eq524 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq345 rule_def_6_0 -- resolution 345,173
  have eq528 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq524 rule_def_4_0 -- subsumption resolution 524,163
  have eq529 : (old sk0 sk1 sk3) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq528 rule_def_0_0 -- subsumption resolution 528,145
  have eq544 : (old sk0 b sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = b ∨ a = sk1 ∨ c = sk1 := Or.assoc4 (eq520.imp_left (fun h : b = sk1 ↦ superpose h eq311)) -- superposition 311,520, 520 into 311, unify on (0).2 in 520 and (0).2 in 311
  have eq552 : (old sk0 b sk3) ∨ c = sk3 ∨ c = sk0 ∨ c = b ∨ a = sk1 ∨ c = sk1 := Or.assoc4 (eq520.imp_left (fun h : b = sk1 ↦ superpose h eq435)) -- superposition 435,520, 520 into 435, unify on (0).2 in 520 and (0).2 in 435
  have eq553 : a ≠ b ∨ a = sk1 ∨ c = sk1 := resolve eq520 trans_resol -- equality factoring 520
  have eq557 : (old sk0 b sk2) ∨ c = sk2 ∨ c = sk0 ∨ a = sk1 ∨ c = sk1 := resolve eq544 bc -- subsumption resolution 544,127
  have eq560 : (old sk0 b sk3) ∨ c = sk3 ∨ c = sk0 ∨ a = sk1 ∨ c = sk1 := resolve eq552 bc -- subsumption resolution 552,127
  have eq594 : b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk0 ∨ c = sk1 ∨ sk2 = sk3 ∨ c = sk2 := resolve eq529 eq320 -- resolution 529,320
  have eq607 : b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ sk2 = sk3 ∨ c = sk2 := resolve eq594 rfl -- duplicate literal removal 594
  have eq608 : c = sk2 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq607 preserve_2 -- subsumption resolution 607,191
  have eq664 : (sP8 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ b = sk0 := Or.assoc10 (eq608.imp_left (fun h : c = sk2 ↦ superpose h eq216)) -- superposition 216,608, 608 into 216, unify on (0).2 in 608 and (0).3 in 216
  have eq683 : (sP8 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq664 p4XY -- subsumption resolution 664,129
  have eq684 : (sP6 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq683 rule_def_8_0 -- subsumption resolution 683,183
  have eq685 : (sP6 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq684 rule_def_3_0 -- subsumption resolution 684,158
  have eq686 : (sP6 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq685 rule_def_1_0 -- subsumption resolution 685,149
  have eq687 : (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq686 rule_def_6_0 -- subsumption resolution 686,173
  have eq688 : (sP5 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq687 rule_def_4_0 -- subsumption resolution 687,163
  have eq689 : (sP5 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq688 rule_def_0_0 -- subsumption resolution 688,145
  have eq690 : (sP5 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq689 rule_def_7_1 -- subsumption resolution 689,179
  have eq691 : (sP2 sk0 sk1 c) ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq690 rule_def_5_0 -- subsumption resolution 690,168
  have eq692 : c = sk1 ∨ a = sk0 ∨ c = sk0 ∨ b = sk0 := resolve eq691 rule_def_2_0 -- subsumption resolution 691,153
  have eq695 : (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (old a a b) ∨ c = sk0 ∨ c = sk1 := resolve eq354 rule_def_6_1 -- resolution 354,174
  have eq701 : (sP3 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old a a b) ∨ c = sk0 ∨ c = sk1 := resolve eq695 rule_def_1_1 -- subsumption resolution 695,150
  have eq706 : (sP8 sk0 c sk2) ∨ (sP6 sk0 c sk2) ∨ (sP5 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (old sk0 c sk2) ∨ (sP7 sk0 c sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk0 := Or.assoc10 (eq692.imp_left (fun h : c = sk1 ↦ superpose h eq216)) -- superposition 216,692, 692 into 216, unify on (0).2 in 692 and (0).2 in 216
  have eq750 : (sP8 sk0 c sk2) ∨ (sP6 sk0 c sk2) ∨ (sP5 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (sP7 sk0 c sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk0 := resolve eq706 p4XZ -- subsumption resolution 706,130
  have eq751 : (sP6 sk0 c sk2) ∨ (sP5 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (sP7 sk0 c sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk0 := resolve eq750 rule_def_8_0 -- subsumption resolution 750,183
  have eq752 : (sP6 sk0 c sk2) ∨ (sP5 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (sP7 sk0 c sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk0 := resolve eq751 rule_def_3_0 -- subsumption resolution 751,158
  have eq753 : (sP6 sk0 c sk2) ∨ (sP5 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (sP7 sk0 c sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk0 := resolve eq752 rule_def_1_0 -- subsumption resolution 752,149
  have eq754 : (sP6 sk0 c sk2) ∨ (sP5 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk0 := resolve eq753 rule_def_7_1 -- subsumption resolution 753,179
  have eq755 : (sP6 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk0 := resolve eq754 rule_def_5_0 -- subsumption resolution 754,168
  have eq756 : (sP6 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk0 := resolve eq755 rule_def_2_0 -- subsumption resolution 755,153
  have eq757 : (sP4 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk0 := resolve eq756 rule_def_6_0 -- subsumption resolution 756,173
  have eq758 : (sP0 sk0 c sk2) ∨ a = sk0 ∨ c = sk0 ∨ b = sk0 := resolve eq757 rule_def_4_0 -- subsumption resolution 757,163
  have eq759 : b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq758 rule_def_0_0 -- subsumption resolution 758,145
  have eq761 : (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (old a a b) ∨ c = sk0 ∨ (old b b a) := resolve eq364 rule_def_6_2 -- resolution 364,175
  have eq771 : (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (old a a b) ∨ c = sk0 ∨ (old b b a) := resolve eq761 rule_def_3_3 -- subsumption resolution 761,161
  have eq788 : (old b sk1 sk2) ∨ c = sk2 ∨ c = b ∨ c = sk1 ∨ c = sk0 ∨ a = sk0 := Or.assoc4 (eq759.imp_left (fun h : b = sk0 ↦ superpose h eq311)) -- superposition 311,759, 759 into 311, unify on (0).2 in 759 and (0).1 in 311
  have eq801 : (old b sk1 sk3) ∨ c = sk3 ∨ c = b ∨ c = sk1 ∨ c = sk0 ∨ a = sk0 := Or.assoc4 (eq759.imp_left (fun h : b = sk0 ↦ superpose h eq435)) -- superposition 435,759, 759 into 435, unify on (0).2 in 759 and (0).1 in 435
  have eq810 : (old b sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq788 bc -- subsumption resolution 788,127
  have eq817 : (old b sk1 sk3) ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq801 bc -- subsumption resolution 801,127
  have eq833 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk1 ∨ a = b ∨ c = sk1 := resolve eq290 rule_def_6_1 -- resolution 290,174
  have eq841 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ a = b ∨ c = sk1 := resolve eq833 rule_def_4_1 -- subsumption resolution 833,164
  have eq842 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ a = b ∨ c = sk1 := resolve eq841 rule_def_1_1 -- subsumption resolution 841,150
  have eq843 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ c = sk1 := resolve eq842 eq553 -- subsumption resolution 842,553
  have eq891 : (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ a = sk1 ∨ a = b ∨ c = sk1 := resolve eq332 rule_def_6_1 -- resolution 332,174
  have eq901 : (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk1 ∨ a = b ∨ c = sk1 := resolve eq891 rule_def_4_1 -- subsumption resolution 891,164
  have eq902 : (sP2 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk1 ∨ a = b ∨ c = sk1 := resolve eq901 rule_def_1_1 -- subsumption resolution 901,150
  have eq903 : (sP2 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk1 ∨ c = sk1 := resolve eq902 eq553 -- subsumption resolution 902,553
  have eq968 : (sP8 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ b = sk1 ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 := Or.assoc10 (eq504.imp_left (fun h : c = sk2 ↦ superpose h eq216)) -- superposition 216,504, 504 into 216, unify on (0).2 in 504 and (0).3 in 216
  have eq998 : (sP8 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ b = sk1 ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq968 p4XY -- subsumption resolution 968,129
  have eq999 : (sP8 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk1 ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq998 rule_def_7_1 -- subsumption resolution 998,179
  have eq1000 : (sP8 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk1 ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq999 rule_def_6_1 -- subsumption resolution 999,174
  have eq1001 : (sP8 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk1 ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq1000 rule_def_5_0 -- subsumption resolution 1000,168
  have eq1002 : (sP8 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk1 ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq1001 rule_def_4_1 -- subsumption resolution 1001,164
  have eq1003 : (sP8 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk1 ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq1002 rule_def_2_0 -- subsumption resolution 1002,153
  have eq1004 : (sP8 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk1 ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq1003 rule_def_1_1 -- subsumption resolution 1003,150
  have eq1005 : (sP3 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk1 ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq1004 rule_def_8_0 -- subsumption resolution 1004,183
  have eq1006 : (sP0 sk0 sk1 c) ∨ b = sk1 ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq1005 rule_def_3_0 -- subsumption resolution 1005,158
  have eq1007 : b = sk1 ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq1006 rule_def_0_1 -- subsumption resolution 1006,146
  have eq1042 : (old sk0 b sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = b ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 := Or.assoc4 (eq1007.imp_left (fun h : b = sk1 ↦ superpose h eq311)) -- superposition 311,1007, 1007 into 311, unify on (0).2 in 1007 and (0).2 in 311
  have eq1056 : (old sk0 b sk3) ∨ c = sk3 ∨ c = sk0 ∨ c = b ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 := Or.assoc4 (eq1007.imp_left (fun h : b = sk1 ↦ superpose h eq435)) -- superposition 435,1007, 1007 into 435, unify on (0).2 in 1007 and (0).2 in 435
  have eq1068 : (old sk0 b sk3) ∨ c = sk3 ∨ c = sk0 ∨ c = b ∨ c = sk1 ∨ b = sk0 := resolve eq1056 rfl -- duplicate literal removal 1056
  have eq1081 : (old sk0 b sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = b ∨ c = sk1 ∨ b = sk0 := resolve eq1042 rfl -- duplicate literal removal 1042
  have eq1117 : (old sk0 b sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq1081 bc -- subsumption resolution 1081,127
  have eq1120 : (old sk0 b sk3) ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq1068 bc -- subsumption resolution 1068,127
  have eq1125 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ b = sk0 ∨ (old sk2 b b) ∨ a = sk0 := resolve eq298 rule_def_6_0 -- resolution 298,173
  have eq1138 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ b = sk0 ∨ (old sk2 b b) ∨ a = sk0 := resolve eq1125 rule_def_4_0 -- subsumption resolution 1125,163
  have eq1139 : (sP5 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ b = sk0 ∨ (old sk2 b b) ∨ a = sk0 := resolve eq1138 rule_def_0_0 -- subsumption resolution 1138,145
  have eq1193 : (sP4 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ b = sk0 ∨ (old sk3 b b) ∨ a = sk0 := resolve eq338 rule_def_6_0 -- resolution 338,173
  have eq1203 : (sP2 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ b = sk0 ∨ (old sk3 b b) ∨ a = sk0 := resolve eq1193 rule_def_4_0 -- subsumption resolution 1193,163
  have eq1204 : (sP5 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ b = sk0 ∨ (old sk3 b b) ∨ a = sk0 := resolve eq1203 rule_def_0_0 -- subsumption resolution 1203,145
  have eq1417 : (old sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 ∨ a = sk0 ∨ a = sk2 := resolve eq403 rule_def_5_2 -- resolution 403,170
  have eq1515 : c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ a = sk1 ∨ a = sk0 := resolve eq483 rule_def_0_0 -- resolution 483,145
  have eq1534 : (sP8 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ c = sk0 ∨ c = sk1 ∨ a = sk1 ∨ a = sk0 := Or.assoc10 (eq1515.imp_left (fun h : c = sk2 ↦ superpose h eq216)) -- superposition 216,1515, 1515 into 216, unify on (0).2 in 1515 and (0).3 in 216
  have eq1587 : (sP8 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ c = sk0 ∨ c = sk1 ∨ a = sk1 ∨ a = sk0 := resolve eq1534 p4XY -- subsumption resolution 1534,129
  have eq1588 : (sP6 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ c = sk0 ∨ c = sk1 ∨ a = sk1 ∨ a = sk0 := resolve eq1587 rule_def_8_1 -- subsumption resolution 1587,184
  have eq1589 : (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ c = sk0 ∨ c = sk1 ∨ a = sk1 ∨ a = sk0 := resolve eq1588 rule_def_6_0 -- subsumption resolution 1588,173
  have eq1590 : (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ c = sk0 ∨ c = sk1 ∨ a = sk1 ∨ a = sk0 := resolve eq1589 rule_def_5_1 -- subsumption resolution 1589,169
  have eq1591 : (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ c = sk0 ∨ c = sk1 ∨ a = sk1 ∨ a = sk0 := resolve eq1590 rule_def_4_0 -- subsumption resolution 1590,163
  have eq1592 : (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ c = sk0 ∨ c = sk1 ∨ a = sk1 ∨ a = sk0 := resolve eq1591 rule_def_3_1 -- subsumption resolution 1591,159
  have eq1593 : (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ c = sk0 ∨ c = sk1 ∨ a = sk1 ∨ a = sk0 := resolve eq1592 rule_def_0_0 -- subsumption resolution 1592,145
  have eq1594 : (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ c = sk0 ∨ c = sk1 ∨ a = sk1 ∨ a = sk0 := resolve eq1593 rule_def_7_1 -- subsumption resolution 1593,179
  have eq1595 : (sP1 sk0 sk1 c) ∨ c = sk0 ∨ c = sk1 ∨ a = sk1 ∨ a = sk0 := resolve eq1594 rule_def_2_0 -- subsumption resolution 1594,153
  have eq1596 : c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ a = sk0 := resolve eq1595 rule_def_1_1 -- subsumption resolution 1595,150
  have eq1613 : (sP7 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (old sk0 c sk2) ∨ (sP6 sk0 c sk2) ∨ a = c ∨ c = sk0 ∨ a = sk1 ∨ a = sk0 := Or.assoc8 (eq1596.imp_left (fun h : c = sk1 ↦ superpose h eq244)) -- superposition 244,1596, 1596 into 244, unify on (0).2 in 1596 and (0).2 in 244
  have eq1617 : (sP7 sk0 c sk3) ∨ (sP4 sk0 c sk3) ∨ (sP2 sk0 c sk3) ∨ (sP1 sk0 c sk3) ∨ (sP0 sk0 c sk3) ∨ (old sk0 c sk3) ∨ (sP6 sk0 c sk3) ∨ a = c ∨ c = sk0 ∨ a = sk1 ∨ a = sk0 := Or.assoc8 (eq1596.imp_left (fun h : c = sk1 ↦ superpose h eq261)) -- superposition 261,1596, 1596 into 261, unify on (0).2 in 1596 and (0).2 in 261
  have eq1718 : (sP7 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (sP6 sk0 c sk2) ∨ a = c ∨ c = sk0 ∨ a = sk1 ∨ a = sk0 := resolve eq1613 p4XZ -- subsumption resolution 1613,130
  have eq1719 : (sP7 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (sP6 sk0 c sk2) ∨ c = sk0 ∨ a = sk1 ∨ a = sk0 := resolve eq1718 ac -- subsumption resolution 1718,126
  have eq1720 : (sP7 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ c = sk0 ∨ a = sk1 ∨ a = sk0 := resolve eq1719 rule_def_6_0 -- subsumption resolution 1719,173
  have eq1721 : (sP7 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ c = sk0 ∨ a = sk1 ∨ a = sk0 := resolve eq1720 rule_def_4_0 -- subsumption resolution 1720,163
  have eq1722 : (sP7 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ c = sk0 ∨ a = sk1 ∨ a = sk0 := resolve eq1721 rule_def_0_0 -- subsumption resolution 1721,145
  have eq1723 : (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ c = sk0 ∨ a = sk1 ∨ a = sk0 := resolve eq1722 rule_def_7_1 -- subsumption resolution 1722,179
  have eq1724 : (sP1 sk0 c sk2) ∨ c = sk0 ∨ a = sk1 ∨ a = sk0 := resolve eq1723 rule_def_2_0 -- subsumption resolution 1723,153
  have eq1736 : (sP7 sk0 c sk3) ∨ (sP4 sk0 c sk3) ∨ (sP2 sk0 c sk3) ∨ (sP1 sk0 c sk3) ∨ (sP0 sk0 c sk3) ∨ (sP6 sk0 c sk3) ∨ a = c ∨ c = sk0 ∨ a = sk1 ∨ a = sk0 := resolve eq1617 p4XZ -- subsumption resolution 1617,130
  have eq1737 : (sP7 sk0 c sk3) ∨ (sP4 sk0 c sk3) ∨ (sP2 sk0 c sk3) ∨ (sP1 sk0 c sk3) ∨ (sP0 sk0 c sk3) ∨ (sP6 sk0 c sk3) ∨ c = sk0 ∨ a = sk1 ∨ a = sk0 := resolve eq1736 ac -- subsumption resolution 1736,126
  have eq1738 : (sP7 sk0 c sk3) ∨ (sP4 sk0 c sk3) ∨ (sP2 sk0 c sk3) ∨ (sP1 sk0 c sk3) ∨ (sP0 sk0 c sk3) ∨ c = sk0 ∨ a = sk1 ∨ a = sk0 := resolve eq1737 rule_def_6_0 -- subsumption resolution 1737,173
  have eq1739 : (sP7 sk0 c sk3) ∨ (sP2 sk0 c sk3) ∨ (sP1 sk0 c sk3) ∨ (sP0 sk0 c sk3) ∨ c = sk0 ∨ a = sk1 ∨ a = sk0 := resolve eq1738 rule_def_4_0 -- subsumption resolution 1738,163
  have eq1740 : (sP7 sk0 c sk3) ∨ (sP2 sk0 c sk3) ∨ (sP1 sk0 c sk3) ∨ c = sk0 ∨ a = sk1 ∨ a = sk0 := resolve eq1739 rule_def_0_0 -- subsumption resolution 1739,145
  have eq1741 : (sP2 sk0 c sk3) ∨ (sP1 sk0 c sk3) ∨ c = sk0 ∨ a = sk1 ∨ a = sk0 := resolve eq1740 rule_def_7_1 -- subsumption resolution 1740,179
  have eq1742 : (sP1 sk0 c sk3) ∨ c = sk0 ∨ a = sk1 ∨ a = sk0 := resolve eq1741 rule_def_2_0 -- subsumption resolution 1741,153
  have eq1744 : (old sk0 sk1 sk3) ∨ b = sk0 ∨ b = sk1 ∨ a = sk0 ∨ a = sk3 := resolve eq500 rule_def_5_2 -- resolution 500,170
  have eq1840 : (old sk2 b a) ∨ a = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq1724 rule_def_1_2 -- resolution 1724,151
  have eq1859 : (old sk3 b a) ∨ a = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq1742 rule_def_1_2 -- resolution 1742,151
  have eq1889 (X0 : G) : ¬(old X0 b a) ∨ a = sk0 ∨ c = sk0 ∨ sk2 = X0 ∨ a = sk1 := resolve eq1840 old_8 -- resolution 1840,140
  have eq1972 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ c = sk1 ∨ b = sk2 := resolve eq843 rule_def_2_2 -- resolution 843,155
  have eq1998 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk1 ∨ c = sk1 ∨ b = sk3 := resolve eq903 rule_def_2_2 -- resolution 903,155
  have eq2347 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ (old sk2 a b) ∨ a = sk2 := resolve eq378 rule_def_4_2 -- resolution 378,165
  have eq2389 : (sP4 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 ∨ (old sk2 a b) ∨ a = sk1 := resolve eq398 rule_def_5_1 -- resolution 398,169
  have eq2546 : (sP1 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = sk1 ∨ b = sk1 ∨ (old sk3 a b) ∨ a = sk3 := resolve eq452 rule_def_4_2 -- resolution 452,165
  have eq2573 : (sP4 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk0 ∨ b = sk1 ∨ (old sk3 a b) ∨ a = sk1 := resolve eq494 rule_def_5_1 -- resolution 494,169
  have eq2664 : a = sk0 ∨ c = sk0 ∨ sk2 = sk3 ∨ a = sk1 ∨ a = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq1889 eq1859 -- resolution 1889,1859
  have eq2665 : a = sk0 ∨ c = sk0 ∨ sk2 = sk3 ∨ a = sk1 := resolve eq2664 rfl -- duplicate literal removal 2664
  have eq2667 : a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq2665 preserve_2 -- subsumption resolution 2665,191
  have eq2711 (X0 : G) : ¬(old sk0 a X0) ∨ c = sk0 ∨ a = c ∨ sk2 = X0 ∨ c = sk2 ∨ c = sk0 ∨ a = sk0 := Or.assoc5 (eq2667.imp_left (fun h : a = sk1 ↦ superpose h eq320)) -- superposition 320,2667, 2667 into 320, unify on (0).2 in 2667 and (0).2 in 320
  have eq2738 : (old sk0 a sk3) ∨ c = sk3 ∨ c = sk0 ∨ a = c ∨ c = sk0 ∨ a = sk0 := Or.assoc4 (eq2667.imp_left (fun h : a = sk1 ↦ superpose h eq435)) -- superposition 435,2667, 2667 into 435, unify on (0).2 in 2667 and (0).2 in 435
  have eq2768 : (old b a sk2) ∨ c = sk2 ∨ a = c ∨ c = sk0 ∨ a = sk0 ∨ c = sk0 ∨ a = sk0 := Or.assoc5 (eq2667.imp_left (fun h : a = sk1 ↦ superpose h eq810)) -- superposition 810,2667, 2667 into 810, unify on (0).2 in 2667 and (0).2 in 810
  have eq2769 : (old b a sk3) ∨ c = sk3 ∨ a = c ∨ c = sk0 ∨ a = sk0 ∨ c = sk0 ∨ a = sk0 := Or.assoc5 (eq2667.imp_left (fun h : a = sk1 ↦ superpose h eq817)) -- superposition 817,2667, 2667 into 817, unify on (0).2 in 2667 and (0).2 in 817
  have eq2790 : (old b a sk3) ∨ c = sk3 ∨ a = c ∨ c = sk0 ∨ a = sk0 := resolve eq2769 rfl -- duplicate literal removal 2769
  have eq2791 : (old b a sk2) ∨ c = sk2 ∨ a = c ∨ c = sk0 ∨ a = sk0 := resolve eq2768 rfl -- duplicate literal removal 2768
  have eq2812 : (old sk0 a sk3) ∨ c = sk3 ∨ c = sk0 ∨ a = c ∨ a = sk0 := resolve eq2738 rfl -- duplicate literal removal 2738
  have eq2827 (X0 : G) : ¬(old sk0 a X0) ∨ c = sk0 ∨ a = c ∨ sk2 = X0 ∨ c = sk2 ∨ a = sk0 := resolve eq2711 rfl -- duplicate literal removal 2711
  have eq2869 (X0 : G) : ¬(old sk0 a X0) ∨ c = sk0 ∨ sk2 = X0 ∨ c = sk2 ∨ a = sk0 := resolve eq2827 ac -- subsumption resolution 2827,126
  have eq2871 : (old sk0 a sk3) ∨ c = sk3 ∨ c = sk0 ∨ a = sk0 := resolve eq2812 ac -- subsumption resolution 2812,126
  have eq2881 : (old b a sk2) ∨ c = sk2 ∨ c = sk0 ∨ a = sk0 := resolve eq2791 ac -- subsumption resolution 2791,126
  have eq2882 : (old b a sk3) ∨ c = sk3 ∨ c = sk0 ∨ a = sk0 := resolve eq2790 ac -- subsumption resolution 2790,126
  have eq3079 : c = sk2 ∨ c = sk0 ∨ a = sk0 ∨ (old a b sk2) ∨ ¬(old a a b) := resolve eq2881 old_4 -- resolution 2881,136
  have eq3084 : c = sk2 ∨ c = sk0 ∨ a = sk0 ∨ (old a b sk2) ∨ ¬(old b b a) := resolve eq2881 old_10 -- resolution 2881,142
  have eq3086 : ¬(old a a b) ∨ c = sk0 ∨ a = sk0 ∨ c = sk2 := resolve eq3079 p3 -- subsumption resolution 3079,128
  have eq3087 : ¬(old b b a) ∨ c = sk0 ∨ a = sk0 ∨ c = sk2 := resolve eq3084 p3 -- subsumption resolution 3084,128
  have eq3104 : c = sk3 ∨ c = sk0 ∨ a = sk0 ∨ (old a b sk3) ∨ ¬(old a a b) := resolve eq2882 old_4 -- resolution 2882,136
  have eq3109 : c = sk3 ∨ c = sk0 ∨ a = sk0 ∨ (old a b sk3) ∨ ¬(old b b a) := resolve eq2882 old_10 -- resolution 2882,142
  have eq3111 : ¬(old a a b) ∨ c = sk0 ∨ a = sk0 ∨ c = sk3 := resolve eq3104 p3 -- subsumption resolution 3104,128
  have eq3112 : ¬(old b b a) ∨ c = sk0 ∨ a = sk0 ∨ c = sk3 := resolve eq3109 p3 -- subsumption resolution 3109,128
  have eq3247 : c = sk0 ∨ sk2 = sk3 ∨ c = sk2 ∨ a = sk0 ∨ c = sk3 ∨ c = sk0 ∨ a = sk0 := resolve eq2869 eq2871 -- resolution 2869,2871
  have eq3249 : c = sk0 ∨ sk2 = sk3 ∨ c = sk2 ∨ a = sk0 ∨ c = sk3 := resolve eq3247 rfl -- duplicate literal removal 3247
  have eq3251 : c = sk3 ∨ c = sk2 ∨ a = sk0 ∨ c = sk0 := resolve eq3249 preserve_2 -- subsumption resolution 3249,191
  have eq3302 : (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (old a a b) ∨ c = sk0 ∨ (old b b a) ∨ c = sk2 ∨ a = sk0 ∨ c = sk0 := Or.assoc6 (eq3251.imp_left (fun h : c = sk3 ↦ superpose h eq771)) -- superposition 771,3251, 3251 into 771, unify on (0).2 in 3251 and (0).3 in 771
  have eq3347 : (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (old a a b) ∨ c = sk0 ∨ (old b b a) ∨ c = sk2 ∨ a = sk0 := resolve eq3302 rfl -- duplicate literal removal 3302
  have eq3378 : (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old a a b) ∨ c = sk0 ∨ (old b b a) ∨ c = sk2 ∨ a = sk0 := resolve eq3347 p4XY -- subsumption resolution 3347,129
  have eq3379 : (sP1 sk0 sk1 c) ∨ (old a a b) ∨ c = sk0 ∨ (old b b a) ∨ c = sk2 ∨ a = sk0 := resolve eq3378 rule_def_0_0 -- subsumption resolution 3378,145
  have eq3380 : (sP1 sk0 sk1 c) ∨ c = sk0 ∨ (old b b a) ∨ c = sk2 ∨ a = sk0 := resolve eq3379 eq3086 -- subsumption resolution 3379,3086
  have eq3381 : (sP1 sk0 sk1 c) ∨ c = sk0 ∨ c = sk2 ∨ a = sk0 := resolve eq3380 eq3087 -- subsumption resolution 3380,3087
  have eq3448 : c = sk0 ∨ c = sk2 ∨ a = sk0 ∨ (old c b a) := resolve eq3381 rule_def_1_2 -- resolution 3381,151
  have eq3461 : c = sk2 ∨ c = sk0 ∨ a = sk0 := resolve eq3448 p4YZ -- subsumption resolution 3448,131
  have eq3514 : (sP3 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old a a b) ∨ c = sk0 ∨ c = sk1 ∨ c = sk0 ∨ a = sk0 := Or.assoc6 (eq3461.imp_left (fun h : c = sk2 ↦ superpose h eq701)) -- superposition 701,3461, 3461 into 701, unify on (0).2 in 3461 and (0).3 in 701
  have eq3560 : (sP3 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old a a b) ∨ c = sk0 ∨ c = sk1 ∨ a = sk0 := resolve eq3514 rfl -- duplicate literal removal 3514
  have eq3591 : (sP3 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old a a b) ∨ c = sk0 ∨ c = sk1 ∨ a = sk0 := resolve eq3560 p4XY -- subsumption resolution 3560,129
  have eq3592 : (sP3 sk0 sk1 c) ∨ (old a a b) ∨ c = sk0 ∨ c = sk1 ∨ a = sk0 := resolve eq3591 rule_def_0_0 -- subsumption resolution 3591,145
  have eq4873 : (old sk0 sk1 sk2) ∨ a = sk1 ∨ c = sk1 ∨ b = sk2 ∨ a = sk0 := resolve eq1972 rule_def_0_0 -- resolution 1972,145
  have eq4930 : (old sk0 sk1 sk3) ∨ a = sk1 ∨ c = sk1 ∨ b = sk3 ∨ a = sk0 := resolve eq1998 rule_def_0_0 -- resolution 1998,145
  have eq6771 : (sP3 sk0 a c) ∨ (old a a b) ∨ c = sk0 ∨ a = c ∨ a = sk0 ∨ c = sk0 ∨ a = sk0 := Or.assoc5 (eq2667.imp_left (fun h : a = sk1 ↦ superpose h eq3592)) -- superposition 3592,2667, 2667 into 3592, unify on (0).2 in 2667 and (0).2 in 3592
  have eq6775 : (sP3 sk0 a c) ∨ (old a a b) ∨ c = sk0 ∨ a = c ∨ a = sk0 := resolve eq6771 rfl -- duplicate literal removal 6771
  have eq6778 : (sP3 sk0 a c) ∨ (old a a b) ∨ c = sk0 ∨ a = sk0 := resolve eq6775 ac -- subsumption resolution 6775,126
  have eq6786 : (old b b a) ∨ c = sk0 ∨ a = sk0 ∨ (old a a b) := resolve eq6778 rule_def_3_3 -- resolution 6778,161
  have eq6810 : c = sk0 ∨ a = sk0 ∨ (old a a b) ∨ c = sk0 ∨ a = sk0 ∨ c = sk3 := resolve eq6786 eq3112 -- resolution 6786,3112
  have eq6826 : c = sk0 ∨ a = sk0 ∨ (old a a b) ∨ c = sk3 := resolve eq6810 rfl -- duplicate literal removal 6810
  have eq6834 : c = sk3 ∨ a = sk0 ∨ c = sk0 := resolve eq6826 eq3111 -- subsumption resolution 6826,3111
  have eq6854 : c ≠ sk2 ∨ a = sk0 ∨ c = sk0 := eq6834.imp_left (fun h : c = sk3 ↦ superpose h preserve_2) -- superposition 191,6834, 6834 into 191, unify on (0).2 in 6834 and (0).2 in 191
  have eq7050 : c = sk0 ∨ a = sk0 := resolve eq6854 eq3461 -- subsumption resolution 6854,3461
  have eq7171 : (sP5 c sk1 sk2) ∨ (old c sk1 sk2) ∨ (sP2 c sk1 sk2) ∨ c = b ∨ (old sk2 b b) ∨ a = c ∨ a = sk0 := Or.assoc6 (eq7050.imp_left (fun h : c = sk0 ↦ superpose h eq1139)) -- superposition 1139,7050, 7050 into 1139, unify on (0).2 in 7050 and (0).1 in 1139
  have eq7182 : (sP5 c sk1 sk3) ∨ (old c sk1 sk3) ∨ (sP2 c sk1 sk3) ∨ c = b ∨ (old sk3 b b) ∨ a = c ∨ a = sk0 := Or.assoc6 (eq7050.imp_left (fun h : c = sk0 ↦ superpose h eq1204)) -- superposition 1204,7050, 7050 into 1204, unify on (0).2 in 7050 and (0).1 in 1204
  have eq7203 : (old c sk1 sk2) ∨ c = b ∨ b = sk1 ∨ a = c ∨ a = sk2 ∨ a = sk0 := Or.assoc5 (eq7050.imp_left (fun h : c = sk0 ↦ superpose h eq1417)) -- superposition 1417,7050, 7050 into 1417, unify on (0).2 in 7050 and (0).1 in 1417
  have eq7208 : (old c sk1 sk3) ∨ c = b ∨ b = sk1 ∨ a = c ∨ a = sk3 ∨ a = sk0 := Or.assoc5 (eq7050.imp_left (fun h : c = sk0 ↦ superpose h eq1744)) -- superposition 1744,7050, 7050 into 1744, unify on (0).2 in 7050 and (0).1 in 1744
  have eq7267 : (old c sk1 sk2) ∨ a = sk1 ∨ c = sk1 ∨ b = sk2 ∨ a = c ∨ a = sk0 := Or.assoc5 (eq7050.imp_left (fun h : c = sk0 ↦ superpose h eq4873)) -- superposition 4873,7050, 7050 into 4873, unify on (0).2 in 7050 and (0).1 in 4873
  have eq7271 : (old c sk1 sk3) ∨ a = sk1 ∨ c = sk1 ∨ b = sk3 ∨ a = c ∨ a = sk0 := Or.assoc5 (eq7050.imp_left (fun h : c = sk0 ↦ superpose h eq4930)) -- superposition 4930,7050, 7050 into 4930, unify on (0).2 in 7050 and (0).1 in 4930
  have eq7420 : (sP5 c sk1 sk2) ∨ (sP2 c sk1 sk2) ∨ c = b ∨ (old sk2 b b) ∨ a = c ∨ a = sk0 := resolve eq7171 p4YZ -- subsumption resolution 7171,131
  have eq7421 : (sP5 c sk1 sk2) ∨ (sP2 c sk1 sk2) ∨ (old sk2 b b) ∨ a = c ∨ a = sk0 := resolve eq7420 bc -- subsumption resolution 7420,127
  have eq7422 : (sP5 c sk1 sk2) ∨ (sP2 c sk1 sk2) ∨ (old sk2 b b) ∨ a = sk0 := resolve eq7421 ac -- subsumption resolution 7421,126
  have eq7438 : (sP5 c sk1 sk3) ∨ (sP2 c sk1 sk3) ∨ c = b ∨ (old sk3 b b) ∨ a = c ∨ a = sk0 := resolve eq7182 p4YZ -- subsumption resolution 7182,131
  have eq7439 : (sP5 c sk1 sk3) ∨ (sP2 c sk1 sk3) ∨ (old sk3 b b) ∨ a = c ∨ a = sk0 := resolve eq7438 bc -- subsumption resolution 7438,127
  have eq7440 : (sP5 c sk1 sk3) ∨ (sP2 c sk1 sk3) ∨ (old sk3 b b) ∨ a = sk0 := resolve eq7439 ac -- subsumption resolution 7439,126
  have eq7471 : c = b ∨ b = sk1 ∨ a = c ∨ a = sk2 ∨ a = sk0 := resolve eq7203 p4YZ -- subsumption resolution 7203,131
  have eq7472 : b = sk1 ∨ a = c ∨ a = sk2 ∨ a = sk0 := resolve eq7471 bc -- subsumption resolution 7471,127
  have eq7473 : a = sk2 ∨ b = sk1 ∨ a = sk0 := resolve eq7472 ac -- subsumption resolution 7472,126
  have eq7476 : c = b ∨ b = sk1 ∨ a = c ∨ a = sk3 ∨ a = sk0 := resolve eq7208 p4YZ -- subsumption resolution 7208,131
  have eq7477 : b = sk1 ∨ a = c ∨ a = sk3 ∨ a = sk0 := resolve eq7476 bc -- subsumption resolution 7476,127
  have eq7478 : a = sk3 ∨ b = sk1 ∨ a = sk0 := resolve eq7477 ac -- subsumption resolution 7477,126
  have eq7538 : a = sk1 ∨ c = sk1 ∨ b = sk2 ∨ a = c ∨ a = sk0 := resolve eq7267 p4YZ -- subsumption resolution 7267,131
  have eq7539 : b = sk2 ∨ c = sk1 ∨ a = sk1 ∨ a = sk0 := resolve eq7538 ac -- subsumption resolution 7538,126
  have eq7541 : a = sk1 ∨ c = sk1 ∨ b = sk3 ∨ a = c ∨ a = sk0 := resolve eq7271 p4YZ -- subsumption resolution 7271,131
  have eq7542 : b = sk3 ∨ c = sk1 ∨ a = sk1 ∨ a = sk0 := resolve eq7541 ac -- subsumption resolution 7541,126
  have eq8394 : a ≠ sk2 ∨ b = sk1 ∨ a = sk0 := eq7478.imp_left (fun h : a = sk3 ↦ superpose h preserve_2) -- superposition 191,7478, 7478 into 191, unify on (0).2 in 7478 and (0).2 in 191
  have eq8664 : b = sk1 ∨ a = sk0 := resolve eq8394 eq7473 -- subsumption resolution 8394,7473
  have eq10723 : b ≠ sk2 ∨ c = sk1 ∨ a = sk1 ∨ a = sk0 := eq7542.imp_left (fun h : b = sk3 ↦ superpose h preserve_2) -- superposition 191,7542, 7542 into 191, unify on (0).2 in 7542 and (0).2 in 191
  have eq11069 : c = sk1 ∨ a = sk1 ∨ a = sk0 := resolve eq10723 eq7539 -- subsumption resolution 10723,7539
  have eq11098 : c = b ∨ a = b ∨ a = sk0 ∨ a = sk0 := Or.assoc3 (eq8664.imp_left (fun h : b = sk1 ↦ superpose h eq11069)) -- superposition 11069,8664, 8664 into 11069, unify on (0).2 in 8664 and (0).2 in 11069
  have eq11457 : c = b ∨ a = b ∨ a = sk0 := resolve eq11098 rfl -- duplicate literal removal 11098
  have eq11461 : a = sk0 ∨ a = b := resolve eq11457 bc -- subsumption resolution 11457,127
  have eq12009 : (old a b sk2) ∨ c = sk2 ∨ a = c ∨ a = sk1 ∨ c = sk1 ∨ a = b := Or.assoc5 (eq11461.imp_left (fun h : a = sk0 ↦ superpose h eq557)) -- superposition 557,11461, 11461 into 557, unify on (0).2 in 11461 and (0).1 in 557
  have eq12010 : (old a b sk3) ∨ c = sk3 ∨ a = c ∨ a = sk1 ∨ c = sk1 ∨ a = b := Or.assoc5 (eq11461.imp_left (fun h : a = sk0 ↦ superpose h eq560)) -- superposition 560,11461, 11461 into 560, unify on (0).2 in 11461 and (0).1 in 560
  have eq12062 : (old a b sk2) ∨ c = sk2 ∨ a = c ∨ c = sk1 ∨ a = b ∨ a = b := Or.assoc5 (eq11461.imp_left (fun h : a = sk0 ↦ superpose h eq1117)) -- superposition 1117,11461, 11461 into 1117, unify on (0).2 in 11461 and (0).1 in 1117
  have eq12063 : (old a b sk3) ∨ c = sk3 ∨ a = c ∨ c = sk1 ∨ a = b ∨ a = b := Or.assoc5 (eq11461.imp_left (fun h : a = sk0 ↦ superpose h eq1120)) -- superposition 1120,11461, 11461 into 1120, unify on (0).2 in 11461 and (0).1 in 1120
  have eq12232 : (old a b sk3) ∨ c = sk3 ∨ a = c ∨ c = sk1 ∨ a = b := resolve eq12063 rfl -- duplicate literal removal 12063
  have eq12233 : (old a b sk2) ∨ c = sk2 ∨ a = c ∨ c = sk1 ∨ a = b := resolve eq12062 rfl -- duplicate literal removal 12062
  have eq12367 : c = sk2 ∨ a = c ∨ a = sk1 ∨ c = sk1 ∨ a = b := resolve eq12009 p3 -- subsumption resolution 12009,128
  have eq12368 : c = sk2 ∨ a = sk1 ∨ c = sk1 ∨ a = b := resolve eq12367 ac -- subsumption resolution 12367,126
  have eq12369 : c = sk2 ∨ a = sk1 ∨ c = sk1 := resolve eq12368 eq553 -- subsumption resolution 12368,553
  have eq12370 : c = sk3 ∨ a = c ∨ a = sk1 ∨ c = sk1 ∨ a = b := resolve eq12010 p3 -- subsumption resolution 12010,128
  have eq12371 : c = sk3 ∨ a = sk1 ∨ c = sk1 ∨ a = b := resolve eq12370 ac -- subsumption resolution 12370,126
  have eq12372 : c = sk3 ∨ a = sk1 ∨ c = sk1 := resolve eq12371 eq553 -- subsumption resolution 12371,553
  have eq12394 : c = sk2 ∨ a = c ∨ c = sk1 ∨ a = b := resolve eq12233 p3 -- subsumption resolution 12233,128
  have eq12395 : c = sk2 ∨ c = sk1 ∨ a = b := resolve eq12394 ac -- subsumption resolution 12394,126
  have eq12396 : c = sk3 ∨ a = c ∨ c = sk1 ∨ a = b := resolve eq12232 p3 -- subsumption resolution 12232,128
  have eq12397 : c = sk3 ∨ c = sk1 ∨ a = b := resolve eq12396 ac -- subsumption resolution 12396,126
  have eq12994 : c ≠ sk2 ∨ a = sk1 ∨ c = sk1 := eq12372.imp_left (fun h : c = sk3 ↦ superpose h preserve_2) -- superposition 191,12372, 12372 into 191, unify on (0).2 in 12372 and (0).2 in 191
  have eq13224 : c = sk1 ∨ a = sk1 := resolve eq12994 eq12369 -- subsumption resolution 12994,12369
  have eq13303 : (sP6 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (old sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ (old a a b) ∨ c = b ∨ a = sk1 := Or.assoc6 (eq13224.imp_left (fun h : c = sk1 ↦ superpose h eq353)) -- superposition 353,13224, 13224 into 353, unify on (0).2 in 13224 and (0).2 in 353
  have eq13308 : (sP6 sk0 c sk3) ∨ (sP1 sk0 c sk3) ∨ (old sk0 c sk3) ∨ (sP3 sk0 c sk3) ∨ (old a a b) ∨ c = b ∨ a = sk1 := Or.assoc6 (eq13224.imp_left (fun h : c = sk1 ↦ superpose h eq363)) -- superposition 363,13224, 13224 into 363, unify on (0).2 in 13224 and (0).2 in 363
  have eq13469 : (sP4 sk0 c sk3) ∨ (old sk0 c sk3) ∨ b = sk0 ∨ c = b ∨ (old sk3 a b) ∨ a = c ∨ a = sk1 := Or.assoc6 (eq13224.imp_left (fun h : c = sk1 ↦ superpose h eq2573)) -- superposition 2573,13224, 13224 into 2573, unify on (0).2 in 13224 and (0).2 in 2573
  have eq13582 : (sP6 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ (old a a b) ∨ c = b ∨ a = sk1 := resolve eq13303 p4XZ -- subsumption resolution 13303,130
  have eq13583 : (sP6 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ (old a a b) ∨ a = sk1 := resolve eq13582 bc -- subsumption resolution 13582,127
  have eq13586 : (sP6 sk0 c sk3) ∨ (sP1 sk0 c sk3) ∨ (sP3 sk0 c sk3) ∨ (old a a b) ∨ c = b ∨ a = sk1 := resolve eq13308 p4XZ -- subsumption resolution 13308,130
  have eq13587 : (sP6 sk0 c sk3) ∨ (sP1 sk0 c sk3) ∨ (sP3 sk0 c sk3) ∨ (old a a b) ∨ a = sk1 := resolve eq13586 bc -- subsumption resolution 13586,127
  have eq13658 : (sP4 sk0 c sk3) ∨ b = sk0 ∨ c = b ∨ (old sk3 a b) ∨ a = c ∨ a = sk1 := resolve eq13469 p4XZ -- subsumption resolution 13469,130
  have eq13659 : (sP4 sk0 c sk3) ∨ b = sk0 ∨ (old sk3 a b) ∨ a = c ∨ a = sk1 := resolve eq13658 bc -- subsumption resolution 13658,127
  have eq13660 : (sP4 sk0 c sk3) ∨ b = sk0 ∨ (old sk3 a b) ∨ a = sk1 := resolve eq13659 ac -- subsumption resolution 13659,126
  have eq14079 : c ≠ sk2 ∨ c = sk1 ∨ a = b := eq12397.imp_left (fun h : c = sk3 ↦ superpose h preserve_2) -- superposition 191,12397, 12397 into 191, unify on (0).2 in 12397 and (0).2 in 191
  have eq14287 : c = sk1 ∨ a = b := resolve eq14079 eq12395 -- subsumption resolution 14079,12395
  have eq14515 : (sP1 sk0 c sk2) ∨ (old sk0 c sk2) ∨ a = c ∨ c = b ∨ (old sk2 a b) ∨ a = sk2 ∨ a = b := Or.assoc6 (eq14287.imp_left (fun h : c = sk1 ↦ superpose h eq2347)) -- superposition 2347,14287, 14287 into 2347, unify on (0).2 in 14287 and (0).2 in 2347
  have eq14517 : (sP4 sk0 c sk2) ∨ (old sk0 c sk2) ∨ b = sk0 ∨ c = b ∨ (old sk2 a b) ∨ a = c ∨ a = b := Or.assoc6 (eq14287.imp_left (fun h : c = sk1 ↦ superpose h eq2389)) -- superposition 2389,14287, 14287 into 2389, unify on (0).2 in 14287 and (0).2 in 2389
  have eq14531 : (sP1 sk0 c sk3) ∨ (old sk0 c sk3) ∨ a = c ∨ c = b ∨ (old sk3 a b) ∨ a = sk3 ∨ a = b := Or.assoc6 (eq14287.imp_left (fun h : c = sk1 ↦ superpose h eq2546)) -- superposition 2546,14287, 14287 into 2546, unify on (0).2 in 14287 and (0).2 in 2546
  have eq14742 : (sP1 sk0 c sk2) ∨ a = c ∨ c = b ∨ (old sk2 a b) ∨ a = sk2 ∨ a = b := resolve eq14515 p4XZ -- subsumption resolution 14515,130
  have eq14743 : (sP1 sk0 c sk2) ∨ c = b ∨ (old sk2 a b) ∨ a = sk2 ∨ a = b := resolve eq14742 ac -- subsumption resolution 14742,126
  have eq14744 : (sP1 sk0 c sk2) ∨ (old sk2 a b) ∨ a = sk2 ∨ a = b := resolve eq14743 bc -- subsumption resolution 14743,127
  have eq14748 : (sP4 sk0 c sk2) ∨ b = sk0 ∨ c = b ∨ (old sk2 a b) ∨ a = c ∨ a = b := resolve eq14517 p4XZ -- subsumption resolution 14517,130
  have eq14749 : (sP4 sk0 c sk2) ∨ b = sk0 ∨ (old sk2 a b) ∨ a = c ∨ a = b := resolve eq14748 bc -- subsumption resolution 14748,127
  have eq14750 : (sP4 sk0 c sk2) ∨ b = sk0 ∨ (old sk2 a b) ∨ a = b := resolve eq14749 ac -- subsumption resolution 14749,126
  have eq14764 : (sP1 sk0 c sk3) ∨ a = c ∨ c = b ∨ (old sk3 a b) ∨ a = sk3 ∨ a = b := resolve eq14531 p4XZ -- subsumption resolution 14531,130
  have eq14765 : (sP1 sk0 c sk3) ∨ c = b ∨ (old sk3 a b) ∨ a = sk3 ∨ a = b := resolve eq14764 ac -- subsumption resolution 14764,126
  have eq14766 : (sP1 sk0 c sk3) ∨ (old sk3 a b) ∨ a = sk3 ∨ a = b := resolve eq14765 bc -- subsumption resolution 14765,127
  have eq22834 : (sP1 a c sk2) ∨ (old sk2 a b) ∨ a = sk2 ∨ a = b ∨ a = b := Or.assoc4 (eq11461.imp_left (fun h : a = sk0 ↦ superpose h eq14744)) -- superposition 14744,11461, 11461 into 14744, unify on (0).2 in 11461 and (0).1 in 14744
  have eq22847 : (sP1 a c sk2) ∨ (old sk2 a b) ∨ a = sk2 ∨ a = b := resolve eq22834 rfl -- duplicate literal removal 22834
  have eq22848 : (old sk2 a b) ∨ a = sk2 ∨ a = b := resolve eq22847 rule_def_1_0 -- subsumption resolution 22847,149
  have eq22945 (X0 : G) : ¬(old X0 a b) ∨ a = b ∨ sk2 = X0 ∨ a = sk2 := resolve eq22848 old_8 -- resolution 22848,140
  have eq25256 : (sP4 a c sk2) ∨ a = b ∨ (old sk2 a b) ∨ a = b ∨ a = b := Or.assoc4 (eq11461.imp_left (fun h : a = sk0 ↦ superpose h eq14750)) -- superposition 14750,11461, 11461 into 14750, unify on (0).2 in 11461 and (0).1 in 14750
  have eq25271 : (sP4 a c sk2) ∨ a = b ∨ (old sk2 a b) := resolve eq25256 rfl -- duplicate literal removal 25256
  have eq25379 : (old sk2 a b) ∨ a = b ∨ (old a a b) := resolve eq25271 rule_def_4_3 -- resolution 25271,166
  have eq26500 : (sP1 a c sk3) ∨ (old sk3 a b) ∨ a = sk3 ∨ a = b ∨ a = b := Or.assoc4 (eq11461.imp_left (fun h : a = sk0 ↦ superpose h eq14766)) -- superposition 14766,11461, 11461 into 14766, unify on (0).2 in 11461 and (0).1 in 14766
  have eq26512 : (sP1 a c sk3) ∨ (old sk3 a b) ∨ a = sk3 ∨ a = b := resolve eq26500 rfl -- duplicate literal removal 26500
  have eq26513 : (old sk3 a b) ∨ a = sk3 ∨ a = b := resolve eq26512 rule_def_1_0 -- subsumption resolution 26512,149
  have eq26618 (X0 : G) : ¬(old X0 a b) ∨ a = b ∨ sk3 = X0 ∨ a = sk3 := resolve eq26513 old_8 -- resolution 26513,140
  have eq27482 : a = b ∨ sk2 = sk3 ∨ a = sk3 ∨ a = b ∨ (old a a b) := resolve eq26618 eq25379 -- resolution 26618,25379
  have eq27496 : a = b ∨ sk2 = sk3 ∨ a = sk3 ∨ (old a a b) := resolve eq27482 rfl -- duplicate literal removal 27482
  have eq27505 : a = b ∨ a = sk3 ∨ (old a a b) := resolve eq27496 preserve_2 -- subsumption resolution 27496,191
  have eq27506 : a = sk3 ∨ a = b := resolve eq27505 eq26618 -- subsumption resolution 27505,26618
  have eq27549 : a ≠ sk2 ∨ a = b := eq27506.imp_left (fun h : a = sk3 ↦ superpose h preserve_2) -- superposition 191,27506, 27506 into 191, unify on (0).2 in 27506 and (0).2 in 191
  have eq27804 : (sP4 sk0 c a) ∨ b = sk0 ∨ (old a a b) ∨ a = sk1 ∨ a = b := Or.assoc4 (eq27506.imp_left (fun h : a = sk3 ↦ superpose h eq13660)) -- superposition 13660,27506, 27506 into 13660, unify on (0).2 in 27506 and (0).3 in 13660
  have eq27923 : (old a a b) ∨ b = sk0 ∨ a = sk1 ∨ a = b := resolve eq27804 rule_def_4_3 -- subsumption resolution 27804,166
  have eq28105 : b = sk0 ∨ a = sk1 ∨ a = b ∨ a = b ∨ a = sk2 ∨ a = sk2 := resolve eq27923 eq22945 -- resolution 27923,22945
  have eq28118 : b = sk0 ∨ a = sk1 ∨ a = b ∨ a = sk2 := resolve eq28105 rfl -- duplicate literal removal 28105
  have eq28123 : a = sk1 ∨ b = sk0 ∨ a = b := resolve eq28118 eq27549 -- subsumption resolution 28118,27549
  have eq28139 : a = c ∨ b = sk0 ∨ a = b ∨ a = b := Or.assoc3 (eq14287.imp_left (fun h : c = sk1 ↦ superpose h eq28123)) -- superposition 28123,14287, 14287 into 28123, unify on (0).2 in 14287 and (0).2 in 28123
  have eq28890 : a = c ∨ b = sk0 ∨ a = b := resolve eq28139 rfl -- duplicate literal removal 28139
  have eq28899 : b = sk0 ∨ a = b := resolve eq28890 ac -- subsumption resolution 28890,126
  have eq28917 : a = b ∨ a = b ∨ a = b := Or.assoc2 (eq11461.imp_left (fun h : a = sk0 ↦ superpose h eq28899)) -- superposition 28899,11461, 11461 into 28899, unify on (0).2 in 11461 and (0).2 in 28899
  have eq29493 : a = b := resolve eq28917 rfl -- duplicate literal removal 28917
  have eq29495 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq29493, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 128,29493
  have eq29498 : ∀ (X0 X1 X2 : G) , ¬(sP1 X0 X1 X2) ∨ (old X2 a a) := Eq.mp (by simp only [eq29493, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_1_2 -- backward demodulation 151,29493
  have eq29501 : ∀ (X0 X1 X2 : G) , (old a a a) ∨ ¬(sP2 X0 X1 X2) := Eq.mp (by simp only [eq29493, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_2_3 -- backward demodulation 156,29493
  have eq29503 : ∀ (X0 X1 X2 : G) , (old a a a) ∨ ¬(sP3 X0 X1 X2) := Eq.mp (by simp only [eq29493, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_3_3 -- backward demodulation 161,29493
  have eq29505 : ∀ (X0 X1 X2 : G) , (old a a a) ∨ ¬(sP5 X0 X1 X2) := Eq.mp (by simp only [eq29493, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_5_3 -- backward demodulation 171,29493
  have eq29506 : ∀ (X0 X1 X2 : G) , (old a a a) ∨ ¬(sP6 X0 X1 X2) := Eq.mp (by simp only [eq29493, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_6_2 -- backward demodulation 175,29493
  have eq30654 : (old sk2 a a) ∨ (sP5 c sk1 sk2) ∨ (sP2 c sk1 sk2) ∨ a = sk0 := Eq.mp (by simp only [eq29493, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq7422 -- backward demodulation 7422,29493
  have eq30665 : (old sk3 a a) ∨ (sP5 c sk1 sk3) ∨ (sP2 c sk1 sk3) ∨ a = sk0 := Eq.mp (by simp only [eq29493, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq7440 -- backward demodulation 7440,29493
  have eq30968 : (old a a a) ∨ (sP6 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ a = sk1 := Eq.mp (by simp only [eq29493, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq13583 -- backward demodulation 13583,29493
  have eq30971 : (old a a a) ∨ (sP6 sk0 c sk3) ∨ (sP1 sk0 c sk3) ∨ (sP3 sk0 c sk3) ∨ a = sk1 := Eq.mp (by simp only [eq29493, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq13587 -- backward demodulation 13587,29493
  have eq31604 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) := resolve eq29501 eq29495 -- subsumption resolution 29501,29495
  have eq31605 (X0 X1 X2 : G) : ¬(sP3 X0 X1 X2) := resolve eq29503 eq29495 -- subsumption resolution 29503,29495
  have eq31607 (X0 X1 X2 : G) : ¬(sP5 X0 X1 X2) := resolve eq29505 eq29495 -- subsumption resolution 29505,29495
  have eq31608 (X0 X1 X2 : G) : ¬(sP6 X0 X1 X2) := resolve eq29506 eq29495 -- subsumption resolution 29506,29495
  have eq32722 : (old sk2 a a) ∨ (sP2 c sk1 sk2) ∨ a = sk0 := resolve eq30654 eq31607 -- subsumption resolution 30654,31607
  have eq32723 : (old sk2 a a) ∨ a = sk0 := resolve eq32722 eq31604 -- subsumption resolution 32722,31604
  have eq32732 : (old sk3 a a) ∨ (sP2 c sk1 sk3) ∨ a = sk0 := resolve eq30665 eq31607 -- subsumption resolution 30665,31607
  have eq32733 : (old sk3 a a) ∨ a = sk0 := resolve eq32732 eq31604 -- subsumption resolution 32732,31604
  have eq33128 : (sP6 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ a = sk1 := resolve eq30968 eq29495 -- subsumption resolution 30968,29495
  have eq33129 : (sP1 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ a = sk1 := resolve eq33128 eq31608 -- subsumption resolution 33128,31608
  have eq33130 : (sP1 sk0 c sk2) ∨ a = sk1 := resolve eq33129 eq31605 -- subsumption resolution 33129,31605
  have eq33137 : (sP6 sk0 c sk3) ∨ (sP1 sk0 c sk3) ∨ (sP3 sk0 c sk3) ∨ a = sk1 := resolve eq30971 eq29495 -- subsumption resolution 30971,29495
  have eq33138 : (sP1 sk0 c sk3) ∨ (sP3 sk0 c sk3) ∨ a = sk1 := resolve eq33137 eq31608 -- subsumption resolution 33137,31608
  have eq33139 : (sP1 sk0 c sk3) ∨ a = sk1 := resolve eq33138 eq31605 -- subsumption resolution 33138,31605
  have eq33738 (X0 : G) : ¬(old X0 a a) ∨ sk2 = X0 ∨ a = sk0 := resolve eq32723 old_8 -- resolution 32723,140
  have eq34145 : (old sk2 a a) ∨ a = sk1 := resolve eq33130 eq29498 -- resolution 33130,29498
  have eq34166 : (old sk3 a a) ∨ a = sk1 := resolve eq33139 eq29498 -- resolution 33139,29498
  have eq34198 (X0 : G) : ¬(old X0 a a) ∨ sk2 = X0 ∨ a = sk1 := resolve eq34145 old_8 -- resolution 34145,140
  have eq34566 : sk2 = sk3 ∨ a = sk0 ∨ a = sk0 := resolve eq33738 eq32733 -- resolution 33738,32733
  have eq34567 : sk2 = sk3 ∨ a = sk0 := resolve eq34566 rfl -- duplicate literal removal 34566
  have eq34575 : a = sk0 := resolve eq34567 preserve_2 -- subsumption resolution 34567,191
  have eq34586 : (old a sk1 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := Eq.mp (by simp only [eq34575, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq311 -- backward demodulation 311,34575
  have eq34598 : (old a sk1 sk3) ∨ c = sk3 ∨ c = sk0 ∨ c = sk1 := Eq.mp (by simp only [eq34575, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq435 -- backward demodulation 435,34575
  have eq34843 : a = c ∨ (old a sk1 sk2) ∨ c = sk2 ∨ c = sk1 := Eq.mp (by simp only [eq34575, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq34586 -- forward demodulation 34586,34575
  have eq34844 : (old a sk1 sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq34843 ac -- subsumption resolution 34843,126
  have eq34873 : a = c ∨ (old a sk1 sk3) ∨ c = sk3 ∨ c = sk1 := Eq.mp (by simp only [eq34575, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq34598 -- forward demodulation 34598,34575
  have eq34874 : (old a sk1 sk3) ∨ c = sk3 ∨ c = sk1 := resolve eq34873 ac -- subsumption resolution 34873,126
  have eq35173 : sk2 = sk3 ∨ a = sk1 ∨ a = sk1 := resolve eq34198 eq34166 -- resolution 34198,34166
  have eq35174 : sk2 = sk3 ∨ a = sk1 := resolve eq35173 rfl -- duplicate literal removal 35173
  have eq35180 : a = sk1 := resolve eq35174 preserve_2 -- subsumption resolution 35174,191
  have eq35218 : a = c ∨ (old a sk1 sk2) ∨ c = sk2 := Eq.mp (by simp only [eq35180, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq34844 -- backward demodulation 34844,35180
  have eq35225 : a = c ∨ (old a sk1 sk3) ∨ c = sk3 := Eq.mp (by simp only [eq35180, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq34874 -- backward demodulation 34874,35180
  have eq35280 : (old a sk1 sk2) ∨ c = sk2 := resolve eq35218 ac -- subsumption resolution 35218,126
  have eq35281 : (old a a sk2) ∨ c = sk2 := Eq.mp (by simp only [eq35180, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq35280 -- forward demodulation 35280,35180
  have eq35282 : c = sk2 := resolve eq35281 eq29495 -- subsumption resolution 35281,29495
  have eq35283 : c ≠ sk3 := Eq.mp (by simp only [eq35282, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_2 -- backward demodulation 191,35282
  have eq35290 : (old a sk1 sk3) ∨ c = sk3 := resolve eq35225 ac -- subsumption resolution 35225,126
  have eq35291 : (old a sk1 sk3) := resolve eq35290 eq35283 -- subsumption resolution 35290,35283
  have eq35292 : (old a a sk3) := Eq.mp (by simp only [eq35180, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq35291 -- forward demodulation 35291,35180
  subsumption eq29495 eq35292 -- subsumption resolution 35292,29495

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (old_1 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X2 X1 X3 ∨ old X1 X3 X0)) (old_3 : (∀ X0 X1, ¬ old X0 X1 X1 ∨ old X1 X0 X1)) (old_8 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X3 = X0)) (imp_new_1 : ∀ X Y Z, a ≠ X ∨ b ≠ Y ∨ c ≠ Z ∨ new X Y Z) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z, b ≠ X ∨ c ≠ Y ∨ ¬ old Z b a ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), b = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z b a ∨ ¬sP1 X Y Z) (imp_new_3 : ∀ X Y Z, c ≠ X ∨ b ≠ Y ∨ b ≠ Z ∨ ¬ old b b a ∨ new X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b b a ∨ ¬sP2 X Y Z) (imp_new_4 : ∀ X Y Z, b ≠ X ∨ a ≠ Y ∨ c ≠ Z ∨ ¬ old b b a ∨ new X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), b = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b b a ∨ ¬sP3 X Y Z) (imp_new_5 : ∀ X Y Z, a ≠ X ∨ c ≠ Y ∨ a ≠ Z ∨ ¬ old a a b ∨ new X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), old a a b ∨ ¬sP4 X Y Z) (imp_new_6 : ∀ X Y Z, c ≠ X ∨ a ≠ Y ∨ a ≠ Z ∨ ¬ old a a b ∨ new X Y Z) (rule_def_5_0 : ∀ (X Y Z : G), c = X ∨ ¬sP5 X Y Z) (rule_def_5_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP5 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), old a a b ∨ ¬sP5 X Y Z) (imp_new_7 : ∀ X Y Z, a ≠ X ∨ c ≠ Y ∨ ¬ old b b a ∨ ¬ old Z a b ∨ new X Y Z) (rule_def_6_0 : ∀ (X Y Z : G), a = X ∨ ¬sP6 X Y Z) (rule_def_6_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP6 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), old b b a ∨ ¬sP6 X Y Z) (rule_def_6_3 : ∀ (X Y Z : G), old Z a b ∨ ¬sP6 X Y Z) (rule_def_7_0 : ∀ (X Y Z : G), a = b ∨ ¬sP7 X Y Z) (rule_def_7_1 : ∀ (X Y Z : G), c = X ∨ ¬sP7 X Y Z) (rule_def_7_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP7 X Y Z) (rule_def_7_3 : ∀ (X Y Z : G), old Z b b ∨ ¬sP7 X Y Z) (imp_new_9 : ∀ X Y Z, b ≠ X ∨ a ≠ Y ∨ c ≠ Z ∨ ¬ old a a b ∨ new X Y Z) (rule_def_8_0 : ∀ (X Y Z : G), b = X ∨ ¬sP8 X Y Z) (rule_def_8_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP8 X Y Z) (rule_def_8_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP8 X Y Z) (rule_def_8_3 : ∀ (X Y Z : G), old a a b ∨ ¬sP8 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X2 X1 X3 ∨ new X1 X3 X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq195 (X0 X1 : G) : (new X0 X1 c) ∨ b ≠ X1 ∨ a ≠ X0 := resolve imp_new_1 rfl -- equality resolution 146
  have eq196 (X0 : G) : (new X0 b c) ∨ a ≠ X0 := resolve eq195 rfl -- equality resolution 195
  have eq197 : (new a b c) := resolve eq196 rfl -- equality resolution 196
  have eq198 (X0 X2 : G) : (new X0 c X2) ∨ ¬(old X2 b a) ∨ b ≠ X0 := resolve imp_new_2 rfl -- equality resolution 150
  have eq199 (X2 : G) : ¬(old X2 b a) ∨ (new b c X2) := resolve eq198 rfl -- equality resolution 198
  have eq200 (X0 X1 : G) : (new X0 X1 b) ∨ ¬(old b b a) ∨ b ≠ X1 ∨ c ≠ X0 := resolve imp_new_3 rfl -- equality resolution 154
  have eq201 (X0 : G) : (new X0 b b) ∨ ¬(old b b a) ∨ c ≠ X0 := resolve eq200 rfl -- equality resolution 200
  have eq202 : ¬(old b b a) ∨ (new c b b) := resolve eq201 rfl -- equality resolution 201
  have eq203 (X0 X1 : G) : (new X0 X1 c) ∨ ¬(old b b a) ∨ a ≠ X1 ∨ b ≠ X0 := resolve imp_new_4 rfl -- equality resolution 159
  have eq204 (X0 : G) : (new X0 a c) ∨ ¬(old b b a) ∨ b ≠ X0 := resolve eq203 rfl -- equality resolution 203
  have eq205 : ¬(old b b a) ∨ (new b a c) := resolve eq204 rfl -- equality resolution 204
  have eq206 (X0 X1 : G) : (new X0 X1 a) ∨ ¬(old a a b) ∨ c ≠ X1 ∨ a ≠ X0 := resolve imp_new_5 rfl -- equality resolution 164
  have eq207 (X0 : G) : (new X0 c a) ∨ ¬(old a a b) ∨ a ≠ X0 := resolve eq206 rfl -- equality resolution 206
  have eq208 : ¬(old a a b) ∨ (new a c a) := resolve eq207 rfl -- equality resolution 207
  have eq209 (X0 X1 : G) : (new X0 X1 a) ∨ ¬(old a a b) ∨ a ≠ X1 ∨ c ≠ X0 := resolve imp_new_6 rfl -- equality resolution 169
  have eq210 (X0 : G) : (new X0 a a) ∨ ¬(old a a b) ∨ c ≠ X0 := resolve eq209 rfl -- equality resolution 209
  have eq211 : ¬(old a a b) ∨ (new c a a) := resolve eq210 rfl -- equality resolution 210
  have eq212 (X0 X2 : G) : (new X0 c X2) ∨ ¬(old X2 a b) ∨ ¬(old b b a) ∨ a ≠ X0 := resolve imp_new_7 rfl -- equality resolution 174
  have eq213 (X2 : G) : ¬(old b b a) ∨ ¬(old X2 a b) ∨ (new a c X2) := resolve eq212 rfl -- equality resolution 212
  have eq216 (X0 X1 : G) : (new X0 X1 c) ∨ ¬(old a a b) ∨ a ≠ X1 ∨ b ≠ X0 := resolve imp_new_9 rfl -- equality resolution 184
  have eq217 (X0 : G) : (new X0 a c) ∨ ¬(old a a b) ∨ b ≠ X0 := resolve eq216 rfl -- equality resolution 216
  have eq218 : ¬(old a a b) ∨ (new b a c) := resolve eq217 rfl -- equality resolution 217
  have eq219 (X0 : G) : ¬(new sk0 sk1 X0) ∨ sk2 = X0 := resolve prev_0 preserve_0 -- resolution 191,192
  have eq220 (X0 : G) : ¬(new sk2 sk1 X0) ∨ sk3 = X0 := resolve prev_0 preserve_1 -- resolution 191,193
  have eq221 (X0 : G) : ¬(new a b X0) ∨ c = X0 := resolve prev_0 eq197 -- resolution 191,197
  have eq225 : (sP8 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 190,192
  have eq226 : (sP8 sk2 sk1 sk3) ∨ (sP6 sk2 sk1 sk3) ∨ (sP5 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP7 sk2 sk1 sk3) := resolve new_imp preserve_1 -- resolution 190,193
  have eq244 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (old a a b) := resolve eq225 rule_def_8_3 -- resolution 225,188
  have eq245 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ c = sk2 := resolve eq225 rule_def_8_2 -- resolution 225,187
  have eq246 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ a = sk1 := resolve eq225 rule_def_8_1 -- resolution 225,186
  have eq247 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ b = sk0 := resolve eq225 rule_def_8_0 -- resolution 225,185
  have eq248 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (old a a b) := resolve eq244 rule_def_4_3 -- subsumption resolution 244,168
  have eq249 : (sP7 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (old a a b) := resolve eq248 rule_def_5_3 -- subsumption resolution 248,173
  have eq250 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ c = sk2 := resolve eq245 rule_def_3_2 -- subsumption resolution 245,162
  have eq251 : (sP7 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ c = sk2 := resolve eq250 rule_def_0_2 -- subsumption resolution 250,149
  have eq252 : (sP6 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ a = sk1 := resolve eq246 rule_def_5_1 -- subsumption resolution 246,171
  have eq253 : (sP7 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ a = sk1 := resolve eq252 rule_def_3_1 -- subsumption resolution 252,161
  have eq254 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ b = sk0 := resolve eq247 rule_def_3_0 -- subsumption resolution 247,160
  have eq255 : (sP7 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ b = sk0 := resolve eq254 rule_def_1_0 -- subsumption resolution 254,151
  have eq261 : (sP6 sk2 sk1 sk3) ∨ (sP5 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP7 sk2 sk1 sk3) ∨ (old a a b) := resolve eq226 rule_def_8_3 -- resolution 226,188
  have eq262 : (sP6 sk2 sk1 sk3) ∨ (sP5 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP7 sk2 sk1 sk3) ∨ c = sk3 := resolve eq226 rule_def_8_2 -- resolution 226,187
  have eq263 : (sP6 sk2 sk1 sk3) ∨ (sP5 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP7 sk2 sk1 sk3) ∨ a = sk1 := resolve eq226 rule_def_8_1 -- resolution 226,186
  have eq264 : (sP6 sk2 sk1 sk3) ∨ (sP5 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP7 sk2 sk1 sk3) ∨ b = sk2 := resolve eq226 rule_def_8_0 -- resolution 226,185
  have eq265 : (sP6 sk2 sk1 sk3) ∨ (sP5 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP7 sk2 sk1 sk3) ∨ (old a a b) := resolve eq261 rule_def_4_3 -- subsumption resolution 261,168
  have eq266 : (sP7 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP6 sk2 sk1 sk3) ∨ (old a a b) := resolve eq265 rule_def_5_3 -- subsumption resolution 265,173
  have eq267 : (sP6 sk2 sk1 sk3) ∨ (sP5 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP7 sk2 sk1 sk3) ∨ c = sk3 := resolve eq262 rule_def_3_2 -- subsumption resolution 262,162
  have eq268 : (sP7 sk2 sk1 sk3) ∨ (sP5 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP6 sk2 sk1 sk3) ∨ c = sk3 := resolve eq267 rule_def_0_2 -- subsumption resolution 267,149
  have eq269 : (sP6 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP7 sk2 sk1 sk3) ∨ a = sk1 := resolve eq263 rule_def_5_1 -- subsumption resolution 263,171
  have eq270 : (sP7 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP6 sk2 sk1 sk3) ∨ a = sk1 := resolve eq269 rule_def_3_1 -- subsumption resolution 269,161
  have eq271 : (sP6 sk2 sk1 sk3) ∨ (sP5 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP7 sk2 sk1 sk3) ∨ b = sk2 := resolve eq264 rule_def_3_0 -- subsumption resolution 264,160
  have eq272 : (sP7 sk2 sk1 sk3) ∨ (sP5 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP6 sk2 sk1 sk3) ∨ b = sk2 := resolve eq271 rule_def_1_0 -- subsumption resolution 271,151
  have eq288 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 := resolve eq251 rule_def_7_1 -- resolution 251,181
  have eq289 : (sP6 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ c = sk2 ∨ a = b := resolve eq251 rule_def_7_0 -- resolution 251,180
  have eq291 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 := resolve eq288 rule_def_5_0 -- subsumption resolution 288,170
  have eq292 : (sP6 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 := resolve eq291 rule_def_2_0 -- subsumption resolution 291,155
  have eq297 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 := resolve eq253 rule_def_7_2 -- resolution 253,182
  have eq298 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ a = sk1 ∨ c = sk0 := resolve eq253 rule_def_7_1 -- resolution 253,181
  have eq299 : (sP6 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk1 ∨ a = b := resolve eq253 rule_def_7_0 -- resolution 253,180
  have eq300 : (sP4 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 := resolve eq297 rule_def_2_1 -- subsumption resolution 297,156
  have eq301 : (sP6 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 := resolve eq300 rule_def_0_1 -- subsumption resolution 300,148
  have eq302 : (sP6 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk1 ∨ c = sk0 := resolve eq298 rule_def_2_0 -- subsumption resolution 298,155
  have eq307 : (sP6 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ b = sk0 ∨ (old sk2 b b) := resolve eq255 rule_def_7_3 -- resolution 255,183
  have eq308 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 := resolve eq255 rule_def_7_2 -- resolution 255,182
  have eq309 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ b = sk0 ∨ c = sk0 := resolve eq255 rule_def_7_1 -- resolution 255,181
  have eq310 : (sP6 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ b = sk0 ∨ a = b := resolve eq255 rule_def_7_0 -- resolution 255,180
  have eq311 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 := resolve eq308 rule_def_2_1 -- subsumption resolution 308,156
  have eq312 : (sP6 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 := resolve eq311 rule_def_0_1 -- subsumption resolution 311,148
  have eq313 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ b = sk0 ∨ c = sk0 := resolve eq309 rule_def_5_0 -- subsumption resolution 309,170
  have eq314 : (sP6 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk0 ∨ c = sk0 := resolve eq313 rule_def_2_0 -- subsumption resolution 313,155
  have eq317 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq292 rule_def_6_1 -- resolution 292,176
  have eq319 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq317 rule_def_4_1 -- subsumption resolution 317,166
  have eq320 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq319 rule_def_1_1 -- subsumption resolution 319,152
  have eq324 : (sP5 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP6 sk2 sk1 sk3) ∨ c = sk3 ∨ c = sk2 := resolve eq268 rule_def_7_1 -- resolution 268,181
  have eq327 : (sP4 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP6 sk2 sk1 sk3) ∨ c = sk3 ∨ c = sk2 := resolve eq324 rule_def_5_0 -- subsumption resolution 324,170
  have eq328 : (sP6 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ c = sk3 ∨ c = sk2 := resolve eq327 rule_def_2_0 -- subsumption resolution 327,155
  have eq339 : (sP4 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP6 sk2 sk1 sk3) ∨ a = sk1 ∨ b = sk1 := resolve eq270 rule_def_7_2 -- resolution 270,182
  have eq340 : (sP4 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP6 sk2 sk1 sk3) ∨ a = sk1 ∨ c = sk2 := resolve eq270 rule_def_7_1 -- resolution 270,181
  have eq341 : (sP6 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ a = sk1 ∨ a = b := resolve eq270 rule_def_7_0 -- resolution 270,180
  have eq342 : (sP4 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP6 sk2 sk1 sk3) ∨ a = sk1 ∨ b = sk1 := resolve eq339 rule_def_2_1 -- subsumption resolution 339,156
  have eq343 : (sP6 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ a = sk1 ∨ b = sk1 := resolve eq342 rule_def_0_1 -- subsumption resolution 342,148
  have eq344 : (sP6 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ a = sk1 ∨ c = sk2 := resolve eq340 rule_def_2_0 -- subsumption resolution 340,155
  have eq347 : (sP6 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP5 sk2 sk1 sk3) ∨ b = sk2 ∨ (old sk3 b b) := resolve eq272 rule_def_7_3 -- resolution 272,183
  have eq348 : (sP5 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP6 sk2 sk1 sk3) ∨ b = sk2 ∨ b = sk1 := resolve eq272 rule_def_7_2 -- resolution 272,182
  have eq349 : (sP5 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP6 sk2 sk1 sk3) ∨ b = sk2 ∨ c = sk2 := resolve eq272 rule_def_7_1 -- resolution 272,181
  have eq351 : (sP5 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP6 sk2 sk1 sk3) ∨ b = sk2 ∨ b = sk1 := resolve eq348 rule_def_2_1 -- subsumption resolution 348,156
  have eq352 : (sP6 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP5 sk2 sk1 sk3) ∨ b = sk2 ∨ b = sk1 := resolve eq351 rule_def_0_1 -- subsumption resolution 351,148
  have eq353 : (sP4 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP6 sk2 sk1 sk3) ∨ b = sk2 ∨ c = sk2 := resolve eq349 rule_def_5_0 -- subsumption resolution 349,170
  have eq354 : (sP6 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk2 ∨ c = sk2 := resolve eq353 rule_def_2_0 -- subsumption resolution 353,155
  have eq358 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 := resolve eq249 rule_def_7_2 -- resolution 249,182
  have eq361 : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 := resolve eq358 rule_def_2_1 -- subsumption resolution 358,156
  have eq362 : (sP6 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 := resolve eq361 rule_def_0_1 -- subsumption resolution 361,148
  have eq368 : (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP6 sk2 sk1 sk3) ∨ (old a a b) ∨ b = sk1 := resolve eq266 rule_def_7_2 -- resolution 266,182
  have eq371 : (sP3 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP6 sk2 sk1 sk3) ∨ (old a a b) ∨ b = sk1 := resolve eq368 rule_def_2_1 -- subsumption resolution 368,156
  have eq372 : (sP6 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (old a a b) ∨ b = sk1 := resolve eq371 rule_def_0_1 -- subsumption resolution 371,148
  have eq387 : (sP4 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ (old sk2 a b) := resolve eq301 rule_def_6_3 -- resolution 301,178
  have eq389 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 := resolve eq301 rule_def_6_1 -- resolution 301,176
  have eq390 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ a = sk0 := resolve eq301 rule_def_6_0 -- resolution 301,175
  have eq391 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 := resolve eq389 rule_def_4_1 -- subsumption resolution 389,166
  have eq392 : (old sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 := resolve eq391 rule_def_1_1 -- subsumption resolution 391,152
  have eq393 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ a = sk0 := resolve eq390 rule_def_4_0 -- subsumption resolution 390,165
  have eq407 : (sP5 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 ∨ (old sk2 a b) := resolve eq312 rule_def_6_3 -- resolution 312,178
  have eq410 : (sP4 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 ∨ a = sk0 := resolve eq312 rule_def_6_0 -- resolution 312,175
  have eq412 : (sP5 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 ∨ a = sk0 := resolve eq410 rule_def_4_0 -- subsumption resolution 410,165
  have eq420 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 := resolve eq314 rule_def_6_1 -- resolution 314,176
  have eq421 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq314 rule_def_6_0 -- resolution 314,175
  have eq422 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk0 ∨ c = sk0 ∨ c = sk1 := resolve eq420 rule_def_4_1 -- subsumption resolution 420,166
  have eq423 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq421 rule_def_4_0 -- subsumption resolution 421,165
  have eq424 : (old sk0 sk1 sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq423 rule_def_0_0 -- subsumption resolution 423,147
  have eq434 (X0 : G) : ¬(old X0 sk1 sk2) ∨ c = sk0 ∨ a = sk0 ∨ sk0 = X0 ∨ b = sk0 := resolve eq424 old_8 -- resolution 424,142
  have eq441 : (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 := resolve eq328 rule_def_6_1 -- resolution 328,176
  have eq443 : (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 := resolve eq441 rule_def_4_1 -- subsumption resolution 441,166
  have eq444 : (old sk2 sk1 sk3) ∨ c = sk3 ∨ c = sk2 ∨ c = sk1 := resolve eq443 rule_def_1_1 -- subsumption resolution 443,152
  have eq447 (X0 : G) : ¬(old X0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ (old sk1 sk3 X0) ∨ c = sk3 := resolve eq444 old_1 -- resolution 444,135
  have eq457 : (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 := resolve eq343 rule_def_6_1 -- resolution 343,176
  have eq458 : (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ a = sk1 ∨ b = sk1 ∨ a = sk2 := resolve eq343 rule_def_6_0 -- resolution 343,175
  have eq459 : (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 := resolve eq457 rule_def_4_1 -- subsumption resolution 457,166
  have eq460 : (old sk2 sk1 sk3) ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 := resolve eq459 rule_def_1_1 -- subsumption resolution 459,152
  have eq461 : (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ a = sk1 ∨ b = sk1 ∨ a = sk2 := resolve eq458 rule_def_4_0 -- subsumption resolution 458,165
  have eq463 (X0 : G) : ¬(old X0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ (old sk1 sk3 X0) ∨ a = sk1 := resolve eq460 old_1 -- resolution 460,135
  have eq471 : (sP5 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk2 ∨ b = sk1 ∨ (old sk3 a b) := resolve eq352 rule_def_6_3 -- resolution 352,178
  have eq474 : (sP4 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP5 sk2 sk1 sk3) ∨ b = sk2 ∨ b = sk1 ∨ a = sk2 := resolve eq352 rule_def_6_0 -- resolution 352,175
  have eq476 : (sP5 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ b = sk2 ∨ b = sk1 ∨ a = sk2 := resolve eq474 rule_def_4_0 -- subsumption resolution 474,165
  have eq486 : (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk2 ∨ c = sk2 ∨ a = sk2 := resolve eq354 rule_def_6_0 -- resolution 354,175
  have eq488 : (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ b = sk2 ∨ c = sk2 ∨ a = sk2 := resolve eq486 rule_def_4_0 -- subsumption resolution 486,165
  have eq489 : (old sk2 sk1 sk3) ∨ b = sk2 ∨ c = sk2 ∨ a = sk2 := resolve eq488 rule_def_0_0 -- subsumption resolution 488,147
  have eq500 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 ∨ (old b b a) := resolve eq362 rule_def_6_2 -- resolution 362,177
  have eq501 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 ∨ c = sk1 := resolve eq362 rule_def_6_1 -- resolution 362,176
  have eq503 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 ∨ (old b b a) := resolve eq500 rule_def_3_3 -- subsumption resolution 500,163
  have eq504 : (sP3 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 ∨ c = sk1 := resolve eq501 rule_def_1_1 -- subsumption resolution 501,152
  have eq514 : (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (old a a b) ∨ b = sk1 ∨ c = sk1 := resolve eq372 rule_def_6_1 -- resolution 372,176
  have eq517 : (sP3 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (old a a b) ∨ b = sk1 ∨ c = sk1 := resolve eq514 rule_def_1_1 -- subsumption resolution 514,152
  have eq552 : (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq302 rule_def_6_0 -- resolution 302,175
  have eq555 : (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq552 rule_def_4_0 -- subsumption resolution 552,165
  have eq556 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq555 rule_def_0_0 -- subsumption resolution 555,147
  have eq577 : (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ a = sk1 ∨ c = sk2 ∨ a = sk2 := resolve eq344 rule_def_6_0 -- resolution 344,175
  have eq580 : (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ a = sk1 ∨ c = sk2 ∨ a = sk2 := resolve eq577 rule_def_4_0 -- subsumption resolution 577,165
  have eq581 : (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ a = sk1 ∨ c = sk2 ∨ a = sk2 := resolve eq580 rule_def_0_0 -- subsumption resolution 580,147
  have eq608 : (old sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ a = sk0 ∨ b = sk0 := resolve eq393 rule_def_1_0 -- resolution 393,151
  have eq611 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ c = sk2 ∨ a = b ∨ c = sk1 := resolve eq289 rule_def_6_1 -- resolution 289,176
  have eq614 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ c = sk2 ∨ a = b ∨ c = sk1 := resolve eq611 rule_def_4_1 -- subsumption resolution 611,166
  have eq615 : (sP5 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ c = sk2 ∨ a = b ∨ c = sk1 := resolve eq614 rule_def_1_1 -- subsumption resolution 614,152
  have eq638 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk1 ∨ a = b ∨ c = sk1 := resolve eq299 rule_def_6_1 -- resolution 299,176
  have eq639 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk1 ∨ a = b ∨ a = sk0 := resolve eq299 rule_def_6_0 -- resolution 299,175
  have eq641 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ a = b ∨ c = sk1 := resolve eq638 rule_def_4_1 -- subsumption resolution 638,166
  have eq642 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ a = b ∨ c = sk1 := resolve eq641 rule_def_1_1 -- subsumption resolution 641,152
  have eq643 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ a = b ∨ a = sk0 := resolve eq639 rule_def_4_0 -- subsumption resolution 639,165
  have eq644 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ a = b ∨ a = sk0 := resolve eq643 rule_def_0_0 -- subsumption resolution 643,147
  have eq652 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ b = sk0 ∨ a = b ∨ a = sk0 := resolve eq310 rule_def_6_0 -- resolution 310,175
  have eq655 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ b = sk0 ∨ a = b ∨ a = sk0 := resolve eq652 rule_def_4_0 -- subsumption resolution 652,165
  have eq656 : (sP5 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ b = sk0 ∨ a = b ∨ a = sk0 := resolve eq655 rule_def_0_0 -- subsumption resolution 655,147
  have eq710 : (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ a = sk1 ∨ a = b ∨ a = sk2 := resolve eq341 rule_def_6_0 -- resolution 341,175
  have eq714 : (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ a = sk1 ∨ a = b ∨ a = sk2 := resolve eq710 rule_def_4_0 -- subsumption resolution 710,165
  have eq715 : (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ a = sk1 ∨ a = b ∨ a = sk2 := resolve eq714 rule_def_0_0 -- subsumption resolution 714,147
  have eq716 : (old sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 ∨ a = sk0 ∨ (old a a b) := resolve eq412 rule_def_5_3 -- resolution 412,173
  have eq717 : (old sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 ∨ a = sk0 ∨ a = sk2 := resolve eq412 rule_def_5_2 -- resolution 412,172
  have eq773 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ b = sk0 ∨ (old sk2 b b) ∨ a = sk0 := resolve eq307 rule_def_6_0 -- resolution 307,175
  have eq776 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ b = sk0 ∨ (old sk2 b b) ∨ a = sk0 := resolve eq773 rule_def_4_0 -- subsumption resolution 773,165
  have eq777 : (sP5 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ b = sk0 ∨ (old sk2 b b) ∨ a = sk0 := resolve eq776 rule_def_0_0 -- subsumption resolution 776,147
  have eq780 : (old sk2 sk1 sk3) ∨ a = sk1 ∨ b = sk1 ∨ a = sk2 ∨ b = sk2 := resolve eq461 rule_def_1_0 -- resolution 461,151
  have eq824 : (sP4 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP5 sk2 sk1 sk3) ∨ b = sk2 ∨ (old sk3 b b) ∨ a = sk2 := resolve eq347 rule_def_6_0 -- resolution 347,175
  have eq827 : (sP2 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP5 sk2 sk1 sk3) ∨ b = sk2 ∨ (old sk3 b b) ∨ a = sk2 := resolve eq824 rule_def_4_0 -- subsumption resolution 824,165
  have eq828 : (sP5 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ b = sk2 ∨ (old sk3 b b) ∨ a = sk2 := resolve eq827 rule_def_0_0 -- subsumption resolution 827,147
  have eq1029 : (old sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 ∨ c = sk1 ∨ (old b b a) := resolve eq504 rule_def_3_3 -- resolution 504,163
  have eq1033 : (old sk2 sk1 sk3) ∨ (old a a b) ∨ b = sk1 ∨ c = sk1 ∨ (old b b a) := resolve eq517 rule_def_3_3 -- resolution 517,163
  have eq1039 : (old sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 ∨ (old b b a) ∨ b = sk0 := resolve eq503 rule_def_1_0 -- resolution 503,151
  have eq1065 : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ a = b ∨ c = sk1 ∨ a = sk1 := resolve eq615 rule_def_5_1 -- resolution 615,171
  have eq1078 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ a = b ∨ c = sk1 ∨ b = sk2 := resolve eq642 rule_def_2_2 -- resolution 642,157
  have eq1082 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ a = b ∨ a = sk0 ∨ b = sk2 := resolve eq644 rule_def_2_2 -- resolution 644,157
  have eq1086 : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk0 ∨ a = b ∨ a = sk0 ∨ a = sk2 := resolve eq656 rule_def_5_2 -- resolution 656,172
  have eq1097 : (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ a = sk1 ∨ a = b ∨ a = sk2 ∨ (old b b a) := resolve eq715 rule_def_2_3 -- resolution 715,158
  have eq1098 : (sP1 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ a = sk1 ∨ a = b ∨ a = sk2 ∨ b = sk3 := resolve eq715 rule_def_2_2 -- resolution 715,157
  have eq1114 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ (old sk2 a b) ∨ a = sk2 := resolve eq387 rule_def_4_2 -- resolution 387,167
  have eq1121 : c = sk2 ∨ c = sk1 ∨ (old sk1 sk3 sk0) ∨ c = sk3 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq447 eq320 -- resolution 447,320
  have eq1137 : (old sk1 sk3 sk0) ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 ∨ c = sk0 := resolve eq1121 rfl -- duplicate literal removal 1121
  have eq1140 : (sP4 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 ∨ (old sk2 a b) ∨ a = sk1 := resolve eq407 rule_def_5_1 -- resolution 407,171
  have eq1152 : c = sk1 ∨ c = sk2 ∨ c = sk3 ∨ c = sk0 ∨ (new sk1 sk3 sk0) := resolve eq1137 imp_new_0 -- resolution 1137,145
  have eq1153 : c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq1152 preserve_2 -- subsumption resolution 1152,194
  have eq1159 : (new sk2 sk1 c) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := eq1153.imp_left (fun h : c = sk3 ↦ superpose h preserve_1) -- superposition 193,1153, 1153 into 193, unify on (0).2 in 1153 and (0).3 in 193
  have eq1160 : ¬(new sk1 c sk0) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := eq1153.imp_left (fun h : c = sk3 ↦ superpose h preserve_2) -- superposition 194,1153, 1153 into 194, unify on (0).2 in 1153 and (0).2 in 194
  have eq1167 : (sP6 sk2 sk1 c) ∨ (sP1 sk2 sk1 c) ∨ (old sk2 sk1 c) ∨ (sP4 sk2 sk1 c) ∨ a = sk1 ∨ b = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := Or.assoc6 (eq1153.imp_left (fun h : c = sk3 ↦ superpose h eq343)) -- superposition 343,1153, 1153 into 343, unify on (0).2 in 1153 and (0).3 in 343
  have eq1171 : (sP6 sk2 sk1 c) ∨ (sP4 sk2 sk1 c) ∨ (old sk2 sk1 c) ∨ (sP5 sk2 sk1 c) ∨ b = sk2 ∨ b = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := Or.assoc6 (eq1153.imp_left (fun h : c = sk3 ↦ superpose h eq352)) -- superposition 352,1153, 1153 into 352, unify on (0).2 in 1153 and (0).3 in 352
  have eq1183 : (old sk2 sk1 c) ∨ b = sk2 ∨ c = sk2 ∨ a = sk2 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := Or.assoc4 (eq1153.imp_left (fun h : c = sk3 ↦ superpose h eq489)) -- superposition 489,1153, 1153 into 489, unify on (0).2 in 1153 and (0).3 in 489
  have eq1188 : (sP1 sk2 sk1 c) ∨ (old sk2 sk1 c) ∨ a = sk1 ∨ c = sk2 ∨ a = sk2 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := Or.assoc5 (eq1153.imp_left (fun h : c = sk3 ↦ superpose h eq581)) -- superposition 581,1153, 1153 into 581, unify on (0).2 in 1153 and (0).3 in 581
  have eq1201 : (sP1 sk2 sk1 c) ∨ (old sk2 sk1 c) ∨ a = sk1 ∨ c = sk2 ∨ a = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq1188 rfl -- duplicate literal removal 1188
  have eq1205 : (old sk2 sk1 c) ∨ b = sk2 ∨ c = sk2 ∨ a = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq1183 rfl -- duplicate literal removal 1183
  have eq1237 : (sP6 sk2 sk1 c) ∨ (sP1 sk2 sk1 c) ∨ (sP4 sk2 sk1 c) ∨ a = sk1 ∨ b = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq1167 p4XY -- subsumption resolution 1167,131
  have eq1238 : (sP1 sk2 sk1 c) ∨ (sP4 sk2 sk1 c) ∨ a = sk1 ∨ b = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq1237 rule_def_6_1 -- subsumption resolution 1237,176
  have eq1239 : (sP1 sk2 sk1 c) ∨ a = sk1 ∨ b = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq1238 rule_def_4_1 -- subsumption resolution 1238,166
  have eq1240 : c = sk2 ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq1239 rule_def_1_1 -- subsumption resolution 1239,152
  have eq1241 : (sP6 sk2 sk1 c) ∨ (sP4 sk2 sk1 c) ∨ (sP5 sk2 sk1 c) ∨ b = sk2 ∨ b = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq1171 p4XY -- subsumption resolution 1171,131
  have eq1242 : (sP4 sk2 sk1 c) ∨ (sP5 sk2 sk1 c) ∨ b = sk2 ∨ b = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq1241 rule_def_6_1 -- subsumption resolution 1241,176
  have eq1243 : (sP4 sk2 sk1 c) ∨ b = sk2 ∨ b = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq1242 rule_def_5_0 -- subsumption resolution 1242,170
  have eq1244 : b = sk2 ∨ b = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq1243 rule_def_4_1 -- subsumption resolution 1243,166
  have eq1248 : b = sk2 ∨ c = sk2 ∨ a = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq1205 p4XY -- subsumption resolution 1205,131
  have eq1251 : (sP1 sk2 sk1 c) ∨ a = sk1 ∨ c = sk2 ∨ a = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq1201 p4XY -- subsumption resolution 1201,131
  have eq1252 : c = sk2 ∨ a = sk1 ∨ a = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq1251 rule_def_1_1 -- subsumption resolution 1251,152
  have eq1259 (X0 : G) : ¬(new sk2 sk1 X0) ∨ c = sk1 ∨ c = sk0 ∨ c = X0 ∨ c = sk2 := resolve eq1159 prev_0 -- resolution 1159,191
  have eq1271 : (sP8 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := Or.assoc10 (eq1240.imp_left (fun h : c = sk2 ↦ superpose h eq225)) -- superposition 225,1240, 1240 into 225, unify on (0).2 in 1240 and (0).3 in 225
  have eq1404 : (sP8 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq1271 p4XY -- subsumption resolution 1271,131
  have eq1405 : (sP8 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq1404 rule_def_7_1 -- subsumption resolution 1404,181
  have eq1406 : (sP8 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq1405 rule_def_6_1 -- subsumption resolution 1405,176
  have eq1407 : (sP8 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq1406 rule_def_5_0 -- subsumption resolution 1406,170
  have eq1408 : (sP8 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq1407 rule_def_4_1 -- subsumption resolution 1407,166
  have eq1409 : (sP8 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq1408 rule_def_2_0 -- subsumption resolution 1408,155
  have eq1410 : (sP8 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq1409 rule_def_1_1 -- subsumption resolution 1409,152
  have eq1411 : (sP3 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq1410 rule_def_8_1 -- subsumption resolution 1410,186
  have eq1412 : (sP0 sk0 sk1 c) ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq1411 rule_def_3_1 -- subsumption resolution 1411,161
  have eq1413 : b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq1412 rule_def_0_1 -- subsumption resolution 1412,148
  have eq1419 : (new sk2 b sk3) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := eq1413.imp_left (fun h : b = sk1 ↦ superpose h preserve_1) -- superposition 193,1413, 1413 into 193, unify on (0).2 in 1413 and (0).2 in 193
  have eq1420 : ¬(new b sk3 sk0) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := eq1413.imp_left (fun h : b = sk1 ↦ superpose h preserve_2) -- superposition 194,1413, 1413 into 194, unify on (0).2 in 1413 and (0).1 in 194
  have eq1444 : (old sk0 b sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = b ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := Or.assoc4 (eq1413.imp_left (fun h : b = sk1 ↦ superpose h eq320)) -- superposition 320,1413, 1413 into 320, unify on (0).2 in 1413 and (0).2 in 320
  have eq1542 : (old sk0 b sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = b ∨ a = sk1 ∨ c = sk1 := resolve eq1444 rfl -- duplicate literal removal 1444
  have eq1563 : (old sk0 b sk2) ∨ c = sk2 ∨ c = sk0 ∨ a = sk1 ∨ c = sk1 := resolve eq1542 bc -- subsumption resolution 1542,129
  have eq1604 : (old sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ b = sk2 ∨ b = sk1 ∨ (old sk3 a b) ∨ a = sk3 := resolve eq471 rule_def_5_2 -- resolution 471,172
  have eq1611 : (old sk3 a b) ∨ b = sk2 ∨ b = sk1 ∨ (old sk2 sk1 sk3) ∨ a = sk3 := resolve eq1604 rule_def_4_2 -- subsumption resolution 1604,167
  have eq1635 : (new sk0 sk1 b) ∨ b = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := eq1244.imp_left (fun h : b = sk2 ↦ superpose h preserve_0) -- superposition 192,1244, 1244 into 192, unify on (0).2 in 1244 and (0).3 in 192
  have eq1950 : a ≠ b ∨ c = sk2 ∨ a = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq1248 trans_resol -- equality factoring 1248
  have eq2105 : (sP1 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 ∨ a = sk1 ∨ a = sk2 ∨ c = sk1 ∨ c = sk0 := Or.assoc5 (eq1252.imp_left (fun h : c = sk2 ↦ superpose h eq556)) -- superposition 556,1252, 1252 into 556, unify on (0).2 in 1252 and (0).3 in 556
  have eq2142 : (sP1 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 ∨ a = sk2 ∨ c = sk1 := resolve eq2105 rfl -- duplicate literal removal 2105
  have eq2218 : (sP1 sk0 sk1 c) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 ∨ a = sk2 ∨ c = sk1 := resolve eq2142 p4XY -- subsumption resolution 2142,131
  have eq2219 : a = sk2 ∨ c = sk0 ∨ a = sk0 ∨ a = sk1 ∨ c = sk1 := resolve eq2218 rule_def_1_1 -- subsumption resolution 2218,152
  have eq2363 : (new a b sk3) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 ∨ c = sk0 ∨ a = sk0 ∨ a = sk1 ∨ c = sk1 := Or.assoc4 (eq2219.imp_left (fun h : a = sk2 ↦ superpose h eq1419)) -- superposition 1419,2219, 2219 into 1419, unify on (0).2 in 2219 and (0).1 in 1419
  have eq2364 : (new a b sk3) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq2363 rfl -- duplicate literal removal 2363
  have eq2552 (X0 : G) : ¬(new b sk1 X0) ∨ c = sk1 ∨ c = sk0 ∨ c = X0 ∨ c = b ∨ c = sk2 ∨ a = sk2 ∨ c = sk1 ∨ c = sk0 := Or.assoc5 (eq1248.imp_left (fun h : b = sk2 ↦ superpose h eq1259)) -- superposition 1259,1248, 1248 into 1259, unify on (0).2 in 1248 and (0).1 in 1259
  have eq2557 (X0 : G) : ¬(new b sk1 X0) ∨ c = sk1 ∨ c = sk0 ∨ c = X0 ∨ c = b ∨ c = sk2 ∨ a = sk2 := resolve eq2552 rfl -- duplicate literal removal 2552
  have eq2561 (X0 : G) : ¬(new b sk1 X0) ∨ c = sk1 ∨ c = sk0 ∨ c = X0 ∨ c = sk2 ∨ a = sk2 := resolve eq2557 bc -- subsumption resolution 2557,129
  have eq2614 : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk0 ∨ (old sk2 b b) ∨ a = sk0 ∨ a = sk2 := resolve eq777 rule_def_5_2 -- resolution 777,172
  have eq2702 : (sP2 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ b = sk2 ∨ (old sk3 b b) ∨ a = sk2 ∨ (old a a b) := resolve eq828 rule_def_5_3 -- resolution 828,173
  have eq3057 : (old sk0 b a) ∨ a = c ∨ c = sk0 ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 ∨ a = sk0 ∨ a = sk1 ∨ c = sk1 := Or.assoc5 (eq2219.imp_left (fun h : a = sk2 ↦ superpose h eq1563)) -- superposition 1563,2219, 2219 into 1563, unify on (0).2 in 2219 and (0).3 in 1563
  have eq3062 : (old sk0 b a) ∨ a = c ∨ c = sk0 ∨ a = sk1 ∨ c = sk1 ∨ a = sk0 := resolve eq3057 rfl -- duplicate literal removal 3057
  have eq3063 : (old sk0 b a) ∨ c = sk0 ∨ a = sk1 ∨ c = sk1 ∨ a = sk0 := resolve eq3062 ac -- subsumption resolution 3062,128
  have eq3338 : c = sk3 ∨ c = sk1 ∨ c = sk0 ∨ a = sk0 ∨ a = sk1 := resolve eq2364 eq221 -- resolution 2364,221
  have eq3425 : ¬(new b c sk0) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 ∨ c = sk1 ∨ c = sk0 ∨ a = sk0 ∨ a = sk1 := Or.assoc4 (eq3338.imp_left (fun h : c = sk3 ↦ superpose h eq1420)) -- superposition 1420,3338, 3338 into 1420, unify on (0).2 in 3338 and (0).2 in 1420
  have eq3444 : ¬(new b c sk0) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq3425 rfl -- duplicate literal removal 3425
  have eq3653 : c = sk0 ∨ a = sk1 ∨ c = sk1 ∨ a = sk0 ∨ (new b c sk0) := resolve eq3063 eq199 -- resolution 3063,199
  have eq3663 : c = sk1 ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq3653 eq3444 -- subsumption resolution 3653,3444
  have eq3683 : ¬(new c sk3 sk0) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := eq3663.imp_left (fun h : c = sk1 ↦ superpose h preserve_2) -- superposition 194,3663, 3663 into 194, unify on (0).2 in 3663 and (0).1 in 194
  have eq3690 : (sP7 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (old sk0 c sk2) ∨ (sP6 sk0 c sk2) ∨ a = c ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := Or.assoc8 (eq3663.imp_left (fun h : c = sk1 ↦ superpose h eq253)) -- superposition 253,3663, 3663 into 253, unify on (0).2 in 3663 and (0).2 in 253
  have eq3691 : (sP7 sk0 c sk2) ∨ (sP5 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (old sk0 c sk2) ∨ (sP6 sk0 c sk2) ∨ b = sk0 ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := Or.assoc8 (eq3663.imp_left (fun h : c = sk1 ↦ superpose h eq255)) -- superposition 255,3663, 3663 into 255, unify on (0).2 in 3663 and (0).2 in 255
  have eq3753 : (sP1 sk2 c sk3) ∨ (old sk2 c sk3) ∨ a = c ∨ c = b ∨ a = sk2 ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := Or.assoc5 (eq3663.imp_left (fun h : c = sk1 ↦ superpose h eq461)) -- superposition 461,3663, 3663 into 461, unify on (0).2 in 3663 and (0).2 in 461
  have eq3801 : (old sk2 c sk3) ∨ a = c ∨ c = b ∨ a = sk2 ∨ b = sk2 ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := Or.assoc5 (eq3663.imp_left (fun h : c = sk1 ↦ superpose h eq780)) -- superposition 780,3663, 3663 into 780, unify on (0).2 in 3663 and (0).2 in 780
  have eq3869 : (sP7 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (sP6 sk0 c sk2) ∨ a = c ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq3690 p4XZ -- subsumption resolution 3690,132
  have eq3870 : (sP7 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (sP6 sk0 c sk2) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq3869 ac -- subsumption resolution 3869,128
  have eq3871 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (sP6 sk0 c sk2) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq3870 rule_def_7_1 -- subsumption resolution 3870,181
  have eq3872 : (sP4 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (sP6 sk0 c sk2) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq3871 rule_def_2_0 -- subsumption resolution 3871,155
  have eq3873 : (sP4 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq3872 rule_def_6_0 -- subsumption resolution 3872,175
  have eq3874 : (sP1 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq3873 rule_def_4_0 -- subsumption resolution 3873,165
  have eq3875 : (sP1 sk0 c sk2) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq3874 rule_def_0_0 -- subsumption resolution 3874,147
  have eq3876 : (sP7 sk0 c sk2) ∨ (sP5 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (sP6 sk0 c sk2) ∨ b = sk0 ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq3691 p4XZ -- subsumption resolution 3691,132
  have eq3877 : (sP5 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (sP6 sk0 c sk2) ∨ b = sk0 ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq3876 rule_def_7_1 -- subsumption resolution 3876,181
  have eq3878 : (sP4 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (sP6 sk0 c sk2) ∨ b = sk0 ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq3877 rule_def_5_0 -- subsumption resolution 3877,170
  have eq3879 : (sP4 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (sP6 sk0 c sk2) ∨ b = sk0 ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq3878 rule_def_2_0 -- subsumption resolution 3878,155
  have eq3880 : (sP4 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ b = sk0 ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq3879 rule_def_6_0 -- subsumption resolution 3879,175
  have eq3881 : (sP0 sk0 c sk2) ∨ b = sk0 ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq3880 rule_def_4_0 -- subsumption resolution 3880,165
  have eq3882 : a = sk1 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq3881 rule_def_0_0 -- subsumption resolution 3881,147
  have eq3918 : (sP1 sk2 c sk3) ∨ a = c ∨ c = b ∨ a = sk2 ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq3753 p4XZ -- subsumption resolution 3753,132
  have eq3919 : (sP1 sk2 c sk3) ∨ c = b ∨ a = sk2 ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq3918 ac -- subsumption resolution 3918,128
  have eq3920 : (sP1 sk2 c sk3) ∨ a = sk2 ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq3919 bc -- subsumption resolution 3919,129
  have eq3934 : a = c ∨ c = b ∨ a = sk2 ∨ b = sk2 ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq3801 p4XZ -- subsumption resolution 3801,132
  have eq3935 : c = b ∨ a = sk2 ∨ b = sk2 ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq3934 ac -- subsumption resolution 3934,128
  have eq3936 : b = sk2 ∨ a = sk2 ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq3935 bc -- subsumption resolution 3935,129
  have eq3961 (X0 : G) : ¬(new sk2 a X0) ∨ sk3 = X0 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := Or.assoc2 (eq3882.imp_left (fun h : a = sk1 ↦ superpose h eq220)) -- superposition 220,3882, 3882 into 220, unify on (0).2 in 3882 and (0).2 in 220
  have eq3962 : (sP8 sk0 a sk2) ∨ (sP6 sk0 a sk2) ∨ (sP5 sk0 a sk2) ∨ (sP4 sk0 a sk2) ∨ (sP3 sk0 a sk2) ∨ (sP2 sk0 a sk2) ∨ (sP1 sk0 a sk2) ∨ (sP0 sk0 a sk2) ∨ (old sk0 a sk2) ∨ (sP7 sk0 a sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := Or.assoc10 (eq3882.imp_left (fun h : a = sk1 ↦ superpose h eq225)) -- superposition 225,3882, 3882 into 225, unify on (0).2 in 3882 and (0).2 in 225
  have eq4019 (X0 : G) : ¬(old X0 a sk2) ∨ c = sk0 ∨ a = sk0 ∨ sk0 = X0 ∨ b = sk0 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := Or.assoc5 (eq3882.imp_left (fun h : a = sk1 ↦ superpose h eq434)) -- superposition 434,3882, 3882 into 434, unify on (0).2 in 3882 and (0).2 in 434
  have eq4098 : (new sk2 a c) ∨ c = sk2 ∨ a = c ∨ c = sk0 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := Or.assoc4 (eq3882.imp_left (fun h : a = sk1 ↦ superpose h eq1159)) -- superposition 1159,3882, 3882 into 1159, unify on (0).2 in 3882 and (0).2 in 1159
  have eq4099 : ¬(new a c sk0) ∨ c = sk2 ∨ a = c ∨ c = sk0 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := Or.assoc4 (eq3882.imp_left (fun h : a = sk1 ↦ superpose h eq1160)) -- superposition 1160,3882, 3882 into 1160, unify on (0).2 in 3882 and (0).1 in 1160
  have eq4120 : ¬(new a c sk0) ∨ c = sk2 ∨ a = c ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := resolve eq4099 rfl -- duplicate literal removal 4099
  have eq4121 : (new sk2 a c) ∨ c = sk2 ∨ a = c ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := resolve eq4098 rfl -- duplicate literal removal 4098
  have eq4141 (X0 : G) : ¬(old X0 a sk2) ∨ c = sk0 ∨ a = sk0 ∨ sk0 = X0 ∨ b = sk0 := resolve eq4019 rfl -- duplicate literal removal 4019
  have eq4176 : (sP8 sk0 a sk2) ∨ (sP5 sk0 a sk2) ∨ (sP4 sk0 a sk2) ∨ (sP3 sk0 a sk2) ∨ (sP2 sk0 a sk2) ∨ (sP1 sk0 a sk2) ∨ (sP0 sk0 a sk2) ∨ (old sk0 a sk2) ∨ (sP7 sk0 a sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq3962 rule_def_6_0 -- subsumption resolution 3962,175
  have eq4177 : (sP8 sk0 a sk2) ∨ (sP5 sk0 a sk2) ∨ (sP3 sk0 a sk2) ∨ (sP2 sk0 a sk2) ∨ (sP1 sk0 a sk2) ∨ (sP0 sk0 a sk2) ∨ (old sk0 a sk2) ∨ (sP7 sk0 a sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq4176 rule_def_4_0 -- subsumption resolution 4176,165
  have eq4178 : (sP8 sk0 a sk2) ∨ (sP5 sk0 a sk2) ∨ (sP3 sk0 a sk2) ∨ (sP2 sk0 a sk2) ∨ (sP1 sk0 a sk2) ∨ (old sk0 a sk2) ∨ (sP7 sk0 a sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq4177 rule_def_0_0 -- subsumption resolution 4177,147
  have eq4179 : (sP8 sk0 a sk2) ∨ (sP5 sk0 a sk2) ∨ (sP3 sk0 a sk2) ∨ (sP2 sk0 a sk2) ∨ (sP1 sk0 a sk2) ∨ (old sk0 a sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq4178 rule_def_7_1 -- subsumption resolution 4178,181
  have eq4180 : (sP8 sk0 a sk2) ∨ (sP3 sk0 a sk2) ∨ (sP2 sk0 a sk2) ∨ (sP1 sk0 a sk2) ∨ (old sk0 a sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq4179 rule_def_5_0 -- subsumption resolution 4179,170
  have eq4181 : (sP8 sk0 a sk2) ∨ (sP3 sk0 a sk2) ∨ (sP1 sk0 a sk2) ∨ (old sk0 a sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq4180 rule_def_2_0 -- subsumption resolution 4180,155
  have eq4182 : (sP3 sk0 a sk2) ∨ (sP1 sk0 a sk2) ∨ (old sk0 a sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq4181 rule_def_8_0 -- subsumption resolution 4181,185
  have eq4183 : (sP1 sk0 a sk2) ∨ (old sk0 a sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq4182 rule_def_3_0 -- subsumption resolution 4182,160
  have eq4184 : (old sk0 a sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq4183 rule_def_1_0 -- subsumption resolution 4183,151
  have eq4212 : (new sk2 a c) ∨ c = sk2 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := resolve eq4121 ac -- subsumption resolution 4121,128
  have eq4213 : ¬(new a c sk0) ∨ c = sk2 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := resolve eq4120 ac -- subsumption resolution 4120,128
  have eq4314 : (old sk2 b a) ∨ c = sk0 ∨ a = sk0 ∨ a = sk1 := resolve eq3875 rule_def_1_2 -- resolution 3875,153
  have eq4469 (X0 : G) : ¬(old X0 b a) ∨ a = sk0 ∨ a = sk1 ∨ sk2 = X0 ∨ c = sk0 := resolve eq4314 old_8 -- resolution 4314,142
  have eq4738 : (old b b a) ∨ c = sk0 ∨ a = sk0 ∨ a = sk1 ∨ a = sk2 ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := Or.assoc4 (eq3936.imp_left (fun h : b = sk2 ↦ superpose h eq4314)) -- superposition 4314,3936, 3936 into 4314, unify on (0).2 in 3936 and (0).1 in 4314
  have eq4741 : a ≠ b ∨ a = sk2 ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq3936 trans_resol -- equality factoring 3936
  have eq4744 : (old b b a) ∨ c = sk0 ∨ a = sk0 ∨ a = sk1 ∨ a = sk2 := resolve eq4738 rfl -- duplicate literal removal 4738
  have eq5215 : (old sk3 b a) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 ∨ a = sk2 := resolve eq3920 rule_def_1_2 -- resolution 3920,153
  have eq5297 : b = sk1 ∨ c = sk1 ∨ (old sk1 sk3 sk0) ∨ a = sk1 ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 := resolve eq463 eq392 -- resolution 463,392
  have eq5323 : (old sk1 sk3 sk0) ∨ c = sk1 ∨ b = sk1 ∨ a = sk1 := resolve eq5297 rfl -- duplicate literal removal 5297
  have eq5333 : c = sk1 ∨ b = sk1 ∨ a = sk1 ∨ (new sk1 sk3 sk0) := resolve eq5323 imp_new_0 -- resolution 5323,145
  have eq5340 : b = sk1 ∨ c = sk1 ∨ a = sk1 := resolve eq5333 preserve_2 -- subsumption resolution 5333,194
  have eq5355 : ¬(new b sk3 sk0) ∨ c = sk1 ∨ a = sk1 := eq5340.imp_left (fun h : b = sk1 ↦ superpose h preserve_2) -- superposition 194,5340, 5340 into 194, unify on (0).2 in 5340 and (0).1 in 194
  have eq5542 : a ≠ b ∨ c = sk1 ∨ a = sk1 := resolve eq5340 trans_resol -- equality factoring 5340
  have eq5878 : c = sk2 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ c = sk3 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq4212 eq3961 -- resolution 4212,3961
  have eq5889 : c = sk3 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ c = sk2 := resolve eq5878 rfl -- duplicate literal removal 5878
  have eq6407 : (old c a b) ∨ b = sk2 ∨ b = sk1 ∨ (old sk2 sk1 c) ∨ a = c ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ c = sk2 := Or.assoc5 (eq5889.imp_left (fun h : c = sk3 ↦ superpose h eq1611)) -- superposition 1611,5889, 5889 into 1611, unify on (0).2 in 5889 and (0).1 in 1611
  have eq6412 : b = sk2 ∨ b = sk1 ∨ (old sk2 sk1 c) ∨ a = c ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ c = sk2 := resolve eq6407 p4YZ -- subsumption resolution 6407,133
  have eq6413 : b = sk2 ∨ b = sk1 ∨ a = c ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ c = sk2 := resolve eq6412 p4XY -- subsumption resolution 6412,131
  have eq6414 : b = sk2 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ c = sk2 := resolve eq6413 ac -- subsumption resolution 6413,128
  have eq6421 : a = sk0 ∨ a = sk1 ∨ sk2 = sk3 ∨ c = sk0 ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 ∨ a = sk2 := resolve eq4469 eq5215 -- resolution 4469,5215
  have eq6427 : sk2 = sk3 ∨ a = sk1 ∨ a = sk0 ∨ c = sk0 ∨ a = sk2 := resolve eq6421 rfl -- duplicate literal removal 6421
  have eq6910 : ¬(new c sk2 sk0) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 ∨ a = sk1 ∨ a = sk0 ∨ c = sk0 ∨ a = sk2 := Or.assoc4 (eq6427.imp_left (fun h : sk2 = sk3 ↦ superpose h eq3683)) -- superposition 3683,6427, 6427 into 3683, unify on (0).2 in 6427 and (0).2 in 3683
  have eq6941 : ¬(new c sk2 sk0) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 ∨ a = sk2 := resolve eq6910 rfl -- duplicate literal removal 6910
  have eq7045 (X0 : G) : ¬(old X0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ (old b b a) ∨ (old sk1 sk3 X0) ∨ (old a a b) := resolve eq1033 old_1 -- resolution 1033,135
  have eq7327 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ a = b ∨ c = sk1 ∨ a = sk1 ∨ (old b b a) := resolve eq1065 rule_def_2_3 -- resolution 1065,158
  have eq7328 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ a = b ∨ c = sk1 ∨ a = sk1 ∨ b = sk2 := resolve eq1065 rule_def_2_2 -- resolution 1065,157
  have eq7343 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ a = sk1 ∨ (old b b a) := resolve eq7327 eq5542 -- subsumption resolution 7327,5542
  have eq7344 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ a = sk1 ∨ b = sk2 := resolve eq7328 eq5542 -- subsumption resolution 7328,5542
  have eq7350 : c = sk2 ∨ c = sk1 ∨ a = sk1 ∨ b = sk2 ∨ c = sk2 ∨ c = sk1 ∨ (old sk1 sk3 sk0) ∨ c = sk3 := resolve eq7344 eq447 -- resolution 7344,447
  have eq7369 : (old sk1 sk3 sk0) ∨ c = sk1 ∨ a = sk1 ∨ b = sk2 ∨ c = sk2 ∨ c = sk3 := resolve eq7350 rfl -- duplicate literal removal 7350
  have eq7378 : (old sk0 sk1 sk2) ∨ a = sk1 ∨ a = b ∨ c = sk1 ∨ b = sk2 ∨ a = sk0 := resolve eq1078 rule_def_0_0 -- resolution 1078,147
  have eq7389 : (old sk0 sk1 sk2) ∨ a = sk1 ∨ c = sk1 ∨ b = sk2 ∨ a = sk0 := resolve eq7378 eq5542 -- subsumption resolution 7378,5542
  have eq7431 : (old sk0 sk1 sk2) ∨ a = sk1 ∨ a = b ∨ a = sk0 ∨ b = sk2 ∨ b = sk0 := resolve eq1082 rule_def_1_0 -- resolution 1082,151
  have eq7510 : (new c b b) ∨ a = sk0 ∨ a = sk1 ∨ a = sk2 ∨ c = sk0 := resolve eq4744 eq202 -- resolution 4744,202
  have eq8219 : ¬(new c b sk0) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 ∨ a = b ∨ a = sk2 ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := Or.assoc5 (eq3936.imp_left (fun h : b = sk2 ↦ superpose h eq6941)) -- superposition 6941,3936, 3936 into 6941, unify on (0).2 in 3936 and (0).2 in 6941
  have eq8228 : ¬(new c b sk0) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 ∨ a = b ∨ a = sk2 := resolve eq8219 rfl -- duplicate literal removal 8219
  have eq8229 : ¬(new c b sk0) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 ∨ a = sk2 := resolve eq8228 eq4741 -- subsumption resolution 8228,4741
  have eq8893 : c = sk2 ∨ c = sk1 ∨ a = sk1 ∨ (old b b a) ∨ c = sk2 ∨ c = sk1 ∨ (old sk1 sk3 sk0) ∨ c = sk3 := resolve eq7343 eq447 -- resolution 7343,447
  have eq8918 : (old sk1 sk3 sk0) ∨ c = sk1 ∨ a = sk1 ∨ (old b b a) ∨ c = sk2 ∨ c = sk3 := resolve eq8893 rfl -- duplicate literal removal 8893
  have eq11942 (X0 : G) : ¬(old X0 a b) ∨ c = sk0 ∨ a = sk0 ∨ sk0 = X0 ∨ b = sk0 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ c = sk2 := Or.assoc5 (eq6414.imp_left (fun h : b = sk2 ↦ superpose h eq4141)) -- superposition 4141,6414, 6414 into 4141, unify on (0).2 in 6414 and (0).3 in 4141
  have eq11943 : (old sk0 a b) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ b = sk1 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 ∨ c = sk2 := Or.assoc4 (eq6414.imp_left (fun h : b = sk2 ↦ superpose h eq4184)) -- superposition 4184,6414, 6414 into 4184, unify on (0).2 in 6414 and (0).3 in 4184
  have eq12017 : (old sk0 a b) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ b = sk1 ∨ c = sk2 := resolve eq11943 rfl -- duplicate literal removal 11943
  have eq12018 (X0 : G) : ¬(old X0 a b) ∨ c = sk0 ∨ a = sk0 ∨ sk0 = X0 ∨ b = sk0 ∨ b = sk1 ∨ c = sk2 := resolve eq11942 rfl -- duplicate literal removal 11942
  have eq12574 : (old sk3 b b) ∨ b = sk2 ∨ (old sk2 sk1 sk3) ∨ a = sk2 ∨ (old a a b) ∨ (old b b a) := resolve eq2702 rule_def_2_3 -- resolution 2702,158
  have eq16453 : c = sk1 ∨ a = sk1 ∨ b = sk2 ∨ c = sk2 ∨ c = sk3 ∨ (new sk1 sk3 sk0) := resolve eq7369 imp_new_0 -- resolution 7369,145
  have eq16466 : c = sk3 ∨ a = sk1 ∨ b = sk2 ∨ c = sk2 ∨ c = sk1 := resolve eq16453 preserve_2 -- subsumption resolution 16453,194
  have eq16526 : (old sk2 sk1 c) ∨ b = sk2 ∨ c = sk2 ∨ a = sk2 ∨ a = sk1 ∨ b = sk2 ∨ c = sk2 ∨ c = sk1 := Or.assoc4 (eq16466.imp_left (fun h : c = sk3 ↦ superpose h eq489)) -- superposition 489,16466, 16466 into 489, unify on (0).2 in 16466 and (0).3 in 489
  have eq16823 : (old sk2 sk1 c) ∨ b = sk2 ∨ c = sk2 ∨ a = sk2 ∨ a = sk1 ∨ c = sk1 := resolve eq16526 rfl -- duplicate literal removal 16526
  have eq16860 : b = sk2 ∨ c = sk2 ∨ a = sk2 ∨ a = sk1 ∨ c = sk1 := resolve eq16823 p4XY -- subsumption resolution 16823,131
  have eq16992 : (sP1 b sk1 sk3) ∨ (old b sk1 sk3) ∨ a = sk1 ∨ c = b ∨ a = b ∨ c = sk2 ∨ a = sk2 ∨ a = sk1 ∨ c = sk1 := Or.assoc5 (eq16860.imp_left (fun h : b = sk2 ↦ superpose h eq581)) -- superposition 581,16860, 16860 into 581, unify on (0).2 in 16860 and (0).1 in 581
  have eq17455 : (sP1 b sk1 sk3) ∨ (old b sk1 sk3) ∨ a = sk1 ∨ c = b ∨ a = b ∨ c = sk2 ∨ a = sk2 ∨ c = sk1 := resolve eq16992 rfl -- duplicate literal removal 16992
  have eq17567 : (sP1 b sk1 sk3) ∨ (old b sk1 sk3) ∨ a = sk1 ∨ a = b ∨ c = sk2 ∨ a = sk2 ∨ c = sk1 := resolve eq17455 bc -- subsumption resolution 17455,129
  have eq17568 : (sP1 b sk1 sk3) ∨ (old b sk1 sk3) ∨ a = sk1 ∨ c = sk2 ∨ a = sk2 ∨ c = sk1 := resolve eq17567 eq5542 -- subsumption resolution 17567,5542
  have eq17569 : (old b sk1 sk3) ∨ a = sk1 ∨ c = sk2 ∨ a = sk2 ∨ c = sk1 := resolve eq17568 rule_def_1_1 -- subsumption resolution 17568,152
  have eq17998 : (old b b sk3) ∨ a = b ∨ c = sk2 ∨ a = sk2 ∨ c = b ∨ c = sk1 ∨ a = sk1 := Or.assoc5 (eq5340.imp_left (fun h : b = sk1 ↦ superpose h eq17569)) -- superposition 17569,5340, 5340 into 17569, unify on (0).2 in 5340 and (0).2 in 17569
  have eq18025 : (old b b sk3) ∨ a = b ∨ c = sk2 ∨ a = sk2 ∨ c = sk1 ∨ a = sk1 := resolve eq17998 bc -- subsumption resolution 17998,129
  have eq18026 : (old b b sk3) ∨ c = sk2 ∨ a = sk2 ∨ c = sk1 ∨ a = sk1 := resolve eq18025 eq5542 -- subsumption resolution 18025,5542
  have eq18050 (X0 : G) : ¬(old b b X0) ∨ a = sk2 ∨ c = sk1 ∨ a = sk1 ∨ sk3 = X0 ∨ c = sk2 := resolve eq18026 old_0 -- resolution 18026,134
  have eq30423 : c = sk1 ∨ a = sk1 ∨ (old b b a) ∨ c = sk2 ∨ c = sk3 ∨ (new sk1 sk3 sk0) := resolve eq8918 imp_new_0 -- resolution 8918,145
  have eq30438 : (old b b a) ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 := resolve eq30423 preserve_2 -- subsumption resolution 30423,194
  have eq30481 : a = sk1 ∨ c = sk1 ∨ c = sk2 ∨ c = sk3 ∨ a = sk2 ∨ c = sk1 ∨ a = sk1 ∨ a = sk3 ∨ c = sk2 := resolve eq30438 eq18050 -- resolution 30438,18050
  have eq30513 : c = sk3 ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 ∨ a = sk2 ∨ a = sk3 := resolve eq30481 rfl -- duplicate literal removal 30481
  have eq30686 : (sP8 sk2 sk1 c) ∨ (sP6 sk2 sk1 c) ∨ (sP5 sk2 sk1 c) ∨ (sP4 sk2 sk1 c) ∨ (sP3 sk2 sk1 c) ∨ (sP2 sk2 sk1 c) ∨ (sP1 sk2 sk1 c) ∨ (sP0 sk2 sk1 c) ∨ (old sk2 sk1 c) ∨ (sP7 sk2 sk1 c) ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 ∨ a = sk2 ∨ a = sk3 := Or.assoc10 (eq30513.imp_left (fun h : c = sk3 ↦ superpose h eq226)) -- superposition 226,30513, 30513 into 226, unify on (0).2 in 30513 and (0).3 in 226
  have eq31147 : (sP8 sk2 sk1 c) ∨ (sP6 sk2 sk1 c) ∨ (sP5 sk2 sk1 c) ∨ (sP4 sk2 sk1 c) ∨ (sP3 sk2 sk1 c) ∨ (sP2 sk2 sk1 c) ∨ (sP1 sk2 sk1 c) ∨ (sP0 sk2 sk1 c) ∨ (sP7 sk2 sk1 c) ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 ∨ a = sk2 ∨ a = sk3 := resolve eq30686 p4XY -- subsumption resolution 30686,131
  have eq31148 : (sP6 sk2 sk1 c) ∨ (sP5 sk2 sk1 c) ∨ (sP4 sk2 sk1 c) ∨ (sP3 sk2 sk1 c) ∨ (sP2 sk2 sk1 c) ∨ (sP1 sk2 sk1 c) ∨ (sP0 sk2 sk1 c) ∨ (sP7 sk2 sk1 c) ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 ∨ a = sk2 ∨ a = sk3 := resolve eq31147 rule_def_8_1 -- subsumption resolution 31147,186
  have eq31149 : (sP5 sk2 sk1 c) ∨ (sP4 sk2 sk1 c) ∨ (sP3 sk2 sk1 c) ∨ (sP2 sk2 sk1 c) ∨ (sP1 sk2 sk1 c) ∨ (sP0 sk2 sk1 c) ∨ (sP7 sk2 sk1 c) ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 ∨ a = sk2 ∨ a = sk3 := resolve eq31148 rule_def_6_0 -- subsumption resolution 31148,175
  have eq31150 : (sP4 sk2 sk1 c) ∨ (sP3 sk2 sk1 c) ∨ (sP2 sk2 sk1 c) ∨ (sP1 sk2 sk1 c) ∨ (sP0 sk2 sk1 c) ∨ (sP7 sk2 sk1 c) ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 ∨ a = sk2 ∨ a = sk3 := resolve eq31149 rule_def_5_1 -- subsumption resolution 31149,171
  have eq31151 : (sP3 sk2 sk1 c) ∨ (sP2 sk2 sk1 c) ∨ (sP1 sk2 sk1 c) ∨ (sP0 sk2 sk1 c) ∨ (sP7 sk2 sk1 c) ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 ∨ a = sk2 ∨ a = sk3 := resolve eq31150 rule_def_4_0 -- subsumption resolution 31150,165
  have eq31152 : (sP2 sk2 sk1 c) ∨ (sP1 sk2 sk1 c) ∨ (sP0 sk2 sk1 c) ∨ (sP7 sk2 sk1 c) ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 ∨ a = sk2 ∨ a = sk3 := resolve eq31151 rule_def_3_1 -- subsumption resolution 31151,161
  have eq31153 : (sP2 sk2 sk1 c) ∨ (sP1 sk2 sk1 c) ∨ (sP7 sk2 sk1 c) ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 ∨ a = sk2 ∨ a = sk3 := resolve eq31152 rule_def_0_0 -- subsumption resolution 31152,147
  have eq31154 : (sP2 sk2 sk1 c) ∨ (sP1 sk2 sk1 c) ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 ∨ a = sk2 ∨ a = sk3 := resolve eq31153 rule_def_7_1 -- subsumption resolution 31153,181
  have eq31155 : (sP1 sk2 sk1 c) ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 ∨ a = sk2 ∨ a = sk3 := resolve eq31154 rule_def_2_0 -- subsumption resolution 31154,155
  have eq31156 : a = sk3 ∨ c = sk2 ∨ a = sk1 ∨ a = sk2 ∨ c = sk1 := resolve eq31155 rule_def_1_1 -- subsumption resolution 31155,152
  have eq31185 : (new sk2 sk1 a) ∨ c = sk2 ∨ a = sk1 ∨ a = sk2 ∨ c = sk1 := eq31156.imp_left (fun h : a = sk3 ↦ superpose h preserve_1) -- superposition 193,31156, 31156 into 193, unify on (0).2 in 31156 and (0).3 in 193
  have eq39266 : b = sk1 ∨ c = sk1 ∨ (old b b a) ∨ (old sk1 sk3 sk0) ∨ (old a a b) ∨ (old a a b) ∨ b = sk1 ∨ c = sk1 ∨ (old b b a) := resolve eq7045 eq1029 -- resolution 7045,1029
  have eq39339 : (old sk1 sk3 sk0) ∨ c = sk1 ∨ (old b b a) ∨ b = sk1 ∨ (old a a b) := resolve eq39266 rfl -- duplicate literal removal 39266
  have eq39364 : c = sk1 ∨ (old b b a) ∨ b = sk1 ∨ (old a a b) ∨ (new sk1 sk3 sk0) := resolve eq39339 imp_new_0 -- resolution 39339,145
  have eq39388 : (old b b a) ∨ c = sk1 ∨ b = sk1 ∨ (old a a b) := resolve eq39364 preserve_2 -- subsumption resolution 39364,194
  have eq39418 (X0 : G) : ¬(old X0 a b) ∨ b = sk1 ∨ (old a a b) ∨ c = sk1 ∨ (new a c X0) := resolve eq39388 eq213 -- resolution 39388,213
  have eq39882 : b = sk1 ∨ (old a a b) ∨ c = sk1 ∨ (new a c sk0) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ b = sk1 ∨ c = sk2 := resolve eq39418 eq12017 -- resolution 39418,12017
  have eq39899 : b = sk1 ∨ (old a a b) ∨ c = sk1 ∨ (new a c sk0) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk2 := resolve eq39882 rfl -- duplicate literal removal 39882
  have eq39902 : b = sk1 ∨ c = sk1 ∨ (new a c sk0) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk2 := resolve eq39899 eq12018 -- subsumption resolution 39899,12018
  have eq39903 : c = sk2 ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ b = sk1 := resolve eq39902 eq4213 -- subsumption resolution 39902,4213
  have eq39978 : (sP8 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ b = sk1 := Or.assoc10 (eq39903.imp_left (fun h : c = sk2 ↦ superpose h eq225)) -- superposition 225,39903, 39903 into 225, unify on (0).2 in 39903 and (0).3 in 225
  have eq40909 : (sP8 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ b = sk1 := resolve eq39978 p4XY -- subsumption resolution 39978,131
  have eq40910 : (sP8 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ b = sk1 := resolve eq40909 rule_def_6_0 -- subsumption resolution 40909,175
  have eq40911 : (sP8 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ b = sk1 := resolve eq40910 rule_def_4_0 -- subsumption resolution 40910,165
  have eq40912 : (sP8 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ b = sk1 := resolve eq40911 rule_def_0_0 -- subsumption resolution 40911,147
  have eq40913 : (sP5 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ b = sk1 := resolve eq40912 rule_def_8_0 -- subsumption resolution 40912,185
  have eq40914 : (sP5 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ b = sk1 := resolve eq40913 rule_def_7_2 -- subsumption resolution 40913,182
  have eq40915 : (sP5 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ b = sk1 := resolve eq40914 rule_def_3_0 -- subsumption resolution 40914,160
  have eq40916 : (sP5 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ b = sk1 := resolve eq40915 rule_def_2_1 -- subsumption resolution 40915,156
  have eq40917 : (sP5 sk0 sk1 c) ∨ c = sk1 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ b = sk1 := resolve eq40916 rule_def_1_0 -- subsumption resolution 40916,151
  have eq40918 : b = sk1 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 := resolve eq40917 rule_def_5_0 -- subsumption resolution 40917,170
  have eq40944 : a = b ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ a = c ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := Or.assoc5 (eq3882.imp_left (fun h : a = sk1 ↦ superpose h eq40918)) -- superposition 40918,3882, 3882 into 40918, unify on (0).2 in 3882 and (0).2 in 40918
  have eq40946 : (new sk2 b sk3) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 := eq40918.imp_left (fun h : b = sk1 ↦ superpose h preserve_1) -- superposition 193,40918, 40918 into 193, unify on (0).2 in 40918 and (0).2 in 193
  have eq40947 : ¬(new b sk3 sk0) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 := eq40918.imp_left (fun h : b = sk1 ↦ superpose h preserve_2) -- superposition 194,40918, 40918 into 194, unify on (0).2 in 40918 and (0).1 in 194
  have eq40950 : (sP8 sk0 b sk2) ∨ (sP6 sk0 b sk2) ∨ (sP5 sk0 b sk2) ∨ (sP4 sk0 b sk2) ∨ (sP3 sk0 b sk2) ∨ (sP2 sk0 b sk2) ∨ (sP1 sk0 b sk2) ∨ (sP0 sk0 b sk2) ∨ (old sk0 b sk2) ∨ (sP7 sk0 b sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 := Or.assoc10 (eq40918.imp_left (fun h : b = sk1 ↦ superpose h eq225)) -- superposition 225,40918, 40918 into 225, unify on (0).2 in 40918 and (0).2 in 225
  have eq41736 : a = b ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ a = c := resolve eq40944 rfl -- duplicate literal removal 40944
  have eq41737 : b = sk0 ∨ a = b ∨ c = sk0 ∨ a = sk0 := resolve eq41736 ac -- subsumption resolution 41736,128
  have eq41738 : (sP8 sk0 b sk2) ∨ (sP5 sk0 b sk2) ∨ (sP4 sk0 b sk2) ∨ (sP3 sk0 b sk2) ∨ (sP2 sk0 b sk2) ∨ (sP1 sk0 b sk2) ∨ (sP0 sk0 b sk2) ∨ (old sk0 b sk2) ∨ (sP7 sk0 b sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 := resolve eq40950 rule_def_6_0 -- subsumption resolution 40950,175
  have eq41739 : (sP8 sk0 b sk2) ∨ (sP5 sk0 b sk2) ∨ (sP3 sk0 b sk2) ∨ (sP2 sk0 b sk2) ∨ (sP1 sk0 b sk2) ∨ (sP0 sk0 b sk2) ∨ (old sk0 b sk2) ∨ (sP7 sk0 b sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 := resolve eq41738 rule_def_4_0 -- subsumption resolution 41738,165
  have eq41740 : (sP8 sk0 b sk2) ∨ (sP5 sk0 b sk2) ∨ (sP3 sk0 b sk2) ∨ (sP2 sk0 b sk2) ∨ (sP1 sk0 b sk2) ∨ (old sk0 b sk2) ∨ (sP7 sk0 b sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 := resolve eq41739 rule_def_0_0 -- subsumption resolution 41739,147
  have eq41741 : (sP8 sk0 b sk2) ∨ (sP5 sk0 b sk2) ∨ (sP3 sk0 b sk2) ∨ (sP2 sk0 b sk2) ∨ (sP1 sk0 b sk2) ∨ (old sk0 b sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 := resolve eq41740 rule_def_7_1 -- subsumption resolution 41740,181
  have eq41742 : (sP8 sk0 b sk2) ∨ (sP3 sk0 b sk2) ∨ (sP2 sk0 b sk2) ∨ (sP1 sk0 b sk2) ∨ (old sk0 b sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 := resolve eq41741 rule_def_5_0 -- subsumption resolution 41741,170
  have eq41743 : (sP8 sk0 b sk2) ∨ (sP3 sk0 b sk2) ∨ (sP1 sk0 b sk2) ∨ (old sk0 b sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 := resolve eq41742 rule_def_2_0 -- subsumption resolution 41742,155
  have eq41744 : (sP3 sk0 b sk2) ∨ (sP1 sk0 b sk2) ∨ (old sk0 b sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 := resolve eq41743 rule_def_8_0 -- subsumption resolution 41743,185
  have eq41745 : (sP1 sk0 b sk2) ∨ (old sk0 b sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 := resolve eq41744 rule_def_3_0 -- subsumption resolution 41744,160
  have eq41746 : (old sk0 b sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 := resolve eq41745 rule_def_1_0 -- subsumption resolution 41745,151
  have eq41806 : (new b sk1 sk2) ∨ a = b ∨ c = sk0 ∨ a = sk0 := eq41737.imp_left (fun h : b = sk0 ↦ superpose h preserve_0) -- superposition 192,41737, 41737 into 192, unify on (0).2 in 41737 and (0).1 in 192
  have eq42061 : ¬(new c b b) ∨ a = sk1 ∨ c = b ∨ a = b ∨ a = sk2 ∨ a = b ∨ c = sk0 ∨ a = sk0 := Or.assoc5 (eq41737.imp_left (fun h : b = sk0 ↦ superpose h eq8229)) -- superposition 8229,41737, 41737 into 8229, unify on (0).2 in 41737 and (0).3 in 8229
  have eq42102 : ¬(new c b b) ∨ a = sk1 ∨ c = b ∨ a = b ∨ a = sk2 ∨ c = sk0 ∨ a = sk0 := resolve eq42061 rfl -- duplicate literal removal 42061
  have eq42269 : ¬(new c b b) ∨ a = sk1 ∨ a = b ∨ a = sk2 ∨ c = sk0 ∨ a = sk0 := resolve eq42102 bc -- subsumption resolution 42102,129
  have eq42270 : ¬(new c b b) ∨ a = sk1 ∨ a = sk2 ∨ c = sk0 ∨ a = sk0 := resolve eq42269 eq4741 -- subsumption resolution 42269,4741
  have eq42271 : a = sk2 ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq42270 eq7510 -- subsumption resolution 42270,7510
  have eq42657 : (old a b a) ∨ c = sk0 ∨ a = sk0 ∨ a = sk1 ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := Or.assoc4 (eq42271.imp_left (fun h : a = sk2 ↦ superpose h eq4314)) -- superposition 4314,42271, 42271 into 4314, unify on (0).2 in 42271 and (0).1 in 4314
  have eq42955 : (old a b a) ∨ c = sk0 ∨ a = sk0 ∨ a = sk1 := resolve eq42657 rfl -- duplicate literal removal 42657
  have eq43216 : a = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq42955 p3 -- subsumption resolution 42955,130
  have eq43237 : ¬(new a sk3 sk0) ∨ a = sk0 ∨ c = sk0 := eq43216.imp_left (fun h : a = sk1 ↦ superpose h preserve_2) -- superposition 194,43216, 43216 into 194, unify on (0).2 in 43216 and (0).1 in 194
  have eq43239 (X0 : G) : ¬(new sk2 a X0) ∨ sk3 = X0 ∨ a = sk0 ∨ c = sk0 := Or.assoc2 (eq43216.imp_left (fun h : a = sk1 ↦ superpose h eq220)) -- superposition 220,43216, 43216 into 220, unify on (0).2 in 43216 and (0).2 in 220
  have eq43510 : (new sk2 a c) ∨ c = sk2 ∨ a = c ∨ c = sk0 ∨ a = sk0 ∨ c = sk0 := Or.assoc4 (eq43216.imp_left (fun h : a = sk1 ↦ superpose h eq1159)) -- superposition 1159,43216, 43216 into 1159, unify on (0).2 in 43216 and (0).2 in 1159
  have eq43856 : (new sk2 a c) ∨ c = sk2 ∨ a = c ∨ c = sk0 ∨ a = sk0 := resolve eq43510 rfl -- duplicate literal removal 43510
  have eq44028 : (new sk2 a c) ∨ c = sk2 ∨ c = sk0 ∨ a = sk0 := resolve eq43856 ac -- subsumption resolution 43856,128
  have eq44365 : ¬(new a sk3 b) ∨ a = b ∨ c = b ∨ a = b ∨ c = sk0 ∨ a = sk0 := Or.assoc3 (eq41737.imp_left (fun h : b = sk0 ↦ superpose h eq43237)) -- superposition 43237,41737, 41737 into 43237, unify on (0).2 in 41737 and (0).3 in 43237
  have eq44366 : ¬(new a sk3 b) ∨ a = b ∨ c = b ∨ c = sk0 ∨ a = sk0 := resolve eq44365 rfl -- duplicate literal removal 44365
  have eq44374 : ¬(new a sk3 b) ∨ a = b ∨ c = sk0 ∨ a = sk0 := resolve eq44366 bc -- subsumption resolution 44366,129
  have eq44440 : a = b ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 ∨ c = sk2 ∨ c = sk2 ∨ a = sk2 := resolve eq41806 eq2561 -- resolution 41806,2561
  have eq44502 : a = b ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ c = sk2 ∨ a = sk2 := resolve eq44440 rfl -- duplicate literal removal 44440
  have eq44506 : c = sk2 ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 ∨ a = sk2 := resolve eq44502 eq1950 -- subsumption resolution 44502,1950
  have eq45565 : c = sk2 ∨ c = sk0 ∨ a = sk0 ∨ c = sk3 ∨ a = sk0 ∨ c = sk0 := resolve eq44028 eq43239 -- resolution 44028,43239
  have eq45598 : c = sk3 ∨ c = sk0 ∨ a = sk0 ∨ c = sk2 := resolve eq45565 rfl -- duplicate literal removal 45565
  have eq45766 : (old c a b) ∨ b = sk2 ∨ b = sk1 ∨ (old sk2 sk1 c) ∨ a = c ∨ c = sk0 ∨ a = sk0 ∨ c = sk2 := Or.assoc5 (eq45598.imp_left (fun h : c = sk3 ↦ superpose h eq1611)) -- superposition 1611,45598, 45598 into 1611, unify on (0).2 in 45598 and (0).1 in 1611
  have eq46101 : b = sk2 ∨ b = sk1 ∨ (old sk2 sk1 c) ∨ a = c ∨ c = sk0 ∨ a = sk0 ∨ c = sk2 := resolve eq45766 p4YZ -- subsumption resolution 45766,133
  have eq46102 : b = sk2 ∨ b = sk1 ∨ a = c ∨ c = sk0 ∨ a = sk0 ∨ c = sk2 := resolve eq46101 p4XY -- subsumption resolution 46101,131
  have eq46103 : b = sk2 ∨ b = sk1 ∨ c = sk0 ∨ a = sk0 ∨ c = sk2 := resolve eq46102 ac -- subsumption resolution 46102,128
  have eq46252 : (old sk2 sk1 sk3) ∨ b = sk2 ∨ a = sk2 ∨ (old a a b) ∨ (old b b a) ∨ (old b sk3 b) := resolve eq12574 old_3 -- resolution 12574,137
  have eq46592 : (sP7 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ b = sk0 ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 ∨ a = sk2 := Or.assoc8 (eq44506.imp_left (fun h : c = sk2 ↦ superpose h eq255)) -- superposition 255,44506, 44506 into 255, unify on (0).2 in 44506 and (0).3 in 255
  have eq47442 : (sP7 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ b = sk0 ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 ∨ a = sk2 := resolve eq46592 p4XY -- subsumption resolution 46592,131
  have eq47443 : (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ b = sk0 ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 ∨ a = sk2 := resolve eq47442 rule_def_7_1 -- subsumption resolution 47442,181
  have eq47444 : (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk0 ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 ∨ a = sk2 := resolve eq47443 rule_def_6_1 -- subsumption resolution 47443,176
  have eq47445 : (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk0 ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 ∨ a = sk2 := resolve eq47444 rule_def_5_0 -- subsumption resolution 47444,170
  have eq47446 : (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk0 ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 ∨ a = sk2 := resolve eq47445 rule_def_4_1 -- subsumption resolution 47445,166
  have eq47447 : (sP0 sk0 sk1 c) ∨ b = sk0 ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 ∨ a = sk2 := resolve eq47446 rule_def_2_0 -- subsumption resolution 47446,155
  have eq47448 : a = sk2 ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 ∨ b = sk0 := resolve eq47447 rule_def_0_0 -- subsumption resolution 47447,147
  have eq49642 : (new b sk1 sk3) ∨ b = sk1 ∨ c = sk0 ∨ a = sk0 ∨ c = sk2 := eq46103.imp_left (fun h : b = sk2 ↦ superpose h preserve_1) -- superposition 193,46103, 46103 into 193, unify on (0).2 in 46103 and (0).1 in 193
  have eq50853 : (new a b sk3) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 ∨ b = sk0 := Or.assoc5 (eq47448.imp_left (fun h : a = sk2 ↦ superpose h eq40946)) -- superposition 40946,47448, 47448 into 40946, unify on (0).2 in 47448 and (0).1 in 40946
  have eq50878 : (new a b sk3) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 := resolve eq50853 rfl -- duplicate literal removal 50853
  have eq51067 : (old sk0 b a) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 ∨ b = sk0 := Or.assoc5 (eq47448.imp_left (fun h : a = sk2 ↦ superpose h eq41746)) -- superposition 41746,47448, 47448 into 41746, unify on (0).2 in 47448 and (0).3 in 41746
  have eq51068 : (old sk0 b a) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 := resolve eq51067 rfl -- duplicate literal removal 51067
  have eq61700 : c = sk3 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq50878 eq221 -- resolution 50878,221
  have eq62112 : ¬(new b c sk0) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ b = sk0 := Or.assoc5 (eq61700.imp_left (fun h : c = sk3 ↦ superpose h eq40947)) -- superposition 40947,61700, 61700 into 40947, unify on (0).2 in 61700 and (0).2 in 40947
  have eq62159 : ¬(new b c sk0) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 := resolve eq62112 rfl -- duplicate literal removal 62112
  have eq62354 : b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ (new b c sk0) := resolve eq51068 eq199 -- resolution 51068,199
  have eq62392 : c = sk1 ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq62354 eq62159 -- subsumption resolution 62354,62159
  have eq62425 : a = c ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := Or.assoc4 (eq3882.imp_left (fun h : a = sk1 ↦ superpose h eq62392)) -- superposition 62392,3882, 3882 into 62392, unify on (0).2 in 3882 and (0).2 in 62392
  have eq63163 : a = c ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq62425 rfl -- duplicate literal removal 62425
  have eq63165 : b = sk0 ∨ a = sk0 ∨ c = sk0 := resolve eq63163 ac -- subsumption resolution 63163,128
  have eq63218 (X0 : G) : ¬(new b sk1 X0) ∨ sk2 = X0 ∨ a = sk0 ∨ c = sk0 := Or.assoc2 (eq63165.imp_left (fun h : b = sk0 ↦ superpose h eq219)) -- superposition 219,63165, 63165 into 219, unify on (0).2 in 63165 and (0).1 in 219
  have eq63532 : a ≠ b ∨ a = sk0 ∨ c = sk0 := resolve eq63165 trans_resol -- equality factoring 63165
  have eq67547 : b = sk1 ∨ c = sk0 ∨ a = sk0 ∨ c = sk2 ∨ sk2 = sk3 ∨ a = sk0 ∨ c = sk0 := resolve eq49642 eq63218 -- resolution 49642,63218
  have eq67592 : sk2 = sk3 ∨ c = sk0 ∨ a = sk0 ∨ c = sk2 ∨ b = sk1 := resolve eq67547 rfl -- duplicate literal removal 67547
  have eq67757 : c = sk2 ∨ c = sk0 ∨ a = sk0 ∨ c = sk2 ∨ b = sk1 ∨ c = sk0 ∨ a = sk0 ∨ c = sk2 := Or.assoc5 (eq45598.imp_left (fun h : c = sk3 ↦ superpose h eq67592)) -- superposition 67592,45598, 45598 into 67592, unify on (0).2 in 45598 and (0).2 in 67592
  have eq68677 : c = sk2 ∨ c = sk0 ∨ a = sk0 ∨ b = sk1 := resolve eq67757 rfl -- duplicate literal removal 67757
  have eq68803 : (sP5 c sk1 sk3) ∨ (old c sk1 sk3) ∨ c = b ∨ b = sk1 ∨ a = c ∨ c = sk0 ∨ a = sk0 ∨ b = sk1 := Or.assoc5 (eq68677.imp_left (fun h : c = sk2 ↦ superpose h eq476)) -- superposition 476,68677, 68677 into 476, unify on (0).2 in 68677 and (0).1 in 476
  have eq69655 : (sP5 c sk1 sk3) ∨ (old c sk1 sk3) ∨ c = b ∨ b = sk1 ∨ a = c ∨ c = sk0 ∨ a = sk0 := resolve eq68803 rfl -- duplicate literal removal 68803
  have eq69744 : (sP5 c sk1 sk3) ∨ c = b ∨ b = sk1 ∨ a = c ∨ c = sk0 ∨ a = sk0 := resolve eq69655 p4YZ -- subsumption resolution 69655,133
  have eq69745 : (sP5 c sk1 sk3) ∨ b = sk1 ∨ a = c ∨ c = sk0 ∨ a = sk0 := resolve eq69744 bc -- subsumption resolution 69744,129
  have eq69746 : (sP5 c sk1 sk3) ∨ b = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq69745 ac -- subsumption resolution 69745,128
  have eq71095 : (sP5 c a sk3) ∨ a = b ∨ c = sk0 ∨ a = sk0 ∨ a = sk0 ∨ c = sk0 := Or.assoc4 (eq43216.imp_left (fun h : a = sk1 ↦ superpose h eq69746)) -- superposition 69746,43216, 43216 into 69746, unify on (0).2 in 43216 and (0).2 in 69746
  have eq71133 : (sP5 c a sk3) ∨ a = b ∨ c = sk0 ∨ a = sk0 := resolve eq71095 rfl -- duplicate literal removal 71095
  have eq71136 : (sP5 c a sk3) ∨ c = sk0 ∨ a = sk0 := resolve eq71133 eq63532 -- subsumption resolution 71133,63532
  have eq71163 : (old a a b) ∨ a = sk0 ∨ c = sk0 := resolve eq71136 rule_def_5_3 -- resolution 71136,173
  have eq71164 : a = sk3 ∨ a = sk0 ∨ c = sk0 := resolve eq71136 rule_def_5_2 -- resolution 71136,172
  have eq71626 : ¬(new a a b) ∨ a = b ∨ c = sk0 ∨ a = sk0 ∨ a = sk0 ∨ c = sk0 := Or.assoc4 (eq71164.imp_left (fun h : a = sk3 ↦ superpose h eq44374)) -- superposition 44374,71164, 71164 into 44374, unify on (0).2 in 71164 and (0).2 in 44374
  have eq71673 : ¬(new a a b) ∨ a = b ∨ c = sk0 ∨ a = sk0 := resolve eq71626 rfl -- duplicate literal removal 71626
  have eq71802 : ¬(new a a b) ∨ c = sk0 ∨ a = sk0 := resolve eq71673 eq63532 -- subsumption resolution 71673,63532
  have eq72782 : a = sk0 ∨ c = sk0 ∨ (new a a b) := resolve eq71163 imp_new_0 -- resolution 71163,145
  have eq72788 : c = sk0 ∨ a = sk0 := resolve eq72782 eq71802 -- subsumption resolution 72782,71802
  have eq72830 : ¬(new sk1 sk3 c) ∨ a = sk0 := eq72788.imp_left (fun h : c = sk0 ↦ superpose h preserve_2) -- superposition 194,72788, 72788 into 194, unify on (0).2 in 72788 and (0).3 in 194
  have eq72871 : (old c sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ a = c ∨ c = b ∨ a = sk0 := Or.assoc5 (eq72788.imp_left (fun h : c = sk0 ↦ superpose h eq608)) -- superposition 608,72788, 72788 into 608, unify on (0).2 in 72788 and (0).1 in 608
  have eq72898 : (old c sk1 sk2) ∨ c = b ∨ b = sk1 ∨ a = c ∨ (old a a b) ∨ a = sk0 := Or.assoc5 (eq72788.imp_left (fun h : c = sk0 ↦ superpose h eq716)) -- superposition 716,72788, 72788 into 716, unify on (0).2 in 72788 and (0).1 in 716
  have eq72899 : (old c sk1 sk2) ∨ c = b ∨ b = sk1 ∨ a = c ∨ a = sk2 ∨ a = sk0 := Or.assoc5 (eq72788.imp_left (fun h : c = sk0 ↦ superpose h eq717)) -- superposition 717,72788, 72788 into 717, unify on (0).2 in 72788 and (0).1 in 717
  have eq72917 : (sP5 c sk1 sk2) ∨ (old c sk1 sk2) ∨ (sP2 c sk1 sk2) ∨ c = b ∨ (old sk2 b b) ∨ a = c ∨ a = sk0 := Or.assoc6 (eq72788.imp_left (fun h : c = sk0 ↦ superpose h eq777)) -- superposition 777,72788, 72788 into 777, unify on (0).2 in 72788 and (0).1 in 777
  have eq72946 : (sP2 c sk1 sk2) ∨ (old c sk1 sk2) ∨ c = b ∨ a = b ∨ a = c ∨ a = sk2 ∨ a = sk0 := Or.assoc6 (eq72788.imp_left (fun h : c = sk0 ↦ superpose h eq1086)) -- superposition 1086,72788, 72788 into 1086, unify on (0).2 in 72788 and (0).1 in 1086
  have eq72965 : (sP2 c sk1 sk2) ∨ (old c sk1 sk2) ∨ c = b ∨ (old sk2 b b) ∨ a = c ∨ a = sk2 ∨ a = sk0 := Or.assoc6 (eq72788.imp_left (fun h : c = sk0 ↦ superpose h eq2614)) -- superposition 2614,72788, 72788 into 2614, unify on (0).2 in 72788 and (0).1 in 2614
  have eq73018 : ¬(new b sk3 c) ∨ c = sk1 ∨ a = sk1 ∨ a = sk0 := Or.assoc3 (eq72788.imp_left (fun h : c = sk0 ↦ superpose h eq5355)) -- superposition 5355,72788, 72788 into 5355, unify on (0).2 in 72788 and (0).3 in 5355
  have eq73076 : (old c sk1 sk2) ∨ a = sk1 ∨ c = sk1 ∨ b = sk2 ∨ a = c ∨ a = sk0 := Or.assoc5 (eq72788.imp_left (fun h : c = sk0 ↦ superpose h eq7389)) -- superposition 7389,72788, 72788 into 7389, unify on (0).2 in 72788 and (0).1 in 7389
  have eq73085 : (old c sk1 sk2) ∨ a = sk1 ∨ a = b ∨ a = c ∨ b = sk2 ∨ c = b ∨ a = sk0 := Or.assoc6 (eq72788.imp_left (fun h : c = sk0 ↦ superpose h eq7431)) -- superposition 7431,72788, 72788 into 7431, unify on (0).2 in 72788 and (0).1 in 7431
  have eq73195 : a = sk1 ∨ b = sk1 ∨ a = c ∨ c = b ∨ a = sk0 := resolve eq72871 p4YZ -- subsumption resolution 72871,133
  have eq73196 : a = sk1 ∨ b = sk1 ∨ c = b ∨ a = sk0 := resolve eq73195 ac -- subsumption resolution 73195,128
  have eq73197 : b = sk1 ∨ a = sk1 ∨ a = sk0 := resolve eq73196 bc -- subsumption resolution 73196,129
  have eq73222 : c = b ∨ b = sk1 ∨ a = c ∨ (old a a b) ∨ a = sk0 := resolve eq72898 p4YZ -- subsumption resolution 72898,133
  have eq73223 : b = sk1 ∨ a = c ∨ (old a a b) ∨ a = sk0 := resolve eq73222 bc -- subsumption resolution 73222,129
  have eq73224 : (old a a b) ∨ b = sk1 ∨ a = sk0 := resolve eq73223 ac -- subsumption resolution 73223,128
  have eq73225 : c = b ∨ b = sk1 ∨ a = c ∨ a = sk2 ∨ a = sk0 := resolve eq72899 p4YZ -- subsumption resolution 72899,133
  have eq73226 : b = sk1 ∨ a = c ∨ a = sk2 ∨ a = sk0 := resolve eq73225 bc -- subsumption resolution 73225,129
  have eq73227 : a = sk2 ∨ b = sk1 ∨ a = sk0 := resolve eq73226 ac -- subsumption resolution 73226,128
  have eq73243 : (sP5 c sk1 sk2) ∨ (sP2 c sk1 sk2) ∨ c = b ∨ (old sk2 b b) ∨ a = c ∨ a = sk0 := resolve eq72917 p4YZ -- subsumption resolution 72917,133
  have eq73244 : (sP5 c sk1 sk2) ∨ (sP2 c sk1 sk2) ∨ (old sk2 b b) ∨ a = c ∨ a = sk0 := resolve eq73243 bc -- subsumption resolution 73243,129
  have eq73245 : (sP5 c sk1 sk2) ∨ (sP2 c sk1 sk2) ∨ (old sk2 b b) ∨ a = sk0 := resolve eq73244 ac -- subsumption resolution 73244,128
  have eq73271 : (sP2 c sk1 sk2) ∨ c = b ∨ a = b ∨ a = c ∨ a = sk2 ∨ a = sk0 := resolve eq72946 p4YZ -- subsumption resolution 72946,133
  have eq73272 : (sP2 c sk1 sk2) ∨ a = b ∨ a = c ∨ a = sk2 ∨ a = sk0 := resolve eq73271 bc -- subsumption resolution 73271,129
  have eq73273 : (sP2 c sk1 sk2) ∨ a = b ∨ a = sk2 ∨ a = sk0 := resolve eq73272 ac -- subsumption resolution 73272,128
  have eq73286 : (sP2 c sk1 sk2) ∨ c = b ∨ (old sk2 b b) ∨ a = c ∨ a = sk2 ∨ a = sk0 := resolve eq72965 p4YZ -- subsumption resolution 72965,133
  have eq73287 : (sP2 c sk1 sk2) ∨ (old sk2 b b) ∨ a = c ∨ a = sk2 ∨ a = sk0 := resolve eq73286 bc -- subsumption resolution 73286,129
  have eq73288 : (sP2 c sk1 sk2) ∨ (old sk2 b b) ∨ a = sk2 ∨ a = sk0 := resolve eq73287 ac -- subsumption resolution 73287,128
  have eq73319 : a = sk1 ∨ c = sk1 ∨ b = sk2 ∨ a = c ∨ a = sk0 := resolve eq73076 p4YZ -- subsumption resolution 73076,133
  have eq73320 : b = sk2 ∨ c = sk1 ∨ a = sk1 ∨ a = sk0 := resolve eq73319 ac -- subsumption resolution 73319,128
  have eq73321 : a = sk1 ∨ a = b ∨ a = c ∨ b = sk2 ∨ c = b ∨ a = sk0 := resolve eq73085 p4YZ -- subsumption resolution 73085,133
  have eq73322 : a = sk1 ∨ a = b ∨ b = sk2 ∨ c = b ∨ a = sk0 := resolve eq73321 ac -- subsumption resolution 73321,128
  have eq73323 : b = sk2 ∨ a = b ∨ a = sk1 ∨ a = sk0 := resolve eq73322 bc -- subsumption resolution 73322,129
  have eq74142 : a ≠ b ∨ a = sk1 ∨ a = sk0 := resolve eq73197 trans_resol -- equality factoring 73197
  have eq77066 : (new a a b) ∨ a = sk0 ∨ b = sk1 := resolve eq73224 imp_new_0 -- resolution 73224,145
  have eq78276 (X0 : G) : ¬(new a a X0) ∨ b = sk1 ∨ b = X0 ∨ a = sk0 := resolve eq77066 prev_0 -- resolution 77066,191
  have eq81370 : (new b sk1 a) ∨ c = b ∨ a = sk1 ∨ a = b ∨ c = sk1 ∨ c = sk1 ∨ a = sk1 ∨ a = sk0 := Or.assoc5 (eq73320.imp_left (fun h : b = sk2 ↦ superpose h eq31185)) -- superposition 31185,73320, 73320 into 31185, unify on (0).2 in 73320 and (0).1 in 31185
  have eq81494 : (new b sk1 a) ∨ c = b ∨ a = sk1 ∨ a = b ∨ c = sk1 ∨ a = sk0 := resolve eq81370 rfl -- duplicate literal removal 81370
  have eq82045 : (new b sk1 a) ∨ a = sk1 ∨ a = b ∨ c = sk1 ∨ a = sk0 := resolve eq81494 bc -- subsumption resolution 81494,129
  have eq82046 : (new b sk1 a) ∨ a = sk1 ∨ c = sk1 ∨ a = sk0 := resolve eq82045 eq74142 -- subsumption resolution 82045,74142
  have eq82118 (X0 : G) : ¬(new b sk1 X0) ∨ sk3 = X0 ∨ a = b ∨ a = sk1 ∨ a = sk0 := Or.assoc2 (eq73323.imp_left (fun h : b = sk2 ↦ superpose h eq220)) -- superposition 220,73323, 73323 into 220, unify on (0).2 in 73323 and (0).1 in 220
  have eq83339 (X0 : G) : ¬(new b sk1 X0) ∨ sk3 = X0 ∨ a = sk1 ∨ a = sk0 := resolve eq82118 eq74142 -- subsumption resolution 82118,74142
  have eq88717 : (sP2 c sk1 b) ∨ a = b ∨ a = b ∨ a = sk0 ∨ a = b ∨ a = sk1 ∨ a = sk0 := Or.assoc4 (eq73323.imp_left (fun h : b = sk2 ↦ superpose h eq73273)) -- superposition 73273,73323, 73323 into 73273, unify on (0).2 in 73323 and (0).3 in 73273
  have eq88722 : (sP2 c sk1 b) ∨ a = b ∨ a = sk0 ∨ a = sk1 := resolve eq88717 rfl -- duplicate literal removal 88717
  have eq88756 : (sP2 c sk1 b) ∨ a = sk0 ∨ a = sk1 := resolve eq88722 eq74142 -- subsumption resolution 88722,74142
  have eq88802 : (old b b a) ∨ a = sk1 ∨ a = sk0 := resolve eq88756 rule_def_2_3 -- resolution 88756,158
  have eq88847 : (new b a c) ∨ a = sk0 ∨ a = sk1 := resolve eq88802 eq205 -- resolution 88802,205
  have eq91916 : a = sk3 ∨ a = sk1 ∨ a = sk0 ∨ a = sk1 ∨ c = sk1 ∨ a = sk0 := resolve eq83339 eq82046 -- resolution 83339,82046
  have eq91984 : a = sk3 ∨ a = sk1 ∨ a = sk0 ∨ c = sk1 := resolve eq91916 rfl -- duplicate literal removal 91916
  have eq92501 : ¬(new b a c) ∨ c = sk1 ∨ a = sk1 ∨ a = sk0 ∨ a = sk1 ∨ a = sk0 ∨ c = sk1 := Or.assoc4 (eq91984.imp_left (fun h : a = sk3 ↦ superpose h eq73018)) -- superposition 73018,91984, 91984 into 73018, unify on (0).2 in 91984 and (0).2 in 73018
  have eq92524 : ¬(new b a c) ∨ c = sk1 ∨ a = sk1 ∨ a = sk0 := resolve eq92501 rfl -- duplicate literal removal 92501
  have eq92898 : c = sk1 ∨ a = sk1 ∨ a = sk0 := resolve eq92524 eq88847 -- subsumption resolution 92524,88847
  have eq92956 : c = b ∨ a = b ∨ a = sk0 ∨ a = sk1 ∨ a = sk0 := Or.assoc3 (eq73197.imp_left (fun h : b = sk1 ↦ superpose h eq92898)) -- superposition 92898,73197, 73197 into 92898, unify on (0).2 in 73197 and (0).2 in 92898
  have eq93756 : c = b ∨ a = b ∨ a = sk0 ∨ a = sk1 := resolve eq92956 rfl -- duplicate literal removal 92956
  have eq93758 : a = b ∨ a = sk0 ∨ a = sk1 := resolve eq93756 bc -- subsumption resolution 93756,129
  have eq93759 : a = sk1 ∨ a = sk0 := resolve eq93758 eq74142 -- subsumption resolution 93758,74142
  have eq93847 : (new sk2 a sk3) ∨ a = sk0 := eq93759.imp_left (fun h : a = sk1 ↦ superpose h preserve_1) -- superposition 193,93759, 93759 into 193, unify on (0).2 in 93759 and (0).2 in 193
  have eq94526 : ¬(new a sk3 c) ∨ a = sk0 ∨ a = sk0 := Or.assoc2 (eq93759.imp_left (fun h : a = sk1 ↦ superpose h eq72830)) -- superposition 72830,93759, 93759 into 72830, unify on (0).2 in 93759 and (0).1 in 72830
  have eq94530 : (sP2 c a sk2) ∨ a = b ∨ a = sk2 ∨ a = sk0 ∨ a = sk0 := Or.assoc4 (eq93759.imp_left (fun h : a = sk1 ↦ superpose h eq73273)) -- superposition 73273,93759, 93759 into 73273, unify on (0).2 in 93759 and (0).2 in 73273
  have eq94541 : (sP2 c a sk2) ∨ a = b ∨ a = sk2 ∨ a = sk0 := resolve eq94530 rfl -- duplicate literal removal 94530
  have eq94545 : ¬(new a sk3 c) ∨ a = sk0 := resolve eq94526 rfl -- duplicate literal removal 94526
  have eq94872 : a = sk2 ∨ a = b ∨ a = sk0 := resolve eq94541 rule_def_2_1 -- subsumption resolution 94541,156
  have eq95138 : (new a a sk3) ∨ a = sk0 ∨ b = sk1 ∨ a = sk0 := Or.assoc2 (eq73227.imp_left (fun h : a = sk2 ↦ superpose h eq93847)) -- superposition 93847,73227, 73227 into 93847, unify on (0).2 in 73227 and (0).1 in 93847
  have eq95183 : (new a a sk3) ∨ a = sk0 ∨ b = sk1 := resolve eq95138 rfl -- duplicate literal removal 95138
  have eq102168 : b = sk1 ∨ b = sk3 ∨ a = sk0 ∨ a = sk0 ∨ b = sk1 := resolve eq78276 eq95183 -- resolution 78276,95183
  have eq102179 : b = sk3 ∨ b = sk1 ∨ a = sk0 := resolve eq102168 rfl -- duplicate literal removal 102168
  have eq102781 : ¬(new a b c) ∨ a = sk0 ∨ b = sk1 ∨ a = sk0 := Or.assoc2 (eq102179.imp_left (fun h : b = sk3 ↦ superpose h eq94545)) -- superposition 94545,102179, 102179 into 94545, unify on (0).2 in 102179 and (0).2 in 94545
  have eq102786 : ¬(new a b c) ∨ a = sk0 ∨ b = sk1 := resolve eq102781 rfl -- duplicate literal removal 102781
  have eq103137 : b = sk1 ∨ a = sk0 := resolve eq102786 eq197 -- subsumption resolution 102786,197
  have eq103226 : a = b ∨ a = sk0 ∨ a = sk0 := Or.assoc2 (eq93759.imp_left (fun h : a = sk1 ↦ superpose h eq103137)) -- superposition 103137,93759, 93759 into 103137, unify on (0).2 in 93759 and (0).2 in 103137
  have eq103231 (X0 : G) : ¬(new sk2 b X0) ∨ sk3 = X0 ∨ a = sk0 := Or.assoc2 (eq103137.imp_left (fun h : b = sk1 ↦ superpose h eq220)) -- superposition 220,103137, 103137 into 220, unify on (0).2 in 103137 and (0).2 in 220
  have eq104208 : a = sk0 ∨ a = b := resolve eq103226 rfl -- duplicate literal removal 103226
  have eq104325 : (new a sk1 sk2) ∨ a = b := eq104208.imp_left (fun h : a = sk0 ↦ superpose h preserve_0) -- superposition 192,104208, 104208 into 192, unify on (0).2 in 104208 and (0).1 in 192
  have eq104326 : ¬(new sk1 sk3 a) ∨ a = b := eq104208.imp_left (fun h : a = sk0 ↦ superpose h preserve_2) -- superposition 194,104208, 104208 into 194, unify on (0).2 in 104208 and (0).3 in 194
  have eq104347 : (old a sk1 sk2) ∨ c = sk2 ∨ a = c ∨ c = sk1 ∨ a = b := Or.assoc4 (eq104208.imp_left (fun h : a = sk0 ↦ superpose h eq320)) -- superposition 320,104208, 104208 into 320, unify on (0).2 in 104208 and (0).1 in 320
  have eq104372 : (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ a = b ∨ a = c ∨ c = sk1 ∨ a = b := Or.assoc5 (eq104208.imp_left (fun h : a = sk0 ↦ superpose h eq422)) -- superposition 422,104208, 104208 into 422, unify on (0).2 in 104208 and (0).1 in 422
  have eq104456 : ¬(new sk1 c a) ∨ c = sk2 ∨ c = sk1 ∨ a = c ∨ a = b := Or.assoc4 (eq104208.imp_left (fun h : a = sk0 ↦ superpose h eq1160)) -- superposition 1160,104208, 104208 into 1160, unify on (0).2 in 104208 and (0).3 in 1160
  have eq104463 : ¬(new b sk3 a) ∨ a = sk1 ∨ c = sk1 ∨ a = c ∨ a = b := Or.assoc4 (eq104208.imp_left (fun h : a = sk0 ↦ superpose h eq1420)) -- superposition 1420,104208, 104208 into 1420, unify on (0).2 in 104208 and (0).3 in 1420
  have eq104465 : (old a b sk2) ∨ c = sk2 ∨ a = c ∨ a = sk1 ∨ c = sk1 ∨ a = b := Or.assoc5 (eq104208.imp_left (fun h : a = sk0 ↦ superpose h eq1563)) -- superposition 1563,104208, 104208 into 1563, unify on (0).2 in 104208 and (0).1 in 1563
  have eq104796 : (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ a = b ∨ a = c ∨ c = sk1 := resolve eq104372 rfl -- duplicate literal removal 104372
  have eq104834 : (old a sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ a = b := resolve eq104347 ac -- subsumption resolution 104347,128
  have eq104850 : (sP0 a sk1 sk2) ∨ (old a sk1 sk2) ∨ a = b ∨ c = sk1 := resolve eq104796 ac -- subsumption resolution 104796,128
  have eq104881 : ¬(new sk1 c a) ∨ c = sk2 ∨ c = sk1 ∨ a = b := resolve eq104456 ac -- subsumption resolution 104456,128
  have eq104886 : ¬(new b sk3 a) ∨ a = sk1 ∨ c = sk1 ∨ a = b := resolve eq104463 ac -- subsumption resolution 104463,128
  have eq104887 : ¬(new b sk3 a) ∨ a = sk1 ∨ c = sk1 := resolve eq104886 eq5542 -- subsumption resolution 104886,5542
  have eq104890 : c = sk2 ∨ a = c ∨ a = sk1 ∨ c = sk1 ∨ a = b := resolve eq104465 p3 -- subsumption resolution 104465,130
  have eq104891 : c = sk2 ∨ a = sk1 ∨ c = sk1 ∨ a = b := resolve eq104890 ac -- subsumption resolution 104890,128
  have eq104892 : c = sk2 ∨ a = sk1 ∨ c = sk1 := resolve eq104891 eq5542 -- subsumption resolution 104891,5542
  have eq106146 : (sP1 c sk1 sk3) ∨ (old c sk1 sk3) ∨ a = sk1 ∨ a = b ∨ a = c ∨ (old b b a) ∨ a = sk1 ∨ c = sk1 := Or.assoc6 (eq104892.imp_left (fun h : c = sk2 ↦ superpose h eq1097)) -- superposition 1097,104892, 104892 into 1097, unify on (0).2 in 104892 and (0).1 in 1097
  have eq106147 : (sP1 c sk1 sk3) ∨ (old c sk1 sk3) ∨ a = sk1 ∨ a = b ∨ a = c ∨ b = sk3 ∨ a = sk1 ∨ c = sk1 := Or.assoc6 (eq104892.imp_left (fun h : c = sk2 ↦ superpose h eq1098)) -- superposition 1098,104892, 104892 into 1098, unify on (0).2 in 104892 and (0).1 in 1098
  have eq106924 : (sP1 c sk1 sk3) ∨ (old c sk1 sk3) ∨ a = sk1 ∨ a = b ∨ a = c ∨ b = sk3 ∨ c = sk1 := resolve eq106147 rfl -- duplicate literal removal 106147
  have eq106925 : (sP1 c sk1 sk3) ∨ (old c sk1 sk3) ∨ a = sk1 ∨ a = b ∨ a = c ∨ (old b b a) ∨ c = sk1 := resolve eq106146 rfl -- duplicate literal removal 106146
  have eq107123 : (sP1 c sk1 sk3) ∨ a = sk1 ∨ a = b ∨ a = c ∨ (old b b a) ∨ c = sk1 := resolve eq106925 p4YZ -- subsumption resolution 106925,133
  have eq107124 : (sP1 c sk1 sk3) ∨ a = sk1 ∨ a = b ∨ (old b b a) ∨ c = sk1 := resolve eq107123 ac -- subsumption resolution 107123,128
  have eq107125 : a = sk1 ∨ a = b ∨ (old b b a) ∨ c = sk1 := resolve eq107124 rule_def_1_1 -- subsumption resolution 107124,152
  have eq107126 : (old b b a) ∨ a = sk1 ∨ c = sk1 := resolve eq107125 eq5542 -- subsumption resolution 107125,5542
  have eq107127 : (sP1 c sk1 sk3) ∨ a = sk1 ∨ a = b ∨ a = c ∨ b = sk3 ∨ c = sk1 := resolve eq106924 p4YZ -- subsumption resolution 106924,133
  have eq107128 : (sP1 c sk1 sk3) ∨ a = sk1 ∨ a = b ∨ b = sk3 ∨ c = sk1 := resolve eq107127 ac -- subsumption resolution 107127,128
  have eq107129 : a = sk1 ∨ a = b ∨ b = sk3 ∨ c = sk1 := resolve eq107128 rule_def_1_1 -- subsumption resolution 107128,152
  have eq107130 : b = sk3 ∨ a = sk1 ∨ c = sk1 := resolve eq107129 eq5542 -- subsumption resolution 107129,5542
  have eq109721 : ¬(new b b a) ∨ a = sk1 ∨ c = sk1 ∨ a = sk1 ∨ c = sk1 := Or.assoc3 (eq107130.imp_left (fun h : b = sk3 ↦ superpose h eq104887)) -- superposition 104887,107130, 107130 into 104887, unify on (0).2 in 107130 and (0).2 in 104887
  have eq109722 : ¬(new b b a) ∨ a = sk1 ∨ c = sk1 := resolve eq109721 rfl -- duplicate literal removal 109721
  have eq110518 : a = sk1 ∨ c = sk1 ∨ (new b b a) := resolve eq107126 imp_new_0 -- resolution 107126,145
  have eq110537 : c = sk1 ∨ a = sk1 := resolve eq110518 eq109722 -- subsumption resolution 110518,109722
  have eq110594 : (sP6 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (old sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ a = c ∨ c = b ∨ a = sk1 := Or.assoc6 (eq110537.imp_left (fun h : c = sk1 ↦ superpose h eq301)) -- superposition 301,110537, 110537 into 301, unify on (0).2 in 110537 and (0).2 in 301
  have eq110739 : (old sk2 c sk3) ∨ a = c ∨ c = b ∨ a = sk2 ∨ b = sk2 ∨ a = sk1 := Or.assoc5 (eq110537.imp_left (fun h : c = sk1 ↦ superpose h eq780)) -- superposition 780,110537, 110537 into 780, unify on (0).2 in 110537 and (0).2 in 780
  have eq110779 : (old sk0 c sk2) ∨ (old a a b) ∨ c = b ∨ (old b b a) ∨ b = sk0 ∨ a = sk1 := Or.assoc5 (eq110537.imp_left (fun h : c = sk1 ↦ superpose h eq1039)) -- superposition 1039,110537, 110537 into 1039, unify on (0).2 in 110537 and (0).2 in 1039
  have eq110800 : (sP1 sk0 c sk2) ∨ (old sk0 c sk2) ∨ a = c ∨ c = b ∨ (old sk2 a b) ∨ a = sk2 ∨ a = sk1 := Or.assoc6 (eq110537.imp_left (fun h : c = sk1 ↦ superpose h eq1114)) -- superposition 1114,110537, 110537 into 1114, unify on (0).2 in 110537 and (0).2 in 1114
  have eq110802 : (sP4 sk0 c sk2) ∨ (old sk0 c sk2) ∨ b = sk0 ∨ c = b ∨ (old sk2 a b) ∨ a = c ∨ a = sk1 := Or.assoc6 (eq110537.imp_left (fun h : c = sk1 ↦ superpose h eq1140)) -- superposition 1140,110537, 110537 into 1140, unify on (0).2 in 110537 and (0).2 in 1140
  have eq111197 : ¬(new c sk3 a) ∨ a = b ∨ a = sk1 := Or.assoc2 (eq110537.imp_left (fun h : c = sk1 ↦ superpose h eq104326)) -- superposition 104326,110537, 110537 into 104326, unify on (0).2 in 110537 and (0).1 in 104326
  have eq111221 : (sP6 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ a = c ∨ c = b ∨ a = sk1 := resolve eq110594 p4XZ -- subsumption resolution 110594,132
  have eq111222 : (sP6 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ c = b ∨ a = sk1 := resolve eq111221 ac -- subsumption resolution 111221,128
  have eq111223 : (sP6 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ a = sk1 := resolve eq111222 bc -- subsumption resolution 111222,129
  have eq111297 : a = c ∨ c = b ∨ a = sk2 ∨ b = sk2 ∨ a = sk1 := resolve eq110739 p4XZ -- subsumption resolution 110739,132
  have eq111298 : c = b ∨ a = sk2 ∨ b = sk2 ∨ a = sk1 := resolve eq111297 ac -- subsumption resolution 111297,128
  have eq111299 : b = sk2 ∨ a = sk2 ∨ a = sk1 := resolve eq111298 bc -- subsumption resolution 111298,129
  have eq111300 : (old a a b) ∨ c = b ∨ (old b b a) ∨ b = sk0 ∨ a = sk1 := resolve eq110779 p4XZ -- subsumption resolution 110779,132
  have eq111301 : (old b b a) ∨ (old a a b) ∨ b = sk0 ∨ a = sk1 := resolve eq111300 bc -- subsumption resolution 111300,129
  have eq111310 : (sP1 sk0 c sk2) ∨ a = c ∨ c = b ∨ (old sk2 a b) ∨ a = sk2 ∨ a = sk1 := resolve eq110800 p4XZ -- subsumption resolution 110800,132
  have eq111311 : (sP1 sk0 c sk2) ∨ c = b ∨ (old sk2 a b) ∨ a = sk2 ∨ a = sk1 := resolve eq111310 ac -- subsumption resolution 111310,128
  have eq111312 : (sP1 sk0 c sk2) ∨ (old sk2 a b) ∨ a = sk2 ∨ a = sk1 := resolve eq111311 bc -- subsumption resolution 111311,129
  have eq111316 : (sP4 sk0 c sk2) ∨ b = sk0 ∨ c = b ∨ (old sk2 a b) ∨ a = c ∨ a = sk1 := resolve eq110802 p4XZ -- subsumption resolution 110802,132
  have eq111317 : (sP4 sk0 c sk2) ∨ b = sk0 ∨ (old sk2 a b) ∨ a = c ∨ a = sk1 := resolve eq111316 bc -- subsumption resolution 111316,129
  have eq111318 : (sP4 sk0 c sk2) ∨ b = sk0 ∨ (old sk2 a b) ∨ a = sk1 := resolve eq111317 ac -- subsumption resolution 111317,128
  have eq112447 : a ≠ b ∨ a = sk2 ∨ a = sk1 := resolve eq111299 trans_resol -- equality factoring 111299
  have eq131136 : (old sk2 b b) ∨ a = sk2 ∨ a = sk0 ∨ b = sk2 := resolve eq73288 rule_def_2_2 -- resolution 73288,157
  have eq131286 : (new sk2 b b) ∨ a = sk0 ∨ b = sk2 ∨ a = sk2 := resolve eq131136 imp_new_0 -- resolution 131136,145
  have eq131377 : a = sk0 ∨ b = sk2 ∨ a = sk2 ∨ b = sk3 ∨ a = sk0 := resolve eq131286 eq103231 -- resolution 131286,103231
  have eq131401 : b = sk3 ∨ b = sk2 ∨ a = sk2 ∨ a = sk0 := resolve eq131377 rfl -- duplicate literal removal 131377
  have eq132076 : ¬(new a b c) ∨ a = sk0 ∨ b = sk2 ∨ a = sk2 ∨ a = sk0 := Or.assoc2 (eq131401.imp_left (fun h : b = sk3 ↦ superpose h eq94545)) -- superposition 94545,131401, 131401 into 94545, unify on (0).2 in 131401 and (0).2 in 94545
  have eq132123 : ¬(new a b c) ∨ a = sk0 ∨ b = sk2 ∨ a = sk2 := resolve eq132076 rfl -- duplicate literal removal 132076
  have eq132582 : b = sk2 ∨ a = sk0 ∨ a = sk2 := resolve eq132123 eq197 -- subsumption resolution 132123,197
  have eq133445 : a ≠ b ∨ a = sk0 ∨ a = sk2 := resolve eq132582 trans_resol -- equality factoring 132582
  have eq133797 : a = sk2 ∨ a = sk0 := resolve eq133445 eq94872 -- subsumption resolution 133445,94872
  have eq143680 : (old a a b) ∨ b = sk0 ∨ a = sk1 ∨ (new b a c) := resolve eq111301 eq205 -- resolution 111301,205
  have eq143760 : (new b a c) ∨ a = sk1 ∨ b = sk0 := resolve eq143680 eq218 -- subsumption resolution 143680,218
  have eq143976 (X0 : G) : ¬(new b a X0) ∨ b = sk0 ∨ c = X0 ∨ a = sk1 := resolve eq143760 prev_0 -- resolution 143760,191
  have eq144916 : (sP1 a c sk2) ∨ (old sk2 a b) ∨ a = sk2 ∨ a = sk1 ∨ a = b := Or.assoc4 (eq104208.imp_left (fun h : a = sk0 ↦ superpose h eq111312)) -- superposition 111312,104208, 104208 into 111312, unify on (0).2 in 104208 and (0).1 in 111312
  have eq144968 : (old sk2 a b) ∨ a = sk2 ∨ a = sk1 ∨ a = b := resolve eq144916 rule_def_1_0 -- subsumption resolution 144916,151
  have eq144969 : (old sk2 a b) ∨ a = sk2 ∨ a = sk1 := resolve eq144968 eq112447 -- subsumption resolution 144968,112447
  have eq145141 (X0 : G) : a = sk2 ∨ a = sk1 ∨ (old a b X0) ∨ ¬(old X0 a sk2) := resolve eq144969 old_1 -- resolution 144969,135
  have eq145148 : (new sk2 a b) ∨ a = sk1 ∨ a = sk2 := resolve eq144969 imp_new_0 -- resolution 144969,145
  have eq145180 : (old b a b) ∨ a = b ∨ a = sk1 ∨ a = sk2 ∨ a = sk1 := Or.assoc3 (eq111299.imp_left (fun h : b = sk2 ↦ superpose h eq144969)) -- superposition 144969,111299, 111299 into 144969, unify on (0).2 in 111299 and (0).1 in 144969
  have eq145182 : (old b a b) ∨ a = b ∨ a = sk1 ∨ a = sk2 := resolve eq145180 rfl -- duplicate literal removal 145180
  have eq145209 (X0 : G) : ¬(old X0 a sk2) ∨ a = sk1 ∨ a = sk2 := resolve eq145141 p3 -- subsumption resolution 145141,130
  have eq145211 : (old b a b) ∨ a = sk1 ∨ a = sk2 := resolve eq145182 eq112447 -- subsumption resolution 145182,112447
  have eq145319 : (new b a b) ∨ a = sk1 ∨ a = b ∨ a = sk2 ∨ a = sk1 := Or.assoc3 (eq111299.imp_left (fun h : b = sk2 ↦ superpose h eq145148)) -- superposition 145148,111299, 111299 into 145148, unify on (0).2 in 111299 and (0).1 in 145148
  have eq145321 : (new b a b) ∨ a = sk1 ∨ a = b ∨ a = sk2 := resolve eq145319 rfl -- duplicate literal removal 145319
  have eq145338 : (new b a b) ∨ a = sk1 ∨ a = sk2 := resolve eq145321 eq112447 -- subsumption resolution 145321,112447
  have eq145572 (X0 : G) : ¬(old X0 a b) ∨ a = sk1 ∨ a = b ∨ a = sk2 ∨ a = sk1 := Or.assoc3 (eq111299.imp_left (fun h : b = sk2 ↦ superpose h eq145209)) -- superposition 145209,111299, 111299 into 145209, unify on (0).2 in 111299 and (0).3 in 145209
  have eq145574 (X0 : G) : ¬(old X0 a b) ∨ a = sk1 ∨ a = b ∨ a = sk2 := resolve eq145572 rfl -- duplicate literal removal 145572
  have eq145590 (X0 : G) : ¬(old X0 a b) ∨ a = sk1 ∨ a = sk2 := resolve eq145574 eq112447 -- subsumption resolution 145574,112447
  have eq145935 : a = sk1 ∨ a = sk2 ∨ b = sk0 ∨ c = b ∨ a = sk1 := resolve eq145338 eq143976 -- resolution 145338,143976
  have eq145940 : a = sk1 ∨ a = sk2 ∨ b = sk0 ∨ c = b := resolve eq145935 rfl -- duplicate literal removal 145935
  have eq145948 : a = sk2 ∨ a = sk1 ∨ b = sk0 := resolve eq145940 bc -- subsumption resolution 145940,129
  have eq147710 : a = sk1 ∨ a = sk2 ∨ a = sk1 ∨ a = sk2 := resolve eq145590 eq145211 -- resolution 145590,145211
  have eq147733 : a = sk2 ∨ a = sk1 := resolve eq147710 rfl -- duplicate literal removal 147710
  have eq147912 (X0 : G) : ¬(new a sk1 X0) ∨ sk3 = X0 ∨ a = sk1 := Or.assoc2 (eq147733.imp_left (fun h : a = sk2 ↦ superpose h eq220)) -- superposition 220,147733, 147733 into 220, unify on (0).2 in 147733 and (0).1 in 220
  have eq148690 : (new a sk1 a) ∨ a = b ∨ a = sk1 := Or.assoc2 (eq147733.imp_left (fun h : a = sk2 ↦ superpose h eq104325)) -- superposition 104325,147733, 147733 into 104325, unify on (0).2 in 147733 and (0).3 in 104325
  have eq152805 : a = b ∨ a = sk1 ∨ a = sk3 ∨ a = sk1 := resolve eq148690 eq147912 -- resolution 148690,147912
  have eq152822 : a = sk3 ∨ a = sk1 ∨ a = b := resolve eq152805 rfl -- duplicate literal removal 152805
  have eq153583 : ¬(new c a a) ∨ a = b ∨ a = sk1 ∨ a = sk1 ∨ a = b := Or.assoc3 (eq152822.imp_left (fun h : a = sk3 ↦ superpose h eq111197)) -- superposition 111197,152822, 152822 into 111197, unify on (0).2 in 152822 and (0).2 in 111197
  have eq153627 : ¬(new c a a) ∨ a = b ∨ a = sk1 := resolve eq153583 rfl -- duplicate literal removal 153583
  have eq160683 : (sP4 sk0 c a) ∨ b = sk0 ∨ (old a a b) ∨ a = sk1 ∨ a = sk1 ∨ b = sk0 := Or.assoc4 (eq145948.imp_left (fun h : a = sk2 ↦ superpose h eq111318)) -- superposition 111318,145948, 145948 into 111318, unify on (0).2 in 145948 and (0).3 in 111318
  have eq160686 : (sP4 sk0 c a) ∨ b = sk0 ∨ (old a a b) ∨ a = sk1 := resolve eq160683 rfl -- duplicate literal removal 160683
  have eq160709 : (old a a b) ∨ b = sk0 ∨ a = sk1 := resolve eq160686 rule_def_4_3 -- subsumption resolution 160686,168
  have eq160779 : (new c a a) ∨ a = sk1 ∨ b = sk0 := resolve eq160709 eq211 -- resolution 160709,211
  have eq160878 : a = sk1 ∨ b = sk0 ∨ a = b ∨ a = sk1 := resolve eq160779 eq153627 -- resolution 160779,153627
  have eq160890 : a = sk1 ∨ b = sk0 ∨ a = b := resolve eq160878 rfl -- duplicate literal removal 160878
  have eq161038 : (new sk0 a sk2) ∨ b = sk0 ∨ a = b := eq160890.imp_left (fun h : a = sk1 ↦ superpose h preserve_0) -- superposition 192,160890, 160890 into 192, unify on (0).2 in 160890 and (0).2 in 192
  have eq161040 : ¬(new a sk3 sk0) ∨ b = sk0 ∨ a = b := eq160890.imp_left (fun h : a = sk1 ↦ superpose h preserve_2) -- superposition 194,160890, 160890 into 194, unify on (0).2 in 160890 and (0).1 in 194
  have eq165410 : (new a a sk2) ∨ a = b ∨ a = b ∨ a = b := Or.assoc3 (eq104208.imp_left (fun h : a = sk0 ↦ superpose h eq161038)) -- superposition 161038,104208, 104208 into 161038, unify on (0).2 in 104208 and (0).1 in 161038
  have eq165472 : (new a a sk2) ∨ a = b := resolve eq165410 rfl -- duplicate literal removal 165410
  have eq165557 (X0 : G) : ¬(new a a X0) ∨ sk2 = X0 ∨ a = b := resolve eq165472 prev_0 -- resolution 165472,191
  have eq165601 : (new a a a) ∨ a = b ∨ a = sk1 := Or.assoc2 (eq147733.imp_left (fun h : a = sk2 ↦ superpose h eq165472)) -- superposition 165472,147733, 147733 into 165472, unify on (0).2 in 147733 and (0).3 in 165472
  have eq165989 : ¬(new a sk3 a) ∨ a = b ∨ a = b ∨ a = b := Or.assoc3 (eq104208.imp_left (fun h : a = sk0 ↦ superpose h eq161040)) -- superposition 161040,104208, 104208 into 161040, unify on (0).2 in 104208 and (0).3 in 161040
  have eq165991 : ¬(new a sk3 a) ∨ a = b := resolve eq165989 rfl -- duplicate literal removal 165989
  have eq166140 : ¬(new a a a) ∨ a = b ∨ a = sk1 ∨ a = b := Or.assoc2 (eq152822.imp_left (fun h : a = sk3 ↦ superpose h eq165991)) -- superposition 165991,152822, 152822 into 165991, unify on (0).2 in 152822 and (0).2 in 165991
  have eq166142 : ¬(new a a a) ∨ a = b ∨ a = sk1 := resolve eq166140 rfl -- duplicate literal removal 166140
  have eq166147 : a = sk1 ∨ a = b := resolve eq166142 eq165601 -- subsumption resolution 166142,165601
  have eq166524 : (new sk0 a b) ∨ a = b ∨ c = sk2 ∨ a = c ∨ c = sk0 ∨ a = b := Or.assoc5 (eq166147.imp_left (fun h : a = sk1 ↦ superpose h eq1635)) -- superposition 1635,166147, 166147 into 1635, unify on (0).2 in 166147 and (0).2 in 1635
  have eq167108 : (old a a sk2) ∨ c = sk2 ∨ a = c ∨ a = b ∨ a = b := Or.assoc4 (eq166147.imp_left (fun h : a = sk1 ↦ superpose h eq104834)) -- superposition 104834,166147, 166147 into 104834, unify on (0).2 in 166147 and (0).2 in 104834
  have eq167109 : (sP0 a a sk2) ∨ (old a a sk2) ∨ a = b ∨ a = c ∨ a = b := Or.assoc4 (eq166147.imp_left (fun h : a = sk1 ↦ superpose h eq104850)) -- superposition 104850,166147, 166147 into 104850, unify on (0).2 in 166147 and (0).2 in 104850
  have eq167111 : ¬(new a c a) ∨ c = sk2 ∨ a = c ∨ a = b ∨ a = b := Or.assoc4 (eq166147.imp_left (fun h : a = sk1 ↦ superpose h eq104881)) -- superposition 104881,166147, 166147 into 104881, unify on (0).2 in 166147 and (0).1 in 104881
  have eq167135 : ¬(new a c a) ∨ c = sk2 ∨ a = c ∨ a = b := resolve eq167111 rfl -- duplicate literal removal 167111
  have eq167137 : (sP0 a a sk2) ∨ (old a a sk2) ∨ a = b ∨ a = c := resolve eq167109 rfl -- duplicate literal removal 167109
  have eq167138 : (old a a sk2) ∨ c = sk2 ∨ a = c ∨ a = b := resolve eq167108 rfl -- duplicate literal removal 167108
  have eq167553 : (new sk0 a b) ∨ a = b ∨ c = sk2 ∨ a = c ∨ c = sk0 := resolve eq166524 rfl -- duplicate literal removal 166524
  have eq167821 : (new sk0 a b) ∨ a = b ∨ c = sk2 ∨ c = sk0 := resolve eq167553 ac -- subsumption resolution 167553,128
  have eq167902 : (old a a sk2) ∨ c = sk2 ∨ a = b := resolve eq167138 ac -- subsumption resolution 167138,128
  have eq167903 : (sP0 a a sk2) ∨ (old a a sk2) ∨ a = b := resolve eq167137 ac -- subsumption resolution 167137,128
  have eq167904 : (old a a sk2) ∨ a = b := resolve eq167903 rule_def_0_1 -- subsumption resolution 167903,148
  have eq167905 : ¬(new a c a) ∨ c = sk2 ∨ a = b := resolve eq167135 ac -- subsumption resolution 167135,128
  have eq177075 : (new a a b) ∨ a = b ∨ c = sk2 ∨ a = c ∨ a = b := Or.assoc4 (eq104208.imp_left (fun h : a = sk0 ↦ superpose h eq167821)) -- superposition 167821,104208, 104208 into 167821, unify on (0).2 in 104208 and (0).1 in 167821
  have eq177079 : (new a a b) ∨ a = b ∨ c = sk2 ∨ a = c := resolve eq177075 rfl -- duplicate literal removal 177075
  have eq177088 : (new a a b) ∨ a = b ∨ c = sk2 := resolve eq177079 ac -- subsumption resolution 177079,128
  have eq177120 : a = b ∨ c = sk2 ∨ b = sk2 ∨ a = b := resolve eq177088 eq165557 -- resolution 177088,165557
  have eq177123 : b = sk2 ∨ c = sk2 ∨ a = b := resolve eq177120 rfl -- duplicate literal removal 177120
  have eq178082 : (old a a b) ∨ c = b ∨ a = b ∨ c = sk2 ∨ a = b := Or.assoc3 (eq177123.imp_left (fun h : b = sk2 ↦ superpose h eq167902)) -- superposition 167902,177123, 177123 into 167902, unify on (0).2 in 177123 and (0).3 in 167902
  have eq178090 : (old a a b) ∨ c = b ∨ a = b ∨ c = sk2 := resolve eq178082 rfl -- duplicate literal removal 178082
  have eq178629 : (old a a b) ∨ a = b ∨ c = sk2 := resolve eq178090 bc -- subsumption resolution 178090,129
  have eq179470 : a = b ∨ c = sk2 ∨ (new a c a) := resolve eq178629 eq208 -- resolution 178629,208
  have eq179525 : c = sk2 ∨ a = b := resolve eq179470 eq167905 -- subsumption resolution 179470,167905
  have eq180477 : (old a a c) ∨ a = b ∨ a = b := Or.assoc2 (eq179525.imp_left (fun h : c = sk2 ↦ superpose h eq167904)) -- superposition 167904,179525, 179525 into 167904, unify on (0).2 in 179525 and (0).3 in 167904
  have eq180482 : (old a a c) ∨ a = b := resolve eq180477 rfl -- duplicate literal removal 180477
  have eq180909 : a = b := resolve eq180482 p4XY -- subsumption resolution 180482,131
  have eq180911 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq180909, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 130,180909
  have eq180914 : ∀ (X0 X1 X2 : G) , ¬(sP1 X0 X1 X2) ∨ (old X2 a a) := Eq.mp (by simp only [eq180909, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_1_2 -- backward demodulation 153,180909
  have eq180917 : ∀ (X0 X1 X2 : G) , (old a a a) ∨ ¬(sP2 X0 X1 X2) := Eq.mp (by simp only [eq180909, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_2_3 -- backward demodulation 158,180909
  have eq180920 : ∀ (X0 X1 X2 : G) , (old a a a) ∨ ¬(sP4 X0 X1 X2) := Eq.mp (by simp only [eq180909, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_4_3 -- backward demodulation 168,180909
  have eq180921 : ∀ (X0 X1 X2 : G) , (old a a a) ∨ ¬(sP5 X0 X1 X2) := Eq.mp (by simp only [eq180909, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_5_3 -- backward demodulation 173,180909
  have eq180922 : ∀ (X0 X1 X2 : G) , (old a a a) ∨ ¬(sP6 X0 X1 X2) := Eq.mp (by simp only [eq180909, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_6_2 -- backward demodulation 177,180909
  have eq184020 : (old a a a) ∨ (old sk2 sk1 sk3) ∨ b = sk2 ∨ a = sk2 ∨ (old a a b) ∨ (old b sk3 b) := Eq.mp (by simp only [eq180909, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq46252 -- backward demodulation 46252,180909
  have eq184777 : (old sk2 a a) ∨ (sP5 c sk1 sk2) ∨ (sP2 c sk1 sk2) ∨ a = sk0 := Eq.mp (by simp only [eq180909, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq73245 -- backward demodulation 73245,180909
  have eq187901 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) := resolve eq180917 eq180911 -- subsumption resolution 180917,180911
  have eq187903 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) := resolve eq180920 eq180911 -- subsumption resolution 180920,180911
  have eq187904 (X0 X1 X2 : G) : ¬(sP5 X0 X1 X2) := resolve eq180921 eq180911 -- subsumption resolution 180921,180911
  have eq187905 (X0 X1 X2 : G) : ¬(sP6 X0 X1 X2) := resolve eq180922 eq180911 -- subsumption resolution 180922,180911
  have eq190186 : (old sk2 sk1 sk3) ∨ b = sk2 ∨ a = sk2 ∨ (old a a b) ∨ (old b sk3 b) := resolve eq184020 eq180911 -- subsumption resolution 184020,180911
  have eq190187 : (old sk2 sk1 sk3) ∨ b = sk2 ∨ a = sk2 ∨ (old b sk3 b) := resolve eq190186 eq180911 -- subsumption resolution 190186,180911
  have eq190188 : a = sk2 ∨ (old sk2 sk1 sk3) ∨ a = sk2 ∨ (old b sk3 b) := Eq.mp (by simp only [eq180909, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq190187 -- forward demodulation 190187,180909
  have eq190189 : a = sk2 ∨ (old sk2 sk1 sk3) ∨ (old b sk3 b) := resolve eq190188 rfl -- duplicate literal removal 190188
  have eq190190 : (old a sk3 a) ∨ a = sk2 ∨ (old sk2 sk1 sk3) := Eq.mp (by simp only [eq180909, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq190189 -- forward demodulation 190189,180909
  have eq190764 : (old sk2 a a) ∨ (sP2 c sk1 sk2) ∨ a = sk0 := resolve eq184777 eq187904 -- subsumption resolution 184777,187904
  have eq190765 : (old sk2 a a) ∨ a = sk0 := resolve eq190764 eq187901 -- subsumption resolution 190764,187901
  have eq192816 : (old a a a) ∨ a = sk0 ∨ a = sk0 := Or.assoc2 (eq133797.imp_left (fun h : a = sk2 ↦ superpose h eq190765)) -- superposition 190765,133797, 133797 into 190765, unify on (0).2 in 133797 and (0).1 in 190765
  have eq192818 : (old a a a) ∨ a = sk0 := resolve eq192816 rfl -- duplicate literal removal 192816
  have eq192828 : a = sk0 := resolve eq192818 eq180911 -- subsumption resolution 192818,180911
  have eq192830 : ¬(new sk1 sk3 a) := Eq.mp (by simp only [eq192828, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_2 -- backward demodulation 194,192828
  have eq192837 : (old a sk1 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := Eq.mp (by simp only [eq192828, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq320 -- backward demodulation 320,192828
  have eq193081 : (sP6 a c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ a = sk1 := Eq.mp (by simp only [eq192828, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq111223 -- backward demodulation 111223,192828
  have eq193242 : a = c ∨ (old a sk1 sk2) ∨ c = sk2 ∨ c = sk1 := Eq.mp (by simp only [eq192828, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq192837 -- forward demodulation 192837,192828
  have eq193243 : (old a sk1 sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq193242 ac -- subsumption resolution 193242,128
  have eq193317 : (sP1 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ a = sk1 := resolve eq193081 eq187905 -- subsumption resolution 193081,187905
  have eq193318 : (sP1 sk0 c sk2) ∨ a = sk1 := resolve eq193317 eq187903 -- subsumption resolution 193317,187903
  have eq193319 : (sP1 a c sk2) ∨ a = sk1 := Eq.mp (by simp only [eq192828, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq193318 -- forward demodulation 193318,192828
  have eq193448 : (old sk2 a a) ∨ a = sk1 := resolve eq193319 eq180914 -- resolution 193319,180914
  have eq193590 : (old a a a) ∨ a = sk1 ∨ a = sk1 := Or.assoc2 (eq147733.imp_left (fun h : a = sk2 ↦ superpose h eq193448)) -- superposition 193448,147733, 147733 into 193448, unify on (0).2 in 147733 and (0).1 in 193448
  have eq193591 : (old a a a) ∨ a = sk1 := resolve eq193590 rfl -- duplicate literal removal 193590
  have eq193595 : a = sk1 := resolve eq193591 eq180911 -- subsumption resolution 193591,180911
  have eq193674 : (old sk2 a sk3) ∨ (old a sk3 a) ∨ a = sk2 := Eq.mp (by simp only [eq193595, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq190190 -- backward demodulation 190190,193595
  have eq193736 : ¬(new a sk3 a) := Eq.mp (by simp only [eq193595, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq192830 -- backward demodulation 192830,193595
  have eq193743 : a = c ∨ (old a sk1 sk2) ∨ c = sk2 := Eq.mp (by simp only [eq193595, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq193243 -- backward demodulation 193243,193595
  have eq193937 : (old a sk1 sk2) ∨ c = sk2 := resolve eq193743 ac -- subsumption resolution 193743,128
  have eq193938 : (old a a sk2) ∨ c = sk2 := Eq.mp (by simp only [eq193595, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq193937 -- forward demodulation 193937,193595
  have eq193939 : c = sk2 := resolve eq193938 eq180911 -- subsumption resolution 193938,180911
  have eq193951 : a = c ∨ (old sk2 a sk3) ∨ (old a sk3 a) := Eq.mp (by simp only [eq193939, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq193674 -- backward demodulation 193674,193939
  have eq194028 : (old sk2 a sk3) ∨ (old a sk3 a) := resolve eq193951 ac -- subsumption resolution 193951,128
  have eq194029 : (old c a sk3) ∨ (old a sk3 a) := Eq.mp (by simp only [eq193939, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq194028 -- forward demodulation 194028,193939
  have eq194030 : (old a sk3 a) := resolve eq194029 p4YZ -- subsumption resolution 194029,133
  have eq194121 : (new a sk3 a) := resolve eq194030 imp_new_0 -- resolution 194030,145
  subsumption eq193736 eq194121 -- subsumption resolution 194121,193736

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (prev_1 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X2 X1 X3 ∨ new X1 X3 X0)) : (∀ X0 X1 X2, ¬ new X0 X1 X2 ∨ ¬ new X1 X1 X0 ∨ new X2 X1 X1) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq228 (X0 : G) : ¬(new X0 sk1 sk0) ∨ (new sk1 sk2 X0) := resolve prev_1 preserve_0 -- resolution 194,195
  have eq231 : (new sk1 sk2 sk1) := resolve eq228 preserve_1 -- resolution 228,196
  have eq232 (X0 : G) : ¬(new X0 sk2 sk1) ∨ (new sk2 sk1 X0) := resolve eq231 prev_1 -- resolution 231,194
  have eq250 : (new sk2 sk1 sk1) := resolve eq232 eq231 -- resolution 232,231
  subsumption preserve_2 eq250 -- subsumption resolution 250,197

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_3_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_3 : (∀ X0 X1, ¬ old X0 X1 X1 ∨ old X1 X0 X1)) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z, b ≠ X ∨ c ≠ Y ∨ ¬ old Z b a ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), b = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z b a ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b b a ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), b = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP3 X Y Z) (imp_new_5 : ∀ X Y Z, a ≠ X ∨ c ≠ Y ∨ a ≠ Z ∨ ¬ old a a b ∨ new X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP4 X Y Z) (rule_def_5_0 : ∀ (X Y Z : G), c = X ∨ ¬sP5 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), old a a b ∨ ¬sP5 X Y Z) (rule_def_6_0 : ∀ (X Y Z : G), a = X ∨ ¬sP6 X Y Z) (rule_def_6_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP6 X Y Z) (rule_def_6_3 : ∀ (X Y Z : G), old Z a b ∨ ¬sP6 X Y Z) (rule_def_7_0 : ∀ (X Y Z : G), a = b ∨ ¬sP7 X Y Z) (rule_def_7_1 : ∀ (X Y Z : G), c = X ∨ ¬sP7 X Y Z) (rule_def_7_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP7 X Y Z) (rule_def_7_3 : ∀ (X Y Z : G), old Z b b ∨ ¬sP7 X Y Z) (rule_def_8_0 : ∀ (X Y Z : G), b = X ∨ ¬sP8 X Y Z) (rule_def_8_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP8 X Y Z) (rule_def_8_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP8 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1, ¬ new X0 X1 X1 ∨ new X1 X0 X1) := by
  by_contra! nh
  obtain ⟨sk0, sk1, preserve_0, preserve_1⟩ := nh
  have eq202 (X0 X2 : G) : (new X0 c X2) ∨ ¬(old X2 b a) ∨ b ≠ X0 := resolve imp_new_2 rfl -- equality resolution 153
  have eq203 (X2 : G) : ¬(old X2 b a) ∨ (new b c X2) := resolve eq202 rfl -- equality resolution 202
  have eq210 (X0 X1 : G) : (new X0 X1 a) ∨ ¬(old a a b) ∨ c ≠ X1 ∨ a ≠ X0 := resolve imp_new_5 rfl -- equality resolution 167
  have eq211 (X0 : G) : (new X0 c a) ∨ ¬(old a a b) ∨ a ≠ X0 := resolve eq210 rfl -- equality resolution 210
  have eq212 : ¬(old a a b) ∨ (new a c a) := resolve eq211 rfl -- equality resolution 211
  have eq229 : (sP8 sk0 sk1 sk1) ∨ (sP6 sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) := resolve new_imp preserve_0 -- resolution 193,197
  have eq248 : (sP6 sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ c = sk1 := resolve eq229 rule_def_8_2 -- resolution 229,190
  have eq249 : (sP6 sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ a = sk1 := resolve eq229 rule_def_8_1 -- resolution 229,189
  have eq250 : (sP6 sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ b = sk0 := resolve eq229 rule_def_8_0 -- resolution 229,188
  have eq253 : (sP5 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ c = sk1 := resolve eq248 rule_def_6_1 -- subsumption resolution 248,179
  have eq254 : (sP5 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ c = sk1 := resolve eq253 rule_def_4_1 -- subsumption resolution 253,169
  have eq255 : (sP5 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ c = sk1 := resolve eq254 rule_def_3_2 -- subsumption resolution 254,165
  have eq256 : (sP5 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ c = sk1 := resolve eq255 rule_def_1_1 -- subsumption resolution 255,155
  have eq257 : (sP7 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ c = sk1 := resolve eq256 rule_def_0_2 -- subsumption resolution 256,152
  have eq258 : (sP6 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ a = sk1 := resolve eq249 rule_def_5_2 -- subsumption resolution 249,175
  have eq259 : (sP6 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ a = sk1 := resolve eq258 rule_def_4_2 -- subsumption resolution 258,170
  have eq260 : (sP7 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP6 sk0 sk1 sk1) ∨ a = sk1 := resolve eq259 rule_def_3_1 -- subsumption resolution 259,164
  have eq261 : (sP6 sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ b = sk0 := resolve eq250 rule_def_3_0 -- subsumption resolution 250,163
  have eq262 : (sP7 sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP6 sk0 sk1 sk1) ∨ b = sk0 := resolve eq261 rule_def_1_0 -- subsumption resolution 261,154
  have eq268 : (sP5 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b) := resolve eq257 rule_def_7_3 -- resolution 257,186
  have eq270 : (sP2 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ c = sk1 ∨ c = sk0 := resolve eq257 rule_def_7_1 -- resolution 257,184
  have eq271 : (sP5 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ c = sk1 ∨ a = b := resolve eq257 rule_def_7_0 -- resolution 257,183
  have eq273 : (sP2 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ c = sk1 ∨ c = sk0 := resolve eq270 rule_def_5_0 -- subsumption resolution 270,173
  have eq274 : (old sk0 sk1 sk1) ∨ c = sk1 ∨ c = sk0 := resolve eq273 rule_def_2_0 -- subsumption resolution 273,158
  have eq276 : (old sk1 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq274 old_3 -- resolution 274,140
  have eq287 : (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP6 sk0 sk1 sk1) ∨ a = sk1 ∨ b = sk1 := resolve eq260 rule_def_7_2 -- resolution 260,185
  have eq290 : (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP6 sk0 sk1 sk1) ∨ a = sk1 ∨ b = sk1 := resolve eq287 rule_def_2_2 -- subsumption resolution 287,160
  have eq291 : (sP6 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ a = sk1 ∨ b = sk1 := resolve eq290 rule_def_0_1 -- subsumption resolution 290,151
  have eq301 : c = sk0 ∨ c = sk1 ∨ (new sk1 sk0 sk1) := resolve eq276 imp_new_0 -- resolution 276,148
  have eq302 : c = sk1 ∨ c = sk0 := resolve eq301 preserve_1 -- subsumption resolution 301,198
  have eq323 : (sP5 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP6 sk0 sk1 sk1) ∨ b = sk0 ∨ b = sk1 := resolve eq262 rule_def_7_2 -- resolution 262,185
  have eq327 : (sP5 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP6 sk0 sk1 sk1) ∨ b = sk0 ∨ b = sk1 := resolve eq323 rule_def_2_2 -- subsumption resolution 323,160
  have eq328 : (sP6 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ b = sk0 ∨ b = sk1 := resolve eq327 rule_def_0_1 -- subsumption resolution 327,151
  have eq353 : (old sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ c = sk1 ∨ a = b ∨ a = sk1 := resolve eq271 rule_def_5_2 -- resolution 271,175
  have eq365 : (sP6 sk0 c c) ∨ (old sk0 c c) ∨ (sP1 sk0 c c) ∨ a = c ∨ c = b ∨ c = sk0 := Or.assoc5 (eq302.imp_left (fun h : c = sk1 ↦ superpose h eq291)) -- superposition 291,302, 302 into 291, unify on (0).2 in 302 and (0).2 in 291
  have eq366 : (sP6 sk0 c c) ∨ (sP1 sk0 c c) ∨ a = c ∨ c = b ∨ c = sk0 := resolve eq365 p4XZ -- subsumption resolution 365,135
  have eq367 : (sP6 sk0 c c) ∨ (sP1 sk0 c c) ∨ c = b ∨ c = sk0 := resolve eq366 ac -- subsumption resolution 366,131
  have eq368 : (sP6 sk0 c c) ∨ (sP1 sk0 c c) ∨ c = sk0 := resolve eq367 bc -- subsumption resolution 367,132
  have eq372 : (old sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b) ∨ (old a a b) := resolve eq268 rule_def_5_3 -- resolution 268,176
  have eq389 : (sP4 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ b = sk0 ∨ b = sk1 ∨ a = sk0 := resolve eq328 rule_def_6_0 -- resolution 328,178
  have eq391 : (old sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ b = sk0 ∨ b = sk1 ∨ a = sk0 := resolve eq389 rule_def_4_0 -- subsumption resolution 389,168
  have eq395 : (sP1 sk0 c c) ∨ c = sk0 ∨ (old c a b) := resolve eq368 rule_def_6_3 -- resolution 368,181
  have eq399 : (sP1 sk0 c c) ∨ c = sk0 := resolve eq395 p4YZ -- subsumption resolution 395,136
  have eq408 : c = sk0 ∨ (old c b a) := resolve eq399 rule_def_1_2 -- resolution 399,156
  have eq411 : c = sk0 := resolve eq408 p4YZ -- subsumption resolution 408,136
  have eq413 : ¬(new sk1 c sk1) := Eq.mp (by simp only [eq411, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_1 -- backward demodulation 198,411
  have eq441 : (sP2 c sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ c = sk1 ∨ a = b ∨ a = sk1 := Eq.mp (by simp only [eq411, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq353 -- backward demodulation 353,411
  have eq445 : (sP2 c sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b) ∨ (old a a b) := Eq.mp (by simp only [eq411, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq372 -- backward demodulation 372,411
  have eq452 : (sP5 c sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ b = sk0 ∨ b = sk1 ∨ a = sk0 := Eq.mp (by simp only [eq411, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq391 -- backward demodulation 391,411
  have eq556 : (old c sk1 sk1) ∨ (sP2 c sk1 sk1) ∨ c = sk1 ∨ a = b ∨ a = sk1 := Eq.mp (by simp only [eq411, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq441 -- forward demodulation 441,411
  have eq557 : (sP2 c sk1 sk1) ∨ c = sk1 ∨ a = b ∨ a = sk1 := resolve eq556 p4YZ -- subsumption resolution 556,136
  have eq566 : (old c sk1 sk1) ∨ (sP2 c sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b) ∨ (old a a b) := Eq.mp (by simp only [eq411, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq445 -- forward demodulation 445,411
  have eq567 : (sP2 c sk1 sk1) ∨ c = sk1 ∨ (old sk1 b b) ∨ (old a a b) := resolve eq566 p4YZ -- subsumption resolution 566,136
  have eq580 : (old c sk1 sk1) ∨ (sP5 c sk1 sk1) ∨ b = sk0 ∨ b = sk1 ∨ a = sk0 := Eq.mp (by simp only [eq411, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq452 -- forward demodulation 452,411
  have eq581 : (sP5 c sk1 sk1) ∨ b = sk0 ∨ b = sk1 ∨ a = sk0 := resolve eq580 p4YZ -- subsumption resolution 580,136
  have eq582 : c = b ∨ (sP5 c sk1 sk1) ∨ b = sk1 ∨ a = sk0 := Eq.mp (by simp only [eq411, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq581 -- forward demodulation 581,411
  have eq583 : (sP5 c sk1 sk1) ∨ b = sk1 ∨ a = sk0 := resolve eq582 bc -- subsumption resolution 582,132
  have eq584 : a = c ∨ (sP5 c sk1 sk1) ∨ b = sk1 := Eq.mp (by simp only [eq411, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq583 -- forward demodulation 583,411
  have eq585 : (sP5 c sk1 sk1) ∨ b = sk1 := resolve eq584 ac -- subsumption resolution 584,131
  have eq590 : (old a a b) ∨ b = sk1 := resolve eq585 rule_def_5_3 -- resolution 585,176
  have eq591 : b = sk1 ∨ a = sk1 := resolve eq585 rule_def_5_2 -- resolution 585,175
  have eq599 : ¬(new b c b) ∨ a = sk1 := eq591.imp_left (fun h : b = sk1 ↦ superpose h eq413) -- superposition 413,591, 591 into 413, unify on (0).2 in 591 and (0).1 in 413
  have eq603 : a ≠ b ∨ a = sk1 := resolve eq591 trans_resol -- equality factoring 591
  have eq618 : (new a c a) ∨ b = sk1 := resolve eq590 eq212 -- resolution 590,212
  have eq795 : (sP2 c b b) ∨ c = b ∨ a = b ∨ a = b ∨ a = sk1 := Or.assoc4 (eq591.imp_left (fun h : b = sk1 ↦ superpose h eq557)) -- superposition 557,591, 591 into 557, unify on (0).2 in 591 and (0).2 in 557
  have eq796 : (sP2 c b b) ∨ c = b ∨ a = b ∨ a = sk1 := resolve eq795 rfl -- duplicate literal removal 795
  have eq801 : (sP2 c b b) ∨ a = b ∨ a = sk1 := resolve eq796 bc -- subsumption resolution 796,132
  have eq802 : (sP2 c b b) ∨ a = sk1 := resolve eq801 eq603 -- subsumption resolution 801,603
  have eq803 : (old b b a) ∨ a = sk1 := resolve eq802 rule_def_2_3 -- resolution 802,161
  have eq816 : a = sk1 ∨ (new b c b) := resolve eq803 eq203 -- resolution 803,203
  have eq827 : a = sk1 := resolve eq816 eq599 -- subsumption resolution 816,599
  have eq829 : ¬(new a c a) := Eq.mp (by simp only [eq827, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq413 -- backward demodulation 413,827
  have eq849 : a = c ∨ (sP2 c sk1 sk1) ∨ (old sk1 b b) ∨ (old a a b) := Eq.mp (by simp only [eq827, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq567 -- backward demodulation 567,827
  have eq857 : a = b ∨ (new a c a) := Eq.mp (by simp only [eq827, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq618 -- backward demodulation 618,827
  have eq955 : (sP2 c sk1 sk1) ∨ (old sk1 b b) ∨ (old a a b) := resolve eq849 ac -- subsumption resolution 849,131
  have eq956 : (sP2 c a a) ∨ (old sk1 b b) ∨ (old a a b) := Eq.mp (by simp only [eq827, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq955 -- forward demodulation 955,827
  have eq957 : (old a b b) ∨ (sP2 c a a) ∨ (old a a b) := Eq.mp (by simp only [eq827, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq956 -- forward demodulation 956,827
  have eq958 : (sP2 c a a) ∨ (old a a b) := resolve eq957 p3 -- subsumption resolution 957,133
  have eq964 : a = b := resolve eq857 eq829 -- subsumption resolution 857,829
  have eq966 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq964, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 133,964
  have eq972 : ∀ (X0 X1 X2 : G) , (old a a a) ∨ ¬(sP2 X0 X1 X2) := Eq.mp (by simp only [eq964, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_2_3 -- backward demodulation 161,964
  have eq1005 : (old a a a) ∨ (sP2 c a a) := Eq.mp (by simp only [eq964, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq958 -- backward demodulation 958,964
  have eq1008 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) := resolve eq972 eq966 -- subsumption resolution 972,966
  have eq1050 : (sP2 c a a) := resolve eq1005 eq966 -- subsumption resolution 1005,966
  subsumption eq1008 eq1050 -- subsumption resolution 1050,1008

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_4_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (prev_1 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X2 X1 X3 ∨ new X1 X3 X0)) (prev_2 : (∀ X0 X1 X2, ¬ new X0 X1 X2 ∨ ¬ new X1 X1 X0 ∨ new X2 X1 X1)) : (∀ X0 X1 X2, ¬ new X0 X0 X1 ∨ ¬ new X1 X0 X2 ∨ new X0 X1 X2) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq234 (X0 : G) : ¬(new X0 sk0 sk0) ∨ (new sk0 sk1 X0) := resolve prev_1 preserve_0 -- resolution 198,201
  have eq237 (X0 : G) : ¬(new sk1 sk0 X0) ∨ (new X0 sk0 sk0) := resolve prev_2 preserve_0 -- resolution 199,201
  have eq247 : (new sk2 sk0 sk0) := resolve eq237 preserve_1 -- resolution 237,202
  have eq248 : (new sk0 sk1 sk2) := resolve eq247 eq234 -- resolution 247,234
  subsumption preserve_2 eq248 -- subsumption resolution 248,203

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_5_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (prev_1 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X2 X1 X3 ∨ new X1 X3 X0)) (old_3 : (∀ X0 X1, ¬ old X0 X1 X1 ∨ old X1 X0 X1)) (old_5 : (∀ X0 X1 X2, ¬ old X0 X0 X1 ∨ ¬ old X0 X1 X2 ∨ old X0 X2 X0)) (imp_new_1 : ∀ X Y Z, a ≠ X ∨ b ≠ Y ∨ c ≠ Z ∨ new X Y Z) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), b = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z b a ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), b = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b b a ∨ ¬sP3 X Y Z) (imp_new_5 : ∀ X Y Z, a ≠ X ∨ c ≠ Y ∨ a ≠ Z ∨ ¬ old a a b ∨ new X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), old a a b ∨ ¬sP4 X Y Z) (rule_def_5_0 : ∀ (X Y Z : G), c = X ∨ ¬sP5 X Y Z) (rule_def_5_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), old a a b ∨ ¬sP5 X Y Z) (rule_def_6_0 : ∀ (X Y Z : G), a = X ∨ ¬sP6 X Y Z) (rule_def_6_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP6 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), old b b a ∨ ¬sP6 X Y Z) (rule_def_7_1 : ∀ (X Y Z : G), c = X ∨ ¬sP7 X Y Z) (rule_def_7_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP7 X Y Z) (rule_def_8_0 : ∀ (X Y Z : G), b = X ∨ ¬sP8 X Y Z) (rule_def_8_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP8 X Y Z) (rule_def_8_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP8 X Y Z) (rule_def_8_3 : ∀ (X Y Z : G), old a a b ∨ ¬sP8 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2, ¬ new X0 X0 X1 ∨ ¬ new X0 X1 X2 ∨ new X0 X2 X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq207 (X0 X1 : G) : (new X0 X1 c) ∨ b ≠ X1 ∨ a ≠ X0 := resolve imp_new_1 rfl -- equality resolution 154
  have eq208 (X0 : G) : (new X0 b c) ∨ a ≠ X0 := resolve eq207 rfl -- equality resolution 207
  have eq209 : (new a b c) := resolve eq208 rfl -- equality resolution 208
  have eq218 (X0 X1 : G) : (new X0 X1 a) ∨ ¬(old a a b) ∨ c ≠ X1 ∨ a ≠ X0 := resolve imp_new_5 rfl -- equality resolution 172
  have eq219 (X0 : G) : (new X0 c a) ∨ ¬(old a a b) ∨ a ≠ X0 := resolve eq218 rfl -- equality resolution 218
  have eq220 : ¬(old a a b) ∨ (new a c a) := resolve eq219 rfl -- equality resolution 219
  have eq239 (X0 : G) : ¬(new X0 b a) ∨ (new b c X0) := resolve prev_1 eq209 -- resolution 200,209
  have eq244 : (sP8 sk0 sk0 sk1) ∨ (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) := resolve new_imp preserve_0 -- resolution 198,204
  have eq245 : (sP8 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) := resolve new_imp preserve_1 -- resolution 198,205
  have eq264 : (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ c = sk1 := resolve eq244 rule_def_8_2 -- resolution 244,195
  have eq265 : (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ a = sk0 := resolve eq244 rule_def_8_1 -- resolution 244,194
  have eq266 : (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ b = sk0 := resolve eq244 rule_def_8_0 -- resolution 244,193
  have eq269 : (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ c = sk1 := resolve eq264 rule_def_3_2 -- subsumption resolution 264,170
  have eq270 : (sP7 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP6 sk0 sk0 sk1) ∨ c = sk1 := resolve eq269 rule_def_0_2 -- subsumption resolution 269,157
  have eq271 : (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ a = sk0 := resolve eq265 rule_def_6_0 -- subsumption resolution 265,183
  have eq272 : (sP4 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ a = sk0 := resolve eq271 rule_def_5_1 -- subsumption resolution 271,179
  have eq273 : (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ a = sk0 := resolve eq272 rule_def_4_0 -- subsumption resolution 272,173
  have eq274 : (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ a = sk0 := resolve eq273 rule_def_3_1 -- subsumption resolution 273,169
  have eq275 : (sP7 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ a = sk0 := resolve eq274 rule_def_0_0 -- subsumption resolution 274,155
  have eq276 : (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 := resolve eq266 rule_def_7_2 -- subsumption resolution 266,190
  have eq277 : (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 := resolve eq276 rule_def_3_0 -- subsumption resolution 276,168
  have eq278 : (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 := resolve eq277 rule_def_2_1 -- subsumption resolution 277,164
  have eq279 : (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 := resolve eq278 rule_def_1_0 -- subsumption resolution 278,159
  have eq280 : (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 := resolve eq279 rule_def_0_1 -- subsumption resolution 279,156
  have eq286 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (old a a b) := resolve eq245 rule_def_8_3 -- resolution 245,196
  have eq287 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ c = sk2 := resolve eq245 rule_def_8_2 -- resolution 245,195
  have eq288 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ a = sk1 := resolve eq245 rule_def_8_1 -- resolution 245,194
  have eq289 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ b = sk0 := resolve eq245 rule_def_8_0 -- resolution 245,193
  have eq290 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (old a a b) := resolve eq286 rule_def_4_3 -- subsumption resolution 286,176
  have eq291 : (sP7 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (old a a b) := resolve eq290 rule_def_5_3 -- subsumption resolution 290,181
  have eq292 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ c = sk2 := resolve eq287 rule_def_3_2 -- subsumption resolution 287,170
  have eq293 : (sP7 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ c = sk2 := resolve eq292 rule_def_0_2 -- subsumption resolution 292,157
  have eq294 : (sP6 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ a = sk1 := resolve eq288 rule_def_5_1 -- subsumption resolution 288,179
  have eq295 : (sP7 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ a = sk1 := resolve eq294 rule_def_3_1 -- subsumption resolution 294,169
  have eq296 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ b = sk0 := resolve eq289 rule_def_3_0 -- subsumption resolution 289,168
  have eq297 : (sP7 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ b = sk0 := resolve eq296 rule_def_1_0 -- subsumption resolution 296,159
  have eq304 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ a = sk0 ∨ b = sk0 := resolve eq275 rule_def_7_2 -- resolution 275,190
  have eq307 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ a = sk0 ∨ b = sk0 := resolve eq304 rule_def_2_1 -- subsumption resolution 304,164
  have eq308 : (old sk0 sk0 sk1) ∨ a = sk0 ∨ b = sk0 := resolve eq307 rule_def_1_0 -- subsumption resolution 307,159
  have eq316 : (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 ∨ c = sk0 := resolve eq280 rule_def_6_1 -- resolution 280,184
  have eq318 : (sP4 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 ∨ c = sk0 := resolve eq316 rule_def_5_0 -- subsumption resolution 316,178
  have eq319 : (old sk0 sk0 sk1) ∨ b = sk0 ∨ c = sk0 := resolve eq318 rule_def_4_1 -- subsumption resolution 318,174
  have eq347 : (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP6 sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := resolve eq270 rule_def_7_1 -- resolution 270,189
  have eq349 : (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := resolve eq347 rule_def_6_1 -- subsumption resolution 347,184
  have eq350 : (sP4 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := resolve eq349 rule_def_5_0 -- subsumption resolution 349,178
  have eq351 : (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := resolve eq350 rule_def_4_1 -- subsumption resolution 350,174
  have eq352 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := resolve eq351 rule_def_2_0 -- subsumption resolution 351,163
  have eq353 : (old sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := resolve eq352 rule_def_1_1 -- subsumption resolution 352,160
  have eq366 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 := resolve eq293 rule_def_7_1 -- resolution 293,189
  have eq369 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 := resolve eq366 rule_def_5_0 -- subsumption resolution 366,178
  have eq370 : (sP6 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 := resolve eq369 rule_def_2_0 -- subsumption resolution 369,163
  have eq382 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 := resolve eq295 rule_def_7_2 -- resolution 295,190
  have eq385 : (sP4 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 := resolve eq382 rule_def_2_1 -- subsumption resolution 382,164
  have eq386 : (sP6 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 := resolve eq385 rule_def_0_1 -- subsumption resolution 385,156
  have eq392 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 := resolve eq297 rule_def_7_2 -- resolution 297,190
  have eq393 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ b = sk0 ∨ c = sk0 := resolve eq297 rule_def_7_1 -- resolution 297,189
  have eq395 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 := resolve eq392 rule_def_2_1 -- subsumption resolution 392,164
  have eq396 : (sP6 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 := resolve eq395 rule_def_0_1 -- subsumption resolution 395,156
  have eq397 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ b = sk0 ∨ c = sk0 := resolve eq393 rule_def_5_0 -- subsumption resolution 393,178
  have eq398 : (sP6 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk0 ∨ c = sk0 := resolve eq397 rule_def_2_0 -- subsumption resolution 397,163
  have eq425 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 := resolve eq291 rule_def_7_2 -- resolution 291,190
  have eq428 : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 := resolve eq425 rule_def_2_1 -- subsumption resolution 425,164
  have eq429 : (sP6 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 := resolve eq428 rule_def_0_1 -- subsumption resolution 428,156
  have eq505 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq370 rule_def_6_1 -- resolution 370,184
  have eq507 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq505 rule_def_4_1 -- subsumption resolution 505,174
  have eq508 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq507 rule_def_1_1 -- subsumption resolution 507,160
  have eq513 : c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ (old sk0 sk2 sk0) ∨ ¬(old sk0 sk0 sk1) := resolve eq508 old_5 -- resolution 508,147
  have eq519 : (old sk0 sk2 sk0) ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := resolve eq513 eq353 -- subsumption resolution 513,353
  have eq552 : c = sk0 ∨ c = sk1 ∨ c = sk2 ∨ (new sk0 sk2 sk0) := resolve eq519 imp_new_0 -- resolution 519,153
  have eq553 : c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq552 preserve_2 -- subsumption resolution 552,206
  have eq557 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq398 rule_def_6_0 -- resolution 398,183
  have eq559 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq557 rule_def_4_0 -- subsumption resolution 557,173
  have eq560 : (old sk0 sk1 sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq559 rule_def_0_0 -- subsumption resolution 559,155
  have eq562 : ¬(new sk0 c sk0) ∨ c = sk1 ∨ c = sk0 := eq553.imp_left (fun h : c = sk2 ↦ superpose h preserve_2) -- superposition 206,553, 553 into 206, unify on (0).2 in 553 and (0).2 in 206
  have eq565 : (sP7 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := Or.assoc8 (eq553.imp_left (fun h : c = sk2 ↦ superpose h eq295)) -- superposition 295,553, 553 into 295, unify on (0).2 in 553 and (0).3 in 295
  have eq567 : (sP6 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := Or.assoc6 (eq553.imp_left (fun h : c = sk2 ↦ superpose h eq386)) -- superposition 386,553, 553 into 386, unify on (0).2 in 553 and (0).3 in 386
  have eq568 : (sP6 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ b = sk0 ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := Or.assoc6 (eq553.imp_left (fun h : c = sk2 ↦ superpose h eq396)) -- superposition 396,553, 553 into 396, unify on (0).2 in 553 and (0).3 in 396
  have eq585 : (sP7 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq565 p4XY -- subsumption resolution 565,139
  have eq586 : (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq585 rule_def_7_1 -- subsumption resolution 585,189
  have eq587 : (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq586 rule_def_6_1 -- subsumption resolution 586,184
  have eq588 : (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq587 rule_def_4_1 -- subsumption resolution 587,174
  have eq589 : (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq588 rule_def_2_0 -- subsumption resolution 588,163
  have eq590 : (sP0 sk0 sk1 c) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq589 rule_def_1_1 -- subsumption resolution 589,160
  have eq597 : (sP6 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq567 p4XY -- subsumption resolution 567,139
  have eq598 : (sP1 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq597 rule_def_6_1 -- subsumption resolution 597,184
  have eq599 : (sP1 sk0 sk1 c) ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq598 rule_def_4_1 -- subsumption resolution 598,174
  have eq600 : b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq599 rule_def_1_1 -- subsumption resolution 599,160
  have eq601 : (sP6 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ b = sk0 ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq568 p4XY -- subsumption resolution 568,139
  have eq602 : (sP4 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ b = sk0 ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq601 rule_def_6_1 -- subsumption resolution 601,184
  have eq603 : (sP4 sk0 sk1 c) ∨ b = sk0 ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq602 rule_def_5_0 -- subsumption resolution 602,178
  have eq604 : b = sk1 ∨ b = sk0 ∨ c = sk1 ∨ c = sk0 := resolve eq603 rule_def_4_1 -- subsumption resolution 603,174
  have eq606 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 ∨ (old b b a) := resolve eq429 rule_def_6_2 -- resolution 429,185
  have eq610 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 ∨ (old b b a) := resolve eq606 rule_def_3_3 -- subsumption resolution 606,171
  have eq641 : (sP7 sk0 sk0 b) ∨ (sP5 sk0 sk0 b) ∨ (sP4 sk0 sk0 b) ∨ (sP2 sk0 sk0 b) ∨ (sP1 sk0 sk0 b) ∨ (old sk0 sk0 b) ∨ (sP6 sk0 sk0 b) ∨ c = b ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := Or.assoc8 (eq600.imp_left (fun h : b = sk1 ↦ superpose h eq270)) -- superposition 270,600, 600 into 270, unify on (0).2 in 600 and (0).3 in 270
  have eq693 : (sP7 sk0 sk0 b) ∨ (sP5 sk0 sk0 b) ∨ (sP4 sk0 sk0 b) ∨ (sP2 sk0 sk0 b) ∨ (sP1 sk0 sk0 b) ∨ (old sk0 sk0 b) ∨ (sP6 sk0 sk0 b) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq641 bc -- subsumption resolution 641,137
  have eq694 : (sP5 sk0 sk0 b) ∨ (sP4 sk0 sk0 b) ∨ (sP2 sk0 sk0 b) ∨ (sP1 sk0 sk0 b) ∨ (old sk0 sk0 b) ∨ (sP6 sk0 sk0 b) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq693 rule_def_7_1 -- subsumption resolution 693,189
  have eq695 : (sP5 sk0 sk0 b) ∨ (sP4 sk0 sk0 b) ∨ (sP2 sk0 sk0 b) ∨ (sP1 sk0 sk0 b) ∨ (old sk0 sk0 b) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq694 rule_def_6_1 -- subsumption resolution 694,184
  have eq696 : (sP4 sk0 sk0 b) ∨ (sP2 sk0 sk0 b) ∨ (sP1 sk0 sk0 b) ∨ (old sk0 sk0 b) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq695 rule_def_5_0 -- subsumption resolution 695,178
  have eq697 : (sP2 sk0 sk0 b) ∨ (sP1 sk0 sk0 b) ∨ (old sk0 sk0 b) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq696 rule_def_4_1 -- subsumption resolution 696,174
  have eq698 : (sP1 sk0 sk0 b) ∨ (old sk0 sk0 b) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq697 rule_def_2_0 -- subsumption resolution 697,163
  have eq699 : (old sk0 sk0 b) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq698 rule_def_1_1 -- subsumption resolution 698,160
  have eq829 : (old sk0 sk1 c) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ c = sk0 := Or.assoc4 (eq553.imp_left (fun h : c = sk2 ↦ superpose h eq560)) -- superposition 560,553, 553 into 560, unify on (0).2 in 553 and (0).3 in 560
  have eq830 : (old sk0 sk1 c) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 := resolve eq829 rfl -- duplicate literal removal 829
  have eq836 : c = sk1 ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq830 p4XY -- subsumption resolution 830,139
  have eq855 : (sP8 sk0 sk0 c) ∨ (sP6 sk0 sk0 c) ∨ (sP5 sk0 sk0 c) ∨ (sP4 sk0 sk0 c) ∨ (sP3 sk0 sk0 c) ∨ (sP2 sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ (old sk0 sk0 c) ∨ (sP7 sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := Or.assoc10 (eq836.imp_left (fun h : c = sk1 ↦ superpose h eq244)) -- superposition 244,836, 836 into 244, unify on (0).2 in 836 and (0).3 in 244
  have eq911 : (sP8 sk0 sk0 c) ∨ (sP6 sk0 sk0 c) ∨ (sP5 sk0 sk0 c) ∨ (sP4 sk0 sk0 c) ∨ (sP3 sk0 sk0 c) ∨ (sP2 sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ (sP7 sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq855 p4XY -- subsumption resolution 855,139
  have eq912 : (sP6 sk0 sk0 c) ∨ (sP5 sk0 sk0 c) ∨ (sP4 sk0 sk0 c) ∨ (sP3 sk0 sk0 c) ∨ (sP2 sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ (sP7 sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq911 rule_def_8_0 -- subsumption resolution 911,193
  have eq913 : (sP6 sk0 sk0 c) ∨ (sP5 sk0 sk0 c) ∨ (sP4 sk0 sk0 c) ∨ (sP3 sk0 sk0 c) ∨ (sP2 sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq912 rule_def_7_2 -- subsumption resolution 912,190
  have eq914 : (sP6 sk0 sk0 c) ∨ (sP5 sk0 sk0 c) ∨ (sP4 sk0 sk0 c) ∨ (sP2 sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq913 rule_def_3_0 -- subsumption resolution 913,168
  have eq915 : (sP6 sk0 sk0 c) ∨ (sP5 sk0 sk0 c) ∨ (sP4 sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq914 rule_def_2_1 -- subsumption resolution 914,164
  have eq916 : (sP6 sk0 sk0 c) ∨ (sP5 sk0 sk0 c) ∨ (sP4 sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq915 rule_def_1_0 -- subsumption resolution 915,159
  have eq917 : (sP6 sk0 sk0 c) ∨ (sP5 sk0 sk0 c) ∨ (sP4 sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq916 rule_def_0_1 -- subsumption resolution 916,156
  have eq918 : (sP5 sk0 sk0 c) ∨ (sP4 sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq917 rule_def_6_0 -- subsumption resolution 917,183
  have eq919 : (sP4 sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 ∨ b = sk0 := resolve eq918 rule_def_5_1 -- subsumption resolution 918,179
  have eq920 : b = sk0 ∨ a = sk0 ∨ c = sk0 := resolve eq919 rule_def_4_0 -- subsumption resolution 919,173
  have eq936 : (new b b sk1) ∨ a = sk0 ∨ c = sk0 := eq920.imp_left (fun h : b = sk0 ↦ superpose h preserve_0) -- superposition 204,920, 920 into 204, unify on (0).2 in 920 and (0).1 in 204
  have eq975 : ¬(new b c b) ∨ c = sk1 ∨ c = b ∨ a = sk0 ∨ c = sk0 := Or.assoc3 (eq920.imp_left (fun h : b = sk0 ↦ superpose h eq562)) -- superposition 562,920, 920 into 562, unify on (0).2 in 920 and (0).1 in 562
  have eq996 : ¬(new b c b) ∨ c = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq975 bc -- subsumption resolution 975,137
  have eq1205 : c = sk1 ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq590 rule_def_0_0 -- resolution 590,155
  have eq1222 : (sP8 sk0 sk0 c) ∨ (sP6 sk0 sk0 c) ∨ (sP5 sk0 sk0 c) ∨ (sP4 sk0 sk0 c) ∨ (sP3 sk0 sk0 c) ∨ (sP2 sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ (old sk0 sk0 c) ∨ (sP7 sk0 sk0 c) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := Or.assoc10 (eq1205.imp_left (fun h : c = sk1 ↦ superpose h eq244)) -- superposition 244,1205, 1205 into 244, unify on (0).2 in 1205 and (0).3 in 244
  have eq1288 : (sP8 sk0 sk0 c) ∨ (sP6 sk0 sk0 c) ∨ (sP5 sk0 sk0 c) ∨ (sP4 sk0 sk0 c) ∨ (sP3 sk0 sk0 c) ∨ (sP2 sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ (sP7 sk0 sk0 c) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq1222 p4XY -- subsumption resolution 1222,139
  have eq1289 : (sP8 sk0 sk0 c) ∨ (sP6 sk0 sk0 c) ∨ (sP5 sk0 sk0 c) ∨ (sP4 sk0 sk0 c) ∨ (sP3 sk0 sk0 c) ∨ (sP2 sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq1288 rule_def_7_1 -- subsumption resolution 1288,189
  have eq1290 : (sP8 sk0 sk0 c) ∨ (sP5 sk0 sk0 c) ∨ (sP4 sk0 sk0 c) ∨ (sP3 sk0 sk0 c) ∨ (sP2 sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq1289 rule_def_6_1 -- subsumption resolution 1289,184
  have eq1291 : (sP8 sk0 sk0 c) ∨ (sP4 sk0 sk0 c) ∨ (sP3 sk0 sk0 c) ∨ (sP2 sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq1290 rule_def_5_0 -- subsumption resolution 1290,178
  have eq1292 : (sP8 sk0 sk0 c) ∨ (sP3 sk0 sk0 c) ∨ (sP2 sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq1291 rule_def_4_1 -- subsumption resolution 1291,174
  have eq1293 : (sP8 sk0 sk0 c) ∨ (sP3 sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq1292 rule_def_2_0 -- subsumption resolution 1292,163
  have eq1294 : (sP8 sk0 sk0 c) ∨ (sP3 sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq1293 rule_def_1_1 -- subsumption resolution 1293,160
  have eq1295 : (sP3 sk0 sk0 c) ∨ (sP0 sk0 sk0 c) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq1294 rule_def_8_1 -- subsumption resolution 1294,194
  have eq1296 : (sP0 sk0 sk0 c) ∨ a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq1295 rule_def_3_1 -- subsumption resolution 1295,169
  have eq1297 : a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq1296 rule_def_0_0 -- subsumption resolution 1296,155
  have eq1371 : (new b b a) ∨ a = sk0 ∨ c = sk0 ∨ c = sk0 ∨ a = sk0 := Or.assoc3 (eq1297.imp_left (fun h : a = sk1 ↦ superpose h eq936)) -- superposition 936,1297, 1297 into 936, unify on (0).2 in 1297 and (0).3 in 936
  have eq1374 : (new b b a) ∨ a = sk0 ∨ c = sk0 := resolve eq1371 rfl -- duplicate literal removal 1371
  have eq1479 : (new b c b) ∨ c = sk0 ∨ a = sk0 := resolve eq1374 eq239 -- resolution 1374,239
  have eq2046 : (old sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 ∨ (old b b a) ∨ (old sk2 b a) := resolve eq610 rule_def_1_2 -- resolution 610,161
  have eq2056 : c = sk1 ∨ a = sk0 ∨ c = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq996 eq1479 -- resolution 996,1479
  have eq2057 : c = sk1 ∨ a = sk0 ∨ c = sk0 := resolve eq2056 rfl -- duplicate literal removal 2056
  have eq2063 : a = c ∨ a = sk0 ∨ c = sk0 ∨ c = sk0 ∨ a = sk0 := Or.assoc3 (eq1297.imp_left (fun h : a = sk1 ↦ superpose h eq2057)) -- superposition 2057,1297, 1297 into 2057, unify on (0).2 in 1297 and (0).2 in 2057
  have eq2176 : a = c ∨ a = sk0 ∨ c = sk0 := resolve eq2063 rfl -- duplicate literal removal 2063
  have eq2177 : c = sk0 ∨ a = sk0 := resolve eq2176 ac -- subsumption resolution 2176,136
  have eq2213 : (old c c sk1) ∨ a = c ∨ c = b ∨ a = sk0 := Or.assoc3 (eq2177.imp_left (fun h : c = sk0 ↦ superpose h eq308)) -- superposition 308,2177, 2177 into 308, unify on (0).2 in 2177 and (0).1 in 308
  have eq2271 : a = c ∨ c = b ∨ a = sk0 := resolve eq2213 p4YZ -- subsumption resolution 2213,141
  have eq2272 : c = b ∨ a = sk0 := resolve eq2271 ac -- subsumption resolution 2271,136
  have eq2273 : a = sk0 := resolve eq2272 bc -- subsumption resolution 2272,137
  have eq2276 : ¬(new a sk2 a) := Eq.mp (by simp only [eq2273, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_2 -- backward demodulation 206,2273
  have eq2299 : (old a a sk1) ∨ b = sk0 ∨ c = sk0 := Eq.mp (by simp only [eq2273, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq319 -- backward demodulation 319,2273
  have eq2302 : (old a a sk1) ∨ c = sk1 ∨ c = sk0 := Eq.mp (by simp only [eq2273, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq353 -- backward demodulation 353,2273
  have eq2383 : a = c ∨ ¬(new sk0 c sk0) ∨ c = sk1 := Eq.mp (by simp only [eq2273, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq562 -- backward demodulation 562,2273
  have eq2389 : a = b ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := Eq.mp (by simp only [eq2273, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq604 -- backward demodulation 604,2273
  have eq2413 : a = c ∨ (old sk0 sk0 b) ∨ a = sk1 ∨ c = sk1 := Eq.mp (by simp only [eq2273, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq699 -- backward demodulation 699,2273
  have eq2548 : (old a sk1 sk2) ∨ (old a a b) ∨ b = sk1 ∨ (old b b a) ∨ (old sk2 b a) := Eq.mp (by simp only [eq2273, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2046 -- backward demodulation 2046,2273
  have eq2623 : a = b ∨ (old a a sk1) ∨ c = sk0 := Eq.mp (by simp only [eq2273, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2299 -- forward demodulation 2299,2273
  have eq2624 : a = c ∨ a = b ∨ (old a a sk1) := Eq.mp (by simp only [eq2273, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2623 -- forward demodulation 2623,2273
  have eq2625 : (old a a sk1) ∨ a = b := resolve eq2624 ac -- subsumption resolution 2624,136
  have eq2637 : a = c ∨ (old a a sk1) ∨ c = sk1 := Eq.mp (by simp only [eq2273, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2302 -- forward demodulation 2302,2273
  have eq2638 : (old a a sk1) ∨ c = sk1 := resolve eq2637 ac -- subsumption resolution 2637,136
  have eq2867 : ¬(new sk0 c sk0) ∨ c = sk1 := resolve eq2383 ac -- subsumption resolution 2383,136
  have eq2868 : ¬(new a c a) ∨ c = sk1 := Eq.mp (by simp only [eq2273, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2867 -- forward demodulation 2867,2273
  have eq2882 : a = c ∨ a = b ∨ b = sk1 ∨ c = sk1 := Eq.mp (by simp only [eq2273, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2389 -- forward demodulation 2389,2273
  have eq2883 : b = sk1 ∨ a = b ∨ c = sk1 := resolve eq2882 ac -- subsumption resolution 2882,136
  have eq2943 : (old sk0 sk0 b) ∨ a = sk1 ∨ c = sk1 := resolve eq2413 ac -- subsumption resolution 2413,136
  have eq2944 : (old a a b) ∨ a = sk1 ∨ c = sk1 := Eq.mp (by simp only [eq2273, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2943 -- forward demodulation 2943,2273
  have eq3558 : a = sk1 ∨ c = sk1 ∨ (new a c a) := resolve eq2944 eq220 -- resolution 2944,220
  have eq3572 : c = sk1 ∨ a = sk1 := resolve eq3558 eq2868 -- subsumption resolution 3558,2868
  have eq3578 : c = b ∨ a = b ∨ a = b ∨ c = sk1 := Or.assoc2 (eq2883.imp_left (fun h : b = sk1 ↦ superpose h eq3572)) -- superposition 3572,2883, 2883 into 3572, unify on (0).2 in 2883 and (0).2 in 3572
  have eq3607 : c = b ∨ a = b ∨ c = sk1 := resolve eq3578 rfl -- duplicate literal removal 3578
  have eq3608 : c = sk1 ∨ a = b := resolve eq3607 bc -- subsumption resolution 3607,137
  have eq3654 : (old a a c) ∨ a = b ∨ a = b := Or.assoc2 (eq3608.imp_left (fun h : c = sk1 ↦ superpose h eq2625)) -- superposition 2625,3608, 3608 into 2625, unify on (0).2 in 3608 and (0).3 in 2625
  have eq3669 : (old a a c) ∨ a = b := resolve eq3654 rfl -- duplicate literal removal 3654
  have eq3706 : a = b := resolve eq3669 p4XY -- subsumption resolution 3669,139
  have eq3708 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq3706, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 138,3706
  have eq3749 : (old a a a) ∨ (old a sk1 sk2) ∨ (old a a b) ∨ b = sk1 ∨ (old sk2 b a) := Eq.mp (by simp only [eq3706, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2548 -- backward demodulation 2548,3706
  have eq3885 : (old a sk1 sk2) ∨ (old a a b) ∨ b = sk1 ∨ (old sk2 b a) := resolve eq3749 eq3708 -- subsumption resolution 3749,3708
  have eq3886 : (old a sk1 sk2) ∨ b = sk1 ∨ (old sk2 b a) := resolve eq3885 eq3708 -- subsumption resolution 3885,3708
  have eq3887 : a = sk1 ∨ (old a sk1 sk2) ∨ (old sk2 b a) := Eq.mp (by simp only [eq3706, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3886 -- forward demodulation 3886,3706
  have eq3888 : (old sk2 a a) ∨ a = sk1 ∨ (old a sk1 sk2) := Eq.mp (by simp only [eq3706, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3887 -- forward demodulation 3887,3706
  have eq3953 : c = sk1 := resolve eq3708 eq2638 -- resolution 3708,2638
  have eq3981 : a = c ∨ (old sk2 a a) ∨ (old a sk1 sk2) := Eq.mp (by simp only [eq3953, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3888 -- backward demodulation 3888,3953
  have eq4046 : (old sk2 a a) ∨ (old a sk1 sk2) := resolve eq3981 ac -- subsumption resolution 3981,136
  have eq4047 : (old a c sk2) ∨ (old sk2 a a) := Eq.mp (by simp only [eq3953, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4046 -- forward demodulation 4046,3953
  have eq4048 : (old sk2 a a) := resolve eq4047 p4XZ -- subsumption resolution 4047,140
  have eq4079 : (old a sk2 a) := resolve eq4048 old_3 -- resolution 4048,145
  have eq4099 : (new a sk2 a) := resolve eq4079 imp_new_0 -- resolution 4079,153
  subsumption eq2276 eq4099 -- subsumption resolution 4099,2276

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_6_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (prev_1 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X2 X1 X3 ∨ new X1 X3 X0)) (prev_5 : (∀ X0 X1 X2, ¬ new X0 X0 X1 ∨ ¬ new X0 X1 X2 ∨ new X0 X2 X0)) : (∀ X0 X1 X2, ¬ new X0 X0 X1 ∨ ¬ new X0 X1 X2 ∨ new X2 X0 X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq248 : (new sk0 sk2 sk0) ∨ ¬(new sk0 sk0 sk1) := resolve prev_5 preserve_1 -- resolution 206,208
  have eq250 : (new sk0 sk2 sk0) := resolve eq248 preserve_0 -- subsumption resolution 248,207
  have eq253 (X0 : G) : ¬(new X0 sk2 sk0) ∨ (new sk2 sk0 X0) := resolve eq250 prev_1 -- resolution 250,202
  have eq272 : (new sk2 sk0 sk0) := resolve eq253 eq250 -- resolution 253,250
  subsumption preserve_2 eq272 -- subsumption resolution 272,209

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_7_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (prev_1 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X2 X1 X3 ∨ new X1 X3 X0)) (prev_4 : (∀ X0 X1 X2, ¬ new X0 X0 X1 ∨ ¬ new X1 X0 X2 ∨ new X0 X1 X2)) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X1 X1 X0 ∨ ¬ new X3 X0 X1 ∨ new X0 X2 X3) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2, preserve_3⟩ := nh
  have eq257 : (new sk1 sk0 sk2) ∨ ¬(new sk1 sk1 sk0) := resolve prev_4 preserve_0 -- resolution 208,211
  have eq260 : (new sk1 sk0 sk2) := resolve eq257 preserve_1 -- subsumption resolution 257,212
  have eq262 (X0 : G) : ¬(new X0 sk0 sk1) ∨ (new sk0 sk2 X0) := resolve eq260 prev_1 -- resolution 260,205
  have eq296 : (new sk0 sk2 sk3) := resolve eq262 preserve_2 -- resolution 262,213
  subsumption preserve_3 eq296 -- subsumption resolution 296,214

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_8_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (old_1 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X2 X1 X3 ∨ old X1 X3 X0)) (prev_1 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X2 X1 X3 ∨ new X1 X3 X0)) (prev_3 : (∀ X0 X1, ¬ new X0 X1 X1 ∨ new X1 X0 X1)) (old_8 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X3 = X0)) (imp_new_1 : ∀ X Y Z, a ≠ X ∨ b ≠ Y ∨ c ≠ Z ∨ new X Y Z) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z, b ≠ X ∨ c ≠ Y ∨ ¬ old Z b a ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), b = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z b a ∨ ¬sP1 X Y Z) (imp_new_3 : ∀ X Y Z, c ≠ X ∨ b ≠ Y ∨ b ≠ Z ∨ ¬ old b b a ∨ new X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b b a ∨ ¬sP2 X Y Z) (imp_new_4 : ∀ X Y Z, b ≠ X ∨ a ≠ Y ∨ c ≠ Z ∨ ¬ old b b a ∨ new X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), b = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b b a ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), old a a b ∨ ¬sP4 X Y Z) (rule_def_5_0 : ∀ (X Y Z : G), c = X ∨ ¬sP5 X Y Z) (rule_def_5_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP5 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), old a a b ∨ ¬sP5 X Y Z) (rule_def_6_0 : ∀ (X Y Z : G), a = X ∨ ¬sP6 X Y Z) (rule_def_6_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP6 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), old b b a ∨ ¬sP6 X Y Z) (rule_def_7_0 : ∀ (X Y Z : G), a = b ∨ ¬sP7 X Y Z) (rule_def_7_1 : ∀ (X Y Z : G), c = X ∨ ¬sP7 X Y Z) (rule_def_7_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP7 X Y Z) (rule_def_7_3 : ∀ (X Y Z : G), old Z b b ∨ ¬sP7 X Y Z) (rule_def_8_0 : ∀ (X Y Z : G), b = X ∨ ¬sP8 X Y Z) (rule_def_8_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP8 X Y Z) (rule_def_8_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP8 X Y Z) (rule_def_8_3 : ∀ (X Y Z : G), old a a b ∨ ¬sP8 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X3 X1 X2 ∨ X3 = X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq216 (X0 X1 : G) : (new X0 X1 c) ∨ b ≠ X1 ∨ a ≠ X0 := resolve imp_new_1 rfl -- equality resolution 160
  have eq217 (X0 : G) : (new X0 b c) ∨ a ≠ X0 := resolve eq216 rfl -- equality resolution 216
  have eq218 : (new a b c) := resolve eq217 rfl -- equality resolution 217
  have eq219 (X0 X2 : G) : (new X0 c X2) ∨ ¬(old X2 b a) ∨ b ≠ X0 := resolve imp_new_2 rfl -- equality resolution 164
  have eq220 (X2 : G) : ¬(old X2 b a) ∨ (new b c X2) := resolve eq219 rfl -- equality resolution 219
  have eq221 (X0 X1 : G) : (new X0 X1 b) ∨ ¬(old b b a) ∨ b ≠ X1 ∨ c ≠ X0 := resolve imp_new_3 rfl -- equality resolution 168
  have eq222 (X0 : G) : (new X0 b b) ∨ ¬(old b b a) ∨ c ≠ X0 := resolve eq221 rfl -- equality resolution 221
  have eq223 : ¬(old b b a) ∨ (new c b b) := resolve eq222 rfl -- equality resolution 222
  have eq224 (X0 X1 : G) : (new X0 X1 c) ∨ ¬(old b b a) ∨ a ≠ X1 ∨ b ≠ X0 := resolve imp_new_4 rfl -- equality resolution 173
  have eq225 (X0 : G) : (new X0 a c) ∨ ¬(old b b a) ∨ b ≠ X0 := resolve eq224 rfl -- equality resolution 224
  have eq226 : ¬(old b b a) ∨ (new b a c) := resolve eq225 rfl -- equality resolution 225
  have eq242 (X0 : G) : ¬(new a b X0) ∨ c = X0 := resolve prev_0 eq218 -- resolution 205,218
  have eq247 (X0 : G) : ¬(new X0 sk1 sk3) ∨ (new sk1 sk2 X0) := resolve prev_1 preserve_1 -- resolution 206,214
  have eq261 : (sP8 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 204,213
  have eq262 : (sP8 sk3 sk1 sk2) ∨ (sP6 sk3 sk1 sk2) ∨ (sP5 sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ (sP3 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP7 sk3 sk1 sk2) := resolve new_imp preserve_1 -- resolution 204,214
  have eq281 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ c = sk2 := resolve eq261 rule_def_8_2 -- resolution 261,201
  have eq282 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ a = sk1 := resolve eq261 rule_def_8_1 -- resolution 261,200
  have eq283 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ b = sk0 := resolve eq261 rule_def_8_0 -- resolution 261,199
  have eq286 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ c = sk2 := resolve eq281 rule_def_3_2 -- subsumption resolution 281,176
  have eq287 : (sP7 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ c = sk2 := resolve eq286 rule_def_0_2 -- subsumption resolution 286,163
  have eq288 : (sP6 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ a = sk1 := resolve eq282 rule_def_5_1 -- subsumption resolution 282,185
  have eq289 : (sP7 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ a = sk1 := resolve eq288 rule_def_3_1 -- subsumption resolution 288,175
  have eq290 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ b = sk0 := resolve eq283 rule_def_3_0 -- subsumption resolution 283,174
  have eq291 : (sP7 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ b = sk0 := resolve eq290 rule_def_1_0 -- subsumption resolution 290,165
  have eq297 : (sP6 sk3 sk1 sk2) ∨ (sP5 sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ (sP3 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP7 sk3 sk1 sk2) ∨ (old a a b) := resolve eq262 rule_def_8_3 -- resolution 262,202
  have eq298 : (sP6 sk3 sk1 sk2) ∨ (sP5 sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ (sP3 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP7 sk3 sk1 sk2) ∨ c = sk2 := resolve eq262 rule_def_8_2 -- resolution 262,201
  have eq299 : (sP6 sk3 sk1 sk2) ∨ (sP5 sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ (sP3 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP7 sk3 sk1 sk2) ∨ a = sk1 := resolve eq262 rule_def_8_1 -- resolution 262,200
  have eq300 : (sP6 sk3 sk1 sk2) ∨ (sP5 sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ (sP3 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP7 sk3 sk1 sk2) ∨ b = sk3 := resolve eq262 rule_def_8_0 -- resolution 262,199
  have eq301 : (sP6 sk3 sk1 sk2) ∨ (sP5 sk3 sk1 sk2) ∨ (sP3 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP7 sk3 sk1 sk2) ∨ (old a a b) := resolve eq297 rule_def_4_3 -- subsumption resolution 297,182
  have eq302 : (sP7 sk3 sk1 sk2) ∨ (sP3 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP6 sk3 sk1 sk2) ∨ (old a a b) := resolve eq301 rule_def_5_3 -- subsumption resolution 301,187
  have eq303 : (sP6 sk3 sk1 sk2) ∨ (sP5 sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP7 sk3 sk1 sk2) ∨ c = sk2 := resolve eq298 rule_def_3_2 -- subsumption resolution 298,176
  have eq304 : (sP7 sk3 sk1 sk2) ∨ (sP5 sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP6 sk3 sk1 sk2) ∨ c = sk2 := resolve eq303 rule_def_0_2 -- subsumption resolution 303,163
  have eq305 : (sP6 sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ (sP3 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP7 sk3 sk1 sk2) ∨ a = sk1 := resolve eq299 rule_def_5_1 -- subsumption resolution 299,185
  have eq306 : (sP7 sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP6 sk3 sk1 sk2) ∨ a = sk1 := resolve eq305 rule_def_3_1 -- subsumption resolution 305,175
  have eq307 : (sP6 sk3 sk1 sk2) ∨ (sP5 sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP7 sk3 sk1 sk2) ∨ b = sk3 := resolve eq300 rule_def_3_0 -- subsumption resolution 300,174
  have eq308 : (sP7 sk3 sk1 sk2) ∨ (sP5 sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP6 sk3 sk1 sk2) ∨ b = sk3 := resolve eq307 rule_def_1_0 -- subsumption resolution 307,165
  have eq323 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk1 := resolve eq287 rule_def_7_2 -- resolution 287,196
  have eq324 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 := resolve eq287 rule_def_7_1 -- resolution 287,195
  have eq325 : (sP6 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ c = sk2 ∨ a = b := resolve eq287 rule_def_7_0 -- resolution 287,194
  have eq326 : (sP6 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk1 := resolve eq323 rule_def_2_1 -- subsumption resolution 323,170
  have eq327 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 := resolve eq324 rule_def_5_0 -- subsumption resolution 324,184
  have eq328 : (sP6 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 := resolve eq327 rule_def_2_0 -- subsumption resolution 327,169
  have eq333 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 := resolve eq289 rule_def_7_2 -- resolution 289,196
  have eq335 : (sP6 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk1 ∨ a = b := resolve eq289 rule_def_7_0 -- resolution 289,194
  have eq336 : (sP4 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 := resolve eq333 rule_def_2_1 -- subsumption resolution 333,170
  have eq337 : (sP6 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 := resolve eq336 rule_def_0_1 -- subsumption resolution 336,162
  have eq343 : (sP6 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ b = sk0 ∨ (old sk2 b b) := resolve eq291 rule_def_7_3 -- resolution 291,197
  have eq344 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 := resolve eq291 rule_def_7_2 -- resolution 291,196
  have eq345 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ b = sk0 ∨ c = sk0 := resolve eq291 rule_def_7_1 -- resolution 291,195
  have eq347 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 := resolve eq344 rule_def_2_1 -- subsumption resolution 344,170
  have eq348 : (sP6 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 := resolve eq347 rule_def_0_1 -- subsumption resolution 347,162
  have eq349 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ b = sk0 ∨ c = sk0 := resolve eq345 rule_def_5_0 -- subsumption resolution 345,184
  have eq350 : (sP6 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk0 ∨ c = sk0 := resolve eq349 rule_def_2_0 -- subsumption resolution 349,169
  have eq353 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq328 rule_def_6_1 -- resolution 328,190
  have eq355 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq353 rule_def_4_1 -- subsumption resolution 353,180
  have eq356 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq355 rule_def_1_1 -- subsumption resolution 355,166
  have eq360 : (sP5 sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP6 sk3 sk1 sk2) ∨ c = sk2 ∨ c = sk3 := resolve eq304 rule_def_7_1 -- resolution 304,195
  have eq361 : (sP6 sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP5 sk3 sk1 sk2) ∨ c = sk2 ∨ a = b := resolve eq304 rule_def_7_0 -- resolution 304,194
  have eq363 : (sP4 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP6 sk3 sk1 sk2) ∨ c = sk2 ∨ c = sk3 := resolve eq360 rule_def_5_0 -- subsumption resolution 360,184
  have eq364 : (sP6 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2 ∨ c = sk3 := resolve eq363 rule_def_2_0 -- subsumption resolution 363,169
  have eq371 (X0 : G) : ¬(old X0 sk1 sk2) ∨ c = sk0 ∨ c = sk1 ∨ sk0 = X0 ∨ c = sk2 := resolve eq356 old_8 -- resolution 356,156
  have eq375 : (sP4 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP6 sk3 sk1 sk2) ∨ a = sk1 ∨ b = sk1 := resolve eq306 rule_def_7_2 -- resolution 306,196
  have eq377 : (sP6 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ a = sk1 ∨ a = b := resolve eq306 rule_def_7_0 -- resolution 306,194
  have eq378 : (sP4 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP6 sk3 sk1 sk2) ∨ a = sk1 ∨ b = sk1 := resolve eq375 rule_def_2_1 -- subsumption resolution 375,170
  have eq379 : (sP6 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ a = sk1 ∨ b = sk1 := resolve eq378 rule_def_0_1 -- subsumption resolution 378,162
  have eq383 : (sP6 sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP5 sk3 sk1 sk2) ∨ b = sk3 ∨ (old sk2 b b) := resolve eq308 rule_def_7_3 -- resolution 308,197
  have eq384 : (sP5 sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP6 sk3 sk1 sk2) ∨ b = sk3 ∨ b = sk1 := resolve eq308 rule_def_7_2 -- resolution 308,196
  have eq387 : (sP5 sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP6 sk3 sk1 sk2) ∨ b = sk3 ∨ b = sk1 := resolve eq384 rule_def_2_1 -- subsumption resolution 384,170
  have eq388 : (sP6 sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP5 sk3 sk1 sk2) ∨ b = sk3 ∨ b = sk1 := resolve eq387 rule_def_0_1 -- subsumption resolution 387,162
  have eq403 : (sP6 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP3 sk3 sk1 sk2) ∨ (old a a b) ∨ (old sk2 b b) := resolve eq302 rule_def_7_3 -- resolution 302,197
  have eq424 : (sP4 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ (old b b a) := resolve eq337 rule_def_6_2 -- resolution 337,191
  have eq425 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 := resolve eq337 rule_def_6_1 -- resolution 337,190
  have eq426 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ a = sk0 := resolve eq337 rule_def_6_0 -- resolution 337,189
  have eq427 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 := resolve eq425 rule_def_4_1 -- subsumption resolution 425,180
  have eq428 : (old sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 := resolve eq427 rule_def_1_1 -- subsumption resolution 427,166
  have eq429 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ a = sk0 := resolve eq426 rule_def_4_0 -- subsumption resolution 426,179
  have eq438 (X0 : G) : ¬(old X0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ sk0 = X0 ∨ a = sk1 := resolve eq428 old_8 -- resolution 428,156
  have eq444 : (sP5 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 ∨ (old b b a) := resolve eq348 rule_def_6_2 -- resolution 348,191
  have eq445 : (sP4 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 ∨ c = sk1 := resolve eq348 rule_def_6_1 -- resolution 348,190
  have eq447 : (sP5 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 ∨ c = sk1 := resolve eq445 rule_def_4_1 -- subsumption resolution 445,180
  have eq477 : (sP1 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ c = sk2 ∨ c = sk3 ∨ c = sk1 := resolve eq364 rule_def_6_1 -- resolution 364,190
  have eq479 : (sP1 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ c = sk2 ∨ c = sk3 ∨ c = sk1 := resolve eq477 rule_def_4_1 -- subsumption resolution 477,180
  have eq480 : (old sk3 sk1 sk2) ∨ c = sk2 ∨ c = sk3 ∨ c = sk1 := resolve eq479 rule_def_1_1 -- subsumption resolution 479,166
  have eq482 : c = sk2 ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 ∨ c = sk1 ∨ sk0 = sk3 ∨ c = sk2 := resolve eq480 eq371 -- resolution 480,371
  have eq489 (X0 : G) : ¬(old X0 sk1 sk2) ∨ c = sk3 ∨ c = sk1 ∨ sk3 = X0 ∨ c = sk2 := resolve eq480 old_8 -- resolution 480,156
  have eq492 : c = sk2 ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 ∨ sk0 = sk3 := resolve eq482 rfl -- duplicate literal removal 482
  have eq493 : c = sk3 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq492 preserve_2 -- subsumption resolution 492,215
  have eq496 : (sP1 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 := resolve eq379 rule_def_6_1 -- resolution 379,190
  have eq497 : (sP1 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ a = sk3 := resolve eq379 rule_def_6_0 -- resolution 379,189
  have eq498 : (sP1 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 := resolve eq496 rule_def_4_1 -- subsumption resolution 496,180
  have eq499 : (old sk3 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 := resolve eq498 rule_def_1_1 -- subsumption resolution 498,166
  have eq500 : (sP1 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ a = sk3 := resolve eq497 rule_def_4_0 -- subsumption resolution 497,179
  have eq513 : (sP6 c sk1 sk2) ∨ (sP1 c sk1 sk2) ∨ (old c sk1 sk2) ∨ (sP4 c sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := Or.assoc6 (eq493.imp_left (fun h : c = sk3 ↦ superpose h eq379)) -- superposition 379,493, 493 into 379, unify on (0).2 in 493 and (0).1 in 379
  have eq532 : (sP6 c sk1 sk2) ∨ (sP1 c sk1 sk2) ∨ (sP4 c sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq513 p4YZ -- subsumption resolution 513,147
  have eq533 : (sP1 c sk1 sk2) ∨ (sP4 c sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq532 rule_def_6_1 -- subsumption resolution 532,190
  have eq534 : (sP1 c sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq533 rule_def_4_1 -- subsumption resolution 533,180
  have eq535 : c = sk2 ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq534 rule_def_1_1 -- subsumption resolution 534,166
  have eq537 : (sP5 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ b = sk3 ∨ b = sk1 ∨ (old b b a) := resolve eq388 rule_def_6_2 -- resolution 388,191
  have eq538 : (sP4 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP5 sk3 sk1 sk2) ∨ b = sk3 ∨ b = sk1 ∨ c = sk1 := resolve eq388 rule_def_6_1 -- resolution 388,190
  have eq540 : (sP6 c sk1 sk2) ∨ (sP4 c sk1 sk2) ∨ (old c sk1 sk2) ∨ (sP5 c sk1 sk2) ∨ c = b ∨ b = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := Or.assoc6 (eq493.imp_left (fun h : c = sk3 ↦ superpose h eq388)) -- superposition 388,493, 493 into 388, unify on (0).2 in 493 and (0).1 in 388
  have eq541 : (sP5 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ b = sk3 ∨ b = sk1 ∨ c = sk1 := resolve eq538 rule_def_4_1 -- subsumption resolution 538,180
  have eq543 : (sP6 c sk1 sk2) ∨ (sP4 c sk1 sk2) ∨ (sP5 c sk1 sk2) ∨ c = b ∨ b = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq540 p4YZ -- subsumption resolution 540,147
  have eq544 : (sP6 c sk1 sk2) ∨ (sP4 c sk1 sk2) ∨ (sP5 c sk1 sk2) ∨ b = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq543 bc -- subsumption resolution 543,143
  have eq545 : (sP4 c sk1 sk2) ∨ (sP5 c sk1 sk2) ∨ b = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq544 rule_def_6_1 -- subsumption resolution 544,190
  have eq546 : (sP5 c sk1 sk2) ∨ b = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq545 rule_def_4_1 -- subsumption resolution 545,180
  have eq605 : (sP8 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := Or.assoc10 (eq535.imp_left (fun h : c = sk2 ↦ superpose h eq261)) -- superposition 261,535, 535 into 261, unify on (0).2 in 535 and (0).3 in 261
  have eq637 : (sP8 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP7 sk0 sk1 c) ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq605 p4XY -- subsumption resolution 605,145
  have eq638 : (sP8 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq637 rule_def_7_1 -- subsumption resolution 637,195
  have eq639 : (sP8 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq638 rule_def_6_1 -- subsumption resolution 638,190
  have eq640 : (sP8 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq639 rule_def_5_0 -- subsumption resolution 639,184
  have eq641 : (sP8 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq640 rule_def_4_1 -- subsumption resolution 640,180
  have eq642 : (sP8 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq641 rule_def_2_0 -- subsumption resolution 641,169
  have eq643 : (sP8 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq642 rule_def_1_1 -- subsumption resolution 642,166
  have eq644 : (sP3 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq643 rule_def_8_1 -- subsumption resolution 643,200
  have eq645 : (sP0 sk0 sk1 c) ∨ b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq644 rule_def_3_1 -- subsumption resolution 644,175
  have eq646 : b = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq645 rule_def_0_1 -- subsumption resolution 645,162
  have eq678 : (old sk0 b sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = b ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := Or.assoc4 (eq646.imp_left (fun h : b = sk1 ↦ superpose h eq356)) -- superposition 356,646, 646 into 356, unify on (0).2 in 646 and (0).2 in 356
  have eq689 : a ≠ b ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq646 trans_resol -- equality factoring 646
  have eq697 : (old sk0 b sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = b ∨ a = sk1 ∨ c = sk1 := resolve eq678 rfl -- duplicate literal removal 678
  have eq714 : (old sk0 b sk2) ∨ c = sk2 ∨ c = sk0 ∨ a = sk1 ∨ c = sk1 := resolve eq697 bc -- subsumption resolution 697,143
  have eq720 : (sP4 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk1 ∨ c = sk1 := resolve eq326 rule_def_6_1 -- resolution 326,190
  have eq722 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk1 ∨ c = sk1 := resolve eq720 rule_def_4_1 -- subsumption resolution 720,180
  have eq723 : (sP5 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk1 ∨ c = sk1 := resolve eq722 rule_def_1_1 -- subsumption resolution 722,166
  have eq783 : b = sk1 ∨ c = sk1 ∨ sk0 = sk3 ∨ a = sk1 ∨ a = sk1 ∨ b = sk1 ∨ c = sk1 := resolve eq438 eq499 -- resolution 438,499
  have eq788 : b = sk1 ∨ c = sk1 ∨ sk0 = sk3 ∨ a = sk1 := resolve eq783 rfl -- duplicate literal removal 783
  have eq792 : b = sk1 ∨ c = sk1 ∨ a = sk1 := resolve eq788 preserve_2 -- subsumption resolution 788,215
  have eq841 : (old sk3 b sk2) ∨ c = sk2 ∨ c = sk3 ∨ c = b ∨ c = sk1 ∨ a = sk1 := Or.assoc4 (eq792.imp_left (fun h : b = sk1 ↦ superpose h eq480)) -- superposition 480,792, 792 into 480, unify on (0).2 in 792 and (0).2 in 480
  have eq845 : a ≠ b ∨ c = sk1 ∨ a = sk1 := resolve eq792 trans_resol -- equality factoring 792
  have eq848 : (old sk3 b sk2) ∨ c = sk2 ∨ c = sk3 ∨ c = sk1 ∨ a = sk1 := resolve eq841 bc -- subsumption resolution 841,143
  have eq861 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ c = sk2 ∨ a = b ∨ c = sk1 := resolve eq325 rule_def_6_1 -- resolution 325,190
  have eq866 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ c = sk2 ∨ a = b ∨ c = sk1 := resolve eq861 rule_def_4_1 -- subsumption resolution 861,180
  have eq867 : (sP5 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ c = sk2 ∨ a = b ∨ c = sk1 := resolve eq866 rule_def_1_1 -- subsumption resolution 866,166
  have eq881 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk1 ∨ a = b ∨ c = sk1 := resolve eq335 rule_def_6_1 -- resolution 335,190
  have eq882 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk1 ∨ a = b ∨ a = sk0 := resolve eq335 rule_def_6_0 -- resolution 335,189
  have eq890 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ a = b ∨ c = sk1 := resolve eq881 rule_def_4_1 -- subsumption resolution 881,180
  have eq891 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ a = b ∨ c = sk1 := resolve eq890 rule_def_1_1 -- subsumption resolution 890,166
  have eq892 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ c = sk1 := resolve eq891 eq845 -- subsumption resolution 891,845
  have eq893 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ a = b ∨ a = sk0 := resolve eq882 rule_def_4_0 -- subsumption resolution 882,179
  have eq894 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ a = b ∨ a = sk0 := resolve eq893 rule_def_0_0 -- subsumption resolution 893,161
  have eq924 : (sP4 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP5 sk3 sk1 sk2) ∨ c = sk2 ∨ a = b ∨ c = sk1 := resolve eq361 rule_def_6_1 -- resolution 361,190
  have eq931 : (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP5 sk3 sk1 sk2) ∨ c = sk2 ∨ a = b ∨ c = sk1 := resolve eq924 rule_def_4_1 -- subsumption resolution 924,180
  have eq932 : (sP5 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ c = sk2 ∨ a = b ∨ c = sk1 := resolve eq931 rule_def_1_1 -- subsumption resolution 931,166
  have eq948 : (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ a = sk1 ∨ a = b ∨ a = sk3 := resolve eq377 rule_def_6_0 -- resolution 377,189
  have eq949 : (sP6 c sk1 sk2) ∨ (sP2 c sk1 sk2) ∨ (sP1 c sk1 sk2) ∨ (sP0 c sk1 sk2) ∨ (old c sk1 sk2) ∨ (sP4 c sk1 sk2) ∨ a = sk1 ∨ a = b ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := Or.assoc8 (eq493.imp_left (fun h : c = sk3 ↦ superpose h eq377)) -- superposition 377,493, 493 into 377, unify on (0).2 in 493 and (0).1 in 377
  have eq960 : (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ a = sk1 ∨ a = b ∨ a = sk3 := resolve eq948 rule_def_4_0 -- subsumption resolution 948,179
  have eq961 : (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ a = sk1 ∨ a = b ∨ a = sk3 := resolve eq960 rule_def_0_0 -- subsumption resolution 960,161
  have eq962 : (sP6 c sk1 sk2) ∨ (sP2 c sk1 sk2) ∨ (sP1 c sk1 sk2) ∨ (sP0 c sk1 sk2) ∨ (sP4 c sk1 sk2) ∨ a = sk1 ∨ a = b ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq949 p4YZ -- subsumption resolution 949,147
  have eq963 : (sP6 c sk1 sk2) ∨ (sP2 c sk1 sk2) ∨ (sP1 c sk1 sk2) ∨ (sP0 c sk1 sk2) ∨ (sP4 c sk1 sk2) ∨ a = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq962 eq689 -- subsumption resolution 962,689
  have eq964 : (sP2 c sk1 sk2) ∨ (sP1 c sk1 sk2) ∨ (sP0 c sk1 sk2) ∨ (sP4 c sk1 sk2) ∨ a = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq963 rule_def_6_1 -- subsumption resolution 963,190
  have eq965 : (sP2 c sk1 sk2) ∨ (sP1 c sk1 sk2) ∨ (sP0 c sk1 sk2) ∨ a = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq964 rule_def_4_1 -- subsumption resolution 964,180
  have eq966 : (sP2 c sk1 sk2) ∨ (sP0 c sk1 sk2) ∨ a = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq965 rule_def_1_1 -- subsumption resolution 965,166
  have eq967 : (sP2 c sk1 sk2) ∨ a = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq966 rule_def_0_2 -- subsumption resolution 966,163
  have eq1009 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ b = sk0 ∨ (old sk2 b b) ∨ a = sk0 := resolve eq343 rule_def_6_0 -- resolution 343,189
  have eq1015 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ b = sk0 ∨ (old sk2 b b) ∨ a = sk0 := resolve eq1009 rule_def_4_0 -- subsumption resolution 1009,179
  have eq1016 : (sP5 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ b = sk0 ∨ (old sk2 b b) ∨ a = sk0 := resolve eq1015 rule_def_0_0 -- subsumption resolution 1015,161
  have eq1138 : (sP2 sk3 sk1 sk2) ∨ (sP1 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP3 sk3 sk1 sk2) ∨ (old a a b) ∨ (old sk2 b b) ∨ (old b b a) := resolve eq403 rule_def_6_2 -- resolution 403,191
  have eq1145 : (sP1 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP3 sk3 sk1 sk2) ∨ (old a a b) ∨ (old sk2 b b) ∨ (old b b a) := resolve eq1138 rule_def_2_3 -- subsumption resolution 1138,172
  have eq1146 : (sP1 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (old a a b) ∨ (old sk2 b b) ∨ (old b b a) := resolve eq1145 rule_def_3_3 -- subsumption resolution 1145,177
  have eq1172 : (old sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ a = sk0 ∨ b = sk0 := resolve eq429 rule_def_1_0 -- resolution 429,165
  have eq1183 : (old sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 ∨ c = sk1 ∨ a = sk2 := resolve eq447 rule_def_5_2 -- resolution 447,186
  have eq1266 : (old sk3 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ a = sk3 ∨ (old sk2 b a) := resolve eq500 rule_def_1_2 -- resolution 500,167
  have eq1268 : (old sk3 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ a = sk3 ∨ b = sk3 := resolve eq500 rule_def_1_0 -- resolution 500,165
  have eq1303 : (old sk3 sk1 sk2) ∨ b = sk3 ∨ b = sk1 ∨ c = sk1 ∨ a = sk2 := resolve eq541 rule_def_5_2 -- resolution 541,186
  have eq1408 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk1 ∨ c = sk1 ∨ a = sk2 := resolve eq723 rule_def_5_2 -- resolution 723,186
  have eq1429 : (old c sk1 sk2) ∨ c = b ∨ b = sk1 ∨ c = sk1 ∨ a = sk2 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := Or.assoc5 (eq493.imp_left (fun h : c = sk3 ↦ superpose h eq1303)) -- superposition 1303,493, 493 into 1303, unify on (0).2 in 493 and (0).1 in 1303
  have eq1432 : (old c sk1 sk2) ∨ c = b ∨ b = sk1 ∨ c = sk1 ∨ a = sk2 ∨ c = sk2 ∨ c = sk0 := resolve eq1429 rfl -- duplicate literal removal 1429
  have eq1443 : c = b ∨ b = sk1 ∨ c = sk1 ∨ a = sk2 ∨ c = sk2 ∨ c = sk0 := resolve eq1432 p4YZ -- subsumption resolution 1432,147
  have eq1444 : c = sk2 ∨ c = sk1 ∨ a = sk2 ∨ b = sk1 ∨ c = sk0 := resolve eq1443 bc -- subsumption resolution 1443,143
  have eq1463 : (sP7 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ b = sk0 ∨ c = sk1 ∨ a = sk2 ∨ b = sk1 ∨ c = sk0 := Or.assoc8 (eq1444.imp_left (fun h : c = sk2 ↦ superpose h eq291)) -- superposition 291,1444, 1444 into 291, unify on (0).2 in 1444 and (0).3 in 291
  have eq1517 : (old sk3 sk1 c) ∨ b = sk3 ∨ b = sk1 ∨ c = sk1 ∨ a = c ∨ c = sk1 ∨ a = sk2 ∨ b = sk1 ∨ c = sk0 := Or.assoc5 (eq1444.imp_left (fun h : c = sk2 ↦ superpose h eq1303)) -- superposition 1303,1444, 1444 into 1303, unify on (0).2 in 1444 and (0).3 in 1303
  have eq1519 : (old sk3 sk1 c) ∨ b = sk3 ∨ b = sk1 ∨ c = sk1 ∨ a = c ∨ a = sk2 ∨ c = sk0 := resolve eq1517 rfl -- duplicate literal removal 1517
  have eq1574 : (sP7 sk0 sk1 c) ∨ (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ b = sk0 ∨ c = sk1 ∨ a = sk2 ∨ b = sk1 ∨ c = sk0 := resolve eq1463 p4XY -- subsumption resolution 1463,145
  have eq1575 : (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP6 sk0 sk1 c) ∨ b = sk0 ∨ c = sk1 ∨ a = sk2 ∨ b = sk1 ∨ c = sk0 := resolve eq1574 rule_def_7_1 -- subsumption resolution 1574,195
  have eq1576 : (sP5 sk0 sk1 c) ∨ (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk0 ∨ c = sk1 ∨ a = sk2 ∨ b = sk1 ∨ c = sk0 := resolve eq1575 rule_def_6_1 -- subsumption resolution 1575,190
  have eq1577 : (sP4 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk0 ∨ c = sk1 ∨ a = sk2 ∨ b = sk1 ∨ c = sk0 := resolve eq1576 rule_def_5_0 -- subsumption resolution 1576,184
  have eq1578 : (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ b = sk0 ∨ c = sk1 ∨ a = sk2 ∨ b = sk1 ∨ c = sk0 := resolve eq1577 rule_def_4_1 -- subsumption resolution 1577,180
  have eq1579 : (sP0 sk0 sk1 c) ∨ b = sk0 ∨ c = sk1 ∨ a = sk2 ∨ b = sk1 ∨ c = sk0 := resolve eq1578 rule_def_2_0 -- subsumption resolution 1578,169
  have eq1580 : a = sk2 ∨ c = sk1 ∨ b = sk0 ∨ b = sk1 ∨ c = sk0 := resolve eq1579 rule_def_0_1 -- subsumption resolution 1579,162
  have eq1597 : b = sk3 ∨ b = sk1 ∨ c = sk1 ∨ a = c ∨ a = sk2 ∨ c = sk0 := resolve eq1519 p4XY -- subsumption resolution 1519,145
  have eq1598 : b = sk3 ∨ b = sk1 ∨ c = sk1 ∨ a = sk2 ∨ c = sk0 := resolve eq1597 ac -- subsumption resolution 1597,142
  have eq1785 : b ≠ sk0 ∨ b = sk1 ∨ c = sk1 ∨ a = sk2 ∨ c = sk0 := eq1598.imp_left (fun h : b = sk3 ↦ superpose h preserve_2) -- superposition 215,1598, 1598 into 215, unify on (0).2 in 1598 and (0).2 in 215
  have eq1840 : a = sk2 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 := resolve eq1785 eq1580 -- subsumption resolution 1785,1580
  have eq2108 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ c = sk1 ∨ b = sk2 := resolve eq892 rule_def_2_2 -- resolution 892,171
  have eq2252 : c = sk2 ∨ b = sk1 ∨ c = sk1 ∨ a = sk2 ∨ c = sk3 ∨ c = sk1 ∨ sk0 = sk3 ∨ c = sk2 := resolve eq1408 eq489 -- resolution 1408,489
  have eq2267 : c = sk2 ∨ b = sk1 ∨ c = sk1 ∨ a = sk2 ∨ c = sk3 ∨ sk0 = sk3 := resolve eq2252 rfl -- duplicate literal removal 2252
  have eq2272 : c = sk3 ∨ b = sk1 ∨ c = sk1 ∨ a = sk2 ∨ c = sk2 := resolve eq2267 preserve_2 -- subsumption resolution 2267,215
  have eq2280 : c ≠ sk0 ∨ b = sk1 ∨ c = sk1 ∨ a = sk2 ∨ c = sk2 := eq2272.imp_left (fun h : c = sk3 ↦ superpose h preserve_2) -- superposition 215,2272, 2272 into 215, unify on (0).2 in 2272 and (0).2 in 215
  have eq2353 : c = sk2 ∨ c = sk1 ∨ a = sk2 ∨ b = sk1 := resolve eq2280 eq1840 -- subsumption resolution 2280,1840
  have eq2429 : (old sk0 sk1 c) ∨ b = sk0 ∨ b = sk1 ∨ c = sk1 ∨ a = c ∨ c = sk1 ∨ a = sk2 ∨ b = sk1 := Or.assoc5 (eq2353.imp_left (fun h : c = sk2 ↦ superpose h eq1183)) -- superposition 1183,2353, 2353 into 1183, unify on (0).2 in 2353 and (0).3 in 1183
  have eq2433 : (old sk3 sk1 c) ∨ b = sk3 ∨ b = sk1 ∨ c = sk1 ∨ a = c ∨ c = sk1 ∨ a = sk2 ∨ b = sk1 := Or.assoc5 (eq2353.imp_left (fun h : c = sk2 ↦ superpose h eq1303)) -- superposition 1303,2353, 2353 into 1303, unify on (0).2 in 2353 and (0).3 in 1303
  have eq2443 : (old sk3 sk1 c) ∨ b = sk3 ∨ b = sk1 ∨ c = sk1 ∨ a = c ∨ a = sk2 := resolve eq2433 rfl -- duplicate literal removal 2433
  have eq2447 : (old sk0 sk1 c) ∨ b = sk0 ∨ b = sk1 ∨ c = sk1 ∨ a = c ∨ a = sk2 := resolve eq2429 rfl -- duplicate literal removal 2429
  have eq2523 : b = sk0 ∨ b = sk1 ∨ c = sk1 ∨ a = c ∨ a = sk2 := resolve eq2447 p4XY -- subsumption resolution 2447,145
  have eq2524 : a = sk2 ∨ b = sk1 ∨ c = sk1 ∨ b = sk0 := resolve eq2523 ac -- subsumption resolution 2523,142
  have eq2525 : b = sk3 ∨ b = sk1 ∨ c = sk1 ∨ a = c ∨ a = sk2 := resolve eq2443 p4XY -- subsumption resolution 2443,145
  have eq2526 : b = sk3 ∨ b = sk1 ∨ c = sk1 ∨ a = sk2 := resolve eq2525 ac -- subsumption resolution 2525,142
  have eq2732 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ c = sk2 ∨ a = b ∨ c = sk1 ∨ a = sk1 := resolve eq867 rule_def_5_1 -- resolution 867,185
  have eq2742 : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ a = sk1 := resolve eq2732 eq845 -- subsumption resolution 2732,845
  have eq2748 : b ≠ sk0 ∨ b = sk1 ∨ c = sk1 ∨ a = sk2 := eq2526.imp_left (fun h : b = sk3 ↦ superpose h preserve_2) -- superposition 215,2526, 2526 into 215, unify on (0).2 in 2526 and (0).2 in 215
  have eq2819 : a = sk2 ∨ c = sk1 ∨ b = sk1 := resolve eq2748 eq2524 -- subsumption resolution 2748,2524
  have eq2821 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ a = b ∨ a = sk0 ∨ b = sk2 := resolve eq894 rule_def_2_2 -- resolution 894,171
  have eq2839 : (new sk0 sk1 a) ∨ c = sk1 ∨ b = sk1 := eq2819.imp_left (fun h : a = sk2 ↦ superpose h preserve_0) -- superposition 213,2819, 2819 into 213, unify on (0).2 in 2819 and (0).3 in 213
  have eq2846 : (sP7 sk0 sk1 a) ∨ (sP5 sk0 sk1 a) ∨ (sP4 sk0 sk1 a) ∨ (sP2 sk0 sk1 a) ∨ (sP1 sk0 sk1 a) ∨ (old sk0 sk1 a) ∨ (sP6 sk0 sk1 a) ∨ a = c ∨ c = sk1 ∨ b = sk1 := Or.assoc8 (eq2819.imp_left (fun h : a = sk2 ↦ superpose h eq287)) -- superposition 287,2819, 2819 into 287, unify on (0).2 in 2819 and (0).3 in 287
  have eq2850 : (sP7 sk3 sk1 a) ∨ (sP5 sk3 sk1 a) ∨ (sP4 sk3 sk1 a) ∨ (sP2 sk3 sk1 a) ∨ (sP1 sk3 sk1 a) ∨ (old sk3 sk1 a) ∨ (sP6 sk3 sk1 a) ∨ a = c ∨ c = sk1 ∨ b = sk1 := Or.assoc8 (eq2819.imp_left (fun h : a = sk2 ↦ superpose h eq304)) -- superposition 304,2819, 2819 into 304, unify on (0).2 in 2819 and (0).3 in 304
  have eq2899 (X0 : G) : ¬(old X0 sk1 a) ∨ c = sk3 ∨ c = sk1 ∨ sk3 = X0 ∨ a = c ∨ c = sk1 ∨ b = sk1 := Or.assoc5 (eq2819.imp_left (fun h : a = sk2 ↦ superpose h eq489)) -- superposition 489,2819, 2819 into 489, unify on (0).2 in 2819 and (0).3 in 489
  have eq2963 (X0 : G) : ¬(old X0 sk1 a) ∨ c = sk3 ∨ c = sk1 ∨ sk3 = X0 ∨ a = c ∨ b = sk1 := resolve eq2899 rfl -- duplicate literal removal 2899
  have eq3001 : (sP7 sk0 sk1 a) ∨ (sP5 sk0 sk1 a) ∨ (sP4 sk0 sk1 a) ∨ (sP2 sk0 sk1 a) ∨ (sP1 sk0 sk1 a) ∨ (old sk0 sk1 a) ∨ (sP6 sk0 sk1 a) ∨ c = sk1 ∨ b = sk1 := resolve eq2846 ac -- subsumption resolution 2846,142
  have eq3002 : (sP5 sk0 sk1 a) ∨ (sP4 sk0 sk1 a) ∨ (sP2 sk0 sk1 a) ∨ (sP1 sk0 sk1 a) ∨ (old sk0 sk1 a) ∨ (sP6 sk0 sk1 a) ∨ c = sk1 ∨ b = sk1 := resolve eq3001 rule_def_7_2 -- subsumption resolution 3001,196
  have eq3003 : (sP5 sk0 sk1 a) ∨ (sP4 sk0 sk1 a) ∨ (sP1 sk0 sk1 a) ∨ (old sk0 sk1 a) ∨ (sP6 sk0 sk1 a) ∨ c = sk1 ∨ b = sk1 := resolve eq3002 rule_def_2_1 -- subsumption resolution 3002,170
  have eq3004 : (sP5 sk0 sk1 a) ∨ (sP4 sk0 sk1 a) ∨ (sP1 sk0 sk1 a) ∨ (old sk0 sk1 a) ∨ c = sk1 ∨ b = sk1 := resolve eq3003 rule_def_6_1 -- subsumption resolution 3003,190
  have eq3005 : (sP5 sk0 sk1 a) ∨ (sP1 sk0 sk1 a) ∨ (old sk0 sk1 a) ∨ c = sk1 ∨ b = sk1 := resolve eq3004 rule_def_4_1 -- subsumption resolution 3004,180
  have eq3006 : (sP5 sk0 sk1 a) ∨ (old sk0 sk1 a) ∨ c = sk1 ∨ b = sk1 := resolve eq3005 rule_def_1_1 -- subsumption resolution 3005,166
  have eq3012 : (sP7 sk3 sk1 a) ∨ (sP5 sk3 sk1 a) ∨ (sP4 sk3 sk1 a) ∨ (sP2 sk3 sk1 a) ∨ (sP1 sk3 sk1 a) ∨ (old sk3 sk1 a) ∨ (sP6 sk3 sk1 a) ∨ c = sk1 ∨ b = sk1 := resolve eq2850 ac -- subsumption resolution 2850,142
  have eq3013 : (sP5 sk3 sk1 a) ∨ (sP4 sk3 sk1 a) ∨ (sP2 sk3 sk1 a) ∨ (sP1 sk3 sk1 a) ∨ (old sk3 sk1 a) ∨ (sP6 sk3 sk1 a) ∨ c = sk1 ∨ b = sk1 := resolve eq3012 rule_def_7_2 -- subsumption resolution 3012,196
  have eq3014 : (sP5 sk3 sk1 a) ∨ (sP4 sk3 sk1 a) ∨ (sP1 sk3 sk1 a) ∨ (old sk3 sk1 a) ∨ (sP6 sk3 sk1 a) ∨ c = sk1 ∨ b = sk1 := resolve eq3013 rule_def_2_1 -- subsumption resolution 3013,170
  have eq3015 : (sP5 sk3 sk1 a) ∨ (sP4 sk3 sk1 a) ∨ (sP1 sk3 sk1 a) ∨ (old sk3 sk1 a) ∨ c = sk1 ∨ b = sk1 := resolve eq3014 rule_def_6_1 -- subsumption resolution 3014,190
  have eq3016 : (sP5 sk3 sk1 a) ∨ (sP1 sk3 sk1 a) ∨ (old sk3 sk1 a) ∨ c = sk1 ∨ b = sk1 := resolve eq3015 rule_def_4_1 -- subsumption resolution 3015,180
  have eq3017 : (sP5 sk3 sk1 a) ∨ (old sk3 sk1 a) ∨ c = sk1 ∨ b = sk1 := resolve eq3016 rule_def_1_1 -- subsumption resolution 3016,166
  have eq3022 (X0 : G) : ¬(old X0 sk1 a) ∨ c = sk3 ∨ c = sk1 ∨ sk3 = X0 ∨ b = sk1 := resolve eq2963 ac -- subsumption resolution 2963,142
  have eq3051 : (old sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ c = sk2 ∨ a = b ∨ c = sk1 ∨ a = sk1 := resolve eq932 rule_def_5_1 -- resolution 932,185
  have eq3071 : (sP2 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ a = sk1 := resolve eq3051 eq845 -- subsumption resolution 3051,845
  have eq3091 : (sP1 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ a = sk1 ∨ a = b ∨ a = sk3 ∨ b = sk2 := resolve eq961 rule_def_2_2 -- resolution 961,171
  have eq3235 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ (old b b a) ∨ a = sk2 := resolve eq424 rule_def_4_2 -- resolution 424,181
  have eq3301 : (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 ∨ (old b b a) ∨ a = sk2 := resolve eq444 rule_def_5_2 -- resolution 444,186
  have eq3318 : (old sk0 sk1 sk2) ∨ b = sk0 ∨ b = sk1 ∨ (old b b a) ∨ a = sk2 := resolve eq3301 rule_def_4_2 -- subsumption resolution 3301,181
  have eq3355 : (old sk0 sk1 a) ∨ c = sk1 ∨ b = sk1 ∨ (old a a b) := resolve eq3006 rule_def_5_3 -- resolution 3006,187
  have eq3378 : (old sk3 sk1 a) ∨ c = sk1 ∨ b = sk1 ∨ (old a a b) := resolve eq3017 rule_def_5_3 -- resolution 3017,187
  have eq3497 : (old sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ b = sk3 ∨ b = sk1 ∨ (old b b a) ∨ a = sk2 := resolve eq537 rule_def_5_2 -- resolution 537,186
  have eq3517 : (old sk3 sk1 sk2) ∨ b = sk3 ∨ b = sk1 ∨ (old b b a) ∨ a = sk2 := resolve eq3497 rule_def_4_2 -- subsumption resolution 3497,181
  have eq3595 (X0 : G) : ¬(old X0 sk1 a) ∨ b = sk1 ∨ (old a a b) ∨ sk0 = X0 ∨ c = sk1 := resolve eq3355 old_8 -- resolution 3355,156
  have eq4001 : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk0 ∨ (old sk2 b b) ∨ a = sk0 ∨ (old a a b) := resolve eq1016 rule_def_5_3 -- resolution 1016,187
  have eq4052 : (sP5 c sk1 a) ∨ b = sk1 ∨ a = c ∨ c = sk1 ∨ c = sk0 ∨ c = sk1 ∨ b = sk1 ∨ c = sk0 := Or.assoc5 (eq1840.imp_left (fun h : a = sk2 ↦ superpose h eq546)) -- superposition 546,1840, 1840 into 546, unify on (0).2 in 1840 and (0).3 in 546
  have eq4057 : (sP5 c sk1 a) ∨ b = sk1 ∨ a = c ∨ c = sk1 ∨ c = sk0 := resolve eq4052 rfl -- duplicate literal removal 4052
  have eq4060 : (sP5 c sk1 a) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq4057 ac -- subsumption resolution 4057,142
  have eq4080 : (old a a b) ∨ c = sk1 ∨ c = sk0 ∨ b = sk1 := resolve eq4060 rule_def_5_3 -- resolution 4060,187
  have eq4104 (X0 : G) : c = sk1 ∨ c = sk0 ∨ b = sk1 ∨ (old a b X0) ∨ ¬(old X0 a a) := resolve eq4080 old_1 -- resolution 4080,149
  have eq4112 (X0 : G) : ¬(old X0 a a) ∨ c = sk0 ∨ b = sk1 ∨ c = sk1 := resolve eq4104 p3 -- subsumption resolution 4104,144
  have eq4314 : (sP1 c sk1 sk2) ∨ (sP0 c sk1 sk2) ∨ (old c sk1 sk2) ∨ (old a a b) ∨ (old sk2 b b) ∨ (old b b a) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := Or.assoc6 (eq493.imp_left (fun h : c = sk3 ↦ superpose h eq1146)) -- superposition 1146,493, 493 into 1146, unify on (0).2 in 493 and (0).1 in 1146
  have eq4324 : (sP1 c sk1 sk2) ∨ (sP0 c sk1 sk2) ∨ (old a a b) ∨ (old sk2 b b) ∨ (old b b a) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq4314 p4YZ -- subsumption resolution 4314,147
  have eq4325 : (sP0 c sk1 sk2) ∨ (old a a b) ∨ (old sk2 b b) ∨ (old b b a) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq4324 rule_def_1_1 -- subsumption resolution 4324,166
  have eq4326 : (old sk2 b b) ∨ (old a a b) ∨ (old b b a) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq4325 rule_def_0_2 -- subsumption resolution 4325,163
  have eq4327 : (old b b a) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 := resolve eq967 rule_def_2_3 -- resolution 967,172
  have eq4328 : b = sk2 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 := resolve eq967 rule_def_2_2 -- resolution 967,171
  have eq4988 : (new b a c) ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 ∨ c = sk2 := resolve eq4327 eq226 -- resolution 4327,226
  have eq5118 : (old sk0 b b) ∨ c = b ∨ c = sk0 ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 ∨ a = sk1 := Or.assoc5 (eq4328.imp_left (fun h : b = sk2 ↦ superpose h eq714)) -- superposition 714,4328, 4328 into 714, unify on (0).2 in 4328 and (0).3 in 714
  have eq5119 : (old sk0 b b) ∨ c = b ∨ c = sk0 ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 := resolve eq5118 rfl -- duplicate literal removal 5118
  have eq5124 : (old sk0 b b) ∨ c = sk0 ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 := resolve eq5119 bc -- subsumption resolution 5119,143
  have eq5602 (X0 : G) : ¬(new b a X0) ∨ c = sk0 ∨ a = sk1 ∨ c = sk2 ∨ c = X0 ∨ c = sk1 := resolve eq4988 prev_0 -- resolution 4988,205
  have eq6109 : c = sk3 ∨ c = sk1 ∨ sk0 = sk3 ∨ b = sk1 ∨ c = sk1 ∨ b = sk1 ∨ (old a a b) := resolve eq3022 eq3355 -- resolution 3022,3355
  have eq6120 : c = sk3 ∨ c = sk1 ∨ sk0 = sk3 ∨ b = sk1 ∨ (old a a b) := resolve eq6109 rfl -- duplicate literal removal 6109
  have eq6122 : (old a a b) ∨ c = sk1 ∨ b = sk1 ∨ c = sk3 := resolve eq6120 preserve_2 -- subsumption resolution 6120,215
  have eq6146 (X0 : G) : c = sk1 ∨ b = sk1 ∨ c = sk3 ∨ (old a b X0) ∨ ¬(old X0 a a) := resolve eq6122 old_1 -- resolution 6122,149
  have eq6154 (X0 : G) : ¬(old X0 a a) ∨ b = sk1 ∨ c = sk3 ∨ c = sk1 := resolve eq6146 p3 -- subsumption resolution 6146,144
  have eq7330 : (old sk0 sk1 sk2) ∨ a = sk1 ∨ c = sk1 ∨ b = sk2 ∨ c = sk2 := resolve eq2108 rule_def_0_2 -- resolution 2108,163
  have eq7390 : a = sk1 ∨ c = sk1 ∨ b = sk2 ∨ c = sk2 ∨ c = sk3 ∨ c = sk1 ∨ sk0 = sk3 ∨ c = sk2 := resolve eq7330 eq489 -- resolution 7330,489
  have eq7415 : a = sk1 ∨ c = sk1 ∨ b = sk2 ∨ c = sk2 ∨ c = sk3 ∨ sk0 = sk3 := resolve eq7390 rfl -- duplicate literal removal 7390
  have eq7421 : c = sk3 ∨ c = sk1 ∨ b = sk2 ∨ c = sk2 ∨ a = sk1 := resolve eq7415 preserve_2 -- subsumption resolution 7415,215
  have eq7424 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ a = sk1 ∨ (old b b a) := resolve eq2742 rule_def_2_3 -- resolution 2742,172
  have eq7446 : c ≠ sk0 ∨ c = sk1 ∨ b = sk2 ∨ c = sk2 ∨ a = sk1 := eq7421.imp_left (fun h : c = sk3 ↦ superpose h preserve_2) -- superposition 215,7421, 7421 into 215, unify on (0).2 in 7421 and (0).2 in 215
  have eq7642 : b = sk2 ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 := resolve eq7446 eq4328 -- subsumption resolution 7446,4328
  have eq7643 : (old sk3 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ a = sk1 ∨ (old b b a) := resolve eq3071 rule_def_2_3 -- resolution 3071,172
  have eq7802 : (old sk3 b b) ∨ c = b ∨ c = sk3 ∨ c = sk1 ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 ∨ a = sk1 := Or.assoc5 (eq7642.imp_left (fun h : b = sk2 ↦ superpose h eq848)) -- superposition 848,7642, 7642 into 848, unify on (0).2 in 7642 and (0).3 in 848
  have eq7972 : (old sk3 b b) ∨ c = b ∨ c = sk3 ∨ c = sk1 ∨ a = sk1 ∨ c = sk2 := resolve eq7802 rfl -- duplicate literal removal 7802
  have eq8076 : (old sk3 b b) ∨ c = sk3 ∨ c = sk1 ∨ a = sk1 ∨ c = sk2 := resolve eq7972 bc -- subsumption resolution 7972,143
  have eq9587 : c = sk2 ∨ c = sk1 ∨ a = sk1 ∨ (old b b a) ∨ c = sk3 ∨ c = sk1 ∨ sk0 = sk3 ∨ c = sk2 := resolve eq7424 eq489 -- resolution 7424,489
  have eq9597 (X0 : G) : ¬(old X0 sk1 sk2) ∨ c = sk1 ∨ a = sk1 ∨ (old b b a) ∨ sk0 = X0 ∨ c = sk2 := resolve eq7424 old_8 -- resolution 7424,156
  have eq9616 : c = sk2 ∨ c = sk1 ∨ a = sk1 ∨ (old b b a) ∨ c = sk3 ∨ sk0 = sk3 := resolve eq9587 rfl -- duplicate literal removal 9587
  have eq9622 : (old b b a) ∨ c = sk1 ∨ a = sk1 ∨ c = sk2 ∨ c = sk3 := resolve eq9616 preserve_2 -- subsumption resolution 9616,215
  have eq9637 : (new b a c) ∨ a = sk1 ∨ c = sk2 ∨ c = sk3 ∨ c = sk1 := resolve eq9622 eq226 -- resolution 9622,226
  have eq9667 (X0 : G) : ¬(new b a X0) ∨ c = sk2 ∨ c = sk3 ∨ c = sk1 ∨ c = X0 ∨ a = sk1 := resolve eq9637 prev_0 -- resolution 9637,205
  have eq11699 : (old sk2 b b) ∨ b = sk0 ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ (old a a b) ∨ (old b b a) := resolve eq4001 rule_def_2_3 -- resolution 4001,172
  have eq12514 : b = sk1 ∨ (old a a b) ∨ sk0 = sk3 ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 ∨ (old a a b) := resolve eq3595 eq3378 -- resolution 3595,3378
  have eq12517 : b = sk1 ∨ (old a a b) ∨ sk0 = sk3 ∨ c = sk1 := resolve eq12514 rfl -- duplicate literal removal 12514
  have eq12524 : (old a a b) ∨ b = sk1 ∨ c = sk1 := resolve eq12517 preserve_2 -- subsumption resolution 12517,215
  have eq12564 : (new a a b) ∨ c = sk1 ∨ b = sk1 := resolve eq12524 imp_new_0 -- resolution 12524,159
  have eq12686 (X0 : G) : ¬(new a a X0) ∨ b = sk1 ∨ b = X0 ∨ c = sk1 := resolve eq12564 prev_0 -- resolution 12564,205
  have eq40766 : c = sk1 ∨ a = sk1 ∨ (old b b a) ∨ sk0 = sk3 ∨ c = sk2 ∨ c = sk2 ∨ c = sk1 ∨ a = sk1 ∨ (old b b a) := resolve eq9597 eq7643 -- resolution 9597,7643
  have eq40816 : c = sk1 ∨ a = sk1 ∨ (old b b a) ∨ sk0 = sk3 ∨ c = sk2 := resolve eq40766 rfl -- duplicate literal removal 40766
  have eq40860 : (old b b a) ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 := resolve eq40816 preserve_2 -- subsumption resolution 40816,215
  have eq40876 (X0 : G) : ¬(old X0 b b) ∨ c = sk1 ∨ c = sk2 ∨ (old b a X0) ∨ a = sk1 := resolve eq40860 old_1 -- resolution 40860,149
  have eq41676 : c = sk1 ∨ c = sk2 ∨ (old b a sk0) ∨ a = sk1 ∨ c = sk0 ∨ a = sk1 ∨ c = sk1 ∨ c = sk2 := resolve eq40876 eq5124 -- resolution 40876,5124
  have eq41678 : c = sk1 ∨ c = sk2 ∨ (old b a sk3) ∨ a = sk1 ∨ c = sk3 ∨ c = sk1 ∨ a = sk1 ∨ c = sk2 := resolve eq40876 eq8076 -- resolution 40876,8076
  have eq41686 : (old b a sk3) ∨ c = sk2 ∨ c = sk1 ∨ a = sk1 ∨ c = sk3 := resolve eq41678 rfl -- duplicate literal removal 41678
  have eq41688 : (old b a sk0) ∨ c = sk2 ∨ c = sk1 ∨ a = sk1 ∨ c = sk0 := resolve eq41676 rfl -- duplicate literal removal 41676
  have eq41853 : c = sk2 ∨ c = sk1 ∨ a = sk1 ∨ c = sk3 ∨ (new b a sk3) := resolve eq41686 imp_new_0 -- resolution 41686,159
  have eq41896 : c = sk3 ∨ c = sk1 ∨ a = sk1 ∨ c = sk2 := resolve eq41853 eq9667 -- subsumption resolution 41853,9667
  have eq41988 : c ≠ sk0 ∨ c = sk1 ∨ a = sk1 ∨ c = sk2 := eq41896.imp_left (fun h : c = sk3 ↦ superpose h preserve_2) -- superposition 215,41896, 41896 into 215, unify on (0).2 in 41896 and (0).2 in 215
  have eq43842 : c = sk2 ∨ c = sk1 ∨ a = sk1 ∨ c = sk0 ∨ (new b a sk0) := resolve eq41688 imp_new_0 -- resolution 41688,159
  have eq43852 : (new b a sk0) ∨ c = sk1 ∨ a = sk1 ∨ c = sk2 := resolve eq43842 eq41988 -- subsumption resolution 43842,41988
  have eq44186 : c = sk1 ∨ a = sk1 ∨ c = sk2 ∨ c = sk0 ∨ a = sk1 ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq43852 eq5602 -- resolution 43852,5602
  have eq44209 : c = sk1 ∨ a = sk1 ∨ c = sk2 ∨ c = sk0 := resolve eq44186 rfl -- duplicate literal removal 44186
  have eq44212 : c = sk2 ∨ a = sk1 ∨ c = sk1 := resolve eq44209 eq41988 -- subsumption resolution 44209,41988
  have eq44601 : (sP1 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ a = sk1 ∨ a = b ∨ a = sk0 ∨ c = b ∨ a = sk1 ∨ c = sk1 := Or.assoc6 (eq44212.imp_left (fun h : c = sk2 ↦ superpose h eq2821)) -- superposition 2821,44212, 44212 into 2821, unify on (0).2 in 44212 and (0).3 in 2821
  have eq44606 : (sP1 sk3 sk1 c) ∨ (old sk3 sk1 c) ∨ a = sk1 ∨ a = b ∨ a = sk3 ∨ c = b ∨ a = sk1 ∨ c = sk1 := Or.assoc6 (eq44212.imp_left (fun h : c = sk2 ↦ superpose h eq3091)) -- superposition 3091,44212, 44212 into 3091, unify on (0).2 in 44212 and (0).3 in 3091
  have eq44960 : (sP1 sk3 sk1 c) ∨ (old sk3 sk1 c) ∨ a = sk1 ∨ a = b ∨ a = sk3 ∨ c = b ∨ c = sk1 := resolve eq44606 rfl -- duplicate literal removal 44606
  have eq44963 : (sP1 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ a = sk1 ∨ a = b ∨ a = sk0 ∨ c = b ∨ c = sk1 := resolve eq44601 rfl -- duplicate literal removal 44601
  have eq45146 : (sP1 sk0 sk1 c) ∨ a = sk1 ∨ a = b ∨ a = sk0 ∨ c = b ∨ c = sk1 := resolve eq44963 p4XY -- subsumption resolution 44963,145
  have eq45147 : (sP1 sk0 sk1 c) ∨ a = sk1 ∨ a = b ∨ a = sk0 ∨ c = sk1 := resolve eq45146 bc -- subsumption resolution 45146,143
  have eq45148 : a = sk1 ∨ a = b ∨ a = sk0 ∨ c = sk1 := resolve eq45147 rule_def_1_1 -- subsumption resolution 45147,166
  have eq45149 : c = sk1 ∨ a = sk0 ∨ a = sk1 := resolve eq45148 eq845 -- subsumption resolution 45148,845
  have eq45153 : (sP1 sk3 sk1 c) ∨ a = sk1 ∨ a = b ∨ a = sk3 ∨ c = b ∨ c = sk1 := resolve eq44960 p4XY -- subsumption resolution 44960,145
  have eq45154 : (sP1 sk3 sk1 c) ∨ a = sk1 ∨ a = b ∨ a = sk3 ∨ c = sk1 := resolve eq45153 bc -- subsumption resolution 45153,143
  have eq45155 : a = sk1 ∨ a = b ∨ a = sk3 ∨ c = sk1 := resolve eq45154 rule_def_1_1 -- subsumption resolution 45154,166
  have eq45156 : a = sk3 ∨ a = sk1 ∨ c = sk1 := resolve eq45155 eq845 -- subsumption resolution 45155,845
  have eq45337 : (sP6 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (old sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ a = c ∨ c = b ∨ a = sk0 ∨ a = sk1 := Or.assoc6 (eq45149.imp_left (fun h : c = sk1 ↦ superpose h eq337)) -- superposition 337,45149, 45149 into 337, unify on (0).2 in 45149 and (0).2 in 337
  have eq45341 : (sP6 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ (old sk0 c sk2) ∨ (sP5 sk0 c sk2) ∨ b = sk0 ∨ c = b ∨ a = sk0 ∨ a = sk1 := Or.assoc6 (eq45149.imp_left (fun h : c = sk1 ↦ superpose h eq348)) -- superposition 348,45149, 45149 into 348, unify on (0).2 in 45149 and (0).2 in 348
  have eq45483 : (old sk0 c sk2) ∨ a = c ∨ c = b ∨ a = sk0 ∨ b = sk0 ∨ a = sk0 ∨ a = sk1 := Or.assoc5 (eq45149.imp_left (fun h : c = sk1 ↦ superpose h eq1172)) -- superposition 1172,45149, 45149 into 1172, unify on (0).2 in 45149 and (0).2 in 1172
  have eq45813 : (old sk0 c sk2) ∨ a = c ∨ c = b ∨ a = sk0 ∨ b = sk0 ∨ a = sk1 := resolve eq45483 rfl -- duplicate literal removal 45483
  have eq45894 : (sP6 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ a = c ∨ c = b ∨ a = sk0 ∨ a = sk1 := resolve eq45337 p4XZ -- subsumption resolution 45337,146
  have eq45895 : (sP6 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ c = b ∨ a = sk0 ∨ a = sk1 := resolve eq45894 ac -- subsumption resolution 45894,142
  have eq45896 : (sP6 sk0 c sk2) ∨ (sP1 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ a = sk0 ∨ a = sk1 := resolve eq45895 bc -- subsumption resolution 45895,143
  have eq45897 : (sP1 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ a = sk0 ∨ a = sk1 := resolve eq45896 rule_def_6_0 -- subsumption resolution 45896,189
  have eq45898 : (sP1 sk0 c sk2) ∨ a = sk0 ∨ a = sk1 := resolve eq45897 rule_def_4_0 -- subsumption resolution 45897,179
  have eq45907 : (sP6 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ (sP5 sk0 c sk2) ∨ b = sk0 ∨ c = b ∨ a = sk0 ∨ a = sk1 := resolve eq45341 p4XZ -- subsumption resolution 45341,146
  have eq45908 : (sP6 sk0 c sk2) ∨ (sP4 sk0 c sk2) ∨ (sP5 sk0 c sk2) ∨ b = sk0 ∨ a = sk0 ∨ a = sk1 := resolve eq45907 bc -- subsumption resolution 45907,143
  have eq45909 : (sP4 sk0 c sk2) ∨ (sP5 sk0 c sk2) ∨ b = sk0 ∨ a = sk0 ∨ a = sk1 := resolve eq45908 rule_def_6_0 -- subsumption resolution 45908,189
  have eq45910 : (sP5 sk0 c sk2) ∨ b = sk0 ∨ a = sk0 ∨ a = sk1 := resolve eq45909 rule_def_4_0 -- subsumption resolution 45909,179
  have eq45961 : a = c ∨ c = b ∨ a = sk0 ∨ b = sk0 ∨ a = sk1 := resolve eq45813 p4XZ -- subsumption resolution 45813,146
  have eq45962 : c = b ∨ a = sk0 ∨ b = sk0 ∨ a = sk1 := resolve eq45961 ac -- subsumption resolution 45961,142
  have eq45963 : a = sk1 ∨ b = sk0 ∨ a = sk0 := resolve eq45962 bc -- subsumption resolution 45962,143
  have eq46067 : a ≠ sk0 ∨ a = sk1 ∨ c = sk1 := eq45156.imp_left (fun h : a = sk3 ↦ superpose h preserve_2) -- superposition 215,45156, 45156 into 215, unify on (0).2 in 45156 and (0).2 in 215
  have eq46654 : c = sk1 ∨ a = sk1 := resolve eq46067 eq45149 -- subsumption resolution 46067,45149
  have eq46697 : (new sk3 c sk2) ∨ a = sk1 := eq46654.imp_left (fun h : c = sk1 ↦ superpose h preserve_1) -- superposition 214,46654, 46654 into 214, unify on (0).2 in 46654 and (0).2 in 214
  have eq46883 : (old sk3 c sk2) ∨ a = c ∨ c = b ∨ a = sk3 ∨ (old sk2 b a) ∨ a = sk1 := Or.assoc5 (eq46654.imp_left (fun h : c = sk1 ↦ superpose h eq1266)) -- superposition 1266,46654, 46654 into 1266, unify on (0).2 in 46654 and (0).2 in 1266
  have eq46884 : (old sk3 c sk2) ∨ a = c ∨ c = b ∨ a = sk3 ∨ b = sk3 ∨ a = sk1 := Or.assoc5 (eq46654.imp_left (fun h : c = sk1 ↦ superpose h eq1268)) -- superposition 1268,46654, 46654 into 1268, unify on (0).2 in 46654 and (0).2 in 1268
  have eq46932 : (sP1 sk0 c sk2) ∨ (old sk0 c sk2) ∨ a = c ∨ c = b ∨ (old b b a) ∨ a = sk2 ∨ a = sk1 := Or.assoc6 (eq46654.imp_left (fun h : c = sk1 ↦ superpose h eq3235)) -- superposition 3235,46654, 46654 into 3235, unify on (0).2 in 46654 and (0).2 in 3235
  have eq46937 : (old sk0 c sk2) ∨ b = sk0 ∨ c = b ∨ (old b b a) ∨ a = sk2 ∨ a = sk1 := Or.assoc5 (eq46654.imp_left (fun h : c = sk1 ↦ superpose h eq3318)) -- superposition 3318,46654, 46654 into 3318, unify on (0).2 in 46654 and (0).2 in 3318
  have eq46955 : (old sk3 c sk2) ∨ b = sk3 ∨ c = b ∨ (old b b a) ∨ a = sk2 ∨ a = sk1 := Or.assoc5 (eq46654.imp_left (fun h : c = sk1 ↦ superpose h eq3517)) -- superposition 3517,46654, 46654 into 3517, unify on (0).2 in 46654 and (0).2 in 3517
  have eq47249 : a = c ∨ c = b ∨ a = sk3 ∨ (old sk2 b a) ∨ a = sk1 := resolve eq46883 p4XZ -- subsumption resolution 46883,146
  have eq47250 : c = b ∨ a = sk3 ∨ (old sk2 b a) ∨ a = sk1 := resolve eq47249 ac -- subsumption resolution 47249,142
  have eq47251 : (old sk2 b a) ∨ a = sk3 ∨ a = sk1 := resolve eq47250 bc -- subsumption resolution 47250,143
  have eq47252 : a = c ∨ c = b ∨ a = sk3 ∨ b = sk3 ∨ a = sk1 := resolve eq46884 p4XZ -- subsumption resolution 46884,146
  have eq47253 : c = b ∨ a = sk3 ∨ b = sk3 ∨ a = sk1 := resolve eq47252 ac -- subsumption resolution 47252,142
  have eq47254 : b = sk3 ∨ a = sk3 ∨ a = sk1 := resolve eq47253 bc -- subsumption resolution 47253,143
  have eq47270 : (sP1 sk0 c sk2) ∨ a = c ∨ c = b ∨ (old b b a) ∨ a = sk2 ∨ a = sk1 := resolve eq46932 p4XZ -- subsumption resolution 46932,146
  have eq47271 : (sP1 sk0 c sk2) ∨ c = b ∨ (old b b a) ∨ a = sk2 ∨ a = sk1 := resolve eq47270 ac -- subsumption resolution 47270,142
  have eq47272 : (sP1 sk0 c sk2) ∨ (old b b a) ∨ a = sk2 ∨ a = sk1 := resolve eq47271 bc -- subsumption resolution 47271,143
  have eq47279 : b = sk0 ∨ c = b ∨ (old b b a) ∨ a = sk2 ∨ a = sk1 := resolve eq46937 p4XZ -- subsumption resolution 46937,146
  have eq47280 : (old b b a) ∨ b = sk0 ∨ a = sk2 ∨ a = sk1 := resolve eq47279 bc -- subsumption resolution 47279,143
  have eq47305 : b = sk3 ∨ c = b ∨ (old b b a) ∨ a = sk2 ∨ a = sk1 := resolve eq46955 p4XZ -- subsumption resolution 46955,146
  have eq47306 : (old b b a) ∨ b = sk3 ∨ a = sk2 ∨ a = sk1 := resolve eq47305 bc -- subsumption resolution 47305,143
  have eq47685 : (sP6 sk0 a sk2) ∨ (sP0 sk0 a sk2) ∨ (old sk0 a sk2) ∨ (sP4 sk0 a sk2) ∨ b = sk0 ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := Or.assoc6 (eq45963.imp_left (fun h : a = sk1 ↦ superpose h eq350)) -- superposition 350,45963, 45963 into 350, unify on (0).2 in 45963 and (0).2 in 350
  have eq47740 : (old sk3 a sk2) ∨ c = sk2 ∨ c = sk3 ∨ a = c ∨ b = sk0 ∨ a = sk0 := Or.assoc4 (eq45963.imp_left (fun h : a = sk1 ↦ superpose h eq480)) -- superposition 480,45963, 45963 into 480, unify on (0).2 in 45963 and (0).2 in 480
  have eq48406 : (sP6 sk0 a sk2) ∨ (sP0 sk0 a sk2) ∨ (old sk0 a sk2) ∨ (sP4 sk0 a sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq47685 rfl -- duplicate literal removal 47685
  have eq48439 : (sP0 sk0 a sk2) ∨ (old sk0 a sk2) ∨ (sP4 sk0 a sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq48406 rule_def_6_0 -- subsumption resolution 48406,189
  have eq48440 : (sP0 sk0 a sk2) ∨ (old sk0 a sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq48439 rule_def_4_0 -- subsumption resolution 48439,179
  have eq48441 : (old sk0 a sk2) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq48440 rule_def_0_0 -- subsumption resolution 48440,161
  have eq48464 : (old sk3 a sk2) ∨ c = sk2 ∨ c = sk3 ∨ b = sk0 ∨ a = sk0 := resolve eq47740 ac -- subsumption resolution 47740,142
  have eq48827 : b ≠ sk0 ∨ a = sk3 ∨ a = sk1 := eq47254.imp_left (fun h : b = sk3 ↦ superpose h preserve_2) -- superposition 215,47254, 47254 into 215, unify on (0).2 in 47254 and (0).2 in 215
  have eq48829 (X0 : G) : ¬(new X0 sk1 b) ∨ (new sk1 sk2 X0) ∨ a = sk3 ∨ a = sk1 := Or.assoc2 (eq47254.imp_left (fun h : b = sk3 ↦ superpose h eq247)) -- superposition 247,47254, 47254 into 247, unify on (0).2 in 47254 and (0).3 in 247
  have eq49142 : a ≠ b ∨ a = sk3 ∨ a = sk1 := resolve eq47254 trans_resol -- equality factoring 47254
  have eq51253 : (old sk2 b a) ∨ a = sk1 ∨ a = sk0 := resolve eq45898 rule_def_1_2 -- resolution 45898,167
  have eq52020 (X0 : G) : ¬(old X0 b a) ∨ a = sk1 ∨ sk2 = X0 ∨ a = sk3 := resolve eq47251 old_8 -- resolution 47251,156
  have eq52571 : (new b c sk2) ∨ a = sk0 ∨ a = sk1 := resolve eq51253 eq220 -- resolution 51253,220
  have eq52585 (X0 : G) : ¬(old X0 b a) ∨ a = sk0 ∨ sk2 = X0 ∨ a = sk1 := resolve eq51253 old_8 -- resolution 51253,156
  have eq53315 (X0 : G) : ¬(new X0 c b) ∨ a = sk1 ∨ (new c sk2 X0) ∨ a = sk0 := resolve eq52571 prev_1 -- resolution 52571,206
  have eq58879 : (new c b b) ∨ a = sk2 ∨ a = sk1 ∨ b = sk0 := resolve eq47280 eq223 -- resolution 47280,223
  have eq59164 : (old sk0 a a) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ b = sk0 ∨ b = sk1 ∨ c = sk0 := Or.assoc4 (eq1580.imp_left (fun h : a = sk2 ↦ superpose h eq48441)) -- superposition 48441,1580, 1580 into 48441, unify on (0).2 in 1580 and (0).3 in 48441
  have eq59178 : (old sk0 a a) ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ b = sk1 := resolve eq59164 rfl -- duplicate literal removal 59164
  have eq59184 : b = sk1 ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ b = sk0 := resolve eq59178 eq4112 -- subsumption resolution 59178,4112
  have eq60588 : a = sk1 ∨ b = sk2 ∨ a = sk3 ∨ b = sk0 ∨ a = sk2 ∨ a = sk1 := resolve eq52020 eq47280 -- resolution 52020,47280
  have eq60626 : a = sk1 ∨ b = sk2 ∨ a = sk3 ∨ b = sk0 ∨ a = sk2 := resolve eq60588 rfl -- duplicate literal removal 60588
  have eq60636 : a = sk3 ∨ b = sk2 ∨ a = sk1 ∨ a = sk2 := resolve eq60626 eq48827 -- subsumption resolution 60626,48827
  have eq60864 : a ≠ sk0 ∨ b = sk2 ∨ a = sk1 ∨ a = sk2 := eq60636.imp_left (fun h : a = sk3 ↦ superpose h preserve_2) -- superposition 215,60636, 60636 into 215, unify on (0).2 in 60636 and (0).2 in 215
  have eq61923 : a = sk0 ∨ b = sk2 ∨ a = sk1 ∨ b = sk3 ∨ a = sk2 ∨ a = sk1 := resolve eq52585 eq47306 -- resolution 52585,47306
  have eq61964 : a = sk0 ∨ b = sk2 ∨ a = sk1 ∨ b = sk3 ∨ a = sk2 := resolve eq61923 rfl -- duplicate literal removal 61923
  have eq61975 : b = sk3 ∨ a = sk1 ∨ b = sk2 ∨ a = sk2 := resolve eq61964 eq60864 -- subsumption resolution 61964,60864
  have eq62056 : a = b ∨ a = sk1 ∨ b = sk2 ∨ a = sk2 ∨ b = sk2 ∨ a = sk1 ∨ a = sk2 := Or.assoc4 (eq60636.imp_left (fun h : a = sk3 ↦ superpose h eq61975)) -- superposition 61975,60636, 60636 into 61975, unify on (0).2 in 60636 and (0).2 in 61975
  have eq62625 : b = sk2 ∨ a = sk1 ∨ a = b ∨ a = sk2 := resolve eq62056 rfl -- duplicate literal removal 62056
  have eq63010 : (new sk0 sk1 b) ∨ a = sk1 ∨ a = b ∨ a = sk2 := eq62625.imp_left (fun h : b = sk2 ↦ superpose h preserve_0) -- superposition 213,62625, 62625 into 213, unify on (0).2 in 62625 and (0).3 in 213
  have eq63621 : (new sk3 c b) ∨ a = sk1 ∨ a = sk1 ∨ a = b ∨ a = sk2 := Or.assoc2 (eq62625.imp_left (fun h : b = sk2 ↦ superpose h eq46697)) -- superposition 46697,62625, 62625 into 46697, unify on (0).2 in 62625 and (0).3 in 46697
  have eq63654 : (new sk3 c b) ∨ a = sk1 ∨ a = b ∨ a = sk2 := resolve eq63621 rfl -- duplicate literal removal 63621
  have eq64494 (X0 : G) : ¬(new c b X0) ∨ a = sk1 ∨ b = sk0 ∨ b = X0 ∨ a = sk2 := resolve eq58879 prev_0 -- resolution 58879,205
  have eq64828 (X0 : G) : b = sk0 ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ (old a a b) ∨ (old b b a) ∨ (old b b X0) ∨ ¬(old X0 b sk2) := resolve eq11699 old_1 -- resolution 11699,149
  have eq70779 : (sP1 sk0 c b) ∨ (old b b a) ∨ a = b ∨ a = sk1 ∨ a = sk1 ∨ a = b ∨ a = sk2 := Or.assoc4 (eq62625.imp_left (fun h : b = sk2 ↦ superpose h eq47272)) -- superposition 47272,62625, 62625 into 47272, unify on (0).2 in 62625 and (0).3 in 47272
  have eq70780 : (sP1 sk0 c b) ∨ (old b b a) ∨ a = b ∨ a = sk1 ∨ a = sk2 := resolve eq70779 rfl -- duplicate literal removal 70779
  have eq70787 : (old b b a) ∨ a = b ∨ a = sk1 ∨ a = sk2 := resolve eq70780 rule_def_1_2 -- subsumption resolution 70780,167
  have eq70794 : (new c b b) ∨ a = sk1 ∨ a = sk2 ∨ a = b := resolve eq70787 eq223 -- resolution 70787,223
  have eq70940 (X0 : G) : a = sk1 ∨ a = sk2 ∨ a = b ∨ b = X0 ∨ ¬(new c b X0) := resolve eq70794 prev_0 -- resolution 70794,205
  have eq72456 : (new sk1 sk2 sk0) ∨ a = sk3 ∨ a = sk1 ∨ a = sk1 ∨ a = b ∨ a = sk2 := resolve eq48829 eq63010 -- resolution 48829,63010
  have eq72474 : (new sk1 sk2 sk0) ∨ a = sk3 ∨ a = sk1 ∨ a = b ∨ a = sk2 := resolve eq72456 rfl -- duplicate literal removal 72456
  have eq72478 : (new sk1 sk2 sk0) ∨ a = sk3 ∨ a = sk1 ∨ a = sk2 := resolve eq72474 eq49142 -- subsumption resolution 72474,49142
  have eq72575 : (new c sk2 sk0) ∨ a = sk3 ∨ a = c ∨ a = sk2 ∨ a = sk1 := Or.assoc4 (eq46654.imp_left (fun h : c = sk1 ↦ superpose h eq72478)) -- superposition 72478,46654, 46654 into 72478, unify on (0).2 in 46654 and (0).1 in 72478
  have eq72600 : (new c sk2 sk0) ∨ a = sk3 ∨ a = sk2 ∨ a = sk1 := resolve eq72575 ac -- subsumption resolution 72575,142
  have eq72904 : (new c b sk0) ∨ a = sk3 ∨ a = b ∨ a = sk1 ∨ a = sk1 ∨ a = b ∨ a = sk2 := Or.assoc4 (eq62625.imp_left (fun h : b = sk2 ↦ superpose h eq72600)) -- superposition 72600,62625, 62625 into 72600, unify on (0).2 in 62625 and (0).2 in 72600
  have eq72905 : (new c b sk0) ∨ a = sk3 ∨ a = b ∨ a = sk1 ∨ a = sk2 := resolve eq72904 rfl -- duplicate literal removal 72904
  have eq72916 : (new c b sk0) ∨ a = sk3 ∨ a = sk1 ∨ a = sk2 := resolve eq72905 eq49142 -- subsumption resolution 72905,49142
  have eq80650 (X0 : G) : (old a a b) ∨ (old b b a) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 ∨ (old b b X0) ∨ ¬(old X0 b sk2) := resolve eq4326 old_1 -- resolution 4326,149
  have eq89536 : (old sk3 a a) ∨ a = c ∨ c = sk3 ∨ b = sk0 ∨ a = sk0 ∨ b = sk1 ∨ c = sk1 ∨ b = sk0 := Or.assoc5 (eq2524.imp_left (fun h : a = sk2 ↦ superpose h eq48464)) -- superposition 48464,2524, 2524 into 48464, unify on (0).2 in 2524 and (0).3 in 48464
  have eq89545 : (old sk3 a a) ∨ a = c ∨ c = sk3 ∨ b = sk0 ∨ a = sk0 ∨ b = sk1 ∨ c = sk1 := resolve eq89536 rfl -- duplicate literal removal 89536
  have eq89579 : (old sk3 a a) ∨ c = sk3 ∨ b = sk0 ∨ a = sk0 ∨ b = sk1 ∨ c = sk1 := resolve eq89545 ac -- subsumption resolution 89545,142
  have eq89580 : c = sk3 ∨ b = sk0 ∨ a = sk0 ∨ b = sk1 ∨ c = sk1 := resolve eq89579 eq6154 -- subsumption resolution 89579,6154
  have eq90426 : c ≠ sk0 ∨ b = sk0 ∨ a = sk0 ∨ b = sk1 ∨ c = sk1 := eq89580.imp_left (fun h : c = sk3 ↦ superpose h preserve_2) -- superposition 215,89580, 89580 into 215, unify on (0).2 in 89580 and (0).2 in 215
  have eq91239 : b = sk1 ∨ a = sk0 ∨ b = sk0 ∨ c = sk1 := resolve eq90426 eq59184 -- subsumption resolution 90426,59184
  have eq91258 : a = b ∨ a = sk0 ∨ b = sk0 ∨ a = c ∨ b = sk0 ∨ a = sk0 := Or.assoc4 (eq45963.imp_left (fun h : a = sk1 ↦ superpose h eq91239)) -- superposition 91239,45963, 45963 into 91239, unify on (0).2 in 45963 and (0).2 in 91239
  have eq92085 : a = b ∨ a = sk0 ∨ b = sk0 ∨ a = c := resolve eq91258 rfl -- duplicate literal removal 91258
  have eq92087 : b = sk0 ∨ a = sk0 ∨ a = b := resolve eq92085 ac -- subsumption resolution 92085,142
  have eq97807 : a = sk1 ∨ b = sk0 ∨ b = sk0 ∨ a = sk2 ∨ a = sk3 ∨ a = sk1 ∨ a = sk2 := resolve eq64494 eq72916 -- resolution 64494,72916
  have eq97816 : a = sk1 ∨ b = sk0 ∨ a = sk2 ∨ a = sk3 := resolve eq97807 rfl -- duplicate literal removal 97807
  have eq97833 : a = sk3 ∨ a = sk2 ∨ a = sk1 := resolve eq97816 eq48827 -- subsumption resolution 97816,48827
  have eq97932 : a ≠ sk0 ∨ a = sk2 ∨ a = sk1 := eq97833.imp_left (fun h : a = sk3 ↦ superpose h preserve_2) -- superposition 215,97833, 97833 into 215, unify on (0).2 in 97833 and (0).2 in 215
  have eq98379 : (new a c b) ∨ a = sk1 ∨ a = b ∨ a = sk2 ∨ a = sk2 ∨ a = sk1 := Or.assoc4 (eq97833.imp_left (fun h : a = sk3 ↦ superpose h eq63654)) -- superposition 63654,97833, 97833 into 63654, unify on (0).2 in 97833 and (0).1 in 63654
  have eq98383 : (new a c b) ∨ a = sk1 ∨ a = b ∨ a = sk2 := resolve eq98379 rfl -- duplicate literal removal 98379
  have eq99025 : a = sk1 ∨ a = b ∨ a = sk2 ∨ a = sk1 ∨ (new c sk2 a) ∨ a = sk0 := resolve eq98383 eq53315 -- resolution 98383,53315
  have eq99035 : a = sk1 ∨ a = b ∨ a = sk2 ∨ (new c sk2 a) ∨ a = sk0 := resolve eq99025 rfl -- duplicate literal removal 99025
  have eq99044 : (new c sk2 a) ∨ a = b ∨ a = sk2 ∨ a = sk1 := resolve eq99035 eq97932 -- subsumption resolution 99035,97932
  have eq99300 : (new c b a) ∨ a = b ∨ a = b ∨ a = sk1 ∨ a = sk1 ∨ a = b ∨ a = sk2 := Or.assoc4 (eq62625.imp_left (fun h : b = sk2 ↦ superpose h eq99044)) -- superposition 99044,62625, 62625 into 99044, unify on (0).2 in 62625 and (0).2 in 99044
  have eq99301 : (new c b a) ∨ a = b ∨ a = sk1 ∨ a = sk2 := resolve eq99300 rfl -- duplicate literal removal 99300
  have eq99315 : a = sk2 ∨ a = sk1 ∨ a = b := resolve eq99301 eq70940 -- subsumption resolution 99301,70940
  have eq100013 : (old a b a) ∨ a = sk3 ∨ a = sk1 ∨ a = sk1 ∨ a = b := Or.assoc3 (eq99315.imp_left (fun h : a = sk2 ↦ superpose h eq47251)) -- superposition 47251,99315, 99315 into 47251, unify on (0).2 in 99315 and (0).1 in 47251
  have eq100036 : (old a b a) ∨ a = sk1 ∨ a = sk0 ∨ a = sk1 ∨ a = b := Or.assoc3 (eq99315.imp_left (fun h : a = sk2 ↦ superpose h eq51253)) -- superposition 51253,99315, 99315 into 51253, unify on (0).2 in 99315 and (0).1 in 51253
  have eq100147 : (old a b a) ∨ a = sk1 ∨ a = sk0 ∨ a = b := resolve eq100036 rfl -- duplicate literal removal 100036
  have eq100163 : (old a b a) ∨ a = sk3 ∨ a = sk1 ∨ a = b := resolve eq100013 rfl -- duplicate literal removal 100013
  have eq100714 : a = sk3 ∨ a = sk1 ∨ a = b := resolve eq100163 p3 -- subsumption resolution 100163,144
  have eq100715 : a = sk3 ∨ a = sk1 := resolve eq100714 eq49142 -- subsumption resolution 100714,49142
  have eq100719 : a = sk1 ∨ a = sk0 ∨ a = b := resolve eq100147 p3 -- subsumption resolution 100147,144
  have eq100812 : a ≠ sk0 ∨ a = sk1 := eq100715.imp_left (fun h : a = sk3 ↦ superpose h preserve_2) -- superposition 215,100715, 100715 into 215, unify on (0).2 in 100715 and (0).2 in 215
  have eq102927 : (new sk0 a a) ∨ a = c ∨ a = b ∨ a = sk0 ∨ a = b := Or.assoc3 (eq100719.imp_left (fun h : a = sk1 ↦ superpose h eq2839)) -- superposition 2839,100719, 100719 into 2839, unify on (0).2 in 100719 and (0).2 in 2839
  have eq103656 : (new sk0 a a) ∨ a = c ∨ a = b ∨ a = sk0 := resolve eq102927 rfl -- duplicate literal removal 102927
  have eq104022 : (new sk0 a a) ∨ a = b ∨ a = sk0 := resolve eq103656 ac -- subsumption resolution 103656,142
  have eq107337 : (new a sk0 a) ∨ a = sk0 ∨ a = b := resolve eq104022 prev_3 -- resolution 104022,208
  have eq108009 : (new a b a) ∨ a = b ∨ a = b ∨ a = sk0 ∨ a = b := Or.assoc3 (eq92087.imp_left (fun h : b = sk0 ↦ superpose h eq107337)) -- superposition 107337,92087, 92087 into 107337, unify on (0).2 in 92087 and (0).2 in 107337
  have eq108012 : (new a b a) ∨ a = b ∨ a = sk0 := resolve eq108009 rfl -- duplicate literal removal 108009
  have eq108639 : a = b ∨ a = sk0 ∨ a = c := resolve eq108012 eq242 -- resolution 108012,242
  have eq108649 : a = sk0 ∨ a = b := resolve eq108639 ac -- subsumption resolution 108639,142
  have eq109100 : a ≠ a ∨ a = sk1 ∨ a = b := Or.assoc2 (eq108649.imp_left (fun h : a = sk0 ↦ superpose h eq100812)) -- superposition 100812,108649, 108649 into 100812, unify on (0).2 in 108649 and (0).2 in 100812
  have eq109101 : a = sk1 ∨ a = b := resolve eq109100 rfl -- trivial inequality removal 109100
  have eq109695 : (new sk0 a a) ∨ a = c ∨ a = b ∨ a = b := Or.assoc3 (eq109101.imp_left (fun h : a = sk1 ↦ superpose h eq2839)) -- superposition 2839,109101, 109101 into 2839, unify on (0).2 in 109101 and (0).2 in 2839
  have eq110428 : (new sk0 a a) ∨ a = c ∨ a = b := resolve eq109695 rfl -- duplicate literal removal 109695
  have eq110803 : (new sk0 a a) ∨ a = b := resolve eq110428 ac -- subsumption resolution 110428,142
  have eq111271 : (new a a a) ∨ a = b ∨ a = b := Or.assoc2 (eq108649.imp_left (fun h : a = sk0 ↦ superpose h eq110803)) -- superposition 110803,108649, 108649 into 110803, unify on (0).2 in 108649 and (0).1 in 110803
  have eq111276 : (new a a a) ∨ a = b := resolve eq111271 rfl -- duplicate literal removal 111271
  have eq111740 : a = b ∨ b = sk1 ∨ a = b ∨ c = sk1 := resolve eq111276 eq12686 -- resolution 111276,12686
  have eq111757 : b = sk1 ∨ a = b ∨ c = sk1 := resolve eq111740 rfl -- duplicate literal removal 111740
  have eq113261 : a = b ∨ a = b ∨ a = c ∨ a = b := Or.assoc3 (eq109101.imp_left (fun h : a = sk1 ↦ superpose h eq111757)) -- superposition 111757,109101, 109101 into 111757, unify on (0).2 in 109101 and (0).2 in 111757
  have eq114412 : a = b ∨ a = c := resolve eq113261 rfl -- duplicate literal removal 113261
  have eq114416 : a = b := resolve eq114412 ac -- subsumption resolution 114412,142
  have eq114418 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq114416, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 144,114416
  have eq114424 : ∀ (X0 X1 X2 : G) , (old a a a) ∨ ¬(sP2 X0 X1 X2) := Eq.mp (by simp only [eq114416, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_2_3 -- backward demodulation 172,114416
  have eq114427 : ∀ (X0 X1 X2 : G) , (old a a a) ∨ ¬(sP4 X0 X1 X2) := Eq.mp (by simp only [eq114416, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_4_3 -- backward demodulation 182,114416
  have eq114428 : ∀ (X0 X1 X2 : G) , (old a a a) ∨ ¬(sP5 X0 X1 X2) := Eq.mp (by simp only [eq114416, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_5_3 -- backward demodulation 187,114416
  have eq114429 : ∀ (X0 X1 X2 : G) , (old a a a) ∨ ¬(sP6 X0 X1 X2) := Eq.mp (by simp only [eq114416, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_6_2 -- backward demodulation 191,114416
  have eq114463 : a = sk0 ∨ (sP6 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (old sk2 b b) := Eq.mp (by simp only [eq114416, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq343 -- backward demodulation 343,114416
  have eq114472 : a = sk3 ∨ (sP6 sk3 sk1 sk2) ∨ (sP4 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP5 sk3 sk1 sk2) ∨ (old sk2 b b) := Eq.mp (by simp only [eq114416, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq383 -- backward demodulation 383,114416
  have eq116919 : a = sk0 ∨ (sP5 sk0 c sk2) ∨ a = sk0 ∨ a = sk1 := Eq.mp (by simp only [eq114416, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq45910 -- backward demodulation 45910,114416
  have eq117900 : ∀ (X0 : G) , (old a a a) ∨ b = sk0 ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ (old a a b) ∨ (old b b X0) ∨ ¬(old X0 b sk2) := Eq.mp (by simp only [eq114416, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq64828 -- backward demodulation 64828,114416
  have eq118644 : ∀ (X0 : G) , (old a a a) ∨ (old a a b) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 ∨ (old b b X0) ∨ ¬(old X0 b sk2) := Eq.mp (by simp only [eq114416, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq80650 -- backward demodulation 80650,114416
  have eq120208 : a = sk0 ∨ (sP5 sk0 c sk2) ∨ a = sk1 := resolve eq116919 rfl -- duplicate literal removal 116919
  have eq120552 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) := resolve eq114424 eq114418 -- subsumption resolution 114424,114418
  have eq120554 (X0 X1 X2 : G) : ¬(sP4 X0 X1 X2) := resolve eq114427 eq114418 -- subsumption resolution 114427,114418
  have eq120555 (X0 X1 X2 : G) : ¬(sP5 X0 X1 X2) := resolve eq114428 eq114418 -- subsumption resolution 114428,114418
  have eq120556 (X0 X1 X2 : G) : ¬(sP6 X0 X1 X2) := resolve eq114429 eq114418 -- subsumption resolution 114429,114418
  have eq120618 : a = sk0 ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (old sk2 b b) := resolve eq114463 eq120556 -- subsumption resolution 114463,120556
  have eq120619 : a = sk0 ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (old sk2 b b) := resolve eq120618 eq120554 -- subsumption resolution 120618,120554
  have eq120620 : a = sk0 ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (old sk2 b b) := resolve eq120619 eq120552 -- subsumption resolution 120619,120552
  have eq120621 : a = sk0 ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (old sk2 b b) := resolve eq120620 eq120555 -- subsumption resolution 120620,120555
  have eq120622 : a = sk0 ∨ (old sk0 sk1 sk2) ∨ (old sk2 b b) := resolve eq120621 rule_def_0_0 -- subsumption resolution 120621,161
  have eq120623 : (old sk2 a a) ∨ a = sk0 ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq114416, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq120622 -- forward demodulation 120622,114416
  have eq120649 : a = sk3 ∨ (sP4 sk3 sk1 sk2) ∨ (sP2 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP5 sk3 sk1 sk2) ∨ (old sk2 b b) := resolve eq114472 eq120556 -- subsumption resolution 114472,120556
  have eq120650 : a = sk3 ∨ (sP2 sk3 sk1 sk2) ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP5 sk3 sk1 sk2) ∨ (old sk2 b b) := resolve eq120649 eq120554 -- subsumption resolution 120649,120554
  have eq120651 : a = sk3 ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (sP5 sk3 sk1 sk2) ∨ (old sk2 b b) := resolve eq120650 eq120552 -- subsumption resolution 120650,120552
  have eq120652 : a = sk3 ∨ (sP0 sk3 sk1 sk2) ∨ (old sk3 sk1 sk2) ∨ (old sk2 b b) := resolve eq120651 eq120555 -- subsumption resolution 120651,120555
  have eq120653 : a = sk3 ∨ (old sk3 sk1 sk2) ∨ (old sk2 b b) := resolve eq120652 rule_def_0_0 -- subsumption resolution 120652,161
  have eq120654 : (old sk2 a a) ∨ a = sk3 ∨ (old sk3 sk1 sk2) := Eq.mp (by simp only [eq114416, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq120653 -- forward demodulation 120653,114416
  have eq122731 : a = sk0 ∨ a = sk1 := resolve eq120208 eq120555 -- subsumption resolution 120208,120555
  have eq122732 : a = sk1 := resolve eq122731 eq100812 -- subsumption resolution 122731,100812
  have eq122755 : (old sk0 a sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := Eq.mp (by simp only [eq122732, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq356 -- backward demodulation 356,122732
  have eq122767 : (old sk3 a sk2) ∨ c = sk2 ∨ c = sk3 ∨ c = sk1 := Eq.mp (by simp only [eq122732, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq480 -- backward demodulation 480,122732
  have eq122846 : (old sk2 a a) ∨ (old sk0 a sk2) ∨ a = sk0 := Eq.mp (by simp only [eq122732, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq120623 -- backward demodulation 120623,122732
  have eq122854 : (old sk3 a sk2) ∨ (old sk2 a a) ∨ a = sk3 := Eq.mp (by simp only [eq122732, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq120654 -- backward demodulation 120654,122732
  have eq122951 : a = c ∨ (old sk0 a sk2) ∨ c = sk2 ∨ c = sk0 := Eq.mp (by simp only [eq122732, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq122755 -- forward demodulation 122755,122732
  have eq122952 : (old sk0 a sk2) ∨ c = sk2 ∨ c = sk0 := resolve eq122951 ac -- subsumption resolution 122951,142
  have eq122979 : a = c ∨ (old sk3 a sk2) ∨ c = sk2 ∨ c = sk3 := Eq.mp (by simp only [eq122732, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq122767 -- forward demodulation 122767,122732
  have eq122980 : (old sk3 a sk2) ∨ c = sk2 ∨ c = sk3 := resolve eq122979 ac -- subsumption resolution 122979,142
  have eq124446 (X0 : G) : b = sk0 ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ (old a a b) ∨ (old b b X0) ∨ ¬(old X0 b sk2) := resolve eq117900 eq114418 -- subsumption resolution 117900,114418
  have eq124447 (X0 : G) : b = sk0 ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ (old b b X0) ∨ ¬(old X0 b sk2) := resolve eq124446 eq114418 -- subsumption resolution 124446,114418
  have eq124448 : ∀ (X0 : G) , a = sk0 ∨ (old sk0 sk1 sk2) ∨ a = sk0 ∨ (old b b X0) ∨ ¬(old X0 b sk2) := Eq.mp (by simp only [eq114416, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq124447 -- forward demodulation 124447,114416
  have eq124449 (X0 : G) : a = sk0 ∨ (old sk0 sk1 sk2) ∨ (old b b X0) ∨ ¬(old X0 b sk2) := resolve eq124448 rfl -- duplicate literal removal 124448
  have eq124450 : ∀ (X0 : G) , (old sk0 a sk2) ∨ a = sk0 ∨ (old b b X0) ∨ ¬(old X0 b sk2) := Eq.mp (by simp only [eq122732, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq124449 -- forward demodulation 124449,122732
  have eq124451 : ∀ (X0 : G) , (old a a X0) ∨ (old sk0 a sk2) ∨ a = sk0 ∨ ¬(old X0 b sk2) := Eq.mp (by simp only [eq114416, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq124450 -- forward demodulation 124450,114416
  have eq124452 (X0 : G) : (old sk0 a sk2) ∨ a = sk0 ∨ ¬(old X0 b sk2) := resolve eq124451 eq114418 -- subsumption resolution 124451,114418
  have eq124453 : ∀ (X0 : G) , ¬(old X0 a sk2) ∨ (old sk0 a sk2) ∨ a = sk0 := Eq.mp (by simp only [eq114416, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq124452 -- forward demodulation 124452,114416
  have eq125692 (X0 : G) : (old a a b) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 ∨ (old b b X0) ∨ ¬(old X0 b sk2) := resolve eq118644 eq114418 -- subsumption resolution 118644,114418
  have eq125693 (X0 : G) : c = sk2 ∨ c = sk1 ∨ c = sk0 ∨ (old b b X0) ∨ ¬(old X0 b sk2) := resolve eq125692 eq114418 -- subsumption resolution 125692,114418
  have eq125694 : ∀ (X0 : G) , a = c ∨ c = sk2 ∨ c = sk0 ∨ (old b b X0) ∨ ¬(old X0 b sk2) := Eq.mp (by simp only [eq122732, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq125693 -- forward demodulation 125693,122732
  have eq125695 (X0 : G) : c = sk2 ∨ c = sk0 ∨ (old b b X0) ∨ ¬(old X0 b sk2) := resolve eq125694 ac -- subsumption resolution 125694,142
  have eq125696 : ∀ (X0 : G) , (old a a X0) ∨ c = sk2 ∨ c = sk0 ∨ ¬(old X0 b sk2) := Eq.mp (by simp only [eq114416, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq125695 -- forward demodulation 125695,114416
  have eq125697 (X0 : G) : c = sk2 ∨ c = sk0 ∨ ¬(old X0 b sk2) := resolve eq125696 eq114418 -- subsumption resolution 125696,114418
  have eq125698 : ∀ (X0 : G) , ¬(old X0 a sk2) ∨ c = sk2 ∨ c = sk0 := Eq.mp (by simp only [eq114416, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq125697 -- forward demodulation 125697,114416
  have eq128107 : c = sk2 ∨ c = sk0 ∨ c = sk2 ∨ c = sk0 := resolve eq125698 eq122952 -- resolution 125698,122952
  have eq128113 : c = sk2 ∨ c = sk0 := resolve eq128107 rfl -- duplicate literal removal 128107
  have eq128129 : (old c a a) ∨ (old sk0 a c) ∨ a = sk0 ∨ c = sk0 := Or.assoc3 (eq128113.imp_left (fun h : c = sk2 ↦ superpose h eq122846)) -- superposition 122846,128113, 128113 into 122846, unify on (0).2 in 128113 and (0).1 in 122846
  have eq128139 : (old sk0 a c) ∨ a = sk0 ∨ c = sk0 := resolve eq128129 p4YZ -- subsumption resolution 128129,147
  have eq128140 : c = sk0 ∨ a = sk0 := resolve eq128139 p4XY -- subsumption resolution 128139,145
  have eq128157 : (old sk3 a c) ∨ (old c a a) ∨ a = sk3 ∨ c = sk0 := Or.assoc3 (eq128113.imp_left (fun h : c = sk2 ↦ superpose h eq122854)) -- superposition 122854,128113, 128113 into 122854, unify on (0).2 in 128113 and (0).3 in 122854
  have eq128158 : (old c a a) ∨ a = sk3 ∨ c = sk0 := resolve eq128157 p4XY -- subsumption resolution 128157,145
  have eq128159 : a = sk3 ∨ c = sk0 := resolve eq128158 p4YZ -- subsumption resolution 128158,147
  have eq128185 : a ≠ sk0 ∨ c = sk0 := eq128159.imp_left (fun h : a = sk3 ↦ superpose h preserve_2) -- superposition 215,128159, 128159 into 215, unify on (0).2 in 128159 and (0).2 in 215
  have eq128199 : c = sk0 := resolve eq128185 eq128140 -- subsumption resolution 128185,128140
  have eq128200 : c ≠ sk3 := Eq.mp (by simp only [eq128199, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_2 -- backward demodulation 215,128199
  have eq128207 : a = c ∨ (old sk2 a a) ∨ (old sk0 a sk2) := Eq.mp (by simp only [eq128199, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq122846 -- backward demodulation 122846,128199
  have eq128235 : ∀ (X0 : G) , a = c ∨ ¬(old X0 a sk2) ∨ (old sk0 a sk2) := Eq.mp (by simp only [eq128199, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq124453 -- backward demodulation 124453,128199
  have eq128308 : (old sk2 a a) ∨ (old sk0 a sk2) := resolve eq128207 ac -- subsumption resolution 128207,142
  have eq128309 : (old c a sk2) ∨ (old sk2 a a) := Eq.mp (by simp only [eq128199, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq128308 -- forward demodulation 128308,128199
  have eq128310 : (old sk2 a a) := resolve eq128309 p4YZ -- subsumption resolution 128309,147
  have eq128351 (X0 : G) : ¬(old X0 a sk2) ∨ (old sk0 a sk2) := resolve eq128235 ac -- subsumption resolution 128235,142
  have eq128352 : ∀ (X0 : G) , (old c a sk2) ∨ ¬(old X0 a sk2) := Eq.mp (by simp only [eq128199, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq128351 -- forward demodulation 128351,128199
  have eq128353 (X0 : G) : ¬(old X0 a sk2) := resolve eq128352 p4YZ -- subsumption resolution 128352,147
  have eq128440 : c = sk2 ∨ c = sk3 := resolve eq128353 eq122980 -- resolution 128353,122980
  have eq128442 : c = sk2 := resolve eq128440 eq128200 -- subsumption resolution 128440,128200
  have eq128487 : (old c a a) := Eq.mp (by simp only [eq128442, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq128310 -- backward demodulation 128310,128442
  subsumption p4YZ eq128487 -- subsumption resolution 128487,147

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_9_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (prev_3 : (∀ X0 X1, ¬ new X0 X1 X1 ∨ new X1 X0 X1)) (old_9 : (∀ X0 X1 X2, ¬ old X0 X0 X1 ∨ ¬ old X2 X0 X0 ∨ old X1 X0 X2)) (imp_new_1 : ∀ X Y Z, a ≠ X ∨ b ≠ Y ∨ c ≠ Z ∨ new X Y Z) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), b = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z b a ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b b a ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), b = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), old a a b ∨ ¬sP4 X Y Z) (rule_def_5_0 : ∀ (X Y Z : G), c = X ∨ ¬sP5 X Y Z) (rule_def_5_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP5 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), old a a b ∨ ¬sP5 X Y Z) (rule_def_6_0 : ∀ (X Y Z : G), a = X ∨ ¬sP6 X Y Z) (rule_def_6_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP6 X Y Z) (imp_new_8 : ∀ X Y Z, a ≠ b ∨ c ≠ X ∨ b ≠ Y ∨ ¬ old Z b b ∨ new X Y Z) (rule_def_7_1 : ∀ (X Y Z : G), c = X ∨ ¬sP7 X Y Z) (rule_def_7_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP7 X Y Z) (rule_def_7_3 : ∀ (X Y Z : G), old Z b b ∨ ¬sP7 X Y Z) (imp_new_9 : ∀ X Y Z, b ≠ X ∨ a ≠ Y ∨ c ≠ Z ∨ ¬ old a a b ∨ new X Y Z) (rule_def_8_0 : ∀ (X Y Z : G), b = X ∨ ¬sP8 X Y Z) (rule_def_8_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP8 X Y Z) (rule_def_8_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP8 X Y Z) (rule_def_8_3 : ∀ (X Y Z : G), old a a b ∨ ¬sP8 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2, ¬ new X0 X0 X1 ∨ ¬ new X2 X0 X0 ∨ new X1 X0 X2) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq219 (X0 X1 : G) : (new X0 X1 c) ∨ b ≠ X1 ∨ a ≠ X0 := resolve imp_new_1 rfl -- equality resolution 162
  have eq220 (X0 : G) : (new X0 b c) ∨ a ≠ X0 := resolve eq219 rfl -- equality resolution 219
  have eq221 : (new a b c) := resolve eq220 rfl -- equality resolution 220
  have eq238 (X0 X2 : G) : (new X0 b X2) ∨ ¬(old X2 b b) ∨ c ≠ X0 ∨ a ≠ b := resolve imp_new_8 rfl -- equality resolution 195
  have eq239 (X2 : G) : a ≠ b ∨ ¬(old X2 b b) ∨ (new c b X2) := resolve eq238 rfl -- equality resolution 238
  have eq240 (X0 X1 : G) : (new X0 X1 c) ∨ ¬(old a a b) ∨ a ≠ X1 ∨ b ≠ X0 := resolve imp_new_9 rfl -- equality resolution 200
  have eq241 (X0 : G) : (new X0 a c) ∨ ¬(old a a b) ∨ b ≠ X0 := resolve eq240 rfl -- equality resolution 240
  have eq242 : ¬(old a a b) ∨ (new b a c) := resolve eq241 rfl -- equality resolution 241
  have eq243 : (new sk0 sk2 sk0) := resolve prev_3 preserve_1 -- resolution 210,217
  have eq244 (X0 : G) : ¬(new sk0 sk0 X0) ∨ sk1 = X0 := resolve prev_0 preserve_0 -- resolution 207,216
  have eq293 : (sP8 sk0 sk0 sk1) ∨ (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) := resolve new_imp preserve_0 -- resolution 206,216
  have eq294 : (sP8 sk2 sk0 sk0) ∨ (sP6 sk2 sk0 sk0) ∨ (sP5 sk2 sk0 sk0) ∨ (sP4 sk2 sk0 sk0) ∨ (sP3 sk2 sk0 sk0) ∨ (sP2 sk2 sk0 sk0) ∨ (sP1 sk2 sk0 sk0) ∨ (sP0 sk2 sk0 sk0) ∨ (old sk2 sk0 sk0) ∨ (sP7 sk2 sk0 sk0) := resolve new_imp preserve_1 -- resolution 206,217
  have eq296 : (sP8 sk0 sk2 sk0) ∨ (sP6 sk0 sk2 sk0) ∨ (sP5 sk0 sk2 sk0) ∨ (sP4 sk0 sk2 sk0) ∨ (sP3 sk0 sk2 sk0) ∨ (sP2 sk0 sk2 sk0) ∨ (sP1 sk0 sk2 sk0) ∨ (sP0 sk0 sk2 sk0) ∨ (old sk0 sk2 sk0) ∨ (sP7 sk0 sk2 sk0) := resolve new_imp eq243 -- resolution 206,243
  have eq311 : (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ c = sk1 := resolve eq293 rule_def_8_2 -- resolution 293,203
  have eq312 : (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ a = sk0 := resolve eq293 rule_def_8_1 -- resolution 293,202
  have eq313 : (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ b = sk0 := resolve eq293 rule_def_8_0 -- resolution 293,201
  have eq316 : (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ c = sk1 := resolve eq311 rule_def_3_2 -- subsumption resolution 311,178
  have eq317 : (sP7 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP6 sk0 sk0 sk1) ∨ c = sk1 := resolve eq316 rule_def_0_2 -- subsumption resolution 316,165
  have eq318 : (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ a = sk0 := resolve eq312 rule_def_6_0 -- subsumption resolution 312,191
  have eq319 : (sP4 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ a = sk0 := resolve eq318 rule_def_5_1 -- subsumption resolution 318,187
  have eq320 : (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ a = sk0 := resolve eq319 rule_def_4_0 -- subsumption resolution 319,181
  have eq321 : (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ a = sk0 := resolve eq320 rule_def_3_1 -- subsumption resolution 320,177
  have eq322 : (sP7 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ a = sk0 := resolve eq321 rule_def_0_0 -- subsumption resolution 321,163
  have eq323 : (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 := resolve eq313 rule_def_7_2 -- subsumption resolution 313,198
  have eq324 : (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 := resolve eq323 rule_def_3_0 -- subsumption resolution 323,176
  have eq325 : (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 := resolve eq324 rule_def_2_1 -- subsumption resolution 324,172
  have eq326 : (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 := resolve eq325 rule_def_1_0 -- subsumption resolution 325,167
  have eq327 : (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 := resolve eq326 rule_def_0_1 -- subsumption resolution 326,164
  have eq329 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ a = sk0 ∨ b = sk0 := resolve eq322 rule_def_7_2 -- resolution 322,198
  have eq330 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ a = sk0 ∨ c = sk0 := resolve eq322 rule_def_7_1 -- resolution 322,197
  have eq332 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ a = sk0 ∨ b = sk0 := resolve eq329 rule_def_2_1 -- subsumption resolution 329,172
  have eq333 : (old sk0 sk0 sk1) ∨ a = sk0 ∨ b = sk0 := resolve eq332 rule_def_1_0 -- subsumption resolution 332,167
  have eq334 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ a = sk0 ∨ c = sk0 := resolve eq330 rule_def_2_0 -- subsumption resolution 330,171
  have eq335 : (old sk0 sk0 sk1) ∨ a = sk0 ∨ c = sk0 := resolve eq334 rule_def_1_1 -- subsumption resolution 334,168
  have eq336 : (sP6 sk2 sk0 sk0) ∨ (sP5 sk2 sk0 sk0) ∨ (sP4 sk2 sk0 sk0) ∨ (sP3 sk2 sk0 sk0) ∨ (sP2 sk2 sk0 sk0) ∨ (sP1 sk2 sk0 sk0) ∨ (sP0 sk2 sk0 sk0) ∨ (old sk2 sk0 sk0) ∨ (sP7 sk2 sk0 sk0) ∨ (old a a b) := resolve eq294 rule_def_8_3 -- resolution 294,204
  have eq337 : (sP6 sk2 sk0 sk0) ∨ (sP5 sk2 sk0 sk0) ∨ (sP4 sk2 sk0 sk0) ∨ (sP3 sk2 sk0 sk0) ∨ (sP2 sk2 sk0 sk0) ∨ (sP1 sk2 sk0 sk0) ∨ (sP0 sk2 sk0 sk0) ∨ (old sk2 sk0 sk0) ∨ (sP7 sk2 sk0 sk0) ∨ c = sk0 := resolve eq294 rule_def_8_2 -- resolution 294,203
  have eq340 : (sP6 sk2 sk0 sk0) ∨ (sP5 sk2 sk0 sk0) ∨ (sP3 sk2 sk0 sk0) ∨ (sP2 sk2 sk0 sk0) ∨ (sP1 sk2 sk0 sk0) ∨ (sP0 sk2 sk0 sk0) ∨ (old sk2 sk0 sk0) ∨ (sP7 sk2 sk0 sk0) ∨ (old a a b) := resolve eq336 rule_def_4_3 -- subsumption resolution 336,184
  have eq341 : (sP7 sk2 sk0 sk0) ∨ (sP3 sk2 sk0 sk0) ∨ (sP2 sk2 sk0 sk0) ∨ (sP1 sk2 sk0 sk0) ∨ (sP0 sk2 sk0 sk0) ∨ (old sk2 sk0 sk0) ∨ (sP6 sk2 sk0 sk0) ∨ (old a a b) := resolve eq340 rule_def_5_3 -- subsumption resolution 340,189
  have eq342 : (sP5 sk2 sk0 sk0) ∨ (sP4 sk2 sk0 sk0) ∨ (sP3 sk2 sk0 sk0) ∨ (sP2 sk2 sk0 sk0) ∨ (sP1 sk2 sk0 sk0) ∨ (sP0 sk2 sk0 sk0) ∨ (old sk2 sk0 sk0) ∨ (sP7 sk2 sk0 sk0) ∨ c = sk0 := resolve eq337 rule_def_6_1 -- subsumption resolution 337,192
  have eq343 : (sP5 sk2 sk0 sk0) ∨ (sP3 sk2 sk0 sk0) ∨ (sP2 sk2 sk0 sk0) ∨ (sP1 sk2 sk0 sk0) ∨ (sP0 sk2 sk0 sk0) ∨ (old sk2 sk0 sk0) ∨ (sP7 sk2 sk0 sk0) ∨ c = sk0 := resolve eq342 rule_def_4_1 -- subsumption resolution 342,182
  have eq344 : (sP5 sk2 sk0 sk0) ∨ (sP2 sk2 sk0 sk0) ∨ (sP1 sk2 sk0 sk0) ∨ (sP0 sk2 sk0 sk0) ∨ (old sk2 sk0 sk0) ∨ (sP7 sk2 sk0 sk0) ∨ c = sk0 := resolve eq343 rule_def_3_2 -- subsumption resolution 343,178
  have eq345 : (sP5 sk2 sk0 sk0) ∨ (sP2 sk2 sk0 sk0) ∨ (sP0 sk2 sk0 sk0) ∨ (old sk2 sk0 sk0) ∨ (sP7 sk2 sk0 sk0) ∨ c = sk0 := resolve eq344 rule_def_1_1 -- subsumption resolution 344,168
  have eq346 : (sP7 sk2 sk0 sk0) ∨ (sP2 sk2 sk0 sk0) ∨ (old sk2 sk0 sk0) ∨ (sP5 sk2 sk0 sk0) ∨ c = sk0 := resolve eq345 rule_def_0_2 -- subsumption resolution 345,165
  have eq364 : (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 ∨ c = sk0 := resolve eq327 rule_def_6_1 -- resolution 327,192
  have eq366 : (sP4 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 ∨ c = sk0 := resolve eq364 rule_def_5_0 -- subsumption resolution 364,186
  have eq367 : (old sk0 sk0 sk1) ∨ b = sk0 ∨ c = sk0 := resolve eq366 rule_def_4_1 -- subsumption resolution 366,182
  have eq378 : (sP5 sk2 sk0 sk0) ∨ (old sk2 sk0 sk0) ∨ (sP2 sk2 sk0 sk0) ∨ c = sk0 ∨ (old sk0 b b) := resolve eq346 rule_def_7_3 -- resolution 346,199
  have eq379 : (sP2 sk2 sk0 sk0) ∨ (old sk2 sk0 sk0) ∨ (sP5 sk2 sk0 sk0) ∨ c = sk0 ∨ b = sk0 := resolve eq346 rule_def_7_2 -- resolution 346,198
  have eq380 : (sP2 sk2 sk0 sk0) ∨ (old sk2 sk0 sk0) ∨ (sP5 sk2 sk0 sk0) ∨ c = sk0 ∨ c = sk2 := resolve eq346 rule_def_7_1 -- resolution 346,197
  have eq382 : (sP5 sk2 sk0 sk0) ∨ (old sk2 sk0 sk0) ∨ c = sk0 ∨ b = sk0 := resolve eq379 rule_def_2_2 -- subsumption resolution 379,173
  have eq383 : (sP2 sk2 sk0 sk0) ∨ (old sk2 sk0 sk0) ∨ c = sk0 ∨ c = sk2 := resolve eq380 rule_def_5_0 -- subsumption resolution 380,186
  have eq384 : (old sk2 sk0 sk0) ∨ c = sk0 ∨ c = sk2 := resolve eq383 rule_def_2_0 -- subsumption resolution 383,171
  have eq400 (X0 : G) : ¬(old sk0 sk0 X0) ∨ c = sk2 ∨ (old X0 sk0 sk2) ∨ c = sk0 := resolve eq384 old_9 -- resolution 384,159
  have eq440 : (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP6 sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := resolve eq317 rule_def_7_1 -- resolution 317,197
  have eq442 : (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := resolve eq440 rule_def_6_1 -- subsumption resolution 440,192
  have eq443 : (sP4 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := resolve eq442 rule_def_5_0 -- subsumption resolution 442,186
  have eq444 : (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := resolve eq443 rule_def_4_1 -- subsumption resolution 443,182
  have eq445 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := resolve eq444 rule_def_2_0 -- subsumption resolution 444,171
  have eq446 : (old sk0 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := resolve eq445 rule_def_1_1 -- subsumption resolution 445,168
  have eq492 : (sP6 sk2 sk0 sk0) ∨ (sP2 sk2 sk0 sk0) ∨ (sP1 sk2 sk0 sk0) ∨ (sP0 sk2 sk0 sk0) ∨ (old sk2 sk0 sk0) ∨ (sP3 sk2 sk0 sk0) ∨ (old a a b) ∨ (old sk0 b b) := resolve eq341 rule_def_7_3 -- resolution 341,199
  have eq622 : (sP2 sk2 sk0 sk0) ∨ (old sk2 sk0 sk0) ∨ c = sk0 ∨ (old sk0 b b) ∨ (old a a b) := resolve eq378 rule_def_5_3 -- resolution 378,189
  have eq809 : c = sk2 ∨ (old sk1 sk0 sk2) ∨ c = sk0 ∨ c = sk1 ∨ c = sk0 := resolve eq400 eq446 -- resolution 400,446
  have eq810 : c = sk2 ∨ (old sk1 sk0 sk2) ∨ c = sk0 ∨ b = sk0 ∨ c = sk0 := resolve eq400 eq367 -- resolution 400,367
  have eq811 : c = sk2 ∨ (old sk1 sk0 sk2) ∨ c = sk0 ∨ a = sk0 ∨ c = sk0 := resolve eq400 eq335 -- resolution 400,335
  have eq813 : (old sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ a = sk0 := resolve eq811 rfl -- duplicate literal removal 811
  have eq814 : (old sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ b = sk0 := resolve eq810 rfl -- duplicate literal removal 810
  have eq815 : (old sk1 sk0 sk2) ∨ c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq809 rfl -- duplicate literal removal 809
  have eq833 : c = sk2 ∨ c = sk0 ∨ a = sk0 ∨ (new sk1 sk0 sk2) := resolve eq813 imp_new_0 -- resolution 813,161
  have eq837 : c = sk2 ∨ c = sk0 ∨ a = sk0 := resolve eq833 preserve_2 -- subsumption resolution 833,218
  have eq845 : ¬(new sk1 sk0 c) ∨ c = sk0 ∨ a = sk0 := eq837.imp_left (fun h : c = sk2 ↦ superpose h preserve_2) -- superposition 218,837, 837 into 218, unify on (0).2 in 837 and (0).3 in 218
  have eq858 : (sP8 sk0 c sk0) ∨ (sP6 sk0 c sk0) ∨ (sP5 sk0 c sk0) ∨ (sP4 sk0 c sk0) ∨ (sP3 sk0 c sk0) ∨ (sP2 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP0 sk0 c sk0) ∨ (old sk0 c sk0) ∨ (sP7 sk0 c sk0) ∨ c = sk0 ∨ a = sk0 := Or.assoc10 (eq837.imp_left (fun h : c = sk2 ↦ superpose h eq296)) -- superposition 296,837, 837 into 296, unify on (0).2 in 837 and (0).2 in 296
  have eq865 : (sP5 c sk0 sk0) ∨ (old c sk0 sk0) ∨ c = sk0 ∨ b = sk0 ∨ c = sk0 ∨ a = sk0 := Or.assoc4 (eq837.imp_left (fun h : c = sk2 ↦ superpose h eq382)) -- superposition 382,837, 837 into 382, unify on (0).2 in 837 and (0).1 in 382
  have eq887 : (sP5 c sk0 sk0) ∨ (old c sk0 sk0) ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := resolve eq865 rfl -- duplicate literal removal 865
  have eq901 : (sP8 sk0 c sk0) ∨ (sP6 sk0 c sk0) ∨ (sP5 sk0 c sk0) ∨ (sP4 sk0 c sk0) ∨ (sP3 sk0 c sk0) ∨ (sP2 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP0 sk0 c sk0) ∨ (sP7 sk0 c sk0) ∨ c = sk0 ∨ a = sk0 := resolve eq858 p4XZ -- subsumption resolution 858,148
  have eq902 : (sP8 sk0 c sk0) ∨ (sP5 sk0 c sk0) ∨ (sP4 sk0 c sk0) ∨ (sP3 sk0 c sk0) ∨ (sP2 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP0 sk0 c sk0) ∨ (sP7 sk0 c sk0) ∨ c = sk0 ∨ a = sk0 := resolve eq901 rule_def_6_0 -- subsumption resolution 901,191
  have eq903 : (sP8 sk0 c sk0) ∨ (sP4 sk0 c sk0) ∨ (sP3 sk0 c sk0) ∨ (sP2 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP0 sk0 c sk0) ∨ (sP7 sk0 c sk0) ∨ c = sk0 ∨ a = sk0 := resolve eq902 rule_def_5_2 -- subsumption resolution 902,188
  have eq904 : (sP8 sk0 c sk0) ∨ (sP3 sk0 c sk0) ∨ (sP2 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP0 sk0 c sk0) ∨ (sP7 sk0 c sk0) ∨ c = sk0 ∨ a = sk0 := resolve eq903 rule_def_4_2 -- subsumption resolution 903,183
  have eq905 : (sP8 sk0 c sk0) ∨ (sP3 sk0 c sk0) ∨ (sP2 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP7 sk0 c sk0) ∨ c = sk0 ∨ a = sk0 := resolve eq904 rule_def_0_0 -- subsumption resolution 904,163
  have eq906 : (sP3 sk0 c sk0) ∨ (sP2 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ (sP7 sk0 c sk0) ∨ c = sk0 ∨ a = sk0 := resolve eq905 rule_def_8_2 -- subsumption resolution 905,203
  have eq907 : (sP3 sk0 c sk0) ∨ (sP2 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ c = sk0 ∨ a = sk0 := resolve eq906 rule_def_7_1 -- subsumption resolution 906,197
  have eq908 : (sP2 sk0 c sk0) ∨ (sP1 sk0 c sk0) ∨ c = sk0 ∨ a = sk0 := resolve eq907 rule_def_3_2 -- subsumption resolution 907,178
  have eq909 : (sP1 sk0 c sk0) ∨ c = sk0 ∨ a = sk0 := resolve eq908 rule_def_2_0 -- subsumption resolution 908,171
  have eq914 : (sP5 c sk0 sk0) ∨ c = sk0 ∨ b = sk0 ∨ a = sk0 := resolve eq887 p4YZ -- subsumption resolution 887,149
  have eq915 : b = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq914 rule_def_5_2 -- subsumption resolution 914,188
  have eq928 (X0 : G) : ¬(new b b X0) ∨ sk1 = X0 ∨ c = sk0 ∨ a = sk0 := Or.assoc2 (eq915.imp_left (fun h : b = sk0 ↦ superpose h eq244)) -- superposition 244,915, 915 into 244, unify on (0).2 in 915 and (0).1 in 244
  have eq997 : a ≠ b ∨ c = sk0 ∨ a = sk0 := resolve eq915 trans_resol -- equality factoring 915
  have eq1066 : ¬(new sk1 b c) ∨ c = b ∨ a = b ∨ c = sk0 ∨ a = sk0 := Or.assoc3 (eq915.imp_left (fun h : b = sk0 ↦ superpose h eq845)) -- superposition 845,915, 915 into 845, unify on (0).2 in 915 and (0).2 in 845
  have eq1067 : ¬(new sk1 b c) ∨ a = b ∨ c = sk0 ∨ a = sk0 := resolve eq1066 bc -- subsumption resolution 1066,145
  have eq1068 : ¬(new sk1 b c) ∨ c = sk0 ∨ a = sk0 := resolve eq1067 eq997 -- subsumption resolution 1067,997
  have eq1108 : (old sk0 b a) ∨ a = sk0 ∨ c = sk0 := resolve eq909 rule_def_1_2 -- resolution 909,169
  have eq1322 : (new sk0 b a) ∨ c = sk0 ∨ a = sk0 := resolve eq1108 imp_new_0 -- resolution 1108,161
  have eq1363 : (new b b a) ∨ c = b ∨ a = b ∨ c = sk0 ∨ a = sk0 := Or.assoc3 (eq915.imp_left (fun h : b = sk0 ↦ superpose h eq1322)) -- superposition 1322,915, 915 into 1322, unify on (0).2 in 915 and (0).1 in 1322
  have eq1364 : (new b b a) ∨ a = b ∨ c = sk0 ∨ a = sk0 := resolve eq1363 bc -- subsumption resolution 1363,145
  have eq1365 : (new b b a) ∨ c = sk0 ∨ a = sk0 := resolve eq1364 eq997 -- subsumption resolution 1364,997
  have eq1433 : c = sk2 ∨ c = sk0 ∨ b = sk0 ∨ (new sk1 sk0 sk2) := resolve eq814 imp_new_0 -- resolution 814,161
  have eq1439 : c = sk2 ∨ c = sk0 ∨ b = sk0 := resolve eq1433 preserve_2 -- subsumption resolution 1433,218
  have eq1446 : ¬(new sk1 sk0 c) ∨ c = sk0 ∨ b = sk0 := eq1439.imp_left (fun h : c = sk2 ↦ superpose h preserve_2) -- superposition 218,1439, 1439 into 218, unify on (0).2 in 1439 and (0).3 in 218
  have eq1461 : (sP7 c sk0 sk0) ∨ (sP3 c sk0 sk0) ∨ (sP2 c sk0 sk0) ∨ (sP1 c sk0 sk0) ∨ (sP0 c sk0 sk0) ∨ (old c sk0 sk0) ∨ (sP6 c sk0 sk0) ∨ (old a a b) ∨ c = sk0 ∨ b = sk0 := Or.assoc8 (eq1439.imp_left (fun h : c = sk2 ↦ superpose h eq341)) -- superposition 341,1439, 1439 into 341, unify on (0).2 in 1439 and (0).1 in 341
  have eq1545 : (sP7 c sk0 sk0) ∨ (sP3 c sk0 sk0) ∨ (sP2 c sk0 sk0) ∨ (sP1 c sk0 sk0) ∨ (sP0 c sk0 sk0) ∨ (sP6 c sk0 sk0) ∨ (old a a b) ∨ c = sk0 ∨ b = sk0 := resolve eq1461 p4YZ -- subsumption resolution 1461,149
  have eq1546 : (sP3 c sk0 sk0) ∨ (sP2 c sk0 sk0) ∨ (sP1 c sk0 sk0) ∨ (sP0 c sk0 sk0) ∨ (sP6 c sk0 sk0) ∨ (old a a b) ∨ c = sk0 ∨ b = sk0 := resolve eq1545 rule_def_7_2 -- subsumption resolution 1545,198
  have eq1547 : (sP3 c sk0 sk0) ∨ (sP1 c sk0 sk0) ∨ (sP0 c sk0 sk0) ∨ (sP6 c sk0 sk0) ∨ (old a a b) ∨ c = sk0 ∨ b = sk0 := resolve eq1546 rule_def_2_2 -- subsumption resolution 1546,173
  have eq1548 : (sP3 c sk0 sk0) ∨ (sP1 c sk0 sk0) ∨ (sP6 c sk0 sk0) ∨ (old a a b) ∨ c = sk0 ∨ b = sk0 := resolve eq1547 rule_def_0_1 -- subsumption resolution 1547,164
  have eq1549 : (sP3 c sk0 sk0) ∨ (sP1 c sk0 sk0) ∨ (old a a b) ∨ c = sk0 ∨ b = sk0 := resolve eq1548 rule_def_6_1 -- subsumption resolution 1548,192
  have eq1550 : (sP1 c sk0 sk0) ∨ (old a a b) ∨ c = sk0 ∨ b = sk0 := resolve eq1549 rule_def_3_2 -- subsumption resolution 1549,178
  have eq1551 : (old a a b) ∨ c = sk0 ∨ b = sk0 := resolve eq1550 rule_def_1_1 -- subsumption resolution 1550,168
  have eq1635 : (new b a c) ∨ b = sk0 ∨ c = sk0 := resolve eq1551 eq242 -- resolution 1551,242
  have eq1647 : (new a a b) ∨ b = sk0 ∨ c = sk0 := resolve eq1551 imp_new_0 -- resolution 1551,161
  have eq1748 : c = sk2 ∨ c = sk0 ∨ c = sk1 ∨ (new sk1 sk0 sk2) := resolve eq815 imp_new_0 -- resolution 815,161
  have eq1754 : c = sk2 ∨ c = sk0 ∨ c = sk1 := resolve eq1748 preserve_2 -- subsumption resolution 1748,218
  have eq1788 : (sP6 c sk0 sk0) ∨ (sP2 c sk0 sk0) ∨ (sP1 c sk0 sk0) ∨ (sP0 c sk0 sk0) ∨ (old c sk0 sk0) ∨ (sP3 c sk0 sk0) ∨ (old a a b) ∨ (old sk0 b b) ∨ c = sk0 ∨ c = sk1 := Or.assoc8 (eq1754.imp_left (fun h : c = sk2 ↦ superpose h eq492)) -- superposition 492,1754, 1754 into 492, unify on (0).2 in 1754 and (0).1 in 492
  have eq1870 : (sP6 c sk0 sk0) ∨ (sP2 c sk0 sk0) ∨ (sP1 c sk0 sk0) ∨ (sP0 c sk0 sk0) ∨ (sP3 c sk0 sk0) ∨ (old a a b) ∨ (old sk0 b b) ∨ c = sk0 ∨ c = sk1 := resolve eq1788 p4YZ -- subsumption resolution 1788,149
  have eq1871 : (sP2 c sk0 sk0) ∨ (sP1 c sk0 sk0) ∨ (sP0 c sk0 sk0) ∨ (sP3 c sk0 sk0) ∨ (old a a b) ∨ (old sk0 b b) ∨ c = sk0 ∨ c = sk1 := resolve eq1870 rule_def_6_1 -- subsumption resolution 1870,192
  have eq1872 : (sP2 c sk0 sk0) ∨ (sP1 c sk0 sk0) ∨ (sP0 c sk0 sk0) ∨ (old a a b) ∨ (old sk0 b b) ∨ c = sk0 ∨ c = sk1 := resolve eq1871 rule_def_3_2 -- subsumption resolution 1871,178
  have eq1873 : (sP2 c sk0 sk0) ∨ (sP0 c sk0 sk0) ∨ (old a a b) ∨ (old sk0 b b) ∨ c = sk0 ∨ c = sk1 := resolve eq1872 rule_def_1_1 -- subsumption resolution 1872,168
  have eq1874 : (sP2 c sk0 sk0) ∨ (old a a b) ∨ (old sk0 b b) ∨ c = sk0 ∨ c = sk1 := resolve eq1873 rule_def_0_2 -- subsumption resolution 1873,165
  have eq2242 : a = sk1 ∨ c = sk0 ∨ a = sk0 ∨ c = sk0 ∨ a = sk0 := resolve eq928 eq1365 -- resolution 928,1365
  have eq2243 : a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq2242 rfl -- duplicate literal removal 2242
  have eq2322 : ¬(new a b c) ∨ c = sk0 ∨ a = sk0 ∨ c = sk0 ∨ a = sk0 := Or.assoc3 (eq2243.imp_left (fun h : a = sk1 ↦ superpose h eq1068)) -- superposition 1068,2243, 2243 into 1068, unify on (0).2 in 2243 and (0).1 in 1068
  have eq2339 : ¬(new a b c) ∨ c = sk0 ∨ a = sk0 := resolve eq2322 rfl -- duplicate literal removal 2322
  have eq2394 : c = sk0 ∨ a = sk0 := resolve eq2339 eq221 -- subsumption resolution 2339,221
  have eq2437 : (old c c sk1) ∨ a = c ∨ c = b ∨ a = sk0 := Or.assoc3 (eq2394.imp_left (fun h : c = sk0 ↦ superpose h eq333)) -- superposition 333,2394, 2394 into 333, unify on (0).2 in 2394 and (0).1 in 333
  have eq2528 : a = c ∨ c = b ∨ a = sk0 := resolve eq2437 p4YZ -- subsumption resolution 2437,149
  have eq2529 : c = b ∨ a = sk0 := resolve eq2528 ac -- subsumption resolution 2528,144
  have eq2530 : a = sk0 := resolve eq2529 bc -- subsumption resolution 2529,145
  have eq2533 : ¬(new sk1 a sk2) := Eq.mp (by simp only [eq2530, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_2 -- backward demodulation 218,2530
  have eq2535 : ∀ (X0 : G) , ¬(new a a X0) ∨ sk1 = X0 := Eq.mp (by simp only [eq2530, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq244 -- backward demodulation 244,2530
  have eq2644 : (sP2 sk2 a a) ∨ (old sk2 sk0 sk0) ∨ c = sk0 ∨ (old sk0 b b) ∨ (old a a b) := Eq.mp (by simp only [eq2530, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq622 -- backward demodulation 622,2530
  have eq2805 : a = b ∨ ¬(new sk1 sk0 c) ∨ c = sk0 := Eq.mp (by simp only [eq2530, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1446 -- backward demodulation 1446,2530
  have eq2832 : a = b ∨ (new b a c) ∨ c = sk0 := Eq.mp (by simp only [eq2530, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1635 -- backward demodulation 1635,2530
  have eq2838 : a = b ∨ (new a a b) ∨ c = sk0 := Eq.mp (by simp only [eq2530, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1647 -- backward demodulation 1647,2530
  have eq2898 : a = c ∨ (sP2 c sk0 sk0) ∨ (old a a b) ∨ (old sk0 b b) ∨ c = sk1 := Eq.mp (by simp only [eq2530, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1874 -- backward demodulation 1874,2530
  have eq3255 : (old sk2 a a) ∨ (sP2 sk2 a a) ∨ c = sk0 ∨ (old sk0 b b) ∨ (old a a b) := Eq.mp (by simp only [eq2530, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2644 -- forward demodulation 2644,2530
  have eq3256 : a = c ∨ (old sk2 a a) ∨ (sP2 sk2 a a) ∨ (old sk0 b b) ∨ (old a a b) := Eq.mp (by simp only [eq2530, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3255 -- forward demodulation 3255,2530
  have eq3257 : (old sk2 a a) ∨ (sP2 sk2 a a) ∨ (old sk0 b b) ∨ (old a a b) := resolve eq3256 ac -- subsumption resolution 3256,144
  have eq3258 : (old a b b) ∨ (old sk2 a a) ∨ (sP2 sk2 a a) ∨ (old a a b) := Eq.mp (by simp only [eq2530, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3257 -- forward demodulation 3257,2530
  have eq3259 : (old sk2 a a) ∨ (sP2 sk2 a a) ∨ (old a a b) := resolve eq3258 p3 -- subsumption resolution 3258,146
  have eq3597 : ¬(new sk1 a c) ∨ a = b ∨ c = sk0 := Eq.mp (by simp only [eq2530, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2805 -- forward demodulation 2805,2530
  have eq3598 : a = c ∨ ¬(new sk1 a c) ∨ a = b := Eq.mp (by simp only [eq2530, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3597 -- forward demodulation 3597,2530
  have eq3599 : ¬(new sk1 a c) ∨ a = b := resolve eq3598 ac -- subsumption resolution 3598,144
  have eq3685 : a = c ∨ a = b ∨ (new b a c) := Eq.mp (by simp only [eq2530, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2832 -- forward demodulation 2832,2530
  have eq3686 : (new b a c) ∨ a = b := resolve eq3685 ac -- subsumption resolution 3685,144
  have eq3693 : a = c ∨ a = b ∨ (new a a b) := Eq.mp (by simp only [eq2530, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2838 -- forward demodulation 2838,2530
  have eq3694 : (new a a b) ∨ a = b := resolve eq3693 ac -- subsumption resolution 3693,144
  have eq3797 : (sP2 c sk0 sk0) ∨ (old a a b) ∨ (old sk0 b b) ∨ c = sk1 := resolve eq2898 ac -- subsumption resolution 2898,144
  have eq3798 : (sP2 c a a) ∨ (old a a b) ∨ (old sk0 b b) ∨ c = sk1 := Eq.mp (by simp only [eq2530, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3797 -- forward demodulation 3797,2530
  have eq3799 : (old a b b) ∨ (sP2 c a a) ∨ (old a a b) ∨ c = sk1 := Eq.mp (by simp only [eq2530, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3798 -- forward demodulation 3798,2530
  have eq3800 : (sP2 c a a) ∨ (old a a b) ∨ c = sk1 := resolve eq3799 p3 -- subsumption resolution 3799,146
  have eq4113 : b = sk1 ∨ a = b := resolve eq3694 eq2535 -- resolution 3694,2535
  have eq4145 : ¬(new b a c) ∨ a = b ∨ a = b := Or.assoc2 (eq4113.imp_left (fun h : b = sk1 ↦ superpose h eq3599)) -- superposition 3599,4113, 4113 into 3599, unify on (0).2 in 4113 and (0).1 in 3599
  have eq4150 : ¬(new b a c) ∨ a = b := resolve eq4145 rfl -- duplicate literal removal 4145
  have eq4155 : a = b := resolve eq4150 eq3686 -- subsumption resolution 4150,3686
  have eq4157 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq4155, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 146,4155
  have eq4163 : ∀ (X0 X1 X2 : G) , (old a a a) ∨ ¬(sP2 X0 X1 X2) := Eq.mp (by simp only [eq4155, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_2_3 -- backward demodulation 174,4155
  have eq4181 : ∀ (X2 : G) , a ≠ a ∨ ¬(old X2 b b) ∨ (new c b X2) := Eq.mp (by simp only [eq4155, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq239 -- backward demodulation 239,4155
  have eq4207 : (old a a a) ∨ (old sk2 a a) ∨ (sP2 sk2 a a) := Eq.mp (by simp only [eq4155, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3259 -- backward demodulation 3259,4155
  have eq4233 : (old a a a) ∨ (sP2 c a a) ∨ c = sk1 := Eq.mp (by simp only [eq4155, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3800 -- backward demodulation 3800,4155
  have eq4238 (X2 : G) : ¬(old X2 b b) ∨ (new c b X2) := resolve eq4181 rfl -- trivial inequality removal 4181
  have eq4239 (X0 X1 X2 : G) : ¬(sP2 X0 X1 X2) := resolve eq4163 eq4157 -- subsumption resolution 4163,4157
  have eq4246 : ∀ (X2 : G) , ¬(old X2 a a) ∨ (new c b X2) := Eq.mp (by simp only [eq4155, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4238 -- forward demodulation 4238,4155
  have eq4247 : ∀ (X2 : G) , ¬(old X2 a a) ∨ (new c a X2) := Eq.mp (by simp only [eq4155, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq4246 -- forward demodulation 4246,4155
  have eq4305 : (old sk2 a a) ∨ (sP2 sk2 a a) := resolve eq4207 eq4157 -- subsumption resolution 4207,4157
  have eq4306 : (old sk2 a a) := resolve eq4305 eq4239 -- subsumption resolution 4305,4239
  have eq4314 : (sP2 c a a) ∨ c = sk1 := resolve eq4233 eq4157 -- subsumption resolution 4233,4157
  have eq4315 : c = sk1 := resolve eq4314 eq4239 -- subsumption resolution 4314,4239
  have eq4317 : ¬(new c a sk2) := Eq.mp (by simp only [eq4315, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2533 -- backward demodulation 2533,4315
  have eq4440 : (new c a sk2) := resolve eq4247 eq4306 -- resolution 4247,4306
  subsumption eq4317 eq4440 -- subsumption resolution 4440,4317

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_10_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (prev_6 : (∀ X0 X1 X2, ¬ new X0 X0 X1 ∨ ¬ new X0 X1 X2 ∨ new X2 X0 X0)) (prev_9 : (∀ X0 X1 X2, ¬ new X0 X0 X1 ∨ ¬ new X2 X0 X0 ∨ new X1 X0 X2)) : (∀ X0 X1 X2, ¬ new X0 X0 X1 ∨ ¬ new X0 X1 X2 ∨ new X1 X0 X2) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq276 : (new sk2 sk0 sk0) ∨ ¬(new sk0 sk0 sk1) := resolve prev_6 preserve_1 -- resolution 215,220
  have eq279 : (new sk2 sk0 sk0) := resolve eq276 preserve_0 -- subsumption resolution 276,219
  have eq288 (X0 : G) : ¬(new sk0 sk0 X0) ∨ (new X0 sk0 sk2) := resolve prev_9 eq279 -- resolution 218,279
  have eq345 : (new sk1 sk0 sk2) := resolve eq288 preserve_0 -- resolution 288,219
  subsumption preserve_2 eq345 -- subsumption resolution 345,221

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (memold : G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), b = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z b a ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b b a ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), b = X ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b b a ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), old a a b ∨ ¬sP4 X Y Z) (rule_def_5_0 : ∀ (X Y Z : G), c = X ∨ ¬sP5 X Y Z) (rule_def_5_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), old a a b ∨ ¬sP5 X Y Z) (rule_def_6_0 : ∀ (X Y Z : G), a = X ∨ ¬sP6 X Y Z) (rule_def_6_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP6 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), old b b a ∨ ¬sP6 X Y Z) (rule_def_7_1 : ∀ (X Y Z : G), c = X ∨ ¬sP7 X Y Z) (rule_def_7_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP7 X Y Z) (rule_def_8_0 : ∀ (X Y Z : G), b = X ∨ ¬sP8 X Y Z) (rule_def_8_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP8 X Y Z) (rule_def_8_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP8 X Y Z) (rule_def_8_3 : ∀ (X Y Z : G), old a a b ∨ ¬sP8 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z) (old_mem1 : ∀ (X Y Z), ¬old X Y Z ∨ memold X) : ∀ (X Y Z : G), ¬new X Y Z ∨ X = a ∨ X = b ∨ memold X ∨ X = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq229 : (sP8 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 196,200
  have eq242 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (old a a b) := resolve eq229 rule_def_8_3 -- resolution 229,194
  have eq243 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ c = sk2 := resolve eq229 rule_def_8_2 -- resolution 229,193
  have eq244 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ a = sk1 := resolve eq229 rule_def_8_1 -- resolution 229,192
  have eq245 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ b = sk0 := resolve eq229 rule_def_8_0 -- resolution 229,191
  have eq246 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (old a a b) := resolve eq242 rule_def_4_3 -- subsumption resolution 242,174
  have eq247 : (sP7 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (old a a b) := resolve eq246 rule_def_5_3 -- subsumption resolution 246,179
  have eq248 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ c = sk2 := resolve eq243 rule_def_3_2 -- subsumption resolution 243,168
  have eq249 : (sP7 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ c = sk2 := resolve eq248 rule_def_0_2 -- subsumption resolution 248,155
  have eq250 : (sP6 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ a = sk1 := resolve eq244 rule_def_5_1 -- subsumption resolution 244,177
  have eq251 : (sP7 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ a = sk1 := resolve eq250 rule_def_3_1 -- subsumption resolution 250,167
  have eq252 : (sP7 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) := resolve eq245 preserve_2 -- subsumption resolution 245,202
  have eq270 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk0 := resolve eq249 rule_def_7_1 -- resolution 249,187
  have eq273 : (sP6 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ c = sk2 := resolve eq270 preserve_4 -- subsumption resolution 270,204
  have eq280 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 := resolve eq251 rule_def_7_2 -- resolution 251,188
  have eq281 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ a = sk1 ∨ c = sk0 := resolve eq251 rule_def_7_1 -- resolution 251,187
  have eq283 : (sP4 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 := resolve eq280 rule_def_2_1 -- subsumption resolution 280,162
  have eq284 : (sP6 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 := resolve eq283 rule_def_0_1 -- subsumption resolution 283,154
  have eq285 : (sP6 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk1 := resolve eq281 preserve_4 -- subsumption resolution 281,204
  have eq291 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (old a a b) ∨ c = sk0 := resolve eq247 rule_def_7_1 -- resolution 247,187
  have eq295 : (sP6 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (old a a b) := resolve eq291 preserve_4 -- subsumption resolution 291,204
  have eq300 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ b = sk1 := resolve eq252 rule_def_7_2 -- resolution 252,188
  have eq303 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ b = sk1 := resolve eq300 rule_def_2_1 -- subsumption resolution 300,162
  have eq304 : (sP6 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ b = sk1 := resolve eq303 rule_def_0_1 -- subsumption resolution 303,154
  have eq313 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ a = sk0 := resolve eq284 rule_def_6_0 -- resolution 284,181
  have eq316 : (sP4 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 := resolve eq313 preserve_1 -- subsumption resolution 313,201
  have eq361 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq273 rule_def_6_1 -- resolution 273,182
  have eq365 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq361 rule_def_4_1 -- subsumption resolution 361,172
  have eq366 : (sP5 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq365 rule_def_1_1 -- subsumption resolution 365,158
  have eq372 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk1 ∨ c = sk1 := resolve eq285 rule_def_6_1 -- resolution 285,182
  have eq376 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ c = sk1 := resolve eq372 rule_def_4_1 -- subsumption resolution 372,172
  have eq377 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ c = sk1 := resolve eq376 rule_def_1_1 -- subsumption resolution 376,158
  have eq383 : (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := resolve eq304 rule_def_6_1 -- resolution 304,182
  have eq386 : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := resolve eq383 rule_def_4_1 -- subsumption resolution 383,172
  have eq387 : (sP5 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := resolve eq386 rule_def_1_1 -- subsumption resolution 386,158
  have eq395 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (old a a b) ∨ (old b b a) := resolve eq295 rule_def_6_2 -- resolution 295,183
  have eq399 : (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (old a a b) ∨ (old b b a) := resolve eq395 rule_def_2_3 -- subsumption resolution 395,164
  have eq400 : (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (old a a b) ∨ (old b b a) := resolve eq399 rule_def_3_3 -- subsumption resolution 399,169
  have eq519 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ a = sk0 := resolve eq316 rule_def_4_0 -- resolution 316,171
  have eq522 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 := resolve eq519 preserve_1 -- subsumption resolution 519,201
  have eq534 : (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq366 rule_def_5_0 -- resolution 366,176
  have eq536 : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq534 preserve_4 -- subsumption resolution 534,204
  have eq543 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq377 rule_def_2_0 -- resolution 377,161
  have eq547 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk1 ∨ c = sk1 := resolve eq543 preserve_4 -- subsumption resolution 543,204
  have eq555 : (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ c = sk0 := resolve eq387 rule_def_5_0 -- resolution 387,176
  have eq558 : (sP3 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := resolve eq555 preserve_4 -- subsumption resolution 555,204
  have eq575 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (old a a b) ∨ (old b b a) ∨ (old sk2 b a) := resolve eq400 rule_def_1_2 -- resolution 400,159
  have eq590 : (old sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 ∨ b = sk0 := resolve eq522 rule_def_1_0 -- resolution 522,157
  have eq593 : (old sk0 sk1 sk2) ∨ a = sk1 ∨ b = sk1 := resolve eq590 preserve_2 -- subsumption resolution 590,202
  have eq611 : a = sk1 ∨ b = sk1 ∨ memold sk0 := resolve eq593 old_mem1 -- resolution 593,197
  have eq618 : b = sk1 ∨ a = sk1 := resolve eq611 preserve_3 -- subsumption resolution 611,203
  have eq642 : a ≠ b ∨ a = sk1 := resolve eq618 trans_resol -- equality factoring 618
  have eq704 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 ∨ c = sk0 := resolve eq536 rule_def_2_0 -- resolution 536,161
  have eq707 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq704 preserve_4 -- subsumption resolution 704,204
  have eq730 : c = sk2 ∨ c = sk1 ∨ memold sk0 := resolve eq707 old_mem1 -- resolution 707,197
  have eq737 : c = sk2 ∨ c = sk1 := resolve eq730 preserve_3 -- subsumption resolution 730,203
  have eq1074 : (old sk0 sk1 sk2) ∨ a = sk1 ∨ c = sk1 ∨ a = sk0 := resolve eq547 rule_def_0_0 -- resolution 547,153
  have eq1083 : (old sk0 sk1 sk2) ∨ a = sk1 ∨ c = sk1 := resolve eq1074 preserve_1 -- subsumption resolution 1074,201
  have eq1111 : a = sk1 ∨ c = sk1 ∨ memold sk0 := resolve eq1083 old_mem1 -- resolution 1083,197
  have eq1128 : c = sk1 ∨ a = sk1 := resolve eq1111 preserve_3 -- subsumption resolution 1111,203
  have eq1134 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 ∨ b = sk0 := resolve eq558 rule_def_3_0 -- resolution 558,166
  have eq1140 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ c = sk1 := resolve eq1134 preserve_2 -- subsumption resolution 1134,202
  have eq1142 : c = b ∨ a = b ∨ a = sk1 := Or.assoc2 (eq618.imp_left (fun h : b = sk1 ↦ superpose h eq1128)) -- superposition 1128,618, 618 into 1128, unify on (0).2 in 618 and (0).2 in 1128
  have eq1193 : a = b ∨ a = sk1 := resolve eq1142 bc -- subsumption resolution 1142,135
  have eq1194 : a = sk1 := resolve eq1193 eq642 -- subsumption resolution 1193,642
  have eq1292 : (sP0 sk0 a sk2) ∨ (old sk0 sk1 sk2) ∨ (old a a b) ∨ (old b b a) ∨ (old sk2 b a) := Eq.mp (by simp only [eq1194, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq575 -- backward demodulation 575,1194
  have eq1323 : a = c ∨ c = sk2 := Eq.mp (by simp only [eq1194, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq737 -- backward demodulation 737,1194
  have eq1347 : (old sk0 a sk2) ∨ b = sk1 ∨ c = sk1 := Eq.mp (by simp only [eq1194, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1140 -- backward demodulation 1140,1194
  have eq1645 : (old sk0 a sk2) ∨ (sP0 sk0 a sk2) ∨ (old a a b) ∨ (old b b a) ∨ (old sk2 b a) := Eq.mp (by simp only [eq1194, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1292 -- forward demodulation 1292,1194
  have eq1693 : c = sk2 := resolve eq1323 ac -- subsumption resolution 1323,134
  have eq1718 : (old c b a) ∨ (old sk0 a sk2) ∨ (sP0 sk0 a sk2) ∨ (old a a b) ∨ (old b b a) := Eq.mp (by simp only [eq1693, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1645 -- backward demodulation 1645,1693
  have eq1836 : (old sk0 a sk2) ∨ (sP0 sk0 a sk2) ∨ (old a a b) ∨ (old b b a) := resolve eq1718 p4YZ -- subsumption resolution 1718,139
  have eq1837 : (old sk0 a c) ∨ (sP0 sk0 a sk2) ∨ (old a a b) ∨ (old b b a) := Eq.mp (by simp only [eq1693, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1836 -- forward demodulation 1836,1693
  have eq1838 : (sP0 sk0 a sk2) ∨ (old a a b) ∨ (old b b a) := resolve eq1837 p4XY -- subsumption resolution 1837,137
  have eq1839 : (sP0 sk0 a c) ∨ (old a a b) ∨ (old b b a) := Eq.mp (by simp only [eq1693, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1838 -- forward demodulation 1838,1693
  have eq1965 : (old sk0 a c) ∨ b = sk1 ∨ c = sk1 := Eq.mp (by simp only [eq1693, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1347 -- forward demodulation 1347,1693
  have eq1966 : b = sk1 ∨ c = sk1 := resolve eq1965 p4XY -- subsumption resolution 1965,137
  have eq1967 : a = b ∨ c = sk1 := Eq.mp (by simp only [eq1194, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1966 -- forward demodulation 1966,1194
  have eq1968 : a = c ∨ a = b := Eq.mp (by simp only [eq1194, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1967 -- forward demodulation 1967,1194
  have eq1969 : a = b := resolve eq1968 ac -- subsumption resolution 1968,134
  have eq1971 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq1969, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 136,1969
  have eq2018 : (old a a a) ∨ (sP0 sk0 a c) ∨ (old a a b) := Eq.mp (by simp only [eq1969, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1839 -- backward demodulation 1839,1969
  have eq2068 : (sP0 sk0 a c) ∨ (old a a b) := resolve eq2018 eq1971 -- subsumption resolution 2018,1971
  have eq2069 : (sP0 sk0 a c) := resolve eq2068 eq1971 -- subsumption resolution 2068,1971
  have eq2074 : a = sk0 := resolve eq2069 rule_def_0_0 -- resolution 2069,153
  subsumption preserve_1 eq2074 -- subsumption resolution 2074,201

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (memold : G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z b a ∨ ¬sP1 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP2 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP3 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP4 X Y Z) (rule_def_5_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP5 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP5 X Y Z) (rule_def_6_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP6 X Y Z) (rule_def_7_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP7 X Y Z) (rule_def_8_1 : ∀ (X Y Z : G), a = Y ∨ ¬sP8 X Y Z) (rule_def_8_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP8 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z) (old_mem2 : ∀ (X Y Z), ¬old X Y Z ∨ memold Y) : ∀ (X Y Z : G), ¬new X Y Z ∨ Y = a ∨ Y = b ∨ memold Y ∨ Y = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq229 : (sP8 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 196,200
  have eq243 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ c = sk2 := resolve eq229 rule_def_8_2 -- resolution 229,193
  have eq244 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ a = sk1 := resolve eq229 rule_def_8_1 -- resolution 229,192
  have eq248 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ c = sk2 := resolve eq243 rule_def_3_2 -- subsumption resolution 243,168
  have eq249 : (sP7 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ c = sk2 := resolve eq248 rule_def_0_2 -- subsumption resolution 248,155
  have eq250 : (sP7 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) := resolve eq244 preserve_1 -- subsumption resolution 244,201
  have eq267 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk1 := resolve eq249 rule_def_7_2 -- resolution 249,188
  have eq270 : (sP6 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ c = sk2 := resolve eq267 preserve_2 -- subsumption resolution 267,202
  have eq285 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ b = sk1 := resolve eq250 rule_def_7_2 -- resolution 250,188
  have eq288 : (sP6 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) := resolve eq285 preserve_2 -- subsumption resolution 285,202
  have eq303 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq270 rule_def_6_1 -- resolution 270,182
  have eq306 : (sP5 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 := resolve eq303 preserve_4 -- subsumption resolution 303,204
  have eq340 : (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ c = sk1 := resolve eq288 rule_def_6_1 -- resolution 288,182
  have eq344 : (sP5 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) := resolve eq340 preserve_4 -- subsumption resolution 340,204
  have eq395 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk2 ∨ a = sk1 := resolve eq306 rule_def_5_1 -- resolution 306,177
  have eq399 : (sP4 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ c = sk2 := resolve eq395 preserve_1 -- subsumption resolution 395,201
  have eq432 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ a = sk2 := resolve eq344 rule_def_5_2 -- resolution 344,178
  have eq435 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk2 := resolve eq432 rule_def_4_2 -- subsumption resolution 432,173
  have eq488 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq399 rule_def_4_1 -- resolution 399,172
  have eq490 : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ c = sk2 := resolve eq488 preserve_4 -- subsumption resolution 488,204
  have eq547 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk2 ∨ a = sk1 := resolve eq435 rule_def_3_1 -- resolution 435,167
  have eq549 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk2 := resolve eq547 preserve_1 -- subsumption resolution 547,201
  have eq636 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ c = sk2 ∨ b = sk1 := resolve eq490 rule_def_2_1 -- resolution 490,162
  have eq638 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk2 := resolve eq636 preserve_2 -- subsumption resolution 636,202
  have eq761 : (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk2 ∨ b = sk2 := resolve eq549 rule_def_2_2 -- resolution 549,163
  have eq806 : (old sk0 sk1 sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq638 rule_def_1_1 -- resolution 638,158
  have eq808 : (old sk0 sk1 sk2) ∨ c = sk2 := resolve eq806 preserve_4 -- subsumption resolution 806,204
  have eq819 : c = sk2 ∨ memold sk1 := resolve eq808 old_mem2 -- resolution 808,198
  have eq821 : c = sk2 := resolve eq819 preserve_3 -- subsumption resolution 819,203
  have eq906 : (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = sk2 ∨ b = sk2 := Eq.mp (by simp only [eq821, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq761 -- backward demodulation 761,821
  have eq1064 : (sP0 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ (old sk0 sk1 sk2) ∨ a = sk2 ∨ b = sk2 := Eq.mp (by simp only [eq821, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq906 -- forward demodulation 906,821
  have eq1065 : (old sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ a = sk2 ∨ b = sk2 := Eq.mp (by simp only [eq821, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1064 -- forward demodulation 1064,821
  have eq1066 : (sP0 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ a = sk2 ∨ b = sk2 := resolve eq1065 p4XY -- subsumption resolution 1065,137
  have eq1067 : a = c ∨ (sP0 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ b = sk2 := Eq.mp (by simp only [eq821, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1066 -- forward demodulation 1066,821
  have eq1068 : (sP0 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) ∨ b = sk2 := resolve eq1067 ac -- subsumption resolution 1067,134
  have eq1069 : c = b ∨ (sP0 sk0 sk1 c) ∨ (sP1 sk0 sk1 c) := Eq.mp (by simp only [eq821, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1068 -- forward demodulation 1068,821
  have eq1070 : (sP1 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) := resolve eq1069 bc -- subsumption resolution 1069,135
  have eq1186 : (sP0 sk0 sk1 c) ∨ (old c b a) := resolve eq1070 rule_def_1_2 -- resolution 1070,159
  have eq1189 : (sP0 sk0 sk1 c) := resolve eq1186 p4YZ -- subsumption resolution 1186,139
  have eq1191 : b = sk1 := resolve eq1189 rule_def_0_1 -- resolution 1189,154
  subsumption preserve_2 eq1191 -- subsumption resolution 1191,202

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (memold : G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_1 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X2 X1 X3 ∨ old X1 X3 X0)) (old_8 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X3 X1 X2 ∨ X3 = X0)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), b = X ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old Z b a ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Z ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), old b b a ∨ ¬sP2 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), old b b a ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = X ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), old a a b ∨ ¬sP4 X Y Z) (rule_def_5_0 : ∀ (X Y Z : G), c = X ∨ ¬sP5 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), a = Z ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), old a a b ∨ ¬sP5 X Y Z) (rule_def_6_0 : ∀ (X Y Z : G), a = X ∨ ¬sP6 X Y Z) (rule_def_6_1 : ∀ (X Y Z : G), c = Y ∨ ¬sP6 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), old b b a ∨ ¬sP6 X Y Z) (rule_def_6_3 : ∀ (X Y Z : G), old Z a b ∨ ¬sP6 X Y Z) (rule_def_7_0 : ∀ (X Y Z : G), a = b ∨ ¬sP7 X Y Z) (rule_def_7_1 : ∀ (X Y Z : G), c = X ∨ ¬sP7 X Y Z) (rule_def_7_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP7 X Y Z) (rule_def_7_3 : ∀ (X Y Z : G), old Z b b ∨ ¬sP7 X Y Z) (rule_def_8_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP8 X Y Z) (rule_def_8_3 : ∀ (X Y Z : G), old a a b ∨ ¬sP8 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z) (old_mem1 : ∀ (X Y Z), ¬old X Y Z ∨ memold X) (old_mem3 : ∀ (X Y Z), ¬old X Y Z ∨ memold Z) : ∀ (X Y Z : G), ¬new X Y Z ∨ Z = a ∨ Z = b ∨ memold Z ∨ Z = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq229 : (sP8 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 196,200
  have eq242 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (old a a b) := resolve eq229 rule_def_8_3 -- resolution 229,194
  have eq243 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ c = sk2 := resolve eq229 rule_def_8_2 -- resolution 229,193
  have eq246 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ (old a a b) := resolve eq242 rule_def_4_3 -- subsumption resolution 242,174
  have eq247 : (sP7 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (old a a b) := resolve eq246 rule_def_5_3 -- subsumption resolution 246,179
  have eq248 : (sP7 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) := resolve eq243 preserve_4 -- subsumption resolution 243,204
  have eq264 : (sP6 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (old a a b) ∨ (old sk2 b b) := resolve eq247 rule_def_7_3 -- resolution 247,189
  have eq265 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 := resolve eq247 rule_def_7_2 -- resolution 247,188
  have eq268 : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 := resolve eq265 rule_def_2_1 -- subsumption resolution 265,162
  have eq269 : (sP6 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 := resolve eq268 rule_def_0_1 -- subsumption resolution 268,154
  have eq277 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ b = sk1 := resolve eq248 rule_def_7_2 -- resolution 248,188
  have eq278 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ c = sk0 := resolve eq248 rule_def_7_1 -- resolution 248,187
  have eq279 : (sP6 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ a = b := resolve eq248 rule_def_7_0 -- resolution 248,186
  have eq280 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ b = sk1 := resolve eq277 rule_def_2_1 -- subsumption resolution 277,162
  have eq281 : (sP6 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ b = sk1 := resolve eq280 rule_def_0_1 -- subsumption resolution 280,154
  have eq282 : (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ c = sk0 := resolve eq278 rule_def_5_0 -- subsumption resolution 278,176
  have eq283 : (sP6 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk0 := resolve eq282 rule_def_2_0 -- subsumption resolution 282,161
  have eq287 : (sP3 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 ∨ (old sk2 a b) := resolve eq269 rule_def_6_3 -- resolution 269,184
  have eq288 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 ∨ (old b b a) := resolve eq269 rule_def_6_2 -- resolution 269,183
  have eq291 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 ∨ (old b b a) := resolve eq288 rule_def_3_3 -- subsumption resolution 288,169
  have eq317 : (sP5 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk1 ∨ (old sk2 a b) := resolve eq281 rule_def_6_3 -- resolution 281,184
  have eq320 : (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ b = sk1 ∨ a = sk0 := resolve eq281 rule_def_6_0 -- resolution 281,181
  have eq324 : (sP5 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ b = sk1 ∨ a = sk0 := resolve eq320 rule_def_4_0 -- subsumption resolution 320,171
  have eq340 : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk0 ∨ c = sk1 := resolve eq283 rule_def_6_1 -- resolution 283,182
  have eq341 : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ c = sk0 ∨ a = sk0 := resolve eq283 rule_def_6_0 -- resolution 283,181
  have eq343 : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk0 ∨ c = sk1 := resolve eq340 rule_def_4_1 -- subsumption resolution 340,172
  have eq344 : (sP3 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk0 ∨ c = sk1 := resolve eq343 rule_def_1_1 -- subsumption resolution 343,158
  have eq345 : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk0 ∨ a = sk0 := resolve eq341 rule_def_4_0 -- subsumption resolution 341,171
  have eq346 : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk0 ∨ a = sk0 := resolve eq345 rule_def_0_0 -- subsumption resolution 345,153
  have eq373 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (old a a b) ∨ (old sk2 b b) ∨ (old b b a) := resolve eq264 rule_def_6_2 -- resolution 264,183
  have eq376 : (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (old a a b) ∨ (old sk2 b b) ∨ (old b b a) := resolve eq373 rule_def_2_3 -- subsumption resolution 373,164
  have eq377 : (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (old a a b) ∨ (old sk2 b b) ∨ (old b b a) := resolve eq376 rule_def_3_3 -- subsumption resolution 376,169
  have eq382 : (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ a = b ∨ c = sk1 := resolve eq279 rule_def_6_1 -- resolution 279,182
  have eq386 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ a = b ∨ c = sk1 := resolve eq382 rule_def_4_1 -- subsumption resolution 382,172
  have eq387 : (sP5 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = b ∨ c = sk1 := resolve eq386 rule_def_1_1 -- subsumption resolution 386,158
  have eq412 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := resolve eq344 rule_def_3_2 -- resolution 344,168
  have eq415 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk0 ∨ c = sk1 := resolve eq412 preserve_4 -- subsumption resolution 412,204
  have eq418 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk0 ∨ a = sk0 ∨ c = sk2 := resolve eq346 rule_def_3_2 -- resolution 346,168
  have eq421 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk0 ∨ a = sk0 := resolve eq418 preserve_4 -- subsumption resolution 418,204
  have eq422 : (old sk2 b a) ∨ (old a a b) ∨ b = sk1 ∨ (old b b a) ∨ (old sk0 sk1 sk2) := resolve eq291 rule_def_1_2 -- resolution 291,159
  have eq493 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ b = sk1 ∨ a = sk0 ∨ a = sk2 := resolve eq324 rule_def_5_2 -- resolution 324,178
  have eq496 : (sP3 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ b = sk1 ∨ a = sk0 := resolve eq493 preserve_1 -- subsumption resolution 493,201
  have eq511 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 ∨ (old sk2 a b) ∨ c = sk2 := resolve eq287 rule_def_3_2 -- resolution 287,168
  have eq514 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 ∨ (old sk2 a b) := resolve eq511 preserve_4 -- subsumption resolution 511,204
  have eq560 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (old a a b) ∨ (old sk2 b b) ∨ (old b b a) ∨ c = sk1 := resolve eq377 rule_def_1_1 -- resolution 377,158
  have eq575 : (old sk0 sk1 sk2) ∨ c = sk0 ∨ c = sk1 ∨ c = sk2 := resolve eq415 rule_def_0_2 -- resolution 415,155
  have eq579 : (old sk0 sk1 sk2) ∨ c = sk0 ∨ c = sk1 := resolve eq575 preserve_4 -- subsumption resolution 575,204
  have eq602 : c = sk0 ∨ c = sk1 ∨ memold sk2 := resolve eq579 old_mem3 -- resolution 579,199
  have eq606 : c = sk1 ∨ c = sk0 := resolve eq602 preserve_3 -- subsumption resolution 602,203
  have eq608 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ a = b ∨ c = sk1 ∨ a = sk2 := resolve eq387 rule_def_5_2 -- resolution 387,178
  have eq612 : (sP3 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = b ∨ c = sk1 := resolve eq608 preserve_1 -- subsumption resolution 608,201
  have eq694 : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk1 ∨ (old sk2 a b) ∨ a = sk2 := resolve eq317 rule_def_5_2 -- resolution 317,178
  have eq698 : (sP4 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ b = sk1 ∨ (old sk2 a b) := resolve eq694 preserve_1 -- subsumption resolution 694,201
  have eq743 : (sP1 sk0 c sk2) ∨ (old sk0 c sk2) ∨ c = sk0 ∨ a = sk0 ∨ c = sk0 := Or.assoc4 (eq606.imp_left (fun h : c = sk1 ↦ superpose h eq421)) -- superposition 421,606, 606 into 421, unify on (0).2 in 606 and (0).2 in 421
  have eq745 : (sP1 sk0 c sk2) ∨ (old sk0 c sk2) ∨ c = sk0 ∨ a = sk0 := resolve eq743 rfl -- duplicate literal removal 743
  have eq746 : (sP1 sk0 c sk2) ∨ c = sk0 ∨ a = sk0 := resolve eq745 p4XZ -- subsumption resolution 745,138
  have eq755 : (old sk2 b a) ∨ a = sk0 ∨ c = sk0 := resolve eq746 rule_def_1_2 -- resolution 746,159
  have eq862 : a = sk0 ∨ c = sk0 ∨ memold sk2 := resolve eq755 old_mem1 -- resolution 755,197
  have eq865 : c = sk0 ∨ a = sk0 := resolve eq862 preserve_3 -- subsumption resolution 862,203
  have eq1086 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ b = sk1 ∨ a = sk0 ∨ c = sk2 := resolve eq496 rule_def_3_2 -- resolution 496,168
  have eq1092 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ a = sk0 := resolve eq1086 preserve_4 -- subsumption resolution 1086,204
  have eq1109 : (old a a b) ∨ b = sk1 ∨ (old b b a) ∨ (old sk0 sk1 sk2) ∨ memold sk2 := resolve eq422 old_mem1 -- resolution 422,197
  have eq1112 : (old sk0 sk1 sk2) ∨ b = sk1 ∨ (old b b a) ∨ (old a a b) := resolve eq1109 preserve_3 -- subsumption resolution 1109,203
  have eq1135 : (old sk2 b a) ∨ (old a a b) ∨ b = sk1 ∨ (old sk2 a b) ∨ (old sk0 sk1 sk2) := resolve eq514 rule_def_1_2 -- resolution 514,159
  have eq1228 : (sP1 c sk1 sk2) ∨ (old c sk1 sk2) ∨ b = sk1 ∨ a = c ∨ a = sk0 := Or.assoc4 (eq865.imp_left (fun h : c = sk0 ↦ superpose h eq1092)) -- superposition 1092,865, 865 into 1092, unify on (0).2 in 865 and (0).1 in 1092
  have eq1231 : (sP1 c sk1 sk2) ∨ b = sk1 ∨ a = c ∨ a = sk0 := resolve eq1228 p4YZ -- subsumption resolution 1228,139
  have eq1232 : (sP1 c sk1 sk2) ∨ b = sk1 ∨ a = sk0 := resolve eq1231 ac -- subsumption resolution 1231,134
  have eq1244 : b = sk1 ∨ a = sk0 ∨ c = b := resolve eq1232 rule_def_1_0 -- resolution 1232,157
  have eq1246 : b = sk1 ∨ a = sk0 := resolve eq1244 bc -- subsumption resolution 1244,135
  have eq1381 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ a = b ∨ c = sk1 ∨ c = sk2 := resolve eq612 rule_def_3_2 -- resolution 612,168
  have eq1389 : (sP2 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ a = b ∨ c = sk1 := resolve eq1381 preserve_4 -- subsumption resolution 1381,204
  have eq1464 : (old sk0 sk1 sk2) ∨ (old a a b) ∨ (old sk2 b b) ∨ (old b b a) ∨ c = sk1 ∨ c = sk2 := resolve eq560 rule_def_0_2 -- resolution 560,155
  have eq1471 : (old sk2 b b) ∨ (old a a b) ∨ (old sk0 sk1 sk2) ∨ (old b b a) ∨ c = sk1 := resolve eq1464 preserve_4 -- subsumption resolution 1464,204
  have eq1501 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ b = sk1 ∨ (old sk2 a b) ∨ a = sk2 := resolve eq698 rule_def_4_2 -- resolution 698,173
  have eq1507 : (sP3 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ b = sk1 ∨ (old sk2 a b) := resolve eq1501 preserve_1 -- subsumption resolution 1501,201
  have eq1728 : b = sk1 ∨ (old b b a) ∨ (old a a b) ∨ memold sk2 := resolve eq1112 old_mem3 -- resolution 1112,199
  have eq1734 : (old b b a) ∨ b = sk1 ∨ (old a a b) := resolve eq1728 preserve_3 -- subsumption resolution 1728,203
  have eq2090 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ a = b ∨ c = sk1 ∨ b = sk2 := resolve eq1389 rule_def_2_2 -- resolution 1389,163
  have eq2097 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = b ∨ c = sk1 := resolve eq2090 preserve_2 -- subsumption resolution 2090,202
  have eq2182 : (old a a b) ∨ b = sk1 ∨ (old sk2 a b) ∨ (old sk0 sk1 sk2) ∨ memold sk2 := resolve eq1135 old_mem1 -- resolution 1135,197
  have eq2185 : (old sk2 a b) ∨ b = sk1 ∨ (old a a b) ∨ (old sk0 sk1 sk2) := resolve eq2182 preserve_3 -- subsumption resolution 2182,203
  have eq2264 (X0 : G) : (old a a b) ∨ (old sk0 sk1 sk2) ∨ (old b b a) ∨ c = sk1 ∨ (old b b X0) ∨ ¬(old X0 b sk2) := resolve eq1471 old_1 -- resolution 1471,141
  have eq2272 : (old a a b) ∨ (old sk0 sk1 sk2) ∨ (old b b a) ∨ c = sk1 ∨ memold sk2 := resolve eq1471 old_mem1 -- resolution 1471,197
  have eq2277 : (old sk0 sk1 sk2) ∨ (old a a b) ∨ (old b b a) ∨ c = sk1 := resolve eq2272 preserve_3 -- subsumption resolution 2272,203
  have eq2297 : (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ b = sk1 ∨ (old sk2 a b) ∨ c = sk2 := resolve eq1507 rule_def_3_2 -- resolution 1507,168
  have eq2303 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk1 ∨ (old sk2 a b) := resolve eq2297 preserve_4 -- subsumption resolution 2297,204
  have eq3208 : (old sk0 sk1 sk2) ∨ a = b ∨ c = sk1 ∨ c = sk2 := resolve eq2097 rule_def_0_2 -- resolution 2097,155
  have eq3215 : (old sk0 sk1 sk2) ∨ a = b ∨ c = sk1 := resolve eq3208 preserve_4 -- subsumption resolution 3208,204
  have eq3310 : b = sk1 ∨ (old a a b) ∨ (old sk0 sk1 sk2) ∨ memold sk2 := resolve eq2185 old_mem1 -- resolution 2185,197
  have eq3316 : (old sk0 sk1 sk2) ∨ (old a a b) ∨ b = sk1 := resolve eq3310 preserve_3 -- subsumption resolution 3310,203
  have eq3393 : a = b ∨ c = sk1 ∨ memold sk2 := resolve eq3215 old_mem3 -- resolution 3215,199
  have eq3404 : c = sk1 ∨ a = b := resolve eq3393 preserve_3 -- subsumption resolution 3393,203
  have eq3439 : c = b ∨ a = b ∨ a = sk0 := Or.assoc2 (eq1246.imp_left (fun h : b = sk1 ↦ superpose h eq3404)) -- superposition 3404,1246, 1246 into 3404, unify on (0).2 in 1246 and (0).2 in 3404
  have eq3573 : a = sk0 ∨ a = b := resolve eq3439 bc -- subsumption resolution 3439,135
  have eq3863 : (sP1 sk0 c sk2) ∨ (old sk0 c sk2) ∨ c = b ∨ (old sk2 a b) ∨ c = sk0 := Or.assoc4 (eq606.imp_left (fun h : c = sk1 ↦ superpose h eq2303)) -- superposition 2303,606, 606 into 2303, unify on (0).2 in 606 and (0).2 in 2303
  have eq3866 : (sP1 sk0 c sk2) ∨ c = b ∨ (old sk2 a b) ∨ c = sk0 := resolve eq3863 p4XZ -- subsumption resolution 3863,138
  have eq3867 : (sP1 sk0 c sk2) ∨ (old sk2 a b) ∨ c = sk0 := resolve eq3866 bc -- subsumption resolution 3866,135
  have eq5061 : (old sk0 c sk2) ∨ (old a a b) ∨ c = b ∨ a = b := Or.assoc3 (eq3404.imp_left (fun h : c = sk1 ↦ superpose h eq3316)) -- superposition 3316,3404, 3404 into 3316, unify on (0).2 in 3404 and (0).2 in 3316
  have eq5072 : (old a a b) ∨ c = b ∨ a = b := resolve eq5061 p4XZ -- subsumption resolution 5061,138
  have eq5073 : (old a a b) ∨ a = b := resolve eq5072 bc -- subsumption resolution 5072,135
  have eq5216 (X0 : G) : ¬(old X0 a b) ∨ a = X0 ∨ a = b := resolve eq5073 old_8 -- resolution 5073,148
  have eq6273 : (sP1 a c sk2) ∨ (old sk2 a b) ∨ a = c ∨ a = b := Or.assoc3 (eq3573.imp_left (fun h : a = sk0 ↦ superpose h eq3867)) -- superposition 3867,3573, 3573 into 3867, unify on (0).2 in 3573 and (0).1 in 3867
  have eq6275 : (sP1 a c sk2) ∨ (old sk2 a b) ∨ a = b := resolve eq6273 ac -- subsumption resolution 6273,134
  have eq6276 : (old sk2 a b) ∨ a = b := resolve eq6275 rule_def_1_0 -- subsumption resolution 6275,157
  have eq6288 : a = b ∨ a = sk2 ∨ a = b := resolve eq6276 eq5216 -- resolution 6276,5216
  have eq6301 : a = b ∨ a = sk2 := resolve eq6288 rfl -- duplicate literal removal 6288
  have eq6306 : a = b := resolve eq6301 preserve_1 -- subsumption resolution 6301,201
  have eq6308 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq6306, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 136,6306
  have eq6681 : (old a a a) ∨ b = sk1 ∨ (old a a b) := Eq.mp (by simp only [eq6306, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1734 -- backward demodulation 1734,6306
  have eq6814 : ∀ (X0 : G) , (old a a a) ∨ (old a a b) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ (old b b X0) ∨ ¬(old X0 b sk2) := Eq.mp (by simp only [eq6306, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2264 -- backward demodulation 2264,6306
  have eq6822 : (old a a a) ∨ (old sk0 sk1 sk2) ∨ (old a a b) ∨ c = sk1 := Eq.mp (by simp only [eq6306, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2277 -- backward demodulation 2277,6306
  have eq7865 : b = sk1 ∨ (old a a b) := resolve eq6681 eq6308 -- subsumption resolution 6681,6308
  have eq7866 : b = sk1 := resolve eq7865 eq6308 -- subsumption resolution 7865,6308
  have eq7867 : a = sk1 := Eq.mp (by simp only [eq6306, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq7866 -- forward demodulation 7866,6306
  have eq7887 : a = c ∨ c = sk0 := Eq.mp (by simp only [eq7867, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq606 -- backward demodulation 606,7867
  have eq7972 : c = sk0 := resolve eq7887 ac -- subsumption resolution 7887,134
  have eq8103 (X0 : G) : (old a a b) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ (old b b X0) ∨ ¬(old X0 b sk2) := resolve eq6814 eq6308 -- subsumption resolution 6814,6308
  have eq8104 (X0 : G) : (old sk0 sk1 sk2) ∨ c = sk1 ∨ (old b b X0) ∨ ¬(old X0 b sk2) := resolve eq8103 eq6308 -- subsumption resolution 8103,6308
  have eq8105 : ∀ (X0 : G) , (old sk0 a sk2) ∨ c = sk1 ∨ (old b b X0) ∨ ¬(old X0 b sk2) := Eq.mp (by simp only [eq7867, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq8104 -- forward demodulation 8104,7867
  have eq8106 : ∀ (X0 : G) , (old c a sk2) ∨ c = sk1 ∨ (old b b X0) ∨ ¬(old X0 b sk2) := Eq.mp (by simp only [eq7972, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq8105 -- forward demodulation 8105,7972
  have eq8107 (X0 : G) : c = sk1 ∨ (old b b X0) ∨ ¬(old X0 b sk2) := resolve eq8106 p4YZ -- subsumption resolution 8106,139
  have eq8108 : ∀ (X0 : G) , a = c ∨ (old b b X0) ∨ ¬(old X0 b sk2) := Eq.mp (by simp only [eq7867, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq8107 -- forward demodulation 8107,7867
  have eq8109 (X0 : G) : (old b b X0) ∨ ¬(old X0 b sk2) := resolve eq8108 ac -- subsumption resolution 8108,134
  have eq8110 : ∀ (X0 : G) , (old a a X0) ∨ ¬(old X0 b sk2) := Eq.mp (by simp only [eq6306, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq8109 -- forward demodulation 8109,6306
  have eq8111 (X0 : G) : ¬(old X0 b sk2) := resolve eq8110 eq6308 -- subsumption resolution 8110,6308
  have eq8112 : ∀ (X0 : G) , ¬(old X0 a sk2) := Eq.mp (by simp only [eq6306, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq8111 -- forward demodulation 8111,6306
  have eq8168 : (old sk0 sk1 sk2) ∨ (old a a b) ∨ c = sk1 := resolve eq6822 eq6308 -- subsumption resolution 6822,6308
  have eq8169 : (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq8168 eq6308 -- subsumption resolution 8168,6308
  have eq8170 : (old sk0 a sk2) ∨ c = sk1 := Eq.mp (by simp only [eq7867, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq8169 -- forward demodulation 8169,7867
  have eq8171 : c = sk1 := resolve eq8170 eq8112 -- subsumption resolution 8170,8112
  have eq8172 : a = c := Eq.mp (by simp only [eq7867, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq8171 -- forward demodulation 8171,7867
  subsumption ac eq8172 -- subsumption resolution 8172,134

structure PartialSolution (G : Type*) where
  R : G → G → G → Prop
  rule_0 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X0 X1 X3 ∨ X2 = X3)
  rule_1 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X2 X1 X3 ∨ R X1 X3 X0)
  rule_2 : (∀ X0 X1 X2, ¬ R X0 X1 X2 ∨ ¬ R X1 X1 X0 ∨ R X2 X1 X1)
  rule_3 : (∀ X0 X1, ¬ R X0 X1 X1 ∨ R X1 X0 X1)
  rule_4 : (∀ X0 X1 X2, ¬ R X0 X0 X1 ∨ ¬ R X1 X0 X2 ∨ R X0 X1 X2)
  rule_5 : (∀ X0 X1 X2, ¬ R X0 X0 X1 ∨ ¬ R X0 X1 X2 ∨ R X0 X2 X0)
  rule_6 : (∀ X0 X1 X2, ¬ R X0 X0 X1 ∨ ¬ R X0 X1 X2 ∨ R X2 X0 X0)
  rule_7 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X1 X1 X0 ∨ ¬ R X3 X0 X1 ∨ R X0 X2 X3)
  rule_8 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X3 X1 X2 ∨ X3 = X0)
  rule_9 : (∀ X0 X1 X2, ¬ R X0 X0 X1 ∨ ¬ R X2 X0 X0 ∨ R X1 X0 X2)
  rule_10 : (∀ X0 X1 X2, ¬ R X0 X0 X1 ∨ ¬ R X0 X1 X2 ∨ R X1 X0 X2)
  finsupp : Finset G
  mem_1 : ∀ X Y Z, ¬R X Y Z ∨ X ∈ finsupp
  mem_2 : ∀ X Y Z, ¬R X Y Z ∨ Y ∈ finsupp
  mem_3 : ∀ X Y Z, ¬R X Y Z ∨ Z ∈ finsupp

variable {G : Type*} (ps : PartialSolution G)

set_option linter.all false in
theorem PartialSolution.adjoin (a b c : G) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ ps.R a b X0)
    (p4XY : ∀ X1 X2, ¬ ps.R X1 X2 c) (p4XZ : ∀ X1 X2, ¬ ps.R X1 c X2) (p4YZ : ∀ X1 X2, ¬ ps.R c X1 X2)
    : ∃ next : PartialSolution G, next.R a b c ∧ ∀ x y z, ps.R x y z → next.R x y z := by classical
  let sP0 (X Y Z) := a = X ∧ b = Y ∧ c = Z
  have hsP0 (X Y Z) (h : sP0 X Y Z) : a = X ∧ b = Y ∧ c = Z := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP0
  obtain ⟨rule_def_0_0, rule_def_0_1, rule_def_0_2⟩ := hsP0
  simp_rw [or_comm] at rule_def_0_0 rule_def_0_1 rule_def_0_2
  let sP1 (X Y Z) := b = X ∧ c = Y ∧ ps.R Z b a
  have hsP1 (X Y Z) (h : sP1 X Y Z) : b = X ∧ c = Y ∧ ps.R Z b a := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP1
  obtain ⟨rule_def_1_0, rule_def_1_1, rule_def_1_2⟩ := hsP1
  simp_rw [or_comm] at rule_def_1_0 rule_def_1_1 rule_def_1_2
  let sP2 (X Y Z) := c = X ∧ b = Y ∧ b = Z ∧ ps.R b b a
  have hsP2 (X Y Z) (h : sP2 X Y Z) : c = X ∧ b = Y ∧ b = Z ∧ ps.R b b a := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP2
  obtain ⟨rule_def_2_0, rule_def_2_1, rule_def_2_2, rule_def_2_3⟩ := hsP2
  simp_rw [or_comm] at rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3
  let sP3 (X Y Z) := b = X ∧ a = Y ∧ c = Z ∧ ps.R b b a
  have hsP3 (X Y Z) (h : sP3 X Y Z) : b = X ∧ a = Y ∧ c = Z ∧ ps.R b b a := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP3
  obtain ⟨rule_def_3_0, rule_def_3_1, rule_def_3_2, rule_def_3_3⟩ := hsP3
  simp_rw [or_comm] at rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3
  let sP4 (X Y Z) := a = X ∧ c = Y ∧ a = Z ∧ ps.R a a b
  have hsP4 (X Y Z) (h : sP4 X Y Z) : a = X ∧ c = Y ∧ a = Z ∧ ps.R a a b := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP4
  obtain ⟨rule_def_4_0, rule_def_4_1, rule_def_4_2, rule_def_4_3⟩ := hsP4
  simp_rw [or_comm] at rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_3
  let sP5 (X Y Z) := c = X ∧ a = Y ∧ a = Z ∧ ps.R a a b
  have hsP5 (X Y Z) (h : sP5 X Y Z) : c = X ∧ a = Y ∧ a = Z ∧ ps.R a a b := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP5
  obtain ⟨rule_def_5_0, rule_def_5_1, rule_def_5_2, rule_def_5_3⟩ := hsP5
  simp_rw [or_comm] at rule_def_5_0 rule_def_5_1 rule_def_5_2 rule_def_5_3
  let sP6 (X Y Z) := a = X ∧ c = Y ∧ ps.R b b a ∧ ps.R Z a b
  have hsP6 (X Y Z) (h : sP6 X Y Z) : a = X ∧ c = Y ∧ ps.R b b a ∧ ps.R Z a b := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP6
  obtain ⟨rule_def_6_0, rule_def_6_1, rule_def_6_2, rule_def_6_3⟩ := hsP6
  simp_rw [or_comm] at rule_def_6_0 rule_def_6_1 rule_def_6_2 rule_def_6_3
  let sP7 (X Y Z) := a = b ∧ c = X ∧ b = Y ∧ ps.R Z b b
  have hsP7 (X Y Z) (h : sP7 X Y Z) : a = b ∧ c = X ∧ b = Y ∧ ps.R Z b b := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP7
  obtain ⟨rule_def_7_0, rule_def_7_1, rule_def_7_2, rule_def_7_3⟩ := hsP7
  simp_rw [or_comm] at rule_def_7_0 rule_def_7_1 rule_def_7_2 rule_def_7_3
  let sP8 (X Y Z) := b = X ∧ a = Y ∧ c = Z ∧ ps.R a a b
  have hsP8 (X Y Z) (h : sP8 X Y Z) : b = X ∧ a = Y ∧ c = Z ∧ ps.R a a b := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP8
  obtain ⟨rule_def_8_0, rule_def_8_1, rule_def_8_2, rule_def_8_3⟩ := hsP8
  simp_rw [or_comm] at rule_def_8_0 rule_def_8_1 rule_def_8_2 rule_def_8_3

  let new (X Y Z) := ps.R X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z
  have new_new : new a b c := by simp only [true_or, or_true, new, sP0, and_true]
  have imp_new_0 (X Y Z) : _ → new X Y Z := Or.inl
  have imp_new_1 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inl
  have imp_new_2 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_3 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_4 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_5 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_6 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_7 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_8 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
  have imp_new_9 (X Y Z) : _ → new X Y Z := Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
  have new_imp (X Y Z) : new X Y Z → ps.R X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z := id

  simp only [imp_iff_not_or] at imp_new_0
  simp only [not_and, not_exists, imp_iff_not_or, sP0, ← forall_or_right, or_assoc] at imp_new_1
  simp only [not_and, not_exists, imp_iff_not_or, sP1, ← forall_or_right, or_assoc] at imp_new_2
  simp only [not_and, not_exists, imp_iff_not_or, sP2, ← forall_or_right, or_assoc] at imp_new_3
  simp only [not_and, not_exists, imp_iff_not_or, sP3, ← forall_or_right, or_assoc] at imp_new_4
  simp only [not_and, not_exists, imp_iff_not_or, sP4, ← forall_or_right, or_assoc] at imp_new_5
  simp only [not_and, not_exists, imp_iff_not_or, sP5, ← forall_or_right, or_assoc] at imp_new_6
  simp only [not_and, not_exists, imp_iff_not_or, sP6, ← forall_or_right, or_assoc] at imp_new_7
  simp only [not_and, not_exists, imp_iff_not_or, sP7, ← forall_or_right, or_assoc] at imp_new_8
  simp only [not_and, not_exists, imp_iff_not_or, sP8, ← forall_or_right, or_assoc] at imp_new_9
  simp only [imp_iff_not_or] at new_imp
  clear_value sP0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 new

  have prev_0 := rule_0_preserved G a b c ps.R new sP0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 ac bc p3 p4XY p4XZ p4YZ ps.rule_0 ps.rule_4 ps.rule_8 ps.rule_10 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_3 rule_def_5_0 rule_def_5_1 rule_def_5_2 rule_def_5_3 rule_def_6_0 rule_def_6_1 rule_def_6_2 rule_def_6_3 rule_def_7_0 rule_def_7_1 rule_def_7_2 rule_def_7_3 rule_def_8_0 rule_def_8_1 rule_def_8_2 rule_def_8_3 new_imp
  have prev_1 := rule_1_preserved G a b c ps.R new sP0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 ac bc p3 p4XY p4XZ p4YZ ps.rule_0 prev_0 ps.rule_1 ps.rule_3 ps.rule_8 imp_new_1 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 imp_new_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 imp_new_4 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 imp_new_5 rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_3 imp_new_6 rule_def_5_0 rule_def_5_1 rule_def_5_2 rule_def_5_3 imp_new_7 rule_def_6_0 rule_def_6_1 rule_def_6_2 rule_def_6_3 rule_def_7_0 rule_def_7_1 rule_def_7_2 rule_def_7_3 imp_new_9 rule_def_8_0 rule_def_8_1 rule_def_8_2 rule_def_8_3 new_imp imp_new_0
  have prev_2 := rule_2_preserved G a b c ps.R new sP0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 prev_1
  have prev_3 := rule_3_preserved G a b c ps.R new sP0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 ac bc p3 p4XZ p4YZ ps.rule_3 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_2_0 rule_def_2_2 rule_def_2_3 rule_def_3_0 rule_def_3_1 rule_def_3_2 imp_new_5 rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_5_0 rule_def_5_2 rule_def_5_3 rule_def_6_0 rule_def_6_1 rule_def_6_3 rule_def_7_0 rule_def_7_1 rule_def_7_2 rule_def_7_3 rule_def_8_0 rule_def_8_1 rule_def_8_2 new_imp imp_new_0
  have prev_4 := rule_4_preserved G a b c ps.R new sP0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 prev_1 prev_2
  have prev_5 := rule_5_preserved G a b c ps.R new sP0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 ac bc p3 p4XY p4XZ p4YZ prev_1 ps.rule_3 ps.rule_5 imp_new_1 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_2_0 rule_def_2_1 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 imp_new_5 rule_def_4_0 rule_def_4_1 rule_def_4_3 rule_def_5_0 rule_def_5_1 rule_def_5_3 rule_def_6_0 rule_def_6_1 rule_def_6_2 rule_def_7_1 rule_def_7_2 rule_def_8_0 rule_def_8_1 rule_def_8_2 rule_def_8_3 new_imp imp_new_0
  have prev_6 := rule_6_preserved G a b c ps.R new sP0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 prev_1 prev_5
  have prev_7 := rule_7_preserved G a b c ps.R new sP0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 prev_1 prev_4
  have prev_8 := rule_8_preserved G a b c ps.R new sP0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 ac bc p3 p4XY p4XZ p4YZ prev_0 ps.rule_1 prev_1 prev_3 ps.rule_8 imp_new_1 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 imp_new_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 imp_new_4 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_3 rule_def_5_0 rule_def_5_1 rule_def_5_2 rule_def_5_3 rule_def_6_0 rule_def_6_1 rule_def_6_2 rule_def_7_0 rule_def_7_1 rule_def_7_2 rule_def_7_3 rule_def_8_0 rule_def_8_1 rule_def_8_2 rule_def_8_3 new_imp imp_new_0
  have prev_9 := rule_9_preserved G a b c ps.R new sP0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 ac bc p3 p4XZ p4YZ prev_0 prev_3 ps.rule_9 imp_new_1 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_3 rule_def_5_0 rule_def_5_1 rule_def_5_2 rule_def_5_3 rule_def_6_0 rule_def_6_1 imp_new_8 rule_def_7_1 rule_def_7_2 rule_def_7_3 imp_new_9 rule_def_8_0 rule_def_8_1 rule_def_8_2 rule_def_8_3 new_imp imp_new_0
  have prev_10 := rule_10_preserved G a b c ps.R new sP0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 prev_6 prev_9

  exact ⟨{
    R := new
    rule_0 := prev_0
    rule_1 := prev_1
    rule_2 := prev_2
    rule_3 := prev_3
    rule_4 := prev_4
    rule_5 := prev_5
    rule_6 := prev_6
    rule_7 := prev_7
    rule_8 := prev_8
    rule_9 := prev_9
    rule_10 := prev_10
    finsupp := ps.finsupp ∪ {a, b, c}
    mem_1 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_0_preserved G a b c ps.R new sP0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 (· ∈ ps.finsupp) ac bc p3 p4XY p4YZ rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_2_0 rule_def_2_1 rule_def_2_3 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_4_0 rule_def_4_1 rule_def_4_3 rule_def_5_0 rule_def_5_1 rule_def_5_3 rule_def_6_0 rule_def_6_1 rule_def_6_2 rule_def_7_1 rule_def_7_2 rule_def_8_0 rule_def_8_1 rule_def_8_2 rule_def_8_3 new_imp ps.mem_1
    mem_2 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_1_preserved G a b c ps.R new sP0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 (· ∈ ps.finsupp) ac bc p4XY p4YZ rule_def_0_1 rule_def_0_2 rule_def_1_1 rule_def_1_2 rule_def_2_1 rule_def_2_2 rule_def_3_1 rule_def_3_2 rule_def_4_1 rule_def_4_2 rule_def_5_1 rule_def_5_2 rule_def_6_1 rule_def_7_2 rule_def_8_1 rule_def_8_2 new_imp ps.mem_2
    mem_3 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_2_preserved G a b c ps.R new sP0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 (· ∈ ps.finsupp) ac bc p3 p4XZ p4YZ ps.rule_1 ps.rule_8 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_3_2 rule_def_3_3 rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_3 rule_def_5_0 rule_def_5_2 rule_def_5_3 rule_def_6_0 rule_def_6_1 rule_def_6_2 rule_def_6_3 rule_def_7_0 rule_def_7_1 rule_def_7_2 rule_def_7_3 rule_def_8_2 rule_def_8_3 new_imp ps.mem_1 ps.mem_3
  }, by simp only [new_new, imp_iff_not_or, imp_new_0, implies_true, and_self]⟩

open scoped Classical in
noncomputable def PartialSolution.addArbitrary [Infinite G] (a b : G) : PartialSolution G :=
  if h : ∃ c, ps.R a b c then ps else
    let c := (Infinite.exists_notMem_finset (ps.finsupp ∪ {a, b})).choose
    have hc : c ∉ _ := (Infinite.exists_notMem_finset (ps.finsupp ∪ {a, b})).choose_spec
    (ps.adjoin a b c (by simp_all [eq_comm]) (by simp_all)
        (by simpa using h) (fun _ _ h ↦ by have := (ps.mem_3 _ _ _).neg_resolve_left h; simp_all)
        (fun _ _ h ↦ by have := (ps.mem_2 _ _ _).neg_resolve_left h; simp_all)
        (fun _ _ h ↦ by have := (ps.mem_1 _ _ _).neg_resolve_left h; simp_all)).choose

lemma PartialSolution.addArbitrary_covers [Infinite G] (a b : G) :
    ∃ c, (ps.addArbitrary a b).R a b c := by
  unfold addArbitrary
  split
  · assumption
  · generalize_proofs h1 h2 h3
    exact ⟨h1.choose, (h3 h2).choose_spec.1⟩

lemma PartialSolution.addArbitrary_contains [Infinite G] (a b : G) :
    ∀ x y z, ps.R x y z → (ps.addArbitrary a b).R x y z := by
  unfold addArbitrary
  split
  · simp
  · generalize_proofs v1 v2 v3
    exact (v3 v2).choose_spec.2

variable (ps : PartialSolution ℕ)

include ps in
noncomputable def PartialSolution.complSeq : ℕ → PartialSolution ℕ
| 0 => ps
| n+1 => (complSeq n).addArbitrary n.unpair.1 n.unpair.2

lemma PartialSolution.complSeq_exists (a b : ℕ) : ∃ c, (complSeq ps (Nat.pair a b + 1)).R a b c := by
  simp [complSeq]
  apply addArbitrary_covers

lemma PartialSolution.complSeq_mono_add_one (i : ℕ) (a b c : ℕ) (h : (complSeq ps i).R a b c) :
    (complSeq ps (i + 1)).R a b c := by
  simp [complSeq]
  apply addArbitrary_contains
  exact h

lemma PartialSolution.complSeq_mono (i j : ℕ) (hij : i ≤ j) (a b c : ℕ) (h : (complSeq ps i).R a b c) :
    (complSeq ps j).R a b c := by
  induction hij
  · exact h
  · apply ps.complSeq_mono_add_one
    assumption

lemma PartialSolution.complSeq_exists_of_lt (a b i : ℕ) (h : Nat.pair a b < i) :
    ∃ c, (complSeq ps i).R a b c := by
  obtain ⟨c, hc⟩ := ps.complSeq_exists a b
  use c
  apply complSeq_mono _ _ _ _ _ _ _ hc
  omega

noncomputable def PartialSolution.compl (a b c : ℕ) : Prop :=
  (ps.complSeq (Nat.pair a b + 1)).R a b c

theorem PartialSolution.compl_rule0 (a b c d : ℕ)
    (h : ps.compl a b c) (h2 : ps.compl a b d) : c = d := by
  unfold compl at *
  have := (ps.complSeq (Nat.pair a b + 1)).rule_0 a b c d
  simp_all

theorem PartialSolution.compl_exists (a b : ℕ) : ∃ c, ps.compl a b c :=
  complSeq_exists ..

lemma PartialSolution.complSeq_of_compl_of_lt (a b i : ℕ) (habi : Nat.pair a b < i)
    (c : ℕ) (h : ps.compl a b c) : (ps.complSeq i).R a b c :=
  PartialSolution.complSeq_mono _ _ _ (by omega) _ _ _ h

lemma PartialSolution.complSeq_iff_of_lt (a b i : ℕ) (habi : Nat.pair a b < i)
    (c : ℕ) : ps.compl a b c ↔ (ps.complSeq i).R a b c := by
  constructor
  · intro
    apply PartialSolution.complSeq_of_compl_of_lt <;> assumption
  · intro h
    have ⟨c', hc⟩ := ps.compl_exists a b
    convert hc
    have := ps.complSeq_of_compl_of_lt a b i habi c' hc
    have := (ps.complSeq i).rule_0 a b c c'
    simp_all

theorem PartialSolution.compl_rule1 (X0 X1 X2 X3 : ℕ) :
    ¬ ps.compl X0 X1 X2 ∨ ¬ ps.compl X2 X1 X3 ∨ ps.compl X1 X3 X0 := by
  let i := 1 + max (Nat.pair X0 X1) (max (Nat.pair X2 X1) (max (Nat.pair X1 X3) 0))
  repeat rw [PartialSolution.complSeq_iff_of_lt _ _ _ i]
  apply PartialSolution.rule_1
  all_goals omega

noncomputable def PartialSolution.complFun (a b : ℕ) : ℕ := (ps.compl_exists a b).choose

theorem PartialSolution.complFun_eq_iff (a b c : ℕ) : ps.complFun a b = c ↔ ps.compl a b c := by
  constructor
  · rintro rfl
    exact (ps.compl_exists a b).choose_spec
  · intro h
    have : ps.compl a b (ps.complFun a b) := (ps.compl_exists a b).choose_spec
    exact ps.compl_rule0 a b _ _ this h

lemma PartialSolution.of_R (a b c : ℕ) (h : ps.R a b c) : ps.complFun a b = c := by
  rw [PartialSolution.complFun_eq_iff]
  apply PartialSolution.complSeq_mono _ 0 _ (by simp) _ _ _ h

noncomputable def PartialSolution.toMagma : Magma ℕ where
  op := ps.complFun

theorem PartialSolution.toMagma_equation118 :
    letI := ps.toMagma
    Equation118 ℕ := by
  simp only [Equation118, PartialSolution.toMagma]
  intro X0 X1
  simpa [← PartialSolution.complFun_eq_iff, eq_comm] using
    ps.compl_rule1 X0 X1 (ps.complFun X0 X1) (ps.complFun (ps.complFun X0 X1) X1)


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter222 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 2, 3), (2, 3, 1)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  rule_4 := by simp only [← imp_iff_not_or]; aesop
  rule_5 := by simp only [← imp_iff_not_or]; aesop
  rule_6 := by simp only [← imp_iff_not_or]; aesop
  rule_7 := by simp only [← imp_iff_not_or]; aesop
  rule_8 := by simp only [← imp_iff_not_or]; aesop
  rule_9 := by simp only [← imp_iff_not_or]; aesop
  rule_10 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation118_not_implies_Equation222 : ∃ (G : Type) (_ : Magma G), Equation118 G ∧ ¬Equation222 G := by
  use ℕ, PartialSolution.counter222.toMagma, PartialSolution.counter222.toMagma_equation118
  simp only [not_forall, PartialSolution.toMagma]
  use 1, 2
  repeat (first | rw [PartialSolution.counter222.of_R 1 2 3] | rw [PartialSolution.counter222.of_R 2 3 1])
  all_goals simp [PartialSolution.counter222]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter274 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 1), (1, 2, 3), (1, 3, 3), (3, 1, 3)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  rule_4 := by simp only [← imp_iff_not_or]; aesop
  rule_5 := by simp only [← imp_iff_not_or]; aesop
  rule_6 := by simp only [← imp_iff_not_or]; aesop
  rule_7 := by simp only [← imp_iff_not_or]; aesop
  rule_8 := by simp only [← imp_iff_not_or]; aesop
  rule_9 := by simp only [← imp_iff_not_or]; aesop
  rule_10 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation118_not_implies_Equation274 : ∃ (G : Type) (_ : Magma G), Equation118 G ∧ ¬Equation274 G := by
  use ℕ, PartialSolution.counter274.toMagma, PartialSolution.counter274.toMagma_equation118
  simp only [not_forall, PartialSolution.toMagma]
  use 2, 1
  repeat (first | rw [PartialSolution.counter274.of_R 1 1 1] | rw [PartialSolution.counter274.of_R 1 2 3] | rw [PartialSolution.counter274.of_R 1 3 3] | rw [PartialSolution.counter274.of_R 3 1 3])
  all_goals simp [PartialSolution.counter274]


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter4435 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 2, 3), (2, 1, 3), (2, 3, 1), (2, 4, 1), (3, 2, 4)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  rule_4 := by simp only [← imp_iff_not_or]; aesop
  rule_5 := by simp only [← imp_iff_not_or]; aesop
  rule_6 := by simp only [← imp_iff_not_or]; aesop
  rule_7 := by simp only [← imp_iff_not_or]; aesop
  rule_8 := by simp only [← imp_iff_not_or]; aesop
  rule_9 := by simp only [← imp_iff_not_or]; aesop
  rule_10 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2, 3, 4}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation118_not_implies_Equation4435 : ∃ (G : Type) (_ : Magma G), Equation118 G ∧ ¬Equation4435 G := by
  use ℕ, PartialSolution.counter4435.toMagma, PartialSolution.counter4435.toMagma_equation118
  simp only [not_forall, PartialSolution.toMagma]
  use 2, 1
  repeat (first | rw [PartialSolution.counter4435.of_R 1 2 3] | rw [PartialSolution.counter4435.of_R 2 1 3] | rw [PartialSolution.counter4435.of_R 2 3 1] | rw [PartialSolution.counter4435.of_R 2 4 1] | rw [PartialSolution.counter4435.of_R 3 2 4])
  all_goals simp [PartialSolution.counter4435]

end Eq118
