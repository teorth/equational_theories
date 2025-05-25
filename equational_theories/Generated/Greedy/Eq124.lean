import equational_theories.Equations.All
import equational_theories.Generated.Greedy.OrLemmas
import equational_theories.Superposition
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Pairing

namespace Eq124

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_0 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X0 X1 X3 ∨ X2 = X3)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), a = b ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), a = b ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = X ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = b ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = X ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP4 X Y Z) (rule_def_5_0 : ∀ (X Y Z : G), a = b ∨ ¬sP5 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP5 X Y Z) (rule_def_6_0 : ∀ (X Y Z : G), a = b ∨ ¬sP6 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP6 X Y Z) (rule_def_6_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP6 X Y Z) (rule_def_7_0 : ∀ (X Y Z : G), a = b ∨ ¬sP7 X Y Z) (rule_def_7_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP7 X Y Z) (rule_def_7_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP7 X Y Z) (rule_def_8_0 : ∀ (X Y Z : G), a = b ∨ ¬sP8 X Y Z) (rule_def_8_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP8 X Y Z) (rule_def_8_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP8 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq203 : (sP8 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 173,174
  have eq204 : (sP8 sk0 sk1 sk3) ∨ (sP6 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) := resolve new_imp preserve_1 -- resolution 173,175
  have eq212 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ b = sk2 := resolve eq203 rule_def_8_3 -- resolution 203,171
  have eq213 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ c = sk1 := resolve eq203 rule_def_8_2 -- resolution 203,170
  have eq215 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ a = b := resolve eq203 rule_def_8_0 -- resolution 203,168
  have eq216 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq212 rule_def_7_3 -- subsumption resolution 212,166
  have eq217 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq216 rule_def_6_3 -- subsumption resolution 216,161
  have eq218 : (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq217 rule_def_5_3 -- subsumption resolution 217,156
  have eq219 : (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq218 rule_def_1_1 -- subsumption resolution 218,135
  have eq220 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq213 rule_def_7_2 -- subsumption resolution 213,165
  have eq221 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq220 rule_def_6_2 -- subsumption resolution 220,160
  have eq222 : (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq221 rule_def_5_2 -- subsumption resolution 221,155
  have eq223 : (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq222 rule_def_1_0 -- subsumption resolution 222,134
  have eq224 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = b := resolve eq215 rule_def_7_0 -- subsumption resolution 215,163
  have eq225 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = b := resolve eq224 rule_def_6_0 -- subsumption resolution 224,158
  have eq226 : (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = b := resolve eq225 rule_def_5_0 -- subsumption resolution 225,153
  have eq227 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = b := resolve eq226 rule_def_4_0 -- subsumption resolution 226,148
  have eq228 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = b := resolve eq227 rule_def_3_0 -- subsumption resolution 227,143
  have eq229 : (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = b := resolve eq228 rule_def_2_0 -- subsumption resolution 228,138
  have eq231 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = b ∨ b = sk2 := resolve eq229 rule_def_1_1 -- resolution 229,135
  have eq232 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = b ∨ c = sk1 := resolve eq229 rule_def_1_0 -- resolution 229,134
  have eq233 : (sP6 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ b = sk3 := resolve eq204 rule_def_8_3 -- resolution 204,171
  have eq234 : (sP6 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ c = sk1 := resolve eq204 rule_def_8_2 -- resolution 204,170
  have eq236 : (sP6 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ (sP7 sk0 sk1 sk3) ∨ a = b := resolve eq204 rule_def_8_0 -- resolution 204,168
  have eq237 : (sP6 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk3 := resolve eq233 rule_def_7_3 -- subsumption resolution 233,166
  have eq238 : (sP5 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk3 := resolve eq237 rule_def_6_3 -- subsumption resolution 237,161
  have eq239 : (sP4 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk3 := resolve eq238 rule_def_5_3 -- subsumption resolution 238,156
  have eq240 : (sP4 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk3 := resolve eq239 rule_def_1_1 -- subsumption resolution 239,135
  have eq241 : (sP6 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk1 := resolve eq234 rule_def_7_2 -- subsumption resolution 234,165
  have eq242 : (sP5 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk1 := resolve eq241 rule_def_6_2 -- subsumption resolution 241,160
  have eq243 : (sP4 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk1 := resolve eq242 rule_def_5_2 -- subsumption resolution 242,155
  have eq244 : (sP4 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk1 := resolve eq243 rule_def_1_0 -- subsumption resolution 243,134
  have eq245 : (sP6 sk0 sk1 sk3) ∨ (sP5 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = b := resolve eq236 rule_def_7_0 -- subsumption resolution 236,163
  have eq246 : (sP5 sk0 sk1 sk3) ∨ (sP4 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = b := resolve eq245 rule_def_6_0 -- subsumption resolution 245,158
  have eq247 : (sP4 sk0 sk1 sk3) ∨ (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = b := resolve eq246 rule_def_5_0 -- subsumption resolution 246,153
  have eq248 : (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = b := resolve eq247 rule_def_4_0 -- subsumption resolution 247,148
  have eq249 : (sP2 sk0 sk1 sk3) ∨ (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = b := resolve eq248 rule_def_3_0 -- subsumption resolution 248,143
  have eq250 : (sP1 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = b := resolve eq249 rule_def_2_0 -- subsumption resolution 249,138
  have eq252 : (old sk0 sk1 sk2) ∨ a = b ∨ b = sk2 ∨ b = sk1 := resolve eq231 rule_def_0_1 -- resolution 231,131
  have eq255 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ a = b ∨ b = sk3 := resolve eq250 rule_def_1_1 -- resolution 250,135
  have eq260 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 ∨ c = sk2 := resolve eq219 rule_def_4_3 -- resolution 219,151
  have eq261 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 ∨ b = sk1 := resolve eq219 rule_def_4_2 -- resolution 219,150
  have eq264 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 ∨ c = sk2 := resolve eq260 rule_def_3_3 -- subsumption resolution 260,146
  have eq265 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 ∨ c = sk2 := resolve eq264 rule_def_2_3 -- subsumption resolution 264,141
  have eq266 : (old sk0 sk1 sk2) ∨ b = sk2 ∨ c = sk2 := resolve eq265 rule_def_0_2 -- subsumption resolution 265,132
  have eq267 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 ∨ b = sk1 := resolve eq261 rule_def_3_2 -- subsumption resolution 261,145
  have eq268 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 ∨ b = sk1 := resolve eq267 rule_def_2_2 -- subsumption resolution 267,140
  have eq269 : (old sk0 sk1 sk2) ∨ b = sk2 ∨ b = sk1 := resolve eq268 rule_def_0_1 -- subsumption resolution 268,131
  have eq275 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq223 rule_def_4_3 -- resolution 223,151
  have eq277 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk0 := resolve eq223 rule_def_4_1 -- resolution 223,149
  have eq279 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq275 rule_def_3_3 -- subsumption resolution 275,146
  have eq280 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq279 rule_def_2_3 -- subsumption resolution 279,141
  have eq281 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq280 rule_def_0_2 -- subsumption resolution 280,132
  have eq285 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk0 := resolve eq277 rule_def_3_1 -- subsumption resolution 277,144
  have eq286 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk0 := resolve eq285 rule_def_2_1 -- subsumption resolution 285,139
  have eq288 (X0 : G) : ¬(old sk0 sk1 X0) ∨ b = sk1 ∨ sk2 = X0 ∨ b = sk2 := resolve eq269 old_0 -- resolution 269,122
  have eq290 : (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk3 ∨ c = sk3 := resolve eq240 rule_def_4_3 -- resolution 240,151
  have eq291 : (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk3 ∨ b = sk1 := resolve eq240 rule_def_4_2 -- resolution 240,150
  have eq292 : (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk3 ∨ c = sk0 := resolve eq240 rule_def_4_1 -- resolution 240,149
  have eq294 : (sP2 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk3 ∨ c = sk3 := resolve eq290 rule_def_3_3 -- subsumption resolution 290,146
  have eq295 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk3 ∨ c = sk3 := resolve eq294 rule_def_2_3 -- subsumption resolution 294,141
  have eq296 : (old sk0 sk1 sk3) ∨ b = sk3 ∨ c = sk3 := resolve eq295 rule_def_0_2 -- subsumption resolution 295,132
  have eq297 : (sP2 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk3 ∨ b = sk1 := resolve eq291 rule_def_3_2 -- subsumption resolution 291,145
  have eq298 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk3 ∨ b = sk1 := resolve eq297 rule_def_2_2 -- subsumption resolution 297,140
  have eq299 : (old sk0 sk1 sk3) ∨ b = sk3 ∨ b = sk1 := resolve eq298 rule_def_0_1 -- subsumption resolution 298,131
  have eq300 : (sP2 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk3 ∨ c = sk0 := resolve eq292 rule_def_3_1 -- subsumption resolution 292,144
  have eq301 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ b = sk3 ∨ c = sk0 := resolve eq300 rule_def_2_1 -- subsumption resolution 300,139
  have eq303 (X0 : G) : ¬(old sk0 sk1 X0) ∨ c = sk2 ∨ sk2 = X0 ∨ c = sk1 := resolve eq281 old_0 -- resolution 281,122
  have eq305 : (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk1 ∨ c = sk3 := resolve eq244 rule_def_4_3 -- resolution 244,151
  have eq306 : (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk1 ∨ b = sk1 := resolve eq244 rule_def_4_2 -- resolution 244,150
  have eq309 : (sP2 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk1 ∨ c = sk3 := resolve eq305 rule_def_3_3 -- subsumption resolution 305,146
  have eq310 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk1 ∨ c = sk3 := resolve eq309 rule_def_2_3 -- subsumption resolution 309,141
  have eq311 : (old sk0 sk1 sk3) ∨ c = sk1 ∨ c = sk3 := resolve eq310 rule_def_0_2 -- subsumption resolution 310,132
  have eq312 : (sP2 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk1 ∨ b = sk1 := resolve eq306 rule_def_3_2 -- subsumption resolution 306,145
  have eq313 : (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) ∨ c = sk1 ∨ b = sk1 := resolve eq312 rule_def_2_2 -- subsumption resolution 312,140
  have eq314 : (old sk0 sk1 sk3) ∨ c = sk1 ∨ b = sk1 := resolve eq313 rule_def_0_1 -- subsumption resolution 313,131
  have eq350 (X0 : G) : ¬(old sk0 sk1 X0) ∨ c = sk3 ∨ sk3 = X0 ∨ c = sk1 := resolve eq311 old_0 -- resolution 311,122
  have eq360 : (old sk0 sk1 sk2) ∨ a = b ∨ c = sk1 ∨ a = sk0 := resolve eq232 rule_def_0_0 -- resolution 232,130
  have eq366 : (old sk0 sk1 sk3) ∨ a = b ∨ b = sk3 ∨ a = sk0 := resolve eq255 rule_def_0_0 -- resolution 255,130
  have eq440 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq286 rule_def_0_0 -- resolution 286,130
  have eq471 : (old sk0 sk1 sk3) ∨ b = sk3 ∨ c = sk0 ∨ a = sk0 := resolve eq301 rule_def_0_0 -- resolution 301,130
  have eq504 : b = sk1 ∨ sk2 = sk3 ∨ b = sk2 ∨ c = sk1 ∨ b = sk1 := resolve eq288 eq314 -- resolution 288,314
  have eq509 : b = sk1 ∨ sk2 = sk3 ∨ b = sk2 ∨ c = sk1 := resolve eq504 rfl -- duplicate literal removal 504
  have eq516 : b = sk2 ∨ b = sk1 ∨ c = sk1 := resolve eq509 preserve_2 -- subsumption resolution 509,176
  have eq621 : c = sk2 ∨ sk2 = sk3 ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 := resolve eq303 eq314 -- resolution 303,314
  have eq622 : c = sk2 ∨ sk2 = sk3 ∨ c = sk1 ∨ c = sk1 ∨ c = sk3 := resolve eq303 eq311 -- resolution 303,311
  have eq627 : c = sk2 ∨ sk2 = sk3 ∨ c = sk1 ∨ c = sk3 := resolve eq622 rfl -- duplicate literal removal 622
  have eq628 : c = sk2 ∨ sk2 = sk3 ∨ c = sk1 ∨ b = sk1 := resolve eq621 rfl -- duplicate literal removal 621
  have eq633 : c = sk2 ∨ c = sk1 ∨ b = sk1 := resolve eq628 preserve_2 -- subsumption resolution 628,176
  have eq634 : c = sk3 ∨ c = sk1 ∨ c = sk2 := resolve eq627 preserve_2 -- subsumption resolution 627,176
  have eq635 : c = b ∨ c = sk1 ∨ b = sk1 ∨ b = sk1 ∨ c = sk1 := Or.assoc3 (eq516.imp_left (fun h : b = sk2 ↦ superpose h eq633)) -- superposition 633,516, 516 into 633, unify on (0).2 in 516 and (0).2 in 633
  have eq662 : c = b ∨ c = sk1 ∨ b = sk1 := resolve eq635 rfl -- duplicate literal removal 635
  have eq663 : b = sk1 ∨ c = sk1 := resolve eq662 bc -- subsumption resolution 662,117
  have eq707 : (old sk0 b sk2) ∨ c = b ∨ c = sk2 ∨ c = sk1 := Or.assoc3 (eq663.imp_left (fun h : b = sk1 ↦ superpose h eq281)) -- superposition 281,663, 663 into 281, unify on (0).2 in 663 and (0).2 in 281
  have eq712 : (old sk0 b sk3) ∨ c = b ∨ c = sk3 ∨ c = sk1 := Or.assoc3 (eq663.imp_left (fun h : b = sk1 ↦ superpose h eq311)) -- superposition 311,663, 663 into 311, unify on (0).2 in 663 and (0).2 in 311
  have eq721 : (old sk0 b sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq707 bc -- subsumption resolution 707,117
  have eq724 : (old sk0 b sk3) ∨ c = sk3 ∨ c = sk1 := resolve eq712 bc -- subsumption resolution 712,117
  have eq864 : a = b ∨ c = sk1 ∨ a = sk0 ∨ c = sk3 ∨ sk2 = sk3 ∨ c = sk1 := resolve eq360 eq350 -- resolution 360,350
  have eq877 : a = b ∨ c = sk1 ∨ a = sk0 ∨ c = sk3 ∨ sk2 = sk3 := resolve eq864 rfl -- duplicate literal removal 864
  have eq881 : c = sk3 ∨ c = sk1 ∨ a = sk0 ∨ a = b := resolve eq877 preserve_2 -- subsumption resolution 877,176
  have eq902 : (old sk0 sk1 c) ∨ a = b ∨ c = b ∨ a = sk0 ∨ c = sk1 ∨ c = sk2 := Or.assoc4 (eq634.imp_left (fun h : c = sk3 ↦ superpose h eq366)) -- superposition 366,634, 634 into 366, unify on (0).2 in 634 and (0).3 in 366
  have eq908 : a = b ∨ c = b ∨ a = sk0 ∨ c = sk1 ∨ c = sk2 := resolve eq902 p4XY -- subsumption resolution 902,119
  have eq909 : a = b ∨ a = sk0 ∨ c = sk1 ∨ c = sk2 := resolve eq908 bc -- subsumption resolution 908,117
  have eq963 : c ≠ sk2 ∨ c = sk1 ∨ a = sk0 ∨ a = b := eq881.imp_left (fun h : c = sk3 ↦ superpose h preserve_2) -- superposition 176,881, 881 into 176, unify on (0).2 in 881 and (0).2 in 176
  have eq992 : c = sk1 ∨ a = sk0 ∨ a = b := resolve eq963 eq909 -- subsumption resolution 963,909
  have eq999 : c = sk1 ∨ c = sk0 ∨ a = sk0 ∨ c = sk3 ∨ sk2 = sk3 ∨ c = sk1 := resolve eq440 eq350 -- resolution 440,350
  have eq1012 : c = sk1 ∨ c = sk0 ∨ a = sk0 ∨ c = sk3 ∨ sk2 = sk3 := resolve eq999 rfl -- duplicate literal removal 999
  have eq1016 : c = sk1 ∨ c = sk0 ∨ a = sk0 ∨ c = sk3 := resolve eq1012 preserve_2 -- subsumption resolution 1012,176
  have eq1024 : (sP4 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ (old sk0 c sk2) ∨ b = sk2 ∨ a = sk0 ∨ a = b := Or.assoc6 (eq992.imp_left (fun h : c = sk1 ↦ superpose h eq219)) -- superposition 219,992, 992 into 219, unify on (0).2 in 992 and (0).2 in 219
  have eq1029 : (sP4 sk0 c sk3) ∨ (sP3 sk0 c sk3) ∨ (sP2 sk0 c sk3) ∨ (sP0 sk0 c sk3) ∨ (old sk0 c sk3) ∨ b = sk3 ∨ a = sk0 ∨ a = b := Or.assoc6 (eq992.imp_left (fun h : c = sk1 ↦ superpose h eq240)) -- superposition 240,992, 992 into 240, unify on (0).2 in 992 and (0).2 in 240
  have eq1080 : (sP4 sk0 c sk2) ∨ (sP3 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ b = sk2 ∨ a = sk0 ∨ a = b := resolve eq1024 p4XZ -- subsumption resolution 1024,120
  have eq1081 : (sP3 sk0 c sk2) ∨ (sP2 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ b = sk2 ∨ a = sk0 ∨ a = b := resolve eq1080 rule_def_4_0 -- subsumption resolution 1080,148
  have eq1082 : (sP2 sk0 c sk2) ∨ (sP0 sk0 c sk2) ∨ b = sk2 ∨ a = sk0 ∨ a = b := resolve eq1081 rule_def_3_0 -- subsumption resolution 1081,143
  have eq1083 : (sP0 sk0 c sk2) ∨ b = sk2 ∨ a = sk0 ∨ a = b := resolve eq1082 rule_def_2_0 -- subsumption resolution 1082,138
  have eq1084 : b = sk2 ∨ a = sk0 ∨ a = b := resolve eq1083 rule_def_0_0 -- subsumption resolution 1083,130
  have eq1087 : (sP4 sk0 c sk3) ∨ (sP3 sk0 c sk3) ∨ (sP2 sk0 c sk3) ∨ (sP0 sk0 c sk3) ∨ b = sk3 ∨ a = sk0 ∨ a = b := resolve eq1029 p4XZ -- subsumption resolution 1029,120
  have eq1088 : (sP3 sk0 c sk3) ∨ (sP2 sk0 c sk3) ∨ (sP0 sk0 c sk3) ∨ b = sk3 ∨ a = sk0 ∨ a = b := resolve eq1087 rule_def_4_0 -- subsumption resolution 1087,148
  have eq1089 : (sP2 sk0 c sk3) ∨ (sP0 sk0 c sk3) ∨ b = sk3 ∨ a = sk0 ∨ a = b := resolve eq1088 rule_def_3_0 -- subsumption resolution 1088,143
  have eq1090 : (sP0 sk0 c sk3) ∨ b = sk3 ∨ a = sk0 ∨ a = b := resolve eq1089 rule_def_2_0 -- subsumption resolution 1089,138
  have eq1091 : b = sk3 ∨ a = sk0 ∨ a = b := resolve eq1090 rule_def_0_0 -- subsumption resolution 1090,130
  have eq1106 : (old sk0 sk1 c) ∨ c = b ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ c = sk2 := Or.assoc4 (eq634.imp_left (fun h : c = sk3 ↦ superpose h eq471)) -- superposition 471,634, 634 into 471, unify on (0).2 in 634 and (0).3 in 471
  have eq1114 : c = b ∨ c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ c = sk2 := resolve eq1106 p4XY -- subsumption resolution 1106,119
  have eq1115 : c = sk0 ∨ a = sk0 ∨ c = sk1 ∨ c = sk2 := resolve eq1114 bc -- subsumption resolution 1114,117
  have eq1176 : b ≠ sk2 ∨ a = sk0 ∨ a = b := eq1091.imp_left (fun h : b = sk3 ↦ superpose h preserve_2) -- superposition 176,1091, 1091 into 176, unify on (0).2 in 1091 and (0).2 in 176
  have eq1201 : a = sk0 ∨ a = b := resolve eq1176 eq1084 -- subsumption resolution 1176,1084
  have eq1252 : (old a b sk2) ∨ c = sk2 ∨ c = sk1 ∨ a = b := Or.assoc3 (eq1201.imp_left (fun h : a = sk0 ↦ superpose h eq721)) -- superposition 721,1201, 1201 into 721, unify on (0).2 in 1201 and (0).1 in 721
  have eq1253 : (old a b sk3) ∨ c = sk3 ∨ c = sk1 ∨ a = b := Or.assoc3 (eq1201.imp_left (fun h : a = sk0 ↦ superpose h eq724)) -- superposition 724,1201, 1201 into 724, unify on (0).2 in 1201 and (0).1 in 724
  have eq1298 : c = sk2 ∨ c = sk1 ∨ a = b := resolve eq1252 p3 -- subsumption resolution 1252,118
  have eq1299 : c = sk3 ∨ c = sk1 ∨ a = b := resolve eq1253 p3 -- subsumption resolution 1253,118
  have eq1388 : c ≠ sk2 ∨ c = sk1 ∨ a = b := eq1299.imp_left (fun h : c = sk3 ↦ superpose h preserve_2) -- superposition 176,1299, 1299 into 176, unify on (0).2 in 1299 and (0).2 in 176
  have eq1425 : c = sk1 ∨ a = b := resolve eq1388 eq1298 -- subsumption resolution 1388,1298
  have eq1442 : (old sk0 c sk2) ∨ a = b ∨ b = sk2 ∨ c = b ∨ a = b := Or.assoc4 (eq1425.imp_left (fun h : c = sk1 ↦ superpose h eq252)) -- superposition 252,1425, 1425 into 252, unify on (0).2 in 1425 and (0).2 in 252
  have eq1454 : (old sk0 c sk3) ∨ b = sk3 ∨ c = b ∨ a = b := Or.assoc3 (eq1425.imp_left (fun h : c = sk1 ↦ superpose h eq299)) -- superposition 299,1425, 1425 into 299, unify on (0).2 in 1425 and (0).2 in 299
  have eq1474 : (old sk0 c sk2) ∨ a = b ∨ b = sk2 ∨ c = b := resolve eq1442 rfl -- duplicate literal removal 1442
  have eq1506 : a = b ∨ b = sk2 ∨ c = b := resolve eq1474 p4XZ -- subsumption resolution 1474,120
  have eq1507 : b = sk2 ∨ a = b := resolve eq1506 bc -- subsumption resolution 1506,117
  have eq1510 : b = sk3 ∨ c = b ∨ a = b := resolve eq1454 p4XZ -- subsumption resolution 1454,120
  have eq1511 : b = sk3 ∨ a = b := resolve eq1510 bc -- subsumption resolution 1510,117
  have eq1554 : b ≠ sk2 ∨ a = b := eq1511.imp_left (fun h : b = sk3 ↦ superpose h preserve_2) -- superposition 176,1511, 1511 into 176, unify on (0).2 in 1511 and (0).2 in 176
  have eq1583 : a = b := resolve eq1554 eq1507 -- subsumption resolution 1554,1507
  have eq1585 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq1583, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 118,1583
  have eq1586 : ∀ (X0 X1 X2 : G) , ¬(sP0 X0 X1 X2) ∨ a = X1 := Eq.mp (by simp only [eq1583, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_0_1 -- backward demodulation 131,1583
  have eq1589 : ∀ (X0 X1 X2 : G) , ¬(sP2 X0 X1 X2) ∨ a = X1 := Eq.mp (by simp only [eq1583, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_2_2 -- backward demodulation 140,1583
  have eq1590 : ∀ (X0 X1 X2 : G) , ¬(sP3 X0 X1 X2) ∨ a = X1 := Eq.mp (by simp only [eq1583, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_3_2 -- backward demodulation 145,1583
  have eq1591 : ∀ (X0 X1 X2 : G) , ¬(sP4 X0 X1 X2) ∨ a = X1 := Eq.mp (by simp only [eq1583, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) rule_def_4_2 -- backward demodulation 150,1583
  have eq1605 : (sP4 sk0 sk1 sk2) ∨ a = sk2 ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq1583, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq219 -- backward demodulation 219,1583
  have eq1607 : (sP4 sk0 sk1 sk3) ∨ a = sk3 ∨ (sP3 sk0 sk1 sk3) ∨ (sP2 sk0 sk1 sk3) ∨ (sP0 sk0 sk1 sk3) ∨ (old sk0 sk1 sk3) := Eq.mp (by simp only [eq1583, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq240 -- backward demodulation 240,1583
  have eq1608 : (old sk0 sk1 sk2) ∨ a = sk2 ∨ c = sk2 := Eq.mp (by simp only [eq1583, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq266 -- backward demodulation 266,1583
  have eq1616 : (old sk0 sk1 sk3) ∨ a = sk3 ∨ c = sk3 := Eq.mp (by simp only [eq1583, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq296 -- backward demodulation 296,1583
  have eq1663 : c = sk1 ∨ a = sk1 := Eq.mp (by simp only [eq1583, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq663 -- backward demodulation 663,1583
  have eq1994 : (old sk0 c sk2) ∨ a = sk2 ∨ c = sk2 ∨ a = sk1 := Or.assoc3 (eq1663.imp_left (fun h : c = sk1 ↦ superpose h eq1608)) -- superposition 1608,1663, 1663 into 1608, unify on (0).2 in 1663 and (0).2 in 1608
  have eq1996 : c = sk2 ∨ a = sk2 ∨ a = sk1 := resolve eq1994 p4XZ -- subsumption resolution 1994,120
  have eq2008 : (sP4 sk0 sk1 c) ∨ a = c ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ a = sk2 ∨ a = sk1 := Or.assoc6 (eq1996.imp_left (fun h : c = sk2 ↦ superpose h eq1605)) -- superposition 1605,1996, 1996 into 1605, unify on (0).2 in 1996 and (0).3 in 1605
  have eq2020 : (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ a = sk2 ∨ a = sk1 := resolve eq2008 ac -- subsumption resolution 2008,116
  have eq2021 : (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ a = sk2 ∨ a = sk1 := resolve eq2020 p4XY -- subsumption resolution 2020,119
  have eq2022 : (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ a = sk2 ∨ a = sk1 := resolve eq2021 eq1591 -- subsumption resolution 2021,1591
  have eq2023 : (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ a = sk2 ∨ a = sk1 := resolve eq2022 eq1590 -- subsumption resolution 2022,1590
  have eq2024 : (sP0 sk0 sk1 c) ∨ a = sk2 ∨ a = sk1 := resolve eq2023 eq1589 -- subsumption resolution 2023,1589
  have eq2025 : a = sk2 ∨ a = sk1 := resolve eq2024 eq1586 -- subsumption resolution 2024,1586
  have eq2115 : (old sk0 c sk3) ∨ a = sk3 ∨ c = sk3 ∨ a = sk1 := Or.assoc3 (eq1663.imp_left (fun h : c = sk1 ↦ superpose h eq1616)) -- superposition 1616,1663, 1663 into 1616, unify on (0).2 in 1663 and (0).2 in 1616
  have eq2117 : c = sk3 ∨ a = sk3 ∨ a = sk1 := resolve eq2115 p4XZ -- subsumption resolution 2115,120
  have eq2135 : (sP4 sk0 sk1 c) ∨ a = c ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ a = sk3 ∨ a = sk1 := Or.assoc6 (eq2117.imp_left (fun h : c = sk3 ↦ superpose h eq1607)) -- superposition 1607,2117, 2117 into 1607, unify on (0).2 in 2117 and (0).3 in 1607
  have eq2150 : (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ a = sk3 ∨ a = sk1 := resolve eq2135 ac -- subsumption resolution 2135,116
  have eq2151 : (sP4 sk0 sk1 c) ∨ (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ a = sk3 ∨ a = sk1 := resolve eq2150 p4XY -- subsumption resolution 2150,119
  have eq2152 : (sP3 sk0 sk1 c) ∨ (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ a = sk3 ∨ a = sk1 := resolve eq2151 eq1591 -- subsumption resolution 2151,1591
  have eq2153 : (sP2 sk0 sk1 c) ∨ (sP0 sk0 sk1 c) ∨ a = sk3 ∨ a = sk1 := resolve eq2152 eq1590 -- subsumption resolution 2152,1590
  have eq2154 : (sP0 sk0 sk1 c) ∨ a = sk3 ∨ a = sk1 := resolve eq2153 eq1589 -- subsumption resolution 2153,1589
  have eq2155 : a = sk3 ∨ a = sk1 := resolve eq2154 eq1586 -- subsumption resolution 2154,1586
  have eq2169 : a ≠ sk2 ∨ a = sk1 := eq2155.imp_left (fun h : a = sk3 ↦ superpose h preserve_2) -- superposition 176,2155, 2155 into 176, unify on (0).2 in 2155 and (0).2 in 176
  have eq2183 : a = sk1 := resolve eq2169 eq2025 -- subsumption resolution 2169,2025
  have eq2190 : (old sk0 a sk2) ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq2183, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq281 -- backward demodulation 281,2183
  have eq2194 : (old sk0 a sk3) ∨ c = sk1 ∨ c = sk3 := Eq.mp (by simp only [eq2183, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq311 -- backward demodulation 311,2183
  have eq2206 : a = c ∨ c = sk0 ∨ a = sk0 ∨ c = sk3 := Eq.mp (by simp only [eq2183, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1016 -- backward demodulation 1016,2183
  have eq2207 : a = c ∨ c = sk0 ∨ a = sk0 ∨ c = sk2 := Eq.mp (by simp only [eq2183, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1115 -- backward demodulation 1115,2183
  have eq2328 : a = c ∨ (old sk0 a sk2) ∨ c = sk2 := Eq.mp (by simp only [eq2183, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2190 -- forward demodulation 2190,2183
  have eq2329 : (old sk0 a sk2) ∨ c = sk2 := resolve eq2328 ac -- subsumption resolution 2328,116
  have eq2338 : a = c ∨ (old sk0 a sk3) ∨ c = sk3 := Eq.mp (by simp only [eq2183, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2194 -- forward demodulation 2194,2183
  have eq2339 : (old sk0 a sk3) ∨ c = sk3 := resolve eq2338 ac -- subsumption resolution 2338,116
  have eq2367 : c = sk3 ∨ a = sk0 ∨ c = sk0 := resolve eq2206 ac -- subsumption resolution 2206,116
  have eq2368 : c = sk0 ∨ a = sk0 ∨ c = sk2 := resolve eq2207 ac -- subsumption resolution 2207,116
  have eq2449 : c ≠ sk2 ∨ a = sk0 ∨ c = sk0 := eq2367.imp_left (fun h : c = sk3 ↦ superpose h preserve_2) -- superposition 176,2367, 2367 into 176, unify on (0).2 in 2367 and (0).2 in 176
  have eq2453 : c = sk0 ∨ a = sk0 := resolve eq2449 eq2368 -- subsumption resolution 2449,2368
  have eq2463 : (old c a sk2) ∨ c = sk2 ∨ a = sk0 := Or.assoc2 (eq2453.imp_left (fun h : c = sk0 ↦ superpose h eq2329)) -- superposition 2329,2453, 2453 into 2329, unify on (0).2 in 2453 and (0).1 in 2329
  have eq2464 : (old c a sk3) ∨ c = sk3 ∨ a = sk0 := Or.assoc2 (eq2453.imp_left (fun h : c = sk0 ↦ superpose h eq2339)) -- superposition 2339,2453, 2453 into 2339, unify on (0).2 in 2453 and (0).1 in 2339
  have eq2472 : c = sk2 ∨ a = sk0 := resolve eq2463 p4YZ -- subsumption resolution 2463,121
  have eq2473 : c = sk3 ∨ a = sk0 := resolve eq2464 p4YZ -- subsumption resolution 2464,121
  have eq2497 : c ≠ sk2 ∨ a = sk0 := eq2473.imp_left (fun h : c = sk3 ↦ superpose h preserve_2) -- superposition 176,2473, 2473 into 176, unify on (0).2 in 2473 and (0).2 in 176
  have eq2503 : a = sk0 := resolve eq2497 eq2472 -- subsumption resolution 2497,2472
  have eq2510 : (old a a sk2) ∨ c = sk2 := Eq.mp (by simp only [eq2503, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2329 -- backward demodulation 2329,2503
  have eq2514 : (old a a sk3) ∨ c = sk3 := Eq.mp (by simp only [eq2503, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2339 -- backward demodulation 2339,2503
  have eq2551 : c = sk2 := resolve eq2510 eq1585 -- subsumption resolution 2510,1585
  have eq2552 : c ≠ sk3 := Eq.mp (by simp only [eq2551, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_2 -- backward demodulation 176,2551
  have eq2572 : c = sk3 := resolve eq2514 eq1585 -- subsumption resolution 2514,1585
  subsumption eq2552 eq2572 -- subsumption resolution 2572,2552

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p3 : ∀ X0, ¬ old a b X0) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (prev_0 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X0 X1 X3 ∨ X2 = X3)) (old_1 : (∀ X0 X1 X2 X3, ¬ old X0 X1 X2 ∨ ¬ old X2 X1 X3 ∨ old X0 X3 X1)) (old_2 : (∀ X0 X1, ¬ old X0 X0 X1 ∨ old X1 X0 X1)) (old_5 : (∀ X0 X1, ¬ old X0 X1 X1 ∨ old X1 X1 X1)) (imp_new_1 : ∀ X Y Z, a ≠ X ∨ b ≠ Y ∨ c ≠ Z ∨ new X Y Z) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (imp_new_2 : ∀ X Y Z, c ≠ Y ∨ b ≠ Z ∨ ¬ old X b a ∨ new X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X b a ∨ ¬sP1 X Y Z) (imp_new_3 : ∀ X Y Z, a ≠ b ∨ c ≠ X ∨ b ≠ Y ∨ c ≠ Z ∨ new X Y Z) (rule_def_2_0 : ∀ (X Y Z : G), a = b ∨ ¬sP2 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP2 X Y Z) (rule_def_3_0 : ∀ (X Y Z : G), a = b ∨ ¬sP3 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = X ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP3 X Y Z) (rule_def_4_0 : ∀ (X Y Z : G), a = b ∨ ¬sP4 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = X ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP4 X Y Z) (imp_new_6 : ∀ X Y Z, a ≠ b ∨ c ≠ X ∨ c ≠ Y ∨ b ≠ Z ∨ new X Y Z) (rule_def_5_0 : ∀ (X Y Z : G), a = b ∨ ¬sP5 X Y Z) (rule_def_5_1 : ∀ (X Y Z : G), c = X ∨ ¬sP5 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP5 X Y Z) (rule_def_6_0 : ∀ (X Y Z : G), a = b ∨ ¬sP6 X Y Z) (rule_def_6_1 : ∀ (X Y Z : G), c = X ∨ ¬sP6 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP6 X Y Z) (rule_def_6_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP6 X Y Z) (rule_def_7_0 : ∀ (X Y Z : G), a = b ∨ ¬sP7 X Y Z) (rule_def_7_1 : ∀ (X Y Z : G), c = X ∨ ¬sP7 X Y Z) (rule_def_7_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP7 X Y Z) (rule_def_7_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP7 X Y Z) (imp_new_9 : ∀ X Y Z, a ≠ b ∨ b ≠ X ∨ c ≠ Y ∨ b ≠ Z ∨ new X Y Z) (rule_def_8_0 : ∀ (X Y Z : G), a = b ∨ ¬sP8 X Y Z) (rule_def_8_1 : ∀ (X Y Z : G), b = X ∨ ¬sP8 X Y Z) (rule_def_8_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP8 X Y Z) (rule_def_8_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP8 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X2 X1 X3 ∨ new X0 X3 X1) := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, sk3, preserve_0, preserve_1, preserve_2⟩ := nh
  have eq180 (X0 X1 : G) : (new X0 X1 c) ∨ b ≠ X1 ∨ a ≠ X0 := resolve imp_new_1 rfl -- equality resolution 131
  have eq181 (X0 : G) : (new X0 b c) ∨ a ≠ X0 := resolve eq180 rfl -- equality resolution 180
  have eq182 : (new a b c) := resolve eq181 rfl -- equality resolution 181
  have eq183 (X0 X1 : G) : (new X0 X1 b) ∨ ¬(old X0 b a) ∨ c ≠ X1 := resolve imp_new_2 rfl -- equality resolution 135
  have eq184 (X0 : G) : ¬(old X0 b a) ∨ (new X0 c b) := resolve eq183 rfl -- equality resolution 183
  have eq185 (X0 X1 : G) : (new X0 X1 c) ∨ b ≠ X1 ∨ c ≠ X0 ∨ a ≠ b := resolve imp_new_3 rfl -- equality resolution 139
  have eq186 (X0 : G) : (new X0 b c) ∨ c ≠ X0 ∨ a ≠ b := resolve eq185 rfl -- equality resolution 185
  have eq187 : a ≠ b ∨ (new c b c) := resolve eq186 rfl -- equality resolution 186
  have eq194 (X0 X1 : G) : (new X0 X1 b) ∨ c ≠ X1 ∨ c ≠ X0 ∨ a ≠ b := resolve imp_new_6 rfl -- equality resolution 154
  have eq195 (X0 : G) : (new X0 c b) ∨ c ≠ X0 ∨ a ≠ b := resolve eq194 rfl -- equality resolution 194
  have eq196 : a ≠ b ∨ (new c c b) := resolve eq195 rfl -- equality resolution 195
  have eq203 (X0 X1 : G) : (new X0 X1 b) ∨ c ≠ X1 ∨ b ≠ X0 ∨ a ≠ b := resolve imp_new_9 rfl -- equality resolution 169
  have eq204 (X0 : G) : (new X0 c b) ∨ b ≠ X0 ∨ a ≠ b := resolve eq203 rfl -- equality resolution 203
  have eq205 : a ≠ b ∨ (new b c b) := resolve eq204 rfl -- equality resolution 204
  have eq210 : (sP8 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 175,177
  have eq211 : (sP8 sk2 sk1 sk3) ∨ (sP6 sk2 sk1 sk3) ∨ (sP5 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP7 sk2 sk1 sk3) := resolve new_imp preserve_1 -- resolution 175,178
  have eq221 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ b = sk2 := resolve eq210 rule_def_8_3 -- resolution 210,173
  have eq222 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ c = sk1 := resolve eq210 rule_def_8_2 -- resolution 210,172
  have eq223 : (sP7 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ b = sk0 := resolve eq210 rule_def_8_1 -- resolution 210,171
  have eq224 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ a = b := resolve eq210 rule_def_8_0 -- resolution 210,170
  have eq225 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq221 rule_def_7_3 -- subsumption resolution 221,168
  have eq226 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq225 rule_def_6_3 -- subsumption resolution 225,163
  have eq227 : (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq226 rule_def_5_3 -- subsumption resolution 226,158
  have eq228 : (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq227 rule_def_1_1 -- subsumption resolution 227,137
  have eq229 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq222 rule_def_7_2 -- subsumption resolution 222,167
  have eq230 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq229 rule_def_6_2 -- subsumption resolution 229,162
  have eq231 : (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq230 rule_def_5_2 -- subsumption resolution 230,157
  have eq232 : (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq231 rule_def_1_0 -- subsumption resolution 231,136
  have eq233 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = b := resolve eq224 rule_def_7_0 -- subsumption resolution 224,165
  have eq234 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = b := resolve eq233 rule_def_6_0 -- subsumption resolution 233,160
  have eq235 : (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = b := resolve eq234 rule_def_5_0 -- subsumption resolution 234,155
  have eq236 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = b := resolve eq235 rule_def_4_0 -- subsumption resolution 235,150
  have eq237 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = b := resolve eq236 rule_def_3_0 -- subsumption resolution 236,145
  have eq238 : (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = b := resolve eq237 rule_def_2_0 -- subsumption resolution 237,140
  have eq240 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ a = b ∨ b = sk2 := resolve eq238 rule_def_1_1 -- resolution 238,137
  have eq242 : (sP6 sk2 sk1 sk3) ∨ (sP5 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP7 sk2 sk1 sk3) ∨ b = sk3 := resolve eq211 rule_def_8_3 -- resolution 211,173
  have eq243 : (sP6 sk2 sk1 sk3) ∨ (sP5 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP7 sk2 sk1 sk3) ∨ c = sk1 := resolve eq211 rule_def_8_2 -- resolution 211,172
  have eq245 : (sP6 sk2 sk1 sk3) ∨ (sP5 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ (sP7 sk2 sk1 sk3) ∨ a = b := resolve eq211 rule_def_8_0 -- resolution 211,170
  have eq246 : (sP6 sk2 sk1 sk3) ∨ (sP5 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ b = sk3 := resolve eq242 rule_def_7_3 -- subsumption resolution 242,168
  have eq247 : (sP5 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ b = sk3 := resolve eq246 rule_def_6_3 -- subsumption resolution 246,163
  have eq248 : (sP4 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ b = sk3 := resolve eq247 rule_def_5_3 -- subsumption resolution 247,158
  have eq249 : (sP4 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ b = sk3 := resolve eq248 rule_def_1_1 -- subsumption resolution 248,137
  have eq250 : (sP6 sk2 sk1 sk3) ∨ (sP5 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ c = sk1 := resolve eq243 rule_def_7_2 -- subsumption resolution 243,167
  have eq251 : (sP5 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ c = sk1 := resolve eq250 rule_def_6_2 -- subsumption resolution 250,162
  have eq252 : (sP4 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ c = sk1 := resolve eq251 rule_def_5_2 -- subsumption resolution 251,157
  have eq253 : (sP4 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ c = sk1 := resolve eq252 rule_def_1_0 -- subsumption resolution 252,136
  have eq254 : (sP6 sk2 sk1 sk3) ∨ (sP5 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ a = b := resolve eq245 rule_def_7_0 -- subsumption resolution 245,165
  have eq255 : (sP5 sk2 sk1 sk3) ∨ (sP4 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ a = b := resolve eq254 rule_def_6_0 -- subsumption resolution 254,160
  have eq256 : (sP4 sk2 sk1 sk3) ∨ (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ a = b := resolve eq255 rule_def_5_0 -- subsumption resolution 255,155
  have eq257 : (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ a = b := resolve eq256 rule_def_4_0 -- subsumption resolution 256,150
  have eq258 : (sP2 sk2 sk1 sk3) ∨ (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ a = b := resolve eq257 rule_def_3_0 -- subsumption resolution 257,145
  have eq259 : (sP1 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ a = b := resolve eq258 rule_def_2_0 -- subsumption resolution 258,140
  have eq261 : (old sk0 sk1 sk2) ∨ a = b ∨ b = sk2 ∨ b = sk1 := resolve eq240 rule_def_0_1 -- resolution 240,133
  have eq263 : (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ a = b ∨ (old sk2 b a) := resolve eq259 rule_def_1_2 -- resolution 259,138
  have eq265 : (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ a = b ∨ c = sk1 := resolve eq259 rule_def_1_0 -- resolution 259,136
  have eq271 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 ∨ c = sk0 := resolve eq228 rule_def_4_1 -- resolution 228,151
  have eq279 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 ∨ c = sk0 := resolve eq271 rule_def_3_1 -- subsumption resolution 271,146
  have eq280 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 ∨ c = sk0 := resolve eq279 rule_def_2_1 -- subsumption resolution 279,141
  have eq284 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq232 rule_def_4_3 -- resolution 232,153
  have eq285 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ b = sk1 := resolve eq232 rule_def_4_2 -- resolution 232,152
  have eq286 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk0 := resolve eq232 rule_def_4_1 -- resolution 232,151
  have eq288 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq284 rule_def_3_3 -- subsumption resolution 284,148
  have eq289 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq288 rule_def_2_3 -- subsumption resolution 288,143
  have eq290 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq289 rule_def_0_2 -- subsumption resolution 289,134
  have eq291 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ b = sk1 := resolve eq285 rule_def_3_2 -- subsumption resolution 285,147
  have eq292 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ b = sk1 := resolve eq291 rule_def_2_2 -- subsumption resolution 291,142
  have eq293 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ b = sk1 := resolve eq292 rule_def_0_1 -- subsumption resolution 292,133
  have eq294 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk0 := resolve eq286 rule_def_3_1 -- subsumption resolution 286,146
  have eq295 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk0 := resolve eq294 rule_def_2_1 -- subsumption resolution 294,141
  have eq300 : (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ b = sk3 ∨ b = sk1 := resolve eq249 rule_def_4_2 -- resolution 249,152
  have eq301 : (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ b = sk3 ∨ c = sk2 := resolve eq249 rule_def_4_1 -- resolution 249,151
  have eq306 : (sP2 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ b = sk3 ∨ b = sk1 := resolve eq300 rule_def_3_2 -- subsumption resolution 300,147
  have eq307 : (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ b = sk3 ∨ b = sk1 := resolve eq306 rule_def_2_2 -- subsumption resolution 306,142
  have eq308 : (old sk2 sk1 sk3) ∨ b = sk3 ∨ b = sk1 := resolve eq307 rule_def_0_1 -- subsumption resolution 307,133
  have eq309 : (sP2 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ b = sk3 ∨ c = sk2 := resolve eq301 rule_def_3_1 -- subsumption resolution 301,146
  have eq310 : (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ b = sk3 ∨ c = sk2 := resolve eq309 rule_def_2_1 -- subsumption resolution 309,141
  have eq314 : (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ c = sk1 ∨ c = sk3 := resolve eq253 rule_def_4_3 -- resolution 253,153
  have eq315 : (sP3 sk2 sk1 sk3) ∨ (sP2 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ c = sk1 ∨ b = sk1 := resolve eq253 rule_def_4_2 -- resolution 253,152
  have eq318 : (sP2 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ c = sk1 ∨ c = sk3 := resolve eq314 rule_def_3_3 -- subsumption resolution 314,148
  have eq319 : (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ c = sk1 ∨ c = sk3 := resolve eq318 rule_def_2_3 -- subsumption resolution 318,143
  have eq320 : (old sk2 sk1 sk3) ∨ c = sk1 ∨ c = sk3 := resolve eq319 rule_def_0_2 -- subsumption resolution 319,134
  have eq321 : (sP2 sk2 sk1 sk3) ∨ (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ c = sk1 ∨ b = sk1 := resolve eq315 rule_def_3_2 -- subsumption resolution 315,147
  have eq322 : (sP0 sk2 sk1 sk3) ∨ (old sk2 sk1 sk3) ∨ c = sk1 ∨ b = sk1 := resolve eq321 rule_def_2_2 -- subsumption resolution 321,142
  have eq323 : (old sk2 sk1 sk3) ∨ c = sk1 ∨ b = sk1 := resolve eq322 rule_def_0_1 -- subsumption resolution 322,133
  have eq339 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ b = sk0 ∨ c = sk0 := resolve eq223 rule_def_7_1 -- resolution 223,166
  have eq341 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk0 ∨ c = sk0 := resolve eq339 rule_def_6_1 -- subsumption resolution 339,161
  have eq342 : (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk0 ∨ c = sk0 := resolve eq341 rule_def_5_1 -- subsumption resolution 341,156
  have eq343 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk0 ∨ c = sk0 := resolve eq342 rule_def_4_1 -- subsumption resolution 342,151
  have eq344 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk0 ∨ c = sk0 := resolve eq343 rule_def_3_1 -- subsumption resolution 343,146
  have eq345 : (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk0 ∨ c = sk0 := resolve eq344 rule_def_2_1 -- subsumption resolution 344,141
  have eq358 (X0 : G) : ¬(old X0 sk1 sk2) ∨ c = sk3 ∨ (old X0 sk3 sk1) ∨ c = sk1 := resolve eq320 old_1 -- resolution 320,125
  have eq361 (X0 : G) : ¬(old X0 sk1 sk2) ∨ b = sk1 ∨ (old X0 sk3 sk1) ∨ c = sk1 := resolve eq323 old_1 -- resolution 323,125
  have eq391 : (old sk2 sk1 sk3) ∨ a = b ∨ c = sk1 ∨ a = sk2 := resolve eq265 rule_def_0_0 -- resolution 265,132
  have eq421 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq295 rule_def_0_0 -- resolution 295,132
  have eq435 : (old sk2 sk1 sk3) ∨ b = sk3 ∨ c = sk2 ∨ a = sk2 := resolve eq310 rule_def_0_0 -- resolution 310,132
  have eq464 : (old sk2 sk1 sk3) ∨ a = b ∨ (old sk2 b a) ∨ b = sk1 := resolve eq263 rule_def_0_1 -- resolution 263,133
  have eq473 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk0 ∨ c = sk0 ∨ (old sk0 b a) := resolve eq345 rule_def_1_2 -- resolution 345,138
  have eq575 : c = sk3 ∨ (old sk0 sk3 sk1) ∨ c = sk1 ∨ c = sk1 ∨ c = sk2 := resolve eq358 eq290 -- resolution 358,290
  have eq579 : c = sk3 ∨ (old sk0 sk3 sk1) ∨ c = sk1 ∨ c = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq358 eq421 -- resolution 358,421
  have eq580 : (old sk0 sk3 sk1) ∨ c = sk3 ∨ c = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq579 rfl -- duplicate literal removal 579
  have eq583 : (old sk0 sk3 sk1) ∨ c = sk3 ∨ c = sk1 ∨ c = sk2 := resolve eq575 rfl -- duplicate literal removal 575
  have eq594 : b = sk1 ∨ (old sk0 sk3 sk1) ∨ c = sk1 ∨ c = sk1 ∨ b = sk1 := resolve eq361 eq293 -- resolution 361,293
  have eq600 : (old sk0 sk3 sk1) ∨ b = sk1 ∨ c = sk1 := resolve eq594 rfl -- duplicate literal removal 594
  have eq649 : b = sk1 ∨ c = sk1 ∨ (new sk0 sk3 sk1) := resolve eq600 imp_new_0 -- resolution 600,130
  have eq652 : b = sk1 ∨ c = sk1 := resolve eq649 preserve_2 -- subsumption resolution 649,179
  have eq670 : ¬(new sk0 sk3 b) ∨ c = sk1 := eq652.imp_left (fun h : b = sk1 ↦ superpose h preserve_2) -- superposition 179,652, 652 into 179, unify on (0).2 in 652 and (0).3 in 179
  have eq695 : (old sk0 b sk2) ∨ c = b ∨ c = sk2 ∨ c = sk1 := Or.assoc3 (eq652.imp_left (fun h : b = sk1 ↦ superpose h eq290)) -- superposition 290,652, 652 into 290, unify on (0).2 in 652 and (0).2 in 290
  have eq701 : (old sk2 b sk3) ∨ c = b ∨ c = sk3 ∨ c = sk1 := Or.assoc3 (eq652.imp_left (fun h : b = sk1 ↦ superpose h eq320)) -- superposition 320,652, 652 into 320, unify on (0).2 in 652 and (0).2 in 320
  have eq722 : (old sk0 b sk2) ∨ c = sk2 ∨ c = sk1 := resolve eq695 bc -- subsumption resolution 695,119
  have eq726 : (old sk2 b sk3) ∨ c = sk3 ∨ c = sk1 := resolve eq701 bc -- subsumption resolution 701,119
  have eq866 : c = sk3 ∨ c = sk1 ∨ c = sk2 ∨ (new sk0 sk3 sk1) := resolve eq583 imp_new_0 -- resolution 583,130
  have eq871 : c = sk3 ∨ c = sk1 ∨ c = sk2 := resolve eq866 preserve_2 -- subsumption resolution 866,179
  have eq891 : (old sk2 sk1 c) ∨ c = b ∨ c = sk2 ∨ a = sk2 ∨ c = sk1 ∨ c = sk2 := Or.assoc4 (eq871.imp_left (fun h : c = sk3 ↦ superpose h eq435)) -- superposition 435,871, 871 into 435, unify on (0).2 in 871 and (0).3 in 435
  have eq910 : (old sk2 sk1 c) ∨ c = b ∨ c = sk2 ∨ a = sk2 ∨ c = sk1 := resolve eq891 rfl -- duplicate literal removal 891
  have eq930 : c = b ∨ c = sk2 ∨ a = sk2 ∨ c = sk1 := resolve eq910 p4XY -- subsumption resolution 910,121
  have eq931 : c = sk2 ∨ a = sk2 ∨ c = sk1 := resolve eq930 bc -- subsumption resolution 930,119
  have eq963 : (sP0 sk0 sk1 c) ∨ (old sk0 sk1 c) ∨ c = b ∨ c = sk0 ∨ a = sk2 ∨ c = sk1 := Or.assoc4 (eq931.imp_left (fun h : c = sk2 ↦ superpose h eq280)) -- superposition 280,931, 931 into 280, unify on (0).2 in 931 and (0).3 in 280
  have eq981 : (old c sk1 sk3) ∨ a = b ∨ c = sk1 ∨ a = c ∨ a = sk2 ∨ c = sk1 := Or.assoc4 (eq931.imp_left (fun h : c = sk2 ↦ superpose h eq391)) -- superposition 391,931, 931 into 391, unify on (0).2 in 931 and (0).1 in 391
  have eq1002 : (old c sk1 sk3) ∨ a = b ∨ c = sk1 ∨ a = c ∨ a = sk2 := resolve eq981 rfl -- duplicate literal removal 981
  have eq1034 : (sP0 sk0 sk1 c) ∨ c = b ∨ c = sk0 ∨ a = sk2 ∨ c = sk1 := resolve eq963 p4XY -- subsumption resolution 963,121
  have eq1035 : (sP0 sk0 sk1 c) ∨ c = sk0 ∨ a = sk2 ∨ c = sk1 := resolve eq1034 bc -- subsumption resolution 1034,119
  have eq1040 : a = b ∨ c = sk1 ∨ a = c ∨ a = sk2 := resolve eq1002 p4YZ -- subsumption resolution 1002,123
  have eq1041 : a = sk2 ∨ c = sk1 ∨ a = b := resolve eq1040 ac -- subsumption resolution 1040,118
  have eq1284 : (old sk0 b a) ∨ a = c ∨ c = sk1 ∨ c = sk1 ∨ a = b := Or.assoc3 (eq1041.imp_left (fun h : a = sk2 ↦ superpose h eq722)) -- superposition 722,1041, 1041 into 722, unify on (0).2 in 1041 and (0).3 in 722
  have eq1285 : (old sk0 b a) ∨ a = c ∨ c = sk1 ∨ a = b := resolve eq1284 rfl -- duplicate literal removal 1284
  have eq1286 : (old sk0 b a) ∨ c = sk1 ∨ a = b := resolve eq1285 ac -- subsumption resolution 1285,118
  have eq1316 : (old a b sk3) ∨ c = sk3 ∨ c = sk1 ∨ c = sk1 ∨ a = b := Or.assoc3 (eq1041.imp_left (fun h : a = sk2 ↦ superpose h eq726)) -- superposition 726,1041, 1041 into 726, unify on (0).2 in 1041 and (0).1 in 726
  have eq1322 : (old a b sk3) ∨ c = sk3 ∨ c = sk1 ∨ a = b := resolve eq1316 rfl -- duplicate literal removal 1316
  have eq1323 : c = sk3 ∨ c = sk1 ∨ a = b := resolve eq1322 p3 -- subsumption resolution 1322,120
  have eq1379 : ¬(new sk0 c b) ∨ c = sk1 ∨ c = sk1 ∨ a = b := Or.assoc2 (eq1323.imp_left (fun h : c = sk3 ↦ superpose h eq670)) -- superposition 670,1323, 1323 into 670, unify on (0).2 in 1323 and (0).2 in 670
  have eq1381 : ¬(new sk0 c b) ∨ c = sk1 ∨ a = b := resolve eq1379 rfl -- duplicate literal removal 1379
  have eq1651 : c = sk3 ∨ c = sk1 ∨ c = sk0 ∨ a = sk0 ∨ (new sk0 sk3 sk1) := resolve eq580 imp_new_0 -- resolution 580,130
  have eq1656 : c = sk3 ∨ c = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq1651 preserve_2 -- subsumption resolution 1651,179
  have eq1783 : c = sk1 ∨ a = b ∨ (new sk0 c b) := resolve eq1286 eq184 -- resolution 1286,184
  have eq1787 : c = sk1 ∨ a = b := resolve eq1783 eq1381 -- subsumption resolution 1783,1381
  have eq1831 : (old sk0 c sk2) ∨ a = b ∨ b = sk2 ∨ c = b ∨ a = b := Or.assoc4 (eq1787.imp_left (fun h : c = sk1 ↦ superpose h eq261)) -- superposition 261,1787, 1787 into 261, unify on (0).2 in 1787 and (0).2 in 261
  have eq1862 : (old sk2 c sk3) ∨ a = b ∨ (old sk2 b a) ∨ c = b ∨ a = b := Or.assoc4 (eq1787.imp_left (fun h : c = sk1 ↦ superpose h eq464)) -- superposition 464,1787, 1787 into 464, unify on (0).2 in 1787 and (0).2 in 464
  have eq1881 : (old sk2 c sk3) ∨ a = b ∨ (old sk2 b a) ∨ c = b := resolve eq1862 rfl -- duplicate literal removal 1862
  have eq1894 : (old sk0 c sk2) ∨ a = b ∨ b = sk2 ∨ c = b := resolve eq1831 rfl -- duplicate literal removal 1831
  have eq1926 : a = b ∨ b = sk2 ∨ c = b := resolve eq1894 p4XZ -- subsumption resolution 1894,122
  have eq1927 : b = sk2 ∨ a = b := resolve eq1926 bc -- subsumption resolution 1926,119
  have eq1936 : a = b ∨ (old sk2 b a) ∨ c = b := resolve eq1881 p4XZ -- subsumption resolution 1881,122
  have eq1937 : (old sk2 b a) ∨ a = b := resolve eq1936 bc -- subsumption resolution 1936,119
  have eq2263 : (old b b a) ∨ a = b ∨ a = b := Or.assoc2 (eq1927.imp_left (fun h : b = sk2 ↦ superpose h eq1937)) -- superposition 1937,1927, 1927 into 1937, unify on (0).2 in 1927 and (0).1 in 1937
  have eq2267 : (old b b a) ∨ a = b := resolve eq2263 rfl -- duplicate literal removal 2263
  have eq2679 : a = b ∨ (old a b a) := resolve eq2267 old_2 -- resolution 2267,126
  have eq2683 : a = b := resolve eq2679 p3 -- subsumption resolution 2679,120
  have eq2685 : ∀ (X0 : G) , ¬(old a a X0) := Eq.mp (by simp only [eq2683, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) p3 -- backward demodulation 120,2683
  have eq2697 : (new a a c) := Eq.mp (by simp only [eq2683, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq182 -- backward demodulation 182,2683
  have eq2698 : ∀ (X0 : G) , ¬(old X0 a a) ∨ (new X0 c b) := Eq.mp (by simp only [eq2683, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq184 -- backward demodulation 184,2683
  have eq2699 : a ≠ a ∨ (new c b c) := Eq.mp (by simp only [eq2683, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq187 -- backward demodulation 187,2683
  have eq2700 : a ≠ a ∨ (new c c b) := Eq.mp (by simp only [eq2683, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq196 -- backward demodulation 196,2683
  have eq2701 : a ≠ a ∨ (new b c b) := Eq.mp (by simp only [eq2683, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq205 -- backward demodulation 205,2683
  have eq2718 : a = sk3 ∨ (old sk2 sk1 sk3) ∨ b = sk1 := Eq.mp (by simp only [eq2683, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq308 -- backward demodulation 308,2683
  have eq2734 : a = sk0 ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk0 ∨ (old sk0 b a) := Eq.mp (by simp only [eq2683, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq473 -- backward demodulation 473,2683
  have eq2767 : c = sk1 ∨ a = sk1 := Eq.mp (by simp only [eq2683, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq652 -- backward demodulation 652,2683
  have eq2874 : (new b c b) := resolve eq2701 rfl -- trivial inequality removal 2701
  have eq2875 : (new c c b) := resolve eq2700 rfl -- trivial inequality removal 2700
  have eq2876 : (new c b c) := resolve eq2699 rfl -- trivial inequality removal 2699
  have eq2877 : ∀ (X0 : G) , ¬(old X0 a a) ∨ (new X0 c a) := Eq.mp (by simp only [eq2683, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2698 -- forward demodulation 2698,2683
  have eq2878 : (new c a c) := Eq.mp (by simp only [eq2683, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2876 -- forward demodulation 2876,2683
  have eq2879 : (new c c a) := Eq.mp (by simp only [eq2683, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2875 -- forward demodulation 2875,2683
  have eq2880 : (new a c a) := Eq.mp (by simp only [eq2683, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2874 -- forward demodulation 2874,2683
  have eq2901 : (old sk2 sk1 sk3) ∨ a = sk3 ∨ a = sk1 := Eq.mp (by simp only [eq2683, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2718 -- forward demodulation 2718,2683
  have eq2912 : a = sk0 ∨ (old sk0 sk1 sk2) ∨ c = sk0 ∨ (old sk0 b a) := resolve eq2734 rule_def_0_0 -- subsumption resolution 2734,132
  have eq2913 : (old sk0 sk1 sk2) ∨ a = sk0 ∨ (old sk0 a a) ∨ c = sk0 := Eq.mp (by simp only [eq2683, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq2912 -- forward demodulation 2912,2683
  have eq3110 (X0 : G) : ¬(new c a X0) ∨ c = X0 := resolve eq2878 prev_0 -- resolution 2878,176
  have eq3122 : ¬(new sk0 sk3 c) ∨ a = sk1 := eq2767.imp_left (fun h : c = sk1 ↦ superpose h preserve_2) -- superposition 179,2767, 2767 into 179, unify on (0).2 in 2767 and (0).3 in 179
  have eq3474 : (old sk2 c sk3) ∨ a = sk3 ∨ a = c ∨ a = sk1 := Or.assoc3 (eq2767.imp_left (fun h : c = sk1 ↦ superpose h eq2901)) -- superposition 2901,2767, 2767 into 2901, unify on (0).2 in 2767 and (0).2 in 2901
  have eq3479 : a = sk3 ∨ a = c ∨ a = sk1 := resolve eq3474 p4XZ -- subsumption resolution 3474,122
  have eq3480 : a = sk3 ∨ a = sk1 := resolve eq3479 ac -- subsumption resolution 3479,118
  have eq3500 : ¬(new sk0 a c) ∨ a = sk1 ∨ a = sk1 := Or.assoc2 (eq3480.imp_left (fun h : a = sk3 ↦ superpose h eq3122)) -- superposition 3122,3480, 3480 into 3122, unify on (0).2 in 3480 and (0).2 in 3122
  have eq3503 : ¬(new sk0 a c) ∨ a = sk1 := resolve eq3500 rfl -- duplicate literal removal 3500
  have eq3930 : (old sk0 c sk2) ∨ a = sk0 ∨ (old sk0 a a) ∨ c = sk0 ∨ a = sk1 := Or.assoc4 (eq2767.imp_left (fun h : c = sk1 ↦ superpose h eq2913)) -- superposition 2913,2767, 2767 into 2913, unify on (0).2 in 2767 and (0).2 in 2913
  have eq3935 : (old sk0 a a) ∨ a = sk0 ∨ c = sk0 ∨ a = sk1 := resolve eq3930 p4XZ -- subsumption resolution 3930,122
  have eq4174 : ¬(new sk0 c sk1) ∨ c = sk1 ∨ c = sk0 ∨ a = sk0 := eq1656.imp_left (fun h : c = sk3 ↦ superpose h preserve_2) -- superposition 179,1656, 1656 into 179, unify on (0).2 in 1656 and (0).2 in 179
  have eq4785 : a = sk0 ∨ c = sk0 ∨ a = sk1 ∨ (old a a a) := resolve eq3935 old_5 -- resolution 3935,129
  have eq4789 : a = sk1 ∨ c = sk0 ∨ a = sk0 := resolve eq4785 eq2685 -- subsumption resolution 4785,2685
  have eq4810 : (sP4 sk0 a sk2) ∨ (sP3 sk0 a sk2) ∨ (sP2 sk0 a sk2) ∨ (sP0 sk0 a sk2) ∨ (old sk0 a sk2) ∨ a = c ∨ c = sk0 ∨ a = sk0 := Or.assoc6 (eq4789.imp_left (fun h : a = sk1 ↦ superpose h eq232)) -- superposition 232,4789, 4789 into 232, unify on (0).2 in 4789 and (0).2 in 232
  have eq4893 : (sP4 sk0 a sk2) ∨ (sP3 sk0 a sk2) ∨ (sP2 sk0 a sk2) ∨ (sP0 sk0 a sk2) ∨ (old sk0 a sk2) ∨ c = sk0 ∨ a = sk0 := resolve eq4810 ac -- subsumption resolution 4810,118
  have eq4894 : (sP4 sk0 a sk2) ∨ (sP3 sk0 a sk2) ∨ (sP2 sk0 a sk2) ∨ (old sk0 a sk2) ∨ c = sk0 ∨ a = sk0 := resolve eq4893 rule_def_0_0 -- subsumption resolution 4893,132
  have eq4895 : (sP3 sk0 a sk2) ∨ (sP2 sk0 a sk2) ∨ (old sk0 a sk2) ∨ c = sk0 ∨ a = sk0 := resolve eq4894 rule_def_4_1 -- subsumption resolution 4894,151
  have eq4896 : (sP2 sk0 a sk2) ∨ (old sk0 a sk2) ∨ c = sk0 ∨ a = sk0 := resolve eq4895 rule_def_3_1 -- subsumption resolution 4895,146
  have eq4897 : (old sk0 a sk2) ∨ c = sk0 ∨ a = sk0 := resolve eq4896 rule_def_2_1 -- subsumption resolution 4896,141
  have eq5079 : ¬(new sk0 c a) ∨ a = c ∨ c = sk0 ∨ a = sk0 ∨ c = sk0 ∨ a = sk0 := Or.assoc4 (eq4789.imp_left (fun h : a = sk1 ↦ superpose h eq4174)) -- superposition 4174,4789, 4789 into 4174, unify on (0).2 in 4789 and (0).3 in 4174
  have eq5080 : ¬(new sk0 c a) ∨ a = c ∨ c = sk0 ∨ a = sk0 := resolve eq5079 rfl -- duplicate literal removal 5079
  have eq5081 : ¬(new sk0 c a) ∨ c = sk0 ∨ a = sk0 := resolve eq5080 ac -- subsumption resolution 5080,118
  have eq5195 : (sP0 sk0 a c) ∨ c = sk0 ∨ a = sk2 ∨ a = c ∨ c = sk0 ∨ a = sk0 := Or.assoc4 (eq4789.imp_left (fun h : a = sk1 ↦ superpose h eq1035)) -- superposition 1035,4789, 4789 into 1035, unify on (0).2 in 4789 and (0).2 in 1035
  have eq5196 : (sP0 sk0 a c) ∨ c = sk0 ∨ a = sk2 ∨ a = c ∨ a = sk0 := resolve eq5195 rfl -- duplicate literal removal 5195
  have eq5197 : (sP0 sk0 a c) ∨ c = sk0 ∨ a = sk2 ∨ a = sk0 := resolve eq5196 ac -- subsumption resolution 5196,118
  have eq5198 : a = sk2 ∨ c = sk0 ∨ a = sk0 := resolve eq5197 rule_def_0_0 -- subsumption resolution 5197,132
  have eq5257 : (old sk0 a a) ∨ c = sk0 ∨ a = sk0 ∨ c = sk0 ∨ a = sk0 := Or.assoc3 (eq5198.imp_left (fun h : a = sk2 ↦ superpose h eq4897)) -- superposition 4897,5198, 5198 into 4897, unify on (0).2 in 5198 and (0).3 in 4897
  have eq5260 : (old sk0 a a) ∨ c = sk0 ∨ a = sk0 := resolve eq5257 rfl -- duplicate literal removal 5257
  have eq5363 : c = sk0 ∨ a = sk0 ∨ (new sk0 c a) := resolve eq5260 eq2877 -- resolution 5260,2877
  have eq5368 : c = sk0 ∨ a = sk0 := resolve eq5363 eq5081 -- subsumption resolution 5363,5081
  have eq5388 : (new c sk1 sk2) ∨ a = sk0 := eq5368.imp_left (fun h : c = sk0 ↦ superpose h preserve_0) -- superposition 177,5368, 5368 into 177, unify on (0).2 in 5368 and (0).1 in 177
  have eq5389 : ¬(new c sk3 sk1) ∨ a = sk0 := eq5368.imp_left (fun h : c = sk0 ↦ superpose h preserve_2) -- superposition 179,5368, 5368 into 179, unify on (0).2 in 5368 and (0).1 in 179
  have eq5452 : ¬(new c a c) ∨ a = sk1 ∨ a = sk0 := Or.assoc2 (eq5368.imp_left (fun h : c = sk0 ↦ superpose h eq3503)) -- superposition 3503,5368, 5368 into 3503, unify on (0).2 in 5368 and (0).1 in 3503
  have eq5469 : a = sk1 ∨ a = sk0 := resolve eq5452 eq2878 -- subsumption resolution 5452,2878
  have eq5501 : (new sk2 a sk3) ∨ a = sk0 := eq5469.imp_left (fun h : a = sk1 ↦ superpose h preserve_1) -- superposition 178,5469, 5469 into 178, unify on (0).2 in 5469 and (0).2 in 178
  have eq5649 : (new c a sk2) ∨ a = sk0 ∨ a = sk0 := Or.assoc2 (eq5469.imp_left (fun h : a = sk1 ↦ superpose h eq5388)) -- superposition 5388,5469, 5469 into 5388, unify on (0).2 in 5469 and (0).2 in 5388
  have eq5660 : (new c a sk2) ∨ a = sk0 := resolve eq5649 rfl -- duplicate literal removal 5649
  have eq5671 : ¬(new c sk3 a) ∨ a = sk0 ∨ a = sk0 := Or.assoc2 (eq5469.imp_left (fun h : a = sk1 ↦ superpose h eq5389)) -- superposition 5389,5469, 5469 into 5389, unify on (0).2 in 5469 and (0).3 in 5389
  have eq5675 : ¬(new c sk3 a) ∨ a = sk0 := resolve eq5671 rfl -- duplicate literal removal 5671
  have eq5772 : c = sk2 ∨ a = sk0 := resolve eq5660 eq3110 -- resolution 5660,3110
  have eq5861 : (new c a sk3) ∨ a = sk0 ∨ a = sk0 := Or.assoc2 (eq5772.imp_left (fun h : c = sk2 ↦ superpose h eq5501)) -- superposition 5501,5772, 5772 into 5501, unify on (0).2 in 5772 and (0).1 in 5501
  have eq5864 : (new c a sk3) ∨ a = sk0 := resolve eq5861 rfl -- duplicate literal removal 5861
  have eq5989 : c = sk3 ∨ a = sk0 := resolve eq5864 eq3110 -- resolution 5864,3110
  have eq6068 : ¬(new c c a) ∨ a = sk0 ∨ a = sk0 := Or.assoc2 (eq5989.imp_left (fun h : c = sk3 ↦ superpose h eq5675)) -- superposition 5675,5989, 5989 into 5675, unify on (0).2 in 5989 and (0).2 in 5675
  have eq6073 : ¬(new c c a) ∨ a = sk0 := resolve eq6068 rfl -- duplicate literal removal 6068
  have eq6089 : a = sk0 := resolve eq6073 eq2879 -- subsumption resolution 6073,2879
  have eq6091 : ¬(new a sk3 sk1) := Eq.mp (by simp only [eq6089, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_2 -- backward demodulation 179,6089
  have eq6095 : (old a sk1 sk2) ∨ c = sk1 ∨ c = sk2 := Eq.mp (by simp only [eq6089, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq290 -- backward demodulation 290,6089
  have eq6175 : ¬(new a a c) ∨ a = sk1 := Eq.mp (by simp only [eq6089, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq3503 -- backward demodulation 3503,6089
  have eq6248 : a = sk1 := resolve eq6175 eq2697 -- subsumption resolution 6175,2697
  have eq6253 : (old sk2 a sk3) ∨ c = sk1 ∨ c = sk3 := Eq.mp (by simp only [eq6248, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq320 -- backward demodulation 320,6248
  have eq6345 : ¬(new a sk3 a) := Eq.mp (by simp only [eq6248, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6091 -- backward demodulation 6091,6248
  have eq6347 : a = c ∨ (old a sk1 sk2) ∨ c = sk2 := Eq.mp (by simp only [eq6248, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6095 -- backward demodulation 6095,6248
  have eq6388 : a = c ∨ (old sk2 a sk3) ∨ c = sk3 := Eq.mp (by simp only [eq6248, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6253 -- forward demodulation 6253,6248
  have eq6389 : (old sk2 a sk3) ∨ c = sk3 := resolve eq6388 ac -- subsumption resolution 6388,118
  have eq6465 : (old a sk1 sk2) ∨ c = sk2 := resolve eq6347 ac -- subsumption resolution 6347,118
  have eq6466 : (old a a sk2) ∨ c = sk2 := Eq.mp (by simp only [eq6248, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6465 -- forward demodulation 6465,6248
  have eq6467 : c = sk2 := resolve eq6466 eq2685 -- subsumption resolution 6466,2685
  have eq6474 : (old c a sk3) ∨ c = sk3 := Eq.mp (by simp only [eq6467, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6389 -- backward demodulation 6389,6467
  have eq6504 : c = sk3 := resolve eq6474 p4YZ -- subsumption resolution 6474,123
  have eq6505 : ¬(new a c a) := Eq.mp (by simp only [eq6504, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq6345 -- backward demodulation 6345,6504
  subsumption eq2880 eq6505 -- subsumption resolution 6505,2880

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (ac : a ≠ c) (bc : c ≠ b) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4YZ : ∀ X1 X2, ¬ old c X1 X2) (old_2 : (∀ X0 X1, ¬ old X0 X0 X1 ∨ old X1 X0 X1)) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X b a ∨ ¬sP1 X Y Z) (imp_new_3 : ∀ X Y Z, a ≠ b ∨ c ≠ X ∨ b ≠ Y ∨ c ≠ Z ∨ new X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP2 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = X ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP3 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = X ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP4 X Y Z) (rule_def_5_0 : ∀ (X Y Z : G), a = b ∨ ¬sP5 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP5 X Y Z) (rule_def_6_0 : ∀ (X Y Z : G), a = b ∨ ¬sP6 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP6 X Y Z) (rule_def_6_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP6 X Y Z) (rule_def_7_0 : ∀ (X Y Z : G), a = b ∨ ¬sP7 X Y Z) (rule_def_7_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP7 X Y Z) (rule_def_7_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP7 X Y Z) (imp_new_9 : ∀ X Y Z, a ≠ b ∨ b ≠ X ∨ c ≠ Y ∨ b ≠ Z ∨ new X Y Z) (rule_def_8_1 : ∀ (X Y Z : G), b = X ∨ ¬sP8 X Y Z) (rule_def_8_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP8 X Y Z) (rule_def_8_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP8 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1, ¬ new X0 X0 X1 ∨ new X1 X0 X1) := by
  by_contra! nh
  obtain ⟨sk0, sk1, preserve_0, preserve_1⟩ := nh
  have eq186 (X0 X1 : G) : (new X0 X1 c) ∨ b ≠ X1 ∨ c ≠ X0 ∨ a ≠ b := resolve imp_new_3 rfl -- equality resolution 140
  have eq187 (X0 : G) : (new X0 b c) ∨ c ≠ X0 ∨ a ≠ b := resolve eq186 rfl -- equality resolution 186
  have eq188 : a ≠ b ∨ (new c b c) := resolve eq187 rfl -- equality resolution 187
  have eq204 (X0 X1 : G) : (new X0 X1 b) ∨ c ≠ X1 ∨ b ≠ X0 ∨ a ≠ b := resolve imp_new_9 rfl -- equality resolution 170
  have eq205 (X0 : G) : (new X0 c b) ∨ b ≠ X0 ∨ a ≠ b := resolve eq204 rfl -- equality resolution 204
  have eq206 : a ≠ b ∨ (new b c b) := resolve eq205 rfl -- equality resolution 205
  have eq213 : (sP8 sk0 sk0 sk1) ∨ (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) := resolve new_imp preserve_0 -- resolution 176,179
  have eq226 : (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ b = sk1 := resolve eq213 rule_def_8_3 -- resolution 213,174
  have eq227 : (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ c = sk0 := resolve eq213 rule_def_8_2 -- resolution 213,173
  have eq228 : (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ b = sk0 := resolve eq213 rule_def_8_1 -- resolution 213,172
  have eq230 : (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk1 := resolve eq226 rule_def_7_3 -- subsumption resolution 226,169
  have eq231 : (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk1 := resolve eq230 rule_def_6_3 -- subsumption resolution 230,164
  have eq232 : (sP4 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk1 := resolve eq231 rule_def_5_3 -- subsumption resolution 231,159
  have eq233 : (sP4 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk1 := resolve eq232 rule_def_1_1 -- subsumption resolution 232,138
  have eq234 : (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk0 := resolve eq227 rule_def_7_2 -- subsumption resolution 227,168
  have eq235 : (sP5 sk0 sk0 sk1) ∨ (sP4 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk0 := resolve eq234 rule_def_6_2 -- subsumption resolution 234,163
  have eq236 : (sP4 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk0 := resolve eq235 rule_def_5_2 -- subsumption resolution 235,158
  have eq237 : (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk0 := resolve eq236 rule_def_4_1 -- subsumption resolution 236,152
  have eq238 : (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk0 := resolve eq237 rule_def_3_1 -- subsumption resolution 237,147
  have eq239 : (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk0 := resolve eq238 rule_def_2_1 -- subsumption resolution 238,142
  have eq240 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ c = sk0 := resolve eq239 rule_def_1_0 -- subsumption resolution 239,137
  have eq241 : (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ b = sk0 := resolve eq228 rule_def_4_2 -- subsumption resolution 228,153
  have eq242 : (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ b = sk0 := resolve eq241 rule_def_3_2 -- subsumption resolution 241,148
  have eq243 : (sP6 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP7 sk0 sk0 sk1) ∨ b = sk0 := resolve eq242 rule_def_2_2 -- subsumption resolution 242,143
  have eq244 : (sP7 sk0 sk0 sk1) ∨ (sP5 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP6 sk0 sk0 sk1) ∨ b = sk0 := resolve eq243 rule_def_0_1 -- subsumption resolution 243,134
  have eq251 : (old sk0 sk0 sk1) ∨ c = sk0 ∨ c = sk1 := resolve eq240 rule_def_0_2 -- resolution 240,135
  have eq253 : (old sk0 sk0 sk1) ∨ c = sk0 ∨ a = sk0 := resolve eq240 rule_def_0_0 -- resolution 240,133
  have eq259 : (old sk1 sk0 sk1) ∨ c = sk1 ∨ c = sk0 := resolve eq251 old_2 -- resolution 251,127
  have eq264 : (sP3 sk0 sk0 sk1) ∨ (sP2 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk1 ∨ b = sk0 := resolve eq233 rule_def_4_2 -- resolution 233,153
  have eq270 : (sP2 sk0 sk0 sk1) ∨ (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk1 ∨ b = sk0 := resolve eq264 rule_def_3_2 -- subsumption resolution 264,148
  have eq271 : (sP0 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk1 ∨ b = sk0 := resolve eq270 rule_def_2_2 -- subsumption resolution 270,143
  have eq272 : (old sk0 sk0 sk1) ∨ b = sk1 ∨ b = sk0 := resolve eq271 rule_def_0_1 -- subsumption resolution 271,134
  have eq282 : (sP5 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ (sP6 sk0 sk0 sk1) ∨ b = sk0 ∨ a = b := resolve eq244 rule_def_7_0 -- resolution 244,166
  have eq283 : (sP5 sk0 sk0 sk1) ∨ (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 ∨ a = b := resolve eq282 rule_def_6_0 -- subsumption resolution 282,161
  have eq284 : (sP1 sk0 sk0 sk1) ∨ (old sk0 sk0 sk1) ∨ b = sk0 ∨ a = b := resolve eq283 rule_def_5_0 -- subsumption resolution 283,156
  have eq309 : (old sk0 sk0 sk1) ∨ b = sk0 ∨ a = b ∨ (old sk0 b a) := resolve eq284 rule_def_1_2 -- resolution 284,139
  have eq323 : c = sk1 ∨ c = sk0 ∨ (new sk1 sk0 sk1) := resolve eq259 imp_new_0 -- resolution 259,131
  have eq324 : c = sk1 ∨ c = sk0 := resolve eq323 preserve_1 -- subsumption resolution 323,180
  have eq331 : ¬(new c sk0 c) ∨ c = sk0 := eq324.imp_left (fun h : c = sk1 ↦ superpose h preserve_1) -- superposition 180,324, 324 into 180, unify on (0).2 in 324 and (0).1 in 180
  have eq335 : (sP7 sk0 sk0 c) ∨ (sP5 sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ (old sk0 sk0 c) ∨ (sP6 sk0 sk0 c) ∨ b = sk0 ∨ c = sk0 := Or.assoc6 (eq324.imp_left (fun h : c = sk1 ↦ superpose h eq244)) -- superposition 244,324, 324 into 244, unify on (0).2 in 324 and (0).3 in 244
  have eq338 : (old sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 ∨ c = sk0 := Or.assoc3 (eq324.imp_left (fun h : c = sk1 ↦ superpose h eq253)) -- superposition 253,324, 324 into 253, unify on (0).2 in 324 and (0).3 in 253
  have eq343 : (old sk0 sk0 c) ∨ c = sk0 ∨ a = sk0 := resolve eq338 rfl -- duplicate literal removal 338
  have eq355 : (sP7 sk0 sk0 c) ∨ (sP5 sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ (sP6 sk0 sk0 c) ∨ b = sk0 ∨ c = sk0 := resolve eq335 p4XY -- subsumption resolution 335,122
  have eq356 : (sP5 sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ (sP6 sk0 sk0 c) ∨ b = sk0 ∨ c = sk0 := resolve eq355 rule_def_7_2 -- subsumption resolution 355,168
  have eq357 : (sP5 sk0 sk0 c) ∨ (sP1 sk0 sk0 c) ∨ b = sk0 ∨ c = sk0 := resolve eq356 rule_def_6_2 -- subsumption resolution 356,163
  have eq358 : (sP1 sk0 sk0 c) ∨ b = sk0 ∨ c = sk0 := resolve eq357 rule_def_5_2 -- subsumption resolution 357,158
  have eq359 : b = sk0 ∨ c = sk0 := resolve eq358 rule_def_1_0 -- subsumption resolution 358,137
  have eq360 : c = sk0 ∨ a = sk0 := resolve eq343 p4XY -- subsumption resolution 343,122
  have eq393 : c = b ∨ a = b ∨ c = sk0 := Or.assoc2 (eq359.imp_left (fun h : b = sk0 ↦ superpose h eq360)) -- superposition 360,359, 359 into 360, unify on (0).2 in 359 and (0).2 in 360
  have eq405 : (old c c sk1) ∨ b = sk1 ∨ c = b ∨ a = sk0 := Or.assoc3 (eq360.imp_left (fun h : c = sk0 ↦ superpose h eq272)) -- superposition 272,360, 360 into 272, unify on (0).2 in 360 and (0).1 in 272
  have eq408 : c = sk0 ∨ a = b := resolve eq393 bc -- subsumption resolution 393,120
  have eq417 : b = sk1 ∨ c = b ∨ a = sk0 := resolve eq405 p4YZ -- subsumption resolution 405,124
  have eq418 : b = sk1 ∨ a = sk0 := resolve eq417 bc -- subsumption resolution 417,120
  have eq563 : ¬(new c b c) ∨ c = b ∨ c = sk0 := Or.assoc2 (eq359.imp_left (fun h : b = sk0 ↦ superpose h eq331)) -- superposition 331,359, 359 into 331, unify on (0).2 in 359 and (0).2 in 331
  have eq564 : ¬(new c b c) ∨ c = sk0 := resolve eq563 bc -- subsumption resolution 563,120
  have eq813 : (old c c sk1) ∨ c = b ∨ a = b ∨ (old c b a) ∨ a = b := Or.assoc4 (eq408.imp_left (fun h : c = sk0 ↦ superpose h eq309)) -- superposition 309,408, 408 into 309, unify on (0).2 in 408 and (0).1 in 309
  have eq822 : (old c c sk1) ∨ c = b ∨ a = b ∨ (old c b a) := resolve eq813 rfl -- duplicate literal removal 813
  have eq825 : c = b ∨ a = b ∨ (old c b a) := resolve eq822 p4YZ -- subsumption resolution 822,124
  have eq826 : a = b ∨ (old c b a) := resolve eq825 bc -- subsumption resolution 825,120
  have eq827 : a = b := resolve eq826 p4YZ -- subsumption resolution 826,124
  have eq843 : a ≠ a ∨ (new c b c) := Eq.mp (by simp only [eq827, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq188 -- backward demodulation 188,827
  have eq845 : a ≠ a ∨ (new b c b) := Eq.mp (by simp only [eq827, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq206 -- backward demodulation 206,827
  have eq882 : a = sk1 ∨ a = sk0 := Eq.mp (by simp only [eq827, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq418 -- backward demodulation 418,827
  have eq891 : ¬(new c a c) ∨ c = sk0 := Eq.mp (by simp only [eq827, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq564 -- backward demodulation 564,827
  have eq929 : (new b c b) := resolve eq845 rfl -- trivial inequality removal 845
  have eq931 : (new c b c) := resolve eq843 rfl -- trivial inequality removal 843
  have eq933 : (new c a c) := Eq.mp (by simp only [eq827, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq931 -- forward demodulation 931,827
  have eq935 : (new a c a) := Eq.mp (by simp only [eq827, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq929 -- forward demodulation 929,827
  have eq1002 : c = sk0 := resolve eq891 eq933 -- subsumption resolution 891,933
  have eq1004 : ¬(new sk1 c sk1) := Eq.mp (by simp only [eq1002, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_1 -- backward demodulation 180,1002
  have eq1029 : a = c ∨ a = sk1 := Eq.mp (by simp only [eq1002, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq882 -- backward demodulation 882,1002
  have eq1067 : a = sk1 := resolve eq1029 ac -- subsumption resolution 1029,119
  have eq1069 : ¬(new a c a) := Eq.mp (by simp only [eq1067, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq1004 -- backward demodulation 1004,1067
  subsumption eq935 eq1069 -- subsumption resolution 1069,935

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_3_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (prev_1 : (∀ X0 X1 X2 X3, ¬ new X0 X1 X2 ∨ ¬ new X2 X1 X3 ∨ new X0 X3 X1)) (prev_2 : (∀ X0 X1, ¬ new X0 X0 X1 ∨ new X1 X0 X1)) : (∀ X0 X1, ¬ new X0 X0 X1 ∨ new X1 X1 X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, preserve_0, preserve_1⟩ := nh
  have eq210 : (new sk1 sk0 sk1) := resolve prev_2 preserve_0 -- resolution 181,182
  have eq218 (X0 : G) : ¬(new X0 sk0 sk1) ∨ (new X0 sk1 sk0) := resolve prev_1 eq210 -- resolution 180,210
  have eq225 : (new sk1 sk1 sk0) := resolve eq218 eq210 -- resolution 218,210
  subsumption preserve_1 eq225 -- subsumption resolution 225,183

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_4_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (prev_2 : (∀ X0 X1, ¬ new X0 X0 X1 ∨ new X1 X0 X1)) (prev_3 : (∀ X0 X1, ¬ new X0 X0 X1 ∨ new X1 X1 X0)) : (∀ X0 X1, ¬ new X0 X0 X1 ∨ new X0 X1 X0) := by
  by_contra! nh
  obtain ⟨sk0, sk1, preserve_0, preserve_1⟩ := nh
  have eq214 : (new sk1 sk1 sk0) := resolve prev_3 preserve_0 -- resolution 184,185
  have eq216 : (new sk0 sk1 sk0) := resolve eq214 prev_2 -- resolution 214,183
  subsumption preserve_1 eq216 -- subsumption resolution 216,186

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_5_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (bc : c ≠ b) (old_5 : (∀ X0 X1, ¬ old X0 X1 X1 ∨ old X1 X1 X1)) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP2 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP3 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP4 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP5 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP6 X Y Z) (rule_def_6_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP6 X Y Z) (rule_def_7_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP7 X Y Z) (rule_def_7_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP7 X Y Z) (rule_def_8_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP8 X Y Z) (rule_def_8_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP8 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z) (imp_new_0 : ∀ (X Y Z), ¬ old X Y Z ∨ new X Y Z) : (∀ X0 X1, ¬ new X0 X1 X1 ∨ new X1 X1 X1) := by
  by_contra! nh
  obtain ⟨sk0, sk1, preserve_0, preserve_1⟩ := nh
  have eq222 : (sP8 sk0 sk1 sk1) ∨ (sP6 sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) := resolve new_imp preserve_0 -- resolution 182,188
  have eq230 : (sP6 sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ b = sk1 := resolve eq222 rule_def_8_3 -- resolution 222,180
  have eq231 : (sP6 sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ (sP7 sk0 sk1 sk1) ∨ c = sk1 := resolve eq222 rule_def_8_2 -- resolution 222,179
  have eq234 : (sP6 sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ b = sk1 := resolve eq230 rule_def_7_3 -- subsumption resolution 230,175
  have eq235 : (sP5 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ b = sk1 := resolve eq234 rule_def_6_3 -- subsumption resolution 234,170
  have eq236 : (sP4 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ b = sk1 := resolve eq235 rule_def_5_3 -- subsumption resolution 235,165
  have eq237 : (sP3 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ b = sk1 := resolve eq236 rule_def_4_2 -- subsumption resolution 236,159
  have eq238 : (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ b = sk1 := resolve eq237 rule_def_3_2 -- subsumption resolution 237,154
  have eq239 : (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ b = sk1 := resolve eq238 rule_def_2_2 -- subsumption resolution 238,149
  have eq240 : (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ b = sk1 := resolve eq239 rule_def_1_1 -- subsumption resolution 239,144
  have eq241 : (old sk0 sk1 sk1) ∨ b = sk1 := resolve eq240 rule_def_0_1 -- subsumption resolution 240,140
  have eq242 : (sP6 sk0 sk1 sk1) ∨ (sP5 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ c = sk1 := resolve eq231 rule_def_7_2 -- subsumption resolution 231,174
  have eq243 : (sP5 sk0 sk1 sk1) ∨ (sP4 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ c = sk1 := resolve eq242 rule_def_6_2 -- subsumption resolution 242,169
  have eq244 : (sP4 sk0 sk1 sk1) ∨ (sP3 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ c = sk1 := resolve eq243 rule_def_5_2 -- subsumption resolution 243,164
  have eq245 : (sP3 sk0 sk1 sk1) ∨ (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ c = sk1 := resolve eq244 rule_def_4_3 -- subsumption resolution 244,160
  have eq246 : (sP2 sk0 sk1 sk1) ∨ (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ c = sk1 := resolve eq245 rule_def_3_3 -- subsumption resolution 245,155
  have eq247 : (sP1 sk0 sk1 sk1) ∨ (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ c = sk1 := resolve eq246 rule_def_2_3 -- subsumption resolution 246,150
  have eq248 : (sP0 sk0 sk1 sk1) ∨ (old sk0 sk1 sk1) ∨ c = sk1 := resolve eq247 rule_def_1_0 -- subsumption resolution 247,143
  have eq249 : (old sk0 sk1 sk1) ∨ c = sk1 := resolve eq248 rule_def_0_2 -- subsumption resolution 248,141
  have eq256 : (old sk1 sk1 sk1) ∨ b = sk1 := resolve eq241 old_5 -- resolution 241,136
  have eq260 : c = sk1 ∨ (old sk1 sk1 sk1) := resolve eq249 old_5 -- resolution 249,136
  have eq270 : b = sk1 ∨ (new sk1 sk1 sk1) := resolve eq256 imp_new_0 -- resolution 256,137
  have eq271 : b = sk1 := resolve eq270 preserve_1 -- subsumption resolution 270,189
  have eq273 : ¬(new b b b) := Eq.mp (by simp only [eq271, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) preserve_1 -- backward demodulation 189,271
  have eq282 : c = b ∨ (old sk1 sk1 sk1) := Eq.mp (by simp only [eq271, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq260 -- backward demodulation 260,271
  have eq309 : (old sk1 sk1 sk1) := resolve eq282 bc -- subsumption resolution 282,126
  have eq310 : (old b b b) := Eq.mp (by simp only [eq271, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq309 -- forward demodulation 309,271
  have eq331 : (new b b b) := resolve eq310 imp_new_0 -- resolution 310,137
  subsumption eq273 eq331 -- subsumption resolution 331,273

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_0_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (memold : G → Prop) (bc : c ≠ b) (p4XY : ∀ X1 X2, ¬ old X1 X2 c) (p4XZ : ∀ X1 X2, ¬ old X1 c X2) (rule_def_0_0 : ∀ (X Y Z : G), a = X ∨ ¬sP0 X Y Z) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_1_2 : ∀ (X Y Z : G), old X b a ∨ ¬sP1 X Y Z) (rule_def_2_1 : ∀ (X Y Z : G), c = X ∨ ¬sP2 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP2 X Y Z) (rule_def_3_1 : ∀ (X Y Z : G), c = X ∨ ¬sP3 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP3 X Y Z) (rule_def_4_1 : ∀ (X Y Z : G), c = X ∨ ¬sP4 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP4 X Y Z) (rule_def_5_1 : ∀ (X Y Z : G), c = X ∨ ¬sP5 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP5 X Y Z) (rule_def_6_1 : ∀ (X Y Z : G), c = X ∨ ¬sP6 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP6 X Y Z) (rule_def_6_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP6 X Y Z) (rule_def_7_1 : ∀ (X Y Z : G), c = X ∨ ¬sP7 X Y Z) (rule_def_7_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP7 X Y Z) (rule_def_7_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP7 X Y Z) (rule_def_8_1 : ∀ (X Y Z : G), b = X ∨ ¬sP8 X Y Z) (rule_def_8_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP8 X Y Z) (rule_def_8_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP8 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z) (old_mem1 : ∀ (X Y Z), ¬old X Y Z ∨ memold X) : ∀ (X Y Z : G), ¬new X Y Z ∨ X = a ∨ X = b ∨ memold X ∨ X = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq216 : (sP8 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 181,185
  have eq229 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ b = sk2 := resolve eq216 rule_def_8_3 -- resolution 216,179
  have eq230 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ c = sk1 := resolve eq216 rule_def_8_2 -- resolution 216,178
  have eq231 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ b = sk0 := resolve eq216 rule_def_8_1 -- resolution 216,177
  have eq233 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq229 rule_def_7_3 -- subsumption resolution 229,174
  have eq234 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq233 rule_def_6_3 -- subsumption resolution 233,169
  have eq235 : (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq234 rule_def_5_3 -- subsumption resolution 234,164
  have eq236 : (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq235 rule_def_1_1 -- subsumption resolution 235,143
  have eq237 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq230 rule_def_7_2 -- subsumption resolution 230,173
  have eq238 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq237 rule_def_6_2 -- subsumption resolution 237,168
  have eq239 : (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq238 rule_def_5_2 -- subsumption resolution 238,163
  have eq240 : (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 := resolve eq239 rule_def_1_0 -- subsumption resolution 239,142
  have eq241 : (sP7 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) := resolve eq231 preserve_2 -- subsumption resolution 231,187
  have eq243 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 ∨ b = sk1 := resolve eq236 rule_def_4_2 -- resolution 236,158
  have eq244 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 ∨ c = sk0 := resolve eq236 rule_def_4_1 -- resolution 236,157
  have eq249 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 ∨ b = sk1 := resolve eq243 rule_def_3_2 -- subsumption resolution 243,153
  have eq250 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 ∨ b = sk1 := resolve eq249 rule_def_2_2 -- subsumption resolution 249,148
  have eq251 : (old sk0 sk1 sk2) ∨ b = sk2 ∨ b = sk1 := resolve eq250 rule_def_0_1 -- subsumption resolution 250,139
  have eq252 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq244 preserve_4 -- subsumption resolution 244,189
  have eq253 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq240 rule_def_4_3 -- resolution 240,159
  have eq257 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq253 rule_def_3_3 -- subsumption resolution 253,154
  have eq258 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq257 rule_def_2_3 -- subsumption resolution 257,149
  have eq259 : (old sk0 sk1 sk2) ∨ c = sk1 ∨ c = sk2 := resolve eq258 rule_def_0_2 -- subsumption resolution 258,140
  have eq273 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ c = sk0 := resolve eq241 rule_def_7_1 -- resolution 241,172
  have eq275 : (sP6 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) := resolve eq273 preserve_4 -- subsumption resolution 273,189
  have eq286 : b = sk2 ∨ b = sk1 ∨ memold sk0 := resolve eq251 old_mem1 -- resolution 251,182
  have eq287 : b = sk2 ∨ b = sk1 := resolve eq286 preserve_3 -- subsumption resolution 286,188
  have eq309 : c = sk1 ∨ c = sk2 ∨ memold sk0 := resolve eq259 old_mem1 -- resolution 259,182
  have eq312 : c = sk2 ∨ c = sk1 := resolve eq309 preserve_3 -- subsumption resolution 309,188
  have eq352 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 ∨ c = sk0 := resolve eq252 rule_def_3_1 -- resolution 252,152
  have eq356 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq352 preserve_4 -- subsumption resolution 352,189
  have eq387 : (sP6 sk0 sk1 b) ∨ (sP4 sk0 sk1 b) ∨ (sP3 sk0 sk1 b) ∨ (sP2 sk0 sk1 b) ∨ (sP1 sk0 sk1 b) ∨ (sP0 sk0 sk1 b) ∨ (old sk0 sk1 b) ∨ (sP5 sk0 sk1 b) ∨ b = sk1 := Or.assoc8 (eq287.imp_left (fun h : b = sk2 ↦ superpose h eq275)) -- superposition 275,287, 287 into 275, unify on (0).2 in 287 and (0).3 in 275
  have eq390 : (sP6 sk0 sk1 b) ∨ (sP3 sk0 sk1 b) ∨ (sP2 sk0 sk1 b) ∨ (sP1 sk0 sk1 b) ∨ (sP0 sk0 sk1 b) ∨ (old sk0 sk1 b) ∨ (sP5 sk0 sk1 b) ∨ b = sk1 := resolve eq387 rule_def_4_2 -- subsumption resolution 387,158
  have eq391 : (sP6 sk0 sk1 b) ∨ (sP2 sk0 sk1 b) ∨ (sP1 sk0 sk1 b) ∨ (sP0 sk0 sk1 b) ∨ (old sk0 sk1 b) ∨ (sP5 sk0 sk1 b) ∨ b = sk1 := resolve eq390 rule_def_3_2 -- subsumption resolution 390,153
  have eq392 : (sP6 sk0 sk1 b) ∨ (sP1 sk0 sk1 b) ∨ (sP0 sk0 sk1 b) ∨ (old sk0 sk1 b) ∨ (sP5 sk0 sk1 b) ∨ b = sk1 := resolve eq391 rule_def_2_2 -- subsumption resolution 391,148
  have eq393 : (sP6 sk0 sk1 b) ∨ (sP1 sk0 sk1 b) ∨ (old sk0 sk1 b) ∨ (sP5 sk0 sk1 b) ∨ b = sk1 := resolve eq392 rule_def_0_1 -- subsumption resolution 392,139
  have eq445 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 ∨ c = sk0 := resolve eq356 rule_def_2_1 -- resolution 356,147
  have eq449 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq445 preserve_4 -- subsumption resolution 445,189
  have eq454 : (old sk0 sk1 sk2) ∨ b = sk2 ∨ a = sk0 := resolve eq449 rule_def_0_0 -- resolution 449,138
  have eq457 : (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq454 preserve_1 -- subsumption resolution 454,186
  have eq481 : (old sk0 sk1 c) ∨ c = b ∨ c = sk1 := Or.assoc2 (eq312.imp_left (fun h : c = sk2 ↦ superpose h eq457)) -- superposition 457,312, 312 into 457, unify on (0).2 in 312 and (0).3 in 457
  have eq582 : c = b ∨ c = sk1 := resolve eq481 p4XY -- subsumption resolution 481,127
  have eq583 : c = sk1 := resolve eq582 bc -- subsumption resolution 582,125
  have eq588 : c = b ∨ (sP6 sk0 sk1 b) ∨ (sP1 sk0 sk1 b) ∨ (old sk0 sk1 b) ∨ (sP5 sk0 sk1 b) := Eq.mp (by simp only [eq583, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq393 -- backward demodulation 393,583
  have eq611 : (sP6 sk0 sk1 b) ∨ (sP1 sk0 sk1 b) ∨ (old sk0 sk1 b) ∨ (sP5 sk0 sk1 b) := resolve eq588 bc -- subsumption resolution 588,125
  have eq612 : (sP6 sk0 c b) ∨ (sP1 sk0 sk1 b) ∨ (old sk0 sk1 b) ∨ (sP5 sk0 sk1 b) := Eq.mp (by simp only [eq583, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq611 -- forward demodulation 611,583
  have eq613 : (sP1 sk0 c b) ∨ (sP6 sk0 c b) ∨ (old sk0 sk1 b) ∨ (sP5 sk0 sk1 b) := Eq.mp (by simp only [eq583, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq612 -- forward demodulation 612,583
  have eq614 : (old sk0 c b) ∨ (sP1 sk0 c b) ∨ (sP6 sk0 c b) ∨ (sP5 sk0 sk1 b) := Eq.mp (by simp only [eq583, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq613 -- forward demodulation 613,583
  have eq615 : (sP1 sk0 c b) ∨ (sP6 sk0 c b) ∨ (sP5 sk0 sk1 b) := resolve eq614 p4XZ -- subsumption resolution 614,128
  have eq616 : (sP6 sk0 c b) ∨ (sP1 sk0 c b) ∨ (sP5 sk0 c b) := Eq.mp (by simp only [eq583, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq615 -- forward demodulation 615,583
  have eq659 : (sP1 sk0 c b) ∨ (sP5 sk0 c b) ∨ c = sk0 := resolve eq616 rule_def_6_1 -- resolution 616,167
  have eq661 : (sP5 sk0 c b) ∨ (sP1 sk0 c b) := resolve eq659 preserve_4 -- subsumption resolution 659,189
  have eq668 : (sP1 sk0 c b) ∨ c = sk0 := resolve eq661 rule_def_5_1 -- resolution 661,162
  have eq670 : (sP1 sk0 c b) := resolve eq668 preserve_4 -- subsumption resolution 668,189
  have eq675 : (old sk0 b a) := resolve eq670 rule_def_1_2 -- resolution 670,144
  have eq688 : memold sk0 := resolve eq675 old_mem1 -- resolution 675,182
  subsumption preserve_3 eq688 -- subsumption resolution 688,188

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_1_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (memold : G → Prop) (bc : c ≠ b) (rule_def_0_1 : ∀ (X Y Z : G), b = Y ∨ ¬sP0 X Y Z) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_0 : ∀ (X Y Z : G), c = Y ∨ ¬sP1 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_2_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP2 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP2 X Y Z) (rule_def_3_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP3 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP3 X Y Z) (rule_def_4_2 : ∀ (X Y Z : G), b = Y ∨ ¬sP4 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP4 X Y Z) (rule_def_5_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP5 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP5 X Y Z) (rule_def_6_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP6 X Y Z) (rule_def_6_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP6 X Y Z) (rule_def_7_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP7 X Y Z) (rule_def_7_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP7 X Y Z) (rule_def_8_2 : ∀ (X Y Z : G), c = Y ∨ ¬sP8 X Y Z) (rule_def_8_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP8 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z) (old_mem2 : ∀ (X Y Z), ¬old X Y Z ∨ memold Y) : ∀ (X Y Z : G), ¬new X Y Z ∨ Y = a ∨ Y = b ∨ memold Y ∨ Y = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq216 : (sP8 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 181,185
  have eq229 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ b = sk2 := resolve eq216 rule_def_8_3 -- resolution 216,179
  have eq230 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ c = sk1 := resolve eq216 rule_def_8_2 -- resolution 216,178
  have eq233 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq229 rule_def_7_3 -- subsumption resolution 229,174
  have eq234 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq233 rule_def_6_3 -- subsumption resolution 233,169
  have eq235 : (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq234 rule_def_5_3 -- subsumption resolution 234,164
  have eq236 : (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq235 rule_def_1_1 -- subsumption resolution 235,143
  have eq237 : (sP7 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) := resolve eq230 preserve_4 -- subsumption resolution 230,189
  have eq239 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 ∨ b = sk1 := resolve eq236 rule_def_4_2 -- resolution 236,158
  have eq245 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq239 preserve_2 -- subsumption resolution 239,187
  have eq247 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ c = sk1 := resolve eq237 rule_def_7_2 -- resolution 237,173
  have eq250 : (sP6 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) := resolve eq247 preserve_4 -- subsumption resolution 247,189
  have eq259 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 ∨ b = sk1 := resolve eq245 rule_def_3_2 -- resolution 245,153
  have eq262 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq259 preserve_2 -- subsumption resolution 259,187
  have eq274 : (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ c = sk1 := resolve eq250 rule_def_6_2 -- resolution 250,168
  have eq278 : (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) := resolve eq274 preserve_4 -- subsumption resolution 274,189
  have eq282 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 ∨ b = sk1 := resolve eq262 rule_def_2_2 -- resolution 262,148
  have eq285 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq282 preserve_2 -- subsumption resolution 282,187
  have eq287 : (old sk0 sk1 sk2) ∨ b = sk2 ∨ b = sk1 := resolve eq285 rule_def_0_1 -- resolution 285,139
  have eq289 : (old sk0 sk1 sk2) ∨ b = sk2 := resolve eq287 preserve_2 -- subsumption resolution 287,187
  have eq300 : b = sk2 ∨ memold sk1 := resolve eq289 old_mem2 -- resolution 289,183
  have eq303 : b = sk2 := resolve eq300 preserve_3 -- subsumption resolution 300,188
  have eq316 : (sP5 sk0 sk1 b) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq303, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq278 -- backward demodulation 278,303
  have eq343 : (sP4 sk0 sk1 b) ∨ (sP5 sk0 sk1 b) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq303, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq316 -- forward demodulation 316,303
  have eq344 : (sP3 sk0 sk1 b) ∨ (sP4 sk0 sk1 b) ∨ (sP5 sk0 sk1 b) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq303, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq343 -- forward demodulation 343,303
  have eq345 : (sP2 sk0 sk1 b) ∨ (sP3 sk0 sk1 b) ∨ (sP4 sk0 sk1 b) ∨ (sP5 sk0 sk1 b) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq303, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq344 -- forward demodulation 344,303
  have eq346 : (sP1 sk0 sk1 b) ∨ (sP2 sk0 sk1 b) ∨ (sP3 sk0 sk1 b) ∨ (sP4 sk0 sk1 b) ∨ (sP5 sk0 sk1 b) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq303, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq345 -- forward demodulation 345,303
  have eq347 : (sP0 sk0 sk1 b) ∨ (sP1 sk0 sk1 b) ∨ (sP2 sk0 sk1 b) ∨ (sP3 sk0 sk1 b) ∨ (sP4 sk0 sk1 b) ∨ (sP5 sk0 sk1 b) ∨ (old sk0 sk1 sk2) := Eq.mp (by simp only [eq303, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq346 -- forward demodulation 346,303
  have eq348 : (sP5 sk0 sk1 b) ∨ (sP0 sk0 sk1 b) ∨ (sP1 sk0 sk1 b) ∨ (sP2 sk0 sk1 b) ∨ (sP3 sk0 sk1 b) ∨ (sP4 sk0 sk1 b) ∨ (old sk0 sk1 b) := Eq.mp (by simp only [eq303, or_comm, or_left_comm, or_assoc, eq_comm, ne_comm]) eq347 -- forward demodulation 347,303
  have eq378 : (sP0 sk0 sk1 b) ∨ (sP1 sk0 sk1 b) ∨ (sP2 sk0 sk1 b) ∨ (sP3 sk0 sk1 b) ∨ (sP4 sk0 sk1 b) ∨ (old sk0 sk1 b) ∨ c = sk1 := resolve eq348 rule_def_5_2 -- resolution 348,163
  have eq381 : (sP4 sk0 sk1 b) ∨ (sP1 sk0 sk1 b) ∨ (sP2 sk0 sk1 b) ∨ (sP3 sk0 sk1 b) ∨ (sP0 sk0 sk1 b) ∨ (old sk0 sk1 b) := resolve eq378 preserve_4 -- subsumption resolution 378,189
  have eq386 : (sP1 sk0 sk1 b) ∨ (sP2 sk0 sk1 b) ∨ (sP3 sk0 sk1 b) ∨ (sP0 sk0 sk1 b) ∨ (old sk0 sk1 b) ∨ c = b := resolve eq381 rule_def_4_3 -- resolution 381,159
  have eq390 : (sP3 sk0 sk1 b) ∨ (sP2 sk0 sk1 b) ∨ (sP1 sk0 sk1 b) ∨ (sP0 sk0 sk1 b) ∨ (old sk0 sk1 b) := resolve eq386 bc -- subsumption resolution 386,125
  have eq394 : (sP2 sk0 sk1 b) ∨ (sP1 sk0 sk1 b) ∨ (sP0 sk0 sk1 b) ∨ (old sk0 sk1 b) ∨ c = b := resolve eq390 rule_def_3_3 -- resolution 390,154
  have eq398 : (sP2 sk0 sk1 b) ∨ (sP1 sk0 sk1 b) ∨ (sP0 sk0 sk1 b) ∨ (old sk0 sk1 b) := resolve eq394 bc -- subsumption resolution 394,125
  have eq399 : (sP1 sk0 sk1 b) ∨ (sP0 sk0 sk1 b) ∨ (old sk0 sk1 b) ∨ c = b := resolve eq398 rule_def_2_3 -- resolution 398,149
  have eq403 : (sP1 sk0 sk1 b) ∨ (sP0 sk0 sk1 b) ∨ (old sk0 sk1 b) := resolve eq399 bc -- subsumption resolution 399,125
  have eq406 : (sP0 sk0 sk1 b) ∨ (old sk0 sk1 b) ∨ c = sk1 := resolve eq403 rule_def_1_0 -- resolution 403,142
  have eq407 : (sP0 sk0 sk1 b) ∨ (old sk0 sk1 b) := resolve eq406 preserve_4 -- subsumption resolution 406,189
  have eq408 : (old sk0 sk1 b) ∨ c = b := resolve eq407 rule_def_0_2 -- resolution 407,140
  have eq411 : (old sk0 sk1 b) := resolve eq408 bc -- subsumption resolution 408,125
  have eq419 : memold sk1 := resolve eq411 old_mem2 -- resolution 411,183
  subsumption preserve_3 eq419 -- subsumption resolution 419,188

set_option linter.all false in
set_option maxHeartbeats 4000000 in
theorem rule_finite_2_preserved (G : Type*) (a b c : G) (old : G → G → G → Prop) (new : G → G → G → Prop) (sP0 : G → G → G → Prop) (sP1 : G → G → G → Prop) (sP2 : G → G → G → Prop) (sP3 : G → G → G → Prop) (sP4 : G → G → G → Prop) (sP5 : G → G → G → Prop) (sP6 : G → G → G → Prop) (sP7 : G → G → G → Prop) (sP8 : G → G → G → Prop) (memold : G → Prop) (rule_def_0_2 : ∀ (X Y Z : G), c = Z ∨ ¬sP0 X Y Z) (rule_def_1_1 : ∀ (X Y Z : G), b = Z ∨ ¬sP1 X Y Z) (rule_def_2_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP2 X Y Z) (rule_def_3_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP3 X Y Z) (rule_def_4_3 : ∀ (X Y Z : G), c = Z ∨ ¬sP4 X Y Z) (rule_def_5_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP5 X Y Z) (rule_def_6_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP6 X Y Z) (rule_def_7_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP7 X Y Z) (rule_def_8_3 : ∀ (X Y Z : G), b = Z ∨ ¬sP8 X Y Z) (new_imp : ∀ (X Y Z), ¬ new X Y Z ∨ old X Y Z ∨ sP0 X Y Z ∨ sP1 X Y Z ∨ sP2 X Y Z ∨ sP3 X Y Z ∨ sP4 X Y Z ∨ sP5 X Y Z ∨ sP6 X Y Z ∨ sP7 X Y Z ∨ sP8 X Y Z) (old_mem3 : ∀ (X Y Z), ¬old X Y Z ∨ memold Z) : ∀ (X Y Z : G), ¬new X Y Z ∨ Z = a ∨ Z = b ∨ memold Z ∨ Z = c := by
  by_contra! nh
  obtain ⟨sk0, sk1, sk2, preserve_0, preserve_1, preserve_2, preserve_3, preserve_4⟩ := nh
  have eq216 : (sP8 sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) := resolve new_imp preserve_0 -- resolution 181,185
  have eq229 : (sP6 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP7 sk0 sk1 sk2) ∨ b = sk2 := resolve eq216 rule_def_8_3 -- resolution 216,179
  have eq233 : (sP7 sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) := resolve eq229 preserve_2 -- subsumption resolution 229,187
  have eq239 : (sP5 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP6 sk0 sk1 sk2) ∨ b = sk2 := resolve eq233 rule_def_7_3 -- resolution 233,174
  have eq243 : (sP6 sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) := resolve eq239 preserve_2 -- subsumption resolution 239,187
  have eq249 : (sP4 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP5 sk0 sk1 sk2) ∨ b = sk2 := resolve eq243 rule_def_6_3 -- resolution 243,169
  have eq253 : (sP5 sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) := resolve eq249 preserve_2 -- subsumption resolution 249,187
  have eq259 : (sP3 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP4 sk0 sk1 sk2) ∨ b = sk2 := resolve eq253 rule_def_5_3 -- resolution 253,164
  have eq263 : (sP4 sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) := resolve eq259 preserve_2 -- subsumption resolution 259,187
  have eq269 : (sP2 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP3 sk0 sk1 sk2) ∨ c = sk2 := resolve eq263 rule_def_4_3 -- resolution 263,159
  have eq273 : (sP3 sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) := resolve eq269 preserve_4 -- subsumption resolution 269,189
  have eq279 : (sP1 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP2 sk0 sk1 sk2) ∨ c = sk2 := resolve eq273 rule_def_3_3 -- resolution 273,154
  have eq283 : (sP2 sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) := resolve eq279 preserve_4 -- subsumption resolution 279,189
  have eq288 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP1 sk0 sk1 sk2) ∨ c = sk2 := resolve eq283 rule_def_2_3 -- resolution 283,149
  have eq292 : (sP1 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) := resolve eq288 preserve_4 -- subsumption resolution 288,189
  have eq297 : (old sk0 sk1 sk2) ∨ (sP0 sk0 sk1 sk2) ∨ b = sk2 := resolve eq292 rule_def_1_1 -- resolution 292,143
  have eq299 : (sP0 sk0 sk1 sk2) ∨ (old sk0 sk1 sk2) := resolve eq297 preserve_2 -- subsumption resolution 297,187
  have eq300 : (old sk0 sk1 sk2) ∨ c = sk2 := resolve eq299 rule_def_0_2 -- resolution 299,140
  have eq303 : (old sk0 sk1 sk2) := resolve eq300 preserve_4 -- subsumption resolution 300,189
  have eq310 : memold sk2 := resolve eq303 old_mem3 -- resolution 303,184
  subsumption preserve_3 eq310 -- subsumption resolution 310,188

structure PartialSolution (G : Type*) where
  R : G → G → G → Prop
  rule_0 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X0 X1 X3 ∨ X2 = X3)
  rule_1 : (∀ X0 X1 X2 X3, ¬ R X0 X1 X2 ∨ ¬ R X2 X1 X3 ∨ R X0 X3 X1)
  rule_2 : (∀ X0 X1, ¬ R X0 X0 X1 ∨ R X1 X0 X1)
  rule_3 : (∀ X0 X1, ¬ R X0 X0 X1 ∨ R X1 X1 X0)
  rule_4 : (∀ X0 X1, ¬ R X0 X0 X1 ∨ R X0 X1 X0)
  rule_5 : (∀ X0 X1, ¬ R X0 X1 X1 ∨ R X1 X1 X1)
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
  let sP1 (X Y Z) := c = Y ∧ b = Z ∧ ps.R X b a
  have hsP1 (X Y Z) (h : sP1 X Y Z) : c = Y ∧ b = Z ∧ ps.R X b a := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP1
  obtain ⟨rule_def_1_0, rule_def_1_1, rule_def_1_2⟩ := hsP1
  simp_rw [or_comm] at rule_def_1_0 rule_def_1_1 rule_def_1_2
  let sP2 (X Y Z) := a = b ∧ c = X ∧ b = Y ∧ c = Z
  have hsP2 (X Y Z) (h : sP2 X Y Z) : a = b ∧ c = X ∧ b = Y ∧ c = Z := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP2
  obtain ⟨rule_def_2_0, rule_def_2_1, rule_def_2_2, rule_def_2_3⟩ := hsP2
  simp_rw [or_comm] at rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3
  let sP3 (X Y Z) := a = b ∧ c = X ∧ b = Y ∧ c = Z
  have hsP3 (X Y Z) (h : sP3 X Y Z) : a = b ∧ c = X ∧ b = Y ∧ c = Z := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP3
  obtain ⟨rule_def_3_0, rule_def_3_1, rule_def_3_2, rule_def_3_3⟩ := hsP3
  simp_rw [or_comm] at rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3
  let sP4 (X Y Z) := a = b ∧ c = X ∧ b = Y ∧ c = Z
  have hsP4 (X Y Z) (h : sP4 X Y Z) : a = b ∧ c = X ∧ b = Y ∧ c = Z := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP4
  obtain ⟨rule_def_4_0, rule_def_4_1, rule_def_4_2, rule_def_4_3⟩ := hsP4
  simp_rw [or_comm] at rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_3
  let sP5 (X Y Z) := a = b ∧ c = X ∧ c = Y ∧ b = Z
  have hsP5 (X Y Z) (h : sP5 X Y Z) : a = b ∧ c = X ∧ c = Y ∧ b = Z := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP5
  obtain ⟨rule_def_5_0, rule_def_5_1, rule_def_5_2, rule_def_5_3⟩ := hsP5
  simp_rw [or_comm] at rule_def_5_0 rule_def_5_1 rule_def_5_2 rule_def_5_3
  let sP6 (X Y Z) := a = b ∧ c = X ∧ c = Y ∧ b = Z
  have hsP6 (X Y Z) (h : sP6 X Y Z) : a = b ∧ c = X ∧ c = Y ∧ b = Z := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP6
  obtain ⟨rule_def_6_0, rule_def_6_1, rule_def_6_2, rule_def_6_3⟩ := hsP6
  simp_rw [or_comm] at rule_def_6_0 rule_def_6_1 rule_def_6_2 rule_def_6_3
  let sP7 (X Y Z) := a = b ∧ c = X ∧ c = Y ∧ b = Z
  have hsP7 (X Y Z) (h : sP7 X Y Z) : a = b ∧ c = X ∧ c = Y ∧ b = Z := h
  simp only [imp_and, imp_iff_not_or, forall_and] at hsP7
  obtain ⟨rule_def_7_0, rule_def_7_1, rule_def_7_2, rule_def_7_3⟩ := hsP7
  simp_rw [or_comm] at rule_def_7_0 rule_def_7_1 rule_def_7_2 rule_def_7_3
  let sP8 (X Y Z) := a = b ∧ b = X ∧ c = Y ∧ b = Z
  have hsP8 (X Y Z) (h : sP8 X Y Z) : a = b ∧ b = X ∧ c = Y ∧ b = Z := h
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

  have prev_0 := rule_0_preserved G a b c ps.R new sP0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 ac bc p3 p4XY p4XZ p4YZ ps.rule_0 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_3 rule_def_5_0 rule_def_5_2 rule_def_5_3 rule_def_6_0 rule_def_6_2 rule_def_6_3 rule_def_7_0 rule_def_7_2 rule_def_7_3 rule_def_8_0 rule_def_8_2 rule_def_8_3 new_imp
  have prev_1 := rule_1_preserved G a b c ps.R new sP0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 ac bc p3 p4XY p4XZ p4YZ prev_0 ps.rule_1 ps.rule_2 ps.rule_5 imp_new_1 rule_def_0_0 rule_def_0_1 rule_def_0_2 imp_new_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 imp_new_3 rule_def_2_0 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_3_0 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_4_0 rule_def_4_1 rule_def_4_2 rule_def_4_3 imp_new_6 rule_def_5_0 rule_def_5_1 rule_def_5_2 rule_def_5_3 rule_def_6_0 rule_def_6_1 rule_def_6_2 rule_def_6_3 rule_def_7_0 rule_def_7_1 rule_def_7_2 rule_def_7_3 imp_new_9 rule_def_8_0 rule_def_8_1 rule_def_8_2 rule_def_8_3 new_imp imp_new_0
  have prev_2 := rule_2_preserved G a b c ps.R new sP0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 ac bc p4XY p4YZ ps.rule_2 rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 imp_new_3 rule_def_2_1 rule_def_2_2 rule_def_3_1 rule_def_3_2 rule_def_4_1 rule_def_4_2 rule_def_5_0 rule_def_5_2 rule_def_5_3 rule_def_6_0 rule_def_6_2 rule_def_6_3 rule_def_7_0 rule_def_7_2 rule_def_7_3 imp_new_9 rule_def_8_1 rule_def_8_2 rule_def_8_3 new_imp imp_new_0
  have prev_3 := rule_3_preserved G a b c ps.R new sP0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 prev_1 prev_2
  have prev_4 := rule_4_preserved G a b c ps.R new sP0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 prev_2 prev_3
  have prev_5 := rule_5_preserved G a b c ps.R new sP0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 bc ps.rule_5 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_2_2 rule_def_2_3 rule_def_3_2 rule_def_3_3 rule_def_4_2 rule_def_4_3 rule_def_5_2 rule_def_5_3 rule_def_6_2 rule_def_6_3 rule_def_7_2 rule_def_7_3 rule_def_8_2 rule_def_8_3 new_imp imp_new_0

  exact ⟨{
    R := new
    rule_0 := prev_0
    rule_1 := prev_1
    rule_2 := prev_2
    rule_3 := prev_3
    rule_4 := prev_4
    rule_5 := prev_5
    finsupp := ps.finsupp ∪ {a, b, c}
    mem_1 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_0_preserved G a b c ps.R new sP0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 (· ∈ ps.finsupp) bc p4XY p4XZ rule_def_0_0 rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_1_2 rule_def_2_1 rule_def_2_2 rule_def_2_3 rule_def_3_1 rule_def_3_2 rule_def_3_3 rule_def_4_1 rule_def_4_2 rule_def_4_3 rule_def_5_1 rule_def_5_2 rule_def_5_3 rule_def_6_1 rule_def_6_2 rule_def_6_3 rule_def_7_1 rule_def_7_2 rule_def_7_3 rule_def_8_1 rule_def_8_2 rule_def_8_3 new_imp ps.mem_1
    mem_2 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_1_preserved G a b c ps.R new sP0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 (· ∈ ps.finsupp) bc rule_def_0_1 rule_def_0_2 rule_def_1_0 rule_def_1_1 rule_def_2_2 rule_def_2_3 rule_def_3_2 rule_def_3_3 rule_def_4_2 rule_def_4_3 rule_def_5_2 rule_def_5_3 rule_def_6_2 rule_def_6_3 rule_def_7_2 rule_def_7_3 rule_def_8_2 rule_def_8_3 new_imp ps.mem_2
    mem_3 := by simpa only [Finset.union_insert, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] using rule_finite_2_preserved G a b c ps.R new sP0 sP1 sP2 sP3 sP4 sP5 sP6 sP7 sP8 (· ∈ ps.finsupp) rule_def_0_2 rule_def_1_1 rule_def_2_3 rule_def_3_3 rule_def_4_3 rule_def_5_3 rule_def_6_3 rule_def_7_3 rule_def_8_3 new_imp ps.mem_3
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
    ¬ ps.compl X0 X1 X2 ∨ ¬ ps.compl X2 X1 X3 ∨ ps.compl X0 X3 X1 := by
  let i := 1 + max (Nat.pair X0 X1) (max (Nat.pair X2 X1) (max (Nat.pair X0 X3) 0))
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

theorem PartialSolution.toMagma_equation124 :
    letI := ps.toMagma
    Equation124 ℕ := by
  simp only [Equation124, PartialSolution.toMagma]
  intro X0 X1
  simpa [← PartialSolution.complFun_eq_iff, eq_comm] using
    ps.compl_rule1 X1 X0 (ps.complFun X1 X0) (ps.complFun (ps.complFun X1 X0) X0)


set_option maxRecDepth 1000 in
noncomputable def PartialSolution.counter1924 : PartialSolution ℕ where
  R x y z := (x, y, z) ∈ ({(1, 1, 3), (1, 2, 3), (1, 3, 1), (2, 1, 3), (2, 3, 1), (3, 1, 3), (3, 3, 1)} : Finset _)
  rule_0 := by simp only [← imp_iff_not_or]; aesop
  rule_1 := by simp only [← imp_iff_not_or]; aesop
  rule_2 := by simp only [← imp_iff_not_or]; aesop
  rule_3 := by simp only [← imp_iff_not_or]; aesop
  rule_4 := by simp only [← imp_iff_not_or]; aesop
  rule_5 := by simp only [← imp_iff_not_or]; aesop
  finsupp := {1, 2, 3}
  mem_1 := by simp only [← imp_iff_not_or]; aesop
  mem_2 := by simp only [← imp_iff_not_or]; aesop
  mem_3 := by simp only [← imp_iff_not_or]; aesop

@[equational_result]
theorem _root_.Equation124_not_implies_Equation1924 : ∃ (G : Type) (_ : Magma G), Equation124 G ∧ ¬Equation1924 G := by
  use ℕ, PartialSolution.counter1924.toMagma, PartialSolution.counter1924.toMagma_equation124
  simp only [not_forall, PartialSolution.toMagma]
  use 2, 1
  repeat (first | rw [PartialSolution.counter1924.of_R 1 1 3] | rw [PartialSolution.counter1924.of_R 1 2 3] | rw [PartialSolution.counter1924.of_R 1 3 1] | rw [PartialSolution.counter1924.of_R 2 1 3] | rw [PartialSolution.counter1924.of_R 2 3 1] | rw [PartialSolution.counter1924.of_R 3 1 3] | rw [PartialSolution.counter1924.of_R 3 3 1])
  all_goals simp [PartialSolution.counter1924]

end Eq124
