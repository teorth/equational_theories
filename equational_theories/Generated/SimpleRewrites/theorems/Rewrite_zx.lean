import Mathlib.Tactic
import Mathlib.Data.Nat.Defs
import equational_theories.AllEquations
import equational_theories.Magma

namespace SimpleRewrites



@[equational_result]
theorem Equation7_implies_Equation5 (G : Type*) [Magma G] (h : Equation7 G) : Equation5 G := λ x y => h x y x
@[equational_result]
theorem Equation12_implies_Equation10 (G : Type*) [Magma G] (h : Equation12 G) : Equation10 G := λ x y => h x y x
@[equational_result]
theorem Equation15_implies_Equation13 (G : Type*) [Magma G] (h : Equation15 G) : Equation13 G := λ x y => h x y x
@[equational_result]
theorem Equation18_implies_Equation16 (G : Type*) [Magma G] (h : Equation18 G) : Equation16 G := λ x y => h x y x
@[equational_result]
theorem Equation19_implies_Equation13 (G : Type*) [Magma G] (h : Equation19 G) : Equation13 G := λ x y => h x y x
@[equational_result]
theorem Equation20_implies_Equation14 (G : Type*) [Magma G] (h : Equation20 G) : Equation14 G := λ x y => h x y x
@[equational_result]
theorem Equation21_implies_Equation13 (G : Type*) [Magma G] (h : Equation21 G) : Equation13 G := λ x y => h x y x
@[equational_result]
theorem Equation27_implies_Equation25 (G : Type*) [Magma G] (h : Equation27 G) : Equation25 G := λ x y => h x y x
@[equational_result]
theorem Equation30_implies_Equation28 (G : Type*) [Magma G] (h : Equation30 G) : Equation28 G := λ x y => h x y x
@[equational_result]
theorem Equation33_implies_Equation31 (G : Type*) [Magma G] (h : Equation33 G) : Equation31 G := λ x y => h x y x
@[equational_result]
theorem Equation34_implies_Equation28 (G : Type*) [Magma G] (h : Equation34 G) : Equation28 G := λ x y => h x y x
@[equational_result]
theorem Equation35_implies_Equation29 (G : Type*) [Magma G] (h : Equation35 G) : Equation29 G := λ x y => h x y x
@[equational_result]
theorem Equation36_implies_Equation28 (G : Type*) [Magma G] (h : Equation36 G) : Equation28 G := λ x y => h x y x
@[equational_result]
theorem Equation41_implies_Equation39 (G : Type*) [Magma G] (h : Equation41 G) : Equation39 G := λ x y => h x y x
@[equational_result]
theorem Equation44_implies_Equation43 (G : Type*) [Magma G] (h : Equation44 G) : Equation43 G := λ x y => h x y x
@[equational_result]
theorem Equation51_implies_Equation49 (G : Type*) [Magma G] (h : Equation51 G) : Equation49 G := λ x y => h x y x
@[equational_result]
theorem Equation54_implies_Equation52 (G : Type*) [Magma G] (h : Equation54 G) : Equation52 G := λ x y => h x y x
@[equational_result]
theorem Equation57_implies_Equation55 (G : Type*) [Magma G] (h : Equation57 G) : Equation55 G := λ x y => h x y x
@[equational_result]
theorem Equation58_implies_Equation52 (G : Type*) [Magma G] (h : Equation58 G) : Equation52 G := λ x y => h x y x
@[equational_result]
theorem Equation59_implies_Equation53 (G : Type*) [Magma G] (h : Equation59 G) : Equation53 G := λ x y => h x y x
@[equational_result]
theorem Equation60_implies_Equation52 (G : Type*) [Magma G] (h : Equation60 G) : Equation52 G := λ x y => h x y x
@[equational_result]
theorem Equation64_implies_Equation62 (G : Type*) [Magma G] (h : Equation64 G) : Equation62 G := λ x y => h x y x
@[equational_result]
theorem Equation67_implies_Equation65 (G : Type*) [Magma G] (h : Equation67 G) : Equation65 G := λ x y => h x y x
@[equational_result]
theorem Equation68_implies_Equation62 (G : Type*) [Magma G] (h : Equation68 G) : Equation62 G := λ x y => h x y x
@[equational_result]
theorem Equation69_implies_Equation63 (G : Type*) [Magma G] (h : Equation69 G) : Equation63 G := λ x y => h x y x
@[equational_result]
theorem Equation70_implies_Equation62 (G : Type*) [Magma G] (h : Equation70 G) : Equation62 G := λ x y => h x y x
@[equational_result]
theorem Equation74_implies_Equation72 (G : Type*) [Magma G] (h : Equation74 G) : Equation72 G := λ x y => h x y x
@[equational_result]
theorem Equation77_implies_Equation75 (G : Type*) [Magma G] (h : Equation77 G) : Equation75 G := λ x y => h x y x
@[equational_result]
theorem Equation78_implies_Equation72 (G : Type*) [Magma G] (h : Equation78 G) : Equation72 G := λ x y => h x y x
@[equational_result]
theorem Equation79_implies_Equation73 (G : Type*) [Magma G] (h : Equation79 G) : Equation73 G := λ x y => h x y x
@[equational_result]
theorem Equation80_implies_Equation72 (G : Type*) [Magma G] (h : Equation80 G) : Equation72 G := λ x y => h x y x
@[equational_result]
theorem Equation82_implies_Equation62 (G : Type*) [Magma G] (h : Equation82 G) : Equation62 G := λ x y => h x y x
@[equational_result]
theorem Equation83_implies_Equation63 (G : Type*) [Magma G] (h : Equation83 G) : Equation63 G := λ x y => h x y x
@[equational_result]
theorem Equation84_implies_Equation62 (G : Type*) [Magma G] (h : Equation84 G) : Equation62 G := λ x y => h x y x
@[equational_result]
theorem Equation86_implies_Equation65 (G : Type*) [Magma G] (h : Equation86 G) : Equation65 G := λ x y => h x y x
@[equational_result]
theorem Equation87_implies_Equation66 (G : Type*) [Magma G] (h : Equation87 G) : Equation66 G := λ x y => h x y x
@[equational_result]
theorem Equation88_implies_Equation65 (G : Type*) [Magma G] (h : Equation88 G) : Equation65 G := λ x y => h x y x
@[equational_result]
theorem Equation90_implies_Equation62 (G : Type*) [Magma G] (h : Equation90 G) : Equation62 G := λ x y => h x y x
@[equational_result]
theorem Equation91_implies_Equation63 (G : Type*) [Magma G] (h : Equation91 G) : Equation63 G := λ x y => h x y x
@[equational_result]
theorem Equation92_implies_Equation62 (G : Type*) [Magma G] (h : Equation92 G) : Equation62 G := λ x y => h x y x
@[equational_result]
theorem Equation103_implies_Equation101 (G : Type*) [Magma G] (h : Equation103 G) : Equation101 G := λ x y => h x y x
@[equational_result]
theorem Equation106_implies_Equation104 (G : Type*) [Magma G] (h : Equation106 G) : Equation104 G := λ x y => h x y x
@[equational_result]
theorem Equation109_implies_Equation107 (G : Type*) [Magma G] (h : Equation109 G) : Equation107 G := λ x y => h x y x
@[equational_result]
theorem Equation110_implies_Equation104 (G : Type*) [Magma G] (h : Equation110 G) : Equation104 G := λ x y => h x y x
@[equational_result]
theorem Equation111_implies_Equation105 (G : Type*) [Magma G] (h : Equation111 G) : Equation105 G := λ x y => h x y x
@[equational_result]
theorem Equation112_implies_Equation104 (G : Type*) [Magma G] (h : Equation112 G) : Equation104 G := λ x y => h x y x
@[equational_result]
theorem Equation116_implies_Equation114 (G : Type*) [Magma G] (h : Equation116 G) : Equation114 G := λ x y => h x y x
@[equational_result]
theorem Equation119_implies_Equation117 (G : Type*) [Magma G] (h : Equation119 G) : Equation117 G := λ x y => h x y x
@[equational_result]
theorem Equation120_implies_Equation114 (G : Type*) [Magma G] (h : Equation120 G) : Equation114 G := λ x y => h x y x
@[equational_result]
theorem Equation121_implies_Equation115 (G : Type*) [Magma G] (h : Equation121 G) : Equation115 G := λ x y => h x y x
@[equational_result]
theorem Equation122_implies_Equation114 (G : Type*) [Magma G] (h : Equation122 G) : Equation114 G := λ x y => h x y x
@[equational_result]
theorem Equation126_implies_Equation124 (G : Type*) [Magma G] (h : Equation126 G) : Equation124 G := λ x y => h x y x
@[equational_result]
theorem Equation129_implies_Equation127 (G : Type*) [Magma G] (h : Equation129 G) : Equation127 G := λ x y => h x y x
@[equational_result]
theorem Equation130_implies_Equation124 (G : Type*) [Magma G] (h : Equation130 G) : Equation124 G := λ x y => h x y x
@[equational_result]
theorem Equation131_implies_Equation125 (G : Type*) [Magma G] (h : Equation131 G) : Equation125 G := λ x y => h x y x
@[equational_result]
theorem Equation132_implies_Equation124 (G : Type*) [Magma G] (h : Equation132 G) : Equation124 G := λ x y => h x y x
@[equational_result]
theorem Equation134_implies_Equation114 (G : Type*) [Magma G] (h : Equation134 G) : Equation114 G := λ x y => h x y x
@[equational_result]
theorem Equation135_implies_Equation115 (G : Type*) [Magma G] (h : Equation135 G) : Equation115 G := λ x y => h x y x
@[equational_result]
theorem Equation136_implies_Equation114 (G : Type*) [Magma G] (h : Equation136 G) : Equation114 G := λ x y => h x y x
@[equational_result]
theorem Equation138_implies_Equation117 (G : Type*) [Magma G] (h : Equation138 G) : Equation117 G := λ x y => h x y x
@[equational_result]
theorem Equation139_implies_Equation118 (G : Type*) [Magma G] (h : Equation139 G) : Equation118 G := λ x y => h x y x
@[equational_result]
theorem Equation140_implies_Equation117 (G : Type*) [Magma G] (h : Equation140 G) : Equation117 G := λ x y => h x y x
@[equational_result]
theorem Equation142_implies_Equation114 (G : Type*) [Magma G] (h : Equation142 G) : Equation114 G := λ x y => h x y x
@[equational_result]
theorem Equation143_implies_Equation115 (G : Type*) [Magma G] (h : Equation143 G) : Equation115 G := λ x y => h x y x
@[equational_result]
theorem Equation144_implies_Equation114 (G : Type*) [Magma G] (h : Equation144 G) : Equation114 G := λ x y => h x y x
@[equational_result]
theorem Equation155_implies_Equation153 (G : Type*) [Magma G] (h : Equation155 G) : Equation153 G := λ x y => h x y x
@[equational_result]
theorem Equation158_implies_Equation156 (G : Type*) [Magma G] (h : Equation158 G) : Equation156 G := λ x y => h x y x
@[equational_result]
theorem Equation161_implies_Equation159 (G : Type*) [Magma G] (h : Equation161 G) : Equation159 G := λ x y => h x y x
@[equational_result]
theorem Equation162_implies_Equation156 (G : Type*) [Magma G] (h : Equation162 G) : Equation156 G := λ x y => h x y x
@[equational_result]
theorem Equation163_implies_Equation157 (G : Type*) [Magma G] (h : Equation163 G) : Equation157 G := λ x y => h x y x
@[equational_result]
theorem Equation164_implies_Equation156 (G : Type*) [Magma G] (h : Equation164 G) : Equation156 G := λ x y => h x y x
@[equational_result]
theorem Equation168_implies_Equation166 (G : Type*) [Magma G] (h : Equation168 G) : Equation166 G := λ x y => h x y x
@[equational_result]
theorem Equation171_implies_Equation169 (G : Type*) [Magma G] (h : Equation171 G) : Equation169 G := λ x y => h x y x
@[equational_result]
theorem Equation172_implies_Equation166 (G : Type*) [Magma G] (h : Equation172 G) : Equation166 G := λ x y => h x y x
@[equational_result]
theorem Equation173_implies_Equation167 (G : Type*) [Magma G] (h : Equation173 G) : Equation167 G := λ x y => h x y x
@[equational_result]
theorem Equation174_implies_Equation166 (G : Type*) [Magma G] (h : Equation174 G) : Equation166 G := λ x y => h x y x
@[equational_result]
theorem Equation178_implies_Equation176 (G : Type*) [Magma G] (h : Equation178 G) : Equation176 G := λ x y => h x y x
@[equational_result]
theorem Equation181_implies_Equation179 (G : Type*) [Magma G] (h : Equation181 G) : Equation179 G := λ x y => h x y x
@[equational_result]
theorem Equation182_implies_Equation176 (G : Type*) [Magma G] (h : Equation182 G) : Equation176 G := λ x y => h x y x
@[equational_result]
theorem Equation183_implies_Equation177 (G : Type*) [Magma G] (h : Equation183 G) : Equation177 G := λ x y => h x y x
@[equational_result]
theorem Equation184_implies_Equation176 (G : Type*) [Magma G] (h : Equation184 G) : Equation176 G := λ x y => h x y x
@[equational_result]
theorem Equation186_implies_Equation166 (G : Type*) [Magma G] (h : Equation186 G) : Equation166 G := λ x y => h x y x
@[equational_result]
theorem Equation187_implies_Equation167 (G : Type*) [Magma G] (h : Equation187 G) : Equation167 G := λ x y => h x y x
@[equational_result]
theorem Equation188_implies_Equation166 (G : Type*) [Magma G] (h : Equation188 G) : Equation166 G := λ x y => h x y x
@[equational_result]
theorem Equation190_implies_Equation169 (G : Type*) [Magma G] (h : Equation190 G) : Equation169 G := λ x y => h x y x
@[equational_result]
theorem Equation191_implies_Equation170 (G : Type*) [Magma G] (h : Equation191 G) : Equation170 G := λ x y => h x y x
@[equational_result]
theorem Equation192_implies_Equation169 (G : Type*) [Magma G] (h : Equation192 G) : Equation169 G := λ x y => h x y x
@[equational_result]
theorem Equation194_implies_Equation166 (G : Type*) [Magma G] (h : Equation194 G) : Equation166 G := λ x y => h x y x
@[equational_result]
theorem Equation195_implies_Equation167 (G : Type*) [Magma G] (h : Equation195 G) : Equation167 G := λ x y => h x y x
@[equational_result]
theorem Equation196_implies_Equation166 (G : Type*) [Magma G] (h : Equation196 G) : Equation166 G := λ x y => h x y x
@[equational_result]
theorem Equation207_implies_Equation205 (G : Type*) [Magma G] (h : Equation207 G) : Equation205 G := λ x y => h x y x
@[equational_result]
theorem Equation210_implies_Equation208 (G : Type*) [Magma G] (h : Equation210 G) : Equation208 G := λ x y => h x y x
@[equational_result]
theorem Equation213_implies_Equation211 (G : Type*) [Magma G] (h : Equation213 G) : Equation211 G := λ x y => h x y x
@[equational_result]
theorem Equation214_implies_Equation208 (G : Type*) [Magma G] (h : Equation214 G) : Equation208 G := λ x y => h x y x
@[equational_result]
theorem Equation215_implies_Equation209 (G : Type*) [Magma G] (h : Equation215 G) : Equation209 G := λ x y => h x y x
@[equational_result]
theorem Equation216_implies_Equation208 (G : Type*) [Magma G] (h : Equation216 G) : Equation208 G := λ x y => h x y x
@[equational_result]
theorem Equation220_implies_Equation218 (G : Type*) [Magma G] (h : Equation220 G) : Equation218 G := λ x y => h x y x
@[equational_result]
theorem Equation223_implies_Equation221 (G : Type*) [Magma G] (h : Equation223 G) : Equation221 G := λ x y => h x y x
@[equational_result]
theorem Equation224_implies_Equation218 (G : Type*) [Magma G] (h : Equation224 G) : Equation218 G := λ x y => h x y x
@[equational_result]
theorem Equation225_implies_Equation219 (G : Type*) [Magma G] (h : Equation225 G) : Equation219 G := λ x y => h x y x
@[equational_result]
theorem Equation226_implies_Equation218 (G : Type*) [Magma G] (h : Equation226 G) : Equation218 G := λ x y => h x y x
@[equational_result]
theorem Equation230_implies_Equation228 (G : Type*) [Magma G] (h : Equation230 G) : Equation228 G := λ x y => h x y x
@[equational_result]
theorem Equation233_implies_Equation231 (G : Type*) [Magma G] (h : Equation233 G) : Equation231 G := λ x y => h x y x
@[equational_result]
theorem Equation234_implies_Equation228 (G : Type*) [Magma G] (h : Equation234 G) : Equation228 G := λ x y => h x y x
@[equational_result]
theorem Equation235_implies_Equation229 (G : Type*) [Magma G] (h : Equation235 G) : Equation229 G := λ x y => h x y x
@[equational_result]
theorem Equation236_implies_Equation228 (G : Type*) [Magma G] (h : Equation236 G) : Equation228 G := λ x y => h x y x
@[equational_result]
theorem Equation238_implies_Equation218 (G : Type*) [Magma G] (h : Equation238 G) : Equation218 G := λ x y => h x y x
@[equational_result]
theorem Equation239_implies_Equation219 (G : Type*) [Magma G] (h : Equation239 G) : Equation219 G := λ x y => h x y x
@[equational_result]
theorem Equation240_implies_Equation218 (G : Type*) [Magma G] (h : Equation240 G) : Equation218 G := λ x y => h x y x
@[equational_result]
theorem Equation242_implies_Equation221 (G : Type*) [Magma G] (h : Equation242 G) : Equation221 G := λ x y => h x y x
@[equational_result]
theorem Equation243_implies_Equation222 (G : Type*) [Magma G] (h : Equation243 G) : Equation222 G := λ x y => h x y x
@[equational_result]
theorem Equation244_implies_Equation221 (G : Type*) [Magma G] (h : Equation244 G) : Equation221 G := λ x y => h x y x
@[equational_result]
theorem Equation246_implies_Equation218 (G : Type*) [Magma G] (h : Equation246 G) : Equation218 G := λ x y => h x y x
@[equational_result]
theorem Equation247_implies_Equation219 (G : Type*) [Magma G] (h : Equation247 G) : Equation219 G := λ x y => h x y x
@[equational_result]
theorem Equation248_implies_Equation218 (G : Type*) [Magma G] (h : Equation248 G) : Equation218 G := λ x y => h x y x
@[equational_result]
theorem Equation259_implies_Equation257 (G : Type*) [Magma G] (h : Equation259 G) : Equation257 G := λ x y => h x y x
@[equational_result]
theorem Equation262_implies_Equation260 (G : Type*) [Magma G] (h : Equation262 G) : Equation260 G := λ x y => h x y x
@[equational_result]
theorem Equation265_implies_Equation263 (G : Type*) [Magma G] (h : Equation265 G) : Equation263 G := λ x y => h x y x
@[equational_result]
theorem Equation266_implies_Equation260 (G : Type*) [Magma G] (h : Equation266 G) : Equation260 G := λ x y => h x y x
@[equational_result]
theorem Equation267_implies_Equation261 (G : Type*) [Magma G] (h : Equation267 G) : Equation261 G := λ x y => h x y x
@[equational_result]
theorem Equation268_implies_Equation260 (G : Type*) [Magma G] (h : Equation268 G) : Equation260 G := λ x y => h x y x
@[equational_result]
theorem Equation272_implies_Equation270 (G : Type*) [Magma G] (h : Equation272 G) : Equation270 G := λ x y => h x y x
@[equational_result]
theorem Equation275_implies_Equation273 (G : Type*) [Magma G] (h : Equation275 G) : Equation273 G := λ x y => h x y x
@[equational_result]
theorem Equation276_implies_Equation270 (G : Type*) [Magma G] (h : Equation276 G) : Equation270 G := λ x y => h x y x
@[equational_result]
theorem Equation277_implies_Equation271 (G : Type*) [Magma G] (h : Equation277 G) : Equation271 G := λ x y => h x y x
@[equational_result]
theorem Equation278_implies_Equation270 (G : Type*) [Magma G] (h : Equation278 G) : Equation270 G := λ x y => h x y x
@[equational_result]
theorem Equation282_implies_Equation280 (G : Type*) [Magma G] (h : Equation282 G) : Equation280 G := λ x y => h x y x
@[equational_result]
theorem Equation285_implies_Equation283 (G : Type*) [Magma G] (h : Equation285 G) : Equation283 G := λ x y => h x y x
@[equational_result]
theorem Equation286_implies_Equation280 (G : Type*) [Magma G] (h : Equation286 G) : Equation280 G := λ x y => h x y x
@[equational_result]
theorem Equation287_implies_Equation281 (G : Type*) [Magma G] (h : Equation287 G) : Equation281 G := λ x y => h x y x
@[equational_result]
theorem Equation288_implies_Equation280 (G : Type*) [Magma G] (h : Equation288 G) : Equation280 G := λ x y => h x y x
@[equational_result]
theorem Equation290_implies_Equation270 (G : Type*) [Magma G] (h : Equation290 G) : Equation270 G := λ x y => h x y x
@[equational_result]
theorem Equation291_implies_Equation271 (G : Type*) [Magma G] (h : Equation291 G) : Equation271 G := λ x y => h x y x
@[equational_result]
theorem Equation292_implies_Equation270 (G : Type*) [Magma G] (h : Equation292 G) : Equation270 G := λ x y => h x y x
@[equational_result]
theorem Equation294_implies_Equation273 (G : Type*) [Magma G] (h : Equation294 G) : Equation273 G := λ x y => h x y x
@[equational_result]
theorem Equation295_implies_Equation274 (G : Type*) [Magma G] (h : Equation295 G) : Equation274 G := λ x y => h x y x
@[equational_result]
theorem Equation296_implies_Equation273 (G : Type*) [Magma G] (h : Equation296 G) : Equation273 G := λ x y => h x y x
@[equational_result]
theorem Equation298_implies_Equation270 (G : Type*) [Magma G] (h : Equation298 G) : Equation270 G := λ x y => h x y x
@[equational_result]
theorem Equation299_implies_Equation271 (G : Type*) [Magma G] (h : Equation299 G) : Equation271 G := λ x y => h x y x
@[equational_result]
theorem Equation300_implies_Equation270 (G : Type*) [Magma G] (h : Equation300 G) : Equation270 G := λ x y => h x y x
@[equational_result]
theorem Equation311_implies_Equation309 (G : Type*) [Magma G] (h : Equation311 G) : Equation309 G := λ x y => h x y x
@[equational_result]
theorem Equation314_implies_Equation312 (G : Type*) [Magma G] (h : Equation314 G) : Equation312 G := λ x y => h x y x
@[equational_result]
theorem Equation317_implies_Equation315 (G : Type*) [Magma G] (h : Equation317 G) : Equation315 G := λ x y => h x y x
@[equational_result]
theorem Equation318_implies_Equation312 (G : Type*) [Magma G] (h : Equation318 G) : Equation312 G := λ x y => h x y x
@[equational_result]
theorem Equation319_implies_Equation313 (G : Type*) [Magma G] (h : Equation319 G) : Equation313 G := λ x y => h x y x
@[equational_result]
theorem Equation320_implies_Equation312 (G : Type*) [Magma G] (h : Equation320 G) : Equation312 G := λ x y => h x y x
@[equational_result]
theorem Equation324_implies_Equation322 (G : Type*) [Magma G] (h : Equation324 G) : Equation322 G := λ x y => h x y x
@[equational_result]
theorem Equation327_implies_Equation325 (G : Type*) [Magma G] (h : Equation327 G) : Equation325 G := λ x y => h x y x
@[equational_result]
theorem Equation328_implies_Equation322 (G : Type*) [Magma G] (h : Equation328 G) : Equation322 G := λ x y => h x y x
@[equational_result]
theorem Equation329_implies_Equation323 (G : Type*) [Magma G] (h : Equation329 G) : Equation323 G := λ x y => h x y x
@[equational_result]
theorem Equation330_implies_Equation322 (G : Type*) [Magma G] (h : Equation330 G) : Equation322 G := λ x y => h x y x
@[equational_result]
theorem Equation334_implies_Equation332 (G : Type*) [Magma G] (h : Equation334 G) : Equation332 G := λ x y => h x y x
@[equational_result]
theorem Equation337_implies_Equation335 (G : Type*) [Magma G] (h : Equation337 G) : Equation335 G := λ x y => h x y x
@[equational_result]
theorem Equation338_implies_Equation332 (G : Type*) [Magma G] (h : Equation338 G) : Equation332 G := λ x y => h x y x
@[equational_result]
theorem Equation339_implies_Equation333 (G : Type*) [Magma G] (h : Equation339 G) : Equation333 G := λ x y => h x y x
@[equational_result]
theorem Equation340_implies_Equation332 (G : Type*) [Magma G] (h : Equation340 G) : Equation332 G := λ x y => h x y x
@[equational_result]
theorem Equation342_implies_Equation322 (G : Type*) [Magma G] (h : Equation342 G) : Equation322 G := λ x y => h x y x
@[equational_result]
theorem Equation343_implies_Equation323 (G : Type*) [Magma G] (h : Equation343 G) : Equation323 G := λ x y => h x y x
@[equational_result]
theorem Equation344_implies_Equation322 (G : Type*) [Magma G] (h : Equation344 G) : Equation322 G := λ x y => h x y x
@[equational_result]
theorem Equation346_implies_Equation325 (G : Type*) [Magma G] (h : Equation346 G) : Equation325 G := λ x y => h x y x
@[equational_result]
theorem Equation347_implies_Equation326 (G : Type*) [Magma G] (h : Equation347 G) : Equation326 G := λ x y => h x y x
@[equational_result]
theorem Equation348_implies_Equation325 (G : Type*) [Magma G] (h : Equation348 G) : Equation325 G := λ x y => h x y x
@[equational_result]
theorem Equation350_implies_Equation322 (G : Type*) [Magma G] (h : Equation350 G) : Equation322 G := λ x y => h x y x
@[equational_result]
theorem Equation351_implies_Equation323 (G : Type*) [Magma G] (h : Equation351 G) : Equation323 G := λ x y => h x y x
@[equational_result]
theorem Equation352_implies_Equation322 (G : Type*) [Magma G] (h : Equation352 G) : Equation322 G := λ x y => h x y x
@[equational_result]
theorem Equation363_implies_Equation361 (G : Type*) [Magma G] (h : Equation363 G) : Equation361 G := λ x y => h x y x
@[equational_result]
theorem Equation366_implies_Equation364 (G : Type*) [Magma G] (h : Equation366 G) : Equation364 G := λ x y => h x y x
@[equational_result]
theorem Equation369_implies_Equation367 (G : Type*) [Magma G] (h : Equation369 G) : Equation367 G := λ x y => h x y x
@[equational_result]
theorem Equation370_implies_Equation364 (G : Type*) [Magma G] (h : Equation370 G) : Equation364 G := λ x y => h x y x
@[equational_result]
theorem Equation371_implies_Equation365 (G : Type*) [Magma G] (h : Equation371 G) : Equation365 G := λ x y => h x y x
@[equational_result]
theorem Equation372_implies_Equation364 (G : Type*) [Magma G] (h : Equation372 G) : Equation364 G := λ x y => h x y x
@[equational_result]
theorem Equation376_implies_Equation374 (G : Type*) [Magma G] (h : Equation376 G) : Equation374 G := λ x y => h x y x
@[equational_result]
theorem Equation379_implies_Equation377 (G : Type*) [Magma G] (h : Equation379 G) : Equation377 G := λ x y => h x y x
@[equational_result]
theorem Equation380_implies_Equation374 (G : Type*) [Magma G] (h : Equation380 G) : Equation374 G := λ x y => h x y x
@[equational_result]
theorem Equation381_implies_Equation375 (G : Type*) [Magma G] (h : Equation381 G) : Equation375 G := λ x y => h x y x
@[equational_result]
theorem Equation382_implies_Equation374 (G : Type*) [Magma G] (h : Equation382 G) : Equation374 G := λ x y => h x y x
@[equational_result]
theorem Equation386_implies_Equation384 (G : Type*) [Magma G] (h : Equation386 G) : Equation384 G := λ x y => h x y x
@[equational_result]
theorem Equation389_implies_Equation387 (G : Type*) [Magma G] (h : Equation389 G) : Equation387 G := λ x y => h x y x
@[equational_result]
theorem Equation390_implies_Equation384 (G : Type*) [Magma G] (h : Equation390 G) : Equation384 G := λ x y => h x y x
@[equational_result]
theorem Equation391_implies_Equation385 (G : Type*) [Magma G] (h : Equation391 G) : Equation385 G := λ x y => h x y x
@[equational_result]
theorem Equation392_implies_Equation384 (G : Type*) [Magma G] (h : Equation392 G) : Equation384 G := λ x y => h x y x
@[equational_result]
theorem Equation394_implies_Equation374 (G : Type*) [Magma G] (h : Equation394 G) : Equation374 G := λ x y => h x y x
@[equational_result]
theorem Equation395_implies_Equation375 (G : Type*) [Magma G] (h : Equation395 G) : Equation375 G := λ x y => h x y x
@[equational_result]
theorem Equation396_implies_Equation374 (G : Type*) [Magma G] (h : Equation396 G) : Equation374 G := λ x y => h x y x
@[equational_result]
theorem Equation398_implies_Equation377 (G : Type*) [Magma G] (h : Equation398 G) : Equation377 G := λ x y => h x y x
@[equational_result]
theorem Equation399_implies_Equation378 (G : Type*) [Magma G] (h : Equation399 G) : Equation378 G := λ x y => h x y x
@[equational_result]
theorem Equation400_implies_Equation377 (G : Type*) [Magma G] (h : Equation400 G) : Equation377 G := λ x y => h x y x
@[equational_result]
theorem Equation402_implies_Equation374 (G : Type*) [Magma G] (h : Equation402 G) : Equation374 G := λ x y => h x y x
@[equational_result]
theorem Equation403_implies_Equation375 (G : Type*) [Magma G] (h : Equation403 G) : Equation375 G := λ x y => h x y x
@[equational_result]
theorem Equation404_implies_Equation374 (G : Type*) [Magma G] (h : Equation404 G) : Equation374 G := λ x y => h x y x
@[equational_result]
theorem Equation415_implies_Equation413 (G : Type*) [Magma G] (h : Equation415 G) : Equation413 G := λ x y => h x y x
@[equational_result]
theorem Equation418_implies_Equation416 (G : Type*) [Magma G] (h : Equation418 G) : Equation416 G := λ x y => h x y x
@[equational_result]
theorem Equation421_implies_Equation419 (G : Type*) [Magma G] (h : Equation421 G) : Equation419 G := λ x y => h x y x
@[equational_result]
theorem Equation422_implies_Equation416 (G : Type*) [Magma G] (h : Equation422 G) : Equation416 G := λ x y => h x y x
@[equational_result]
theorem Equation423_implies_Equation417 (G : Type*) [Magma G] (h : Equation423 G) : Equation417 G := λ x y => h x y x
@[equational_result]
theorem Equation424_implies_Equation416 (G : Type*) [Magma G] (h : Equation424 G) : Equation416 G := λ x y => h x y x
@[equational_result]
theorem Equation428_implies_Equation426 (G : Type*) [Magma G] (h : Equation428 G) : Equation426 G := λ x y => h x y x
@[equational_result]
theorem Equation431_implies_Equation429 (G : Type*) [Magma G] (h : Equation431 G) : Equation429 G := λ x y => h x y x
@[equational_result]
theorem Equation432_implies_Equation426 (G : Type*) [Magma G] (h : Equation432 G) : Equation426 G := λ x y => h x y x
@[equational_result]
theorem Equation433_implies_Equation427 (G : Type*) [Magma G] (h : Equation433 G) : Equation427 G := λ x y => h x y x
@[equational_result]
theorem Equation434_implies_Equation426 (G : Type*) [Magma G] (h : Equation434 G) : Equation426 G := λ x y => h x y x
@[equational_result]
theorem Equation438_implies_Equation436 (G : Type*) [Magma G] (h : Equation438 G) : Equation436 G := λ x y => h x y x
@[equational_result]
theorem Equation441_implies_Equation439 (G : Type*) [Magma G] (h : Equation441 G) : Equation439 G := λ x y => h x y x
@[equational_result]
theorem Equation442_implies_Equation436 (G : Type*) [Magma G] (h : Equation442 G) : Equation436 G := λ x y => h x y x
@[equational_result]
theorem Equation443_implies_Equation437 (G : Type*) [Magma G] (h : Equation443 G) : Equation437 G := λ x y => h x y x
@[equational_result]
theorem Equation444_implies_Equation436 (G : Type*) [Magma G] (h : Equation444 G) : Equation436 G := λ x y => h x y x
@[equational_result]
theorem Equation446_implies_Equation426 (G : Type*) [Magma G] (h : Equation446 G) : Equation426 G := λ x y => h x y x
@[equational_result]
theorem Equation447_implies_Equation427 (G : Type*) [Magma G] (h : Equation447 G) : Equation427 G := λ x y => h x y x
@[equational_result]
theorem Equation448_implies_Equation426 (G : Type*) [Magma G] (h : Equation448 G) : Equation426 G := λ x y => h x y x
@[equational_result]
theorem Equation450_implies_Equation429 (G : Type*) [Magma G] (h : Equation450 G) : Equation429 G := λ x y => h x y x
@[equational_result]
theorem Equation451_implies_Equation430 (G : Type*) [Magma G] (h : Equation451 G) : Equation430 G := λ x y => h x y x
@[equational_result]
theorem Equation452_implies_Equation429 (G : Type*) [Magma G] (h : Equation452 G) : Equation429 G := λ x y => h x y x
@[equational_result]
theorem Equation454_implies_Equation426 (G : Type*) [Magma G] (h : Equation454 G) : Equation426 G := λ x y => h x y x
@[equational_result]
theorem Equation455_implies_Equation427 (G : Type*) [Magma G] (h : Equation455 G) : Equation427 G := λ x y => h x y x
@[equational_result]
theorem Equation456_implies_Equation426 (G : Type*) [Magma G] (h : Equation456 G) : Equation426 G := λ x y => h x y x
@[equational_result]
theorem Equation465_implies_Equation463 (G : Type*) [Magma G] (h : Equation465 G) : Equation463 G := λ x y => h x y x
@[equational_result]
theorem Equation468_implies_Equation466 (G : Type*) [Magma G] (h : Equation468 G) : Equation466 G := λ x y => h x y x
@[equational_result]
theorem Equation469_implies_Equation463 (G : Type*) [Magma G] (h : Equation469 G) : Equation463 G := λ x y => h x y x
@[equational_result]
theorem Equation470_implies_Equation464 (G : Type*) [Magma G] (h : Equation470 G) : Equation464 G := λ x y => h x y x
@[equational_result]
theorem Equation471_implies_Equation463 (G : Type*) [Magma G] (h : Equation471 G) : Equation463 G := λ x y => h x y x
@[equational_result]
theorem Equation475_implies_Equation473 (G : Type*) [Magma G] (h : Equation475 G) : Equation473 G := λ x y => h x y x
@[equational_result]
theorem Equation478_implies_Equation476 (G : Type*) [Magma G] (h : Equation478 G) : Equation476 G := λ x y => h x y x
@[equational_result]
theorem Equation479_implies_Equation473 (G : Type*) [Magma G] (h : Equation479 G) : Equation473 G := λ x y => h x y x
@[equational_result]
theorem Equation480_implies_Equation474 (G : Type*) [Magma G] (h : Equation480 G) : Equation474 G := λ x y => h x y x
@[equational_result]
theorem Equation481_implies_Equation473 (G : Type*) [Magma G] (h : Equation481 G) : Equation473 G := λ x y => h x y x
@[equational_result]
theorem Equation483_implies_Equation463 (G : Type*) [Magma G] (h : Equation483 G) : Equation463 G := λ x y => h x y x
@[equational_result]
theorem Equation484_implies_Equation464 (G : Type*) [Magma G] (h : Equation484 G) : Equation464 G := λ x y => h x y x
@[equational_result]
theorem Equation485_implies_Equation463 (G : Type*) [Magma G] (h : Equation485 G) : Equation463 G := λ x y => h x y x
@[equational_result]
theorem Equation487_implies_Equation466 (G : Type*) [Magma G] (h : Equation487 G) : Equation466 G := λ x y => h x y x
@[equational_result]
theorem Equation488_implies_Equation467 (G : Type*) [Magma G] (h : Equation488 G) : Equation467 G := λ x y => h x y x
@[equational_result]
theorem Equation489_implies_Equation466 (G : Type*) [Magma G] (h : Equation489 G) : Equation466 G := λ x y => h x y x
@[equational_result]
theorem Equation491_implies_Equation463 (G : Type*) [Magma G] (h : Equation491 G) : Equation463 G := λ x y => h x y x
@[equational_result]
theorem Equation492_implies_Equation464 (G : Type*) [Magma G] (h : Equation492 G) : Equation464 G := λ x y => h x y x
@[equational_result]
theorem Equation493_implies_Equation463 (G : Type*) [Magma G] (h : Equation493 G) : Equation463 G := λ x y => h x y x
@[equational_result]
theorem Equation502_implies_Equation500 (G : Type*) [Magma G] (h : Equation502 G) : Equation500 G := λ x y => h x y x
@[equational_result]
theorem Equation505_implies_Equation503 (G : Type*) [Magma G] (h : Equation505 G) : Equation503 G := λ x y => h x y x
@[equational_result]
theorem Equation506_implies_Equation500 (G : Type*) [Magma G] (h : Equation506 G) : Equation500 G := λ x y => h x y x
@[equational_result]
theorem Equation507_implies_Equation501 (G : Type*) [Magma G] (h : Equation507 G) : Equation501 G := λ x y => h x y x
@[equational_result]
theorem Equation508_implies_Equation500 (G : Type*) [Magma G] (h : Equation508 G) : Equation500 G := λ x y => h x y x
@[equational_result]
theorem Equation512_implies_Equation510 (G : Type*) [Magma G] (h : Equation512 G) : Equation510 G := λ x y => h x y x
@[equational_result]
theorem Equation515_implies_Equation513 (G : Type*) [Magma G] (h : Equation515 G) : Equation513 G := λ x y => h x y x
@[equational_result]
theorem Equation516_implies_Equation510 (G : Type*) [Magma G] (h : Equation516 G) : Equation510 G := λ x y => h x y x
@[equational_result]
theorem Equation517_implies_Equation511 (G : Type*) [Magma G] (h : Equation517 G) : Equation511 G := λ x y => h x y x
@[equational_result]
theorem Equation518_implies_Equation510 (G : Type*) [Magma G] (h : Equation518 G) : Equation510 G := λ x y => h x y x
@[equational_result]
theorem Equation520_implies_Equation500 (G : Type*) [Magma G] (h : Equation520 G) : Equation500 G := λ x y => h x y x
@[equational_result]
theorem Equation521_implies_Equation501 (G : Type*) [Magma G] (h : Equation521 G) : Equation501 G := λ x y => h x y x
@[equational_result]
theorem Equation522_implies_Equation500 (G : Type*) [Magma G] (h : Equation522 G) : Equation500 G := λ x y => h x y x
@[equational_result]
theorem Equation524_implies_Equation503 (G : Type*) [Magma G] (h : Equation524 G) : Equation503 G := λ x y => h x y x
@[equational_result]
theorem Equation525_implies_Equation504 (G : Type*) [Magma G] (h : Equation525 G) : Equation504 G := λ x y => h x y x
@[equational_result]
theorem Equation526_implies_Equation503 (G : Type*) [Magma G] (h : Equation526 G) : Equation503 G := λ x y => h x y x
@[equational_result]
theorem Equation528_implies_Equation500 (G : Type*) [Magma G] (h : Equation528 G) : Equation500 G := λ x y => h x y x
@[equational_result]
theorem Equation529_implies_Equation501 (G : Type*) [Magma G] (h : Equation529 G) : Equation501 G := λ x y => h x y x
@[equational_result]
theorem Equation530_implies_Equation500 (G : Type*) [Magma G] (h : Equation530 G) : Equation500 G := λ x y => h x y x
@[equational_result]
theorem Equation537_implies_Equation463 (G : Type*) [Magma G] (h : Equation537 G) : Equation463 G := λ x y => h x y x
@[equational_result]
theorem Equation538_implies_Equation464 (G : Type*) [Magma G] (h : Equation538 G) : Equation464 G := λ x y => h x y x
@[equational_result]
theorem Equation539_implies_Equation463 (G : Type*) [Magma G] (h : Equation539 G) : Equation463 G := λ x y => h x y x
@[equational_result]
theorem Equation541_implies_Equation466 (G : Type*) [Magma G] (h : Equation541 G) : Equation466 G := λ x y => h x y x
@[equational_result]
theorem Equation542_implies_Equation467 (G : Type*) [Magma G] (h : Equation542 G) : Equation467 G := λ x y => h x y x
@[equational_result]
theorem Equation543_implies_Equation466 (G : Type*) [Magma G] (h : Equation543 G) : Equation466 G := λ x y => h x y x
@[equational_result]
theorem Equation545_implies_Equation463 (G : Type*) [Magma G] (h : Equation545 G) : Equation463 G := λ x y => h x y x
@[equational_result]
theorem Equation546_implies_Equation464 (G : Type*) [Magma G] (h : Equation546 G) : Equation464 G := λ x y => h x y x
@[equational_result]
theorem Equation547_implies_Equation463 (G : Type*) [Magma G] (h : Equation547 G) : Equation463 G := λ x y => h x y x
@[equational_result]
theorem Equation554_implies_Equation473 (G : Type*) [Magma G] (h : Equation554 G) : Equation473 G := λ x y => h x y x
@[equational_result]
theorem Equation555_implies_Equation474 (G : Type*) [Magma G] (h : Equation555 G) : Equation474 G := λ x y => h x y x
@[equational_result]
theorem Equation556_implies_Equation473 (G : Type*) [Magma G] (h : Equation556 G) : Equation473 G := λ x y => h x y x
@[equational_result]
theorem Equation558_implies_Equation476 (G : Type*) [Magma G] (h : Equation558 G) : Equation476 G := λ x y => h x y x
@[equational_result]
theorem Equation559_implies_Equation477 (G : Type*) [Magma G] (h : Equation559 G) : Equation477 G := λ x y => h x y x
@[equational_result]
theorem Equation560_implies_Equation476 (G : Type*) [Magma G] (h : Equation560 G) : Equation476 G := λ x y => h x y x
@[equational_result]
theorem Equation562_implies_Equation473 (G : Type*) [Magma G] (h : Equation562 G) : Equation473 G := λ x y => h x y x
@[equational_result]
theorem Equation563_implies_Equation474 (G : Type*) [Magma G] (h : Equation563 G) : Equation474 G := λ x y => h x y x
@[equational_result]
theorem Equation564_implies_Equation473 (G : Type*) [Magma G] (h : Equation564 G) : Equation473 G := λ x y => h x y x
@[equational_result]
theorem Equation571_implies_Equation463 (G : Type*) [Magma G] (h : Equation571 G) : Equation463 G := λ x y => h x y x
@[equational_result]
theorem Equation572_implies_Equation464 (G : Type*) [Magma G] (h : Equation572 G) : Equation464 G := λ x y => h x y x
@[equational_result]
theorem Equation573_implies_Equation463 (G : Type*) [Magma G] (h : Equation573 G) : Equation463 G := λ x y => h x y x
@[equational_result]
theorem Equation575_implies_Equation466 (G : Type*) [Magma G] (h : Equation575 G) : Equation466 G := λ x y => h x y x
@[equational_result]
theorem Equation576_implies_Equation467 (G : Type*) [Magma G] (h : Equation576 G) : Equation467 G := λ x y => h x y x
@[equational_result]
theorem Equation577_implies_Equation466 (G : Type*) [Magma G] (h : Equation577 G) : Equation466 G := λ x y => h x y x
@[equational_result]
theorem Equation579_implies_Equation463 (G : Type*) [Magma G] (h : Equation579 G) : Equation463 G := λ x y => h x y x
@[equational_result]
theorem Equation580_implies_Equation464 (G : Type*) [Magma G] (h : Equation580 G) : Equation464 G := λ x y => h x y x
@[equational_result]
theorem Equation581_implies_Equation463 (G : Type*) [Magma G] (h : Equation581 G) : Equation463 G := λ x y => h x y x
@[equational_result]
theorem Equation618_implies_Equation616 (G : Type*) [Magma G] (h : Equation618 G) : Equation616 G := λ x y => h x y x
@[equational_result]
theorem Equation621_implies_Equation619 (G : Type*) [Magma G] (h : Equation621 G) : Equation619 G := λ x y => h x y x
@[equational_result]
theorem Equation624_implies_Equation622 (G : Type*) [Magma G] (h : Equation624 G) : Equation622 G := λ x y => h x y x
@[equational_result]
theorem Equation625_implies_Equation619 (G : Type*) [Magma G] (h : Equation625 G) : Equation619 G := λ x y => h x y x
@[equational_result]
theorem Equation626_implies_Equation620 (G : Type*) [Magma G] (h : Equation626 G) : Equation620 G := λ x y => h x y x
@[equational_result]
theorem Equation627_implies_Equation619 (G : Type*) [Magma G] (h : Equation627 G) : Equation619 G := λ x y => h x y x
@[equational_result]
theorem Equation631_implies_Equation629 (G : Type*) [Magma G] (h : Equation631 G) : Equation629 G := λ x y => h x y x
@[equational_result]
theorem Equation634_implies_Equation632 (G : Type*) [Magma G] (h : Equation634 G) : Equation632 G := λ x y => h x y x
@[equational_result]
theorem Equation635_implies_Equation629 (G : Type*) [Magma G] (h : Equation635 G) : Equation629 G := λ x y => h x y x
@[equational_result]
theorem Equation636_implies_Equation630 (G : Type*) [Magma G] (h : Equation636 G) : Equation630 G := λ x y => h x y x
@[equational_result]
theorem Equation637_implies_Equation629 (G : Type*) [Magma G] (h : Equation637 G) : Equation629 G := λ x y => h x y x
@[equational_result]
theorem Equation641_implies_Equation639 (G : Type*) [Magma G] (h : Equation641 G) : Equation639 G := λ x y => h x y x
@[equational_result]
theorem Equation644_implies_Equation642 (G : Type*) [Magma G] (h : Equation644 G) : Equation642 G := λ x y => h x y x
@[equational_result]
theorem Equation645_implies_Equation639 (G : Type*) [Magma G] (h : Equation645 G) : Equation639 G := λ x y => h x y x
@[equational_result]
theorem Equation646_implies_Equation640 (G : Type*) [Magma G] (h : Equation646 G) : Equation640 G := λ x y => h x y x
@[equational_result]
theorem Equation647_implies_Equation639 (G : Type*) [Magma G] (h : Equation647 G) : Equation639 G := λ x y => h x y x
@[equational_result]
theorem Equation649_implies_Equation629 (G : Type*) [Magma G] (h : Equation649 G) : Equation629 G := λ x y => h x y x
@[equational_result]
theorem Equation650_implies_Equation630 (G : Type*) [Magma G] (h : Equation650 G) : Equation630 G := λ x y => h x y x
@[equational_result]
theorem Equation651_implies_Equation629 (G : Type*) [Magma G] (h : Equation651 G) : Equation629 G := λ x y => h x y x
@[equational_result]
theorem Equation653_implies_Equation632 (G : Type*) [Magma G] (h : Equation653 G) : Equation632 G := λ x y => h x y x
@[equational_result]
theorem Equation654_implies_Equation633 (G : Type*) [Magma G] (h : Equation654 G) : Equation633 G := λ x y => h x y x
@[equational_result]
theorem Equation655_implies_Equation632 (G : Type*) [Magma G] (h : Equation655 G) : Equation632 G := λ x y => h x y x
@[equational_result]
theorem Equation657_implies_Equation629 (G : Type*) [Magma G] (h : Equation657 G) : Equation629 G := λ x y => h x y x
@[equational_result]
theorem Equation658_implies_Equation630 (G : Type*) [Magma G] (h : Equation658 G) : Equation630 G := λ x y => h x y x
@[equational_result]
theorem Equation659_implies_Equation629 (G : Type*) [Magma G] (h : Equation659 G) : Equation629 G := λ x y => h x y x
@[equational_result]
theorem Equation668_implies_Equation666 (G : Type*) [Magma G] (h : Equation668 G) : Equation666 G := λ x y => h x y x
@[equational_result]
theorem Equation671_implies_Equation669 (G : Type*) [Magma G] (h : Equation671 G) : Equation669 G := λ x y => h x y x
@[equational_result]
theorem Equation672_implies_Equation666 (G : Type*) [Magma G] (h : Equation672 G) : Equation666 G := λ x y => h x y x
@[equational_result]
theorem Equation673_implies_Equation667 (G : Type*) [Magma G] (h : Equation673 G) : Equation667 G := λ x y => h x y x
@[equational_result]
theorem Equation674_implies_Equation666 (G : Type*) [Magma G] (h : Equation674 G) : Equation666 G := λ x y => h x y x
@[equational_result]
theorem Equation678_implies_Equation676 (G : Type*) [Magma G] (h : Equation678 G) : Equation676 G := λ x y => h x y x
@[equational_result]
theorem Equation681_implies_Equation679 (G : Type*) [Magma G] (h : Equation681 G) : Equation679 G := λ x y => h x y x
@[equational_result]
theorem Equation682_implies_Equation676 (G : Type*) [Magma G] (h : Equation682 G) : Equation676 G := λ x y => h x y x
@[equational_result]
theorem Equation683_implies_Equation677 (G : Type*) [Magma G] (h : Equation683 G) : Equation677 G := λ x y => h x y x
@[equational_result]
theorem Equation684_implies_Equation676 (G : Type*) [Magma G] (h : Equation684 G) : Equation676 G := λ x y => h x y x
@[equational_result]
theorem Equation686_implies_Equation666 (G : Type*) [Magma G] (h : Equation686 G) : Equation666 G := λ x y => h x y x
@[equational_result]
theorem Equation687_implies_Equation667 (G : Type*) [Magma G] (h : Equation687 G) : Equation667 G := λ x y => h x y x
@[equational_result]
theorem Equation688_implies_Equation666 (G : Type*) [Magma G] (h : Equation688 G) : Equation666 G := λ x y => h x y x
@[equational_result]
theorem Equation690_implies_Equation669 (G : Type*) [Magma G] (h : Equation690 G) : Equation669 G := λ x y => h x y x
@[equational_result]
theorem Equation691_implies_Equation670 (G : Type*) [Magma G] (h : Equation691 G) : Equation670 G := λ x y => h x y x
@[equational_result]
theorem Equation692_implies_Equation669 (G : Type*) [Magma G] (h : Equation692 G) : Equation669 G := λ x y => h x y x
@[equational_result]
theorem Equation694_implies_Equation666 (G : Type*) [Magma G] (h : Equation694 G) : Equation666 G := λ x y => h x y x
@[equational_result]
theorem Equation695_implies_Equation667 (G : Type*) [Magma G] (h : Equation695 G) : Equation667 G := λ x y => h x y x
@[equational_result]
theorem Equation696_implies_Equation666 (G : Type*) [Magma G] (h : Equation696 G) : Equation666 G := λ x y => h x y x
@[equational_result]
theorem Equation705_implies_Equation703 (G : Type*) [Magma G] (h : Equation705 G) : Equation703 G := λ x y => h x y x
@[equational_result]
theorem Equation708_implies_Equation706 (G : Type*) [Magma G] (h : Equation708 G) : Equation706 G := λ x y => h x y x
@[equational_result]
theorem Equation709_implies_Equation703 (G : Type*) [Magma G] (h : Equation709 G) : Equation703 G := λ x y => h x y x
@[equational_result]
theorem Equation710_implies_Equation704 (G : Type*) [Magma G] (h : Equation710 G) : Equation704 G := λ x y => h x y x
@[equational_result]
theorem Equation711_implies_Equation703 (G : Type*) [Magma G] (h : Equation711 G) : Equation703 G := λ x y => h x y x
@[equational_result]
theorem Equation715_implies_Equation713 (G : Type*) [Magma G] (h : Equation715 G) : Equation713 G := λ x y => h x y x
@[equational_result]
theorem Equation718_implies_Equation716 (G : Type*) [Magma G] (h : Equation718 G) : Equation716 G := λ x y => h x y x
@[equational_result]
theorem Equation719_implies_Equation713 (G : Type*) [Magma G] (h : Equation719 G) : Equation713 G := λ x y => h x y x
@[equational_result]
theorem Equation720_implies_Equation714 (G : Type*) [Magma G] (h : Equation720 G) : Equation714 G := λ x y => h x y x
@[equational_result]
theorem Equation721_implies_Equation713 (G : Type*) [Magma G] (h : Equation721 G) : Equation713 G := λ x y => h x y x
@[equational_result]
theorem Equation723_implies_Equation703 (G : Type*) [Magma G] (h : Equation723 G) : Equation703 G := λ x y => h x y x
@[equational_result]
theorem Equation724_implies_Equation704 (G : Type*) [Magma G] (h : Equation724 G) : Equation704 G := λ x y => h x y x
@[equational_result]
theorem Equation725_implies_Equation703 (G : Type*) [Magma G] (h : Equation725 G) : Equation703 G := λ x y => h x y x
@[equational_result]
theorem Equation727_implies_Equation706 (G : Type*) [Magma G] (h : Equation727 G) : Equation706 G := λ x y => h x y x
@[equational_result]
theorem Equation728_implies_Equation707 (G : Type*) [Magma G] (h : Equation728 G) : Equation707 G := λ x y => h x y x
@[equational_result]
theorem Equation729_implies_Equation706 (G : Type*) [Magma G] (h : Equation729 G) : Equation706 G := λ x y => h x y x
@[equational_result]
theorem Equation731_implies_Equation703 (G : Type*) [Magma G] (h : Equation731 G) : Equation703 G := λ x y => h x y x
@[equational_result]
theorem Equation732_implies_Equation704 (G : Type*) [Magma G] (h : Equation732 G) : Equation704 G := λ x y => h x y x
@[equational_result]
theorem Equation733_implies_Equation703 (G : Type*) [Magma G] (h : Equation733 G) : Equation703 G := λ x y => h x y x
@[equational_result]
theorem Equation740_implies_Equation666 (G : Type*) [Magma G] (h : Equation740 G) : Equation666 G := λ x y => h x y x
@[equational_result]
theorem Equation741_implies_Equation667 (G : Type*) [Magma G] (h : Equation741 G) : Equation667 G := λ x y => h x y x
@[equational_result]
theorem Equation742_implies_Equation666 (G : Type*) [Magma G] (h : Equation742 G) : Equation666 G := λ x y => h x y x
@[equational_result]
theorem Equation744_implies_Equation669 (G : Type*) [Magma G] (h : Equation744 G) : Equation669 G := λ x y => h x y x
@[equational_result]
theorem Equation745_implies_Equation670 (G : Type*) [Magma G] (h : Equation745 G) : Equation670 G := λ x y => h x y x
@[equational_result]
theorem Equation746_implies_Equation669 (G : Type*) [Magma G] (h : Equation746 G) : Equation669 G := λ x y => h x y x
@[equational_result]
theorem Equation748_implies_Equation666 (G : Type*) [Magma G] (h : Equation748 G) : Equation666 G := λ x y => h x y x
@[equational_result]
theorem Equation749_implies_Equation667 (G : Type*) [Magma G] (h : Equation749 G) : Equation667 G := λ x y => h x y x
@[equational_result]
theorem Equation750_implies_Equation666 (G : Type*) [Magma G] (h : Equation750 G) : Equation666 G := λ x y => h x y x
@[equational_result]
theorem Equation757_implies_Equation676 (G : Type*) [Magma G] (h : Equation757 G) : Equation676 G := λ x y => h x y x
@[equational_result]
theorem Equation758_implies_Equation677 (G : Type*) [Magma G] (h : Equation758 G) : Equation677 G := λ x y => h x y x
@[equational_result]
theorem Equation759_implies_Equation676 (G : Type*) [Magma G] (h : Equation759 G) : Equation676 G := λ x y => h x y x
@[equational_result]
theorem Equation761_implies_Equation679 (G : Type*) [Magma G] (h : Equation761 G) : Equation679 G := λ x y => h x y x
@[equational_result]
theorem Equation762_implies_Equation680 (G : Type*) [Magma G] (h : Equation762 G) : Equation680 G := λ x y => h x y x
@[equational_result]
theorem Equation763_implies_Equation679 (G : Type*) [Magma G] (h : Equation763 G) : Equation679 G := λ x y => h x y x
@[equational_result]
theorem Equation765_implies_Equation676 (G : Type*) [Magma G] (h : Equation765 G) : Equation676 G := λ x y => h x y x
@[equational_result]
theorem Equation766_implies_Equation677 (G : Type*) [Magma G] (h : Equation766 G) : Equation677 G := λ x y => h x y x
@[equational_result]
theorem Equation767_implies_Equation676 (G : Type*) [Magma G] (h : Equation767 G) : Equation676 G := λ x y => h x y x
@[equational_result]
theorem Equation774_implies_Equation666 (G : Type*) [Magma G] (h : Equation774 G) : Equation666 G := λ x y => h x y x
@[equational_result]
theorem Equation775_implies_Equation667 (G : Type*) [Magma G] (h : Equation775 G) : Equation667 G := λ x y => h x y x
@[equational_result]
theorem Equation776_implies_Equation666 (G : Type*) [Magma G] (h : Equation776 G) : Equation666 G := λ x y => h x y x
@[equational_result]
theorem Equation778_implies_Equation669 (G : Type*) [Magma G] (h : Equation778 G) : Equation669 G := λ x y => h x y x
@[equational_result]
theorem Equation779_implies_Equation670 (G : Type*) [Magma G] (h : Equation779 G) : Equation670 G := λ x y => h x y x
@[equational_result]
theorem Equation780_implies_Equation669 (G : Type*) [Magma G] (h : Equation780 G) : Equation669 G := λ x y => h x y x
@[equational_result]
theorem Equation782_implies_Equation666 (G : Type*) [Magma G] (h : Equation782 G) : Equation666 G := λ x y => h x y x
@[equational_result]
theorem Equation783_implies_Equation667 (G : Type*) [Magma G] (h : Equation783 G) : Equation667 G := λ x y => h x y x
@[equational_result]
theorem Equation784_implies_Equation666 (G : Type*) [Magma G] (h : Equation784 G) : Equation666 G := λ x y => h x y x
@[equational_result]
theorem Equation821_implies_Equation819 (G : Type*) [Magma G] (h : Equation821 G) : Equation819 G := λ x y => h x y x
@[equational_result]
theorem Equation824_implies_Equation822 (G : Type*) [Magma G] (h : Equation824 G) : Equation822 G := λ x y => h x y x
@[equational_result]
theorem Equation827_implies_Equation825 (G : Type*) [Magma G] (h : Equation827 G) : Equation825 G := λ x y => h x y x
@[equational_result]
theorem Equation828_implies_Equation822 (G : Type*) [Magma G] (h : Equation828 G) : Equation822 G := λ x y => h x y x
@[equational_result]
theorem Equation829_implies_Equation823 (G : Type*) [Magma G] (h : Equation829 G) : Equation823 G := λ x y => h x y x
@[equational_result]
theorem Equation830_implies_Equation822 (G : Type*) [Magma G] (h : Equation830 G) : Equation822 G := λ x y => h x y x
@[equational_result]
theorem Equation834_implies_Equation832 (G : Type*) [Magma G] (h : Equation834 G) : Equation832 G := λ x y => h x y x
@[equational_result]
theorem Equation837_implies_Equation835 (G : Type*) [Magma G] (h : Equation837 G) : Equation835 G := λ x y => h x y x
@[equational_result]
theorem Equation838_implies_Equation832 (G : Type*) [Magma G] (h : Equation838 G) : Equation832 G := λ x y => h x y x
@[equational_result]
theorem Equation839_implies_Equation833 (G : Type*) [Magma G] (h : Equation839 G) : Equation833 G := λ x y => h x y x
@[equational_result]
theorem Equation840_implies_Equation832 (G : Type*) [Magma G] (h : Equation840 G) : Equation832 G := λ x y => h x y x
@[equational_result]
theorem Equation844_implies_Equation842 (G : Type*) [Magma G] (h : Equation844 G) : Equation842 G := λ x y => h x y x
@[equational_result]
theorem Equation847_implies_Equation845 (G : Type*) [Magma G] (h : Equation847 G) : Equation845 G := λ x y => h x y x
@[equational_result]
theorem Equation848_implies_Equation842 (G : Type*) [Magma G] (h : Equation848 G) : Equation842 G := λ x y => h x y x
@[equational_result]
theorem Equation849_implies_Equation843 (G : Type*) [Magma G] (h : Equation849 G) : Equation843 G := λ x y => h x y x
@[equational_result]
theorem Equation850_implies_Equation842 (G : Type*) [Magma G] (h : Equation850 G) : Equation842 G := λ x y => h x y x
@[equational_result]
theorem Equation852_implies_Equation832 (G : Type*) [Magma G] (h : Equation852 G) : Equation832 G := λ x y => h x y x
@[equational_result]
theorem Equation853_implies_Equation833 (G : Type*) [Magma G] (h : Equation853 G) : Equation833 G := λ x y => h x y x
@[equational_result]
theorem Equation854_implies_Equation832 (G : Type*) [Magma G] (h : Equation854 G) : Equation832 G := λ x y => h x y x
@[equational_result]
theorem Equation856_implies_Equation835 (G : Type*) [Magma G] (h : Equation856 G) : Equation835 G := λ x y => h x y x
@[equational_result]
theorem Equation857_implies_Equation836 (G : Type*) [Magma G] (h : Equation857 G) : Equation836 G := λ x y => h x y x
@[equational_result]
theorem Equation858_implies_Equation835 (G : Type*) [Magma G] (h : Equation858 G) : Equation835 G := λ x y => h x y x
@[equational_result]
theorem Equation860_implies_Equation832 (G : Type*) [Magma G] (h : Equation860 G) : Equation832 G := λ x y => h x y x
@[equational_result]
theorem Equation861_implies_Equation833 (G : Type*) [Magma G] (h : Equation861 G) : Equation833 G := λ x y => h x y x
@[equational_result]
theorem Equation862_implies_Equation832 (G : Type*) [Magma G] (h : Equation862 G) : Equation832 G := λ x y => h x y x
@[equational_result]
theorem Equation871_implies_Equation869 (G : Type*) [Magma G] (h : Equation871 G) : Equation869 G := λ x y => h x y x
@[equational_result]
theorem Equation874_implies_Equation872 (G : Type*) [Magma G] (h : Equation874 G) : Equation872 G := λ x y => h x y x
@[equational_result]
theorem Equation875_implies_Equation869 (G : Type*) [Magma G] (h : Equation875 G) : Equation869 G := λ x y => h x y x
@[equational_result]
theorem Equation876_implies_Equation870 (G : Type*) [Magma G] (h : Equation876 G) : Equation870 G := λ x y => h x y x
@[equational_result]
theorem Equation877_implies_Equation869 (G : Type*) [Magma G] (h : Equation877 G) : Equation869 G := λ x y => h x y x
@[equational_result]
theorem Equation881_implies_Equation879 (G : Type*) [Magma G] (h : Equation881 G) : Equation879 G := λ x y => h x y x
@[equational_result]
theorem Equation884_implies_Equation882 (G : Type*) [Magma G] (h : Equation884 G) : Equation882 G := λ x y => h x y x
@[equational_result]
theorem Equation885_implies_Equation879 (G : Type*) [Magma G] (h : Equation885 G) : Equation879 G := λ x y => h x y x
@[equational_result]
theorem Equation886_implies_Equation880 (G : Type*) [Magma G] (h : Equation886 G) : Equation880 G := λ x y => h x y x
@[equational_result]
theorem Equation887_implies_Equation879 (G : Type*) [Magma G] (h : Equation887 G) : Equation879 G := λ x y => h x y x
@[equational_result]
theorem Equation889_implies_Equation869 (G : Type*) [Magma G] (h : Equation889 G) : Equation869 G := λ x y => h x y x
@[equational_result]
theorem Equation890_implies_Equation870 (G : Type*) [Magma G] (h : Equation890 G) : Equation870 G := λ x y => h x y x
@[equational_result]
theorem Equation891_implies_Equation869 (G : Type*) [Magma G] (h : Equation891 G) : Equation869 G := λ x y => h x y x
@[equational_result]
theorem Equation893_implies_Equation872 (G : Type*) [Magma G] (h : Equation893 G) : Equation872 G := λ x y => h x y x
@[equational_result]
theorem Equation894_implies_Equation873 (G : Type*) [Magma G] (h : Equation894 G) : Equation873 G := λ x y => h x y x
@[equational_result]
theorem Equation895_implies_Equation872 (G : Type*) [Magma G] (h : Equation895 G) : Equation872 G := λ x y => h x y x
@[equational_result]
theorem Equation897_implies_Equation869 (G : Type*) [Magma G] (h : Equation897 G) : Equation869 G := λ x y => h x y x
@[equational_result]
theorem Equation898_implies_Equation870 (G : Type*) [Magma G] (h : Equation898 G) : Equation870 G := λ x y => h x y x
@[equational_result]
theorem Equation899_implies_Equation869 (G : Type*) [Magma G] (h : Equation899 G) : Equation869 G := λ x y => h x y x
@[equational_result]
theorem Equation908_implies_Equation906 (G : Type*) [Magma G] (h : Equation908 G) : Equation906 G := λ x y => h x y x
@[equational_result]
theorem Equation911_implies_Equation909 (G : Type*) [Magma G] (h : Equation911 G) : Equation909 G := λ x y => h x y x
@[equational_result]
theorem Equation912_implies_Equation906 (G : Type*) [Magma G] (h : Equation912 G) : Equation906 G := λ x y => h x y x
@[equational_result]
theorem Equation913_implies_Equation907 (G : Type*) [Magma G] (h : Equation913 G) : Equation907 G := λ x y => h x y x
@[equational_result]
theorem Equation914_implies_Equation906 (G : Type*) [Magma G] (h : Equation914 G) : Equation906 G := λ x y => h x y x
@[equational_result]
theorem Equation918_implies_Equation916 (G : Type*) [Magma G] (h : Equation918 G) : Equation916 G := λ x y => h x y x
@[equational_result]
theorem Equation921_implies_Equation919 (G : Type*) [Magma G] (h : Equation921 G) : Equation919 G := λ x y => h x y x
@[equational_result]
theorem Equation922_implies_Equation916 (G : Type*) [Magma G] (h : Equation922 G) : Equation916 G := λ x y => h x y x
@[equational_result]
theorem Equation923_implies_Equation917 (G : Type*) [Magma G] (h : Equation923 G) : Equation917 G := λ x y => h x y x
@[equational_result]
theorem Equation924_implies_Equation916 (G : Type*) [Magma G] (h : Equation924 G) : Equation916 G := λ x y => h x y x
@[equational_result]
theorem Equation926_implies_Equation906 (G : Type*) [Magma G] (h : Equation926 G) : Equation906 G := λ x y => h x y x
@[equational_result]
theorem Equation927_implies_Equation907 (G : Type*) [Magma G] (h : Equation927 G) : Equation907 G := λ x y => h x y x
@[equational_result]
theorem Equation928_implies_Equation906 (G : Type*) [Magma G] (h : Equation928 G) : Equation906 G := λ x y => h x y x
@[equational_result]
theorem Equation930_implies_Equation909 (G : Type*) [Magma G] (h : Equation930 G) : Equation909 G := λ x y => h x y x
@[equational_result]
theorem Equation931_implies_Equation910 (G : Type*) [Magma G] (h : Equation931 G) : Equation910 G := λ x y => h x y x
@[equational_result]
theorem Equation932_implies_Equation909 (G : Type*) [Magma G] (h : Equation932 G) : Equation909 G := λ x y => h x y x
@[equational_result]
theorem Equation934_implies_Equation906 (G : Type*) [Magma G] (h : Equation934 G) : Equation906 G := λ x y => h x y x
@[equational_result]
theorem Equation935_implies_Equation907 (G : Type*) [Magma G] (h : Equation935 G) : Equation907 G := λ x y => h x y x
@[equational_result]
theorem Equation936_implies_Equation906 (G : Type*) [Magma G] (h : Equation936 G) : Equation906 G := λ x y => h x y x
@[equational_result]
theorem Equation943_implies_Equation869 (G : Type*) [Magma G] (h : Equation943 G) : Equation869 G := λ x y => h x y x
@[equational_result]
theorem Equation944_implies_Equation870 (G : Type*) [Magma G] (h : Equation944 G) : Equation870 G := λ x y => h x y x
@[equational_result]
theorem Equation945_implies_Equation869 (G : Type*) [Magma G] (h : Equation945 G) : Equation869 G := λ x y => h x y x
@[equational_result]
theorem Equation947_implies_Equation872 (G : Type*) [Magma G] (h : Equation947 G) : Equation872 G := λ x y => h x y x
@[equational_result]
theorem Equation948_implies_Equation873 (G : Type*) [Magma G] (h : Equation948 G) : Equation873 G := λ x y => h x y x
@[equational_result]
theorem Equation949_implies_Equation872 (G : Type*) [Magma G] (h : Equation949 G) : Equation872 G := λ x y => h x y x
@[equational_result]
theorem Equation951_implies_Equation869 (G : Type*) [Magma G] (h : Equation951 G) : Equation869 G := λ x y => h x y x
@[equational_result]
theorem Equation952_implies_Equation870 (G : Type*) [Magma G] (h : Equation952 G) : Equation870 G := λ x y => h x y x
@[equational_result]
theorem Equation953_implies_Equation869 (G : Type*) [Magma G] (h : Equation953 G) : Equation869 G := λ x y => h x y x
@[equational_result]
theorem Equation960_implies_Equation879 (G : Type*) [Magma G] (h : Equation960 G) : Equation879 G := λ x y => h x y x
@[equational_result]
theorem Equation961_implies_Equation880 (G : Type*) [Magma G] (h : Equation961 G) : Equation880 G := λ x y => h x y x
@[equational_result]
theorem Equation962_implies_Equation879 (G : Type*) [Magma G] (h : Equation962 G) : Equation879 G := λ x y => h x y x
@[equational_result]
theorem Equation964_implies_Equation882 (G : Type*) [Magma G] (h : Equation964 G) : Equation882 G := λ x y => h x y x
@[equational_result]
theorem Equation965_implies_Equation883 (G : Type*) [Magma G] (h : Equation965 G) : Equation883 G := λ x y => h x y x
@[equational_result]
theorem Equation966_implies_Equation882 (G : Type*) [Magma G] (h : Equation966 G) : Equation882 G := λ x y => h x y x
@[equational_result]
theorem Equation968_implies_Equation879 (G : Type*) [Magma G] (h : Equation968 G) : Equation879 G := λ x y => h x y x
@[equational_result]
theorem Equation969_implies_Equation880 (G : Type*) [Magma G] (h : Equation969 G) : Equation880 G := λ x y => h x y x
@[equational_result]
theorem Equation970_implies_Equation879 (G : Type*) [Magma G] (h : Equation970 G) : Equation879 G := λ x y => h x y x
@[equational_result]
theorem Equation977_implies_Equation869 (G : Type*) [Magma G] (h : Equation977 G) : Equation869 G := λ x y => h x y x
@[equational_result]
theorem Equation978_implies_Equation870 (G : Type*) [Magma G] (h : Equation978 G) : Equation870 G := λ x y => h x y x
@[equational_result]
theorem Equation979_implies_Equation869 (G : Type*) [Magma G] (h : Equation979 G) : Equation869 G := λ x y => h x y x
@[equational_result]
theorem Equation981_implies_Equation872 (G : Type*) [Magma G] (h : Equation981 G) : Equation872 G := λ x y => h x y x
@[equational_result]
theorem Equation982_implies_Equation873 (G : Type*) [Magma G] (h : Equation982 G) : Equation873 G := λ x y => h x y x
@[equational_result]
theorem Equation983_implies_Equation872 (G : Type*) [Magma G] (h : Equation983 G) : Equation872 G := λ x y => h x y x
@[equational_result]
theorem Equation985_implies_Equation869 (G : Type*) [Magma G] (h : Equation985 G) : Equation869 G := λ x y => h x y x
@[equational_result]
theorem Equation986_implies_Equation870 (G : Type*) [Magma G] (h : Equation986 G) : Equation870 G := λ x y => h x y x
@[equational_result]
theorem Equation987_implies_Equation869 (G : Type*) [Magma G] (h : Equation987 G) : Equation869 G := λ x y => h x y x
@[equational_result]
theorem Equation1024_implies_Equation1022 (G : Type*) [Magma G] (h : Equation1024 G) : Equation1022 G := λ x y => h x y x
@[equational_result]
theorem Equation1027_implies_Equation1025 (G : Type*) [Magma G] (h : Equation1027 G) : Equation1025 G := λ x y => h x y x
@[equational_result]
theorem Equation1030_implies_Equation1028 (G : Type*) [Magma G] (h : Equation1030 G) : Equation1028 G := λ x y => h x y x
@[equational_result]
theorem Equation1031_implies_Equation1025 (G : Type*) [Magma G] (h : Equation1031 G) : Equation1025 G := λ x y => h x y x
@[equational_result]
theorem Equation1032_implies_Equation1026 (G : Type*) [Magma G] (h : Equation1032 G) : Equation1026 G := λ x y => h x y x
@[equational_result]
theorem Equation1033_implies_Equation1025 (G : Type*) [Magma G] (h : Equation1033 G) : Equation1025 G := λ x y => h x y x
@[equational_result]
theorem Equation1037_implies_Equation1035 (G : Type*) [Magma G] (h : Equation1037 G) : Equation1035 G := λ x y => h x y x
@[equational_result]
theorem Equation1040_implies_Equation1038 (G : Type*) [Magma G] (h : Equation1040 G) : Equation1038 G := λ x y => h x y x
@[equational_result]
theorem Equation1041_implies_Equation1035 (G : Type*) [Magma G] (h : Equation1041 G) : Equation1035 G := λ x y => h x y x
@[equational_result]
theorem Equation1042_implies_Equation1036 (G : Type*) [Magma G] (h : Equation1042 G) : Equation1036 G := λ x y => h x y x
@[equational_result]
theorem Equation1043_implies_Equation1035 (G : Type*) [Magma G] (h : Equation1043 G) : Equation1035 G := λ x y => h x y x
@[equational_result]
theorem Equation1047_implies_Equation1045 (G : Type*) [Magma G] (h : Equation1047 G) : Equation1045 G := λ x y => h x y x
@[equational_result]
theorem Equation1050_implies_Equation1048 (G : Type*) [Magma G] (h : Equation1050 G) : Equation1048 G := λ x y => h x y x
@[equational_result]
theorem Equation1051_implies_Equation1045 (G : Type*) [Magma G] (h : Equation1051 G) : Equation1045 G := λ x y => h x y x
@[equational_result]
theorem Equation1052_implies_Equation1046 (G : Type*) [Magma G] (h : Equation1052 G) : Equation1046 G := λ x y => h x y x
@[equational_result]
theorem Equation1053_implies_Equation1045 (G : Type*) [Magma G] (h : Equation1053 G) : Equation1045 G := λ x y => h x y x
@[equational_result]
theorem Equation1055_implies_Equation1035 (G : Type*) [Magma G] (h : Equation1055 G) : Equation1035 G := λ x y => h x y x
@[equational_result]
theorem Equation1056_implies_Equation1036 (G : Type*) [Magma G] (h : Equation1056 G) : Equation1036 G := λ x y => h x y x
@[equational_result]
theorem Equation1057_implies_Equation1035 (G : Type*) [Magma G] (h : Equation1057 G) : Equation1035 G := λ x y => h x y x
@[equational_result]
theorem Equation1059_implies_Equation1038 (G : Type*) [Magma G] (h : Equation1059 G) : Equation1038 G := λ x y => h x y x
@[equational_result]
theorem Equation1060_implies_Equation1039 (G : Type*) [Magma G] (h : Equation1060 G) : Equation1039 G := λ x y => h x y x
@[equational_result]
theorem Equation1061_implies_Equation1038 (G : Type*) [Magma G] (h : Equation1061 G) : Equation1038 G := λ x y => h x y x
@[equational_result]
theorem Equation1063_implies_Equation1035 (G : Type*) [Magma G] (h : Equation1063 G) : Equation1035 G := λ x y => h x y x
@[equational_result]
theorem Equation1064_implies_Equation1036 (G : Type*) [Magma G] (h : Equation1064 G) : Equation1036 G := λ x y => h x y x
@[equational_result]
theorem Equation1065_implies_Equation1035 (G : Type*) [Magma G] (h : Equation1065 G) : Equation1035 G := λ x y => h x y x
@[equational_result]
theorem Equation1074_implies_Equation1072 (G : Type*) [Magma G] (h : Equation1074 G) : Equation1072 G := λ x y => h x y x
@[equational_result]
theorem Equation1077_implies_Equation1075 (G : Type*) [Magma G] (h : Equation1077 G) : Equation1075 G := λ x y => h x y x
@[equational_result]
theorem Equation1078_implies_Equation1072 (G : Type*) [Magma G] (h : Equation1078 G) : Equation1072 G := λ x y => h x y x
@[equational_result]
theorem Equation1079_implies_Equation1073 (G : Type*) [Magma G] (h : Equation1079 G) : Equation1073 G := λ x y => h x y x
@[equational_result]
theorem Equation1080_implies_Equation1072 (G : Type*) [Magma G] (h : Equation1080 G) : Equation1072 G := λ x y => h x y x
@[equational_result]
theorem Equation1084_implies_Equation1082 (G : Type*) [Magma G] (h : Equation1084 G) : Equation1082 G := λ x y => h x y x
@[equational_result]
theorem Equation1087_implies_Equation1085 (G : Type*) [Magma G] (h : Equation1087 G) : Equation1085 G := λ x y => h x y x
@[equational_result]
theorem Equation1088_implies_Equation1082 (G : Type*) [Magma G] (h : Equation1088 G) : Equation1082 G := λ x y => h x y x
@[equational_result]
theorem Equation1089_implies_Equation1083 (G : Type*) [Magma G] (h : Equation1089 G) : Equation1083 G := λ x y => h x y x
@[equational_result]
theorem Equation1090_implies_Equation1082 (G : Type*) [Magma G] (h : Equation1090 G) : Equation1082 G := λ x y => h x y x
@[equational_result]
theorem Equation1092_implies_Equation1072 (G : Type*) [Magma G] (h : Equation1092 G) : Equation1072 G := λ x y => h x y x
@[equational_result]
theorem Equation1093_implies_Equation1073 (G : Type*) [Magma G] (h : Equation1093 G) : Equation1073 G := λ x y => h x y x
@[equational_result]
theorem Equation1094_implies_Equation1072 (G : Type*) [Magma G] (h : Equation1094 G) : Equation1072 G := λ x y => h x y x
@[equational_result]
theorem Equation1096_implies_Equation1075 (G : Type*) [Magma G] (h : Equation1096 G) : Equation1075 G := λ x y => h x y x
@[equational_result]
theorem Equation1097_implies_Equation1076 (G : Type*) [Magma G] (h : Equation1097 G) : Equation1076 G := λ x y => h x y x
@[equational_result]
theorem Equation1098_implies_Equation1075 (G : Type*) [Magma G] (h : Equation1098 G) : Equation1075 G := λ x y => h x y x
@[equational_result]
theorem Equation1100_implies_Equation1072 (G : Type*) [Magma G] (h : Equation1100 G) : Equation1072 G := λ x y => h x y x
@[equational_result]
theorem Equation1101_implies_Equation1073 (G : Type*) [Magma G] (h : Equation1101 G) : Equation1073 G := λ x y => h x y x
@[equational_result]
theorem Equation1102_implies_Equation1072 (G : Type*) [Magma G] (h : Equation1102 G) : Equation1072 G := λ x y => h x y x
@[equational_result]
theorem Equation1111_implies_Equation1109 (G : Type*) [Magma G] (h : Equation1111 G) : Equation1109 G := λ x y => h x y x
@[equational_result]
theorem Equation1114_implies_Equation1112 (G : Type*) [Magma G] (h : Equation1114 G) : Equation1112 G := λ x y => h x y x
@[equational_result]
theorem Equation1115_implies_Equation1109 (G : Type*) [Magma G] (h : Equation1115 G) : Equation1109 G := λ x y => h x y x
@[equational_result]
theorem Equation1116_implies_Equation1110 (G : Type*) [Magma G] (h : Equation1116 G) : Equation1110 G := λ x y => h x y x
@[equational_result]
theorem Equation1117_implies_Equation1109 (G : Type*) [Magma G] (h : Equation1117 G) : Equation1109 G := λ x y => h x y x
@[equational_result]
theorem Equation1121_implies_Equation1119 (G : Type*) [Magma G] (h : Equation1121 G) : Equation1119 G := λ x y => h x y x
@[equational_result]
theorem Equation1124_implies_Equation1122 (G : Type*) [Magma G] (h : Equation1124 G) : Equation1122 G := λ x y => h x y x
@[equational_result]
theorem Equation1125_implies_Equation1119 (G : Type*) [Magma G] (h : Equation1125 G) : Equation1119 G := λ x y => h x y x
@[equational_result]
theorem Equation1126_implies_Equation1120 (G : Type*) [Magma G] (h : Equation1126 G) : Equation1120 G := λ x y => h x y x
@[equational_result]
theorem Equation1127_implies_Equation1119 (G : Type*) [Magma G] (h : Equation1127 G) : Equation1119 G := λ x y => h x y x
@[equational_result]
theorem Equation1129_implies_Equation1109 (G : Type*) [Magma G] (h : Equation1129 G) : Equation1109 G := λ x y => h x y x
@[equational_result]
theorem Equation1130_implies_Equation1110 (G : Type*) [Magma G] (h : Equation1130 G) : Equation1110 G := λ x y => h x y x
@[equational_result]
theorem Equation1131_implies_Equation1109 (G : Type*) [Magma G] (h : Equation1131 G) : Equation1109 G := λ x y => h x y x
@[equational_result]
theorem Equation1133_implies_Equation1112 (G : Type*) [Magma G] (h : Equation1133 G) : Equation1112 G := λ x y => h x y x
@[equational_result]
theorem Equation1134_implies_Equation1113 (G : Type*) [Magma G] (h : Equation1134 G) : Equation1113 G := λ x y => h x y x
@[equational_result]
theorem Equation1135_implies_Equation1112 (G : Type*) [Magma G] (h : Equation1135 G) : Equation1112 G := λ x y => h x y x
@[equational_result]
theorem Equation1137_implies_Equation1109 (G : Type*) [Magma G] (h : Equation1137 G) : Equation1109 G := λ x y => h x y x
@[equational_result]
theorem Equation1138_implies_Equation1110 (G : Type*) [Magma G] (h : Equation1138 G) : Equation1110 G := λ x y => h x y x
@[equational_result]
theorem Equation1139_implies_Equation1109 (G : Type*) [Magma G] (h : Equation1139 G) : Equation1109 G := λ x y => h x y x
@[equational_result]
theorem Equation1146_implies_Equation1072 (G : Type*) [Magma G] (h : Equation1146 G) : Equation1072 G := λ x y => h x y x
@[equational_result]
theorem Equation1147_implies_Equation1073 (G : Type*) [Magma G] (h : Equation1147 G) : Equation1073 G := λ x y => h x y x
@[equational_result]
theorem Equation1148_implies_Equation1072 (G : Type*) [Magma G] (h : Equation1148 G) : Equation1072 G := λ x y => h x y x
@[equational_result]
theorem Equation1150_implies_Equation1075 (G : Type*) [Magma G] (h : Equation1150 G) : Equation1075 G := λ x y => h x y x
@[equational_result]
theorem Equation1151_implies_Equation1076 (G : Type*) [Magma G] (h : Equation1151 G) : Equation1076 G := λ x y => h x y x
@[equational_result]
theorem Equation1152_implies_Equation1075 (G : Type*) [Magma G] (h : Equation1152 G) : Equation1075 G := λ x y => h x y x
@[equational_result]
theorem Equation1154_implies_Equation1072 (G : Type*) [Magma G] (h : Equation1154 G) : Equation1072 G := λ x y => h x y x
@[equational_result]
theorem Equation1155_implies_Equation1073 (G : Type*) [Magma G] (h : Equation1155 G) : Equation1073 G := λ x y => h x y x
@[equational_result]
theorem Equation1156_implies_Equation1072 (G : Type*) [Magma G] (h : Equation1156 G) : Equation1072 G := λ x y => h x y x
@[equational_result]
theorem Equation1163_implies_Equation1082 (G : Type*) [Magma G] (h : Equation1163 G) : Equation1082 G := λ x y => h x y x
@[equational_result]
theorem Equation1164_implies_Equation1083 (G : Type*) [Magma G] (h : Equation1164 G) : Equation1083 G := λ x y => h x y x
@[equational_result]
theorem Equation1165_implies_Equation1082 (G : Type*) [Magma G] (h : Equation1165 G) : Equation1082 G := λ x y => h x y x
@[equational_result]
theorem Equation1167_implies_Equation1085 (G : Type*) [Magma G] (h : Equation1167 G) : Equation1085 G := λ x y => h x y x
@[equational_result]
theorem Equation1168_implies_Equation1086 (G : Type*) [Magma G] (h : Equation1168 G) : Equation1086 G := λ x y => h x y x
@[equational_result]
theorem Equation1169_implies_Equation1085 (G : Type*) [Magma G] (h : Equation1169 G) : Equation1085 G := λ x y => h x y x
@[equational_result]
theorem Equation1171_implies_Equation1082 (G : Type*) [Magma G] (h : Equation1171 G) : Equation1082 G := λ x y => h x y x
@[equational_result]
theorem Equation1172_implies_Equation1083 (G : Type*) [Magma G] (h : Equation1172 G) : Equation1083 G := λ x y => h x y x
@[equational_result]
theorem Equation1173_implies_Equation1082 (G : Type*) [Magma G] (h : Equation1173 G) : Equation1082 G := λ x y => h x y x
@[equational_result]
theorem Equation1180_implies_Equation1072 (G : Type*) [Magma G] (h : Equation1180 G) : Equation1072 G := λ x y => h x y x
@[equational_result]
theorem Equation1181_implies_Equation1073 (G : Type*) [Magma G] (h : Equation1181 G) : Equation1073 G := λ x y => h x y x
@[equational_result]
theorem Equation1182_implies_Equation1072 (G : Type*) [Magma G] (h : Equation1182 G) : Equation1072 G := λ x y => h x y x
@[equational_result]
theorem Equation1184_implies_Equation1075 (G : Type*) [Magma G] (h : Equation1184 G) : Equation1075 G := λ x y => h x y x
@[equational_result]
theorem Equation1185_implies_Equation1076 (G : Type*) [Magma G] (h : Equation1185 G) : Equation1076 G := λ x y => h x y x
@[equational_result]
theorem Equation1186_implies_Equation1075 (G : Type*) [Magma G] (h : Equation1186 G) : Equation1075 G := λ x y => h x y x
@[equational_result]
theorem Equation1188_implies_Equation1072 (G : Type*) [Magma G] (h : Equation1188 G) : Equation1072 G := λ x y => h x y x
@[equational_result]
theorem Equation1189_implies_Equation1073 (G : Type*) [Magma G] (h : Equation1189 G) : Equation1073 G := λ x y => h x y x
@[equational_result]
theorem Equation1190_implies_Equation1072 (G : Type*) [Magma G] (h : Equation1190 G) : Equation1072 G := λ x y => h x y x
@[equational_result]
theorem Equation1227_implies_Equation1225 (G : Type*) [Magma G] (h : Equation1227 G) : Equation1225 G := λ x y => h x y x
@[equational_result]
theorem Equation1230_implies_Equation1228 (G : Type*) [Magma G] (h : Equation1230 G) : Equation1228 G := λ x y => h x y x
@[equational_result]
theorem Equation1233_implies_Equation1231 (G : Type*) [Magma G] (h : Equation1233 G) : Equation1231 G := λ x y => h x y x
@[equational_result]
theorem Equation1234_implies_Equation1228 (G : Type*) [Magma G] (h : Equation1234 G) : Equation1228 G := λ x y => h x y x
@[equational_result]
theorem Equation1235_implies_Equation1229 (G : Type*) [Magma G] (h : Equation1235 G) : Equation1229 G := λ x y => h x y x
@[equational_result]
theorem Equation1236_implies_Equation1228 (G : Type*) [Magma G] (h : Equation1236 G) : Equation1228 G := λ x y => h x y x
@[equational_result]
theorem Equation1240_implies_Equation1238 (G : Type*) [Magma G] (h : Equation1240 G) : Equation1238 G := λ x y => h x y x
@[equational_result]
theorem Equation1243_implies_Equation1241 (G : Type*) [Magma G] (h : Equation1243 G) : Equation1241 G := λ x y => h x y x
@[equational_result]
theorem Equation1244_implies_Equation1238 (G : Type*) [Magma G] (h : Equation1244 G) : Equation1238 G := λ x y => h x y x
@[equational_result]
theorem Equation1245_implies_Equation1239 (G : Type*) [Magma G] (h : Equation1245 G) : Equation1239 G := λ x y => h x y x
@[equational_result]
theorem Equation1246_implies_Equation1238 (G : Type*) [Magma G] (h : Equation1246 G) : Equation1238 G := λ x y => h x y x
@[equational_result]
theorem Equation1250_implies_Equation1248 (G : Type*) [Magma G] (h : Equation1250 G) : Equation1248 G := λ x y => h x y x
@[equational_result]
theorem Equation1253_implies_Equation1251 (G : Type*) [Magma G] (h : Equation1253 G) : Equation1251 G := λ x y => h x y x
@[equational_result]
theorem Equation1254_implies_Equation1248 (G : Type*) [Magma G] (h : Equation1254 G) : Equation1248 G := λ x y => h x y x
@[equational_result]
theorem Equation1255_implies_Equation1249 (G : Type*) [Magma G] (h : Equation1255 G) : Equation1249 G := λ x y => h x y x
@[equational_result]
theorem Equation1256_implies_Equation1248 (G : Type*) [Magma G] (h : Equation1256 G) : Equation1248 G := λ x y => h x y x
@[equational_result]
theorem Equation1258_implies_Equation1238 (G : Type*) [Magma G] (h : Equation1258 G) : Equation1238 G := λ x y => h x y x
@[equational_result]
theorem Equation1259_implies_Equation1239 (G : Type*) [Magma G] (h : Equation1259 G) : Equation1239 G := λ x y => h x y x
@[equational_result]
theorem Equation1260_implies_Equation1238 (G : Type*) [Magma G] (h : Equation1260 G) : Equation1238 G := λ x y => h x y x
@[equational_result]
theorem Equation1262_implies_Equation1241 (G : Type*) [Magma G] (h : Equation1262 G) : Equation1241 G := λ x y => h x y x
@[equational_result]
theorem Equation1263_implies_Equation1242 (G : Type*) [Magma G] (h : Equation1263 G) : Equation1242 G := λ x y => h x y x
@[equational_result]
theorem Equation1264_implies_Equation1241 (G : Type*) [Magma G] (h : Equation1264 G) : Equation1241 G := λ x y => h x y x
@[equational_result]
theorem Equation1266_implies_Equation1238 (G : Type*) [Magma G] (h : Equation1266 G) : Equation1238 G := λ x y => h x y x
@[equational_result]
theorem Equation1267_implies_Equation1239 (G : Type*) [Magma G] (h : Equation1267 G) : Equation1239 G := λ x y => h x y x
@[equational_result]
theorem Equation1268_implies_Equation1238 (G : Type*) [Magma G] (h : Equation1268 G) : Equation1238 G := λ x y => h x y x
@[equational_result]
theorem Equation1277_implies_Equation1275 (G : Type*) [Magma G] (h : Equation1277 G) : Equation1275 G := λ x y => h x y x
@[equational_result]
theorem Equation1280_implies_Equation1278 (G : Type*) [Magma G] (h : Equation1280 G) : Equation1278 G := λ x y => h x y x
@[equational_result]
theorem Equation1281_implies_Equation1275 (G : Type*) [Magma G] (h : Equation1281 G) : Equation1275 G := λ x y => h x y x
@[equational_result]
theorem Equation1282_implies_Equation1276 (G : Type*) [Magma G] (h : Equation1282 G) : Equation1276 G := λ x y => h x y x
@[equational_result]
theorem Equation1283_implies_Equation1275 (G : Type*) [Magma G] (h : Equation1283 G) : Equation1275 G := λ x y => h x y x
@[equational_result]
theorem Equation1287_implies_Equation1285 (G : Type*) [Magma G] (h : Equation1287 G) : Equation1285 G := λ x y => h x y x
@[equational_result]
theorem Equation1290_implies_Equation1288 (G : Type*) [Magma G] (h : Equation1290 G) : Equation1288 G := λ x y => h x y x
@[equational_result]
theorem Equation1291_implies_Equation1285 (G : Type*) [Magma G] (h : Equation1291 G) : Equation1285 G := λ x y => h x y x
@[equational_result]
theorem Equation1292_implies_Equation1286 (G : Type*) [Magma G] (h : Equation1292 G) : Equation1286 G := λ x y => h x y x
@[equational_result]
theorem Equation1293_implies_Equation1285 (G : Type*) [Magma G] (h : Equation1293 G) : Equation1285 G := λ x y => h x y x
@[equational_result]
theorem Equation1295_implies_Equation1275 (G : Type*) [Magma G] (h : Equation1295 G) : Equation1275 G := λ x y => h x y x
@[equational_result]
theorem Equation1296_implies_Equation1276 (G : Type*) [Magma G] (h : Equation1296 G) : Equation1276 G := λ x y => h x y x
@[equational_result]
theorem Equation1297_implies_Equation1275 (G : Type*) [Magma G] (h : Equation1297 G) : Equation1275 G := λ x y => h x y x
@[equational_result]
theorem Equation1299_implies_Equation1278 (G : Type*) [Magma G] (h : Equation1299 G) : Equation1278 G := λ x y => h x y x
@[equational_result]
theorem Equation1300_implies_Equation1279 (G : Type*) [Magma G] (h : Equation1300 G) : Equation1279 G := λ x y => h x y x
@[equational_result]
theorem Equation1301_implies_Equation1278 (G : Type*) [Magma G] (h : Equation1301 G) : Equation1278 G := λ x y => h x y x
@[equational_result]
theorem Equation1303_implies_Equation1275 (G : Type*) [Magma G] (h : Equation1303 G) : Equation1275 G := λ x y => h x y x
@[equational_result]
theorem Equation1304_implies_Equation1276 (G : Type*) [Magma G] (h : Equation1304 G) : Equation1276 G := λ x y => h x y x
@[equational_result]
theorem Equation1305_implies_Equation1275 (G : Type*) [Magma G] (h : Equation1305 G) : Equation1275 G := λ x y => h x y x
@[equational_result]
theorem Equation1314_implies_Equation1312 (G : Type*) [Magma G] (h : Equation1314 G) : Equation1312 G := λ x y => h x y x
@[equational_result]
theorem Equation1317_implies_Equation1315 (G : Type*) [Magma G] (h : Equation1317 G) : Equation1315 G := λ x y => h x y x
@[equational_result]
theorem Equation1318_implies_Equation1312 (G : Type*) [Magma G] (h : Equation1318 G) : Equation1312 G := λ x y => h x y x
@[equational_result]
theorem Equation1319_implies_Equation1313 (G : Type*) [Magma G] (h : Equation1319 G) : Equation1313 G := λ x y => h x y x
@[equational_result]
theorem Equation1320_implies_Equation1312 (G : Type*) [Magma G] (h : Equation1320 G) : Equation1312 G := λ x y => h x y x
@[equational_result]
theorem Equation1324_implies_Equation1322 (G : Type*) [Magma G] (h : Equation1324 G) : Equation1322 G := λ x y => h x y x
@[equational_result]
theorem Equation1327_implies_Equation1325 (G : Type*) [Magma G] (h : Equation1327 G) : Equation1325 G := λ x y => h x y x
@[equational_result]
theorem Equation1328_implies_Equation1322 (G : Type*) [Magma G] (h : Equation1328 G) : Equation1322 G := λ x y => h x y x
@[equational_result]
theorem Equation1329_implies_Equation1323 (G : Type*) [Magma G] (h : Equation1329 G) : Equation1323 G := λ x y => h x y x
@[equational_result]
theorem Equation1330_implies_Equation1322 (G : Type*) [Magma G] (h : Equation1330 G) : Equation1322 G := λ x y => h x y x
@[equational_result]
theorem Equation1332_implies_Equation1312 (G : Type*) [Magma G] (h : Equation1332 G) : Equation1312 G := λ x y => h x y x
@[equational_result]
theorem Equation1333_implies_Equation1313 (G : Type*) [Magma G] (h : Equation1333 G) : Equation1313 G := λ x y => h x y x
@[equational_result]
theorem Equation1334_implies_Equation1312 (G : Type*) [Magma G] (h : Equation1334 G) : Equation1312 G := λ x y => h x y x
@[equational_result]
theorem Equation1336_implies_Equation1315 (G : Type*) [Magma G] (h : Equation1336 G) : Equation1315 G := λ x y => h x y x
@[equational_result]
theorem Equation1337_implies_Equation1316 (G : Type*) [Magma G] (h : Equation1337 G) : Equation1316 G := λ x y => h x y x
@[equational_result]
theorem Equation1338_implies_Equation1315 (G : Type*) [Magma G] (h : Equation1338 G) : Equation1315 G := λ x y => h x y x
@[equational_result]
theorem Equation1340_implies_Equation1312 (G : Type*) [Magma G] (h : Equation1340 G) : Equation1312 G := λ x y => h x y x
@[equational_result]
theorem Equation1341_implies_Equation1313 (G : Type*) [Magma G] (h : Equation1341 G) : Equation1313 G := λ x y => h x y x
@[equational_result]
theorem Equation1342_implies_Equation1312 (G : Type*) [Magma G] (h : Equation1342 G) : Equation1312 G := λ x y => h x y x
@[equational_result]
theorem Equation1349_implies_Equation1275 (G : Type*) [Magma G] (h : Equation1349 G) : Equation1275 G := λ x y => h x y x
@[equational_result]
theorem Equation1350_implies_Equation1276 (G : Type*) [Magma G] (h : Equation1350 G) : Equation1276 G := λ x y => h x y x
@[equational_result]
theorem Equation1351_implies_Equation1275 (G : Type*) [Magma G] (h : Equation1351 G) : Equation1275 G := λ x y => h x y x
@[equational_result]
theorem Equation1353_implies_Equation1278 (G : Type*) [Magma G] (h : Equation1353 G) : Equation1278 G := λ x y => h x y x
@[equational_result]
theorem Equation1354_implies_Equation1279 (G : Type*) [Magma G] (h : Equation1354 G) : Equation1279 G := λ x y => h x y x
@[equational_result]
theorem Equation1355_implies_Equation1278 (G : Type*) [Magma G] (h : Equation1355 G) : Equation1278 G := λ x y => h x y x
@[equational_result]
theorem Equation1357_implies_Equation1275 (G : Type*) [Magma G] (h : Equation1357 G) : Equation1275 G := λ x y => h x y x
@[equational_result]
theorem Equation1358_implies_Equation1276 (G : Type*) [Magma G] (h : Equation1358 G) : Equation1276 G := λ x y => h x y x
@[equational_result]
theorem Equation1359_implies_Equation1275 (G : Type*) [Magma G] (h : Equation1359 G) : Equation1275 G := λ x y => h x y x
@[equational_result]
theorem Equation1366_implies_Equation1285 (G : Type*) [Magma G] (h : Equation1366 G) : Equation1285 G := λ x y => h x y x
@[equational_result]
theorem Equation1367_implies_Equation1286 (G : Type*) [Magma G] (h : Equation1367 G) : Equation1286 G := λ x y => h x y x
@[equational_result]
theorem Equation1368_implies_Equation1285 (G : Type*) [Magma G] (h : Equation1368 G) : Equation1285 G := λ x y => h x y x
@[equational_result]
theorem Equation1370_implies_Equation1288 (G : Type*) [Magma G] (h : Equation1370 G) : Equation1288 G := λ x y => h x y x
@[equational_result]
theorem Equation1371_implies_Equation1289 (G : Type*) [Magma G] (h : Equation1371 G) : Equation1289 G := λ x y => h x y x
@[equational_result]
theorem Equation1372_implies_Equation1288 (G : Type*) [Magma G] (h : Equation1372 G) : Equation1288 G := λ x y => h x y x
@[equational_result]
theorem Equation1374_implies_Equation1285 (G : Type*) [Magma G] (h : Equation1374 G) : Equation1285 G := λ x y => h x y x
@[equational_result]
theorem Equation1375_implies_Equation1286 (G : Type*) [Magma G] (h : Equation1375 G) : Equation1286 G := λ x y => h x y x
@[equational_result]
theorem Equation1376_implies_Equation1285 (G : Type*) [Magma G] (h : Equation1376 G) : Equation1285 G := λ x y => h x y x
@[equational_result]
theorem Equation1383_implies_Equation1275 (G : Type*) [Magma G] (h : Equation1383 G) : Equation1275 G := λ x y => h x y x
@[equational_result]
theorem Equation1384_implies_Equation1276 (G : Type*) [Magma G] (h : Equation1384 G) : Equation1276 G := λ x y => h x y x
@[equational_result]
theorem Equation1385_implies_Equation1275 (G : Type*) [Magma G] (h : Equation1385 G) : Equation1275 G := λ x y => h x y x
@[equational_result]
theorem Equation1387_implies_Equation1278 (G : Type*) [Magma G] (h : Equation1387 G) : Equation1278 G := λ x y => h x y x
@[equational_result]
theorem Equation1388_implies_Equation1279 (G : Type*) [Magma G] (h : Equation1388 G) : Equation1279 G := λ x y => h x y x
@[equational_result]
theorem Equation1389_implies_Equation1278 (G : Type*) [Magma G] (h : Equation1389 G) : Equation1278 G := λ x y => h x y x
@[equational_result]
theorem Equation1391_implies_Equation1275 (G : Type*) [Magma G] (h : Equation1391 G) : Equation1275 G := λ x y => h x y x
@[equational_result]
theorem Equation1392_implies_Equation1276 (G : Type*) [Magma G] (h : Equation1392 G) : Equation1276 G := λ x y => h x y x
@[equational_result]
theorem Equation1393_implies_Equation1275 (G : Type*) [Magma G] (h : Equation1393 G) : Equation1275 G := λ x y => h x y x
@[equational_result]
theorem Equation1430_implies_Equation1428 (G : Type*) [Magma G] (h : Equation1430 G) : Equation1428 G := λ x y => h x y x
@[equational_result]
theorem Equation1433_implies_Equation1431 (G : Type*) [Magma G] (h : Equation1433 G) : Equation1431 G := λ x y => h x y x
@[equational_result]
theorem Equation1436_implies_Equation1434 (G : Type*) [Magma G] (h : Equation1436 G) : Equation1434 G := λ x y => h x y x
@[equational_result]
theorem Equation1437_implies_Equation1431 (G : Type*) [Magma G] (h : Equation1437 G) : Equation1431 G := λ x y => h x y x
@[equational_result]
theorem Equation1438_implies_Equation1432 (G : Type*) [Magma G] (h : Equation1438 G) : Equation1432 G := λ x y => h x y x
@[equational_result]
theorem Equation1439_implies_Equation1431 (G : Type*) [Magma G] (h : Equation1439 G) : Equation1431 G := λ x y => h x y x
@[equational_result]
theorem Equation1443_implies_Equation1441 (G : Type*) [Magma G] (h : Equation1443 G) : Equation1441 G := λ x y => h x y x
@[equational_result]
theorem Equation1446_implies_Equation1444 (G : Type*) [Magma G] (h : Equation1446 G) : Equation1444 G := λ x y => h x y x
@[equational_result]
theorem Equation1447_implies_Equation1441 (G : Type*) [Magma G] (h : Equation1447 G) : Equation1441 G := λ x y => h x y x
@[equational_result]
theorem Equation1448_implies_Equation1442 (G : Type*) [Magma G] (h : Equation1448 G) : Equation1442 G := λ x y => h x y x
@[equational_result]
theorem Equation1449_implies_Equation1441 (G : Type*) [Magma G] (h : Equation1449 G) : Equation1441 G := λ x y => h x y x
@[equational_result]
theorem Equation1453_implies_Equation1451 (G : Type*) [Magma G] (h : Equation1453 G) : Equation1451 G := λ x y => h x y x
@[equational_result]
theorem Equation1456_implies_Equation1454 (G : Type*) [Magma G] (h : Equation1456 G) : Equation1454 G := λ x y => h x y x
@[equational_result]
theorem Equation1457_implies_Equation1451 (G : Type*) [Magma G] (h : Equation1457 G) : Equation1451 G := λ x y => h x y x
@[equational_result]
theorem Equation1458_implies_Equation1452 (G : Type*) [Magma G] (h : Equation1458 G) : Equation1452 G := λ x y => h x y x
@[equational_result]
theorem Equation1459_implies_Equation1451 (G : Type*) [Magma G] (h : Equation1459 G) : Equation1451 G := λ x y => h x y x
@[equational_result]
theorem Equation1461_implies_Equation1441 (G : Type*) [Magma G] (h : Equation1461 G) : Equation1441 G := λ x y => h x y x
@[equational_result]
theorem Equation1462_implies_Equation1442 (G : Type*) [Magma G] (h : Equation1462 G) : Equation1442 G := λ x y => h x y x
@[equational_result]
theorem Equation1463_implies_Equation1441 (G : Type*) [Magma G] (h : Equation1463 G) : Equation1441 G := λ x y => h x y x
@[equational_result]
theorem Equation1465_implies_Equation1444 (G : Type*) [Magma G] (h : Equation1465 G) : Equation1444 G := λ x y => h x y x
@[equational_result]
theorem Equation1466_implies_Equation1445 (G : Type*) [Magma G] (h : Equation1466 G) : Equation1445 G := λ x y => h x y x
@[equational_result]
theorem Equation1467_implies_Equation1444 (G : Type*) [Magma G] (h : Equation1467 G) : Equation1444 G := λ x y => h x y x
@[equational_result]
theorem Equation1469_implies_Equation1441 (G : Type*) [Magma G] (h : Equation1469 G) : Equation1441 G := λ x y => h x y x
@[equational_result]
theorem Equation1470_implies_Equation1442 (G : Type*) [Magma G] (h : Equation1470 G) : Equation1442 G := λ x y => h x y x
@[equational_result]
theorem Equation1471_implies_Equation1441 (G : Type*) [Magma G] (h : Equation1471 G) : Equation1441 G := λ x y => h x y x
@[equational_result]
theorem Equation1480_implies_Equation1478 (G : Type*) [Magma G] (h : Equation1480 G) : Equation1478 G := λ x y => h x y x
@[equational_result]
theorem Equation1483_implies_Equation1481 (G : Type*) [Magma G] (h : Equation1483 G) : Equation1481 G := λ x y => h x y x
@[equational_result]
theorem Equation1484_implies_Equation1478 (G : Type*) [Magma G] (h : Equation1484 G) : Equation1478 G := λ x y => h x y x
@[equational_result]
theorem Equation1485_implies_Equation1479 (G : Type*) [Magma G] (h : Equation1485 G) : Equation1479 G := λ x y => h x y x
@[equational_result]
theorem Equation1486_implies_Equation1478 (G : Type*) [Magma G] (h : Equation1486 G) : Equation1478 G := λ x y => h x y x
@[equational_result]
theorem Equation1490_implies_Equation1488 (G : Type*) [Magma G] (h : Equation1490 G) : Equation1488 G := λ x y => h x y x
@[equational_result]
theorem Equation1493_implies_Equation1491 (G : Type*) [Magma G] (h : Equation1493 G) : Equation1491 G := λ x y => h x y x
@[equational_result]
theorem Equation1494_implies_Equation1488 (G : Type*) [Magma G] (h : Equation1494 G) : Equation1488 G := λ x y => h x y x
@[equational_result]
theorem Equation1495_implies_Equation1489 (G : Type*) [Magma G] (h : Equation1495 G) : Equation1489 G := λ x y => h x y x
@[equational_result]
theorem Equation1496_implies_Equation1488 (G : Type*) [Magma G] (h : Equation1496 G) : Equation1488 G := λ x y => h x y x
@[equational_result]
theorem Equation1498_implies_Equation1478 (G : Type*) [Magma G] (h : Equation1498 G) : Equation1478 G := λ x y => h x y x
@[equational_result]
theorem Equation1499_implies_Equation1479 (G : Type*) [Magma G] (h : Equation1499 G) : Equation1479 G := λ x y => h x y x
@[equational_result]
theorem Equation1500_implies_Equation1478 (G : Type*) [Magma G] (h : Equation1500 G) : Equation1478 G := λ x y => h x y x
@[equational_result]
theorem Equation1502_implies_Equation1481 (G : Type*) [Magma G] (h : Equation1502 G) : Equation1481 G := λ x y => h x y x
@[equational_result]
theorem Equation1503_implies_Equation1482 (G : Type*) [Magma G] (h : Equation1503 G) : Equation1482 G := λ x y => h x y x
@[equational_result]
theorem Equation1504_implies_Equation1481 (G : Type*) [Magma G] (h : Equation1504 G) : Equation1481 G := λ x y => h x y x
@[equational_result]
theorem Equation1506_implies_Equation1478 (G : Type*) [Magma G] (h : Equation1506 G) : Equation1478 G := λ x y => h x y x
@[equational_result]
theorem Equation1507_implies_Equation1479 (G : Type*) [Magma G] (h : Equation1507 G) : Equation1479 G := λ x y => h x y x
@[equational_result]
theorem Equation1508_implies_Equation1478 (G : Type*) [Magma G] (h : Equation1508 G) : Equation1478 G := λ x y => h x y x
@[equational_result]
theorem Equation1517_implies_Equation1515 (G : Type*) [Magma G] (h : Equation1517 G) : Equation1515 G := λ x y => h x y x
@[equational_result]
theorem Equation1520_implies_Equation1518 (G : Type*) [Magma G] (h : Equation1520 G) : Equation1518 G := λ x y => h x y x
@[equational_result]
theorem Equation1521_implies_Equation1515 (G : Type*) [Magma G] (h : Equation1521 G) : Equation1515 G := λ x y => h x y x
@[equational_result]
theorem Equation1522_implies_Equation1516 (G : Type*) [Magma G] (h : Equation1522 G) : Equation1516 G := λ x y => h x y x
@[equational_result]
theorem Equation1523_implies_Equation1515 (G : Type*) [Magma G] (h : Equation1523 G) : Equation1515 G := λ x y => h x y x
@[equational_result]
theorem Equation1527_implies_Equation1525 (G : Type*) [Magma G] (h : Equation1527 G) : Equation1525 G := λ x y => h x y x
@[equational_result]
theorem Equation1530_implies_Equation1528 (G : Type*) [Magma G] (h : Equation1530 G) : Equation1528 G := λ x y => h x y x
@[equational_result]
theorem Equation1531_implies_Equation1525 (G : Type*) [Magma G] (h : Equation1531 G) : Equation1525 G := λ x y => h x y x
@[equational_result]
theorem Equation1532_implies_Equation1526 (G : Type*) [Magma G] (h : Equation1532 G) : Equation1526 G := λ x y => h x y x
@[equational_result]
theorem Equation1533_implies_Equation1525 (G : Type*) [Magma G] (h : Equation1533 G) : Equation1525 G := λ x y => h x y x
@[equational_result]
theorem Equation1535_implies_Equation1515 (G : Type*) [Magma G] (h : Equation1535 G) : Equation1515 G := λ x y => h x y x
@[equational_result]
theorem Equation1536_implies_Equation1516 (G : Type*) [Magma G] (h : Equation1536 G) : Equation1516 G := λ x y => h x y x
@[equational_result]
theorem Equation1537_implies_Equation1515 (G : Type*) [Magma G] (h : Equation1537 G) : Equation1515 G := λ x y => h x y x
@[equational_result]
theorem Equation1539_implies_Equation1518 (G : Type*) [Magma G] (h : Equation1539 G) : Equation1518 G := λ x y => h x y x
@[equational_result]
theorem Equation1540_implies_Equation1519 (G : Type*) [Magma G] (h : Equation1540 G) : Equation1519 G := λ x y => h x y x
@[equational_result]
theorem Equation1541_implies_Equation1518 (G : Type*) [Magma G] (h : Equation1541 G) : Equation1518 G := λ x y => h x y x
@[equational_result]
theorem Equation1543_implies_Equation1515 (G : Type*) [Magma G] (h : Equation1543 G) : Equation1515 G := λ x y => h x y x
@[equational_result]
theorem Equation1544_implies_Equation1516 (G : Type*) [Magma G] (h : Equation1544 G) : Equation1516 G := λ x y => h x y x
@[equational_result]
theorem Equation1545_implies_Equation1515 (G : Type*) [Magma G] (h : Equation1545 G) : Equation1515 G := λ x y => h x y x
@[equational_result]
theorem Equation1552_implies_Equation1478 (G : Type*) [Magma G] (h : Equation1552 G) : Equation1478 G := λ x y => h x y x
@[equational_result]
theorem Equation1553_implies_Equation1479 (G : Type*) [Magma G] (h : Equation1553 G) : Equation1479 G := λ x y => h x y x
@[equational_result]
theorem Equation1554_implies_Equation1478 (G : Type*) [Magma G] (h : Equation1554 G) : Equation1478 G := λ x y => h x y x
@[equational_result]
theorem Equation1556_implies_Equation1481 (G : Type*) [Magma G] (h : Equation1556 G) : Equation1481 G := λ x y => h x y x
@[equational_result]
theorem Equation1557_implies_Equation1482 (G : Type*) [Magma G] (h : Equation1557 G) : Equation1482 G := λ x y => h x y x
@[equational_result]
theorem Equation1558_implies_Equation1481 (G : Type*) [Magma G] (h : Equation1558 G) : Equation1481 G := λ x y => h x y x
@[equational_result]
theorem Equation1560_implies_Equation1478 (G : Type*) [Magma G] (h : Equation1560 G) : Equation1478 G := λ x y => h x y x
@[equational_result]
theorem Equation1561_implies_Equation1479 (G : Type*) [Magma G] (h : Equation1561 G) : Equation1479 G := λ x y => h x y x
@[equational_result]
theorem Equation1562_implies_Equation1478 (G : Type*) [Magma G] (h : Equation1562 G) : Equation1478 G := λ x y => h x y x
@[equational_result]
theorem Equation1569_implies_Equation1488 (G : Type*) [Magma G] (h : Equation1569 G) : Equation1488 G := λ x y => h x y x
@[equational_result]
theorem Equation1570_implies_Equation1489 (G : Type*) [Magma G] (h : Equation1570 G) : Equation1489 G := λ x y => h x y x
@[equational_result]
theorem Equation1571_implies_Equation1488 (G : Type*) [Magma G] (h : Equation1571 G) : Equation1488 G := λ x y => h x y x
@[equational_result]
theorem Equation1573_implies_Equation1491 (G : Type*) [Magma G] (h : Equation1573 G) : Equation1491 G := λ x y => h x y x
@[equational_result]
theorem Equation1574_implies_Equation1492 (G : Type*) [Magma G] (h : Equation1574 G) : Equation1492 G := λ x y => h x y x
@[equational_result]
theorem Equation1575_implies_Equation1491 (G : Type*) [Magma G] (h : Equation1575 G) : Equation1491 G := λ x y => h x y x
@[equational_result]
theorem Equation1577_implies_Equation1488 (G : Type*) [Magma G] (h : Equation1577 G) : Equation1488 G := λ x y => h x y x
@[equational_result]
theorem Equation1578_implies_Equation1489 (G : Type*) [Magma G] (h : Equation1578 G) : Equation1489 G := λ x y => h x y x
@[equational_result]
theorem Equation1579_implies_Equation1488 (G : Type*) [Magma G] (h : Equation1579 G) : Equation1488 G := λ x y => h x y x
@[equational_result]
theorem Equation1586_implies_Equation1478 (G : Type*) [Magma G] (h : Equation1586 G) : Equation1478 G := λ x y => h x y x
@[equational_result]
theorem Equation1587_implies_Equation1479 (G : Type*) [Magma G] (h : Equation1587 G) : Equation1479 G := λ x y => h x y x
@[equational_result]
theorem Equation1588_implies_Equation1478 (G : Type*) [Magma G] (h : Equation1588 G) : Equation1478 G := λ x y => h x y x
@[equational_result]
theorem Equation1590_implies_Equation1481 (G : Type*) [Magma G] (h : Equation1590 G) : Equation1481 G := λ x y => h x y x
@[equational_result]
theorem Equation1591_implies_Equation1482 (G : Type*) [Magma G] (h : Equation1591 G) : Equation1482 G := λ x y => h x y x
@[equational_result]
theorem Equation1592_implies_Equation1481 (G : Type*) [Magma G] (h : Equation1592 G) : Equation1481 G := λ x y => h x y x
@[equational_result]
theorem Equation1594_implies_Equation1478 (G : Type*) [Magma G] (h : Equation1594 G) : Equation1478 G := λ x y => h x y x
@[equational_result]
theorem Equation1595_implies_Equation1479 (G : Type*) [Magma G] (h : Equation1595 G) : Equation1479 G := λ x y => h x y x
@[equational_result]
theorem Equation1596_implies_Equation1478 (G : Type*) [Magma G] (h : Equation1596 G) : Equation1478 G := λ x y => h x y x
@[equational_result]
theorem Equation1633_implies_Equation1631 (G : Type*) [Magma G] (h : Equation1633 G) : Equation1631 G := λ x y => h x y x
@[equational_result]
theorem Equation1636_implies_Equation1634 (G : Type*) [Magma G] (h : Equation1636 G) : Equation1634 G := λ x y => h x y x
@[equational_result]
theorem Equation1639_implies_Equation1637 (G : Type*) [Magma G] (h : Equation1639 G) : Equation1637 G := λ x y => h x y x
@[equational_result]
theorem Equation1640_implies_Equation1634 (G : Type*) [Magma G] (h : Equation1640 G) : Equation1634 G := λ x y => h x y x
@[equational_result]
theorem Equation1641_implies_Equation1635 (G : Type*) [Magma G] (h : Equation1641 G) : Equation1635 G := λ x y => h x y x
@[equational_result]
theorem Equation1642_implies_Equation1634 (G : Type*) [Magma G] (h : Equation1642 G) : Equation1634 G := λ x y => h x y x
@[equational_result]
theorem Equation1646_implies_Equation1644 (G : Type*) [Magma G] (h : Equation1646 G) : Equation1644 G := λ x y => h x y x
@[equational_result]
theorem Equation1649_implies_Equation1647 (G : Type*) [Magma G] (h : Equation1649 G) : Equation1647 G := λ x y => h x y x
@[equational_result]
theorem Equation1650_implies_Equation1644 (G : Type*) [Magma G] (h : Equation1650 G) : Equation1644 G := λ x y => h x y x
@[equational_result]
theorem Equation1651_implies_Equation1645 (G : Type*) [Magma G] (h : Equation1651 G) : Equation1645 G := λ x y => h x y x
@[equational_result]
theorem Equation1652_implies_Equation1644 (G : Type*) [Magma G] (h : Equation1652 G) : Equation1644 G := λ x y => h x y x
@[equational_result]
theorem Equation1656_implies_Equation1654 (G : Type*) [Magma G] (h : Equation1656 G) : Equation1654 G := λ x y => h x y x
@[equational_result]
theorem Equation1659_implies_Equation1657 (G : Type*) [Magma G] (h : Equation1659 G) : Equation1657 G := λ x y => h x y x
@[equational_result]
theorem Equation1660_implies_Equation1654 (G : Type*) [Magma G] (h : Equation1660 G) : Equation1654 G := λ x y => h x y x
@[equational_result]
theorem Equation1661_implies_Equation1655 (G : Type*) [Magma G] (h : Equation1661 G) : Equation1655 G := λ x y => h x y x
@[equational_result]
theorem Equation1662_implies_Equation1654 (G : Type*) [Magma G] (h : Equation1662 G) : Equation1654 G := λ x y => h x y x
@[equational_result]
theorem Equation1664_implies_Equation1644 (G : Type*) [Magma G] (h : Equation1664 G) : Equation1644 G := λ x y => h x y x
@[equational_result]
theorem Equation1665_implies_Equation1645 (G : Type*) [Magma G] (h : Equation1665 G) : Equation1645 G := λ x y => h x y x
@[equational_result]
theorem Equation1666_implies_Equation1644 (G : Type*) [Magma G] (h : Equation1666 G) : Equation1644 G := λ x y => h x y x
@[equational_result]
theorem Equation1668_implies_Equation1647 (G : Type*) [Magma G] (h : Equation1668 G) : Equation1647 G := λ x y => h x y x
@[equational_result]
theorem Equation1669_implies_Equation1648 (G : Type*) [Magma G] (h : Equation1669 G) : Equation1648 G := λ x y => h x y x
@[equational_result]
theorem Equation1670_implies_Equation1647 (G : Type*) [Magma G] (h : Equation1670 G) : Equation1647 G := λ x y => h x y x
@[equational_result]
theorem Equation1672_implies_Equation1644 (G : Type*) [Magma G] (h : Equation1672 G) : Equation1644 G := λ x y => h x y x
@[equational_result]
theorem Equation1673_implies_Equation1645 (G : Type*) [Magma G] (h : Equation1673 G) : Equation1645 G := λ x y => h x y x
@[equational_result]
theorem Equation1674_implies_Equation1644 (G : Type*) [Magma G] (h : Equation1674 G) : Equation1644 G := λ x y => h x y x
@[equational_result]
theorem Equation1683_implies_Equation1681 (G : Type*) [Magma G] (h : Equation1683 G) : Equation1681 G := λ x y => h x y x
@[equational_result]
theorem Equation1686_implies_Equation1684 (G : Type*) [Magma G] (h : Equation1686 G) : Equation1684 G := λ x y => h x y x
@[equational_result]
theorem Equation1687_implies_Equation1681 (G : Type*) [Magma G] (h : Equation1687 G) : Equation1681 G := λ x y => h x y x
@[equational_result]
theorem Equation1688_implies_Equation1682 (G : Type*) [Magma G] (h : Equation1688 G) : Equation1682 G := λ x y => h x y x
@[equational_result]
theorem Equation1689_implies_Equation1681 (G : Type*) [Magma G] (h : Equation1689 G) : Equation1681 G := λ x y => h x y x
@[equational_result]
theorem Equation1693_implies_Equation1691 (G : Type*) [Magma G] (h : Equation1693 G) : Equation1691 G := λ x y => h x y x
@[equational_result]
theorem Equation1696_implies_Equation1694 (G : Type*) [Magma G] (h : Equation1696 G) : Equation1694 G := λ x y => h x y x
@[equational_result]
theorem Equation1697_implies_Equation1691 (G : Type*) [Magma G] (h : Equation1697 G) : Equation1691 G := λ x y => h x y x
@[equational_result]
theorem Equation1698_implies_Equation1692 (G : Type*) [Magma G] (h : Equation1698 G) : Equation1692 G := λ x y => h x y x
@[equational_result]
theorem Equation1699_implies_Equation1691 (G : Type*) [Magma G] (h : Equation1699 G) : Equation1691 G := λ x y => h x y x
@[equational_result]
theorem Equation1701_implies_Equation1681 (G : Type*) [Magma G] (h : Equation1701 G) : Equation1681 G := λ x y => h x y x
@[equational_result]
theorem Equation1702_implies_Equation1682 (G : Type*) [Magma G] (h : Equation1702 G) : Equation1682 G := λ x y => h x y x
@[equational_result]
theorem Equation1703_implies_Equation1681 (G : Type*) [Magma G] (h : Equation1703 G) : Equation1681 G := λ x y => h x y x
@[equational_result]
theorem Equation1705_implies_Equation1684 (G : Type*) [Magma G] (h : Equation1705 G) : Equation1684 G := λ x y => h x y x
@[equational_result]
theorem Equation1706_implies_Equation1685 (G : Type*) [Magma G] (h : Equation1706 G) : Equation1685 G := λ x y => h x y x
@[equational_result]
theorem Equation1707_implies_Equation1684 (G : Type*) [Magma G] (h : Equation1707 G) : Equation1684 G := λ x y => h x y x
@[equational_result]
theorem Equation1709_implies_Equation1681 (G : Type*) [Magma G] (h : Equation1709 G) : Equation1681 G := λ x y => h x y x
@[equational_result]
theorem Equation1710_implies_Equation1682 (G : Type*) [Magma G] (h : Equation1710 G) : Equation1682 G := λ x y => h x y x
@[equational_result]
theorem Equation1711_implies_Equation1681 (G : Type*) [Magma G] (h : Equation1711 G) : Equation1681 G := λ x y => h x y x
@[equational_result]
theorem Equation1720_implies_Equation1718 (G : Type*) [Magma G] (h : Equation1720 G) : Equation1718 G := λ x y => h x y x
@[equational_result]
theorem Equation1723_implies_Equation1721 (G : Type*) [Magma G] (h : Equation1723 G) : Equation1721 G := λ x y => h x y x
@[equational_result]
theorem Equation1724_implies_Equation1718 (G : Type*) [Magma G] (h : Equation1724 G) : Equation1718 G := λ x y => h x y x
@[equational_result]
theorem Equation1725_implies_Equation1719 (G : Type*) [Magma G] (h : Equation1725 G) : Equation1719 G := λ x y => h x y x
@[equational_result]
theorem Equation1726_implies_Equation1718 (G : Type*) [Magma G] (h : Equation1726 G) : Equation1718 G := λ x y => h x y x
@[equational_result]
theorem Equation1730_implies_Equation1728 (G : Type*) [Magma G] (h : Equation1730 G) : Equation1728 G := λ x y => h x y x
@[equational_result]
theorem Equation1733_implies_Equation1731 (G : Type*) [Magma G] (h : Equation1733 G) : Equation1731 G := λ x y => h x y x
@[equational_result]
theorem Equation1734_implies_Equation1728 (G : Type*) [Magma G] (h : Equation1734 G) : Equation1728 G := λ x y => h x y x
@[equational_result]
theorem Equation1735_implies_Equation1729 (G : Type*) [Magma G] (h : Equation1735 G) : Equation1729 G := λ x y => h x y x
@[equational_result]
theorem Equation1736_implies_Equation1728 (G : Type*) [Magma G] (h : Equation1736 G) : Equation1728 G := λ x y => h x y x
@[equational_result]
theorem Equation1738_implies_Equation1718 (G : Type*) [Magma G] (h : Equation1738 G) : Equation1718 G := λ x y => h x y x
@[equational_result]
theorem Equation1739_implies_Equation1719 (G : Type*) [Magma G] (h : Equation1739 G) : Equation1719 G := λ x y => h x y x
@[equational_result]
theorem Equation1740_implies_Equation1718 (G : Type*) [Magma G] (h : Equation1740 G) : Equation1718 G := λ x y => h x y x
@[equational_result]
theorem Equation1742_implies_Equation1721 (G : Type*) [Magma G] (h : Equation1742 G) : Equation1721 G := λ x y => h x y x
@[equational_result]
theorem Equation1743_implies_Equation1722 (G : Type*) [Magma G] (h : Equation1743 G) : Equation1722 G := λ x y => h x y x
@[equational_result]
theorem Equation1744_implies_Equation1721 (G : Type*) [Magma G] (h : Equation1744 G) : Equation1721 G := λ x y => h x y x
@[equational_result]
theorem Equation1746_implies_Equation1718 (G : Type*) [Magma G] (h : Equation1746 G) : Equation1718 G := λ x y => h x y x
@[equational_result]
theorem Equation1747_implies_Equation1719 (G : Type*) [Magma G] (h : Equation1747 G) : Equation1719 G := λ x y => h x y x
@[equational_result]
theorem Equation1748_implies_Equation1718 (G : Type*) [Magma G] (h : Equation1748 G) : Equation1718 G := λ x y => h x y x
@[equational_result]
theorem Equation1755_implies_Equation1681 (G : Type*) [Magma G] (h : Equation1755 G) : Equation1681 G := λ x y => h x y x
@[equational_result]
theorem Equation1756_implies_Equation1682 (G : Type*) [Magma G] (h : Equation1756 G) : Equation1682 G := λ x y => h x y x
@[equational_result]
theorem Equation1757_implies_Equation1681 (G : Type*) [Magma G] (h : Equation1757 G) : Equation1681 G := λ x y => h x y x
@[equational_result]
theorem Equation1759_implies_Equation1684 (G : Type*) [Magma G] (h : Equation1759 G) : Equation1684 G := λ x y => h x y x
@[equational_result]
theorem Equation1760_implies_Equation1685 (G : Type*) [Magma G] (h : Equation1760 G) : Equation1685 G := λ x y => h x y x
@[equational_result]
theorem Equation1761_implies_Equation1684 (G : Type*) [Magma G] (h : Equation1761 G) : Equation1684 G := λ x y => h x y x
@[equational_result]
theorem Equation1763_implies_Equation1681 (G : Type*) [Magma G] (h : Equation1763 G) : Equation1681 G := λ x y => h x y x
@[equational_result]
theorem Equation1764_implies_Equation1682 (G : Type*) [Magma G] (h : Equation1764 G) : Equation1682 G := λ x y => h x y x
@[equational_result]
theorem Equation1765_implies_Equation1681 (G : Type*) [Magma G] (h : Equation1765 G) : Equation1681 G := λ x y => h x y x
@[equational_result]
theorem Equation1772_implies_Equation1691 (G : Type*) [Magma G] (h : Equation1772 G) : Equation1691 G := λ x y => h x y x
@[equational_result]
theorem Equation1773_implies_Equation1692 (G : Type*) [Magma G] (h : Equation1773 G) : Equation1692 G := λ x y => h x y x
@[equational_result]
theorem Equation1774_implies_Equation1691 (G : Type*) [Magma G] (h : Equation1774 G) : Equation1691 G := λ x y => h x y x
@[equational_result]
theorem Equation1776_implies_Equation1694 (G : Type*) [Magma G] (h : Equation1776 G) : Equation1694 G := λ x y => h x y x
@[equational_result]
theorem Equation1777_implies_Equation1695 (G : Type*) [Magma G] (h : Equation1777 G) : Equation1695 G := λ x y => h x y x
@[equational_result]
theorem Equation1778_implies_Equation1694 (G : Type*) [Magma G] (h : Equation1778 G) : Equation1694 G := λ x y => h x y x
@[equational_result]
theorem Equation1780_implies_Equation1691 (G : Type*) [Magma G] (h : Equation1780 G) : Equation1691 G := λ x y => h x y x
@[equational_result]
theorem Equation1781_implies_Equation1692 (G : Type*) [Magma G] (h : Equation1781 G) : Equation1692 G := λ x y => h x y x
@[equational_result]
theorem Equation1782_implies_Equation1691 (G : Type*) [Magma G] (h : Equation1782 G) : Equation1691 G := λ x y => h x y x
@[equational_result]
theorem Equation1789_implies_Equation1681 (G : Type*) [Magma G] (h : Equation1789 G) : Equation1681 G := λ x y => h x y x
@[equational_result]
theorem Equation1790_implies_Equation1682 (G : Type*) [Magma G] (h : Equation1790 G) : Equation1682 G := λ x y => h x y x
@[equational_result]
theorem Equation1791_implies_Equation1681 (G : Type*) [Magma G] (h : Equation1791 G) : Equation1681 G := λ x y => h x y x
@[equational_result]
theorem Equation1793_implies_Equation1684 (G : Type*) [Magma G] (h : Equation1793 G) : Equation1684 G := λ x y => h x y x
@[equational_result]
theorem Equation1794_implies_Equation1685 (G : Type*) [Magma G] (h : Equation1794 G) : Equation1685 G := λ x y => h x y x
@[equational_result]
theorem Equation1795_implies_Equation1684 (G : Type*) [Magma G] (h : Equation1795 G) : Equation1684 G := λ x y => h x y x
@[equational_result]
theorem Equation1797_implies_Equation1681 (G : Type*) [Magma G] (h : Equation1797 G) : Equation1681 G := λ x y => h x y x
@[equational_result]
theorem Equation1798_implies_Equation1682 (G : Type*) [Magma G] (h : Equation1798 G) : Equation1682 G := λ x y => h x y x
@[equational_result]
theorem Equation1799_implies_Equation1681 (G : Type*) [Magma G] (h : Equation1799 G) : Equation1681 G := λ x y => h x y x
@[equational_result]
theorem Equation1836_implies_Equation1834 (G : Type*) [Magma G] (h : Equation1836 G) : Equation1834 G := λ x y => h x y x
@[equational_result]
theorem Equation1839_implies_Equation1837 (G : Type*) [Magma G] (h : Equation1839 G) : Equation1837 G := λ x y => h x y x
@[equational_result]
theorem Equation1842_implies_Equation1840 (G : Type*) [Magma G] (h : Equation1842 G) : Equation1840 G := λ x y => h x y x
@[equational_result]
theorem Equation1843_implies_Equation1837 (G : Type*) [Magma G] (h : Equation1843 G) : Equation1837 G := λ x y => h x y x
@[equational_result]
theorem Equation1844_implies_Equation1838 (G : Type*) [Magma G] (h : Equation1844 G) : Equation1838 G := λ x y => h x y x
@[equational_result]
theorem Equation1845_implies_Equation1837 (G : Type*) [Magma G] (h : Equation1845 G) : Equation1837 G := λ x y => h x y x
@[equational_result]
theorem Equation1849_implies_Equation1847 (G : Type*) [Magma G] (h : Equation1849 G) : Equation1847 G := λ x y => h x y x
@[equational_result]
theorem Equation1852_implies_Equation1850 (G : Type*) [Magma G] (h : Equation1852 G) : Equation1850 G := λ x y => h x y x
@[equational_result]
theorem Equation1853_implies_Equation1847 (G : Type*) [Magma G] (h : Equation1853 G) : Equation1847 G := λ x y => h x y x
@[equational_result]
theorem Equation1854_implies_Equation1848 (G : Type*) [Magma G] (h : Equation1854 G) : Equation1848 G := λ x y => h x y x
@[equational_result]
theorem Equation1855_implies_Equation1847 (G : Type*) [Magma G] (h : Equation1855 G) : Equation1847 G := λ x y => h x y x
@[equational_result]
theorem Equation1859_implies_Equation1857 (G : Type*) [Magma G] (h : Equation1859 G) : Equation1857 G := λ x y => h x y x
@[equational_result]
theorem Equation1862_implies_Equation1860 (G : Type*) [Magma G] (h : Equation1862 G) : Equation1860 G := λ x y => h x y x
@[equational_result]
theorem Equation1863_implies_Equation1857 (G : Type*) [Magma G] (h : Equation1863 G) : Equation1857 G := λ x y => h x y x
@[equational_result]
theorem Equation1864_implies_Equation1858 (G : Type*) [Magma G] (h : Equation1864 G) : Equation1858 G := λ x y => h x y x
@[equational_result]
theorem Equation1865_implies_Equation1857 (G : Type*) [Magma G] (h : Equation1865 G) : Equation1857 G := λ x y => h x y x
@[equational_result]
theorem Equation1867_implies_Equation1847 (G : Type*) [Magma G] (h : Equation1867 G) : Equation1847 G := λ x y => h x y x
@[equational_result]
theorem Equation1868_implies_Equation1848 (G : Type*) [Magma G] (h : Equation1868 G) : Equation1848 G := λ x y => h x y x
@[equational_result]
theorem Equation1869_implies_Equation1847 (G : Type*) [Magma G] (h : Equation1869 G) : Equation1847 G := λ x y => h x y x
@[equational_result]
theorem Equation1871_implies_Equation1850 (G : Type*) [Magma G] (h : Equation1871 G) : Equation1850 G := λ x y => h x y x
@[equational_result]
theorem Equation1872_implies_Equation1851 (G : Type*) [Magma G] (h : Equation1872 G) : Equation1851 G := λ x y => h x y x
@[equational_result]
theorem Equation1873_implies_Equation1850 (G : Type*) [Magma G] (h : Equation1873 G) : Equation1850 G := λ x y => h x y x
@[equational_result]
theorem Equation1875_implies_Equation1847 (G : Type*) [Magma G] (h : Equation1875 G) : Equation1847 G := λ x y => h x y x
@[equational_result]
theorem Equation1876_implies_Equation1848 (G : Type*) [Magma G] (h : Equation1876 G) : Equation1848 G := λ x y => h x y x
@[equational_result]
theorem Equation1877_implies_Equation1847 (G : Type*) [Magma G] (h : Equation1877 G) : Equation1847 G := λ x y => h x y x
@[equational_result]
theorem Equation1886_implies_Equation1884 (G : Type*) [Magma G] (h : Equation1886 G) : Equation1884 G := λ x y => h x y x
@[equational_result]
theorem Equation1889_implies_Equation1887 (G : Type*) [Magma G] (h : Equation1889 G) : Equation1887 G := λ x y => h x y x
@[equational_result]
theorem Equation1890_implies_Equation1884 (G : Type*) [Magma G] (h : Equation1890 G) : Equation1884 G := λ x y => h x y x
@[equational_result]
theorem Equation1891_implies_Equation1885 (G : Type*) [Magma G] (h : Equation1891 G) : Equation1885 G := λ x y => h x y x
@[equational_result]
theorem Equation1892_implies_Equation1884 (G : Type*) [Magma G] (h : Equation1892 G) : Equation1884 G := λ x y => h x y x
@[equational_result]
theorem Equation1896_implies_Equation1894 (G : Type*) [Magma G] (h : Equation1896 G) : Equation1894 G := λ x y => h x y x
@[equational_result]
theorem Equation1899_implies_Equation1897 (G : Type*) [Magma G] (h : Equation1899 G) : Equation1897 G := λ x y => h x y x
@[equational_result]
theorem Equation1900_implies_Equation1894 (G : Type*) [Magma G] (h : Equation1900 G) : Equation1894 G := λ x y => h x y x
@[equational_result]
theorem Equation1901_implies_Equation1895 (G : Type*) [Magma G] (h : Equation1901 G) : Equation1895 G := λ x y => h x y x
@[equational_result]
theorem Equation1902_implies_Equation1894 (G : Type*) [Magma G] (h : Equation1902 G) : Equation1894 G := λ x y => h x y x
@[equational_result]
theorem Equation1904_implies_Equation1884 (G : Type*) [Magma G] (h : Equation1904 G) : Equation1884 G := λ x y => h x y x
@[equational_result]
theorem Equation1905_implies_Equation1885 (G : Type*) [Magma G] (h : Equation1905 G) : Equation1885 G := λ x y => h x y x
@[equational_result]
theorem Equation1906_implies_Equation1884 (G : Type*) [Magma G] (h : Equation1906 G) : Equation1884 G := λ x y => h x y x
@[equational_result]
theorem Equation1908_implies_Equation1887 (G : Type*) [Magma G] (h : Equation1908 G) : Equation1887 G := λ x y => h x y x
@[equational_result]
theorem Equation1909_implies_Equation1888 (G : Type*) [Magma G] (h : Equation1909 G) : Equation1888 G := λ x y => h x y x
@[equational_result]
theorem Equation1910_implies_Equation1887 (G : Type*) [Magma G] (h : Equation1910 G) : Equation1887 G := λ x y => h x y x
@[equational_result]
theorem Equation1912_implies_Equation1884 (G : Type*) [Magma G] (h : Equation1912 G) : Equation1884 G := λ x y => h x y x
@[equational_result]
theorem Equation1913_implies_Equation1885 (G : Type*) [Magma G] (h : Equation1913 G) : Equation1885 G := λ x y => h x y x
@[equational_result]
theorem Equation1914_implies_Equation1884 (G : Type*) [Magma G] (h : Equation1914 G) : Equation1884 G := λ x y => h x y x
@[equational_result]
theorem Equation1923_implies_Equation1921 (G : Type*) [Magma G] (h : Equation1923 G) : Equation1921 G := λ x y => h x y x
@[equational_result]
theorem Equation1926_implies_Equation1924 (G : Type*) [Magma G] (h : Equation1926 G) : Equation1924 G := λ x y => h x y x
@[equational_result]
theorem Equation1927_implies_Equation1921 (G : Type*) [Magma G] (h : Equation1927 G) : Equation1921 G := λ x y => h x y x
@[equational_result]
theorem Equation1928_implies_Equation1922 (G : Type*) [Magma G] (h : Equation1928 G) : Equation1922 G := λ x y => h x y x
@[equational_result]
theorem Equation1929_implies_Equation1921 (G : Type*) [Magma G] (h : Equation1929 G) : Equation1921 G := λ x y => h x y x
@[equational_result]
theorem Equation1933_implies_Equation1931 (G : Type*) [Magma G] (h : Equation1933 G) : Equation1931 G := λ x y => h x y x
@[equational_result]
theorem Equation1936_implies_Equation1934 (G : Type*) [Magma G] (h : Equation1936 G) : Equation1934 G := λ x y => h x y x
@[equational_result]
theorem Equation1937_implies_Equation1931 (G : Type*) [Magma G] (h : Equation1937 G) : Equation1931 G := λ x y => h x y x
@[equational_result]
theorem Equation1938_implies_Equation1932 (G : Type*) [Magma G] (h : Equation1938 G) : Equation1932 G := λ x y => h x y x
@[equational_result]
theorem Equation1939_implies_Equation1931 (G : Type*) [Magma G] (h : Equation1939 G) : Equation1931 G := λ x y => h x y x
@[equational_result]
theorem Equation1941_implies_Equation1921 (G : Type*) [Magma G] (h : Equation1941 G) : Equation1921 G := λ x y => h x y x
@[equational_result]
theorem Equation1942_implies_Equation1922 (G : Type*) [Magma G] (h : Equation1942 G) : Equation1922 G := λ x y => h x y x
@[equational_result]
theorem Equation1943_implies_Equation1921 (G : Type*) [Magma G] (h : Equation1943 G) : Equation1921 G := λ x y => h x y x
@[equational_result]
theorem Equation1945_implies_Equation1924 (G : Type*) [Magma G] (h : Equation1945 G) : Equation1924 G := λ x y => h x y x
@[equational_result]
theorem Equation1946_implies_Equation1925 (G : Type*) [Magma G] (h : Equation1946 G) : Equation1925 G := λ x y => h x y x
@[equational_result]
theorem Equation1947_implies_Equation1924 (G : Type*) [Magma G] (h : Equation1947 G) : Equation1924 G := λ x y => h x y x
@[equational_result]
theorem Equation1949_implies_Equation1921 (G : Type*) [Magma G] (h : Equation1949 G) : Equation1921 G := λ x y => h x y x
@[equational_result]
theorem Equation1950_implies_Equation1922 (G : Type*) [Magma G] (h : Equation1950 G) : Equation1922 G := λ x y => h x y x
@[equational_result]
theorem Equation1951_implies_Equation1921 (G : Type*) [Magma G] (h : Equation1951 G) : Equation1921 G := λ x y => h x y x
@[equational_result]
theorem Equation1958_implies_Equation1884 (G : Type*) [Magma G] (h : Equation1958 G) : Equation1884 G := λ x y => h x y x
@[equational_result]
theorem Equation1959_implies_Equation1885 (G : Type*) [Magma G] (h : Equation1959 G) : Equation1885 G := λ x y => h x y x
@[equational_result]
theorem Equation1960_implies_Equation1884 (G : Type*) [Magma G] (h : Equation1960 G) : Equation1884 G := λ x y => h x y x
@[equational_result]
theorem Equation1962_implies_Equation1887 (G : Type*) [Magma G] (h : Equation1962 G) : Equation1887 G := λ x y => h x y x
@[equational_result]
theorem Equation1963_implies_Equation1888 (G : Type*) [Magma G] (h : Equation1963 G) : Equation1888 G := λ x y => h x y x
@[equational_result]
theorem Equation1964_implies_Equation1887 (G : Type*) [Magma G] (h : Equation1964 G) : Equation1887 G := λ x y => h x y x
@[equational_result]
theorem Equation1966_implies_Equation1884 (G : Type*) [Magma G] (h : Equation1966 G) : Equation1884 G := λ x y => h x y x
@[equational_result]
theorem Equation1967_implies_Equation1885 (G : Type*) [Magma G] (h : Equation1967 G) : Equation1885 G := λ x y => h x y x
@[equational_result]
theorem Equation1968_implies_Equation1884 (G : Type*) [Magma G] (h : Equation1968 G) : Equation1884 G := λ x y => h x y x
@[equational_result]
theorem Equation1975_implies_Equation1894 (G : Type*) [Magma G] (h : Equation1975 G) : Equation1894 G := λ x y => h x y x
@[equational_result]
theorem Equation1976_implies_Equation1895 (G : Type*) [Magma G] (h : Equation1976 G) : Equation1895 G := λ x y => h x y x
@[equational_result]
theorem Equation1977_implies_Equation1894 (G : Type*) [Magma G] (h : Equation1977 G) : Equation1894 G := λ x y => h x y x
@[equational_result]
theorem Equation1979_implies_Equation1897 (G : Type*) [Magma G] (h : Equation1979 G) : Equation1897 G := λ x y => h x y x
@[equational_result]
theorem Equation1980_implies_Equation1898 (G : Type*) [Magma G] (h : Equation1980 G) : Equation1898 G := λ x y => h x y x
@[equational_result]
theorem Equation1981_implies_Equation1897 (G : Type*) [Magma G] (h : Equation1981 G) : Equation1897 G := λ x y => h x y x
@[equational_result]
theorem Equation1983_implies_Equation1894 (G : Type*) [Magma G] (h : Equation1983 G) : Equation1894 G := λ x y => h x y x
@[equational_result]
theorem Equation1984_implies_Equation1895 (G : Type*) [Magma G] (h : Equation1984 G) : Equation1895 G := λ x y => h x y x
@[equational_result]
theorem Equation1985_implies_Equation1894 (G : Type*) [Magma G] (h : Equation1985 G) : Equation1894 G := λ x y => h x y x
@[equational_result]
theorem Equation1992_implies_Equation1884 (G : Type*) [Magma G] (h : Equation1992 G) : Equation1884 G := λ x y => h x y x
@[equational_result]
theorem Equation1993_implies_Equation1885 (G : Type*) [Magma G] (h : Equation1993 G) : Equation1885 G := λ x y => h x y x
@[equational_result]
theorem Equation1994_implies_Equation1884 (G : Type*) [Magma G] (h : Equation1994 G) : Equation1884 G := λ x y => h x y x
@[equational_result]
theorem Equation1996_implies_Equation1887 (G : Type*) [Magma G] (h : Equation1996 G) : Equation1887 G := λ x y => h x y x
@[equational_result]
theorem Equation1997_implies_Equation1888 (G : Type*) [Magma G] (h : Equation1997 G) : Equation1888 G := λ x y => h x y x
@[equational_result]
theorem Equation1998_implies_Equation1887 (G : Type*) [Magma G] (h : Equation1998 G) : Equation1887 G := λ x y => h x y x
@[equational_result]
theorem Equation2000_implies_Equation1884 (G : Type*) [Magma G] (h : Equation2000 G) : Equation1884 G := λ x y => h x y x
@[equational_result]
theorem Equation2001_implies_Equation1885 (G : Type*) [Magma G] (h : Equation2001 G) : Equation1885 G := λ x y => h x y x
@[equational_result]
theorem Equation2002_implies_Equation1884 (G : Type*) [Magma G] (h : Equation2002 G) : Equation1884 G := λ x y => h x y x
@[equational_result]
theorem Equation2039_implies_Equation2037 (G : Type*) [Magma G] (h : Equation2039 G) : Equation2037 G := λ x y => h x y x
@[equational_result]
theorem Equation2042_implies_Equation2040 (G : Type*) [Magma G] (h : Equation2042 G) : Equation2040 G := λ x y => h x y x
@[equational_result]
theorem Equation2045_implies_Equation2043 (G : Type*) [Magma G] (h : Equation2045 G) : Equation2043 G := λ x y => h x y x
@[equational_result]
theorem Equation2046_implies_Equation2040 (G : Type*) [Magma G] (h : Equation2046 G) : Equation2040 G := λ x y => h x y x
@[equational_result]
theorem Equation2047_implies_Equation2041 (G : Type*) [Magma G] (h : Equation2047 G) : Equation2041 G := λ x y => h x y x
@[equational_result]
theorem Equation2048_implies_Equation2040 (G : Type*) [Magma G] (h : Equation2048 G) : Equation2040 G := λ x y => h x y x
@[equational_result]
theorem Equation2052_implies_Equation2050 (G : Type*) [Magma G] (h : Equation2052 G) : Equation2050 G := λ x y => h x y x
@[equational_result]
theorem Equation2055_implies_Equation2053 (G : Type*) [Magma G] (h : Equation2055 G) : Equation2053 G := λ x y => h x y x
@[equational_result]
theorem Equation2056_implies_Equation2050 (G : Type*) [Magma G] (h : Equation2056 G) : Equation2050 G := λ x y => h x y x
@[equational_result]
theorem Equation2057_implies_Equation2051 (G : Type*) [Magma G] (h : Equation2057 G) : Equation2051 G := λ x y => h x y x
@[equational_result]
theorem Equation2058_implies_Equation2050 (G : Type*) [Magma G] (h : Equation2058 G) : Equation2050 G := λ x y => h x y x
@[equational_result]
theorem Equation2062_implies_Equation2060 (G : Type*) [Magma G] (h : Equation2062 G) : Equation2060 G := λ x y => h x y x
@[equational_result]
theorem Equation2065_implies_Equation2063 (G : Type*) [Magma G] (h : Equation2065 G) : Equation2063 G := λ x y => h x y x
@[equational_result]
theorem Equation2066_implies_Equation2060 (G : Type*) [Magma G] (h : Equation2066 G) : Equation2060 G := λ x y => h x y x
@[equational_result]
theorem Equation2067_implies_Equation2061 (G : Type*) [Magma G] (h : Equation2067 G) : Equation2061 G := λ x y => h x y x
@[equational_result]
theorem Equation2068_implies_Equation2060 (G : Type*) [Magma G] (h : Equation2068 G) : Equation2060 G := λ x y => h x y x
@[equational_result]
theorem Equation2070_implies_Equation2050 (G : Type*) [Magma G] (h : Equation2070 G) : Equation2050 G := λ x y => h x y x
@[equational_result]
theorem Equation2071_implies_Equation2051 (G : Type*) [Magma G] (h : Equation2071 G) : Equation2051 G := λ x y => h x y x
@[equational_result]
theorem Equation2072_implies_Equation2050 (G : Type*) [Magma G] (h : Equation2072 G) : Equation2050 G := λ x y => h x y x
@[equational_result]
theorem Equation2074_implies_Equation2053 (G : Type*) [Magma G] (h : Equation2074 G) : Equation2053 G := λ x y => h x y x
@[equational_result]
theorem Equation2075_implies_Equation2054 (G : Type*) [Magma G] (h : Equation2075 G) : Equation2054 G := λ x y => h x y x
@[equational_result]
theorem Equation2076_implies_Equation2053 (G : Type*) [Magma G] (h : Equation2076 G) : Equation2053 G := λ x y => h x y x
@[equational_result]
theorem Equation2078_implies_Equation2050 (G : Type*) [Magma G] (h : Equation2078 G) : Equation2050 G := λ x y => h x y x
@[equational_result]
theorem Equation2079_implies_Equation2051 (G : Type*) [Magma G] (h : Equation2079 G) : Equation2051 G := λ x y => h x y x
@[equational_result]
theorem Equation2080_implies_Equation2050 (G : Type*) [Magma G] (h : Equation2080 G) : Equation2050 G := λ x y => h x y x
@[equational_result]
theorem Equation2089_implies_Equation2087 (G : Type*) [Magma G] (h : Equation2089 G) : Equation2087 G := λ x y => h x y x
@[equational_result]
theorem Equation2092_implies_Equation2090 (G : Type*) [Magma G] (h : Equation2092 G) : Equation2090 G := λ x y => h x y x
@[equational_result]
theorem Equation2093_implies_Equation2087 (G : Type*) [Magma G] (h : Equation2093 G) : Equation2087 G := λ x y => h x y x
@[equational_result]
theorem Equation2094_implies_Equation2088 (G : Type*) [Magma G] (h : Equation2094 G) : Equation2088 G := λ x y => h x y x
@[equational_result]
theorem Equation2095_implies_Equation2087 (G : Type*) [Magma G] (h : Equation2095 G) : Equation2087 G := λ x y => h x y x
@[equational_result]
theorem Equation2099_implies_Equation2097 (G : Type*) [Magma G] (h : Equation2099 G) : Equation2097 G := λ x y => h x y x
@[equational_result]
theorem Equation2102_implies_Equation2100 (G : Type*) [Magma G] (h : Equation2102 G) : Equation2100 G := λ x y => h x y x
@[equational_result]
theorem Equation2103_implies_Equation2097 (G : Type*) [Magma G] (h : Equation2103 G) : Equation2097 G := λ x y => h x y x
@[equational_result]
theorem Equation2104_implies_Equation2098 (G : Type*) [Magma G] (h : Equation2104 G) : Equation2098 G := λ x y => h x y x
@[equational_result]
theorem Equation2105_implies_Equation2097 (G : Type*) [Magma G] (h : Equation2105 G) : Equation2097 G := λ x y => h x y x
@[equational_result]
theorem Equation2107_implies_Equation2087 (G : Type*) [Magma G] (h : Equation2107 G) : Equation2087 G := λ x y => h x y x
@[equational_result]
theorem Equation2108_implies_Equation2088 (G : Type*) [Magma G] (h : Equation2108 G) : Equation2088 G := λ x y => h x y x
@[equational_result]
theorem Equation2109_implies_Equation2087 (G : Type*) [Magma G] (h : Equation2109 G) : Equation2087 G := λ x y => h x y x
@[equational_result]
theorem Equation2111_implies_Equation2090 (G : Type*) [Magma G] (h : Equation2111 G) : Equation2090 G := λ x y => h x y x
@[equational_result]
theorem Equation2112_implies_Equation2091 (G : Type*) [Magma G] (h : Equation2112 G) : Equation2091 G := λ x y => h x y x
@[equational_result]
theorem Equation2113_implies_Equation2090 (G : Type*) [Magma G] (h : Equation2113 G) : Equation2090 G := λ x y => h x y x
@[equational_result]
theorem Equation2115_implies_Equation2087 (G : Type*) [Magma G] (h : Equation2115 G) : Equation2087 G := λ x y => h x y x
@[equational_result]
theorem Equation2116_implies_Equation2088 (G : Type*) [Magma G] (h : Equation2116 G) : Equation2088 G := λ x y => h x y x
@[equational_result]
theorem Equation2117_implies_Equation2087 (G : Type*) [Magma G] (h : Equation2117 G) : Equation2087 G := λ x y => h x y x
@[equational_result]
theorem Equation2126_implies_Equation2124 (G : Type*) [Magma G] (h : Equation2126 G) : Equation2124 G := λ x y => h x y x
@[equational_result]
theorem Equation2129_implies_Equation2127 (G : Type*) [Magma G] (h : Equation2129 G) : Equation2127 G := λ x y => h x y x
@[equational_result]
theorem Equation2130_implies_Equation2124 (G : Type*) [Magma G] (h : Equation2130 G) : Equation2124 G := λ x y => h x y x
@[equational_result]
theorem Equation2131_implies_Equation2125 (G : Type*) [Magma G] (h : Equation2131 G) : Equation2125 G := λ x y => h x y x
@[equational_result]
theorem Equation2132_implies_Equation2124 (G : Type*) [Magma G] (h : Equation2132 G) : Equation2124 G := λ x y => h x y x
@[equational_result]
theorem Equation2136_implies_Equation2134 (G : Type*) [Magma G] (h : Equation2136 G) : Equation2134 G := λ x y => h x y x
@[equational_result]
theorem Equation2139_implies_Equation2137 (G : Type*) [Magma G] (h : Equation2139 G) : Equation2137 G := λ x y => h x y x
@[equational_result]
theorem Equation2140_implies_Equation2134 (G : Type*) [Magma G] (h : Equation2140 G) : Equation2134 G := λ x y => h x y x
@[equational_result]
theorem Equation2141_implies_Equation2135 (G : Type*) [Magma G] (h : Equation2141 G) : Equation2135 G := λ x y => h x y x
@[equational_result]
theorem Equation2142_implies_Equation2134 (G : Type*) [Magma G] (h : Equation2142 G) : Equation2134 G := λ x y => h x y x
@[equational_result]
theorem Equation2144_implies_Equation2124 (G : Type*) [Magma G] (h : Equation2144 G) : Equation2124 G := λ x y => h x y x
@[equational_result]
theorem Equation2145_implies_Equation2125 (G : Type*) [Magma G] (h : Equation2145 G) : Equation2125 G := λ x y => h x y x
@[equational_result]
theorem Equation2146_implies_Equation2124 (G : Type*) [Magma G] (h : Equation2146 G) : Equation2124 G := λ x y => h x y x
@[equational_result]
theorem Equation2148_implies_Equation2127 (G : Type*) [Magma G] (h : Equation2148 G) : Equation2127 G := λ x y => h x y x
@[equational_result]
theorem Equation2149_implies_Equation2128 (G : Type*) [Magma G] (h : Equation2149 G) : Equation2128 G := λ x y => h x y x
@[equational_result]
theorem Equation2150_implies_Equation2127 (G : Type*) [Magma G] (h : Equation2150 G) : Equation2127 G := λ x y => h x y x
@[equational_result]
theorem Equation2152_implies_Equation2124 (G : Type*) [Magma G] (h : Equation2152 G) : Equation2124 G := λ x y => h x y x
@[equational_result]
theorem Equation2153_implies_Equation2125 (G : Type*) [Magma G] (h : Equation2153 G) : Equation2125 G := λ x y => h x y x
@[equational_result]
theorem Equation2154_implies_Equation2124 (G : Type*) [Magma G] (h : Equation2154 G) : Equation2124 G := λ x y => h x y x
@[equational_result]
theorem Equation2161_implies_Equation2087 (G : Type*) [Magma G] (h : Equation2161 G) : Equation2087 G := λ x y => h x y x
@[equational_result]
theorem Equation2162_implies_Equation2088 (G : Type*) [Magma G] (h : Equation2162 G) : Equation2088 G := λ x y => h x y x
@[equational_result]
theorem Equation2163_implies_Equation2087 (G : Type*) [Magma G] (h : Equation2163 G) : Equation2087 G := λ x y => h x y x
@[equational_result]
theorem Equation2165_implies_Equation2090 (G : Type*) [Magma G] (h : Equation2165 G) : Equation2090 G := λ x y => h x y x
@[equational_result]
theorem Equation2166_implies_Equation2091 (G : Type*) [Magma G] (h : Equation2166 G) : Equation2091 G := λ x y => h x y x
@[equational_result]
theorem Equation2167_implies_Equation2090 (G : Type*) [Magma G] (h : Equation2167 G) : Equation2090 G := λ x y => h x y x
@[equational_result]
theorem Equation2169_implies_Equation2087 (G : Type*) [Magma G] (h : Equation2169 G) : Equation2087 G := λ x y => h x y x
@[equational_result]
theorem Equation2170_implies_Equation2088 (G : Type*) [Magma G] (h : Equation2170 G) : Equation2088 G := λ x y => h x y x
@[equational_result]
theorem Equation2171_implies_Equation2087 (G : Type*) [Magma G] (h : Equation2171 G) : Equation2087 G := λ x y => h x y x
@[equational_result]
theorem Equation2178_implies_Equation2097 (G : Type*) [Magma G] (h : Equation2178 G) : Equation2097 G := λ x y => h x y x
@[equational_result]
theorem Equation2179_implies_Equation2098 (G : Type*) [Magma G] (h : Equation2179 G) : Equation2098 G := λ x y => h x y x
@[equational_result]
theorem Equation2180_implies_Equation2097 (G : Type*) [Magma G] (h : Equation2180 G) : Equation2097 G := λ x y => h x y x
@[equational_result]
theorem Equation2182_implies_Equation2100 (G : Type*) [Magma G] (h : Equation2182 G) : Equation2100 G := λ x y => h x y x
@[equational_result]
theorem Equation2183_implies_Equation2101 (G : Type*) [Magma G] (h : Equation2183 G) : Equation2101 G := λ x y => h x y x
@[equational_result]
theorem Equation2184_implies_Equation2100 (G : Type*) [Magma G] (h : Equation2184 G) : Equation2100 G := λ x y => h x y x
@[equational_result]
theorem Equation2186_implies_Equation2097 (G : Type*) [Magma G] (h : Equation2186 G) : Equation2097 G := λ x y => h x y x
@[equational_result]
theorem Equation2187_implies_Equation2098 (G : Type*) [Magma G] (h : Equation2187 G) : Equation2098 G := λ x y => h x y x
@[equational_result]
theorem Equation2188_implies_Equation2097 (G : Type*) [Magma G] (h : Equation2188 G) : Equation2097 G := λ x y => h x y x
@[equational_result]
theorem Equation2195_implies_Equation2087 (G : Type*) [Magma G] (h : Equation2195 G) : Equation2087 G := λ x y => h x y x
@[equational_result]
theorem Equation2196_implies_Equation2088 (G : Type*) [Magma G] (h : Equation2196 G) : Equation2088 G := λ x y => h x y x
@[equational_result]
theorem Equation2197_implies_Equation2087 (G : Type*) [Magma G] (h : Equation2197 G) : Equation2087 G := λ x y => h x y x
@[equational_result]
theorem Equation2199_implies_Equation2090 (G : Type*) [Magma G] (h : Equation2199 G) : Equation2090 G := λ x y => h x y x
@[equational_result]
theorem Equation2200_implies_Equation2091 (G : Type*) [Magma G] (h : Equation2200 G) : Equation2091 G := λ x y => h x y x
@[equational_result]
theorem Equation2201_implies_Equation2090 (G : Type*) [Magma G] (h : Equation2201 G) : Equation2090 G := λ x y => h x y x
@[equational_result]
theorem Equation2203_implies_Equation2087 (G : Type*) [Magma G] (h : Equation2203 G) : Equation2087 G := λ x y => h x y x
@[equational_result]
theorem Equation2204_implies_Equation2088 (G : Type*) [Magma G] (h : Equation2204 G) : Equation2088 G := λ x y => h x y x
@[equational_result]
theorem Equation2205_implies_Equation2087 (G : Type*) [Magma G] (h : Equation2205 G) : Equation2087 G := λ x y => h x y x
@[equational_result]
theorem Equation2242_implies_Equation2240 (G : Type*) [Magma G] (h : Equation2242 G) : Equation2240 G := λ x y => h x y x
@[equational_result]
theorem Equation2245_implies_Equation2243 (G : Type*) [Magma G] (h : Equation2245 G) : Equation2243 G := λ x y => h x y x
@[equational_result]
theorem Equation2248_implies_Equation2246 (G : Type*) [Magma G] (h : Equation2248 G) : Equation2246 G := λ x y => h x y x
@[equational_result]
theorem Equation2249_implies_Equation2243 (G : Type*) [Magma G] (h : Equation2249 G) : Equation2243 G := λ x y => h x y x
@[equational_result]
theorem Equation2250_implies_Equation2244 (G : Type*) [Magma G] (h : Equation2250 G) : Equation2244 G := λ x y => h x y x
@[equational_result]
theorem Equation2251_implies_Equation2243 (G : Type*) [Magma G] (h : Equation2251 G) : Equation2243 G := λ x y => h x y x
@[equational_result]
theorem Equation2255_implies_Equation2253 (G : Type*) [Magma G] (h : Equation2255 G) : Equation2253 G := λ x y => h x y x
@[equational_result]
theorem Equation2258_implies_Equation2256 (G : Type*) [Magma G] (h : Equation2258 G) : Equation2256 G := λ x y => h x y x
@[equational_result]
theorem Equation2259_implies_Equation2253 (G : Type*) [Magma G] (h : Equation2259 G) : Equation2253 G := λ x y => h x y x
@[equational_result]
theorem Equation2260_implies_Equation2254 (G : Type*) [Magma G] (h : Equation2260 G) : Equation2254 G := λ x y => h x y x
@[equational_result]
theorem Equation2261_implies_Equation2253 (G : Type*) [Magma G] (h : Equation2261 G) : Equation2253 G := λ x y => h x y x
@[equational_result]
theorem Equation2265_implies_Equation2263 (G : Type*) [Magma G] (h : Equation2265 G) : Equation2263 G := λ x y => h x y x
@[equational_result]
theorem Equation2268_implies_Equation2266 (G : Type*) [Magma G] (h : Equation2268 G) : Equation2266 G := λ x y => h x y x
@[equational_result]
theorem Equation2269_implies_Equation2263 (G : Type*) [Magma G] (h : Equation2269 G) : Equation2263 G := λ x y => h x y x
@[equational_result]
theorem Equation2270_implies_Equation2264 (G : Type*) [Magma G] (h : Equation2270 G) : Equation2264 G := λ x y => h x y x
@[equational_result]
theorem Equation2271_implies_Equation2263 (G : Type*) [Magma G] (h : Equation2271 G) : Equation2263 G := λ x y => h x y x
@[equational_result]
theorem Equation2273_implies_Equation2253 (G : Type*) [Magma G] (h : Equation2273 G) : Equation2253 G := λ x y => h x y x
@[equational_result]
theorem Equation2274_implies_Equation2254 (G : Type*) [Magma G] (h : Equation2274 G) : Equation2254 G := λ x y => h x y x
@[equational_result]
theorem Equation2275_implies_Equation2253 (G : Type*) [Magma G] (h : Equation2275 G) : Equation2253 G := λ x y => h x y x
@[equational_result]
theorem Equation2277_implies_Equation2256 (G : Type*) [Magma G] (h : Equation2277 G) : Equation2256 G := λ x y => h x y x
@[equational_result]
theorem Equation2278_implies_Equation2257 (G : Type*) [Magma G] (h : Equation2278 G) : Equation2257 G := λ x y => h x y x
@[equational_result]
theorem Equation2279_implies_Equation2256 (G : Type*) [Magma G] (h : Equation2279 G) : Equation2256 G := λ x y => h x y x
@[equational_result]
theorem Equation2281_implies_Equation2253 (G : Type*) [Magma G] (h : Equation2281 G) : Equation2253 G := λ x y => h x y x
@[equational_result]
theorem Equation2282_implies_Equation2254 (G : Type*) [Magma G] (h : Equation2282 G) : Equation2254 G := λ x y => h x y x
@[equational_result]
theorem Equation2283_implies_Equation2253 (G : Type*) [Magma G] (h : Equation2283 G) : Equation2253 G := λ x y => h x y x
@[equational_result]
theorem Equation2292_implies_Equation2290 (G : Type*) [Magma G] (h : Equation2292 G) : Equation2290 G := λ x y => h x y x
@[equational_result]
theorem Equation2295_implies_Equation2293 (G : Type*) [Magma G] (h : Equation2295 G) : Equation2293 G := λ x y => h x y x
@[equational_result]
theorem Equation2296_implies_Equation2290 (G : Type*) [Magma G] (h : Equation2296 G) : Equation2290 G := λ x y => h x y x
@[equational_result]
theorem Equation2297_implies_Equation2291 (G : Type*) [Magma G] (h : Equation2297 G) : Equation2291 G := λ x y => h x y x
@[equational_result]
theorem Equation2298_implies_Equation2290 (G : Type*) [Magma G] (h : Equation2298 G) : Equation2290 G := λ x y => h x y x
@[equational_result]
theorem Equation2302_implies_Equation2300 (G : Type*) [Magma G] (h : Equation2302 G) : Equation2300 G := λ x y => h x y x
@[equational_result]
theorem Equation2305_implies_Equation2303 (G : Type*) [Magma G] (h : Equation2305 G) : Equation2303 G := λ x y => h x y x
@[equational_result]
theorem Equation2306_implies_Equation2300 (G : Type*) [Magma G] (h : Equation2306 G) : Equation2300 G := λ x y => h x y x
@[equational_result]
theorem Equation2307_implies_Equation2301 (G : Type*) [Magma G] (h : Equation2307 G) : Equation2301 G := λ x y => h x y x
@[equational_result]
theorem Equation2308_implies_Equation2300 (G : Type*) [Magma G] (h : Equation2308 G) : Equation2300 G := λ x y => h x y x
@[equational_result]
theorem Equation2310_implies_Equation2290 (G : Type*) [Magma G] (h : Equation2310 G) : Equation2290 G := λ x y => h x y x
@[equational_result]
theorem Equation2311_implies_Equation2291 (G : Type*) [Magma G] (h : Equation2311 G) : Equation2291 G := λ x y => h x y x
@[equational_result]
theorem Equation2312_implies_Equation2290 (G : Type*) [Magma G] (h : Equation2312 G) : Equation2290 G := λ x y => h x y x
@[equational_result]
theorem Equation2314_implies_Equation2293 (G : Type*) [Magma G] (h : Equation2314 G) : Equation2293 G := λ x y => h x y x
@[equational_result]
theorem Equation2315_implies_Equation2294 (G : Type*) [Magma G] (h : Equation2315 G) : Equation2294 G := λ x y => h x y x
@[equational_result]
theorem Equation2316_implies_Equation2293 (G : Type*) [Magma G] (h : Equation2316 G) : Equation2293 G := λ x y => h x y x
@[equational_result]
theorem Equation2318_implies_Equation2290 (G : Type*) [Magma G] (h : Equation2318 G) : Equation2290 G := λ x y => h x y x
@[equational_result]
theorem Equation2319_implies_Equation2291 (G : Type*) [Magma G] (h : Equation2319 G) : Equation2291 G := λ x y => h x y x
@[equational_result]
theorem Equation2320_implies_Equation2290 (G : Type*) [Magma G] (h : Equation2320 G) : Equation2290 G := λ x y => h x y x
@[equational_result]
theorem Equation2329_implies_Equation2327 (G : Type*) [Magma G] (h : Equation2329 G) : Equation2327 G := λ x y => h x y x
@[equational_result]
theorem Equation2332_implies_Equation2330 (G : Type*) [Magma G] (h : Equation2332 G) : Equation2330 G := λ x y => h x y x
@[equational_result]
theorem Equation2333_implies_Equation2327 (G : Type*) [Magma G] (h : Equation2333 G) : Equation2327 G := λ x y => h x y x
@[equational_result]
theorem Equation2334_implies_Equation2328 (G : Type*) [Magma G] (h : Equation2334 G) : Equation2328 G := λ x y => h x y x
@[equational_result]
theorem Equation2335_implies_Equation2327 (G : Type*) [Magma G] (h : Equation2335 G) : Equation2327 G := λ x y => h x y x
@[equational_result]
theorem Equation2339_implies_Equation2337 (G : Type*) [Magma G] (h : Equation2339 G) : Equation2337 G := λ x y => h x y x
@[equational_result]
theorem Equation2342_implies_Equation2340 (G : Type*) [Magma G] (h : Equation2342 G) : Equation2340 G := λ x y => h x y x
@[equational_result]
theorem Equation2343_implies_Equation2337 (G : Type*) [Magma G] (h : Equation2343 G) : Equation2337 G := λ x y => h x y x
@[equational_result]
theorem Equation2344_implies_Equation2338 (G : Type*) [Magma G] (h : Equation2344 G) : Equation2338 G := λ x y => h x y x
@[equational_result]
theorem Equation2345_implies_Equation2337 (G : Type*) [Magma G] (h : Equation2345 G) : Equation2337 G := λ x y => h x y x
@[equational_result]
theorem Equation2347_implies_Equation2327 (G : Type*) [Magma G] (h : Equation2347 G) : Equation2327 G := λ x y => h x y x
@[equational_result]
theorem Equation2348_implies_Equation2328 (G : Type*) [Magma G] (h : Equation2348 G) : Equation2328 G := λ x y => h x y x
@[equational_result]
theorem Equation2349_implies_Equation2327 (G : Type*) [Magma G] (h : Equation2349 G) : Equation2327 G := λ x y => h x y x
@[equational_result]
theorem Equation2351_implies_Equation2330 (G : Type*) [Magma G] (h : Equation2351 G) : Equation2330 G := λ x y => h x y x
@[equational_result]
theorem Equation2352_implies_Equation2331 (G : Type*) [Magma G] (h : Equation2352 G) : Equation2331 G := λ x y => h x y x
@[equational_result]
theorem Equation2353_implies_Equation2330 (G : Type*) [Magma G] (h : Equation2353 G) : Equation2330 G := λ x y => h x y x
@[equational_result]
theorem Equation2355_implies_Equation2327 (G : Type*) [Magma G] (h : Equation2355 G) : Equation2327 G := λ x y => h x y x
@[equational_result]
theorem Equation2356_implies_Equation2328 (G : Type*) [Magma G] (h : Equation2356 G) : Equation2328 G := λ x y => h x y x
@[equational_result]
theorem Equation2357_implies_Equation2327 (G : Type*) [Magma G] (h : Equation2357 G) : Equation2327 G := λ x y => h x y x
@[equational_result]
theorem Equation2364_implies_Equation2290 (G : Type*) [Magma G] (h : Equation2364 G) : Equation2290 G := λ x y => h x y x
@[equational_result]
theorem Equation2365_implies_Equation2291 (G : Type*) [Magma G] (h : Equation2365 G) : Equation2291 G := λ x y => h x y x
@[equational_result]
theorem Equation2366_implies_Equation2290 (G : Type*) [Magma G] (h : Equation2366 G) : Equation2290 G := λ x y => h x y x
@[equational_result]
theorem Equation2368_implies_Equation2293 (G : Type*) [Magma G] (h : Equation2368 G) : Equation2293 G := λ x y => h x y x
@[equational_result]
theorem Equation2369_implies_Equation2294 (G : Type*) [Magma G] (h : Equation2369 G) : Equation2294 G := λ x y => h x y x
@[equational_result]
theorem Equation2370_implies_Equation2293 (G : Type*) [Magma G] (h : Equation2370 G) : Equation2293 G := λ x y => h x y x
@[equational_result]
theorem Equation2372_implies_Equation2290 (G : Type*) [Magma G] (h : Equation2372 G) : Equation2290 G := λ x y => h x y x
@[equational_result]
theorem Equation2373_implies_Equation2291 (G : Type*) [Magma G] (h : Equation2373 G) : Equation2291 G := λ x y => h x y x
@[equational_result]
theorem Equation2374_implies_Equation2290 (G : Type*) [Magma G] (h : Equation2374 G) : Equation2290 G := λ x y => h x y x
@[equational_result]
theorem Equation2381_implies_Equation2300 (G : Type*) [Magma G] (h : Equation2381 G) : Equation2300 G := λ x y => h x y x
@[equational_result]
theorem Equation2382_implies_Equation2301 (G : Type*) [Magma G] (h : Equation2382 G) : Equation2301 G := λ x y => h x y x
@[equational_result]
theorem Equation2383_implies_Equation2300 (G : Type*) [Magma G] (h : Equation2383 G) : Equation2300 G := λ x y => h x y x
@[equational_result]
theorem Equation2385_implies_Equation2303 (G : Type*) [Magma G] (h : Equation2385 G) : Equation2303 G := λ x y => h x y x
@[equational_result]
theorem Equation2386_implies_Equation2304 (G : Type*) [Magma G] (h : Equation2386 G) : Equation2304 G := λ x y => h x y x
@[equational_result]
theorem Equation2387_implies_Equation2303 (G : Type*) [Magma G] (h : Equation2387 G) : Equation2303 G := λ x y => h x y x
@[equational_result]
theorem Equation2389_implies_Equation2300 (G : Type*) [Magma G] (h : Equation2389 G) : Equation2300 G := λ x y => h x y x
@[equational_result]
theorem Equation2390_implies_Equation2301 (G : Type*) [Magma G] (h : Equation2390 G) : Equation2301 G := λ x y => h x y x
@[equational_result]
theorem Equation2391_implies_Equation2300 (G : Type*) [Magma G] (h : Equation2391 G) : Equation2300 G := λ x y => h x y x
@[equational_result]
theorem Equation2398_implies_Equation2290 (G : Type*) [Magma G] (h : Equation2398 G) : Equation2290 G := λ x y => h x y x
@[equational_result]
theorem Equation2399_implies_Equation2291 (G : Type*) [Magma G] (h : Equation2399 G) : Equation2291 G := λ x y => h x y x
@[equational_result]
theorem Equation2400_implies_Equation2290 (G : Type*) [Magma G] (h : Equation2400 G) : Equation2290 G := λ x y => h x y x
@[equational_result]
theorem Equation2402_implies_Equation2293 (G : Type*) [Magma G] (h : Equation2402 G) : Equation2293 G := λ x y => h x y x
@[equational_result]
theorem Equation2403_implies_Equation2294 (G : Type*) [Magma G] (h : Equation2403 G) : Equation2294 G := λ x y => h x y x
@[equational_result]
theorem Equation2404_implies_Equation2293 (G : Type*) [Magma G] (h : Equation2404 G) : Equation2293 G := λ x y => h x y x
@[equational_result]
theorem Equation2406_implies_Equation2290 (G : Type*) [Magma G] (h : Equation2406 G) : Equation2290 G := λ x y => h x y x
@[equational_result]
theorem Equation2407_implies_Equation2291 (G : Type*) [Magma G] (h : Equation2407 G) : Equation2291 G := λ x y => h x y x
@[equational_result]
theorem Equation2408_implies_Equation2290 (G : Type*) [Magma G] (h : Equation2408 G) : Equation2290 G := λ x y => h x y x
@[equational_result]
theorem Equation2445_implies_Equation2443 (G : Type*) [Magma G] (h : Equation2445 G) : Equation2443 G := λ x y => h x y x
@[equational_result]
theorem Equation2448_implies_Equation2446 (G : Type*) [Magma G] (h : Equation2448 G) : Equation2446 G := λ x y => h x y x
@[equational_result]
theorem Equation2451_implies_Equation2449 (G : Type*) [Magma G] (h : Equation2451 G) : Equation2449 G := λ x y => h x y x
@[equational_result]
theorem Equation2452_implies_Equation2446 (G : Type*) [Magma G] (h : Equation2452 G) : Equation2446 G := λ x y => h x y x
@[equational_result]
theorem Equation2453_implies_Equation2447 (G : Type*) [Magma G] (h : Equation2453 G) : Equation2447 G := λ x y => h x y x
@[equational_result]
theorem Equation2454_implies_Equation2446 (G : Type*) [Magma G] (h : Equation2454 G) : Equation2446 G := λ x y => h x y x
@[equational_result]
theorem Equation2458_implies_Equation2456 (G : Type*) [Magma G] (h : Equation2458 G) : Equation2456 G := λ x y => h x y x
@[equational_result]
theorem Equation2461_implies_Equation2459 (G : Type*) [Magma G] (h : Equation2461 G) : Equation2459 G := λ x y => h x y x
@[equational_result]
theorem Equation2462_implies_Equation2456 (G : Type*) [Magma G] (h : Equation2462 G) : Equation2456 G := λ x y => h x y x
@[equational_result]
theorem Equation2463_implies_Equation2457 (G : Type*) [Magma G] (h : Equation2463 G) : Equation2457 G := λ x y => h x y x
@[equational_result]
theorem Equation2464_implies_Equation2456 (G : Type*) [Magma G] (h : Equation2464 G) : Equation2456 G := λ x y => h x y x
@[equational_result]
theorem Equation2468_implies_Equation2466 (G : Type*) [Magma G] (h : Equation2468 G) : Equation2466 G := λ x y => h x y x
@[equational_result]
theorem Equation2471_implies_Equation2469 (G : Type*) [Magma G] (h : Equation2471 G) : Equation2469 G := λ x y => h x y x
@[equational_result]
theorem Equation2472_implies_Equation2466 (G : Type*) [Magma G] (h : Equation2472 G) : Equation2466 G := λ x y => h x y x
@[equational_result]
theorem Equation2473_implies_Equation2467 (G : Type*) [Magma G] (h : Equation2473 G) : Equation2467 G := λ x y => h x y x
@[equational_result]
theorem Equation2474_implies_Equation2466 (G : Type*) [Magma G] (h : Equation2474 G) : Equation2466 G := λ x y => h x y x
@[equational_result]
theorem Equation2476_implies_Equation2456 (G : Type*) [Magma G] (h : Equation2476 G) : Equation2456 G := λ x y => h x y x
@[equational_result]
theorem Equation2477_implies_Equation2457 (G : Type*) [Magma G] (h : Equation2477 G) : Equation2457 G := λ x y => h x y x
@[equational_result]
theorem Equation2478_implies_Equation2456 (G : Type*) [Magma G] (h : Equation2478 G) : Equation2456 G := λ x y => h x y x
@[equational_result]
theorem Equation2480_implies_Equation2459 (G : Type*) [Magma G] (h : Equation2480 G) : Equation2459 G := λ x y => h x y x
@[equational_result]
theorem Equation2481_implies_Equation2460 (G : Type*) [Magma G] (h : Equation2481 G) : Equation2460 G := λ x y => h x y x
@[equational_result]
theorem Equation2482_implies_Equation2459 (G : Type*) [Magma G] (h : Equation2482 G) : Equation2459 G := λ x y => h x y x
@[equational_result]
theorem Equation2484_implies_Equation2456 (G : Type*) [Magma G] (h : Equation2484 G) : Equation2456 G := λ x y => h x y x
@[equational_result]
theorem Equation2485_implies_Equation2457 (G : Type*) [Magma G] (h : Equation2485 G) : Equation2457 G := λ x y => h x y x
@[equational_result]
theorem Equation2486_implies_Equation2456 (G : Type*) [Magma G] (h : Equation2486 G) : Equation2456 G := λ x y => h x y x
@[equational_result]
theorem Equation2495_implies_Equation2493 (G : Type*) [Magma G] (h : Equation2495 G) : Equation2493 G := λ x y => h x y x
@[equational_result]
theorem Equation2498_implies_Equation2496 (G : Type*) [Magma G] (h : Equation2498 G) : Equation2496 G := λ x y => h x y x
@[equational_result]
theorem Equation2499_implies_Equation2493 (G : Type*) [Magma G] (h : Equation2499 G) : Equation2493 G := λ x y => h x y x
@[equational_result]
theorem Equation2500_implies_Equation2494 (G : Type*) [Magma G] (h : Equation2500 G) : Equation2494 G := λ x y => h x y x
@[equational_result]
theorem Equation2501_implies_Equation2493 (G : Type*) [Magma G] (h : Equation2501 G) : Equation2493 G := λ x y => h x y x
@[equational_result]
theorem Equation2505_implies_Equation2503 (G : Type*) [Magma G] (h : Equation2505 G) : Equation2503 G := λ x y => h x y x
@[equational_result]
theorem Equation2508_implies_Equation2506 (G : Type*) [Magma G] (h : Equation2508 G) : Equation2506 G := λ x y => h x y x
@[equational_result]
theorem Equation2509_implies_Equation2503 (G : Type*) [Magma G] (h : Equation2509 G) : Equation2503 G := λ x y => h x y x
@[equational_result]
theorem Equation2510_implies_Equation2504 (G : Type*) [Magma G] (h : Equation2510 G) : Equation2504 G := λ x y => h x y x
@[equational_result]
theorem Equation2511_implies_Equation2503 (G : Type*) [Magma G] (h : Equation2511 G) : Equation2503 G := λ x y => h x y x
@[equational_result]
theorem Equation2513_implies_Equation2493 (G : Type*) [Magma G] (h : Equation2513 G) : Equation2493 G := λ x y => h x y x
@[equational_result]
theorem Equation2514_implies_Equation2494 (G : Type*) [Magma G] (h : Equation2514 G) : Equation2494 G := λ x y => h x y x
@[equational_result]
theorem Equation2515_implies_Equation2493 (G : Type*) [Magma G] (h : Equation2515 G) : Equation2493 G := λ x y => h x y x
@[equational_result]
theorem Equation2517_implies_Equation2496 (G : Type*) [Magma G] (h : Equation2517 G) : Equation2496 G := λ x y => h x y x
@[equational_result]
theorem Equation2518_implies_Equation2497 (G : Type*) [Magma G] (h : Equation2518 G) : Equation2497 G := λ x y => h x y x
@[equational_result]
theorem Equation2519_implies_Equation2496 (G : Type*) [Magma G] (h : Equation2519 G) : Equation2496 G := λ x y => h x y x
@[equational_result]
theorem Equation2521_implies_Equation2493 (G : Type*) [Magma G] (h : Equation2521 G) : Equation2493 G := λ x y => h x y x
@[equational_result]
theorem Equation2522_implies_Equation2494 (G : Type*) [Magma G] (h : Equation2522 G) : Equation2494 G := λ x y => h x y x
@[equational_result]
theorem Equation2523_implies_Equation2493 (G : Type*) [Magma G] (h : Equation2523 G) : Equation2493 G := λ x y => h x y x
@[equational_result]
theorem Equation2532_implies_Equation2530 (G : Type*) [Magma G] (h : Equation2532 G) : Equation2530 G := λ x y => h x y x
@[equational_result]
theorem Equation2535_implies_Equation2533 (G : Type*) [Magma G] (h : Equation2535 G) : Equation2533 G := λ x y => h x y x
@[equational_result]
theorem Equation2536_implies_Equation2530 (G : Type*) [Magma G] (h : Equation2536 G) : Equation2530 G := λ x y => h x y x
@[equational_result]
theorem Equation2537_implies_Equation2531 (G : Type*) [Magma G] (h : Equation2537 G) : Equation2531 G := λ x y => h x y x
@[equational_result]
theorem Equation2538_implies_Equation2530 (G : Type*) [Magma G] (h : Equation2538 G) : Equation2530 G := λ x y => h x y x
@[equational_result]
theorem Equation2542_implies_Equation2540 (G : Type*) [Magma G] (h : Equation2542 G) : Equation2540 G := λ x y => h x y x
@[equational_result]
theorem Equation2545_implies_Equation2543 (G : Type*) [Magma G] (h : Equation2545 G) : Equation2543 G := λ x y => h x y x
@[equational_result]
theorem Equation2546_implies_Equation2540 (G : Type*) [Magma G] (h : Equation2546 G) : Equation2540 G := λ x y => h x y x
@[equational_result]
theorem Equation2547_implies_Equation2541 (G : Type*) [Magma G] (h : Equation2547 G) : Equation2541 G := λ x y => h x y x
@[equational_result]
theorem Equation2548_implies_Equation2540 (G : Type*) [Magma G] (h : Equation2548 G) : Equation2540 G := λ x y => h x y x
@[equational_result]
theorem Equation2550_implies_Equation2530 (G : Type*) [Magma G] (h : Equation2550 G) : Equation2530 G := λ x y => h x y x
@[equational_result]
theorem Equation2551_implies_Equation2531 (G : Type*) [Magma G] (h : Equation2551 G) : Equation2531 G := λ x y => h x y x
@[equational_result]
theorem Equation2552_implies_Equation2530 (G : Type*) [Magma G] (h : Equation2552 G) : Equation2530 G := λ x y => h x y x
@[equational_result]
theorem Equation2554_implies_Equation2533 (G : Type*) [Magma G] (h : Equation2554 G) : Equation2533 G := λ x y => h x y x
@[equational_result]
theorem Equation2555_implies_Equation2534 (G : Type*) [Magma G] (h : Equation2555 G) : Equation2534 G := λ x y => h x y x
@[equational_result]
theorem Equation2556_implies_Equation2533 (G : Type*) [Magma G] (h : Equation2556 G) : Equation2533 G := λ x y => h x y x
@[equational_result]
theorem Equation2558_implies_Equation2530 (G : Type*) [Magma G] (h : Equation2558 G) : Equation2530 G := λ x y => h x y x
@[equational_result]
theorem Equation2559_implies_Equation2531 (G : Type*) [Magma G] (h : Equation2559 G) : Equation2531 G := λ x y => h x y x
@[equational_result]
theorem Equation2560_implies_Equation2530 (G : Type*) [Magma G] (h : Equation2560 G) : Equation2530 G := λ x y => h x y x
@[equational_result]
theorem Equation2567_implies_Equation2493 (G : Type*) [Magma G] (h : Equation2567 G) : Equation2493 G := λ x y => h x y x
@[equational_result]
theorem Equation2568_implies_Equation2494 (G : Type*) [Magma G] (h : Equation2568 G) : Equation2494 G := λ x y => h x y x
@[equational_result]
theorem Equation2569_implies_Equation2493 (G : Type*) [Magma G] (h : Equation2569 G) : Equation2493 G := λ x y => h x y x
@[equational_result]
theorem Equation2571_implies_Equation2496 (G : Type*) [Magma G] (h : Equation2571 G) : Equation2496 G := λ x y => h x y x
@[equational_result]
theorem Equation2572_implies_Equation2497 (G : Type*) [Magma G] (h : Equation2572 G) : Equation2497 G := λ x y => h x y x
@[equational_result]
theorem Equation2573_implies_Equation2496 (G : Type*) [Magma G] (h : Equation2573 G) : Equation2496 G := λ x y => h x y x
@[equational_result]
theorem Equation2575_implies_Equation2493 (G : Type*) [Magma G] (h : Equation2575 G) : Equation2493 G := λ x y => h x y x
@[equational_result]
theorem Equation2576_implies_Equation2494 (G : Type*) [Magma G] (h : Equation2576 G) : Equation2494 G := λ x y => h x y x
@[equational_result]
theorem Equation2577_implies_Equation2493 (G : Type*) [Magma G] (h : Equation2577 G) : Equation2493 G := λ x y => h x y x
@[equational_result]
theorem Equation2584_implies_Equation2503 (G : Type*) [Magma G] (h : Equation2584 G) : Equation2503 G := λ x y => h x y x
@[equational_result]
theorem Equation2585_implies_Equation2504 (G : Type*) [Magma G] (h : Equation2585 G) : Equation2504 G := λ x y => h x y x
@[equational_result]
theorem Equation2586_implies_Equation2503 (G : Type*) [Magma G] (h : Equation2586 G) : Equation2503 G := λ x y => h x y x
@[equational_result]
theorem Equation2588_implies_Equation2506 (G : Type*) [Magma G] (h : Equation2588 G) : Equation2506 G := λ x y => h x y x
@[equational_result]
theorem Equation2589_implies_Equation2507 (G : Type*) [Magma G] (h : Equation2589 G) : Equation2507 G := λ x y => h x y x
@[equational_result]
theorem Equation2590_implies_Equation2506 (G : Type*) [Magma G] (h : Equation2590 G) : Equation2506 G := λ x y => h x y x
@[equational_result]
theorem Equation2592_implies_Equation2503 (G : Type*) [Magma G] (h : Equation2592 G) : Equation2503 G := λ x y => h x y x
@[equational_result]
theorem Equation2593_implies_Equation2504 (G : Type*) [Magma G] (h : Equation2593 G) : Equation2504 G := λ x y => h x y x
@[equational_result]
theorem Equation2594_implies_Equation2503 (G : Type*) [Magma G] (h : Equation2594 G) : Equation2503 G := λ x y => h x y x
@[equational_result]
theorem Equation2601_implies_Equation2493 (G : Type*) [Magma G] (h : Equation2601 G) : Equation2493 G := λ x y => h x y x
@[equational_result]
theorem Equation2602_implies_Equation2494 (G : Type*) [Magma G] (h : Equation2602 G) : Equation2494 G := λ x y => h x y x
@[equational_result]
theorem Equation2603_implies_Equation2493 (G : Type*) [Magma G] (h : Equation2603 G) : Equation2493 G := λ x y => h x y x
@[equational_result]
theorem Equation2605_implies_Equation2496 (G : Type*) [Magma G] (h : Equation2605 G) : Equation2496 G := λ x y => h x y x
@[equational_result]
theorem Equation2606_implies_Equation2497 (G : Type*) [Magma G] (h : Equation2606 G) : Equation2497 G := λ x y => h x y x
@[equational_result]
theorem Equation2607_implies_Equation2496 (G : Type*) [Magma G] (h : Equation2607 G) : Equation2496 G := λ x y => h x y x
@[equational_result]
theorem Equation2609_implies_Equation2493 (G : Type*) [Magma G] (h : Equation2609 G) : Equation2493 G := λ x y => h x y x
@[equational_result]
theorem Equation2610_implies_Equation2494 (G : Type*) [Magma G] (h : Equation2610 G) : Equation2494 G := λ x y => h x y x
@[equational_result]
theorem Equation2611_implies_Equation2493 (G : Type*) [Magma G] (h : Equation2611 G) : Equation2493 G := λ x y => h x y x
@[equational_result]
theorem Equation2648_implies_Equation2646 (G : Type*) [Magma G] (h : Equation2648 G) : Equation2646 G := λ x y => h x y x
@[equational_result]
theorem Equation2651_implies_Equation2649 (G : Type*) [Magma G] (h : Equation2651 G) : Equation2649 G := λ x y => h x y x
@[equational_result]
theorem Equation2654_implies_Equation2652 (G : Type*) [Magma G] (h : Equation2654 G) : Equation2652 G := λ x y => h x y x
@[equational_result]
theorem Equation2655_implies_Equation2649 (G : Type*) [Magma G] (h : Equation2655 G) : Equation2649 G := λ x y => h x y x
@[equational_result]
theorem Equation2656_implies_Equation2650 (G : Type*) [Magma G] (h : Equation2656 G) : Equation2650 G := λ x y => h x y x
@[equational_result]
theorem Equation2657_implies_Equation2649 (G : Type*) [Magma G] (h : Equation2657 G) : Equation2649 G := λ x y => h x y x
@[equational_result]
theorem Equation2661_implies_Equation2659 (G : Type*) [Magma G] (h : Equation2661 G) : Equation2659 G := λ x y => h x y x
@[equational_result]
theorem Equation2664_implies_Equation2662 (G : Type*) [Magma G] (h : Equation2664 G) : Equation2662 G := λ x y => h x y x
@[equational_result]
theorem Equation2665_implies_Equation2659 (G : Type*) [Magma G] (h : Equation2665 G) : Equation2659 G := λ x y => h x y x
@[equational_result]
theorem Equation2666_implies_Equation2660 (G : Type*) [Magma G] (h : Equation2666 G) : Equation2660 G := λ x y => h x y x
@[equational_result]
theorem Equation2667_implies_Equation2659 (G : Type*) [Magma G] (h : Equation2667 G) : Equation2659 G := λ x y => h x y x
@[equational_result]
theorem Equation2671_implies_Equation2669 (G : Type*) [Magma G] (h : Equation2671 G) : Equation2669 G := λ x y => h x y x
@[equational_result]
theorem Equation2674_implies_Equation2672 (G : Type*) [Magma G] (h : Equation2674 G) : Equation2672 G := λ x y => h x y x
@[equational_result]
theorem Equation2675_implies_Equation2669 (G : Type*) [Magma G] (h : Equation2675 G) : Equation2669 G := λ x y => h x y x
@[equational_result]
theorem Equation2676_implies_Equation2670 (G : Type*) [Magma G] (h : Equation2676 G) : Equation2670 G := λ x y => h x y x
@[equational_result]
theorem Equation2677_implies_Equation2669 (G : Type*) [Magma G] (h : Equation2677 G) : Equation2669 G := λ x y => h x y x
@[equational_result]
theorem Equation2679_implies_Equation2659 (G : Type*) [Magma G] (h : Equation2679 G) : Equation2659 G := λ x y => h x y x
@[equational_result]
theorem Equation2680_implies_Equation2660 (G : Type*) [Magma G] (h : Equation2680 G) : Equation2660 G := λ x y => h x y x
@[equational_result]
theorem Equation2681_implies_Equation2659 (G : Type*) [Magma G] (h : Equation2681 G) : Equation2659 G := λ x y => h x y x
@[equational_result]
theorem Equation2683_implies_Equation2662 (G : Type*) [Magma G] (h : Equation2683 G) : Equation2662 G := λ x y => h x y x
@[equational_result]
theorem Equation2684_implies_Equation2663 (G : Type*) [Magma G] (h : Equation2684 G) : Equation2663 G := λ x y => h x y x
@[equational_result]
theorem Equation2685_implies_Equation2662 (G : Type*) [Magma G] (h : Equation2685 G) : Equation2662 G := λ x y => h x y x
@[equational_result]
theorem Equation2687_implies_Equation2659 (G : Type*) [Magma G] (h : Equation2687 G) : Equation2659 G := λ x y => h x y x
@[equational_result]
theorem Equation2688_implies_Equation2660 (G : Type*) [Magma G] (h : Equation2688 G) : Equation2660 G := λ x y => h x y x
@[equational_result]
theorem Equation2689_implies_Equation2659 (G : Type*) [Magma G] (h : Equation2689 G) : Equation2659 G := λ x y => h x y x
@[equational_result]
theorem Equation2698_implies_Equation2696 (G : Type*) [Magma G] (h : Equation2698 G) : Equation2696 G := λ x y => h x y x
@[equational_result]
theorem Equation2701_implies_Equation2699 (G : Type*) [Magma G] (h : Equation2701 G) : Equation2699 G := λ x y => h x y x
@[equational_result]
theorem Equation2702_implies_Equation2696 (G : Type*) [Magma G] (h : Equation2702 G) : Equation2696 G := λ x y => h x y x
@[equational_result]
theorem Equation2703_implies_Equation2697 (G : Type*) [Magma G] (h : Equation2703 G) : Equation2697 G := λ x y => h x y x
@[equational_result]
theorem Equation2704_implies_Equation2696 (G : Type*) [Magma G] (h : Equation2704 G) : Equation2696 G := λ x y => h x y x
@[equational_result]
theorem Equation2708_implies_Equation2706 (G : Type*) [Magma G] (h : Equation2708 G) : Equation2706 G := λ x y => h x y x
@[equational_result]
theorem Equation2711_implies_Equation2709 (G : Type*) [Magma G] (h : Equation2711 G) : Equation2709 G := λ x y => h x y x
@[equational_result]
theorem Equation2712_implies_Equation2706 (G : Type*) [Magma G] (h : Equation2712 G) : Equation2706 G := λ x y => h x y x
@[equational_result]
theorem Equation2713_implies_Equation2707 (G : Type*) [Magma G] (h : Equation2713 G) : Equation2707 G := λ x y => h x y x
@[equational_result]
theorem Equation2714_implies_Equation2706 (G : Type*) [Magma G] (h : Equation2714 G) : Equation2706 G := λ x y => h x y x
@[equational_result]
theorem Equation2716_implies_Equation2696 (G : Type*) [Magma G] (h : Equation2716 G) : Equation2696 G := λ x y => h x y x
@[equational_result]
theorem Equation2717_implies_Equation2697 (G : Type*) [Magma G] (h : Equation2717 G) : Equation2697 G := λ x y => h x y x
@[equational_result]
theorem Equation2718_implies_Equation2696 (G : Type*) [Magma G] (h : Equation2718 G) : Equation2696 G := λ x y => h x y x
@[equational_result]
theorem Equation2720_implies_Equation2699 (G : Type*) [Magma G] (h : Equation2720 G) : Equation2699 G := λ x y => h x y x
@[equational_result]
theorem Equation2721_implies_Equation2700 (G : Type*) [Magma G] (h : Equation2721 G) : Equation2700 G := λ x y => h x y x
@[equational_result]
theorem Equation2722_implies_Equation2699 (G : Type*) [Magma G] (h : Equation2722 G) : Equation2699 G := λ x y => h x y x
@[equational_result]
theorem Equation2724_implies_Equation2696 (G : Type*) [Magma G] (h : Equation2724 G) : Equation2696 G := λ x y => h x y x
@[equational_result]
theorem Equation2725_implies_Equation2697 (G : Type*) [Magma G] (h : Equation2725 G) : Equation2697 G := λ x y => h x y x
@[equational_result]
theorem Equation2726_implies_Equation2696 (G : Type*) [Magma G] (h : Equation2726 G) : Equation2696 G := λ x y => h x y x
@[equational_result]
theorem Equation2735_implies_Equation2733 (G : Type*) [Magma G] (h : Equation2735 G) : Equation2733 G := λ x y => h x y x
@[equational_result]
theorem Equation2738_implies_Equation2736 (G : Type*) [Magma G] (h : Equation2738 G) : Equation2736 G := λ x y => h x y x
@[equational_result]
theorem Equation2739_implies_Equation2733 (G : Type*) [Magma G] (h : Equation2739 G) : Equation2733 G := λ x y => h x y x
@[equational_result]
theorem Equation2740_implies_Equation2734 (G : Type*) [Magma G] (h : Equation2740 G) : Equation2734 G := λ x y => h x y x
@[equational_result]
theorem Equation2741_implies_Equation2733 (G : Type*) [Magma G] (h : Equation2741 G) : Equation2733 G := λ x y => h x y x
@[equational_result]
theorem Equation2745_implies_Equation2743 (G : Type*) [Magma G] (h : Equation2745 G) : Equation2743 G := λ x y => h x y x
@[equational_result]
theorem Equation2748_implies_Equation2746 (G : Type*) [Magma G] (h : Equation2748 G) : Equation2746 G := λ x y => h x y x
@[equational_result]
theorem Equation2749_implies_Equation2743 (G : Type*) [Magma G] (h : Equation2749 G) : Equation2743 G := λ x y => h x y x
@[equational_result]
theorem Equation2750_implies_Equation2744 (G : Type*) [Magma G] (h : Equation2750 G) : Equation2744 G := λ x y => h x y x
@[equational_result]
theorem Equation2751_implies_Equation2743 (G : Type*) [Magma G] (h : Equation2751 G) : Equation2743 G := λ x y => h x y x
@[equational_result]
theorem Equation2753_implies_Equation2733 (G : Type*) [Magma G] (h : Equation2753 G) : Equation2733 G := λ x y => h x y x
@[equational_result]
theorem Equation2754_implies_Equation2734 (G : Type*) [Magma G] (h : Equation2754 G) : Equation2734 G := λ x y => h x y x
@[equational_result]
theorem Equation2755_implies_Equation2733 (G : Type*) [Magma G] (h : Equation2755 G) : Equation2733 G := λ x y => h x y x
@[equational_result]
theorem Equation2757_implies_Equation2736 (G : Type*) [Magma G] (h : Equation2757 G) : Equation2736 G := λ x y => h x y x
@[equational_result]
theorem Equation2758_implies_Equation2737 (G : Type*) [Magma G] (h : Equation2758 G) : Equation2737 G := λ x y => h x y x
@[equational_result]
theorem Equation2759_implies_Equation2736 (G : Type*) [Magma G] (h : Equation2759 G) : Equation2736 G := λ x y => h x y x
@[equational_result]
theorem Equation2761_implies_Equation2733 (G : Type*) [Magma G] (h : Equation2761 G) : Equation2733 G := λ x y => h x y x
@[equational_result]
theorem Equation2762_implies_Equation2734 (G : Type*) [Magma G] (h : Equation2762 G) : Equation2734 G := λ x y => h x y x
@[equational_result]
theorem Equation2763_implies_Equation2733 (G : Type*) [Magma G] (h : Equation2763 G) : Equation2733 G := λ x y => h x y x
@[equational_result]
theorem Equation2770_implies_Equation2696 (G : Type*) [Magma G] (h : Equation2770 G) : Equation2696 G := λ x y => h x y x
@[equational_result]
theorem Equation2771_implies_Equation2697 (G : Type*) [Magma G] (h : Equation2771 G) : Equation2697 G := λ x y => h x y x
@[equational_result]
theorem Equation2772_implies_Equation2696 (G : Type*) [Magma G] (h : Equation2772 G) : Equation2696 G := λ x y => h x y x
@[equational_result]
theorem Equation2774_implies_Equation2699 (G : Type*) [Magma G] (h : Equation2774 G) : Equation2699 G := λ x y => h x y x
@[equational_result]
theorem Equation2775_implies_Equation2700 (G : Type*) [Magma G] (h : Equation2775 G) : Equation2700 G := λ x y => h x y x
@[equational_result]
theorem Equation2776_implies_Equation2699 (G : Type*) [Magma G] (h : Equation2776 G) : Equation2699 G := λ x y => h x y x
@[equational_result]
theorem Equation2778_implies_Equation2696 (G : Type*) [Magma G] (h : Equation2778 G) : Equation2696 G := λ x y => h x y x
@[equational_result]
theorem Equation2779_implies_Equation2697 (G : Type*) [Magma G] (h : Equation2779 G) : Equation2697 G := λ x y => h x y x
@[equational_result]
theorem Equation2780_implies_Equation2696 (G : Type*) [Magma G] (h : Equation2780 G) : Equation2696 G := λ x y => h x y x
@[equational_result]
theorem Equation2787_implies_Equation2706 (G : Type*) [Magma G] (h : Equation2787 G) : Equation2706 G := λ x y => h x y x
@[equational_result]
theorem Equation2788_implies_Equation2707 (G : Type*) [Magma G] (h : Equation2788 G) : Equation2707 G := λ x y => h x y x
@[equational_result]
theorem Equation2789_implies_Equation2706 (G : Type*) [Magma G] (h : Equation2789 G) : Equation2706 G := λ x y => h x y x
@[equational_result]
theorem Equation2791_implies_Equation2709 (G : Type*) [Magma G] (h : Equation2791 G) : Equation2709 G := λ x y => h x y x
@[equational_result]
theorem Equation2792_implies_Equation2710 (G : Type*) [Magma G] (h : Equation2792 G) : Equation2710 G := λ x y => h x y x
@[equational_result]
theorem Equation2793_implies_Equation2709 (G : Type*) [Magma G] (h : Equation2793 G) : Equation2709 G := λ x y => h x y x
@[equational_result]
theorem Equation2795_implies_Equation2706 (G : Type*) [Magma G] (h : Equation2795 G) : Equation2706 G := λ x y => h x y x
@[equational_result]
theorem Equation2796_implies_Equation2707 (G : Type*) [Magma G] (h : Equation2796 G) : Equation2707 G := λ x y => h x y x
@[equational_result]
theorem Equation2797_implies_Equation2706 (G : Type*) [Magma G] (h : Equation2797 G) : Equation2706 G := λ x y => h x y x
@[equational_result]
theorem Equation2804_implies_Equation2696 (G : Type*) [Magma G] (h : Equation2804 G) : Equation2696 G := λ x y => h x y x
@[equational_result]
theorem Equation2805_implies_Equation2697 (G : Type*) [Magma G] (h : Equation2805 G) : Equation2697 G := λ x y => h x y x
@[equational_result]
theorem Equation2806_implies_Equation2696 (G : Type*) [Magma G] (h : Equation2806 G) : Equation2696 G := λ x y => h x y x
@[equational_result]
theorem Equation2808_implies_Equation2699 (G : Type*) [Magma G] (h : Equation2808 G) : Equation2699 G := λ x y => h x y x
@[equational_result]
theorem Equation2809_implies_Equation2700 (G : Type*) [Magma G] (h : Equation2809 G) : Equation2700 G := λ x y => h x y x
@[equational_result]
theorem Equation2810_implies_Equation2699 (G : Type*) [Magma G] (h : Equation2810 G) : Equation2699 G := λ x y => h x y x
@[equational_result]
theorem Equation2812_implies_Equation2696 (G : Type*) [Magma G] (h : Equation2812 G) : Equation2696 G := λ x y => h x y x
@[equational_result]
theorem Equation2813_implies_Equation2697 (G : Type*) [Magma G] (h : Equation2813 G) : Equation2697 G := λ x y => h x y x
@[equational_result]
theorem Equation2814_implies_Equation2696 (G : Type*) [Magma G] (h : Equation2814 G) : Equation2696 G := λ x y => h x y x
@[equational_result]
theorem Equation2851_implies_Equation2849 (G : Type*) [Magma G] (h : Equation2851 G) : Equation2849 G := λ x y => h x y x
@[equational_result]
theorem Equation2854_implies_Equation2852 (G : Type*) [Magma G] (h : Equation2854 G) : Equation2852 G := λ x y => h x y x
@[equational_result]
theorem Equation2857_implies_Equation2855 (G : Type*) [Magma G] (h : Equation2857 G) : Equation2855 G := λ x y => h x y x
@[equational_result]
theorem Equation2858_implies_Equation2852 (G : Type*) [Magma G] (h : Equation2858 G) : Equation2852 G := λ x y => h x y x
@[equational_result]
theorem Equation2859_implies_Equation2853 (G : Type*) [Magma G] (h : Equation2859 G) : Equation2853 G := λ x y => h x y x
@[equational_result]
theorem Equation2860_implies_Equation2852 (G : Type*) [Magma G] (h : Equation2860 G) : Equation2852 G := λ x y => h x y x
@[equational_result]
theorem Equation2864_implies_Equation2862 (G : Type*) [Magma G] (h : Equation2864 G) : Equation2862 G := λ x y => h x y x
@[equational_result]
theorem Equation2867_implies_Equation2865 (G : Type*) [Magma G] (h : Equation2867 G) : Equation2865 G := λ x y => h x y x
@[equational_result]
theorem Equation2868_implies_Equation2862 (G : Type*) [Magma G] (h : Equation2868 G) : Equation2862 G := λ x y => h x y x
@[equational_result]
theorem Equation2869_implies_Equation2863 (G : Type*) [Magma G] (h : Equation2869 G) : Equation2863 G := λ x y => h x y x
@[equational_result]
theorem Equation2870_implies_Equation2862 (G : Type*) [Magma G] (h : Equation2870 G) : Equation2862 G := λ x y => h x y x
@[equational_result]
theorem Equation2874_implies_Equation2872 (G : Type*) [Magma G] (h : Equation2874 G) : Equation2872 G := λ x y => h x y x
@[equational_result]
theorem Equation2877_implies_Equation2875 (G : Type*) [Magma G] (h : Equation2877 G) : Equation2875 G := λ x y => h x y x
@[equational_result]
theorem Equation2878_implies_Equation2872 (G : Type*) [Magma G] (h : Equation2878 G) : Equation2872 G := λ x y => h x y x
@[equational_result]
theorem Equation2879_implies_Equation2873 (G : Type*) [Magma G] (h : Equation2879 G) : Equation2873 G := λ x y => h x y x
@[equational_result]
theorem Equation2880_implies_Equation2872 (G : Type*) [Magma G] (h : Equation2880 G) : Equation2872 G := λ x y => h x y x
@[equational_result]
theorem Equation2882_implies_Equation2862 (G : Type*) [Magma G] (h : Equation2882 G) : Equation2862 G := λ x y => h x y x
@[equational_result]
theorem Equation2883_implies_Equation2863 (G : Type*) [Magma G] (h : Equation2883 G) : Equation2863 G := λ x y => h x y x
@[equational_result]
theorem Equation2884_implies_Equation2862 (G : Type*) [Magma G] (h : Equation2884 G) : Equation2862 G := λ x y => h x y x
@[equational_result]
theorem Equation2886_implies_Equation2865 (G : Type*) [Magma G] (h : Equation2886 G) : Equation2865 G := λ x y => h x y x
@[equational_result]
theorem Equation2887_implies_Equation2866 (G : Type*) [Magma G] (h : Equation2887 G) : Equation2866 G := λ x y => h x y x
@[equational_result]
theorem Equation2888_implies_Equation2865 (G : Type*) [Magma G] (h : Equation2888 G) : Equation2865 G := λ x y => h x y x
@[equational_result]
theorem Equation2890_implies_Equation2862 (G : Type*) [Magma G] (h : Equation2890 G) : Equation2862 G := λ x y => h x y x
@[equational_result]
theorem Equation2891_implies_Equation2863 (G : Type*) [Magma G] (h : Equation2891 G) : Equation2863 G := λ x y => h x y x
@[equational_result]
theorem Equation2892_implies_Equation2862 (G : Type*) [Magma G] (h : Equation2892 G) : Equation2862 G := λ x y => h x y x
@[equational_result]
theorem Equation2901_implies_Equation2899 (G : Type*) [Magma G] (h : Equation2901 G) : Equation2899 G := λ x y => h x y x
@[equational_result]
theorem Equation2904_implies_Equation2902 (G : Type*) [Magma G] (h : Equation2904 G) : Equation2902 G := λ x y => h x y x
@[equational_result]
theorem Equation2905_implies_Equation2899 (G : Type*) [Magma G] (h : Equation2905 G) : Equation2899 G := λ x y => h x y x
@[equational_result]
theorem Equation2906_implies_Equation2900 (G : Type*) [Magma G] (h : Equation2906 G) : Equation2900 G := λ x y => h x y x
@[equational_result]
theorem Equation2907_implies_Equation2899 (G : Type*) [Magma G] (h : Equation2907 G) : Equation2899 G := λ x y => h x y x
@[equational_result]
theorem Equation2911_implies_Equation2909 (G : Type*) [Magma G] (h : Equation2911 G) : Equation2909 G := λ x y => h x y x
@[equational_result]
theorem Equation2914_implies_Equation2912 (G : Type*) [Magma G] (h : Equation2914 G) : Equation2912 G := λ x y => h x y x
@[equational_result]
theorem Equation2915_implies_Equation2909 (G : Type*) [Magma G] (h : Equation2915 G) : Equation2909 G := λ x y => h x y x
@[equational_result]
theorem Equation2916_implies_Equation2910 (G : Type*) [Magma G] (h : Equation2916 G) : Equation2910 G := λ x y => h x y x
@[equational_result]
theorem Equation2917_implies_Equation2909 (G : Type*) [Magma G] (h : Equation2917 G) : Equation2909 G := λ x y => h x y x
@[equational_result]
theorem Equation2919_implies_Equation2899 (G : Type*) [Magma G] (h : Equation2919 G) : Equation2899 G := λ x y => h x y x
@[equational_result]
theorem Equation2920_implies_Equation2900 (G : Type*) [Magma G] (h : Equation2920 G) : Equation2900 G := λ x y => h x y x
@[equational_result]
theorem Equation2921_implies_Equation2899 (G : Type*) [Magma G] (h : Equation2921 G) : Equation2899 G := λ x y => h x y x
@[equational_result]
theorem Equation2923_implies_Equation2902 (G : Type*) [Magma G] (h : Equation2923 G) : Equation2902 G := λ x y => h x y x
@[equational_result]
theorem Equation2924_implies_Equation2903 (G : Type*) [Magma G] (h : Equation2924 G) : Equation2903 G := λ x y => h x y x
@[equational_result]
theorem Equation2925_implies_Equation2902 (G : Type*) [Magma G] (h : Equation2925 G) : Equation2902 G := λ x y => h x y x
@[equational_result]
theorem Equation2927_implies_Equation2899 (G : Type*) [Magma G] (h : Equation2927 G) : Equation2899 G := λ x y => h x y x
@[equational_result]
theorem Equation2928_implies_Equation2900 (G : Type*) [Magma G] (h : Equation2928 G) : Equation2900 G := λ x y => h x y x
@[equational_result]
theorem Equation2929_implies_Equation2899 (G : Type*) [Magma G] (h : Equation2929 G) : Equation2899 G := λ x y => h x y x
@[equational_result]
theorem Equation2938_implies_Equation2936 (G : Type*) [Magma G] (h : Equation2938 G) : Equation2936 G := λ x y => h x y x
@[equational_result]
theorem Equation2941_implies_Equation2939 (G : Type*) [Magma G] (h : Equation2941 G) : Equation2939 G := λ x y => h x y x
@[equational_result]
theorem Equation2942_implies_Equation2936 (G : Type*) [Magma G] (h : Equation2942 G) : Equation2936 G := λ x y => h x y x
@[equational_result]
theorem Equation2943_implies_Equation2937 (G : Type*) [Magma G] (h : Equation2943 G) : Equation2937 G := λ x y => h x y x
@[equational_result]
theorem Equation2944_implies_Equation2936 (G : Type*) [Magma G] (h : Equation2944 G) : Equation2936 G := λ x y => h x y x
@[equational_result]
theorem Equation2948_implies_Equation2946 (G : Type*) [Magma G] (h : Equation2948 G) : Equation2946 G := λ x y => h x y x
@[equational_result]
theorem Equation2951_implies_Equation2949 (G : Type*) [Magma G] (h : Equation2951 G) : Equation2949 G := λ x y => h x y x
@[equational_result]
theorem Equation2952_implies_Equation2946 (G : Type*) [Magma G] (h : Equation2952 G) : Equation2946 G := λ x y => h x y x
@[equational_result]
theorem Equation2953_implies_Equation2947 (G : Type*) [Magma G] (h : Equation2953 G) : Equation2947 G := λ x y => h x y x
@[equational_result]
theorem Equation2954_implies_Equation2946 (G : Type*) [Magma G] (h : Equation2954 G) : Equation2946 G := λ x y => h x y x
@[equational_result]
theorem Equation2956_implies_Equation2936 (G : Type*) [Magma G] (h : Equation2956 G) : Equation2936 G := λ x y => h x y x
@[equational_result]
theorem Equation2957_implies_Equation2937 (G : Type*) [Magma G] (h : Equation2957 G) : Equation2937 G := λ x y => h x y x
@[equational_result]
theorem Equation2958_implies_Equation2936 (G : Type*) [Magma G] (h : Equation2958 G) : Equation2936 G := λ x y => h x y x
@[equational_result]
theorem Equation2960_implies_Equation2939 (G : Type*) [Magma G] (h : Equation2960 G) : Equation2939 G := λ x y => h x y x
@[equational_result]
theorem Equation2961_implies_Equation2940 (G : Type*) [Magma G] (h : Equation2961 G) : Equation2940 G := λ x y => h x y x
@[equational_result]
theorem Equation2962_implies_Equation2939 (G : Type*) [Magma G] (h : Equation2962 G) : Equation2939 G := λ x y => h x y x
@[equational_result]
theorem Equation2964_implies_Equation2936 (G : Type*) [Magma G] (h : Equation2964 G) : Equation2936 G := λ x y => h x y x
@[equational_result]
theorem Equation2965_implies_Equation2937 (G : Type*) [Magma G] (h : Equation2965 G) : Equation2937 G := λ x y => h x y x
@[equational_result]
theorem Equation2966_implies_Equation2936 (G : Type*) [Magma G] (h : Equation2966 G) : Equation2936 G := λ x y => h x y x
@[equational_result]
theorem Equation2973_implies_Equation2899 (G : Type*) [Magma G] (h : Equation2973 G) : Equation2899 G := λ x y => h x y x
@[equational_result]
theorem Equation2974_implies_Equation2900 (G : Type*) [Magma G] (h : Equation2974 G) : Equation2900 G := λ x y => h x y x
@[equational_result]
theorem Equation2975_implies_Equation2899 (G : Type*) [Magma G] (h : Equation2975 G) : Equation2899 G := λ x y => h x y x
@[equational_result]
theorem Equation2977_implies_Equation2902 (G : Type*) [Magma G] (h : Equation2977 G) : Equation2902 G := λ x y => h x y x
@[equational_result]
theorem Equation2978_implies_Equation2903 (G : Type*) [Magma G] (h : Equation2978 G) : Equation2903 G := λ x y => h x y x
@[equational_result]
theorem Equation2979_implies_Equation2902 (G : Type*) [Magma G] (h : Equation2979 G) : Equation2902 G := λ x y => h x y x
@[equational_result]
theorem Equation2981_implies_Equation2899 (G : Type*) [Magma G] (h : Equation2981 G) : Equation2899 G := λ x y => h x y x
@[equational_result]
theorem Equation2982_implies_Equation2900 (G : Type*) [Magma G] (h : Equation2982 G) : Equation2900 G := λ x y => h x y x
@[equational_result]
theorem Equation2983_implies_Equation2899 (G : Type*) [Magma G] (h : Equation2983 G) : Equation2899 G := λ x y => h x y x
@[equational_result]
theorem Equation2990_implies_Equation2909 (G : Type*) [Magma G] (h : Equation2990 G) : Equation2909 G := λ x y => h x y x
@[equational_result]
theorem Equation2991_implies_Equation2910 (G : Type*) [Magma G] (h : Equation2991 G) : Equation2910 G := λ x y => h x y x
@[equational_result]
theorem Equation2992_implies_Equation2909 (G : Type*) [Magma G] (h : Equation2992 G) : Equation2909 G := λ x y => h x y x
@[equational_result]
theorem Equation2994_implies_Equation2912 (G : Type*) [Magma G] (h : Equation2994 G) : Equation2912 G := λ x y => h x y x
@[equational_result]
theorem Equation2995_implies_Equation2913 (G : Type*) [Magma G] (h : Equation2995 G) : Equation2913 G := λ x y => h x y x
@[equational_result]
theorem Equation2996_implies_Equation2912 (G : Type*) [Magma G] (h : Equation2996 G) : Equation2912 G := λ x y => h x y x
@[equational_result]
theorem Equation2998_implies_Equation2909 (G : Type*) [Magma G] (h : Equation2998 G) : Equation2909 G := λ x y => h x y x
@[equational_result]
theorem Equation2999_implies_Equation2910 (G : Type*) [Magma G] (h : Equation2999 G) : Equation2910 G := λ x y => h x y x
@[equational_result]
theorem Equation3000_implies_Equation2909 (G : Type*) [Magma G] (h : Equation3000 G) : Equation2909 G := λ x y => h x y x
@[equational_result]
theorem Equation3007_implies_Equation2899 (G : Type*) [Magma G] (h : Equation3007 G) : Equation2899 G := λ x y => h x y x
@[equational_result]
theorem Equation3008_implies_Equation2900 (G : Type*) [Magma G] (h : Equation3008 G) : Equation2900 G := λ x y => h x y x
@[equational_result]
theorem Equation3009_implies_Equation2899 (G : Type*) [Magma G] (h : Equation3009 G) : Equation2899 G := λ x y => h x y x
@[equational_result]
theorem Equation3011_implies_Equation2902 (G : Type*) [Magma G] (h : Equation3011 G) : Equation2902 G := λ x y => h x y x
@[equational_result]
theorem Equation3012_implies_Equation2903 (G : Type*) [Magma G] (h : Equation3012 G) : Equation2903 G := λ x y => h x y x
@[equational_result]
theorem Equation3013_implies_Equation2902 (G : Type*) [Magma G] (h : Equation3013 G) : Equation2902 G := λ x y => h x y x
@[equational_result]
theorem Equation3015_implies_Equation2899 (G : Type*) [Magma G] (h : Equation3015 G) : Equation2899 G := λ x y => h x y x
@[equational_result]
theorem Equation3016_implies_Equation2900 (G : Type*) [Magma G] (h : Equation3016 G) : Equation2900 G := λ x y => h x y x
@[equational_result]
theorem Equation3017_implies_Equation2899 (G : Type*) [Magma G] (h : Equation3017 G) : Equation2899 G := λ x y => h x y x
@[equational_result]
theorem Equation3054_implies_Equation3052 (G : Type*) [Magma G] (h : Equation3054 G) : Equation3052 G := λ x y => h x y x
@[equational_result]
theorem Equation3057_implies_Equation3055 (G : Type*) [Magma G] (h : Equation3057 G) : Equation3055 G := λ x y => h x y x
@[equational_result]
theorem Equation3060_implies_Equation3058 (G : Type*) [Magma G] (h : Equation3060 G) : Equation3058 G := λ x y => h x y x
@[equational_result]
theorem Equation3061_implies_Equation3055 (G : Type*) [Magma G] (h : Equation3061 G) : Equation3055 G := λ x y => h x y x
@[equational_result]
theorem Equation3062_implies_Equation3056 (G : Type*) [Magma G] (h : Equation3062 G) : Equation3056 G := λ x y => h x y x
@[equational_result]
theorem Equation3063_implies_Equation3055 (G : Type*) [Magma G] (h : Equation3063 G) : Equation3055 G := λ x y => h x y x
@[equational_result]
theorem Equation3067_implies_Equation3065 (G : Type*) [Magma G] (h : Equation3067 G) : Equation3065 G := λ x y => h x y x
@[equational_result]
theorem Equation3070_implies_Equation3068 (G : Type*) [Magma G] (h : Equation3070 G) : Equation3068 G := λ x y => h x y x
@[equational_result]
theorem Equation3071_implies_Equation3065 (G : Type*) [Magma G] (h : Equation3071 G) : Equation3065 G := λ x y => h x y x
@[equational_result]
theorem Equation3072_implies_Equation3066 (G : Type*) [Magma G] (h : Equation3072 G) : Equation3066 G := λ x y => h x y x
@[equational_result]
theorem Equation3073_implies_Equation3065 (G : Type*) [Magma G] (h : Equation3073 G) : Equation3065 G := λ x y => h x y x
@[equational_result]
theorem Equation3077_implies_Equation3075 (G : Type*) [Magma G] (h : Equation3077 G) : Equation3075 G := λ x y => h x y x
@[equational_result]
theorem Equation3080_implies_Equation3078 (G : Type*) [Magma G] (h : Equation3080 G) : Equation3078 G := λ x y => h x y x
@[equational_result]
theorem Equation3081_implies_Equation3075 (G : Type*) [Magma G] (h : Equation3081 G) : Equation3075 G := λ x y => h x y x
@[equational_result]
theorem Equation3082_implies_Equation3076 (G : Type*) [Magma G] (h : Equation3082 G) : Equation3076 G := λ x y => h x y x
@[equational_result]
theorem Equation3083_implies_Equation3075 (G : Type*) [Magma G] (h : Equation3083 G) : Equation3075 G := λ x y => h x y x
@[equational_result]
theorem Equation3085_implies_Equation3065 (G : Type*) [Magma G] (h : Equation3085 G) : Equation3065 G := λ x y => h x y x
@[equational_result]
theorem Equation3086_implies_Equation3066 (G : Type*) [Magma G] (h : Equation3086 G) : Equation3066 G := λ x y => h x y x
@[equational_result]
theorem Equation3087_implies_Equation3065 (G : Type*) [Magma G] (h : Equation3087 G) : Equation3065 G := λ x y => h x y x
@[equational_result]
theorem Equation3089_implies_Equation3068 (G : Type*) [Magma G] (h : Equation3089 G) : Equation3068 G := λ x y => h x y x
@[equational_result]
theorem Equation3090_implies_Equation3069 (G : Type*) [Magma G] (h : Equation3090 G) : Equation3069 G := λ x y => h x y x
@[equational_result]
theorem Equation3091_implies_Equation3068 (G : Type*) [Magma G] (h : Equation3091 G) : Equation3068 G := λ x y => h x y x
@[equational_result]
theorem Equation3093_implies_Equation3065 (G : Type*) [Magma G] (h : Equation3093 G) : Equation3065 G := λ x y => h x y x
@[equational_result]
theorem Equation3094_implies_Equation3066 (G : Type*) [Magma G] (h : Equation3094 G) : Equation3066 G := λ x y => h x y x
@[equational_result]
theorem Equation3095_implies_Equation3065 (G : Type*) [Magma G] (h : Equation3095 G) : Equation3065 G := λ x y => h x y x
@[equational_result]
theorem Equation3104_implies_Equation3102 (G : Type*) [Magma G] (h : Equation3104 G) : Equation3102 G := λ x y => h x y x
@[equational_result]
theorem Equation3107_implies_Equation3105 (G : Type*) [Magma G] (h : Equation3107 G) : Equation3105 G := λ x y => h x y x
@[equational_result]
theorem Equation3108_implies_Equation3102 (G : Type*) [Magma G] (h : Equation3108 G) : Equation3102 G := λ x y => h x y x
@[equational_result]
theorem Equation3109_implies_Equation3103 (G : Type*) [Magma G] (h : Equation3109 G) : Equation3103 G := λ x y => h x y x
@[equational_result]
theorem Equation3110_implies_Equation3102 (G : Type*) [Magma G] (h : Equation3110 G) : Equation3102 G := λ x y => h x y x
@[equational_result]
theorem Equation3114_implies_Equation3112 (G : Type*) [Magma G] (h : Equation3114 G) : Equation3112 G := λ x y => h x y x
@[equational_result]
theorem Equation3117_implies_Equation3115 (G : Type*) [Magma G] (h : Equation3117 G) : Equation3115 G := λ x y => h x y x
@[equational_result]
theorem Equation3118_implies_Equation3112 (G : Type*) [Magma G] (h : Equation3118 G) : Equation3112 G := λ x y => h x y x
@[equational_result]
theorem Equation3119_implies_Equation3113 (G : Type*) [Magma G] (h : Equation3119 G) : Equation3113 G := λ x y => h x y x
@[equational_result]
theorem Equation3120_implies_Equation3112 (G : Type*) [Magma G] (h : Equation3120 G) : Equation3112 G := λ x y => h x y x
@[equational_result]
theorem Equation3122_implies_Equation3102 (G : Type*) [Magma G] (h : Equation3122 G) : Equation3102 G := λ x y => h x y x
@[equational_result]
theorem Equation3123_implies_Equation3103 (G : Type*) [Magma G] (h : Equation3123 G) : Equation3103 G := λ x y => h x y x
@[equational_result]
theorem Equation3124_implies_Equation3102 (G : Type*) [Magma G] (h : Equation3124 G) : Equation3102 G := λ x y => h x y x
@[equational_result]
theorem Equation3126_implies_Equation3105 (G : Type*) [Magma G] (h : Equation3126 G) : Equation3105 G := λ x y => h x y x
@[equational_result]
theorem Equation3127_implies_Equation3106 (G : Type*) [Magma G] (h : Equation3127 G) : Equation3106 G := λ x y => h x y x
@[equational_result]
theorem Equation3128_implies_Equation3105 (G : Type*) [Magma G] (h : Equation3128 G) : Equation3105 G := λ x y => h x y x
@[equational_result]
theorem Equation3130_implies_Equation3102 (G : Type*) [Magma G] (h : Equation3130 G) : Equation3102 G := λ x y => h x y x
@[equational_result]
theorem Equation3131_implies_Equation3103 (G : Type*) [Magma G] (h : Equation3131 G) : Equation3103 G := λ x y => h x y x
@[equational_result]
theorem Equation3132_implies_Equation3102 (G : Type*) [Magma G] (h : Equation3132 G) : Equation3102 G := λ x y => h x y x
@[equational_result]
theorem Equation3141_implies_Equation3139 (G : Type*) [Magma G] (h : Equation3141 G) : Equation3139 G := λ x y => h x y x
@[equational_result]
theorem Equation3144_implies_Equation3142 (G : Type*) [Magma G] (h : Equation3144 G) : Equation3142 G := λ x y => h x y x
@[equational_result]
theorem Equation3145_implies_Equation3139 (G : Type*) [Magma G] (h : Equation3145 G) : Equation3139 G := λ x y => h x y x
@[equational_result]
theorem Equation3146_implies_Equation3140 (G : Type*) [Magma G] (h : Equation3146 G) : Equation3140 G := λ x y => h x y x
@[equational_result]
theorem Equation3147_implies_Equation3139 (G : Type*) [Magma G] (h : Equation3147 G) : Equation3139 G := λ x y => h x y x
@[equational_result]
theorem Equation3151_implies_Equation3149 (G : Type*) [Magma G] (h : Equation3151 G) : Equation3149 G := λ x y => h x y x
@[equational_result]
theorem Equation3154_implies_Equation3152 (G : Type*) [Magma G] (h : Equation3154 G) : Equation3152 G := λ x y => h x y x
@[equational_result]
theorem Equation3155_implies_Equation3149 (G : Type*) [Magma G] (h : Equation3155 G) : Equation3149 G := λ x y => h x y x
@[equational_result]
theorem Equation3156_implies_Equation3150 (G : Type*) [Magma G] (h : Equation3156 G) : Equation3150 G := λ x y => h x y x
@[equational_result]
theorem Equation3157_implies_Equation3149 (G : Type*) [Magma G] (h : Equation3157 G) : Equation3149 G := λ x y => h x y x
@[equational_result]
theorem Equation3159_implies_Equation3139 (G : Type*) [Magma G] (h : Equation3159 G) : Equation3139 G := λ x y => h x y x
@[equational_result]
theorem Equation3160_implies_Equation3140 (G : Type*) [Magma G] (h : Equation3160 G) : Equation3140 G := λ x y => h x y x
@[equational_result]
theorem Equation3161_implies_Equation3139 (G : Type*) [Magma G] (h : Equation3161 G) : Equation3139 G := λ x y => h x y x
@[equational_result]
theorem Equation3163_implies_Equation3142 (G : Type*) [Magma G] (h : Equation3163 G) : Equation3142 G := λ x y => h x y x
@[equational_result]
theorem Equation3164_implies_Equation3143 (G : Type*) [Magma G] (h : Equation3164 G) : Equation3143 G := λ x y => h x y x
@[equational_result]
theorem Equation3165_implies_Equation3142 (G : Type*) [Magma G] (h : Equation3165 G) : Equation3142 G := λ x y => h x y x
@[equational_result]
theorem Equation3167_implies_Equation3139 (G : Type*) [Magma G] (h : Equation3167 G) : Equation3139 G := λ x y => h x y x
@[equational_result]
theorem Equation3168_implies_Equation3140 (G : Type*) [Magma G] (h : Equation3168 G) : Equation3140 G := λ x y => h x y x
@[equational_result]
theorem Equation3169_implies_Equation3139 (G : Type*) [Magma G] (h : Equation3169 G) : Equation3139 G := λ x y => h x y x
@[equational_result]
theorem Equation3176_implies_Equation3102 (G : Type*) [Magma G] (h : Equation3176 G) : Equation3102 G := λ x y => h x y x
@[equational_result]
theorem Equation3177_implies_Equation3103 (G : Type*) [Magma G] (h : Equation3177 G) : Equation3103 G := λ x y => h x y x
@[equational_result]
theorem Equation3178_implies_Equation3102 (G : Type*) [Magma G] (h : Equation3178 G) : Equation3102 G := λ x y => h x y x
@[equational_result]
theorem Equation3180_implies_Equation3105 (G : Type*) [Magma G] (h : Equation3180 G) : Equation3105 G := λ x y => h x y x
@[equational_result]
theorem Equation3181_implies_Equation3106 (G : Type*) [Magma G] (h : Equation3181 G) : Equation3106 G := λ x y => h x y x
@[equational_result]
theorem Equation3182_implies_Equation3105 (G : Type*) [Magma G] (h : Equation3182 G) : Equation3105 G := λ x y => h x y x
@[equational_result]
theorem Equation3184_implies_Equation3102 (G : Type*) [Magma G] (h : Equation3184 G) : Equation3102 G := λ x y => h x y x
@[equational_result]
theorem Equation3185_implies_Equation3103 (G : Type*) [Magma G] (h : Equation3185 G) : Equation3103 G := λ x y => h x y x
@[equational_result]
theorem Equation3186_implies_Equation3102 (G : Type*) [Magma G] (h : Equation3186 G) : Equation3102 G := λ x y => h x y x
@[equational_result]
theorem Equation3193_implies_Equation3112 (G : Type*) [Magma G] (h : Equation3193 G) : Equation3112 G := λ x y => h x y x
@[equational_result]
theorem Equation3194_implies_Equation3113 (G : Type*) [Magma G] (h : Equation3194 G) : Equation3113 G := λ x y => h x y x
@[equational_result]
theorem Equation3195_implies_Equation3112 (G : Type*) [Magma G] (h : Equation3195 G) : Equation3112 G := λ x y => h x y x
@[equational_result]
theorem Equation3197_implies_Equation3115 (G : Type*) [Magma G] (h : Equation3197 G) : Equation3115 G := λ x y => h x y x
@[equational_result]
theorem Equation3198_implies_Equation3116 (G : Type*) [Magma G] (h : Equation3198 G) : Equation3116 G := λ x y => h x y x
@[equational_result]
theorem Equation3199_implies_Equation3115 (G : Type*) [Magma G] (h : Equation3199 G) : Equation3115 G := λ x y => h x y x
@[equational_result]
theorem Equation3201_implies_Equation3112 (G : Type*) [Magma G] (h : Equation3201 G) : Equation3112 G := λ x y => h x y x
@[equational_result]
theorem Equation3202_implies_Equation3113 (G : Type*) [Magma G] (h : Equation3202 G) : Equation3113 G := λ x y => h x y x
@[equational_result]
theorem Equation3203_implies_Equation3112 (G : Type*) [Magma G] (h : Equation3203 G) : Equation3112 G := λ x y => h x y x
@[equational_result]
theorem Equation3210_implies_Equation3102 (G : Type*) [Magma G] (h : Equation3210 G) : Equation3102 G := λ x y => h x y x
@[equational_result]
theorem Equation3211_implies_Equation3103 (G : Type*) [Magma G] (h : Equation3211 G) : Equation3103 G := λ x y => h x y x
@[equational_result]
theorem Equation3212_implies_Equation3102 (G : Type*) [Magma G] (h : Equation3212 G) : Equation3102 G := λ x y => h x y x
@[equational_result]
theorem Equation3214_implies_Equation3105 (G : Type*) [Magma G] (h : Equation3214 G) : Equation3105 G := λ x y => h x y x
@[equational_result]
theorem Equation3215_implies_Equation3106 (G : Type*) [Magma G] (h : Equation3215 G) : Equation3106 G := λ x y => h x y x
@[equational_result]
theorem Equation3216_implies_Equation3105 (G : Type*) [Magma G] (h : Equation3216 G) : Equation3105 G := λ x y => h x y x
@[equational_result]
theorem Equation3218_implies_Equation3102 (G : Type*) [Magma G] (h : Equation3218 G) : Equation3102 G := λ x y => h x y x
@[equational_result]
theorem Equation3219_implies_Equation3103 (G : Type*) [Magma G] (h : Equation3219 G) : Equation3103 G := λ x y => h x y x
@[equational_result]
theorem Equation3220_implies_Equation3102 (G : Type*) [Magma G] (h : Equation3220 G) : Equation3102 G := λ x y => h x y x
@[equational_result]
theorem Equation3257_implies_Equation3255 (G : Type*) [Magma G] (h : Equation3257 G) : Equation3255 G := λ x y => h x y x
@[equational_result]
theorem Equation3260_implies_Equation3258 (G : Type*) [Magma G] (h : Equation3260 G) : Equation3258 G := λ x y => h x y x
@[equational_result]
theorem Equation3263_implies_Equation3261 (G : Type*) [Magma G] (h : Equation3263 G) : Equation3261 G := λ x y => h x y x
@[equational_result]
theorem Equation3264_implies_Equation3258 (G : Type*) [Magma G] (h : Equation3264 G) : Equation3258 G := λ x y => h x y x
@[equational_result]
theorem Equation3265_implies_Equation3259 (G : Type*) [Magma G] (h : Equation3265 G) : Equation3259 G := λ x y => h x y x
@[equational_result]
theorem Equation3266_implies_Equation3258 (G : Type*) [Magma G] (h : Equation3266 G) : Equation3258 G := λ x y => h x y x
@[equational_result]
theorem Equation3270_implies_Equation3268 (G : Type*) [Magma G] (h : Equation3270 G) : Equation3268 G := λ x y => h x y x
@[equational_result]
theorem Equation3273_implies_Equation3271 (G : Type*) [Magma G] (h : Equation3273 G) : Equation3271 G := λ x y => h x y x
@[equational_result]
theorem Equation3274_implies_Equation3268 (G : Type*) [Magma G] (h : Equation3274 G) : Equation3268 G := λ x y => h x y x
@[equational_result]
theorem Equation3275_implies_Equation3269 (G : Type*) [Magma G] (h : Equation3275 G) : Equation3269 G := λ x y => h x y x
@[equational_result]
theorem Equation3276_implies_Equation3268 (G : Type*) [Magma G] (h : Equation3276 G) : Equation3268 G := λ x y => h x y x
@[equational_result]
theorem Equation3280_implies_Equation3278 (G : Type*) [Magma G] (h : Equation3280 G) : Equation3278 G := λ x y => h x y x
@[equational_result]
theorem Equation3283_implies_Equation3281 (G : Type*) [Magma G] (h : Equation3283 G) : Equation3281 G := λ x y => h x y x
@[equational_result]
theorem Equation3284_implies_Equation3278 (G : Type*) [Magma G] (h : Equation3284 G) : Equation3278 G := λ x y => h x y x
@[equational_result]
theorem Equation3285_implies_Equation3279 (G : Type*) [Magma G] (h : Equation3285 G) : Equation3279 G := λ x y => h x y x
@[equational_result]
theorem Equation3286_implies_Equation3278 (G : Type*) [Magma G] (h : Equation3286 G) : Equation3278 G := λ x y => h x y x
@[equational_result]
theorem Equation3288_implies_Equation3268 (G : Type*) [Magma G] (h : Equation3288 G) : Equation3268 G := λ x y => h x y x
@[equational_result]
theorem Equation3289_implies_Equation3269 (G : Type*) [Magma G] (h : Equation3289 G) : Equation3269 G := λ x y => h x y x
@[equational_result]
theorem Equation3290_implies_Equation3268 (G : Type*) [Magma G] (h : Equation3290 G) : Equation3268 G := λ x y => h x y x
@[equational_result]
theorem Equation3292_implies_Equation3271 (G : Type*) [Magma G] (h : Equation3292 G) : Equation3271 G := λ x y => h x y x
@[equational_result]
theorem Equation3293_implies_Equation3272 (G : Type*) [Magma G] (h : Equation3293 G) : Equation3272 G := λ x y => h x y x
@[equational_result]
theorem Equation3294_implies_Equation3271 (G : Type*) [Magma G] (h : Equation3294 G) : Equation3271 G := λ x y => h x y x
@[equational_result]
theorem Equation3296_implies_Equation3268 (G : Type*) [Magma G] (h : Equation3296 G) : Equation3268 G := λ x y => h x y x
@[equational_result]
theorem Equation3297_implies_Equation3269 (G : Type*) [Magma G] (h : Equation3297 G) : Equation3269 G := λ x y => h x y x
@[equational_result]
theorem Equation3298_implies_Equation3268 (G : Type*) [Magma G] (h : Equation3298 G) : Equation3268 G := λ x y => h x y x
@[equational_result]
theorem Equation3307_implies_Equation3305 (G : Type*) [Magma G] (h : Equation3307 G) : Equation3305 G := λ x y => h x y x
@[equational_result]
theorem Equation3310_implies_Equation3308 (G : Type*) [Magma G] (h : Equation3310 G) : Equation3308 G := λ x y => h x y x
@[equational_result]
theorem Equation3311_implies_Equation3305 (G : Type*) [Magma G] (h : Equation3311 G) : Equation3305 G := λ x y => h x y x
@[equational_result]
theorem Equation3312_implies_Equation3306 (G : Type*) [Magma G] (h : Equation3312 G) : Equation3306 G := λ x y => h x y x
@[equational_result]
theorem Equation3313_implies_Equation3305 (G : Type*) [Magma G] (h : Equation3313 G) : Equation3305 G := λ x y => h x y x
@[equational_result]
theorem Equation3317_implies_Equation3315 (G : Type*) [Magma G] (h : Equation3317 G) : Equation3315 G := λ x y => h x y x
@[equational_result]
theorem Equation3320_implies_Equation3318 (G : Type*) [Magma G] (h : Equation3320 G) : Equation3318 G := λ x y => h x y x
@[equational_result]
theorem Equation3321_implies_Equation3315 (G : Type*) [Magma G] (h : Equation3321 G) : Equation3315 G := λ x y => h x y x
@[equational_result]
theorem Equation3322_implies_Equation3316 (G : Type*) [Magma G] (h : Equation3322 G) : Equation3316 G := λ x y => h x y x
@[equational_result]
theorem Equation3323_implies_Equation3315 (G : Type*) [Magma G] (h : Equation3323 G) : Equation3315 G := λ x y => h x y x
@[equational_result]
theorem Equation3325_implies_Equation3305 (G : Type*) [Magma G] (h : Equation3325 G) : Equation3305 G := λ x y => h x y x
@[equational_result]
theorem Equation3326_implies_Equation3306 (G : Type*) [Magma G] (h : Equation3326 G) : Equation3306 G := λ x y => h x y x
@[equational_result]
theorem Equation3327_implies_Equation3305 (G : Type*) [Magma G] (h : Equation3327 G) : Equation3305 G := λ x y => h x y x
@[equational_result]
theorem Equation3329_implies_Equation3308 (G : Type*) [Magma G] (h : Equation3329 G) : Equation3308 G := λ x y => h x y x
@[equational_result]
theorem Equation3330_implies_Equation3309 (G : Type*) [Magma G] (h : Equation3330 G) : Equation3309 G := λ x y => h x y x
@[equational_result]
theorem Equation3331_implies_Equation3308 (G : Type*) [Magma G] (h : Equation3331 G) : Equation3308 G := λ x y => h x y x
@[equational_result]
theorem Equation3333_implies_Equation3305 (G : Type*) [Magma G] (h : Equation3333 G) : Equation3305 G := λ x y => h x y x
@[equational_result]
theorem Equation3334_implies_Equation3306 (G : Type*) [Magma G] (h : Equation3334 G) : Equation3306 G := λ x y => h x y x
@[equational_result]
theorem Equation3335_implies_Equation3305 (G : Type*) [Magma G] (h : Equation3335 G) : Equation3305 G := λ x y => h x y x
@[equational_result]
theorem Equation3344_implies_Equation3342 (G : Type*) [Magma G] (h : Equation3344 G) : Equation3342 G := λ x y => h x y x
@[equational_result]
theorem Equation3347_implies_Equation3345 (G : Type*) [Magma G] (h : Equation3347 G) : Equation3345 G := λ x y => h x y x
@[equational_result]
theorem Equation3348_implies_Equation3342 (G : Type*) [Magma G] (h : Equation3348 G) : Equation3342 G := λ x y => h x y x
@[equational_result]
theorem Equation3349_implies_Equation3343 (G : Type*) [Magma G] (h : Equation3349 G) : Equation3343 G := λ x y => h x y x
@[equational_result]
theorem Equation3350_implies_Equation3342 (G : Type*) [Magma G] (h : Equation3350 G) : Equation3342 G := λ x y => h x y x
@[equational_result]
theorem Equation3354_implies_Equation3352 (G : Type*) [Magma G] (h : Equation3354 G) : Equation3352 G := λ x y => h x y x
@[equational_result]
theorem Equation3357_implies_Equation3355 (G : Type*) [Magma G] (h : Equation3357 G) : Equation3355 G := λ x y => h x y x
@[equational_result]
theorem Equation3358_implies_Equation3352 (G : Type*) [Magma G] (h : Equation3358 G) : Equation3352 G := λ x y => h x y x
@[equational_result]
theorem Equation3359_implies_Equation3353 (G : Type*) [Magma G] (h : Equation3359 G) : Equation3353 G := λ x y => h x y x
@[equational_result]
theorem Equation3360_implies_Equation3352 (G : Type*) [Magma G] (h : Equation3360 G) : Equation3352 G := λ x y => h x y x
@[equational_result]
theorem Equation3362_implies_Equation3342 (G : Type*) [Magma G] (h : Equation3362 G) : Equation3342 G := λ x y => h x y x
@[equational_result]
theorem Equation3363_implies_Equation3343 (G : Type*) [Magma G] (h : Equation3363 G) : Equation3343 G := λ x y => h x y x
@[equational_result]
theorem Equation3364_implies_Equation3342 (G : Type*) [Magma G] (h : Equation3364 G) : Equation3342 G := λ x y => h x y x
@[equational_result]
theorem Equation3366_implies_Equation3345 (G : Type*) [Magma G] (h : Equation3366 G) : Equation3345 G := λ x y => h x y x
@[equational_result]
theorem Equation3367_implies_Equation3346 (G : Type*) [Magma G] (h : Equation3367 G) : Equation3346 G := λ x y => h x y x
@[equational_result]
theorem Equation3368_implies_Equation3345 (G : Type*) [Magma G] (h : Equation3368 G) : Equation3345 G := λ x y => h x y x
@[equational_result]
theorem Equation3370_implies_Equation3342 (G : Type*) [Magma G] (h : Equation3370 G) : Equation3342 G := λ x y => h x y x
@[equational_result]
theorem Equation3371_implies_Equation3343 (G : Type*) [Magma G] (h : Equation3371 G) : Equation3343 G := λ x y => h x y x
@[equational_result]
theorem Equation3372_implies_Equation3342 (G : Type*) [Magma G] (h : Equation3372 G) : Equation3342 G := λ x y => h x y x
@[equational_result]
theorem Equation3379_implies_Equation3305 (G : Type*) [Magma G] (h : Equation3379 G) : Equation3305 G := λ x y => h x y x
@[equational_result]
theorem Equation3380_implies_Equation3306 (G : Type*) [Magma G] (h : Equation3380 G) : Equation3306 G := λ x y => h x y x
@[equational_result]
theorem Equation3381_implies_Equation3305 (G : Type*) [Magma G] (h : Equation3381 G) : Equation3305 G := λ x y => h x y x
@[equational_result]
theorem Equation3383_implies_Equation3308 (G : Type*) [Magma G] (h : Equation3383 G) : Equation3308 G := λ x y => h x y x
@[equational_result]
theorem Equation3384_implies_Equation3309 (G : Type*) [Magma G] (h : Equation3384 G) : Equation3309 G := λ x y => h x y x
@[equational_result]
theorem Equation3385_implies_Equation3308 (G : Type*) [Magma G] (h : Equation3385 G) : Equation3308 G := λ x y => h x y x
@[equational_result]
theorem Equation3387_implies_Equation3305 (G : Type*) [Magma G] (h : Equation3387 G) : Equation3305 G := λ x y => h x y x
@[equational_result]
theorem Equation3388_implies_Equation3306 (G : Type*) [Magma G] (h : Equation3388 G) : Equation3306 G := λ x y => h x y x
@[equational_result]
theorem Equation3389_implies_Equation3305 (G : Type*) [Magma G] (h : Equation3389 G) : Equation3305 G := λ x y => h x y x
@[equational_result]
theorem Equation3396_implies_Equation3315 (G : Type*) [Magma G] (h : Equation3396 G) : Equation3315 G := λ x y => h x y x
@[equational_result]
theorem Equation3397_implies_Equation3316 (G : Type*) [Magma G] (h : Equation3397 G) : Equation3316 G := λ x y => h x y x
@[equational_result]
theorem Equation3398_implies_Equation3315 (G : Type*) [Magma G] (h : Equation3398 G) : Equation3315 G := λ x y => h x y x
@[equational_result]
theorem Equation3400_implies_Equation3318 (G : Type*) [Magma G] (h : Equation3400 G) : Equation3318 G := λ x y => h x y x
@[equational_result]
theorem Equation3401_implies_Equation3319 (G : Type*) [Magma G] (h : Equation3401 G) : Equation3319 G := λ x y => h x y x
@[equational_result]
theorem Equation3402_implies_Equation3318 (G : Type*) [Magma G] (h : Equation3402 G) : Equation3318 G := λ x y => h x y x
@[equational_result]
theorem Equation3404_implies_Equation3315 (G : Type*) [Magma G] (h : Equation3404 G) : Equation3315 G := λ x y => h x y x
@[equational_result]
theorem Equation3405_implies_Equation3316 (G : Type*) [Magma G] (h : Equation3405 G) : Equation3316 G := λ x y => h x y x
@[equational_result]
theorem Equation3406_implies_Equation3315 (G : Type*) [Magma G] (h : Equation3406 G) : Equation3315 G := λ x y => h x y x
@[equational_result]
theorem Equation3413_implies_Equation3305 (G : Type*) [Magma G] (h : Equation3413 G) : Equation3305 G := λ x y => h x y x
@[equational_result]
theorem Equation3414_implies_Equation3306 (G : Type*) [Magma G] (h : Equation3414 G) : Equation3306 G := λ x y => h x y x
@[equational_result]
theorem Equation3415_implies_Equation3305 (G : Type*) [Magma G] (h : Equation3415 G) : Equation3305 G := λ x y => h x y x
@[equational_result]
theorem Equation3417_implies_Equation3308 (G : Type*) [Magma G] (h : Equation3417 G) : Equation3308 G := λ x y => h x y x
@[equational_result]
theorem Equation3418_implies_Equation3309 (G : Type*) [Magma G] (h : Equation3418 G) : Equation3309 G := λ x y => h x y x
@[equational_result]
theorem Equation3419_implies_Equation3308 (G : Type*) [Magma G] (h : Equation3419 G) : Equation3308 G := λ x y => h x y x
@[equational_result]
theorem Equation3421_implies_Equation3305 (G : Type*) [Magma G] (h : Equation3421 G) : Equation3305 G := λ x y => h x y x
@[equational_result]
theorem Equation3422_implies_Equation3306 (G : Type*) [Magma G] (h : Equation3422 G) : Equation3306 G := λ x y => h x y x
@[equational_result]
theorem Equation3423_implies_Equation3305 (G : Type*) [Magma G] (h : Equation3423 G) : Equation3305 G := λ x y => h x y x
@[equational_result]
theorem Equation3460_implies_Equation3458 (G : Type*) [Magma G] (h : Equation3460 G) : Equation3458 G := λ x y => h x y x
@[equational_result]
theorem Equation3463_implies_Equation3461 (G : Type*) [Magma G] (h : Equation3463 G) : Equation3461 G := λ x y => h x y x
@[equational_result]
theorem Equation3466_implies_Equation3464 (G : Type*) [Magma G] (h : Equation3466 G) : Equation3464 G := λ x y => h x y x
@[equational_result]
theorem Equation3467_implies_Equation3461 (G : Type*) [Magma G] (h : Equation3467 G) : Equation3461 G := λ x y => h x y x
@[equational_result]
theorem Equation3468_implies_Equation3462 (G : Type*) [Magma G] (h : Equation3468 G) : Equation3462 G := λ x y => h x y x
@[equational_result]
theorem Equation3469_implies_Equation3461 (G : Type*) [Magma G] (h : Equation3469 G) : Equation3461 G := λ x y => h x y x
@[equational_result]
theorem Equation3473_implies_Equation3471 (G : Type*) [Magma G] (h : Equation3473 G) : Equation3471 G := λ x y => h x y x
@[equational_result]
theorem Equation3476_implies_Equation3474 (G : Type*) [Magma G] (h : Equation3476 G) : Equation3474 G := λ x y => h x y x
@[equational_result]
theorem Equation3477_implies_Equation3471 (G : Type*) [Magma G] (h : Equation3477 G) : Equation3471 G := λ x y => h x y x
@[equational_result]
theorem Equation3478_implies_Equation3472 (G : Type*) [Magma G] (h : Equation3478 G) : Equation3472 G := λ x y => h x y x
@[equational_result]
theorem Equation3479_implies_Equation3471 (G : Type*) [Magma G] (h : Equation3479 G) : Equation3471 G := λ x y => h x y x
@[equational_result]
theorem Equation3483_implies_Equation3481 (G : Type*) [Magma G] (h : Equation3483 G) : Equation3481 G := λ x y => h x y x
@[equational_result]
theorem Equation3486_implies_Equation3484 (G : Type*) [Magma G] (h : Equation3486 G) : Equation3484 G := λ x y => h x y x
@[equational_result]
theorem Equation3487_implies_Equation3481 (G : Type*) [Magma G] (h : Equation3487 G) : Equation3481 G := λ x y => h x y x
@[equational_result]
theorem Equation3488_implies_Equation3482 (G : Type*) [Magma G] (h : Equation3488 G) : Equation3482 G := λ x y => h x y x
@[equational_result]
theorem Equation3489_implies_Equation3481 (G : Type*) [Magma G] (h : Equation3489 G) : Equation3481 G := λ x y => h x y x
@[equational_result]
theorem Equation3491_implies_Equation3471 (G : Type*) [Magma G] (h : Equation3491 G) : Equation3471 G := λ x y => h x y x
@[equational_result]
theorem Equation3492_implies_Equation3472 (G : Type*) [Magma G] (h : Equation3492 G) : Equation3472 G := λ x y => h x y x
@[equational_result]
theorem Equation3493_implies_Equation3471 (G : Type*) [Magma G] (h : Equation3493 G) : Equation3471 G := λ x y => h x y x
@[equational_result]
theorem Equation3495_implies_Equation3474 (G : Type*) [Magma G] (h : Equation3495 G) : Equation3474 G := λ x y => h x y x
@[equational_result]
theorem Equation3496_implies_Equation3475 (G : Type*) [Magma G] (h : Equation3496 G) : Equation3475 G := λ x y => h x y x
@[equational_result]
theorem Equation3497_implies_Equation3474 (G : Type*) [Magma G] (h : Equation3497 G) : Equation3474 G := λ x y => h x y x
@[equational_result]
theorem Equation3499_implies_Equation3471 (G : Type*) [Magma G] (h : Equation3499 G) : Equation3471 G := λ x y => h x y x
@[equational_result]
theorem Equation3500_implies_Equation3472 (G : Type*) [Magma G] (h : Equation3500 G) : Equation3472 G := λ x y => h x y x
@[equational_result]
theorem Equation3501_implies_Equation3471 (G : Type*) [Magma G] (h : Equation3501 G) : Equation3471 G := λ x y => h x y x
@[equational_result]
theorem Equation3510_implies_Equation3508 (G : Type*) [Magma G] (h : Equation3510 G) : Equation3508 G := λ x y => h x y x
@[equational_result]
theorem Equation3513_implies_Equation3511 (G : Type*) [Magma G] (h : Equation3513 G) : Equation3511 G := λ x y => h x y x
@[equational_result]
theorem Equation3514_implies_Equation3508 (G : Type*) [Magma G] (h : Equation3514 G) : Equation3508 G := λ x y => h x y x
@[equational_result]
theorem Equation3515_implies_Equation3509 (G : Type*) [Magma G] (h : Equation3515 G) : Equation3509 G := λ x y => h x y x
@[equational_result]
theorem Equation3516_implies_Equation3508 (G : Type*) [Magma G] (h : Equation3516 G) : Equation3508 G := λ x y => h x y x
@[equational_result]
theorem Equation3520_implies_Equation3518 (G : Type*) [Magma G] (h : Equation3520 G) : Equation3518 G := λ x y => h x y x
@[equational_result]
theorem Equation3523_implies_Equation3521 (G : Type*) [Magma G] (h : Equation3523 G) : Equation3521 G := λ x y => h x y x
@[equational_result]
theorem Equation3524_implies_Equation3518 (G : Type*) [Magma G] (h : Equation3524 G) : Equation3518 G := λ x y => h x y x
@[equational_result]
theorem Equation3525_implies_Equation3519 (G : Type*) [Magma G] (h : Equation3525 G) : Equation3519 G := λ x y => h x y x
@[equational_result]
theorem Equation3526_implies_Equation3518 (G : Type*) [Magma G] (h : Equation3526 G) : Equation3518 G := λ x y => h x y x
@[equational_result]
theorem Equation3528_implies_Equation3508 (G : Type*) [Magma G] (h : Equation3528 G) : Equation3508 G := λ x y => h x y x
@[equational_result]
theorem Equation3529_implies_Equation3509 (G : Type*) [Magma G] (h : Equation3529 G) : Equation3509 G := λ x y => h x y x
@[equational_result]
theorem Equation3530_implies_Equation3508 (G : Type*) [Magma G] (h : Equation3530 G) : Equation3508 G := λ x y => h x y x
@[equational_result]
theorem Equation3532_implies_Equation3511 (G : Type*) [Magma G] (h : Equation3532 G) : Equation3511 G := λ x y => h x y x
@[equational_result]
theorem Equation3533_implies_Equation3512 (G : Type*) [Magma G] (h : Equation3533 G) : Equation3512 G := λ x y => h x y x
@[equational_result]
theorem Equation3534_implies_Equation3511 (G : Type*) [Magma G] (h : Equation3534 G) : Equation3511 G := λ x y => h x y x
@[equational_result]
theorem Equation3536_implies_Equation3508 (G : Type*) [Magma G] (h : Equation3536 G) : Equation3508 G := λ x y => h x y x
@[equational_result]
theorem Equation3537_implies_Equation3509 (G : Type*) [Magma G] (h : Equation3537 G) : Equation3509 G := λ x y => h x y x
@[equational_result]
theorem Equation3538_implies_Equation3508 (G : Type*) [Magma G] (h : Equation3538 G) : Equation3508 G := λ x y => h x y x
@[equational_result]
theorem Equation3547_implies_Equation3545 (G : Type*) [Magma G] (h : Equation3547 G) : Equation3545 G := λ x y => h x y x
@[equational_result]
theorem Equation3550_implies_Equation3548 (G : Type*) [Magma G] (h : Equation3550 G) : Equation3548 G := λ x y => h x y x
@[equational_result]
theorem Equation3551_implies_Equation3545 (G : Type*) [Magma G] (h : Equation3551 G) : Equation3545 G := λ x y => h x y x
@[equational_result]
theorem Equation3552_implies_Equation3546 (G : Type*) [Magma G] (h : Equation3552 G) : Equation3546 G := λ x y => h x y x
@[equational_result]
theorem Equation3553_implies_Equation3545 (G : Type*) [Magma G] (h : Equation3553 G) : Equation3545 G := λ x y => h x y x
@[equational_result]
theorem Equation3557_implies_Equation3555 (G : Type*) [Magma G] (h : Equation3557 G) : Equation3555 G := λ x y => h x y x
@[equational_result]
theorem Equation3560_implies_Equation3558 (G : Type*) [Magma G] (h : Equation3560 G) : Equation3558 G := λ x y => h x y x
@[equational_result]
theorem Equation3561_implies_Equation3555 (G : Type*) [Magma G] (h : Equation3561 G) : Equation3555 G := λ x y => h x y x
@[equational_result]
theorem Equation3562_implies_Equation3556 (G : Type*) [Magma G] (h : Equation3562 G) : Equation3556 G := λ x y => h x y x
@[equational_result]
theorem Equation3563_implies_Equation3555 (G : Type*) [Magma G] (h : Equation3563 G) : Equation3555 G := λ x y => h x y x
@[equational_result]
theorem Equation3565_implies_Equation3545 (G : Type*) [Magma G] (h : Equation3565 G) : Equation3545 G := λ x y => h x y x
@[equational_result]
theorem Equation3566_implies_Equation3546 (G : Type*) [Magma G] (h : Equation3566 G) : Equation3546 G := λ x y => h x y x
@[equational_result]
theorem Equation3567_implies_Equation3545 (G : Type*) [Magma G] (h : Equation3567 G) : Equation3545 G := λ x y => h x y x
@[equational_result]
theorem Equation3569_implies_Equation3548 (G : Type*) [Magma G] (h : Equation3569 G) : Equation3548 G := λ x y => h x y x
@[equational_result]
theorem Equation3570_implies_Equation3549 (G : Type*) [Magma G] (h : Equation3570 G) : Equation3549 G := λ x y => h x y x
@[equational_result]
theorem Equation3571_implies_Equation3548 (G : Type*) [Magma G] (h : Equation3571 G) : Equation3548 G := λ x y => h x y x
@[equational_result]
theorem Equation3573_implies_Equation3545 (G : Type*) [Magma G] (h : Equation3573 G) : Equation3545 G := λ x y => h x y x
@[equational_result]
theorem Equation3574_implies_Equation3546 (G : Type*) [Magma G] (h : Equation3574 G) : Equation3546 G := λ x y => h x y x
@[equational_result]
theorem Equation3575_implies_Equation3545 (G : Type*) [Magma G] (h : Equation3575 G) : Equation3545 G := λ x y => h x y x
@[equational_result]
theorem Equation3582_implies_Equation3508 (G : Type*) [Magma G] (h : Equation3582 G) : Equation3508 G := λ x y => h x y x
@[equational_result]
theorem Equation3583_implies_Equation3509 (G : Type*) [Magma G] (h : Equation3583 G) : Equation3509 G := λ x y => h x y x
@[equational_result]
theorem Equation3584_implies_Equation3508 (G : Type*) [Magma G] (h : Equation3584 G) : Equation3508 G := λ x y => h x y x
@[equational_result]
theorem Equation3586_implies_Equation3511 (G : Type*) [Magma G] (h : Equation3586 G) : Equation3511 G := λ x y => h x y x
@[equational_result]
theorem Equation3587_implies_Equation3512 (G : Type*) [Magma G] (h : Equation3587 G) : Equation3512 G := λ x y => h x y x
@[equational_result]
theorem Equation3588_implies_Equation3511 (G : Type*) [Magma G] (h : Equation3588 G) : Equation3511 G := λ x y => h x y x
@[equational_result]
theorem Equation3590_implies_Equation3508 (G : Type*) [Magma G] (h : Equation3590 G) : Equation3508 G := λ x y => h x y x
@[equational_result]
theorem Equation3591_implies_Equation3509 (G : Type*) [Magma G] (h : Equation3591 G) : Equation3509 G := λ x y => h x y x
@[equational_result]
theorem Equation3592_implies_Equation3508 (G : Type*) [Magma G] (h : Equation3592 G) : Equation3508 G := λ x y => h x y x
@[equational_result]
theorem Equation3599_implies_Equation3518 (G : Type*) [Magma G] (h : Equation3599 G) : Equation3518 G := λ x y => h x y x
@[equational_result]
theorem Equation3600_implies_Equation3519 (G : Type*) [Magma G] (h : Equation3600 G) : Equation3519 G := λ x y => h x y x
@[equational_result]
theorem Equation3601_implies_Equation3518 (G : Type*) [Magma G] (h : Equation3601 G) : Equation3518 G := λ x y => h x y x
@[equational_result]
theorem Equation3603_implies_Equation3521 (G : Type*) [Magma G] (h : Equation3603 G) : Equation3521 G := λ x y => h x y x
@[equational_result]
theorem Equation3604_implies_Equation3522 (G : Type*) [Magma G] (h : Equation3604 G) : Equation3522 G := λ x y => h x y x
@[equational_result]
theorem Equation3605_implies_Equation3521 (G : Type*) [Magma G] (h : Equation3605 G) : Equation3521 G := λ x y => h x y x
@[equational_result]
theorem Equation3607_implies_Equation3518 (G : Type*) [Magma G] (h : Equation3607 G) : Equation3518 G := λ x y => h x y x
@[equational_result]
theorem Equation3608_implies_Equation3519 (G : Type*) [Magma G] (h : Equation3608 G) : Equation3519 G := λ x y => h x y x
@[equational_result]
theorem Equation3609_implies_Equation3518 (G : Type*) [Magma G] (h : Equation3609 G) : Equation3518 G := λ x y => h x y x
@[equational_result]
theorem Equation3616_implies_Equation3508 (G : Type*) [Magma G] (h : Equation3616 G) : Equation3508 G := λ x y => h x y x
@[equational_result]
theorem Equation3617_implies_Equation3509 (G : Type*) [Magma G] (h : Equation3617 G) : Equation3509 G := λ x y => h x y x
@[equational_result]
theorem Equation3618_implies_Equation3508 (G : Type*) [Magma G] (h : Equation3618 G) : Equation3508 G := λ x y => h x y x
@[equational_result]
theorem Equation3620_implies_Equation3511 (G : Type*) [Magma G] (h : Equation3620 G) : Equation3511 G := λ x y => h x y x
@[equational_result]
theorem Equation3621_implies_Equation3512 (G : Type*) [Magma G] (h : Equation3621 G) : Equation3512 G := λ x y => h x y x
@[equational_result]
theorem Equation3622_implies_Equation3511 (G : Type*) [Magma G] (h : Equation3622 G) : Equation3511 G := λ x y => h x y x
@[equational_result]
theorem Equation3624_implies_Equation3508 (G : Type*) [Magma G] (h : Equation3624 G) : Equation3508 G := λ x y => h x y x
@[equational_result]
theorem Equation3625_implies_Equation3509 (G : Type*) [Magma G] (h : Equation3625 G) : Equation3509 G := λ x y => h x y x
@[equational_result]
theorem Equation3626_implies_Equation3508 (G : Type*) [Magma G] (h : Equation3626 G) : Equation3508 G := λ x y => h x y x
@[equational_result]
theorem Equation3663_implies_Equation3661 (G : Type*) [Magma G] (h : Equation3663 G) : Equation3661 G := λ x y => h x y x
@[equational_result]
theorem Equation3666_implies_Equation3664 (G : Type*) [Magma G] (h : Equation3666 G) : Equation3664 G := λ x y => h x y x
@[equational_result]
theorem Equation3669_implies_Equation3667 (G : Type*) [Magma G] (h : Equation3669 G) : Equation3667 G := λ x y => h x y x
@[equational_result]
theorem Equation3670_implies_Equation3664 (G : Type*) [Magma G] (h : Equation3670 G) : Equation3664 G := λ x y => h x y x
@[equational_result]
theorem Equation3671_implies_Equation3665 (G : Type*) [Magma G] (h : Equation3671 G) : Equation3665 G := λ x y => h x y x
@[equational_result]
theorem Equation3672_implies_Equation3664 (G : Type*) [Magma G] (h : Equation3672 G) : Equation3664 G := λ x y => h x y x
@[equational_result]
theorem Equation3676_implies_Equation3674 (G : Type*) [Magma G] (h : Equation3676 G) : Equation3674 G := λ x y => h x y x
@[equational_result]
theorem Equation3679_implies_Equation3677 (G : Type*) [Magma G] (h : Equation3679 G) : Equation3677 G := λ x y => h x y x
@[equational_result]
theorem Equation3680_implies_Equation3674 (G : Type*) [Magma G] (h : Equation3680 G) : Equation3674 G := λ x y => h x y x
@[equational_result]
theorem Equation3681_implies_Equation3675 (G : Type*) [Magma G] (h : Equation3681 G) : Equation3675 G := λ x y => h x y x
@[equational_result]
theorem Equation3682_implies_Equation3674 (G : Type*) [Magma G] (h : Equation3682 G) : Equation3674 G := λ x y => h x y x
@[equational_result]
theorem Equation3686_implies_Equation3684 (G : Type*) [Magma G] (h : Equation3686 G) : Equation3684 G := λ x y => h x y x
@[equational_result]
theorem Equation3689_implies_Equation3687 (G : Type*) [Magma G] (h : Equation3689 G) : Equation3687 G := λ x y => h x y x
@[equational_result]
theorem Equation3690_implies_Equation3684 (G : Type*) [Magma G] (h : Equation3690 G) : Equation3684 G := λ x y => h x y x
@[equational_result]
theorem Equation3691_implies_Equation3685 (G : Type*) [Magma G] (h : Equation3691 G) : Equation3685 G := λ x y => h x y x
@[equational_result]
theorem Equation3692_implies_Equation3684 (G : Type*) [Magma G] (h : Equation3692 G) : Equation3684 G := λ x y => h x y x
@[equational_result]
theorem Equation3694_implies_Equation3674 (G : Type*) [Magma G] (h : Equation3694 G) : Equation3674 G := λ x y => h x y x
@[equational_result]
theorem Equation3695_implies_Equation3675 (G : Type*) [Magma G] (h : Equation3695 G) : Equation3675 G := λ x y => h x y x
@[equational_result]
theorem Equation3696_implies_Equation3674 (G : Type*) [Magma G] (h : Equation3696 G) : Equation3674 G := λ x y => h x y x
@[equational_result]
theorem Equation3698_implies_Equation3677 (G : Type*) [Magma G] (h : Equation3698 G) : Equation3677 G := λ x y => h x y x
@[equational_result]
theorem Equation3699_implies_Equation3678 (G : Type*) [Magma G] (h : Equation3699 G) : Equation3678 G := λ x y => h x y x
@[equational_result]
theorem Equation3700_implies_Equation3677 (G : Type*) [Magma G] (h : Equation3700 G) : Equation3677 G := λ x y => h x y x
@[equational_result]
theorem Equation3702_implies_Equation3674 (G : Type*) [Magma G] (h : Equation3702 G) : Equation3674 G := λ x y => h x y x
@[equational_result]
theorem Equation3703_implies_Equation3675 (G : Type*) [Magma G] (h : Equation3703 G) : Equation3675 G := λ x y => h x y x
@[equational_result]
theorem Equation3704_implies_Equation3674 (G : Type*) [Magma G] (h : Equation3704 G) : Equation3674 G := λ x y => h x y x
@[equational_result]
theorem Equation3713_implies_Equation3711 (G : Type*) [Magma G] (h : Equation3713 G) : Equation3711 G := λ x y => h x y x
@[equational_result]
theorem Equation3716_implies_Equation3714 (G : Type*) [Magma G] (h : Equation3716 G) : Equation3714 G := λ x y => h x y x
@[equational_result]
theorem Equation3717_implies_Equation3711 (G : Type*) [Magma G] (h : Equation3717 G) : Equation3711 G := λ x y => h x y x
@[equational_result]
theorem Equation3718_implies_Equation3712 (G : Type*) [Magma G] (h : Equation3718 G) : Equation3712 G := λ x y => h x y x
@[equational_result]
theorem Equation3719_implies_Equation3711 (G : Type*) [Magma G] (h : Equation3719 G) : Equation3711 G := λ x y => h x y x
@[equational_result]
theorem Equation3723_implies_Equation3721 (G : Type*) [Magma G] (h : Equation3723 G) : Equation3721 G := λ x y => h x y x
@[equational_result]
theorem Equation3726_implies_Equation3724 (G : Type*) [Magma G] (h : Equation3726 G) : Equation3724 G := λ x y => h x y x
@[equational_result]
theorem Equation3727_implies_Equation3721 (G : Type*) [Magma G] (h : Equation3727 G) : Equation3721 G := λ x y => h x y x
@[equational_result]
theorem Equation3728_implies_Equation3722 (G : Type*) [Magma G] (h : Equation3728 G) : Equation3722 G := λ x y => h x y x
@[equational_result]
theorem Equation3729_implies_Equation3721 (G : Type*) [Magma G] (h : Equation3729 G) : Equation3721 G := λ x y => h x y x
@[equational_result]
theorem Equation3731_implies_Equation3711 (G : Type*) [Magma G] (h : Equation3731 G) : Equation3711 G := λ x y => h x y x
@[equational_result]
theorem Equation3732_implies_Equation3712 (G : Type*) [Magma G] (h : Equation3732 G) : Equation3712 G := λ x y => h x y x
@[equational_result]
theorem Equation3733_implies_Equation3711 (G : Type*) [Magma G] (h : Equation3733 G) : Equation3711 G := λ x y => h x y x
@[equational_result]
theorem Equation3735_implies_Equation3714 (G : Type*) [Magma G] (h : Equation3735 G) : Equation3714 G := λ x y => h x y x
@[equational_result]
theorem Equation3736_implies_Equation3715 (G : Type*) [Magma G] (h : Equation3736 G) : Equation3715 G := λ x y => h x y x
@[equational_result]
theorem Equation3737_implies_Equation3714 (G : Type*) [Magma G] (h : Equation3737 G) : Equation3714 G := λ x y => h x y x
@[equational_result]
theorem Equation3739_implies_Equation3711 (G : Type*) [Magma G] (h : Equation3739 G) : Equation3711 G := λ x y => h x y x
@[equational_result]
theorem Equation3740_implies_Equation3712 (G : Type*) [Magma G] (h : Equation3740 G) : Equation3712 G := λ x y => h x y x
@[equational_result]
theorem Equation3741_implies_Equation3711 (G : Type*) [Magma G] (h : Equation3741 G) : Equation3711 G := λ x y => h x y x
@[equational_result]
theorem Equation3750_implies_Equation3748 (G : Type*) [Magma G] (h : Equation3750 G) : Equation3748 G := λ x y => h x y x
@[equational_result]
theorem Equation3753_implies_Equation3751 (G : Type*) [Magma G] (h : Equation3753 G) : Equation3751 G := λ x y => h x y x
@[equational_result]
theorem Equation3754_implies_Equation3748 (G : Type*) [Magma G] (h : Equation3754 G) : Equation3748 G := λ x y => h x y x
@[equational_result]
theorem Equation3755_implies_Equation3749 (G : Type*) [Magma G] (h : Equation3755 G) : Equation3749 G := λ x y => h x y x
@[equational_result]
theorem Equation3756_implies_Equation3748 (G : Type*) [Magma G] (h : Equation3756 G) : Equation3748 G := λ x y => h x y x
@[equational_result]
theorem Equation3760_implies_Equation3758 (G : Type*) [Magma G] (h : Equation3760 G) : Equation3758 G := λ x y => h x y x
@[equational_result]
theorem Equation3763_implies_Equation3761 (G : Type*) [Magma G] (h : Equation3763 G) : Equation3761 G := λ x y => h x y x
@[equational_result]
theorem Equation3764_implies_Equation3758 (G : Type*) [Magma G] (h : Equation3764 G) : Equation3758 G := λ x y => h x y x
@[equational_result]
theorem Equation3765_implies_Equation3759 (G : Type*) [Magma G] (h : Equation3765 G) : Equation3759 G := λ x y => h x y x
@[equational_result]
theorem Equation3766_implies_Equation3758 (G : Type*) [Magma G] (h : Equation3766 G) : Equation3758 G := λ x y => h x y x
@[equational_result]
theorem Equation3768_implies_Equation3748 (G : Type*) [Magma G] (h : Equation3768 G) : Equation3748 G := λ x y => h x y x
@[equational_result]
theorem Equation3769_implies_Equation3749 (G : Type*) [Magma G] (h : Equation3769 G) : Equation3749 G := λ x y => h x y x
@[equational_result]
theorem Equation3770_implies_Equation3748 (G : Type*) [Magma G] (h : Equation3770 G) : Equation3748 G := λ x y => h x y x
@[equational_result]
theorem Equation3772_implies_Equation3751 (G : Type*) [Magma G] (h : Equation3772 G) : Equation3751 G := λ x y => h x y x
@[equational_result]
theorem Equation3773_implies_Equation3752 (G : Type*) [Magma G] (h : Equation3773 G) : Equation3752 G := λ x y => h x y x
@[equational_result]
theorem Equation3774_implies_Equation3751 (G : Type*) [Magma G] (h : Equation3774 G) : Equation3751 G := λ x y => h x y x
@[equational_result]
theorem Equation3776_implies_Equation3748 (G : Type*) [Magma G] (h : Equation3776 G) : Equation3748 G := λ x y => h x y x
@[equational_result]
theorem Equation3777_implies_Equation3749 (G : Type*) [Magma G] (h : Equation3777 G) : Equation3749 G := λ x y => h x y x
@[equational_result]
theorem Equation3778_implies_Equation3748 (G : Type*) [Magma G] (h : Equation3778 G) : Equation3748 G := λ x y => h x y x
@[equational_result]
theorem Equation3785_implies_Equation3711 (G : Type*) [Magma G] (h : Equation3785 G) : Equation3711 G := λ x y => h x y x
@[equational_result]
theorem Equation3786_implies_Equation3712 (G : Type*) [Magma G] (h : Equation3786 G) : Equation3712 G := λ x y => h x y x
@[equational_result]
theorem Equation3787_implies_Equation3711 (G : Type*) [Magma G] (h : Equation3787 G) : Equation3711 G := λ x y => h x y x
@[equational_result]
theorem Equation3789_implies_Equation3714 (G : Type*) [Magma G] (h : Equation3789 G) : Equation3714 G := λ x y => h x y x
@[equational_result]
theorem Equation3790_implies_Equation3715 (G : Type*) [Magma G] (h : Equation3790 G) : Equation3715 G := λ x y => h x y x
@[equational_result]
theorem Equation3791_implies_Equation3714 (G : Type*) [Magma G] (h : Equation3791 G) : Equation3714 G := λ x y => h x y x
@[equational_result]
theorem Equation3793_implies_Equation3711 (G : Type*) [Magma G] (h : Equation3793 G) : Equation3711 G := λ x y => h x y x
@[equational_result]
theorem Equation3794_implies_Equation3712 (G : Type*) [Magma G] (h : Equation3794 G) : Equation3712 G := λ x y => h x y x
@[equational_result]
theorem Equation3795_implies_Equation3711 (G : Type*) [Magma G] (h : Equation3795 G) : Equation3711 G := λ x y => h x y x
@[equational_result]
theorem Equation3802_implies_Equation3721 (G : Type*) [Magma G] (h : Equation3802 G) : Equation3721 G := λ x y => h x y x
@[equational_result]
theorem Equation3803_implies_Equation3722 (G : Type*) [Magma G] (h : Equation3803 G) : Equation3722 G := λ x y => h x y x
@[equational_result]
theorem Equation3804_implies_Equation3721 (G : Type*) [Magma G] (h : Equation3804 G) : Equation3721 G := λ x y => h x y x
@[equational_result]
theorem Equation3806_implies_Equation3724 (G : Type*) [Magma G] (h : Equation3806 G) : Equation3724 G := λ x y => h x y x
@[equational_result]
theorem Equation3807_implies_Equation3725 (G : Type*) [Magma G] (h : Equation3807 G) : Equation3725 G := λ x y => h x y x
@[equational_result]
theorem Equation3808_implies_Equation3724 (G : Type*) [Magma G] (h : Equation3808 G) : Equation3724 G := λ x y => h x y x
@[equational_result]
theorem Equation3810_implies_Equation3721 (G : Type*) [Magma G] (h : Equation3810 G) : Equation3721 G := λ x y => h x y x
@[equational_result]
theorem Equation3811_implies_Equation3722 (G : Type*) [Magma G] (h : Equation3811 G) : Equation3722 G := λ x y => h x y x
@[equational_result]
theorem Equation3812_implies_Equation3721 (G : Type*) [Magma G] (h : Equation3812 G) : Equation3721 G := λ x y => h x y x
@[equational_result]
theorem Equation3819_implies_Equation3711 (G : Type*) [Magma G] (h : Equation3819 G) : Equation3711 G := λ x y => h x y x
@[equational_result]
theorem Equation3820_implies_Equation3712 (G : Type*) [Magma G] (h : Equation3820 G) : Equation3712 G := λ x y => h x y x
@[equational_result]
theorem Equation3821_implies_Equation3711 (G : Type*) [Magma G] (h : Equation3821 G) : Equation3711 G := λ x y => h x y x
@[equational_result]
theorem Equation3823_implies_Equation3714 (G : Type*) [Magma G] (h : Equation3823 G) : Equation3714 G := λ x y => h x y x
@[equational_result]
theorem Equation3824_implies_Equation3715 (G : Type*) [Magma G] (h : Equation3824 G) : Equation3715 G := λ x y => h x y x
@[equational_result]
theorem Equation3825_implies_Equation3714 (G : Type*) [Magma G] (h : Equation3825 G) : Equation3714 G := λ x y => h x y x
@[equational_result]
theorem Equation3827_implies_Equation3711 (G : Type*) [Magma G] (h : Equation3827 G) : Equation3711 G := λ x y => h x y x
@[equational_result]
theorem Equation3828_implies_Equation3712 (G : Type*) [Magma G] (h : Equation3828 G) : Equation3712 G := λ x y => h x y x
@[equational_result]
theorem Equation3829_implies_Equation3711 (G : Type*) [Magma G] (h : Equation3829 G) : Equation3711 G := λ x y => h x y x
@[equational_result]
theorem Equation3866_implies_Equation3864 (G : Type*) [Magma G] (h : Equation3866 G) : Equation3864 G := λ x y => h x y x
@[equational_result]
theorem Equation3869_implies_Equation3867 (G : Type*) [Magma G] (h : Equation3869 G) : Equation3867 G := λ x y => h x y x
@[equational_result]
theorem Equation3872_implies_Equation3870 (G : Type*) [Magma G] (h : Equation3872 G) : Equation3870 G := λ x y => h x y x
@[equational_result]
theorem Equation3873_implies_Equation3867 (G : Type*) [Magma G] (h : Equation3873 G) : Equation3867 G := λ x y => h x y x
@[equational_result]
theorem Equation3874_implies_Equation3868 (G : Type*) [Magma G] (h : Equation3874 G) : Equation3868 G := λ x y => h x y x
@[equational_result]
theorem Equation3875_implies_Equation3867 (G : Type*) [Magma G] (h : Equation3875 G) : Equation3867 G := λ x y => h x y x
@[equational_result]
theorem Equation3879_implies_Equation3877 (G : Type*) [Magma G] (h : Equation3879 G) : Equation3877 G := λ x y => h x y x
@[equational_result]
theorem Equation3882_implies_Equation3880 (G : Type*) [Magma G] (h : Equation3882 G) : Equation3880 G := λ x y => h x y x
@[equational_result]
theorem Equation3883_implies_Equation3877 (G : Type*) [Magma G] (h : Equation3883 G) : Equation3877 G := λ x y => h x y x
@[equational_result]
theorem Equation3884_implies_Equation3878 (G : Type*) [Magma G] (h : Equation3884 G) : Equation3878 G := λ x y => h x y x
@[equational_result]
theorem Equation3885_implies_Equation3877 (G : Type*) [Magma G] (h : Equation3885 G) : Equation3877 G := λ x y => h x y x
@[equational_result]
theorem Equation3889_implies_Equation3887 (G : Type*) [Magma G] (h : Equation3889 G) : Equation3887 G := λ x y => h x y x
@[equational_result]
theorem Equation3892_implies_Equation3890 (G : Type*) [Magma G] (h : Equation3892 G) : Equation3890 G := λ x y => h x y x
@[equational_result]
theorem Equation3893_implies_Equation3887 (G : Type*) [Magma G] (h : Equation3893 G) : Equation3887 G := λ x y => h x y x
@[equational_result]
theorem Equation3894_implies_Equation3888 (G : Type*) [Magma G] (h : Equation3894 G) : Equation3888 G := λ x y => h x y x
@[equational_result]
theorem Equation3895_implies_Equation3887 (G : Type*) [Magma G] (h : Equation3895 G) : Equation3887 G := λ x y => h x y x
@[equational_result]
theorem Equation3897_implies_Equation3877 (G : Type*) [Magma G] (h : Equation3897 G) : Equation3877 G := λ x y => h x y x
@[equational_result]
theorem Equation3898_implies_Equation3878 (G : Type*) [Magma G] (h : Equation3898 G) : Equation3878 G := λ x y => h x y x
@[equational_result]
theorem Equation3899_implies_Equation3877 (G : Type*) [Magma G] (h : Equation3899 G) : Equation3877 G := λ x y => h x y x
@[equational_result]
theorem Equation3901_implies_Equation3880 (G : Type*) [Magma G] (h : Equation3901 G) : Equation3880 G := λ x y => h x y x
@[equational_result]
theorem Equation3902_implies_Equation3881 (G : Type*) [Magma G] (h : Equation3902 G) : Equation3881 G := λ x y => h x y x
@[equational_result]
theorem Equation3903_implies_Equation3880 (G : Type*) [Magma G] (h : Equation3903 G) : Equation3880 G := λ x y => h x y x
@[equational_result]
theorem Equation3905_implies_Equation3877 (G : Type*) [Magma G] (h : Equation3905 G) : Equation3877 G := λ x y => h x y x
@[equational_result]
theorem Equation3906_implies_Equation3878 (G : Type*) [Magma G] (h : Equation3906 G) : Equation3878 G := λ x y => h x y x
@[equational_result]
theorem Equation3907_implies_Equation3877 (G : Type*) [Magma G] (h : Equation3907 G) : Equation3877 G := λ x y => h x y x
@[equational_result]
theorem Equation3916_implies_Equation3914 (G : Type*) [Magma G] (h : Equation3916 G) : Equation3914 G := λ x y => h x y x
@[equational_result]
theorem Equation3919_implies_Equation3917 (G : Type*) [Magma G] (h : Equation3919 G) : Equation3917 G := λ x y => h x y x
@[equational_result]
theorem Equation3920_implies_Equation3914 (G : Type*) [Magma G] (h : Equation3920 G) : Equation3914 G := λ x y => h x y x
@[equational_result]
theorem Equation3921_implies_Equation3915 (G : Type*) [Magma G] (h : Equation3921 G) : Equation3915 G := λ x y => h x y x
@[equational_result]
theorem Equation3922_implies_Equation3914 (G : Type*) [Magma G] (h : Equation3922 G) : Equation3914 G := λ x y => h x y x
@[equational_result]
theorem Equation3926_implies_Equation3924 (G : Type*) [Magma G] (h : Equation3926 G) : Equation3924 G := λ x y => h x y x
@[equational_result]
theorem Equation3929_implies_Equation3927 (G : Type*) [Magma G] (h : Equation3929 G) : Equation3927 G := λ x y => h x y x
@[equational_result]
theorem Equation3930_implies_Equation3924 (G : Type*) [Magma G] (h : Equation3930 G) : Equation3924 G := λ x y => h x y x
@[equational_result]
theorem Equation3931_implies_Equation3925 (G : Type*) [Magma G] (h : Equation3931 G) : Equation3925 G := λ x y => h x y x
@[equational_result]
theorem Equation3932_implies_Equation3924 (G : Type*) [Magma G] (h : Equation3932 G) : Equation3924 G := λ x y => h x y x
@[equational_result]
theorem Equation3934_implies_Equation3914 (G : Type*) [Magma G] (h : Equation3934 G) : Equation3914 G := λ x y => h x y x
@[equational_result]
theorem Equation3935_implies_Equation3915 (G : Type*) [Magma G] (h : Equation3935 G) : Equation3915 G := λ x y => h x y x
@[equational_result]
theorem Equation3936_implies_Equation3914 (G : Type*) [Magma G] (h : Equation3936 G) : Equation3914 G := λ x y => h x y x
@[equational_result]
theorem Equation3938_implies_Equation3917 (G : Type*) [Magma G] (h : Equation3938 G) : Equation3917 G := λ x y => h x y x
@[equational_result]
theorem Equation3939_implies_Equation3918 (G : Type*) [Magma G] (h : Equation3939 G) : Equation3918 G := λ x y => h x y x
@[equational_result]
theorem Equation3940_implies_Equation3917 (G : Type*) [Magma G] (h : Equation3940 G) : Equation3917 G := λ x y => h x y x
@[equational_result]
theorem Equation3942_implies_Equation3914 (G : Type*) [Magma G] (h : Equation3942 G) : Equation3914 G := λ x y => h x y x
@[equational_result]
theorem Equation3943_implies_Equation3915 (G : Type*) [Magma G] (h : Equation3943 G) : Equation3915 G := λ x y => h x y x
@[equational_result]
theorem Equation3944_implies_Equation3914 (G : Type*) [Magma G] (h : Equation3944 G) : Equation3914 G := λ x y => h x y x
@[equational_result]
theorem Equation3953_implies_Equation3951 (G : Type*) [Magma G] (h : Equation3953 G) : Equation3951 G := λ x y => h x y x
@[equational_result]
theorem Equation3956_implies_Equation3954 (G : Type*) [Magma G] (h : Equation3956 G) : Equation3954 G := λ x y => h x y x
@[equational_result]
theorem Equation3957_implies_Equation3951 (G : Type*) [Magma G] (h : Equation3957 G) : Equation3951 G := λ x y => h x y x
@[equational_result]
theorem Equation3958_implies_Equation3952 (G : Type*) [Magma G] (h : Equation3958 G) : Equation3952 G := λ x y => h x y x
@[equational_result]
theorem Equation3959_implies_Equation3951 (G : Type*) [Magma G] (h : Equation3959 G) : Equation3951 G := λ x y => h x y x
@[equational_result]
theorem Equation3963_implies_Equation3961 (G : Type*) [Magma G] (h : Equation3963 G) : Equation3961 G := λ x y => h x y x
@[equational_result]
theorem Equation3966_implies_Equation3964 (G : Type*) [Magma G] (h : Equation3966 G) : Equation3964 G := λ x y => h x y x
@[equational_result]
theorem Equation3967_implies_Equation3961 (G : Type*) [Magma G] (h : Equation3967 G) : Equation3961 G := λ x y => h x y x
@[equational_result]
theorem Equation3968_implies_Equation3962 (G : Type*) [Magma G] (h : Equation3968 G) : Equation3962 G := λ x y => h x y x
@[equational_result]
theorem Equation3969_implies_Equation3961 (G : Type*) [Magma G] (h : Equation3969 G) : Equation3961 G := λ x y => h x y x
@[equational_result]
theorem Equation3971_implies_Equation3951 (G : Type*) [Magma G] (h : Equation3971 G) : Equation3951 G := λ x y => h x y x
@[equational_result]
theorem Equation3972_implies_Equation3952 (G : Type*) [Magma G] (h : Equation3972 G) : Equation3952 G := λ x y => h x y x
@[equational_result]
theorem Equation3973_implies_Equation3951 (G : Type*) [Magma G] (h : Equation3973 G) : Equation3951 G := λ x y => h x y x
@[equational_result]
theorem Equation3975_implies_Equation3954 (G : Type*) [Magma G] (h : Equation3975 G) : Equation3954 G := λ x y => h x y x
@[equational_result]
theorem Equation3976_implies_Equation3955 (G : Type*) [Magma G] (h : Equation3976 G) : Equation3955 G := λ x y => h x y x
@[equational_result]
theorem Equation3977_implies_Equation3954 (G : Type*) [Magma G] (h : Equation3977 G) : Equation3954 G := λ x y => h x y x
@[equational_result]
theorem Equation3979_implies_Equation3951 (G : Type*) [Magma G] (h : Equation3979 G) : Equation3951 G := λ x y => h x y x
@[equational_result]
theorem Equation3980_implies_Equation3952 (G : Type*) [Magma G] (h : Equation3980 G) : Equation3952 G := λ x y => h x y x
@[equational_result]
theorem Equation3981_implies_Equation3951 (G : Type*) [Magma G] (h : Equation3981 G) : Equation3951 G := λ x y => h x y x
@[equational_result]
theorem Equation3988_implies_Equation3914 (G : Type*) [Magma G] (h : Equation3988 G) : Equation3914 G := λ x y => h x y x
@[equational_result]
theorem Equation3989_implies_Equation3915 (G : Type*) [Magma G] (h : Equation3989 G) : Equation3915 G := λ x y => h x y x
@[equational_result]
theorem Equation3990_implies_Equation3914 (G : Type*) [Magma G] (h : Equation3990 G) : Equation3914 G := λ x y => h x y x
@[equational_result]
theorem Equation3992_implies_Equation3917 (G : Type*) [Magma G] (h : Equation3992 G) : Equation3917 G := λ x y => h x y x
@[equational_result]
theorem Equation3993_implies_Equation3918 (G : Type*) [Magma G] (h : Equation3993 G) : Equation3918 G := λ x y => h x y x
@[equational_result]
theorem Equation3994_implies_Equation3917 (G : Type*) [Magma G] (h : Equation3994 G) : Equation3917 G := λ x y => h x y x
@[equational_result]
theorem Equation3996_implies_Equation3914 (G : Type*) [Magma G] (h : Equation3996 G) : Equation3914 G := λ x y => h x y x
@[equational_result]
theorem Equation3997_implies_Equation3915 (G : Type*) [Magma G] (h : Equation3997 G) : Equation3915 G := λ x y => h x y x
@[equational_result]
theorem Equation3998_implies_Equation3914 (G : Type*) [Magma G] (h : Equation3998 G) : Equation3914 G := λ x y => h x y x
@[equational_result]
theorem Equation4005_implies_Equation3924 (G : Type*) [Magma G] (h : Equation4005 G) : Equation3924 G := λ x y => h x y x
@[equational_result]
theorem Equation4006_implies_Equation3925 (G : Type*) [Magma G] (h : Equation4006 G) : Equation3925 G := λ x y => h x y x
@[equational_result]
theorem Equation4007_implies_Equation3924 (G : Type*) [Magma G] (h : Equation4007 G) : Equation3924 G := λ x y => h x y x
@[equational_result]
theorem Equation4009_implies_Equation3927 (G : Type*) [Magma G] (h : Equation4009 G) : Equation3927 G := λ x y => h x y x
@[equational_result]
theorem Equation4010_implies_Equation3928 (G : Type*) [Magma G] (h : Equation4010 G) : Equation3928 G := λ x y => h x y x
@[equational_result]
theorem Equation4011_implies_Equation3927 (G : Type*) [Magma G] (h : Equation4011 G) : Equation3927 G := λ x y => h x y x
@[equational_result]
theorem Equation4013_implies_Equation3924 (G : Type*) [Magma G] (h : Equation4013 G) : Equation3924 G := λ x y => h x y x
@[equational_result]
theorem Equation4014_implies_Equation3925 (G : Type*) [Magma G] (h : Equation4014 G) : Equation3925 G := λ x y => h x y x
@[equational_result]
theorem Equation4015_implies_Equation3924 (G : Type*) [Magma G] (h : Equation4015 G) : Equation3924 G := λ x y => h x y x
@[equational_result]
theorem Equation4022_implies_Equation3914 (G : Type*) [Magma G] (h : Equation4022 G) : Equation3914 G := λ x y => h x y x
@[equational_result]
theorem Equation4023_implies_Equation3915 (G : Type*) [Magma G] (h : Equation4023 G) : Equation3915 G := λ x y => h x y x
@[equational_result]
theorem Equation4024_implies_Equation3914 (G : Type*) [Magma G] (h : Equation4024 G) : Equation3914 G := λ x y => h x y x
@[equational_result]
theorem Equation4026_implies_Equation3917 (G : Type*) [Magma G] (h : Equation4026 G) : Equation3917 G := λ x y => h x y x
@[equational_result]
theorem Equation4027_implies_Equation3918 (G : Type*) [Magma G] (h : Equation4027 G) : Equation3918 G := λ x y => h x y x
@[equational_result]
theorem Equation4028_implies_Equation3917 (G : Type*) [Magma G] (h : Equation4028 G) : Equation3917 G := λ x y => h x y x
@[equational_result]
theorem Equation4030_implies_Equation3914 (G : Type*) [Magma G] (h : Equation4030 G) : Equation3914 G := λ x y => h x y x
@[equational_result]
theorem Equation4031_implies_Equation3915 (G : Type*) [Magma G] (h : Equation4031 G) : Equation3915 G := λ x y => h x y x
@[equational_result]
theorem Equation4032_implies_Equation3914 (G : Type*) [Magma G] (h : Equation4032 G) : Equation3914 G := λ x y => h x y x
@[equational_result]
theorem Equation4069_implies_Equation4067 (G : Type*) [Magma G] (h : Equation4069 G) : Equation4067 G := λ x y => h x y x
@[equational_result]
theorem Equation4072_implies_Equation4070 (G : Type*) [Magma G] (h : Equation4072 G) : Equation4070 G := λ x y => h x y x
@[equational_result]
theorem Equation4075_implies_Equation4073 (G : Type*) [Magma G] (h : Equation4075 G) : Equation4073 G := λ x y => h x y x
@[equational_result]
theorem Equation4076_implies_Equation4070 (G : Type*) [Magma G] (h : Equation4076 G) : Equation4070 G := λ x y => h x y x
@[equational_result]
theorem Equation4077_implies_Equation4071 (G : Type*) [Magma G] (h : Equation4077 G) : Equation4071 G := λ x y => h x y x
@[equational_result]
theorem Equation4078_implies_Equation4070 (G : Type*) [Magma G] (h : Equation4078 G) : Equation4070 G := λ x y => h x y x
@[equational_result]
theorem Equation4082_implies_Equation4080 (G : Type*) [Magma G] (h : Equation4082 G) : Equation4080 G := λ x y => h x y x
@[equational_result]
theorem Equation4085_implies_Equation4083 (G : Type*) [Magma G] (h : Equation4085 G) : Equation4083 G := λ x y => h x y x
@[equational_result]
theorem Equation4086_implies_Equation4080 (G : Type*) [Magma G] (h : Equation4086 G) : Equation4080 G := λ x y => h x y x
@[equational_result]
theorem Equation4087_implies_Equation4081 (G : Type*) [Magma G] (h : Equation4087 G) : Equation4081 G := λ x y => h x y x
@[equational_result]
theorem Equation4088_implies_Equation4080 (G : Type*) [Magma G] (h : Equation4088 G) : Equation4080 G := λ x y => h x y x
@[equational_result]
theorem Equation4092_implies_Equation4090 (G : Type*) [Magma G] (h : Equation4092 G) : Equation4090 G := λ x y => h x y x
@[equational_result]
theorem Equation4095_implies_Equation4093 (G : Type*) [Magma G] (h : Equation4095 G) : Equation4093 G := λ x y => h x y x
@[equational_result]
theorem Equation4096_implies_Equation4090 (G : Type*) [Magma G] (h : Equation4096 G) : Equation4090 G := λ x y => h x y x
@[equational_result]
theorem Equation4097_implies_Equation4091 (G : Type*) [Magma G] (h : Equation4097 G) : Equation4091 G := λ x y => h x y x
@[equational_result]
theorem Equation4098_implies_Equation4090 (G : Type*) [Magma G] (h : Equation4098 G) : Equation4090 G := λ x y => h x y x
@[equational_result]
theorem Equation4100_implies_Equation4080 (G : Type*) [Magma G] (h : Equation4100 G) : Equation4080 G := λ x y => h x y x
@[equational_result]
theorem Equation4101_implies_Equation4081 (G : Type*) [Magma G] (h : Equation4101 G) : Equation4081 G := λ x y => h x y x
@[equational_result]
theorem Equation4102_implies_Equation4080 (G : Type*) [Magma G] (h : Equation4102 G) : Equation4080 G := λ x y => h x y x
@[equational_result]
theorem Equation4104_implies_Equation4083 (G : Type*) [Magma G] (h : Equation4104 G) : Equation4083 G := λ x y => h x y x
@[equational_result]
theorem Equation4105_implies_Equation4084 (G : Type*) [Magma G] (h : Equation4105 G) : Equation4084 G := λ x y => h x y x
@[equational_result]
theorem Equation4106_implies_Equation4083 (G : Type*) [Magma G] (h : Equation4106 G) : Equation4083 G := λ x y => h x y x
@[equational_result]
theorem Equation4108_implies_Equation4080 (G : Type*) [Magma G] (h : Equation4108 G) : Equation4080 G := λ x y => h x y x
@[equational_result]
theorem Equation4109_implies_Equation4081 (G : Type*) [Magma G] (h : Equation4109 G) : Equation4081 G := λ x y => h x y x
@[equational_result]
theorem Equation4110_implies_Equation4080 (G : Type*) [Magma G] (h : Equation4110 G) : Equation4080 G := λ x y => h x y x
@[equational_result]
theorem Equation4119_implies_Equation4117 (G : Type*) [Magma G] (h : Equation4119 G) : Equation4117 G := λ x y => h x y x
@[equational_result]
theorem Equation4122_implies_Equation4120 (G : Type*) [Magma G] (h : Equation4122 G) : Equation4120 G := λ x y => h x y x
@[equational_result]
theorem Equation4123_implies_Equation4117 (G : Type*) [Magma G] (h : Equation4123 G) : Equation4117 G := λ x y => h x y x
@[equational_result]
theorem Equation4124_implies_Equation4118 (G : Type*) [Magma G] (h : Equation4124 G) : Equation4118 G := λ x y => h x y x
@[equational_result]
theorem Equation4125_implies_Equation4117 (G : Type*) [Magma G] (h : Equation4125 G) : Equation4117 G := λ x y => h x y x
@[equational_result]
theorem Equation4129_implies_Equation4127 (G : Type*) [Magma G] (h : Equation4129 G) : Equation4127 G := λ x y => h x y x
@[equational_result]
theorem Equation4132_implies_Equation4130 (G : Type*) [Magma G] (h : Equation4132 G) : Equation4130 G := λ x y => h x y x
@[equational_result]
theorem Equation4133_implies_Equation4127 (G : Type*) [Magma G] (h : Equation4133 G) : Equation4127 G := λ x y => h x y x
@[equational_result]
theorem Equation4134_implies_Equation4128 (G : Type*) [Magma G] (h : Equation4134 G) : Equation4128 G := λ x y => h x y x
@[equational_result]
theorem Equation4135_implies_Equation4127 (G : Type*) [Magma G] (h : Equation4135 G) : Equation4127 G := λ x y => h x y x
@[equational_result]
theorem Equation4137_implies_Equation4117 (G : Type*) [Magma G] (h : Equation4137 G) : Equation4117 G := λ x y => h x y x
@[equational_result]
theorem Equation4138_implies_Equation4118 (G : Type*) [Magma G] (h : Equation4138 G) : Equation4118 G := λ x y => h x y x
@[equational_result]
theorem Equation4139_implies_Equation4117 (G : Type*) [Magma G] (h : Equation4139 G) : Equation4117 G := λ x y => h x y x
@[equational_result]
theorem Equation4141_implies_Equation4120 (G : Type*) [Magma G] (h : Equation4141 G) : Equation4120 G := λ x y => h x y x
@[equational_result]
theorem Equation4142_implies_Equation4121 (G : Type*) [Magma G] (h : Equation4142 G) : Equation4121 G := λ x y => h x y x
@[equational_result]
theorem Equation4143_implies_Equation4120 (G : Type*) [Magma G] (h : Equation4143 G) : Equation4120 G := λ x y => h x y x
@[equational_result]
theorem Equation4145_implies_Equation4117 (G : Type*) [Magma G] (h : Equation4145 G) : Equation4117 G := λ x y => h x y x
@[equational_result]
theorem Equation4146_implies_Equation4118 (G : Type*) [Magma G] (h : Equation4146 G) : Equation4118 G := λ x y => h x y x
@[equational_result]
theorem Equation4147_implies_Equation4117 (G : Type*) [Magma G] (h : Equation4147 G) : Equation4117 G := λ x y => h x y x
@[equational_result]
theorem Equation4156_implies_Equation4154 (G : Type*) [Magma G] (h : Equation4156 G) : Equation4154 G := λ x y => h x y x
@[equational_result]
theorem Equation4159_implies_Equation4157 (G : Type*) [Magma G] (h : Equation4159 G) : Equation4157 G := λ x y => h x y x
@[equational_result]
theorem Equation4160_implies_Equation4154 (G : Type*) [Magma G] (h : Equation4160 G) : Equation4154 G := λ x y => h x y x
@[equational_result]
theorem Equation4161_implies_Equation4155 (G : Type*) [Magma G] (h : Equation4161 G) : Equation4155 G := λ x y => h x y x
@[equational_result]
theorem Equation4162_implies_Equation4154 (G : Type*) [Magma G] (h : Equation4162 G) : Equation4154 G := λ x y => h x y x
@[equational_result]
theorem Equation4166_implies_Equation4164 (G : Type*) [Magma G] (h : Equation4166 G) : Equation4164 G := λ x y => h x y x
@[equational_result]
theorem Equation4169_implies_Equation4167 (G : Type*) [Magma G] (h : Equation4169 G) : Equation4167 G := λ x y => h x y x
@[equational_result]
theorem Equation4170_implies_Equation4164 (G : Type*) [Magma G] (h : Equation4170 G) : Equation4164 G := λ x y => h x y x
@[equational_result]
theorem Equation4171_implies_Equation4165 (G : Type*) [Magma G] (h : Equation4171 G) : Equation4165 G := λ x y => h x y x
@[equational_result]
theorem Equation4172_implies_Equation4164 (G : Type*) [Magma G] (h : Equation4172 G) : Equation4164 G := λ x y => h x y x
@[equational_result]
theorem Equation4174_implies_Equation4154 (G : Type*) [Magma G] (h : Equation4174 G) : Equation4154 G := λ x y => h x y x
@[equational_result]
theorem Equation4175_implies_Equation4155 (G : Type*) [Magma G] (h : Equation4175 G) : Equation4155 G := λ x y => h x y x
@[equational_result]
theorem Equation4176_implies_Equation4154 (G : Type*) [Magma G] (h : Equation4176 G) : Equation4154 G := λ x y => h x y x
@[equational_result]
theorem Equation4178_implies_Equation4157 (G : Type*) [Magma G] (h : Equation4178 G) : Equation4157 G := λ x y => h x y x
@[equational_result]
theorem Equation4179_implies_Equation4158 (G : Type*) [Magma G] (h : Equation4179 G) : Equation4158 G := λ x y => h x y x
@[equational_result]
theorem Equation4180_implies_Equation4157 (G : Type*) [Magma G] (h : Equation4180 G) : Equation4157 G := λ x y => h x y x
@[equational_result]
theorem Equation4182_implies_Equation4154 (G : Type*) [Magma G] (h : Equation4182 G) : Equation4154 G := λ x y => h x y x
@[equational_result]
theorem Equation4183_implies_Equation4155 (G : Type*) [Magma G] (h : Equation4183 G) : Equation4155 G := λ x y => h x y x
@[equational_result]
theorem Equation4184_implies_Equation4154 (G : Type*) [Magma G] (h : Equation4184 G) : Equation4154 G := λ x y => h x y x
@[equational_result]
theorem Equation4191_implies_Equation4117 (G : Type*) [Magma G] (h : Equation4191 G) : Equation4117 G := λ x y => h x y x
@[equational_result]
theorem Equation4192_implies_Equation4118 (G : Type*) [Magma G] (h : Equation4192 G) : Equation4118 G := λ x y => h x y x
@[equational_result]
theorem Equation4193_implies_Equation4117 (G : Type*) [Magma G] (h : Equation4193 G) : Equation4117 G := λ x y => h x y x
@[equational_result]
theorem Equation4195_implies_Equation4120 (G : Type*) [Magma G] (h : Equation4195 G) : Equation4120 G := λ x y => h x y x
@[equational_result]
theorem Equation4196_implies_Equation4121 (G : Type*) [Magma G] (h : Equation4196 G) : Equation4121 G := λ x y => h x y x
@[equational_result]
theorem Equation4197_implies_Equation4120 (G : Type*) [Magma G] (h : Equation4197 G) : Equation4120 G := λ x y => h x y x
@[equational_result]
theorem Equation4199_implies_Equation4117 (G : Type*) [Magma G] (h : Equation4199 G) : Equation4117 G := λ x y => h x y x
@[equational_result]
theorem Equation4200_implies_Equation4118 (G : Type*) [Magma G] (h : Equation4200 G) : Equation4118 G := λ x y => h x y x
@[equational_result]
theorem Equation4201_implies_Equation4117 (G : Type*) [Magma G] (h : Equation4201 G) : Equation4117 G := λ x y => h x y x
@[equational_result]
theorem Equation4208_implies_Equation4127 (G : Type*) [Magma G] (h : Equation4208 G) : Equation4127 G := λ x y => h x y x
@[equational_result]
theorem Equation4209_implies_Equation4128 (G : Type*) [Magma G] (h : Equation4209 G) : Equation4128 G := λ x y => h x y x
@[equational_result]
theorem Equation4210_implies_Equation4127 (G : Type*) [Magma G] (h : Equation4210 G) : Equation4127 G := λ x y => h x y x
@[equational_result]
theorem Equation4212_implies_Equation4130 (G : Type*) [Magma G] (h : Equation4212 G) : Equation4130 G := λ x y => h x y x
@[equational_result]
theorem Equation4213_implies_Equation4131 (G : Type*) [Magma G] (h : Equation4213 G) : Equation4131 G := λ x y => h x y x
@[equational_result]
theorem Equation4214_implies_Equation4130 (G : Type*) [Magma G] (h : Equation4214 G) : Equation4130 G := λ x y => h x y x
@[equational_result]
theorem Equation4216_implies_Equation4127 (G : Type*) [Magma G] (h : Equation4216 G) : Equation4127 G := λ x y => h x y x
@[equational_result]
theorem Equation4217_implies_Equation4128 (G : Type*) [Magma G] (h : Equation4217 G) : Equation4128 G := λ x y => h x y x
@[equational_result]
theorem Equation4218_implies_Equation4127 (G : Type*) [Magma G] (h : Equation4218 G) : Equation4127 G := λ x y => h x y x
@[equational_result]
theorem Equation4225_implies_Equation4117 (G : Type*) [Magma G] (h : Equation4225 G) : Equation4117 G := λ x y => h x y x
@[equational_result]
theorem Equation4226_implies_Equation4118 (G : Type*) [Magma G] (h : Equation4226 G) : Equation4118 G := λ x y => h x y x
@[equational_result]
theorem Equation4227_implies_Equation4117 (G : Type*) [Magma G] (h : Equation4227 G) : Equation4117 G := λ x y => h x y x
@[equational_result]
theorem Equation4229_implies_Equation4120 (G : Type*) [Magma G] (h : Equation4229 G) : Equation4120 G := λ x y => h x y x
@[equational_result]
theorem Equation4230_implies_Equation4121 (G : Type*) [Magma G] (h : Equation4230 G) : Equation4121 G := λ x y => h x y x
@[equational_result]
theorem Equation4231_implies_Equation4120 (G : Type*) [Magma G] (h : Equation4231 G) : Equation4120 G := λ x y => h x y x
@[equational_result]
theorem Equation4233_implies_Equation4117 (G : Type*) [Magma G] (h : Equation4233 G) : Equation4117 G := λ x y => h x y x
@[equational_result]
theorem Equation4234_implies_Equation4118 (G : Type*) [Magma G] (h : Equation4234 G) : Equation4118 G := λ x y => h x y x
@[equational_result]
theorem Equation4235_implies_Equation4117 (G : Type*) [Magma G] (h : Equation4235 G) : Equation4117 G := λ x y => h x y x
@[equational_result]
theorem Equation4271_implies_Equation4269 (G : Type*) [Magma G] (h : Equation4271 G) : Equation4269 G := λ x y => h x y x
@[equational_result]
theorem Equation4274_implies_Equation4272 (G : Type*) [Magma G] (h : Equation4274 G) : Equation4272 G := λ x y => h x y x
@[equational_result]
theorem Equation4277_implies_Equation4275 (G : Type*) [Magma G] (h : Equation4277 G) : Equation4275 G := λ x y => h x y x
@[equational_result]
theorem Equation4278_implies_Equation4272 (G : Type*) [Magma G] (h : Equation4278 G) : Equation4272 G := λ x y => h x y x
@[equational_result]
theorem Equation4279_implies_Equation4273 (G : Type*) [Magma G] (h : Equation4279 G) : Equation4273 G := λ x y => h x y x
@[equational_result]
theorem Equation4280_implies_Equation4272 (G : Type*) [Magma G] (h : Equation4280 G) : Equation4272 G := λ x y => h x y x
@[equational_result]
theorem Equation4285_implies_Equation4283 (G : Type*) [Magma G] (h : Equation4285 G) : Equation4283 G := λ x y => h x y x
@[equational_result]
theorem Equation4292_implies_Equation4290 (G : Type*) [Magma G] (h : Equation4292 G) : Equation4290 G := λ x y => h x y x
@[equational_result]
theorem Equation4294_implies_Equation4293 (G : Type*) [Magma G] (h : Equation4294 G) : Equation4293 G := λ x y => h x y x
@[equational_result]
theorem Equation4295_implies_Equation4290 (G : Type*) [Magma G] (h : Equation4295 G) : Equation4290 G := λ x y => h x y x
@[equational_result]
theorem Equation4296_implies_Equation4291 (G : Type*) [Magma G] (h : Equation4296 G) : Equation4291 G := λ x y => h x y x
@[equational_result]
theorem Equation4297_implies_Equation4290 (G : Type*) [Magma G] (h : Equation4297 G) : Equation4290 G := λ x y => h x y x
@[equational_result]
theorem Equation4303_implies_Equation4283 (G : Type*) [Magma G] (h : Equation4303 G) : Equation4283 G := λ x y => h x y x
@[equational_result]
theorem Equation4304_implies_Equation4284 (G : Type*) [Magma G] (h : Equation4304 G) : Equation4284 G := λ x y => h x y x
@[equational_result]
theorem Equation4305_implies_Equation4283 (G : Type*) [Magma G] (h : Equation4305 G) : Equation4283 G := λ x y => h x y x
@[equational_result]
theorem Equation4322_implies_Equation4320 (G : Type*) [Magma G] (h : Equation4322 G) : Equation4320 G := λ x y => h x y x
@[equational_result]
theorem Equation4323_implies_Equation4320 (G : Type*) [Magma G] (h : Equation4323 G) : Equation4320 G := λ x y => h x y x
@[equational_result]
theorem Equation4324_implies_Equation4321 (G : Type*) [Magma G] (h : Equation4324 G) : Equation4321 G := λ x y => h x y x
@[equational_result]
theorem Equation4325_implies_Equation4320 (G : Type*) [Magma G] (h : Equation4325 G) : Equation4320 G := λ x y => h x y x
@[equational_result]
theorem Equation4331_implies_Equation4314 (G : Type*) [Magma G] (h : Equation4331 G) : Equation4314 G := λ x y => h x y x
@[equational_result]
theorem Equation4344_implies_Equation4343 (G : Type*) [Magma G] (h : Equation4344 G) : Equation4343 G := λ x y => h x y x
@[equational_result]
theorem Equation4345_implies_Equation4343 (G : Type*) [Magma G] (h : Equation4345 G) : Equation4343 G := λ x y => h x y x
@[equational_result]
theorem Equation4346_implies_Equation4343 (G : Type*) [Magma G] (h : Equation4346 G) : Equation4343 G := λ x y => h x y x
@[equational_result]
theorem Equation4362_implies_Equation4320 (G : Type*) [Magma G] (h : Equation4362 G) : Equation4320 G := λ x y => h x y x
@[equational_result]
theorem Equation4364_implies_Equation4320 (G : Type*) [Magma G] (h : Equation4364 G) : Equation4320 G := λ x y => h x y x
@[equational_result]
theorem Equation4384_implies_Equation4382 (G : Type*) [Magma G] (h : Equation4384 G) : Equation4382 G := λ x y => h x y x
@[equational_result]
theorem Equation4387_implies_Equation4385 (G : Type*) [Magma G] (h : Equation4387 G) : Equation4385 G := λ x y => h x y x
@[equational_result]
theorem Equation4390_implies_Equation4388 (G : Type*) [Magma G] (h : Equation4390 G) : Equation4388 G := λ x y => h x y x
@[equational_result]
theorem Equation4391_implies_Equation4385 (G : Type*) [Magma G] (h : Equation4391 G) : Equation4385 G := λ x y => h x y x
@[equational_result]
theorem Equation4392_implies_Equation4386 (G : Type*) [Magma G] (h : Equation4392 G) : Equation4386 G := λ x y => h x y x
@[equational_result]
theorem Equation4393_implies_Equation4385 (G : Type*) [Magma G] (h : Equation4393 G) : Equation4385 G := λ x y => h x y x
@[equational_result]
theorem Equation4397_implies_Equation4395 (G : Type*) [Magma G] (h : Equation4397 G) : Equation4395 G := λ x y => h x y x
@[equational_result]
theorem Equation4400_implies_Equation4398 (G : Type*) [Magma G] (h : Equation4400 G) : Equation4398 G := λ x y => h x y x
@[equational_result]
theorem Equation4401_implies_Equation4395 (G : Type*) [Magma G] (h : Equation4401 G) : Equation4395 G := λ x y => h x y x
@[equational_result]
theorem Equation4402_implies_Equation4396 (G : Type*) [Magma G] (h : Equation4402 G) : Equation4396 G := λ x y => h x y x
@[equational_result]
theorem Equation4403_implies_Equation4395 (G : Type*) [Magma G] (h : Equation4403 G) : Equation4395 G := λ x y => h x y x
@[equational_result]
theorem Equation4407_implies_Equation4405 (G : Type*) [Magma G] (h : Equation4407 G) : Equation4405 G := λ x y => h x y x
@[equational_result]
theorem Equation4410_implies_Equation4408 (G : Type*) [Magma G] (h : Equation4410 G) : Equation4408 G := λ x y => h x y x
@[equational_result]
theorem Equation4411_implies_Equation4405 (G : Type*) [Magma G] (h : Equation4411 G) : Equation4405 G := λ x y => h x y x
@[equational_result]
theorem Equation4412_implies_Equation4406 (G : Type*) [Magma G] (h : Equation4412 G) : Equation4406 G := λ x y => h x y x
@[equational_result]
theorem Equation4413_implies_Equation4405 (G : Type*) [Magma G] (h : Equation4413 G) : Equation4405 G := λ x y => h x y x
@[equational_result]
theorem Equation4415_implies_Equation4395 (G : Type*) [Magma G] (h : Equation4415 G) : Equation4395 G := λ x y => h x y x
@[equational_result]
theorem Equation4416_implies_Equation4396 (G : Type*) [Magma G] (h : Equation4416 G) : Equation4396 G := λ x y => h x y x
@[equational_result]
theorem Equation4417_implies_Equation4395 (G : Type*) [Magma G] (h : Equation4417 G) : Equation4395 G := λ x y => h x y x
@[equational_result]
theorem Equation4419_implies_Equation4398 (G : Type*) [Magma G] (h : Equation4419 G) : Equation4398 G := λ x y => h x y x
@[equational_result]
theorem Equation4420_implies_Equation4399 (G : Type*) [Magma G] (h : Equation4420 G) : Equation4399 G := λ x y => h x y x
@[equational_result]
theorem Equation4421_implies_Equation4398 (G : Type*) [Magma G] (h : Equation4421 G) : Equation4398 G := λ x y => h x y x
@[equational_result]
theorem Equation4423_implies_Equation4395 (G : Type*) [Magma G] (h : Equation4423 G) : Equation4395 G := λ x y => h x y x
@[equational_result]
theorem Equation4424_implies_Equation4396 (G : Type*) [Magma G] (h : Equation4424 G) : Equation4396 G := λ x y => h x y x
@[equational_result]
theorem Equation4425_implies_Equation4395 (G : Type*) [Magma G] (h : Equation4425 G) : Equation4395 G := λ x y => h x y x
@[equational_result]
theorem Equation4434_implies_Equation4432 (G : Type*) [Magma G] (h : Equation4434 G) : Equation4432 G := λ x y => h x y x
@[equational_result]
theorem Equation4437_implies_Equation4435 (G : Type*) [Magma G] (h : Equation4437 G) : Equation4435 G := λ x y => h x y x
@[equational_result]
theorem Equation4438_implies_Equation4432 (G : Type*) [Magma G] (h : Equation4438 G) : Equation4432 G := λ x y => h x y x
@[equational_result]
theorem Equation4439_implies_Equation4433 (G : Type*) [Magma G] (h : Equation4439 G) : Equation4433 G := λ x y => h x y x
@[equational_result]
theorem Equation4440_implies_Equation4432 (G : Type*) [Magma G] (h : Equation4440 G) : Equation4432 G := λ x y => h x y x
@[equational_result]
theorem Equation4444_implies_Equation4442 (G : Type*) [Magma G] (h : Equation4444 G) : Equation4442 G := λ x y => h x y x
@[equational_result]
theorem Equation4447_implies_Equation4445 (G : Type*) [Magma G] (h : Equation4447 G) : Equation4445 G := λ x y => h x y x
@[equational_result]
theorem Equation4448_implies_Equation4442 (G : Type*) [Magma G] (h : Equation4448 G) : Equation4442 G := λ x y => h x y x
@[equational_result]
theorem Equation4449_implies_Equation4443 (G : Type*) [Magma G] (h : Equation4449 G) : Equation4443 G := λ x y => h x y x
@[equational_result]
theorem Equation4450_implies_Equation4442 (G : Type*) [Magma G] (h : Equation4450 G) : Equation4442 G := λ x y => h x y x
@[equational_result]
theorem Equation4452_implies_Equation4432 (G : Type*) [Magma G] (h : Equation4452 G) : Equation4432 G := λ x y => h x y x
@[equational_result]
theorem Equation4453_implies_Equation4433 (G : Type*) [Magma G] (h : Equation4453 G) : Equation4433 G := λ x y => h x y x
@[equational_result]
theorem Equation4454_implies_Equation4432 (G : Type*) [Magma G] (h : Equation4454 G) : Equation4432 G := λ x y => h x y x
@[equational_result]
theorem Equation4456_implies_Equation4435 (G : Type*) [Magma G] (h : Equation4456 G) : Equation4435 G := λ x y => h x y x
@[equational_result]
theorem Equation4457_implies_Equation4436 (G : Type*) [Magma G] (h : Equation4457 G) : Equation4436 G := λ x y => h x y x
@[equational_result]
theorem Equation4458_implies_Equation4435 (G : Type*) [Magma G] (h : Equation4458 G) : Equation4435 G := λ x y => h x y x
@[equational_result]
theorem Equation4460_implies_Equation4432 (G : Type*) [Magma G] (h : Equation4460 G) : Equation4432 G := λ x y => h x y x
@[equational_result]
theorem Equation4461_implies_Equation4433 (G : Type*) [Magma G] (h : Equation4461 G) : Equation4433 G := λ x y => h x y x
@[equational_result]
theorem Equation4462_implies_Equation4432 (G : Type*) [Magma G] (h : Equation4462 G) : Equation4432 G := λ x y => h x y x
@[equational_result]
theorem Equation4471_implies_Equation4469 (G : Type*) [Magma G] (h : Equation4471 G) : Equation4469 G := λ x y => h x y x
@[equational_result]
theorem Equation4474_implies_Equation4472 (G : Type*) [Magma G] (h : Equation4474 G) : Equation4472 G := λ x y => h x y x
@[equational_result]
theorem Equation4475_implies_Equation4469 (G : Type*) [Magma G] (h : Equation4475 G) : Equation4469 G := λ x y => h x y x
@[equational_result]
theorem Equation4476_implies_Equation4470 (G : Type*) [Magma G] (h : Equation4476 G) : Equation4470 G := λ x y => h x y x
@[equational_result]
theorem Equation4477_implies_Equation4469 (G : Type*) [Magma G] (h : Equation4477 G) : Equation4469 G := λ x y => h x y x
@[equational_result]
theorem Equation4481_implies_Equation4479 (G : Type*) [Magma G] (h : Equation4481 G) : Equation4479 G := λ x y => h x y x
@[equational_result]
theorem Equation4484_implies_Equation4482 (G : Type*) [Magma G] (h : Equation4484 G) : Equation4482 G := λ x y => h x y x
@[equational_result]
theorem Equation4485_implies_Equation4479 (G : Type*) [Magma G] (h : Equation4485 G) : Equation4479 G := λ x y => h x y x
@[equational_result]
theorem Equation4486_implies_Equation4480 (G : Type*) [Magma G] (h : Equation4486 G) : Equation4480 G := λ x y => h x y x
@[equational_result]
theorem Equation4487_implies_Equation4479 (G : Type*) [Magma G] (h : Equation4487 G) : Equation4479 G := λ x y => h x y x
@[equational_result]
theorem Equation4489_implies_Equation4469 (G : Type*) [Magma G] (h : Equation4489 G) : Equation4469 G := λ x y => h x y x
@[equational_result]
theorem Equation4490_implies_Equation4470 (G : Type*) [Magma G] (h : Equation4490 G) : Equation4470 G := λ x y => h x y x
@[equational_result]
theorem Equation4491_implies_Equation4469 (G : Type*) [Magma G] (h : Equation4491 G) : Equation4469 G := λ x y => h x y x
@[equational_result]
theorem Equation4493_implies_Equation4472 (G : Type*) [Magma G] (h : Equation4493 G) : Equation4472 G := λ x y => h x y x
@[equational_result]
theorem Equation4494_implies_Equation4473 (G : Type*) [Magma G] (h : Equation4494 G) : Equation4473 G := λ x y => h x y x
@[equational_result]
theorem Equation4495_implies_Equation4472 (G : Type*) [Magma G] (h : Equation4495 G) : Equation4472 G := λ x y => h x y x
@[equational_result]
theorem Equation4497_implies_Equation4469 (G : Type*) [Magma G] (h : Equation4497 G) : Equation4469 G := λ x y => h x y x
@[equational_result]
theorem Equation4498_implies_Equation4470 (G : Type*) [Magma G] (h : Equation4498 G) : Equation4470 G := λ x y => h x y x
@[equational_result]
theorem Equation4499_implies_Equation4469 (G : Type*) [Magma G] (h : Equation4499 G) : Equation4469 G := λ x y => h x y x
@[equational_result]
theorem Equation4506_implies_Equation4432 (G : Type*) [Magma G] (h : Equation4506 G) : Equation4432 G := λ x y => h x y x
@[equational_result]
theorem Equation4507_implies_Equation4433 (G : Type*) [Magma G] (h : Equation4507 G) : Equation4433 G := λ x y => h x y x
@[equational_result]
theorem Equation4508_implies_Equation4432 (G : Type*) [Magma G] (h : Equation4508 G) : Equation4432 G := λ x y => h x y x
@[equational_result]
theorem Equation4510_implies_Equation4435 (G : Type*) [Magma G] (h : Equation4510 G) : Equation4435 G := λ x y => h x y x
@[equational_result]
theorem Equation4511_implies_Equation4436 (G : Type*) [Magma G] (h : Equation4511 G) : Equation4436 G := λ x y => h x y x
@[equational_result]
theorem Equation4512_implies_Equation4435 (G : Type*) [Magma G] (h : Equation4512 G) : Equation4435 G := λ x y => h x y x
@[equational_result]
theorem Equation4514_implies_Equation4432 (G : Type*) [Magma G] (h : Equation4514 G) : Equation4432 G := λ x y => h x y x
@[equational_result]
theorem Equation4515_implies_Equation4433 (G : Type*) [Magma G] (h : Equation4515 G) : Equation4433 G := λ x y => h x y x
@[equational_result]
theorem Equation4516_implies_Equation4432 (G : Type*) [Magma G] (h : Equation4516 G) : Equation4432 G := λ x y => h x y x
@[equational_result]
theorem Equation4523_implies_Equation4442 (G : Type*) [Magma G] (h : Equation4523 G) : Equation4442 G := λ x y => h x y x
@[equational_result]
theorem Equation4524_implies_Equation4443 (G : Type*) [Magma G] (h : Equation4524 G) : Equation4443 G := λ x y => h x y x
@[equational_result]
theorem Equation4525_implies_Equation4442 (G : Type*) [Magma G] (h : Equation4525 G) : Equation4442 G := λ x y => h x y x
@[equational_result]
theorem Equation4527_implies_Equation4445 (G : Type*) [Magma G] (h : Equation4527 G) : Equation4445 G := λ x y => h x y x
@[equational_result]
theorem Equation4528_implies_Equation4446 (G : Type*) [Magma G] (h : Equation4528 G) : Equation4446 G := λ x y => h x y x
@[equational_result]
theorem Equation4529_implies_Equation4445 (G : Type*) [Magma G] (h : Equation4529 G) : Equation4445 G := λ x y => h x y x
@[equational_result]
theorem Equation4531_implies_Equation4442 (G : Type*) [Magma G] (h : Equation4531 G) : Equation4442 G := λ x y => h x y x
@[equational_result]
theorem Equation4532_implies_Equation4443 (G : Type*) [Magma G] (h : Equation4532 G) : Equation4443 G := λ x y => h x y x
@[equational_result]
theorem Equation4533_implies_Equation4442 (G : Type*) [Magma G] (h : Equation4533 G) : Equation4442 G := λ x y => h x y x
@[equational_result]
theorem Equation4540_implies_Equation4432 (G : Type*) [Magma G] (h : Equation4540 G) : Equation4432 G := λ x y => h x y x
@[equational_result]
theorem Equation4541_implies_Equation4433 (G : Type*) [Magma G] (h : Equation4541 G) : Equation4433 G := λ x y => h x y x
@[equational_result]
theorem Equation4542_implies_Equation4432 (G : Type*) [Magma G] (h : Equation4542 G) : Equation4432 G := λ x y => h x y x
@[equational_result]
theorem Equation4544_implies_Equation4435 (G : Type*) [Magma G] (h : Equation4544 G) : Equation4435 G := λ x y => h x y x
@[equational_result]
theorem Equation4545_implies_Equation4436 (G : Type*) [Magma G] (h : Equation4545 G) : Equation4436 G := λ x y => h x y x
@[equational_result]
theorem Equation4546_implies_Equation4435 (G : Type*) [Magma G] (h : Equation4546 G) : Equation4435 G := λ x y => h x y x
@[equational_result]
theorem Equation4548_implies_Equation4432 (G : Type*) [Magma G] (h : Equation4548 G) : Equation4432 G := λ x y => h x y x
@[equational_result]
theorem Equation4549_implies_Equation4433 (G : Type*) [Magma G] (h : Equation4549 G) : Equation4433 G := λ x y => h x y x
@[equational_result]
theorem Equation4550_implies_Equation4432 (G : Type*) [Magma G] (h : Equation4550 G) : Equation4432 G := λ x y => h x y x
@[equational_result]
theorem Equation4586_implies_Equation4584 (G : Type*) [Magma G] (h : Equation4586 G) : Equation4584 G := λ x y => h x y x
@[equational_result]
theorem Equation4589_implies_Equation4587 (G : Type*) [Magma G] (h : Equation4589 G) : Equation4587 G := λ x y => h x y x
@[equational_result]
theorem Equation4592_implies_Equation4590 (G : Type*) [Magma G] (h : Equation4592 G) : Equation4590 G := λ x y => h x y x
@[equational_result]
theorem Equation4593_implies_Equation4587 (G : Type*) [Magma G] (h : Equation4593 G) : Equation4587 G := λ x y => h x y x
@[equational_result]
theorem Equation4594_implies_Equation4588 (G : Type*) [Magma G] (h : Equation4594 G) : Equation4588 G := λ x y => h x y x
@[equational_result]
theorem Equation4595_implies_Equation4587 (G : Type*) [Magma G] (h : Equation4595 G) : Equation4587 G := λ x y => h x y x
@[equational_result]
theorem Equation4600_implies_Equation4598 (G : Type*) [Magma G] (h : Equation4600 G) : Equation4598 G := λ x y => h x y x
@[equational_result]
theorem Equation4607_implies_Equation4605 (G : Type*) [Magma G] (h : Equation4607 G) : Equation4605 G := λ x y => h x y x
@[equational_result]
theorem Equation4609_implies_Equation4608 (G : Type*) [Magma G] (h : Equation4609 G) : Equation4608 G := λ x y => h x y x
@[equational_result]
theorem Equation4610_implies_Equation4605 (G : Type*) [Magma G] (h : Equation4610 G) : Equation4605 G := λ x y => h x y x
@[equational_result]
theorem Equation4611_implies_Equation4606 (G : Type*) [Magma G] (h : Equation4611 G) : Equation4606 G := λ x y => h x y x
@[equational_result]
theorem Equation4612_implies_Equation4605 (G : Type*) [Magma G] (h : Equation4612 G) : Equation4605 G := λ x y => h x y x
@[equational_result]
theorem Equation4618_implies_Equation4598 (G : Type*) [Magma G] (h : Equation4618 G) : Equation4598 G := λ x y => h x y x
@[equational_result]
theorem Equation4619_implies_Equation4599 (G : Type*) [Magma G] (h : Equation4619 G) : Equation4599 G := λ x y => h x y x
@[equational_result]
theorem Equation4620_implies_Equation4598 (G : Type*) [Magma G] (h : Equation4620 G) : Equation4598 G := λ x y => h x y x
@[equational_result]
theorem Equation4637_implies_Equation4635 (G : Type*) [Magma G] (h : Equation4637 G) : Equation4635 G := λ x y => h x y x
@[equational_result]
theorem Equation4638_implies_Equation4635 (G : Type*) [Magma G] (h : Equation4638 G) : Equation4635 G := λ x y => h x y x
@[equational_result]
theorem Equation4639_implies_Equation4636 (G : Type*) [Magma G] (h : Equation4639 G) : Equation4636 G := λ x y => h x y x
@[equational_result]
theorem Equation4640_implies_Equation4635 (G : Type*) [Magma G] (h : Equation4640 G) : Equation4635 G := λ x y => h x y x
@[equational_result]
theorem Equation4646_implies_Equation4629 (G : Type*) [Magma G] (h : Equation4646 G) : Equation4629 G := λ x y => h x y x
@[equational_result]
theorem Equation4659_implies_Equation4658 (G : Type*) [Magma G] (h : Equation4659 G) : Equation4658 G := λ x y => h x y x
@[equational_result]
theorem Equation4660_implies_Equation4658 (G : Type*) [Magma G] (h : Equation4660 G) : Equation4658 G := λ x y => h x y x
@[equational_result]
theorem Equation4661_implies_Equation4658 (G : Type*) [Magma G] (h : Equation4661 G) : Equation4658 G := λ x y => h x y x
@[equational_result]
theorem Equation4677_implies_Equation4635 (G : Type*) [Magma G] (h : Equation4677 G) : Equation4635 G := λ x y => h x y x
@[equational_result]
theorem Equation4679_implies_Equation4635 (G : Type*) [Magma G] (h : Equation4679 G) : Equation4635 G := λ x y => h x y x
end SimpleRewrites