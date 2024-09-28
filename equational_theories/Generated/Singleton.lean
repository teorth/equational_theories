import equational_theories.Magma
import equational_theories.AllEquations
import Mathlib.Tactic

namespace Singleton

/- Equational laws that imply the magma has a single element -/

theorem Equation6_implies_Equation2 (G: Type*) [Magma G] (h: Equation6 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

theorem Equation7_implies_Equation2 (G: Type*) [Magma G] (h: Equation7 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation17_implies_Equation2 (G: Type*) [Magma G] (h: Equation17 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

theorem Equation18_implies_Equation2 (G: Type*) [Magma G] (h: Equation18 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation20_implies_Equation2 (G: Type*) [Magma G] (h: Equation20 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation21_implies_Equation2 (G: Type*) [Magma G] (h: Equation21 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation22_implies_Equation2 (G: Type*) [Magma G] (h: Equation22 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation32_implies_Equation2 (G: Type*) [Magma G] (h: Equation32 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

theorem Equation33_implies_Equation2 (G: Type*) [Magma G] (h: Equation33 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation35_implies_Equation2 (G: Type*) [Magma G] (h: Equation35 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation36_implies_Equation2 (G: Type*) [Magma G] (h: Equation36 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation37_implies_Equation2 (G: Type*) [Magma G] (h: Equation37 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation76_implies_Equation2 (G: Type*) [Magma G] (h: Equation76 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

theorem Equation77_implies_Equation2 (G: Type*) [Magma G] (h: Equation77 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation79_implies_Equation2 (G: Type*) [Magma G] (h: Equation79 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation80_implies_Equation2 (G: Type*) [Magma G] (h: Equation80 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation81_implies_Equation2 (G: Type*) [Magma G] (h: Equation81 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation87_implies_Equation2 (G: Type*) [Magma G] (h: Equation87 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation88_implies_Equation2 (G: Type*) [Magma G] (h: Equation88 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation89_implies_Equation2 (G: Type*) [Magma G] (h: Equation89 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation91_implies_Equation2 (G: Type*) [Magma G] (h: Equation91 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation92_implies_Equation2 (G: Type*) [Magma G] (h: Equation92 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation93_implies_Equation2 (G: Type*) [Magma G] (h: Equation93 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation95_implies_Equation2 (G: Type*) [Magma G] (h: Equation95 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation96_implies_Equation2 (G: Type*) [Magma G] (h: Equation96 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation97_implies_Equation2 (G: Type*) [Magma G] (h: Equation97 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation98_implies_Equation2 (G: Type*) [Magma G] (h: Equation98 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation128_implies_Equation2 (G: Type*) [Magma G] (h: Equation128 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

theorem Equation129_implies_Equation2 (G: Type*) [Magma G] (h: Equation129 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation131_implies_Equation2 (G: Type*) [Magma G] (h: Equation131 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation132_implies_Equation2 (G: Type*) [Magma G] (h: Equation132 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation133_implies_Equation2 (G: Type*) [Magma G] (h: Equation133 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation139_implies_Equation2 (G: Type*) [Magma G] (h: Equation139 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation140_implies_Equation2 (G: Type*) [Magma G] (h: Equation140 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation141_implies_Equation2 (G: Type*) [Magma G] (h: Equation141 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation143_implies_Equation2 (G: Type*) [Magma G] (h: Equation143 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation144_implies_Equation2 (G: Type*) [Magma G] (h: Equation144 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation145_implies_Equation2 (G: Type*) [Magma G] (h: Equation145 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation147_implies_Equation2 (G: Type*) [Magma G] (h: Equation147 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation148_implies_Equation2 (G: Type*) [Magma G] (h: Equation148 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation149_implies_Equation2 (G: Type*) [Magma G] (h: Equation149 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation150_implies_Equation2 (G: Type*) [Magma G] (h: Equation150 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation180_implies_Equation2 (G: Type*) [Magma G] (h: Equation180 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

theorem Equation181_implies_Equation2 (G: Type*) [Magma G] (h: Equation181 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation183_implies_Equation2 (G: Type*) [Magma G] (h: Equation183 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation184_implies_Equation2 (G: Type*) [Magma G] (h: Equation184 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation185_implies_Equation2 (G: Type*) [Magma G] (h: Equation185 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation191_implies_Equation2 (G: Type*) [Magma G] (h: Equation191 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation192_implies_Equation2 (G: Type*) [Magma G] (h: Equation192 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation193_implies_Equation2 (G: Type*) [Magma G] (h: Equation193 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation195_implies_Equation2 (G: Type*) [Magma G] (h: Equation195 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation196_implies_Equation2 (G: Type*) [Magma G] (h: Equation196 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation197_implies_Equation2 (G: Type*) [Magma G] (h: Equation197 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation199_implies_Equation2 (G: Type*) [Magma G] (h: Equation199 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation200_implies_Equation2 (G: Type*) [Magma G] (h: Equation200 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation201_implies_Equation2 (G: Type*) [Magma G] (h: Equation201 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation202_implies_Equation2 (G: Type*) [Magma G] (h: Equation202 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation232_implies_Equation2 (G: Type*) [Magma G] (h: Equation232 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

theorem Equation233_implies_Equation2 (G: Type*) [Magma G] (h: Equation233 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation235_implies_Equation2 (G: Type*) [Magma G] (h: Equation235 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation236_implies_Equation2 (G: Type*) [Magma G] (h: Equation236 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation237_implies_Equation2 (G: Type*) [Magma G] (h: Equation237 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation243_implies_Equation2 (G: Type*) [Magma G] (h: Equation243 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation244_implies_Equation2 (G: Type*) [Magma G] (h: Equation244 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation245_implies_Equation2 (G: Type*) [Magma G] (h: Equation245 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation247_implies_Equation2 (G: Type*) [Magma G] (h: Equation247 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation248_implies_Equation2 (G: Type*) [Magma G] (h: Equation248 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation249_implies_Equation2 (G: Type*) [Magma G] (h: Equation249 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation251_implies_Equation2 (G: Type*) [Magma G] (h: Equation251 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation252_implies_Equation2 (G: Type*) [Magma G] (h: Equation252 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation253_implies_Equation2 (G: Type*) [Magma G] (h: Equation253 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation254_implies_Equation2 (G: Type*) [Magma G] (h: Equation254 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation284_implies_Equation2 (G: Type*) [Magma G] (h: Equation284 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

theorem Equation285_implies_Equation2 (G: Type*) [Magma G] (h: Equation285 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation287_implies_Equation2 (G: Type*) [Magma G] (h: Equation287 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation288_implies_Equation2 (G: Type*) [Magma G] (h: Equation288 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation289_implies_Equation2 (G: Type*) [Magma G] (h: Equation289 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation295_implies_Equation2 (G: Type*) [Magma G] (h: Equation295 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation296_implies_Equation2 (G: Type*) [Magma G] (h: Equation296 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation297_implies_Equation2 (G: Type*) [Magma G] (h: Equation297 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation299_implies_Equation2 (G: Type*) [Magma G] (h: Equation299 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation300_implies_Equation2 (G: Type*) [Magma G] (h: Equation300 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation301_implies_Equation2 (G: Type*) [Magma G] (h: Equation301 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation303_implies_Equation2 (G: Type*) [Magma G] (h: Equation303 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation304_implies_Equation2 (G: Type*) [Magma G] (h: Equation304 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation305_implies_Equation2 (G: Type*) [Magma G] (h: Equation305 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation306_implies_Equation2 (G: Type*) [Magma G] (h: Equation306 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation514_implies_Equation2 (G: Type*) [Magma G] (h: Equation514 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

theorem Equation515_implies_Equation2 (G: Type*) [Magma G] (h: Equation515 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation517_implies_Equation2 (G: Type*) [Magma G] (h: Equation517 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation518_implies_Equation2 (G: Type*) [Magma G] (h: Equation518 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation519_implies_Equation2 (G: Type*) [Magma G] (h: Equation519 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation525_implies_Equation2 (G: Type*) [Magma G] (h: Equation525 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation526_implies_Equation2 (G: Type*) [Magma G] (h: Equation526 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation527_implies_Equation2 (G: Type*) [Magma G] (h: Equation527 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation529_implies_Equation2 (G: Type*) [Magma G] (h: Equation529 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation530_implies_Equation2 (G: Type*) [Magma G] (h: Equation530 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation531_implies_Equation2 (G: Type*) [Magma G] (h: Equation531 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation533_implies_Equation2 (G: Type*) [Magma G] (h: Equation533 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation534_implies_Equation2 (G: Type*) [Magma G] (h: Equation534 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation535_implies_Equation2 (G: Type*) [Magma G] (h: Equation535 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation536_implies_Equation2 (G: Type*) [Magma G] (h: Equation536 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation559_implies_Equation2 (G: Type*) [Magma G] (h: Equation559 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation560_implies_Equation2 (G: Type*) [Magma G] (h: Equation560 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation561_implies_Equation2 (G: Type*) [Magma G] (h: Equation561 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation563_implies_Equation2 (G: Type*) [Magma G] (h: Equation563 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation564_implies_Equation2 (G: Type*) [Magma G] (h: Equation564 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation565_implies_Equation2 (G: Type*) [Magma G] (h: Equation565 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation567_implies_Equation2 (G: Type*) [Magma G] (h: Equation567 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation568_implies_Equation2 (G: Type*) [Magma G] (h: Equation568 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation569_implies_Equation2 (G: Type*) [Magma G] (h: Equation569 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation570_implies_Equation2 (G: Type*) [Magma G] (h: Equation570 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation576_implies_Equation2 (G: Type*) [Magma G] (h: Equation576 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation577_implies_Equation2 (G: Type*) [Magma G] (h: Equation577 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation578_implies_Equation2 (G: Type*) [Magma G] (h: Equation578 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation580_implies_Equation2 (G: Type*) [Magma G] (h: Equation580 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation581_implies_Equation2 (G: Type*) [Magma G] (h: Equation581 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation582_implies_Equation2 (G: Type*) [Magma G] (h: Equation582 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation584_implies_Equation2 (G: Type*) [Magma G] (h: Equation584 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation585_implies_Equation2 (G: Type*) [Magma G] (h: Equation585 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation586_implies_Equation2 (G: Type*) [Magma G] (h: Equation586 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation587_implies_Equation2 (G: Type*) [Magma G] (h: Equation587 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation594_implies_Equation2 (G: Type*) [Magma G] (h: Equation594 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation595_implies_Equation2 (G: Type*) [Magma G] (h: Equation595 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation596_implies_Equation2 (G: Type*) [Magma G] (h: Equation596 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation597_implies_Equation2 (G: Type*) [Magma G] (h: Equation597 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation599_implies_Equation2 (G: Type*) [Magma G] (h: Equation599 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation600_implies_Equation2 (G: Type*) [Magma G] (h: Equation600 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation601_implies_Equation2 (G: Type*) [Magma G] (h: Equation601 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation602_implies_Equation2 (G: Type*) [Magma G] (h: Equation602 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation604_implies_Equation2 (G: Type*) [Magma G] (h: Equation604 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation605_implies_Equation2 (G: Type*) [Magma G] (h: Equation605 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation606_implies_Equation2 (G: Type*) [Magma G] (h: Equation606 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation607_implies_Equation2 (G: Type*) [Magma G] (h: Equation607 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation609_implies_Equation2 (G: Type*) [Magma G] (h: Equation609 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation610_implies_Equation2 (G: Type*) [Magma G] (h: Equation610 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation611_implies_Equation2 (G: Type*) [Magma G] (h: Equation611 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation612_implies_Equation2 (G: Type*) [Magma G] (h: Equation612 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation613_implies_Equation2 (G: Type*) [Magma G] (h: Equation613 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a a, ← h]

theorem Equation717_implies_Equation2 (G: Type*) [Magma G] (h: Equation717 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

theorem Equation718_implies_Equation2 (G: Type*) [Magma G] (h: Equation718 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation720_implies_Equation2 (G: Type*) [Magma G] (h: Equation720 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation721_implies_Equation2 (G: Type*) [Magma G] (h: Equation721 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation722_implies_Equation2 (G: Type*) [Magma G] (h: Equation722 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation728_implies_Equation2 (G: Type*) [Magma G] (h: Equation728 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation729_implies_Equation2 (G: Type*) [Magma G] (h: Equation729 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation730_implies_Equation2 (G: Type*) [Magma G] (h: Equation730 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation732_implies_Equation2 (G: Type*) [Magma G] (h: Equation732 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation733_implies_Equation2 (G: Type*) [Magma G] (h: Equation733 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation734_implies_Equation2 (G: Type*) [Magma G] (h: Equation734 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation736_implies_Equation2 (G: Type*) [Magma G] (h: Equation736 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation737_implies_Equation2 (G: Type*) [Magma G] (h: Equation737 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation738_implies_Equation2 (G: Type*) [Magma G] (h: Equation738 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation739_implies_Equation2 (G: Type*) [Magma G] (h: Equation739 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation762_implies_Equation2 (G: Type*) [Magma G] (h: Equation762 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation763_implies_Equation2 (G: Type*) [Magma G] (h: Equation763 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation764_implies_Equation2 (G: Type*) [Magma G] (h: Equation764 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation766_implies_Equation2 (G: Type*) [Magma G] (h: Equation766 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation767_implies_Equation2 (G: Type*) [Magma G] (h: Equation767 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation768_implies_Equation2 (G: Type*) [Magma G] (h: Equation768 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation770_implies_Equation2 (G: Type*) [Magma G] (h: Equation770 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation771_implies_Equation2 (G: Type*) [Magma G] (h: Equation771 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation772_implies_Equation2 (G: Type*) [Magma G] (h: Equation772 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation773_implies_Equation2 (G: Type*) [Magma G] (h: Equation773 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation779_implies_Equation2 (G: Type*) [Magma G] (h: Equation779 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation780_implies_Equation2 (G: Type*) [Magma G] (h: Equation780 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation781_implies_Equation2 (G: Type*) [Magma G] (h: Equation781 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation783_implies_Equation2 (G: Type*) [Magma G] (h: Equation783 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation784_implies_Equation2 (G: Type*) [Magma G] (h: Equation784 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation785_implies_Equation2 (G: Type*) [Magma G] (h: Equation785 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation787_implies_Equation2 (G: Type*) [Magma G] (h: Equation787 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation788_implies_Equation2 (G: Type*) [Magma G] (h: Equation788 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation789_implies_Equation2 (G: Type*) [Magma G] (h: Equation789 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation790_implies_Equation2 (G: Type*) [Magma G] (h: Equation790 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation797_implies_Equation2 (G: Type*) [Magma G] (h: Equation797 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation798_implies_Equation2 (G: Type*) [Magma G] (h: Equation798 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation799_implies_Equation2 (G: Type*) [Magma G] (h: Equation799 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation800_implies_Equation2 (G: Type*) [Magma G] (h: Equation800 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation802_implies_Equation2 (G: Type*) [Magma G] (h: Equation802 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation803_implies_Equation2 (G: Type*) [Magma G] (h: Equation803 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation804_implies_Equation2 (G: Type*) [Magma G] (h: Equation804 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation805_implies_Equation2 (G: Type*) [Magma G] (h: Equation805 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation807_implies_Equation2 (G: Type*) [Magma G] (h: Equation807 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation808_implies_Equation2 (G: Type*) [Magma G] (h: Equation808 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation809_implies_Equation2 (G: Type*) [Magma G] (h: Equation809 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation810_implies_Equation2 (G: Type*) [Magma G] (h: Equation810 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation812_implies_Equation2 (G: Type*) [Magma G] (h: Equation812 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation813_implies_Equation2 (G: Type*) [Magma G] (h: Equation813 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation814_implies_Equation2 (G: Type*) [Magma G] (h: Equation814 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation815_implies_Equation2 (G: Type*) [Magma G] (h: Equation815 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation816_implies_Equation2 (G: Type*) [Magma G] (h: Equation816 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a a, ← h]

theorem Equation920_implies_Equation2 (G: Type*) [Magma G] (h: Equation920 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

theorem Equation921_implies_Equation2 (G: Type*) [Magma G] (h: Equation921 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation923_implies_Equation2 (G: Type*) [Magma G] (h: Equation923 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation924_implies_Equation2 (G: Type*) [Magma G] (h: Equation924 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation925_implies_Equation2 (G: Type*) [Magma G] (h: Equation925 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation931_implies_Equation2 (G: Type*) [Magma G] (h: Equation931 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation932_implies_Equation2 (G: Type*) [Magma G] (h: Equation932 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation933_implies_Equation2 (G: Type*) [Magma G] (h: Equation933 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation935_implies_Equation2 (G: Type*) [Magma G] (h: Equation935 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation936_implies_Equation2 (G: Type*) [Magma G] (h: Equation936 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation937_implies_Equation2 (G: Type*) [Magma G] (h: Equation937 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation939_implies_Equation2 (G: Type*) [Magma G] (h: Equation939 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation940_implies_Equation2 (G: Type*) [Magma G] (h: Equation940 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation941_implies_Equation2 (G: Type*) [Magma G] (h: Equation941 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation942_implies_Equation2 (G: Type*) [Magma G] (h: Equation942 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation965_implies_Equation2 (G: Type*) [Magma G] (h: Equation965 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation966_implies_Equation2 (G: Type*) [Magma G] (h: Equation966 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation967_implies_Equation2 (G: Type*) [Magma G] (h: Equation967 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation969_implies_Equation2 (G: Type*) [Magma G] (h: Equation969 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation970_implies_Equation2 (G: Type*) [Magma G] (h: Equation970 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation971_implies_Equation2 (G: Type*) [Magma G] (h: Equation971 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation973_implies_Equation2 (G: Type*) [Magma G] (h: Equation973 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation974_implies_Equation2 (G: Type*) [Magma G] (h: Equation974 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation975_implies_Equation2 (G: Type*) [Magma G] (h: Equation975 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation976_implies_Equation2 (G: Type*) [Magma G] (h: Equation976 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation982_implies_Equation2 (G: Type*) [Magma G] (h: Equation982 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation983_implies_Equation2 (G: Type*) [Magma G] (h: Equation983 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation984_implies_Equation2 (G: Type*) [Magma G] (h: Equation984 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation986_implies_Equation2 (G: Type*) [Magma G] (h: Equation986 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation987_implies_Equation2 (G: Type*) [Magma G] (h: Equation987 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation988_implies_Equation2 (G: Type*) [Magma G] (h: Equation988 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation990_implies_Equation2 (G: Type*) [Magma G] (h: Equation990 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation991_implies_Equation2 (G: Type*) [Magma G] (h: Equation991 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation992_implies_Equation2 (G: Type*) [Magma G] (h: Equation992 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation993_implies_Equation2 (G: Type*) [Magma G] (h: Equation993 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1000_implies_Equation2 (G: Type*) [Magma G] (h: Equation1000 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1001_implies_Equation2 (G: Type*) [Magma G] (h: Equation1001 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1002_implies_Equation2 (G: Type*) [Magma G] (h: Equation1002 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1003_implies_Equation2 (G: Type*) [Magma G] (h: Equation1003 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1005_implies_Equation2 (G: Type*) [Magma G] (h: Equation1005 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1006_implies_Equation2 (G: Type*) [Magma G] (h: Equation1006 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1007_implies_Equation2 (G: Type*) [Magma G] (h: Equation1007 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1008_implies_Equation2 (G: Type*) [Magma G] (h: Equation1008 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1010_implies_Equation2 (G: Type*) [Magma G] (h: Equation1010 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1011_implies_Equation2 (G: Type*) [Magma G] (h: Equation1011 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1012_implies_Equation2 (G: Type*) [Magma G] (h: Equation1012 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1013_implies_Equation2 (G: Type*) [Magma G] (h: Equation1013 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1015_implies_Equation2 (G: Type*) [Magma G] (h: Equation1015 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1016_implies_Equation2 (G: Type*) [Magma G] (h: Equation1016 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1017_implies_Equation2 (G: Type*) [Magma G] (h: Equation1017 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1018_implies_Equation2 (G: Type*) [Magma G] (h: Equation1018 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1019_implies_Equation2 (G: Type*) [Magma G] (h: Equation1019 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a a, ← h]

theorem Equation1123_implies_Equation2 (G: Type*) [Magma G] (h: Equation1123 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

theorem Equation1124_implies_Equation2 (G: Type*) [Magma G] (h: Equation1124 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1126_implies_Equation2 (G: Type*) [Magma G] (h: Equation1126 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1127_implies_Equation2 (G: Type*) [Magma G] (h: Equation1127 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1128_implies_Equation2 (G: Type*) [Magma G] (h: Equation1128 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1134_implies_Equation2 (G: Type*) [Magma G] (h: Equation1134 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1135_implies_Equation2 (G: Type*) [Magma G] (h: Equation1135 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1136_implies_Equation2 (G: Type*) [Magma G] (h: Equation1136 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1138_implies_Equation2 (G: Type*) [Magma G] (h: Equation1138 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1139_implies_Equation2 (G: Type*) [Magma G] (h: Equation1139 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1140_implies_Equation2 (G: Type*) [Magma G] (h: Equation1140 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1142_implies_Equation2 (G: Type*) [Magma G] (h: Equation1142 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1143_implies_Equation2 (G: Type*) [Magma G] (h: Equation1143 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1144_implies_Equation2 (G: Type*) [Magma G] (h: Equation1144 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1145_implies_Equation2 (G: Type*) [Magma G] (h: Equation1145 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1168_implies_Equation2 (G: Type*) [Magma G] (h: Equation1168 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1169_implies_Equation2 (G: Type*) [Magma G] (h: Equation1169 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1170_implies_Equation2 (G: Type*) [Magma G] (h: Equation1170 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1172_implies_Equation2 (G: Type*) [Magma G] (h: Equation1172 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1173_implies_Equation2 (G: Type*) [Magma G] (h: Equation1173 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1174_implies_Equation2 (G: Type*) [Magma G] (h: Equation1174 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1176_implies_Equation2 (G: Type*) [Magma G] (h: Equation1176 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1177_implies_Equation2 (G: Type*) [Magma G] (h: Equation1177 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1178_implies_Equation2 (G: Type*) [Magma G] (h: Equation1178 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1179_implies_Equation2 (G: Type*) [Magma G] (h: Equation1179 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1185_implies_Equation2 (G: Type*) [Magma G] (h: Equation1185 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1186_implies_Equation2 (G: Type*) [Magma G] (h: Equation1186 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1187_implies_Equation2 (G: Type*) [Magma G] (h: Equation1187 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1189_implies_Equation2 (G: Type*) [Magma G] (h: Equation1189 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1190_implies_Equation2 (G: Type*) [Magma G] (h: Equation1190 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1191_implies_Equation2 (G: Type*) [Magma G] (h: Equation1191 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1193_implies_Equation2 (G: Type*) [Magma G] (h: Equation1193 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1194_implies_Equation2 (G: Type*) [Magma G] (h: Equation1194 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1195_implies_Equation2 (G: Type*) [Magma G] (h: Equation1195 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1196_implies_Equation2 (G: Type*) [Magma G] (h: Equation1196 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1203_implies_Equation2 (G: Type*) [Magma G] (h: Equation1203 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1204_implies_Equation2 (G: Type*) [Magma G] (h: Equation1204 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1205_implies_Equation2 (G: Type*) [Magma G] (h: Equation1205 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1206_implies_Equation2 (G: Type*) [Magma G] (h: Equation1206 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1208_implies_Equation2 (G: Type*) [Magma G] (h: Equation1208 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1209_implies_Equation2 (G: Type*) [Magma G] (h: Equation1209 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1210_implies_Equation2 (G: Type*) [Magma G] (h: Equation1210 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1211_implies_Equation2 (G: Type*) [Magma G] (h: Equation1211 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1213_implies_Equation2 (G: Type*) [Magma G] (h: Equation1213 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1214_implies_Equation2 (G: Type*) [Magma G] (h: Equation1214 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1215_implies_Equation2 (G: Type*) [Magma G] (h: Equation1215 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1216_implies_Equation2 (G: Type*) [Magma G] (h: Equation1216 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1218_implies_Equation2 (G: Type*) [Magma G] (h: Equation1218 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1219_implies_Equation2 (G: Type*) [Magma G] (h: Equation1219 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1220_implies_Equation2 (G: Type*) [Magma G] (h: Equation1220 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1221_implies_Equation2 (G: Type*) [Magma G] (h: Equation1221 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1222_implies_Equation2 (G: Type*) [Magma G] (h: Equation1222 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a a, ← h]

theorem Equation1326_implies_Equation2 (G: Type*) [Magma G] (h: Equation1326 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

theorem Equation1327_implies_Equation2 (G: Type*) [Magma G] (h: Equation1327 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1329_implies_Equation2 (G: Type*) [Magma G] (h: Equation1329 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1330_implies_Equation2 (G: Type*) [Magma G] (h: Equation1330 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1331_implies_Equation2 (G: Type*) [Magma G] (h: Equation1331 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1337_implies_Equation2 (G: Type*) [Magma G] (h: Equation1337 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1338_implies_Equation2 (G: Type*) [Magma G] (h: Equation1338 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1339_implies_Equation2 (G: Type*) [Magma G] (h: Equation1339 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1341_implies_Equation2 (G: Type*) [Magma G] (h: Equation1341 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1342_implies_Equation2 (G: Type*) [Magma G] (h: Equation1342 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1343_implies_Equation2 (G: Type*) [Magma G] (h: Equation1343 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1345_implies_Equation2 (G: Type*) [Magma G] (h: Equation1345 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1346_implies_Equation2 (G: Type*) [Magma G] (h: Equation1346 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1347_implies_Equation2 (G: Type*) [Magma G] (h: Equation1347 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1348_implies_Equation2 (G: Type*) [Magma G] (h: Equation1348 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1371_implies_Equation2 (G: Type*) [Magma G] (h: Equation1371 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1372_implies_Equation2 (G: Type*) [Magma G] (h: Equation1372 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1373_implies_Equation2 (G: Type*) [Magma G] (h: Equation1373 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1375_implies_Equation2 (G: Type*) [Magma G] (h: Equation1375 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1376_implies_Equation2 (G: Type*) [Magma G] (h: Equation1376 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1377_implies_Equation2 (G: Type*) [Magma G] (h: Equation1377 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1379_implies_Equation2 (G: Type*) [Magma G] (h: Equation1379 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1380_implies_Equation2 (G: Type*) [Magma G] (h: Equation1380 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1381_implies_Equation2 (G: Type*) [Magma G] (h: Equation1381 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1382_implies_Equation2 (G: Type*) [Magma G] (h: Equation1382 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1388_implies_Equation2 (G: Type*) [Magma G] (h: Equation1388 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1389_implies_Equation2 (G: Type*) [Magma G] (h: Equation1389 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1390_implies_Equation2 (G: Type*) [Magma G] (h: Equation1390 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1392_implies_Equation2 (G: Type*) [Magma G] (h: Equation1392 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1393_implies_Equation2 (G: Type*) [Magma G] (h: Equation1393 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1394_implies_Equation2 (G: Type*) [Magma G] (h: Equation1394 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1396_implies_Equation2 (G: Type*) [Magma G] (h: Equation1396 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1397_implies_Equation2 (G: Type*) [Magma G] (h: Equation1397 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1398_implies_Equation2 (G: Type*) [Magma G] (h: Equation1398 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1399_implies_Equation2 (G: Type*) [Magma G] (h: Equation1399 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1406_implies_Equation2 (G: Type*) [Magma G] (h: Equation1406 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1407_implies_Equation2 (G: Type*) [Magma G] (h: Equation1407 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1408_implies_Equation2 (G: Type*) [Magma G] (h: Equation1408 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1409_implies_Equation2 (G: Type*) [Magma G] (h: Equation1409 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1411_implies_Equation2 (G: Type*) [Magma G] (h: Equation1411 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1412_implies_Equation2 (G: Type*) [Magma G] (h: Equation1412 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1413_implies_Equation2 (G: Type*) [Magma G] (h: Equation1413 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1414_implies_Equation2 (G: Type*) [Magma G] (h: Equation1414 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1416_implies_Equation2 (G: Type*) [Magma G] (h: Equation1416 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1417_implies_Equation2 (G: Type*) [Magma G] (h: Equation1417 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1418_implies_Equation2 (G: Type*) [Magma G] (h: Equation1418 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1419_implies_Equation2 (G: Type*) [Magma G] (h: Equation1419 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1421_implies_Equation2 (G: Type*) [Magma G] (h: Equation1421 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1422_implies_Equation2 (G: Type*) [Magma G] (h: Equation1422 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1423_implies_Equation2 (G: Type*) [Magma G] (h: Equation1423 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1424_implies_Equation2 (G: Type*) [Magma G] (h: Equation1424 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1425_implies_Equation2 (G: Type*) [Magma G] (h: Equation1425 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a a, ← h]

theorem Equation1529_implies_Equation2 (G: Type*) [Magma G] (h: Equation1529 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

theorem Equation1530_implies_Equation2 (G: Type*) [Magma G] (h: Equation1530 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1532_implies_Equation2 (G: Type*) [Magma G] (h: Equation1532 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1533_implies_Equation2 (G: Type*) [Magma G] (h: Equation1533 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1534_implies_Equation2 (G: Type*) [Magma G] (h: Equation1534 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1540_implies_Equation2 (G: Type*) [Magma G] (h: Equation1540 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1541_implies_Equation2 (G: Type*) [Magma G] (h: Equation1541 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1542_implies_Equation2 (G: Type*) [Magma G] (h: Equation1542 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1544_implies_Equation2 (G: Type*) [Magma G] (h: Equation1544 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1545_implies_Equation2 (G: Type*) [Magma G] (h: Equation1545 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1546_implies_Equation2 (G: Type*) [Magma G] (h: Equation1546 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1548_implies_Equation2 (G: Type*) [Magma G] (h: Equation1548 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1549_implies_Equation2 (G: Type*) [Magma G] (h: Equation1549 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1550_implies_Equation2 (G: Type*) [Magma G] (h: Equation1550 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1551_implies_Equation2 (G: Type*) [Magma G] (h: Equation1551 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1574_implies_Equation2 (G: Type*) [Magma G] (h: Equation1574 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1575_implies_Equation2 (G: Type*) [Magma G] (h: Equation1575 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1576_implies_Equation2 (G: Type*) [Magma G] (h: Equation1576 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1578_implies_Equation2 (G: Type*) [Magma G] (h: Equation1578 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1579_implies_Equation2 (G: Type*) [Magma G] (h: Equation1579 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1580_implies_Equation2 (G: Type*) [Magma G] (h: Equation1580 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1582_implies_Equation2 (G: Type*) [Magma G] (h: Equation1582 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1583_implies_Equation2 (G: Type*) [Magma G] (h: Equation1583 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1584_implies_Equation2 (G: Type*) [Magma G] (h: Equation1584 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1585_implies_Equation2 (G: Type*) [Magma G] (h: Equation1585 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1591_implies_Equation2 (G: Type*) [Magma G] (h: Equation1591 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1592_implies_Equation2 (G: Type*) [Magma G] (h: Equation1592 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1593_implies_Equation2 (G: Type*) [Magma G] (h: Equation1593 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1595_implies_Equation2 (G: Type*) [Magma G] (h: Equation1595 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1596_implies_Equation2 (G: Type*) [Magma G] (h: Equation1596 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1597_implies_Equation2 (G: Type*) [Magma G] (h: Equation1597 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1599_implies_Equation2 (G: Type*) [Magma G] (h: Equation1599 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1600_implies_Equation2 (G: Type*) [Magma G] (h: Equation1600 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1601_implies_Equation2 (G: Type*) [Magma G] (h: Equation1601 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1602_implies_Equation2 (G: Type*) [Magma G] (h: Equation1602 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1609_implies_Equation2 (G: Type*) [Magma G] (h: Equation1609 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1610_implies_Equation2 (G: Type*) [Magma G] (h: Equation1610 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1611_implies_Equation2 (G: Type*) [Magma G] (h: Equation1611 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1612_implies_Equation2 (G: Type*) [Magma G] (h: Equation1612 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1614_implies_Equation2 (G: Type*) [Magma G] (h: Equation1614 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1615_implies_Equation2 (G: Type*) [Magma G] (h: Equation1615 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1616_implies_Equation2 (G: Type*) [Magma G] (h: Equation1616 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1617_implies_Equation2 (G: Type*) [Magma G] (h: Equation1617 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1619_implies_Equation2 (G: Type*) [Magma G] (h: Equation1619 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1620_implies_Equation2 (G: Type*) [Magma G] (h: Equation1620 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1621_implies_Equation2 (G: Type*) [Magma G] (h: Equation1621 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1622_implies_Equation2 (G: Type*) [Magma G] (h: Equation1622 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1624_implies_Equation2 (G: Type*) [Magma G] (h: Equation1624 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1625_implies_Equation2 (G: Type*) [Magma G] (h: Equation1625 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1626_implies_Equation2 (G: Type*) [Magma G] (h: Equation1626 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1627_implies_Equation2 (G: Type*) [Magma G] (h: Equation1627 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1628_implies_Equation2 (G: Type*) [Magma G] (h: Equation1628 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a a, ← h]

theorem Equation1732_implies_Equation2 (G: Type*) [Magma G] (h: Equation1732 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

theorem Equation1733_implies_Equation2 (G: Type*) [Magma G] (h: Equation1733 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1735_implies_Equation2 (G: Type*) [Magma G] (h: Equation1735 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1736_implies_Equation2 (G: Type*) [Magma G] (h: Equation1736 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1737_implies_Equation2 (G: Type*) [Magma G] (h: Equation1737 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1743_implies_Equation2 (G: Type*) [Magma G] (h: Equation1743 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1744_implies_Equation2 (G: Type*) [Magma G] (h: Equation1744 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1745_implies_Equation2 (G: Type*) [Magma G] (h: Equation1745 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1747_implies_Equation2 (G: Type*) [Magma G] (h: Equation1747 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1748_implies_Equation2 (G: Type*) [Magma G] (h: Equation1748 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1749_implies_Equation2 (G: Type*) [Magma G] (h: Equation1749 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1751_implies_Equation2 (G: Type*) [Magma G] (h: Equation1751 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1752_implies_Equation2 (G: Type*) [Magma G] (h: Equation1752 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1753_implies_Equation2 (G: Type*) [Magma G] (h: Equation1753 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1754_implies_Equation2 (G: Type*) [Magma G] (h: Equation1754 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1777_implies_Equation2 (G: Type*) [Magma G] (h: Equation1777 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1778_implies_Equation2 (G: Type*) [Magma G] (h: Equation1778 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1779_implies_Equation2 (G: Type*) [Magma G] (h: Equation1779 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1781_implies_Equation2 (G: Type*) [Magma G] (h: Equation1781 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1782_implies_Equation2 (G: Type*) [Magma G] (h: Equation1782 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1783_implies_Equation2 (G: Type*) [Magma G] (h: Equation1783 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1785_implies_Equation2 (G: Type*) [Magma G] (h: Equation1785 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1786_implies_Equation2 (G: Type*) [Magma G] (h: Equation1786 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1787_implies_Equation2 (G: Type*) [Magma G] (h: Equation1787 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1788_implies_Equation2 (G: Type*) [Magma G] (h: Equation1788 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1794_implies_Equation2 (G: Type*) [Magma G] (h: Equation1794 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1795_implies_Equation2 (G: Type*) [Magma G] (h: Equation1795 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1796_implies_Equation2 (G: Type*) [Magma G] (h: Equation1796 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1798_implies_Equation2 (G: Type*) [Magma G] (h: Equation1798 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1799_implies_Equation2 (G: Type*) [Magma G] (h: Equation1799 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1800_implies_Equation2 (G: Type*) [Magma G] (h: Equation1800 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1802_implies_Equation2 (G: Type*) [Magma G] (h: Equation1802 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1803_implies_Equation2 (G: Type*) [Magma G] (h: Equation1803 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1804_implies_Equation2 (G: Type*) [Magma G] (h: Equation1804 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1805_implies_Equation2 (G: Type*) [Magma G] (h: Equation1805 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1812_implies_Equation2 (G: Type*) [Magma G] (h: Equation1812 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1813_implies_Equation2 (G: Type*) [Magma G] (h: Equation1813 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1814_implies_Equation2 (G: Type*) [Magma G] (h: Equation1814 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1815_implies_Equation2 (G: Type*) [Magma G] (h: Equation1815 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1817_implies_Equation2 (G: Type*) [Magma G] (h: Equation1817 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1818_implies_Equation2 (G: Type*) [Magma G] (h: Equation1818 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1819_implies_Equation2 (G: Type*) [Magma G] (h: Equation1819 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1820_implies_Equation2 (G: Type*) [Magma G] (h: Equation1820 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1822_implies_Equation2 (G: Type*) [Magma G] (h: Equation1822 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1823_implies_Equation2 (G: Type*) [Magma G] (h: Equation1823 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1824_implies_Equation2 (G: Type*) [Magma G] (h: Equation1824 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1825_implies_Equation2 (G: Type*) [Magma G] (h: Equation1825 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1827_implies_Equation2 (G: Type*) [Magma G] (h: Equation1827 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1828_implies_Equation2 (G: Type*) [Magma G] (h: Equation1828 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1829_implies_Equation2 (G: Type*) [Magma G] (h: Equation1829 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1830_implies_Equation2 (G: Type*) [Magma G] (h: Equation1830 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1831_implies_Equation2 (G: Type*) [Magma G] (h: Equation1831 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a a, ← h]

theorem Equation1935_implies_Equation2 (G: Type*) [Magma G] (h: Equation1935 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

theorem Equation1936_implies_Equation2 (G: Type*) [Magma G] (h: Equation1936 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1938_implies_Equation2 (G: Type*) [Magma G] (h: Equation1938 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1939_implies_Equation2 (G: Type*) [Magma G] (h: Equation1939 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1940_implies_Equation2 (G: Type*) [Magma G] (h: Equation1940 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1946_implies_Equation2 (G: Type*) [Magma G] (h: Equation1946 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1947_implies_Equation2 (G: Type*) [Magma G] (h: Equation1947 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1948_implies_Equation2 (G: Type*) [Magma G] (h: Equation1948 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1950_implies_Equation2 (G: Type*) [Magma G] (h: Equation1950 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1951_implies_Equation2 (G: Type*) [Magma G] (h: Equation1951 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1952_implies_Equation2 (G: Type*) [Magma G] (h: Equation1952 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1954_implies_Equation2 (G: Type*) [Magma G] (h: Equation1954 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1955_implies_Equation2 (G: Type*) [Magma G] (h: Equation1955 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1956_implies_Equation2 (G: Type*) [Magma G] (h: Equation1956 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1957_implies_Equation2 (G: Type*) [Magma G] (h: Equation1957 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1980_implies_Equation2 (G: Type*) [Magma G] (h: Equation1980 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1981_implies_Equation2 (G: Type*) [Magma G] (h: Equation1981 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1982_implies_Equation2 (G: Type*) [Magma G] (h: Equation1982 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1984_implies_Equation2 (G: Type*) [Magma G] (h: Equation1984 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1985_implies_Equation2 (G: Type*) [Magma G] (h: Equation1985 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1986_implies_Equation2 (G: Type*) [Magma G] (h: Equation1986 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1988_implies_Equation2 (G: Type*) [Magma G] (h: Equation1988 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1989_implies_Equation2 (G: Type*) [Magma G] (h: Equation1989 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1990_implies_Equation2 (G: Type*) [Magma G] (h: Equation1990 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation1991_implies_Equation2 (G: Type*) [Magma G] (h: Equation1991 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation1997_implies_Equation2 (G: Type*) [Magma G] (h: Equation1997 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1998_implies_Equation2 (G: Type*) [Magma G] (h: Equation1998 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation1999_implies_Equation2 (G: Type*) [Magma G] (h: Equation1999 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2001_implies_Equation2 (G: Type*) [Magma G] (h: Equation2001 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2002_implies_Equation2 (G: Type*) [Magma G] (h: Equation2002 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2003_implies_Equation2 (G: Type*) [Magma G] (h: Equation2003 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2005_implies_Equation2 (G: Type*) [Magma G] (h: Equation2005 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2006_implies_Equation2 (G: Type*) [Magma G] (h: Equation2006 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2007_implies_Equation2 (G: Type*) [Magma G] (h: Equation2007 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2008_implies_Equation2 (G: Type*) [Magma G] (h: Equation2008 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2015_implies_Equation2 (G: Type*) [Magma G] (h: Equation2015 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2016_implies_Equation2 (G: Type*) [Magma G] (h: Equation2016 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2017_implies_Equation2 (G: Type*) [Magma G] (h: Equation2017 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2018_implies_Equation2 (G: Type*) [Magma G] (h: Equation2018 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2020_implies_Equation2 (G: Type*) [Magma G] (h: Equation2020 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2021_implies_Equation2 (G: Type*) [Magma G] (h: Equation2021 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2022_implies_Equation2 (G: Type*) [Magma G] (h: Equation2022 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2023_implies_Equation2 (G: Type*) [Magma G] (h: Equation2023 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2025_implies_Equation2 (G: Type*) [Magma G] (h: Equation2025 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2026_implies_Equation2 (G: Type*) [Magma G] (h: Equation2026 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2027_implies_Equation2 (G: Type*) [Magma G] (h: Equation2027 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2028_implies_Equation2 (G: Type*) [Magma G] (h: Equation2028 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2030_implies_Equation2 (G: Type*) [Magma G] (h: Equation2030 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2031_implies_Equation2 (G: Type*) [Magma G] (h: Equation2031 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2032_implies_Equation2 (G: Type*) [Magma G] (h: Equation2032 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2033_implies_Equation2 (G: Type*) [Magma G] (h: Equation2033 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2034_implies_Equation2 (G: Type*) [Magma G] (h: Equation2034 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a a, ← h]

theorem Equation2138_implies_Equation2 (G: Type*) [Magma G] (h: Equation2138 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

theorem Equation2139_implies_Equation2 (G: Type*) [Magma G] (h: Equation2139 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2141_implies_Equation2 (G: Type*) [Magma G] (h: Equation2141 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2142_implies_Equation2 (G: Type*) [Magma G] (h: Equation2142 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2143_implies_Equation2 (G: Type*) [Magma G] (h: Equation2143 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2149_implies_Equation2 (G: Type*) [Magma G] (h: Equation2149 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2150_implies_Equation2 (G: Type*) [Magma G] (h: Equation2150 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2151_implies_Equation2 (G: Type*) [Magma G] (h: Equation2151 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2153_implies_Equation2 (G: Type*) [Magma G] (h: Equation2153 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2154_implies_Equation2 (G: Type*) [Magma G] (h: Equation2154 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2155_implies_Equation2 (G: Type*) [Magma G] (h: Equation2155 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2157_implies_Equation2 (G: Type*) [Magma G] (h: Equation2157 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2158_implies_Equation2 (G: Type*) [Magma G] (h: Equation2158 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2159_implies_Equation2 (G: Type*) [Magma G] (h: Equation2159 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2160_implies_Equation2 (G: Type*) [Magma G] (h: Equation2160 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2183_implies_Equation2 (G: Type*) [Magma G] (h: Equation2183 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2184_implies_Equation2 (G: Type*) [Magma G] (h: Equation2184 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2185_implies_Equation2 (G: Type*) [Magma G] (h: Equation2185 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2187_implies_Equation2 (G: Type*) [Magma G] (h: Equation2187 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2188_implies_Equation2 (G: Type*) [Magma G] (h: Equation2188 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2189_implies_Equation2 (G: Type*) [Magma G] (h: Equation2189 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2191_implies_Equation2 (G: Type*) [Magma G] (h: Equation2191 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2192_implies_Equation2 (G: Type*) [Magma G] (h: Equation2192 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2193_implies_Equation2 (G: Type*) [Magma G] (h: Equation2193 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2194_implies_Equation2 (G: Type*) [Magma G] (h: Equation2194 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2200_implies_Equation2 (G: Type*) [Magma G] (h: Equation2200 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2201_implies_Equation2 (G: Type*) [Magma G] (h: Equation2201 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2202_implies_Equation2 (G: Type*) [Magma G] (h: Equation2202 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2204_implies_Equation2 (G: Type*) [Magma G] (h: Equation2204 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2205_implies_Equation2 (G: Type*) [Magma G] (h: Equation2205 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2206_implies_Equation2 (G: Type*) [Magma G] (h: Equation2206 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2208_implies_Equation2 (G: Type*) [Magma G] (h: Equation2208 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2209_implies_Equation2 (G: Type*) [Magma G] (h: Equation2209 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2210_implies_Equation2 (G: Type*) [Magma G] (h: Equation2210 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2211_implies_Equation2 (G: Type*) [Magma G] (h: Equation2211 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2218_implies_Equation2 (G: Type*) [Magma G] (h: Equation2218 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2219_implies_Equation2 (G: Type*) [Magma G] (h: Equation2219 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2220_implies_Equation2 (G: Type*) [Magma G] (h: Equation2220 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2221_implies_Equation2 (G: Type*) [Magma G] (h: Equation2221 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2223_implies_Equation2 (G: Type*) [Magma G] (h: Equation2223 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2224_implies_Equation2 (G: Type*) [Magma G] (h: Equation2224 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2225_implies_Equation2 (G: Type*) [Magma G] (h: Equation2225 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2226_implies_Equation2 (G: Type*) [Magma G] (h: Equation2226 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2228_implies_Equation2 (G: Type*) [Magma G] (h: Equation2228 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2229_implies_Equation2 (G: Type*) [Magma G] (h: Equation2229 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2230_implies_Equation2 (G: Type*) [Magma G] (h: Equation2230 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2231_implies_Equation2 (G: Type*) [Magma G] (h: Equation2231 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2233_implies_Equation2 (G: Type*) [Magma G] (h: Equation2233 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2234_implies_Equation2 (G: Type*) [Magma G] (h: Equation2234 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2235_implies_Equation2 (G: Type*) [Magma G] (h: Equation2235 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2236_implies_Equation2 (G: Type*) [Magma G] (h: Equation2236 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2237_implies_Equation2 (G: Type*) [Magma G] (h: Equation2237 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a a, ← h]

theorem Equation2341_implies_Equation2 (G: Type*) [Magma G] (h: Equation2341 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

theorem Equation2342_implies_Equation2 (G: Type*) [Magma G] (h: Equation2342 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2344_implies_Equation2 (G: Type*) [Magma G] (h: Equation2344 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2345_implies_Equation2 (G: Type*) [Magma G] (h: Equation2345 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2346_implies_Equation2 (G: Type*) [Magma G] (h: Equation2346 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2352_implies_Equation2 (G: Type*) [Magma G] (h: Equation2352 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2353_implies_Equation2 (G: Type*) [Magma G] (h: Equation2353 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2354_implies_Equation2 (G: Type*) [Magma G] (h: Equation2354 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2356_implies_Equation2 (G: Type*) [Magma G] (h: Equation2356 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2357_implies_Equation2 (G: Type*) [Magma G] (h: Equation2357 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2358_implies_Equation2 (G: Type*) [Magma G] (h: Equation2358 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2360_implies_Equation2 (G: Type*) [Magma G] (h: Equation2360 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2361_implies_Equation2 (G: Type*) [Magma G] (h: Equation2361 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2362_implies_Equation2 (G: Type*) [Magma G] (h: Equation2362 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2363_implies_Equation2 (G: Type*) [Magma G] (h: Equation2363 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2386_implies_Equation2 (G: Type*) [Magma G] (h: Equation2386 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2387_implies_Equation2 (G: Type*) [Magma G] (h: Equation2387 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2388_implies_Equation2 (G: Type*) [Magma G] (h: Equation2388 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2390_implies_Equation2 (G: Type*) [Magma G] (h: Equation2390 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2391_implies_Equation2 (G: Type*) [Magma G] (h: Equation2391 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2392_implies_Equation2 (G: Type*) [Magma G] (h: Equation2392 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2394_implies_Equation2 (G: Type*) [Magma G] (h: Equation2394 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2395_implies_Equation2 (G: Type*) [Magma G] (h: Equation2395 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2396_implies_Equation2 (G: Type*) [Magma G] (h: Equation2396 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2397_implies_Equation2 (G: Type*) [Magma G] (h: Equation2397 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2403_implies_Equation2 (G: Type*) [Magma G] (h: Equation2403 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2404_implies_Equation2 (G: Type*) [Magma G] (h: Equation2404 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2405_implies_Equation2 (G: Type*) [Magma G] (h: Equation2405 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2407_implies_Equation2 (G: Type*) [Magma G] (h: Equation2407 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2408_implies_Equation2 (G: Type*) [Magma G] (h: Equation2408 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2409_implies_Equation2 (G: Type*) [Magma G] (h: Equation2409 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2411_implies_Equation2 (G: Type*) [Magma G] (h: Equation2411 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2412_implies_Equation2 (G: Type*) [Magma G] (h: Equation2412 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2413_implies_Equation2 (G: Type*) [Magma G] (h: Equation2413 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2414_implies_Equation2 (G: Type*) [Magma G] (h: Equation2414 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2421_implies_Equation2 (G: Type*) [Magma G] (h: Equation2421 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2422_implies_Equation2 (G: Type*) [Magma G] (h: Equation2422 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2423_implies_Equation2 (G: Type*) [Magma G] (h: Equation2423 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2424_implies_Equation2 (G: Type*) [Magma G] (h: Equation2424 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2426_implies_Equation2 (G: Type*) [Magma G] (h: Equation2426 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2427_implies_Equation2 (G: Type*) [Magma G] (h: Equation2427 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2428_implies_Equation2 (G: Type*) [Magma G] (h: Equation2428 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2429_implies_Equation2 (G: Type*) [Magma G] (h: Equation2429 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2431_implies_Equation2 (G: Type*) [Magma G] (h: Equation2431 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2432_implies_Equation2 (G: Type*) [Magma G] (h: Equation2432 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2433_implies_Equation2 (G: Type*) [Magma G] (h: Equation2433 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2434_implies_Equation2 (G: Type*) [Magma G] (h: Equation2434 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2436_implies_Equation2 (G: Type*) [Magma G] (h: Equation2436 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2437_implies_Equation2 (G: Type*) [Magma G] (h: Equation2437 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2438_implies_Equation2 (G: Type*) [Magma G] (h: Equation2438 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2439_implies_Equation2 (G: Type*) [Magma G] (h: Equation2439 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2440_implies_Equation2 (G: Type*) [Magma G] (h: Equation2440 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a a, ← h]

theorem Equation2544_implies_Equation2 (G: Type*) [Magma G] (h: Equation2544 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

theorem Equation2545_implies_Equation2 (G: Type*) [Magma G] (h: Equation2545 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2547_implies_Equation2 (G: Type*) [Magma G] (h: Equation2547 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2548_implies_Equation2 (G: Type*) [Magma G] (h: Equation2548 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2549_implies_Equation2 (G: Type*) [Magma G] (h: Equation2549 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2555_implies_Equation2 (G: Type*) [Magma G] (h: Equation2555 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2556_implies_Equation2 (G: Type*) [Magma G] (h: Equation2556 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2557_implies_Equation2 (G: Type*) [Magma G] (h: Equation2557 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2559_implies_Equation2 (G: Type*) [Magma G] (h: Equation2559 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2560_implies_Equation2 (G: Type*) [Magma G] (h: Equation2560 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2561_implies_Equation2 (G: Type*) [Magma G] (h: Equation2561 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2563_implies_Equation2 (G: Type*) [Magma G] (h: Equation2563 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2564_implies_Equation2 (G: Type*) [Magma G] (h: Equation2564 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2565_implies_Equation2 (G: Type*) [Magma G] (h: Equation2565 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2566_implies_Equation2 (G: Type*) [Magma G] (h: Equation2566 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2589_implies_Equation2 (G: Type*) [Magma G] (h: Equation2589 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2590_implies_Equation2 (G: Type*) [Magma G] (h: Equation2590 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2591_implies_Equation2 (G: Type*) [Magma G] (h: Equation2591 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2593_implies_Equation2 (G: Type*) [Magma G] (h: Equation2593 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2594_implies_Equation2 (G: Type*) [Magma G] (h: Equation2594 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2595_implies_Equation2 (G: Type*) [Magma G] (h: Equation2595 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2597_implies_Equation2 (G: Type*) [Magma G] (h: Equation2597 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2598_implies_Equation2 (G: Type*) [Magma G] (h: Equation2598 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2599_implies_Equation2 (G: Type*) [Magma G] (h: Equation2599 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2600_implies_Equation2 (G: Type*) [Magma G] (h: Equation2600 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2606_implies_Equation2 (G: Type*) [Magma G] (h: Equation2606 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2607_implies_Equation2 (G: Type*) [Magma G] (h: Equation2607 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2608_implies_Equation2 (G: Type*) [Magma G] (h: Equation2608 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2610_implies_Equation2 (G: Type*) [Magma G] (h: Equation2610 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2611_implies_Equation2 (G: Type*) [Magma G] (h: Equation2611 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2612_implies_Equation2 (G: Type*) [Magma G] (h: Equation2612 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2614_implies_Equation2 (G: Type*) [Magma G] (h: Equation2614 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2615_implies_Equation2 (G: Type*) [Magma G] (h: Equation2615 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2616_implies_Equation2 (G: Type*) [Magma G] (h: Equation2616 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2617_implies_Equation2 (G: Type*) [Magma G] (h: Equation2617 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2624_implies_Equation2 (G: Type*) [Magma G] (h: Equation2624 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2625_implies_Equation2 (G: Type*) [Magma G] (h: Equation2625 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2626_implies_Equation2 (G: Type*) [Magma G] (h: Equation2626 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2627_implies_Equation2 (G: Type*) [Magma G] (h: Equation2627 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2629_implies_Equation2 (G: Type*) [Magma G] (h: Equation2629 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2630_implies_Equation2 (G: Type*) [Magma G] (h: Equation2630 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2631_implies_Equation2 (G: Type*) [Magma G] (h: Equation2631 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2632_implies_Equation2 (G: Type*) [Magma G] (h: Equation2632 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2634_implies_Equation2 (G: Type*) [Magma G] (h: Equation2634 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2635_implies_Equation2 (G: Type*) [Magma G] (h: Equation2635 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2636_implies_Equation2 (G: Type*) [Magma G] (h: Equation2636 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2637_implies_Equation2 (G: Type*) [Magma G] (h: Equation2637 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2639_implies_Equation2 (G: Type*) [Magma G] (h: Equation2639 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2640_implies_Equation2 (G: Type*) [Magma G] (h: Equation2640 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2641_implies_Equation2 (G: Type*) [Magma G] (h: Equation2641 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2642_implies_Equation2 (G: Type*) [Magma G] (h: Equation2642 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2643_implies_Equation2 (G: Type*) [Magma G] (h: Equation2643 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a a, ← h]

theorem Equation2747_implies_Equation2 (G: Type*) [Magma G] (h: Equation2747 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

theorem Equation2748_implies_Equation2 (G: Type*) [Magma G] (h: Equation2748 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2750_implies_Equation2 (G: Type*) [Magma G] (h: Equation2750 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2751_implies_Equation2 (G: Type*) [Magma G] (h: Equation2751 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2752_implies_Equation2 (G: Type*) [Magma G] (h: Equation2752 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2758_implies_Equation2 (G: Type*) [Magma G] (h: Equation2758 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2759_implies_Equation2 (G: Type*) [Magma G] (h: Equation2759 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2760_implies_Equation2 (G: Type*) [Magma G] (h: Equation2760 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2762_implies_Equation2 (G: Type*) [Magma G] (h: Equation2762 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2763_implies_Equation2 (G: Type*) [Magma G] (h: Equation2763 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2764_implies_Equation2 (G: Type*) [Magma G] (h: Equation2764 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2766_implies_Equation2 (G: Type*) [Magma G] (h: Equation2766 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2767_implies_Equation2 (G: Type*) [Magma G] (h: Equation2767 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2768_implies_Equation2 (G: Type*) [Magma G] (h: Equation2768 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2769_implies_Equation2 (G: Type*) [Magma G] (h: Equation2769 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2792_implies_Equation2 (G: Type*) [Magma G] (h: Equation2792 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2793_implies_Equation2 (G: Type*) [Magma G] (h: Equation2793 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2794_implies_Equation2 (G: Type*) [Magma G] (h: Equation2794 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2796_implies_Equation2 (G: Type*) [Magma G] (h: Equation2796 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2797_implies_Equation2 (G: Type*) [Magma G] (h: Equation2797 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2798_implies_Equation2 (G: Type*) [Magma G] (h: Equation2798 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2800_implies_Equation2 (G: Type*) [Magma G] (h: Equation2800 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2801_implies_Equation2 (G: Type*) [Magma G] (h: Equation2801 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2802_implies_Equation2 (G: Type*) [Magma G] (h: Equation2802 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2803_implies_Equation2 (G: Type*) [Magma G] (h: Equation2803 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2809_implies_Equation2 (G: Type*) [Magma G] (h: Equation2809 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2810_implies_Equation2 (G: Type*) [Magma G] (h: Equation2810 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2811_implies_Equation2 (G: Type*) [Magma G] (h: Equation2811 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2813_implies_Equation2 (G: Type*) [Magma G] (h: Equation2813 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2814_implies_Equation2 (G: Type*) [Magma G] (h: Equation2814 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2815_implies_Equation2 (G: Type*) [Magma G] (h: Equation2815 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2817_implies_Equation2 (G: Type*) [Magma G] (h: Equation2817 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2818_implies_Equation2 (G: Type*) [Magma G] (h: Equation2818 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2819_implies_Equation2 (G: Type*) [Magma G] (h: Equation2819 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2820_implies_Equation2 (G: Type*) [Magma G] (h: Equation2820 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2827_implies_Equation2 (G: Type*) [Magma G] (h: Equation2827 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2828_implies_Equation2 (G: Type*) [Magma G] (h: Equation2828 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2829_implies_Equation2 (G: Type*) [Magma G] (h: Equation2829 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2830_implies_Equation2 (G: Type*) [Magma G] (h: Equation2830 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2832_implies_Equation2 (G: Type*) [Magma G] (h: Equation2832 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2833_implies_Equation2 (G: Type*) [Magma G] (h: Equation2833 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2834_implies_Equation2 (G: Type*) [Magma G] (h: Equation2834 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2835_implies_Equation2 (G: Type*) [Magma G] (h: Equation2835 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2837_implies_Equation2 (G: Type*) [Magma G] (h: Equation2837 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2838_implies_Equation2 (G: Type*) [Magma G] (h: Equation2838 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2839_implies_Equation2 (G: Type*) [Magma G] (h: Equation2839 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2840_implies_Equation2 (G: Type*) [Magma G] (h: Equation2840 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2842_implies_Equation2 (G: Type*) [Magma G] (h: Equation2842 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2843_implies_Equation2 (G: Type*) [Magma G] (h: Equation2843 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2844_implies_Equation2 (G: Type*) [Magma G] (h: Equation2844 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2845_implies_Equation2 (G: Type*) [Magma G] (h: Equation2845 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2846_implies_Equation2 (G: Type*) [Magma G] (h: Equation2846 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a a, ← h]

theorem Equation2950_implies_Equation2 (G: Type*) [Magma G] (h: Equation2950 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

theorem Equation2951_implies_Equation2 (G: Type*) [Magma G] (h: Equation2951 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2953_implies_Equation2 (G: Type*) [Magma G] (h: Equation2953 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2954_implies_Equation2 (G: Type*) [Magma G] (h: Equation2954 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2955_implies_Equation2 (G: Type*) [Magma G] (h: Equation2955 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2961_implies_Equation2 (G: Type*) [Magma G] (h: Equation2961 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2962_implies_Equation2 (G: Type*) [Magma G] (h: Equation2962 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2963_implies_Equation2 (G: Type*) [Magma G] (h: Equation2963 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2965_implies_Equation2 (G: Type*) [Magma G] (h: Equation2965 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2966_implies_Equation2 (G: Type*) [Magma G] (h: Equation2966 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2967_implies_Equation2 (G: Type*) [Magma G] (h: Equation2967 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2969_implies_Equation2 (G: Type*) [Magma G] (h: Equation2969 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2970_implies_Equation2 (G: Type*) [Magma G] (h: Equation2970 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2971_implies_Equation2 (G: Type*) [Magma G] (h: Equation2971 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2972_implies_Equation2 (G: Type*) [Magma G] (h: Equation2972 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation2995_implies_Equation2 (G: Type*) [Magma G] (h: Equation2995 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2996_implies_Equation2 (G: Type*) [Magma G] (h: Equation2996 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation2997_implies_Equation2 (G: Type*) [Magma G] (h: Equation2997 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation2999_implies_Equation2 (G: Type*) [Magma G] (h: Equation2999 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation3000_implies_Equation2 (G: Type*) [Magma G] (h: Equation3000 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation3001_implies_Equation2 (G: Type*) [Magma G] (h: Equation3001 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3003_implies_Equation2 (G: Type*) [Magma G] (h: Equation3003 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3004_implies_Equation2 (G: Type*) [Magma G] (h: Equation3004 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3005_implies_Equation2 (G: Type*) [Magma G] (h: Equation3005 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3006_implies_Equation2 (G: Type*) [Magma G] (h: Equation3006 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation3012_implies_Equation2 (G: Type*) [Magma G] (h: Equation3012 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation3013_implies_Equation2 (G: Type*) [Magma G] (h: Equation3013 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation3014_implies_Equation2 (G: Type*) [Magma G] (h: Equation3014 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3016_implies_Equation2 (G: Type*) [Magma G] (h: Equation3016 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation3017_implies_Equation2 (G: Type*) [Magma G] (h: Equation3017 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation3018_implies_Equation2 (G: Type*) [Magma G] (h: Equation3018 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3020_implies_Equation2 (G: Type*) [Magma G] (h: Equation3020 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3021_implies_Equation2 (G: Type*) [Magma G] (h: Equation3021 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3022_implies_Equation2 (G: Type*) [Magma G] (h: Equation3022 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3023_implies_Equation2 (G: Type*) [Magma G] (h: Equation3023 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation3030_implies_Equation2 (G: Type*) [Magma G] (h: Equation3030 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3031_implies_Equation2 (G: Type*) [Magma G] (h: Equation3031 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3032_implies_Equation2 (G: Type*) [Magma G] (h: Equation3032 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3033_implies_Equation2 (G: Type*) [Magma G] (h: Equation3033 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation3035_implies_Equation2 (G: Type*) [Magma G] (h: Equation3035 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3036_implies_Equation2 (G: Type*) [Magma G] (h: Equation3036 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3037_implies_Equation2 (G: Type*) [Magma G] (h: Equation3037 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3038_implies_Equation2 (G: Type*) [Magma G] (h: Equation3038 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation3040_implies_Equation2 (G: Type*) [Magma G] (h: Equation3040 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3041_implies_Equation2 (G: Type*) [Magma G] (h: Equation3041 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3042_implies_Equation2 (G: Type*) [Magma G] (h: Equation3042 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3043_implies_Equation2 (G: Type*) [Magma G] (h: Equation3043 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation3045_implies_Equation2 (G: Type*) [Magma G] (h: Equation3045 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation3046_implies_Equation2 (G: Type*) [Magma G] (h: Equation3046 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation3047_implies_Equation2 (G: Type*) [Magma G] (h: Equation3047 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation3048_implies_Equation2 (G: Type*) [Magma G] (h: Equation3048 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation3049_implies_Equation2 (G: Type*) [Magma G] (h: Equation3049 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a a, ← h]

theorem Equation3153_implies_Equation2 (G: Type*) [Magma G] (h: Equation3153 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a, ← h]

theorem Equation3154_implies_Equation2 (G: Type*) [Magma G] (h: Equation3154 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation3156_implies_Equation2 (G: Type*) [Magma G] (h: Equation3156 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation3157_implies_Equation2 (G: Type*) [Magma G] (h: Equation3157 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation3158_implies_Equation2 (G: Type*) [Magma G] (h: Equation3158 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3164_implies_Equation2 (G: Type*) [Magma G] (h: Equation3164 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation3165_implies_Equation2 (G: Type*) [Magma G] (h: Equation3165 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation3166_implies_Equation2 (G: Type*) [Magma G] (h: Equation3166 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3168_implies_Equation2 (G: Type*) [Magma G] (h: Equation3168 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation3169_implies_Equation2 (G: Type*) [Magma G] (h: Equation3169 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation3170_implies_Equation2 (G: Type*) [Magma G] (h: Equation3170 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3172_implies_Equation2 (G: Type*) [Magma G] (h: Equation3172 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3173_implies_Equation2 (G: Type*) [Magma G] (h: Equation3173 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3174_implies_Equation2 (G: Type*) [Magma G] (h: Equation3174 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3175_implies_Equation2 (G: Type*) [Magma G] (h: Equation3175 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation3198_implies_Equation2 (G: Type*) [Magma G] (h: Equation3198 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation3199_implies_Equation2 (G: Type*) [Magma G] (h: Equation3199 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation3200_implies_Equation2 (G: Type*) [Magma G] (h: Equation3200 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3202_implies_Equation2 (G: Type*) [Magma G] (h: Equation3202 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation3203_implies_Equation2 (G: Type*) [Magma G] (h: Equation3203 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation3204_implies_Equation2 (G: Type*) [Magma G] (h: Equation3204 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3206_implies_Equation2 (G: Type*) [Magma G] (h: Equation3206 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3207_implies_Equation2 (G: Type*) [Magma G] (h: Equation3207 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3208_implies_Equation2 (G: Type*) [Magma G] (h: Equation3208 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3209_implies_Equation2 (G: Type*) [Magma G] (h: Equation3209 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation3215_implies_Equation2 (G: Type*) [Magma G] (h: Equation3215 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation3216_implies_Equation2 (G: Type*) [Magma G] (h: Equation3216 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation3217_implies_Equation2 (G: Type*) [Magma G] (h: Equation3217 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3219_implies_Equation2 (G: Type*) [Magma G] (h: Equation3219 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation3220_implies_Equation2 (G: Type*) [Magma G] (h: Equation3220 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a, ← h]

theorem Equation3221_implies_Equation2 (G: Type*) [Magma G] (h: Equation3221 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3223_implies_Equation2 (G: Type*) [Magma G] (h: Equation3223 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3224_implies_Equation2 (G: Type*) [Magma G] (h: Equation3224 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3225_implies_Equation2 (G: Type*) [Magma G] (h: Equation3225 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3226_implies_Equation2 (G: Type*) [Magma G] (h: Equation3226 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation3233_implies_Equation2 (G: Type*) [Magma G] (h: Equation3233 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3234_implies_Equation2 (G: Type*) [Magma G] (h: Equation3234 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3235_implies_Equation2 (G: Type*) [Magma G] (h: Equation3235 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3236_implies_Equation2 (G: Type*) [Magma G] (h: Equation3236 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation3238_implies_Equation2 (G: Type*) [Magma G] (h: Equation3238 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3239_implies_Equation2 (G: Type*) [Magma G] (h: Equation3239 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3240_implies_Equation2 (G: Type*) [Magma G] (h: Equation3240 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3241_implies_Equation2 (G: Type*) [Magma G] (h: Equation3241 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation3243_implies_Equation2 (G: Type*) [Magma G] (h: Equation3243 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3244_implies_Equation2 (G: Type*) [Magma G] (h: Equation3244 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3245_implies_Equation2 (G: Type*) [Magma G] (h: Equation3245 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a, ← h]

theorem Equation3246_implies_Equation2 (G: Type*) [Magma G] (h: Equation3246 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation3248_implies_Equation2 (G: Type*) [Magma G] (h: Equation3248 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation3249_implies_Equation2 (G: Type*) [Magma G] (h: Equation3249 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation3250_implies_Equation2 (G: Type*) [Magma G] (h: Equation3250 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation3251_implies_Equation2 (G: Type*) [Magma G] (h: Equation3251 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a, ← h]

theorem Equation3252_implies_Equation2 (G: Type*) [Magma G] (h: Equation3252 G) : Equation2 G :=
  fun a _ ↦ by rw [h a a a a a a, ← h]

end Singleton
