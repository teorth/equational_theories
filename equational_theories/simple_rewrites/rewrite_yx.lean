import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation1 (G: Type*) [Magma G] := ∀ x : G, x = x
def Equation2 (G: Type*) [Magma G] := ∀ x y : G, x = y
def Equation3 (G: Type*) [Magma G] := ∀ x : G, x = x ∘ x
def Equation4 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ y
def Equation5 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ x
def Equation6 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ y
def Equation8 (G: Type*) [Magma G] := ∀ x : G, x = x ∘ (x ∘ x)
def Equation9 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ y)
def Equation10 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ x)
def Equation11 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ y)
def Equation13 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ x)
def Equation14 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ y)
def Equation16 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ x)
def Equation17 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ y)
def Equation23 (G: Type*) [Magma G] := ∀ x : G, x = (x ∘ x) ∘ x
def Equation24 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ y
def Equation25 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ x
def Equation26 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ y
def Equation28 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ x
def Equation29 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ y
def Equation31 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ x
def Equation32 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ y
def Equation47 (G: Type*) [Magma G] := ∀ x : G, x = x ∘ (x ∘ (x ∘ x))
def Equation48 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (x ∘ y))
def Equation49 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (y ∘ x))
def Equation50 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (y ∘ y))
def Equation52 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (x ∘ x))
def Equation53 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (x ∘ y))
def Equation55 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (y ∘ x))
def Equation56 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (y ∘ y))
def Equation62 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (x ∘ x))
def Equation63 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (x ∘ y))
def Equation65 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (y ∘ x))
def Equation66 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (y ∘ y))
def Equation72 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (x ∘ x))
def Equation73 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (x ∘ y))
def Equation75 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (y ∘ x))
def Equation76 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (y ∘ y))
def Equation99 (G: Type*) [Magma G] := ∀ x : G, x = x ∘ ((x ∘ x) ∘ x)
def Equation100 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ x) ∘ y)
def Equation101 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ y) ∘ x)
def Equation102 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ y) ∘ y)
def Equation104 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ x) ∘ x)
def Equation105 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ x) ∘ y)
def Equation107 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ y) ∘ x)
def Equation108 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ y) ∘ y)
def Equation114 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ x) ∘ x)
def Equation115 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ x) ∘ y)
def Equation117 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ y) ∘ x)
def Equation118 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ y) ∘ y)
def Equation124 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ x) ∘ x)
def Equation125 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ x) ∘ y)
def Equation127 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ y) ∘ x)
def Equation128 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ y) ∘ y)
def Equation151 (G: Type*) [Magma G] := ∀ x : G, x = (x ∘ x) ∘ (x ∘ x)
def Equation152 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ (x ∘ y)
def Equation153 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ (y ∘ x)
def Equation154 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ (y ∘ y)
def Equation156 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (x ∘ x)
def Equation157 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (x ∘ y)
def Equation159 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (y ∘ x)
def Equation160 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (y ∘ y)
def Equation166 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (x ∘ x)
def Equation167 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (x ∘ y)
def Equation169 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (y ∘ x)
def Equation170 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (y ∘ y)
def Equation176 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (x ∘ x)
def Equation177 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (x ∘ y)
def Equation179 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (y ∘ x)
def Equation180 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (y ∘ y)
def Equation203 (G: Type*) [Magma G] := ∀ x : G, x = (x ∘ (x ∘ x)) ∘ x
def Equation204 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ x)) ∘ y
def Equation205 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ y)) ∘ x
def Equation206 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ y)) ∘ y
def Equation208 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ x)) ∘ x
def Equation209 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ x)) ∘ y
def Equation211 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ y)) ∘ x
def Equation212 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ y)) ∘ y
def Equation218 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ x)) ∘ x
def Equation219 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ x)) ∘ y
def Equation221 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ y)) ∘ x
def Equation222 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ y)) ∘ y
def Equation228 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ x)) ∘ x
def Equation229 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ x)) ∘ y
def Equation231 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ y)) ∘ x
def Equation232 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ y)) ∘ y
def Equation255 (G: Type*) [Magma G] := ∀ x : G, x = ((x ∘ x) ∘ x) ∘ x
def Equation256 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ x) ∘ y
def Equation257 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ y) ∘ x
def Equation258 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ y) ∘ y
def Equation260 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ x) ∘ x
def Equation261 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ x) ∘ y
def Equation263 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ y) ∘ x
def Equation264 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ y) ∘ y
def Equation270 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ x) ∘ x
def Equation271 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ x) ∘ y
def Equation273 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ y) ∘ x
def Equation274 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ y) ∘ y
def Equation280 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ x) ∘ x
def Equation281 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ x) ∘ y
def Equation283 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ y) ∘ x
def Equation284 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ y) ∘ y
def Equation307 (G: Type*) [Magma G] := ∀ x : G, x ∘ x = x ∘ (x ∘ x)
def Equation308 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ (x ∘ y)
def Equation309 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ (y ∘ x)
def Equation310 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ (y ∘ y)
def Equation312 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (x ∘ x)
def Equation313 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (x ∘ y)
def Equation315 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (y ∘ x)
def Equation316 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (y ∘ y)
def Equation322 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (x ∘ x)
def Equation323 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (x ∘ y)
def Equation325 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (y ∘ x)
def Equation326 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (y ∘ y)
def Equation332 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (x ∘ x)
def Equation333 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (x ∘ y)
def Equation335 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (y ∘ x)
def Equation336 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (y ∘ y)
def Equation359 (G: Type*) [Magma G] := ∀ x : G, x ∘ x = (x ∘ x) ∘ x
def Equation360 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ x) ∘ y
def Equation361 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ y) ∘ x
def Equation362 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ y) ∘ y
def Equation364 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ x) ∘ x
def Equation365 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ x) ∘ y
def Equation367 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ y) ∘ x
def Equation368 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ y) ∘ y
def Equation374 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ x) ∘ x
def Equation375 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ x) ∘ y
def Equation377 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ y) ∘ x
def Equation378 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ y) ∘ y
def Equation384 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ x) ∘ x
def Equation385 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ x) ∘ y
def Equation387 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ y) ∘ x
def Equation388 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ y) ∘ y
def Equation411 (G: Type*) [Magma G] := ∀ x : G, x = x ∘ (x ∘ (x ∘ (x ∘ x)))
def Equation412 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (x ∘ (x ∘ y)))
def Equation413 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (x ∘ (y ∘ x)))
def Equation414 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (x ∘ (y ∘ y)))
def Equation416 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (y ∘ (x ∘ x)))
def Equation417 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (y ∘ (x ∘ y)))
def Equation419 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (y ∘ (y ∘ x)))
def Equation420 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (y ∘ (y ∘ y)))
def Equation426 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (x ∘ (x ∘ x)))
def Equation427 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (x ∘ (x ∘ y)))
def Equation429 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (x ∘ (y ∘ x)))
def Equation430 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (x ∘ (y ∘ y)))
def Equation436 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (y ∘ (x ∘ x)))
def Equation437 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (y ∘ (x ∘ y)))
def Equation439 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (y ∘ (y ∘ x)))
def Equation440 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (y ∘ (y ∘ y)))
def Equation463 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (x ∘ (x ∘ x)))
def Equation464 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (x ∘ (x ∘ y)))
def Equation466 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (x ∘ (y ∘ x)))
def Equation467 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (x ∘ (y ∘ y)))
def Equation473 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (y ∘ (x ∘ x)))
def Equation474 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (y ∘ (x ∘ y)))
def Equation476 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (y ∘ (y ∘ x)))
def Equation477 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (y ∘ (y ∘ y)))
def Equation500 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (x ∘ (x ∘ x)))
def Equation501 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (x ∘ (x ∘ y)))
def Equation503 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (x ∘ (y ∘ x)))
def Equation504 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (x ∘ (y ∘ y)))
def Equation510 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (y ∘ (x ∘ x)))
def Equation511 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (y ∘ (x ∘ y)))
def Equation513 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (y ∘ (y ∘ x)))
def Equation514 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (y ∘ (y ∘ y)))
def Equation614 (G: Type*) [Magma G] := ∀ x : G, x = x ∘ (x ∘ ((x ∘ x) ∘ x))
def Equation615 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ ((x ∘ x) ∘ y))
def Equation616 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ ((x ∘ y) ∘ x))
def Equation617 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ ((x ∘ y) ∘ y))
def Equation619 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ ((y ∘ x) ∘ x))
def Equation620 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ ((y ∘ x) ∘ y))
def Equation622 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ ((y ∘ y) ∘ x))
def Equation623 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ ((y ∘ y) ∘ y))
def Equation629 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ ((x ∘ x) ∘ x))
def Equation630 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ ((x ∘ x) ∘ y))
def Equation632 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ ((x ∘ y) ∘ x))
def Equation633 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ ((x ∘ y) ∘ y))
def Equation639 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ ((y ∘ x) ∘ x))
def Equation640 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ ((y ∘ x) ∘ y))
def Equation642 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ ((y ∘ y) ∘ x))
def Equation643 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ ((y ∘ y) ∘ y))
def Equation666 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((x ∘ x) ∘ x))
def Equation667 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((x ∘ x) ∘ y))
def Equation669 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((x ∘ y) ∘ x))
def Equation670 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((x ∘ y) ∘ y))
def Equation676 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((y ∘ x) ∘ x))
def Equation677 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((y ∘ x) ∘ y))
def Equation679 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((y ∘ y) ∘ x))
def Equation680 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((y ∘ y) ∘ y))
def Equation703 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ ((x ∘ x) ∘ x))
def Equation704 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ ((x ∘ x) ∘ y))
def Equation706 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ ((x ∘ y) ∘ x))
def Equation707 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ ((x ∘ y) ∘ y))
def Equation713 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ ((y ∘ x) ∘ x))
def Equation714 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ ((y ∘ x) ∘ y))
def Equation716 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ ((y ∘ y) ∘ x))
def Equation717 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ ((y ∘ y) ∘ y))
def Equation817 (G: Type*) [Magma G] := ∀ x : G, x = x ∘ ((x ∘ x) ∘ (x ∘ x))
def Equation818 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ x) ∘ (x ∘ y))
def Equation819 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ x) ∘ (y ∘ x))
def Equation820 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ x) ∘ (y ∘ y))
def Equation822 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ y) ∘ (x ∘ x))
def Equation823 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ y) ∘ (x ∘ y))
def Equation825 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ y) ∘ (y ∘ x))
def Equation826 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ y) ∘ (y ∘ y))
def Equation832 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ x) ∘ (x ∘ x))
def Equation833 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ x) ∘ (x ∘ y))
def Equation835 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ x) ∘ (y ∘ x))
def Equation836 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ x) ∘ (y ∘ y))
def Equation842 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ y) ∘ (x ∘ x))
def Equation843 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ y) ∘ (x ∘ y))
def Equation845 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ y) ∘ (y ∘ x))
def Equation846 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ y) ∘ (y ∘ y))
def Equation869 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ x) ∘ (x ∘ x))
def Equation870 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ x) ∘ (x ∘ y))
def Equation872 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ x) ∘ (y ∘ x))
def Equation873 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ x) ∘ (y ∘ y))
def Equation879 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ y) ∘ (x ∘ x))
def Equation880 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ y) ∘ (x ∘ y))
def Equation882 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ y) ∘ (y ∘ x))
def Equation883 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ y) ∘ (y ∘ y))
def Equation906 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ x) ∘ (x ∘ x))
def Equation907 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ x) ∘ (x ∘ y))
def Equation909 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ x) ∘ (y ∘ x))
def Equation910 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ x) ∘ (y ∘ y))
def Equation916 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ y) ∘ (x ∘ x))
def Equation917 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ y) ∘ (x ∘ y))
def Equation919 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ y) ∘ (y ∘ x))
def Equation920 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ y) ∘ (y ∘ y))
def Equation1020 (G: Type*) [Magma G] := ∀ x : G, x = x ∘ ((x ∘ (x ∘ x)) ∘ x)
def Equation1021 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ (x ∘ x)) ∘ y)
def Equation1022 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ (x ∘ y)) ∘ x)
def Equation1023 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ (x ∘ y)) ∘ y)
def Equation1025 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ (y ∘ x)) ∘ x)
def Equation1026 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ (y ∘ x)) ∘ y)
def Equation1028 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ (y ∘ y)) ∘ x)
def Equation1029 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ (y ∘ y)) ∘ y)
def Equation1035 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ (x ∘ x)) ∘ x)
def Equation1036 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ (x ∘ x)) ∘ y)
def Equation1038 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ (x ∘ y)) ∘ x)
def Equation1039 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ (x ∘ y)) ∘ y)
def Equation1045 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ (y ∘ x)) ∘ x)
def Equation1046 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ (y ∘ x)) ∘ y)
def Equation1048 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ (y ∘ y)) ∘ x)
def Equation1049 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ (y ∘ y)) ∘ y)
def Equation1072 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (x ∘ x)) ∘ x)
def Equation1073 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (x ∘ x)) ∘ y)
def Equation1075 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (x ∘ y)) ∘ x)
def Equation1076 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (x ∘ y)) ∘ y)
def Equation1082 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (y ∘ x)) ∘ x)
def Equation1083 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (y ∘ x)) ∘ y)
def Equation1085 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (y ∘ y)) ∘ x)
def Equation1086 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (y ∘ y)) ∘ y)
def Equation1109 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ (x ∘ x)) ∘ x)
def Equation1110 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ (x ∘ x)) ∘ y)
def Equation1112 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ (x ∘ y)) ∘ x)
def Equation1113 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ (x ∘ y)) ∘ y)
def Equation1119 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ (y ∘ x)) ∘ x)
def Equation1120 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ (y ∘ x)) ∘ y)
def Equation1122 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ (y ∘ y)) ∘ x)
def Equation1123 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ (y ∘ y)) ∘ y)
def Equation1223 (G: Type*) [Magma G] := ∀ x : G, x = x ∘ (((x ∘ x) ∘ x) ∘ x)
def Equation1224 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((x ∘ x) ∘ x) ∘ y)
def Equation1225 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((x ∘ x) ∘ y) ∘ x)
def Equation1226 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((x ∘ x) ∘ y) ∘ y)
def Equation1228 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((x ∘ y) ∘ x) ∘ x)
def Equation1229 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((x ∘ y) ∘ x) ∘ y)
def Equation1231 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((x ∘ y) ∘ y) ∘ x)
def Equation1232 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((x ∘ y) ∘ y) ∘ y)
def Equation1238 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((y ∘ x) ∘ x) ∘ x)
def Equation1239 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((y ∘ x) ∘ x) ∘ y)
def Equation1241 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((y ∘ x) ∘ y) ∘ x)
def Equation1242 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((y ∘ x) ∘ y) ∘ y)
def Equation1248 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((y ∘ y) ∘ x) ∘ x)
def Equation1249 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((y ∘ y) ∘ x) ∘ y)
def Equation1251 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((y ∘ y) ∘ y) ∘ x)
def Equation1252 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((y ∘ y) ∘ y) ∘ y)
def Equation1275 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ x) ∘ x) ∘ x)
def Equation1276 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ x) ∘ x) ∘ y)
def Equation1278 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ x) ∘ y) ∘ x)
def Equation1279 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ x) ∘ y) ∘ y)
def Equation1285 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ y) ∘ x) ∘ x)
def Equation1286 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ y) ∘ x) ∘ y)
def Equation1288 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ y) ∘ y) ∘ x)
def Equation1289 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ y) ∘ y) ∘ y)
def Equation1312 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((y ∘ x) ∘ x) ∘ x)
def Equation1313 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((y ∘ x) ∘ x) ∘ y)
def Equation1315 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((y ∘ x) ∘ y) ∘ x)
def Equation1316 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((y ∘ x) ∘ y) ∘ y)
def Equation1322 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((y ∘ y) ∘ x) ∘ x)
def Equation1323 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((y ∘ y) ∘ x) ∘ y)
def Equation1325 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((y ∘ y) ∘ y) ∘ x)
def Equation1326 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((y ∘ y) ∘ y) ∘ y)
def Equation1426 (G: Type*) [Magma G] := ∀ x : G, x = (x ∘ x) ∘ (x ∘ (x ∘ x))
def Equation1427 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ (x ∘ (x ∘ y))
def Equation1428 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ (x ∘ (y ∘ x))
def Equation1429 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ (x ∘ (y ∘ y))
def Equation1431 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ (y ∘ (x ∘ x))
def Equation1432 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ (y ∘ (x ∘ y))
def Equation1434 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ (y ∘ (y ∘ x))
def Equation1435 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ (y ∘ (y ∘ y))
def Equation1441 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (x ∘ (x ∘ x))
def Equation1442 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (x ∘ (x ∘ y))
def Equation1444 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (x ∘ (y ∘ x))
def Equation1445 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (x ∘ (y ∘ y))
def Equation1451 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (y ∘ (x ∘ x))
def Equation1452 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (y ∘ (x ∘ y))
def Equation1454 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (y ∘ (y ∘ x))
def Equation1455 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (y ∘ (y ∘ y))
def Equation1478 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (x ∘ (x ∘ x))
def Equation1479 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (x ∘ (x ∘ y))
def Equation1481 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (x ∘ (y ∘ x))
def Equation1482 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (x ∘ (y ∘ y))
def Equation1488 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (y ∘ (x ∘ x))
def Equation1489 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (y ∘ (x ∘ y))
def Equation1491 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (y ∘ (y ∘ x))
def Equation1492 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (y ∘ (y ∘ y))
def Equation1515 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (x ∘ (x ∘ x))
def Equation1516 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (x ∘ (x ∘ y))
def Equation1518 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (x ∘ (y ∘ x))
def Equation1519 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (x ∘ (y ∘ y))
def Equation1525 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (y ∘ (x ∘ x))
def Equation1526 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (y ∘ (x ∘ y))
def Equation1528 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (y ∘ (y ∘ x))
def Equation1529 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (y ∘ (y ∘ y))
def Equation1629 (G: Type*) [Magma G] := ∀ x : G, x = (x ∘ x) ∘ ((x ∘ x) ∘ x)
def Equation1630 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ ((x ∘ x) ∘ y)
def Equation1631 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ ((x ∘ y) ∘ x)
def Equation1632 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ ((x ∘ y) ∘ y)
def Equation1634 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ ((y ∘ x) ∘ x)
def Equation1635 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ ((y ∘ x) ∘ y)
def Equation1637 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ ((y ∘ y) ∘ x)
def Equation1638 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ ((y ∘ y) ∘ y)
def Equation1644 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ ((x ∘ x) ∘ x)
def Equation1645 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ ((x ∘ x) ∘ y)
def Equation1647 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ ((x ∘ y) ∘ x)
def Equation1648 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ ((x ∘ y) ∘ y)
def Equation1654 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ ((y ∘ x) ∘ x)
def Equation1655 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ ((y ∘ x) ∘ y)
def Equation1657 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ ((y ∘ y) ∘ x)
def Equation1658 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ ((y ∘ y) ∘ y)
def Equation1681 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((x ∘ x) ∘ x)
def Equation1682 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((x ∘ x) ∘ y)
def Equation1684 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((x ∘ y) ∘ x)
def Equation1685 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((x ∘ y) ∘ y)
def Equation1691 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((y ∘ x) ∘ x)
def Equation1692 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((y ∘ x) ∘ y)
def Equation1694 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((y ∘ y) ∘ x)
def Equation1695 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((y ∘ y) ∘ y)
def Equation1718 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ ((x ∘ x) ∘ x)
def Equation1719 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ ((x ∘ x) ∘ y)
def Equation1721 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ ((x ∘ y) ∘ x)
def Equation1722 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ ((x ∘ y) ∘ y)
def Equation1728 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ ((y ∘ x) ∘ x)
def Equation1729 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ ((y ∘ x) ∘ y)
def Equation1731 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ ((y ∘ y) ∘ x)
def Equation1732 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ ((y ∘ y) ∘ y)
def Equation1832 (G: Type*) [Magma G] := ∀ x : G, x = (x ∘ (x ∘ x)) ∘ (x ∘ x)
def Equation1833 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ x)) ∘ (x ∘ y)
def Equation1834 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ x)) ∘ (y ∘ x)
def Equation1835 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ x)) ∘ (y ∘ y)
def Equation1837 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ y)) ∘ (x ∘ x)
def Equation1838 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ y)) ∘ (x ∘ y)
def Equation1840 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ y)) ∘ (y ∘ x)
def Equation1841 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ y)) ∘ (y ∘ y)
def Equation1847 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ x)) ∘ (x ∘ x)
def Equation1848 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ x)) ∘ (x ∘ y)
def Equation1850 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ x)) ∘ (y ∘ x)
def Equation1851 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ x)) ∘ (y ∘ y)
def Equation1857 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ y)) ∘ (x ∘ x)
def Equation1858 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ y)) ∘ (x ∘ y)
def Equation1860 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ y)) ∘ (y ∘ x)
def Equation1861 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ y)) ∘ (y ∘ y)
def Equation1884 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ x)) ∘ (x ∘ x)
def Equation1885 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ x)) ∘ (x ∘ y)
def Equation1887 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ x)) ∘ (y ∘ x)
def Equation1888 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ x)) ∘ (y ∘ y)
def Equation1894 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ y)) ∘ (x ∘ x)
def Equation1895 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ y)) ∘ (x ∘ y)
def Equation1897 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ y)) ∘ (y ∘ x)
def Equation1898 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ y)) ∘ (y ∘ y)
def Equation1921 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ x)) ∘ (x ∘ x)
def Equation1922 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ x)) ∘ (x ∘ y)
def Equation1924 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ x)) ∘ (y ∘ x)
def Equation1925 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ x)) ∘ (y ∘ y)
def Equation1931 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ y)) ∘ (x ∘ x)
def Equation1932 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ y)) ∘ (x ∘ y)
def Equation1934 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ y)) ∘ (y ∘ x)
def Equation1935 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ y)) ∘ (y ∘ y)
def Equation2035 (G: Type*) [Magma G] := ∀ x : G, x = ((x ∘ x) ∘ x) ∘ (x ∘ x)
def Equation2036 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ x) ∘ (x ∘ y)
def Equation2037 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ x) ∘ (y ∘ x)
def Equation2038 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ x) ∘ (y ∘ y)
def Equation2040 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ y) ∘ (x ∘ x)
def Equation2041 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ y) ∘ (x ∘ y)
def Equation2043 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ y) ∘ (y ∘ x)
def Equation2044 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ y) ∘ (y ∘ y)
def Equation2050 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ x) ∘ (x ∘ x)
def Equation2051 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ x) ∘ (x ∘ y)
def Equation2053 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ x) ∘ (y ∘ x)
def Equation2054 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ x) ∘ (y ∘ y)
def Equation2060 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ y) ∘ (x ∘ x)
def Equation2061 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ y) ∘ (x ∘ y)
def Equation2063 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ y) ∘ (y ∘ x)
def Equation2064 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ y) ∘ (y ∘ y)
def Equation2087 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ x) ∘ (x ∘ x)
def Equation2088 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ x) ∘ (x ∘ y)
def Equation2090 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ x) ∘ (y ∘ x)
def Equation2091 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ x) ∘ (y ∘ y)
def Equation2097 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ y) ∘ (x ∘ x)
def Equation2098 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ y) ∘ (x ∘ y)
def Equation2100 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ y) ∘ (y ∘ x)
def Equation2101 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ y) ∘ (y ∘ y)
def Equation2124 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ x) ∘ (x ∘ x)
def Equation2125 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ x) ∘ (x ∘ y)
def Equation2127 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ x) ∘ (y ∘ x)
def Equation2128 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ x) ∘ (y ∘ y)
def Equation2134 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ y) ∘ (x ∘ x)
def Equation2135 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ y) ∘ (x ∘ y)
def Equation2137 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ y) ∘ (y ∘ x)
def Equation2138 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ y) ∘ (y ∘ y)
def Equation2238 (G: Type*) [Magma G] := ∀ x : G, x = (x ∘ (x ∘ (x ∘ x))) ∘ x
def Equation2239 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ (x ∘ x))) ∘ y
def Equation2240 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ (x ∘ y))) ∘ x
def Equation2241 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ (x ∘ y))) ∘ y
def Equation2243 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ (y ∘ x))) ∘ x
def Equation2244 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ (y ∘ x))) ∘ y
def Equation2246 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ (y ∘ y))) ∘ x
def Equation2247 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ (y ∘ y))) ∘ y
def Equation2253 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ (x ∘ x))) ∘ x
def Equation2254 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ (x ∘ x))) ∘ y
def Equation2256 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ (x ∘ y))) ∘ x
def Equation2257 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ (x ∘ y))) ∘ y
def Equation2263 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ (y ∘ x))) ∘ x
def Equation2264 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ (y ∘ x))) ∘ y
def Equation2266 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ (y ∘ y))) ∘ x
def Equation2267 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ (y ∘ y))) ∘ y
def Equation2290 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (x ∘ x))) ∘ x
def Equation2291 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (x ∘ x))) ∘ y
def Equation2293 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (x ∘ y))) ∘ x
def Equation2294 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (x ∘ y))) ∘ y
def Equation2300 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (y ∘ x))) ∘ x
def Equation2301 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (y ∘ x))) ∘ y
def Equation2303 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (y ∘ y))) ∘ x
def Equation2304 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (y ∘ y))) ∘ y
def Equation2327 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ (x ∘ x))) ∘ x
def Equation2328 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ (x ∘ x))) ∘ y
def Equation2330 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ (x ∘ y))) ∘ x
def Equation2331 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ (x ∘ y))) ∘ y
def Equation2337 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ (y ∘ x))) ∘ x
def Equation2338 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ (y ∘ x))) ∘ y
def Equation2340 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ (y ∘ y))) ∘ x
def Equation2341 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ (y ∘ y))) ∘ y
def Equation2441 (G: Type*) [Magma G] := ∀ x : G, x = (x ∘ ((x ∘ x) ∘ x)) ∘ x
def Equation2442 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((x ∘ x) ∘ x)) ∘ y
def Equation2443 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((x ∘ x) ∘ y)) ∘ x
def Equation2444 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((x ∘ x) ∘ y)) ∘ y
def Equation2446 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((x ∘ y) ∘ x)) ∘ x
def Equation2447 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((x ∘ y) ∘ x)) ∘ y
def Equation2449 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((x ∘ y) ∘ y)) ∘ x
def Equation2450 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((x ∘ y) ∘ y)) ∘ y
def Equation2456 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((y ∘ x) ∘ x)) ∘ x
def Equation2457 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((y ∘ x) ∘ x)) ∘ y
def Equation2459 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((y ∘ x) ∘ y)) ∘ x
def Equation2460 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((y ∘ x) ∘ y)) ∘ y
def Equation2466 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((y ∘ y) ∘ x)) ∘ x
def Equation2467 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((y ∘ y) ∘ x)) ∘ y
def Equation2469 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((y ∘ y) ∘ y)) ∘ x
def Equation2470 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((y ∘ y) ∘ y)) ∘ y
def Equation2493 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ x) ∘ x)) ∘ x
def Equation2494 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ x) ∘ x)) ∘ y
def Equation2496 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ x) ∘ y)) ∘ x
def Equation2497 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ x) ∘ y)) ∘ y
def Equation2503 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ y) ∘ x)) ∘ x
def Equation2504 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ y) ∘ x)) ∘ y
def Equation2506 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ y) ∘ y)) ∘ x
def Equation2507 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ y) ∘ y)) ∘ y
def Equation2530 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((y ∘ x) ∘ x)) ∘ x
def Equation2531 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((y ∘ x) ∘ x)) ∘ y
def Equation2533 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((y ∘ x) ∘ y)) ∘ x
def Equation2534 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((y ∘ x) ∘ y)) ∘ y
def Equation2540 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((y ∘ y) ∘ x)) ∘ x
def Equation2541 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((y ∘ y) ∘ x)) ∘ y
def Equation2543 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((y ∘ y) ∘ y)) ∘ x
def Equation2544 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((y ∘ y) ∘ y)) ∘ y
def Equation2644 (G: Type*) [Magma G] := ∀ x : G, x = ((x ∘ x) ∘ (x ∘ x)) ∘ x
def Equation2645 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ (x ∘ x)) ∘ y
def Equation2646 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ (x ∘ y)) ∘ x
def Equation2647 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ (x ∘ y)) ∘ y
def Equation2649 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ (y ∘ x)) ∘ x
def Equation2650 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ (y ∘ x)) ∘ y
def Equation2652 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ (y ∘ y)) ∘ x
def Equation2653 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ (y ∘ y)) ∘ y
def Equation2659 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ (x ∘ x)) ∘ x
def Equation2660 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ (x ∘ x)) ∘ y
def Equation2662 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ (x ∘ y)) ∘ x
def Equation2663 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ (x ∘ y)) ∘ y
def Equation2669 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ (y ∘ x)) ∘ x
def Equation2670 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ (y ∘ x)) ∘ y
def Equation2672 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ (y ∘ y)) ∘ x
def Equation2673 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ (y ∘ y)) ∘ y
def Equation2696 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (x ∘ x)) ∘ x
def Equation2697 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (x ∘ x)) ∘ y
def Equation2699 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (x ∘ y)) ∘ x
def Equation2700 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (x ∘ y)) ∘ y
def Equation2706 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (y ∘ x)) ∘ x
def Equation2707 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (y ∘ x)) ∘ y
def Equation2709 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (y ∘ y)) ∘ x
def Equation2710 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (y ∘ y)) ∘ y
def Equation2733 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ (x ∘ x)) ∘ x
def Equation2734 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ (x ∘ x)) ∘ y
def Equation2736 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ (x ∘ y)) ∘ x
def Equation2737 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ (x ∘ y)) ∘ y
def Equation2743 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ (y ∘ x)) ∘ x
def Equation2744 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ (y ∘ x)) ∘ y
def Equation2746 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ (y ∘ y)) ∘ x
def Equation2747 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ (y ∘ y)) ∘ y
def Equation2847 (G: Type*) [Magma G] := ∀ x : G, x = ((x ∘ (x ∘ x)) ∘ x) ∘ x
def Equation2848 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (x ∘ x)) ∘ x) ∘ y
def Equation2849 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (x ∘ x)) ∘ y) ∘ x
def Equation2850 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (x ∘ x)) ∘ y) ∘ y
def Equation2852 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (x ∘ y)) ∘ x) ∘ x
def Equation2853 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (x ∘ y)) ∘ x) ∘ y
def Equation2855 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (x ∘ y)) ∘ y) ∘ x
def Equation2856 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (x ∘ y)) ∘ y) ∘ y
def Equation2862 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (y ∘ x)) ∘ x) ∘ x
def Equation2863 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (y ∘ x)) ∘ x) ∘ y
def Equation2865 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (y ∘ x)) ∘ y) ∘ x
def Equation2866 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (y ∘ x)) ∘ y) ∘ y
def Equation2872 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (y ∘ y)) ∘ x) ∘ x
def Equation2873 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (y ∘ y)) ∘ x) ∘ y
def Equation2875 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (y ∘ y)) ∘ y) ∘ x
def Equation2876 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (y ∘ y)) ∘ y) ∘ y
def Equation2899 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ x)) ∘ x) ∘ x
def Equation2900 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ x)) ∘ x) ∘ y
def Equation2902 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ x)) ∘ y) ∘ x
def Equation2903 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ x)) ∘ y) ∘ y
def Equation2909 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ y)) ∘ x) ∘ x
def Equation2910 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ y)) ∘ x) ∘ y
def Equation2912 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ y)) ∘ y) ∘ x
def Equation2913 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ y)) ∘ y) ∘ y
def Equation2936 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (y ∘ x)) ∘ x) ∘ x
def Equation2937 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (y ∘ x)) ∘ x) ∘ y
def Equation2939 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (y ∘ x)) ∘ y) ∘ x
def Equation2940 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (y ∘ x)) ∘ y) ∘ y
def Equation2946 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (y ∘ y)) ∘ x) ∘ x
def Equation2947 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (y ∘ y)) ∘ x) ∘ y
def Equation2949 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (y ∘ y)) ∘ y) ∘ x
def Equation2950 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (y ∘ y)) ∘ y) ∘ y
def Equation3050 (G: Type*) [Magma G] := ∀ x : G, x = (((x ∘ x) ∘ x) ∘ x) ∘ x
def Equation3051 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ x) ∘ x) ∘ x) ∘ y
def Equation3052 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ x) ∘ x) ∘ y) ∘ x
def Equation3053 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ x) ∘ x) ∘ y) ∘ y
def Equation3055 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ x) ∘ y) ∘ x) ∘ x
def Equation3056 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ x) ∘ y) ∘ x) ∘ y
def Equation3058 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ x) ∘ y) ∘ y) ∘ x
def Equation3059 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ x) ∘ y) ∘ y) ∘ y
def Equation3065 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ y) ∘ x) ∘ x) ∘ x
def Equation3066 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ y) ∘ x) ∘ x) ∘ y
def Equation3068 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ y) ∘ x) ∘ y) ∘ x
def Equation3069 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ y) ∘ x) ∘ y) ∘ y
def Equation3075 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ y) ∘ y) ∘ x) ∘ x
def Equation3076 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ y) ∘ y) ∘ x) ∘ y
def Equation3078 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ y) ∘ y) ∘ y) ∘ x
def Equation3079 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ y) ∘ y) ∘ y) ∘ y
def Equation3102 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ x) ∘ x) ∘ x
def Equation3103 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ x) ∘ x) ∘ y
def Equation3105 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ x) ∘ y) ∘ x
def Equation3106 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ x) ∘ y) ∘ y
def Equation3112 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ y) ∘ x) ∘ x
def Equation3113 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ y) ∘ x) ∘ y
def Equation3115 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ y) ∘ y) ∘ x
def Equation3116 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ y) ∘ y) ∘ y
def Equation3139 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ y) ∘ x) ∘ x) ∘ x
def Equation3140 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ y) ∘ x) ∘ x) ∘ y
def Equation3142 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ y) ∘ x) ∘ y) ∘ x
def Equation3143 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ y) ∘ x) ∘ y) ∘ y
def Equation3149 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ y) ∘ y) ∘ x) ∘ x
def Equation3150 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ y) ∘ y) ∘ x) ∘ y
def Equation3152 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ y) ∘ y) ∘ y) ∘ x
def Equation3153 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ y) ∘ y) ∘ y) ∘ y
def Equation3253 (G: Type*) [Magma G] := ∀ x : G, x ∘ x = x ∘ (x ∘ (x ∘ x))
def Equation3254 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ (x ∘ (x ∘ y))
def Equation3255 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ (x ∘ (y ∘ x))
def Equation3256 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ (x ∘ (y ∘ y))
def Equation3258 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ (y ∘ (x ∘ x))
def Equation3259 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ (y ∘ (x ∘ y))
def Equation3261 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ (y ∘ (y ∘ x))
def Equation3262 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ (y ∘ (y ∘ y))
def Equation3268 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (x ∘ (x ∘ x))
def Equation3269 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (x ∘ (x ∘ y))
def Equation3271 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (x ∘ (y ∘ x))
def Equation3272 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (x ∘ (y ∘ y))
def Equation3278 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (y ∘ (x ∘ x))
def Equation3279 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (y ∘ (x ∘ y))
def Equation3281 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (y ∘ (y ∘ x))
def Equation3282 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (y ∘ (y ∘ y))
def Equation3305 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (x ∘ (x ∘ x))
def Equation3306 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (x ∘ (x ∘ y))
def Equation3308 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (x ∘ (y ∘ x))
def Equation3309 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (x ∘ (y ∘ y))
def Equation3315 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (y ∘ (x ∘ x))
def Equation3316 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (y ∘ (x ∘ y))
def Equation3318 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (y ∘ (y ∘ x))
def Equation3319 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (y ∘ (y ∘ y))
def Equation3342 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (x ∘ (x ∘ x))
def Equation3343 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (x ∘ (x ∘ y))
def Equation3345 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (x ∘ (y ∘ x))
def Equation3346 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (x ∘ (y ∘ y))
def Equation3352 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (y ∘ (x ∘ x))
def Equation3353 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (y ∘ (x ∘ y))
def Equation3355 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (y ∘ (y ∘ x))
def Equation3356 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (y ∘ (y ∘ y))
def Equation3456 (G: Type*) [Magma G] := ∀ x : G, x ∘ x = x ∘ ((x ∘ x) ∘ x)
def Equation3457 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ ((x ∘ x) ∘ y)
def Equation3458 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ ((x ∘ y) ∘ x)
def Equation3459 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ ((x ∘ y) ∘ y)
def Equation3461 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ ((y ∘ x) ∘ x)
def Equation3462 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ ((y ∘ x) ∘ y)
def Equation3464 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ ((y ∘ y) ∘ x)
def Equation3465 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ ((y ∘ y) ∘ y)
def Equation3471 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ ((x ∘ x) ∘ x)
def Equation3472 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ ((x ∘ x) ∘ y)
def Equation3474 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ ((x ∘ y) ∘ x)
def Equation3475 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ ((x ∘ y) ∘ y)
def Equation3481 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ ((y ∘ x) ∘ x)
def Equation3482 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ ((y ∘ x) ∘ y)
def Equation3484 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ ((y ∘ y) ∘ x)
def Equation3485 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ ((y ∘ y) ∘ y)
def Equation3508 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((x ∘ x) ∘ x)
def Equation3509 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((x ∘ x) ∘ y)
def Equation3511 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((x ∘ y) ∘ x)
def Equation3512 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((x ∘ y) ∘ y)
def Equation3518 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((y ∘ x) ∘ x)
def Equation3519 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((y ∘ x) ∘ y)
def Equation3521 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((y ∘ y) ∘ x)
def Equation3522 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((y ∘ y) ∘ y)
def Equation3545 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ ((x ∘ x) ∘ x)
def Equation3546 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ ((x ∘ x) ∘ y)
def Equation3548 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ ((x ∘ y) ∘ x)
def Equation3549 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ ((x ∘ y) ∘ y)
def Equation3555 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ ((y ∘ x) ∘ x)
def Equation3556 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ ((y ∘ x) ∘ y)
def Equation3558 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ ((y ∘ y) ∘ x)
def Equation3559 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ ((y ∘ y) ∘ y)
def Equation3659 (G: Type*) [Magma G] := ∀ x : G, x ∘ x = (x ∘ x) ∘ (x ∘ x)
def Equation3660 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ x) ∘ (x ∘ y)
def Equation3661 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ x) ∘ (y ∘ x)
def Equation3662 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ x) ∘ (y ∘ y)
def Equation3664 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ y) ∘ (x ∘ x)
def Equation3665 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ y) ∘ (x ∘ y)
def Equation3667 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ y) ∘ (y ∘ x)
def Equation3668 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ y) ∘ (y ∘ y)
def Equation3674 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ x) ∘ (x ∘ x)
def Equation3675 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ x) ∘ (x ∘ y)
def Equation3677 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ x) ∘ (y ∘ x)
def Equation3678 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ x) ∘ (y ∘ y)
def Equation3684 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ y) ∘ (x ∘ x)
def Equation3685 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ y) ∘ (x ∘ y)
def Equation3687 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ y) ∘ (y ∘ x)
def Equation3688 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ y) ∘ (y ∘ y)
def Equation3711 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ x) ∘ (x ∘ x)
def Equation3712 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ x) ∘ (x ∘ y)
def Equation3714 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ x) ∘ (y ∘ x)
def Equation3715 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ x) ∘ (y ∘ y)
def Equation3721 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ y) ∘ (x ∘ x)
def Equation3722 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ y) ∘ (x ∘ y)
def Equation3724 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ y) ∘ (y ∘ x)
def Equation3725 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ y) ∘ (y ∘ y)
def Equation3748 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ x) ∘ (x ∘ x)
def Equation3749 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ x) ∘ (x ∘ y)
def Equation3751 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ x) ∘ (y ∘ x)
def Equation3752 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ x) ∘ (y ∘ y)
def Equation3758 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ y) ∘ (x ∘ x)
def Equation3759 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ y) ∘ (x ∘ y)
def Equation3761 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ y) ∘ (y ∘ x)
def Equation3762 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ y) ∘ (y ∘ y)
def Equation3862 (G: Type*) [Magma G] := ∀ x : G, x ∘ x = (x ∘ (x ∘ x)) ∘ x
def Equation3863 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ (x ∘ x)) ∘ y
def Equation3864 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ (x ∘ y)) ∘ x
def Equation3865 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ (x ∘ y)) ∘ y
def Equation3867 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ (y ∘ x)) ∘ x
def Equation3868 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ (y ∘ x)) ∘ y
def Equation3870 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ (y ∘ y)) ∘ x
def Equation3871 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ (y ∘ y)) ∘ y
def Equation3877 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ (x ∘ x)) ∘ x
def Equation3878 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ (x ∘ x)) ∘ y
def Equation3880 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ (x ∘ y)) ∘ x
def Equation3881 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ (x ∘ y)) ∘ y
def Equation3887 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ (y ∘ x)) ∘ x
def Equation3888 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ (y ∘ x)) ∘ y
def Equation3890 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ (y ∘ y)) ∘ x
def Equation3891 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ (y ∘ y)) ∘ y
def Equation3914 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (x ∘ x)) ∘ x
def Equation3915 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (x ∘ x)) ∘ y
def Equation3917 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (x ∘ y)) ∘ x
def Equation3918 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (x ∘ y)) ∘ y
def Equation3924 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (y ∘ x)) ∘ x
def Equation3925 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (y ∘ x)) ∘ y
def Equation3927 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (y ∘ y)) ∘ x
def Equation3928 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (y ∘ y)) ∘ y
def Equation3951 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ (x ∘ x)) ∘ x
def Equation3952 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ (x ∘ x)) ∘ y
def Equation3954 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ (x ∘ y)) ∘ x
def Equation3955 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ (x ∘ y)) ∘ y
def Equation3961 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ (y ∘ x)) ∘ x
def Equation3962 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ (y ∘ x)) ∘ y
def Equation3964 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ (y ∘ y)) ∘ x
def Equation3965 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ (y ∘ y)) ∘ y
def Equation4065 (G: Type*) [Magma G] := ∀ x : G, x ∘ x = ((x ∘ x) ∘ x) ∘ x
def Equation4066 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((x ∘ x) ∘ x) ∘ y
def Equation4067 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((x ∘ x) ∘ y) ∘ x
def Equation4068 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((x ∘ x) ∘ y) ∘ y
def Equation4070 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((x ∘ y) ∘ x) ∘ x
def Equation4071 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((x ∘ y) ∘ x) ∘ y
def Equation4073 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((x ∘ y) ∘ y) ∘ x
def Equation4074 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((x ∘ y) ∘ y) ∘ y
def Equation4080 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((y ∘ x) ∘ x) ∘ x
def Equation4081 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((y ∘ x) ∘ x) ∘ y
def Equation4083 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((y ∘ x) ∘ y) ∘ x
def Equation4084 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((y ∘ x) ∘ y) ∘ y
def Equation4090 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((y ∘ y) ∘ x) ∘ x
def Equation4091 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((y ∘ y) ∘ x) ∘ y
def Equation4093 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((y ∘ y) ∘ y) ∘ x
def Equation4094 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((y ∘ y) ∘ y) ∘ y
def Equation4117 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ x) ∘ x) ∘ x
def Equation4118 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ x) ∘ x) ∘ y
def Equation4120 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ x) ∘ y) ∘ x
def Equation4121 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ x) ∘ y) ∘ y
def Equation4127 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ y) ∘ x) ∘ x
def Equation4128 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ y) ∘ x) ∘ y
def Equation4130 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ y) ∘ y) ∘ x
def Equation4131 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ y) ∘ y) ∘ y
def Equation4154 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((y ∘ x) ∘ x) ∘ x
def Equation4155 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((y ∘ x) ∘ x) ∘ y
def Equation4157 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((y ∘ x) ∘ y) ∘ x
def Equation4158 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((y ∘ x) ∘ y) ∘ y
def Equation4164 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((y ∘ y) ∘ x) ∘ x
def Equation4165 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((y ∘ y) ∘ x) ∘ y
def Equation4167 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((y ∘ y) ∘ y) ∘ x
def Equation4168 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((y ∘ y) ∘ y) ∘ y
def Equation4380 (G: Type*) [Magma G] := ∀ x : G, x ∘ (x ∘ x) = (x ∘ x) ∘ x
def Equation4381 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = (x ∘ x) ∘ y
def Equation4382 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = (x ∘ y) ∘ x
def Equation4383 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = (x ∘ y) ∘ y
def Equation4385 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = (y ∘ x) ∘ x
def Equation4386 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = (y ∘ x) ∘ y
def Equation4388 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = (y ∘ y) ∘ x
def Equation4389 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = (y ∘ y) ∘ y
def Equation4395 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = (x ∘ x) ∘ x
def Equation4396 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = (x ∘ x) ∘ y
def Equation4398 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = (x ∘ y) ∘ x
def Equation4399 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = (x ∘ y) ∘ y
def Equation4405 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = (y ∘ x) ∘ x
def Equation4406 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = (y ∘ x) ∘ y
def Equation4408 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = (y ∘ y) ∘ x
def Equation4409 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = (y ∘ y) ∘ y
def Equation4432 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (x ∘ x) ∘ x
def Equation4433 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (x ∘ x) ∘ y
def Equation4435 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (x ∘ y) ∘ x
def Equation4436 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (x ∘ y) ∘ y
def Equation4442 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (y ∘ x) ∘ x
def Equation4443 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (y ∘ x) ∘ y
def Equation4445 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (y ∘ y) ∘ x
def Equation4446 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (y ∘ y) ∘ y
def Equation4469 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = (x ∘ x) ∘ x
def Equation4470 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = (x ∘ x) ∘ y
def Equation4472 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = (x ∘ y) ∘ x
def Equation4473 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = (x ∘ y) ∘ y
def Equation4479 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = (y ∘ x) ∘ x
def Equation4480 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = (y ∘ x) ∘ y
def Equation4482 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = (y ∘ y) ∘ x
def Equation4483 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = (y ∘ y) ∘ y
theorem Equation2_implies_Equation1 (G : Type*) [Magma G] (h : Equation2 G) : Equation1 G := λ x => h x x
theorem Equation4_implies_Equation3 (G : Type*) [Magma G] (h : Equation4 G) : Equation3 G := λ x => h x x
theorem Equation5_implies_Equation3 (G : Type*) [Magma G] (h : Equation5 G) : Equation3 G := λ x => h x x
theorem Equation6_implies_Equation3 (G : Type*) [Magma G] (h : Equation6 G) : Equation3 G := λ x => h x x
theorem Equation9_implies_Equation8 (G : Type*) [Magma G] (h : Equation9 G) : Equation8 G := λ x => h x x
theorem Equation10_implies_Equation8 (G : Type*) [Magma G] (h : Equation10 G) : Equation8 G := λ x => h x x
theorem Equation11_implies_Equation8 (G : Type*) [Magma G] (h : Equation11 G) : Equation8 G := λ x => h x x
theorem Equation13_implies_Equation8 (G : Type*) [Magma G] (h : Equation13 G) : Equation8 G := λ x => h x x
theorem Equation14_implies_Equation8 (G : Type*) [Magma G] (h : Equation14 G) : Equation8 G := λ x => h x x
theorem Equation16_implies_Equation8 (G : Type*) [Magma G] (h : Equation16 G) : Equation8 G := λ x => h x x
theorem Equation17_implies_Equation8 (G : Type*) [Magma G] (h : Equation17 G) : Equation8 G := λ x => h x x
theorem Equation24_implies_Equation23 (G : Type*) [Magma G] (h : Equation24 G) : Equation23 G := λ x => h x x
theorem Equation25_implies_Equation23 (G : Type*) [Magma G] (h : Equation25 G) : Equation23 G := λ x => h x x
theorem Equation26_implies_Equation23 (G : Type*) [Magma G] (h : Equation26 G) : Equation23 G := λ x => h x x
theorem Equation28_implies_Equation23 (G : Type*) [Magma G] (h : Equation28 G) : Equation23 G := λ x => h x x
theorem Equation29_implies_Equation23 (G : Type*) [Magma G] (h : Equation29 G) : Equation23 G := λ x => h x x
theorem Equation31_implies_Equation23 (G : Type*) [Magma G] (h : Equation31 G) : Equation23 G := λ x => h x x
theorem Equation32_implies_Equation23 (G : Type*) [Magma G] (h : Equation32 G) : Equation23 G := λ x => h x x
theorem Equation48_implies_Equation47 (G : Type*) [Magma G] (h : Equation48 G) : Equation47 G := λ x => h x x
theorem Equation49_implies_Equation47 (G : Type*) [Magma G] (h : Equation49 G) : Equation47 G := λ x => h x x
theorem Equation50_implies_Equation47 (G : Type*) [Magma G] (h : Equation50 G) : Equation47 G := λ x => h x x
theorem Equation52_implies_Equation47 (G : Type*) [Magma G] (h : Equation52 G) : Equation47 G := λ x => h x x
theorem Equation53_implies_Equation47 (G : Type*) [Magma G] (h : Equation53 G) : Equation47 G := λ x => h x x
theorem Equation55_implies_Equation47 (G : Type*) [Magma G] (h : Equation55 G) : Equation47 G := λ x => h x x
theorem Equation56_implies_Equation47 (G : Type*) [Magma G] (h : Equation56 G) : Equation47 G := λ x => h x x
theorem Equation62_implies_Equation47 (G : Type*) [Magma G] (h : Equation62 G) : Equation47 G := λ x => h x x
theorem Equation63_implies_Equation47 (G : Type*) [Magma G] (h : Equation63 G) : Equation47 G := λ x => h x x
theorem Equation65_implies_Equation47 (G : Type*) [Magma G] (h : Equation65 G) : Equation47 G := λ x => h x x
theorem Equation66_implies_Equation47 (G : Type*) [Magma G] (h : Equation66 G) : Equation47 G := λ x => h x x
theorem Equation72_implies_Equation47 (G : Type*) [Magma G] (h : Equation72 G) : Equation47 G := λ x => h x x
theorem Equation73_implies_Equation47 (G : Type*) [Magma G] (h : Equation73 G) : Equation47 G := λ x => h x x
theorem Equation75_implies_Equation47 (G : Type*) [Magma G] (h : Equation75 G) : Equation47 G := λ x => h x x
theorem Equation76_implies_Equation47 (G : Type*) [Magma G] (h : Equation76 G) : Equation47 G := λ x => h x x
theorem Equation100_implies_Equation99 (G : Type*) [Magma G] (h : Equation100 G) : Equation99 G := λ x => h x x
theorem Equation101_implies_Equation99 (G : Type*) [Magma G] (h : Equation101 G) : Equation99 G := λ x => h x x
theorem Equation102_implies_Equation99 (G : Type*) [Magma G] (h : Equation102 G) : Equation99 G := λ x => h x x
theorem Equation104_implies_Equation99 (G : Type*) [Magma G] (h : Equation104 G) : Equation99 G := λ x => h x x
theorem Equation105_implies_Equation99 (G : Type*) [Magma G] (h : Equation105 G) : Equation99 G := λ x => h x x
theorem Equation107_implies_Equation99 (G : Type*) [Magma G] (h : Equation107 G) : Equation99 G := λ x => h x x
theorem Equation108_implies_Equation99 (G : Type*) [Magma G] (h : Equation108 G) : Equation99 G := λ x => h x x
theorem Equation114_implies_Equation99 (G : Type*) [Magma G] (h : Equation114 G) : Equation99 G := λ x => h x x
theorem Equation115_implies_Equation99 (G : Type*) [Magma G] (h : Equation115 G) : Equation99 G := λ x => h x x
theorem Equation117_implies_Equation99 (G : Type*) [Magma G] (h : Equation117 G) : Equation99 G := λ x => h x x
theorem Equation118_implies_Equation99 (G : Type*) [Magma G] (h : Equation118 G) : Equation99 G := λ x => h x x
theorem Equation124_implies_Equation99 (G : Type*) [Magma G] (h : Equation124 G) : Equation99 G := λ x => h x x
theorem Equation125_implies_Equation99 (G : Type*) [Magma G] (h : Equation125 G) : Equation99 G := λ x => h x x
theorem Equation127_implies_Equation99 (G : Type*) [Magma G] (h : Equation127 G) : Equation99 G := λ x => h x x
theorem Equation128_implies_Equation99 (G : Type*) [Magma G] (h : Equation128 G) : Equation99 G := λ x => h x x
theorem Equation152_implies_Equation151 (G : Type*) [Magma G] (h : Equation152 G) : Equation151 G := λ x => h x x
theorem Equation153_implies_Equation151 (G : Type*) [Magma G] (h : Equation153 G) : Equation151 G := λ x => h x x
theorem Equation154_implies_Equation151 (G : Type*) [Magma G] (h : Equation154 G) : Equation151 G := λ x => h x x
theorem Equation156_implies_Equation151 (G : Type*) [Magma G] (h : Equation156 G) : Equation151 G := λ x => h x x
theorem Equation157_implies_Equation151 (G : Type*) [Magma G] (h : Equation157 G) : Equation151 G := λ x => h x x
theorem Equation159_implies_Equation151 (G : Type*) [Magma G] (h : Equation159 G) : Equation151 G := λ x => h x x
theorem Equation160_implies_Equation151 (G : Type*) [Magma G] (h : Equation160 G) : Equation151 G := λ x => h x x
theorem Equation166_implies_Equation151 (G : Type*) [Magma G] (h : Equation166 G) : Equation151 G := λ x => h x x
theorem Equation167_implies_Equation151 (G : Type*) [Magma G] (h : Equation167 G) : Equation151 G := λ x => h x x
theorem Equation169_implies_Equation151 (G : Type*) [Magma G] (h : Equation169 G) : Equation151 G := λ x => h x x
theorem Equation170_implies_Equation151 (G : Type*) [Magma G] (h : Equation170 G) : Equation151 G := λ x => h x x
theorem Equation176_implies_Equation151 (G : Type*) [Magma G] (h : Equation176 G) : Equation151 G := λ x => h x x
theorem Equation177_implies_Equation151 (G : Type*) [Magma G] (h : Equation177 G) : Equation151 G := λ x => h x x
theorem Equation179_implies_Equation151 (G : Type*) [Magma G] (h : Equation179 G) : Equation151 G := λ x => h x x
theorem Equation180_implies_Equation151 (G : Type*) [Magma G] (h : Equation180 G) : Equation151 G := λ x => h x x
theorem Equation204_implies_Equation203 (G : Type*) [Magma G] (h : Equation204 G) : Equation203 G := λ x => h x x
theorem Equation205_implies_Equation203 (G : Type*) [Magma G] (h : Equation205 G) : Equation203 G := λ x => h x x
theorem Equation206_implies_Equation203 (G : Type*) [Magma G] (h : Equation206 G) : Equation203 G := λ x => h x x
theorem Equation208_implies_Equation203 (G : Type*) [Magma G] (h : Equation208 G) : Equation203 G := λ x => h x x
theorem Equation209_implies_Equation203 (G : Type*) [Magma G] (h : Equation209 G) : Equation203 G := λ x => h x x
theorem Equation211_implies_Equation203 (G : Type*) [Magma G] (h : Equation211 G) : Equation203 G := λ x => h x x
theorem Equation212_implies_Equation203 (G : Type*) [Magma G] (h : Equation212 G) : Equation203 G := λ x => h x x
theorem Equation218_implies_Equation203 (G : Type*) [Magma G] (h : Equation218 G) : Equation203 G := λ x => h x x
theorem Equation219_implies_Equation203 (G : Type*) [Magma G] (h : Equation219 G) : Equation203 G := λ x => h x x
theorem Equation221_implies_Equation203 (G : Type*) [Magma G] (h : Equation221 G) : Equation203 G := λ x => h x x
theorem Equation222_implies_Equation203 (G : Type*) [Magma G] (h : Equation222 G) : Equation203 G := λ x => h x x
theorem Equation228_implies_Equation203 (G : Type*) [Magma G] (h : Equation228 G) : Equation203 G := λ x => h x x
theorem Equation229_implies_Equation203 (G : Type*) [Magma G] (h : Equation229 G) : Equation203 G := λ x => h x x
theorem Equation231_implies_Equation203 (G : Type*) [Magma G] (h : Equation231 G) : Equation203 G := λ x => h x x
theorem Equation232_implies_Equation203 (G : Type*) [Magma G] (h : Equation232 G) : Equation203 G := λ x => h x x
theorem Equation256_implies_Equation255 (G : Type*) [Magma G] (h : Equation256 G) : Equation255 G := λ x => h x x
theorem Equation257_implies_Equation255 (G : Type*) [Magma G] (h : Equation257 G) : Equation255 G := λ x => h x x
theorem Equation258_implies_Equation255 (G : Type*) [Magma G] (h : Equation258 G) : Equation255 G := λ x => h x x
theorem Equation260_implies_Equation255 (G : Type*) [Magma G] (h : Equation260 G) : Equation255 G := λ x => h x x
theorem Equation261_implies_Equation255 (G : Type*) [Magma G] (h : Equation261 G) : Equation255 G := λ x => h x x
theorem Equation263_implies_Equation255 (G : Type*) [Magma G] (h : Equation263 G) : Equation255 G := λ x => h x x
theorem Equation264_implies_Equation255 (G : Type*) [Magma G] (h : Equation264 G) : Equation255 G := λ x => h x x
theorem Equation270_implies_Equation255 (G : Type*) [Magma G] (h : Equation270 G) : Equation255 G := λ x => h x x
theorem Equation271_implies_Equation255 (G : Type*) [Magma G] (h : Equation271 G) : Equation255 G := λ x => h x x
theorem Equation273_implies_Equation255 (G : Type*) [Magma G] (h : Equation273 G) : Equation255 G := λ x => h x x
theorem Equation274_implies_Equation255 (G : Type*) [Magma G] (h : Equation274 G) : Equation255 G := λ x => h x x
theorem Equation280_implies_Equation255 (G : Type*) [Magma G] (h : Equation280 G) : Equation255 G := λ x => h x x
theorem Equation281_implies_Equation255 (G : Type*) [Magma G] (h : Equation281 G) : Equation255 G := λ x => h x x
theorem Equation283_implies_Equation255 (G : Type*) [Magma G] (h : Equation283 G) : Equation255 G := λ x => h x x
theorem Equation284_implies_Equation255 (G : Type*) [Magma G] (h : Equation284 G) : Equation255 G := λ x => h x x
theorem Equation308_implies_Equation307 (G : Type*) [Magma G] (h : Equation308 G) : Equation307 G := λ x => h x x
theorem Equation309_implies_Equation307 (G : Type*) [Magma G] (h : Equation309 G) : Equation307 G := λ x => h x x
theorem Equation310_implies_Equation307 (G : Type*) [Magma G] (h : Equation310 G) : Equation307 G := λ x => h x x
theorem Equation312_implies_Equation307 (G : Type*) [Magma G] (h : Equation312 G) : Equation307 G := λ x => h x x
theorem Equation313_implies_Equation307 (G : Type*) [Magma G] (h : Equation313 G) : Equation307 G := λ x => h x x
theorem Equation315_implies_Equation307 (G : Type*) [Magma G] (h : Equation315 G) : Equation307 G := λ x => h x x
theorem Equation316_implies_Equation307 (G : Type*) [Magma G] (h : Equation316 G) : Equation307 G := λ x => h x x
theorem Equation322_implies_Equation307 (G : Type*) [Magma G] (h : Equation322 G) : Equation307 G := λ x => h x x
theorem Equation323_implies_Equation307 (G : Type*) [Magma G] (h : Equation323 G) : Equation307 G := λ x => h x x
theorem Equation325_implies_Equation307 (G : Type*) [Magma G] (h : Equation325 G) : Equation307 G := λ x => h x x
theorem Equation326_implies_Equation307 (G : Type*) [Magma G] (h : Equation326 G) : Equation307 G := λ x => h x x
theorem Equation332_implies_Equation307 (G : Type*) [Magma G] (h : Equation332 G) : Equation307 G := λ x => h x x
theorem Equation333_implies_Equation307 (G : Type*) [Magma G] (h : Equation333 G) : Equation307 G := λ x => h x x
theorem Equation335_implies_Equation307 (G : Type*) [Magma G] (h : Equation335 G) : Equation307 G := λ x => h x x
theorem Equation336_implies_Equation307 (G : Type*) [Magma G] (h : Equation336 G) : Equation307 G := λ x => h x x
theorem Equation360_implies_Equation359 (G : Type*) [Magma G] (h : Equation360 G) : Equation359 G := λ x => h x x
theorem Equation361_implies_Equation359 (G : Type*) [Magma G] (h : Equation361 G) : Equation359 G := λ x => h x x
theorem Equation362_implies_Equation359 (G : Type*) [Magma G] (h : Equation362 G) : Equation359 G := λ x => h x x
theorem Equation364_implies_Equation359 (G : Type*) [Magma G] (h : Equation364 G) : Equation359 G := λ x => h x x
theorem Equation365_implies_Equation359 (G : Type*) [Magma G] (h : Equation365 G) : Equation359 G := λ x => h x x
theorem Equation367_implies_Equation359 (G : Type*) [Magma G] (h : Equation367 G) : Equation359 G := λ x => h x x
theorem Equation368_implies_Equation359 (G : Type*) [Magma G] (h : Equation368 G) : Equation359 G := λ x => h x x
theorem Equation374_implies_Equation359 (G : Type*) [Magma G] (h : Equation374 G) : Equation359 G := λ x => h x x
theorem Equation375_implies_Equation359 (G : Type*) [Magma G] (h : Equation375 G) : Equation359 G := λ x => h x x
theorem Equation377_implies_Equation359 (G : Type*) [Magma G] (h : Equation377 G) : Equation359 G := λ x => h x x
theorem Equation378_implies_Equation359 (G : Type*) [Magma G] (h : Equation378 G) : Equation359 G := λ x => h x x
theorem Equation384_implies_Equation359 (G : Type*) [Magma G] (h : Equation384 G) : Equation359 G := λ x => h x x
theorem Equation385_implies_Equation359 (G : Type*) [Magma G] (h : Equation385 G) : Equation359 G := λ x => h x x
theorem Equation387_implies_Equation359 (G : Type*) [Magma G] (h : Equation387 G) : Equation359 G := λ x => h x x
theorem Equation388_implies_Equation359 (G : Type*) [Magma G] (h : Equation388 G) : Equation359 G := λ x => h x x
theorem Equation412_implies_Equation411 (G : Type*) [Magma G] (h : Equation412 G) : Equation411 G := λ x => h x x
theorem Equation413_implies_Equation411 (G : Type*) [Magma G] (h : Equation413 G) : Equation411 G := λ x => h x x
theorem Equation414_implies_Equation411 (G : Type*) [Magma G] (h : Equation414 G) : Equation411 G := λ x => h x x
theorem Equation416_implies_Equation411 (G : Type*) [Magma G] (h : Equation416 G) : Equation411 G := λ x => h x x
theorem Equation417_implies_Equation411 (G : Type*) [Magma G] (h : Equation417 G) : Equation411 G := λ x => h x x
theorem Equation419_implies_Equation411 (G : Type*) [Magma G] (h : Equation419 G) : Equation411 G := λ x => h x x
theorem Equation420_implies_Equation411 (G : Type*) [Magma G] (h : Equation420 G) : Equation411 G := λ x => h x x
theorem Equation426_implies_Equation411 (G : Type*) [Magma G] (h : Equation426 G) : Equation411 G := λ x => h x x
theorem Equation427_implies_Equation411 (G : Type*) [Magma G] (h : Equation427 G) : Equation411 G := λ x => h x x
theorem Equation429_implies_Equation411 (G : Type*) [Magma G] (h : Equation429 G) : Equation411 G := λ x => h x x
theorem Equation430_implies_Equation411 (G : Type*) [Magma G] (h : Equation430 G) : Equation411 G := λ x => h x x
theorem Equation436_implies_Equation411 (G : Type*) [Magma G] (h : Equation436 G) : Equation411 G := λ x => h x x
theorem Equation437_implies_Equation411 (G : Type*) [Magma G] (h : Equation437 G) : Equation411 G := λ x => h x x
theorem Equation439_implies_Equation411 (G : Type*) [Magma G] (h : Equation439 G) : Equation411 G := λ x => h x x
theorem Equation440_implies_Equation411 (G : Type*) [Magma G] (h : Equation440 G) : Equation411 G := λ x => h x x
theorem Equation463_implies_Equation411 (G : Type*) [Magma G] (h : Equation463 G) : Equation411 G := λ x => h x x
theorem Equation464_implies_Equation411 (G : Type*) [Magma G] (h : Equation464 G) : Equation411 G := λ x => h x x
theorem Equation466_implies_Equation411 (G : Type*) [Magma G] (h : Equation466 G) : Equation411 G := λ x => h x x
theorem Equation467_implies_Equation411 (G : Type*) [Magma G] (h : Equation467 G) : Equation411 G := λ x => h x x
theorem Equation473_implies_Equation411 (G : Type*) [Magma G] (h : Equation473 G) : Equation411 G := λ x => h x x
theorem Equation474_implies_Equation411 (G : Type*) [Magma G] (h : Equation474 G) : Equation411 G := λ x => h x x
theorem Equation476_implies_Equation411 (G : Type*) [Magma G] (h : Equation476 G) : Equation411 G := λ x => h x x
theorem Equation477_implies_Equation411 (G : Type*) [Magma G] (h : Equation477 G) : Equation411 G := λ x => h x x
theorem Equation500_implies_Equation411 (G : Type*) [Magma G] (h : Equation500 G) : Equation411 G := λ x => h x x
theorem Equation501_implies_Equation411 (G : Type*) [Magma G] (h : Equation501 G) : Equation411 G := λ x => h x x
theorem Equation503_implies_Equation411 (G : Type*) [Magma G] (h : Equation503 G) : Equation411 G := λ x => h x x
theorem Equation504_implies_Equation411 (G : Type*) [Magma G] (h : Equation504 G) : Equation411 G := λ x => h x x
theorem Equation510_implies_Equation411 (G : Type*) [Magma G] (h : Equation510 G) : Equation411 G := λ x => h x x
theorem Equation511_implies_Equation411 (G : Type*) [Magma G] (h : Equation511 G) : Equation411 G := λ x => h x x
theorem Equation513_implies_Equation411 (G : Type*) [Magma G] (h : Equation513 G) : Equation411 G := λ x => h x x
theorem Equation514_implies_Equation411 (G : Type*) [Magma G] (h : Equation514 G) : Equation411 G := λ x => h x x
theorem Equation615_implies_Equation614 (G : Type*) [Magma G] (h : Equation615 G) : Equation614 G := λ x => h x x
theorem Equation616_implies_Equation614 (G : Type*) [Magma G] (h : Equation616 G) : Equation614 G := λ x => h x x
theorem Equation617_implies_Equation614 (G : Type*) [Magma G] (h : Equation617 G) : Equation614 G := λ x => h x x
theorem Equation619_implies_Equation614 (G : Type*) [Magma G] (h : Equation619 G) : Equation614 G := λ x => h x x
theorem Equation620_implies_Equation614 (G : Type*) [Magma G] (h : Equation620 G) : Equation614 G := λ x => h x x
theorem Equation622_implies_Equation614 (G : Type*) [Magma G] (h : Equation622 G) : Equation614 G := λ x => h x x
theorem Equation623_implies_Equation614 (G : Type*) [Magma G] (h : Equation623 G) : Equation614 G := λ x => h x x
theorem Equation629_implies_Equation614 (G : Type*) [Magma G] (h : Equation629 G) : Equation614 G := λ x => h x x
theorem Equation630_implies_Equation614 (G : Type*) [Magma G] (h : Equation630 G) : Equation614 G := λ x => h x x
theorem Equation632_implies_Equation614 (G : Type*) [Magma G] (h : Equation632 G) : Equation614 G := λ x => h x x
theorem Equation633_implies_Equation614 (G : Type*) [Magma G] (h : Equation633 G) : Equation614 G := λ x => h x x
theorem Equation639_implies_Equation614 (G : Type*) [Magma G] (h : Equation639 G) : Equation614 G := λ x => h x x
theorem Equation640_implies_Equation614 (G : Type*) [Magma G] (h : Equation640 G) : Equation614 G := λ x => h x x
theorem Equation642_implies_Equation614 (G : Type*) [Magma G] (h : Equation642 G) : Equation614 G := λ x => h x x
theorem Equation643_implies_Equation614 (G : Type*) [Magma G] (h : Equation643 G) : Equation614 G := λ x => h x x
theorem Equation666_implies_Equation614 (G : Type*) [Magma G] (h : Equation666 G) : Equation614 G := λ x => h x x
theorem Equation667_implies_Equation614 (G : Type*) [Magma G] (h : Equation667 G) : Equation614 G := λ x => h x x
theorem Equation669_implies_Equation614 (G : Type*) [Magma G] (h : Equation669 G) : Equation614 G := λ x => h x x
theorem Equation670_implies_Equation614 (G : Type*) [Magma G] (h : Equation670 G) : Equation614 G := λ x => h x x
theorem Equation676_implies_Equation614 (G : Type*) [Magma G] (h : Equation676 G) : Equation614 G := λ x => h x x
theorem Equation677_implies_Equation614 (G : Type*) [Magma G] (h : Equation677 G) : Equation614 G := λ x => h x x
theorem Equation679_implies_Equation614 (G : Type*) [Magma G] (h : Equation679 G) : Equation614 G := λ x => h x x
theorem Equation680_implies_Equation614 (G : Type*) [Magma G] (h : Equation680 G) : Equation614 G := λ x => h x x
theorem Equation703_implies_Equation614 (G : Type*) [Magma G] (h : Equation703 G) : Equation614 G := λ x => h x x
theorem Equation704_implies_Equation614 (G : Type*) [Magma G] (h : Equation704 G) : Equation614 G := λ x => h x x
theorem Equation706_implies_Equation614 (G : Type*) [Magma G] (h : Equation706 G) : Equation614 G := λ x => h x x
theorem Equation707_implies_Equation614 (G : Type*) [Magma G] (h : Equation707 G) : Equation614 G := λ x => h x x
theorem Equation713_implies_Equation614 (G : Type*) [Magma G] (h : Equation713 G) : Equation614 G := λ x => h x x
theorem Equation714_implies_Equation614 (G : Type*) [Magma G] (h : Equation714 G) : Equation614 G := λ x => h x x
theorem Equation716_implies_Equation614 (G : Type*) [Magma G] (h : Equation716 G) : Equation614 G := λ x => h x x
theorem Equation717_implies_Equation614 (G : Type*) [Magma G] (h : Equation717 G) : Equation614 G := λ x => h x x
theorem Equation818_implies_Equation817 (G : Type*) [Magma G] (h : Equation818 G) : Equation817 G := λ x => h x x
theorem Equation819_implies_Equation817 (G : Type*) [Magma G] (h : Equation819 G) : Equation817 G := λ x => h x x
theorem Equation820_implies_Equation817 (G : Type*) [Magma G] (h : Equation820 G) : Equation817 G := λ x => h x x
theorem Equation822_implies_Equation817 (G : Type*) [Magma G] (h : Equation822 G) : Equation817 G := λ x => h x x
theorem Equation823_implies_Equation817 (G : Type*) [Magma G] (h : Equation823 G) : Equation817 G := λ x => h x x
theorem Equation825_implies_Equation817 (G : Type*) [Magma G] (h : Equation825 G) : Equation817 G := λ x => h x x
theorem Equation826_implies_Equation817 (G : Type*) [Magma G] (h : Equation826 G) : Equation817 G := λ x => h x x
theorem Equation832_implies_Equation817 (G : Type*) [Magma G] (h : Equation832 G) : Equation817 G := λ x => h x x
theorem Equation833_implies_Equation817 (G : Type*) [Magma G] (h : Equation833 G) : Equation817 G := λ x => h x x
theorem Equation835_implies_Equation817 (G : Type*) [Magma G] (h : Equation835 G) : Equation817 G := λ x => h x x
theorem Equation836_implies_Equation817 (G : Type*) [Magma G] (h : Equation836 G) : Equation817 G := λ x => h x x
theorem Equation842_implies_Equation817 (G : Type*) [Magma G] (h : Equation842 G) : Equation817 G := λ x => h x x
theorem Equation843_implies_Equation817 (G : Type*) [Magma G] (h : Equation843 G) : Equation817 G := λ x => h x x
theorem Equation845_implies_Equation817 (G : Type*) [Magma G] (h : Equation845 G) : Equation817 G := λ x => h x x
theorem Equation846_implies_Equation817 (G : Type*) [Magma G] (h : Equation846 G) : Equation817 G := λ x => h x x
theorem Equation869_implies_Equation817 (G : Type*) [Magma G] (h : Equation869 G) : Equation817 G := λ x => h x x
theorem Equation870_implies_Equation817 (G : Type*) [Magma G] (h : Equation870 G) : Equation817 G := λ x => h x x
theorem Equation872_implies_Equation817 (G : Type*) [Magma G] (h : Equation872 G) : Equation817 G := λ x => h x x
theorem Equation873_implies_Equation817 (G : Type*) [Magma G] (h : Equation873 G) : Equation817 G := λ x => h x x
theorem Equation879_implies_Equation817 (G : Type*) [Magma G] (h : Equation879 G) : Equation817 G := λ x => h x x
theorem Equation880_implies_Equation817 (G : Type*) [Magma G] (h : Equation880 G) : Equation817 G := λ x => h x x
theorem Equation882_implies_Equation817 (G : Type*) [Magma G] (h : Equation882 G) : Equation817 G := λ x => h x x
theorem Equation883_implies_Equation817 (G : Type*) [Magma G] (h : Equation883 G) : Equation817 G := λ x => h x x
theorem Equation906_implies_Equation817 (G : Type*) [Magma G] (h : Equation906 G) : Equation817 G := λ x => h x x
theorem Equation907_implies_Equation817 (G : Type*) [Magma G] (h : Equation907 G) : Equation817 G := λ x => h x x
theorem Equation909_implies_Equation817 (G : Type*) [Magma G] (h : Equation909 G) : Equation817 G := λ x => h x x
theorem Equation910_implies_Equation817 (G : Type*) [Magma G] (h : Equation910 G) : Equation817 G := λ x => h x x
theorem Equation916_implies_Equation817 (G : Type*) [Magma G] (h : Equation916 G) : Equation817 G := λ x => h x x
theorem Equation917_implies_Equation817 (G : Type*) [Magma G] (h : Equation917 G) : Equation817 G := λ x => h x x
theorem Equation919_implies_Equation817 (G : Type*) [Magma G] (h : Equation919 G) : Equation817 G := λ x => h x x
theorem Equation920_implies_Equation817 (G : Type*) [Magma G] (h : Equation920 G) : Equation817 G := λ x => h x x
theorem Equation1021_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1021 G) : Equation1020 G := λ x => h x x
theorem Equation1022_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1022 G) : Equation1020 G := λ x => h x x
theorem Equation1023_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1023 G) : Equation1020 G := λ x => h x x
theorem Equation1025_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1025 G) : Equation1020 G := λ x => h x x
theorem Equation1026_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1026 G) : Equation1020 G := λ x => h x x
theorem Equation1028_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1028 G) : Equation1020 G := λ x => h x x
theorem Equation1029_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1029 G) : Equation1020 G := λ x => h x x
theorem Equation1035_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1035 G) : Equation1020 G := λ x => h x x
theorem Equation1036_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1036 G) : Equation1020 G := λ x => h x x
theorem Equation1038_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1038 G) : Equation1020 G := λ x => h x x
theorem Equation1039_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1039 G) : Equation1020 G := λ x => h x x
theorem Equation1045_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1045 G) : Equation1020 G := λ x => h x x
theorem Equation1046_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1046 G) : Equation1020 G := λ x => h x x
theorem Equation1048_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1048 G) : Equation1020 G := λ x => h x x
theorem Equation1049_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1049 G) : Equation1020 G := λ x => h x x
theorem Equation1072_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1072 G) : Equation1020 G := λ x => h x x
theorem Equation1073_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1073 G) : Equation1020 G := λ x => h x x
theorem Equation1075_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1075 G) : Equation1020 G := λ x => h x x
theorem Equation1076_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1076 G) : Equation1020 G := λ x => h x x
theorem Equation1082_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1082 G) : Equation1020 G := λ x => h x x
theorem Equation1083_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1083 G) : Equation1020 G := λ x => h x x
theorem Equation1085_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1085 G) : Equation1020 G := λ x => h x x
theorem Equation1086_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1086 G) : Equation1020 G := λ x => h x x
theorem Equation1109_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1109 G) : Equation1020 G := λ x => h x x
theorem Equation1110_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1110 G) : Equation1020 G := λ x => h x x
theorem Equation1112_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1112 G) : Equation1020 G := λ x => h x x
theorem Equation1113_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1113 G) : Equation1020 G := λ x => h x x
theorem Equation1119_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1119 G) : Equation1020 G := λ x => h x x
theorem Equation1120_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1120 G) : Equation1020 G := λ x => h x x
theorem Equation1122_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1122 G) : Equation1020 G := λ x => h x x
theorem Equation1123_implies_Equation1020 (G : Type*) [Magma G] (h : Equation1123 G) : Equation1020 G := λ x => h x x
theorem Equation1224_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1224 G) : Equation1223 G := λ x => h x x
theorem Equation1225_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1225 G) : Equation1223 G := λ x => h x x
theorem Equation1226_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1226 G) : Equation1223 G := λ x => h x x
theorem Equation1228_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1228 G) : Equation1223 G := λ x => h x x
theorem Equation1229_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1229 G) : Equation1223 G := λ x => h x x
theorem Equation1231_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1231 G) : Equation1223 G := λ x => h x x
theorem Equation1232_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1232 G) : Equation1223 G := λ x => h x x
theorem Equation1238_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1238 G) : Equation1223 G := λ x => h x x
theorem Equation1239_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1239 G) : Equation1223 G := λ x => h x x
theorem Equation1241_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1241 G) : Equation1223 G := λ x => h x x
theorem Equation1242_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1242 G) : Equation1223 G := λ x => h x x
theorem Equation1248_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1248 G) : Equation1223 G := λ x => h x x
theorem Equation1249_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1249 G) : Equation1223 G := λ x => h x x
theorem Equation1251_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1251 G) : Equation1223 G := λ x => h x x
theorem Equation1252_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1252 G) : Equation1223 G := λ x => h x x
theorem Equation1275_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1275 G) : Equation1223 G := λ x => h x x
theorem Equation1276_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1276 G) : Equation1223 G := λ x => h x x
theorem Equation1278_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1278 G) : Equation1223 G := λ x => h x x
theorem Equation1279_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1279 G) : Equation1223 G := λ x => h x x
theorem Equation1285_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1285 G) : Equation1223 G := λ x => h x x
theorem Equation1286_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1286 G) : Equation1223 G := λ x => h x x
theorem Equation1288_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1288 G) : Equation1223 G := λ x => h x x
theorem Equation1289_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1289 G) : Equation1223 G := λ x => h x x
theorem Equation1312_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1312 G) : Equation1223 G := λ x => h x x
theorem Equation1313_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1313 G) : Equation1223 G := λ x => h x x
theorem Equation1315_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1315 G) : Equation1223 G := λ x => h x x
theorem Equation1316_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1316 G) : Equation1223 G := λ x => h x x
theorem Equation1322_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1322 G) : Equation1223 G := λ x => h x x
theorem Equation1323_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1323 G) : Equation1223 G := λ x => h x x
theorem Equation1325_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1325 G) : Equation1223 G := λ x => h x x
theorem Equation1326_implies_Equation1223 (G : Type*) [Magma G] (h : Equation1326 G) : Equation1223 G := λ x => h x x
theorem Equation1427_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1427 G) : Equation1426 G := λ x => h x x
theorem Equation1428_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1428 G) : Equation1426 G := λ x => h x x
theorem Equation1429_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1429 G) : Equation1426 G := λ x => h x x
theorem Equation1431_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1431 G) : Equation1426 G := λ x => h x x
theorem Equation1432_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1432 G) : Equation1426 G := λ x => h x x
theorem Equation1434_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1434 G) : Equation1426 G := λ x => h x x
theorem Equation1435_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1435 G) : Equation1426 G := λ x => h x x
theorem Equation1441_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1441 G) : Equation1426 G := λ x => h x x
theorem Equation1442_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1442 G) : Equation1426 G := λ x => h x x
theorem Equation1444_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1444 G) : Equation1426 G := λ x => h x x
theorem Equation1445_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1445 G) : Equation1426 G := λ x => h x x
theorem Equation1451_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1451 G) : Equation1426 G := λ x => h x x
theorem Equation1452_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1452 G) : Equation1426 G := λ x => h x x
theorem Equation1454_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1454 G) : Equation1426 G := λ x => h x x
theorem Equation1455_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1455 G) : Equation1426 G := λ x => h x x
theorem Equation1478_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1478 G) : Equation1426 G := λ x => h x x
theorem Equation1479_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1479 G) : Equation1426 G := λ x => h x x
theorem Equation1481_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1481 G) : Equation1426 G := λ x => h x x
theorem Equation1482_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1482 G) : Equation1426 G := λ x => h x x
theorem Equation1488_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1488 G) : Equation1426 G := λ x => h x x
theorem Equation1489_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1489 G) : Equation1426 G := λ x => h x x
theorem Equation1491_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1491 G) : Equation1426 G := λ x => h x x
theorem Equation1492_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1492 G) : Equation1426 G := λ x => h x x
theorem Equation1515_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1515 G) : Equation1426 G := λ x => h x x
theorem Equation1516_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1516 G) : Equation1426 G := λ x => h x x
theorem Equation1518_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1518 G) : Equation1426 G := λ x => h x x
theorem Equation1519_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1519 G) : Equation1426 G := λ x => h x x
theorem Equation1525_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1525 G) : Equation1426 G := λ x => h x x
theorem Equation1526_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1526 G) : Equation1426 G := λ x => h x x
theorem Equation1528_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1528 G) : Equation1426 G := λ x => h x x
theorem Equation1529_implies_Equation1426 (G : Type*) [Magma G] (h : Equation1529 G) : Equation1426 G := λ x => h x x
theorem Equation1630_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1630 G) : Equation1629 G := λ x => h x x
theorem Equation1631_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1631 G) : Equation1629 G := λ x => h x x
theorem Equation1632_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1632 G) : Equation1629 G := λ x => h x x
theorem Equation1634_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1634 G) : Equation1629 G := λ x => h x x
theorem Equation1635_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1635 G) : Equation1629 G := λ x => h x x
theorem Equation1637_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1637 G) : Equation1629 G := λ x => h x x
theorem Equation1638_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1638 G) : Equation1629 G := λ x => h x x
theorem Equation1644_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1644 G) : Equation1629 G := λ x => h x x
theorem Equation1645_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1645 G) : Equation1629 G := λ x => h x x
theorem Equation1647_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1647 G) : Equation1629 G := λ x => h x x
theorem Equation1648_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1648 G) : Equation1629 G := λ x => h x x
theorem Equation1654_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1654 G) : Equation1629 G := λ x => h x x
theorem Equation1655_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1655 G) : Equation1629 G := λ x => h x x
theorem Equation1657_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1657 G) : Equation1629 G := λ x => h x x
theorem Equation1658_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1658 G) : Equation1629 G := λ x => h x x
theorem Equation1681_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1681 G) : Equation1629 G := λ x => h x x
theorem Equation1682_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1682 G) : Equation1629 G := λ x => h x x
theorem Equation1684_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1684 G) : Equation1629 G := λ x => h x x
theorem Equation1685_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1685 G) : Equation1629 G := λ x => h x x
theorem Equation1691_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1691 G) : Equation1629 G := λ x => h x x
theorem Equation1692_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1692 G) : Equation1629 G := λ x => h x x
theorem Equation1694_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1694 G) : Equation1629 G := λ x => h x x
theorem Equation1695_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1695 G) : Equation1629 G := λ x => h x x
theorem Equation1718_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1718 G) : Equation1629 G := λ x => h x x
theorem Equation1719_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1719 G) : Equation1629 G := λ x => h x x
theorem Equation1721_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1721 G) : Equation1629 G := λ x => h x x
theorem Equation1722_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1722 G) : Equation1629 G := λ x => h x x
theorem Equation1728_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1728 G) : Equation1629 G := λ x => h x x
theorem Equation1729_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1729 G) : Equation1629 G := λ x => h x x
theorem Equation1731_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1731 G) : Equation1629 G := λ x => h x x
theorem Equation1732_implies_Equation1629 (G : Type*) [Magma G] (h : Equation1732 G) : Equation1629 G := λ x => h x x
theorem Equation1833_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1833 G) : Equation1832 G := λ x => h x x
theorem Equation1834_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1834 G) : Equation1832 G := λ x => h x x
theorem Equation1835_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1835 G) : Equation1832 G := λ x => h x x
theorem Equation1837_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1837 G) : Equation1832 G := λ x => h x x
theorem Equation1838_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1838 G) : Equation1832 G := λ x => h x x
theorem Equation1840_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1840 G) : Equation1832 G := λ x => h x x
theorem Equation1841_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1841 G) : Equation1832 G := λ x => h x x
theorem Equation1847_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1847 G) : Equation1832 G := λ x => h x x
theorem Equation1848_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1848 G) : Equation1832 G := λ x => h x x
theorem Equation1850_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1850 G) : Equation1832 G := λ x => h x x
theorem Equation1851_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1851 G) : Equation1832 G := λ x => h x x
theorem Equation1857_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1857 G) : Equation1832 G := λ x => h x x
theorem Equation1858_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1858 G) : Equation1832 G := λ x => h x x
theorem Equation1860_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1860 G) : Equation1832 G := λ x => h x x
theorem Equation1861_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1861 G) : Equation1832 G := λ x => h x x
theorem Equation1884_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1884 G) : Equation1832 G := λ x => h x x
theorem Equation1885_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1885 G) : Equation1832 G := λ x => h x x
theorem Equation1887_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1887 G) : Equation1832 G := λ x => h x x
theorem Equation1888_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1888 G) : Equation1832 G := λ x => h x x
theorem Equation1894_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1894 G) : Equation1832 G := λ x => h x x
theorem Equation1895_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1895 G) : Equation1832 G := λ x => h x x
theorem Equation1897_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1897 G) : Equation1832 G := λ x => h x x
theorem Equation1898_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1898 G) : Equation1832 G := λ x => h x x
theorem Equation1921_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1921 G) : Equation1832 G := λ x => h x x
theorem Equation1922_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1922 G) : Equation1832 G := λ x => h x x
theorem Equation1924_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1924 G) : Equation1832 G := λ x => h x x
theorem Equation1925_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1925 G) : Equation1832 G := λ x => h x x
theorem Equation1931_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1931 G) : Equation1832 G := λ x => h x x
theorem Equation1932_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1932 G) : Equation1832 G := λ x => h x x
theorem Equation1934_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1934 G) : Equation1832 G := λ x => h x x
theorem Equation1935_implies_Equation1832 (G : Type*) [Magma G] (h : Equation1935 G) : Equation1832 G := λ x => h x x
theorem Equation2036_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2036 G) : Equation2035 G := λ x => h x x
theorem Equation2037_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2037 G) : Equation2035 G := λ x => h x x
theorem Equation2038_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2038 G) : Equation2035 G := λ x => h x x
theorem Equation2040_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2040 G) : Equation2035 G := λ x => h x x
theorem Equation2041_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2041 G) : Equation2035 G := λ x => h x x
theorem Equation2043_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2043 G) : Equation2035 G := λ x => h x x
theorem Equation2044_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2044 G) : Equation2035 G := λ x => h x x
theorem Equation2050_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2050 G) : Equation2035 G := λ x => h x x
theorem Equation2051_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2051 G) : Equation2035 G := λ x => h x x
theorem Equation2053_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2053 G) : Equation2035 G := λ x => h x x
theorem Equation2054_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2054 G) : Equation2035 G := λ x => h x x
theorem Equation2060_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2060 G) : Equation2035 G := λ x => h x x
theorem Equation2061_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2061 G) : Equation2035 G := λ x => h x x
theorem Equation2063_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2063 G) : Equation2035 G := λ x => h x x
theorem Equation2064_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2064 G) : Equation2035 G := λ x => h x x
theorem Equation2087_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2087 G) : Equation2035 G := λ x => h x x
theorem Equation2088_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2088 G) : Equation2035 G := λ x => h x x
theorem Equation2090_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2090 G) : Equation2035 G := λ x => h x x
theorem Equation2091_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2091 G) : Equation2035 G := λ x => h x x
theorem Equation2097_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2097 G) : Equation2035 G := λ x => h x x
theorem Equation2098_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2098 G) : Equation2035 G := λ x => h x x
theorem Equation2100_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2100 G) : Equation2035 G := λ x => h x x
theorem Equation2101_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2101 G) : Equation2035 G := λ x => h x x
theorem Equation2124_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2124 G) : Equation2035 G := λ x => h x x
theorem Equation2125_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2125 G) : Equation2035 G := λ x => h x x
theorem Equation2127_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2127 G) : Equation2035 G := λ x => h x x
theorem Equation2128_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2128 G) : Equation2035 G := λ x => h x x
theorem Equation2134_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2134 G) : Equation2035 G := λ x => h x x
theorem Equation2135_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2135 G) : Equation2035 G := λ x => h x x
theorem Equation2137_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2137 G) : Equation2035 G := λ x => h x x
theorem Equation2138_implies_Equation2035 (G : Type*) [Magma G] (h : Equation2138 G) : Equation2035 G := λ x => h x x
theorem Equation2239_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2239 G) : Equation2238 G := λ x => h x x
theorem Equation2240_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2240 G) : Equation2238 G := λ x => h x x
theorem Equation2241_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2241 G) : Equation2238 G := λ x => h x x
theorem Equation2243_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2243 G) : Equation2238 G := λ x => h x x
theorem Equation2244_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2244 G) : Equation2238 G := λ x => h x x
theorem Equation2246_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2246 G) : Equation2238 G := λ x => h x x
theorem Equation2247_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2247 G) : Equation2238 G := λ x => h x x
theorem Equation2253_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2253 G) : Equation2238 G := λ x => h x x
theorem Equation2254_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2254 G) : Equation2238 G := λ x => h x x
theorem Equation2256_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2256 G) : Equation2238 G := λ x => h x x
theorem Equation2257_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2257 G) : Equation2238 G := λ x => h x x
theorem Equation2263_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2263 G) : Equation2238 G := λ x => h x x
theorem Equation2264_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2264 G) : Equation2238 G := λ x => h x x
theorem Equation2266_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2266 G) : Equation2238 G := λ x => h x x
theorem Equation2267_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2267 G) : Equation2238 G := λ x => h x x
theorem Equation2290_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2290 G) : Equation2238 G := λ x => h x x
theorem Equation2291_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2291 G) : Equation2238 G := λ x => h x x
theorem Equation2293_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2293 G) : Equation2238 G := λ x => h x x
theorem Equation2294_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2294 G) : Equation2238 G := λ x => h x x
theorem Equation2300_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2300 G) : Equation2238 G := λ x => h x x
theorem Equation2301_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2301 G) : Equation2238 G := λ x => h x x
theorem Equation2303_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2303 G) : Equation2238 G := λ x => h x x
theorem Equation2304_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2304 G) : Equation2238 G := λ x => h x x
theorem Equation2327_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2327 G) : Equation2238 G := λ x => h x x
theorem Equation2328_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2328 G) : Equation2238 G := λ x => h x x
theorem Equation2330_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2330 G) : Equation2238 G := λ x => h x x
theorem Equation2331_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2331 G) : Equation2238 G := λ x => h x x
theorem Equation2337_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2337 G) : Equation2238 G := λ x => h x x
theorem Equation2338_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2338 G) : Equation2238 G := λ x => h x x
theorem Equation2340_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2340 G) : Equation2238 G := λ x => h x x
theorem Equation2341_implies_Equation2238 (G : Type*) [Magma G] (h : Equation2341 G) : Equation2238 G := λ x => h x x
theorem Equation2442_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2442 G) : Equation2441 G := λ x => h x x
theorem Equation2443_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2443 G) : Equation2441 G := λ x => h x x
theorem Equation2444_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2444 G) : Equation2441 G := λ x => h x x
theorem Equation2446_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2446 G) : Equation2441 G := λ x => h x x
theorem Equation2447_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2447 G) : Equation2441 G := λ x => h x x
theorem Equation2449_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2449 G) : Equation2441 G := λ x => h x x
theorem Equation2450_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2450 G) : Equation2441 G := λ x => h x x
theorem Equation2456_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2456 G) : Equation2441 G := λ x => h x x
theorem Equation2457_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2457 G) : Equation2441 G := λ x => h x x
theorem Equation2459_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2459 G) : Equation2441 G := λ x => h x x
theorem Equation2460_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2460 G) : Equation2441 G := λ x => h x x
theorem Equation2466_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2466 G) : Equation2441 G := λ x => h x x
theorem Equation2467_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2467 G) : Equation2441 G := λ x => h x x
theorem Equation2469_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2469 G) : Equation2441 G := λ x => h x x
theorem Equation2470_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2470 G) : Equation2441 G := λ x => h x x
theorem Equation2493_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2493 G) : Equation2441 G := λ x => h x x
theorem Equation2494_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2494 G) : Equation2441 G := λ x => h x x
theorem Equation2496_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2496 G) : Equation2441 G := λ x => h x x
theorem Equation2497_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2497 G) : Equation2441 G := λ x => h x x
theorem Equation2503_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2503 G) : Equation2441 G := λ x => h x x
theorem Equation2504_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2504 G) : Equation2441 G := λ x => h x x
theorem Equation2506_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2506 G) : Equation2441 G := λ x => h x x
theorem Equation2507_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2507 G) : Equation2441 G := λ x => h x x
theorem Equation2530_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2530 G) : Equation2441 G := λ x => h x x
theorem Equation2531_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2531 G) : Equation2441 G := λ x => h x x
theorem Equation2533_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2533 G) : Equation2441 G := λ x => h x x
theorem Equation2534_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2534 G) : Equation2441 G := λ x => h x x
theorem Equation2540_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2540 G) : Equation2441 G := λ x => h x x
theorem Equation2541_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2541 G) : Equation2441 G := λ x => h x x
theorem Equation2543_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2543 G) : Equation2441 G := λ x => h x x
theorem Equation2544_implies_Equation2441 (G : Type*) [Magma G] (h : Equation2544 G) : Equation2441 G := λ x => h x x
theorem Equation2645_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2645 G) : Equation2644 G := λ x => h x x
theorem Equation2646_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2646 G) : Equation2644 G := λ x => h x x
theorem Equation2647_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2647 G) : Equation2644 G := λ x => h x x
theorem Equation2649_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2649 G) : Equation2644 G := λ x => h x x
theorem Equation2650_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2650 G) : Equation2644 G := λ x => h x x
theorem Equation2652_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2652 G) : Equation2644 G := λ x => h x x
theorem Equation2653_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2653 G) : Equation2644 G := λ x => h x x
theorem Equation2659_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2659 G) : Equation2644 G := λ x => h x x
theorem Equation2660_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2660 G) : Equation2644 G := λ x => h x x
theorem Equation2662_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2662 G) : Equation2644 G := λ x => h x x
theorem Equation2663_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2663 G) : Equation2644 G := λ x => h x x
theorem Equation2669_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2669 G) : Equation2644 G := λ x => h x x
theorem Equation2670_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2670 G) : Equation2644 G := λ x => h x x
theorem Equation2672_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2672 G) : Equation2644 G := λ x => h x x
theorem Equation2673_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2673 G) : Equation2644 G := λ x => h x x
theorem Equation2696_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2696 G) : Equation2644 G := λ x => h x x
theorem Equation2697_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2697 G) : Equation2644 G := λ x => h x x
theorem Equation2699_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2699 G) : Equation2644 G := λ x => h x x
theorem Equation2700_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2700 G) : Equation2644 G := λ x => h x x
theorem Equation2706_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2706 G) : Equation2644 G := λ x => h x x
theorem Equation2707_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2707 G) : Equation2644 G := λ x => h x x
theorem Equation2709_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2709 G) : Equation2644 G := λ x => h x x
theorem Equation2710_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2710 G) : Equation2644 G := λ x => h x x
theorem Equation2733_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2733 G) : Equation2644 G := λ x => h x x
theorem Equation2734_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2734 G) : Equation2644 G := λ x => h x x
theorem Equation2736_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2736 G) : Equation2644 G := λ x => h x x
theorem Equation2737_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2737 G) : Equation2644 G := λ x => h x x
theorem Equation2743_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2743 G) : Equation2644 G := λ x => h x x
theorem Equation2744_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2744 G) : Equation2644 G := λ x => h x x
theorem Equation2746_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2746 G) : Equation2644 G := λ x => h x x
theorem Equation2747_implies_Equation2644 (G : Type*) [Magma G] (h : Equation2747 G) : Equation2644 G := λ x => h x x
theorem Equation2848_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2848 G) : Equation2847 G := λ x => h x x
theorem Equation2849_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2849 G) : Equation2847 G := λ x => h x x
theorem Equation2850_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2850 G) : Equation2847 G := λ x => h x x
theorem Equation2852_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2852 G) : Equation2847 G := λ x => h x x
theorem Equation2853_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2853 G) : Equation2847 G := λ x => h x x
theorem Equation2855_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2855 G) : Equation2847 G := λ x => h x x
theorem Equation2856_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2856 G) : Equation2847 G := λ x => h x x
theorem Equation2862_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2862 G) : Equation2847 G := λ x => h x x
theorem Equation2863_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2863 G) : Equation2847 G := λ x => h x x
theorem Equation2865_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2865 G) : Equation2847 G := λ x => h x x
theorem Equation2866_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2866 G) : Equation2847 G := λ x => h x x
theorem Equation2872_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2872 G) : Equation2847 G := λ x => h x x
theorem Equation2873_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2873 G) : Equation2847 G := λ x => h x x
theorem Equation2875_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2875 G) : Equation2847 G := λ x => h x x
theorem Equation2876_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2876 G) : Equation2847 G := λ x => h x x
theorem Equation2899_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2899 G) : Equation2847 G := λ x => h x x
theorem Equation2900_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2900 G) : Equation2847 G := λ x => h x x
theorem Equation2902_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2902 G) : Equation2847 G := λ x => h x x
theorem Equation2903_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2903 G) : Equation2847 G := λ x => h x x
theorem Equation2909_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2909 G) : Equation2847 G := λ x => h x x
theorem Equation2910_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2910 G) : Equation2847 G := λ x => h x x
theorem Equation2912_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2912 G) : Equation2847 G := λ x => h x x
theorem Equation2913_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2913 G) : Equation2847 G := λ x => h x x
theorem Equation2936_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2936 G) : Equation2847 G := λ x => h x x
theorem Equation2937_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2937 G) : Equation2847 G := λ x => h x x
theorem Equation2939_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2939 G) : Equation2847 G := λ x => h x x
theorem Equation2940_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2940 G) : Equation2847 G := λ x => h x x
theorem Equation2946_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2946 G) : Equation2847 G := λ x => h x x
theorem Equation2947_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2947 G) : Equation2847 G := λ x => h x x
theorem Equation2949_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2949 G) : Equation2847 G := λ x => h x x
theorem Equation2950_implies_Equation2847 (G : Type*) [Magma G] (h : Equation2950 G) : Equation2847 G := λ x => h x x
theorem Equation3051_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3051 G) : Equation3050 G := λ x => h x x
theorem Equation3052_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3052 G) : Equation3050 G := λ x => h x x
theorem Equation3053_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3053 G) : Equation3050 G := λ x => h x x
theorem Equation3055_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3055 G) : Equation3050 G := λ x => h x x
theorem Equation3056_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3056 G) : Equation3050 G := λ x => h x x
theorem Equation3058_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3058 G) : Equation3050 G := λ x => h x x
theorem Equation3059_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3059 G) : Equation3050 G := λ x => h x x
theorem Equation3065_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3065 G) : Equation3050 G := λ x => h x x
theorem Equation3066_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3066 G) : Equation3050 G := λ x => h x x
theorem Equation3068_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3068 G) : Equation3050 G := λ x => h x x
theorem Equation3069_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3069 G) : Equation3050 G := λ x => h x x
theorem Equation3075_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3075 G) : Equation3050 G := λ x => h x x
theorem Equation3076_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3076 G) : Equation3050 G := λ x => h x x
theorem Equation3078_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3078 G) : Equation3050 G := λ x => h x x
theorem Equation3079_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3079 G) : Equation3050 G := λ x => h x x
theorem Equation3102_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3102 G) : Equation3050 G := λ x => h x x
theorem Equation3103_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3103 G) : Equation3050 G := λ x => h x x
theorem Equation3105_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3105 G) : Equation3050 G := λ x => h x x
theorem Equation3106_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3106 G) : Equation3050 G := λ x => h x x
theorem Equation3112_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3112 G) : Equation3050 G := λ x => h x x
theorem Equation3113_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3113 G) : Equation3050 G := λ x => h x x
theorem Equation3115_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3115 G) : Equation3050 G := λ x => h x x
theorem Equation3116_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3116 G) : Equation3050 G := λ x => h x x
theorem Equation3139_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3139 G) : Equation3050 G := λ x => h x x
theorem Equation3140_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3140 G) : Equation3050 G := λ x => h x x
theorem Equation3142_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3142 G) : Equation3050 G := λ x => h x x
theorem Equation3143_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3143 G) : Equation3050 G := λ x => h x x
theorem Equation3149_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3149 G) : Equation3050 G := λ x => h x x
theorem Equation3150_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3150 G) : Equation3050 G := λ x => h x x
theorem Equation3152_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3152 G) : Equation3050 G := λ x => h x x
theorem Equation3153_implies_Equation3050 (G : Type*) [Magma G] (h : Equation3153 G) : Equation3050 G := λ x => h x x
theorem Equation3254_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3254 G) : Equation3253 G := λ x => h x x
theorem Equation3255_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3255 G) : Equation3253 G := λ x => h x x
theorem Equation3256_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3256 G) : Equation3253 G := λ x => h x x
theorem Equation3258_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3258 G) : Equation3253 G := λ x => h x x
theorem Equation3259_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3259 G) : Equation3253 G := λ x => h x x
theorem Equation3261_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3261 G) : Equation3253 G := λ x => h x x
theorem Equation3262_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3262 G) : Equation3253 G := λ x => h x x
theorem Equation3268_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3268 G) : Equation3253 G := λ x => h x x
theorem Equation3269_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3269 G) : Equation3253 G := λ x => h x x
theorem Equation3271_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3271 G) : Equation3253 G := λ x => h x x
theorem Equation3272_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3272 G) : Equation3253 G := λ x => h x x
theorem Equation3278_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3278 G) : Equation3253 G := λ x => h x x
theorem Equation3279_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3279 G) : Equation3253 G := λ x => h x x
theorem Equation3281_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3281 G) : Equation3253 G := λ x => h x x
theorem Equation3282_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3282 G) : Equation3253 G := λ x => h x x
theorem Equation3305_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3305 G) : Equation3253 G := λ x => h x x
theorem Equation3306_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3306 G) : Equation3253 G := λ x => h x x
theorem Equation3308_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3308 G) : Equation3253 G := λ x => h x x
theorem Equation3309_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3309 G) : Equation3253 G := λ x => h x x
theorem Equation3315_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3315 G) : Equation3253 G := λ x => h x x
theorem Equation3316_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3316 G) : Equation3253 G := λ x => h x x
theorem Equation3318_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3318 G) : Equation3253 G := λ x => h x x
theorem Equation3319_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3319 G) : Equation3253 G := λ x => h x x
theorem Equation3342_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3342 G) : Equation3253 G := λ x => h x x
theorem Equation3343_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3343 G) : Equation3253 G := λ x => h x x
theorem Equation3345_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3345 G) : Equation3253 G := λ x => h x x
theorem Equation3346_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3346 G) : Equation3253 G := λ x => h x x
theorem Equation3352_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3352 G) : Equation3253 G := λ x => h x x
theorem Equation3353_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3353 G) : Equation3253 G := λ x => h x x
theorem Equation3355_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3355 G) : Equation3253 G := λ x => h x x
theorem Equation3356_implies_Equation3253 (G : Type*) [Magma G] (h : Equation3356 G) : Equation3253 G := λ x => h x x
theorem Equation3457_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3457 G) : Equation3456 G := λ x => h x x
theorem Equation3458_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3458 G) : Equation3456 G := λ x => h x x
theorem Equation3459_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3459 G) : Equation3456 G := λ x => h x x
theorem Equation3461_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3461 G) : Equation3456 G := λ x => h x x
theorem Equation3462_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3462 G) : Equation3456 G := λ x => h x x
theorem Equation3464_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3464 G) : Equation3456 G := λ x => h x x
theorem Equation3465_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3465 G) : Equation3456 G := λ x => h x x
theorem Equation3471_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3471 G) : Equation3456 G := λ x => h x x
theorem Equation3472_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3472 G) : Equation3456 G := λ x => h x x
theorem Equation3474_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3474 G) : Equation3456 G := λ x => h x x
theorem Equation3475_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3475 G) : Equation3456 G := λ x => h x x
theorem Equation3481_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3481 G) : Equation3456 G := λ x => h x x
theorem Equation3482_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3482 G) : Equation3456 G := λ x => h x x
theorem Equation3484_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3484 G) : Equation3456 G := λ x => h x x
theorem Equation3485_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3485 G) : Equation3456 G := λ x => h x x
theorem Equation3508_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3508 G) : Equation3456 G := λ x => h x x
theorem Equation3509_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3509 G) : Equation3456 G := λ x => h x x
theorem Equation3511_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3511 G) : Equation3456 G := λ x => h x x
theorem Equation3512_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3512 G) : Equation3456 G := λ x => h x x
theorem Equation3518_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3518 G) : Equation3456 G := λ x => h x x
theorem Equation3519_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3519 G) : Equation3456 G := λ x => h x x
theorem Equation3521_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3521 G) : Equation3456 G := λ x => h x x
theorem Equation3522_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3522 G) : Equation3456 G := λ x => h x x
theorem Equation3545_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3545 G) : Equation3456 G := λ x => h x x
theorem Equation3546_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3546 G) : Equation3456 G := λ x => h x x
theorem Equation3548_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3548 G) : Equation3456 G := λ x => h x x
theorem Equation3549_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3549 G) : Equation3456 G := λ x => h x x
theorem Equation3555_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3555 G) : Equation3456 G := λ x => h x x
theorem Equation3556_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3556 G) : Equation3456 G := λ x => h x x
theorem Equation3558_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3558 G) : Equation3456 G := λ x => h x x
theorem Equation3559_implies_Equation3456 (G : Type*) [Magma G] (h : Equation3559 G) : Equation3456 G := λ x => h x x
theorem Equation3660_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3660 G) : Equation3659 G := λ x => h x x
theorem Equation3661_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3661 G) : Equation3659 G := λ x => h x x
theorem Equation3662_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3662 G) : Equation3659 G := λ x => h x x
theorem Equation3664_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3664 G) : Equation3659 G := λ x => h x x
theorem Equation3665_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3665 G) : Equation3659 G := λ x => h x x
theorem Equation3667_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3667 G) : Equation3659 G := λ x => h x x
theorem Equation3668_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3668 G) : Equation3659 G := λ x => h x x
theorem Equation3674_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3674 G) : Equation3659 G := λ x => h x x
theorem Equation3675_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3675 G) : Equation3659 G := λ x => h x x
theorem Equation3677_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3677 G) : Equation3659 G := λ x => h x x
theorem Equation3678_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3678 G) : Equation3659 G := λ x => h x x
theorem Equation3684_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3684 G) : Equation3659 G := λ x => h x x
theorem Equation3685_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3685 G) : Equation3659 G := λ x => h x x
theorem Equation3687_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3687 G) : Equation3659 G := λ x => h x x
theorem Equation3688_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3688 G) : Equation3659 G := λ x => h x x
theorem Equation3711_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3711 G) : Equation3659 G := λ x => h x x
theorem Equation3712_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3712 G) : Equation3659 G := λ x => h x x
theorem Equation3714_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3714 G) : Equation3659 G := λ x => h x x
theorem Equation3715_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3715 G) : Equation3659 G := λ x => h x x
theorem Equation3721_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3721 G) : Equation3659 G := λ x => h x x
theorem Equation3722_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3722 G) : Equation3659 G := λ x => h x x
theorem Equation3724_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3724 G) : Equation3659 G := λ x => h x x
theorem Equation3725_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3725 G) : Equation3659 G := λ x => h x x
theorem Equation3748_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3748 G) : Equation3659 G := λ x => h x x
theorem Equation3749_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3749 G) : Equation3659 G := λ x => h x x
theorem Equation3751_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3751 G) : Equation3659 G := λ x => h x x
theorem Equation3752_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3752 G) : Equation3659 G := λ x => h x x
theorem Equation3758_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3758 G) : Equation3659 G := λ x => h x x
theorem Equation3759_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3759 G) : Equation3659 G := λ x => h x x
theorem Equation3761_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3761 G) : Equation3659 G := λ x => h x x
theorem Equation3762_implies_Equation3659 (G : Type*) [Magma G] (h : Equation3762 G) : Equation3659 G := λ x => h x x
theorem Equation3863_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3863 G) : Equation3862 G := λ x => h x x
theorem Equation3864_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3864 G) : Equation3862 G := λ x => h x x
theorem Equation3865_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3865 G) : Equation3862 G := λ x => h x x
theorem Equation3867_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3867 G) : Equation3862 G := λ x => h x x
theorem Equation3868_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3868 G) : Equation3862 G := λ x => h x x
theorem Equation3870_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3870 G) : Equation3862 G := λ x => h x x
theorem Equation3871_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3871 G) : Equation3862 G := λ x => h x x
theorem Equation3877_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3877 G) : Equation3862 G := λ x => h x x
theorem Equation3878_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3878 G) : Equation3862 G := λ x => h x x
theorem Equation3880_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3880 G) : Equation3862 G := λ x => h x x
theorem Equation3881_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3881 G) : Equation3862 G := λ x => h x x
theorem Equation3887_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3887 G) : Equation3862 G := λ x => h x x
theorem Equation3888_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3888 G) : Equation3862 G := λ x => h x x
theorem Equation3890_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3890 G) : Equation3862 G := λ x => h x x
theorem Equation3891_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3891 G) : Equation3862 G := λ x => h x x
theorem Equation3914_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3914 G) : Equation3862 G := λ x => h x x
theorem Equation3915_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3915 G) : Equation3862 G := λ x => h x x
theorem Equation3917_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3917 G) : Equation3862 G := λ x => h x x
theorem Equation3918_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3918 G) : Equation3862 G := λ x => h x x
theorem Equation3924_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3924 G) : Equation3862 G := λ x => h x x
theorem Equation3925_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3925 G) : Equation3862 G := λ x => h x x
theorem Equation3927_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3927 G) : Equation3862 G := λ x => h x x
theorem Equation3928_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3928 G) : Equation3862 G := λ x => h x x
theorem Equation3951_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3951 G) : Equation3862 G := λ x => h x x
theorem Equation3952_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3952 G) : Equation3862 G := λ x => h x x
theorem Equation3954_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3954 G) : Equation3862 G := λ x => h x x
theorem Equation3955_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3955 G) : Equation3862 G := λ x => h x x
theorem Equation3961_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3961 G) : Equation3862 G := λ x => h x x
theorem Equation3962_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3962 G) : Equation3862 G := λ x => h x x
theorem Equation3964_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3964 G) : Equation3862 G := λ x => h x x
theorem Equation3965_implies_Equation3862 (G : Type*) [Magma G] (h : Equation3965 G) : Equation3862 G := λ x => h x x
theorem Equation4066_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4066 G) : Equation4065 G := λ x => h x x
theorem Equation4067_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4067 G) : Equation4065 G := λ x => h x x
theorem Equation4068_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4068 G) : Equation4065 G := λ x => h x x
theorem Equation4070_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4070 G) : Equation4065 G := λ x => h x x
theorem Equation4071_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4071 G) : Equation4065 G := λ x => h x x
theorem Equation4073_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4073 G) : Equation4065 G := λ x => h x x
theorem Equation4074_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4074 G) : Equation4065 G := λ x => h x x
theorem Equation4080_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4080 G) : Equation4065 G := λ x => h x x
theorem Equation4081_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4081 G) : Equation4065 G := λ x => h x x
theorem Equation4083_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4083 G) : Equation4065 G := λ x => h x x
theorem Equation4084_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4084 G) : Equation4065 G := λ x => h x x
theorem Equation4090_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4090 G) : Equation4065 G := λ x => h x x
theorem Equation4091_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4091 G) : Equation4065 G := λ x => h x x
theorem Equation4093_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4093 G) : Equation4065 G := λ x => h x x
theorem Equation4094_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4094 G) : Equation4065 G := λ x => h x x
theorem Equation4117_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4117 G) : Equation4065 G := λ x => h x x
theorem Equation4118_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4118 G) : Equation4065 G := λ x => h x x
theorem Equation4120_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4120 G) : Equation4065 G := λ x => h x x
theorem Equation4121_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4121 G) : Equation4065 G := λ x => h x x
theorem Equation4127_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4127 G) : Equation4065 G := λ x => h x x
theorem Equation4128_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4128 G) : Equation4065 G := λ x => h x x
theorem Equation4130_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4130 G) : Equation4065 G := λ x => h x x
theorem Equation4131_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4131 G) : Equation4065 G := λ x => h x x
theorem Equation4154_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4154 G) : Equation4065 G := λ x => h x x
theorem Equation4155_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4155 G) : Equation4065 G := λ x => h x x
theorem Equation4157_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4157 G) : Equation4065 G := λ x => h x x
theorem Equation4158_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4158 G) : Equation4065 G := λ x => h x x
theorem Equation4164_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4164 G) : Equation4065 G := λ x => h x x
theorem Equation4165_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4165 G) : Equation4065 G := λ x => h x x
theorem Equation4167_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4167 G) : Equation4065 G := λ x => h x x
theorem Equation4168_implies_Equation4065 (G : Type*) [Magma G] (h : Equation4168 G) : Equation4065 G := λ x => h x x
theorem Equation4381_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4381 G) : Equation4380 G := λ x => h x x
theorem Equation4382_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4382 G) : Equation4380 G := λ x => h x x
theorem Equation4383_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4383 G) : Equation4380 G := λ x => h x x
theorem Equation4385_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4385 G) : Equation4380 G := λ x => h x x
theorem Equation4386_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4386 G) : Equation4380 G := λ x => h x x
theorem Equation4388_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4388 G) : Equation4380 G := λ x => h x x
theorem Equation4389_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4389 G) : Equation4380 G := λ x => h x x
theorem Equation4395_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4395 G) : Equation4380 G := λ x => h x x
theorem Equation4396_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4396 G) : Equation4380 G := λ x => h x x
theorem Equation4398_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4398 G) : Equation4380 G := λ x => h x x
theorem Equation4399_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4399 G) : Equation4380 G := λ x => h x x
theorem Equation4405_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4405 G) : Equation4380 G := λ x => h x x
theorem Equation4406_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4406 G) : Equation4380 G := λ x => h x x
theorem Equation4408_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4408 G) : Equation4380 G := λ x => h x x
theorem Equation4409_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4409 G) : Equation4380 G := λ x => h x x
theorem Equation4432_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4432 G) : Equation4380 G := λ x => h x x
theorem Equation4433_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4433 G) : Equation4380 G := λ x => h x x
theorem Equation4435_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4435 G) : Equation4380 G := λ x => h x x
theorem Equation4436_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4436 G) : Equation4380 G := λ x => h x x
theorem Equation4442_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4442 G) : Equation4380 G := λ x => h x x
theorem Equation4443_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4443 G) : Equation4380 G := λ x => h x x
theorem Equation4445_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4445 G) : Equation4380 G := λ x => h x x
theorem Equation4446_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4446 G) : Equation4380 G := λ x => h x x
theorem Equation4469_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4469 G) : Equation4380 G := λ x => h x x
theorem Equation4470_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4470 G) : Equation4380 G := λ x => h x x
theorem Equation4472_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4472 G) : Equation4380 G := λ x => h x x
theorem Equation4473_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4473 G) : Equation4380 G := λ x => h x x
theorem Equation4479_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4479 G) : Equation4380 G := λ x => h x x
theorem Equation4480_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4480 G) : Equation4380 G := λ x => h x x
theorem Equation4482_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4482 G) : Equation4380 G := λ x => h x x
theorem Equation4483_implies_Equation4380 (G : Type*) [Magma G] (h : Equation4483 G) : Equation4380 G := λ x => h x x