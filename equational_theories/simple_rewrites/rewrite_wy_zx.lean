import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation14 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ y)
def Equation22 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ w)
def Equation29 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ y
def Equation37 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ w
def Equation53 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (x ∘ y))
def Equation61 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ w))
def Equation63 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (x ∘ y))
def Equation65 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (y ∘ x))
def Equation66 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (y ∘ y))
def Equation71 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ w))
def Equation73 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (x ∘ y))
def Equation81 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ w))
def Equation85 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ w))
def Equation89 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ w))
def Equation93 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ w))
def Equation94 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ x))
def Equation95 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ y))
def Equation96 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ z))
def Equation97 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ w))
def Equation105 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ x) ∘ y)
def Equation113 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ w)
def Equation115 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ x) ∘ y)
def Equation117 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ y) ∘ x)
def Equation118 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ y) ∘ y)
def Equation123 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ w)
def Equation125 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ x) ∘ y)
def Equation133 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ w)
def Equation137 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ w)
def Equation141 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ w)
def Equation145 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ w)
def Equation146 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ x)
def Equation147 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ y)
def Equation148 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ z)
def Equation149 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ w)
def Equation157 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (x ∘ y)
def Equation165 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ w)
def Equation167 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (x ∘ y)
def Equation169 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (y ∘ x)
def Equation170 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (y ∘ y)
def Equation175 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ w)
def Equation177 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (x ∘ y)
def Equation185 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ w)
def Equation189 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ w)
def Equation193 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ w)
def Equation197 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ w)
def Equation198 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ x)
def Equation199 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ y)
def Equation200 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ z)
def Equation201 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ w)
def Equation209 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ x)) ∘ y
def Equation217 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ w
def Equation219 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ x)) ∘ y
def Equation221 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ y)) ∘ x
def Equation222 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ y)) ∘ y
def Equation227 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ w
def Equation229 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ x)) ∘ y
def Equation237 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ w
def Equation241 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ w
def Equation245 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ w
def Equation249 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ w
def Equation250 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ x
def Equation251 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ y
def Equation252 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ z
def Equation253 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ w
def Equation261 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ x) ∘ y
def Equation269 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ w
def Equation271 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ x) ∘ y
def Equation273 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ y) ∘ x
def Equation274 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ y) ∘ y
def Equation279 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ w
def Equation281 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ x) ∘ y
def Equation289 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ w
def Equation293 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ w
def Equation297 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ w
def Equation301 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ w
def Equation302 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ x
def Equation303 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ y
def Equation304 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ z
def Equation305 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ w
def Equation313 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (x ∘ y)
def Equation321 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ w)
def Equation323 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (x ∘ y)
def Equation325 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (y ∘ x)
def Equation326 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (y ∘ y)
def Equation331 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ w)
def Equation333 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (x ∘ y)
def Equation341 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ w)
def Equation345 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ w)
def Equation349 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ w)
def Equation353 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ w)
def Equation354 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ x)
def Equation355 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ y)
def Equation356 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ z)
def Equation357 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ w)
def Equation365 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ x) ∘ y
def Equation373 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ w
def Equation375 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ x) ∘ y
def Equation377 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ y) ∘ x
def Equation378 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ y) ∘ y
def Equation383 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ w
def Equation385 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ x) ∘ y
def Equation393 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ w
def Equation397 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ w
def Equation401 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ w
def Equation405 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ w
def Equation406 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ x
def Equation407 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ y
def Equation408 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ z
def Equation409 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ w
def Equation417 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (y ∘ (x ∘ y)))
def Equation425 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (x ∘ (y ∘ (z ∘ w)))
def Equation427 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (x ∘ (x ∘ y)))
def Equation429 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (x ∘ (y ∘ x)))
def Equation430 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (x ∘ (y ∘ y)))
def Equation435 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (x ∘ (z ∘ w)))
def Equation437 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (y ∘ (x ∘ y)))
def Equation445 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (y ∘ (z ∘ w)))
def Equation449 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (x ∘ w)))
def Equation453 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (y ∘ w)))
def Equation457 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (z ∘ w)))
def Equation458 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (w ∘ x)))
def Equation459 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (w ∘ y)))
def Equation460 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (w ∘ z)))
def Equation461 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (w ∘ w)))
def Equation464 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (x ∘ (x ∘ y)))
def Equation466 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (x ∘ (y ∘ x)))
def Equation467 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (x ∘ (y ∘ y)))
def Equation472 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (x ∘ (z ∘ w)))
def Equation473 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (y ∘ (x ∘ x)))
def Equation474 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (y ∘ (x ∘ y)))
def Equation476 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (y ∘ (y ∘ x)))
def Equation477 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (y ∘ (y ∘ y)))
def Equation482 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (y ∘ (z ∘ w)))
def Equation486 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (x ∘ w)))
def Equation490 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (y ∘ w)))
def Equation494 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (z ∘ w)))
def Equation495 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (w ∘ x)))
def Equation496 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (w ∘ y)))
def Equation497 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (w ∘ z)))
def Equation498 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (w ∘ w)))
def Equation501 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (x ∘ (x ∘ y)))
def Equation503 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (x ∘ (y ∘ x)))
def Equation504 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (x ∘ (y ∘ y)))
def Equation509 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (x ∘ (z ∘ w)))
def Equation511 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (y ∘ (x ∘ y)))
def Equation519 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (y ∘ (z ∘ w)))
def Equation523 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (x ∘ w)))
def Equation527 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (y ∘ w)))
def Equation531 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (z ∘ w)))
def Equation532 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (w ∘ x)))
def Equation533 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (w ∘ y)))
def Equation534 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (w ∘ z)))
def Equation535 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (w ∘ w)))
def Equation540 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (x ∘ w)))
def Equation544 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (y ∘ w)))
def Equation548 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (z ∘ w)))
def Equation549 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (w ∘ x)))
def Equation550 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (w ∘ y)))
def Equation551 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (w ∘ z)))
def Equation552 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (w ∘ w)))
def Equation557 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (x ∘ w)))
def Equation561 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (y ∘ w)))
def Equation565 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (z ∘ w)))
def Equation566 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (w ∘ x)))
def Equation567 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (w ∘ y)))
def Equation568 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (w ∘ z)))
def Equation569 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (w ∘ w)))
def Equation574 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (x ∘ w)))
def Equation578 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (y ∘ w)))
def Equation582 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (z ∘ w)))
def Equation583 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (w ∘ x)))
def Equation584 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (w ∘ y)))
def Equation585 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (w ∘ z)))
def Equation586 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (w ∘ w)))
def Equation588 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (x ∘ x)))
def Equation589 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (x ∘ y)))
def Equation590 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (x ∘ z)))
def Equation591 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (x ∘ w)))
def Equation593 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (y ∘ x)))
def Equation594 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (y ∘ y)))
def Equation595 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (y ∘ z)))
def Equation596 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (y ∘ w)))
def Equation598 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (z ∘ x)))
def Equation599 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (z ∘ y)))
def Equation600 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (z ∘ z)))
def Equation601 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (z ∘ w)))
def Equation603 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (w ∘ x)))
def Equation604 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (w ∘ y)))
def Equation605 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (w ∘ z)))
def Equation606 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (w ∘ w)))
def Equation620 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ ((y ∘ x) ∘ y))
def Equation628 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (x ∘ ((y ∘ z) ∘ w))
def Equation630 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ ((x ∘ x) ∘ y))
def Equation632 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ ((x ∘ y) ∘ x))
def Equation633 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ ((x ∘ y) ∘ y))
def Equation638 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((x ∘ z) ∘ w))
def Equation640 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ ((y ∘ x) ∘ y))
def Equation648 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((y ∘ z) ∘ w))
def Equation652 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ x) ∘ w))
def Equation656 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ y) ∘ w))
def Equation660 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ z) ∘ w))
def Equation661 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ w) ∘ x))
def Equation662 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ w) ∘ y))
def Equation663 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ w) ∘ z))
def Equation664 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ w) ∘ w))
def Equation667 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((x ∘ x) ∘ y))
def Equation669 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((x ∘ y) ∘ x))
def Equation670 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((x ∘ y) ∘ y))
def Equation675 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((x ∘ z) ∘ w))
def Equation676 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((y ∘ x) ∘ x))
def Equation677 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((y ∘ x) ∘ y))
def Equation679 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((y ∘ y) ∘ x))
def Equation680 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((y ∘ y) ∘ y))
def Equation685 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((y ∘ z) ∘ w))
def Equation689 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ x) ∘ w))
def Equation693 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ y) ∘ w))
def Equation697 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ z) ∘ w))
def Equation698 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ w) ∘ x))
def Equation699 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ w) ∘ y))
def Equation700 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ w) ∘ z))
def Equation701 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ w) ∘ w))
def Equation704 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ ((x ∘ x) ∘ y))
def Equation706 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ ((x ∘ y) ∘ x))
def Equation707 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ ((x ∘ y) ∘ y))
def Equation712 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((x ∘ z) ∘ w))
def Equation714 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ ((y ∘ x) ∘ y))
def Equation722 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((y ∘ z) ∘ w))
def Equation726 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ x) ∘ w))
def Equation730 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ y) ∘ w))
def Equation734 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ z) ∘ w))
def Equation735 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ w) ∘ x))
def Equation736 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ w) ∘ y))
def Equation737 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ w) ∘ z))
def Equation738 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ w) ∘ w))
def Equation743 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ x) ∘ w))
def Equation747 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ y) ∘ w))
def Equation751 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ z) ∘ w))
def Equation752 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ w) ∘ x))
def Equation753 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ w) ∘ y))
def Equation754 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ w) ∘ z))
def Equation755 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ w) ∘ w))
def Equation760 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ x) ∘ w))
def Equation764 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ y) ∘ w))
def Equation768 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ z) ∘ w))
def Equation769 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ w) ∘ x))
def Equation770 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ w) ∘ y))
def Equation771 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ w) ∘ z))
def Equation772 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ w) ∘ w))
def Equation777 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ x) ∘ w))
def Equation781 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ y) ∘ w))
def Equation785 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ z) ∘ w))
def Equation786 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ w) ∘ x))
def Equation787 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ w) ∘ y))
def Equation788 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ w) ∘ z))
def Equation789 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ w) ∘ w))
def Equation791 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ x) ∘ x))
def Equation792 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ x) ∘ y))
def Equation793 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ x) ∘ z))
def Equation794 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ x) ∘ w))
def Equation796 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ y) ∘ x))
def Equation797 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ y) ∘ y))
def Equation798 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ y) ∘ z))
def Equation799 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ y) ∘ w))
def Equation801 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ z) ∘ x))
def Equation802 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ z) ∘ y))
def Equation803 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ z) ∘ z))
def Equation804 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ z) ∘ w))
def Equation806 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ w) ∘ x))
def Equation807 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ w) ∘ y))
def Equation808 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ w) ∘ z))
def Equation809 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ w) ∘ w))
def Equation823 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ y) ∘ (x ∘ y))
def Equation831 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((x ∘ y) ∘ (z ∘ w))
def Equation833 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ x) ∘ (x ∘ y))
def Equation835 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ x) ∘ (y ∘ x))
def Equation836 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ x) ∘ (y ∘ y))
def Equation841 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ x) ∘ (z ∘ w))
def Equation843 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ y) ∘ (x ∘ y))
def Equation851 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ y) ∘ (z ∘ w))
def Equation855 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (x ∘ w))
def Equation859 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (y ∘ w))
def Equation863 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (z ∘ w))
def Equation864 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (w ∘ x))
def Equation865 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (w ∘ y))
def Equation866 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (w ∘ z))
def Equation867 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (w ∘ w))
def Equation870 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ x) ∘ (x ∘ y))
def Equation872 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ x) ∘ (y ∘ x))
def Equation873 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ x) ∘ (y ∘ y))
def Equation878 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ x) ∘ (z ∘ w))
def Equation879 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ y) ∘ (x ∘ x))
def Equation880 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ y) ∘ (x ∘ y))
def Equation882 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ y) ∘ (y ∘ x))
def Equation883 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ y) ∘ (y ∘ y))
def Equation888 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ y) ∘ (z ∘ w))
def Equation892 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (x ∘ w))
def Equation896 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (y ∘ w))
def Equation900 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (z ∘ w))
def Equation901 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (w ∘ x))
def Equation902 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (w ∘ y))
def Equation903 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (w ∘ z))
def Equation904 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (w ∘ w))
def Equation907 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ x) ∘ (x ∘ y))
def Equation909 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ x) ∘ (y ∘ x))
def Equation910 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ x) ∘ (y ∘ y))
def Equation915 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ x) ∘ (z ∘ w))
def Equation917 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ y) ∘ (x ∘ y))
def Equation925 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ y) ∘ (z ∘ w))
def Equation929 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (x ∘ w))
def Equation933 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (y ∘ w))
def Equation937 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (z ∘ w))
def Equation938 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (w ∘ x))
def Equation939 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (w ∘ y))
def Equation940 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (w ∘ z))
def Equation941 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (w ∘ w))
def Equation946 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (x ∘ w))
def Equation950 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (y ∘ w))
def Equation954 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (z ∘ w))
def Equation955 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (w ∘ x))
def Equation956 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (w ∘ y))
def Equation957 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (w ∘ z))
def Equation958 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (w ∘ w))
def Equation963 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (x ∘ w))
def Equation967 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (y ∘ w))
def Equation971 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (z ∘ w))
def Equation972 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (w ∘ x))
def Equation973 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (w ∘ y))
def Equation974 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (w ∘ z))
def Equation975 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (w ∘ w))
def Equation980 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (x ∘ w))
def Equation984 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (y ∘ w))
def Equation988 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (z ∘ w))
def Equation989 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (w ∘ x))
def Equation990 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (w ∘ y))
def Equation991 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (w ∘ z))
def Equation992 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (w ∘ w))
def Equation994 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (x ∘ x))
def Equation995 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (x ∘ y))
def Equation996 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (x ∘ z))
def Equation997 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (x ∘ w))
def Equation999 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (y ∘ x))
def Equation1000 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (y ∘ y))
def Equation1001 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (y ∘ z))
def Equation1002 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (y ∘ w))
def Equation1004 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (z ∘ x))
def Equation1005 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (z ∘ y))
def Equation1006 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (z ∘ z))
def Equation1007 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (z ∘ w))
def Equation1009 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (w ∘ x))
def Equation1010 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (w ∘ y))
def Equation1011 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (w ∘ z))
def Equation1012 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (w ∘ w))
def Equation1026 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ (y ∘ x)) ∘ y)
def Equation1034 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((x ∘ (y ∘ z)) ∘ w)
def Equation1036 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ (x ∘ x)) ∘ y)
def Equation1038 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ (x ∘ y)) ∘ x)
def Equation1039 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ (x ∘ y)) ∘ y)
def Equation1044 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (x ∘ z)) ∘ w)
def Equation1046 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ (y ∘ x)) ∘ y)
def Equation1054 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (y ∘ z)) ∘ w)
def Equation1058 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ x)) ∘ w)
def Equation1062 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ y)) ∘ w)
def Equation1066 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ z)) ∘ w)
def Equation1067 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ x)
def Equation1068 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ y)
def Equation1069 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ z)
def Equation1070 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ w)
def Equation1073 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (x ∘ x)) ∘ y)
def Equation1075 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (x ∘ y)) ∘ x)
def Equation1076 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (x ∘ y)) ∘ y)
def Equation1081 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (x ∘ z)) ∘ w)
def Equation1082 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (y ∘ x)) ∘ x)
def Equation1083 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (y ∘ x)) ∘ y)
def Equation1085 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (y ∘ y)) ∘ x)
def Equation1086 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (y ∘ y)) ∘ y)
def Equation1091 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (y ∘ z)) ∘ w)
def Equation1095 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ x)) ∘ w)
def Equation1099 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ y)) ∘ w)
def Equation1103 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ z)) ∘ w)
def Equation1104 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ w)) ∘ x)
def Equation1105 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ w)) ∘ y)
def Equation1106 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ w)) ∘ z)
def Equation1107 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ w)) ∘ w)
def Equation1110 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ (x ∘ x)) ∘ y)
def Equation1112 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ (x ∘ y)) ∘ x)
def Equation1113 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ (x ∘ y)) ∘ y)
def Equation1118 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (x ∘ z)) ∘ w)
def Equation1120 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ (y ∘ x)) ∘ y)
def Equation1128 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (y ∘ z)) ∘ w)
def Equation1132 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ x)) ∘ w)
def Equation1136 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ y)) ∘ w)
def Equation1140 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ z)) ∘ w)
def Equation1141 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ w)) ∘ x)
def Equation1142 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ w)) ∘ y)
def Equation1143 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ w)) ∘ z)
def Equation1144 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ w)) ∘ w)
def Equation1149 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ x)) ∘ w)
def Equation1153 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ y)) ∘ w)
def Equation1157 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ z)) ∘ w)
def Equation1158 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ x)
def Equation1159 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ y)
def Equation1160 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ z)
def Equation1161 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ w)
def Equation1166 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ x)) ∘ w)
def Equation1170 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ y)) ∘ w)
def Equation1174 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ z)) ∘ w)
def Equation1175 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ x)
def Equation1176 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ y)
def Equation1177 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ z)
def Equation1178 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ w)
def Equation1183 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ x)) ∘ w)
def Equation1187 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ y)) ∘ w)
def Equation1191 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ z)) ∘ w)
def Equation1192 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ w)) ∘ x)
def Equation1193 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ w)) ∘ y)
def Equation1194 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ w)) ∘ z)
def Equation1195 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ w)) ∘ w)
def Equation1197 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ x)) ∘ x)
def Equation1198 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ x)) ∘ y)
def Equation1199 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ x)) ∘ z)
def Equation1200 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ x)) ∘ w)
def Equation1202 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ y)) ∘ x)
def Equation1203 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ y)) ∘ y)
def Equation1204 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ y)) ∘ z)
def Equation1205 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ y)) ∘ w)
def Equation1207 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ z)) ∘ x)
def Equation1208 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ z)) ∘ y)
def Equation1209 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ z)) ∘ z)
def Equation1210 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ z)) ∘ w)
def Equation1212 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ w)) ∘ x)
def Equation1213 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ w)) ∘ y)
def Equation1214 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ w)) ∘ z)
def Equation1215 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ w)) ∘ w)
def Equation1229 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((x ∘ y) ∘ x) ∘ y)
def Equation1237 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((x ∘ y) ∘ z) ∘ w)
def Equation1239 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((y ∘ x) ∘ x) ∘ y)
def Equation1241 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((y ∘ x) ∘ y) ∘ x)
def Equation1242 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((y ∘ x) ∘ y) ∘ y)
def Equation1247 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ x) ∘ z) ∘ w)
def Equation1249 (G: Type*) [Magma G] := ∀ x y : G, x = x ∘ (((y ∘ y) ∘ x) ∘ y)
def Equation1257 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ y) ∘ z) ∘ w)
def Equation1261 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ x) ∘ w)
def Equation1265 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ y) ∘ w)
def Equation1269 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ z) ∘ w)
def Equation1270 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ w) ∘ x)
def Equation1271 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ w) ∘ y)
def Equation1272 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ w) ∘ z)
def Equation1273 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ w) ∘ w)
def Equation1276 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ x) ∘ x) ∘ y)
def Equation1278 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ x) ∘ y) ∘ x)
def Equation1279 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ x) ∘ y) ∘ y)
def Equation1284 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ x) ∘ z) ∘ w)
def Equation1285 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ y) ∘ x) ∘ x)
def Equation1286 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ y) ∘ x) ∘ y)
def Equation1288 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ y) ∘ y) ∘ x)
def Equation1289 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ y) ∘ y) ∘ y)
def Equation1294 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ y) ∘ z) ∘ w)
def Equation1298 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ x) ∘ w)
def Equation1302 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ y) ∘ w)
def Equation1306 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ z) ∘ w)
def Equation1307 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ w) ∘ x)
def Equation1308 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ w) ∘ y)
def Equation1309 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ w) ∘ z)
def Equation1310 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ w) ∘ w)
def Equation1313 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((y ∘ x) ∘ x) ∘ y)
def Equation1315 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((y ∘ x) ∘ y) ∘ x)
def Equation1316 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((y ∘ x) ∘ y) ∘ y)
def Equation1321 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ x) ∘ z) ∘ w)
def Equation1323 (G: Type*) [Magma G] := ∀ x y : G, x = y ∘ (((y ∘ y) ∘ x) ∘ y)
def Equation1331 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ y) ∘ z) ∘ w)
def Equation1335 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ x) ∘ w)
def Equation1339 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ y) ∘ w)
def Equation1343 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ z) ∘ w)
def Equation1344 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ w) ∘ x)
def Equation1345 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ w) ∘ y)
def Equation1346 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ w) ∘ z)
def Equation1347 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ w) ∘ w)
def Equation1352 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ x) ∘ w)
def Equation1356 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ y) ∘ w)
def Equation1360 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ z) ∘ w)
def Equation1361 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ w) ∘ x)
def Equation1362 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ w) ∘ y)
def Equation1363 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ w) ∘ z)
def Equation1364 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ w) ∘ w)
def Equation1369 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ x) ∘ w)
def Equation1373 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ y) ∘ w)
def Equation1377 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ z) ∘ w)
def Equation1378 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ w) ∘ x)
def Equation1379 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ w) ∘ y)
def Equation1380 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ w) ∘ z)
def Equation1381 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ w) ∘ w)
def Equation1386 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ x) ∘ w)
def Equation1390 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ y) ∘ w)
def Equation1394 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ z) ∘ w)
def Equation1395 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ w) ∘ x)
def Equation1396 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ w) ∘ y)
def Equation1397 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ w) ∘ z)
def Equation1398 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ w) ∘ w)
def Equation1400 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ x) ∘ x)
def Equation1401 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ x) ∘ y)
def Equation1402 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ x) ∘ z)
def Equation1403 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ x) ∘ w)
def Equation1405 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ y) ∘ x)
def Equation1406 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ y) ∘ y)
def Equation1407 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ y) ∘ z)
def Equation1408 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ y) ∘ w)
def Equation1410 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ z) ∘ x)
def Equation1411 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ z) ∘ y)
def Equation1412 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ z) ∘ z)
def Equation1413 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ z) ∘ w)
def Equation1415 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ w) ∘ x)
def Equation1416 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ w) ∘ y)
def Equation1417 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ w) ∘ z)
def Equation1418 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ w) ∘ w)
def Equation1432 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ (y ∘ (x ∘ y))
def Equation1440 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ x) ∘ (y ∘ (z ∘ w))
def Equation1442 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (x ∘ (x ∘ y))
def Equation1444 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (x ∘ (y ∘ x))
def Equation1445 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (x ∘ (y ∘ y))
def Equation1450 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (x ∘ (z ∘ w))
def Equation1452 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (y ∘ (x ∘ y))
def Equation1460 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (y ∘ (z ∘ w))
def Equation1464 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (x ∘ w))
def Equation1468 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (y ∘ w))
def Equation1472 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (z ∘ w))
def Equation1473 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (w ∘ x))
def Equation1474 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (w ∘ y))
def Equation1475 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (w ∘ z))
def Equation1476 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (w ∘ w))
def Equation1479 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (x ∘ (x ∘ y))
def Equation1481 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (x ∘ (y ∘ x))
def Equation1482 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (x ∘ (y ∘ y))
def Equation1487 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (x ∘ (z ∘ w))
def Equation1488 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (y ∘ (x ∘ x))
def Equation1489 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (y ∘ (x ∘ y))
def Equation1491 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (y ∘ (y ∘ x))
def Equation1492 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (y ∘ (y ∘ y))
def Equation1497 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (y ∘ (z ∘ w))
def Equation1501 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (x ∘ w))
def Equation1505 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (y ∘ w))
def Equation1509 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (z ∘ w))
def Equation1510 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (w ∘ x))
def Equation1511 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (w ∘ y))
def Equation1512 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (w ∘ z))
def Equation1513 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (w ∘ w))
def Equation1516 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (x ∘ (x ∘ y))
def Equation1518 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (x ∘ (y ∘ x))
def Equation1519 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (x ∘ (y ∘ y))
def Equation1524 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (x ∘ (z ∘ w))
def Equation1526 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (y ∘ (x ∘ y))
def Equation1534 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (y ∘ (z ∘ w))
def Equation1538 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (x ∘ w))
def Equation1542 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (y ∘ w))
def Equation1546 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (z ∘ w))
def Equation1547 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (w ∘ x))
def Equation1548 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (w ∘ y))
def Equation1549 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (w ∘ z))
def Equation1550 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (w ∘ w))
def Equation1555 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (x ∘ w))
def Equation1559 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (y ∘ w))
def Equation1563 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (z ∘ w))
def Equation1564 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (w ∘ x))
def Equation1565 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (w ∘ y))
def Equation1566 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (w ∘ z))
def Equation1567 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (w ∘ w))
def Equation1572 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (x ∘ w))
def Equation1576 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (y ∘ w))
def Equation1580 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (z ∘ w))
def Equation1581 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (w ∘ x))
def Equation1582 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (w ∘ y))
def Equation1583 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (w ∘ z))
def Equation1584 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (w ∘ w))
def Equation1589 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (x ∘ w))
def Equation1593 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (y ∘ w))
def Equation1597 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (z ∘ w))
def Equation1598 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (w ∘ x))
def Equation1599 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (w ∘ y))
def Equation1600 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (w ∘ z))
def Equation1601 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (w ∘ w))
def Equation1603 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (x ∘ x))
def Equation1604 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (x ∘ y))
def Equation1605 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (x ∘ z))
def Equation1606 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (x ∘ w))
def Equation1608 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (y ∘ x))
def Equation1609 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (y ∘ y))
def Equation1610 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (y ∘ z))
def Equation1611 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (y ∘ w))
def Equation1613 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (z ∘ x))
def Equation1614 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (z ∘ y))
def Equation1615 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (z ∘ z))
def Equation1616 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (z ∘ w))
def Equation1618 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (w ∘ x))
def Equation1619 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (w ∘ y))
def Equation1620 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (w ∘ z))
def Equation1621 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (w ∘ w))
def Equation1635 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ ((y ∘ x) ∘ y)
def Equation1643 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ x) ∘ ((y ∘ z) ∘ w)
def Equation1645 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ ((x ∘ x) ∘ y)
def Equation1647 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ ((x ∘ y) ∘ x)
def Equation1648 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ ((x ∘ y) ∘ y)
def Equation1653 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((x ∘ z) ∘ w)
def Equation1655 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ ((y ∘ x) ∘ y)
def Equation1663 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((y ∘ z) ∘ w)
def Equation1667 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ x) ∘ w)
def Equation1671 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ y) ∘ w)
def Equation1675 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ z) ∘ w)
def Equation1676 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ x)
def Equation1677 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ y)
def Equation1678 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ z)
def Equation1679 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ w)
def Equation1682 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((x ∘ x) ∘ y)
def Equation1684 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((x ∘ y) ∘ x)
def Equation1685 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((x ∘ y) ∘ y)
def Equation1690 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((x ∘ z) ∘ w)
def Equation1691 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((y ∘ x) ∘ x)
def Equation1692 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((y ∘ x) ∘ y)
def Equation1694 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((y ∘ y) ∘ x)
def Equation1695 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((y ∘ y) ∘ y)
def Equation1700 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((y ∘ z) ∘ w)
def Equation1704 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ x) ∘ w)
def Equation1708 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ y) ∘ w)
def Equation1712 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ z) ∘ w)
def Equation1713 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ w) ∘ x)
def Equation1714 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ w) ∘ y)
def Equation1715 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ w) ∘ z)
def Equation1716 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ w) ∘ w)
def Equation1719 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ ((x ∘ x) ∘ y)
def Equation1721 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ ((x ∘ y) ∘ x)
def Equation1722 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ ((x ∘ y) ∘ y)
def Equation1727 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((x ∘ z) ∘ w)
def Equation1729 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ ((y ∘ x) ∘ y)
def Equation1737 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((y ∘ z) ∘ w)
def Equation1741 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ x) ∘ w)
def Equation1745 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ y) ∘ w)
def Equation1749 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ z) ∘ w)
def Equation1750 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ w) ∘ x)
def Equation1751 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ w) ∘ y)
def Equation1752 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ w) ∘ z)
def Equation1753 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ w) ∘ w)
def Equation1758 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ x) ∘ w)
def Equation1762 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ y) ∘ w)
def Equation1766 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ z) ∘ w)
def Equation1767 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ x)
def Equation1768 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ y)
def Equation1769 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ z)
def Equation1770 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ w)
def Equation1775 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ x) ∘ w)
def Equation1779 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ y) ∘ w)
def Equation1783 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ z) ∘ w)
def Equation1784 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ x)
def Equation1785 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ y)
def Equation1786 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ z)
def Equation1787 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ w)
def Equation1792 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ x) ∘ w)
def Equation1796 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ y) ∘ w)
def Equation1800 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ z) ∘ w)
def Equation1801 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ w) ∘ x)
def Equation1802 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ w) ∘ y)
def Equation1803 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ w) ∘ z)
def Equation1804 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ w) ∘ w)
def Equation1806 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ x) ∘ x)
def Equation1807 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ x) ∘ y)
def Equation1808 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ x) ∘ z)
def Equation1809 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ x) ∘ w)
def Equation1811 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ y) ∘ x)
def Equation1812 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ y) ∘ y)
def Equation1813 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ y) ∘ z)
def Equation1814 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ y) ∘ w)
def Equation1816 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ z) ∘ x)
def Equation1817 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ z) ∘ y)
def Equation1818 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ z) ∘ z)
def Equation1819 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ z) ∘ w)
def Equation1821 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ w) ∘ x)
def Equation1822 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ w) ∘ y)
def Equation1823 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ w) ∘ z)
def Equation1824 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ w) ∘ w)
def Equation1838 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ y)) ∘ (x ∘ y)
def Equation1846 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (x ∘ y)) ∘ (z ∘ w)
def Equation1848 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ x)) ∘ (x ∘ y)
def Equation1850 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ x)) ∘ (y ∘ x)
def Equation1851 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ x)) ∘ (y ∘ y)
def Equation1856 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ x)) ∘ (z ∘ w)
def Equation1858 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ y)) ∘ (x ∘ y)
def Equation1866 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ y)) ∘ (z ∘ w)
def Equation1870 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (x ∘ w)
def Equation1874 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (y ∘ w)
def Equation1878 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (z ∘ w)
def Equation1879 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ x)
def Equation1880 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ y)
def Equation1881 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ z)
def Equation1882 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ w)
def Equation1885 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ x)) ∘ (x ∘ y)
def Equation1887 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ x)) ∘ (y ∘ x)
def Equation1888 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ x)) ∘ (y ∘ y)
def Equation1893 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ x)) ∘ (z ∘ w)
def Equation1894 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ y)) ∘ (x ∘ x)
def Equation1895 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ y)) ∘ (x ∘ y)
def Equation1897 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ y)) ∘ (y ∘ x)
def Equation1898 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ y)) ∘ (y ∘ y)
def Equation1903 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ y)) ∘ (z ∘ w)
def Equation1907 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (x ∘ w)
def Equation1911 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (y ∘ w)
def Equation1915 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (z ∘ w)
def Equation1916 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (w ∘ x)
def Equation1917 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (w ∘ y)
def Equation1918 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (w ∘ z)
def Equation1919 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (w ∘ w)
def Equation1922 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ x)) ∘ (x ∘ y)
def Equation1924 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ x)) ∘ (y ∘ x)
def Equation1925 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ x)) ∘ (y ∘ y)
def Equation1930 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ x)) ∘ (z ∘ w)
def Equation1932 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ y)) ∘ (x ∘ y)
def Equation1940 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ y)) ∘ (z ∘ w)
def Equation1944 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (x ∘ w)
def Equation1948 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (y ∘ w)
def Equation1952 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (z ∘ w)
def Equation1953 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (w ∘ x)
def Equation1954 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (w ∘ y)
def Equation1955 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (w ∘ z)
def Equation1956 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (w ∘ w)
def Equation1961 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (x ∘ w)
def Equation1965 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (y ∘ w)
def Equation1969 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (z ∘ w)
def Equation1970 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ x)
def Equation1971 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ y)
def Equation1972 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ z)
def Equation1973 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ w)
def Equation1978 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (x ∘ w)
def Equation1982 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (y ∘ w)
def Equation1986 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (z ∘ w)
def Equation1987 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ x)
def Equation1988 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ y)
def Equation1989 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ z)
def Equation1990 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ w)
def Equation1995 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (x ∘ w)
def Equation1999 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (y ∘ w)
def Equation2003 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (z ∘ w)
def Equation2004 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (w ∘ x)
def Equation2005 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (w ∘ y)
def Equation2006 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (w ∘ z)
def Equation2007 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (w ∘ w)
def Equation2009 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (x ∘ x)
def Equation2010 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (x ∘ y)
def Equation2011 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (x ∘ z)
def Equation2012 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (x ∘ w)
def Equation2014 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (y ∘ x)
def Equation2015 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (y ∘ y)
def Equation2016 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (y ∘ z)
def Equation2017 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (y ∘ w)
def Equation2019 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (z ∘ x)
def Equation2020 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (z ∘ y)
def Equation2021 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (z ∘ z)
def Equation2022 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (z ∘ w)
def Equation2024 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (w ∘ x)
def Equation2025 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (w ∘ y)
def Equation2026 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (w ∘ z)
def Equation2027 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (w ∘ w)
def Equation2041 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ y) ∘ (x ∘ y)
def Equation2049 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ x) ∘ y) ∘ (z ∘ w)
def Equation2051 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ x) ∘ (x ∘ y)
def Equation2053 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ x) ∘ (y ∘ x)
def Equation2054 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ x) ∘ (y ∘ y)
def Equation2059 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ x) ∘ (z ∘ w)
def Equation2061 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ y) ∘ (x ∘ y)
def Equation2069 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ y) ∘ (z ∘ w)
def Equation2073 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (x ∘ w)
def Equation2077 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (y ∘ w)
def Equation2081 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (z ∘ w)
def Equation2082 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ x)
def Equation2083 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ y)
def Equation2084 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ z)
def Equation2085 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ w)
def Equation2088 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ x) ∘ (x ∘ y)
def Equation2090 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ x) ∘ (y ∘ x)
def Equation2091 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ x) ∘ (y ∘ y)
def Equation2096 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ x) ∘ (z ∘ w)
def Equation2097 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ y) ∘ (x ∘ x)
def Equation2098 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ y) ∘ (x ∘ y)
def Equation2100 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ y) ∘ (y ∘ x)
def Equation2101 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ y) ∘ (y ∘ y)
def Equation2106 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ y) ∘ (z ∘ w)
def Equation2110 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (x ∘ w)
def Equation2114 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (y ∘ w)
def Equation2118 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (z ∘ w)
def Equation2119 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (w ∘ x)
def Equation2120 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (w ∘ y)
def Equation2121 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (w ∘ z)
def Equation2122 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (w ∘ w)
def Equation2125 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ x) ∘ (x ∘ y)
def Equation2127 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ x) ∘ (y ∘ x)
def Equation2128 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ x) ∘ (y ∘ y)
def Equation2133 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ x) ∘ (z ∘ w)
def Equation2135 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ y) ∘ (x ∘ y)
def Equation2143 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ y) ∘ (z ∘ w)
def Equation2147 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (x ∘ w)
def Equation2151 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (y ∘ w)
def Equation2155 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (z ∘ w)
def Equation2156 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (w ∘ x)
def Equation2157 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (w ∘ y)
def Equation2158 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (w ∘ z)
def Equation2159 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (w ∘ w)
def Equation2164 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (x ∘ w)
def Equation2168 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (y ∘ w)
def Equation2172 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (z ∘ w)
def Equation2173 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ x)
def Equation2174 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ y)
def Equation2175 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ z)
def Equation2176 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ w)
def Equation2181 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (x ∘ w)
def Equation2185 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (y ∘ w)
def Equation2189 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (z ∘ w)
def Equation2190 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ x)
def Equation2191 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ y)
def Equation2192 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ z)
def Equation2193 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ w)
def Equation2198 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (x ∘ w)
def Equation2202 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (y ∘ w)
def Equation2206 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (z ∘ w)
def Equation2207 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (w ∘ x)
def Equation2208 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (w ∘ y)
def Equation2209 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (w ∘ z)
def Equation2210 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (w ∘ w)
def Equation2212 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (x ∘ x)
def Equation2213 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (x ∘ y)
def Equation2214 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (x ∘ z)
def Equation2215 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (x ∘ w)
def Equation2217 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (y ∘ x)
def Equation2218 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (y ∘ y)
def Equation2219 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (y ∘ z)
def Equation2220 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (y ∘ w)
def Equation2222 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (z ∘ x)
def Equation2223 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (z ∘ y)
def Equation2224 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (z ∘ z)
def Equation2225 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (z ∘ w)
def Equation2227 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (w ∘ x)
def Equation2228 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (w ∘ y)
def Equation2229 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (w ∘ z)
def Equation2230 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (w ∘ w)
def Equation2244 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ (y ∘ x))) ∘ y
def Equation2252 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (x ∘ (y ∘ z))) ∘ w
def Equation2254 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ (x ∘ x))) ∘ y
def Equation2256 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ (x ∘ y))) ∘ x
def Equation2257 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ (x ∘ y))) ∘ y
def Equation2262 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (x ∘ z))) ∘ w
def Equation2264 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ (y ∘ x))) ∘ y
def Equation2272 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (y ∘ z))) ∘ w
def Equation2276 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ x))) ∘ w
def Equation2280 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ y))) ∘ w
def Equation2284 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ z))) ∘ w
def Equation2285 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ x
def Equation2286 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ y
def Equation2287 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ z
def Equation2288 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ w
def Equation2291 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (x ∘ x))) ∘ y
def Equation2293 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (x ∘ y))) ∘ x
def Equation2294 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (x ∘ y))) ∘ y
def Equation2299 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (x ∘ z))) ∘ w
def Equation2300 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (y ∘ x))) ∘ x
def Equation2301 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (y ∘ x))) ∘ y
def Equation2303 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (y ∘ y))) ∘ x
def Equation2304 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (y ∘ y))) ∘ y
def Equation2309 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (y ∘ z))) ∘ w
def Equation2313 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ x))) ∘ w
def Equation2317 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ y))) ∘ w
def Equation2321 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ z))) ∘ w
def Equation2322 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ w))) ∘ x
def Equation2323 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ w))) ∘ y
def Equation2324 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ w))) ∘ z
def Equation2325 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ w))) ∘ w
def Equation2328 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ (x ∘ x))) ∘ y
def Equation2330 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ (x ∘ y))) ∘ x
def Equation2331 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ (x ∘ y))) ∘ y
def Equation2336 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (x ∘ z))) ∘ w
def Equation2338 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ (y ∘ x))) ∘ y
def Equation2346 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (y ∘ z))) ∘ w
def Equation2350 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ x))) ∘ w
def Equation2354 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ y))) ∘ w
def Equation2358 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ z))) ∘ w
def Equation2359 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ w))) ∘ x
def Equation2360 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ w))) ∘ y
def Equation2361 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ w))) ∘ z
def Equation2362 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ w))) ∘ w
def Equation2367 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ x))) ∘ w
def Equation2371 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ y))) ∘ w
def Equation2375 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ z))) ∘ w
def Equation2376 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ x
def Equation2377 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ y
def Equation2378 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ z
def Equation2379 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ w
def Equation2384 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ x))) ∘ w
def Equation2388 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ y))) ∘ w
def Equation2392 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ z))) ∘ w
def Equation2393 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ x
def Equation2394 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ y
def Equation2395 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ z
def Equation2396 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ w
def Equation2401 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ x))) ∘ w
def Equation2405 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ y))) ∘ w
def Equation2409 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ z))) ∘ w
def Equation2410 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ w))) ∘ x
def Equation2411 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ w))) ∘ y
def Equation2412 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ w))) ∘ z
def Equation2413 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ w))) ∘ w
def Equation2415 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ x))) ∘ x
def Equation2416 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ x))) ∘ y
def Equation2417 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ x))) ∘ z
def Equation2418 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ x))) ∘ w
def Equation2420 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ y))) ∘ x
def Equation2421 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ y))) ∘ y
def Equation2422 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ y))) ∘ z
def Equation2423 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ y))) ∘ w
def Equation2425 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ z))) ∘ x
def Equation2426 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ z))) ∘ y
def Equation2427 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ z))) ∘ z
def Equation2428 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ z))) ∘ w
def Equation2430 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ w))) ∘ x
def Equation2431 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ w))) ∘ y
def Equation2432 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ w))) ∘ z
def Equation2433 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ w))) ∘ w
def Equation2447 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((x ∘ y) ∘ x)) ∘ y
def Equation2455 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((x ∘ y) ∘ z)) ∘ w
def Equation2457 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((y ∘ x) ∘ x)) ∘ y
def Equation2459 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((y ∘ x) ∘ y)) ∘ x
def Equation2460 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((y ∘ x) ∘ y)) ∘ y
def Equation2465 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ x) ∘ z)) ∘ w
def Equation2467 (G: Type*) [Magma G] := ∀ x y : G, x = (x ∘ ((y ∘ y) ∘ x)) ∘ y
def Equation2475 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ y) ∘ z)) ∘ w
def Equation2479 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ x)) ∘ w
def Equation2483 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ y)) ∘ w
def Equation2487 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ z)) ∘ w
def Equation2488 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ x
def Equation2489 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ y
def Equation2490 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ z
def Equation2491 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ w
def Equation2494 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ x) ∘ x)) ∘ y
def Equation2496 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ x) ∘ y)) ∘ x
def Equation2497 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ x) ∘ y)) ∘ y
def Equation2502 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ x) ∘ z)) ∘ w
def Equation2503 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ y) ∘ x)) ∘ x
def Equation2504 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ y) ∘ x)) ∘ y
def Equation2506 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ y) ∘ y)) ∘ x
def Equation2507 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ y) ∘ y)) ∘ y
def Equation2512 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ y) ∘ z)) ∘ w
def Equation2516 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ x)) ∘ w
def Equation2520 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ y)) ∘ w
def Equation2524 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ z)) ∘ w
def Equation2525 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ w)) ∘ x
def Equation2526 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ w)) ∘ y
def Equation2527 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ w)) ∘ z
def Equation2528 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ w)) ∘ w
def Equation2531 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((y ∘ x) ∘ x)) ∘ y
def Equation2533 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((y ∘ x) ∘ y)) ∘ x
def Equation2534 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((y ∘ x) ∘ y)) ∘ y
def Equation2539 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ x) ∘ z)) ∘ w
def Equation2541 (G: Type*) [Magma G] := ∀ x y : G, x = (y ∘ ((y ∘ y) ∘ x)) ∘ y
def Equation2549 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ y) ∘ z)) ∘ w
def Equation2553 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ x)) ∘ w
def Equation2557 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ y)) ∘ w
def Equation2561 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ z)) ∘ w
def Equation2562 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ w)) ∘ x
def Equation2563 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ w)) ∘ y
def Equation2564 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ w)) ∘ z
def Equation2565 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ w)) ∘ w
def Equation2570 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ x)) ∘ w
def Equation2574 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ y)) ∘ w
def Equation2578 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ z)) ∘ w
def Equation2579 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ x
def Equation2580 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ y
def Equation2581 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ z
def Equation2582 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ w
def Equation2587 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ x)) ∘ w
def Equation2591 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ y)) ∘ w
def Equation2595 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ z)) ∘ w
def Equation2596 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ x
def Equation2597 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ y
def Equation2598 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ z
def Equation2599 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ w
def Equation2604 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ x)) ∘ w
def Equation2608 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ y)) ∘ w
def Equation2612 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ z)) ∘ w
def Equation2613 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ w)) ∘ x
def Equation2614 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ w)) ∘ y
def Equation2615 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ w)) ∘ z
def Equation2616 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ w)) ∘ w
def Equation2618 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ x)) ∘ x
def Equation2619 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ x)) ∘ y
def Equation2620 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ x)) ∘ z
def Equation2621 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ x)) ∘ w
def Equation2623 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ y)) ∘ x
def Equation2624 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ y)) ∘ y
def Equation2625 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ y)) ∘ z
def Equation2626 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ y)) ∘ w
def Equation2628 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ z)) ∘ x
def Equation2629 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ z)) ∘ y
def Equation2630 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ z)) ∘ z
def Equation2631 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ z)) ∘ w
def Equation2633 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ w)) ∘ x
def Equation2634 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ w)) ∘ y
def Equation2635 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ w)) ∘ z
def Equation2636 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ w)) ∘ w
def Equation2650 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ (y ∘ x)) ∘ y
def Equation2658 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ x) ∘ (y ∘ z)) ∘ w
def Equation2660 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ (x ∘ x)) ∘ y
def Equation2662 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ (x ∘ y)) ∘ x
def Equation2663 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ (x ∘ y)) ∘ y
def Equation2668 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (x ∘ z)) ∘ w
def Equation2670 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ (y ∘ x)) ∘ y
def Equation2678 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (y ∘ z)) ∘ w
def Equation2682 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ x)) ∘ w
def Equation2686 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ y)) ∘ w
def Equation2690 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ z)) ∘ w
def Equation2691 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ x
def Equation2692 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ y
def Equation2693 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ z
def Equation2694 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ w
def Equation2697 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (x ∘ x)) ∘ y
def Equation2699 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (x ∘ y)) ∘ x
def Equation2700 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (x ∘ y)) ∘ y
def Equation2705 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (x ∘ z)) ∘ w
def Equation2706 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (y ∘ x)) ∘ x
def Equation2707 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (y ∘ x)) ∘ y
def Equation2709 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (y ∘ y)) ∘ x
def Equation2710 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (y ∘ y)) ∘ y
def Equation2715 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (y ∘ z)) ∘ w
def Equation2719 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ x)) ∘ w
def Equation2723 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ y)) ∘ w
def Equation2727 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ z)) ∘ w
def Equation2728 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ w)) ∘ x
def Equation2729 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ w)) ∘ y
def Equation2730 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ w)) ∘ z
def Equation2731 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ w)) ∘ w
def Equation2734 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ (x ∘ x)) ∘ y
def Equation2736 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ (x ∘ y)) ∘ x
def Equation2737 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ (x ∘ y)) ∘ y
def Equation2742 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (x ∘ z)) ∘ w
def Equation2744 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ (y ∘ x)) ∘ y
def Equation2752 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (y ∘ z)) ∘ w
def Equation2756 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ x)) ∘ w
def Equation2760 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ y)) ∘ w
def Equation2764 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ z)) ∘ w
def Equation2765 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ w)) ∘ x
def Equation2766 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ w)) ∘ y
def Equation2767 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ w)) ∘ z
def Equation2768 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ w)) ∘ w
def Equation2773 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ x)) ∘ w
def Equation2777 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ y)) ∘ w
def Equation2781 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ z)) ∘ w
def Equation2782 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ x
def Equation2783 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ y
def Equation2784 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ z
def Equation2785 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ w
def Equation2790 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ x)) ∘ w
def Equation2794 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ y)) ∘ w
def Equation2798 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ z)) ∘ w
def Equation2799 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ x
def Equation2800 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ y
def Equation2801 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ z
def Equation2802 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ w
def Equation2807 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ x)) ∘ w
def Equation2811 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ y)) ∘ w
def Equation2815 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ z)) ∘ w
def Equation2816 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ w)) ∘ x
def Equation2817 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ w)) ∘ y
def Equation2818 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ w)) ∘ z
def Equation2819 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ w)) ∘ w
def Equation2821 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ x)) ∘ x
def Equation2822 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ x)) ∘ y
def Equation2823 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ x)) ∘ z
def Equation2824 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ x)) ∘ w
def Equation2826 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ y)) ∘ x
def Equation2827 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ y)) ∘ y
def Equation2828 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ y)) ∘ z
def Equation2829 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ y)) ∘ w
def Equation2831 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ z)) ∘ x
def Equation2832 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ z)) ∘ y
def Equation2833 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ z)) ∘ z
def Equation2834 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ z)) ∘ w
def Equation2836 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ w)) ∘ x
def Equation2837 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ w)) ∘ y
def Equation2838 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ w)) ∘ z
def Equation2839 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ w)) ∘ w
def Equation2853 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (x ∘ y)) ∘ x) ∘ y
def Equation2861 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (x ∘ y)) ∘ z) ∘ w
def Equation2863 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (y ∘ x)) ∘ x) ∘ y
def Equation2865 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (y ∘ x)) ∘ y) ∘ x
def Equation2866 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (y ∘ x)) ∘ y) ∘ y
def Equation2871 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ x)) ∘ z) ∘ w
def Equation2873 (G: Type*) [Magma G] := ∀ x y : G, x = ((x ∘ (y ∘ y)) ∘ x) ∘ y
def Equation2881 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ y)) ∘ z) ∘ w
def Equation2885 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ x) ∘ w
def Equation2889 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ y) ∘ w
def Equation2893 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ z) ∘ w
def Equation2894 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ x
def Equation2895 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ y
def Equation2896 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ z
def Equation2897 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ w
def Equation2900 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ x)) ∘ x) ∘ y
def Equation2902 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ x)) ∘ y) ∘ x
def Equation2903 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ x)) ∘ y) ∘ y
def Equation2908 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ x)) ∘ z) ∘ w
def Equation2909 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ y)) ∘ x) ∘ x
def Equation2910 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ y)) ∘ x) ∘ y
def Equation2912 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ y)) ∘ y) ∘ x
def Equation2913 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ y)) ∘ y) ∘ y
def Equation2918 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ y)) ∘ z) ∘ w
def Equation2922 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ x) ∘ w
def Equation2926 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ y) ∘ w
def Equation2930 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ z) ∘ w
def Equation2931 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ w) ∘ x
def Equation2932 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ w) ∘ y
def Equation2933 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ w) ∘ z
def Equation2934 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ w) ∘ w
def Equation2937 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (y ∘ x)) ∘ x) ∘ y
def Equation2939 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (y ∘ x)) ∘ y) ∘ x
def Equation2940 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (y ∘ x)) ∘ y) ∘ y
def Equation2945 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ x)) ∘ z) ∘ w
def Equation2947 (G: Type*) [Magma G] := ∀ x y : G, x = ((y ∘ (y ∘ y)) ∘ x) ∘ y
def Equation2955 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ y)) ∘ z) ∘ w
def Equation2959 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ x) ∘ w
def Equation2963 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ y) ∘ w
def Equation2967 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ z) ∘ w
def Equation2968 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ w) ∘ x
def Equation2969 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ w) ∘ y
def Equation2970 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ w) ∘ z
def Equation2971 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ w) ∘ w
def Equation2976 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ x) ∘ w
def Equation2980 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ y) ∘ w
def Equation2984 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ z) ∘ w
def Equation2985 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ x
def Equation2986 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ y
def Equation2987 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ z
def Equation2988 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ w
def Equation2993 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ x) ∘ w
def Equation2997 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ y) ∘ w
def Equation3001 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ z) ∘ w
def Equation3002 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ x
def Equation3003 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ y
def Equation3004 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ z
def Equation3005 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ w
def Equation3010 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ x) ∘ w
def Equation3014 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ y) ∘ w
def Equation3018 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ z) ∘ w
def Equation3019 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ w) ∘ x
def Equation3020 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ w) ∘ y
def Equation3021 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ w) ∘ z
def Equation3022 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ w) ∘ w
def Equation3024 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ x) ∘ x
def Equation3025 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ x) ∘ y
def Equation3026 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ x) ∘ z
def Equation3027 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ x) ∘ w
def Equation3029 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ y) ∘ x
def Equation3030 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ y) ∘ y
def Equation3031 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ y) ∘ z
def Equation3032 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ y) ∘ w
def Equation3034 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ z) ∘ x
def Equation3035 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ z) ∘ y
def Equation3036 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ z) ∘ z
def Equation3037 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ z) ∘ w
def Equation3039 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ w) ∘ x
def Equation3040 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ w) ∘ y
def Equation3041 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ w) ∘ z
def Equation3042 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ w) ∘ w
def Equation3056 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ x) ∘ y) ∘ x) ∘ y
def Equation3064 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ x) ∘ y) ∘ z) ∘ w
def Equation3066 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ y) ∘ x) ∘ x) ∘ y
def Equation3068 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ y) ∘ x) ∘ y) ∘ x
def Equation3069 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ y) ∘ x) ∘ y) ∘ y
def Equation3074 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ x) ∘ z) ∘ w
def Equation3076 (G: Type*) [Magma G] := ∀ x y : G, x = (((x ∘ y) ∘ y) ∘ x) ∘ y
def Equation3084 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ y) ∘ z) ∘ w
def Equation3088 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ x) ∘ w
def Equation3092 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ y) ∘ w
def Equation3096 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ z) ∘ w
def Equation3097 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ x
def Equation3098 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ y
def Equation3099 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ z
def Equation3100 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ w
def Equation3103 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ x) ∘ x) ∘ y
def Equation3105 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ x) ∘ y) ∘ x
def Equation3106 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ x) ∘ y) ∘ y
def Equation3111 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ x) ∘ z) ∘ w
def Equation3112 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ y) ∘ x) ∘ x
def Equation3113 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ y) ∘ x) ∘ y
def Equation3115 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ y) ∘ y) ∘ x
def Equation3116 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ y) ∘ y) ∘ y
def Equation3121 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ y) ∘ z) ∘ w
def Equation3125 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ x) ∘ w
def Equation3129 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ y) ∘ w
def Equation3133 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ z) ∘ w
def Equation3134 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ w) ∘ x
def Equation3135 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ w) ∘ y
def Equation3136 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ w) ∘ z
def Equation3137 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ w) ∘ w
def Equation3140 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ y) ∘ x) ∘ x) ∘ y
def Equation3142 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ y) ∘ x) ∘ y) ∘ x
def Equation3143 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ y) ∘ x) ∘ y) ∘ y
def Equation3148 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ x) ∘ z) ∘ w
def Equation3150 (G: Type*) [Magma G] := ∀ x y : G, x = (((y ∘ y) ∘ y) ∘ x) ∘ y
def Equation3158 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ y) ∘ z) ∘ w
def Equation3162 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ x) ∘ w
def Equation3166 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ y) ∘ w
def Equation3170 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ z) ∘ w
def Equation3171 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ w) ∘ x
def Equation3172 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ w) ∘ y
def Equation3173 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ w) ∘ z
def Equation3174 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ w) ∘ w
def Equation3179 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ x) ∘ w
def Equation3183 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ y) ∘ w
def Equation3187 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ z) ∘ w
def Equation3188 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ x
def Equation3189 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ y
def Equation3190 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ z
def Equation3191 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ w
def Equation3196 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ x) ∘ w
def Equation3200 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ y) ∘ w
def Equation3204 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ z) ∘ w
def Equation3205 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ x
def Equation3206 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ y
def Equation3207 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ z
def Equation3208 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ w
def Equation3213 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ x) ∘ w
def Equation3217 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ y) ∘ w
def Equation3221 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ z) ∘ w
def Equation3222 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ w) ∘ x
def Equation3223 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ w) ∘ y
def Equation3224 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ w) ∘ z
def Equation3225 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ w) ∘ w
def Equation3227 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ x) ∘ x
def Equation3228 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ x) ∘ y
def Equation3229 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ x) ∘ z
def Equation3230 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ x) ∘ w
def Equation3232 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ y) ∘ x
def Equation3233 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ y) ∘ y
def Equation3234 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ y) ∘ z
def Equation3235 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ y) ∘ w
def Equation3237 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ z) ∘ x
def Equation3238 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ z) ∘ y
def Equation3239 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ z) ∘ z
def Equation3240 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ z) ∘ w
def Equation3242 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ w) ∘ x
def Equation3243 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ w) ∘ y
def Equation3244 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ w) ∘ z
def Equation3245 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ w) ∘ w
def Equation3259 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ (y ∘ (x ∘ y))
def Equation3267 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = x ∘ (y ∘ (z ∘ w))
def Equation3269 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (x ∘ (x ∘ y))
def Equation3271 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (x ∘ (y ∘ x))
def Equation3272 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (x ∘ (y ∘ y))
def Equation3277 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (x ∘ (z ∘ w))
def Equation3279 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (y ∘ (x ∘ y))
def Equation3287 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (y ∘ (z ∘ w))
def Equation3291 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (x ∘ w))
def Equation3295 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (y ∘ w))
def Equation3299 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (z ∘ w))
def Equation3300 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (w ∘ x))
def Equation3301 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (w ∘ y))
def Equation3302 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (w ∘ z))
def Equation3303 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (w ∘ w))
def Equation3306 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (x ∘ (x ∘ y))
def Equation3308 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (x ∘ (y ∘ x))
def Equation3309 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (x ∘ (y ∘ y))
def Equation3314 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (x ∘ (z ∘ w))
def Equation3315 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (y ∘ (x ∘ x))
def Equation3316 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (y ∘ (x ∘ y))
def Equation3318 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (y ∘ (y ∘ x))
def Equation3319 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (y ∘ (y ∘ y))
def Equation3324 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (y ∘ (z ∘ w))
def Equation3328 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (x ∘ w))
def Equation3332 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (y ∘ w))
def Equation3336 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (z ∘ w))
def Equation3337 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (w ∘ x))
def Equation3338 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (w ∘ y))
def Equation3339 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (w ∘ z))
def Equation3340 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (w ∘ w))
def Equation3343 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (x ∘ (x ∘ y))
def Equation3345 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (x ∘ (y ∘ x))
def Equation3346 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (x ∘ (y ∘ y))
def Equation3351 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (x ∘ (z ∘ w))
def Equation3353 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (y ∘ (x ∘ y))
def Equation3361 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (y ∘ (z ∘ w))
def Equation3365 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (x ∘ w))
def Equation3369 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (y ∘ w))
def Equation3373 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (z ∘ w))
def Equation3374 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (w ∘ x))
def Equation3375 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (w ∘ y))
def Equation3376 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (w ∘ z))
def Equation3377 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (w ∘ w))
def Equation3382 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (x ∘ w))
def Equation3386 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (y ∘ w))
def Equation3390 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (z ∘ w))
def Equation3391 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (w ∘ x))
def Equation3392 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (w ∘ y))
def Equation3393 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (w ∘ z))
def Equation3394 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (w ∘ w))
def Equation3399 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (x ∘ w))
def Equation3403 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (y ∘ w))
def Equation3407 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (z ∘ w))
def Equation3408 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (w ∘ x))
def Equation3409 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (w ∘ y))
def Equation3410 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (w ∘ z))
def Equation3411 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (w ∘ w))
def Equation3416 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (x ∘ w))
def Equation3420 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (y ∘ w))
def Equation3424 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (z ∘ w))
def Equation3425 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (w ∘ x))
def Equation3426 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (w ∘ y))
def Equation3427 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (w ∘ z))
def Equation3428 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (w ∘ w))
def Equation3430 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (x ∘ x))
def Equation3431 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (x ∘ y))
def Equation3432 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (x ∘ z))
def Equation3433 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (x ∘ w))
def Equation3435 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (y ∘ x))
def Equation3436 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (y ∘ y))
def Equation3437 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (y ∘ z))
def Equation3438 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (y ∘ w))
def Equation3440 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (z ∘ x))
def Equation3441 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (z ∘ y))
def Equation3442 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (z ∘ z))
def Equation3443 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (z ∘ w))
def Equation3445 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (w ∘ x))
def Equation3446 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (w ∘ y))
def Equation3447 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (w ∘ z))
def Equation3448 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (w ∘ w))
def Equation3462 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = x ∘ ((y ∘ x) ∘ y)
def Equation3470 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = x ∘ ((y ∘ z) ∘ w)
def Equation3472 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ ((x ∘ x) ∘ y)
def Equation3474 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ ((x ∘ y) ∘ x)
def Equation3475 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ ((x ∘ y) ∘ y)
def Equation3480 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((x ∘ z) ∘ w)
def Equation3482 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = y ∘ ((y ∘ x) ∘ y)
def Equation3490 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((y ∘ z) ∘ w)
def Equation3494 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ x) ∘ w)
def Equation3498 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ y) ∘ w)
def Equation3502 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ z) ∘ w)
def Equation3503 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ w) ∘ x)
def Equation3504 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ w) ∘ y)
def Equation3505 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ w) ∘ z)
def Equation3506 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ w) ∘ w)
def Equation3509 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((x ∘ x) ∘ y)
def Equation3511 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((x ∘ y) ∘ x)
def Equation3512 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((x ∘ y) ∘ y)
def Equation3517 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((x ∘ z) ∘ w)
def Equation3518 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((y ∘ x) ∘ x)
def Equation3519 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((y ∘ x) ∘ y)
def Equation3521 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((y ∘ y) ∘ x)
def Equation3522 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((y ∘ y) ∘ y)
def Equation3527 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((y ∘ z) ∘ w)
def Equation3531 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ x) ∘ w)
def Equation3535 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ y) ∘ w)
def Equation3539 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ z) ∘ w)
def Equation3540 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ w) ∘ x)
def Equation3541 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ w) ∘ y)
def Equation3542 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ w) ∘ z)
def Equation3543 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ w) ∘ w)
def Equation3546 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ ((x ∘ x) ∘ y)
def Equation3548 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ ((x ∘ y) ∘ x)
def Equation3549 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ ((x ∘ y) ∘ y)
def Equation3554 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((x ∘ z) ∘ w)
def Equation3556 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = y ∘ ((y ∘ x) ∘ y)
def Equation3564 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((y ∘ z) ∘ w)
def Equation3568 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ x) ∘ w)
def Equation3572 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ y) ∘ w)
def Equation3576 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ z) ∘ w)
def Equation3577 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ w) ∘ x)
def Equation3578 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ w) ∘ y)
def Equation3579 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ w) ∘ z)
def Equation3580 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ w) ∘ w)
def Equation3585 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ x) ∘ w)
def Equation3589 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ y) ∘ w)
def Equation3593 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ z) ∘ w)
def Equation3594 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ w) ∘ x)
def Equation3595 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ w) ∘ y)
def Equation3596 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ w) ∘ z)
def Equation3597 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ w) ∘ w)
def Equation3602 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ x) ∘ w)
def Equation3606 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ y) ∘ w)
def Equation3610 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ z) ∘ w)
def Equation3611 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ w) ∘ x)
def Equation3612 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ w) ∘ y)
def Equation3613 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ w) ∘ z)
def Equation3614 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ w) ∘ w)
def Equation3619 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ x) ∘ w)
def Equation3623 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ y) ∘ w)
def Equation3627 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ z) ∘ w)
def Equation3628 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ w) ∘ x)
def Equation3629 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ w) ∘ y)
def Equation3630 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ w) ∘ z)
def Equation3631 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ w) ∘ w)
def Equation3633 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ x) ∘ x)
def Equation3634 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ x) ∘ y)
def Equation3635 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ x) ∘ z)
def Equation3636 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ x) ∘ w)
def Equation3638 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ y) ∘ x)
def Equation3639 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ y) ∘ y)
def Equation3640 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ y) ∘ z)
def Equation3641 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ y) ∘ w)
def Equation3643 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ z) ∘ x)
def Equation3644 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ z) ∘ y)
def Equation3645 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ z) ∘ z)
def Equation3646 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ z) ∘ w)
def Equation3648 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ w) ∘ x)
def Equation3649 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ w) ∘ y)
def Equation3650 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ w) ∘ z)
def Equation3651 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ w) ∘ w)
def Equation3665 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ y) ∘ (x ∘ y)
def Equation3673 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (x ∘ y) ∘ (z ∘ w)
def Equation3675 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ x) ∘ (x ∘ y)
def Equation3677 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ x) ∘ (y ∘ x)
def Equation3678 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ x) ∘ (y ∘ y)
def Equation3683 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ x) ∘ (z ∘ w)
def Equation3685 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ y) ∘ (x ∘ y)
def Equation3693 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ y) ∘ (z ∘ w)
def Equation3697 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (x ∘ w)
def Equation3701 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (y ∘ w)
def Equation3705 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (z ∘ w)
def Equation3706 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (w ∘ x)
def Equation3707 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (w ∘ y)
def Equation3708 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (w ∘ z)
def Equation3709 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (w ∘ w)
def Equation3712 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ x) ∘ (x ∘ y)
def Equation3714 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ x) ∘ (y ∘ x)
def Equation3715 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ x) ∘ (y ∘ y)
def Equation3720 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ x) ∘ (z ∘ w)
def Equation3721 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ y) ∘ (x ∘ x)
def Equation3722 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ y) ∘ (x ∘ y)
def Equation3724 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ y) ∘ (y ∘ x)
def Equation3725 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ y) ∘ (y ∘ y)
def Equation3730 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ y) ∘ (z ∘ w)
def Equation3734 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (x ∘ w)
def Equation3738 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (y ∘ w)
def Equation3742 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (z ∘ w)
def Equation3743 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (w ∘ x)
def Equation3744 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (w ∘ y)
def Equation3745 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (w ∘ z)
def Equation3746 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (w ∘ w)
def Equation3749 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ x) ∘ (x ∘ y)
def Equation3751 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ x) ∘ (y ∘ x)
def Equation3752 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ x) ∘ (y ∘ y)
def Equation3757 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ x) ∘ (z ∘ w)
def Equation3759 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ y) ∘ (x ∘ y)
def Equation3767 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ y) ∘ (z ∘ w)
def Equation3771 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (x ∘ w)
def Equation3775 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (y ∘ w)
def Equation3779 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (z ∘ w)
def Equation3780 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (w ∘ x)
def Equation3781 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (w ∘ y)
def Equation3782 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (w ∘ z)
def Equation3783 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (w ∘ w)
def Equation3788 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (x ∘ w)
def Equation3792 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (y ∘ w)
def Equation3796 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (z ∘ w)
def Equation3797 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (w ∘ x)
def Equation3798 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (w ∘ y)
def Equation3799 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (w ∘ z)
def Equation3800 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (w ∘ w)
def Equation3805 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (x ∘ w)
def Equation3809 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (y ∘ w)
def Equation3813 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (z ∘ w)
def Equation3814 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (w ∘ x)
def Equation3815 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (w ∘ y)
def Equation3816 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (w ∘ z)
def Equation3817 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (w ∘ w)
def Equation3822 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (x ∘ w)
def Equation3826 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (y ∘ w)
def Equation3830 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (z ∘ w)
def Equation3831 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (w ∘ x)
def Equation3832 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (w ∘ y)
def Equation3833 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (w ∘ z)
def Equation3834 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (w ∘ w)
def Equation3836 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (x ∘ x)
def Equation3837 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (x ∘ y)
def Equation3838 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (x ∘ z)
def Equation3839 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (x ∘ w)
def Equation3841 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (y ∘ x)
def Equation3842 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (y ∘ y)
def Equation3843 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (y ∘ z)
def Equation3844 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (y ∘ w)
def Equation3846 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (z ∘ x)
def Equation3847 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (z ∘ y)
def Equation3848 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (z ∘ z)
def Equation3849 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (z ∘ w)
def Equation3851 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (w ∘ x)
def Equation3852 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (w ∘ y)
def Equation3853 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (w ∘ z)
def Equation3854 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (w ∘ w)
def Equation3868 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ (y ∘ x)) ∘ y
def Equation3876 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (x ∘ (y ∘ z)) ∘ w
def Equation3878 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ (x ∘ x)) ∘ y
def Equation3880 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ (x ∘ y)) ∘ x
def Equation3881 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ (x ∘ y)) ∘ y
def Equation3886 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (x ∘ z)) ∘ w
def Equation3888 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ (y ∘ x)) ∘ y
def Equation3896 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (y ∘ z)) ∘ w
def Equation3900 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ x)) ∘ w
def Equation3904 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ y)) ∘ w
def Equation3908 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ z)) ∘ w
def Equation3909 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ w)) ∘ x
def Equation3910 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ w)) ∘ y
def Equation3911 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ w)) ∘ z
def Equation3912 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ w)) ∘ w
def Equation3915 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (x ∘ x)) ∘ y
def Equation3917 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (x ∘ y)) ∘ x
def Equation3918 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (x ∘ y)) ∘ y
def Equation3923 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (x ∘ z)) ∘ w
def Equation3924 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (y ∘ x)) ∘ x
def Equation3925 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (y ∘ x)) ∘ y
def Equation3927 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (y ∘ y)) ∘ x
def Equation3928 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (y ∘ y)) ∘ y
def Equation3933 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (y ∘ z)) ∘ w
def Equation3937 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ x)) ∘ w
def Equation3941 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ y)) ∘ w
def Equation3945 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ z)) ∘ w
def Equation3946 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ w)) ∘ x
def Equation3947 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ w)) ∘ y
def Equation3948 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ w)) ∘ z
def Equation3949 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ w)) ∘ w
def Equation3952 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ (x ∘ x)) ∘ y
def Equation3954 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ (x ∘ y)) ∘ x
def Equation3955 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ (x ∘ y)) ∘ y
def Equation3960 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (x ∘ z)) ∘ w
def Equation3962 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ (y ∘ x)) ∘ y
def Equation3970 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (y ∘ z)) ∘ w
def Equation3974 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ x)) ∘ w
def Equation3978 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ y)) ∘ w
def Equation3982 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ z)) ∘ w
def Equation3983 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ w)) ∘ x
def Equation3984 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ w)) ∘ y
def Equation3985 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ w)) ∘ z
def Equation3986 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ w)) ∘ w
def Equation3991 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ x)) ∘ w
def Equation3995 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ y)) ∘ w
def Equation3999 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ z)) ∘ w
def Equation4000 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ w)) ∘ x
def Equation4001 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ w)) ∘ y
def Equation4002 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ w)) ∘ z
def Equation4003 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ w)) ∘ w
def Equation4008 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ x)) ∘ w
def Equation4012 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ y)) ∘ w
def Equation4016 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ z)) ∘ w
def Equation4017 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ w)) ∘ x
def Equation4018 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ w)) ∘ y
def Equation4019 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ w)) ∘ z
def Equation4020 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ w)) ∘ w
def Equation4025 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ x)) ∘ w
def Equation4029 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ y)) ∘ w
def Equation4033 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ z)) ∘ w
def Equation4034 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ w)) ∘ x
def Equation4035 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ w)) ∘ y
def Equation4036 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ w)) ∘ z
def Equation4037 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ w)) ∘ w
def Equation4039 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ x)) ∘ x
def Equation4040 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ x)) ∘ y
def Equation4041 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ x)) ∘ z
def Equation4042 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ x)) ∘ w
def Equation4044 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ y)) ∘ x
def Equation4045 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ y)) ∘ y
def Equation4046 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ y)) ∘ z
def Equation4047 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ y)) ∘ w
def Equation4049 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ z)) ∘ x
def Equation4050 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ z)) ∘ y
def Equation4051 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ z)) ∘ z
def Equation4052 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ z)) ∘ w
def Equation4054 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ w)) ∘ x
def Equation4055 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ w)) ∘ y
def Equation4056 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ w)) ∘ z
def Equation4057 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ w)) ∘ w
def Equation4071 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((x ∘ y) ∘ x) ∘ y
def Equation4079 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((x ∘ y) ∘ z) ∘ w
def Equation4081 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((y ∘ x) ∘ x) ∘ y
def Equation4083 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((y ∘ x) ∘ y) ∘ x
def Equation4084 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((y ∘ x) ∘ y) ∘ y
def Equation4089 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ x) ∘ z) ∘ w
def Equation4091 (G: Type*) [Magma G] := ∀ x y : G, x ∘ x = ((y ∘ y) ∘ x) ∘ y
def Equation4099 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ y) ∘ z) ∘ w
def Equation4103 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ x) ∘ w
def Equation4107 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ y) ∘ w
def Equation4111 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ z) ∘ w
def Equation4112 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ w) ∘ x
def Equation4113 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ w) ∘ y
def Equation4114 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ w) ∘ z
def Equation4115 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ w) ∘ w
def Equation4118 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ x) ∘ x) ∘ y
def Equation4120 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ x) ∘ y) ∘ x
def Equation4121 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ x) ∘ y) ∘ y
def Equation4126 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ x) ∘ z) ∘ w
def Equation4127 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ y) ∘ x) ∘ x
def Equation4128 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ y) ∘ x) ∘ y
def Equation4130 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ y) ∘ y) ∘ x
def Equation4131 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ y) ∘ y) ∘ y
def Equation4136 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ y) ∘ z) ∘ w
def Equation4140 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ x) ∘ w
def Equation4144 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ y) ∘ w
def Equation4148 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ z) ∘ w
def Equation4149 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ w) ∘ x
def Equation4150 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ w) ∘ y
def Equation4151 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ w) ∘ z
def Equation4152 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ w) ∘ w
def Equation4155 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((y ∘ x) ∘ x) ∘ y
def Equation4157 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((y ∘ x) ∘ y) ∘ x
def Equation4158 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((y ∘ x) ∘ y) ∘ y
def Equation4163 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ x) ∘ z) ∘ w
def Equation4165 (G: Type*) [Magma G] := ∀ x y : G, x ∘ y = ((y ∘ y) ∘ x) ∘ y
def Equation4173 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ y) ∘ z) ∘ w
def Equation4177 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ x) ∘ w
def Equation4181 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ y) ∘ w
def Equation4185 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ z) ∘ w
def Equation4186 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ w) ∘ x
def Equation4187 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ w) ∘ y
def Equation4188 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ w) ∘ z
def Equation4189 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ w) ∘ w
def Equation4194 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ x) ∘ w
def Equation4198 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ y) ∘ w
def Equation4202 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ z) ∘ w
def Equation4203 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ w) ∘ x
def Equation4204 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ w) ∘ y
def Equation4205 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ w) ∘ z
def Equation4206 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ w) ∘ w
def Equation4211 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ x) ∘ w
def Equation4215 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ y) ∘ w
def Equation4219 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ z) ∘ w
def Equation4220 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ w) ∘ x
def Equation4221 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ w) ∘ y
def Equation4222 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ w) ∘ z
def Equation4223 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ w) ∘ w
def Equation4228 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ x) ∘ w
def Equation4232 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ y) ∘ w
def Equation4236 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ z) ∘ w
def Equation4237 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ w) ∘ x
def Equation4238 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ w) ∘ y
def Equation4239 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ w) ∘ z
def Equation4240 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ w) ∘ w
def Equation4242 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ x) ∘ x
def Equation4243 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ x) ∘ y
def Equation4244 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ x) ∘ z
def Equation4245 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ x) ∘ w
def Equation4247 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ y) ∘ x
def Equation4248 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ y) ∘ y
def Equation4249 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ y) ∘ z
def Equation4250 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ y) ∘ w
def Equation4252 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ z) ∘ x
def Equation4253 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ z) ∘ y
def Equation4254 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ z) ∘ z
def Equation4255 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ z) ∘ w
def Equation4257 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ w) ∘ x
def Equation4258 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ w) ∘ y
def Equation4259 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ w) ∘ z
def Equation4260 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ w) ∘ w
def Equation4273 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = y ∘ (x ∘ y)
def Equation4281 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ x) = y ∘ (z ∘ w)
def Equation4283 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = x ∘ (y ∘ x)
def Equation4284 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = x ∘ (y ∘ y)
def Equation4291 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = y ∘ (x ∘ y)
def Equation4298 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = y ∘ (z ∘ w)
def Equation4306 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (y ∘ w)
def Equation4309 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (w ∘ x)
def Equation4310 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (w ∘ y)
def Equation4311 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (w ∘ z)
def Equation4312 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (w ∘ w)
def Equation4314 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = x ∘ (y ∘ y)
def Equation4321 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = y ∘ (x ∘ y)
def Equation4326 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = y ∘ (z ∘ w)
def Equation4333 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = z ∘ (y ∘ w)
def Equation4335 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = z ∘ (w ∘ y)
def Equation4337 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = z ∘ (w ∘ w)
def Equation4357 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = x ∘ (y ∘ w)
def Equation4363 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = y ∘ (x ∘ w)
def Equation4365 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = y ∘ (z ∘ w)
def Equation4370 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = z ∘ (y ∘ w)
def Equation4372 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = z ∘ (w ∘ y)
def Equation4376 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = w ∘ (z ∘ y)
def Equation4386 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = (y ∘ x) ∘ y
def Equation4394 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ x) = (y ∘ z) ∘ w
def Equation4396 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = (x ∘ x) ∘ y
def Equation4398 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = (x ∘ y) ∘ x
def Equation4399 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = (x ∘ y) ∘ y
def Equation4404 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (x ∘ z) ∘ w
def Equation4406 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = (y ∘ x) ∘ y
def Equation4414 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (y ∘ z) ∘ w
def Equation4418 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ x) ∘ w
def Equation4422 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ y) ∘ w
def Equation4426 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ z) ∘ w
def Equation4427 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ w) ∘ x
def Equation4428 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ w) ∘ y
def Equation4429 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ w) ∘ z
def Equation4430 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ w) ∘ w
def Equation4433 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (x ∘ x) ∘ y
def Equation4435 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (x ∘ y) ∘ x
def Equation4436 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (x ∘ y) ∘ y
def Equation4441 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (x ∘ z) ∘ w
def Equation4442 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (y ∘ x) ∘ x
def Equation4443 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (y ∘ x) ∘ y
def Equation4445 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (y ∘ y) ∘ x
def Equation4446 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (y ∘ y) ∘ y
def Equation4451 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (y ∘ z) ∘ w
def Equation4455 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ x) ∘ w
def Equation4459 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ y) ∘ w
def Equation4463 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ z) ∘ w
def Equation4464 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ w) ∘ x
def Equation4465 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ w) ∘ y
def Equation4466 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ w) ∘ z
def Equation4467 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ w) ∘ w
def Equation4470 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = (x ∘ x) ∘ y
def Equation4472 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = (x ∘ y) ∘ x
def Equation4473 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = (x ∘ y) ∘ y
def Equation4478 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (x ∘ z) ∘ w
def Equation4480 (G: Type*) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = (y ∘ x) ∘ y
def Equation4488 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (y ∘ z) ∘ w
def Equation4492 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ x) ∘ w
def Equation4496 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ y) ∘ w
def Equation4500 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ z) ∘ w
def Equation4501 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ w) ∘ x
def Equation4502 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ w) ∘ y
def Equation4503 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ w) ∘ z
def Equation4504 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ w) ∘ w
def Equation4509 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ x) ∘ w
def Equation4513 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ y) ∘ w
def Equation4517 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ z) ∘ w
def Equation4518 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ w) ∘ x
def Equation4519 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ w) ∘ y
def Equation4520 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ w) ∘ z
def Equation4521 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ w) ∘ w
def Equation4526 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ x) ∘ w
def Equation4530 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ y) ∘ w
def Equation4534 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ z) ∘ w
def Equation4535 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ w) ∘ x
def Equation4536 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ w) ∘ y
def Equation4537 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ w) ∘ z
def Equation4538 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ w) ∘ w
def Equation4543 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ x) ∘ w
def Equation4547 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ y) ∘ w
def Equation4551 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ z) ∘ w
def Equation4552 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ w) ∘ x
def Equation4553 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ w) ∘ y
def Equation4554 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ w) ∘ z
def Equation4555 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ w) ∘ w
def Equation4557 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ x) ∘ x
def Equation4558 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ x) ∘ y
def Equation4559 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ x) ∘ z
def Equation4560 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ x) ∘ w
def Equation4562 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ y) ∘ x
def Equation4563 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ y) ∘ y
def Equation4564 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ y) ∘ z
def Equation4565 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ y) ∘ w
def Equation4567 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ z) ∘ x
def Equation4568 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ z) ∘ y
def Equation4569 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ z) ∘ z
def Equation4570 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ z) ∘ w
def Equation4572 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ w) ∘ x
def Equation4573 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ w) ∘ y
def Equation4574 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ w) ∘ z
def Equation4575 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ w) ∘ w
def Equation4588 (G: Type*) [Magma G] := ∀ x y : G, (x ∘ x) ∘ x = (y ∘ x) ∘ y
def Equation4596 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ x = (y ∘ z) ∘ w
def Equation4598 (G: Type*) [Magma G] := ∀ x y : G, (x ∘ x) ∘ y = (x ∘ y) ∘ x
def Equation4599 (G: Type*) [Magma G] := ∀ x y : G, (x ∘ x) ∘ y = (x ∘ y) ∘ y
def Equation4606 (G: Type*) [Magma G] := ∀ x y : G, (x ∘ x) ∘ y = (y ∘ x) ∘ y
def Equation4613 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (y ∘ z) ∘ w
def Equation4621 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ y) ∘ w
def Equation4624 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ w) ∘ x
def Equation4625 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ w) ∘ y
def Equation4626 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ w) ∘ z
def Equation4627 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ w) ∘ w
def Equation4629 (G: Type*) [Magma G] := ∀ x y : G, (x ∘ y) ∘ x = (x ∘ y) ∘ y
def Equation4636 (G: Type*) [Magma G] := ∀ x y : G, (x ∘ y) ∘ x = (y ∘ x) ∘ y
def Equation4641 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ x = (y ∘ z) ∘ w
def Equation4648 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ x = (z ∘ y) ∘ w
def Equation4650 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ x = (z ∘ w) ∘ y
def Equation4652 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ x = (z ∘ w) ∘ w
def Equation4672 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (x ∘ y) ∘ w
def Equation4678 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (y ∘ x) ∘ w
def Equation4680 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (y ∘ z) ∘ w
def Equation4685 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (z ∘ y) ∘ w
def Equation4687 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (z ∘ w) ∘ y
def Equation4691 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (w ∘ z) ∘ y
theorem Equation22_implies_Equation14 (G : Type*) [Magma G] (h : Equation22 G) : Equation14 G := λ x y => h x y x y
theorem Equation37_implies_Equation29 (G : Type*) [Magma G] (h : Equation37 G) : Equation29 G := λ x y => h x y x y
theorem Equation61_implies_Equation53 (G : Type*) [Magma G] (h : Equation61 G) : Equation53 G := λ x y => h x y x y
theorem Equation71_implies_Equation63 (G : Type*) [Magma G] (h : Equation71 G) : Equation63 G := λ x y => h x y x y
theorem Equation81_implies_Equation73 (G : Type*) [Magma G] (h : Equation81 G) : Equation73 G := λ x y => h x y x y
theorem Equation85_implies_Equation63 (G : Type*) [Magma G] (h : Equation85 G) : Equation63 G := λ x y => h x y x y
theorem Equation89_implies_Equation66 (G : Type*) [Magma G] (h : Equation89 G) : Equation66 G := λ x y => h x y x y
theorem Equation93_implies_Equation63 (G : Type*) [Magma G] (h : Equation93 G) : Equation63 G := λ x y => h x y x y
theorem Equation94_implies_Equation65 (G : Type*) [Magma G] (h : Equation94 G) : Equation65 G := λ x y => h x y x y
theorem Equation95_implies_Equation66 (G : Type*) [Magma G] (h : Equation95 G) : Equation66 G := λ x y => h x y x y
theorem Equation96_implies_Equation65 (G : Type*) [Magma G] (h : Equation96 G) : Equation65 G := λ x y => h x y x y
theorem Equation97_implies_Equation66 (G : Type*) [Magma G] (h : Equation97 G) : Equation66 G := λ x y => h x y x y
theorem Equation113_implies_Equation105 (G : Type*) [Magma G] (h : Equation113 G) : Equation105 G := λ x y => h x y x y
theorem Equation123_implies_Equation115 (G : Type*) [Magma G] (h : Equation123 G) : Equation115 G := λ x y => h x y x y
theorem Equation133_implies_Equation125 (G : Type*) [Magma G] (h : Equation133 G) : Equation125 G := λ x y => h x y x y
theorem Equation137_implies_Equation115 (G : Type*) [Magma G] (h : Equation137 G) : Equation115 G := λ x y => h x y x y
theorem Equation141_implies_Equation118 (G : Type*) [Magma G] (h : Equation141 G) : Equation118 G := λ x y => h x y x y
theorem Equation145_implies_Equation115 (G : Type*) [Magma G] (h : Equation145 G) : Equation115 G := λ x y => h x y x y
theorem Equation146_implies_Equation117 (G : Type*) [Magma G] (h : Equation146 G) : Equation117 G := λ x y => h x y x y
theorem Equation147_implies_Equation118 (G : Type*) [Magma G] (h : Equation147 G) : Equation118 G := λ x y => h x y x y
theorem Equation148_implies_Equation117 (G : Type*) [Magma G] (h : Equation148 G) : Equation117 G := λ x y => h x y x y
theorem Equation149_implies_Equation118 (G : Type*) [Magma G] (h : Equation149 G) : Equation118 G := λ x y => h x y x y
theorem Equation165_implies_Equation157 (G : Type*) [Magma G] (h : Equation165 G) : Equation157 G := λ x y => h x y x y
theorem Equation175_implies_Equation167 (G : Type*) [Magma G] (h : Equation175 G) : Equation167 G := λ x y => h x y x y
theorem Equation185_implies_Equation177 (G : Type*) [Magma G] (h : Equation185 G) : Equation177 G := λ x y => h x y x y
theorem Equation189_implies_Equation167 (G : Type*) [Magma G] (h : Equation189 G) : Equation167 G := λ x y => h x y x y
theorem Equation193_implies_Equation170 (G : Type*) [Magma G] (h : Equation193 G) : Equation170 G := λ x y => h x y x y
theorem Equation197_implies_Equation167 (G : Type*) [Magma G] (h : Equation197 G) : Equation167 G := λ x y => h x y x y
theorem Equation198_implies_Equation169 (G : Type*) [Magma G] (h : Equation198 G) : Equation169 G := λ x y => h x y x y
theorem Equation199_implies_Equation170 (G : Type*) [Magma G] (h : Equation199 G) : Equation170 G := λ x y => h x y x y
theorem Equation200_implies_Equation169 (G : Type*) [Magma G] (h : Equation200 G) : Equation169 G := λ x y => h x y x y
theorem Equation201_implies_Equation170 (G : Type*) [Magma G] (h : Equation201 G) : Equation170 G := λ x y => h x y x y
theorem Equation217_implies_Equation209 (G : Type*) [Magma G] (h : Equation217 G) : Equation209 G := λ x y => h x y x y
theorem Equation227_implies_Equation219 (G : Type*) [Magma G] (h : Equation227 G) : Equation219 G := λ x y => h x y x y
theorem Equation237_implies_Equation229 (G : Type*) [Magma G] (h : Equation237 G) : Equation229 G := λ x y => h x y x y
theorem Equation241_implies_Equation219 (G : Type*) [Magma G] (h : Equation241 G) : Equation219 G := λ x y => h x y x y
theorem Equation245_implies_Equation222 (G : Type*) [Magma G] (h : Equation245 G) : Equation222 G := λ x y => h x y x y
theorem Equation249_implies_Equation219 (G : Type*) [Magma G] (h : Equation249 G) : Equation219 G := λ x y => h x y x y
theorem Equation250_implies_Equation221 (G : Type*) [Magma G] (h : Equation250 G) : Equation221 G := λ x y => h x y x y
theorem Equation251_implies_Equation222 (G : Type*) [Magma G] (h : Equation251 G) : Equation222 G := λ x y => h x y x y
theorem Equation252_implies_Equation221 (G : Type*) [Magma G] (h : Equation252 G) : Equation221 G := λ x y => h x y x y
theorem Equation253_implies_Equation222 (G : Type*) [Magma G] (h : Equation253 G) : Equation222 G := λ x y => h x y x y
theorem Equation269_implies_Equation261 (G : Type*) [Magma G] (h : Equation269 G) : Equation261 G := λ x y => h x y x y
theorem Equation279_implies_Equation271 (G : Type*) [Magma G] (h : Equation279 G) : Equation271 G := λ x y => h x y x y
theorem Equation289_implies_Equation281 (G : Type*) [Magma G] (h : Equation289 G) : Equation281 G := λ x y => h x y x y
theorem Equation293_implies_Equation271 (G : Type*) [Magma G] (h : Equation293 G) : Equation271 G := λ x y => h x y x y
theorem Equation297_implies_Equation274 (G : Type*) [Magma G] (h : Equation297 G) : Equation274 G := λ x y => h x y x y
theorem Equation301_implies_Equation271 (G : Type*) [Magma G] (h : Equation301 G) : Equation271 G := λ x y => h x y x y
theorem Equation302_implies_Equation273 (G : Type*) [Magma G] (h : Equation302 G) : Equation273 G := λ x y => h x y x y
theorem Equation303_implies_Equation274 (G : Type*) [Magma G] (h : Equation303 G) : Equation274 G := λ x y => h x y x y
theorem Equation304_implies_Equation273 (G : Type*) [Magma G] (h : Equation304 G) : Equation273 G := λ x y => h x y x y
theorem Equation305_implies_Equation274 (G : Type*) [Magma G] (h : Equation305 G) : Equation274 G := λ x y => h x y x y
theorem Equation321_implies_Equation313 (G : Type*) [Magma G] (h : Equation321 G) : Equation313 G := λ x y => h x y x y
theorem Equation331_implies_Equation323 (G : Type*) [Magma G] (h : Equation331 G) : Equation323 G := λ x y => h x y x y
theorem Equation341_implies_Equation333 (G : Type*) [Magma G] (h : Equation341 G) : Equation333 G := λ x y => h x y x y
theorem Equation345_implies_Equation323 (G : Type*) [Magma G] (h : Equation345 G) : Equation323 G := λ x y => h x y x y
theorem Equation349_implies_Equation326 (G : Type*) [Magma G] (h : Equation349 G) : Equation326 G := λ x y => h x y x y
theorem Equation353_implies_Equation323 (G : Type*) [Magma G] (h : Equation353 G) : Equation323 G := λ x y => h x y x y
theorem Equation354_implies_Equation325 (G : Type*) [Magma G] (h : Equation354 G) : Equation325 G := λ x y => h x y x y
theorem Equation355_implies_Equation326 (G : Type*) [Magma G] (h : Equation355 G) : Equation326 G := λ x y => h x y x y
theorem Equation356_implies_Equation325 (G : Type*) [Magma G] (h : Equation356 G) : Equation325 G := λ x y => h x y x y
theorem Equation357_implies_Equation326 (G : Type*) [Magma G] (h : Equation357 G) : Equation326 G := λ x y => h x y x y
theorem Equation373_implies_Equation365 (G : Type*) [Magma G] (h : Equation373 G) : Equation365 G := λ x y => h x y x y
theorem Equation383_implies_Equation375 (G : Type*) [Magma G] (h : Equation383 G) : Equation375 G := λ x y => h x y x y
theorem Equation393_implies_Equation385 (G : Type*) [Magma G] (h : Equation393 G) : Equation385 G := λ x y => h x y x y
theorem Equation397_implies_Equation375 (G : Type*) [Magma G] (h : Equation397 G) : Equation375 G := λ x y => h x y x y
theorem Equation401_implies_Equation378 (G : Type*) [Magma G] (h : Equation401 G) : Equation378 G := λ x y => h x y x y
theorem Equation405_implies_Equation375 (G : Type*) [Magma G] (h : Equation405 G) : Equation375 G := λ x y => h x y x y
theorem Equation406_implies_Equation377 (G : Type*) [Magma G] (h : Equation406 G) : Equation377 G := λ x y => h x y x y
theorem Equation407_implies_Equation378 (G : Type*) [Magma G] (h : Equation407 G) : Equation378 G := λ x y => h x y x y
theorem Equation408_implies_Equation377 (G : Type*) [Magma G] (h : Equation408 G) : Equation377 G := λ x y => h x y x y
theorem Equation409_implies_Equation378 (G : Type*) [Magma G] (h : Equation409 G) : Equation378 G := λ x y => h x y x y
theorem Equation425_implies_Equation417 (G : Type*) [Magma G] (h : Equation425 G) : Equation417 G := λ x y => h x y x y
theorem Equation435_implies_Equation427 (G : Type*) [Magma G] (h : Equation435 G) : Equation427 G := λ x y => h x y x y
theorem Equation445_implies_Equation437 (G : Type*) [Magma G] (h : Equation445 G) : Equation437 G := λ x y => h x y x y
theorem Equation449_implies_Equation427 (G : Type*) [Magma G] (h : Equation449 G) : Equation427 G := λ x y => h x y x y
theorem Equation453_implies_Equation430 (G : Type*) [Magma G] (h : Equation453 G) : Equation430 G := λ x y => h x y x y
theorem Equation457_implies_Equation427 (G : Type*) [Magma G] (h : Equation457 G) : Equation427 G := λ x y => h x y x y
theorem Equation458_implies_Equation429 (G : Type*) [Magma G] (h : Equation458 G) : Equation429 G := λ x y => h x y x y
theorem Equation459_implies_Equation430 (G : Type*) [Magma G] (h : Equation459 G) : Equation430 G := λ x y => h x y x y
theorem Equation460_implies_Equation429 (G : Type*) [Magma G] (h : Equation460 G) : Equation429 G := λ x y => h x y x y
theorem Equation461_implies_Equation430 (G : Type*) [Magma G] (h : Equation461 G) : Equation430 G := λ x y => h x y x y
theorem Equation472_implies_Equation464 (G : Type*) [Magma G] (h : Equation472 G) : Equation464 G := λ x y => h x y x y
theorem Equation482_implies_Equation474 (G : Type*) [Magma G] (h : Equation482 G) : Equation474 G := λ x y => h x y x y
theorem Equation486_implies_Equation464 (G : Type*) [Magma G] (h : Equation486 G) : Equation464 G := λ x y => h x y x y
theorem Equation490_implies_Equation467 (G : Type*) [Magma G] (h : Equation490 G) : Equation467 G := λ x y => h x y x y
theorem Equation494_implies_Equation464 (G : Type*) [Magma G] (h : Equation494 G) : Equation464 G := λ x y => h x y x y
theorem Equation495_implies_Equation466 (G : Type*) [Magma G] (h : Equation495 G) : Equation466 G := λ x y => h x y x y
theorem Equation496_implies_Equation467 (G : Type*) [Magma G] (h : Equation496 G) : Equation467 G := λ x y => h x y x y
theorem Equation497_implies_Equation466 (G : Type*) [Magma G] (h : Equation497 G) : Equation466 G := λ x y => h x y x y
theorem Equation498_implies_Equation467 (G : Type*) [Magma G] (h : Equation498 G) : Equation467 G := λ x y => h x y x y
theorem Equation509_implies_Equation501 (G : Type*) [Magma G] (h : Equation509 G) : Equation501 G := λ x y => h x y x y
theorem Equation519_implies_Equation511 (G : Type*) [Magma G] (h : Equation519 G) : Equation511 G := λ x y => h x y x y
theorem Equation523_implies_Equation501 (G : Type*) [Magma G] (h : Equation523 G) : Equation501 G := λ x y => h x y x y
theorem Equation527_implies_Equation504 (G : Type*) [Magma G] (h : Equation527 G) : Equation504 G := λ x y => h x y x y
theorem Equation531_implies_Equation501 (G : Type*) [Magma G] (h : Equation531 G) : Equation501 G := λ x y => h x y x y
theorem Equation532_implies_Equation503 (G : Type*) [Magma G] (h : Equation532 G) : Equation503 G := λ x y => h x y x y
theorem Equation533_implies_Equation504 (G : Type*) [Magma G] (h : Equation533 G) : Equation504 G := λ x y => h x y x y
theorem Equation534_implies_Equation503 (G : Type*) [Magma G] (h : Equation534 G) : Equation503 G := λ x y => h x y x y
theorem Equation535_implies_Equation504 (G : Type*) [Magma G] (h : Equation535 G) : Equation504 G := λ x y => h x y x y
theorem Equation540_implies_Equation464 (G : Type*) [Magma G] (h : Equation540 G) : Equation464 G := λ x y => h x y x y
theorem Equation544_implies_Equation467 (G : Type*) [Magma G] (h : Equation544 G) : Equation467 G := λ x y => h x y x y
theorem Equation548_implies_Equation464 (G : Type*) [Magma G] (h : Equation548 G) : Equation464 G := λ x y => h x y x y
theorem Equation549_implies_Equation466 (G : Type*) [Magma G] (h : Equation549 G) : Equation466 G := λ x y => h x y x y
theorem Equation550_implies_Equation467 (G : Type*) [Magma G] (h : Equation550 G) : Equation467 G := λ x y => h x y x y
theorem Equation551_implies_Equation466 (G : Type*) [Magma G] (h : Equation551 G) : Equation466 G := λ x y => h x y x y
theorem Equation552_implies_Equation467 (G : Type*) [Magma G] (h : Equation552 G) : Equation467 G := λ x y => h x y x y
theorem Equation557_implies_Equation474 (G : Type*) [Magma G] (h : Equation557 G) : Equation474 G := λ x y => h x y x y
theorem Equation561_implies_Equation477 (G : Type*) [Magma G] (h : Equation561 G) : Equation477 G := λ x y => h x y x y
theorem Equation565_implies_Equation474 (G : Type*) [Magma G] (h : Equation565 G) : Equation474 G := λ x y => h x y x y
theorem Equation566_implies_Equation476 (G : Type*) [Magma G] (h : Equation566 G) : Equation476 G := λ x y => h x y x y
theorem Equation567_implies_Equation477 (G : Type*) [Magma G] (h : Equation567 G) : Equation477 G := λ x y => h x y x y
theorem Equation568_implies_Equation476 (G : Type*) [Magma G] (h : Equation568 G) : Equation476 G := λ x y => h x y x y
theorem Equation569_implies_Equation477 (G : Type*) [Magma G] (h : Equation569 G) : Equation477 G := λ x y => h x y x y
theorem Equation574_implies_Equation464 (G : Type*) [Magma G] (h : Equation574 G) : Equation464 G := λ x y => h x y x y
theorem Equation578_implies_Equation467 (G : Type*) [Magma G] (h : Equation578 G) : Equation467 G := λ x y => h x y x y
theorem Equation582_implies_Equation464 (G : Type*) [Magma G] (h : Equation582 G) : Equation464 G := λ x y => h x y x y
theorem Equation583_implies_Equation466 (G : Type*) [Magma G] (h : Equation583 G) : Equation466 G := λ x y => h x y x y
theorem Equation584_implies_Equation467 (G : Type*) [Magma G] (h : Equation584 G) : Equation467 G := λ x y => h x y x y
theorem Equation585_implies_Equation466 (G : Type*) [Magma G] (h : Equation585 G) : Equation466 G := λ x y => h x y x y
theorem Equation586_implies_Equation467 (G : Type*) [Magma G] (h : Equation586 G) : Equation467 G := λ x y => h x y x y
theorem Equation588_implies_Equation473 (G : Type*) [Magma G] (h : Equation588 G) : Equation473 G := λ x y => h x y x y
theorem Equation589_implies_Equation474 (G : Type*) [Magma G] (h : Equation589 G) : Equation474 G := λ x y => h x y x y
theorem Equation590_implies_Equation473 (G : Type*) [Magma G] (h : Equation590 G) : Equation473 G := λ x y => h x y x y
theorem Equation591_implies_Equation474 (G : Type*) [Magma G] (h : Equation591 G) : Equation474 G := λ x y => h x y x y
theorem Equation593_implies_Equation476 (G : Type*) [Magma G] (h : Equation593 G) : Equation476 G := λ x y => h x y x y
theorem Equation594_implies_Equation477 (G : Type*) [Magma G] (h : Equation594 G) : Equation477 G := λ x y => h x y x y
theorem Equation595_implies_Equation476 (G : Type*) [Magma G] (h : Equation595 G) : Equation476 G := λ x y => h x y x y
theorem Equation596_implies_Equation477 (G : Type*) [Magma G] (h : Equation596 G) : Equation477 G := λ x y => h x y x y
theorem Equation598_implies_Equation473 (G : Type*) [Magma G] (h : Equation598 G) : Equation473 G := λ x y => h x y x y
theorem Equation599_implies_Equation474 (G : Type*) [Magma G] (h : Equation599 G) : Equation474 G := λ x y => h x y x y
theorem Equation600_implies_Equation473 (G : Type*) [Magma G] (h : Equation600 G) : Equation473 G := λ x y => h x y x y
theorem Equation601_implies_Equation474 (G : Type*) [Magma G] (h : Equation601 G) : Equation474 G := λ x y => h x y x y
theorem Equation603_implies_Equation476 (G : Type*) [Magma G] (h : Equation603 G) : Equation476 G := λ x y => h x y x y
theorem Equation604_implies_Equation477 (G : Type*) [Magma G] (h : Equation604 G) : Equation477 G := λ x y => h x y x y
theorem Equation605_implies_Equation476 (G : Type*) [Magma G] (h : Equation605 G) : Equation476 G := λ x y => h x y x y
theorem Equation606_implies_Equation477 (G : Type*) [Magma G] (h : Equation606 G) : Equation477 G := λ x y => h x y x y
theorem Equation628_implies_Equation620 (G : Type*) [Magma G] (h : Equation628 G) : Equation620 G := λ x y => h x y x y
theorem Equation638_implies_Equation630 (G : Type*) [Magma G] (h : Equation638 G) : Equation630 G := λ x y => h x y x y
theorem Equation648_implies_Equation640 (G : Type*) [Magma G] (h : Equation648 G) : Equation640 G := λ x y => h x y x y
theorem Equation652_implies_Equation630 (G : Type*) [Magma G] (h : Equation652 G) : Equation630 G := λ x y => h x y x y
theorem Equation656_implies_Equation633 (G : Type*) [Magma G] (h : Equation656 G) : Equation633 G := λ x y => h x y x y
theorem Equation660_implies_Equation630 (G : Type*) [Magma G] (h : Equation660 G) : Equation630 G := λ x y => h x y x y
theorem Equation661_implies_Equation632 (G : Type*) [Magma G] (h : Equation661 G) : Equation632 G := λ x y => h x y x y
theorem Equation662_implies_Equation633 (G : Type*) [Magma G] (h : Equation662 G) : Equation633 G := λ x y => h x y x y
theorem Equation663_implies_Equation632 (G : Type*) [Magma G] (h : Equation663 G) : Equation632 G := λ x y => h x y x y
theorem Equation664_implies_Equation633 (G : Type*) [Magma G] (h : Equation664 G) : Equation633 G := λ x y => h x y x y
theorem Equation675_implies_Equation667 (G : Type*) [Magma G] (h : Equation675 G) : Equation667 G := λ x y => h x y x y
theorem Equation685_implies_Equation677 (G : Type*) [Magma G] (h : Equation685 G) : Equation677 G := λ x y => h x y x y
theorem Equation689_implies_Equation667 (G : Type*) [Magma G] (h : Equation689 G) : Equation667 G := λ x y => h x y x y
theorem Equation693_implies_Equation670 (G : Type*) [Magma G] (h : Equation693 G) : Equation670 G := λ x y => h x y x y
theorem Equation697_implies_Equation667 (G : Type*) [Magma G] (h : Equation697 G) : Equation667 G := λ x y => h x y x y
theorem Equation698_implies_Equation669 (G : Type*) [Magma G] (h : Equation698 G) : Equation669 G := λ x y => h x y x y
theorem Equation699_implies_Equation670 (G : Type*) [Magma G] (h : Equation699 G) : Equation670 G := λ x y => h x y x y
theorem Equation700_implies_Equation669 (G : Type*) [Magma G] (h : Equation700 G) : Equation669 G := λ x y => h x y x y
theorem Equation701_implies_Equation670 (G : Type*) [Magma G] (h : Equation701 G) : Equation670 G := λ x y => h x y x y
theorem Equation712_implies_Equation704 (G : Type*) [Magma G] (h : Equation712 G) : Equation704 G := λ x y => h x y x y
theorem Equation722_implies_Equation714 (G : Type*) [Magma G] (h : Equation722 G) : Equation714 G := λ x y => h x y x y
theorem Equation726_implies_Equation704 (G : Type*) [Magma G] (h : Equation726 G) : Equation704 G := λ x y => h x y x y
theorem Equation730_implies_Equation707 (G : Type*) [Magma G] (h : Equation730 G) : Equation707 G := λ x y => h x y x y
theorem Equation734_implies_Equation704 (G : Type*) [Magma G] (h : Equation734 G) : Equation704 G := λ x y => h x y x y
theorem Equation735_implies_Equation706 (G : Type*) [Magma G] (h : Equation735 G) : Equation706 G := λ x y => h x y x y
theorem Equation736_implies_Equation707 (G : Type*) [Magma G] (h : Equation736 G) : Equation707 G := λ x y => h x y x y
theorem Equation737_implies_Equation706 (G : Type*) [Magma G] (h : Equation737 G) : Equation706 G := λ x y => h x y x y
theorem Equation738_implies_Equation707 (G : Type*) [Magma G] (h : Equation738 G) : Equation707 G := λ x y => h x y x y
theorem Equation743_implies_Equation667 (G : Type*) [Magma G] (h : Equation743 G) : Equation667 G := λ x y => h x y x y
theorem Equation747_implies_Equation670 (G : Type*) [Magma G] (h : Equation747 G) : Equation670 G := λ x y => h x y x y
theorem Equation751_implies_Equation667 (G : Type*) [Magma G] (h : Equation751 G) : Equation667 G := λ x y => h x y x y
theorem Equation752_implies_Equation669 (G : Type*) [Magma G] (h : Equation752 G) : Equation669 G := λ x y => h x y x y
theorem Equation753_implies_Equation670 (G : Type*) [Magma G] (h : Equation753 G) : Equation670 G := λ x y => h x y x y
theorem Equation754_implies_Equation669 (G : Type*) [Magma G] (h : Equation754 G) : Equation669 G := λ x y => h x y x y
theorem Equation755_implies_Equation670 (G : Type*) [Magma G] (h : Equation755 G) : Equation670 G := λ x y => h x y x y
theorem Equation760_implies_Equation677 (G : Type*) [Magma G] (h : Equation760 G) : Equation677 G := λ x y => h x y x y
theorem Equation764_implies_Equation680 (G : Type*) [Magma G] (h : Equation764 G) : Equation680 G := λ x y => h x y x y
theorem Equation768_implies_Equation677 (G : Type*) [Magma G] (h : Equation768 G) : Equation677 G := λ x y => h x y x y
theorem Equation769_implies_Equation679 (G : Type*) [Magma G] (h : Equation769 G) : Equation679 G := λ x y => h x y x y
theorem Equation770_implies_Equation680 (G : Type*) [Magma G] (h : Equation770 G) : Equation680 G := λ x y => h x y x y
theorem Equation771_implies_Equation679 (G : Type*) [Magma G] (h : Equation771 G) : Equation679 G := λ x y => h x y x y
theorem Equation772_implies_Equation680 (G : Type*) [Magma G] (h : Equation772 G) : Equation680 G := λ x y => h x y x y
theorem Equation777_implies_Equation667 (G : Type*) [Magma G] (h : Equation777 G) : Equation667 G := λ x y => h x y x y
theorem Equation781_implies_Equation670 (G : Type*) [Magma G] (h : Equation781 G) : Equation670 G := λ x y => h x y x y
theorem Equation785_implies_Equation667 (G : Type*) [Magma G] (h : Equation785 G) : Equation667 G := λ x y => h x y x y
theorem Equation786_implies_Equation669 (G : Type*) [Magma G] (h : Equation786 G) : Equation669 G := λ x y => h x y x y
theorem Equation787_implies_Equation670 (G : Type*) [Magma G] (h : Equation787 G) : Equation670 G := λ x y => h x y x y
theorem Equation788_implies_Equation669 (G : Type*) [Magma G] (h : Equation788 G) : Equation669 G := λ x y => h x y x y
theorem Equation789_implies_Equation670 (G : Type*) [Magma G] (h : Equation789 G) : Equation670 G := λ x y => h x y x y
theorem Equation791_implies_Equation676 (G : Type*) [Magma G] (h : Equation791 G) : Equation676 G := λ x y => h x y x y
theorem Equation792_implies_Equation677 (G : Type*) [Magma G] (h : Equation792 G) : Equation677 G := λ x y => h x y x y
theorem Equation793_implies_Equation676 (G : Type*) [Magma G] (h : Equation793 G) : Equation676 G := λ x y => h x y x y
theorem Equation794_implies_Equation677 (G : Type*) [Magma G] (h : Equation794 G) : Equation677 G := λ x y => h x y x y
theorem Equation796_implies_Equation679 (G : Type*) [Magma G] (h : Equation796 G) : Equation679 G := λ x y => h x y x y
theorem Equation797_implies_Equation680 (G : Type*) [Magma G] (h : Equation797 G) : Equation680 G := λ x y => h x y x y
theorem Equation798_implies_Equation679 (G : Type*) [Magma G] (h : Equation798 G) : Equation679 G := λ x y => h x y x y
theorem Equation799_implies_Equation680 (G : Type*) [Magma G] (h : Equation799 G) : Equation680 G := λ x y => h x y x y
theorem Equation801_implies_Equation676 (G : Type*) [Magma G] (h : Equation801 G) : Equation676 G := λ x y => h x y x y
theorem Equation802_implies_Equation677 (G : Type*) [Magma G] (h : Equation802 G) : Equation677 G := λ x y => h x y x y
theorem Equation803_implies_Equation676 (G : Type*) [Magma G] (h : Equation803 G) : Equation676 G := λ x y => h x y x y
theorem Equation804_implies_Equation677 (G : Type*) [Magma G] (h : Equation804 G) : Equation677 G := λ x y => h x y x y
theorem Equation806_implies_Equation679 (G : Type*) [Magma G] (h : Equation806 G) : Equation679 G := λ x y => h x y x y
theorem Equation807_implies_Equation680 (G : Type*) [Magma G] (h : Equation807 G) : Equation680 G := λ x y => h x y x y
theorem Equation808_implies_Equation679 (G : Type*) [Magma G] (h : Equation808 G) : Equation679 G := λ x y => h x y x y
theorem Equation809_implies_Equation680 (G : Type*) [Magma G] (h : Equation809 G) : Equation680 G := λ x y => h x y x y
theorem Equation831_implies_Equation823 (G : Type*) [Magma G] (h : Equation831 G) : Equation823 G := λ x y => h x y x y
theorem Equation841_implies_Equation833 (G : Type*) [Magma G] (h : Equation841 G) : Equation833 G := λ x y => h x y x y
theorem Equation851_implies_Equation843 (G : Type*) [Magma G] (h : Equation851 G) : Equation843 G := λ x y => h x y x y
theorem Equation855_implies_Equation833 (G : Type*) [Magma G] (h : Equation855 G) : Equation833 G := λ x y => h x y x y
theorem Equation859_implies_Equation836 (G : Type*) [Magma G] (h : Equation859 G) : Equation836 G := λ x y => h x y x y
theorem Equation863_implies_Equation833 (G : Type*) [Magma G] (h : Equation863 G) : Equation833 G := λ x y => h x y x y
theorem Equation864_implies_Equation835 (G : Type*) [Magma G] (h : Equation864 G) : Equation835 G := λ x y => h x y x y
theorem Equation865_implies_Equation836 (G : Type*) [Magma G] (h : Equation865 G) : Equation836 G := λ x y => h x y x y
theorem Equation866_implies_Equation835 (G : Type*) [Magma G] (h : Equation866 G) : Equation835 G := λ x y => h x y x y
theorem Equation867_implies_Equation836 (G : Type*) [Magma G] (h : Equation867 G) : Equation836 G := λ x y => h x y x y
theorem Equation878_implies_Equation870 (G : Type*) [Magma G] (h : Equation878 G) : Equation870 G := λ x y => h x y x y
theorem Equation888_implies_Equation880 (G : Type*) [Magma G] (h : Equation888 G) : Equation880 G := λ x y => h x y x y
theorem Equation892_implies_Equation870 (G : Type*) [Magma G] (h : Equation892 G) : Equation870 G := λ x y => h x y x y
theorem Equation896_implies_Equation873 (G : Type*) [Magma G] (h : Equation896 G) : Equation873 G := λ x y => h x y x y
theorem Equation900_implies_Equation870 (G : Type*) [Magma G] (h : Equation900 G) : Equation870 G := λ x y => h x y x y
theorem Equation901_implies_Equation872 (G : Type*) [Magma G] (h : Equation901 G) : Equation872 G := λ x y => h x y x y
theorem Equation902_implies_Equation873 (G : Type*) [Magma G] (h : Equation902 G) : Equation873 G := λ x y => h x y x y
theorem Equation903_implies_Equation872 (G : Type*) [Magma G] (h : Equation903 G) : Equation872 G := λ x y => h x y x y
theorem Equation904_implies_Equation873 (G : Type*) [Magma G] (h : Equation904 G) : Equation873 G := λ x y => h x y x y
theorem Equation915_implies_Equation907 (G : Type*) [Magma G] (h : Equation915 G) : Equation907 G := λ x y => h x y x y
theorem Equation925_implies_Equation917 (G : Type*) [Magma G] (h : Equation925 G) : Equation917 G := λ x y => h x y x y
theorem Equation929_implies_Equation907 (G : Type*) [Magma G] (h : Equation929 G) : Equation907 G := λ x y => h x y x y
theorem Equation933_implies_Equation910 (G : Type*) [Magma G] (h : Equation933 G) : Equation910 G := λ x y => h x y x y
theorem Equation937_implies_Equation907 (G : Type*) [Magma G] (h : Equation937 G) : Equation907 G := λ x y => h x y x y
theorem Equation938_implies_Equation909 (G : Type*) [Magma G] (h : Equation938 G) : Equation909 G := λ x y => h x y x y
theorem Equation939_implies_Equation910 (G : Type*) [Magma G] (h : Equation939 G) : Equation910 G := λ x y => h x y x y
theorem Equation940_implies_Equation909 (G : Type*) [Magma G] (h : Equation940 G) : Equation909 G := λ x y => h x y x y
theorem Equation941_implies_Equation910 (G : Type*) [Magma G] (h : Equation941 G) : Equation910 G := λ x y => h x y x y
theorem Equation946_implies_Equation870 (G : Type*) [Magma G] (h : Equation946 G) : Equation870 G := λ x y => h x y x y
theorem Equation950_implies_Equation873 (G : Type*) [Magma G] (h : Equation950 G) : Equation873 G := λ x y => h x y x y
theorem Equation954_implies_Equation870 (G : Type*) [Magma G] (h : Equation954 G) : Equation870 G := λ x y => h x y x y
theorem Equation955_implies_Equation872 (G : Type*) [Magma G] (h : Equation955 G) : Equation872 G := λ x y => h x y x y
theorem Equation956_implies_Equation873 (G : Type*) [Magma G] (h : Equation956 G) : Equation873 G := λ x y => h x y x y
theorem Equation957_implies_Equation872 (G : Type*) [Magma G] (h : Equation957 G) : Equation872 G := λ x y => h x y x y
theorem Equation958_implies_Equation873 (G : Type*) [Magma G] (h : Equation958 G) : Equation873 G := λ x y => h x y x y
theorem Equation963_implies_Equation880 (G : Type*) [Magma G] (h : Equation963 G) : Equation880 G := λ x y => h x y x y
theorem Equation967_implies_Equation883 (G : Type*) [Magma G] (h : Equation967 G) : Equation883 G := λ x y => h x y x y
theorem Equation971_implies_Equation880 (G : Type*) [Magma G] (h : Equation971 G) : Equation880 G := λ x y => h x y x y
theorem Equation972_implies_Equation882 (G : Type*) [Magma G] (h : Equation972 G) : Equation882 G := λ x y => h x y x y
theorem Equation973_implies_Equation883 (G : Type*) [Magma G] (h : Equation973 G) : Equation883 G := λ x y => h x y x y
theorem Equation974_implies_Equation882 (G : Type*) [Magma G] (h : Equation974 G) : Equation882 G := λ x y => h x y x y
theorem Equation975_implies_Equation883 (G : Type*) [Magma G] (h : Equation975 G) : Equation883 G := λ x y => h x y x y
theorem Equation980_implies_Equation870 (G : Type*) [Magma G] (h : Equation980 G) : Equation870 G := λ x y => h x y x y
theorem Equation984_implies_Equation873 (G : Type*) [Magma G] (h : Equation984 G) : Equation873 G := λ x y => h x y x y
theorem Equation988_implies_Equation870 (G : Type*) [Magma G] (h : Equation988 G) : Equation870 G := λ x y => h x y x y
theorem Equation989_implies_Equation872 (G : Type*) [Magma G] (h : Equation989 G) : Equation872 G := λ x y => h x y x y
theorem Equation990_implies_Equation873 (G : Type*) [Magma G] (h : Equation990 G) : Equation873 G := λ x y => h x y x y
theorem Equation991_implies_Equation872 (G : Type*) [Magma G] (h : Equation991 G) : Equation872 G := λ x y => h x y x y
theorem Equation992_implies_Equation873 (G : Type*) [Magma G] (h : Equation992 G) : Equation873 G := λ x y => h x y x y
theorem Equation994_implies_Equation879 (G : Type*) [Magma G] (h : Equation994 G) : Equation879 G := λ x y => h x y x y
theorem Equation995_implies_Equation880 (G : Type*) [Magma G] (h : Equation995 G) : Equation880 G := λ x y => h x y x y
theorem Equation996_implies_Equation879 (G : Type*) [Magma G] (h : Equation996 G) : Equation879 G := λ x y => h x y x y
theorem Equation997_implies_Equation880 (G : Type*) [Magma G] (h : Equation997 G) : Equation880 G := λ x y => h x y x y
theorem Equation999_implies_Equation882 (G : Type*) [Magma G] (h : Equation999 G) : Equation882 G := λ x y => h x y x y
theorem Equation1000_implies_Equation883 (G : Type*) [Magma G] (h : Equation1000 G) : Equation883 G := λ x y => h x y x y
theorem Equation1001_implies_Equation882 (G : Type*) [Magma G] (h : Equation1001 G) : Equation882 G := λ x y => h x y x y
theorem Equation1002_implies_Equation883 (G : Type*) [Magma G] (h : Equation1002 G) : Equation883 G := λ x y => h x y x y
theorem Equation1004_implies_Equation879 (G : Type*) [Magma G] (h : Equation1004 G) : Equation879 G := λ x y => h x y x y
theorem Equation1005_implies_Equation880 (G : Type*) [Magma G] (h : Equation1005 G) : Equation880 G := λ x y => h x y x y
theorem Equation1006_implies_Equation879 (G : Type*) [Magma G] (h : Equation1006 G) : Equation879 G := λ x y => h x y x y
theorem Equation1007_implies_Equation880 (G : Type*) [Magma G] (h : Equation1007 G) : Equation880 G := λ x y => h x y x y
theorem Equation1009_implies_Equation882 (G : Type*) [Magma G] (h : Equation1009 G) : Equation882 G := λ x y => h x y x y
theorem Equation1010_implies_Equation883 (G : Type*) [Magma G] (h : Equation1010 G) : Equation883 G := λ x y => h x y x y
theorem Equation1011_implies_Equation882 (G : Type*) [Magma G] (h : Equation1011 G) : Equation882 G := λ x y => h x y x y
theorem Equation1012_implies_Equation883 (G : Type*) [Magma G] (h : Equation1012 G) : Equation883 G := λ x y => h x y x y
theorem Equation1034_implies_Equation1026 (G : Type*) [Magma G] (h : Equation1034 G) : Equation1026 G := λ x y => h x y x y
theorem Equation1044_implies_Equation1036 (G : Type*) [Magma G] (h : Equation1044 G) : Equation1036 G := λ x y => h x y x y
theorem Equation1054_implies_Equation1046 (G : Type*) [Magma G] (h : Equation1054 G) : Equation1046 G := λ x y => h x y x y
theorem Equation1058_implies_Equation1036 (G : Type*) [Magma G] (h : Equation1058 G) : Equation1036 G := λ x y => h x y x y
theorem Equation1062_implies_Equation1039 (G : Type*) [Magma G] (h : Equation1062 G) : Equation1039 G := λ x y => h x y x y
theorem Equation1066_implies_Equation1036 (G : Type*) [Magma G] (h : Equation1066 G) : Equation1036 G := λ x y => h x y x y
theorem Equation1067_implies_Equation1038 (G : Type*) [Magma G] (h : Equation1067 G) : Equation1038 G := λ x y => h x y x y
theorem Equation1068_implies_Equation1039 (G : Type*) [Magma G] (h : Equation1068 G) : Equation1039 G := λ x y => h x y x y
theorem Equation1069_implies_Equation1038 (G : Type*) [Magma G] (h : Equation1069 G) : Equation1038 G := λ x y => h x y x y
theorem Equation1070_implies_Equation1039 (G : Type*) [Magma G] (h : Equation1070 G) : Equation1039 G := λ x y => h x y x y
theorem Equation1081_implies_Equation1073 (G : Type*) [Magma G] (h : Equation1081 G) : Equation1073 G := λ x y => h x y x y
theorem Equation1091_implies_Equation1083 (G : Type*) [Magma G] (h : Equation1091 G) : Equation1083 G := λ x y => h x y x y
theorem Equation1095_implies_Equation1073 (G : Type*) [Magma G] (h : Equation1095 G) : Equation1073 G := λ x y => h x y x y
theorem Equation1099_implies_Equation1076 (G : Type*) [Magma G] (h : Equation1099 G) : Equation1076 G := λ x y => h x y x y
theorem Equation1103_implies_Equation1073 (G : Type*) [Magma G] (h : Equation1103 G) : Equation1073 G := λ x y => h x y x y
theorem Equation1104_implies_Equation1075 (G : Type*) [Magma G] (h : Equation1104 G) : Equation1075 G := λ x y => h x y x y
theorem Equation1105_implies_Equation1076 (G : Type*) [Magma G] (h : Equation1105 G) : Equation1076 G := λ x y => h x y x y
theorem Equation1106_implies_Equation1075 (G : Type*) [Magma G] (h : Equation1106 G) : Equation1075 G := λ x y => h x y x y
theorem Equation1107_implies_Equation1076 (G : Type*) [Magma G] (h : Equation1107 G) : Equation1076 G := λ x y => h x y x y
theorem Equation1118_implies_Equation1110 (G : Type*) [Magma G] (h : Equation1118 G) : Equation1110 G := λ x y => h x y x y
theorem Equation1128_implies_Equation1120 (G : Type*) [Magma G] (h : Equation1128 G) : Equation1120 G := λ x y => h x y x y
theorem Equation1132_implies_Equation1110 (G : Type*) [Magma G] (h : Equation1132 G) : Equation1110 G := λ x y => h x y x y
theorem Equation1136_implies_Equation1113 (G : Type*) [Magma G] (h : Equation1136 G) : Equation1113 G := λ x y => h x y x y
theorem Equation1140_implies_Equation1110 (G : Type*) [Magma G] (h : Equation1140 G) : Equation1110 G := λ x y => h x y x y
theorem Equation1141_implies_Equation1112 (G : Type*) [Magma G] (h : Equation1141 G) : Equation1112 G := λ x y => h x y x y
theorem Equation1142_implies_Equation1113 (G : Type*) [Magma G] (h : Equation1142 G) : Equation1113 G := λ x y => h x y x y
theorem Equation1143_implies_Equation1112 (G : Type*) [Magma G] (h : Equation1143 G) : Equation1112 G := λ x y => h x y x y
theorem Equation1144_implies_Equation1113 (G : Type*) [Magma G] (h : Equation1144 G) : Equation1113 G := λ x y => h x y x y
theorem Equation1149_implies_Equation1073 (G : Type*) [Magma G] (h : Equation1149 G) : Equation1073 G := λ x y => h x y x y
theorem Equation1153_implies_Equation1076 (G : Type*) [Magma G] (h : Equation1153 G) : Equation1076 G := λ x y => h x y x y
theorem Equation1157_implies_Equation1073 (G : Type*) [Magma G] (h : Equation1157 G) : Equation1073 G := λ x y => h x y x y
theorem Equation1158_implies_Equation1075 (G : Type*) [Magma G] (h : Equation1158 G) : Equation1075 G := λ x y => h x y x y
theorem Equation1159_implies_Equation1076 (G : Type*) [Magma G] (h : Equation1159 G) : Equation1076 G := λ x y => h x y x y
theorem Equation1160_implies_Equation1075 (G : Type*) [Magma G] (h : Equation1160 G) : Equation1075 G := λ x y => h x y x y
theorem Equation1161_implies_Equation1076 (G : Type*) [Magma G] (h : Equation1161 G) : Equation1076 G := λ x y => h x y x y
theorem Equation1166_implies_Equation1083 (G : Type*) [Magma G] (h : Equation1166 G) : Equation1083 G := λ x y => h x y x y
theorem Equation1170_implies_Equation1086 (G : Type*) [Magma G] (h : Equation1170 G) : Equation1086 G := λ x y => h x y x y
theorem Equation1174_implies_Equation1083 (G : Type*) [Magma G] (h : Equation1174 G) : Equation1083 G := λ x y => h x y x y
theorem Equation1175_implies_Equation1085 (G : Type*) [Magma G] (h : Equation1175 G) : Equation1085 G := λ x y => h x y x y
theorem Equation1176_implies_Equation1086 (G : Type*) [Magma G] (h : Equation1176 G) : Equation1086 G := λ x y => h x y x y
theorem Equation1177_implies_Equation1085 (G : Type*) [Magma G] (h : Equation1177 G) : Equation1085 G := λ x y => h x y x y
theorem Equation1178_implies_Equation1086 (G : Type*) [Magma G] (h : Equation1178 G) : Equation1086 G := λ x y => h x y x y
theorem Equation1183_implies_Equation1073 (G : Type*) [Magma G] (h : Equation1183 G) : Equation1073 G := λ x y => h x y x y
theorem Equation1187_implies_Equation1076 (G : Type*) [Magma G] (h : Equation1187 G) : Equation1076 G := λ x y => h x y x y
theorem Equation1191_implies_Equation1073 (G : Type*) [Magma G] (h : Equation1191 G) : Equation1073 G := λ x y => h x y x y
theorem Equation1192_implies_Equation1075 (G : Type*) [Magma G] (h : Equation1192 G) : Equation1075 G := λ x y => h x y x y
theorem Equation1193_implies_Equation1076 (G : Type*) [Magma G] (h : Equation1193 G) : Equation1076 G := λ x y => h x y x y
theorem Equation1194_implies_Equation1075 (G : Type*) [Magma G] (h : Equation1194 G) : Equation1075 G := λ x y => h x y x y
theorem Equation1195_implies_Equation1076 (G : Type*) [Magma G] (h : Equation1195 G) : Equation1076 G := λ x y => h x y x y
theorem Equation1197_implies_Equation1082 (G : Type*) [Magma G] (h : Equation1197 G) : Equation1082 G := λ x y => h x y x y
theorem Equation1198_implies_Equation1083 (G : Type*) [Magma G] (h : Equation1198 G) : Equation1083 G := λ x y => h x y x y
theorem Equation1199_implies_Equation1082 (G : Type*) [Magma G] (h : Equation1199 G) : Equation1082 G := λ x y => h x y x y
theorem Equation1200_implies_Equation1083 (G : Type*) [Magma G] (h : Equation1200 G) : Equation1083 G := λ x y => h x y x y
theorem Equation1202_implies_Equation1085 (G : Type*) [Magma G] (h : Equation1202 G) : Equation1085 G := λ x y => h x y x y
theorem Equation1203_implies_Equation1086 (G : Type*) [Magma G] (h : Equation1203 G) : Equation1086 G := λ x y => h x y x y
theorem Equation1204_implies_Equation1085 (G : Type*) [Magma G] (h : Equation1204 G) : Equation1085 G := λ x y => h x y x y
theorem Equation1205_implies_Equation1086 (G : Type*) [Magma G] (h : Equation1205 G) : Equation1086 G := λ x y => h x y x y
theorem Equation1207_implies_Equation1082 (G : Type*) [Magma G] (h : Equation1207 G) : Equation1082 G := λ x y => h x y x y
theorem Equation1208_implies_Equation1083 (G : Type*) [Magma G] (h : Equation1208 G) : Equation1083 G := λ x y => h x y x y
theorem Equation1209_implies_Equation1082 (G : Type*) [Magma G] (h : Equation1209 G) : Equation1082 G := λ x y => h x y x y
theorem Equation1210_implies_Equation1083 (G : Type*) [Magma G] (h : Equation1210 G) : Equation1083 G := λ x y => h x y x y
theorem Equation1212_implies_Equation1085 (G : Type*) [Magma G] (h : Equation1212 G) : Equation1085 G := λ x y => h x y x y
theorem Equation1213_implies_Equation1086 (G : Type*) [Magma G] (h : Equation1213 G) : Equation1086 G := λ x y => h x y x y
theorem Equation1214_implies_Equation1085 (G : Type*) [Magma G] (h : Equation1214 G) : Equation1085 G := λ x y => h x y x y
theorem Equation1215_implies_Equation1086 (G : Type*) [Magma G] (h : Equation1215 G) : Equation1086 G := λ x y => h x y x y
theorem Equation1237_implies_Equation1229 (G : Type*) [Magma G] (h : Equation1237 G) : Equation1229 G := λ x y => h x y x y
theorem Equation1247_implies_Equation1239 (G : Type*) [Magma G] (h : Equation1247 G) : Equation1239 G := λ x y => h x y x y
theorem Equation1257_implies_Equation1249 (G : Type*) [Magma G] (h : Equation1257 G) : Equation1249 G := λ x y => h x y x y
theorem Equation1261_implies_Equation1239 (G : Type*) [Magma G] (h : Equation1261 G) : Equation1239 G := λ x y => h x y x y
theorem Equation1265_implies_Equation1242 (G : Type*) [Magma G] (h : Equation1265 G) : Equation1242 G := λ x y => h x y x y
theorem Equation1269_implies_Equation1239 (G : Type*) [Magma G] (h : Equation1269 G) : Equation1239 G := λ x y => h x y x y
theorem Equation1270_implies_Equation1241 (G : Type*) [Magma G] (h : Equation1270 G) : Equation1241 G := λ x y => h x y x y
theorem Equation1271_implies_Equation1242 (G : Type*) [Magma G] (h : Equation1271 G) : Equation1242 G := λ x y => h x y x y
theorem Equation1272_implies_Equation1241 (G : Type*) [Magma G] (h : Equation1272 G) : Equation1241 G := λ x y => h x y x y
theorem Equation1273_implies_Equation1242 (G : Type*) [Magma G] (h : Equation1273 G) : Equation1242 G := λ x y => h x y x y
theorem Equation1284_implies_Equation1276 (G : Type*) [Magma G] (h : Equation1284 G) : Equation1276 G := λ x y => h x y x y
theorem Equation1294_implies_Equation1286 (G : Type*) [Magma G] (h : Equation1294 G) : Equation1286 G := λ x y => h x y x y
theorem Equation1298_implies_Equation1276 (G : Type*) [Magma G] (h : Equation1298 G) : Equation1276 G := λ x y => h x y x y
theorem Equation1302_implies_Equation1279 (G : Type*) [Magma G] (h : Equation1302 G) : Equation1279 G := λ x y => h x y x y
theorem Equation1306_implies_Equation1276 (G : Type*) [Magma G] (h : Equation1306 G) : Equation1276 G := λ x y => h x y x y
theorem Equation1307_implies_Equation1278 (G : Type*) [Magma G] (h : Equation1307 G) : Equation1278 G := λ x y => h x y x y
theorem Equation1308_implies_Equation1279 (G : Type*) [Magma G] (h : Equation1308 G) : Equation1279 G := λ x y => h x y x y
theorem Equation1309_implies_Equation1278 (G : Type*) [Magma G] (h : Equation1309 G) : Equation1278 G := λ x y => h x y x y
theorem Equation1310_implies_Equation1279 (G : Type*) [Magma G] (h : Equation1310 G) : Equation1279 G := λ x y => h x y x y
theorem Equation1321_implies_Equation1313 (G : Type*) [Magma G] (h : Equation1321 G) : Equation1313 G := λ x y => h x y x y
theorem Equation1331_implies_Equation1323 (G : Type*) [Magma G] (h : Equation1331 G) : Equation1323 G := λ x y => h x y x y
theorem Equation1335_implies_Equation1313 (G : Type*) [Magma G] (h : Equation1335 G) : Equation1313 G := λ x y => h x y x y
theorem Equation1339_implies_Equation1316 (G : Type*) [Magma G] (h : Equation1339 G) : Equation1316 G := λ x y => h x y x y
theorem Equation1343_implies_Equation1313 (G : Type*) [Magma G] (h : Equation1343 G) : Equation1313 G := λ x y => h x y x y
theorem Equation1344_implies_Equation1315 (G : Type*) [Magma G] (h : Equation1344 G) : Equation1315 G := λ x y => h x y x y
theorem Equation1345_implies_Equation1316 (G : Type*) [Magma G] (h : Equation1345 G) : Equation1316 G := λ x y => h x y x y
theorem Equation1346_implies_Equation1315 (G : Type*) [Magma G] (h : Equation1346 G) : Equation1315 G := λ x y => h x y x y
theorem Equation1347_implies_Equation1316 (G : Type*) [Magma G] (h : Equation1347 G) : Equation1316 G := λ x y => h x y x y
theorem Equation1352_implies_Equation1276 (G : Type*) [Magma G] (h : Equation1352 G) : Equation1276 G := λ x y => h x y x y
theorem Equation1356_implies_Equation1279 (G : Type*) [Magma G] (h : Equation1356 G) : Equation1279 G := λ x y => h x y x y
theorem Equation1360_implies_Equation1276 (G : Type*) [Magma G] (h : Equation1360 G) : Equation1276 G := λ x y => h x y x y
theorem Equation1361_implies_Equation1278 (G : Type*) [Magma G] (h : Equation1361 G) : Equation1278 G := λ x y => h x y x y
theorem Equation1362_implies_Equation1279 (G : Type*) [Magma G] (h : Equation1362 G) : Equation1279 G := λ x y => h x y x y
theorem Equation1363_implies_Equation1278 (G : Type*) [Magma G] (h : Equation1363 G) : Equation1278 G := λ x y => h x y x y
theorem Equation1364_implies_Equation1279 (G : Type*) [Magma G] (h : Equation1364 G) : Equation1279 G := λ x y => h x y x y
theorem Equation1369_implies_Equation1286 (G : Type*) [Magma G] (h : Equation1369 G) : Equation1286 G := λ x y => h x y x y
theorem Equation1373_implies_Equation1289 (G : Type*) [Magma G] (h : Equation1373 G) : Equation1289 G := λ x y => h x y x y
theorem Equation1377_implies_Equation1286 (G : Type*) [Magma G] (h : Equation1377 G) : Equation1286 G := λ x y => h x y x y
theorem Equation1378_implies_Equation1288 (G : Type*) [Magma G] (h : Equation1378 G) : Equation1288 G := λ x y => h x y x y
theorem Equation1379_implies_Equation1289 (G : Type*) [Magma G] (h : Equation1379 G) : Equation1289 G := λ x y => h x y x y
theorem Equation1380_implies_Equation1288 (G : Type*) [Magma G] (h : Equation1380 G) : Equation1288 G := λ x y => h x y x y
theorem Equation1381_implies_Equation1289 (G : Type*) [Magma G] (h : Equation1381 G) : Equation1289 G := λ x y => h x y x y
theorem Equation1386_implies_Equation1276 (G : Type*) [Magma G] (h : Equation1386 G) : Equation1276 G := λ x y => h x y x y
theorem Equation1390_implies_Equation1279 (G : Type*) [Magma G] (h : Equation1390 G) : Equation1279 G := λ x y => h x y x y
theorem Equation1394_implies_Equation1276 (G : Type*) [Magma G] (h : Equation1394 G) : Equation1276 G := λ x y => h x y x y
theorem Equation1395_implies_Equation1278 (G : Type*) [Magma G] (h : Equation1395 G) : Equation1278 G := λ x y => h x y x y
theorem Equation1396_implies_Equation1279 (G : Type*) [Magma G] (h : Equation1396 G) : Equation1279 G := λ x y => h x y x y
theorem Equation1397_implies_Equation1278 (G : Type*) [Magma G] (h : Equation1397 G) : Equation1278 G := λ x y => h x y x y
theorem Equation1398_implies_Equation1279 (G : Type*) [Magma G] (h : Equation1398 G) : Equation1279 G := λ x y => h x y x y
theorem Equation1400_implies_Equation1285 (G : Type*) [Magma G] (h : Equation1400 G) : Equation1285 G := λ x y => h x y x y
theorem Equation1401_implies_Equation1286 (G : Type*) [Magma G] (h : Equation1401 G) : Equation1286 G := λ x y => h x y x y
theorem Equation1402_implies_Equation1285 (G : Type*) [Magma G] (h : Equation1402 G) : Equation1285 G := λ x y => h x y x y
theorem Equation1403_implies_Equation1286 (G : Type*) [Magma G] (h : Equation1403 G) : Equation1286 G := λ x y => h x y x y
theorem Equation1405_implies_Equation1288 (G : Type*) [Magma G] (h : Equation1405 G) : Equation1288 G := λ x y => h x y x y
theorem Equation1406_implies_Equation1289 (G : Type*) [Magma G] (h : Equation1406 G) : Equation1289 G := λ x y => h x y x y
theorem Equation1407_implies_Equation1288 (G : Type*) [Magma G] (h : Equation1407 G) : Equation1288 G := λ x y => h x y x y
theorem Equation1408_implies_Equation1289 (G : Type*) [Magma G] (h : Equation1408 G) : Equation1289 G := λ x y => h x y x y
theorem Equation1410_implies_Equation1285 (G : Type*) [Magma G] (h : Equation1410 G) : Equation1285 G := λ x y => h x y x y
theorem Equation1411_implies_Equation1286 (G : Type*) [Magma G] (h : Equation1411 G) : Equation1286 G := λ x y => h x y x y
theorem Equation1412_implies_Equation1285 (G : Type*) [Magma G] (h : Equation1412 G) : Equation1285 G := λ x y => h x y x y
theorem Equation1413_implies_Equation1286 (G : Type*) [Magma G] (h : Equation1413 G) : Equation1286 G := λ x y => h x y x y
theorem Equation1415_implies_Equation1288 (G : Type*) [Magma G] (h : Equation1415 G) : Equation1288 G := λ x y => h x y x y
theorem Equation1416_implies_Equation1289 (G : Type*) [Magma G] (h : Equation1416 G) : Equation1289 G := λ x y => h x y x y
theorem Equation1417_implies_Equation1288 (G : Type*) [Magma G] (h : Equation1417 G) : Equation1288 G := λ x y => h x y x y
theorem Equation1418_implies_Equation1289 (G : Type*) [Magma G] (h : Equation1418 G) : Equation1289 G := λ x y => h x y x y
theorem Equation1440_implies_Equation1432 (G : Type*) [Magma G] (h : Equation1440 G) : Equation1432 G := λ x y => h x y x y
theorem Equation1450_implies_Equation1442 (G : Type*) [Magma G] (h : Equation1450 G) : Equation1442 G := λ x y => h x y x y
theorem Equation1460_implies_Equation1452 (G : Type*) [Magma G] (h : Equation1460 G) : Equation1452 G := λ x y => h x y x y
theorem Equation1464_implies_Equation1442 (G : Type*) [Magma G] (h : Equation1464 G) : Equation1442 G := λ x y => h x y x y
theorem Equation1468_implies_Equation1445 (G : Type*) [Magma G] (h : Equation1468 G) : Equation1445 G := λ x y => h x y x y
theorem Equation1472_implies_Equation1442 (G : Type*) [Magma G] (h : Equation1472 G) : Equation1442 G := λ x y => h x y x y
theorem Equation1473_implies_Equation1444 (G : Type*) [Magma G] (h : Equation1473 G) : Equation1444 G := λ x y => h x y x y
theorem Equation1474_implies_Equation1445 (G : Type*) [Magma G] (h : Equation1474 G) : Equation1445 G := λ x y => h x y x y
theorem Equation1475_implies_Equation1444 (G : Type*) [Magma G] (h : Equation1475 G) : Equation1444 G := λ x y => h x y x y
theorem Equation1476_implies_Equation1445 (G : Type*) [Magma G] (h : Equation1476 G) : Equation1445 G := λ x y => h x y x y
theorem Equation1487_implies_Equation1479 (G : Type*) [Magma G] (h : Equation1487 G) : Equation1479 G := λ x y => h x y x y
theorem Equation1497_implies_Equation1489 (G : Type*) [Magma G] (h : Equation1497 G) : Equation1489 G := λ x y => h x y x y
theorem Equation1501_implies_Equation1479 (G : Type*) [Magma G] (h : Equation1501 G) : Equation1479 G := λ x y => h x y x y
theorem Equation1505_implies_Equation1482 (G : Type*) [Magma G] (h : Equation1505 G) : Equation1482 G := λ x y => h x y x y
theorem Equation1509_implies_Equation1479 (G : Type*) [Magma G] (h : Equation1509 G) : Equation1479 G := λ x y => h x y x y
theorem Equation1510_implies_Equation1481 (G : Type*) [Magma G] (h : Equation1510 G) : Equation1481 G := λ x y => h x y x y
theorem Equation1511_implies_Equation1482 (G : Type*) [Magma G] (h : Equation1511 G) : Equation1482 G := λ x y => h x y x y
theorem Equation1512_implies_Equation1481 (G : Type*) [Magma G] (h : Equation1512 G) : Equation1481 G := λ x y => h x y x y
theorem Equation1513_implies_Equation1482 (G : Type*) [Magma G] (h : Equation1513 G) : Equation1482 G := λ x y => h x y x y
theorem Equation1524_implies_Equation1516 (G : Type*) [Magma G] (h : Equation1524 G) : Equation1516 G := λ x y => h x y x y
theorem Equation1534_implies_Equation1526 (G : Type*) [Magma G] (h : Equation1534 G) : Equation1526 G := λ x y => h x y x y
theorem Equation1538_implies_Equation1516 (G : Type*) [Magma G] (h : Equation1538 G) : Equation1516 G := λ x y => h x y x y
theorem Equation1542_implies_Equation1519 (G : Type*) [Magma G] (h : Equation1542 G) : Equation1519 G := λ x y => h x y x y
theorem Equation1546_implies_Equation1516 (G : Type*) [Magma G] (h : Equation1546 G) : Equation1516 G := λ x y => h x y x y
theorem Equation1547_implies_Equation1518 (G : Type*) [Magma G] (h : Equation1547 G) : Equation1518 G := λ x y => h x y x y
theorem Equation1548_implies_Equation1519 (G : Type*) [Magma G] (h : Equation1548 G) : Equation1519 G := λ x y => h x y x y
theorem Equation1549_implies_Equation1518 (G : Type*) [Magma G] (h : Equation1549 G) : Equation1518 G := λ x y => h x y x y
theorem Equation1550_implies_Equation1519 (G : Type*) [Magma G] (h : Equation1550 G) : Equation1519 G := λ x y => h x y x y
theorem Equation1555_implies_Equation1479 (G : Type*) [Magma G] (h : Equation1555 G) : Equation1479 G := λ x y => h x y x y
theorem Equation1559_implies_Equation1482 (G : Type*) [Magma G] (h : Equation1559 G) : Equation1482 G := λ x y => h x y x y
theorem Equation1563_implies_Equation1479 (G : Type*) [Magma G] (h : Equation1563 G) : Equation1479 G := λ x y => h x y x y
theorem Equation1564_implies_Equation1481 (G : Type*) [Magma G] (h : Equation1564 G) : Equation1481 G := λ x y => h x y x y
theorem Equation1565_implies_Equation1482 (G : Type*) [Magma G] (h : Equation1565 G) : Equation1482 G := λ x y => h x y x y
theorem Equation1566_implies_Equation1481 (G : Type*) [Magma G] (h : Equation1566 G) : Equation1481 G := λ x y => h x y x y
theorem Equation1567_implies_Equation1482 (G : Type*) [Magma G] (h : Equation1567 G) : Equation1482 G := λ x y => h x y x y
theorem Equation1572_implies_Equation1489 (G : Type*) [Magma G] (h : Equation1572 G) : Equation1489 G := λ x y => h x y x y
theorem Equation1576_implies_Equation1492 (G : Type*) [Magma G] (h : Equation1576 G) : Equation1492 G := λ x y => h x y x y
theorem Equation1580_implies_Equation1489 (G : Type*) [Magma G] (h : Equation1580 G) : Equation1489 G := λ x y => h x y x y
theorem Equation1581_implies_Equation1491 (G : Type*) [Magma G] (h : Equation1581 G) : Equation1491 G := λ x y => h x y x y
theorem Equation1582_implies_Equation1492 (G : Type*) [Magma G] (h : Equation1582 G) : Equation1492 G := λ x y => h x y x y
theorem Equation1583_implies_Equation1491 (G : Type*) [Magma G] (h : Equation1583 G) : Equation1491 G := λ x y => h x y x y
theorem Equation1584_implies_Equation1492 (G : Type*) [Magma G] (h : Equation1584 G) : Equation1492 G := λ x y => h x y x y
theorem Equation1589_implies_Equation1479 (G : Type*) [Magma G] (h : Equation1589 G) : Equation1479 G := λ x y => h x y x y
theorem Equation1593_implies_Equation1482 (G : Type*) [Magma G] (h : Equation1593 G) : Equation1482 G := λ x y => h x y x y
theorem Equation1597_implies_Equation1479 (G : Type*) [Magma G] (h : Equation1597 G) : Equation1479 G := λ x y => h x y x y
theorem Equation1598_implies_Equation1481 (G : Type*) [Magma G] (h : Equation1598 G) : Equation1481 G := λ x y => h x y x y
theorem Equation1599_implies_Equation1482 (G : Type*) [Magma G] (h : Equation1599 G) : Equation1482 G := λ x y => h x y x y
theorem Equation1600_implies_Equation1481 (G : Type*) [Magma G] (h : Equation1600 G) : Equation1481 G := λ x y => h x y x y
theorem Equation1601_implies_Equation1482 (G : Type*) [Magma G] (h : Equation1601 G) : Equation1482 G := λ x y => h x y x y
theorem Equation1603_implies_Equation1488 (G : Type*) [Magma G] (h : Equation1603 G) : Equation1488 G := λ x y => h x y x y
theorem Equation1604_implies_Equation1489 (G : Type*) [Magma G] (h : Equation1604 G) : Equation1489 G := λ x y => h x y x y
theorem Equation1605_implies_Equation1488 (G : Type*) [Magma G] (h : Equation1605 G) : Equation1488 G := λ x y => h x y x y
theorem Equation1606_implies_Equation1489 (G : Type*) [Magma G] (h : Equation1606 G) : Equation1489 G := λ x y => h x y x y
theorem Equation1608_implies_Equation1491 (G : Type*) [Magma G] (h : Equation1608 G) : Equation1491 G := λ x y => h x y x y
theorem Equation1609_implies_Equation1492 (G : Type*) [Magma G] (h : Equation1609 G) : Equation1492 G := λ x y => h x y x y
theorem Equation1610_implies_Equation1491 (G : Type*) [Magma G] (h : Equation1610 G) : Equation1491 G := λ x y => h x y x y
theorem Equation1611_implies_Equation1492 (G : Type*) [Magma G] (h : Equation1611 G) : Equation1492 G := λ x y => h x y x y
theorem Equation1613_implies_Equation1488 (G : Type*) [Magma G] (h : Equation1613 G) : Equation1488 G := λ x y => h x y x y
theorem Equation1614_implies_Equation1489 (G : Type*) [Magma G] (h : Equation1614 G) : Equation1489 G := λ x y => h x y x y
theorem Equation1615_implies_Equation1488 (G : Type*) [Magma G] (h : Equation1615 G) : Equation1488 G := λ x y => h x y x y
theorem Equation1616_implies_Equation1489 (G : Type*) [Magma G] (h : Equation1616 G) : Equation1489 G := λ x y => h x y x y
theorem Equation1618_implies_Equation1491 (G : Type*) [Magma G] (h : Equation1618 G) : Equation1491 G := λ x y => h x y x y
theorem Equation1619_implies_Equation1492 (G : Type*) [Magma G] (h : Equation1619 G) : Equation1492 G := λ x y => h x y x y
theorem Equation1620_implies_Equation1491 (G : Type*) [Magma G] (h : Equation1620 G) : Equation1491 G := λ x y => h x y x y
theorem Equation1621_implies_Equation1492 (G : Type*) [Magma G] (h : Equation1621 G) : Equation1492 G := λ x y => h x y x y
theorem Equation1643_implies_Equation1635 (G : Type*) [Magma G] (h : Equation1643 G) : Equation1635 G := λ x y => h x y x y
theorem Equation1653_implies_Equation1645 (G : Type*) [Magma G] (h : Equation1653 G) : Equation1645 G := λ x y => h x y x y
theorem Equation1663_implies_Equation1655 (G : Type*) [Magma G] (h : Equation1663 G) : Equation1655 G := λ x y => h x y x y
theorem Equation1667_implies_Equation1645 (G : Type*) [Magma G] (h : Equation1667 G) : Equation1645 G := λ x y => h x y x y
theorem Equation1671_implies_Equation1648 (G : Type*) [Magma G] (h : Equation1671 G) : Equation1648 G := λ x y => h x y x y
theorem Equation1675_implies_Equation1645 (G : Type*) [Magma G] (h : Equation1675 G) : Equation1645 G := λ x y => h x y x y
theorem Equation1676_implies_Equation1647 (G : Type*) [Magma G] (h : Equation1676 G) : Equation1647 G := λ x y => h x y x y
theorem Equation1677_implies_Equation1648 (G : Type*) [Magma G] (h : Equation1677 G) : Equation1648 G := λ x y => h x y x y
theorem Equation1678_implies_Equation1647 (G : Type*) [Magma G] (h : Equation1678 G) : Equation1647 G := λ x y => h x y x y
theorem Equation1679_implies_Equation1648 (G : Type*) [Magma G] (h : Equation1679 G) : Equation1648 G := λ x y => h x y x y
theorem Equation1690_implies_Equation1682 (G : Type*) [Magma G] (h : Equation1690 G) : Equation1682 G := λ x y => h x y x y
theorem Equation1700_implies_Equation1692 (G : Type*) [Magma G] (h : Equation1700 G) : Equation1692 G := λ x y => h x y x y
theorem Equation1704_implies_Equation1682 (G : Type*) [Magma G] (h : Equation1704 G) : Equation1682 G := λ x y => h x y x y
theorem Equation1708_implies_Equation1685 (G : Type*) [Magma G] (h : Equation1708 G) : Equation1685 G := λ x y => h x y x y
theorem Equation1712_implies_Equation1682 (G : Type*) [Magma G] (h : Equation1712 G) : Equation1682 G := λ x y => h x y x y
theorem Equation1713_implies_Equation1684 (G : Type*) [Magma G] (h : Equation1713 G) : Equation1684 G := λ x y => h x y x y
theorem Equation1714_implies_Equation1685 (G : Type*) [Magma G] (h : Equation1714 G) : Equation1685 G := λ x y => h x y x y
theorem Equation1715_implies_Equation1684 (G : Type*) [Magma G] (h : Equation1715 G) : Equation1684 G := λ x y => h x y x y
theorem Equation1716_implies_Equation1685 (G : Type*) [Magma G] (h : Equation1716 G) : Equation1685 G := λ x y => h x y x y
theorem Equation1727_implies_Equation1719 (G : Type*) [Magma G] (h : Equation1727 G) : Equation1719 G := λ x y => h x y x y
theorem Equation1737_implies_Equation1729 (G : Type*) [Magma G] (h : Equation1737 G) : Equation1729 G := λ x y => h x y x y
theorem Equation1741_implies_Equation1719 (G : Type*) [Magma G] (h : Equation1741 G) : Equation1719 G := λ x y => h x y x y
theorem Equation1745_implies_Equation1722 (G : Type*) [Magma G] (h : Equation1745 G) : Equation1722 G := λ x y => h x y x y
theorem Equation1749_implies_Equation1719 (G : Type*) [Magma G] (h : Equation1749 G) : Equation1719 G := λ x y => h x y x y
theorem Equation1750_implies_Equation1721 (G : Type*) [Magma G] (h : Equation1750 G) : Equation1721 G := λ x y => h x y x y
theorem Equation1751_implies_Equation1722 (G : Type*) [Magma G] (h : Equation1751 G) : Equation1722 G := λ x y => h x y x y
theorem Equation1752_implies_Equation1721 (G : Type*) [Magma G] (h : Equation1752 G) : Equation1721 G := λ x y => h x y x y
theorem Equation1753_implies_Equation1722 (G : Type*) [Magma G] (h : Equation1753 G) : Equation1722 G := λ x y => h x y x y
theorem Equation1758_implies_Equation1682 (G : Type*) [Magma G] (h : Equation1758 G) : Equation1682 G := λ x y => h x y x y
theorem Equation1762_implies_Equation1685 (G : Type*) [Magma G] (h : Equation1762 G) : Equation1685 G := λ x y => h x y x y
theorem Equation1766_implies_Equation1682 (G : Type*) [Magma G] (h : Equation1766 G) : Equation1682 G := λ x y => h x y x y
theorem Equation1767_implies_Equation1684 (G : Type*) [Magma G] (h : Equation1767 G) : Equation1684 G := λ x y => h x y x y
theorem Equation1768_implies_Equation1685 (G : Type*) [Magma G] (h : Equation1768 G) : Equation1685 G := λ x y => h x y x y
theorem Equation1769_implies_Equation1684 (G : Type*) [Magma G] (h : Equation1769 G) : Equation1684 G := λ x y => h x y x y
theorem Equation1770_implies_Equation1685 (G : Type*) [Magma G] (h : Equation1770 G) : Equation1685 G := λ x y => h x y x y
theorem Equation1775_implies_Equation1692 (G : Type*) [Magma G] (h : Equation1775 G) : Equation1692 G := λ x y => h x y x y
theorem Equation1779_implies_Equation1695 (G : Type*) [Magma G] (h : Equation1779 G) : Equation1695 G := λ x y => h x y x y
theorem Equation1783_implies_Equation1692 (G : Type*) [Magma G] (h : Equation1783 G) : Equation1692 G := λ x y => h x y x y
theorem Equation1784_implies_Equation1694 (G : Type*) [Magma G] (h : Equation1784 G) : Equation1694 G := λ x y => h x y x y
theorem Equation1785_implies_Equation1695 (G : Type*) [Magma G] (h : Equation1785 G) : Equation1695 G := λ x y => h x y x y
theorem Equation1786_implies_Equation1694 (G : Type*) [Magma G] (h : Equation1786 G) : Equation1694 G := λ x y => h x y x y
theorem Equation1787_implies_Equation1695 (G : Type*) [Magma G] (h : Equation1787 G) : Equation1695 G := λ x y => h x y x y
theorem Equation1792_implies_Equation1682 (G : Type*) [Magma G] (h : Equation1792 G) : Equation1682 G := λ x y => h x y x y
theorem Equation1796_implies_Equation1685 (G : Type*) [Magma G] (h : Equation1796 G) : Equation1685 G := λ x y => h x y x y
theorem Equation1800_implies_Equation1682 (G : Type*) [Magma G] (h : Equation1800 G) : Equation1682 G := λ x y => h x y x y
theorem Equation1801_implies_Equation1684 (G : Type*) [Magma G] (h : Equation1801 G) : Equation1684 G := λ x y => h x y x y
theorem Equation1802_implies_Equation1685 (G : Type*) [Magma G] (h : Equation1802 G) : Equation1685 G := λ x y => h x y x y
theorem Equation1803_implies_Equation1684 (G : Type*) [Magma G] (h : Equation1803 G) : Equation1684 G := λ x y => h x y x y
theorem Equation1804_implies_Equation1685 (G : Type*) [Magma G] (h : Equation1804 G) : Equation1685 G := λ x y => h x y x y
theorem Equation1806_implies_Equation1691 (G : Type*) [Magma G] (h : Equation1806 G) : Equation1691 G := λ x y => h x y x y
theorem Equation1807_implies_Equation1692 (G : Type*) [Magma G] (h : Equation1807 G) : Equation1692 G := λ x y => h x y x y
theorem Equation1808_implies_Equation1691 (G : Type*) [Magma G] (h : Equation1808 G) : Equation1691 G := λ x y => h x y x y
theorem Equation1809_implies_Equation1692 (G : Type*) [Magma G] (h : Equation1809 G) : Equation1692 G := λ x y => h x y x y
theorem Equation1811_implies_Equation1694 (G : Type*) [Magma G] (h : Equation1811 G) : Equation1694 G := λ x y => h x y x y
theorem Equation1812_implies_Equation1695 (G : Type*) [Magma G] (h : Equation1812 G) : Equation1695 G := λ x y => h x y x y
theorem Equation1813_implies_Equation1694 (G : Type*) [Magma G] (h : Equation1813 G) : Equation1694 G := λ x y => h x y x y
theorem Equation1814_implies_Equation1695 (G : Type*) [Magma G] (h : Equation1814 G) : Equation1695 G := λ x y => h x y x y
theorem Equation1816_implies_Equation1691 (G : Type*) [Magma G] (h : Equation1816 G) : Equation1691 G := λ x y => h x y x y
theorem Equation1817_implies_Equation1692 (G : Type*) [Magma G] (h : Equation1817 G) : Equation1692 G := λ x y => h x y x y
theorem Equation1818_implies_Equation1691 (G : Type*) [Magma G] (h : Equation1818 G) : Equation1691 G := λ x y => h x y x y
theorem Equation1819_implies_Equation1692 (G : Type*) [Magma G] (h : Equation1819 G) : Equation1692 G := λ x y => h x y x y
theorem Equation1821_implies_Equation1694 (G : Type*) [Magma G] (h : Equation1821 G) : Equation1694 G := λ x y => h x y x y
theorem Equation1822_implies_Equation1695 (G : Type*) [Magma G] (h : Equation1822 G) : Equation1695 G := λ x y => h x y x y
theorem Equation1823_implies_Equation1694 (G : Type*) [Magma G] (h : Equation1823 G) : Equation1694 G := λ x y => h x y x y
theorem Equation1824_implies_Equation1695 (G : Type*) [Magma G] (h : Equation1824 G) : Equation1695 G := λ x y => h x y x y
theorem Equation1846_implies_Equation1838 (G : Type*) [Magma G] (h : Equation1846 G) : Equation1838 G := λ x y => h x y x y
theorem Equation1856_implies_Equation1848 (G : Type*) [Magma G] (h : Equation1856 G) : Equation1848 G := λ x y => h x y x y
theorem Equation1866_implies_Equation1858 (G : Type*) [Magma G] (h : Equation1866 G) : Equation1858 G := λ x y => h x y x y
theorem Equation1870_implies_Equation1848 (G : Type*) [Magma G] (h : Equation1870 G) : Equation1848 G := λ x y => h x y x y
theorem Equation1874_implies_Equation1851 (G : Type*) [Magma G] (h : Equation1874 G) : Equation1851 G := λ x y => h x y x y
theorem Equation1878_implies_Equation1848 (G : Type*) [Magma G] (h : Equation1878 G) : Equation1848 G := λ x y => h x y x y
theorem Equation1879_implies_Equation1850 (G : Type*) [Magma G] (h : Equation1879 G) : Equation1850 G := λ x y => h x y x y
theorem Equation1880_implies_Equation1851 (G : Type*) [Magma G] (h : Equation1880 G) : Equation1851 G := λ x y => h x y x y
theorem Equation1881_implies_Equation1850 (G : Type*) [Magma G] (h : Equation1881 G) : Equation1850 G := λ x y => h x y x y
theorem Equation1882_implies_Equation1851 (G : Type*) [Magma G] (h : Equation1882 G) : Equation1851 G := λ x y => h x y x y
theorem Equation1893_implies_Equation1885 (G : Type*) [Magma G] (h : Equation1893 G) : Equation1885 G := λ x y => h x y x y
theorem Equation1903_implies_Equation1895 (G : Type*) [Magma G] (h : Equation1903 G) : Equation1895 G := λ x y => h x y x y
theorem Equation1907_implies_Equation1885 (G : Type*) [Magma G] (h : Equation1907 G) : Equation1885 G := λ x y => h x y x y
theorem Equation1911_implies_Equation1888 (G : Type*) [Magma G] (h : Equation1911 G) : Equation1888 G := λ x y => h x y x y
theorem Equation1915_implies_Equation1885 (G : Type*) [Magma G] (h : Equation1915 G) : Equation1885 G := λ x y => h x y x y
theorem Equation1916_implies_Equation1887 (G : Type*) [Magma G] (h : Equation1916 G) : Equation1887 G := λ x y => h x y x y
theorem Equation1917_implies_Equation1888 (G : Type*) [Magma G] (h : Equation1917 G) : Equation1888 G := λ x y => h x y x y
theorem Equation1918_implies_Equation1887 (G : Type*) [Magma G] (h : Equation1918 G) : Equation1887 G := λ x y => h x y x y
theorem Equation1919_implies_Equation1888 (G : Type*) [Magma G] (h : Equation1919 G) : Equation1888 G := λ x y => h x y x y
theorem Equation1930_implies_Equation1922 (G : Type*) [Magma G] (h : Equation1930 G) : Equation1922 G := λ x y => h x y x y
theorem Equation1940_implies_Equation1932 (G : Type*) [Magma G] (h : Equation1940 G) : Equation1932 G := λ x y => h x y x y
theorem Equation1944_implies_Equation1922 (G : Type*) [Magma G] (h : Equation1944 G) : Equation1922 G := λ x y => h x y x y
theorem Equation1948_implies_Equation1925 (G : Type*) [Magma G] (h : Equation1948 G) : Equation1925 G := λ x y => h x y x y
theorem Equation1952_implies_Equation1922 (G : Type*) [Magma G] (h : Equation1952 G) : Equation1922 G := λ x y => h x y x y
theorem Equation1953_implies_Equation1924 (G : Type*) [Magma G] (h : Equation1953 G) : Equation1924 G := λ x y => h x y x y
theorem Equation1954_implies_Equation1925 (G : Type*) [Magma G] (h : Equation1954 G) : Equation1925 G := λ x y => h x y x y
theorem Equation1955_implies_Equation1924 (G : Type*) [Magma G] (h : Equation1955 G) : Equation1924 G := λ x y => h x y x y
theorem Equation1956_implies_Equation1925 (G : Type*) [Magma G] (h : Equation1956 G) : Equation1925 G := λ x y => h x y x y
theorem Equation1961_implies_Equation1885 (G : Type*) [Magma G] (h : Equation1961 G) : Equation1885 G := λ x y => h x y x y
theorem Equation1965_implies_Equation1888 (G : Type*) [Magma G] (h : Equation1965 G) : Equation1888 G := λ x y => h x y x y
theorem Equation1969_implies_Equation1885 (G : Type*) [Magma G] (h : Equation1969 G) : Equation1885 G := λ x y => h x y x y
theorem Equation1970_implies_Equation1887 (G : Type*) [Magma G] (h : Equation1970 G) : Equation1887 G := λ x y => h x y x y
theorem Equation1971_implies_Equation1888 (G : Type*) [Magma G] (h : Equation1971 G) : Equation1888 G := λ x y => h x y x y
theorem Equation1972_implies_Equation1887 (G : Type*) [Magma G] (h : Equation1972 G) : Equation1887 G := λ x y => h x y x y
theorem Equation1973_implies_Equation1888 (G : Type*) [Magma G] (h : Equation1973 G) : Equation1888 G := λ x y => h x y x y
theorem Equation1978_implies_Equation1895 (G : Type*) [Magma G] (h : Equation1978 G) : Equation1895 G := λ x y => h x y x y
theorem Equation1982_implies_Equation1898 (G : Type*) [Magma G] (h : Equation1982 G) : Equation1898 G := λ x y => h x y x y
theorem Equation1986_implies_Equation1895 (G : Type*) [Magma G] (h : Equation1986 G) : Equation1895 G := λ x y => h x y x y
theorem Equation1987_implies_Equation1897 (G : Type*) [Magma G] (h : Equation1987 G) : Equation1897 G := λ x y => h x y x y
theorem Equation1988_implies_Equation1898 (G : Type*) [Magma G] (h : Equation1988 G) : Equation1898 G := λ x y => h x y x y
theorem Equation1989_implies_Equation1897 (G : Type*) [Magma G] (h : Equation1989 G) : Equation1897 G := λ x y => h x y x y
theorem Equation1990_implies_Equation1898 (G : Type*) [Magma G] (h : Equation1990 G) : Equation1898 G := λ x y => h x y x y
theorem Equation1995_implies_Equation1885 (G : Type*) [Magma G] (h : Equation1995 G) : Equation1885 G := λ x y => h x y x y
theorem Equation1999_implies_Equation1888 (G : Type*) [Magma G] (h : Equation1999 G) : Equation1888 G := λ x y => h x y x y
theorem Equation2003_implies_Equation1885 (G : Type*) [Magma G] (h : Equation2003 G) : Equation1885 G := λ x y => h x y x y
theorem Equation2004_implies_Equation1887 (G : Type*) [Magma G] (h : Equation2004 G) : Equation1887 G := λ x y => h x y x y
theorem Equation2005_implies_Equation1888 (G : Type*) [Magma G] (h : Equation2005 G) : Equation1888 G := λ x y => h x y x y
theorem Equation2006_implies_Equation1887 (G : Type*) [Magma G] (h : Equation2006 G) : Equation1887 G := λ x y => h x y x y
theorem Equation2007_implies_Equation1888 (G : Type*) [Magma G] (h : Equation2007 G) : Equation1888 G := λ x y => h x y x y
theorem Equation2009_implies_Equation1894 (G : Type*) [Magma G] (h : Equation2009 G) : Equation1894 G := λ x y => h x y x y
theorem Equation2010_implies_Equation1895 (G : Type*) [Magma G] (h : Equation2010 G) : Equation1895 G := λ x y => h x y x y
theorem Equation2011_implies_Equation1894 (G : Type*) [Magma G] (h : Equation2011 G) : Equation1894 G := λ x y => h x y x y
theorem Equation2012_implies_Equation1895 (G : Type*) [Magma G] (h : Equation2012 G) : Equation1895 G := λ x y => h x y x y
theorem Equation2014_implies_Equation1897 (G : Type*) [Magma G] (h : Equation2014 G) : Equation1897 G := λ x y => h x y x y
theorem Equation2015_implies_Equation1898 (G : Type*) [Magma G] (h : Equation2015 G) : Equation1898 G := λ x y => h x y x y
theorem Equation2016_implies_Equation1897 (G : Type*) [Magma G] (h : Equation2016 G) : Equation1897 G := λ x y => h x y x y
theorem Equation2017_implies_Equation1898 (G : Type*) [Magma G] (h : Equation2017 G) : Equation1898 G := λ x y => h x y x y
theorem Equation2019_implies_Equation1894 (G : Type*) [Magma G] (h : Equation2019 G) : Equation1894 G := λ x y => h x y x y
theorem Equation2020_implies_Equation1895 (G : Type*) [Magma G] (h : Equation2020 G) : Equation1895 G := λ x y => h x y x y
theorem Equation2021_implies_Equation1894 (G : Type*) [Magma G] (h : Equation2021 G) : Equation1894 G := λ x y => h x y x y
theorem Equation2022_implies_Equation1895 (G : Type*) [Magma G] (h : Equation2022 G) : Equation1895 G := λ x y => h x y x y
theorem Equation2024_implies_Equation1897 (G : Type*) [Magma G] (h : Equation2024 G) : Equation1897 G := λ x y => h x y x y
theorem Equation2025_implies_Equation1898 (G : Type*) [Magma G] (h : Equation2025 G) : Equation1898 G := λ x y => h x y x y
theorem Equation2026_implies_Equation1897 (G : Type*) [Magma G] (h : Equation2026 G) : Equation1897 G := λ x y => h x y x y
theorem Equation2027_implies_Equation1898 (G : Type*) [Magma G] (h : Equation2027 G) : Equation1898 G := λ x y => h x y x y
theorem Equation2049_implies_Equation2041 (G : Type*) [Magma G] (h : Equation2049 G) : Equation2041 G := λ x y => h x y x y
theorem Equation2059_implies_Equation2051 (G : Type*) [Magma G] (h : Equation2059 G) : Equation2051 G := λ x y => h x y x y
theorem Equation2069_implies_Equation2061 (G : Type*) [Magma G] (h : Equation2069 G) : Equation2061 G := λ x y => h x y x y
theorem Equation2073_implies_Equation2051 (G : Type*) [Magma G] (h : Equation2073 G) : Equation2051 G := λ x y => h x y x y
theorem Equation2077_implies_Equation2054 (G : Type*) [Magma G] (h : Equation2077 G) : Equation2054 G := λ x y => h x y x y
theorem Equation2081_implies_Equation2051 (G : Type*) [Magma G] (h : Equation2081 G) : Equation2051 G := λ x y => h x y x y
theorem Equation2082_implies_Equation2053 (G : Type*) [Magma G] (h : Equation2082 G) : Equation2053 G := λ x y => h x y x y
theorem Equation2083_implies_Equation2054 (G : Type*) [Magma G] (h : Equation2083 G) : Equation2054 G := λ x y => h x y x y
theorem Equation2084_implies_Equation2053 (G : Type*) [Magma G] (h : Equation2084 G) : Equation2053 G := λ x y => h x y x y
theorem Equation2085_implies_Equation2054 (G : Type*) [Magma G] (h : Equation2085 G) : Equation2054 G := λ x y => h x y x y
theorem Equation2096_implies_Equation2088 (G : Type*) [Magma G] (h : Equation2096 G) : Equation2088 G := λ x y => h x y x y
theorem Equation2106_implies_Equation2098 (G : Type*) [Magma G] (h : Equation2106 G) : Equation2098 G := λ x y => h x y x y
theorem Equation2110_implies_Equation2088 (G : Type*) [Magma G] (h : Equation2110 G) : Equation2088 G := λ x y => h x y x y
theorem Equation2114_implies_Equation2091 (G : Type*) [Magma G] (h : Equation2114 G) : Equation2091 G := λ x y => h x y x y
theorem Equation2118_implies_Equation2088 (G : Type*) [Magma G] (h : Equation2118 G) : Equation2088 G := λ x y => h x y x y
theorem Equation2119_implies_Equation2090 (G : Type*) [Magma G] (h : Equation2119 G) : Equation2090 G := λ x y => h x y x y
theorem Equation2120_implies_Equation2091 (G : Type*) [Magma G] (h : Equation2120 G) : Equation2091 G := λ x y => h x y x y
theorem Equation2121_implies_Equation2090 (G : Type*) [Magma G] (h : Equation2121 G) : Equation2090 G := λ x y => h x y x y
theorem Equation2122_implies_Equation2091 (G : Type*) [Magma G] (h : Equation2122 G) : Equation2091 G := λ x y => h x y x y
theorem Equation2133_implies_Equation2125 (G : Type*) [Magma G] (h : Equation2133 G) : Equation2125 G := λ x y => h x y x y
theorem Equation2143_implies_Equation2135 (G : Type*) [Magma G] (h : Equation2143 G) : Equation2135 G := λ x y => h x y x y
theorem Equation2147_implies_Equation2125 (G : Type*) [Magma G] (h : Equation2147 G) : Equation2125 G := λ x y => h x y x y
theorem Equation2151_implies_Equation2128 (G : Type*) [Magma G] (h : Equation2151 G) : Equation2128 G := λ x y => h x y x y
theorem Equation2155_implies_Equation2125 (G : Type*) [Magma G] (h : Equation2155 G) : Equation2125 G := λ x y => h x y x y
theorem Equation2156_implies_Equation2127 (G : Type*) [Magma G] (h : Equation2156 G) : Equation2127 G := λ x y => h x y x y
theorem Equation2157_implies_Equation2128 (G : Type*) [Magma G] (h : Equation2157 G) : Equation2128 G := λ x y => h x y x y
theorem Equation2158_implies_Equation2127 (G : Type*) [Magma G] (h : Equation2158 G) : Equation2127 G := λ x y => h x y x y
theorem Equation2159_implies_Equation2128 (G : Type*) [Magma G] (h : Equation2159 G) : Equation2128 G := λ x y => h x y x y
theorem Equation2164_implies_Equation2088 (G : Type*) [Magma G] (h : Equation2164 G) : Equation2088 G := λ x y => h x y x y
theorem Equation2168_implies_Equation2091 (G : Type*) [Magma G] (h : Equation2168 G) : Equation2091 G := λ x y => h x y x y
theorem Equation2172_implies_Equation2088 (G : Type*) [Magma G] (h : Equation2172 G) : Equation2088 G := λ x y => h x y x y
theorem Equation2173_implies_Equation2090 (G : Type*) [Magma G] (h : Equation2173 G) : Equation2090 G := λ x y => h x y x y
theorem Equation2174_implies_Equation2091 (G : Type*) [Magma G] (h : Equation2174 G) : Equation2091 G := λ x y => h x y x y
theorem Equation2175_implies_Equation2090 (G : Type*) [Magma G] (h : Equation2175 G) : Equation2090 G := λ x y => h x y x y
theorem Equation2176_implies_Equation2091 (G : Type*) [Magma G] (h : Equation2176 G) : Equation2091 G := λ x y => h x y x y
theorem Equation2181_implies_Equation2098 (G : Type*) [Magma G] (h : Equation2181 G) : Equation2098 G := λ x y => h x y x y
theorem Equation2185_implies_Equation2101 (G : Type*) [Magma G] (h : Equation2185 G) : Equation2101 G := λ x y => h x y x y
theorem Equation2189_implies_Equation2098 (G : Type*) [Magma G] (h : Equation2189 G) : Equation2098 G := λ x y => h x y x y
theorem Equation2190_implies_Equation2100 (G : Type*) [Magma G] (h : Equation2190 G) : Equation2100 G := λ x y => h x y x y
theorem Equation2191_implies_Equation2101 (G : Type*) [Magma G] (h : Equation2191 G) : Equation2101 G := λ x y => h x y x y
theorem Equation2192_implies_Equation2100 (G : Type*) [Magma G] (h : Equation2192 G) : Equation2100 G := λ x y => h x y x y
theorem Equation2193_implies_Equation2101 (G : Type*) [Magma G] (h : Equation2193 G) : Equation2101 G := λ x y => h x y x y
theorem Equation2198_implies_Equation2088 (G : Type*) [Magma G] (h : Equation2198 G) : Equation2088 G := λ x y => h x y x y
theorem Equation2202_implies_Equation2091 (G : Type*) [Magma G] (h : Equation2202 G) : Equation2091 G := λ x y => h x y x y
theorem Equation2206_implies_Equation2088 (G : Type*) [Magma G] (h : Equation2206 G) : Equation2088 G := λ x y => h x y x y
theorem Equation2207_implies_Equation2090 (G : Type*) [Magma G] (h : Equation2207 G) : Equation2090 G := λ x y => h x y x y
theorem Equation2208_implies_Equation2091 (G : Type*) [Magma G] (h : Equation2208 G) : Equation2091 G := λ x y => h x y x y
theorem Equation2209_implies_Equation2090 (G : Type*) [Magma G] (h : Equation2209 G) : Equation2090 G := λ x y => h x y x y
theorem Equation2210_implies_Equation2091 (G : Type*) [Magma G] (h : Equation2210 G) : Equation2091 G := λ x y => h x y x y
theorem Equation2212_implies_Equation2097 (G : Type*) [Magma G] (h : Equation2212 G) : Equation2097 G := λ x y => h x y x y
theorem Equation2213_implies_Equation2098 (G : Type*) [Magma G] (h : Equation2213 G) : Equation2098 G := λ x y => h x y x y
theorem Equation2214_implies_Equation2097 (G : Type*) [Magma G] (h : Equation2214 G) : Equation2097 G := λ x y => h x y x y
theorem Equation2215_implies_Equation2098 (G : Type*) [Magma G] (h : Equation2215 G) : Equation2098 G := λ x y => h x y x y
theorem Equation2217_implies_Equation2100 (G : Type*) [Magma G] (h : Equation2217 G) : Equation2100 G := λ x y => h x y x y
theorem Equation2218_implies_Equation2101 (G : Type*) [Magma G] (h : Equation2218 G) : Equation2101 G := λ x y => h x y x y
theorem Equation2219_implies_Equation2100 (G : Type*) [Magma G] (h : Equation2219 G) : Equation2100 G := λ x y => h x y x y
theorem Equation2220_implies_Equation2101 (G : Type*) [Magma G] (h : Equation2220 G) : Equation2101 G := λ x y => h x y x y
theorem Equation2222_implies_Equation2097 (G : Type*) [Magma G] (h : Equation2222 G) : Equation2097 G := λ x y => h x y x y
theorem Equation2223_implies_Equation2098 (G : Type*) [Magma G] (h : Equation2223 G) : Equation2098 G := λ x y => h x y x y
theorem Equation2224_implies_Equation2097 (G : Type*) [Magma G] (h : Equation2224 G) : Equation2097 G := λ x y => h x y x y
theorem Equation2225_implies_Equation2098 (G : Type*) [Magma G] (h : Equation2225 G) : Equation2098 G := λ x y => h x y x y
theorem Equation2227_implies_Equation2100 (G : Type*) [Magma G] (h : Equation2227 G) : Equation2100 G := λ x y => h x y x y
theorem Equation2228_implies_Equation2101 (G : Type*) [Magma G] (h : Equation2228 G) : Equation2101 G := λ x y => h x y x y
theorem Equation2229_implies_Equation2100 (G : Type*) [Magma G] (h : Equation2229 G) : Equation2100 G := λ x y => h x y x y
theorem Equation2230_implies_Equation2101 (G : Type*) [Magma G] (h : Equation2230 G) : Equation2101 G := λ x y => h x y x y
theorem Equation2252_implies_Equation2244 (G : Type*) [Magma G] (h : Equation2252 G) : Equation2244 G := λ x y => h x y x y
theorem Equation2262_implies_Equation2254 (G : Type*) [Magma G] (h : Equation2262 G) : Equation2254 G := λ x y => h x y x y
theorem Equation2272_implies_Equation2264 (G : Type*) [Magma G] (h : Equation2272 G) : Equation2264 G := λ x y => h x y x y
theorem Equation2276_implies_Equation2254 (G : Type*) [Magma G] (h : Equation2276 G) : Equation2254 G := λ x y => h x y x y
theorem Equation2280_implies_Equation2257 (G : Type*) [Magma G] (h : Equation2280 G) : Equation2257 G := λ x y => h x y x y
theorem Equation2284_implies_Equation2254 (G : Type*) [Magma G] (h : Equation2284 G) : Equation2254 G := λ x y => h x y x y
theorem Equation2285_implies_Equation2256 (G : Type*) [Magma G] (h : Equation2285 G) : Equation2256 G := λ x y => h x y x y
theorem Equation2286_implies_Equation2257 (G : Type*) [Magma G] (h : Equation2286 G) : Equation2257 G := λ x y => h x y x y
theorem Equation2287_implies_Equation2256 (G : Type*) [Magma G] (h : Equation2287 G) : Equation2256 G := λ x y => h x y x y
theorem Equation2288_implies_Equation2257 (G : Type*) [Magma G] (h : Equation2288 G) : Equation2257 G := λ x y => h x y x y
theorem Equation2299_implies_Equation2291 (G : Type*) [Magma G] (h : Equation2299 G) : Equation2291 G := λ x y => h x y x y
theorem Equation2309_implies_Equation2301 (G : Type*) [Magma G] (h : Equation2309 G) : Equation2301 G := λ x y => h x y x y
theorem Equation2313_implies_Equation2291 (G : Type*) [Magma G] (h : Equation2313 G) : Equation2291 G := λ x y => h x y x y
theorem Equation2317_implies_Equation2294 (G : Type*) [Magma G] (h : Equation2317 G) : Equation2294 G := λ x y => h x y x y
theorem Equation2321_implies_Equation2291 (G : Type*) [Magma G] (h : Equation2321 G) : Equation2291 G := λ x y => h x y x y
theorem Equation2322_implies_Equation2293 (G : Type*) [Magma G] (h : Equation2322 G) : Equation2293 G := λ x y => h x y x y
theorem Equation2323_implies_Equation2294 (G : Type*) [Magma G] (h : Equation2323 G) : Equation2294 G := λ x y => h x y x y
theorem Equation2324_implies_Equation2293 (G : Type*) [Magma G] (h : Equation2324 G) : Equation2293 G := λ x y => h x y x y
theorem Equation2325_implies_Equation2294 (G : Type*) [Magma G] (h : Equation2325 G) : Equation2294 G := λ x y => h x y x y
theorem Equation2336_implies_Equation2328 (G : Type*) [Magma G] (h : Equation2336 G) : Equation2328 G := λ x y => h x y x y
theorem Equation2346_implies_Equation2338 (G : Type*) [Magma G] (h : Equation2346 G) : Equation2338 G := λ x y => h x y x y
theorem Equation2350_implies_Equation2328 (G : Type*) [Magma G] (h : Equation2350 G) : Equation2328 G := λ x y => h x y x y
theorem Equation2354_implies_Equation2331 (G : Type*) [Magma G] (h : Equation2354 G) : Equation2331 G := λ x y => h x y x y
theorem Equation2358_implies_Equation2328 (G : Type*) [Magma G] (h : Equation2358 G) : Equation2328 G := λ x y => h x y x y
theorem Equation2359_implies_Equation2330 (G : Type*) [Magma G] (h : Equation2359 G) : Equation2330 G := λ x y => h x y x y
theorem Equation2360_implies_Equation2331 (G : Type*) [Magma G] (h : Equation2360 G) : Equation2331 G := λ x y => h x y x y
theorem Equation2361_implies_Equation2330 (G : Type*) [Magma G] (h : Equation2361 G) : Equation2330 G := λ x y => h x y x y
theorem Equation2362_implies_Equation2331 (G : Type*) [Magma G] (h : Equation2362 G) : Equation2331 G := λ x y => h x y x y
theorem Equation2367_implies_Equation2291 (G : Type*) [Magma G] (h : Equation2367 G) : Equation2291 G := λ x y => h x y x y
theorem Equation2371_implies_Equation2294 (G : Type*) [Magma G] (h : Equation2371 G) : Equation2294 G := λ x y => h x y x y
theorem Equation2375_implies_Equation2291 (G : Type*) [Magma G] (h : Equation2375 G) : Equation2291 G := λ x y => h x y x y
theorem Equation2376_implies_Equation2293 (G : Type*) [Magma G] (h : Equation2376 G) : Equation2293 G := λ x y => h x y x y
theorem Equation2377_implies_Equation2294 (G : Type*) [Magma G] (h : Equation2377 G) : Equation2294 G := λ x y => h x y x y
theorem Equation2378_implies_Equation2293 (G : Type*) [Magma G] (h : Equation2378 G) : Equation2293 G := λ x y => h x y x y
theorem Equation2379_implies_Equation2294 (G : Type*) [Magma G] (h : Equation2379 G) : Equation2294 G := λ x y => h x y x y
theorem Equation2384_implies_Equation2301 (G : Type*) [Magma G] (h : Equation2384 G) : Equation2301 G := λ x y => h x y x y
theorem Equation2388_implies_Equation2304 (G : Type*) [Magma G] (h : Equation2388 G) : Equation2304 G := λ x y => h x y x y
theorem Equation2392_implies_Equation2301 (G : Type*) [Magma G] (h : Equation2392 G) : Equation2301 G := λ x y => h x y x y
theorem Equation2393_implies_Equation2303 (G : Type*) [Magma G] (h : Equation2393 G) : Equation2303 G := λ x y => h x y x y
theorem Equation2394_implies_Equation2304 (G : Type*) [Magma G] (h : Equation2394 G) : Equation2304 G := λ x y => h x y x y
theorem Equation2395_implies_Equation2303 (G : Type*) [Magma G] (h : Equation2395 G) : Equation2303 G := λ x y => h x y x y
theorem Equation2396_implies_Equation2304 (G : Type*) [Magma G] (h : Equation2396 G) : Equation2304 G := λ x y => h x y x y
theorem Equation2401_implies_Equation2291 (G : Type*) [Magma G] (h : Equation2401 G) : Equation2291 G := λ x y => h x y x y
theorem Equation2405_implies_Equation2294 (G : Type*) [Magma G] (h : Equation2405 G) : Equation2294 G := λ x y => h x y x y
theorem Equation2409_implies_Equation2291 (G : Type*) [Magma G] (h : Equation2409 G) : Equation2291 G := λ x y => h x y x y
theorem Equation2410_implies_Equation2293 (G : Type*) [Magma G] (h : Equation2410 G) : Equation2293 G := λ x y => h x y x y
theorem Equation2411_implies_Equation2294 (G : Type*) [Magma G] (h : Equation2411 G) : Equation2294 G := λ x y => h x y x y
theorem Equation2412_implies_Equation2293 (G : Type*) [Magma G] (h : Equation2412 G) : Equation2293 G := λ x y => h x y x y
theorem Equation2413_implies_Equation2294 (G : Type*) [Magma G] (h : Equation2413 G) : Equation2294 G := λ x y => h x y x y
theorem Equation2415_implies_Equation2300 (G : Type*) [Magma G] (h : Equation2415 G) : Equation2300 G := λ x y => h x y x y
theorem Equation2416_implies_Equation2301 (G : Type*) [Magma G] (h : Equation2416 G) : Equation2301 G := λ x y => h x y x y
theorem Equation2417_implies_Equation2300 (G : Type*) [Magma G] (h : Equation2417 G) : Equation2300 G := λ x y => h x y x y
theorem Equation2418_implies_Equation2301 (G : Type*) [Magma G] (h : Equation2418 G) : Equation2301 G := λ x y => h x y x y
theorem Equation2420_implies_Equation2303 (G : Type*) [Magma G] (h : Equation2420 G) : Equation2303 G := λ x y => h x y x y
theorem Equation2421_implies_Equation2304 (G : Type*) [Magma G] (h : Equation2421 G) : Equation2304 G := λ x y => h x y x y
theorem Equation2422_implies_Equation2303 (G : Type*) [Magma G] (h : Equation2422 G) : Equation2303 G := λ x y => h x y x y
theorem Equation2423_implies_Equation2304 (G : Type*) [Magma G] (h : Equation2423 G) : Equation2304 G := λ x y => h x y x y
theorem Equation2425_implies_Equation2300 (G : Type*) [Magma G] (h : Equation2425 G) : Equation2300 G := λ x y => h x y x y
theorem Equation2426_implies_Equation2301 (G : Type*) [Magma G] (h : Equation2426 G) : Equation2301 G := λ x y => h x y x y
theorem Equation2427_implies_Equation2300 (G : Type*) [Magma G] (h : Equation2427 G) : Equation2300 G := λ x y => h x y x y
theorem Equation2428_implies_Equation2301 (G : Type*) [Magma G] (h : Equation2428 G) : Equation2301 G := λ x y => h x y x y
theorem Equation2430_implies_Equation2303 (G : Type*) [Magma G] (h : Equation2430 G) : Equation2303 G := λ x y => h x y x y
theorem Equation2431_implies_Equation2304 (G : Type*) [Magma G] (h : Equation2431 G) : Equation2304 G := λ x y => h x y x y
theorem Equation2432_implies_Equation2303 (G : Type*) [Magma G] (h : Equation2432 G) : Equation2303 G := λ x y => h x y x y
theorem Equation2433_implies_Equation2304 (G : Type*) [Magma G] (h : Equation2433 G) : Equation2304 G := λ x y => h x y x y
theorem Equation2455_implies_Equation2447 (G : Type*) [Magma G] (h : Equation2455 G) : Equation2447 G := λ x y => h x y x y
theorem Equation2465_implies_Equation2457 (G : Type*) [Magma G] (h : Equation2465 G) : Equation2457 G := λ x y => h x y x y
theorem Equation2475_implies_Equation2467 (G : Type*) [Magma G] (h : Equation2475 G) : Equation2467 G := λ x y => h x y x y
theorem Equation2479_implies_Equation2457 (G : Type*) [Magma G] (h : Equation2479 G) : Equation2457 G := λ x y => h x y x y
theorem Equation2483_implies_Equation2460 (G : Type*) [Magma G] (h : Equation2483 G) : Equation2460 G := λ x y => h x y x y
theorem Equation2487_implies_Equation2457 (G : Type*) [Magma G] (h : Equation2487 G) : Equation2457 G := λ x y => h x y x y
theorem Equation2488_implies_Equation2459 (G : Type*) [Magma G] (h : Equation2488 G) : Equation2459 G := λ x y => h x y x y
theorem Equation2489_implies_Equation2460 (G : Type*) [Magma G] (h : Equation2489 G) : Equation2460 G := λ x y => h x y x y
theorem Equation2490_implies_Equation2459 (G : Type*) [Magma G] (h : Equation2490 G) : Equation2459 G := λ x y => h x y x y
theorem Equation2491_implies_Equation2460 (G : Type*) [Magma G] (h : Equation2491 G) : Equation2460 G := λ x y => h x y x y
theorem Equation2502_implies_Equation2494 (G : Type*) [Magma G] (h : Equation2502 G) : Equation2494 G := λ x y => h x y x y
theorem Equation2512_implies_Equation2504 (G : Type*) [Magma G] (h : Equation2512 G) : Equation2504 G := λ x y => h x y x y
theorem Equation2516_implies_Equation2494 (G : Type*) [Magma G] (h : Equation2516 G) : Equation2494 G := λ x y => h x y x y
theorem Equation2520_implies_Equation2497 (G : Type*) [Magma G] (h : Equation2520 G) : Equation2497 G := λ x y => h x y x y
theorem Equation2524_implies_Equation2494 (G : Type*) [Magma G] (h : Equation2524 G) : Equation2494 G := λ x y => h x y x y
theorem Equation2525_implies_Equation2496 (G : Type*) [Magma G] (h : Equation2525 G) : Equation2496 G := λ x y => h x y x y
theorem Equation2526_implies_Equation2497 (G : Type*) [Magma G] (h : Equation2526 G) : Equation2497 G := λ x y => h x y x y
theorem Equation2527_implies_Equation2496 (G : Type*) [Magma G] (h : Equation2527 G) : Equation2496 G := λ x y => h x y x y
theorem Equation2528_implies_Equation2497 (G : Type*) [Magma G] (h : Equation2528 G) : Equation2497 G := λ x y => h x y x y
theorem Equation2539_implies_Equation2531 (G : Type*) [Magma G] (h : Equation2539 G) : Equation2531 G := λ x y => h x y x y
theorem Equation2549_implies_Equation2541 (G : Type*) [Magma G] (h : Equation2549 G) : Equation2541 G := λ x y => h x y x y
theorem Equation2553_implies_Equation2531 (G : Type*) [Magma G] (h : Equation2553 G) : Equation2531 G := λ x y => h x y x y
theorem Equation2557_implies_Equation2534 (G : Type*) [Magma G] (h : Equation2557 G) : Equation2534 G := λ x y => h x y x y
theorem Equation2561_implies_Equation2531 (G : Type*) [Magma G] (h : Equation2561 G) : Equation2531 G := λ x y => h x y x y
theorem Equation2562_implies_Equation2533 (G : Type*) [Magma G] (h : Equation2562 G) : Equation2533 G := λ x y => h x y x y
theorem Equation2563_implies_Equation2534 (G : Type*) [Magma G] (h : Equation2563 G) : Equation2534 G := λ x y => h x y x y
theorem Equation2564_implies_Equation2533 (G : Type*) [Magma G] (h : Equation2564 G) : Equation2533 G := λ x y => h x y x y
theorem Equation2565_implies_Equation2534 (G : Type*) [Magma G] (h : Equation2565 G) : Equation2534 G := λ x y => h x y x y
theorem Equation2570_implies_Equation2494 (G : Type*) [Magma G] (h : Equation2570 G) : Equation2494 G := λ x y => h x y x y
theorem Equation2574_implies_Equation2497 (G : Type*) [Magma G] (h : Equation2574 G) : Equation2497 G := λ x y => h x y x y
theorem Equation2578_implies_Equation2494 (G : Type*) [Magma G] (h : Equation2578 G) : Equation2494 G := λ x y => h x y x y
theorem Equation2579_implies_Equation2496 (G : Type*) [Magma G] (h : Equation2579 G) : Equation2496 G := λ x y => h x y x y
theorem Equation2580_implies_Equation2497 (G : Type*) [Magma G] (h : Equation2580 G) : Equation2497 G := λ x y => h x y x y
theorem Equation2581_implies_Equation2496 (G : Type*) [Magma G] (h : Equation2581 G) : Equation2496 G := λ x y => h x y x y
theorem Equation2582_implies_Equation2497 (G : Type*) [Magma G] (h : Equation2582 G) : Equation2497 G := λ x y => h x y x y
theorem Equation2587_implies_Equation2504 (G : Type*) [Magma G] (h : Equation2587 G) : Equation2504 G := λ x y => h x y x y
theorem Equation2591_implies_Equation2507 (G : Type*) [Magma G] (h : Equation2591 G) : Equation2507 G := λ x y => h x y x y
theorem Equation2595_implies_Equation2504 (G : Type*) [Magma G] (h : Equation2595 G) : Equation2504 G := λ x y => h x y x y
theorem Equation2596_implies_Equation2506 (G : Type*) [Magma G] (h : Equation2596 G) : Equation2506 G := λ x y => h x y x y
theorem Equation2597_implies_Equation2507 (G : Type*) [Magma G] (h : Equation2597 G) : Equation2507 G := λ x y => h x y x y
theorem Equation2598_implies_Equation2506 (G : Type*) [Magma G] (h : Equation2598 G) : Equation2506 G := λ x y => h x y x y
theorem Equation2599_implies_Equation2507 (G : Type*) [Magma G] (h : Equation2599 G) : Equation2507 G := λ x y => h x y x y
theorem Equation2604_implies_Equation2494 (G : Type*) [Magma G] (h : Equation2604 G) : Equation2494 G := λ x y => h x y x y
theorem Equation2608_implies_Equation2497 (G : Type*) [Magma G] (h : Equation2608 G) : Equation2497 G := λ x y => h x y x y
theorem Equation2612_implies_Equation2494 (G : Type*) [Magma G] (h : Equation2612 G) : Equation2494 G := λ x y => h x y x y
theorem Equation2613_implies_Equation2496 (G : Type*) [Magma G] (h : Equation2613 G) : Equation2496 G := λ x y => h x y x y
theorem Equation2614_implies_Equation2497 (G : Type*) [Magma G] (h : Equation2614 G) : Equation2497 G := λ x y => h x y x y
theorem Equation2615_implies_Equation2496 (G : Type*) [Magma G] (h : Equation2615 G) : Equation2496 G := λ x y => h x y x y
theorem Equation2616_implies_Equation2497 (G : Type*) [Magma G] (h : Equation2616 G) : Equation2497 G := λ x y => h x y x y
theorem Equation2618_implies_Equation2503 (G : Type*) [Magma G] (h : Equation2618 G) : Equation2503 G := λ x y => h x y x y
theorem Equation2619_implies_Equation2504 (G : Type*) [Magma G] (h : Equation2619 G) : Equation2504 G := λ x y => h x y x y
theorem Equation2620_implies_Equation2503 (G : Type*) [Magma G] (h : Equation2620 G) : Equation2503 G := λ x y => h x y x y
theorem Equation2621_implies_Equation2504 (G : Type*) [Magma G] (h : Equation2621 G) : Equation2504 G := λ x y => h x y x y
theorem Equation2623_implies_Equation2506 (G : Type*) [Magma G] (h : Equation2623 G) : Equation2506 G := λ x y => h x y x y
theorem Equation2624_implies_Equation2507 (G : Type*) [Magma G] (h : Equation2624 G) : Equation2507 G := λ x y => h x y x y
theorem Equation2625_implies_Equation2506 (G : Type*) [Magma G] (h : Equation2625 G) : Equation2506 G := λ x y => h x y x y
theorem Equation2626_implies_Equation2507 (G : Type*) [Magma G] (h : Equation2626 G) : Equation2507 G := λ x y => h x y x y
theorem Equation2628_implies_Equation2503 (G : Type*) [Magma G] (h : Equation2628 G) : Equation2503 G := λ x y => h x y x y
theorem Equation2629_implies_Equation2504 (G : Type*) [Magma G] (h : Equation2629 G) : Equation2504 G := λ x y => h x y x y
theorem Equation2630_implies_Equation2503 (G : Type*) [Magma G] (h : Equation2630 G) : Equation2503 G := λ x y => h x y x y
theorem Equation2631_implies_Equation2504 (G : Type*) [Magma G] (h : Equation2631 G) : Equation2504 G := λ x y => h x y x y
theorem Equation2633_implies_Equation2506 (G : Type*) [Magma G] (h : Equation2633 G) : Equation2506 G := λ x y => h x y x y
theorem Equation2634_implies_Equation2507 (G : Type*) [Magma G] (h : Equation2634 G) : Equation2507 G := λ x y => h x y x y
theorem Equation2635_implies_Equation2506 (G : Type*) [Magma G] (h : Equation2635 G) : Equation2506 G := λ x y => h x y x y
theorem Equation2636_implies_Equation2507 (G : Type*) [Magma G] (h : Equation2636 G) : Equation2507 G := λ x y => h x y x y
theorem Equation2658_implies_Equation2650 (G : Type*) [Magma G] (h : Equation2658 G) : Equation2650 G := λ x y => h x y x y
theorem Equation2668_implies_Equation2660 (G : Type*) [Magma G] (h : Equation2668 G) : Equation2660 G := λ x y => h x y x y
theorem Equation2678_implies_Equation2670 (G : Type*) [Magma G] (h : Equation2678 G) : Equation2670 G := λ x y => h x y x y
theorem Equation2682_implies_Equation2660 (G : Type*) [Magma G] (h : Equation2682 G) : Equation2660 G := λ x y => h x y x y
theorem Equation2686_implies_Equation2663 (G : Type*) [Magma G] (h : Equation2686 G) : Equation2663 G := λ x y => h x y x y
theorem Equation2690_implies_Equation2660 (G : Type*) [Magma G] (h : Equation2690 G) : Equation2660 G := λ x y => h x y x y
theorem Equation2691_implies_Equation2662 (G : Type*) [Magma G] (h : Equation2691 G) : Equation2662 G := λ x y => h x y x y
theorem Equation2692_implies_Equation2663 (G : Type*) [Magma G] (h : Equation2692 G) : Equation2663 G := λ x y => h x y x y
theorem Equation2693_implies_Equation2662 (G : Type*) [Magma G] (h : Equation2693 G) : Equation2662 G := λ x y => h x y x y
theorem Equation2694_implies_Equation2663 (G : Type*) [Magma G] (h : Equation2694 G) : Equation2663 G := λ x y => h x y x y
theorem Equation2705_implies_Equation2697 (G : Type*) [Magma G] (h : Equation2705 G) : Equation2697 G := λ x y => h x y x y
theorem Equation2715_implies_Equation2707 (G : Type*) [Magma G] (h : Equation2715 G) : Equation2707 G := λ x y => h x y x y
theorem Equation2719_implies_Equation2697 (G : Type*) [Magma G] (h : Equation2719 G) : Equation2697 G := λ x y => h x y x y
theorem Equation2723_implies_Equation2700 (G : Type*) [Magma G] (h : Equation2723 G) : Equation2700 G := λ x y => h x y x y
theorem Equation2727_implies_Equation2697 (G : Type*) [Magma G] (h : Equation2727 G) : Equation2697 G := λ x y => h x y x y
theorem Equation2728_implies_Equation2699 (G : Type*) [Magma G] (h : Equation2728 G) : Equation2699 G := λ x y => h x y x y
theorem Equation2729_implies_Equation2700 (G : Type*) [Magma G] (h : Equation2729 G) : Equation2700 G := λ x y => h x y x y
theorem Equation2730_implies_Equation2699 (G : Type*) [Magma G] (h : Equation2730 G) : Equation2699 G := λ x y => h x y x y
theorem Equation2731_implies_Equation2700 (G : Type*) [Magma G] (h : Equation2731 G) : Equation2700 G := λ x y => h x y x y
theorem Equation2742_implies_Equation2734 (G : Type*) [Magma G] (h : Equation2742 G) : Equation2734 G := λ x y => h x y x y
theorem Equation2752_implies_Equation2744 (G : Type*) [Magma G] (h : Equation2752 G) : Equation2744 G := λ x y => h x y x y
theorem Equation2756_implies_Equation2734 (G : Type*) [Magma G] (h : Equation2756 G) : Equation2734 G := λ x y => h x y x y
theorem Equation2760_implies_Equation2737 (G : Type*) [Magma G] (h : Equation2760 G) : Equation2737 G := λ x y => h x y x y
theorem Equation2764_implies_Equation2734 (G : Type*) [Magma G] (h : Equation2764 G) : Equation2734 G := λ x y => h x y x y
theorem Equation2765_implies_Equation2736 (G : Type*) [Magma G] (h : Equation2765 G) : Equation2736 G := λ x y => h x y x y
theorem Equation2766_implies_Equation2737 (G : Type*) [Magma G] (h : Equation2766 G) : Equation2737 G := λ x y => h x y x y
theorem Equation2767_implies_Equation2736 (G : Type*) [Magma G] (h : Equation2767 G) : Equation2736 G := λ x y => h x y x y
theorem Equation2768_implies_Equation2737 (G : Type*) [Magma G] (h : Equation2768 G) : Equation2737 G := λ x y => h x y x y
theorem Equation2773_implies_Equation2697 (G : Type*) [Magma G] (h : Equation2773 G) : Equation2697 G := λ x y => h x y x y
theorem Equation2777_implies_Equation2700 (G : Type*) [Magma G] (h : Equation2777 G) : Equation2700 G := λ x y => h x y x y
theorem Equation2781_implies_Equation2697 (G : Type*) [Magma G] (h : Equation2781 G) : Equation2697 G := λ x y => h x y x y
theorem Equation2782_implies_Equation2699 (G : Type*) [Magma G] (h : Equation2782 G) : Equation2699 G := λ x y => h x y x y
theorem Equation2783_implies_Equation2700 (G : Type*) [Magma G] (h : Equation2783 G) : Equation2700 G := λ x y => h x y x y
theorem Equation2784_implies_Equation2699 (G : Type*) [Magma G] (h : Equation2784 G) : Equation2699 G := λ x y => h x y x y
theorem Equation2785_implies_Equation2700 (G : Type*) [Magma G] (h : Equation2785 G) : Equation2700 G := λ x y => h x y x y
theorem Equation2790_implies_Equation2707 (G : Type*) [Magma G] (h : Equation2790 G) : Equation2707 G := λ x y => h x y x y
theorem Equation2794_implies_Equation2710 (G : Type*) [Magma G] (h : Equation2794 G) : Equation2710 G := λ x y => h x y x y
theorem Equation2798_implies_Equation2707 (G : Type*) [Magma G] (h : Equation2798 G) : Equation2707 G := λ x y => h x y x y
theorem Equation2799_implies_Equation2709 (G : Type*) [Magma G] (h : Equation2799 G) : Equation2709 G := λ x y => h x y x y
theorem Equation2800_implies_Equation2710 (G : Type*) [Magma G] (h : Equation2800 G) : Equation2710 G := λ x y => h x y x y
theorem Equation2801_implies_Equation2709 (G : Type*) [Magma G] (h : Equation2801 G) : Equation2709 G := λ x y => h x y x y
theorem Equation2802_implies_Equation2710 (G : Type*) [Magma G] (h : Equation2802 G) : Equation2710 G := λ x y => h x y x y
theorem Equation2807_implies_Equation2697 (G : Type*) [Magma G] (h : Equation2807 G) : Equation2697 G := λ x y => h x y x y
theorem Equation2811_implies_Equation2700 (G : Type*) [Magma G] (h : Equation2811 G) : Equation2700 G := λ x y => h x y x y
theorem Equation2815_implies_Equation2697 (G : Type*) [Magma G] (h : Equation2815 G) : Equation2697 G := λ x y => h x y x y
theorem Equation2816_implies_Equation2699 (G : Type*) [Magma G] (h : Equation2816 G) : Equation2699 G := λ x y => h x y x y
theorem Equation2817_implies_Equation2700 (G : Type*) [Magma G] (h : Equation2817 G) : Equation2700 G := λ x y => h x y x y
theorem Equation2818_implies_Equation2699 (G : Type*) [Magma G] (h : Equation2818 G) : Equation2699 G := λ x y => h x y x y
theorem Equation2819_implies_Equation2700 (G : Type*) [Magma G] (h : Equation2819 G) : Equation2700 G := λ x y => h x y x y
theorem Equation2821_implies_Equation2706 (G : Type*) [Magma G] (h : Equation2821 G) : Equation2706 G := λ x y => h x y x y
theorem Equation2822_implies_Equation2707 (G : Type*) [Magma G] (h : Equation2822 G) : Equation2707 G := λ x y => h x y x y
theorem Equation2823_implies_Equation2706 (G : Type*) [Magma G] (h : Equation2823 G) : Equation2706 G := λ x y => h x y x y
theorem Equation2824_implies_Equation2707 (G : Type*) [Magma G] (h : Equation2824 G) : Equation2707 G := λ x y => h x y x y
theorem Equation2826_implies_Equation2709 (G : Type*) [Magma G] (h : Equation2826 G) : Equation2709 G := λ x y => h x y x y
theorem Equation2827_implies_Equation2710 (G : Type*) [Magma G] (h : Equation2827 G) : Equation2710 G := λ x y => h x y x y
theorem Equation2828_implies_Equation2709 (G : Type*) [Magma G] (h : Equation2828 G) : Equation2709 G := λ x y => h x y x y
theorem Equation2829_implies_Equation2710 (G : Type*) [Magma G] (h : Equation2829 G) : Equation2710 G := λ x y => h x y x y
theorem Equation2831_implies_Equation2706 (G : Type*) [Magma G] (h : Equation2831 G) : Equation2706 G := λ x y => h x y x y
theorem Equation2832_implies_Equation2707 (G : Type*) [Magma G] (h : Equation2832 G) : Equation2707 G := λ x y => h x y x y
theorem Equation2833_implies_Equation2706 (G : Type*) [Magma G] (h : Equation2833 G) : Equation2706 G := λ x y => h x y x y
theorem Equation2834_implies_Equation2707 (G : Type*) [Magma G] (h : Equation2834 G) : Equation2707 G := λ x y => h x y x y
theorem Equation2836_implies_Equation2709 (G : Type*) [Magma G] (h : Equation2836 G) : Equation2709 G := λ x y => h x y x y
theorem Equation2837_implies_Equation2710 (G : Type*) [Magma G] (h : Equation2837 G) : Equation2710 G := λ x y => h x y x y
theorem Equation2838_implies_Equation2709 (G : Type*) [Magma G] (h : Equation2838 G) : Equation2709 G := λ x y => h x y x y
theorem Equation2839_implies_Equation2710 (G : Type*) [Magma G] (h : Equation2839 G) : Equation2710 G := λ x y => h x y x y
theorem Equation2861_implies_Equation2853 (G : Type*) [Magma G] (h : Equation2861 G) : Equation2853 G := λ x y => h x y x y
theorem Equation2871_implies_Equation2863 (G : Type*) [Magma G] (h : Equation2871 G) : Equation2863 G := λ x y => h x y x y
theorem Equation2881_implies_Equation2873 (G : Type*) [Magma G] (h : Equation2881 G) : Equation2873 G := λ x y => h x y x y
theorem Equation2885_implies_Equation2863 (G : Type*) [Magma G] (h : Equation2885 G) : Equation2863 G := λ x y => h x y x y
theorem Equation2889_implies_Equation2866 (G : Type*) [Magma G] (h : Equation2889 G) : Equation2866 G := λ x y => h x y x y
theorem Equation2893_implies_Equation2863 (G : Type*) [Magma G] (h : Equation2893 G) : Equation2863 G := λ x y => h x y x y
theorem Equation2894_implies_Equation2865 (G : Type*) [Magma G] (h : Equation2894 G) : Equation2865 G := λ x y => h x y x y
theorem Equation2895_implies_Equation2866 (G : Type*) [Magma G] (h : Equation2895 G) : Equation2866 G := λ x y => h x y x y
theorem Equation2896_implies_Equation2865 (G : Type*) [Magma G] (h : Equation2896 G) : Equation2865 G := λ x y => h x y x y
theorem Equation2897_implies_Equation2866 (G : Type*) [Magma G] (h : Equation2897 G) : Equation2866 G := λ x y => h x y x y
theorem Equation2908_implies_Equation2900 (G : Type*) [Magma G] (h : Equation2908 G) : Equation2900 G := λ x y => h x y x y
theorem Equation2918_implies_Equation2910 (G : Type*) [Magma G] (h : Equation2918 G) : Equation2910 G := λ x y => h x y x y
theorem Equation2922_implies_Equation2900 (G : Type*) [Magma G] (h : Equation2922 G) : Equation2900 G := λ x y => h x y x y
theorem Equation2926_implies_Equation2903 (G : Type*) [Magma G] (h : Equation2926 G) : Equation2903 G := λ x y => h x y x y
theorem Equation2930_implies_Equation2900 (G : Type*) [Magma G] (h : Equation2930 G) : Equation2900 G := λ x y => h x y x y
theorem Equation2931_implies_Equation2902 (G : Type*) [Magma G] (h : Equation2931 G) : Equation2902 G := λ x y => h x y x y
theorem Equation2932_implies_Equation2903 (G : Type*) [Magma G] (h : Equation2932 G) : Equation2903 G := λ x y => h x y x y
theorem Equation2933_implies_Equation2902 (G : Type*) [Magma G] (h : Equation2933 G) : Equation2902 G := λ x y => h x y x y
theorem Equation2934_implies_Equation2903 (G : Type*) [Magma G] (h : Equation2934 G) : Equation2903 G := λ x y => h x y x y
theorem Equation2945_implies_Equation2937 (G : Type*) [Magma G] (h : Equation2945 G) : Equation2937 G := λ x y => h x y x y
theorem Equation2955_implies_Equation2947 (G : Type*) [Magma G] (h : Equation2955 G) : Equation2947 G := λ x y => h x y x y
theorem Equation2959_implies_Equation2937 (G : Type*) [Magma G] (h : Equation2959 G) : Equation2937 G := λ x y => h x y x y
theorem Equation2963_implies_Equation2940 (G : Type*) [Magma G] (h : Equation2963 G) : Equation2940 G := λ x y => h x y x y
theorem Equation2967_implies_Equation2937 (G : Type*) [Magma G] (h : Equation2967 G) : Equation2937 G := λ x y => h x y x y
theorem Equation2968_implies_Equation2939 (G : Type*) [Magma G] (h : Equation2968 G) : Equation2939 G := λ x y => h x y x y
theorem Equation2969_implies_Equation2940 (G : Type*) [Magma G] (h : Equation2969 G) : Equation2940 G := λ x y => h x y x y
theorem Equation2970_implies_Equation2939 (G : Type*) [Magma G] (h : Equation2970 G) : Equation2939 G := λ x y => h x y x y
theorem Equation2971_implies_Equation2940 (G : Type*) [Magma G] (h : Equation2971 G) : Equation2940 G := λ x y => h x y x y
theorem Equation2976_implies_Equation2900 (G : Type*) [Magma G] (h : Equation2976 G) : Equation2900 G := λ x y => h x y x y
theorem Equation2980_implies_Equation2903 (G : Type*) [Magma G] (h : Equation2980 G) : Equation2903 G := λ x y => h x y x y
theorem Equation2984_implies_Equation2900 (G : Type*) [Magma G] (h : Equation2984 G) : Equation2900 G := λ x y => h x y x y
theorem Equation2985_implies_Equation2902 (G : Type*) [Magma G] (h : Equation2985 G) : Equation2902 G := λ x y => h x y x y
theorem Equation2986_implies_Equation2903 (G : Type*) [Magma G] (h : Equation2986 G) : Equation2903 G := λ x y => h x y x y
theorem Equation2987_implies_Equation2902 (G : Type*) [Magma G] (h : Equation2987 G) : Equation2902 G := λ x y => h x y x y
theorem Equation2988_implies_Equation2903 (G : Type*) [Magma G] (h : Equation2988 G) : Equation2903 G := λ x y => h x y x y
theorem Equation2993_implies_Equation2910 (G : Type*) [Magma G] (h : Equation2993 G) : Equation2910 G := λ x y => h x y x y
theorem Equation2997_implies_Equation2913 (G : Type*) [Magma G] (h : Equation2997 G) : Equation2913 G := λ x y => h x y x y
theorem Equation3001_implies_Equation2910 (G : Type*) [Magma G] (h : Equation3001 G) : Equation2910 G := λ x y => h x y x y
theorem Equation3002_implies_Equation2912 (G : Type*) [Magma G] (h : Equation3002 G) : Equation2912 G := λ x y => h x y x y
theorem Equation3003_implies_Equation2913 (G : Type*) [Magma G] (h : Equation3003 G) : Equation2913 G := λ x y => h x y x y
theorem Equation3004_implies_Equation2912 (G : Type*) [Magma G] (h : Equation3004 G) : Equation2912 G := λ x y => h x y x y
theorem Equation3005_implies_Equation2913 (G : Type*) [Magma G] (h : Equation3005 G) : Equation2913 G := λ x y => h x y x y
theorem Equation3010_implies_Equation2900 (G : Type*) [Magma G] (h : Equation3010 G) : Equation2900 G := λ x y => h x y x y
theorem Equation3014_implies_Equation2903 (G : Type*) [Magma G] (h : Equation3014 G) : Equation2903 G := λ x y => h x y x y
theorem Equation3018_implies_Equation2900 (G : Type*) [Magma G] (h : Equation3018 G) : Equation2900 G := λ x y => h x y x y
theorem Equation3019_implies_Equation2902 (G : Type*) [Magma G] (h : Equation3019 G) : Equation2902 G := λ x y => h x y x y
theorem Equation3020_implies_Equation2903 (G : Type*) [Magma G] (h : Equation3020 G) : Equation2903 G := λ x y => h x y x y
theorem Equation3021_implies_Equation2902 (G : Type*) [Magma G] (h : Equation3021 G) : Equation2902 G := λ x y => h x y x y
theorem Equation3022_implies_Equation2903 (G : Type*) [Magma G] (h : Equation3022 G) : Equation2903 G := λ x y => h x y x y
theorem Equation3024_implies_Equation2909 (G : Type*) [Magma G] (h : Equation3024 G) : Equation2909 G := λ x y => h x y x y
theorem Equation3025_implies_Equation2910 (G : Type*) [Magma G] (h : Equation3025 G) : Equation2910 G := λ x y => h x y x y
theorem Equation3026_implies_Equation2909 (G : Type*) [Magma G] (h : Equation3026 G) : Equation2909 G := λ x y => h x y x y
theorem Equation3027_implies_Equation2910 (G : Type*) [Magma G] (h : Equation3027 G) : Equation2910 G := λ x y => h x y x y
theorem Equation3029_implies_Equation2912 (G : Type*) [Magma G] (h : Equation3029 G) : Equation2912 G := λ x y => h x y x y
theorem Equation3030_implies_Equation2913 (G : Type*) [Magma G] (h : Equation3030 G) : Equation2913 G := λ x y => h x y x y
theorem Equation3031_implies_Equation2912 (G : Type*) [Magma G] (h : Equation3031 G) : Equation2912 G := λ x y => h x y x y
theorem Equation3032_implies_Equation2913 (G : Type*) [Magma G] (h : Equation3032 G) : Equation2913 G := λ x y => h x y x y
theorem Equation3034_implies_Equation2909 (G : Type*) [Magma G] (h : Equation3034 G) : Equation2909 G := λ x y => h x y x y
theorem Equation3035_implies_Equation2910 (G : Type*) [Magma G] (h : Equation3035 G) : Equation2910 G := λ x y => h x y x y
theorem Equation3036_implies_Equation2909 (G : Type*) [Magma G] (h : Equation3036 G) : Equation2909 G := λ x y => h x y x y
theorem Equation3037_implies_Equation2910 (G : Type*) [Magma G] (h : Equation3037 G) : Equation2910 G := λ x y => h x y x y
theorem Equation3039_implies_Equation2912 (G : Type*) [Magma G] (h : Equation3039 G) : Equation2912 G := λ x y => h x y x y
theorem Equation3040_implies_Equation2913 (G : Type*) [Magma G] (h : Equation3040 G) : Equation2913 G := λ x y => h x y x y
theorem Equation3041_implies_Equation2912 (G : Type*) [Magma G] (h : Equation3041 G) : Equation2912 G := λ x y => h x y x y
theorem Equation3042_implies_Equation2913 (G : Type*) [Magma G] (h : Equation3042 G) : Equation2913 G := λ x y => h x y x y
theorem Equation3064_implies_Equation3056 (G : Type*) [Magma G] (h : Equation3064 G) : Equation3056 G := λ x y => h x y x y
theorem Equation3074_implies_Equation3066 (G : Type*) [Magma G] (h : Equation3074 G) : Equation3066 G := λ x y => h x y x y
theorem Equation3084_implies_Equation3076 (G : Type*) [Magma G] (h : Equation3084 G) : Equation3076 G := λ x y => h x y x y
theorem Equation3088_implies_Equation3066 (G : Type*) [Magma G] (h : Equation3088 G) : Equation3066 G := λ x y => h x y x y
theorem Equation3092_implies_Equation3069 (G : Type*) [Magma G] (h : Equation3092 G) : Equation3069 G := λ x y => h x y x y
theorem Equation3096_implies_Equation3066 (G : Type*) [Magma G] (h : Equation3096 G) : Equation3066 G := λ x y => h x y x y
theorem Equation3097_implies_Equation3068 (G : Type*) [Magma G] (h : Equation3097 G) : Equation3068 G := λ x y => h x y x y
theorem Equation3098_implies_Equation3069 (G : Type*) [Magma G] (h : Equation3098 G) : Equation3069 G := λ x y => h x y x y
theorem Equation3099_implies_Equation3068 (G : Type*) [Magma G] (h : Equation3099 G) : Equation3068 G := λ x y => h x y x y
theorem Equation3100_implies_Equation3069 (G : Type*) [Magma G] (h : Equation3100 G) : Equation3069 G := λ x y => h x y x y
theorem Equation3111_implies_Equation3103 (G : Type*) [Magma G] (h : Equation3111 G) : Equation3103 G := λ x y => h x y x y
theorem Equation3121_implies_Equation3113 (G : Type*) [Magma G] (h : Equation3121 G) : Equation3113 G := λ x y => h x y x y
theorem Equation3125_implies_Equation3103 (G : Type*) [Magma G] (h : Equation3125 G) : Equation3103 G := λ x y => h x y x y
theorem Equation3129_implies_Equation3106 (G : Type*) [Magma G] (h : Equation3129 G) : Equation3106 G := λ x y => h x y x y
theorem Equation3133_implies_Equation3103 (G : Type*) [Magma G] (h : Equation3133 G) : Equation3103 G := λ x y => h x y x y
theorem Equation3134_implies_Equation3105 (G : Type*) [Magma G] (h : Equation3134 G) : Equation3105 G := λ x y => h x y x y
theorem Equation3135_implies_Equation3106 (G : Type*) [Magma G] (h : Equation3135 G) : Equation3106 G := λ x y => h x y x y
theorem Equation3136_implies_Equation3105 (G : Type*) [Magma G] (h : Equation3136 G) : Equation3105 G := λ x y => h x y x y
theorem Equation3137_implies_Equation3106 (G : Type*) [Magma G] (h : Equation3137 G) : Equation3106 G := λ x y => h x y x y
theorem Equation3148_implies_Equation3140 (G : Type*) [Magma G] (h : Equation3148 G) : Equation3140 G := λ x y => h x y x y
theorem Equation3158_implies_Equation3150 (G : Type*) [Magma G] (h : Equation3158 G) : Equation3150 G := λ x y => h x y x y
theorem Equation3162_implies_Equation3140 (G : Type*) [Magma G] (h : Equation3162 G) : Equation3140 G := λ x y => h x y x y
theorem Equation3166_implies_Equation3143 (G : Type*) [Magma G] (h : Equation3166 G) : Equation3143 G := λ x y => h x y x y
theorem Equation3170_implies_Equation3140 (G : Type*) [Magma G] (h : Equation3170 G) : Equation3140 G := λ x y => h x y x y
theorem Equation3171_implies_Equation3142 (G : Type*) [Magma G] (h : Equation3171 G) : Equation3142 G := λ x y => h x y x y
theorem Equation3172_implies_Equation3143 (G : Type*) [Magma G] (h : Equation3172 G) : Equation3143 G := λ x y => h x y x y
theorem Equation3173_implies_Equation3142 (G : Type*) [Magma G] (h : Equation3173 G) : Equation3142 G := λ x y => h x y x y
theorem Equation3174_implies_Equation3143 (G : Type*) [Magma G] (h : Equation3174 G) : Equation3143 G := λ x y => h x y x y
theorem Equation3179_implies_Equation3103 (G : Type*) [Magma G] (h : Equation3179 G) : Equation3103 G := λ x y => h x y x y
theorem Equation3183_implies_Equation3106 (G : Type*) [Magma G] (h : Equation3183 G) : Equation3106 G := λ x y => h x y x y
theorem Equation3187_implies_Equation3103 (G : Type*) [Magma G] (h : Equation3187 G) : Equation3103 G := λ x y => h x y x y
theorem Equation3188_implies_Equation3105 (G : Type*) [Magma G] (h : Equation3188 G) : Equation3105 G := λ x y => h x y x y
theorem Equation3189_implies_Equation3106 (G : Type*) [Magma G] (h : Equation3189 G) : Equation3106 G := λ x y => h x y x y
theorem Equation3190_implies_Equation3105 (G : Type*) [Magma G] (h : Equation3190 G) : Equation3105 G := λ x y => h x y x y
theorem Equation3191_implies_Equation3106 (G : Type*) [Magma G] (h : Equation3191 G) : Equation3106 G := λ x y => h x y x y
theorem Equation3196_implies_Equation3113 (G : Type*) [Magma G] (h : Equation3196 G) : Equation3113 G := λ x y => h x y x y
theorem Equation3200_implies_Equation3116 (G : Type*) [Magma G] (h : Equation3200 G) : Equation3116 G := λ x y => h x y x y
theorem Equation3204_implies_Equation3113 (G : Type*) [Magma G] (h : Equation3204 G) : Equation3113 G := λ x y => h x y x y
theorem Equation3205_implies_Equation3115 (G : Type*) [Magma G] (h : Equation3205 G) : Equation3115 G := λ x y => h x y x y
theorem Equation3206_implies_Equation3116 (G : Type*) [Magma G] (h : Equation3206 G) : Equation3116 G := λ x y => h x y x y
theorem Equation3207_implies_Equation3115 (G : Type*) [Magma G] (h : Equation3207 G) : Equation3115 G := λ x y => h x y x y
theorem Equation3208_implies_Equation3116 (G : Type*) [Magma G] (h : Equation3208 G) : Equation3116 G := λ x y => h x y x y
theorem Equation3213_implies_Equation3103 (G : Type*) [Magma G] (h : Equation3213 G) : Equation3103 G := λ x y => h x y x y
theorem Equation3217_implies_Equation3106 (G : Type*) [Magma G] (h : Equation3217 G) : Equation3106 G := λ x y => h x y x y
theorem Equation3221_implies_Equation3103 (G : Type*) [Magma G] (h : Equation3221 G) : Equation3103 G := λ x y => h x y x y
theorem Equation3222_implies_Equation3105 (G : Type*) [Magma G] (h : Equation3222 G) : Equation3105 G := λ x y => h x y x y
theorem Equation3223_implies_Equation3106 (G : Type*) [Magma G] (h : Equation3223 G) : Equation3106 G := λ x y => h x y x y
theorem Equation3224_implies_Equation3105 (G : Type*) [Magma G] (h : Equation3224 G) : Equation3105 G := λ x y => h x y x y
theorem Equation3225_implies_Equation3106 (G : Type*) [Magma G] (h : Equation3225 G) : Equation3106 G := λ x y => h x y x y
theorem Equation3227_implies_Equation3112 (G : Type*) [Magma G] (h : Equation3227 G) : Equation3112 G := λ x y => h x y x y
theorem Equation3228_implies_Equation3113 (G : Type*) [Magma G] (h : Equation3228 G) : Equation3113 G := λ x y => h x y x y
theorem Equation3229_implies_Equation3112 (G : Type*) [Magma G] (h : Equation3229 G) : Equation3112 G := λ x y => h x y x y
theorem Equation3230_implies_Equation3113 (G : Type*) [Magma G] (h : Equation3230 G) : Equation3113 G := λ x y => h x y x y
theorem Equation3232_implies_Equation3115 (G : Type*) [Magma G] (h : Equation3232 G) : Equation3115 G := λ x y => h x y x y
theorem Equation3233_implies_Equation3116 (G : Type*) [Magma G] (h : Equation3233 G) : Equation3116 G := λ x y => h x y x y
theorem Equation3234_implies_Equation3115 (G : Type*) [Magma G] (h : Equation3234 G) : Equation3115 G := λ x y => h x y x y
theorem Equation3235_implies_Equation3116 (G : Type*) [Magma G] (h : Equation3235 G) : Equation3116 G := λ x y => h x y x y
theorem Equation3237_implies_Equation3112 (G : Type*) [Magma G] (h : Equation3237 G) : Equation3112 G := λ x y => h x y x y
theorem Equation3238_implies_Equation3113 (G : Type*) [Magma G] (h : Equation3238 G) : Equation3113 G := λ x y => h x y x y
theorem Equation3239_implies_Equation3112 (G : Type*) [Magma G] (h : Equation3239 G) : Equation3112 G := λ x y => h x y x y
theorem Equation3240_implies_Equation3113 (G : Type*) [Magma G] (h : Equation3240 G) : Equation3113 G := λ x y => h x y x y
theorem Equation3242_implies_Equation3115 (G : Type*) [Magma G] (h : Equation3242 G) : Equation3115 G := λ x y => h x y x y
theorem Equation3243_implies_Equation3116 (G : Type*) [Magma G] (h : Equation3243 G) : Equation3116 G := λ x y => h x y x y
theorem Equation3244_implies_Equation3115 (G : Type*) [Magma G] (h : Equation3244 G) : Equation3115 G := λ x y => h x y x y
theorem Equation3245_implies_Equation3116 (G : Type*) [Magma G] (h : Equation3245 G) : Equation3116 G := λ x y => h x y x y
theorem Equation3267_implies_Equation3259 (G : Type*) [Magma G] (h : Equation3267 G) : Equation3259 G := λ x y => h x y x y
theorem Equation3277_implies_Equation3269 (G : Type*) [Magma G] (h : Equation3277 G) : Equation3269 G := λ x y => h x y x y
theorem Equation3287_implies_Equation3279 (G : Type*) [Magma G] (h : Equation3287 G) : Equation3279 G := λ x y => h x y x y
theorem Equation3291_implies_Equation3269 (G : Type*) [Magma G] (h : Equation3291 G) : Equation3269 G := λ x y => h x y x y
theorem Equation3295_implies_Equation3272 (G : Type*) [Magma G] (h : Equation3295 G) : Equation3272 G := λ x y => h x y x y
theorem Equation3299_implies_Equation3269 (G : Type*) [Magma G] (h : Equation3299 G) : Equation3269 G := λ x y => h x y x y
theorem Equation3300_implies_Equation3271 (G : Type*) [Magma G] (h : Equation3300 G) : Equation3271 G := λ x y => h x y x y
theorem Equation3301_implies_Equation3272 (G : Type*) [Magma G] (h : Equation3301 G) : Equation3272 G := λ x y => h x y x y
theorem Equation3302_implies_Equation3271 (G : Type*) [Magma G] (h : Equation3302 G) : Equation3271 G := λ x y => h x y x y
theorem Equation3303_implies_Equation3272 (G : Type*) [Magma G] (h : Equation3303 G) : Equation3272 G := λ x y => h x y x y
theorem Equation3314_implies_Equation3306 (G : Type*) [Magma G] (h : Equation3314 G) : Equation3306 G := λ x y => h x y x y
theorem Equation3324_implies_Equation3316 (G : Type*) [Magma G] (h : Equation3324 G) : Equation3316 G := λ x y => h x y x y
theorem Equation3328_implies_Equation3306 (G : Type*) [Magma G] (h : Equation3328 G) : Equation3306 G := λ x y => h x y x y
theorem Equation3332_implies_Equation3309 (G : Type*) [Magma G] (h : Equation3332 G) : Equation3309 G := λ x y => h x y x y
theorem Equation3336_implies_Equation3306 (G : Type*) [Magma G] (h : Equation3336 G) : Equation3306 G := λ x y => h x y x y
theorem Equation3337_implies_Equation3308 (G : Type*) [Magma G] (h : Equation3337 G) : Equation3308 G := λ x y => h x y x y
theorem Equation3338_implies_Equation3309 (G : Type*) [Magma G] (h : Equation3338 G) : Equation3309 G := λ x y => h x y x y
theorem Equation3339_implies_Equation3308 (G : Type*) [Magma G] (h : Equation3339 G) : Equation3308 G := λ x y => h x y x y
theorem Equation3340_implies_Equation3309 (G : Type*) [Magma G] (h : Equation3340 G) : Equation3309 G := λ x y => h x y x y
theorem Equation3351_implies_Equation3343 (G : Type*) [Magma G] (h : Equation3351 G) : Equation3343 G := λ x y => h x y x y
theorem Equation3361_implies_Equation3353 (G : Type*) [Magma G] (h : Equation3361 G) : Equation3353 G := λ x y => h x y x y
theorem Equation3365_implies_Equation3343 (G : Type*) [Magma G] (h : Equation3365 G) : Equation3343 G := λ x y => h x y x y
theorem Equation3369_implies_Equation3346 (G : Type*) [Magma G] (h : Equation3369 G) : Equation3346 G := λ x y => h x y x y
theorem Equation3373_implies_Equation3343 (G : Type*) [Magma G] (h : Equation3373 G) : Equation3343 G := λ x y => h x y x y
theorem Equation3374_implies_Equation3345 (G : Type*) [Magma G] (h : Equation3374 G) : Equation3345 G := λ x y => h x y x y
theorem Equation3375_implies_Equation3346 (G : Type*) [Magma G] (h : Equation3375 G) : Equation3346 G := λ x y => h x y x y
theorem Equation3376_implies_Equation3345 (G : Type*) [Magma G] (h : Equation3376 G) : Equation3345 G := λ x y => h x y x y
theorem Equation3377_implies_Equation3346 (G : Type*) [Magma G] (h : Equation3377 G) : Equation3346 G := λ x y => h x y x y
theorem Equation3382_implies_Equation3306 (G : Type*) [Magma G] (h : Equation3382 G) : Equation3306 G := λ x y => h x y x y
theorem Equation3386_implies_Equation3309 (G : Type*) [Magma G] (h : Equation3386 G) : Equation3309 G := λ x y => h x y x y
theorem Equation3390_implies_Equation3306 (G : Type*) [Magma G] (h : Equation3390 G) : Equation3306 G := λ x y => h x y x y
theorem Equation3391_implies_Equation3308 (G : Type*) [Magma G] (h : Equation3391 G) : Equation3308 G := λ x y => h x y x y
theorem Equation3392_implies_Equation3309 (G : Type*) [Magma G] (h : Equation3392 G) : Equation3309 G := λ x y => h x y x y
theorem Equation3393_implies_Equation3308 (G : Type*) [Magma G] (h : Equation3393 G) : Equation3308 G := λ x y => h x y x y
theorem Equation3394_implies_Equation3309 (G : Type*) [Magma G] (h : Equation3394 G) : Equation3309 G := λ x y => h x y x y
theorem Equation3399_implies_Equation3316 (G : Type*) [Magma G] (h : Equation3399 G) : Equation3316 G := λ x y => h x y x y
theorem Equation3403_implies_Equation3319 (G : Type*) [Magma G] (h : Equation3403 G) : Equation3319 G := λ x y => h x y x y
theorem Equation3407_implies_Equation3316 (G : Type*) [Magma G] (h : Equation3407 G) : Equation3316 G := λ x y => h x y x y
theorem Equation3408_implies_Equation3318 (G : Type*) [Magma G] (h : Equation3408 G) : Equation3318 G := λ x y => h x y x y
theorem Equation3409_implies_Equation3319 (G : Type*) [Magma G] (h : Equation3409 G) : Equation3319 G := λ x y => h x y x y
theorem Equation3410_implies_Equation3318 (G : Type*) [Magma G] (h : Equation3410 G) : Equation3318 G := λ x y => h x y x y
theorem Equation3411_implies_Equation3319 (G : Type*) [Magma G] (h : Equation3411 G) : Equation3319 G := λ x y => h x y x y
theorem Equation3416_implies_Equation3306 (G : Type*) [Magma G] (h : Equation3416 G) : Equation3306 G := λ x y => h x y x y
theorem Equation3420_implies_Equation3309 (G : Type*) [Magma G] (h : Equation3420 G) : Equation3309 G := λ x y => h x y x y
theorem Equation3424_implies_Equation3306 (G : Type*) [Magma G] (h : Equation3424 G) : Equation3306 G := λ x y => h x y x y
theorem Equation3425_implies_Equation3308 (G : Type*) [Magma G] (h : Equation3425 G) : Equation3308 G := λ x y => h x y x y
theorem Equation3426_implies_Equation3309 (G : Type*) [Magma G] (h : Equation3426 G) : Equation3309 G := λ x y => h x y x y
theorem Equation3427_implies_Equation3308 (G : Type*) [Magma G] (h : Equation3427 G) : Equation3308 G := λ x y => h x y x y
theorem Equation3428_implies_Equation3309 (G : Type*) [Magma G] (h : Equation3428 G) : Equation3309 G := λ x y => h x y x y
theorem Equation3430_implies_Equation3315 (G : Type*) [Magma G] (h : Equation3430 G) : Equation3315 G := λ x y => h x y x y
theorem Equation3431_implies_Equation3316 (G : Type*) [Magma G] (h : Equation3431 G) : Equation3316 G := λ x y => h x y x y
theorem Equation3432_implies_Equation3315 (G : Type*) [Magma G] (h : Equation3432 G) : Equation3315 G := λ x y => h x y x y
theorem Equation3433_implies_Equation3316 (G : Type*) [Magma G] (h : Equation3433 G) : Equation3316 G := λ x y => h x y x y
theorem Equation3435_implies_Equation3318 (G : Type*) [Magma G] (h : Equation3435 G) : Equation3318 G := λ x y => h x y x y
theorem Equation3436_implies_Equation3319 (G : Type*) [Magma G] (h : Equation3436 G) : Equation3319 G := λ x y => h x y x y
theorem Equation3437_implies_Equation3318 (G : Type*) [Magma G] (h : Equation3437 G) : Equation3318 G := λ x y => h x y x y
theorem Equation3438_implies_Equation3319 (G : Type*) [Magma G] (h : Equation3438 G) : Equation3319 G := λ x y => h x y x y
theorem Equation3440_implies_Equation3315 (G : Type*) [Magma G] (h : Equation3440 G) : Equation3315 G := λ x y => h x y x y
theorem Equation3441_implies_Equation3316 (G : Type*) [Magma G] (h : Equation3441 G) : Equation3316 G := λ x y => h x y x y
theorem Equation3442_implies_Equation3315 (G : Type*) [Magma G] (h : Equation3442 G) : Equation3315 G := λ x y => h x y x y
theorem Equation3443_implies_Equation3316 (G : Type*) [Magma G] (h : Equation3443 G) : Equation3316 G := λ x y => h x y x y
theorem Equation3445_implies_Equation3318 (G : Type*) [Magma G] (h : Equation3445 G) : Equation3318 G := λ x y => h x y x y
theorem Equation3446_implies_Equation3319 (G : Type*) [Magma G] (h : Equation3446 G) : Equation3319 G := λ x y => h x y x y
theorem Equation3447_implies_Equation3318 (G : Type*) [Magma G] (h : Equation3447 G) : Equation3318 G := λ x y => h x y x y
theorem Equation3448_implies_Equation3319 (G : Type*) [Magma G] (h : Equation3448 G) : Equation3319 G := λ x y => h x y x y
theorem Equation3470_implies_Equation3462 (G : Type*) [Magma G] (h : Equation3470 G) : Equation3462 G := λ x y => h x y x y
theorem Equation3480_implies_Equation3472 (G : Type*) [Magma G] (h : Equation3480 G) : Equation3472 G := λ x y => h x y x y
theorem Equation3490_implies_Equation3482 (G : Type*) [Magma G] (h : Equation3490 G) : Equation3482 G := λ x y => h x y x y
theorem Equation3494_implies_Equation3472 (G : Type*) [Magma G] (h : Equation3494 G) : Equation3472 G := λ x y => h x y x y
theorem Equation3498_implies_Equation3475 (G : Type*) [Magma G] (h : Equation3498 G) : Equation3475 G := λ x y => h x y x y
theorem Equation3502_implies_Equation3472 (G : Type*) [Magma G] (h : Equation3502 G) : Equation3472 G := λ x y => h x y x y
theorem Equation3503_implies_Equation3474 (G : Type*) [Magma G] (h : Equation3503 G) : Equation3474 G := λ x y => h x y x y
theorem Equation3504_implies_Equation3475 (G : Type*) [Magma G] (h : Equation3504 G) : Equation3475 G := λ x y => h x y x y
theorem Equation3505_implies_Equation3474 (G : Type*) [Magma G] (h : Equation3505 G) : Equation3474 G := λ x y => h x y x y
theorem Equation3506_implies_Equation3475 (G : Type*) [Magma G] (h : Equation3506 G) : Equation3475 G := λ x y => h x y x y
theorem Equation3517_implies_Equation3509 (G : Type*) [Magma G] (h : Equation3517 G) : Equation3509 G := λ x y => h x y x y
theorem Equation3527_implies_Equation3519 (G : Type*) [Magma G] (h : Equation3527 G) : Equation3519 G := λ x y => h x y x y
theorem Equation3531_implies_Equation3509 (G : Type*) [Magma G] (h : Equation3531 G) : Equation3509 G := λ x y => h x y x y
theorem Equation3535_implies_Equation3512 (G : Type*) [Magma G] (h : Equation3535 G) : Equation3512 G := λ x y => h x y x y
theorem Equation3539_implies_Equation3509 (G : Type*) [Magma G] (h : Equation3539 G) : Equation3509 G := λ x y => h x y x y
theorem Equation3540_implies_Equation3511 (G : Type*) [Magma G] (h : Equation3540 G) : Equation3511 G := λ x y => h x y x y
theorem Equation3541_implies_Equation3512 (G : Type*) [Magma G] (h : Equation3541 G) : Equation3512 G := λ x y => h x y x y
theorem Equation3542_implies_Equation3511 (G : Type*) [Magma G] (h : Equation3542 G) : Equation3511 G := λ x y => h x y x y
theorem Equation3543_implies_Equation3512 (G : Type*) [Magma G] (h : Equation3543 G) : Equation3512 G := λ x y => h x y x y
theorem Equation3554_implies_Equation3546 (G : Type*) [Magma G] (h : Equation3554 G) : Equation3546 G := λ x y => h x y x y
theorem Equation3564_implies_Equation3556 (G : Type*) [Magma G] (h : Equation3564 G) : Equation3556 G := λ x y => h x y x y
theorem Equation3568_implies_Equation3546 (G : Type*) [Magma G] (h : Equation3568 G) : Equation3546 G := λ x y => h x y x y
theorem Equation3572_implies_Equation3549 (G : Type*) [Magma G] (h : Equation3572 G) : Equation3549 G := λ x y => h x y x y
theorem Equation3576_implies_Equation3546 (G : Type*) [Magma G] (h : Equation3576 G) : Equation3546 G := λ x y => h x y x y
theorem Equation3577_implies_Equation3548 (G : Type*) [Magma G] (h : Equation3577 G) : Equation3548 G := λ x y => h x y x y
theorem Equation3578_implies_Equation3549 (G : Type*) [Magma G] (h : Equation3578 G) : Equation3549 G := λ x y => h x y x y
theorem Equation3579_implies_Equation3548 (G : Type*) [Magma G] (h : Equation3579 G) : Equation3548 G := λ x y => h x y x y
theorem Equation3580_implies_Equation3549 (G : Type*) [Magma G] (h : Equation3580 G) : Equation3549 G := λ x y => h x y x y
theorem Equation3585_implies_Equation3509 (G : Type*) [Magma G] (h : Equation3585 G) : Equation3509 G := λ x y => h x y x y
theorem Equation3589_implies_Equation3512 (G : Type*) [Magma G] (h : Equation3589 G) : Equation3512 G := λ x y => h x y x y
theorem Equation3593_implies_Equation3509 (G : Type*) [Magma G] (h : Equation3593 G) : Equation3509 G := λ x y => h x y x y
theorem Equation3594_implies_Equation3511 (G : Type*) [Magma G] (h : Equation3594 G) : Equation3511 G := λ x y => h x y x y
theorem Equation3595_implies_Equation3512 (G : Type*) [Magma G] (h : Equation3595 G) : Equation3512 G := λ x y => h x y x y
theorem Equation3596_implies_Equation3511 (G : Type*) [Magma G] (h : Equation3596 G) : Equation3511 G := λ x y => h x y x y
theorem Equation3597_implies_Equation3512 (G : Type*) [Magma G] (h : Equation3597 G) : Equation3512 G := λ x y => h x y x y
theorem Equation3602_implies_Equation3519 (G : Type*) [Magma G] (h : Equation3602 G) : Equation3519 G := λ x y => h x y x y
theorem Equation3606_implies_Equation3522 (G : Type*) [Magma G] (h : Equation3606 G) : Equation3522 G := λ x y => h x y x y
theorem Equation3610_implies_Equation3519 (G : Type*) [Magma G] (h : Equation3610 G) : Equation3519 G := λ x y => h x y x y
theorem Equation3611_implies_Equation3521 (G : Type*) [Magma G] (h : Equation3611 G) : Equation3521 G := λ x y => h x y x y
theorem Equation3612_implies_Equation3522 (G : Type*) [Magma G] (h : Equation3612 G) : Equation3522 G := λ x y => h x y x y
theorem Equation3613_implies_Equation3521 (G : Type*) [Magma G] (h : Equation3613 G) : Equation3521 G := λ x y => h x y x y
theorem Equation3614_implies_Equation3522 (G : Type*) [Magma G] (h : Equation3614 G) : Equation3522 G := λ x y => h x y x y
theorem Equation3619_implies_Equation3509 (G : Type*) [Magma G] (h : Equation3619 G) : Equation3509 G := λ x y => h x y x y
theorem Equation3623_implies_Equation3512 (G : Type*) [Magma G] (h : Equation3623 G) : Equation3512 G := λ x y => h x y x y
theorem Equation3627_implies_Equation3509 (G : Type*) [Magma G] (h : Equation3627 G) : Equation3509 G := λ x y => h x y x y
theorem Equation3628_implies_Equation3511 (G : Type*) [Magma G] (h : Equation3628 G) : Equation3511 G := λ x y => h x y x y
theorem Equation3629_implies_Equation3512 (G : Type*) [Magma G] (h : Equation3629 G) : Equation3512 G := λ x y => h x y x y
theorem Equation3630_implies_Equation3511 (G : Type*) [Magma G] (h : Equation3630 G) : Equation3511 G := λ x y => h x y x y
theorem Equation3631_implies_Equation3512 (G : Type*) [Magma G] (h : Equation3631 G) : Equation3512 G := λ x y => h x y x y
theorem Equation3633_implies_Equation3518 (G : Type*) [Magma G] (h : Equation3633 G) : Equation3518 G := λ x y => h x y x y
theorem Equation3634_implies_Equation3519 (G : Type*) [Magma G] (h : Equation3634 G) : Equation3519 G := λ x y => h x y x y
theorem Equation3635_implies_Equation3518 (G : Type*) [Magma G] (h : Equation3635 G) : Equation3518 G := λ x y => h x y x y
theorem Equation3636_implies_Equation3519 (G : Type*) [Magma G] (h : Equation3636 G) : Equation3519 G := λ x y => h x y x y
theorem Equation3638_implies_Equation3521 (G : Type*) [Magma G] (h : Equation3638 G) : Equation3521 G := λ x y => h x y x y
theorem Equation3639_implies_Equation3522 (G : Type*) [Magma G] (h : Equation3639 G) : Equation3522 G := λ x y => h x y x y
theorem Equation3640_implies_Equation3521 (G : Type*) [Magma G] (h : Equation3640 G) : Equation3521 G := λ x y => h x y x y
theorem Equation3641_implies_Equation3522 (G : Type*) [Magma G] (h : Equation3641 G) : Equation3522 G := λ x y => h x y x y
theorem Equation3643_implies_Equation3518 (G : Type*) [Magma G] (h : Equation3643 G) : Equation3518 G := λ x y => h x y x y
theorem Equation3644_implies_Equation3519 (G : Type*) [Magma G] (h : Equation3644 G) : Equation3519 G := λ x y => h x y x y
theorem Equation3645_implies_Equation3518 (G : Type*) [Magma G] (h : Equation3645 G) : Equation3518 G := λ x y => h x y x y
theorem Equation3646_implies_Equation3519 (G : Type*) [Magma G] (h : Equation3646 G) : Equation3519 G := λ x y => h x y x y
theorem Equation3648_implies_Equation3521 (G : Type*) [Magma G] (h : Equation3648 G) : Equation3521 G := λ x y => h x y x y
theorem Equation3649_implies_Equation3522 (G : Type*) [Magma G] (h : Equation3649 G) : Equation3522 G := λ x y => h x y x y
theorem Equation3650_implies_Equation3521 (G : Type*) [Magma G] (h : Equation3650 G) : Equation3521 G := λ x y => h x y x y
theorem Equation3651_implies_Equation3522 (G : Type*) [Magma G] (h : Equation3651 G) : Equation3522 G := λ x y => h x y x y
theorem Equation3673_implies_Equation3665 (G : Type*) [Magma G] (h : Equation3673 G) : Equation3665 G := λ x y => h x y x y
theorem Equation3683_implies_Equation3675 (G : Type*) [Magma G] (h : Equation3683 G) : Equation3675 G := λ x y => h x y x y
theorem Equation3693_implies_Equation3685 (G : Type*) [Magma G] (h : Equation3693 G) : Equation3685 G := λ x y => h x y x y
theorem Equation3697_implies_Equation3675 (G : Type*) [Magma G] (h : Equation3697 G) : Equation3675 G := λ x y => h x y x y
theorem Equation3701_implies_Equation3678 (G : Type*) [Magma G] (h : Equation3701 G) : Equation3678 G := λ x y => h x y x y
theorem Equation3705_implies_Equation3675 (G : Type*) [Magma G] (h : Equation3705 G) : Equation3675 G := λ x y => h x y x y
theorem Equation3706_implies_Equation3677 (G : Type*) [Magma G] (h : Equation3706 G) : Equation3677 G := λ x y => h x y x y
theorem Equation3707_implies_Equation3678 (G : Type*) [Magma G] (h : Equation3707 G) : Equation3678 G := λ x y => h x y x y
theorem Equation3708_implies_Equation3677 (G : Type*) [Magma G] (h : Equation3708 G) : Equation3677 G := λ x y => h x y x y
theorem Equation3709_implies_Equation3678 (G : Type*) [Magma G] (h : Equation3709 G) : Equation3678 G := λ x y => h x y x y
theorem Equation3720_implies_Equation3712 (G : Type*) [Magma G] (h : Equation3720 G) : Equation3712 G := λ x y => h x y x y
theorem Equation3730_implies_Equation3722 (G : Type*) [Magma G] (h : Equation3730 G) : Equation3722 G := λ x y => h x y x y
theorem Equation3734_implies_Equation3712 (G : Type*) [Magma G] (h : Equation3734 G) : Equation3712 G := λ x y => h x y x y
theorem Equation3738_implies_Equation3715 (G : Type*) [Magma G] (h : Equation3738 G) : Equation3715 G := λ x y => h x y x y
theorem Equation3742_implies_Equation3712 (G : Type*) [Magma G] (h : Equation3742 G) : Equation3712 G := λ x y => h x y x y
theorem Equation3743_implies_Equation3714 (G : Type*) [Magma G] (h : Equation3743 G) : Equation3714 G := λ x y => h x y x y
theorem Equation3744_implies_Equation3715 (G : Type*) [Magma G] (h : Equation3744 G) : Equation3715 G := λ x y => h x y x y
theorem Equation3745_implies_Equation3714 (G : Type*) [Magma G] (h : Equation3745 G) : Equation3714 G := λ x y => h x y x y
theorem Equation3746_implies_Equation3715 (G : Type*) [Magma G] (h : Equation3746 G) : Equation3715 G := λ x y => h x y x y
theorem Equation3757_implies_Equation3749 (G : Type*) [Magma G] (h : Equation3757 G) : Equation3749 G := λ x y => h x y x y
theorem Equation3767_implies_Equation3759 (G : Type*) [Magma G] (h : Equation3767 G) : Equation3759 G := λ x y => h x y x y
theorem Equation3771_implies_Equation3749 (G : Type*) [Magma G] (h : Equation3771 G) : Equation3749 G := λ x y => h x y x y
theorem Equation3775_implies_Equation3752 (G : Type*) [Magma G] (h : Equation3775 G) : Equation3752 G := λ x y => h x y x y
theorem Equation3779_implies_Equation3749 (G : Type*) [Magma G] (h : Equation3779 G) : Equation3749 G := λ x y => h x y x y
theorem Equation3780_implies_Equation3751 (G : Type*) [Magma G] (h : Equation3780 G) : Equation3751 G := λ x y => h x y x y
theorem Equation3781_implies_Equation3752 (G : Type*) [Magma G] (h : Equation3781 G) : Equation3752 G := λ x y => h x y x y
theorem Equation3782_implies_Equation3751 (G : Type*) [Magma G] (h : Equation3782 G) : Equation3751 G := λ x y => h x y x y
theorem Equation3783_implies_Equation3752 (G : Type*) [Magma G] (h : Equation3783 G) : Equation3752 G := λ x y => h x y x y
theorem Equation3788_implies_Equation3712 (G : Type*) [Magma G] (h : Equation3788 G) : Equation3712 G := λ x y => h x y x y
theorem Equation3792_implies_Equation3715 (G : Type*) [Magma G] (h : Equation3792 G) : Equation3715 G := λ x y => h x y x y
theorem Equation3796_implies_Equation3712 (G : Type*) [Magma G] (h : Equation3796 G) : Equation3712 G := λ x y => h x y x y
theorem Equation3797_implies_Equation3714 (G : Type*) [Magma G] (h : Equation3797 G) : Equation3714 G := λ x y => h x y x y
theorem Equation3798_implies_Equation3715 (G : Type*) [Magma G] (h : Equation3798 G) : Equation3715 G := λ x y => h x y x y
theorem Equation3799_implies_Equation3714 (G : Type*) [Magma G] (h : Equation3799 G) : Equation3714 G := λ x y => h x y x y
theorem Equation3800_implies_Equation3715 (G : Type*) [Magma G] (h : Equation3800 G) : Equation3715 G := λ x y => h x y x y
theorem Equation3805_implies_Equation3722 (G : Type*) [Magma G] (h : Equation3805 G) : Equation3722 G := λ x y => h x y x y
theorem Equation3809_implies_Equation3725 (G : Type*) [Magma G] (h : Equation3809 G) : Equation3725 G := λ x y => h x y x y
theorem Equation3813_implies_Equation3722 (G : Type*) [Magma G] (h : Equation3813 G) : Equation3722 G := λ x y => h x y x y
theorem Equation3814_implies_Equation3724 (G : Type*) [Magma G] (h : Equation3814 G) : Equation3724 G := λ x y => h x y x y
theorem Equation3815_implies_Equation3725 (G : Type*) [Magma G] (h : Equation3815 G) : Equation3725 G := λ x y => h x y x y
theorem Equation3816_implies_Equation3724 (G : Type*) [Magma G] (h : Equation3816 G) : Equation3724 G := λ x y => h x y x y
theorem Equation3817_implies_Equation3725 (G : Type*) [Magma G] (h : Equation3817 G) : Equation3725 G := λ x y => h x y x y
theorem Equation3822_implies_Equation3712 (G : Type*) [Magma G] (h : Equation3822 G) : Equation3712 G := λ x y => h x y x y
theorem Equation3826_implies_Equation3715 (G : Type*) [Magma G] (h : Equation3826 G) : Equation3715 G := λ x y => h x y x y
theorem Equation3830_implies_Equation3712 (G : Type*) [Magma G] (h : Equation3830 G) : Equation3712 G := λ x y => h x y x y
theorem Equation3831_implies_Equation3714 (G : Type*) [Magma G] (h : Equation3831 G) : Equation3714 G := λ x y => h x y x y
theorem Equation3832_implies_Equation3715 (G : Type*) [Magma G] (h : Equation3832 G) : Equation3715 G := λ x y => h x y x y
theorem Equation3833_implies_Equation3714 (G : Type*) [Magma G] (h : Equation3833 G) : Equation3714 G := λ x y => h x y x y
theorem Equation3834_implies_Equation3715 (G : Type*) [Magma G] (h : Equation3834 G) : Equation3715 G := λ x y => h x y x y
theorem Equation3836_implies_Equation3721 (G : Type*) [Magma G] (h : Equation3836 G) : Equation3721 G := λ x y => h x y x y
theorem Equation3837_implies_Equation3722 (G : Type*) [Magma G] (h : Equation3837 G) : Equation3722 G := λ x y => h x y x y
theorem Equation3838_implies_Equation3721 (G : Type*) [Magma G] (h : Equation3838 G) : Equation3721 G := λ x y => h x y x y
theorem Equation3839_implies_Equation3722 (G : Type*) [Magma G] (h : Equation3839 G) : Equation3722 G := λ x y => h x y x y
theorem Equation3841_implies_Equation3724 (G : Type*) [Magma G] (h : Equation3841 G) : Equation3724 G := λ x y => h x y x y
theorem Equation3842_implies_Equation3725 (G : Type*) [Magma G] (h : Equation3842 G) : Equation3725 G := λ x y => h x y x y
theorem Equation3843_implies_Equation3724 (G : Type*) [Magma G] (h : Equation3843 G) : Equation3724 G := λ x y => h x y x y
theorem Equation3844_implies_Equation3725 (G : Type*) [Magma G] (h : Equation3844 G) : Equation3725 G := λ x y => h x y x y
theorem Equation3846_implies_Equation3721 (G : Type*) [Magma G] (h : Equation3846 G) : Equation3721 G := λ x y => h x y x y
theorem Equation3847_implies_Equation3722 (G : Type*) [Magma G] (h : Equation3847 G) : Equation3722 G := λ x y => h x y x y
theorem Equation3848_implies_Equation3721 (G : Type*) [Magma G] (h : Equation3848 G) : Equation3721 G := λ x y => h x y x y
theorem Equation3849_implies_Equation3722 (G : Type*) [Magma G] (h : Equation3849 G) : Equation3722 G := λ x y => h x y x y
theorem Equation3851_implies_Equation3724 (G : Type*) [Magma G] (h : Equation3851 G) : Equation3724 G := λ x y => h x y x y
theorem Equation3852_implies_Equation3725 (G : Type*) [Magma G] (h : Equation3852 G) : Equation3725 G := λ x y => h x y x y
theorem Equation3853_implies_Equation3724 (G : Type*) [Magma G] (h : Equation3853 G) : Equation3724 G := λ x y => h x y x y
theorem Equation3854_implies_Equation3725 (G : Type*) [Magma G] (h : Equation3854 G) : Equation3725 G := λ x y => h x y x y
theorem Equation3876_implies_Equation3868 (G : Type*) [Magma G] (h : Equation3876 G) : Equation3868 G := λ x y => h x y x y
theorem Equation3886_implies_Equation3878 (G : Type*) [Magma G] (h : Equation3886 G) : Equation3878 G := λ x y => h x y x y
theorem Equation3896_implies_Equation3888 (G : Type*) [Magma G] (h : Equation3896 G) : Equation3888 G := λ x y => h x y x y
theorem Equation3900_implies_Equation3878 (G : Type*) [Magma G] (h : Equation3900 G) : Equation3878 G := λ x y => h x y x y
theorem Equation3904_implies_Equation3881 (G : Type*) [Magma G] (h : Equation3904 G) : Equation3881 G := λ x y => h x y x y
theorem Equation3908_implies_Equation3878 (G : Type*) [Magma G] (h : Equation3908 G) : Equation3878 G := λ x y => h x y x y
theorem Equation3909_implies_Equation3880 (G : Type*) [Magma G] (h : Equation3909 G) : Equation3880 G := λ x y => h x y x y
theorem Equation3910_implies_Equation3881 (G : Type*) [Magma G] (h : Equation3910 G) : Equation3881 G := λ x y => h x y x y
theorem Equation3911_implies_Equation3880 (G : Type*) [Magma G] (h : Equation3911 G) : Equation3880 G := λ x y => h x y x y
theorem Equation3912_implies_Equation3881 (G : Type*) [Magma G] (h : Equation3912 G) : Equation3881 G := λ x y => h x y x y
theorem Equation3923_implies_Equation3915 (G : Type*) [Magma G] (h : Equation3923 G) : Equation3915 G := λ x y => h x y x y
theorem Equation3933_implies_Equation3925 (G : Type*) [Magma G] (h : Equation3933 G) : Equation3925 G := λ x y => h x y x y
theorem Equation3937_implies_Equation3915 (G : Type*) [Magma G] (h : Equation3937 G) : Equation3915 G := λ x y => h x y x y
theorem Equation3941_implies_Equation3918 (G : Type*) [Magma G] (h : Equation3941 G) : Equation3918 G := λ x y => h x y x y
theorem Equation3945_implies_Equation3915 (G : Type*) [Magma G] (h : Equation3945 G) : Equation3915 G := λ x y => h x y x y
theorem Equation3946_implies_Equation3917 (G : Type*) [Magma G] (h : Equation3946 G) : Equation3917 G := λ x y => h x y x y
theorem Equation3947_implies_Equation3918 (G : Type*) [Magma G] (h : Equation3947 G) : Equation3918 G := λ x y => h x y x y
theorem Equation3948_implies_Equation3917 (G : Type*) [Magma G] (h : Equation3948 G) : Equation3917 G := λ x y => h x y x y
theorem Equation3949_implies_Equation3918 (G : Type*) [Magma G] (h : Equation3949 G) : Equation3918 G := λ x y => h x y x y
theorem Equation3960_implies_Equation3952 (G : Type*) [Magma G] (h : Equation3960 G) : Equation3952 G := λ x y => h x y x y
theorem Equation3970_implies_Equation3962 (G : Type*) [Magma G] (h : Equation3970 G) : Equation3962 G := λ x y => h x y x y
theorem Equation3974_implies_Equation3952 (G : Type*) [Magma G] (h : Equation3974 G) : Equation3952 G := λ x y => h x y x y
theorem Equation3978_implies_Equation3955 (G : Type*) [Magma G] (h : Equation3978 G) : Equation3955 G := λ x y => h x y x y
theorem Equation3982_implies_Equation3952 (G : Type*) [Magma G] (h : Equation3982 G) : Equation3952 G := λ x y => h x y x y
theorem Equation3983_implies_Equation3954 (G : Type*) [Magma G] (h : Equation3983 G) : Equation3954 G := λ x y => h x y x y
theorem Equation3984_implies_Equation3955 (G : Type*) [Magma G] (h : Equation3984 G) : Equation3955 G := λ x y => h x y x y
theorem Equation3985_implies_Equation3954 (G : Type*) [Magma G] (h : Equation3985 G) : Equation3954 G := λ x y => h x y x y
theorem Equation3986_implies_Equation3955 (G : Type*) [Magma G] (h : Equation3986 G) : Equation3955 G := λ x y => h x y x y
theorem Equation3991_implies_Equation3915 (G : Type*) [Magma G] (h : Equation3991 G) : Equation3915 G := λ x y => h x y x y
theorem Equation3995_implies_Equation3918 (G : Type*) [Magma G] (h : Equation3995 G) : Equation3918 G := λ x y => h x y x y
theorem Equation3999_implies_Equation3915 (G : Type*) [Magma G] (h : Equation3999 G) : Equation3915 G := λ x y => h x y x y
theorem Equation4000_implies_Equation3917 (G : Type*) [Magma G] (h : Equation4000 G) : Equation3917 G := λ x y => h x y x y
theorem Equation4001_implies_Equation3918 (G : Type*) [Magma G] (h : Equation4001 G) : Equation3918 G := λ x y => h x y x y
theorem Equation4002_implies_Equation3917 (G : Type*) [Magma G] (h : Equation4002 G) : Equation3917 G := λ x y => h x y x y
theorem Equation4003_implies_Equation3918 (G : Type*) [Magma G] (h : Equation4003 G) : Equation3918 G := λ x y => h x y x y
theorem Equation4008_implies_Equation3925 (G : Type*) [Magma G] (h : Equation4008 G) : Equation3925 G := λ x y => h x y x y
theorem Equation4012_implies_Equation3928 (G : Type*) [Magma G] (h : Equation4012 G) : Equation3928 G := λ x y => h x y x y
theorem Equation4016_implies_Equation3925 (G : Type*) [Magma G] (h : Equation4016 G) : Equation3925 G := λ x y => h x y x y
theorem Equation4017_implies_Equation3927 (G : Type*) [Magma G] (h : Equation4017 G) : Equation3927 G := λ x y => h x y x y
theorem Equation4018_implies_Equation3928 (G : Type*) [Magma G] (h : Equation4018 G) : Equation3928 G := λ x y => h x y x y
theorem Equation4019_implies_Equation3927 (G : Type*) [Magma G] (h : Equation4019 G) : Equation3927 G := λ x y => h x y x y
theorem Equation4020_implies_Equation3928 (G : Type*) [Magma G] (h : Equation4020 G) : Equation3928 G := λ x y => h x y x y
theorem Equation4025_implies_Equation3915 (G : Type*) [Magma G] (h : Equation4025 G) : Equation3915 G := λ x y => h x y x y
theorem Equation4029_implies_Equation3918 (G : Type*) [Magma G] (h : Equation4029 G) : Equation3918 G := λ x y => h x y x y
theorem Equation4033_implies_Equation3915 (G : Type*) [Magma G] (h : Equation4033 G) : Equation3915 G := λ x y => h x y x y
theorem Equation4034_implies_Equation3917 (G : Type*) [Magma G] (h : Equation4034 G) : Equation3917 G := λ x y => h x y x y
theorem Equation4035_implies_Equation3918 (G : Type*) [Magma G] (h : Equation4035 G) : Equation3918 G := λ x y => h x y x y
theorem Equation4036_implies_Equation3917 (G : Type*) [Magma G] (h : Equation4036 G) : Equation3917 G := λ x y => h x y x y
theorem Equation4037_implies_Equation3918 (G : Type*) [Magma G] (h : Equation4037 G) : Equation3918 G := λ x y => h x y x y
theorem Equation4039_implies_Equation3924 (G : Type*) [Magma G] (h : Equation4039 G) : Equation3924 G := λ x y => h x y x y
theorem Equation4040_implies_Equation3925 (G : Type*) [Magma G] (h : Equation4040 G) : Equation3925 G := λ x y => h x y x y
theorem Equation4041_implies_Equation3924 (G : Type*) [Magma G] (h : Equation4041 G) : Equation3924 G := λ x y => h x y x y
theorem Equation4042_implies_Equation3925 (G : Type*) [Magma G] (h : Equation4042 G) : Equation3925 G := λ x y => h x y x y
theorem Equation4044_implies_Equation3927 (G : Type*) [Magma G] (h : Equation4044 G) : Equation3927 G := λ x y => h x y x y
theorem Equation4045_implies_Equation3928 (G : Type*) [Magma G] (h : Equation4045 G) : Equation3928 G := λ x y => h x y x y
theorem Equation4046_implies_Equation3927 (G : Type*) [Magma G] (h : Equation4046 G) : Equation3927 G := λ x y => h x y x y
theorem Equation4047_implies_Equation3928 (G : Type*) [Magma G] (h : Equation4047 G) : Equation3928 G := λ x y => h x y x y
theorem Equation4049_implies_Equation3924 (G : Type*) [Magma G] (h : Equation4049 G) : Equation3924 G := λ x y => h x y x y
theorem Equation4050_implies_Equation3925 (G : Type*) [Magma G] (h : Equation4050 G) : Equation3925 G := λ x y => h x y x y
theorem Equation4051_implies_Equation3924 (G : Type*) [Magma G] (h : Equation4051 G) : Equation3924 G := λ x y => h x y x y
theorem Equation4052_implies_Equation3925 (G : Type*) [Magma G] (h : Equation4052 G) : Equation3925 G := λ x y => h x y x y
theorem Equation4054_implies_Equation3927 (G : Type*) [Magma G] (h : Equation4054 G) : Equation3927 G := λ x y => h x y x y
theorem Equation4055_implies_Equation3928 (G : Type*) [Magma G] (h : Equation4055 G) : Equation3928 G := λ x y => h x y x y
theorem Equation4056_implies_Equation3927 (G : Type*) [Magma G] (h : Equation4056 G) : Equation3927 G := λ x y => h x y x y
theorem Equation4057_implies_Equation3928 (G : Type*) [Magma G] (h : Equation4057 G) : Equation3928 G := λ x y => h x y x y
theorem Equation4079_implies_Equation4071 (G : Type*) [Magma G] (h : Equation4079 G) : Equation4071 G := λ x y => h x y x y
theorem Equation4089_implies_Equation4081 (G : Type*) [Magma G] (h : Equation4089 G) : Equation4081 G := λ x y => h x y x y
theorem Equation4099_implies_Equation4091 (G : Type*) [Magma G] (h : Equation4099 G) : Equation4091 G := λ x y => h x y x y
theorem Equation4103_implies_Equation4081 (G : Type*) [Magma G] (h : Equation4103 G) : Equation4081 G := λ x y => h x y x y
theorem Equation4107_implies_Equation4084 (G : Type*) [Magma G] (h : Equation4107 G) : Equation4084 G := λ x y => h x y x y
theorem Equation4111_implies_Equation4081 (G : Type*) [Magma G] (h : Equation4111 G) : Equation4081 G := λ x y => h x y x y
theorem Equation4112_implies_Equation4083 (G : Type*) [Magma G] (h : Equation4112 G) : Equation4083 G := λ x y => h x y x y
theorem Equation4113_implies_Equation4084 (G : Type*) [Magma G] (h : Equation4113 G) : Equation4084 G := λ x y => h x y x y
theorem Equation4114_implies_Equation4083 (G : Type*) [Magma G] (h : Equation4114 G) : Equation4083 G := λ x y => h x y x y
theorem Equation4115_implies_Equation4084 (G : Type*) [Magma G] (h : Equation4115 G) : Equation4084 G := λ x y => h x y x y
theorem Equation4126_implies_Equation4118 (G : Type*) [Magma G] (h : Equation4126 G) : Equation4118 G := λ x y => h x y x y
theorem Equation4136_implies_Equation4128 (G : Type*) [Magma G] (h : Equation4136 G) : Equation4128 G := λ x y => h x y x y
theorem Equation4140_implies_Equation4118 (G : Type*) [Magma G] (h : Equation4140 G) : Equation4118 G := λ x y => h x y x y
theorem Equation4144_implies_Equation4121 (G : Type*) [Magma G] (h : Equation4144 G) : Equation4121 G := λ x y => h x y x y
theorem Equation4148_implies_Equation4118 (G : Type*) [Magma G] (h : Equation4148 G) : Equation4118 G := λ x y => h x y x y
theorem Equation4149_implies_Equation4120 (G : Type*) [Magma G] (h : Equation4149 G) : Equation4120 G := λ x y => h x y x y
theorem Equation4150_implies_Equation4121 (G : Type*) [Magma G] (h : Equation4150 G) : Equation4121 G := λ x y => h x y x y
theorem Equation4151_implies_Equation4120 (G : Type*) [Magma G] (h : Equation4151 G) : Equation4120 G := λ x y => h x y x y
theorem Equation4152_implies_Equation4121 (G : Type*) [Magma G] (h : Equation4152 G) : Equation4121 G := λ x y => h x y x y
theorem Equation4163_implies_Equation4155 (G : Type*) [Magma G] (h : Equation4163 G) : Equation4155 G := λ x y => h x y x y
theorem Equation4173_implies_Equation4165 (G : Type*) [Magma G] (h : Equation4173 G) : Equation4165 G := λ x y => h x y x y
theorem Equation4177_implies_Equation4155 (G : Type*) [Magma G] (h : Equation4177 G) : Equation4155 G := λ x y => h x y x y
theorem Equation4181_implies_Equation4158 (G : Type*) [Magma G] (h : Equation4181 G) : Equation4158 G := λ x y => h x y x y
theorem Equation4185_implies_Equation4155 (G : Type*) [Magma G] (h : Equation4185 G) : Equation4155 G := λ x y => h x y x y
theorem Equation4186_implies_Equation4157 (G : Type*) [Magma G] (h : Equation4186 G) : Equation4157 G := λ x y => h x y x y
theorem Equation4187_implies_Equation4158 (G : Type*) [Magma G] (h : Equation4187 G) : Equation4158 G := λ x y => h x y x y
theorem Equation4188_implies_Equation4157 (G : Type*) [Magma G] (h : Equation4188 G) : Equation4157 G := λ x y => h x y x y
theorem Equation4189_implies_Equation4158 (G : Type*) [Magma G] (h : Equation4189 G) : Equation4158 G := λ x y => h x y x y
theorem Equation4194_implies_Equation4118 (G : Type*) [Magma G] (h : Equation4194 G) : Equation4118 G := λ x y => h x y x y
theorem Equation4198_implies_Equation4121 (G : Type*) [Magma G] (h : Equation4198 G) : Equation4121 G := λ x y => h x y x y
theorem Equation4202_implies_Equation4118 (G : Type*) [Magma G] (h : Equation4202 G) : Equation4118 G := λ x y => h x y x y
theorem Equation4203_implies_Equation4120 (G : Type*) [Magma G] (h : Equation4203 G) : Equation4120 G := λ x y => h x y x y
theorem Equation4204_implies_Equation4121 (G : Type*) [Magma G] (h : Equation4204 G) : Equation4121 G := λ x y => h x y x y
theorem Equation4205_implies_Equation4120 (G : Type*) [Magma G] (h : Equation4205 G) : Equation4120 G := λ x y => h x y x y
theorem Equation4206_implies_Equation4121 (G : Type*) [Magma G] (h : Equation4206 G) : Equation4121 G := λ x y => h x y x y
theorem Equation4211_implies_Equation4128 (G : Type*) [Magma G] (h : Equation4211 G) : Equation4128 G := λ x y => h x y x y
theorem Equation4215_implies_Equation4131 (G : Type*) [Magma G] (h : Equation4215 G) : Equation4131 G := λ x y => h x y x y
theorem Equation4219_implies_Equation4128 (G : Type*) [Magma G] (h : Equation4219 G) : Equation4128 G := λ x y => h x y x y
theorem Equation4220_implies_Equation4130 (G : Type*) [Magma G] (h : Equation4220 G) : Equation4130 G := λ x y => h x y x y
theorem Equation4221_implies_Equation4131 (G : Type*) [Magma G] (h : Equation4221 G) : Equation4131 G := λ x y => h x y x y
theorem Equation4222_implies_Equation4130 (G : Type*) [Magma G] (h : Equation4222 G) : Equation4130 G := λ x y => h x y x y
theorem Equation4223_implies_Equation4131 (G : Type*) [Magma G] (h : Equation4223 G) : Equation4131 G := λ x y => h x y x y
theorem Equation4228_implies_Equation4118 (G : Type*) [Magma G] (h : Equation4228 G) : Equation4118 G := λ x y => h x y x y
theorem Equation4232_implies_Equation4121 (G : Type*) [Magma G] (h : Equation4232 G) : Equation4121 G := λ x y => h x y x y
theorem Equation4236_implies_Equation4118 (G : Type*) [Magma G] (h : Equation4236 G) : Equation4118 G := λ x y => h x y x y
theorem Equation4237_implies_Equation4120 (G : Type*) [Magma G] (h : Equation4237 G) : Equation4120 G := λ x y => h x y x y
theorem Equation4238_implies_Equation4121 (G : Type*) [Magma G] (h : Equation4238 G) : Equation4121 G := λ x y => h x y x y
theorem Equation4239_implies_Equation4120 (G : Type*) [Magma G] (h : Equation4239 G) : Equation4120 G := λ x y => h x y x y
theorem Equation4240_implies_Equation4121 (G : Type*) [Magma G] (h : Equation4240 G) : Equation4121 G := λ x y => h x y x y
theorem Equation4242_implies_Equation4127 (G : Type*) [Magma G] (h : Equation4242 G) : Equation4127 G := λ x y => h x y x y
theorem Equation4243_implies_Equation4128 (G : Type*) [Magma G] (h : Equation4243 G) : Equation4128 G := λ x y => h x y x y
theorem Equation4244_implies_Equation4127 (G : Type*) [Magma G] (h : Equation4244 G) : Equation4127 G := λ x y => h x y x y
theorem Equation4245_implies_Equation4128 (G : Type*) [Magma G] (h : Equation4245 G) : Equation4128 G := λ x y => h x y x y
theorem Equation4247_implies_Equation4130 (G : Type*) [Magma G] (h : Equation4247 G) : Equation4130 G := λ x y => h x y x y
theorem Equation4248_implies_Equation4131 (G : Type*) [Magma G] (h : Equation4248 G) : Equation4131 G := λ x y => h x y x y
theorem Equation4249_implies_Equation4130 (G : Type*) [Magma G] (h : Equation4249 G) : Equation4130 G := λ x y => h x y x y
theorem Equation4250_implies_Equation4131 (G : Type*) [Magma G] (h : Equation4250 G) : Equation4131 G := λ x y => h x y x y
theorem Equation4252_implies_Equation4127 (G : Type*) [Magma G] (h : Equation4252 G) : Equation4127 G := λ x y => h x y x y
theorem Equation4253_implies_Equation4128 (G : Type*) [Magma G] (h : Equation4253 G) : Equation4128 G := λ x y => h x y x y
theorem Equation4254_implies_Equation4127 (G : Type*) [Magma G] (h : Equation4254 G) : Equation4127 G := λ x y => h x y x y
theorem Equation4255_implies_Equation4128 (G : Type*) [Magma G] (h : Equation4255 G) : Equation4128 G := λ x y => h x y x y
theorem Equation4257_implies_Equation4130 (G : Type*) [Magma G] (h : Equation4257 G) : Equation4130 G := λ x y => h x y x y
theorem Equation4258_implies_Equation4131 (G : Type*) [Magma G] (h : Equation4258 G) : Equation4131 G := λ x y => h x y x y
theorem Equation4259_implies_Equation4130 (G : Type*) [Magma G] (h : Equation4259 G) : Equation4130 G := λ x y => h x y x y
theorem Equation4260_implies_Equation4131 (G : Type*) [Magma G] (h : Equation4260 G) : Equation4131 G := λ x y => h x y x y
theorem Equation4281_implies_Equation4273 (G : Type*) [Magma G] (h : Equation4281 G) : Equation4273 G := λ x y => h x y x y
theorem Equation4298_implies_Equation4291 (G : Type*) [Magma G] (h : Equation4298 G) : Equation4291 G := λ x y => h x y x y
theorem Equation4306_implies_Equation4284 (G : Type*) [Magma G] (h : Equation4306 G) : Equation4284 G := λ x y => h x y x y
theorem Equation4309_implies_Equation4283 (G : Type*) [Magma G] (h : Equation4309 G) : Equation4283 G := λ x y => h x y x y
theorem Equation4310_implies_Equation4284 (G : Type*) [Magma G] (h : Equation4310 G) : Equation4284 G := λ x y => h x y x y
theorem Equation4311_implies_Equation4283 (G : Type*) [Magma G] (h : Equation4311 G) : Equation4283 G := λ x y => h x y x y
theorem Equation4312_implies_Equation4284 (G : Type*) [Magma G] (h : Equation4312 G) : Equation4284 G := λ x y => h x y x y
theorem Equation4326_implies_Equation4321 (G : Type*) [Magma G] (h : Equation4326 G) : Equation4321 G := λ x y => h x y x y
theorem Equation4333_implies_Equation4314 (G : Type*) [Magma G] (h : Equation4333 G) : Equation4314 G := λ x y => h x y x y
theorem Equation4335_implies_Equation4314 (G : Type*) [Magma G] (h : Equation4335 G) : Equation4314 G := λ x y => h x y x y
theorem Equation4337_implies_Equation4314 (G : Type*) [Magma G] (h : Equation4337 G) : Equation4314 G := λ x y => h x y x y
theorem Equation4357_implies_Equation4314 (G : Type*) [Magma G] (h : Equation4357 G) : Equation4314 G := λ x y => h x y x y
theorem Equation4363_implies_Equation4321 (G : Type*) [Magma G] (h : Equation4363 G) : Equation4321 G := λ x y => h x y x y
theorem Equation4365_implies_Equation4321 (G : Type*) [Magma G] (h : Equation4365 G) : Equation4321 G := λ x y => h x y x y
theorem Equation4370_implies_Equation4314 (G : Type*) [Magma G] (h : Equation4370 G) : Equation4314 G := λ x y => h x y x y
theorem Equation4372_implies_Equation4314 (G : Type*) [Magma G] (h : Equation4372 G) : Equation4314 G := λ x y => h x y x y
theorem Equation4376_implies_Equation4321 (G : Type*) [Magma G] (h : Equation4376 G) : Equation4321 G := λ x y => h x y x y
theorem Equation4394_implies_Equation4386 (G : Type*) [Magma G] (h : Equation4394 G) : Equation4386 G := λ x y => h x y x y
theorem Equation4404_implies_Equation4396 (G : Type*) [Magma G] (h : Equation4404 G) : Equation4396 G := λ x y => h x y x y
theorem Equation4414_implies_Equation4406 (G : Type*) [Magma G] (h : Equation4414 G) : Equation4406 G := λ x y => h x y x y
theorem Equation4418_implies_Equation4396 (G : Type*) [Magma G] (h : Equation4418 G) : Equation4396 G := λ x y => h x y x y
theorem Equation4422_implies_Equation4399 (G : Type*) [Magma G] (h : Equation4422 G) : Equation4399 G := λ x y => h x y x y
theorem Equation4426_implies_Equation4396 (G : Type*) [Magma G] (h : Equation4426 G) : Equation4396 G := λ x y => h x y x y
theorem Equation4427_implies_Equation4398 (G : Type*) [Magma G] (h : Equation4427 G) : Equation4398 G := λ x y => h x y x y
theorem Equation4428_implies_Equation4399 (G : Type*) [Magma G] (h : Equation4428 G) : Equation4399 G := λ x y => h x y x y
theorem Equation4429_implies_Equation4398 (G : Type*) [Magma G] (h : Equation4429 G) : Equation4398 G := λ x y => h x y x y
theorem Equation4430_implies_Equation4399 (G : Type*) [Magma G] (h : Equation4430 G) : Equation4399 G := λ x y => h x y x y
theorem Equation4441_implies_Equation4433 (G : Type*) [Magma G] (h : Equation4441 G) : Equation4433 G := λ x y => h x y x y
theorem Equation4451_implies_Equation4443 (G : Type*) [Magma G] (h : Equation4451 G) : Equation4443 G := λ x y => h x y x y
theorem Equation4455_implies_Equation4433 (G : Type*) [Magma G] (h : Equation4455 G) : Equation4433 G := λ x y => h x y x y
theorem Equation4459_implies_Equation4436 (G : Type*) [Magma G] (h : Equation4459 G) : Equation4436 G := λ x y => h x y x y
theorem Equation4463_implies_Equation4433 (G : Type*) [Magma G] (h : Equation4463 G) : Equation4433 G := λ x y => h x y x y
theorem Equation4464_implies_Equation4435 (G : Type*) [Magma G] (h : Equation4464 G) : Equation4435 G := λ x y => h x y x y
theorem Equation4465_implies_Equation4436 (G : Type*) [Magma G] (h : Equation4465 G) : Equation4436 G := λ x y => h x y x y
theorem Equation4466_implies_Equation4435 (G : Type*) [Magma G] (h : Equation4466 G) : Equation4435 G := λ x y => h x y x y
theorem Equation4467_implies_Equation4436 (G : Type*) [Magma G] (h : Equation4467 G) : Equation4436 G := λ x y => h x y x y
theorem Equation4478_implies_Equation4470 (G : Type*) [Magma G] (h : Equation4478 G) : Equation4470 G := λ x y => h x y x y
theorem Equation4488_implies_Equation4480 (G : Type*) [Magma G] (h : Equation4488 G) : Equation4480 G := λ x y => h x y x y
theorem Equation4492_implies_Equation4470 (G : Type*) [Magma G] (h : Equation4492 G) : Equation4470 G := λ x y => h x y x y
theorem Equation4496_implies_Equation4473 (G : Type*) [Magma G] (h : Equation4496 G) : Equation4473 G := λ x y => h x y x y
theorem Equation4500_implies_Equation4470 (G : Type*) [Magma G] (h : Equation4500 G) : Equation4470 G := λ x y => h x y x y
theorem Equation4501_implies_Equation4472 (G : Type*) [Magma G] (h : Equation4501 G) : Equation4472 G := λ x y => h x y x y
theorem Equation4502_implies_Equation4473 (G : Type*) [Magma G] (h : Equation4502 G) : Equation4473 G := λ x y => h x y x y
theorem Equation4503_implies_Equation4472 (G : Type*) [Magma G] (h : Equation4503 G) : Equation4472 G := λ x y => h x y x y
theorem Equation4504_implies_Equation4473 (G : Type*) [Magma G] (h : Equation4504 G) : Equation4473 G := λ x y => h x y x y
theorem Equation4509_implies_Equation4433 (G : Type*) [Magma G] (h : Equation4509 G) : Equation4433 G := λ x y => h x y x y
theorem Equation4513_implies_Equation4436 (G : Type*) [Magma G] (h : Equation4513 G) : Equation4436 G := λ x y => h x y x y
theorem Equation4517_implies_Equation4433 (G : Type*) [Magma G] (h : Equation4517 G) : Equation4433 G := λ x y => h x y x y
theorem Equation4518_implies_Equation4435 (G : Type*) [Magma G] (h : Equation4518 G) : Equation4435 G := λ x y => h x y x y
theorem Equation4519_implies_Equation4436 (G : Type*) [Magma G] (h : Equation4519 G) : Equation4436 G := λ x y => h x y x y
theorem Equation4520_implies_Equation4435 (G : Type*) [Magma G] (h : Equation4520 G) : Equation4435 G := λ x y => h x y x y
theorem Equation4521_implies_Equation4436 (G : Type*) [Magma G] (h : Equation4521 G) : Equation4436 G := λ x y => h x y x y
theorem Equation4526_implies_Equation4443 (G : Type*) [Magma G] (h : Equation4526 G) : Equation4443 G := λ x y => h x y x y
theorem Equation4530_implies_Equation4446 (G : Type*) [Magma G] (h : Equation4530 G) : Equation4446 G := λ x y => h x y x y
theorem Equation4534_implies_Equation4443 (G : Type*) [Magma G] (h : Equation4534 G) : Equation4443 G := λ x y => h x y x y
theorem Equation4535_implies_Equation4445 (G : Type*) [Magma G] (h : Equation4535 G) : Equation4445 G := λ x y => h x y x y
theorem Equation4536_implies_Equation4446 (G : Type*) [Magma G] (h : Equation4536 G) : Equation4446 G := λ x y => h x y x y
theorem Equation4537_implies_Equation4445 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4445 G := λ x y => h x y x y
theorem Equation4538_implies_Equation4446 (G : Type*) [Magma G] (h : Equation4538 G) : Equation4446 G := λ x y => h x y x y
theorem Equation4543_implies_Equation4433 (G : Type*) [Magma G] (h : Equation4543 G) : Equation4433 G := λ x y => h x y x y
theorem Equation4547_implies_Equation4436 (G : Type*) [Magma G] (h : Equation4547 G) : Equation4436 G := λ x y => h x y x y
theorem Equation4551_implies_Equation4433 (G : Type*) [Magma G] (h : Equation4551 G) : Equation4433 G := λ x y => h x y x y
theorem Equation4552_implies_Equation4435 (G : Type*) [Magma G] (h : Equation4552 G) : Equation4435 G := λ x y => h x y x y
theorem Equation4553_implies_Equation4436 (G : Type*) [Magma G] (h : Equation4553 G) : Equation4436 G := λ x y => h x y x y
theorem Equation4554_implies_Equation4435 (G : Type*) [Magma G] (h : Equation4554 G) : Equation4435 G := λ x y => h x y x y
theorem Equation4555_implies_Equation4436 (G : Type*) [Magma G] (h : Equation4555 G) : Equation4436 G := λ x y => h x y x y
theorem Equation4557_implies_Equation4442 (G : Type*) [Magma G] (h : Equation4557 G) : Equation4442 G := λ x y => h x y x y
theorem Equation4558_implies_Equation4443 (G : Type*) [Magma G] (h : Equation4558 G) : Equation4443 G := λ x y => h x y x y
theorem Equation4559_implies_Equation4442 (G : Type*) [Magma G] (h : Equation4559 G) : Equation4442 G := λ x y => h x y x y
theorem Equation4560_implies_Equation4443 (G : Type*) [Magma G] (h : Equation4560 G) : Equation4443 G := λ x y => h x y x y
theorem Equation4562_implies_Equation4445 (G : Type*) [Magma G] (h : Equation4562 G) : Equation4445 G := λ x y => h x y x y
theorem Equation4563_implies_Equation4446 (G : Type*) [Magma G] (h : Equation4563 G) : Equation4446 G := λ x y => h x y x y
theorem Equation4564_implies_Equation4445 (G : Type*) [Magma G] (h : Equation4564 G) : Equation4445 G := λ x y => h x y x y
theorem Equation4565_implies_Equation4446 (G : Type*) [Magma G] (h : Equation4565 G) : Equation4446 G := λ x y => h x y x y
theorem Equation4567_implies_Equation4442 (G : Type*) [Magma G] (h : Equation4567 G) : Equation4442 G := λ x y => h x y x y
theorem Equation4568_implies_Equation4443 (G : Type*) [Magma G] (h : Equation4568 G) : Equation4443 G := λ x y => h x y x y
theorem Equation4569_implies_Equation4442 (G : Type*) [Magma G] (h : Equation4569 G) : Equation4442 G := λ x y => h x y x y
theorem Equation4570_implies_Equation4443 (G : Type*) [Magma G] (h : Equation4570 G) : Equation4443 G := λ x y => h x y x y
theorem Equation4572_implies_Equation4445 (G : Type*) [Magma G] (h : Equation4572 G) : Equation4445 G := λ x y => h x y x y
theorem Equation4573_implies_Equation4446 (G : Type*) [Magma G] (h : Equation4573 G) : Equation4446 G := λ x y => h x y x y
theorem Equation4574_implies_Equation4445 (G : Type*) [Magma G] (h : Equation4574 G) : Equation4445 G := λ x y => h x y x y
theorem Equation4575_implies_Equation4446 (G : Type*) [Magma G] (h : Equation4575 G) : Equation4446 G := λ x y => h x y x y
theorem Equation4596_implies_Equation4588 (G : Type*) [Magma G] (h : Equation4596 G) : Equation4588 G := λ x y => h x y x y
theorem Equation4613_implies_Equation4606 (G : Type*) [Magma G] (h : Equation4613 G) : Equation4606 G := λ x y => h x y x y
theorem Equation4621_implies_Equation4599 (G : Type*) [Magma G] (h : Equation4621 G) : Equation4599 G := λ x y => h x y x y
theorem Equation4624_implies_Equation4598 (G : Type*) [Magma G] (h : Equation4624 G) : Equation4598 G := λ x y => h x y x y
theorem Equation4625_implies_Equation4599 (G : Type*) [Magma G] (h : Equation4625 G) : Equation4599 G := λ x y => h x y x y
theorem Equation4626_implies_Equation4598 (G : Type*) [Magma G] (h : Equation4626 G) : Equation4598 G := λ x y => h x y x y
theorem Equation4627_implies_Equation4599 (G : Type*) [Magma G] (h : Equation4627 G) : Equation4599 G := λ x y => h x y x y
theorem Equation4641_implies_Equation4636 (G : Type*) [Magma G] (h : Equation4641 G) : Equation4636 G := λ x y => h x y x y
theorem Equation4648_implies_Equation4629 (G : Type*) [Magma G] (h : Equation4648 G) : Equation4629 G := λ x y => h x y x y
theorem Equation4650_implies_Equation4629 (G : Type*) [Magma G] (h : Equation4650 G) : Equation4629 G := λ x y => h x y x y
theorem Equation4652_implies_Equation4629 (G : Type*) [Magma G] (h : Equation4652 G) : Equation4629 G := λ x y => h x y x y
theorem Equation4672_implies_Equation4629 (G : Type*) [Magma G] (h : Equation4672 G) : Equation4629 G := λ x y => h x y x y
theorem Equation4678_implies_Equation4636 (G : Type*) [Magma G] (h : Equation4678 G) : Equation4636 G := λ x y => h x y x y
theorem Equation4680_implies_Equation4636 (G : Type*) [Magma G] (h : Equation4680 G) : Equation4636 G := λ x y => h x y x y
theorem Equation4685_implies_Equation4629 (G : Type*) [Magma G] (h : Equation4685 G) : Equation4629 G := λ x y => h x y x y
theorem Equation4687_implies_Equation4629 (G : Type*) [Magma G] (h : Equation4687 G) : Equation4629 G := λ x y => h x y x y
theorem Equation4691_implies_Equation4636 (G : Type*) [Magma G] (h : Equation4691 G) : Equation4636 G := λ x y => h x y x y