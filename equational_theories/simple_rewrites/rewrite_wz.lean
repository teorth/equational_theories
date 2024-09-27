import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation21 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ z)
def Equation22 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ w)
def Equation36 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ z
def Equation37 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ w
def Equation60 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ z))
def Equation61 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ w))
def Equation70 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ z))
def Equation71 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ w))
def Equation80 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ z))
def Equation81 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ w))
def Equation84 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ z))
def Equation85 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ w))
def Equation88 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ z))
def Equation89 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ w))
def Equation90 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ x))
def Equation91 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ y))
def Equation92 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ z))
def Equation93 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ w))
def Equation94 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ x))
def Equation95 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ y))
def Equation96 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ z))
def Equation97 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ w))
def Equation112 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ z)
def Equation113 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ w)
def Equation122 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ z)
def Equation123 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ w)
def Equation132 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ z)
def Equation133 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ w)
def Equation136 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ z)
def Equation137 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ w)
def Equation140 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ z)
def Equation141 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ w)
def Equation142 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ x)
def Equation143 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ y)
def Equation144 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ z)
def Equation145 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ w)
def Equation146 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ x)
def Equation147 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ y)
def Equation148 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ z)
def Equation149 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ w)
def Equation164 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ z)
def Equation165 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ w)
def Equation174 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ z)
def Equation175 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ w)
def Equation184 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ z)
def Equation185 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ w)
def Equation188 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ z)
def Equation189 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ w)
def Equation192 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ z)
def Equation193 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ w)
def Equation194 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ x)
def Equation195 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ y)
def Equation196 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ z)
def Equation197 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ w)
def Equation198 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ x)
def Equation199 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ y)
def Equation200 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ z)
def Equation201 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ w)
def Equation216 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ z
def Equation217 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ w
def Equation226 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ z
def Equation227 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ w
def Equation236 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ z
def Equation237 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ w
def Equation240 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ z
def Equation241 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ w
def Equation244 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ z
def Equation245 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ w
def Equation246 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ x
def Equation247 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ y
def Equation248 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ z
def Equation249 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ w
def Equation250 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ x
def Equation251 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ y
def Equation252 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ z
def Equation253 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ w
def Equation268 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ z
def Equation269 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ w
def Equation278 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ z
def Equation279 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ w
def Equation288 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ z
def Equation289 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ w
def Equation292 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ z
def Equation293 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ w
def Equation296 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ z
def Equation297 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ w
def Equation298 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ x
def Equation299 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ y
def Equation300 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ z
def Equation301 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ w
def Equation302 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ x
def Equation303 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ y
def Equation304 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ z
def Equation305 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ w
def Equation320 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ z)
def Equation321 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ w)
def Equation330 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ z)
def Equation331 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ w)
def Equation340 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ z)
def Equation341 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ w)
def Equation344 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ z)
def Equation345 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ w)
def Equation348 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ z)
def Equation349 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ w)
def Equation350 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ x)
def Equation351 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ y)
def Equation352 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ z)
def Equation353 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ w)
def Equation354 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ x)
def Equation355 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ y)
def Equation356 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ z)
def Equation357 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ w)
def Equation372 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ z
def Equation373 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ w
def Equation382 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ z
def Equation383 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ w
def Equation392 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ z
def Equation393 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ w
def Equation396 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ z
def Equation397 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ w
def Equation400 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ z
def Equation401 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ w
def Equation402 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ x
def Equation403 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ y
def Equation404 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ z
def Equation405 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ w
def Equation406 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ x
def Equation407 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ y
def Equation408 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ z
def Equation409 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ w
def Equation424 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ (y ∘ (z ∘ z)))
def Equation425 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (x ∘ (y ∘ (z ∘ w)))
def Equation434 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (x ∘ (z ∘ z)))
def Equation435 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (x ∘ (z ∘ w)))
def Equation444 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (y ∘ (z ∘ z)))
def Equation445 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (y ∘ (z ∘ w)))
def Equation448 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ (x ∘ z)))
def Equation449 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (x ∘ w)))
def Equation452 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ (y ∘ z)))
def Equation453 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (y ∘ w)))
def Equation454 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ (z ∘ x)))
def Equation455 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ (z ∘ y)))
def Equation456 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ (z ∘ z)))
def Equation457 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (z ∘ w)))
def Equation458 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (w ∘ x)))
def Equation459 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (w ∘ y)))
def Equation460 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (w ∘ z)))
def Equation461 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (w ∘ w)))
def Equation471 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (x ∘ (z ∘ z)))
def Equation472 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (x ∘ (z ∘ w)))
def Equation481 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (y ∘ (z ∘ z)))
def Equation482 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (y ∘ (z ∘ w)))
def Equation485 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ (x ∘ z)))
def Equation486 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (x ∘ w)))
def Equation489 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ (y ∘ z)))
def Equation490 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (y ∘ w)))
def Equation491 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ (z ∘ x)))
def Equation492 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ (z ∘ y)))
def Equation493 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ (z ∘ z)))
def Equation494 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (z ∘ w)))
def Equation495 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (w ∘ x)))
def Equation496 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (w ∘ y)))
def Equation497 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (w ∘ z)))
def Equation498 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (w ∘ w)))
def Equation508 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (x ∘ (z ∘ z)))
def Equation509 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (x ∘ (z ∘ w)))
def Equation518 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (y ∘ (z ∘ z)))
def Equation519 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (y ∘ (z ∘ w)))
def Equation522 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ (x ∘ z)))
def Equation523 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (x ∘ w)))
def Equation526 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ (y ∘ z)))
def Equation527 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (y ∘ w)))
def Equation528 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ (z ∘ x)))
def Equation529 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ (z ∘ y)))
def Equation530 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ (z ∘ z)))
def Equation531 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (z ∘ w)))
def Equation532 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (w ∘ x)))
def Equation533 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (w ∘ y)))
def Equation534 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (w ∘ z)))
def Equation535 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (w ∘ w)))
def Equation539 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ (x ∘ z)))
def Equation540 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (x ∘ w)))
def Equation543 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ (y ∘ z)))
def Equation544 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (y ∘ w)))
def Equation545 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ (z ∘ x)))
def Equation546 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ (z ∘ y)))
def Equation547 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ (z ∘ z)))
def Equation548 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (z ∘ w)))
def Equation549 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (w ∘ x)))
def Equation550 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (w ∘ y)))
def Equation551 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (w ∘ z)))
def Equation552 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (w ∘ w)))
def Equation556 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ (x ∘ z)))
def Equation557 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (x ∘ w)))
def Equation560 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ (y ∘ z)))
def Equation561 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (y ∘ w)))
def Equation562 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ (z ∘ x)))
def Equation563 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ (z ∘ y)))
def Equation564 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ (z ∘ z)))
def Equation565 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (z ∘ w)))
def Equation566 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (w ∘ x)))
def Equation567 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (w ∘ y)))
def Equation568 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (w ∘ z)))
def Equation569 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (w ∘ w)))
def Equation571 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (x ∘ x)))
def Equation572 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (x ∘ y)))
def Equation573 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (x ∘ z)))
def Equation574 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (x ∘ w)))
def Equation575 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (y ∘ x)))
def Equation576 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (y ∘ y)))
def Equation577 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (y ∘ z)))
def Equation578 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (y ∘ w)))
def Equation579 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (z ∘ x)))
def Equation580 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (z ∘ y)))
def Equation581 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (z ∘ z)))
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
def Equation627 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ ((y ∘ z) ∘ z))
def Equation628 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (x ∘ ((y ∘ z) ∘ w))
def Equation637 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((x ∘ z) ∘ z))
def Equation638 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((x ∘ z) ∘ w))
def Equation647 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((y ∘ z) ∘ z))
def Equation648 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((y ∘ z) ∘ w))
def Equation651 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((z ∘ x) ∘ z))
def Equation652 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ x) ∘ w))
def Equation655 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((z ∘ y) ∘ z))
def Equation656 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ y) ∘ w))
def Equation657 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((z ∘ z) ∘ x))
def Equation658 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((z ∘ z) ∘ y))
def Equation659 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((z ∘ z) ∘ z))
def Equation660 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ z) ∘ w))
def Equation661 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ w) ∘ x))
def Equation662 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ w) ∘ y))
def Equation663 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ w) ∘ z))
def Equation664 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ w) ∘ w))
def Equation674 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((x ∘ z) ∘ z))
def Equation675 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((x ∘ z) ∘ w))
def Equation684 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((y ∘ z) ∘ z))
def Equation685 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((y ∘ z) ∘ w))
def Equation688 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((z ∘ x) ∘ z))
def Equation689 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ x) ∘ w))
def Equation692 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((z ∘ y) ∘ z))
def Equation693 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ y) ∘ w))
def Equation694 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((z ∘ z) ∘ x))
def Equation695 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((z ∘ z) ∘ y))
def Equation696 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((z ∘ z) ∘ z))
def Equation697 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ z) ∘ w))
def Equation698 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ w) ∘ x))
def Equation699 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ w) ∘ y))
def Equation700 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ w) ∘ z))
def Equation701 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ w) ∘ w))
def Equation711 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((x ∘ z) ∘ z))
def Equation712 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((x ∘ z) ∘ w))
def Equation721 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((y ∘ z) ∘ z))
def Equation722 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((y ∘ z) ∘ w))
def Equation725 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((z ∘ x) ∘ z))
def Equation726 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ x) ∘ w))
def Equation729 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((z ∘ y) ∘ z))
def Equation730 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ y) ∘ w))
def Equation731 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((z ∘ z) ∘ x))
def Equation732 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((z ∘ z) ∘ y))
def Equation733 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((z ∘ z) ∘ z))
def Equation734 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ z) ∘ w))
def Equation735 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ w) ∘ x))
def Equation736 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ w) ∘ y))
def Equation737 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ w) ∘ z))
def Equation738 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ w) ∘ w))
def Equation742 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((x ∘ x) ∘ z))
def Equation743 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ x) ∘ w))
def Equation746 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((x ∘ y) ∘ z))
def Equation747 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ y) ∘ w))
def Equation748 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((x ∘ z) ∘ x))
def Equation749 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((x ∘ z) ∘ y))
def Equation750 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((x ∘ z) ∘ z))
def Equation751 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ z) ∘ w))
def Equation752 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ w) ∘ x))
def Equation753 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ w) ∘ y))
def Equation754 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ w) ∘ z))
def Equation755 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ w) ∘ w))
def Equation759 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((y ∘ x) ∘ z))
def Equation760 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ x) ∘ w))
def Equation763 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((y ∘ y) ∘ z))
def Equation764 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ y) ∘ w))
def Equation765 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((y ∘ z) ∘ x))
def Equation766 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((y ∘ z) ∘ y))
def Equation767 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((y ∘ z) ∘ z))
def Equation768 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ z) ∘ w))
def Equation769 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ w) ∘ x))
def Equation770 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ w) ∘ y))
def Equation771 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ w) ∘ z))
def Equation772 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ w) ∘ w))
def Equation774 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ x) ∘ x))
def Equation775 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ x) ∘ y))
def Equation776 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ x) ∘ z))
def Equation777 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ x) ∘ w))
def Equation778 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ y) ∘ x))
def Equation779 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ y) ∘ y))
def Equation780 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ y) ∘ z))
def Equation781 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ y) ∘ w))
def Equation782 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ z) ∘ x))
def Equation783 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ z) ∘ y))
def Equation784 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ z) ∘ z))
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
def Equation830 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ y) ∘ (z ∘ z))
def Equation831 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((x ∘ y) ∘ (z ∘ w))
def Equation840 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ x) ∘ (z ∘ z))
def Equation841 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ x) ∘ (z ∘ w))
def Equation850 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ y) ∘ (z ∘ z))
def Equation851 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ y) ∘ (z ∘ w))
def Equation854 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ (x ∘ z))
def Equation855 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (x ∘ w))
def Equation858 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ (y ∘ z))
def Equation859 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (y ∘ w))
def Equation860 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ (z ∘ x))
def Equation861 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ (z ∘ y))
def Equation862 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ (z ∘ z))
def Equation863 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (z ∘ w))
def Equation864 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (w ∘ x))
def Equation865 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (w ∘ y))
def Equation866 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (w ∘ z))
def Equation867 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (w ∘ w))
def Equation877 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ x) ∘ (z ∘ z))
def Equation878 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ x) ∘ (z ∘ w))
def Equation887 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ y) ∘ (z ∘ z))
def Equation888 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ y) ∘ (z ∘ w))
def Equation891 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ (x ∘ z))
def Equation892 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (x ∘ w))
def Equation895 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ (y ∘ z))
def Equation896 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (y ∘ w))
def Equation897 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ (z ∘ x))
def Equation898 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ (z ∘ y))
def Equation899 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ (z ∘ z))
def Equation900 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (z ∘ w))
def Equation901 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (w ∘ x))
def Equation902 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (w ∘ y))
def Equation903 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (w ∘ z))
def Equation904 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (w ∘ w))
def Equation914 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ x) ∘ (z ∘ z))
def Equation915 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ x) ∘ (z ∘ w))
def Equation924 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ y) ∘ (z ∘ z))
def Equation925 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ y) ∘ (z ∘ w))
def Equation928 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ (x ∘ z))
def Equation929 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (x ∘ w))
def Equation932 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ (y ∘ z))
def Equation933 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (y ∘ w))
def Equation934 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ (z ∘ x))
def Equation935 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ (z ∘ y))
def Equation936 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ (z ∘ z))
def Equation937 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (z ∘ w))
def Equation938 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (w ∘ x))
def Equation939 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (w ∘ y))
def Equation940 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (w ∘ z))
def Equation941 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (w ∘ w))
def Equation945 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ (x ∘ z))
def Equation946 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (x ∘ w))
def Equation949 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ (y ∘ z))
def Equation950 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (y ∘ w))
def Equation951 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ (z ∘ x))
def Equation952 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ (z ∘ y))
def Equation953 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ (z ∘ z))
def Equation954 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (z ∘ w))
def Equation955 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (w ∘ x))
def Equation956 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (w ∘ y))
def Equation957 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (w ∘ z))
def Equation958 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (w ∘ w))
def Equation962 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ (x ∘ z))
def Equation963 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (x ∘ w))
def Equation966 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ (y ∘ z))
def Equation967 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (y ∘ w))
def Equation968 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ (z ∘ x))
def Equation969 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ (z ∘ y))
def Equation970 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ (z ∘ z))
def Equation971 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (z ∘ w))
def Equation972 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (w ∘ x))
def Equation973 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (w ∘ y))
def Equation974 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (w ∘ z))
def Equation975 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (w ∘ w))
def Equation977 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (x ∘ x))
def Equation978 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (x ∘ y))
def Equation979 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (x ∘ z))
def Equation980 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (x ∘ w))
def Equation981 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (y ∘ x))
def Equation982 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (y ∘ y))
def Equation983 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (y ∘ z))
def Equation984 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (y ∘ w))
def Equation985 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (z ∘ x))
def Equation986 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (z ∘ y))
def Equation987 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (z ∘ z))
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
def Equation1033 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ (y ∘ z)) ∘ z)
def Equation1034 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((x ∘ (y ∘ z)) ∘ w)
def Equation1043 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (x ∘ z)) ∘ z)
def Equation1044 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (x ∘ z)) ∘ w)
def Equation1053 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (y ∘ z)) ∘ z)
def Equation1054 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (y ∘ z)) ∘ w)
def Equation1057 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (z ∘ x)) ∘ z)
def Equation1058 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ x)) ∘ w)
def Equation1061 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (z ∘ y)) ∘ z)
def Equation1062 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ y)) ∘ w)
def Equation1063 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (z ∘ z)) ∘ x)
def Equation1064 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (z ∘ z)) ∘ y)
def Equation1065 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (z ∘ z)) ∘ z)
def Equation1066 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ z)) ∘ w)
def Equation1067 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ x)
def Equation1068 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ y)
def Equation1069 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ z)
def Equation1070 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ w)
def Equation1080 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (x ∘ z)) ∘ z)
def Equation1081 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (x ∘ z)) ∘ w)
def Equation1090 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (y ∘ z)) ∘ z)
def Equation1091 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (y ∘ z)) ∘ w)
def Equation1094 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (z ∘ x)) ∘ z)
def Equation1095 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ x)) ∘ w)
def Equation1098 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (z ∘ y)) ∘ z)
def Equation1099 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ y)) ∘ w)
def Equation1100 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (z ∘ z)) ∘ x)
def Equation1101 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (z ∘ z)) ∘ y)
def Equation1102 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (z ∘ z)) ∘ z)
def Equation1103 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ z)) ∘ w)
def Equation1104 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ w)) ∘ x)
def Equation1105 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ w)) ∘ y)
def Equation1106 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ w)) ∘ z)
def Equation1107 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ w)) ∘ w)
def Equation1117 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (x ∘ z)) ∘ z)
def Equation1118 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (x ∘ z)) ∘ w)
def Equation1127 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (y ∘ z)) ∘ z)
def Equation1128 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (y ∘ z)) ∘ w)
def Equation1131 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (z ∘ x)) ∘ z)
def Equation1132 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ x)) ∘ w)
def Equation1135 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (z ∘ y)) ∘ z)
def Equation1136 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ y)) ∘ w)
def Equation1137 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (z ∘ z)) ∘ x)
def Equation1138 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (z ∘ z)) ∘ y)
def Equation1139 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (z ∘ z)) ∘ z)
def Equation1140 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ z)) ∘ w)
def Equation1141 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ w)) ∘ x)
def Equation1142 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ w)) ∘ y)
def Equation1143 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ w)) ∘ z)
def Equation1144 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ w)) ∘ w)
def Equation1148 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (x ∘ x)) ∘ z)
def Equation1149 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ x)) ∘ w)
def Equation1152 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (x ∘ y)) ∘ z)
def Equation1153 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ y)) ∘ w)
def Equation1154 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (x ∘ z)) ∘ x)
def Equation1155 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (x ∘ z)) ∘ y)
def Equation1156 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (x ∘ z)) ∘ z)
def Equation1157 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ z)) ∘ w)
def Equation1158 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ x)
def Equation1159 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ y)
def Equation1160 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ z)
def Equation1161 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ w)
def Equation1165 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (y ∘ x)) ∘ z)
def Equation1166 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ x)) ∘ w)
def Equation1169 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (y ∘ y)) ∘ z)
def Equation1170 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ y)) ∘ w)
def Equation1171 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (y ∘ z)) ∘ x)
def Equation1172 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (y ∘ z)) ∘ y)
def Equation1173 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (y ∘ z)) ∘ z)
def Equation1174 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ z)) ∘ w)
def Equation1175 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ x)
def Equation1176 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ y)
def Equation1177 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ z)
def Equation1178 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ w)
def Equation1180 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ x)) ∘ x)
def Equation1181 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ x)) ∘ y)
def Equation1182 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ x)) ∘ z)
def Equation1183 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ x)) ∘ w)
def Equation1184 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ y)) ∘ x)
def Equation1185 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ y)) ∘ y)
def Equation1186 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ y)) ∘ z)
def Equation1187 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ y)) ∘ w)
def Equation1188 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ z)) ∘ x)
def Equation1189 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ z)) ∘ y)
def Equation1190 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ z)) ∘ z)
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
def Equation1236 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((x ∘ y) ∘ z) ∘ z)
def Equation1237 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((x ∘ y) ∘ z) ∘ w)
def Equation1246 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ x) ∘ z) ∘ z)
def Equation1247 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ x) ∘ z) ∘ w)
def Equation1256 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ y) ∘ z) ∘ z)
def Equation1257 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ y) ∘ z) ∘ w)
def Equation1260 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ z) ∘ x) ∘ z)
def Equation1261 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ x) ∘ w)
def Equation1264 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ z) ∘ y) ∘ z)
def Equation1265 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ y) ∘ w)
def Equation1266 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ z) ∘ z) ∘ x)
def Equation1267 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ z) ∘ z) ∘ y)
def Equation1268 (G: Type*) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ z) ∘ z) ∘ z)
def Equation1269 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ z) ∘ w)
def Equation1270 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ w) ∘ x)
def Equation1271 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ w) ∘ y)
def Equation1272 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ w) ∘ z)
def Equation1273 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ w) ∘ w)
def Equation1283 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ x) ∘ z) ∘ z)
def Equation1284 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ x) ∘ z) ∘ w)
def Equation1293 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ y) ∘ z) ∘ z)
def Equation1294 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ y) ∘ z) ∘ w)
def Equation1297 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ z) ∘ x) ∘ z)
def Equation1298 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ x) ∘ w)
def Equation1301 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ z) ∘ y) ∘ z)
def Equation1302 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ y) ∘ w)
def Equation1303 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ z) ∘ z) ∘ x)
def Equation1304 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ z) ∘ z) ∘ y)
def Equation1305 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ z) ∘ z) ∘ z)
def Equation1306 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ z) ∘ w)
def Equation1307 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ w) ∘ x)
def Equation1308 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ w) ∘ y)
def Equation1309 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ w) ∘ z)
def Equation1310 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ w) ∘ w)
def Equation1320 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ x) ∘ z) ∘ z)
def Equation1321 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ x) ∘ z) ∘ w)
def Equation1330 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ y) ∘ z) ∘ z)
def Equation1331 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ y) ∘ z) ∘ w)
def Equation1334 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ z) ∘ x) ∘ z)
def Equation1335 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ x) ∘ w)
def Equation1338 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ z) ∘ y) ∘ z)
def Equation1339 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ y) ∘ w)
def Equation1340 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ z) ∘ z) ∘ x)
def Equation1341 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ z) ∘ z) ∘ y)
def Equation1342 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ z) ∘ z) ∘ z)
def Equation1343 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ z) ∘ w)
def Equation1344 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ w) ∘ x)
def Equation1345 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ w) ∘ y)
def Equation1346 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ w) ∘ z)
def Equation1347 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ w) ∘ w)
def Equation1351 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ x) ∘ x) ∘ z)
def Equation1352 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ x) ∘ w)
def Equation1355 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ x) ∘ y) ∘ z)
def Equation1356 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ y) ∘ w)
def Equation1357 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ x) ∘ z) ∘ x)
def Equation1358 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ x) ∘ z) ∘ y)
def Equation1359 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ x) ∘ z) ∘ z)
def Equation1360 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ z) ∘ w)
def Equation1361 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ w) ∘ x)
def Equation1362 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ w) ∘ y)
def Equation1363 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ w) ∘ z)
def Equation1364 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ w) ∘ w)
def Equation1368 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ y) ∘ x) ∘ z)
def Equation1369 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ x) ∘ w)
def Equation1372 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ y) ∘ y) ∘ z)
def Equation1373 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ y) ∘ w)
def Equation1374 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ y) ∘ z) ∘ x)
def Equation1375 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ y) ∘ z) ∘ y)
def Equation1376 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ y) ∘ z) ∘ z)
def Equation1377 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ z) ∘ w)
def Equation1378 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ w) ∘ x)
def Equation1379 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ w) ∘ y)
def Equation1380 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ w) ∘ z)
def Equation1381 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ w) ∘ w)
def Equation1383 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ x) ∘ x)
def Equation1384 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ x) ∘ y)
def Equation1385 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ x) ∘ z)
def Equation1386 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ x) ∘ w)
def Equation1387 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ y) ∘ x)
def Equation1388 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ y) ∘ y)
def Equation1389 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ y) ∘ z)
def Equation1390 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ y) ∘ w)
def Equation1391 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ z) ∘ x)
def Equation1392 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ z) ∘ y)
def Equation1393 (G: Type*) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ z) ∘ z)
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
def Equation1439 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ (y ∘ (z ∘ z))
def Equation1440 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ x) ∘ (y ∘ (z ∘ w))
def Equation1449 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (x ∘ (z ∘ z))
def Equation1450 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (x ∘ (z ∘ w))
def Equation1459 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (y ∘ (z ∘ z))
def Equation1460 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (y ∘ (z ∘ w))
def Equation1463 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ (x ∘ z))
def Equation1464 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (x ∘ w))
def Equation1467 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ (y ∘ z))
def Equation1468 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (y ∘ w))
def Equation1469 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ (z ∘ x))
def Equation1470 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ (z ∘ y))
def Equation1471 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ (z ∘ z))
def Equation1472 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (z ∘ w))
def Equation1473 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (w ∘ x))
def Equation1474 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (w ∘ y))
def Equation1475 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (w ∘ z))
def Equation1476 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (w ∘ w))
def Equation1486 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (x ∘ (z ∘ z))
def Equation1487 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (x ∘ (z ∘ w))
def Equation1496 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (y ∘ (z ∘ z))
def Equation1497 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (y ∘ (z ∘ w))
def Equation1500 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ (x ∘ z))
def Equation1501 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (x ∘ w))
def Equation1504 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ (y ∘ z))
def Equation1505 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (y ∘ w))
def Equation1506 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ (z ∘ x))
def Equation1507 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ (z ∘ y))
def Equation1508 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ (z ∘ z))
def Equation1509 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (z ∘ w))
def Equation1510 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (w ∘ x))
def Equation1511 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (w ∘ y))
def Equation1512 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (w ∘ z))
def Equation1513 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (w ∘ w))
def Equation1523 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (x ∘ (z ∘ z))
def Equation1524 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (x ∘ (z ∘ w))
def Equation1533 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (y ∘ (z ∘ z))
def Equation1534 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (y ∘ (z ∘ w))
def Equation1537 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ (x ∘ z))
def Equation1538 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (x ∘ w))
def Equation1541 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ (y ∘ z))
def Equation1542 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (y ∘ w))
def Equation1543 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ (z ∘ x))
def Equation1544 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ (z ∘ y))
def Equation1545 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ (z ∘ z))
def Equation1546 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (z ∘ w))
def Equation1547 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (w ∘ x))
def Equation1548 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (w ∘ y))
def Equation1549 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (w ∘ z))
def Equation1550 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (w ∘ w))
def Equation1554 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ (x ∘ z))
def Equation1555 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (x ∘ w))
def Equation1558 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ (y ∘ z))
def Equation1559 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (y ∘ w))
def Equation1560 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ (z ∘ x))
def Equation1561 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ (z ∘ y))
def Equation1562 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ (z ∘ z))
def Equation1563 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (z ∘ w))
def Equation1564 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (w ∘ x))
def Equation1565 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (w ∘ y))
def Equation1566 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (w ∘ z))
def Equation1567 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (w ∘ w))
def Equation1571 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ (x ∘ z))
def Equation1572 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (x ∘ w))
def Equation1575 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ (y ∘ z))
def Equation1576 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (y ∘ w))
def Equation1577 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ (z ∘ x))
def Equation1578 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ (z ∘ y))
def Equation1579 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ (z ∘ z))
def Equation1580 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (z ∘ w))
def Equation1581 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (w ∘ x))
def Equation1582 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (w ∘ y))
def Equation1583 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (w ∘ z))
def Equation1584 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (w ∘ w))
def Equation1586 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (x ∘ x))
def Equation1587 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (x ∘ y))
def Equation1588 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (x ∘ z))
def Equation1589 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (x ∘ w))
def Equation1590 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (y ∘ x))
def Equation1591 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (y ∘ y))
def Equation1592 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (y ∘ z))
def Equation1593 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (y ∘ w))
def Equation1594 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (z ∘ x))
def Equation1595 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (z ∘ y))
def Equation1596 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (z ∘ z))
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
def Equation1642 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ ((y ∘ z) ∘ z)
def Equation1643 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ x) ∘ ((y ∘ z) ∘ w)
def Equation1652 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((x ∘ z) ∘ z)
def Equation1653 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((x ∘ z) ∘ w)
def Equation1662 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((y ∘ z) ∘ z)
def Equation1663 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((y ∘ z) ∘ w)
def Equation1666 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((z ∘ x) ∘ z)
def Equation1667 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ x) ∘ w)
def Equation1670 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((z ∘ y) ∘ z)
def Equation1671 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ y) ∘ w)
def Equation1672 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((z ∘ z) ∘ x)
def Equation1673 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((z ∘ z) ∘ y)
def Equation1674 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((z ∘ z) ∘ z)
def Equation1675 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ z) ∘ w)
def Equation1676 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ x)
def Equation1677 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ y)
def Equation1678 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ z)
def Equation1679 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ w)
def Equation1689 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((x ∘ z) ∘ z)
def Equation1690 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((x ∘ z) ∘ w)
def Equation1699 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((y ∘ z) ∘ z)
def Equation1700 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((y ∘ z) ∘ w)
def Equation1703 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((z ∘ x) ∘ z)
def Equation1704 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ x) ∘ w)
def Equation1707 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((z ∘ y) ∘ z)
def Equation1708 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ y) ∘ w)
def Equation1709 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((z ∘ z) ∘ x)
def Equation1710 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((z ∘ z) ∘ y)
def Equation1711 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((z ∘ z) ∘ z)
def Equation1712 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ z) ∘ w)
def Equation1713 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ w) ∘ x)
def Equation1714 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ w) ∘ y)
def Equation1715 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ w) ∘ z)
def Equation1716 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ w) ∘ w)
def Equation1726 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((x ∘ z) ∘ z)
def Equation1727 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((x ∘ z) ∘ w)
def Equation1736 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((y ∘ z) ∘ z)
def Equation1737 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((y ∘ z) ∘ w)
def Equation1740 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((z ∘ x) ∘ z)
def Equation1741 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ x) ∘ w)
def Equation1744 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((z ∘ y) ∘ z)
def Equation1745 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ y) ∘ w)
def Equation1746 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((z ∘ z) ∘ x)
def Equation1747 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((z ∘ z) ∘ y)
def Equation1748 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((z ∘ z) ∘ z)
def Equation1749 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ z) ∘ w)
def Equation1750 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ w) ∘ x)
def Equation1751 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ w) ∘ y)
def Equation1752 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ w) ∘ z)
def Equation1753 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ w) ∘ w)
def Equation1757 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((x ∘ x) ∘ z)
def Equation1758 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ x) ∘ w)
def Equation1761 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((x ∘ y) ∘ z)
def Equation1762 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ y) ∘ w)
def Equation1763 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((x ∘ z) ∘ x)
def Equation1764 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((x ∘ z) ∘ y)
def Equation1765 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((x ∘ z) ∘ z)
def Equation1766 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ z) ∘ w)
def Equation1767 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ x)
def Equation1768 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ y)
def Equation1769 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ z)
def Equation1770 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ w)
def Equation1774 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((y ∘ x) ∘ z)
def Equation1775 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ x) ∘ w)
def Equation1778 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((y ∘ y) ∘ z)
def Equation1779 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ y) ∘ w)
def Equation1780 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((y ∘ z) ∘ x)
def Equation1781 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((y ∘ z) ∘ y)
def Equation1782 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((y ∘ z) ∘ z)
def Equation1783 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ z) ∘ w)
def Equation1784 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ x)
def Equation1785 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ y)
def Equation1786 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ z)
def Equation1787 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ w)
def Equation1789 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ x) ∘ x)
def Equation1790 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ x) ∘ y)
def Equation1791 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ x) ∘ z)
def Equation1792 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ x) ∘ w)
def Equation1793 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ y) ∘ x)
def Equation1794 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ y) ∘ y)
def Equation1795 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ y) ∘ z)
def Equation1796 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ y) ∘ w)
def Equation1797 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ z) ∘ x)
def Equation1798 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ z) ∘ y)
def Equation1799 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ z) ∘ z)
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
def Equation1845 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ y)) ∘ (z ∘ z)
def Equation1846 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (x ∘ y)) ∘ (z ∘ w)
def Equation1855 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ x)) ∘ (z ∘ z)
def Equation1856 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ x)) ∘ (z ∘ w)
def Equation1865 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ y)) ∘ (z ∘ z)
def Equation1866 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ y)) ∘ (z ∘ w)
def Equation1869 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ (x ∘ z)
def Equation1870 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (x ∘ w)
def Equation1873 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ (y ∘ z)
def Equation1874 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (y ∘ w)
def Equation1875 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ (z ∘ x)
def Equation1876 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ (z ∘ y)
def Equation1877 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ (z ∘ z)
def Equation1878 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (z ∘ w)
def Equation1879 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ x)
def Equation1880 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ y)
def Equation1881 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ z)
def Equation1882 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ w)
def Equation1892 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ x)) ∘ (z ∘ z)
def Equation1893 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ x)) ∘ (z ∘ w)
def Equation1902 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ y)) ∘ (z ∘ z)
def Equation1903 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ y)) ∘ (z ∘ w)
def Equation1906 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ (x ∘ z)
def Equation1907 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (x ∘ w)
def Equation1910 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ (y ∘ z)
def Equation1911 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (y ∘ w)
def Equation1912 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ (z ∘ x)
def Equation1913 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ (z ∘ y)
def Equation1914 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ (z ∘ z)
def Equation1915 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (z ∘ w)
def Equation1916 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (w ∘ x)
def Equation1917 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (w ∘ y)
def Equation1918 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (w ∘ z)
def Equation1919 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (w ∘ w)
def Equation1929 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ x)) ∘ (z ∘ z)
def Equation1930 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ x)) ∘ (z ∘ w)
def Equation1939 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ y)) ∘ (z ∘ z)
def Equation1940 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ y)) ∘ (z ∘ w)
def Equation1943 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ (x ∘ z)
def Equation1944 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (x ∘ w)
def Equation1947 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ (y ∘ z)
def Equation1948 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (y ∘ w)
def Equation1949 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ (z ∘ x)
def Equation1950 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ (z ∘ y)
def Equation1951 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ (z ∘ z)
def Equation1952 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (z ∘ w)
def Equation1953 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (w ∘ x)
def Equation1954 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (w ∘ y)
def Equation1955 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (w ∘ z)
def Equation1956 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (w ∘ w)
def Equation1960 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ (x ∘ z)
def Equation1961 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (x ∘ w)
def Equation1964 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ (y ∘ z)
def Equation1965 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (y ∘ w)
def Equation1966 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ (z ∘ x)
def Equation1967 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ (z ∘ y)
def Equation1968 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ (z ∘ z)
def Equation1969 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (z ∘ w)
def Equation1970 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ x)
def Equation1971 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ y)
def Equation1972 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ z)
def Equation1973 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ w)
def Equation1977 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ (x ∘ z)
def Equation1978 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (x ∘ w)
def Equation1981 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ (y ∘ z)
def Equation1982 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (y ∘ w)
def Equation1983 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ (z ∘ x)
def Equation1984 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ (z ∘ y)
def Equation1985 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ (z ∘ z)
def Equation1986 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (z ∘ w)
def Equation1987 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ x)
def Equation1988 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ y)
def Equation1989 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ z)
def Equation1990 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ w)
def Equation1992 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (x ∘ x)
def Equation1993 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (x ∘ y)
def Equation1994 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (x ∘ z)
def Equation1995 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (x ∘ w)
def Equation1996 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (y ∘ x)
def Equation1997 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (y ∘ y)
def Equation1998 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (y ∘ z)
def Equation1999 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (y ∘ w)
def Equation2000 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (z ∘ x)
def Equation2001 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (z ∘ y)
def Equation2002 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (z ∘ z)
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
def Equation2048 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ y) ∘ (z ∘ z)
def Equation2049 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ x) ∘ y) ∘ (z ∘ w)
def Equation2058 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ x) ∘ (z ∘ z)
def Equation2059 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ x) ∘ (z ∘ w)
def Equation2068 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ y) ∘ (z ∘ z)
def Equation2069 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ y) ∘ (z ∘ w)
def Equation2072 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ (x ∘ z)
def Equation2073 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (x ∘ w)
def Equation2076 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ (y ∘ z)
def Equation2077 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (y ∘ w)
def Equation2078 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ (z ∘ x)
def Equation2079 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ (z ∘ y)
def Equation2080 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ (z ∘ z)
def Equation2081 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (z ∘ w)
def Equation2082 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ x)
def Equation2083 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ y)
def Equation2084 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ z)
def Equation2085 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ w)
def Equation2095 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ x) ∘ (z ∘ z)
def Equation2096 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ x) ∘ (z ∘ w)
def Equation2105 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ y) ∘ (z ∘ z)
def Equation2106 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ y) ∘ (z ∘ w)
def Equation2109 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ (x ∘ z)
def Equation2110 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (x ∘ w)
def Equation2113 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ (y ∘ z)
def Equation2114 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (y ∘ w)
def Equation2115 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ (z ∘ x)
def Equation2116 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ (z ∘ y)
def Equation2117 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ (z ∘ z)
def Equation2118 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (z ∘ w)
def Equation2119 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (w ∘ x)
def Equation2120 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (w ∘ y)
def Equation2121 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (w ∘ z)
def Equation2122 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (w ∘ w)
def Equation2132 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ x) ∘ (z ∘ z)
def Equation2133 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ x) ∘ (z ∘ w)
def Equation2142 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ y) ∘ (z ∘ z)
def Equation2143 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ y) ∘ (z ∘ w)
def Equation2146 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ (x ∘ z)
def Equation2147 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (x ∘ w)
def Equation2150 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ (y ∘ z)
def Equation2151 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (y ∘ w)
def Equation2152 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ (z ∘ x)
def Equation2153 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ (z ∘ y)
def Equation2154 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ (z ∘ z)
def Equation2155 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (z ∘ w)
def Equation2156 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (w ∘ x)
def Equation2157 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (w ∘ y)
def Equation2158 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (w ∘ z)
def Equation2159 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (w ∘ w)
def Equation2163 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ (x ∘ z)
def Equation2164 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (x ∘ w)
def Equation2167 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ (y ∘ z)
def Equation2168 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (y ∘ w)
def Equation2169 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ (z ∘ x)
def Equation2170 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ (z ∘ y)
def Equation2171 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ (z ∘ z)
def Equation2172 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (z ∘ w)
def Equation2173 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ x)
def Equation2174 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ y)
def Equation2175 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ z)
def Equation2176 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ w)
def Equation2180 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ (x ∘ z)
def Equation2181 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (x ∘ w)
def Equation2184 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ (y ∘ z)
def Equation2185 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (y ∘ w)
def Equation2186 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ (z ∘ x)
def Equation2187 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ (z ∘ y)
def Equation2188 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ (z ∘ z)
def Equation2189 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (z ∘ w)
def Equation2190 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ x)
def Equation2191 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ y)
def Equation2192 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ z)
def Equation2193 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ w)
def Equation2195 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (x ∘ x)
def Equation2196 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (x ∘ y)
def Equation2197 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (x ∘ z)
def Equation2198 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (x ∘ w)
def Equation2199 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (y ∘ x)
def Equation2200 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (y ∘ y)
def Equation2201 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (y ∘ z)
def Equation2202 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (y ∘ w)
def Equation2203 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (z ∘ x)
def Equation2204 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (z ∘ y)
def Equation2205 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (z ∘ z)
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
def Equation2251 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ (y ∘ z))) ∘ z
def Equation2252 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (x ∘ (y ∘ z))) ∘ w
def Equation2261 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (x ∘ z))) ∘ z
def Equation2262 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (x ∘ z))) ∘ w
def Equation2271 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (y ∘ z))) ∘ z
def Equation2272 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (y ∘ z))) ∘ w
def Equation2275 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (z ∘ x))) ∘ z
def Equation2276 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ x))) ∘ w
def Equation2279 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (z ∘ y))) ∘ z
def Equation2280 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ y))) ∘ w
def Equation2281 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (z ∘ z))) ∘ x
def Equation2282 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (z ∘ z))) ∘ y
def Equation2283 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (z ∘ z))) ∘ z
def Equation2284 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ z))) ∘ w
def Equation2285 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ x
def Equation2286 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ y
def Equation2287 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ z
def Equation2288 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ w
def Equation2298 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (x ∘ z))) ∘ z
def Equation2299 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (x ∘ z))) ∘ w
def Equation2308 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (y ∘ z))) ∘ z
def Equation2309 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (y ∘ z))) ∘ w
def Equation2312 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (z ∘ x))) ∘ z
def Equation2313 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ x))) ∘ w
def Equation2316 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (z ∘ y))) ∘ z
def Equation2317 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ y))) ∘ w
def Equation2318 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (z ∘ z))) ∘ x
def Equation2319 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (z ∘ z))) ∘ y
def Equation2320 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (z ∘ z))) ∘ z
def Equation2321 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ z))) ∘ w
def Equation2322 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ w))) ∘ x
def Equation2323 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ w))) ∘ y
def Equation2324 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ w))) ∘ z
def Equation2325 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ w))) ∘ w
def Equation2335 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (x ∘ z))) ∘ z
def Equation2336 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (x ∘ z))) ∘ w
def Equation2345 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (y ∘ z))) ∘ z
def Equation2346 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (y ∘ z))) ∘ w
def Equation2349 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (z ∘ x))) ∘ z
def Equation2350 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ x))) ∘ w
def Equation2353 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (z ∘ y))) ∘ z
def Equation2354 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ y))) ∘ w
def Equation2355 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (z ∘ z))) ∘ x
def Equation2356 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (z ∘ z))) ∘ y
def Equation2357 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (z ∘ z))) ∘ z
def Equation2358 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ z))) ∘ w
def Equation2359 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ w))) ∘ x
def Equation2360 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ w))) ∘ y
def Equation2361 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ w))) ∘ z
def Equation2362 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ w))) ∘ w
def Equation2366 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (x ∘ x))) ∘ z
def Equation2367 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ x))) ∘ w
def Equation2370 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (x ∘ y))) ∘ z
def Equation2371 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ y))) ∘ w
def Equation2372 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (x ∘ z))) ∘ x
def Equation2373 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (x ∘ z))) ∘ y
def Equation2374 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (x ∘ z))) ∘ z
def Equation2375 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ z))) ∘ w
def Equation2376 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ x
def Equation2377 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ y
def Equation2378 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ z
def Equation2379 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ w
def Equation2383 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (y ∘ x))) ∘ z
def Equation2384 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ x))) ∘ w
def Equation2387 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (y ∘ y))) ∘ z
def Equation2388 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ y))) ∘ w
def Equation2389 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (y ∘ z))) ∘ x
def Equation2390 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (y ∘ z))) ∘ y
def Equation2391 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (y ∘ z))) ∘ z
def Equation2392 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ z))) ∘ w
def Equation2393 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ x
def Equation2394 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ y
def Equation2395 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ z
def Equation2396 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ w
def Equation2398 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ x))) ∘ x
def Equation2399 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ x))) ∘ y
def Equation2400 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ x))) ∘ z
def Equation2401 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ x))) ∘ w
def Equation2402 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ y))) ∘ x
def Equation2403 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ y))) ∘ y
def Equation2404 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ y))) ∘ z
def Equation2405 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ y))) ∘ w
def Equation2406 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ z))) ∘ x
def Equation2407 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ z))) ∘ y
def Equation2408 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ z))) ∘ z
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
def Equation2454 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((x ∘ y) ∘ z)) ∘ z
def Equation2455 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((x ∘ y) ∘ z)) ∘ w
def Equation2464 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ x) ∘ z)) ∘ z
def Equation2465 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ x) ∘ z)) ∘ w
def Equation2474 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ y) ∘ z)) ∘ z
def Equation2475 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ y) ∘ z)) ∘ w
def Equation2478 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ z) ∘ x)) ∘ z
def Equation2479 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ x)) ∘ w
def Equation2482 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ z) ∘ y)) ∘ z
def Equation2483 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ y)) ∘ w
def Equation2484 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ z) ∘ z)) ∘ x
def Equation2485 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ z) ∘ z)) ∘ y
def Equation2486 (G: Type*) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ z) ∘ z)) ∘ z
def Equation2487 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ z)) ∘ w
def Equation2488 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ x
def Equation2489 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ y
def Equation2490 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ z
def Equation2491 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ w
def Equation2501 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ x) ∘ z)) ∘ z
def Equation2502 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ x) ∘ z)) ∘ w
def Equation2511 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ y) ∘ z)) ∘ z
def Equation2512 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ y) ∘ z)) ∘ w
def Equation2515 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ z) ∘ x)) ∘ z
def Equation2516 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ x)) ∘ w
def Equation2519 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ z) ∘ y)) ∘ z
def Equation2520 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ y)) ∘ w
def Equation2521 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ z) ∘ z)) ∘ x
def Equation2522 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ z) ∘ z)) ∘ y
def Equation2523 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ z) ∘ z)) ∘ z
def Equation2524 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ z)) ∘ w
def Equation2525 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ w)) ∘ x
def Equation2526 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ w)) ∘ y
def Equation2527 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ w)) ∘ z
def Equation2528 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ w)) ∘ w
def Equation2538 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ x) ∘ z)) ∘ z
def Equation2539 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ x) ∘ z)) ∘ w
def Equation2548 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ y) ∘ z)) ∘ z
def Equation2549 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ y) ∘ z)) ∘ w
def Equation2552 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ z) ∘ x)) ∘ z
def Equation2553 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ x)) ∘ w
def Equation2556 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ z) ∘ y)) ∘ z
def Equation2557 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ y)) ∘ w
def Equation2558 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ z) ∘ z)) ∘ x
def Equation2559 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ z) ∘ z)) ∘ y
def Equation2560 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ z) ∘ z)) ∘ z
def Equation2561 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ z)) ∘ w
def Equation2562 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ w)) ∘ x
def Equation2563 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ w)) ∘ y
def Equation2564 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ w)) ∘ z
def Equation2565 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ w)) ∘ w
def Equation2569 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ x) ∘ x)) ∘ z
def Equation2570 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ x)) ∘ w
def Equation2573 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ x) ∘ y)) ∘ z
def Equation2574 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ y)) ∘ w
def Equation2575 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ x) ∘ z)) ∘ x
def Equation2576 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ x) ∘ z)) ∘ y
def Equation2577 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ x) ∘ z)) ∘ z
def Equation2578 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ z)) ∘ w
def Equation2579 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ x
def Equation2580 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ y
def Equation2581 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ z
def Equation2582 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ w
def Equation2586 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ y) ∘ x)) ∘ z
def Equation2587 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ x)) ∘ w
def Equation2590 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ y) ∘ y)) ∘ z
def Equation2591 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ y)) ∘ w
def Equation2592 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ y) ∘ z)) ∘ x
def Equation2593 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ y) ∘ z)) ∘ y
def Equation2594 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ y) ∘ z)) ∘ z
def Equation2595 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ z)) ∘ w
def Equation2596 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ x
def Equation2597 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ y
def Equation2598 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ z
def Equation2599 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ w
def Equation2601 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ x)) ∘ x
def Equation2602 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ x)) ∘ y
def Equation2603 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ x)) ∘ z
def Equation2604 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ x)) ∘ w
def Equation2605 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ y)) ∘ x
def Equation2606 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ y)) ∘ y
def Equation2607 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ y)) ∘ z
def Equation2608 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ y)) ∘ w
def Equation2609 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ z)) ∘ x
def Equation2610 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ z)) ∘ y
def Equation2611 (G: Type*) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ z)) ∘ z
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
def Equation2657 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ (y ∘ z)) ∘ z
def Equation2658 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ x) ∘ (y ∘ z)) ∘ w
def Equation2667 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (x ∘ z)) ∘ z
def Equation2668 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (x ∘ z)) ∘ w
def Equation2677 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (y ∘ z)) ∘ z
def Equation2678 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (y ∘ z)) ∘ w
def Equation2681 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (z ∘ x)) ∘ z
def Equation2682 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ x)) ∘ w
def Equation2685 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (z ∘ y)) ∘ z
def Equation2686 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ y)) ∘ w
def Equation2687 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (z ∘ z)) ∘ x
def Equation2688 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (z ∘ z)) ∘ y
def Equation2689 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (z ∘ z)) ∘ z
def Equation2690 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ z)) ∘ w
def Equation2691 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ x
def Equation2692 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ y
def Equation2693 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ z
def Equation2694 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ w
def Equation2704 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (x ∘ z)) ∘ z
def Equation2705 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (x ∘ z)) ∘ w
def Equation2714 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (y ∘ z)) ∘ z
def Equation2715 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (y ∘ z)) ∘ w
def Equation2718 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (z ∘ x)) ∘ z
def Equation2719 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ x)) ∘ w
def Equation2722 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (z ∘ y)) ∘ z
def Equation2723 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ y)) ∘ w
def Equation2724 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (z ∘ z)) ∘ x
def Equation2725 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (z ∘ z)) ∘ y
def Equation2726 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (z ∘ z)) ∘ z
def Equation2727 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ z)) ∘ w
def Equation2728 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ w)) ∘ x
def Equation2729 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ w)) ∘ y
def Equation2730 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ w)) ∘ z
def Equation2731 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ w)) ∘ w
def Equation2741 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (x ∘ z)) ∘ z
def Equation2742 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (x ∘ z)) ∘ w
def Equation2751 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (y ∘ z)) ∘ z
def Equation2752 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (y ∘ z)) ∘ w
def Equation2755 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (z ∘ x)) ∘ z
def Equation2756 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ x)) ∘ w
def Equation2759 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (z ∘ y)) ∘ z
def Equation2760 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ y)) ∘ w
def Equation2761 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (z ∘ z)) ∘ x
def Equation2762 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (z ∘ z)) ∘ y
def Equation2763 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (z ∘ z)) ∘ z
def Equation2764 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ z)) ∘ w
def Equation2765 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ w)) ∘ x
def Equation2766 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ w)) ∘ y
def Equation2767 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ w)) ∘ z
def Equation2768 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ w)) ∘ w
def Equation2772 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (x ∘ x)) ∘ z
def Equation2773 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ x)) ∘ w
def Equation2776 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (x ∘ y)) ∘ z
def Equation2777 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ y)) ∘ w
def Equation2778 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (x ∘ z)) ∘ x
def Equation2779 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (x ∘ z)) ∘ y
def Equation2780 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (x ∘ z)) ∘ z
def Equation2781 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ z)) ∘ w
def Equation2782 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ x
def Equation2783 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ y
def Equation2784 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ z
def Equation2785 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ w
def Equation2789 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (y ∘ x)) ∘ z
def Equation2790 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ x)) ∘ w
def Equation2793 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (y ∘ y)) ∘ z
def Equation2794 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ y)) ∘ w
def Equation2795 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (y ∘ z)) ∘ x
def Equation2796 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (y ∘ z)) ∘ y
def Equation2797 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (y ∘ z)) ∘ z
def Equation2798 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ z)) ∘ w
def Equation2799 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ x
def Equation2800 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ y
def Equation2801 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ z
def Equation2802 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ w
def Equation2804 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ x)) ∘ x
def Equation2805 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ x)) ∘ y
def Equation2806 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ x)) ∘ z
def Equation2807 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ x)) ∘ w
def Equation2808 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ y)) ∘ x
def Equation2809 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ y)) ∘ y
def Equation2810 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ y)) ∘ z
def Equation2811 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ y)) ∘ w
def Equation2812 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ z)) ∘ x
def Equation2813 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ z)) ∘ y
def Equation2814 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ z)) ∘ z
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
def Equation2860 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (x ∘ y)) ∘ z) ∘ z
def Equation2861 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (x ∘ y)) ∘ z) ∘ w
def Equation2870 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ x)) ∘ z) ∘ z
def Equation2871 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ x)) ∘ z) ∘ w
def Equation2880 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ y)) ∘ z) ∘ z
def Equation2881 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ y)) ∘ z) ∘ w
def Equation2884 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ z)) ∘ x) ∘ z
def Equation2885 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ x) ∘ w
def Equation2888 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ z)) ∘ y) ∘ z
def Equation2889 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ y) ∘ w
def Equation2890 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ z)) ∘ z) ∘ x
def Equation2891 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ z)) ∘ z) ∘ y
def Equation2892 (G: Type*) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ z)) ∘ z) ∘ z
def Equation2893 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ z) ∘ w
def Equation2894 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ x
def Equation2895 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ y
def Equation2896 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ z
def Equation2897 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ w
def Equation2907 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ x)) ∘ z) ∘ z
def Equation2908 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ x)) ∘ z) ∘ w
def Equation2917 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ y)) ∘ z) ∘ z
def Equation2918 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ y)) ∘ z) ∘ w
def Equation2921 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ z)) ∘ x) ∘ z
def Equation2922 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ x) ∘ w
def Equation2925 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ z)) ∘ y) ∘ z
def Equation2926 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ y) ∘ w
def Equation2927 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ z)) ∘ z) ∘ x
def Equation2928 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ z)) ∘ z) ∘ y
def Equation2929 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ z)) ∘ z) ∘ z
def Equation2930 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ z) ∘ w
def Equation2931 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ w) ∘ x
def Equation2932 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ w) ∘ y
def Equation2933 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ w) ∘ z
def Equation2934 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ w) ∘ w
def Equation2944 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ x)) ∘ z) ∘ z
def Equation2945 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ x)) ∘ z) ∘ w
def Equation2954 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ y)) ∘ z) ∘ z
def Equation2955 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ y)) ∘ z) ∘ w
def Equation2958 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ z)) ∘ x) ∘ z
def Equation2959 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ x) ∘ w
def Equation2962 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ z)) ∘ y) ∘ z
def Equation2963 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ y) ∘ w
def Equation2964 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ z)) ∘ z) ∘ x
def Equation2965 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ z)) ∘ z) ∘ y
def Equation2966 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ z)) ∘ z) ∘ z
def Equation2967 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ z) ∘ w
def Equation2968 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ w) ∘ x
def Equation2969 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ w) ∘ y
def Equation2970 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ w) ∘ z
def Equation2971 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ w) ∘ w
def Equation2975 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ x)) ∘ x) ∘ z
def Equation2976 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ x) ∘ w
def Equation2979 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ x)) ∘ y) ∘ z
def Equation2980 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ y) ∘ w
def Equation2981 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ x)) ∘ z) ∘ x
def Equation2982 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ x)) ∘ z) ∘ y
def Equation2983 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ x)) ∘ z) ∘ z
def Equation2984 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ z) ∘ w
def Equation2985 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ x
def Equation2986 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ y
def Equation2987 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ z
def Equation2988 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ w
def Equation2992 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ y)) ∘ x) ∘ z
def Equation2993 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ x) ∘ w
def Equation2996 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ y)) ∘ y) ∘ z
def Equation2997 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ y) ∘ w
def Equation2998 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ y)) ∘ z) ∘ x
def Equation2999 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ y)) ∘ z) ∘ y
def Equation3000 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ y)) ∘ z) ∘ z
def Equation3001 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ z) ∘ w
def Equation3002 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ x
def Equation3003 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ y
def Equation3004 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ z
def Equation3005 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ w
def Equation3007 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ x) ∘ x
def Equation3008 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ x) ∘ y
def Equation3009 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ x) ∘ z
def Equation3010 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ x) ∘ w
def Equation3011 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ y) ∘ x
def Equation3012 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ y) ∘ y
def Equation3013 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ y) ∘ z
def Equation3014 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ y) ∘ w
def Equation3015 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ z) ∘ x
def Equation3016 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ z) ∘ y
def Equation3017 (G: Type*) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ z) ∘ z
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
def Equation3063 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ x) ∘ y) ∘ z) ∘ z
def Equation3064 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ x) ∘ y) ∘ z) ∘ w
def Equation3073 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ x) ∘ z) ∘ z
def Equation3074 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ x) ∘ z) ∘ w
def Equation3083 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ y) ∘ z) ∘ z
def Equation3084 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ y) ∘ z) ∘ w
def Equation3087 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ z) ∘ x) ∘ z
def Equation3088 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ x) ∘ w
def Equation3091 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ z) ∘ y) ∘ z
def Equation3092 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ y) ∘ w
def Equation3093 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ z) ∘ z) ∘ x
def Equation3094 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ z) ∘ z) ∘ y
def Equation3095 (G: Type*) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ z) ∘ z) ∘ z
def Equation3096 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ z) ∘ w
def Equation3097 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ x
def Equation3098 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ y
def Equation3099 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ z
def Equation3100 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ w
def Equation3110 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ x) ∘ z) ∘ z
def Equation3111 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ x) ∘ z) ∘ w
def Equation3120 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ y) ∘ z) ∘ z
def Equation3121 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ y) ∘ z) ∘ w
def Equation3124 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ z) ∘ x) ∘ z
def Equation3125 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ x) ∘ w
def Equation3128 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ z) ∘ y) ∘ z
def Equation3129 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ y) ∘ w
def Equation3130 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ z) ∘ z) ∘ x
def Equation3131 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ z) ∘ z) ∘ y
def Equation3132 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ z) ∘ z) ∘ z
def Equation3133 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ z) ∘ w
def Equation3134 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ w) ∘ x
def Equation3135 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ w) ∘ y
def Equation3136 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ w) ∘ z
def Equation3137 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ w) ∘ w
def Equation3147 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ x) ∘ z) ∘ z
def Equation3148 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ x) ∘ z) ∘ w
def Equation3157 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ y) ∘ z) ∘ z
def Equation3158 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ y) ∘ z) ∘ w
def Equation3161 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ z) ∘ x) ∘ z
def Equation3162 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ x) ∘ w
def Equation3165 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ z) ∘ y) ∘ z
def Equation3166 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ y) ∘ w
def Equation3167 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ z) ∘ z) ∘ x
def Equation3168 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ z) ∘ z) ∘ y
def Equation3169 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ z) ∘ z) ∘ z
def Equation3170 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ z) ∘ w
def Equation3171 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ w) ∘ x
def Equation3172 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ w) ∘ y
def Equation3173 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ w) ∘ z
def Equation3174 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ w) ∘ w
def Equation3178 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ x) ∘ x) ∘ z
def Equation3179 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ x) ∘ w
def Equation3182 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ x) ∘ y) ∘ z
def Equation3183 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ y) ∘ w
def Equation3184 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ x) ∘ z) ∘ x
def Equation3185 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ x) ∘ z) ∘ y
def Equation3186 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ x) ∘ z) ∘ z
def Equation3187 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ z) ∘ w
def Equation3188 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ x
def Equation3189 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ y
def Equation3190 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ z
def Equation3191 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ w
def Equation3195 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ y) ∘ x) ∘ z
def Equation3196 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ x) ∘ w
def Equation3199 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ y) ∘ y) ∘ z
def Equation3200 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ y) ∘ w
def Equation3201 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ y) ∘ z) ∘ x
def Equation3202 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ y) ∘ z) ∘ y
def Equation3203 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ y) ∘ z) ∘ z
def Equation3204 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ z) ∘ w
def Equation3205 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ x
def Equation3206 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ y
def Equation3207 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ z
def Equation3208 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ w
def Equation3210 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ x) ∘ x
def Equation3211 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ x) ∘ y
def Equation3212 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ x) ∘ z
def Equation3213 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ x) ∘ w
def Equation3214 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ y) ∘ x
def Equation3215 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ y) ∘ y
def Equation3216 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ y) ∘ z
def Equation3217 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ y) ∘ w
def Equation3218 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ z) ∘ x
def Equation3219 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ z) ∘ y
def Equation3220 (G: Type*) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ z) ∘ z
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
def Equation3266 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ (y ∘ (z ∘ z))
def Equation3267 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = x ∘ (y ∘ (z ∘ w))
def Equation3276 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (x ∘ (z ∘ z))
def Equation3277 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (x ∘ (z ∘ w))
def Equation3286 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (y ∘ (z ∘ z))
def Equation3287 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (y ∘ (z ∘ w))
def Equation3290 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ (x ∘ z))
def Equation3291 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (x ∘ w))
def Equation3294 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ (y ∘ z))
def Equation3295 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (y ∘ w))
def Equation3296 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ (z ∘ x))
def Equation3297 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ (z ∘ y))
def Equation3298 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ (z ∘ z))
def Equation3299 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (z ∘ w))
def Equation3300 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (w ∘ x))
def Equation3301 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (w ∘ y))
def Equation3302 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (w ∘ z))
def Equation3303 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (w ∘ w))
def Equation3313 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (x ∘ (z ∘ z))
def Equation3314 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (x ∘ (z ∘ w))
def Equation3323 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (y ∘ (z ∘ z))
def Equation3324 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (y ∘ (z ∘ w))
def Equation3327 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ (x ∘ z))
def Equation3328 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (x ∘ w))
def Equation3331 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ (y ∘ z))
def Equation3332 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (y ∘ w))
def Equation3333 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ (z ∘ x))
def Equation3334 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ (z ∘ y))
def Equation3335 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ (z ∘ z))
def Equation3336 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (z ∘ w))
def Equation3337 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (w ∘ x))
def Equation3338 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (w ∘ y))
def Equation3339 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (w ∘ z))
def Equation3340 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (w ∘ w))
def Equation3350 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (x ∘ (z ∘ z))
def Equation3351 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (x ∘ (z ∘ w))
def Equation3360 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (y ∘ (z ∘ z))
def Equation3361 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (y ∘ (z ∘ w))
def Equation3364 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ (x ∘ z))
def Equation3365 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (x ∘ w))
def Equation3368 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ (y ∘ z))
def Equation3369 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (y ∘ w))
def Equation3370 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ (z ∘ x))
def Equation3371 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ (z ∘ y))
def Equation3372 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ (z ∘ z))
def Equation3373 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (z ∘ w))
def Equation3374 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (w ∘ x))
def Equation3375 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (w ∘ y))
def Equation3376 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (w ∘ z))
def Equation3377 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (w ∘ w))
def Equation3381 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ (x ∘ z))
def Equation3382 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (x ∘ w))
def Equation3385 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ (y ∘ z))
def Equation3386 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (y ∘ w))
def Equation3387 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ (z ∘ x))
def Equation3388 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ (z ∘ y))
def Equation3389 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ (z ∘ z))
def Equation3390 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (z ∘ w))
def Equation3391 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (w ∘ x))
def Equation3392 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (w ∘ y))
def Equation3393 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (w ∘ z))
def Equation3394 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (w ∘ w))
def Equation3398 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ (x ∘ z))
def Equation3399 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (x ∘ w))
def Equation3402 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ (y ∘ z))
def Equation3403 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (y ∘ w))
def Equation3404 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ (z ∘ x))
def Equation3405 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ (z ∘ y))
def Equation3406 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ (z ∘ z))
def Equation3407 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (z ∘ w))
def Equation3408 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (w ∘ x))
def Equation3409 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (w ∘ y))
def Equation3410 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (w ∘ z))
def Equation3411 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (w ∘ w))
def Equation3413 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (x ∘ x))
def Equation3414 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (x ∘ y))
def Equation3415 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (x ∘ z))
def Equation3416 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (x ∘ w))
def Equation3417 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (y ∘ x))
def Equation3418 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (y ∘ y))
def Equation3419 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (y ∘ z))
def Equation3420 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (y ∘ w))
def Equation3421 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (z ∘ x))
def Equation3422 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (z ∘ y))
def Equation3423 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (z ∘ z))
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
def Equation3469 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ ((y ∘ z) ∘ z)
def Equation3470 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = x ∘ ((y ∘ z) ∘ w)
def Equation3479 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((x ∘ z) ∘ z)
def Equation3480 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((x ∘ z) ∘ w)
def Equation3489 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((y ∘ z) ∘ z)
def Equation3490 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((y ∘ z) ∘ w)
def Equation3493 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((z ∘ x) ∘ z)
def Equation3494 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ x) ∘ w)
def Equation3497 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((z ∘ y) ∘ z)
def Equation3498 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ y) ∘ w)
def Equation3499 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((z ∘ z) ∘ x)
def Equation3500 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((z ∘ z) ∘ y)
def Equation3501 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((z ∘ z) ∘ z)
def Equation3502 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ z) ∘ w)
def Equation3503 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ w) ∘ x)
def Equation3504 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ w) ∘ y)
def Equation3505 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ w) ∘ z)
def Equation3506 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ w) ∘ w)
def Equation3516 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((x ∘ z) ∘ z)
def Equation3517 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((x ∘ z) ∘ w)
def Equation3526 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((y ∘ z) ∘ z)
def Equation3527 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((y ∘ z) ∘ w)
def Equation3530 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((z ∘ x) ∘ z)
def Equation3531 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ x) ∘ w)
def Equation3534 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((z ∘ y) ∘ z)
def Equation3535 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ y) ∘ w)
def Equation3536 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((z ∘ z) ∘ x)
def Equation3537 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((z ∘ z) ∘ y)
def Equation3538 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((z ∘ z) ∘ z)
def Equation3539 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ z) ∘ w)
def Equation3540 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ w) ∘ x)
def Equation3541 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ w) ∘ y)
def Equation3542 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ w) ∘ z)
def Equation3543 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ w) ∘ w)
def Equation3553 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((x ∘ z) ∘ z)
def Equation3554 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((x ∘ z) ∘ w)
def Equation3563 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((y ∘ z) ∘ z)
def Equation3564 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((y ∘ z) ∘ w)
def Equation3567 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((z ∘ x) ∘ z)
def Equation3568 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ x) ∘ w)
def Equation3571 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((z ∘ y) ∘ z)
def Equation3572 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ y) ∘ w)
def Equation3573 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((z ∘ z) ∘ x)
def Equation3574 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((z ∘ z) ∘ y)
def Equation3575 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((z ∘ z) ∘ z)
def Equation3576 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ z) ∘ w)
def Equation3577 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ w) ∘ x)
def Equation3578 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ w) ∘ y)
def Equation3579 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ w) ∘ z)
def Equation3580 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ w) ∘ w)
def Equation3584 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((x ∘ x) ∘ z)
def Equation3585 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ x) ∘ w)
def Equation3588 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((x ∘ y) ∘ z)
def Equation3589 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ y) ∘ w)
def Equation3590 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((x ∘ z) ∘ x)
def Equation3591 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((x ∘ z) ∘ y)
def Equation3592 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((x ∘ z) ∘ z)
def Equation3593 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ z) ∘ w)
def Equation3594 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ w) ∘ x)
def Equation3595 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ w) ∘ y)
def Equation3596 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ w) ∘ z)
def Equation3597 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ w) ∘ w)
def Equation3601 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((y ∘ x) ∘ z)
def Equation3602 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ x) ∘ w)
def Equation3605 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((y ∘ y) ∘ z)
def Equation3606 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ y) ∘ w)
def Equation3607 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((y ∘ z) ∘ x)
def Equation3608 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((y ∘ z) ∘ y)
def Equation3609 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((y ∘ z) ∘ z)
def Equation3610 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ z) ∘ w)
def Equation3611 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ w) ∘ x)
def Equation3612 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ w) ∘ y)
def Equation3613 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ w) ∘ z)
def Equation3614 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ w) ∘ w)
def Equation3616 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ x) ∘ x)
def Equation3617 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ x) ∘ y)
def Equation3618 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ x) ∘ z)
def Equation3619 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ x) ∘ w)
def Equation3620 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ y) ∘ x)
def Equation3621 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ y) ∘ y)
def Equation3622 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ y) ∘ z)
def Equation3623 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ y) ∘ w)
def Equation3624 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ z) ∘ x)
def Equation3625 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ z) ∘ y)
def Equation3626 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ z) ∘ z)
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
def Equation3672 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ y) ∘ (z ∘ z)
def Equation3673 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (x ∘ y) ∘ (z ∘ w)
def Equation3682 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ x) ∘ (z ∘ z)
def Equation3683 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ x) ∘ (z ∘ w)
def Equation3692 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ y) ∘ (z ∘ z)
def Equation3693 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ y) ∘ (z ∘ w)
def Equation3696 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ (x ∘ z)
def Equation3697 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (x ∘ w)
def Equation3700 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ (y ∘ z)
def Equation3701 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (y ∘ w)
def Equation3702 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ (z ∘ x)
def Equation3703 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ (z ∘ y)
def Equation3704 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ (z ∘ z)
def Equation3705 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (z ∘ w)
def Equation3706 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (w ∘ x)
def Equation3707 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (w ∘ y)
def Equation3708 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (w ∘ z)
def Equation3709 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (w ∘ w)
def Equation3719 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ x) ∘ (z ∘ z)
def Equation3720 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ x) ∘ (z ∘ w)
def Equation3729 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ y) ∘ (z ∘ z)
def Equation3730 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ y) ∘ (z ∘ w)
def Equation3733 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ (x ∘ z)
def Equation3734 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (x ∘ w)
def Equation3737 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ (y ∘ z)
def Equation3738 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (y ∘ w)
def Equation3739 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ (z ∘ x)
def Equation3740 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ (z ∘ y)
def Equation3741 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ (z ∘ z)
def Equation3742 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (z ∘ w)
def Equation3743 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (w ∘ x)
def Equation3744 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (w ∘ y)
def Equation3745 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (w ∘ z)
def Equation3746 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (w ∘ w)
def Equation3756 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ x) ∘ (z ∘ z)
def Equation3757 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ x) ∘ (z ∘ w)
def Equation3766 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ y) ∘ (z ∘ z)
def Equation3767 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ y) ∘ (z ∘ w)
def Equation3770 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ (x ∘ z)
def Equation3771 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (x ∘ w)
def Equation3774 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ (y ∘ z)
def Equation3775 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (y ∘ w)
def Equation3776 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ (z ∘ x)
def Equation3777 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ (z ∘ y)
def Equation3778 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ (z ∘ z)
def Equation3779 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (z ∘ w)
def Equation3780 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (w ∘ x)
def Equation3781 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (w ∘ y)
def Equation3782 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (w ∘ z)
def Equation3783 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (w ∘ w)
def Equation3787 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ (x ∘ z)
def Equation3788 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (x ∘ w)
def Equation3791 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ (y ∘ z)
def Equation3792 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (y ∘ w)
def Equation3793 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ (z ∘ x)
def Equation3794 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ (z ∘ y)
def Equation3795 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ (z ∘ z)
def Equation3796 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (z ∘ w)
def Equation3797 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (w ∘ x)
def Equation3798 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (w ∘ y)
def Equation3799 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (w ∘ z)
def Equation3800 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (w ∘ w)
def Equation3804 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ (x ∘ z)
def Equation3805 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (x ∘ w)
def Equation3808 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ (y ∘ z)
def Equation3809 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (y ∘ w)
def Equation3810 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ (z ∘ x)
def Equation3811 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ (z ∘ y)
def Equation3812 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ (z ∘ z)
def Equation3813 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (z ∘ w)
def Equation3814 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (w ∘ x)
def Equation3815 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (w ∘ y)
def Equation3816 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (w ∘ z)
def Equation3817 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (w ∘ w)
def Equation3819 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (x ∘ x)
def Equation3820 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (x ∘ y)
def Equation3821 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (x ∘ z)
def Equation3822 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (x ∘ w)
def Equation3823 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (y ∘ x)
def Equation3824 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (y ∘ y)
def Equation3825 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (y ∘ z)
def Equation3826 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (y ∘ w)
def Equation3827 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (z ∘ x)
def Equation3828 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (z ∘ y)
def Equation3829 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (z ∘ z)
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
def Equation3875 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ (y ∘ z)) ∘ z
def Equation3876 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (x ∘ (y ∘ z)) ∘ w
def Equation3885 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (x ∘ z)) ∘ z
def Equation3886 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (x ∘ z)) ∘ w
def Equation3895 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (y ∘ z)) ∘ z
def Equation3896 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (y ∘ z)) ∘ w
def Equation3899 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (z ∘ x)) ∘ z
def Equation3900 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ x)) ∘ w
def Equation3903 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (z ∘ y)) ∘ z
def Equation3904 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ y)) ∘ w
def Equation3905 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (z ∘ z)) ∘ x
def Equation3906 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (z ∘ z)) ∘ y
def Equation3907 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (z ∘ z)) ∘ z
def Equation3908 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ z)) ∘ w
def Equation3909 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ w)) ∘ x
def Equation3910 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ w)) ∘ y
def Equation3911 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ w)) ∘ z
def Equation3912 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ w)) ∘ w
def Equation3922 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (x ∘ z)) ∘ z
def Equation3923 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (x ∘ z)) ∘ w
def Equation3932 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (y ∘ z)) ∘ z
def Equation3933 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (y ∘ z)) ∘ w
def Equation3936 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (z ∘ x)) ∘ z
def Equation3937 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ x)) ∘ w
def Equation3940 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (z ∘ y)) ∘ z
def Equation3941 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ y)) ∘ w
def Equation3942 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (z ∘ z)) ∘ x
def Equation3943 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (z ∘ z)) ∘ y
def Equation3944 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (z ∘ z)) ∘ z
def Equation3945 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ z)) ∘ w
def Equation3946 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ w)) ∘ x
def Equation3947 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ w)) ∘ y
def Equation3948 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ w)) ∘ z
def Equation3949 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ w)) ∘ w
def Equation3959 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (x ∘ z)) ∘ z
def Equation3960 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (x ∘ z)) ∘ w
def Equation3969 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (y ∘ z)) ∘ z
def Equation3970 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (y ∘ z)) ∘ w
def Equation3973 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (z ∘ x)) ∘ z
def Equation3974 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ x)) ∘ w
def Equation3977 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (z ∘ y)) ∘ z
def Equation3978 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ y)) ∘ w
def Equation3979 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (z ∘ z)) ∘ x
def Equation3980 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (z ∘ z)) ∘ y
def Equation3981 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (z ∘ z)) ∘ z
def Equation3982 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ z)) ∘ w
def Equation3983 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ w)) ∘ x
def Equation3984 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ w)) ∘ y
def Equation3985 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ w)) ∘ z
def Equation3986 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ w)) ∘ w
def Equation3990 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (x ∘ x)) ∘ z
def Equation3991 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ x)) ∘ w
def Equation3994 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (x ∘ y)) ∘ z
def Equation3995 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ y)) ∘ w
def Equation3996 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (x ∘ z)) ∘ x
def Equation3997 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (x ∘ z)) ∘ y
def Equation3998 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (x ∘ z)) ∘ z
def Equation3999 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ z)) ∘ w
def Equation4000 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ w)) ∘ x
def Equation4001 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ w)) ∘ y
def Equation4002 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ w)) ∘ z
def Equation4003 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ w)) ∘ w
def Equation4007 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (y ∘ x)) ∘ z
def Equation4008 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ x)) ∘ w
def Equation4011 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (y ∘ y)) ∘ z
def Equation4012 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ y)) ∘ w
def Equation4013 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (y ∘ z)) ∘ x
def Equation4014 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (y ∘ z)) ∘ y
def Equation4015 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (y ∘ z)) ∘ z
def Equation4016 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ z)) ∘ w
def Equation4017 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ w)) ∘ x
def Equation4018 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ w)) ∘ y
def Equation4019 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ w)) ∘ z
def Equation4020 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ w)) ∘ w
def Equation4022 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ x)) ∘ x
def Equation4023 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ x)) ∘ y
def Equation4024 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ x)) ∘ z
def Equation4025 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ x)) ∘ w
def Equation4026 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ y)) ∘ x
def Equation4027 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ y)) ∘ y
def Equation4028 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ y)) ∘ z
def Equation4029 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ y)) ∘ w
def Equation4030 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ z)) ∘ x
def Equation4031 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ z)) ∘ y
def Equation4032 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ z)) ∘ z
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
def Equation4078 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((x ∘ y) ∘ z) ∘ z
def Equation4079 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((x ∘ y) ∘ z) ∘ w
def Equation4088 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ x) ∘ z) ∘ z
def Equation4089 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ x) ∘ z) ∘ w
def Equation4098 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ y) ∘ z) ∘ z
def Equation4099 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ y) ∘ z) ∘ w
def Equation4102 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ z) ∘ x) ∘ z
def Equation4103 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ x) ∘ w
def Equation4106 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ z) ∘ y) ∘ z
def Equation4107 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ y) ∘ w
def Equation4108 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ z) ∘ z) ∘ x
def Equation4109 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ z) ∘ z) ∘ y
def Equation4110 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ z) ∘ z) ∘ z
def Equation4111 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ z) ∘ w
def Equation4112 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ w) ∘ x
def Equation4113 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ w) ∘ y
def Equation4114 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ w) ∘ z
def Equation4115 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ w) ∘ w
def Equation4125 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ x) ∘ z) ∘ z
def Equation4126 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ x) ∘ z) ∘ w
def Equation4135 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ y) ∘ z) ∘ z
def Equation4136 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ y) ∘ z) ∘ w
def Equation4139 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ z) ∘ x) ∘ z
def Equation4140 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ x) ∘ w
def Equation4143 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ z) ∘ y) ∘ z
def Equation4144 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ y) ∘ w
def Equation4145 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ z) ∘ z) ∘ x
def Equation4146 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ z) ∘ z) ∘ y
def Equation4147 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ z) ∘ z) ∘ z
def Equation4148 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ z) ∘ w
def Equation4149 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ w) ∘ x
def Equation4150 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ w) ∘ y
def Equation4151 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ w) ∘ z
def Equation4152 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ w) ∘ w
def Equation4162 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ x) ∘ z) ∘ z
def Equation4163 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ x) ∘ z) ∘ w
def Equation4172 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ y) ∘ z) ∘ z
def Equation4173 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ y) ∘ z) ∘ w
def Equation4176 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ z) ∘ x) ∘ z
def Equation4177 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ x) ∘ w
def Equation4180 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ z) ∘ y) ∘ z
def Equation4181 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ y) ∘ w
def Equation4182 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ z) ∘ z) ∘ x
def Equation4183 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ z) ∘ z) ∘ y
def Equation4184 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ z) ∘ z) ∘ z
def Equation4185 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ z) ∘ w
def Equation4186 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ w) ∘ x
def Equation4187 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ w) ∘ y
def Equation4188 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ w) ∘ z
def Equation4189 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ w) ∘ w
def Equation4193 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ x) ∘ x) ∘ z
def Equation4194 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ x) ∘ w
def Equation4197 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ x) ∘ y) ∘ z
def Equation4198 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ y) ∘ w
def Equation4199 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ x) ∘ z) ∘ x
def Equation4200 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ x) ∘ z) ∘ y
def Equation4201 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ x) ∘ z) ∘ z
def Equation4202 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ z) ∘ w
def Equation4203 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ w) ∘ x
def Equation4204 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ w) ∘ y
def Equation4205 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ w) ∘ z
def Equation4206 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ w) ∘ w
def Equation4210 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ y) ∘ x) ∘ z
def Equation4211 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ x) ∘ w
def Equation4214 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ y) ∘ y) ∘ z
def Equation4215 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ y) ∘ w
def Equation4216 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ y) ∘ z) ∘ x
def Equation4217 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ y) ∘ z) ∘ y
def Equation4218 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ y) ∘ z) ∘ z
def Equation4219 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ z) ∘ w
def Equation4220 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ w) ∘ x
def Equation4221 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ w) ∘ y
def Equation4222 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ w) ∘ z
def Equation4223 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ w) ∘ w
def Equation4225 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ x) ∘ x
def Equation4226 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ x) ∘ y
def Equation4227 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ x) ∘ z
def Equation4228 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ x) ∘ w
def Equation4229 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ y) ∘ x
def Equation4230 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ y) ∘ y
def Equation4231 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ y) ∘ z
def Equation4232 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ y) ∘ w
def Equation4233 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ z) ∘ x
def Equation4234 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ z) ∘ y
def Equation4235 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ z) ∘ z
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
def Equation4280 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ x) = y ∘ (z ∘ z)
def Equation4281 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ x) = y ∘ (z ∘ w)
def Equation4288 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = x ∘ (z ∘ z)
def Equation4289 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = x ∘ (z ∘ w)
def Equation4297 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = y ∘ (z ∘ z)
def Equation4298 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = y ∘ (z ∘ w)
def Equation4301 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = z ∘ (x ∘ z)
def Equation4302 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (x ∘ w)
def Equation4305 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = z ∘ (y ∘ z)
def Equation4306 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (y ∘ w)
def Equation4307 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = z ∘ (z ∘ y)
def Equation4310 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (w ∘ y)
def Equation4318 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = x ∘ (z ∘ z)
def Equation4319 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = x ∘ (z ∘ w)
def Equation4325 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = y ∘ (z ∘ z)
def Equation4326 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = y ∘ (z ∘ w)
def Equation4332 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = z ∘ (y ∘ z)
def Equation4333 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = z ∘ (y ∘ w)
def Equation4341 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = x ∘ (z ∘ z)
def Equation4342 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = x ∘ (z ∘ w)
def Equation4346 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = y ∘ (z ∘ z)
def Equation4347 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = y ∘ (z ∘ w)
def Equation4362 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = y ∘ (x ∘ z)
def Equation4363 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = y ∘ (x ∘ w)
def Equation4364 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = y ∘ (z ∘ x)
def Equation4366 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = y ∘ (w ∘ x)
def Equation4393 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ x) = (y ∘ z) ∘ z
def Equation4394 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ x) = (y ∘ z) ∘ w
def Equation4403 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (x ∘ z) ∘ z
def Equation4404 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (x ∘ z) ∘ w
def Equation4413 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (y ∘ z) ∘ z
def Equation4414 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (y ∘ z) ∘ w
def Equation4417 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (z ∘ x) ∘ z
def Equation4418 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ x) ∘ w
def Equation4421 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (z ∘ y) ∘ z
def Equation4422 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ y) ∘ w
def Equation4423 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (z ∘ z) ∘ x
def Equation4424 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (z ∘ z) ∘ y
def Equation4425 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (z ∘ z) ∘ z
def Equation4426 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ z) ∘ w
def Equation4427 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ w) ∘ x
def Equation4428 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ w) ∘ y
def Equation4429 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ w) ∘ z
def Equation4430 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ w) ∘ w
def Equation4440 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (x ∘ z) ∘ z
def Equation4441 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (x ∘ z) ∘ w
def Equation4450 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (y ∘ z) ∘ z
def Equation4451 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (y ∘ z) ∘ w
def Equation4454 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (z ∘ x) ∘ z
def Equation4455 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ x) ∘ w
def Equation4458 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (z ∘ y) ∘ z
def Equation4459 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ y) ∘ w
def Equation4460 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (z ∘ z) ∘ x
def Equation4461 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (z ∘ z) ∘ y
def Equation4462 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (z ∘ z) ∘ z
def Equation4463 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ z) ∘ w
def Equation4464 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ w) ∘ x
def Equation4465 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ w) ∘ y
def Equation4466 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ w) ∘ z
def Equation4467 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ w) ∘ w
def Equation4477 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (x ∘ z) ∘ z
def Equation4478 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (x ∘ z) ∘ w
def Equation4487 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (y ∘ z) ∘ z
def Equation4488 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (y ∘ z) ∘ w
def Equation4491 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (z ∘ x) ∘ z
def Equation4492 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ x) ∘ w
def Equation4495 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (z ∘ y) ∘ z
def Equation4496 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ y) ∘ w
def Equation4497 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (z ∘ z) ∘ x
def Equation4498 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (z ∘ z) ∘ y
def Equation4499 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (z ∘ z) ∘ z
def Equation4500 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ z) ∘ w
def Equation4501 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ w) ∘ x
def Equation4502 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ w) ∘ y
def Equation4503 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ w) ∘ z
def Equation4504 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ w) ∘ w
def Equation4508 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ x) ∘ z
def Equation4509 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ x) ∘ w
def Equation4512 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ y) ∘ z
def Equation4513 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ y) ∘ w
def Equation4514 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ z) ∘ x
def Equation4515 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ z) ∘ y
def Equation4516 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ z) ∘ z
def Equation4517 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ z) ∘ w
def Equation4518 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ w) ∘ x
def Equation4519 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ w) ∘ y
def Equation4520 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ w) ∘ z
def Equation4521 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ w) ∘ w
def Equation4525 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (y ∘ x) ∘ z
def Equation4526 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ x) ∘ w
def Equation4529 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (y ∘ y) ∘ z
def Equation4530 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ y) ∘ w
def Equation4531 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (y ∘ z) ∘ x
def Equation4532 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (y ∘ z) ∘ y
def Equation4533 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (y ∘ z) ∘ z
def Equation4534 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ z) ∘ w
def Equation4535 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ w) ∘ x
def Equation4536 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ w) ∘ y
def Equation4537 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ w) ∘ z
def Equation4538 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ w) ∘ w
def Equation4540 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ x) ∘ x
def Equation4541 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ x) ∘ y
def Equation4542 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ x) ∘ z
def Equation4543 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ x) ∘ w
def Equation4544 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ y) ∘ x
def Equation4545 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ y) ∘ y
def Equation4546 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ y) ∘ z
def Equation4547 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ y) ∘ w
def Equation4548 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ z) ∘ x
def Equation4549 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ z) ∘ y
def Equation4550 (G: Type*) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ z) ∘ z
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
def Equation4595 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ x = (y ∘ z) ∘ z
def Equation4596 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ x = (y ∘ z) ∘ w
def Equation4603 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (x ∘ z) ∘ z
def Equation4604 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (x ∘ z) ∘ w
def Equation4612 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (y ∘ z) ∘ z
def Equation4613 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (y ∘ z) ∘ w
def Equation4616 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (z ∘ x) ∘ z
def Equation4617 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ x) ∘ w
def Equation4620 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (z ∘ y) ∘ z
def Equation4621 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ y) ∘ w
def Equation4622 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (z ∘ z) ∘ y
def Equation4625 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ w) ∘ y
def Equation4633 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (x ∘ z) ∘ z
def Equation4634 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ x = (x ∘ z) ∘ w
def Equation4640 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (y ∘ z) ∘ z
def Equation4641 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ x = (y ∘ z) ∘ w
def Equation4647 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (z ∘ y) ∘ z
def Equation4648 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ x = (z ∘ y) ∘ w
def Equation4656 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ y = (x ∘ z) ∘ z
def Equation4657 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ y = (x ∘ z) ∘ w
def Equation4661 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ y = (y ∘ z) ∘ z
def Equation4662 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ y = (y ∘ z) ∘ w
def Equation4677 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ z = (y ∘ x) ∘ z
def Equation4678 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (y ∘ x) ∘ w
def Equation4679 (G: Type*) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ z = (y ∘ z) ∘ x
def Equation4681 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (y ∘ w) ∘ x
theorem Equation22_implies_Equation21 (G : Type*) [Magma G] (h : Equation22 G) : Equation21 G := λ x y z => h x y z z
theorem Equation37_implies_Equation36 (G : Type*) [Magma G] (h : Equation37 G) : Equation36 G := λ x y z => h x y z z
theorem Equation61_implies_Equation60 (G : Type*) [Magma G] (h : Equation61 G) : Equation60 G := λ x y z => h x y z z
theorem Equation71_implies_Equation70 (G : Type*) [Magma G] (h : Equation71 G) : Equation70 G := λ x y z => h x y z z
theorem Equation81_implies_Equation80 (G : Type*) [Magma G] (h : Equation81 G) : Equation80 G := λ x y z => h x y z z
theorem Equation85_implies_Equation84 (G : Type*) [Magma G] (h : Equation85 G) : Equation84 G := λ x y z => h x y z z
theorem Equation89_implies_Equation88 (G : Type*) [Magma G] (h : Equation89 G) : Equation88 G := λ x y z => h x y z z
theorem Equation93_implies_Equation92 (G : Type*) [Magma G] (h : Equation93 G) : Equation92 G := λ x y z => h x y z z
theorem Equation94_implies_Equation90 (G : Type*) [Magma G] (h : Equation94 G) : Equation90 G := λ x y z => h x y z z
theorem Equation95_implies_Equation91 (G : Type*) [Magma G] (h : Equation95 G) : Equation91 G := λ x y z => h x y z z
theorem Equation96_implies_Equation92 (G : Type*) [Magma G] (h : Equation96 G) : Equation92 G := λ x y z => h x y z z
theorem Equation97_implies_Equation92 (G : Type*) [Magma G] (h : Equation97 G) : Equation92 G := λ x y z => h x y z z
theorem Equation113_implies_Equation112 (G : Type*) [Magma G] (h : Equation113 G) : Equation112 G := λ x y z => h x y z z
theorem Equation123_implies_Equation122 (G : Type*) [Magma G] (h : Equation123 G) : Equation122 G := λ x y z => h x y z z
theorem Equation133_implies_Equation132 (G : Type*) [Magma G] (h : Equation133 G) : Equation132 G := λ x y z => h x y z z
theorem Equation137_implies_Equation136 (G : Type*) [Magma G] (h : Equation137 G) : Equation136 G := λ x y z => h x y z z
theorem Equation141_implies_Equation140 (G : Type*) [Magma G] (h : Equation141 G) : Equation140 G := λ x y z => h x y z z
theorem Equation145_implies_Equation144 (G : Type*) [Magma G] (h : Equation145 G) : Equation144 G := λ x y z => h x y z z
theorem Equation146_implies_Equation142 (G : Type*) [Magma G] (h : Equation146 G) : Equation142 G := λ x y z => h x y z z
theorem Equation147_implies_Equation143 (G : Type*) [Magma G] (h : Equation147 G) : Equation143 G := λ x y z => h x y z z
theorem Equation148_implies_Equation144 (G : Type*) [Magma G] (h : Equation148 G) : Equation144 G := λ x y z => h x y z z
theorem Equation149_implies_Equation144 (G : Type*) [Magma G] (h : Equation149 G) : Equation144 G := λ x y z => h x y z z
theorem Equation165_implies_Equation164 (G : Type*) [Magma G] (h : Equation165 G) : Equation164 G := λ x y z => h x y z z
theorem Equation175_implies_Equation174 (G : Type*) [Magma G] (h : Equation175 G) : Equation174 G := λ x y z => h x y z z
theorem Equation185_implies_Equation184 (G : Type*) [Magma G] (h : Equation185 G) : Equation184 G := λ x y z => h x y z z
theorem Equation189_implies_Equation188 (G : Type*) [Magma G] (h : Equation189 G) : Equation188 G := λ x y z => h x y z z
theorem Equation193_implies_Equation192 (G : Type*) [Magma G] (h : Equation193 G) : Equation192 G := λ x y z => h x y z z
theorem Equation197_implies_Equation196 (G : Type*) [Magma G] (h : Equation197 G) : Equation196 G := λ x y z => h x y z z
theorem Equation198_implies_Equation194 (G : Type*) [Magma G] (h : Equation198 G) : Equation194 G := λ x y z => h x y z z
theorem Equation199_implies_Equation195 (G : Type*) [Magma G] (h : Equation199 G) : Equation195 G := λ x y z => h x y z z
theorem Equation200_implies_Equation196 (G : Type*) [Magma G] (h : Equation200 G) : Equation196 G := λ x y z => h x y z z
theorem Equation201_implies_Equation196 (G : Type*) [Magma G] (h : Equation201 G) : Equation196 G := λ x y z => h x y z z
theorem Equation217_implies_Equation216 (G : Type*) [Magma G] (h : Equation217 G) : Equation216 G := λ x y z => h x y z z
theorem Equation227_implies_Equation226 (G : Type*) [Magma G] (h : Equation227 G) : Equation226 G := λ x y z => h x y z z
theorem Equation237_implies_Equation236 (G : Type*) [Magma G] (h : Equation237 G) : Equation236 G := λ x y z => h x y z z
theorem Equation241_implies_Equation240 (G : Type*) [Magma G] (h : Equation241 G) : Equation240 G := λ x y z => h x y z z
theorem Equation245_implies_Equation244 (G : Type*) [Magma G] (h : Equation245 G) : Equation244 G := λ x y z => h x y z z
theorem Equation249_implies_Equation248 (G : Type*) [Magma G] (h : Equation249 G) : Equation248 G := λ x y z => h x y z z
theorem Equation250_implies_Equation246 (G : Type*) [Magma G] (h : Equation250 G) : Equation246 G := λ x y z => h x y z z
theorem Equation251_implies_Equation247 (G : Type*) [Magma G] (h : Equation251 G) : Equation247 G := λ x y z => h x y z z
theorem Equation252_implies_Equation248 (G : Type*) [Magma G] (h : Equation252 G) : Equation248 G := λ x y z => h x y z z
theorem Equation253_implies_Equation248 (G : Type*) [Magma G] (h : Equation253 G) : Equation248 G := λ x y z => h x y z z
theorem Equation269_implies_Equation268 (G : Type*) [Magma G] (h : Equation269 G) : Equation268 G := λ x y z => h x y z z
theorem Equation279_implies_Equation278 (G : Type*) [Magma G] (h : Equation279 G) : Equation278 G := λ x y z => h x y z z
theorem Equation289_implies_Equation288 (G : Type*) [Magma G] (h : Equation289 G) : Equation288 G := λ x y z => h x y z z
theorem Equation293_implies_Equation292 (G : Type*) [Magma G] (h : Equation293 G) : Equation292 G := λ x y z => h x y z z
theorem Equation297_implies_Equation296 (G : Type*) [Magma G] (h : Equation297 G) : Equation296 G := λ x y z => h x y z z
theorem Equation301_implies_Equation300 (G : Type*) [Magma G] (h : Equation301 G) : Equation300 G := λ x y z => h x y z z
theorem Equation302_implies_Equation298 (G : Type*) [Magma G] (h : Equation302 G) : Equation298 G := λ x y z => h x y z z
theorem Equation303_implies_Equation299 (G : Type*) [Magma G] (h : Equation303 G) : Equation299 G := λ x y z => h x y z z
theorem Equation304_implies_Equation300 (G : Type*) [Magma G] (h : Equation304 G) : Equation300 G := λ x y z => h x y z z
theorem Equation305_implies_Equation300 (G : Type*) [Magma G] (h : Equation305 G) : Equation300 G := λ x y z => h x y z z
theorem Equation321_implies_Equation320 (G : Type*) [Magma G] (h : Equation321 G) : Equation320 G := λ x y z => h x y z z
theorem Equation331_implies_Equation330 (G : Type*) [Magma G] (h : Equation331 G) : Equation330 G := λ x y z => h x y z z
theorem Equation341_implies_Equation340 (G : Type*) [Magma G] (h : Equation341 G) : Equation340 G := λ x y z => h x y z z
theorem Equation345_implies_Equation344 (G : Type*) [Magma G] (h : Equation345 G) : Equation344 G := λ x y z => h x y z z
theorem Equation349_implies_Equation348 (G : Type*) [Magma G] (h : Equation349 G) : Equation348 G := λ x y z => h x y z z
theorem Equation353_implies_Equation352 (G : Type*) [Magma G] (h : Equation353 G) : Equation352 G := λ x y z => h x y z z
theorem Equation354_implies_Equation350 (G : Type*) [Magma G] (h : Equation354 G) : Equation350 G := λ x y z => h x y z z
theorem Equation355_implies_Equation351 (G : Type*) [Magma G] (h : Equation355 G) : Equation351 G := λ x y z => h x y z z
theorem Equation356_implies_Equation352 (G : Type*) [Magma G] (h : Equation356 G) : Equation352 G := λ x y z => h x y z z
theorem Equation357_implies_Equation352 (G : Type*) [Magma G] (h : Equation357 G) : Equation352 G := λ x y z => h x y z z
theorem Equation373_implies_Equation372 (G : Type*) [Magma G] (h : Equation373 G) : Equation372 G := λ x y z => h x y z z
theorem Equation383_implies_Equation382 (G : Type*) [Magma G] (h : Equation383 G) : Equation382 G := λ x y z => h x y z z
theorem Equation393_implies_Equation392 (G : Type*) [Magma G] (h : Equation393 G) : Equation392 G := λ x y z => h x y z z
theorem Equation397_implies_Equation396 (G : Type*) [Magma G] (h : Equation397 G) : Equation396 G := λ x y z => h x y z z
theorem Equation401_implies_Equation400 (G : Type*) [Magma G] (h : Equation401 G) : Equation400 G := λ x y z => h x y z z
theorem Equation405_implies_Equation404 (G : Type*) [Magma G] (h : Equation405 G) : Equation404 G := λ x y z => h x y z z
theorem Equation406_implies_Equation402 (G : Type*) [Magma G] (h : Equation406 G) : Equation402 G := λ x y z => h x y z z
theorem Equation407_implies_Equation403 (G : Type*) [Magma G] (h : Equation407 G) : Equation403 G := λ x y z => h x y z z
theorem Equation408_implies_Equation404 (G : Type*) [Magma G] (h : Equation408 G) : Equation404 G := λ x y z => h x y z z
theorem Equation409_implies_Equation404 (G : Type*) [Magma G] (h : Equation409 G) : Equation404 G := λ x y z => h x y z z
theorem Equation425_implies_Equation424 (G : Type*) [Magma G] (h : Equation425 G) : Equation424 G := λ x y z => h x y z z
theorem Equation435_implies_Equation434 (G : Type*) [Magma G] (h : Equation435 G) : Equation434 G := λ x y z => h x y z z
theorem Equation445_implies_Equation444 (G : Type*) [Magma G] (h : Equation445 G) : Equation444 G := λ x y z => h x y z z
theorem Equation449_implies_Equation448 (G : Type*) [Magma G] (h : Equation449 G) : Equation448 G := λ x y z => h x y z z
theorem Equation453_implies_Equation452 (G : Type*) [Magma G] (h : Equation453 G) : Equation452 G := λ x y z => h x y z z
theorem Equation457_implies_Equation456 (G : Type*) [Magma G] (h : Equation457 G) : Equation456 G := λ x y z => h x y z z
theorem Equation458_implies_Equation454 (G : Type*) [Magma G] (h : Equation458 G) : Equation454 G := λ x y z => h x y z z
theorem Equation459_implies_Equation455 (G : Type*) [Magma G] (h : Equation459 G) : Equation455 G := λ x y z => h x y z z
theorem Equation460_implies_Equation456 (G : Type*) [Magma G] (h : Equation460 G) : Equation456 G := λ x y z => h x y z z
theorem Equation461_implies_Equation456 (G : Type*) [Magma G] (h : Equation461 G) : Equation456 G := λ x y z => h x y z z
theorem Equation472_implies_Equation471 (G : Type*) [Magma G] (h : Equation472 G) : Equation471 G := λ x y z => h x y z z
theorem Equation482_implies_Equation481 (G : Type*) [Magma G] (h : Equation482 G) : Equation481 G := λ x y z => h x y z z
theorem Equation486_implies_Equation485 (G : Type*) [Magma G] (h : Equation486 G) : Equation485 G := λ x y z => h x y z z
theorem Equation490_implies_Equation489 (G : Type*) [Magma G] (h : Equation490 G) : Equation489 G := λ x y z => h x y z z
theorem Equation494_implies_Equation493 (G : Type*) [Magma G] (h : Equation494 G) : Equation493 G := λ x y z => h x y z z
theorem Equation495_implies_Equation491 (G : Type*) [Magma G] (h : Equation495 G) : Equation491 G := λ x y z => h x y z z
theorem Equation496_implies_Equation492 (G : Type*) [Magma G] (h : Equation496 G) : Equation492 G := λ x y z => h x y z z
theorem Equation497_implies_Equation493 (G : Type*) [Magma G] (h : Equation497 G) : Equation493 G := λ x y z => h x y z z
theorem Equation498_implies_Equation493 (G : Type*) [Magma G] (h : Equation498 G) : Equation493 G := λ x y z => h x y z z
theorem Equation509_implies_Equation508 (G : Type*) [Magma G] (h : Equation509 G) : Equation508 G := λ x y z => h x y z z
theorem Equation519_implies_Equation518 (G : Type*) [Magma G] (h : Equation519 G) : Equation518 G := λ x y z => h x y z z
theorem Equation523_implies_Equation522 (G : Type*) [Magma G] (h : Equation523 G) : Equation522 G := λ x y z => h x y z z
theorem Equation527_implies_Equation526 (G : Type*) [Magma G] (h : Equation527 G) : Equation526 G := λ x y z => h x y z z
theorem Equation531_implies_Equation530 (G : Type*) [Magma G] (h : Equation531 G) : Equation530 G := λ x y z => h x y z z
theorem Equation532_implies_Equation528 (G : Type*) [Magma G] (h : Equation532 G) : Equation528 G := λ x y z => h x y z z
theorem Equation533_implies_Equation529 (G : Type*) [Magma G] (h : Equation533 G) : Equation529 G := λ x y z => h x y z z
theorem Equation534_implies_Equation530 (G : Type*) [Magma G] (h : Equation534 G) : Equation530 G := λ x y z => h x y z z
theorem Equation535_implies_Equation530 (G : Type*) [Magma G] (h : Equation535 G) : Equation530 G := λ x y z => h x y z z
theorem Equation540_implies_Equation539 (G : Type*) [Magma G] (h : Equation540 G) : Equation539 G := λ x y z => h x y z z
theorem Equation544_implies_Equation543 (G : Type*) [Magma G] (h : Equation544 G) : Equation543 G := λ x y z => h x y z z
theorem Equation548_implies_Equation547 (G : Type*) [Magma G] (h : Equation548 G) : Equation547 G := λ x y z => h x y z z
theorem Equation549_implies_Equation545 (G : Type*) [Magma G] (h : Equation549 G) : Equation545 G := λ x y z => h x y z z
theorem Equation550_implies_Equation546 (G : Type*) [Magma G] (h : Equation550 G) : Equation546 G := λ x y z => h x y z z
theorem Equation551_implies_Equation547 (G : Type*) [Magma G] (h : Equation551 G) : Equation547 G := λ x y z => h x y z z
theorem Equation552_implies_Equation547 (G : Type*) [Magma G] (h : Equation552 G) : Equation547 G := λ x y z => h x y z z
theorem Equation557_implies_Equation556 (G : Type*) [Magma G] (h : Equation557 G) : Equation556 G := λ x y z => h x y z z
theorem Equation561_implies_Equation560 (G : Type*) [Magma G] (h : Equation561 G) : Equation560 G := λ x y z => h x y z z
theorem Equation565_implies_Equation564 (G : Type*) [Magma G] (h : Equation565 G) : Equation564 G := λ x y z => h x y z z
theorem Equation566_implies_Equation562 (G : Type*) [Magma G] (h : Equation566 G) : Equation562 G := λ x y z => h x y z z
theorem Equation567_implies_Equation563 (G : Type*) [Magma G] (h : Equation567 G) : Equation563 G := λ x y z => h x y z z
theorem Equation568_implies_Equation564 (G : Type*) [Magma G] (h : Equation568 G) : Equation564 G := λ x y z => h x y z z
theorem Equation569_implies_Equation564 (G : Type*) [Magma G] (h : Equation569 G) : Equation564 G := λ x y z => h x y z z
theorem Equation574_implies_Equation573 (G : Type*) [Magma G] (h : Equation574 G) : Equation573 G := λ x y z => h x y z z
theorem Equation578_implies_Equation577 (G : Type*) [Magma G] (h : Equation578 G) : Equation577 G := λ x y z => h x y z z
theorem Equation582_implies_Equation581 (G : Type*) [Magma G] (h : Equation582 G) : Equation581 G := λ x y z => h x y z z
theorem Equation583_implies_Equation579 (G : Type*) [Magma G] (h : Equation583 G) : Equation579 G := λ x y z => h x y z z
theorem Equation584_implies_Equation580 (G : Type*) [Magma G] (h : Equation584 G) : Equation580 G := λ x y z => h x y z z
theorem Equation585_implies_Equation581 (G : Type*) [Magma G] (h : Equation585 G) : Equation581 G := λ x y z => h x y z z
theorem Equation586_implies_Equation581 (G : Type*) [Magma G] (h : Equation586 G) : Equation581 G := λ x y z => h x y z z
theorem Equation588_implies_Equation571 (G : Type*) [Magma G] (h : Equation588 G) : Equation571 G := λ x y z => h x y z z
theorem Equation589_implies_Equation572 (G : Type*) [Magma G] (h : Equation589 G) : Equation572 G := λ x y z => h x y z z
theorem Equation590_implies_Equation573 (G : Type*) [Magma G] (h : Equation590 G) : Equation573 G := λ x y z => h x y z z
theorem Equation591_implies_Equation573 (G : Type*) [Magma G] (h : Equation591 G) : Equation573 G := λ x y z => h x y z z
theorem Equation593_implies_Equation575 (G : Type*) [Magma G] (h : Equation593 G) : Equation575 G := λ x y z => h x y z z
theorem Equation594_implies_Equation576 (G : Type*) [Magma G] (h : Equation594 G) : Equation576 G := λ x y z => h x y z z
theorem Equation595_implies_Equation577 (G : Type*) [Magma G] (h : Equation595 G) : Equation577 G := λ x y z => h x y z z
theorem Equation596_implies_Equation577 (G : Type*) [Magma G] (h : Equation596 G) : Equation577 G := λ x y z => h x y z z
theorem Equation598_implies_Equation579 (G : Type*) [Magma G] (h : Equation598 G) : Equation579 G := λ x y z => h x y z z
theorem Equation599_implies_Equation580 (G : Type*) [Magma G] (h : Equation599 G) : Equation580 G := λ x y z => h x y z z
theorem Equation600_implies_Equation581 (G : Type*) [Magma G] (h : Equation600 G) : Equation581 G := λ x y z => h x y z z
theorem Equation601_implies_Equation581 (G : Type*) [Magma G] (h : Equation601 G) : Equation581 G := λ x y z => h x y z z
theorem Equation603_implies_Equation579 (G : Type*) [Magma G] (h : Equation603 G) : Equation579 G := λ x y z => h x y z z
theorem Equation604_implies_Equation580 (G : Type*) [Magma G] (h : Equation604 G) : Equation580 G := λ x y z => h x y z z
theorem Equation605_implies_Equation581 (G : Type*) [Magma G] (h : Equation605 G) : Equation581 G := λ x y z => h x y z z
theorem Equation606_implies_Equation581 (G : Type*) [Magma G] (h : Equation606 G) : Equation581 G := λ x y z => h x y z z
theorem Equation628_implies_Equation627 (G : Type*) [Magma G] (h : Equation628 G) : Equation627 G := λ x y z => h x y z z
theorem Equation638_implies_Equation637 (G : Type*) [Magma G] (h : Equation638 G) : Equation637 G := λ x y z => h x y z z
theorem Equation648_implies_Equation647 (G : Type*) [Magma G] (h : Equation648 G) : Equation647 G := λ x y z => h x y z z
theorem Equation652_implies_Equation651 (G : Type*) [Magma G] (h : Equation652 G) : Equation651 G := λ x y z => h x y z z
theorem Equation656_implies_Equation655 (G : Type*) [Magma G] (h : Equation656 G) : Equation655 G := λ x y z => h x y z z
theorem Equation660_implies_Equation659 (G : Type*) [Magma G] (h : Equation660 G) : Equation659 G := λ x y z => h x y z z
theorem Equation661_implies_Equation657 (G : Type*) [Magma G] (h : Equation661 G) : Equation657 G := λ x y z => h x y z z
theorem Equation662_implies_Equation658 (G : Type*) [Magma G] (h : Equation662 G) : Equation658 G := λ x y z => h x y z z
theorem Equation663_implies_Equation659 (G : Type*) [Magma G] (h : Equation663 G) : Equation659 G := λ x y z => h x y z z
theorem Equation664_implies_Equation659 (G : Type*) [Magma G] (h : Equation664 G) : Equation659 G := λ x y z => h x y z z
theorem Equation675_implies_Equation674 (G : Type*) [Magma G] (h : Equation675 G) : Equation674 G := λ x y z => h x y z z
theorem Equation685_implies_Equation684 (G : Type*) [Magma G] (h : Equation685 G) : Equation684 G := λ x y z => h x y z z
theorem Equation689_implies_Equation688 (G : Type*) [Magma G] (h : Equation689 G) : Equation688 G := λ x y z => h x y z z
theorem Equation693_implies_Equation692 (G : Type*) [Magma G] (h : Equation693 G) : Equation692 G := λ x y z => h x y z z
theorem Equation697_implies_Equation696 (G : Type*) [Magma G] (h : Equation697 G) : Equation696 G := λ x y z => h x y z z
theorem Equation698_implies_Equation694 (G : Type*) [Magma G] (h : Equation698 G) : Equation694 G := λ x y z => h x y z z
theorem Equation699_implies_Equation695 (G : Type*) [Magma G] (h : Equation699 G) : Equation695 G := λ x y z => h x y z z
theorem Equation700_implies_Equation696 (G : Type*) [Magma G] (h : Equation700 G) : Equation696 G := λ x y z => h x y z z
theorem Equation701_implies_Equation696 (G : Type*) [Magma G] (h : Equation701 G) : Equation696 G := λ x y z => h x y z z
theorem Equation712_implies_Equation711 (G : Type*) [Magma G] (h : Equation712 G) : Equation711 G := λ x y z => h x y z z
theorem Equation722_implies_Equation721 (G : Type*) [Magma G] (h : Equation722 G) : Equation721 G := λ x y z => h x y z z
theorem Equation726_implies_Equation725 (G : Type*) [Magma G] (h : Equation726 G) : Equation725 G := λ x y z => h x y z z
theorem Equation730_implies_Equation729 (G : Type*) [Magma G] (h : Equation730 G) : Equation729 G := λ x y z => h x y z z
theorem Equation734_implies_Equation733 (G : Type*) [Magma G] (h : Equation734 G) : Equation733 G := λ x y z => h x y z z
theorem Equation735_implies_Equation731 (G : Type*) [Magma G] (h : Equation735 G) : Equation731 G := λ x y z => h x y z z
theorem Equation736_implies_Equation732 (G : Type*) [Magma G] (h : Equation736 G) : Equation732 G := λ x y z => h x y z z
theorem Equation737_implies_Equation733 (G : Type*) [Magma G] (h : Equation737 G) : Equation733 G := λ x y z => h x y z z
theorem Equation738_implies_Equation733 (G : Type*) [Magma G] (h : Equation738 G) : Equation733 G := λ x y z => h x y z z
theorem Equation743_implies_Equation742 (G : Type*) [Magma G] (h : Equation743 G) : Equation742 G := λ x y z => h x y z z
theorem Equation747_implies_Equation746 (G : Type*) [Magma G] (h : Equation747 G) : Equation746 G := λ x y z => h x y z z
theorem Equation751_implies_Equation750 (G : Type*) [Magma G] (h : Equation751 G) : Equation750 G := λ x y z => h x y z z
theorem Equation752_implies_Equation748 (G : Type*) [Magma G] (h : Equation752 G) : Equation748 G := λ x y z => h x y z z
theorem Equation753_implies_Equation749 (G : Type*) [Magma G] (h : Equation753 G) : Equation749 G := λ x y z => h x y z z
theorem Equation754_implies_Equation750 (G : Type*) [Magma G] (h : Equation754 G) : Equation750 G := λ x y z => h x y z z
theorem Equation755_implies_Equation750 (G : Type*) [Magma G] (h : Equation755 G) : Equation750 G := λ x y z => h x y z z
theorem Equation760_implies_Equation759 (G : Type*) [Magma G] (h : Equation760 G) : Equation759 G := λ x y z => h x y z z
theorem Equation764_implies_Equation763 (G : Type*) [Magma G] (h : Equation764 G) : Equation763 G := λ x y z => h x y z z
theorem Equation768_implies_Equation767 (G : Type*) [Magma G] (h : Equation768 G) : Equation767 G := λ x y z => h x y z z
theorem Equation769_implies_Equation765 (G : Type*) [Magma G] (h : Equation769 G) : Equation765 G := λ x y z => h x y z z
theorem Equation770_implies_Equation766 (G : Type*) [Magma G] (h : Equation770 G) : Equation766 G := λ x y z => h x y z z
theorem Equation771_implies_Equation767 (G : Type*) [Magma G] (h : Equation771 G) : Equation767 G := λ x y z => h x y z z
theorem Equation772_implies_Equation767 (G : Type*) [Magma G] (h : Equation772 G) : Equation767 G := λ x y z => h x y z z
theorem Equation777_implies_Equation776 (G : Type*) [Magma G] (h : Equation777 G) : Equation776 G := λ x y z => h x y z z
theorem Equation781_implies_Equation780 (G : Type*) [Magma G] (h : Equation781 G) : Equation780 G := λ x y z => h x y z z
theorem Equation785_implies_Equation784 (G : Type*) [Magma G] (h : Equation785 G) : Equation784 G := λ x y z => h x y z z
theorem Equation786_implies_Equation782 (G : Type*) [Magma G] (h : Equation786 G) : Equation782 G := λ x y z => h x y z z
theorem Equation787_implies_Equation783 (G : Type*) [Magma G] (h : Equation787 G) : Equation783 G := λ x y z => h x y z z
theorem Equation788_implies_Equation784 (G : Type*) [Magma G] (h : Equation788 G) : Equation784 G := λ x y z => h x y z z
theorem Equation789_implies_Equation784 (G : Type*) [Magma G] (h : Equation789 G) : Equation784 G := λ x y z => h x y z z
theorem Equation791_implies_Equation774 (G : Type*) [Magma G] (h : Equation791 G) : Equation774 G := λ x y z => h x y z z
theorem Equation792_implies_Equation775 (G : Type*) [Magma G] (h : Equation792 G) : Equation775 G := λ x y z => h x y z z
theorem Equation793_implies_Equation776 (G : Type*) [Magma G] (h : Equation793 G) : Equation776 G := λ x y z => h x y z z
theorem Equation794_implies_Equation776 (G : Type*) [Magma G] (h : Equation794 G) : Equation776 G := λ x y z => h x y z z
theorem Equation796_implies_Equation778 (G : Type*) [Magma G] (h : Equation796 G) : Equation778 G := λ x y z => h x y z z
theorem Equation797_implies_Equation779 (G : Type*) [Magma G] (h : Equation797 G) : Equation779 G := λ x y z => h x y z z
theorem Equation798_implies_Equation780 (G : Type*) [Magma G] (h : Equation798 G) : Equation780 G := λ x y z => h x y z z
theorem Equation799_implies_Equation780 (G : Type*) [Magma G] (h : Equation799 G) : Equation780 G := λ x y z => h x y z z
theorem Equation801_implies_Equation782 (G : Type*) [Magma G] (h : Equation801 G) : Equation782 G := λ x y z => h x y z z
theorem Equation802_implies_Equation783 (G : Type*) [Magma G] (h : Equation802 G) : Equation783 G := λ x y z => h x y z z
theorem Equation803_implies_Equation784 (G : Type*) [Magma G] (h : Equation803 G) : Equation784 G := λ x y z => h x y z z
theorem Equation804_implies_Equation784 (G : Type*) [Magma G] (h : Equation804 G) : Equation784 G := λ x y z => h x y z z
theorem Equation806_implies_Equation782 (G : Type*) [Magma G] (h : Equation806 G) : Equation782 G := λ x y z => h x y z z
theorem Equation807_implies_Equation783 (G : Type*) [Magma G] (h : Equation807 G) : Equation783 G := λ x y z => h x y z z
theorem Equation808_implies_Equation784 (G : Type*) [Magma G] (h : Equation808 G) : Equation784 G := λ x y z => h x y z z
theorem Equation809_implies_Equation784 (G : Type*) [Magma G] (h : Equation809 G) : Equation784 G := λ x y z => h x y z z
theorem Equation831_implies_Equation830 (G : Type*) [Magma G] (h : Equation831 G) : Equation830 G := λ x y z => h x y z z
theorem Equation841_implies_Equation840 (G : Type*) [Magma G] (h : Equation841 G) : Equation840 G := λ x y z => h x y z z
theorem Equation851_implies_Equation850 (G : Type*) [Magma G] (h : Equation851 G) : Equation850 G := λ x y z => h x y z z
theorem Equation855_implies_Equation854 (G : Type*) [Magma G] (h : Equation855 G) : Equation854 G := λ x y z => h x y z z
theorem Equation859_implies_Equation858 (G : Type*) [Magma G] (h : Equation859 G) : Equation858 G := λ x y z => h x y z z
theorem Equation863_implies_Equation862 (G : Type*) [Magma G] (h : Equation863 G) : Equation862 G := λ x y z => h x y z z
theorem Equation864_implies_Equation860 (G : Type*) [Magma G] (h : Equation864 G) : Equation860 G := λ x y z => h x y z z
theorem Equation865_implies_Equation861 (G : Type*) [Magma G] (h : Equation865 G) : Equation861 G := λ x y z => h x y z z
theorem Equation866_implies_Equation862 (G : Type*) [Magma G] (h : Equation866 G) : Equation862 G := λ x y z => h x y z z
theorem Equation867_implies_Equation862 (G : Type*) [Magma G] (h : Equation867 G) : Equation862 G := λ x y z => h x y z z
theorem Equation878_implies_Equation877 (G : Type*) [Magma G] (h : Equation878 G) : Equation877 G := λ x y z => h x y z z
theorem Equation888_implies_Equation887 (G : Type*) [Magma G] (h : Equation888 G) : Equation887 G := λ x y z => h x y z z
theorem Equation892_implies_Equation891 (G : Type*) [Magma G] (h : Equation892 G) : Equation891 G := λ x y z => h x y z z
theorem Equation896_implies_Equation895 (G : Type*) [Magma G] (h : Equation896 G) : Equation895 G := λ x y z => h x y z z
theorem Equation900_implies_Equation899 (G : Type*) [Magma G] (h : Equation900 G) : Equation899 G := λ x y z => h x y z z
theorem Equation901_implies_Equation897 (G : Type*) [Magma G] (h : Equation901 G) : Equation897 G := λ x y z => h x y z z
theorem Equation902_implies_Equation898 (G : Type*) [Magma G] (h : Equation902 G) : Equation898 G := λ x y z => h x y z z
theorem Equation903_implies_Equation899 (G : Type*) [Magma G] (h : Equation903 G) : Equation899 G := λ x y z => h x y z z
theorem Equation904_implies_Equation899 (G : Type*) [Magma G] (h : Equation904 G) : Equation899 G := λ x y z => h x y z z
theorem Equation915_implies_Equation914 (G : Type*) [Magma G] (h : Equation915 G) : Equation914 G := λ x y z => h x y z z
theorem Equation925_implies_Equation924 (G : Type*) [Magma G] (h : Equation925 G) : Equation924 G := λ x y z => h x y z z
theorem Equation929_implies_Equation928 (G : Type*) [Magma G] (h : Equation929 G) : Equation928 G := λ x y z => h x y z z
theorem Equation933_implies_Equation932 (G : Type*) [Magma G] (h : Equation933 G) : Equation932 G := λ x y z => h x y z z
theorem Equation937_implies_Equation936 (G : Type*) [Magma G] (h : Equation937 G) : Equation936 G := λ x y z => h x y z z
theorem Equation938_implies_Equation934 (G : Type*) [Magma G] (h : Equation938 G) : Equation934 G := λ x y z => h x y z z
theorem Equation939_implies_Equation935 (G : Type*) [Magma G] (h : Equation939 G) : Equation935 G := λ x y z => h x y z z
theorem Equation940_implies_Equation936 (G : Type*) [Magma G] (h : Equation940 G) : Equation936 G := λ x y z => h x y z z
theorem Equation941_implies_Equation936 (G : Type*) [Magma G] (h : Equation941 G) : Equation936 G := λ x y z => h x y z z
theorem Equation946_implies_Equation945 (G : Type*) [Magma G] (h : Equation946 G) : Equation945 G := λ x y z => h x y z z
theorem Equation950_implies_Equation949 (G : Type*) [Magma G] (h : Equation950 G) : Equation949 G := λ x y z => h x y z z
theorem Equation954_implies_Equation953 (G : Type*) [Magma G] (h : Equation954 G) : Equation953 G := λ x y z => h x y z z
theorem Equation955_implies_Equation951 (G : Type*) [Magma G] (h : Equation955 G) : Equation951 G := λ x y z => h x y z z
theorem Equation956_implies_Equation952 (G : Type*) [Magma G] (h : Equation956 G) : Equation952 G := λ x y z => h x y z z
theorem Equation957_implies_Equation953 (G : Type*) [Magma G] (h : Equation957 G) : Equation953 G := λ x y z => h x y z z
theorem Equation958_implies_Equation953 (G : Type*) [Magma G] (h : Equation958 G) : Equation953 G := λ x y z => h x y z z
theorem Equation963_implies_Equation962 (G : Type*) [Magma G] (h : Equation963 G) : Equation962 G := λ x y z => h x y z z
theorem Equation967_implies_Equation966 (G : Type*) [Magma G] (h : Equation967 G) : Equation966 G := λ x y z => h x y z z
theorem Equation971_implies_Equation970 (G : Type*) [Magma G] (h : Equation971 G) : Equation970 G := λ x y z => h x y z z
theorem Equation972_implies_Equation968 (G : Type*) [Magma G] (h : Equation972 G) : Equation968 G := λ x y z => h x y z z
theorem Equation973_implies_Equation969 (G : Type*) [Magma G] (h : Equation973 G) : Equation969 G := λ x y z => h x y z z
theorem Equation974_implies_Equation970 (G : Type*) [Magma G] (h : Equation974 G) : Equation970 G := λ x y z => h x y z z
theorem Equation975_implies_Equation970 (G : Type*) [Magma G] (h : Equation975 G) : Equation970 G := λ x y z => h x y z z
theorem Equation980_implies_Equation979 (G : Type*) [Magma G] (h : Equation980 G) : Equation979 G := λ x y z => h x y z z
theorem Equation984_implies_Equation983 (G : Type*) [Magma G] (h : Equation984 G) : Equation983 G := λ x y z => h x y z z
theorem Equation988_implies_Equation987 (G : Type*) [Magma G] (h : Equation988 G) : Equation987 G := λ x y z => h x y z z
theorem Equation989_implies_Equation985 (G : Type*) [Magma G] (h : Equation989 G) : Equation985 G := λ x y z => h x y z z
theorem Equation990_implies_Equation986 (G : Type*) [Magma G] (h : Equation990 G) : Equation986 G := λ x y z => h x y z z
theorem Equation991_implies_Equation987 (G : Type*) [Magma G] (h : Equation991 G) : Equation987 G := λ x y z => h x y z z
theorem Equation992_implies_Equation987 (G : Type*) [Magma G] (h : Equation992 G) : Equation987 G := λ x y z => h x y z z
theorem Equation994_implies_Equation977 (G : Type*) [Magma G] (h : Equation994 G) : Equation977 G := λ x y z => h x y z z
theorem Equation995_implies_Equation978 (G : Type*) [Magma G] (h : Equation995 G) : Equation978 G := λ x y z => h x y z z
theorem Equation996_implies_Equation979 (G : Type*) [Magma G] (h : Equation996 G) : Equation979 G := λ x y z => h x y z z
theorem Equation997_implies_Equation979 (G : Type*) [Magma G] (h : Equation997 G) : Equation979 G := λ x y z => h x y z z
theorem Equation999_implies_Equation981 (G : Type*) [Magma G] (h : Equation999 G) : Equation981 G := λ x y z => h x y z z
theorem Equation1000_implies_Equation982 (G : Type*) [Magma G] (h : Equation1000 G) : Equation982 G := λ x y z => h x y z z
theorem Equation1001_implies_Equation983 (G : Type*) [Magma G] (h : Equation1001 G) : Equation983 G := λ x y z => h x y z z
theorem Equation1002_implies_Equation983 (G : Type*) [Magma G] (h : Equation1002 G) : Equation983 G := λ x y z => h x y z z
theorem Equation1004_implies_Equation985 (G : Type*) [Magma G] (h : Equation1004 G) : Equation985 G := λ x y z => h x y z z
theorem Equation1005_implies_Equation986 (G : Type*) [Magma G] (h : Equation1005 G) : Equation986 G := λ x y z => h x y z z
theorem Equation1006_implies_Equation987 (G : Type*) [Magma G] (h : Equation1006 G) : Equation987 G := λ x y z => h x y z z
theorem Equation1007_implies_Equation987 (G : Type*) [Magma G] (h : Equation1007 G) : Equation987 G := λ x y z => h x y z z
theorem Equation1009_implies_Equation985 (G : Type*) [Magma G] (h : Equation1009 G) : Equation985 G := λ x y z => h x y z z
theorem Equation1010_implies_Equation986 (G : Type*) [Magma G] (h : Equation1010 G) : Equation986 G := λ x y z => h x y z z
theorem Equation1011_implies_Equation987 (G : Type*) [Magma G] (h : Equation1011 G) : Equation987 G := λ x y z => h x y z z
theorem Equation1012_implies_Equation987 (G : Type*) [Magma G] (h : Equation1012 G) : Equation987 G := λ x y z => h x y z z
theorem Equation1034_implies_Equation1033 (G : Type*) [Magma G] (h : Equation1034 G) : Equation1033 G := λ x y z => h x y z z
theorem Equation1044_implies_Equation1043 (G : Type*) [Magma G] (h : Equation1044 G) : Equation1043 G := λ x y z => h x y z z
theorem Equation1054_implies_Equation1053 (G : Type*) [Magma G] (h : Equation1054 G) : Equation1053 G := λ x y z => h x y z z
theorem Equation1058_implies_Equation1057 (G : Type*) [Magma G] (h : Equation1058 G) : Equation1057 G := λ x y z => h x y z z
theorem Equation1062_implies_Equation1061 (G : Type*) [Magma G] (h : Equation1062 G) : Equation1061 G := λ x y z => h x y z z
theorem Equation1066_implies_Equation1065 (G : Type*) [Magma G] (h : Equation1066 G) : Equation1065 G := λ x y z => h x y z z
theorem Equation1067_implies_Equation1063 (G : Type*) [Magma G] (h : Equation1067 G) : Equation1063 G := λ x y z => h x y z z
theorem Equation1068_implies_Equation1064 (G : Type*) [Magma G] (h : Equation1068 G) : Equation1064 G := λ x y z => h x y z z
theorem Equation1069_implies_Equation1065 (G : Type*) [Magma G] (h : Equation1069 G) : Equation1065 G := λ x y z => h x y z z
theorem Equation1070_implies_Equation1065 (G : Type*) [Magma G] (h : Equation1070 G) : Equation1065 G := λ x y z => h x y z z
theorem Equation1081_implies_Equation1080 (G : Type*) [Magma G] (h : Equation1081 G) : Equation1080 G := λ x y z => h x y z z
theorem Equation1091_implies_Equation1090 (G : Type*) [Magma G] (h : Equation1091 G) : Equation1090 G := λ x y z => h x y z z
theorem Equation1095_implies_Equation1094 (G : Type*) [Magma G] (h : Equation1095 G) : Equation1094 G := λ x y z => h x y z z
theorem Equation1099_implies_Equation1098 (G : Type*) [Magma G] (h : Equation1099 G) : Equation1098 G := λ x y z => h x y z z
theorem Equation1103_implies_Equation1102 (G : Type*) [Magma G] (h : Equation1103 G) : Equation1102 G := λ x y z => h x y z z
theorem Equation1104_implies_Equation1100 (G : Type*) [Magma G] (h : Equation1104 G) : Equation1100 G := λ x y z => h x y z z
theorem Equation1105_implies_Equation1101 (G : Type*) [Magma G] (h : Equation1105 G) : Equation1101 G := λ x y z => h x y z z
theorem Equation1106_implies_Equation1102 (G : Type*) [Magma G] (h : Equation1106 G) : Equation1102 G := λ x y z => h x y z z
theorem Equation1107_implies_Equation1102 (G : Type*) [Magma G] (h : Equation1107 G) : Equation1102 G := λ x y z => h x y z z
theorem Equation1118_implies_Equation1117 (G : Type*) [Magma G] (h : Equation1118 G) : Equation1117 G := λ x y z => h x y z z
theorem Equation1128_implies_Equation1127 (G : Type*) [Magma G] (h : Equation1128 G) : Equation1127 G := λ x y z => h x y z z
theorem Equation1132_implies_Equation1131 (G : Type*) [Magma G] (h : Equation1132 G) : Equation1131 G := λ x y z => h x y z z
theorem Equation1136_implies_Equation1135 (G : Type*) [Magma G] (h : Equation1136 G) : Equation1135 G := λ x y z => h x y z z
theorem Equation1140_implies_Equation1139 (G : Type*) [Magma G] (h : Equation1140 G) : Equation1139 G := λ x y z => h x y z z
theorem Equation1141_implies_Equation1137 (G : Type*) [Magma G] (h : Equation1141 G) : Equation1137 G := λ x y z => h x y z z
theorem Equation1142_implies_Equation1138 (G : Type*) [Magma G] (h : Equation1142 G) : Equation1138 G := λ x y z => h x y z z
theorem Equation1143_implies_Equation1139 (G : Type*) [Magma G] (h : Equation1143 G) : Equation1139 G := λ x y z => h x y z z
theorem Equation1144_implies_Equation1139 (G : Type*) [Magma G] (h : Equation1144 G) : Equation1139 G := λ x y z => h x y z z
theorem Equation1149_implies_Equation1148 (G : Type*) [Magma G] (h : Equation1149 G) : Equation1148 G := λ x y z => h x y z z
theorem Equation1153_implies_Equation1152 (G : Type*) [Magma G] (h : Equation1153 G) : Equation1152 G := λ x y z => h x y z z
theorem Equation1157_implies_Equation1156 (G : Type*) [Magma G] (h : Equation1157 G) : Equation1156 G := λ x y z => h x y z z
theorem Equation1158_implies_Equation1154 (G : Type*) [Magma G] (h : Equation1158 G) : Equation1154 G := λ x y z => h x y z z
theorem Equation1159_implies_Equation1155 (G : Type*) [Magma G] (h : Equation1159 G) : Equation1155 G := λ x y z => h x y z z
theorem Equation1160_implies_Equation1156 (G : Type*) [Magma G] (h : Equation1160 G) : Equation1156 G := λ x y z => h x y z z
theorem Equation1161_implies_Equation1156 (G : Type*) [Magma G] (h : Equation1161 G) : Equation1156 G := λ x y z => h x y z z
theorem Equation1166_implies_Equation1165 (G : Type*) [Magma G] (h : Equation1166 G) : Equation1165 G := λ x y z => h x y z z
theorem Equation1170_implies_Equation1169 (G : Type*) [Magma G] (h : Equation1170 G) : Equation1169 G := λ x y z => h x y z z
theorem Equation1174_implies_Equation1173 (G : Type*) [Magma G] (h : Equation1174 G) : Equation1173 G := λ x y z => h x y z z
theorem Equation1175_implies_Equation1171 (G : Type*) [Magma G] (h : Equation1175 G) : Equation1171 G := λ x y z => h x y z z
theorem Equation1176_implies_Equation1172 (G : Type*) [Magma G] (h : Equation1176 G) : Equation1172 G := λ x y z => h x y z z
theorem Equation1177_implies_Equation1173 (G : Type*) [Magma G] (h : Equation1177 G) : Equation1173 G := λ x y z => h x y z z
theorem Equation1178_implies_Equation1173 (G : Type*) [Magma G] (h : Equation1178 G) : Equation1173 G := λ x y z => h x y z z
theorem Equation1183_implies_Equation1182 (G : Type*) [Magma G] (h : Equation1183 G) : Equation1182 G := λ x y z => h x y z z
theorem Equation1187_implies_Equation1186 (G : Type*) [Magma G] (h : Equation1187 G) : Equation1186 G := λ x y z => h x y z z
theorem Equation1191_implies_Equation1190 (G : Type*) [Magma G] (h : Equation1191 G) : Equation1190 G := λ x y z => h x y z z
theorem Equation1192_implies_Equation1188 (G : Type*) [Magma G] (h : Equation1192 G) : Equation1188 G := λ x y z => h x y z z
theorem Equation1193_implies_Equation1189 (G : Type*) [Magma G] (h : Equation1193 G) : Equation1189 G := λ x y z => h x y z z
theorem Equation1194_implies_Equation1190 (G : Type*) [Magma G] (h : Equation1194 G) : Equation1190 G := λ x y z => h x y z z
theorem Equation1195_implies_Equation1190 (G : Type*) [Magma G] (h : Equation1195 G) : Equation1190 G := λ x y z => h x y z z
theorem Equation1197_implies_Equation1180 (G : Type*) [Magma G] (h : Equation1197 G) : Equation1180 G := λ x y z => h x y z z
theorem Equation1198_implies_Equation1181 (G : Type*) [Magma G] (h : Equation1198 G) : Equation1181 G := λ x y z => h x y z z
theorem Equation1199_implies_Equation1182 (G : Type*) [Magma G] (h : Equation1199 G) : Equation1182 G := λ x y z => h x y z z
theorem Equation1200_implies_Equation1182 (G : Type*) [Magma G] (h : Equation1200 G) : Equation1182 G := λ x y z => h x y z z
theorem Equation1202_implies_Equation1184 (G : Type*) [Magma G] (h : Equation1202 G) : Equation1184 G := λ x y z => h x y z z
theorem Equation1203_implies_Equation1185 (G : Type*) [Magma G] (h : Equation1203 G) : Equation1185 G := λ x y z => h x y z z
theorem Equation1204_implies_Equation1186 (G : Type*) [Magma G] (h : Equation1204 G) : Equation1186 G := λ x y z => h x y z z
theorem Equation1205_implies_Equation1186 (G : Type*) [Magma G] (h : Equation1205 G) : Equation1186 G := λ x y z => h x y z z
theorem Equation1207_implies_Equation1188 (G : Type*) [Magma G] (h : Equation1207 G) : Equation1188 G := λ x y z => h x y z z
theorem Equation1208_implies_Equation1189 (G : Type*) [Magma G] (h : Equation1208 G) : Equation1189 G := λ x y z => h x y z z
theorem Equation1209_implies_Equation1190 (G : Type*) [Magma G] (h : Equation1209 G) : Equation1190 G := λ x y z => h x y z z
theorem Equation1210_implies_Equation1190 (G : Type*) [Magma G] (h : Equation1210 G) : Equation1190 G := λ x y z => h x y z z
theorem Equation1212_implies_Equation1188 (G : Type*) [Magma G] (h : Equation1212 G) : Equation1188 G := λ x y z => h x y z z
theorem Equation1213_implies_Equation1189 (G : Type*) [Magma G] (h : Equation1213 G) : Equation1189 G := λ x y z => h x y z z
theorem Equation1214_implies_Equation1190 (G : Type*) [Magma G] (h : Equation1214 G) : Equation1190 G := λ x y z => h x y z z
theorem Equation1215_implies_Equation1190 (G : Type*) [Magma G] (h : Equation1215 G) : Equation1190 G := λ x y z => h x y z z
theorem Equation1237_implies_Equation1236 (G : Type*) [Magma G] (h : Equation1237 G) : Equation1236 G := λ x y z => h x y z z
theorem Equation1247_implies_Equation1246 (G : Type*) [Magma G] (h : Equation1247 G) : Equation1246 G := λ x y z => h x y z z
theorem Equation1257_implies_Equation1256 (G : Type*) [Magma G] (h : Equation1257 G) : Equation1256 G := λ x y z => h x y z z
theorem Equation1261_implies_Equation1260 (G : Type*) [Magma G] (h : Equation1261 G) : Equation1260 G := λ x y z => h x y z z
theorem Equation1265_implies_Equation1264 (G : Type*) [Magma G] (h : Equation1265 G) : Equation1264 G := λ x y z => h x y z z
theorem Equation1269_implies_Equation1268 (G : Type*) [Magma G] (h : Equation1269 G) : Equation1268 G := λ x y z => h x y z z
theorem Equation1270_implies_Equation1266 (G : Type*) [Magma G] (h : Equation1270 G) : Equation1266 G := λ x y z => h x y z z
theorem Equation1271_implies_Equation1267 (G : Type*) [Magma G] (h : Equation1271 G) : Equation1267 G := λ x y z => h x y z z
theorem Equation1272_implies_Equation1268 (G : Type*) [Magma G] (h : Equation1272 G) : Equation1268 G := λ x y z => h x y z z
theorem Equation1273_implies_Equation1268 (G : Type*) [Magma G] (h : Equation1273 G) : Equation1268 G := λ x y z => h x y z z
theorem Equation1284_implies_Equation1283 (G : Type*) [Magma G] (h : Equation1284 G) : Equation1283 G := λ x y z => h x y z z
theorem Equation1294_implies_Equation1293 (G : Type*) [Magma G] (h : Equation1294 G) : Equation1293 G := λ x y z => h x y z z
theorem Equation1298_implies_Equation1297 (G : Type*) [Magma G] (h : Equation1298 G) : Equation1297 G := λ x y z => h x y z z
theorem Equation1302_implies_Equation1301 (G : Type*) [Magma G] (h : Equation1302 G) : Equation1301 G := λ x y z => h x y z z
theorem Equation1306_implies_Equation1305 (G : Type*) [Magma G] (h : Equation1306 G) : Equation1305 G := λ x y z => h x y z z
theorem Equation1307_implies_Equation1303 (G : Type*) [Magma G] (h : Equation1307 G) : Equation1303 G := λ x y z => h x y z z
theorem Equation1308_implies_Equation1304 (G : Type*) [Magma G] (h : Equation1308 G) : Equation1304 G := λ x y z => h x y z z
theorem Equation1309_implies_Equation1305 (G : Type*) [Magma G] (h : Equation1309 G) : Equation1305 G := λ x y z => h x y z z
theorem Equation1310_implies_Equation1305 (G : Type*) [Magma G] (h : Equation1310 G) : Equation1305 G := λ x y z => h x y z z
theorem Equation1321_implies_Equation1320 (G : Type*) [Magma G] (h : Equation1321 G) : Equation1320 G := λ x y z => h x y z z
theorem Equation1331_implies_Equation1330 (G : Type*) [Magma G] (h : Equation1331 G) : Equation1330 G := λ x y z => h x y z z
theorem Equation1335_implies_Equation1334 (G : Type*) [Magma G] (h : Equation1335 G) : Equation1334 G := λ x y z => h x y z z
theorem Equation1339_implies_Equation1338 (G : Type*) [Magma G] (h : Equation1339 G) : Equation1338 G := λ x y z => h x y z z
theorem Equation1343_implies_Equation1342 (G : Type*) [Magma G] (h : Equation1343 G) : Equation1342 G := λ x y z => h x y z z
theorem Equation1344_implies_Equation1340 (G : Type*) [Magma G] (h : Equation1344 G) : Equation1340 G := λ x y z => h x y z z
theorem Equation1345_implies_Equation1341 (G : Type*) [Magma G] (h : Equation1345 G) : Equation1341 G := λ x y z => h x y z z
theorem Equation1346_implies_Equation1342 (G : Type*) [Magma G] (h : Equation1346 G) : Equation1342 G := λ x y z => h x y z z
theorem Equation1347_implies_Equation1342 (G : Type*) [Magma G] (h : Equation1347 G) : Equation1342 G := λ x y z => h x y z z
theorem Equation1352_implies_Equation1351 (G : Type*) [Magma G] (h : Equation1352 G) : Equation1351 G := λ x y z => h x y z z
theorem Equation1356_implies_Equation1355 (G : Type*) [Magma G] (h : Equation1356 G) : Equation1355 G := λ x y z => h x y z z
theorem Equation1360_implies_Equation1359 (G : Type*) [Magma G] (h : Equation1360 G) : Equation1359 G := λ x y z => h x y z z
theorem Equation1361_implies_Equation1357 (G : Type*) [Magma G] (h : Equation1361 G) : Equation1357 G := λ x y z => h x y z z
theorem Equation1362_implies_Equation1358 (G : Type*) [Magma G] (h : Equation1362 G) : Equation1358 G := λ x y z => h x y z z
theorem Equation1363_implies_Equation1359 (G : Type*) [Magma G] (h : Equation1363 G) : Equation1359 G := λ x y z => h x y z z
theorem Equation1364_implies_Equation1359 (G : Type*) [Magma G] (h : Equation1364 G) : Equation1359 G := λ x y z => h x y z z
theorem Equation1369_implies_Equation1368 (G : Type*) [Magma G] (h : Equation1369 G) : Equation1368 G := λ x y z => h x y z z
theorem Equation1373_implies_Equation1372 (G : Type*) [Magma G] (h : Equation1373 G) : Equation1372 G := λ x y z => h x y z z
theorem Equation1377_implies_Equation1376 (G : Type*) [Magma G] (h : Equation1377 G) : Equation1376 G := λ x y z => h x y z z
theorem Equation1378_implies_Equation1374 (G : Type*) [Magma G] (h : Equation1378 G) : Equation1374 G := λ x y z => h x y z z
theorem Equation1379_implies_Equation1375 (G : Type*) [Magma G] (h : Equation1379 G) : Equation1375 G := λ x y z => h x y z z
theorem Equation1380_implies_Equation1376 (G : Type*) [Magma G] (h : Equation1380 G) : Equation1376 G := λ x y z => h x y z z
theorem Equation1381_implies_Equation1376 (G : Type*) [Magma G] (h : Equation1381 G) : Equation1376 G := λ x y z => h x y z z
theorem Equation1386_implies_Equation1385 (G : Type*) [Magma G] (h : Equation1386 G) : Equation1385 G := λ x y z => h x y z z
theorem Equation1390_implies_Equation1389 (G : Type*) [Magma G] (h : Equation1390 G) : Equation1389 G := λ x y z => h x y z z
theorem Equation1394_implies_Equation1393 (G : Type*) [Magma G] (h : Equation1394 G) : Equation1393 G := λ x y z => h x y z z
theorem Equation1395_implies_Equation1391 (G : Type*) [Magma G] (h : Equation1395 G) : Equation1391 G := λ x y z => h x y z z
theorem Equation1396_implies_Equation1392 (G : Type*) [Magma G] (h : Equation1396 G) : Equation1392 G := λ x y z => h x y z z
theorem Equation1397_implies_Equation1393 (G : Type*) [Magma G] (h : Equation1397 G) : Equation1393 G := λ x y z => h x y z z
theorem Equation1398_implies_Equation1393 (G : Type*) [Magma G] (h : Equation1398 G) : Equation1393 G := λ x y z => h x y z z
theorem Equation1400_implies_Equation1383 (G : Type*) [Magma G] (h : Equation1400 G) : Equation1383 G := λ x y z => h x y z z
theorem Equation1401_implies_Equation1384 (G : Type*) [Magma G] (h : Equation1401 G) : Equation1384 G := λ x y z => h x y z z
theorem Equation1402_implies_Equation1385 (G : Type*) [Magma G] (h : Equation1402 G) : Equation1385 G := λ x y z => h x y z z
theorem Equation1403_implies_Equation1385 (G : Type*) [Magma G] (h : Equation1403 G) : Equation1385 G := λ x y z => h x y z z
theorem Equation1405_implies_Equation1387 (G : Type*) [Magma G] (h : Equation1405 G) : Equation1387 G := λ x y z => h x y z z
theorem Equation1406_implies_Equation1388 (G : Type*) [Magma G] (h : Equation1406 G) : Equation1388 G := λ x y z => h x y z z
theorem Equation1407_implies_Equation1389 (G : Type*) [Magma G] (h : Equation1407 G) : Equation1389 G := λ x y z => h x y z z
theorem Equation1408_implies_Equation1389 (G : Type*) [Magma G] (h : Equation1408 G) : Equation1389 G := λ x y z => h x y z z
theorem Equation1410_implies_Equation1391 (G : Type*) [Magma G] (h : Equation1410 G) : Equation1391 G := λ x y z => h x y z z
theorem Equation1411_implies_Equation1392 (G : Type*) [Magma G] (h : Equation1411 G) : Equation1392 G := λ x y z => h x y z z
theorem Equation1412_implies_Equation1393 (G : Type*) [Magma G] (h : Equation1412 G) : Equation1393 G := λ x y z => h x y z z
theorem Equation1413_implies_Equation1393 (G : Type*) [Magma G] (h : Equation1413 G) : Equation1393 G := λ x y z => h x y z z
theorem Equation1415_implies_Equation1391 (G : Type*) [Magma G] (h : Equation1415 G) : Equation1391 G := λ x y z => h x y z z
theorem Equation1416_implies_Equation1392 (G : Type*) [Magma G] (h : Equation1416 G) : Equation1392 G := λ x y z => h x y z z
theorem Equation1417_implies_Equation1393 (G : Type*) [Magma G] (h : Equation1417 G) : Equation1393 G := λ x y z => h x y z z
theorem Equation1418_implies_Equation1393 (G : Type*) [Magma G] (h : Equation1418 G) : Equation1393 G := λ x y z => h x y z z
theorem Equation1440_implies_Equation1439 (G : Type*) [Magma G] (h : Equation1440 G) : Equation1439 G := λ x y z => h x y z z
theorem Equation1450_implies_Equation1449 (G : Type*) [Magma G] (h : Equation1450 G) : Equation1449 G := λ x y z => h x y z z
theorem Equation1460_implies_Equation1459 (G : Type*) [Magma G] (h : Equation1460 G) : Equation1459 G := λ x y z => h x y z z
theorem Equation1464_implies_Equation1463 (G : Type*) [Magma G] (h : Equation1464 G) : Equation1463 G := λ x y z => h x y z z
theorem Equation1468_implies_Equation1467 (G : Type*) [Magma G] (h : Equation1468 G) : Equation1467 G := λ x y z => h x y z z
theorem Equation1472_implies_Equation1471 (G : Type*) [Magma G] (h : Equation1472 G) : Equation1471 G := λ x y z => h x y z z
theorem Equation1473_implies_Equation1469 (G : Type*) [Magma G] (h : Equation1473 G) : Equation1469 G := λ x y z => h x y z z
theorem Equation1474_implies_Equation1470 (G : Type*) [Magma G] (h : Equation1474 G) : Equation1470 G := λ x y z => h x y z z
theorem Equation1475_implies_Equation1471 (G : Type*) [Magma G] (h : Equation1475 G) : Equation1471 G := λ x y z => h x y z z
theorem Equation1476_implies_Equation1471 (G : Type*) [Magma G] (h : Equation1476 G) : Equation1471 G := λ x y z => h x y z z
theorem Equation1487_implies_Equation1486 (G : Type*) [Magma G] (h : Equation1487 G) : Equation1486 G := λ x y z => h x y z z
theorem Equation1497_implies_Equation1496 (G : Type*) [Magma G] (h : Equation1497 G) : Equation1496 G := λ x y z => h x y z z
theorem Equation1501_implies_Equation1500 (G : Type*) [Magma G] (h : Equation1501 G) : Equation1500 G := λ x y z => h x y z z
theorem Equation1505_implies_Equation1504 (G : Type*) [Magma G] (h : Equation1505 G) : Equation1504 G := λ x y z => h x y z z
theorem Equation1509_implies_Equation1508 (G : Type*) [Magma G] (h : Equation1509 G) : Equation1508 G := λ x y z => h x y z z
theorem Equation1510_implies_Equation1506 (G : Type*) [Magma G] (h : Equation1510 G) : Equation1506 G := λ x y z => h x y z z
theorem Equation1511_implies_Equation1507 (G : Type*) [Magma G] (h : Equation1511 G) : Equation1507 G := λ x y z => h x y z z
theorem Equation1512_implies_Equation1508 (G : Type*) [Magma G] (h : Equation1512 G) : Equation1508 G := λ x y z => h x y z z
theorem Equation1513_implies_Equation1508 (G : Type*) [Magma G] (h : Equation1513 G) : Equation1508 G := λ x y z => h x y z z
theorem Equation1524_implies_Equation1523 (G : Type*) [Magma G] (h : Equation1524 G) : Equation1523 G := λ x y z => h x y z z
theorem Equation1534_implies_Equation1533 (G : Type*) [Magma G] (h : Equation1534 G) : Equation1533 G := λ x y z => h x y z z
theorem Equation1538_implies_Equation1537 (G : Type*) [Magma G] (h : Equation1538 G) : Equation1537 G := λ x y z => h x y z z
theorem Equation1542_implies_Equation1541 (G : Type*) [Magma G] (h : Equation1542 G) : Equation1541 G := λ x y z => h x y z z
theorem Equation1546_implies_Equation1545 (G : Type*) [Magma G] (h : Equation1546 G) : Equation1545 G := λ x y z => h x y z z
theorem Equation1547_implies_Equation1543 (G : Type*) [Magma G] (h : Equation1547 G) : Equation1543 G := λ x y z => h x y z z
theorem Equation1548_implies_Equation1544 (G : Type*) [Magma G] (h : Equation1548 G) : Equation1544 G := λ x y z => h x y z z
theorem Equation1549_implies_Equation1545 (G : Type*) [Magma G] (h : Equation1549 G) : Equation1545 G := λ x y z => h x y z z
theorem Equation1550_implies_Equation1545 (G : Type*) [Magma G] (h : Equation1550 G) : Equation1545 G := λ x y z => h x y z z
theorem Equation1555_implies_Equation1554 (G : Type*) [Magma G] (h : Equation1555 G) : Equation1554 G := λ x y z => h x y z z
theorem Equation1559_implies_Equation1558 (G : Type*) [Magma G] (h : Equation1559 G) : Equation1558 G := λ x y z => h x y z z
theorem Equation1563_implies_Equation1562 (G : Type*) [Magma G] (h : Equation1563 G) : Equation1562 G := λ x y z => h x y z z
theorem Equation1564_implies_Equation1560 (G : Type*) [Magma G] (h : Equation1564 G) : Equation1560 G := λ x y z => h x y z z
theorem Equation1565_implies_Equation1561 (G : Type*) [Magma G] (h : Equation1565 G) : Equation1561 G := λ x y z => h x y z z
theorem Equation1566_implies_Equation1562 (G : Type*) [Magma G] (h : Equation1566 G) : Equation1562 G := λ x y z => h x y z z
theorem Equation1567_implies_Equation1562 (G : Type*) [Magma G] (h : Equation1567 G) : Equation1562 G := λ x y z => h x y z z
theorem Equation1572_implies_Equation1571 (G : Type*) [Magma G] (h : Equation1572 G) : Equation1571 G := λ x y z => h x y z z
theorem Equation1576_implies_Equation1575 (G : Type*) [Magma G] (h : Equation1576 G) : Equation1575 G := λ x y z => h x y z z
theorem Equation1580_implies_Equation1579 (G : Type*) [Magma G] (h : Equation1580 G) : Equation1579 G := λ x y z => h x y z z
theorem Equation1581_implies_Equation1577 (G : Type*) [Magma G] (h : Equation1581 G) : Equation1577 G := λ x y z => h x y z z
theorem Equation1582_implies_Equation1578 (G : Type*) [Magma G] (h : Equation1582 G) : Equation1578 G := λ x y z => h x y z z
theorem Equation1583_implies_Equation1579 (G : Type*) [Magma G] (h : Equation1583 G) : Equation1579 G := λ x y z => h x y z z
theorem Equation1584_implies_Equation1579 (G : Type*) [Magma G] (h : Equation1584 G) : Equation1579 G := λ x y z => h x y z z
theorem Equation1589_implies_Equation1588 (G : Type*) [Magma G] (h : Equation1589 G) : Equation1588 G := λ x y z => h x y z z
theorem Equation1593_implies_Equation1592 (G : Type*) [Magma G] (h : Equation1593 G) : Equation1592 G := λ x y z => h x y z z
theorem Equation1597_implies_Equation1596 (G : Type*) [Magma G] (h : Equation1597 G) : Equation1596 G := λ x y z => h x y z z
theorem Equation1598_implies_Equation1594 (G : Type*) [Magma G] (h : Equation1598 G) : Equation1594 G := λ x y z => h x y z z
theorem Equation1599_implies_Equation1595 (G : Type*) [Magma G] (h : Equation1599 G) : Equation1595 G := λ x y z => h x y z z
theorem Equation1600_implies_Equation1596 (G : Type*) [Magma G] (h : Equation1600 G) : Equation1596 G := λ x y z => h x y z z
theorem Equation1601_implies_Equation1596 (G : Type*) [Magma G] (h : Equation1601 G) : Equation1596 G := λ x y z => h x y z z
theorem Equation1603_implies_Equation1586 (G : Type*) [Magma G] (h : Equation1603 G) : Equation1586 G := λ x y z => h x y z z
theorem Equation1604_implies_Equation1587 (G : Type*) [Magma G] (h : Equation1604 G) : Equation1587 G := λ x y z => h x y z z
theorem Equation1605_implies_Equation1588 (G : Type*) [Magma G] (h : Equation1605 G) : Equation1588 G := λ x y z => h x y z z
theorem Equation1606_implies_Equation1588 (G : Type*) [Magma G] (h : Equation1606 G) : Equation1588 G := λ x y z => h x y z z
theorem Equation1608_implies_Equation1590 (G : Type*) [Magma G] (h : Equation1608 G) : Equation1590 G := λ x y z => h x y z z
theorem Equation1609_implies_Equation1591 (G : Type*) [Magma G] (h : Equation1609 G) : Equation1591 G := λ x y z => h x y z z
theorem Equation1610_implies_Equation1592 (G : Type*) [Magma G] (h : Equation1610 G) : Equation1592 G := λ x y z => h x y z z
theorem Equation1611_implies_Equation1592 (G : Type*) [Magma G] (h : Equation1611 G) : Equation1592 G := λ x y z => h x y z z
theorem Equation1613_implies_Equation1594 (G : Type*) [Magma G] (h : Equation1613 G) : Equation1594 G := λ x y z => h x y z z
theorem Equation1614_implies_Equation1595 (G : Type*) [Magma G] (h : Equation1614 G) : Equation1595 G := λ x y z => h x y z z
theorem Equation1615_implies_Equation1596 (G : Type*) [Magma G] (h : Equation1615 G) : Equation1596 G := λ x y z => h x y z z
theorem Equation1616_implies_Equation1596 (G : Type*) [Magma G] (h : Equation1616 G) : Equation1596 G := λ x y z => h x y z z
theorem Equation1618_implies_Equation1594 (G : Type*) [Magma G] (h : Equation1618 G) : Equation1594 G := λ x y z => h x y z z
theorem Equation1619_implies_Equation1595 (G : Type*) [Magma G] (h : Equation1619 G) : Equation1595 G := λ x y z => h x y z z
theorem Equation1620_implies_Equation1596 (G : Type*) [Magma G] (h : Equation1620 G) : Equation1596 G := λ x y z => h x y z z
theorem Equation1621_implies_Equation1596 (G : Type*) [Magma G] (h : Equation1621 G) : Equation1596 G := λ x y z => h x y z z
theorem Equation1643_implies_Equation1642 (G : Type*) [Magma G] (h : Equation1643 G) : Equation1642 G := λ x y z => h x y z z
theorem Equation1653_implies_Equation1652 (G : Type*) [Magma G] (h : Equation1653 G) : Equation1652 G := λ x y z => h x y z z
theorem Equation1663_implies_Equation1662 (G : Type*) [Magma G] (h : Equation1663 G) : Equation1662 G := λ x y z => h x y z z
theorem Equation1667_implies_Equation1666 (G : Type*) [Magma G] (h : Equation1667 G) : Equation1666 G := λ x y z => h x y z z
theorem Equation1671_implies_Equation1670 (G : Type*) [Magma G] (h : Equation1671 G) : Equation1670 G := λ x y z => h x y z z
theorem Equation1675_implies_Equation1674 (G : Type*) [Magma G] (h : Equation1675 G) : Equation1674 G := λ x y z => h x y z z
theorem Equation1676_implies_Equation1672 (G : Type*) [Magma G] (h : Equation1676 G) : Equation1672 G := λ x y z => h x y z z
theorem Equation1677_implies_Equation1673 (G : Type*) [Magma G] (h : Equation1677 G) : Equation1673 G := λ x y z => h x y z z
theorem Equation1678_implies_Equation1674 (G : Type*) [Magma G] (h : Equation1678 G) : Equation1674 G := λ x y z => h x y z z
theorem Equation1679_implies_Equation1674 (G : Type*) [Magma G] (h : Equation1679 G) : Equation1674 G := λ x y z => h x y z z
theorem Equation1690_implies_Equation1689 (G : Type*) [Magma G] (h : Equation1690 G) : Equation1689 G := λ x y z => h x y z z
theorem Equation1700_implies_Equation1699 (G : Type*) [Magma G] (h : Equation1700 G) : Equation1699 G := λ x y z => h x y z z
theorem Equation1704_implies_Equation1703 (G : Type*) [Magma G] (h : Equation1704 G) : Equation1703 G := λ x y z => h x y z z
theorem Equation1708_implies_Equation1707 (G : Type*) [Magma G] (h : Equation1708 G) : Equation1707 G := λ x y z => h x y z z
theorem Equation1712_implies_Equation1711 (G : Type*) [Magma G] (h : Equation1712 G) : Equation1711 G := λ x y z => h x y z z
theorem Equation1713_implies_Equation1709 (G : Type*) [Magma G] (h : Equation1713 G) : Equation1709 G := λ x y z => h x y z z
theorem Equation1714_implies_Equation1710 (G : Type*) [Magma G] (h : Equation1714 G) : Equation1710 G := λ x y z => h x y z z
theorem Equation1715_implies_Equation1711 (G : Type*) [Magma G] (h : Equation1715 G) : Equation1711 G := λ x y z => h x y z z
theorem Equation1716_implies_Equation1711 (G : Type*) [Magma G] (h : Equation1716 G) : Equation1711 G := λ x y z => h x y z z
theorem Equation1727_implies_Equation1726 (G : Type*) [Magma G] (h : Equation1727 G) : Equation1726 G := λ x y z => h x y z z
theorem Equation1737_implies_Equation1736 (G : Type*) [Magma G] (h : Equation1737 G) : Equation1736 G := λ x y z => h x y z z
theorem Equation1741_implies_Equation1740 (G : Type*) [Magma G] (h : Equation1741 G) : Equation1740 G := λ x y z => h x y z z
theorem Equation1745_implies_Equation1744 (G : Type*) [Magma G] (h : Equation1745 G) : Equation1744 G := λ x y z => h x y z z
theorem Equation1749_implies_Equation1748 (G : Type*) [Magma G] (h : Equation1749 G) : Equation1748 G := λ x y z => h x y z z
theorem Equation1750_implies_Equation1746 (G : Type*) [Magma G] (h : Equation1750 G) : Equation1746 G := λ x y z => h x y z z
theorem Equation1751_implies_Equation1747 (G : Type*) [Magma G] (h : Equation1751 G) : Equation1747 G := λ x y z => h x y z z
theorem Equation1752_implies_Equation1748 (G : Type*) [Magma G] (h : Equation1752 G) : Equation1748 G := λ x y z => h x y z z
theorem Equation1753_implies_Equation1748 (G : Type*) [Magma G] (h : Equation1753 G) : Equation1748 G := λ x y z => h x y z z
theorem Equation1758_implies_Equation1757 (G : Type*) [Magma G] (h : Equation1758 G) : Equation1757 G := λ x y z => h x y z z
theorem Equation1762_implies_Equation1761 (G : Type*) [Magma G] (h : Equation1762 G) : Equation1761 G := λ x y z => h x y z z
theorem Equation1766_implies_Equation1765 (G : Type*) [Magma G] (h : Equation1766 G) : Equation1765 G := λ x y z => h x y z z
theorem Equation1767_implies_Equation1763 (G : Type*) [Magma G] (h : Equation1767 G) : Equation1763 G := λ x y z => h x y z z
theorem Equation1768_implies_Equation1764 (G : Type*) [Magma G] (h : Equation1768 G) : Equation1764 G := λ x y z => h x y z z
theorem Equation1769_implies_Equation1765 (G : Type*) [Magma G] (h : Equation1769 G) : Equation1765 G := λ x y z => h x y z z
theorem Equation1770_implies_Equation1765 (G : Type*) [Magma G] (h : Equation1770 G) : Equation1765 G := λ x y z => h x y z z
theorem Equation1775_implies_Equation1774 (G : Type*) [Magma G] (h : Equation1775 G) : Equation1774 G := λ x y z => h x y z z
theorem Equation1779_implies_Equation1778 (G : Type*) [Magma G] (h : Equation1779 G) : Equation1778 G := λ x y z => h x y z z
theorem Equation1783_implies_Equation1782 (G : Type*) [Magma G] (h : Equation1783 G) : Equation1782 G := λ x y z => h x y z z
theorem Equation1784_implies_Equation1780 (G : Type*) [Magma G] (h : Equation1784 G) : Equation1780 G := λ x y z => h x y z z
theorem Equation1785_implies_Equation1781 (G : Type*) [Magma G] (h : Equation1785 G) : Equation1781 G := λ x y z => h x y z z
theorem Equation1786_implies_Equation1782 (G : Type*) [Magma G] (h : Equation1786 G) : Equation1782 G := λ x y z => h x y z z
theorem Equation1787_implies_Equation1782 (G : Type*) [Magma G] (h : Equation1787 G) : Equation1782 G := λ x y z => h x y z z
theorem Equation1792_implies_Equation1791 (G : Type*) [Magma G] (h : Equation1792 G) : Equation1791 G := λ x y z => h x y z z
theorem Equation1796_implies_Equation1795 (G : Type*) [Magma G] (h : Equation1796 G) : Equation1795 G := λ x y z => h x y z z
theorem Equation1800_implies_Equation1799 (G : Type*) [Magma G] (h : Equation1800 G) : Equation1799 G := λ x y z => h x y z z
theorem Equation1801_implies_Equation1797 (G : Type*) [Magma G] (h : Equation1801 G) : Equation1797 G := λ x y z => h x y z z
theorem Equation1802_implies_Equation1798 (G : Type*) [Magma G] (h : Equation1802 G) : Equation1798 G := λ x y z => h x y z z
theorem Equation1803_implies_Equation1799 (G : Type*) [Magma G] (h : Equation1803 G) : Equation1799 G := λ x y z => h x y z z
theorem Equation1804_implies_Equation1799 (G : Type*) [Magma G] (h : Equation1804 G) : Equation1799 G := λ x y z => h x y z z
theorem Equation1806_implies_Equation1789 (G : Type*) [Magma G] (h : Equation1806 G) : Equation1789 G := λ x y z => h x y z z
theorem Equation1807_implies_Equation1790 (G : Type*) [Magma G] (h : Equation1807 G) : Equation1790 G := λ x y z => h x y z z
theorem Equation1808_implies_Equation1791 (G : Type*) [Magma G] (h : Equation1808 G) : Equation1791 G := λ x y z => h x y z z
theorem Equation1809_implies_Equation1791 (G : Type*) [Magma G] (h : Equation1809 G) : Equation1791 G := λ x y z => h x y z z
theorem Equation1811_implies_Equation1793 (G : Type*) [Magma G] (h : Equation1811 G) : Equation1793 G := λ x y z => h x y z z
theorem Equation1812_implies_Equation1794 (G : Type*) [Magma G] (h : Equation1812 G) : Equation1794 G := λ x y z => h x y z z
theorem Equation1813_implies_Equation1795 (G : Type*) [Magma G] (h : Equation1813 G) : Equation1795 G := λ x y z => h x y z z
theorem Equation1814_implies_Equation1795 (G : Type*) [Magma G] (h : Equation1814 G) : Equation1795 G := λ x y z => h x y z z
theorem Equation1816_implies_Equation1797 (G : Type*) [Magma G] (h : Equation1816 G) : Equation1797 G := λ x y z => h x y z z
theorem Equation1817_implies_Equation1798 (G : Type*) [Magma G] (h : Equation1817 G) : Equation1798 G := λ x y z => h x y z z
theorem Equation1818_implies_Equation1799 (G : Type*) [Magma G] (h : Equation1818 G) : Equation1799 G := λ x y z => h x y z z
theorem Equation1819_implies_Equation1799 (G : Type*) [Magma G] (h : Equation1819 G) : Equation1799 G := λ x y z => h x y z z
theorem Equation1821_implies_Equation1797 (G : Type*) [Magma G] (h : Equation1821 G) : Equation1797 G := λ x y z => h x y z z
theorem Equation1822_implies_Equation1798 (G : Type*) [Magma G] (h : Equation1822 G) : Equation1798 G := λ x y z => h x y z z
theorem Equation1823_implies_Equation1799 (G : Type*) [Magma G] (h : Equation1823 G) : Equation1799 G := λ x y z => h x y z z
theorem Equation1824_implies_Equation1799 (G : Type*) [Magma G] (h : Equation1824 G) : Equation1799 G := λ x y z => h x y z z
theorem Equation1846_implies_Equation1845 (G : Type*) [Magma G] (h : Equation1846 G) : Equation1845 G := λ x y z => h x y z z
theorem Equation1856_implies_Equation1855 (G : Type*) [Magma G] (h : Equation1856 G) : Equation1855 G := λ x y z => h x y z z
theorem Equation1866_implies_Equation1865 (G : Type*) [Magma G] (h : Equation1866 G) : Equation1865 G := λ x y z => h x y z z
theorem Equation1870_implies_Equation1869 (G : Type*) [Magma G] (h : Equation1870 G) : Equation1869 G := λ x y z => h x y z z
theorem Equation1874_implies_Equation1873 (G : Type*) [Magma G] (h : Equation1874 G) : Equation1873 G := λ x y z => h x y z z
theorem Equation1878_implies_Equation1877 (G : Type*) [Magma G] (h : Equation1878 G) : Equation1877 G := λ x y z => h x y z z
theorem Equation1879_implies_Equation1875 (G : Type*) [Magma G] (h : Equation1879 G) : Equation1875 G := λ x y z => h x y z z
theorem Equation1880_implies_Equation1876 (G : Type*) [Magma G] (h : Equation1880 G) : Equation1876 G := λ x y z => h x y z z
theorem Equation1881_implies_Equation1877 (G : Type*) [Magma G] (h : Equation1881 G) : Equation1877 G := λ x y z => h x y z z
theorem Equation1882_implies_Equation1877 (G : Type*) [Magma G] (h : Equation1882 G) : Equation1877 G := λ x y z => h x y z z
theorem Equation1893_implies_Equation1892 (G : Type*) [Magma G] (h : Equation1893 G) : Equation1892 G := λ x y z => h x y z z
theorem Equation1903_implies_Equation1902 (G : Type*) [Magma G] (h : Equation1903 G) : Equation1902 G := λ x y z => h x y z z
theorem Equation1907_implies_Equation1906 (G : Type*) [Magma G] (h : Equation1907 G) : Equation1906 G := λ x y z => h x y z z
theorem Equation1911_implies_Equation1910 (G : Type*) [Magma G] (h : Equation1911 G) : Equation1910 G := λ x y z => h x y z z
theorem Equation1915_implies_Equation1914 (G : Type*) [Magma G] (h : Equation1915 G) : Equation1914 G := λ x y z => h x y z z
theorem Equation1916_implies_Equation1912 (G : Type*) [Magma G] (h : Equation1916 G) : Equation1912 G := λ x y z => h x y z z
theorem Equation1917_implies_Equation1913 (G : Type*) [Magma G] (h : Equation1917 G) : Equation1913 G := λ x y z => h x y z z
theorem Equation1918_implies_Equation1914 (G : Type*) [Magma G] (h : Equation1918 G) : Equation1914 G := λ x y z => h x y z z
theorem Equation1919_implies_Equation1914 (G : Type*) [Magma G] (h : Equation1919 G) : Equation1914 G := λ x y z => h x y z z
theorem Equation1930_implies_Equation1929 (G : Type*) [Magma G] (h : Equation1930 G) : Equation1929 G := λ x y z => h x y z z
theorem Equation1940_implies_Equation1939 (G : Type*) [Magma G] (h : Equation1940 G) : Equation1939 G := λ x y z => h x y z z
theorem Equation1944_implies_Equation1943 (G : Type*) [Magma G] (h : Equation1944 G) : Equation1943 G := λ x y z => h x y z z
theorem Equation1948_implies_Equation1947 (G : Type*) [Magma G] (h : Equation1948 G) : Equation1947 G := λ x y z => h x y z z
theorem Equation1952_implies_Equation1951 (G : Type*) [Magma G] (h : Equation1952 G) : Equation1951 G := λ x y z => h x y z z
theorem Equation1953_implies_Equation1949 (G : Type*) [Magma G] (h : Equation1953 G) : Equation1949 G := λ x y z => h x y z z
theorem Equation1954_implies_Equation1950 (G : Type*) [Magma G] (h : Equation1954 G) : Equation1950 G := λ x y z => h x y z z
theorem Equation1955_implies_Equation1951 (G : Type*) [Magma G] (h : Equation1955 G) : Equation1951 G := λ x y z => h x y z z
theorem Equation1956_implies_Equation1951 (G : Type*) [Magma G] (h : Equation1956 G) : Equation1951 G := λ x y z => h x y z z
theorem Equation1961_implies_Equation1960 (G : Type*) [Magma G] (h : Equation1961 G) : Equation1960 G := λ x y z => h x y z z
theorem Equation1965_implies_Equation1964 (G : Type*) [Magma G] (h : Equation1965 G) : Equation1964 G := λ x y z => h x y z z
theorem Equation1969_implies_Equation1968 (G : Type*) [Magma G] (h : Equation1969 G) : Equation1968 G := λ x y z => h x y z z
theorem Equation1970_implies_Equation1966 (G : Type*) [Magma G] (h : Equation1970 G) : Equation1966 G := λ x y z => h x y z z
theorem Equation1971_implies_Equation1967 (G : Type*) [Magma G] (h : Equation1971 G) : Equation1967 G := λ x y z => h x y z z
theorem Equation1972_implies_Equation1968 (G : Type*) [Magma G] (h : Equation1972 G) : Equation1968 G := λ x y z => h x y z z
theorem Equation1973_implies_Equation1968 (G : Type*) [Magma G] (h : Equation1973 G) : Equation1968 G := λ x y z => h x y z z
theorem Equation1978_implies_Equation1977 (G : Type*) [Magma G] (h : Equation1978 G) : Equation1977 G := λ x y z => h x y z z
theorem Equation1982_implies_Equation1981 (G : Type*) [Magma G] (h : Equation1982 G) : Equation1981 G := λ x y z => h x y z z
theorem Equation1986_implies_Equation1985 (G : Type*) [Magma G] (h : Equation1986 G) : Equation1985 G := λ x y z => h x y z z
theorem Equation1987_implies_Equation1983 (G : Type*) [Magma G] (h : Equation1987 G) : Equation1983 G := λ x y z => h x y z z
theorem Equation1988_implies_Equation1984 (G : Type*) [Magma G] (h : Equation1988 G) : Equation1984 G := λ x y z => h x y z z
theorem Equation1989_implies_Equation1985 (G : Type*) [Magma G] (h : Equation1989 G) : Equation1985 G := λ x y z => h x y z z
theorem Equation1990_implies_Equation1985 (G : Type*) [Magma G] (h : Equation1990 G) : Equation1985 G := λ x y z => h x y z z
theorem Equation1995_implies_Equation1994 (G : Type*) [Magma G] (h : Equation1995 G) : Equation1994 G := λ x y z => h x y z z
theorem Equation1999_implies_Equation1998 (G : Type*) [Magma G] (h : Equation1999 G) : Equation1998 G := λ x y z => h x y z z
theorem Equation2003_implies_Equation2002 (G : Type*) [Magma G] (h : Equation2003 G) : Equation2002 G := λ x y z => h x y z z
theorem Equation2004_implies_Equation2000 (G : Type*) [Magma G] (h : Equation2004 G) : Equation2000 G := λ x y z => h x y z z
theorem Equation2005_implies_Equation2001 (G : Type*) [Magma G] (h : Equation2005 G) : Equation2001 G := λ x y z => h x y z z
theorem Equation2006_implies_Equation2002 (G : Type*) [Magma G] (h : Equation2006 G) : Equation2002 G := λ x y z => h x y z z
theorem Equation2007_implies_Equation2002 (G : Type*) [Magma G] (h : Equation2007 G) : Equation2002 G := λ x y z => h x y z z
theorem Equation2009_implies_Equation1992 (G : Type*) [Magma G] (h : Equation2009 G) : Equation1992 G := λ x y z => h x y z z
theorem Equation2010_implies_Equation1993 (G : Type*) [Magma G] (h : Equation2010 G) : Equation1993 G := λ x y z => h x y z z
theorem Equation2011_implies_Equation1994 (G : Type*) [Magma G] (h : Equation2011 G) : Equation1994 G := λ x y z => h x y z z
theorem Equation2012_implies_Equation1994 (G : Type*) [Magma G] (h : Equation2012 G) : Equation1994 G := λ x y z => h x y z z
theorem Equation2014_implies_Equation1996 (G : Type*) [Magma G] (h : Equation2014 G) : Equation1996 G := λ x y z => h x y z z
theorem Equation2015_implies_Equation1997 (G : Type*) [Magma G] (h : Equation2015 G) : Equation1997 G := λ x y z => h x y z z
theorem Equation2016_implies_Equation1998 (G : Type*) [Magma G] (h : Equation2016 G) : Equation1998 G := λ x y z => h x y z z
theorem Equation2017_implies_Equation1998 (G : Type*) [Magma G] (h : Equation2017 G) : Equation1998 G := λ x y z => h x y z z
theorem Equation2019_implies_Equation2000 (G : Type*) [Magma G] (h : Equation2019 G) : Equation2000 G := λ x y z => h x y z z
theorem Equation2020_implies_Equation2001 (G : Type*) [Magma G] (h : Equation2020 G) : Equation2001 G := λ x y z => h x y z z
theorem Equation2021_implies_Equation2002 (G : Type*) [Magma G] (h : Equation2021 G) : Equation2002 G := λ x y z => h x y z z
theorem Equation2022_implies_Equation2002 (G : Type*) [Magma G] (h : Equation2022 G) : Equation2002 G := λ x y z => h x y z z
theorem Equation2024_implies_Equation2000 (G : Type*) [Magma G] (h : Equation2024 G) : Equation2000 G := λ x y z => h x y z z
theorem Equation2025_implies_Equation2001 (G : Type*) [Magma G] (h : Equation2025 G) : Equation2001 G := λ x y z => h x y z z
theorem Equation2026_implies_Equation2002 (G : Type*) [Magma G] (h : Equation2026 G) : Equation2002 G := λ x y z => h x y z z
theorem Equation2027_implies_Equation2002 (G : Type*) [Magma G] (h : Equation2027 G) : Equation2002 G := λ x y z => h x y z z
theorem Equation2049_implies_Equation2048 (G : Type*) [Magma G] (h : Equation2049 G) : Equation2048 G := λ x y z => h x y z z
theorem Equation2059_implies_Equation2058 (G : Type*) [Magma G] (h : Equation2059 G) : Equation2058 G := λ x y z => h x y z z
theorem Equation2069_implies_Equation2068 (G : Type*) [Magma G] (h : Equation2069 G) : Equation2068 G := λ x y z => h x y z z
theorem Equation2073_implies_Equation2072 (G : Type*) [Magma G] (h : Equation2073 G) : Equation2072 G := λ x y z => h x y z z
theorem Equation2077_implies_Equation2076 (G : Type*) [Magma G] (h : Equation2077 G) : Equation2076 G := λ x y z => h x y z z
theorem Equation2081_implies_Equation2080 (G : Type*) [Magma G] (h : Equation2081 G) : Equation2080 G := λ x y z => h x y z z
theorem Equation2082_implies_Equation2078 (G : Type*) [Magma G] (h : Equation2082 G) : Equation2078 G := λ x y z => h x y z z
theorem Equation2083_implies_Equation2079 (G : Type*) [Magma G] (h : Equation2083 G) : Equation2079 G := λ x y z => h x y z z
theorem Equation2084_implies_Equation2080 (G : Type*) [Magma G] (h : Equation2084 G) : Equation2080 G := λ x y z => h x y z z
theorem Equation2085_implies_Equation2080 (G : Type*) [Magma G] (h : Equation2085 G) : Equation2080 G := λ x y z => h x y z z
theorem Equation2096_implies_Equation2095 (G : Type*) [Magma G] (h : Equation2096 G) : Equation2095 G := λ x y z => h x y z z
theorem Equation2106_implies_Equation2105 (G : Type*) [Magma G] (h : Equation2106 G) : Equation2105 G := λ x y z => h x y z z
theorem Equation2110_implies_Equation2109 (G : Type*) [Magma G] (h : Equation2110 G) : Equation2109 G := λ x y z => h x y z z
theorem Equation2114_implies_Equation2113 (G : Type*) [Magma G] (h : Equation2114 G) : Equation2113 G := λ x y z => h x y z z
theorem Equation2118_implies_Equation2117 (G : Type*) [Magma G] (h : Equation2118 G) : Equation2117 G := λ x y z => h x y z z
theorem Equation2119_implies_Equation2115 (G : Type*) [Magma G] (h : Equation2119 G) : Equation2115 G := λ x y z => h x y z z
theorem Equation2120_implies_Equation2116 (G : Type*) [Magma G] (h : Equation2120 G) : Equation2116 G := λ x y z => h x y z z
theorem Equation2121_implies_Equation2117 (G : Type*) [Magma G] (h : Equation2121 G) : Equation2117 G := λ x y z => h x y z z
theorem Equation2122_implies_Equation2117 (G : Type*) [Magma G] (h : Equation2122 G) : Equation2117 G := λ x y z => h x y z z
theorem Equation2133_implies_Equation2132 (G : Type*) [Magma G] (h : Equation2133 G) : Equation2132 G := λ x y z => h x y z z
theorem Equation2143_implies_Equation2142 (G : Type*) [Magma G] (h : Equation2143 G) : Equation2142 G := λ x y z => h x y z z
theorem Equation2147_implies_Equation2146 (G : Type*) [Magma G] (h : Equation2147 G) : Equation2146 G := λ x y z => h x y z z
theorem Equation2151_implies_Equation2150 (G : Type*) [Magma G] (h : Equation2151 G) : Equation2150 G := λ x y z => h x y z z
theorem Equation2155_implies_Equation2154 (G : Type*) [Magma G] (h : Equation2155 G) : Equation2154 G := λ x y z => h x y z z
theorem Equation2156_implies_Equation2152 (G : Type*) [Magma G] (h : Equation2156 G) : Equation2152 G := λ x y z => h x y z z
theorem Equation2157_implies_Equation2153 (G : Type*) [Magma G] (h : Equation2157 G) : Equation2153 G := λ x y z => h x y z z
theorem Equation2158_implies_Equation2154 (G : Type*) [Magma G] (h : Equation2158 G) : Equation2154 G := λ x y z => h x y z z
theorem Equation2159_implies_Equation2154 (G : Type*) [Magma G] (h : Equation2159 G) : Equation2154 G := λ x y z => h x y z z
theorem Equation2164_implies_Equation2163 (G : Type*) [Magma G] (h : Equation2164 G) : Equation2163 G := λ x y z => h x y z z
theorem Equation2168_implies_Equation2167 (G : Type*) [Magma G] (h : Equation2168 G) : Equation2167 G := λ x y z => h x y z z
theorem Equation2172_implies_Equation2171 (G : Type*) [Magma G] (h : Equation2172 G) : Equation2171 G := λ x y z => h x y z z
theorem Equation2173_implies_Equation2169 (G : Type*) [Magma G] (h : Equation2173 G) : Equation2169 G := λ x y z => h x y z z
theorem Equation2174_implies_Equation2170 (G : Type*) [Magma G] (h : Equation2174 G) : Equation2170 G := λ x y z => h x y z z
theorem Equation2175_implies_Equation2171 (G : Type*) [Magma G] (h : Equation2175 G) : Equation2171 G := λ x y z => h x y z z
theorem Equation2176_implies_Equation2171 (G : Type*) [Magma G] (h : Equation2176 G) : Equation2171 G := λ x y z => h x y z z
theorem Equation2181_implies_Equation2180 (G : Type*) [Magma G] (h : Equation2181 G) : Equation2180 G := λ x y z => h x y z z
theorem Equation2185_implies_Equation2184 (G : Type*) [Magma G] (h : Equation2185 G) : Equation2184 G := λ x y z => h x y z z
theorem Equation2189_implies_Equation2188 (G : Type*) [Magma G] (h : Equation2189 G) : Equation2188 G := λ x y z => h x y z z
theorem Equation2190_implies_Equation2186 (G : Type*) [Magma G] (h : Equation2190 G) : Equation2186 G := λ x y z => h x y z z
theorem Equation2191_implies_Equation2187 (G : Type*) [Magma G] (h : Equation2191 G) : Equation2187 G := λ x y z => h x y z z
theorem Equation2192_implies_Equation2188 (G : Type*) [Magma G] (h : Equation2192 G) : Equation2188 G := λ x y z => h x y z z
theorem Equation2193_implies_Equation2188 (G : Type*) [Magma G] (h : Equation2193 G) : Equation2188 G := λ x y z => h x y z z
theorem Equation2198_implies_Equation2197 (G : Type*) [Magma G] (h : Equation2198 G) : Equation2197 G := λ x y z => h x y z z
theorem Equation2202_implies_Equation2201 (G : Type*) [Magma G] (h : Equation2202 G) : Equation2201 G := λ x y z => h x y z z
theorem Equation2206_implies_Equation2205 (G : Type*) [Magma G] (h : Equation2206 G) : Equation2205 G := λ x y z => h x y z z
theorem Equation2207_implies_Equation2203 (G : Type*) [Magma G] (h : Equation2207 G) : Equation2203 G := λ x y z => h x y z z
theorem Equation2208_implies_Equation2204 (G : Type*) [Magma G] (h : Equation2208 G) : Equation2204 G := λ x y z => h x y z z
theorem Equation2209_implies_Equation2205 (G : Type*) [Magma G] (h : Equation2209 G) : Equation2205 G := λ x y z => h x y z z
theorem Equation2210_implies_Equation2205 (G : Type*) [Magma G] (h : Equation2210 G) : Equation2205 G := λ x y z => h x y z z
theorem Equation2212_implies_Equation2195 (G : Type*) [Magma G] (h : Equation2212 G) : Equation2195 G := λ x y z => h x y z z
theorem Equation2213_implies_Equation2196 (G : Type*) [Magma G] (h : Equation2213 G) : Equation2196 G := λ x y z => h x y z z
theorem Equation2214_implies_Equation2197 (G : Type*) [Magma G] (h : Equation2214 G) : Equation2197 G := λ x y z => h x y z z
theorem Equation2215_implies_Equation2197 (G : Type*) [Magma G] (h : Equation2215 G) : Equation2197 G := λ x y z => h x y z z
theorem Equation2217_implies_Equation2199 (G : Type*) [Magma G] (h : Equation2217 G) : Equation2199 G := λ x y z => h x y z z
theorem Equation2218_implies_Equation2200 (G : Type*) [Magma G] (h : Equation2218 G) : Equation2200 G := λ x y z => h x y z z
theorem Equation2219_implies_Equation2201 (G : Type*) [Magma G] (h : Equation2219 G) : Equation2201 G := λ x y z => h x y z z
theorem Equation2220_implies_Equation2201 (G : Type*) [Magma G] (h : Equation2220 G) : Equation2201 G := λ x y z => h x y z z
theorem Equation2222_implies_Equation2203 (G : Type*) [Magma G] (h : Equation2222 G) : Equation2203 G := λ x y z => h x y z z
theorem Equation2223_implies_Equation2204 (G : Type*) [Magma G] (h : Equation2223 G) : Equation2204 G := λ x y z => h x y z z
theorem Equation2224_implies_Equation2205 (G : Type*) [Magma G] (h : Equation2224 G) : Equation2205 G := λ x y z => h x y z z
theorem Equation2225_implies_Equation2205 (G : Type*) [Magma G] (h : Equation2225 G) : Equation2205 G := λ x y z => h x y z z
theorem Equation2227_implies_Equation2203 (G : Type*) [Magma G] (h : Equation2227 G) : Equation2203 G := λ x y z => h x y z z
theorem Equation2228_implies_Equation2204 (G : Type*) [Magma G] (h : Equation2228 G) : Equation2204 G := λ x y z => h x y z z
theorem Equation2229_implies_Equation2205 (G : Type*) [Magma G] (h : Equation2229 G) : Equation2205 G := λ x y z => h x y z z
theorem Equation2230_implies_Equation2205 (G : Type*) [Magma G] (h : Equation2230 G) : Equation2205 G := λ x y z => h x y z z
theorem Equation2252_implies_Equation2251 (G : Type*) [Magma G] (h : Equation2252 G) : Equation2251 G := λ x y z => h x y z z
theorem Equation2262_implies_Equation2261 (G : Type*) [Magma G] (h : Equation2262 G) : Equation2261 G := λ x y z => h x y z z
theorem Equation2272_implies_Equation2271 (G : Type*) [Magma G] (h : Equation2272 G) : Equation2271 G := λ x y z => h x y z z
theorem Equation2276_implies_Equation2275 (G : Type*) [Magma G] (h : Equation2276 G) : Equation2275 G := λ x y z => h x y z z
theorem Equation2280_implies_Equation2279 (G : Type*) [Magma G] (h : Equation2280 G) : Equation2279 G := λ x y z => h x y z z
theorem Equation2284_implies_Equation2283 (G : Type*) [Magma G] (h : Equation2284 G) : Equation2283 G := λ x y z => h x y z z
theorem Equation2285_implies_Equation2281 (G : Type*) [Magma G] (h : Equation2285 G) : Equation2281 G := λ x y z => h x y z z
theorem Equation2286_implies_Equation2282 (G : Type*) [Magma G] (h : Equation2286 G) : Equation2282 G := λ x y z => h x y z z
theorem Equation2287_implies_Equation2283 (G : Type*) [Magma G] (h : Equation2287 G) : Equation2283 G := λ x y z => h x y z z
theorem Equation2288_implies_Equation2283 (G : Type*) [Magma G] (h : Equation2288 G) : Equation2283 G := λ x y z => h x y z z
theorem Equation2299_implies_Equation2298 (G : Type*) [Magma G] (h : Equation2299 G) : Equation2298 G := λ x y z => h x y z z
theorem Equation2309_implies_Equation2308 (G : Type*) [Magma G] (h : Equation2309 G) : Equation2308 G := λ x y z => h x y z z
theorem Equation2313_implies_Equation2312 (G : Type*) [Magma G] (h : Equation2313 G) : Equation2312 G := λ x y z => h x y z z
theorem Equation2317_implies_Equation2316 (G : Type*) [Magma G] (h : Equation2317 G) : Equation2316 G := λ x y z => h x y z z
theorem Equation2321_implies_Equation2320 (G : Type*) [Magma G] (h : Equation2321 G) : Equation2320 G := λ x y z => h x y z z
theorem Equation2322_implies_Equation2318 (G : Type*) [Magma G] (h : Equation2322 G) : Equation2318 G := λ x y z => h x y z z
theorem Equation2323_implies_Equation2319 (G : Type*) [Magma G] (h : Equation2323 G) : Equation2319 G := λ x y z => h x y z z
theorem Equation2324_implies_Equation2320 (G : Type*) [Magma G] (h : Equation2324 G) : Equation2320 G := λ x y z => h x y z z
theorem Equation2325_implies_Equation2320 (G : Type*) [Magma G] (h : Equation2325 G) : Equation2320 G := λ x y z => h x y z z
theorem Equation2336_implies_Equation2335 (G : Type*) [Magma G] (h : Equation2336 G) : Equation2335 G := λ x y z => h x y z z
theorem Equation2346_implies_Equation2345 (G : Type*) [Magma G] (h : Equation2346 G) : Equation2345 G := λ x y z => h x y z z
theorem Equation2350_implies_Equation2349 (G : Type*) [Magma G] (h : Equation2350 G) : Equation2349 G := λ x y z => h x y z z
theorem Equation2354_implies_Equation2353 (G : Type*) [Magma G] (h : Equation2354 G) : Equation2353 G := λ x y z => h x y z z
theorem Equation2358_implies_Equation2357 (G : Type*) [Magma G] (h : Equation2358 G) : Equation2357 G := λ x y z => h x y z z
theorem Equation2359_implies_Equation2355 (G : Type*) [Magma G] (h : Equation2359 G) : Equation2355 G := λ x y z => h x y z z
theorem Equation2360_implies_Equation2356 (G : Type*) [Magma G] (h : Equation2360 G) : Equation2356 G := λ x y z => h x y z z
theorem Equation2361_implies_Equation2357 (G : Type*) [Magma G] (h : Equation2361 G) : Equation2357 G := λ x y z => h x y z z
theorem Equation2362_implies_Equation2357 (G : Type*) [Magma G] (h : Equation2362 G) : Equation2357 G := λ x y z => h x y z z
theorem Equation2367_implies_Equation2366 (G : Type*) [Magma G] (h : Equation2367 G) : Equation2366 G := λ x y z => h x y z z
theorem Equation2371_implies_Equation2370 (G : Type*) [Magma G] (h : Equation2371 G) : Equation2370 G := λ x y z => h x y z z
theorem Equation2375_implies_Equation2374 (G : Type*) [Magma G] (h : Equation2375 G) : Equation2374 G := λ x y z => h x y z z
theorem Equation2376_implies_Equation2372 (G : Type*) [Magma G] (h : Equation2376 G) : Equation2372 G := λ x y z => h x y z z
theorem Equation2377_implies_Equation2373 (G : Type*) [Magma G] (h : Equation2377 G) : Equation2373 G := λ x y z => h x y z z
theorem Equation2378_implies_Equation2374 (G : Type*) [Magma G] (h : Equation2378 G) : Equation2374 G := λ x y z => h x y z z
theorem Equation2379_implies_Equation2374 (G : Type*) [Magma G] (h : Equation2379 G) : Equation2374 G := λ x y z => h x y z z
theorem Equation2384_implies_Equation2383 (G : Type*) [Magma G] (h : Equation2384 G) : Equation2383 G := λ x y z => h x y z z
theorem Equation2388_implies_Equation2387 (G : Type*) [Magma G] (h : Equation2388 G) : Equation2387 G := λ x y z => h x y z z
theorem Equation2392_implies_Equation2391 (G : Type*) [Magma G] (h : Equation2392 G) : Equation2391 G := λ x y z => h x y z z
theorem Equation2393_implies_Equation2389 (G : Type*) [Magma G] (h : Equation2393 G) : Equation2389 G := λ x y z => h x y z z
theorem Equation2394_implies_Equation2390 (G : Type*) [Magma G] (h : Equation2394 G) : Equation2390 G := λ x y z => h x y z z
theorem Equation2395_implies_Equation2391 (G : Type*) [Magma G] (h : Equation2395 G) : Equation2391 G := λ x y z => h x y z z
theorem Equation2396_implies_Equation2391 (G : Type*) [Magma G] (h : Equation2396 G) : Equation2391 G := λ x y z => h x y z z
theorem Equation2401_implies_Equation2400 (G : Type*) [Magma G] (h : Equation2401 G) : Equation2400 G := λ x y z => h x y z z
theorem Equation2405_implies_Equation2404 (G : Type*) [Magma G] (h : Equation2405 G) : Equation2404 G := λ x y z => h x y z z
theorem Equation2409_implies_Equation2408 (G : Type*) [Magma G] (h : Equation2409 G) : Equation2408 G := λ x y z => h x y z z
theorem Equation2410_implies_Equation2406 (G : Type*) [Magma G] (h : Equation2410 G) : Equation2406 G := λ x y z => h x y z z
theorem Equation2411_implies_Equation2407 (G : Type*) [Magma G] (h : Equation2411 G) : Equation2407 G := λ x y z => h x y z z
theorem Equation2412_implies_Equation2408 (G : Type*) [Magma G] (h : Equation2412 G) : Equation2408 G := λ x y z => h x y z z
theorem Equation2413_implies_Equation2408 (G : Type*) [Magma G] (h : Equation2413 G) : Equation2408 G := λ x y z => h x y z z
theorem Equation2415_implies_Equation2398 (G : Type*) [Magma G] (h : Equation2415 G) : Equation2398 G := λ x y z => h x y z z
theorem Equation2416_implies_Equation2399 (G : Type*) [Magma G] (h : Equation2416 G) : Equation2399 G := λ x y z => h x y z z
theorem Equation2417_implies_Equation2400 (G : Type*) [Magma G] (h : Equation2417 G) : Equation2400 G := λ x y z => h x y z z
theorem Equation2418_implies_Equation2400 (G : Type*) [Magma G] (h : Equation2418 G) : Equation2400 G := λ x y z => h x y z z
theorem Equation2420_implies_Equation2402 (G : Type*) [Magma G] (h : Equation2420 G) : Equation2402 G := λ x y z => h x y z z
theorem Equation2421_implies_Equation2403 (G : Type*) [Magma G] (h : Equation2421 G) : Equation2403 G := λ x y z => h x y z z
theorem Equation2422_implies_Equation2404 (G : Type*) [Magma G] (h : Equation2422 G) : Equation2404 G := λ x y z => h x y z z
theorem Equation2423_implies_Equation2404 (G : Type*) [Magma G] (h : Equation2423 G) : Equation2404 G := λ x y z => h x y z z
theorem Equation2425_implies_Equation2406 (G : Type*) [Magma G] (h : Equation2425 G) : Equation2406 G := λ x y z => h x y z z
theorem Equation2426_implies_Equation2407 (G : Type*) [Magma G] (h : Equation2426 G) : Equation2407 G := λ x y z => h x y z z
theorem Equation2427_implies_Equation2408 (G : Type*) [Magma G] (h : Equation2427 G) : Equation2408 G := λ x y z => h x y z z
theorem Equation2428_implies_Equation2408 (G : Type*) [Magma G] (h : Equation2428 G) : Equation2408 G := λ x y z => h x y z z
theorem Equation2430_implies_Equation2406 (G : Type*) [Magma G] (h : Equation2430 G) : Equation2406 G := λ x y z => h x y z z
theorem Equation2431_implies_Equation2407 (G : Type*) [Magma G] (h : Equation2431 G) : Equation2407 G := λ x y z => h x y z z
theorem Equation2432_implies_Equation2408 (G : Type*) [Magma G] (h : Equation2432 G) : Equation2408 G := λ x y z => h x y z z
theorem Equation2433_implies_Equation2408 (G : Type*) [Magma G] (h : Equation2433 G) : Equation2408 G := λ x y z => h x y z z
theorem Equation2455_implies_Equation2454 (G : Type*) [Magma G] (h : Equation2455 G) : Equation2454 G := λ x y z => h x y z z
theorem Equation2465_implies_Equation2464 (G : Type*) [Magma G] (h : Equation2465 G) : Equation2464 G := λ x y z => h x y z z
theorem Equation2475_implies_Equation2474 (G : Type*) [Magma G] (h : Equation2475 G) : Equation2474 G := λ x y z => h x y z z
theorem Equation2479_implies_Equation2478 (G : Type*) [Magma G] (h : Equation2479 G) : Equation2478 G := λ x y z => h x y z z
theorem Equation2483_implies_Equation2482 (G : Type*) [Magma G] (h : Equation2483 G) : Equation2482 G := λ x y z => h x y z z
theorem Equation2487_implies_Equation2486 (G : Type*) [Magma G] (h : Equation2487 G) : Equation2486 G := λ x y z => h x y z z
theorem Equation2488_implies_Equation2484 (G : Type*) [Magma G] (h : Equation2488 G) : Equation2484 G := λ x y z => h x y z z
theorem Equation2489_implies_Equation2485 (G : Type*) [Magma G] (h : Equation2489 G) : Equation2485 G := λ x y z => h x y z z
theorem Equation2490_implies_Equation2486 (G : Type*) [Magma G] (h : Equation2490 G) : Equation2486 G := λ x y z => h x y z z
theorem Equation2491_implies_Equation2486 (G : Type*) [Magma G] (h : Equation2491 G) : Equation2486 G := λ x y z => h x y z z
theorem Equation2502_implies_Equation2501 (G : Type*) [Magma G] (h : Equation2502 G) : Equation2501 G := λ x y z => h x y z z
theorem Equation2512_implies_Equation2511 (G : Type*) [Magma G] (h : Equation2512 G) : Equation2511 G := λ x y z => h x y z z
theorem Equation2516_implies_Equation2515 (G : Type*) [Magma G] (h : Equation2516 G) : Equation2515 G := λ x y z => h x y z z
theorem Equation2520_implies_Equation2519 (G : Type*) [Magma G] (h : Equation2520 G) : Equation2519 G := λ x y z => h x y z z
theorem Equation2524_implies_Equation2523 (G : Type*) [Magma G] (h : Equation2524 G) : Equation2523 G := λ x y z => h x y z z
theorem Equation2525_implies_Equation2521 (G : Type*) [Magma G] (h : Equation2525 G) : Equation2521 G := λ x y z => h x y z z
theorem Equation2526_implies_Equation2522 (G : Type*) [Magma G] (h : Equation2526 G) : Equation2522 G := λ x y z => h x y z z
theorem Equation2527_implies_Equation2523 (G : Type*) [Magma G] (h : Equation2527 G) : Equation2523 G := λ x y z => h x y z z
theorem Equation2528_implies_Equation2523 (G : Type*) [Magma G] (h : Equation2528 G) : Equation2523 G := λ x y z => h x y z z
theorem Equation2539_implies_Equation2538 (G : Type*) [Magma G] (h : Equation2539 G) : Equation2538 G := λ x y z => h x y z z
theorem Equation2549_implies_Equation2548 (G : Type*) [Magma G] (h : Equation2549 G) : Equation2548 G := λ x y z => h x y z z
theorem Equation2553_implies_Equation2552 (G : Type*) [Magma G] (h : Equation2553 G) : Equation2552 G := λ x y z => h x y z z
theorem Equation2557_implies_Equation2556 (G : Type*) [Magma G] (h : Equation2557 G) : Equation2556 G := λ x y z => h x y z z
theorem Equation2561_implies_Equation2560 (G : Type*) [Magma G] (h : Equation2561 G) : Equation2560 G := λ x y z => h x y z z
theorem Equation2562_implies_Equation2558 (G : Type*) [Magma G] (h : Equation2562 G) : Equation2558 G := λ x y z => h x y z z
theorem Equation2563_implies_Equation2559 (G : Type*) [Magma G] (h : Equation2563 G) : Equation2559 G := λ x y z => h x y z z
theorem Equation2564_implies_Equation2560 (G : Type*) [Magma G] (h : Equation2564 G) : Equation2560 G := λ x y z => h x y z z
theorem Equation2565_implies_Equation2560 (G : Type*) [Magma G] (h : Equation2565 G) : Equation2560 G := λ x y z => h x y z z
theorem Equation2570_implies_Equation2569 (G : Type*) [Magma G] (h : Equation2570 G) : Equation2569 G := λ x y z => h x y z z
theorem Equation2574_implies_Equation2573 (G : Type*) [Magma G] (h : Equation2574 G) : Equation2573 G := λ x y z => h x y z z
theorem Equation2578_implies_Equation2577 (G : Type*) [Magma G] (h : Equation2578 G) : Equation2577 G := λ x y z => h x y z z
theorem Equation2579_implies_Equation2575 (G : Type*) [Magma G] (h : Equation2579 G) : Equation2575 G := λ x y z => h x y z z
theorem Equation2580_implies_Equation2576 (G : Type*) [Magma G] (h : Equation2580 G) : Equation2576 G := λ x y z => h x y z z
theorem Equation2581_implies_Equation2577 (G : Type*) [Magma G] (h : Equation2581 G) : Equation2577 G := λ x y z => h x y z z
theorem Equation2582_implies_Equation2577 (G : Type*) [Magma G] (h : Equation2582 G) : Equation2577 G := λ x y z => h x y z z
theorem Equation2587_implies_Equation2586 (G : Type*) [Magma G] (h : Equation2587 G) : Equation2586 G := λ x y z => h x y z z
theorem Equation2591_implies_Equation2590 (G : Type*) [Magma G] (h : Equation2591 G) : Equation2590 G := λ x y z => h x y z z
theorem Equation2595_implies_Equation2594 (G : Type*) [Magma G] (h : Equation2595 G) : Equation2594 G := λ x y z => h x y z z
theorem Equation2596_implies_Equation2592 (G : Type*) [Magma G] (h : Equation2596 G) : Equation2592 G := λ x y z => h x y z z
theorem Equation2597_implies_Equation2593 (G : Type*) [Magma G] (h : Equation2597 G) : Equation2593 G := λ x y z => h x y z z
theorem Equation2598_implies_Equation2594 (G : Type*) [Magma G] (h : Equation2598 G) : Equation2594 G := λ x y z => h x y z z
theorem Equation2599_implies_Equation2594 (G : Type*) [Magma G] (h : Equation2599 G) : Equation2594 G := λ x y z => h x y z z
theorem Equation2604_implies_Equation2603 (G : Type*) [Magma G] (h : Equation2604 G) : Equation2603 G := λ x y z => h x y z z
theorem Equation2608_implies_Equation2607 (G : Type*) [Magma G] (h : Equation2608 G) : Equation2607 G := λ x y z => h x y z z
theorem Equation2612_implies_Equation2611 (G : Type*) [Magma G] (h : Equation2612 G) : Equation2611 G := λ x y z => h x y z z
theorem Equation2613_implies_Equation2609 (G : Type*) [Magma G] (h : Equation2613 G) : Equation2609 G := λ x y z => h x y z z
theorem Equation2614_implies_Equation2610 (G : Type*) [Magma G] (h : Equation2614 G) : Equation2610 G := λ x y z => h x y z z
theorem Equation2615_implies_Equation2611 (G : Type*) [Magma G] (h : Equation2615 G) : Equation2611 G := λ x y z => h x y z z
theorem Equation2616_implies_Equation2611 (G : Type*) [Magma G] (h : Equation2616 G) : Equation2611 G := λ x y z => h x y z z
theorem Equation2618_implies_Equation2601 (G : Type*) [Magma G] (h : Equation2618 G) : Equation2601 G := λ x y z => h x y z z
theorem Equation2619_implies_Equation2602 (G : Type*) [Magma G] (h : Equation2619 G) : Equation2602 G := λ x y z => h x y z z
theorem Equation2620_implies_Equation2603 (G : Type*) [Magma G] (h : Equation2620 G) : Equation2603 G := λ x y z => h x y z z
theorem Equation2621_implies_Equation2603 (G : Type*) [Magma G] (h : Equation2621 G) : Equation2603 G := λ x y z => h x y z z
theorem Equation2623_implies_Equation2605 (G : Type*) [Magma G] (h : Equation2623 G) : Equation2605 G := λ x y z => h x y z z
theorem Equation2624_implies_Equation2606 (G : Type*) [Magma G] (h : Equation2624 G) : Equation2606 G := λ x y z => h x y z z
theorem Equation2625_implies_Equation2607 (G : Type*) [Magma G] (h : Equation2625 G) : Equation2607 G := λ x y z => h x y z z
theorem Equation2626_implies_Equation2607 (G : Type*) [Magma G] (h : Equation2626 G) : Equation2607 G := λ x y z => h x y z z
theorem Equation2628_implies_Equation2609 (G : Type*) [Magma G] (h : Equation2628 G) : Equation2609 G := λ x y z => h x y z z
theorem Equation2629_implies_Equation2610 (G : Type*) [Magma G] (h : Equation2629 G) : Equation2610 G := λ x y z => h x y z z
theorem Equation2630_implies_Equation2611 (G : Type*) [Magma G] (h : Equation2630 G) : Equation2611 G := λ x y z => h x y z z
theorem Equation2631_implies_Equation2611 (G : Type*) [Magma G] (h : Equation2631 G) : Equation2611 G := λ x y z => h x y z z
theorem Equation2633_implies_Equation2609 (G : Type*) [Magma G] (h : Equation2633 G) : Equation2609 G := λ x y z => h x y z z
theorem Equation2634_implies_Equation2610 (G : Type*) [Magma G] (h : Equation2634 G) : Equation2610 G := λ x y z => h x y z z
theorem Equation2635_implies_Equation2611 (G : Type*) [Magma G] (h : Equation2635 G) : Equation2611 G := λ x y z => h x y z z
theorem Equation2636_implies_Equation2611 (G : Type*) [Magma G] (h : Equation2636 G) : Equation2611 G := λ x y z => h x y z z
theorem Equation2658_implies_Equation2657 (G : Type*) [Magma G] (h : Equation2658 G) : Equation2657 G := λ x y z => h x y z z
theorem Equation2668_implies_Equation2667 (G : Type*) [Magma G] (h : Equation2668 G) : Equation2667 G := λ x y z => h x y z z
theorem Equation2678_implies_Equation2677 (G : Type*) [Magma G] (h : Equation2678 G) : Equation2677 G := λ x y z => h x y z z
theorem Equation2682_implies_Equation2681 (G : Type*) [Magma G] (h : Equation2682 G) : Equation2681 G := λ x y z => h x y z z
theorem Equation2686_implies_Equation2685 (G : Type*) [Magma G] (h : Equation2686 G) : Equation2685 G := λ x y z => h x y z z
theorem Equation2690_implies_Equation2689 (G : Type*) [Magma G] (h : Equation2690 G) : Equation2689 G := λ x y z => h x y z z
theorem Equation2691_implies_Equation2687 (G : Type*) [Magma G] (h : Equation2691 G) : Equation2687 G := λ x y z => h x y z z
theorem Equation2692_implies_Equation2688 (G : Type*) [Magma G] (h : Equation2692 G) : Equation2688 G := λ x y z => h x y z z
theorem Equation2693_implies_Equation2689 (G : Type*) [Magma G] (h : Equation2693 G) : Equation2689 G := λ x y z => h x y z z
theorem Equation2694_implies_Equation2689 (G : Type*) [Magma G] (h : Equation2694 G) : Equation2689 G := λ x y z => h x y z z
theorem Equation2705_implies_Equation2704 (G : Type*) [Magma G] (h : Equation2705 G) : Equation2704 G := λ x y z => h x y z z
theorem Equation2715_implies_Equation2714 (G : Type*) [Magma G] (h : Equation2715 G) : Equation2714 G := λ x y z => h x y z z
theorem Equation2719_implies_Equation2718 (G : Type*) [Magma G] (h : Equation2719 G) : Equation2718 G := λ x y z => h x y z z
theorem Equation2723_implies_Equation2722 (G : Type*) [Magma G] (h : Equation2723 G) : Equation2722 G := λ x y z => h x y z z
theorem Equation2727_implies_Equation2726 (G : Type*) [Magma G] (h : Equation2727 G) : Equation2726 G := λ x y z => h x y z z
theorem Equation2728_implies_Equation2724 (G : Type*) [Magma G] (h : Equation2728 G) : Equation2724 G := λ x y z => h x y z z
theorem Equation2729_implies_Equation2725 (G : Type*) [Magma G] (h : Equation2729 G) : Equation2725 G := λ x y z => h x y z z
theorem Equation2730_implies_Equation2726 (G : Type*) [Magma G] (h : Equation2730 G) : Equation2726 G := λ x y z => h x y z z
theorem Equation2731_implies_Equation2726 (G : Type*) [Magma G] (h : Equation2731 G) : Equation2726 G := λ x y z => h x y z z
theorem Equation2742_implies_Equation2741 (G : Type*) [Magma G] (h : Equation2742 G) : Equation2741 G := λ x y z => h x y z z
theorem Equation2752_implies_Equation2751 (G : Type*) [Magma G] (h : Equation2752 G) : Equation2751 G := λ x y z => h x y z z
theorem Equation2756_implies_Equation2755 (G : Type*) [Magma G] (h : Equation2756 G) : Equation2755 G := λ x y z => h x y z z
theorem Equation2760_implies_Equation2759 (G : Type*) [Magma G] (h : Equation2760 G) : Equation2759 G := λ x y z => h x y z z
theorem Equation2764_implies_Equation2763 (G : Type*) [Magma G] (h : Equation2764 G) : Equation2763 G := λ x y z => h x y z z
theorem Equation2765_implies_Equation2761 (G : Type*) [Magma G] (h : Equation2765 G) : Equation2761 G := λ x y z => h x y z z
theorem Equation2766_implies_Equation2762 (G : Type*) [Magma G] (h : Equation2766 G) : Equation2762 G := λ x y z => h x y z z
theorem Equation2767_implies_Equation2763 (G : Type*) [Magma G] (h : Equation2767 G) : Equation2763 G := λ x y z => h x y z z
theorem Equation2768_implies_Equation2763 (G : Type*) [Magma G] (h : Equation2768 G) : Equation2763 G := λ x y z => h x y z z
theorem Equation2773_implies_Equation2772 (G : Type*) [Magma G] (h : Equation2773 G) : Equation2772 G := λ x y z => h x y z z
theorem Equation2777_implies_Equation2776 (G : Type*) [Magma G] (h : Equation2777 G) : Equation2776 G := λ x y z => h x y z z
theorem Equation2781_implies_Equation2780 (G : Type*) [Magma G] (h : Equation2781 G) : Equation2780 G := λ x y z => h x y z z
theorem Equation2782_implies_Equation2778 (G : Type*) [Magma G] (h : Equation2782 G) : Equation2778 G := λ x y z => h x y z z
theorem Equation2783_implies_Equation2779 (G : Type*) [Magma G] (h : Equation2783 G) : Equation2779 G := λ x y z => h x y z z
theorem Equation2784_implies_Equation2780 (G : Type*) [Magma G] (h : Equation2784 G) : Equation2780 G := λ x y z => h x y z z
theorem Equation2785_implies_Equation2780 (G : Type*) [Magma G] (h : Equation2785 G) : Equation2780 G := λ x y z => h x y z z
theorem Equation2790_implies_Equation2789 (G : Type*) [Magma G] (h : Equation2790 G) : Equation2789 G := λ x y z => h x y z z
theorem Equation2794_implies_Equation2793 (G : Type*) [Magma G] (h : Equation2794 G) : Equation2793 G := λ x y z => h x y z z
theorem Equation2798_implies_Equation2797 (G : Type*) [Magma G] (h : Equation2798 G) : Equation2797 G := λ x y z => h x y z z
theorem Equation2799_implies_Equation2795 (G : Type*) [Magma G] (h : Equation2799 G) : Equation2795 G := λ x y z => h x y z z
theorem Equation2800_implies_Equation2796 (G : Type*) [Magma G] (h : Equation2800 G) : Equation2796 G := λ x y z => h x y z z
theorem Equation2801_implies_Equation2797 (G : Type*) [Magma G] (h : Equation2801 G) : Equation2797 G := λ x y z => h x y z z
theorem Equation2802_implies_Equation2797 (G : Type*) [Magma G] (h : Equation2802 G) : Equation2797 G := λ x y z => h x y z z
theorem Equation2807_implies_Equation2806 (G : Type*) [Magma G] (h : Equation2807 G) : Equation2806 G := λ x y z => h x y z z
theorem Equation2811_implies_Equation2810 (G : Type*) [Magma G] (h : Equation2811 G) : Equation2810 G := λ x y z => h x y z z
theorem Equation2815_implies_Equation2814 (G : Type*) [Magma G] (h : Equation2815 G) : Equation2814 G := λ x y z => h x y z z
theorem Equation2816_implies_Equation2812 (G : Type*) [Magma G] (h : Equation2816 G) : Equation2812 G := λ x y z => h x y z z
theorem Equation2817_implies_Equation2813 (G : Type*) [Magma G] (h : Equation2817 G) : Equation2813 G := λ x y z => h x y z z
theorem Equation2818_implies_Equation2814 (G : Type*) [Magma G] (h : Equation2818 G) : Equation2814 G := λ x y z => h x y z z
theorem Equation2819_implies_Equation2814 (G : Type*) [Magma G] (h : Equation2819 G) : Equation2814 G := λ x y z => h x y z z
theorem Equation2821_implies_Equation2804 (G : Type*) [Magma G] (h : Equation2821 G) : Equation2804 G := λ x y z => h x y z z
theorem Equation2822_implies_Equation2805 (G : Type*) [Magma G] (h : Equation2822 G) : Equation2805 G := λ x y z => h x y z z
theorem Equation2823_implies_Equation2806 (G : Type*) [Magma G] (h : Equation2823 G) : Equation2806 G := λ x y z => h x y z z
theorem Equation2824_implies_Equation2806 (G : Type*) [Magma G] (h : Equation2824 G) : Equation2806 G := λ x y z => h x y z z
theorem Equation2826_implies_Equation2808 (G : Type*) [Magma G] (h : Equation2826 G) : Equation2808 G := λ x y z => h x y z z
theorem Equation2827_implies_Equation2809 (G : Type*) [Magma G] (h : Equation2827 G) : Equation2809 G := λ x y z => h x y z z
theorem Equation2828_implies_Equation2810 (G : Type*) [Magma G] (h : Equation2828 G) : Equation2810 G := λ x y z => h x y z z
theorem Equation2829_implies_Equation2810 (G : Type*) [Magma G] (h : Equation2829 G) : Equation2810 G := λ x y z => h x y z z
theorem Equation2831_implies_Equation2812 (G : Type*) [Magma G] (h : Equation2831 G) : Equation2812 G := λ x y z => h x y z z
theorem Equation2832_implies_Equation2813 (G : Type*) [Magma G] (h : Equation2832 G) : Equation2813 G := λ x y z => h x y z z
theorem Equation2833_implies_Equation2814 (G : Type*) [Magma G] (h : Equation2833 G) : Equation2814 G := λ x y z => h x y z z
theorem Equation2834_implies_Equation2814 (G : Type*) [Magma G] (h : Equation2834 G) : Equation2814 G := λ x y z => h x y z z
theorem Equation2836_implies_Equation2812 (G : Type*) [Magma G] (h : Equation2836 G) : Equation2812 G := λ x y z => h x y z z
theorem Equation2837_implies_Equation2813 (G : Type*) [Magma G] (h : Equation2837 G) : Equation2813 G := λ x y z => h x y z z
theorem Equation2838_implies_Equation2814 (G : Type*) [Magma G] (h : Equation2838 G) : Equation2814 G := λ x y z => h x y z z
theorem Equation2839_implies_Equation2814 (G : Type*) [Magma G] (h : Equation2839 G) : Equation2814 G := λ x y z => h x y z z
theorem Equation2861_implies_Equation2860 (G : Type*) [Magma G] (h : Equation2861 G) : Equation2860 G := λ x y z => h x y z z
theorem Equation2871_implies_Equation2870 (G : Type*) [Magma G] (h : Equation2871 G) : Equation2870 G := λ x y z => h x y z z
theorem Equation2881_implies_Equation2880 (G : Type*) [Magma G] (h : Equation2881 G) : Equation2880 G := λ x y z => h x y z z
theorem Equation2885_implies_Equation2884 (G : Type*) [Magma G] (h : Equation2885 G) : Equation2884 G := λ x y z => h x y z z
theorem Equation2889_implies_Equation2888 (G : Type*) [Magma G] (h : Equation2889 G) : Equation2888 G := λ x y z => h x y z z
theorem Equation2893_implies_Equation2892 (G : Type*) [Magma G] (h : Equation2893 G) : Equation2892 G := λ x y z => h x y z z
theorem Equation2894_implies_Equation2890 (G : Type*) [Magma G] (h : Equation2894 G) : Equation2890 G := λ x y z => h x y z z
theorem Equation2895_implies_Equation2891 (G : Type*) [Magma G] (h : Equation2895 G) : Equation2891 G := λ x y z => h x y z z
theorem Equation2896_implies_Equation2892 (G : Type*) [Magma G] (h : Equation2896 G) : Equation2892 G := λ x y z => h x y z z
theorem Equation2897_implies_Equation2892 (G : Type*) [Magma G] (h : Equation2897 G) : Equation2892 G := λ x y z => h x y z z
theorem Equation2908_implies_Equation2907 (G : Type*) [Magma G] (h : Equation2908 G) : Equation2907 G := λ x y z => h x y z z
theorem Equation2918_implies_Equation2917 (G : Type*) [Magma G] (h : Equation2918 G) : Equation2917 G := λ x y z => h x y z z
theorem Equation2922_implies_Equation2921 (G : Type*) [Magma G] (h : Equation2922 G) : Equation2921 G := λ x y z => h x y z z
theorem Equation2926_implies_Equation2925 (G : Type*) [Magma G] (h : Equation2926 G) : Equation2925 G := λ x y z => h x y z z
theorem Equation2930_implies_Equation2929 (G : Type*) [Magma G] (h : Equation2930 G) : Equation2929 G := λ x y z => h x y z z
theorem Equation2931_implies_Equation2927 (G : Type*) [Magma G] (h : Equation2931 G) : Equation2927 G := λ x y z => h x y z z
theorem Equation2932_implies_Equation2928 (G : Type*) [Magma G] (h : Equation2932 G) : Equation2928 G := λ x y z => h x y z z
theorem Equation2933_implies_Equation2929 (G : Type*) [Magma G] (h : Equation2933 G) : Equation2929 G := λ x y z => h x y z z
theorem Equation2934_implies_Equation2929 (G : Type*) [Magma G] (h : Equation2934 G) : Equation2929 G := λ x y z => h x y z z
theorem Equation2945_implies_Equation2944 (G : Type*) [Magma G] (h : Equation2945 G) : Equation2944 G := λ x y z => h x y z z
theorem Equation2955_implies_Equation2954 (G : Type*) [Magma G] (h : Equation2955 G) : Equation2954 G := λ x y z => h x y z z
theorem Equation2959_implies_Equation2958 (G : Type*) [Magma G] (h : Equation2959 G) : Equation2958 G := λ x y z => h x y z z
theorem Equation2963_implies_Equation2962 (G : Type*) [Magma G] (h : Equation2963 G) : Equation2962 G := λ x y z => h x y z z
theorem Equation2967_implies_Equation2966 (G : Type*) [Magma G] (h : Equation2967 G) : Equation2966 G := λ x y z => h x y z z
theorem Equation2968_implies_Equation2964 (G : Type*) [Magma G] (h : Equation2968 G) : Equation2964 G := λ x y z => h x y z z
theorem Equation2969_implies_Equation2965 (G : Type*) [Magma G] (h : Equation2969 G) : Equation2965 G := λ x y z => h x y z z
theorem Equation2970_implies_Equation2966 (G : Type*) [Magma G] (h : Equation2970 G) : Equation2966 G := λ x y z => h x y z z
theorem Equation2971_implies_Equation2966 (G : Type*) [Magma G] (h : Equation2971 G) : Equation2966 G := λ x y z => h x y z z
theorem Equation2976_implies_Equation2975 (G : Type*) [Magma G] (h : Equation2976 G) : Equation2975 G := λ x y z => h x y z z
theorem Equation2980_implies_Equation2979 (G : Type*) [Magma G] (h : Equation2980 G) : Equation2979 G := λ x y z => h x y z z
theorem Equation2984_implies_Equation2983 (G : Type*) [Magma G] (h : Equation2984 G) : Equation2983 G := λ x y z => h x y z z
theorem Equation2985_implies_Equation2981 (G : Type*) [Magma G] (h : Equation2985 G) : Equation2981 G := λ x y z => h x y z z
theorem Equation2986_implies_Equation2982 (G : Type*) [Magma G] (h : Equation2986 G) : Equation2982 G := λ x y z => h x y z z
theorem Equation2987_implies_Equation2983 (G : Type*) [Magma G] (h : Equation2987 G) : Equation2983 G := λ x y z => h x y z z
theorem Equation2988_implies_Equation2983 (G : Type*) [Magma G] (h : Equation2988 G) : Equation2983 G := λ x y z => h x y z z
theorem Equation2993_implies_Equation2992 (G : Type*) [Magma G] (h : Equation2993 G) : Equation2992 G := λ x y z => h x y z z
theorem Equation2997_implies_Equation2996 (G : Type*) [Magma G] (h : Equation2997 G) : Equation2996 G := λ x y z => h x y z z
theorem Equation3001_implies_Equation3000 (G : Type*) [Magma G] (h : Equation3001 G) : Equation3000 G := λ x y z => h x y z z
theorem Equation3002_implies_Equation2998 (G : Type*) [Magma G] (h : Equation3002 G) : Equation2998 G := λ x y z => h x y z z
theorem Equation3003_implies_Equation2999 (G : Type*) [Magma G] (h : Equation3003 G) : Equation2999 G := λ x y z => h x y z z
theorem Equation3004_implies_Equation3000 (G : Type*) [Magma G] (h : Equation3004 G) : Equation3000 G := λ x y z => h x y z z
theorem Equation3005_implies_Equation3000 (G : Type*) [Magma G] (h : Equation3005 G) : Equation3000 G := λ x y z => h x y z z
theorem Equation3010_implies_Equation3009 (G : Type*) [Magma G] (h : Equation3010 G) : Equation3009 G := λ x y z => h x y z z
theorem Equation3014_implies_Equation3013 (G : Type*) [Magma G] (h : Equation3014 G) : Equation3013 G := λ x y z => h x y z z
theorem Equation3018_implies_Equation3017 (G : Type*) [Magma G] (h : Equation3018 G) : Equation3017 G := λ x y z => h x y z z
theorem Equation3019_implies_Equation3015 (G : Type*) [Magma G] (h : Equation3019 G) : Equation3015 G := λ x y z => h x y z z
theorem Equation3020_implies_Equation3016 (G : Type*) [Magma G] (h : Equation3020 G) : Equation3016 G := λ x y z => h x y z z
theorem Equation3021_implies_Equation3017 (G : Type*) [Magma G] (h : Equation3021 G) : Equation3017 G := λ x y z => h x y z z
theorem Equation3022_implies_Equation3017 (G : Type*) [Magma G] (h : Equation3022 G) : Equation3017 G := λ x y z => h x y z z
theorem Equation3024_implies_Equation3007 (G : Type*) [Magma G] (h : Equation3024 G) : Equation3007 G := λ x y z => h x y z z
theorem Equation3025_implies_Equation3008 (G : Type*) [Magma G] (h : Equation3025 G) : Equation3008 G := λ x y z => h x y z z
theorem Equation3026_implies_Equation3009 (G : Type*) [Magma G] (h : Equation3026 G) : Equation3009 G := λ x y z => h x y z z
theorem Equation3027_implies_Equation3009 (G : Type*) [Magma G] (h : Equation3027 G) : Equation3009 G := λ x y z => h x y z z
theorem Equation3029_implies_Equation3011 (G : Type*) [Magma G] (h : Equation3029 G) : Equation3011 G := λ x y z => h x y z z
theorem Equation3030_implies_Equation3012 (G : Type*) [Magma G] (h : Equation3030 G) : Equation3012 G := λ x y z => h x y z z
theorem Equation3031_implies_Equation3013 (G : Type*) [Magma G] (h : Equation3031 G) : Equation3013 G := λ x y z => h x y z z
theorem Equation3032_implies_Equation3013 (G : Type*) [Magma G] (h : Equation3032 G) : Equation3013 G := λ x y z => h x y z z
theorem Equation3034_implies_Equation3015 (G : Type*) [Magma G] (h : Equation3034 G) : Equation3015 G := λ x y z => h x y z z
theorem Equation3035_implies_Equation3016 (G : Type*) [Magma G] (h : Equation3035 G) : Equation3016 G := λ x y z => h x y z z
theorem Equation3036_implies_Equation3017 (G : Type*) [Magma G] (h : Equation3036 G) : Equation3017 G := λ x y z => h x y z z
theorem Equation3037_implies_Equation3017 (G : Type*) [Magma G] (h : Equation3037 G) : Equation3017 G := λ x y z => h x y z z
theorem Equation3039_implies_Equation3015 (G : Type*) [Magma G] (h : Equation3039 G) : Equation3015 G := λ x y z => h x y z z
theorem Equation3040_implies_Equation3016 (G : Type*) [Magma G] (h : Equation3040 G) : Equation3016 G := λ x y z => h x y z z
theorem Equation3041_implies_Equation3017 (G : Type*) [Magma G] (h : Equation3041 G) : Equation3017 G := λ x y z => h x y z z
theorem Equation3042_implies_Equation3017 (G : Type*) [Magma G] (h : Equation3042 G) : Equation3017 G := λ x y z => h x y z z
theorem Equation3064_implies_Equation3063 (G : Type*) [Magma G] (h : Equation3064 G) : Equation3063 G := λ x y z => h x y z z
theorem Equation3074_implies_Equation3073 (G : Type*) [Magma G] (h : Equation3074 G) : Equation3073 G := λ x y z => h x y z z
theorem Equation3084_implies_Equation3083 (G : Type*) [Magma G] (h : Equation3084 G) : Equation3083 G := λ x y z => h x y z z
theorem Equation3088_implies_Equation3087 (G : Type*) [Magma G] (h : Equation3088 G) : Equation3087 G := λ x y z => h x y z z
theorem Equation3092_implies_Equation3091 (G : Type*) [Magma G] (h : Equation3092 G) : Equation3091 G := λ x y z => h x y z z
theorem Equation3096_implies_Equation3095 (G : Type*) [Magma G] (h : Equation3096 G) : Equation3095 G := λ x y z => h x y z z
theorem Equation3097_implies_Equation3093 (G : Type*) [Magma G] (h : Equation3097 G) : Equation3093 G := λ x y z => h x y z z
theorem Equation3098_implies_Equation3094 (G : Type*) [Magma G] (h : Equation3098 G) : Equation3094 G := λ x y z => h x y z z
theorem Equation3099_implies_Equation3095 (G : Type*) [Magma G] (h : Equation3099 G) : Equation3095 G := λ x y z => h x y z z
theorem Equation3100_implies_Equation3095 (G : Type*) [Magma G] (h : Equation3100 G) : Equation3095 G := λ x y z => h x y z z
theorem Equation3111_implies_Equation3110 (G : Type*) [Magma G] (h : Equation3111 G) : Equation3110 G := λ x y z => h x y z z
theorem Equation3121_implies_Equation3120 (G : Type*) [Magma G] (h : Equation3121 G) : Equation3120 G := λ x y z => h x y z z
theorem Equation3125_implies_Equation3124 (G : Type*) [Magma G] (h : Equation3125 G) : Equation3124 G := λ x y z => h x y z z
theorem Equation3129_implies_Equation3128 (G : Type*) [Magma G] (h : Equation3129 G) : Equation3128 G := λ x y z => h x y z z
theorem Equation3133_implies_Equation3132 (G : Type*) [Magma G] (h : Equation3133 G) : Equation3132 G := λ x y z => h x y z z
theorem Equation3134_implies_Equation3130 (G : Type*) [Magma G] (h : Equation3134 G) : Equation3130 G := λ x y z => h x y z z
theorem Equation3135_implies_Equation3131 (G : Type*) [Magma G] (h : Equation3135 G) : Equation3131 G := λ x y z => h x y z z
theorem Equation3136_implies_Equation3132 (G : Type*) [Magma G] (h : Equation3136 G) : Equation3132 G := λ x y z => h x y z z
theorem Equation3137_implies_Equation3132 (G : Type*) [Magma G] (h : Equation3137 G) : Equation3132 G := λ x y z => h x y z z
theorem Equation3148_implies_Equation3147 (G : Type*) [Magma G] (h : Equation3148 G) : Equation3147 G := λ x y z => h x y z z
theorem Equation3158_implies_Equation3157 (G : Type*) [Magma G] (h : Equation3158 G) : Equation3157 G := λ x y z => h x y z z
theorem Equation3162_implies_Equation3161 (G : Type*) [Magma G] (h : Equation3162 G) : Equation3161 G := λ x y z => h x y z z
theorem Equation3166_implies_Equation3165 (G : Type*) [Magma G] (h : Equation3166 G) : Equation3165 G := λ x y z => h x y z z
theorem Equation3170_implies_Equation3169 (G : Type*) [Magma G] (h : Equation3170 G) : Equation3169 G := λ x y z => h x y z z
theorem Equation3171_implies_Equation3167 (G : Type*) [Magma G] (h : Equation3171 G) : Equation3167 G := λ x y z => h x y z z
theorem Equation3172_implies_Equation3168 (G : Type*) [Magma G] (h : Equation3172 G) : Equation3168 G := λ x y z => h x y z z
theorem Equation3173_implies_Equation3169 (G : Type*) [Magma G] (h : Equation3173 G) : Equation3169 G := λ x y z => h x y z z
theorem Equation3174_implies_Equation3169 (G : Type*) [Magma G] (h : Equation3174 G) : Equation3169 G := λ x y z => h x y z z
theorem Equation3179_implies_Equation3178 (G : Type*) [Magma G] (h : Equation3179 G) : Equation3178 G := λ x y z => h x y z z
theorem Equation3183_implies_Equation3182 (G : Type*) [Magma G] (h : Equation3183 G) : Equation3182 G := λ x y z => h x y z z
theorem Equation3187_implies_Equation3186 (G : Type*) [Magma G] (h : Equation3187 G) : Equation3186 G := λ x y z => h x y z z
theorem Equation3188_implies_Equation3184 (G : Type*) [Magma G] (h : Equation3188 G) : Equation3184 G := λ x y z => h x y z z
theorem Equation3189_implies_Equation3185 (G : Type*) [Magma G] (h : Equation3189 G) : Equation3185 G := λ x y z => h x y z z
theorem Equation3190_implies_Equation3186 (G : Type*) [Magma G] (h : Equation3190 G) : Equation3186 G := λ x y z => h x y z z
theorem Equation3191_implies_Equation3186 (G : Type*) [Magma G] (h : Equation3191 G) : Equation3186 G := λ x y z => h x y z z
theorem Equation3196_implies_Equation3195 (G : Type*) [Magma G] (h : Equation3196 G) : Equation3195 G := λ x y z => h x y z z
theorem Equation3200_implies_Equation3199 (G : Type*) [Magma G] (h : Equation3200 G) : Equation3199 G := λ x y z => h x y z z
theorem Equation3204_implies_Equation3203 (G : Type*) [Magma G] (h : Equation3204 G) : Equation3203 G := λ x y z => h x y z z
theorem Equation3205_implies_Equation3201 (G : Type*) [Magma G] (h : Equation3205 G) : Equation3201 G := λ x y z => h x y z z
theorem Equation3206_implies_Equation3202 (G : Type*) [Magma G] (h : Equation3206 G) : Equation3202 G := λ x y z => h x y z z
theorem Equation3207_implies_Equation3203 (G : Type*) [Magma G] (h : Equation3207 G) : Equation3203 G := λ x y z => h x y z z
theorem Equation3208_implies_Equation3203 (G : Type*) [Magma G] (h : Equation3208 G) : Equation3203 G := λ x y z => h x y z z
theorem Equation3213_implies_Equation3212 (G : Type*) [Magma G] (h : Equation3213 G) : Equation3212 G := λ x y z => h x y z z
theorem Equation3217_implies_Equation3216 (G : Type*) [Magma G] (h : Equation3217 G) : Equation3216 G := λ x y z => h x y z z
theorem Equation3221_implies_Equation3220 (G : Type*) [Magma G] (h : Equation3221 G) : Equation3220 G := λ x y z => h x y z z
theorem Equation3222_implies_Equation3218 (G : Type*) [Magma G] (h : Equation3222 G) : Equation3218 G := λ x y z => h x y z z
theorem Equation3223_implies_Equation3219 (G : Type*) [Magma G] (h : Equation3223 G) : Equation3219 G := λ x y z => h x y z z
theorem Equation3224_implies_Equation3220 (G : Type*) [Magma G] (h : Equation3224 G) : Equation3220 G := λ x y z => h x y z z
theorem Equation3225_implies_Equation3220 (G : Type*) [Magma G] (h : Equation3225 G) : Equation3220 G := λ x y z => h x y z z
theorem Equation3227_implies_Equation3210 (G : Type*) [Magma G] (h : Equation3227 G) : Equation3210 G := λ x y z => h x y z z
theorem Equation3228_implies_Equation3211 (G : Type*) [Magma G] (h : Equation3228 G) : Equation3211 G := λ x y z => h x y z z
theorem Equation3229_implies_Equation3212 (G : Type*) [Magma G] (h : Equation3229 G) : Equation3212 G := λ x y z => h x y z z
theorem Equation3230_implies_Equation3212 (G : Type*) [Magma G] (h : Equation3230 G) : Equation3212 G := λ x y z => h x y z z
theorem Equation3232_implies_Equation3214 (G : Type*) [Magma G] (h : Equation3232 G) : Equation3214 G := λ x y z => h x y z z
theorem Equation3233_implies_Equation3215 (G : Type*) [Magma G] (h : Equation3233 G) : Equation3215 G := λ x y z => h x y z z
theorem Equation3234_implies_Equation3216 (G : Type*) [Magma G] (h : Equation3234 G) : Equation3216 G := λ x y z => h x y z z
theorem Equation3235_implies_Equation3216 (G : Type*) [Magma G] (h : Equation3235 G) : Equation3216 G := λ x y z => h x y z z
theorem Equation3237_implies_Equation3218 (G : Type*) [Magma G] (h : Equation3237 G) : Equation3218 G := λ x y z => h x y z z
theorem Equation3238_implies_Equation3219 (G : Type*) [Magma G] (h : Equation3238 G) : Equation3219 G := λ x y z => h x y z z
theorem Equation3239_implies_Equation3220 (G : Type*) [Magma G] (h : Equation3239 G) : Equation3220 G := λ x y z => h x y z z
theorem Equation3240_implies_Equation3220 (G : Type*) [Magma G] (h : Equation3240 G) : Equation3220 G := λ x y z => h x y z z
theorem Equation3242_implies_Equation3218 (G : Type*) [Magma G] (h : Equation3242 G) : Equation3218 G := λ x y z => h x y z z
theorem Equation3243_implies_Equation3219 (G : Type*) [Magma G] (h : Equation3243 G) : Equation3219 G := λ x y z => h x y z z
theorem Equation3244_implies_Equation3220 (G : Type*) [Magma G] (h : Equation3244 G) : Equation3220 G := λ x y z => h x y z z
theorem Equation3245_implies_Equation3220 (G : Type*) [Magma G] (h : Equation3245 G) : Equation3220 G := λ x y z => h x y z z
theorem Equation3267_implies_Equation3266 (G : Type*) [Magma G] (h : Equation3267 G) : Equation3266 G := λ x y z => h x y z z
theorem Equation3277_implies_Equation3276 (G : Type*) [Magma G] (h : Equation3277 G) : Equation3276 G := λ x y z => h x y z z
theorem Equation3287_implies_Equation3286 (G : Type*) [Magma G] (h : Equation3287 G) : Equation3286 G := λ x y z => h x y z z
theorem Equation3291_implies_Equation3290 (G : Type*) [Magma G] (h : Equation3291 G) : Equation3290 G := λ x y z => h x y z z
theorem Equation3295_implies_Equation3294 (G : Type*) [Magma G] (h : Equation3295 G) : Equation3294 G := λ x y z => h x y z z
theorem Equation3299_implies_Equation3298 (G : Type*) [Magma G] (h : Equation3299 G) : Equation3298 G := λ x y z => h x y z z
theorem Equation3300_implies_Equation3296 (G : Type*) [Magma G] (h : Equation3300 G) : Equation3296 G := λ x y z => h x y z z
theorem Equation3301_implies_Equation3297 (G : Type*) [Magma G] (h : Equation3301 G) : Equation3297 G := λ x y z => h x y z z
theorem Equation3302_implies_Equation3298 (G : Type*) [Magma G] (h : Equation3302 G) : Equation3298 G := λ x y z => h x y z z
theorem Equation3303_implies_Equation3298 (G : Type*) [Magma G] (h : Equation3303 G) : Equation3298 G := λ x y z => h x y z z
theorem Equation3314_implies_Equation3313 (G : Type*) [Magma G] (h : Equation3314 G) : Equation3313 G := λ x y z => h x y z z
theorem Equation3324_implies_Equation3323 (G : Type*) [Magma G] (h : Equation3324 G) : Equation3323 G := λ x y z => h x y z z
theorem Equation3328_implies_Equation3327 (G : Type*) [Magma G] (h : Equation3328 G) : Equation3327 G := λ x y z => h x y z z
theorem Equation3332_implies_Equation3331 (G : Type*) [Magma G] (h : Equation3332 G) : Equation3331 G := λ x y z => h x y z z
theorem Equation3336_implies_Equation3335 (G : Type*) [Magma G] (h : Equation3336 G) : Equation3335 G := λ x y z => h x y z z
theorem Equation3337_implies_Equation3333 (G : Type*) [Magma G] (h : Equation3337 G) : Equation3333 G := λ x y z => h x y z z
theorem Equation3338_implies_Equation3334 (G : Type*) [Magma G] (h : Equation3338 G) : Equation3334 G := λ x y z => h x y z z
theorem Equation3339_implies_Equation3335 (G : Type*) [Magma G] (h : Equation3339 G) : Equation3335 G := λ x y z => h x y z z
theorem Equation3340_implies_Equation3335 (G : Type*) [Magma G] (h : Equation3340 G) : Equation3335 G := λ x y z => h x y z z
theorem Equation3351_implies_Equation3350 (G : Type*) [Magma G] (h : Equation3351 G) : Equation3350 G := λ x y z => h x y z z
theorem Equation3361_implies_Equation3360 (G : Type*) [Magma G] (h : Equation3361 G) : Equation3360 G := λ x y z => h x y z z
theorem Equation3365_implies_Equation3364 (G : Type*) [Magma G] (h : Equation3365 G) : Equation3364 G := λ x y z => h x y z z
theorem Equation3369_implies_Equation3368 (G : Type*) [Magma G] (h : Equation3369 G) : Equation3368 G := λ x y z => h x y z z
theorem Equation3373_implies_Equation3372 (G : Type*) [Magma G] (h : Equation3373 G) : Equation3372 G := λ x y z => h x y z z
theorem Equation3374_implies_Equation3370 (G : Type*) [Magma G] (h : Equation3374 G) : Equation3370 G := λ x y z => h x y z z
theorem Equation3375_implies_Equation3371 (G : Type*) [Magma G] (h : Equation3375 G) : Equation3371 G := λ x y z => h x y z z
theorem Equation3376_implies_Equation3372 (G : Type*) [Magma G] (h : Equation3376 G) : Equation3372 G := λ x y z => h x y z z
theorem Equation3377_implies_Equation3372 (G : Type*) [Magma G] (h : Equation3377 G) : Equation3372 G := λ x y z => h x y z z
theorem Equation3382_implies_Equation3381 (G : Type*) [Magma G] (h : Equation3382 G) : Equation3381 G := λ x y z => h x y z z
theorem Equation3386_implies_Equation3385 (G : Type*) [Magma G] (h : Equation3386 G) : Equation3385 G := λ x y z => h x y z z
theorem Equation3390_implies_Equation3389 (G : Type*) [Magma G] (h : Equation3390 G) : Equation3389 G := λ x y z => h x y z z
theorem Equation3391_implies_Equation3387 (G : Type*) [Magma G] (h : Equation3391 G) : Equation3387 G := λ x y z => h x y z z
theorem Equation3392_implies_Equation3388 (G : Type*) [Magma G] (h : Equation3392 G) : Equation3388 G := λ x y z => h x y z z
theorem Equation3393_implies_Equation3389 (G : Type*) [Magma G] (h : Equation3393 G) : Equation3389 G := λ x y z => h x y z z
theorem Equation3394_implies_Equation3389 (G : Type*) [Magma G] (h : Equation3394 G) : Equation3389 G := λ x y z => h x y z z
theorem Equation3399_implies_Equation3398 (G : Type*) [Magma G] (h : Equation3399 G) : Equation3398 G := λ x y z => h x y z z
theorem Equation3403_implies_Equation3402 (G : Type*) [Magma G] (h : Equation3403 G) : Equation3402 G := λ x y z => h x y z z
theorem Equation3407_implies_Equation3406 (G : Type*) [Magma G] (h : Equation3407 G) : Equation3406 G := λ x y z => h x y z z
theorem Equation3408_implies_Equation3404 (G : Type*) [Magma G] (h : Equation3408 G) : Equation3404 G := λ x y z => h x y z z
theorem Equation3409_implies_Equation3405 (G : Type*) [Magma G] (h : Equation3409 G) : Equation3405 G := λ x y z => h x y z z
theorem Equation3410_implies_Equation3406 (G : Type*) [Magma G] (h : Equation3410 G) : Equation3406 G := λ x y z => h x y z z
theorem Equation3411_implies_Equation3406 (G : Type*) [Magma G] (h : Equation3411 G) : Equation3406 G := λ x y z => h x y z z
theorem Equation3416_implies_Equation3415 (G : Type*) [Magma G] (h : Equation3416 G) : Equation3415 G := λ x y z => h x y z z
theorem Equation3420_implies_Equation3419 (G : Type*) [Magma G] (h : Equation3420 G) : Equation3419 G := λ x y z => h x y z z
theorem Equation3424_implies_Equation3423 (G : Type*) [Magma G] (h : Equation3424 G) : Equation3423 G := λ x y z => h x y z z
theorem Equation3425_implies_Equation3421 (G : Type*) [Magma G] (h : Equation3425 G) : Equation3421 G := λ x y z => h x y z z
theorem Equation3426_implies_Equation3422 (G : Type*) [Magma G] (h : Equation3426 G) : Equation3422 G := λ x y z => h x y z z
theorem Equation3427_implies_Equation3423 (G : Type*) [Magma G] (h : Equation3427 G) : Equation3423 G := λ x y z => h x y z z
theorem Equation3428_implies_Equation3423 (G : Type*) [Magma G] (h : Equation3428 G) : Equation3423 G := λ x y z => h x y z z
theorem Equation3430_implies_Equation3413 (G : Type*) [Magma G] (h : Equation3430 G) : Equation3413 G := λ x y z => h x y z z
theorem Equation3431_implies_Equation3414 (G : Type*) [Magma G] (h : Equation3431 G) : Equation3414 G := λ x y z => h x y z z
theorem Equation3432_implies_Equation3415 (G : Type*) [Magma G] (h : Equation3432 G) : Equation3415 G := λ x y z => h x y z z
theorem Equation3433_implies_Equation3415 (G : Type*) [Magma G] (h : Equation3433 G) : Equation3415 G := λ x y z => h x y z z
theorem Equation3435_implies_Equation3417 (G : Type*) [Magma G] (h : Equation3435 G) : Equation3417 G := λ x y z => h x y z z
theorem Equation3436_implies_Equation3418 (G : Type*) [Magma G] (h : Equation3436 G) : Equation3418 G := λ x y z => h x y z z
theorem Equation3437_implies_Equation3419 (G : Type*) [Magma G] (h : Equation3437 G) : Equation3419 G := λ x y z => h x y z z
theorem Equation3438_implies_Equation3419 (G : Type*) [Magma G] (h : Equation3438 G) : Equation3419 G := λ x y z => h x y z z
theorem Equation3440_implies_Equation3421 (G : Type*) [Magma G] (h : Equation3440 G) : Equation3421 G := λ x y z => h x y z z
theorem Equation3441_implies_Equation3422 (G : Type*) [Magma G] (h : Equation3441 G) : Equation3422 G := λ x y z => h x y z z
theorem Equation3442_implies_Equation3423 (G : Type*) [Magma G] (h : Equation3442 G) : Equation3423 G := λ x y z => h x y z z
theorem Equation3443_implies_Equation3423 (G : Type*) [Magma G] (h : Equation3443 G) : Equation3423 G := λ x y z => h x y z z
theorem Equation3445_implies_Equation3421 (G : Type*) [Magma G] (h : Equation3445 G) : Equation3421 G := λ x y z => h x y z z
theorem Equation3446_implies_Equation3422 (G : Type*) [Magma G] (h : Equation3446 G) : Equation3422 G := λ x y z => h x y z z
theorem Equation3447_implies_Equation3423 (G : Type*) [Magma G] (h : Equation3447 G) : Equation3423 G := λ x y z => h x y z z
theorem Equation3448_implies_Equation3423 (G : Type*) [Magma G] (h : Equation3448 G) : Equation3423 G := λ x y z => h x y z z
theorem Equation3470_implies_Equation3469 (G : Type*) [Magma G] (h : Equation3470 G) : Equation3469 G := λ x y z => h x y z z
theorem Equation3480_implies_Equation3479 (G : Type*) [Magma G] (h : Equation3480 G) : Equation3479 G := λ x y z => h x y z z
theorem Equation3490_implies_Equation3489 (G : Type*) [Magma G] (h : Equation3490 G) : Equation3489 G := λ x y z => h x y z z
theorem Equation3494_implies_Equation3493 (G : Type*) [Magma G] (h : Equation3494 G) : Equation3493 G := λ x y z => h x y z z
theorem Equation3498_implies_Equation3497 (G : Type*) [Magma G] (h : Equation3498 G) : Equation3497 G := λ x y z => h x y z z
theorem Equation3502_implies_Equation3501 (G : Type*) [Magma G] (h : Equation3502 G) : Equation3501 G := λ x y z => h x y z z
theorem Equation3503_implies_Equation3499 (G : Type*) [Magma G] (h : Equation3503 G) : Equation3499 G := λ x y z => h x y z z
theorem Equation3504_implies_Equation3500 (G : Type*) [Magma G] (h : Equation3504 G) : Equation3500 G := λ x y z => h x y z z
theorem Equation3505_implies_Equation3501 (G : Type*) [Magma G] (h : Equation3505 G) : Equation3501 G := λ x y z => h x y z z
theorem Equation3506_implies_Equation3501 (G : Type*) [Magma G] (h : Equation3506 G) : Equation3501 G := λ x y z => h x y z z
theorem Equation3517_implies_Equation3516 (G : Type*) [Magma G] (h : Equation3517 G) : Equation3516 G := λ x y z => h x y z z
theorem Equation3527_implies_Equation3526 (G : Type*) [Magma G] (h : Equation3527 G) : Equation3526 G := λ x y z => h x y z z
theorem Equation3531_implies_Equation3530 (G : Type*) [Magma G] (h : Equation3531 G) : Equation3530 G := λ x y z => h x y z z
theorem Equation3535_implies_Equation3534 (G : Type*) [Magma G] (h : Equation3535 G) : Equation3534 G := λ x y z => h x y z z
theorem Equation3539_implies_Equation3538 (G : Type*) [Magma G] (h : Equation3539 G) : Equation3538 G := λ x y z => h x y z z
theorem Equation3540_implies_Equation3536 (G : Type*) [Magma G] (h : Equation3540 G) : Equation3536 G := λ x y z => h x y z z
theorem Equation3541_implies_Equation3537 (G : Type*) [Magma G] (h : Equation3541 G) : Equation3537 G := λ x y z => h x y z z
theorem Equation3542_implies_Equation3538 (G : Type*) [Magma G] (h : Equation3542 G) : Equation3538 G := λ x y z => h x y z z
theorem Equation3543_implies_Equation3538 (G : Type*) [Magma G] (h : Equation3543 G) : Equation3538 G := λ x y z => h x y z z
theorem Equation3554_implies_Equation3553 (G : Type*) [Magma G] (h : Equation3554 G) : Equation3553 G := λ x y z => h x y z z
theorem Equation3564_implies_Equation3563 (G : Type*) [Magma G] (h : Equation3564 G) : Equation3563 G := λ x y z => h x y z z
theorem Equation3568_implies_Equation3567 (G : Type*) [Magma G] (h : Equation3568 G) : Equation3567 G := λ x y z => h x y z z
theorem Equation3572_implies_Equation3571 (G : Type*) [Magma G] (h : Equation3572 G) : Equation3571 G := λ x y z => h x y z z
theorem Equation3576_implies_Equation3575 (G : Type*) [Magma G] (h : Equation3576 G) : Equation3575 G := λ x y z => h x y z z
theorem Equation3577_implies_Equation3573 (G : Type*) [Magma G] (h : Equation3577 G) : Equation3573 G := λ x y z => h x y z z
theorem Equation3578_implies_Equation3574 (G : Type*) [Magma G] (h : Equation3578 G) : Equation3574 G := λ x y z => h x y z z
theorem Equation3579_implies_Equation3575 (G : Type*) [Magma G] (h : Equation3579 G) : Equation3575 G := λ x y z => h x y z z
theorem Equation3580_implies_Equation3575 (G : Type*) [Magma G] (h : Equation3580 G) : Equation3575 G := λ x y z => h x y z z
theorem Equation3585_implies_Equation3584 (G : Type*) [Magma G] (h : Equation3585 G) : Equation3584 G := λ x y z => h x y z z
theorem Equation3589_implies_Equation3588 (G : Type*) [Magma G] (h : Equation3589 G) : Equation3588 G := λ x y z => h x y z z
theorem Equation3593_implies_Equation3592 (G : Type*) [Magma G] (h : Equation3593 G) : Equation3592 G := λ x y z => h x y z z
theorem Equation3594_implies_Equation3590 (G : Type*) [Magma G] (h : Equation3594 G) : Equation3590 G := λ x y z => h x y z z
theorem Equation3595_implies_Equation3591 (G : Type*) [Magma G] (h : Equation3595 G) : Equation3591 G := λ x y z => h x y z z
theorem Equation3596_implies_Equation3592 (G : Type*) [Magma G] (h : Equation3596 G) : Equation3592 G := λ x y z => h x y z z
theorem Equation3597_implies_Equation3592 (G : Type*) [Magma G] (h : Equation3597 G) : Equation3592 G := λ x y z => h x y z z
theorem Equation3602_implies_Equation3601 (G : Type*) [Magma G] (h : Equation3602 G) : Equation3601 G := λ x y z => h x y z z
theorem Equation3606_implies_Equation3605 (G : Type*) [Magma G] (h : Equation3606 G) : Equation3605 G := λ x y z => h x y z z
theorem Equation3610_implies_Equation3609 (G : Type*) [Magma G] (h : Equation3610 G) : Equation3609 G := λ x y z => h x y z z
theorem Equation3611_implies_Equation3607 (G : Type*) [Magma G] (h : Equation3611 G) : Equation3607 G := λ x y z => h x y z z
theorem Equation3612_implies_Equation3608 (G : Type*) [Magma G] (h : Equation3612 G) : Equation3608 G := λ x y z => h x y z z
theorem Equation3613_implies_Equation3609 (G : Type*) [Magma G] (h : Equation3613 G) : Equation3609 G := λ x y z => h x y z z
theorem Equation3614_implies_Equation3609 (G : Type*) [Magma G] (h : Equation3614 G) : Equation3609 G := λ x y z => h x y z z
theorem Equation3619_implies_Equation3618 (G : Type*) [Magma G] (h : Equation3619 G) : Equation3618 G := λ x y z => h x y z z
theorem Equation3623_implies_Equation3622 (G : Type*) [Magma G] (h : Equation3623 G) : Equation3622 G := λ x y z => h x y z z
theorem Equation3627_implies_Equation3626 (G : Type*) [Magma G] (h : Equation3627 G) : Equation3626 G := λ x y z => h x y z z
theorem Equation3628_implies_Equation3624 (G : Type*) [Magma G] (h : Equation3628 G) : Equation3624 G := λ x y z => h x y z z
theorem Equation3629_implies_Equation3625 (G : Type*) [Magma G] (h : Equation3629 G) : Equation3625 G := λ x y z => h x y z z
theorem Equation3630_implies_Equation3626 (G : Type*) [Magma G] (h : Equation3630 G) : Equation3626 G := λ x y z => h x y z z
theorem Equation3631_implies_Equation3626 (G : Type*) [Magma G] (h : Equation3631 G) : Equation3626 G := λ x y z => h x y z z
theorem Equation3633_implies_Equation3616 (G : Type*) [Magma G] (h : Equation3633 G) : Equation3616 G := λ x y z => h x y z z
theorem Equation3634_implies_Equation3617 (G : Type*) [Magma G] (h : Equation3634 G) : Equation3617 G := λ x y z => h x y z z
theorem Equation3635_implies_Equation3618 (G : Type*) [Magma G] (h : Equation3635 G) : Equation3618 G := λ x y z => h x y z z
theorem Equation3636_implies_Equation3618 (G : Type*) [Magma G] (h : Equation3636 G) : Equation3618 G := λ x y z => h x y z z
theorem Equation3638_implies_Equation3620 (G : Type*) [Magma G] (h : Equation3638 G) : Equation3620 G := λ x y z => h x y z z
theorem Equation3639_implies_Equation3621 (G : Type*) [Magma G] (h : Equation3639 G) : Equation3621 G := λ x y z => h x y z z
theorem Equation3640_implies_Equation3622 (G : Type*) [Magma G] (h : Equation3640 G) : Equation3622 G := λ x y z => h x y z z
theorem Equation3641_implies_Equation3622 (G : Type*) [Magma G] (h : Equation3641 G) : Equation3622 G := λ x y z => h x y z z
theorem Equation3643_implies_Equation3624 (G : Type*) [Magma G] (h : Equation3643 G) : Equation3624 G := λ x y z => h x y z z
theorem Equation3644_implies_Equation3625 (G : Type*) [Magma G] (h : Equation3644 G) : Equation3625 G := λ x y z => h x y z z
theorem Equation3645_implies_Equation3626 (G : Type*) [Magma G] (h : Equation3645 G) : Equation3626 G := λ x y z => h x y z z
theorem Equation3646_implies_Equation3626 (G : Type*) [Magma G] (h : Equation3646 G) : Equation3626 G := λ x y z => h x y z z
theorem Equation3648_implies_Equation3624 (G : Type*) [Magma G] (h : Equation3648 G) : Equation3624 G := λ x y z => h x y z z
theorem Equation3649_implies_Equation3625 (G : Type*) [Magma G] (h : Equation3649 G) : Equation3625 G := λ x y z => h x y z z
theorem Equation3650_implies_Equation3626 (G : Type*) [Magma G] (h : Equation3650 G) : Equation3626 G := λ x y z => h x y z z
theorem Equation3651_implies_Equation3626 (G : Type*) [Magma G] (h : Equation3651 G) : Equation3626 G := λ x y z => h x y z z
theorem Equation3673_implies_Equation3672 (G : Type*) [Magma G] (h : Equation3673 G) : Equation3672 G := λ x y z => h x y z z
theorem Equation3683_implies_Equation3682 (G : Type*) [Magma G] (h : Equation3683 G) : Equation3682 G := λ x y z => h x y z z
theorem Equation3693_implies_Equation3692 (G : Type*) [Magma G] (h : Equation3693 G) : Equation3692 G := λ x y z => h x y z z
theorem Equation3697_implies_Equation3696 (G : Type*) [Magma G] (h : Equation3697 G) : Equation3696 G := λ x y z => h x y z z
theorem Equation3701_implies_Equation3700 (G : Type*) [Magma G] (h : Equation3701 G) : Equation3700 G := λ x y z => h x y z z
theorem Equation3705_implies_Equation3704 (G : Type*) [Magma G] (h : Equation3705 G) : Equation3704 G := λ x y z => h x y z z
theorem Equation3706_implies_Equation3702 (G : Type*) [Magma G] (h : Equation3706 G) : Equation3702 G := λ x y z => h x y z z
theorem Equation3707_implies_Equation3703 (G : Type*) [Magma G] (h : Equation3707 G) : Equation3703 G := λ x y z => h x y z z
theorem Equation3708_implies_Equation3704 (G : Type*) [Magma G] (h : Equation3708 G) : Equation3704 G := λ x y z => h x y z z
theorem Equation3709_implies_Equation3704 (G : Type*) [Magma G] (h : Equation3709 G) : Equation3704 G := λ x y z => h x y z z
theorem Equation3720_implies_Equation3719 (G : Type*) [Magma G] (h : Equation3720 G) : Equation3719 G := λ x y z => h x y z z
theorem Equation3730_implies_Equation3729 (G : Type*) [Magma G] (h : Equation3730 G) : Equation3729 G := λ x y z => h x y z z
theorem Equation3734_implies_Equation3733 (G : Type*) [Magma G] (h : Equation3734 G) : Equation3733 G := λ x y z => h x y z z
theorem Equation3738_implies_Equation3737 (G : Type*) [Magma G] (h : Equation3738 G) : Equation3737 G := λ x y z => h x y z z
theorem Equation3742_implies_Equation3741 (G : Type*) [Magma G] (h : Equation3742 G) : Equation3741 G := λ x y z => h x y z z
theorem Equation3743_implies_Equation3739 (G : Type*) [Magma G] (h : Equation3743 G) : Equation3739 G := λ x y z => h x y z z
theorem Equation3744_implies_Equation3740 (G : Type*) [Magma G] (h : Equation3744 G) : Equation3740 G := λ x y z => h x y z z
theorem Equation3745_implies_Equation3741 (G : Type*) [Magma G] (h : Equation3745 G) : Equation3741 G := λ x y z => h x y z z
theorem Equation3746_implies_Equation3741 (G : Type*) [Magma G] (h : Equation3746 G) : Equation3741 G := λ x y z => h x y z z
theorem Equation3757_implies_Equation3756 (G : Type*) [Magma G] (h : Equation3757 G) : Equation3756 G := λ x y z => h x y z z
theorem Equation3767_implies_Equation3766 (G : Type*) [Magma G] (h : Equation3767 G) : Equation3766 G := λ x y z => h x y z z
theorem Equation3771_implies_Equation3770 (G : Type*) [Magma G] (h : Equation3771 G) : Equation3770 G := λ x y z => h x y z z
theorem Equation3775_implies_Equation3774 (G : Type*) [Magma G] (h : Equation3775 G) : Equation3774 G := λ x y z => h x y z z
theorem Equation3779_implies_Equation3778 (G : Type*) [Magma G] (h : Equation3779 G) : Equation3778 G := λ x y z => h x y z z
theorem Equation3780_implies_Equation3776 (G : Type*) [Magma G] (h : Equation3780 G) : Equation3776 G := λ x y z => h x y z z
theorem Equation3781_implies_Equation3777 (G : Type*) [Magma G] (h : Equation3781 G) : Equation3777 G := λ x y z => h x y z z
theorem Equation3782_implies_Equation3778 (G : Type*) [Magma G] (h : Equation3782 G) : Equation3778 G := λ x y z => h x y z z
theorem Equation3783_implies_Equation3778 (G : Type*) [Magma G] (h : Equation3783 G) : Equation3778 G := λ x y z => h x y z z
theorem Equation3788_implies_Equation3787 (G : Type*) [Magma G] (h : Equation3788 G) : Equation3787 G := λ x y z => h x y z z
theorem Equation3792_implies_Equation3791 (G : Type*) [Magma G] (h : Equation3792 G) : Equation3791 G := λ x y z => h x y z z
theorem Equation3796_implies_Equation3795 (G : Type*) [Magma G] (h : Equation3796 G) : Equation3795 G := λ x y z => h x y z z
theorem Equation3797_implies_Equation3793 (G : Type*) [Magma G] (h : Equation3797 G) : Equation3793 G := λ x y z => h x y z z
theorem Equation3798_implies_Equation3794 (G : Type*) [Magma G] (h : Equation3798 G) : Equation3794 G := λ x y z => h x y z z
theorem Equation3799_implies_Equation3795 (G : Type*) [Magma G] (h : Equation3799 G) : Equation3795 G := λ x y z => h x y z z
theorem Equation3800_implies_Equation3795 (G : Type*) [Magma G] (h : Equation3800 G) : Equation3795 G := λ x y z => h x y z z
theorem Equation3805_implies_Equation3804 (G : Type*) [Magma G] (h : Equation3805 G) : Equation3804 G := λ x y z => h x y z z
theorem Equation3809_implies_Equation3808 (G : Type*) [Magma G] (h : Equation3809 G) : Equation3808 G := λ x y z => h x y z z
theorem Equation3813_implies_Equation3812 (G : Type*) [Magma G] (h : Equation3813 G) : Equation3812 G := λ x y z => h x y z z
theorem Equation3814_implies_Equation3810 (G : Type*) [Magma G] (h : Equation3814 G) : Equation3810 G := λ x y z => h x y z z
theorem Equation3815_implies_Equation3811 (G : Type*) [Magma G] (h : Equation3815 G) : Equation3811 G := λ x y z => h x y z z
theorem Equation3816_implies_Equation3812 (G : Type*) [Magma G] (h : Equation3816 G) : Equation3812 G := λ x y z => h x y z z
theorem Equation3817_implies_Equation3812 (G : Type*) [Magma G] (h : Equation3817 G) : Equation3812 G := λ x y z => h x y z z
theorem Equation3822_implies_Equation3821 (G : Type*) [Magma G] (h : Equation3822 G) : Equation3821 G := λ x y z => h x y z z
theorem Equation3826_implies_Equation3825 (G : Type*) [Magma G] (h : Equation3826 G) : Equation3825 G := λ x y z => h x y z z
theorem Equation3830_implies_Equation3829 (G : Type*) [Magma G] (h : Equation3830 G) : Equation3829 G := λ x y z => h x y z z
theorem Equation3831_implies_Equation3827 (G : Type*) [Magma G] (h : Equation3831 G) : Equation3827 G := λ x y z => h x y z z
theorem Equation3832_implies_Equation3828 (G : Type*) [Magma G] (h : Equation3832 G) : Equation3828 G := λ x y z => h x y z z
theorem Equation3833_implies_Equation3829 (G : Type*) [Magma G] (h : Equation3833 G) : Equation3829 G := λ x y z => h x y z z
theorem Equation3834_implies_Equation3829 (G : Type*) [Magma G] (h : Equation3834 G) : Equation3829 G := λ x y z => h x y z z
theorem Equation3836_implies_Equation3819 (G : Type*) [Magma G] (h : Equation3836 G) : Equation3819 G := λ x y z => h x y z z
theorem Equation3837_implies_Equation3820 (G : Type*) [Magma G] (h : Equation3837 G) : Equation3820 G := λ x y z => h x y z z
theorem Equation3838_implies_Equation3821 (G : Type*) [Magma G] (h : Equation3838 G) : Equation3821 G := λ x y z => h x y z z
theorem Equation3839_implies_Equation3821 (G : Type*) [Magma G] (h : Equation3839 G) : Equation3821 G := λ x y z => h x y z z
theorem Equation3841_implies_Equation3823 (G : Type*) [Magma G] (h : Equation3841 G) : Equation3823 G := λ x y z => h x y z z
theorem Equation3842_implies_Equation3824 (G : Type*) [Magma G] (h : Equation3842 G) : Equation3824 G := λ x y z => h x y z z
theorem Equation3843_implies_Equation3825 (G : Type*) [Magma G] (h : Equation3843 G) : Equation3825 G := λ x y z => h x y z z
theorem Equation3844_implies_Equation3825 (G : Type*) [Magma G] (h : Equation3844 G) : Equation3825 G := λ x y z => h x y z z
theorem Equation3846_implies_Equation3827 (G : Type*) [Magma G] (h : Equation3846 G) : Equation3827 G := λ x y z => h x y z z
theorem Equation3847_implies_Equation3828 (G : Type*) [Magma G] (h : Equation3847 G) : Equation3828 G := λ x y z => h x y z z
theorem Equation3848_implies_Equation3829 (G : Type*) [Magma G] (h : Equation3848 G) : Equation3829 G := λ x y z => h x y z z
theorem Equation3849_implies_Equation3829 (G : Type*) [Magma G] (h : Equation3849 G) : Equation3829 G := λ x y z => h x y z z
theorem Equation3851_implies_Equation3827 (G : Type*) [Magma G] (h : Equation3851 G) : Equation3827 G := λ x y z => h x y z z
theorem Equation3852_implies_Equation3828 (G : Type*) [Magma G] (h : Equation3852 G) : Equation3828 G := λ x y z => h x y z z
theorem Equation3853_implies_Equation3829 (G : Type*) [Magma G] (h : Equation3853 G) : Equation3829 G := λ x y z => h x y z z
theorem Equation3854_implies_Equation3829 (G : Type*) [Magma G] (h : Equation3854 G) : Equation3829 G := λ x y z => h x y z z
theorem Equation3876_implies_Equation3875 (G : Type*) [Magma G] (h : Equation3876 G) : Equation3875 G := λ x y z => h x y z z
theorem Equation3886_implies_Equation3885 (G : Type*) [Magma G] (h : Equation3886 G) : Equation3885 G := λ x y z => h x y z z
theorem Equation3896_implies_Equation3895 (G : Type*) [Magma G] (h : Equation3896 G) : Equation3895 G := λ x y z => h x y z z
theorem Equation3900_implies_Equation3899 (G : Type*) [Magma G] (h : Equation3900 G) : Equation3899 G := λ x y z => h x y z z
theorem Equation3904_implies_Equation3903 (G : Type*) [Magma G] (h : Equation3904 G) : Equation3903 G := λ x y z => h x y z z
theorem Equation3908_implies_Equation3907 (G : Type*) [Magma G] (h : Equation3908 G) : Equation3907 G := λ x y z => h x y z z
theorem Equation3909_implies_Equation3905 (G : Type*) [Magma G] (h : Equation3909 G) : Equation3905 G := λ x y z => h x y z z
theorem Equation3910_implies_Equation3906 (G : Type*) [Magma G] (h : Equation3910 G) : Equation3906 G := λ x y z => h x y z z
theorem Equation3911_implies_Equation3907 (G : Type*) [Magma G] (h : Equation3911 G) : Equation3907 G := λ x y z => h x y z z
theorem Equation3912_implies_Equation3907 (G : Type*) [Magma G] (h : Equation3912 G) : Equation3907 G := λ x y z => h x y z z
theorem Equation3923_implies_Equation3922 (G : Type*) [Magma G] (h : Equation3923 G) : Equation3922 G := λ x y z => h x y z z
theorem Equation3933_implies_Equation3932 (G : Type*) [Magma G] (h : Equation3933 G) : Equation3932 G := λ x y z => h x y z z
theorem Equation3937_implies_Equation3936 (G : Type*) [Magma G] (h : Equation3937 G) : Equation3936 G := λ x y z => h x y z z
theorem Equation3941_implies_Equation3940 (G : Type*) [Magma G] (h : Equation3941 G) : Equation3940 G := λ x y z => h x y z z
theorem Equation3945_implies_Equation3944 (G : Type*) [Magma G] (h : Equation3945 G) : Equation3944 G := λ x y z => h x y z z
theorem Equation3946_implies_Equation3942 (G : Type*) [Magma G] (h : Equation3946 G) : Equation3942 G := λ x y z => h x y z z
theorem Equation3947_implies_Equation3943 (G : Type*) [Magma G] (h : Equation3947 G) : Equation3943 G := λ x y z => h x y z z
theorem Equation3948_implies_Equation3944 (G : Type*) [Magma G] (h : Equation3948 G) : Equation3944 G := λ x y z => h x y z z
theorem Equation3949_implies_Equation3944 (G : Type*) [Magma G] (h : Equation3949 G) : Equation3944 G := λ x y z => h x y z z
theorem Equation3960_implies_Equation3959 (G : Type*) [Magma G] (h : Equation3960 G) : Equation3959 G := λ x y z => h x y z z
theorem Equation3970_implies_Equation3969 (G : Type*) [Magma G] (h : Equation3970 G) : Equation3969 G := λ x y z => h x y z z
theorem Equation3974_implies_Equation3973 (G : Type*) [Magma G] (h : Equation3974 G) : Equation3973 G := λ x y z => h x y z z
theorem Equation3978_implies_Equation3977 (G : Type*) [Magma G] (h : Equation3978 G) : Equation3977 G := λ x y z => h x y z z
theorem Equation3982_implies_Equation3981 (G : Type*) [Magma G] (h : Equation3982 G) : Equation3981 G := λ x y z => h x y z z
theorem Equation3983_implies_Equation3979 (G : Type*) [Magma G] (h : Equation3983 G) : Equation3979 G := λ x y z => h x y z z
theorem Equation3984_implies_Equation3980 (G : Type*) [Magma G] (h : Equation3984 G) : Equation3980 G := λ x y z => h x y z z
theorem Equation3985_implies_Equation3981 (G : Type*) [Magma G] (h : Equation3985 G) : Equation3981 G := λ x y z => h x y z z
theorem Equation3986_implies_Equation3981 (G : Type*) [Magma G] (h : Equation3986 G) : Equation3981 G := λ x y z => h x y z z
theorem Equation3991_implies_Equation3990 (G : Type*) [Magma G] (h : Equation3991 G) : Equation3990 G := λ x y z => h x y z z
theorem Equation3995_implies_Equation3994 (G : Type*) [Magma G] (h : Equation3995 G) : Equation3994 G := λ x y z => h x y z z
theorem Equation3999_implies_Equation3998 (G : Type*) [Magma G] (h : Equation3999 G) : Equation3998 G := λ x y z => h x y z z
theorem Equation4000_implies_Equation3996 (G : Type*) [Magma G] (h : Equation4000 G) : Equation3996 G := λ x y z => h x y z z
theorem Equation4001_implies_Equation3997 (G : Type*) [Magma G] (h : Equation4001 G) : Equation3997 G := λ x y z => h x y z z
theorem Equation4002_implies_Equation3998 (G : Type*) [Magma G] (h : Equation4002 G) : Equation3998 G := λ x y z => h x y z z
theorem Equation4003_implies_Equation3998 (G : Type*) [Magma G] (h : Equation4003 G) : Equation3998 G := λ x y z => h x y z z
theorem Equation4008_implies_Equation4007 (G : Type*) [Magma G] (h : Equation4008 G) : Equation4007 G := λ x y z => h x y z z
theorem Equation4012_implies_Equation4011 (G : Type*) [Magma G] (h : Equation4012 G) : Equation4011 G := λ x y z => h x y z z
theorem Equation4016_implies_Equation4015 (G : Type*) [Magma G] (h : Equation4016 G) : Equation4015 G := λ x y z => h x y z z
theorem Equation4017_implies_Equation4013 (G : Type*) [Magma G] (h : Equation4017 G) : Equation4013 G := λ x y z => h x y z z
theorem Equation4018_implies_Equation4014 (G : Type*) [Magma G] (h : Equation4018 G) : Equation4014 G := λ x y z => h x y z z
theorem Equation4019_implies_Equation4015 (G : Type*) [Magma G] (h : Equation4019 G) : Equation4015 G := λ x y z => h x y z z
theorem Equation4020_implies_Equation4015 (G : Type*) [Magma G] (h : Equation4020 G) : Equation4015 G := λ x y z => h x y z z
theorem Equation4025_implies_Equation4024 (G : Type*) [Magma G] (h : Equation4025 G) : Equation4024 G := λ x y z => h x y z z
theorem Equation4029_implies_Equation4028 (G : Type*) [Magma G] (h : Equation4029 G) : Equation4028 G := λ x y z => h x y z z
theorem Equation4033_implies_Equation4032 (G : Type*) [Magma G] (h : Equation4033 G) : Equation4032 G := λ x y z => h x y z z
theorem Equation4034_implies_Equation4030 (G : Type*) [Magma G] (h : Equation4034 G) : Equation4030 G := λ x y z => h x y z z
theorem Equation4035_implies_Equation4031 (G : Type*) [Magma G] (h : Equation4035 G) : Equation4031 G := λ x y z => h x y z z
theorem Equation4036_implies_Equation4032 (G : Type*) [Magma G] (h : Equation4036 G) : Equation4032 G := λ x y z => h x y z z
theorem Equation4037_implies_Equation4032 (G : Type*) [Magma G] (h : Equation4037 G) : Equation4032 G := λ x y z => h x y z z
theorem Equation4039_implies_Equation4022 (G : Type*) [Magma G] (h : Equation4039 G) : Equation4022 G := λ x y z => h x y z z
theorem Equation4040_implies_Equation4023 (G : Type*) [Magma G] (h : Equation4040 G) : Equation4023 G := λ x y z => h x y z z
theorem Equation4041_implies_Equation4024 (G : Type*) [Magma G] (h : Equation4041 G) : Equation4024 G := λ x y z => h x y z z
theorem Equation4042_implies_Equation4024 (G : Type*) [Magma G] (h : Equation4042 G) : Equation4024 G := λ x y z => h x y z z
theorem Equation4044_implies_Equation4026 (G : Type*) [Magma G] (h : Equation4044 G) : Equation4026 G := λ x y z => h x y z z
theorem Equation4045_implies_Equation4027 (G : Type*) [Magma G] (h : Equation4045 G) : Equation4027 G := λ x y z => h x y z z
theorem Equation4046_implies_Equation4028 (G : Type*) [Magma G] (h : Equation4046 G) : Equation4028 G := λ x y z => h x y z z
theorem Equation4047_implies_Equation4028 (G : Type*) [Magma G] (h : Equation4047 G) : Equation4028 G := λ x y z => h x y z z
theorem Equation4049_implies_Equation4030 (G : Type*) [Magma G] (h : Equation4049 G) : Equation4030 G := λ x y z => h x y z z
theorem Equation4050_implies_Equation4031 (G : Type*) [Magma G] (h : Equation4050 G) : Equation4031 G := λ x y z => h x y z z
theorem Equation4051_implies_Equation4032 (G : Type*) [Magma G] (h : Equation4051 G) : Equation4032 G := λ x y z => h x y z z
theorem Equation4052_implies_Equation4032 (G : Type*) [Magma G] (h : Equation4052 G) : Equation4032 G := λ x y z => h x y z z
theorem Equation4054_implies_Equation4030 (G : Type*) [Magma G] (h : Equation4054 G) : Equation4030 G := λ x y z => h x y z z
theorem Equation4055_implies_Equation4031 (G : Type*) [Magma G] (h : Equation4055 G) : Equation4031 G := λ x y z => h x y z z
theorem Equation4056_implies_Equation4032 (G : Type*) [Magma G] (h : Equation4056 G) : Equation4032 G := λ x y z => h x y z z
theorem Equation4057_implies_Equation4032 (G : Type*) [Magma G] (h : Equation4057 G) : Equation4032 G := λ x y z => h x y z z
theorem Equation4079_implies_Equation4078 (G : Type*) [Magma G] (h : Equation4079 G) : Equation4078 G := λ x y z => h x y z z
theorem Equation4089_implies_Equation4088 (G : Type*) [Magma G] (h : Equation4089 G) : Equation4088 G := λ x y z => h x y z z
theorem Equation4099_implies_Equation4098 (G : Type*) [Magma G] (h : Equation4099 G) : Equation4098 G := λ x y z => h x y z z
theorem Equation4103_implies_Equation4102 (G : Type*) [Magma G] (h : Equation4103 G) : Equation4102 G := λ x y z => h x y z z
theorem Equation4107_implies_Equation4106 (G : Type*) [Magma G] (h : Equation4107 G) : Equation4106 G := λ x y z => h x y z z
theorem Equation4111_implies_Equation4110 (G : Type*) [Magma G] (h : Equation4111 G) : Equation4110 G := λ x y z => h x y z z
theorem Equation4112_implies_Equation4108 (G : Type*) [Magma G] (h : Equation4112 G) : Equation4108 G := λ x y z => h x y z z
theorem Equation4113_implies_Equation4109 (G : Type*) [Magma G] (h : Equation4113 G) : Equation4109 G := λ x y z => h x y z z
theorem Equation4114_implies_Equation4110 (G : Type*) [Magma G] (h : Equation4114 G) : Equation4110 G := λ x y z => h x y z z
theorem Equation4115_implies_Equation4110 (G : Type*) [Magma G] (h : Equation4115 G) : Equation4110 G := λ x y z => h x y z z
theorem Equation4126_implies_Equation4125 (G : Type*) [Magma G] (h : Equation4126 G) : Equation4125 G := λ x y z => h x y z z
theorem Equation4136_implies_Equation4135 (G : Type*) [Magma G] (h : Equation4136 G) : Equation4135 G := λ x y z => h x y z z
theorem Equation4140_implies_Equation4139 (G : Type*) [Magma G] (h : Equation4140 G) : Equation4139 G := λ x y z => h x y z z
theorem Equation4144_implies_Equation4143 (G : Type*) [Magma G] (h : Equation4144 G) : Equation4143 G := λ x y z => h x y z z
theorem Equation4148_implies_Equation4147 (G : Type*) [Magma G] (h : Equation4148 G) : Equation4147 G := λ x y z => h x y z z
theorem Equation4149_implies_Equation4145 (G : Type*) [Magma G] (h : Equation4149 G) : Equation4145 G := λ x y z => h x y z z
theorem Equation4150_implies_Equation4146 (G : Type*) [Magma G] (h : Equation4150 G) : Equation4146 G := λ x y z => h x y z z
theorem Equation4151_implies_Equation4147 (G : Type*) [Magma G] (h : Equation4151 G) : Equation4147 G := λ x y z => h x y z z
theorem Equation4152_implies_Equation4147 (G : Type*) [Magma G] (h : Equation4152 G) : Equation4147 G := λ x y z => h x y z z
theorem Equation4163_implies_Equation4162 (G : Type*) [Magma G] (h : Equation4163 G) : Equation4162 G := λ x y z => h x y z z
theorem Equation4173_implies_Equation4172 (G : Type*) [Magma G] (h : Equation4173 G) : Equation4172 G := λ x y z => h x y z z
theorem Equation4177_implies_Equation4176 (G : Type*) [Magma G] (h : Equation4177 G) : Equation4176 G := λ x y z => h x y z z
theorem Equation4181_implies_Equation4180 (G : Type*) [Magma G] (h : Equation4181 G) : Equation4180 G := λ x y z => h x y z z
theorem Equation4185_implies_Equation4184 (G : Type*) [Magma G] (h : Equation4185 G) : Equation4184 G := λ x y z => h x y z z
theorem Equation4186_implies_Equation4182 (G : Type*) [Magma G] (h : Equation4186 G) : Equation4182 G := λ x y z => h x y z z
theorem Equation4187_implies_Equation4183 (G : Type*) [Magma G] (h : Equation4187 G) : Equation4183 G := λ x y z => h x y z z
theorem Equation4188_implies_Equation4184 (G : Type*) [Magma G] (h : Equation4188 G) : Equation4184 G := λ x y z => h x y z z
theorem Equation4189_implies_Equation4184 (G : Type*) [Magma G] (h : Equation4189 G) : Equation4184 G := λ x y z => h x y z z
theorem Equation4194_implies_Equation4193 (G : Type*) [Magma G] (h : Equation4194 G) : Equation4193 G := λ x y z => h x y z z
theorem Equation4198_implies_Equation4197 (G : Type*) [Magma G] (h : Equation4198 G) : Equation4197 G := λ x y z => h x y z z
theorem Equation4202_implies_Equation4201 (G : Type*) [Magma G] (h : Equation4202 G) : Equation4201 G := λ x y z => h x y z z
theorem Equation4203_implies_Equation4199 (G : Type*) [Magma G] (h : Equation4203 G) : Equation4199 G := λ x y z => h x y z z
theorem Equation4204_implies_Equation4200 (G : Type*) [Magma G] (h : Equation4204 G) : Equation4200 G := λ x y z => h x y z z
theorem Equation4205_implies_Equation4201 (G : Type*) [Magma G] (h : Equation4205 G) : Equation4201 G := λ x y z => h x y z z
theorem Equation4206_implies_Equation4201 (G : Type*) [Magma G] (h : Equation4206 G) : Equation4201 G := λ x y z => h x y z z
theorem Equation4211_implies_Equation4210 (G : Type*) [Magma G] (h : Equation4211 G) : Equation4210 G := λ x y z => h x y z z
theorem Equation4215_implies_Equation4214 (G : Type*) [Magma G] (h : Equation4215 G) : Equation4214 G := λ x y z => h x y z z
theorem Equation4219_implies_Equation4218 (G : Type*) [Magma G] (h : Equation4219 G) : Equation4218 G := λ x y z => h x y z z
theorem Equation4220_implies_Equation4216 (G : Type*) [Magma G] (h : Equation4220 G) : Equation4216 G := λ x y z => h x y z z
theorem Equation4221_implies_Equation4217 (G : Type*) [Magma G] (h : Equation4221 G) : Equation4217 G := λ x y z => h x y z z
theorem Equation4222_implies_Equation4218 (G : Type*) [Magma G] (h : Equation4222 G) : Equation4218 G := λ x y z => h x y z z
theorem Equation4223_implies_Equation4218 (G : Type*) [Magma G] (h : Equation4223 G) : Equation4218 G := λ x y z => h x y z z
theorem Equation4228_implies_Equation4227 (G : Type*) [Magma G] (h : Equation4228 G) : Equation4227 G := λ x y z => h x y z z
theorem Equation4232_implies_Equation4231 (G : Type*) [Magma G] (h : Equation4232 G) : Equation4231 G := λ x y z => h x y z z
theorem Equation4236_implies_Equation4235 (G : Type*) [Magma G] (h : Equation4236 G) : Equation4235 G := λ x y z => h x y z z
theorem Equation4237_implies_Equation4233 (G : Type*) [Magma G] (h : Equation4237 G) : Equation4233 G := λ x y z => h x y z z
theorem Equation4238_implies_Equation4234 (G : Type*) [Magma G] (h : Equation4238 G) : Equation4234 G := λ x y z => h x y z z
theorem Equation4239_implies_Equation4235 (G : Type*) [Magma G] (h : Equation4239 G) : Equation4235 G := λ x y z => h x y z z
theorem Equation4240_implies_Equation4235 (G : Type*) [Magma G] (h : Equation4240 G) : Equation4235 G := λ x y z => h x y z z
theorem Equation4242_implies_Equation4225 (G : Type*) [Magma G] (h : Equation4242 G) : Equation4225 G := λ x y z => h x y z z
theorem Equation4243_implies_Equation4226 (G : Type*) [Magma G] (h : Equation4243 G) : Equation4226 G := λ x y z => h x y z z
theorem Equation4244_implies_Equation4227 (G : Type*) [Magma G] (h : Equation4244 G) : Equation4227 G := λ x y z => h x y z z
theorem Equation4245_implies_Equation4227 (G : Type*) [Magma G] (h : Equation4245 G) : Equation4227 G := λ x y z => h x y z z
theorem Equation4247_implies_Equation4229 (G : Type*) [Magma G] (h : Equation4247 G) : Equation4229 G := λ x y z => h x y z z
theorem Equation4248_implies_Equation4230 (G : Type*) [Magma G] (h : Equation4248 G) : Equation4230 G := λ x y z => h x y z z
theorem Equation4249_implies_Equation4231 (G : Type*) [Magma G] (h : Equation4249 G) : Equation4231 G := λ x y z => h x y z z
theorem Equation4250_implies_Equation4231 (G : Type*) [Magma G] (h : Equation4250 G) : Equation4231 G := λ x y z => h x y z z
theorem Equation4252_implies_Equation4233 (G : Type*) [Magma G] (h : Equation4252 G) : Equation4233 G := λ x y z => h x y z z
theorem Equation4253_implies_Equation4234 (G : Type*) [Magma G] (h : Equation4253 G) : Equation4234 G := λ x y z => h x y z z
theorem Equation4254_implies_Equation4235 (G : Type*) [Magma G] (h : Equation4254 G) : Equation4235 G := λ x y z => h x y z z
theorem Equation4255_implies_Equation4235 (G : Type*) [Magma G] (h : Equation4255 G) : Equation4235 G := λ x y z => h x y z z
theorem Equation4257_implies_Equation4233 (G : Type*) [Magma G] (h : Equation4257 G) : Equation4233 G := λ x y z => h x y z z
theorem Equation4258_implies_Equation4234 (G : Type*) [Magma G] (h : Equation4258 G) : Equation4234 G := λ x y z => h x y z z
theorem Equation4259_implies_Equation4235 (G : Type*) [Magma G] (h : Equation4259 G) : Equation4235 G := λ x y z => h x y z z
theorem Equation4260_implies_Equation4235 (G : Type*) [Magma G] (h : Equation4260 G) : Equation4235 G := λ x y z => h x y z z
theorem Equation4281_implies_Equation4280 (G : Type*) [Magma G] (h : Equation4281 G) : Equation4280 G := λ x y z => h x y z z
theorem Equation4289_implies_Equation4288 (G : Type*) [Magma G] (h : Equation4289 G) : Equation4288 G := λ x y z => h x y z z
theorem Equation4298_implies_Equation4297 (G : Type*) [Magma G] (h : Equation4298 G) : Equation4297 G := λ x y z => h x y z z
theorem Equation4302_implies_Equation4301 (G : Type*) [Magma G] (h : Equation4302 G) : Equation4301 G := λ x y z => h x y z z
theorem Equation4306_implies_Equation4305 (G : Type*) [Magma G] (h : Equation4306 G) : Equation4305 G := λ x y z => h x y z z
theorem Equation4310_implies_Equation4307 (G : Type*) [Magma G] (h : Equation4310 G) : Equation4307 G := λ x y z => h x y z z
theorem Equation4319_implies_Equation4318 (G : Type*) [Magma G] (h : Equation4319 G) : Equation4318 G := λ x y z => h x y z z
theorem Equation4326_implies_Equation4325 (G : Type*) [Magma G] (h : Equation4326 G) : Equation4325 G := λ x y z => h x y z z
theorem Equation4333_implies_Equation4332 (G : Type*) [Magma G] (h : Equation4333 G) : Equation4332 G := λ x y z => h x y z z
theorem Equation4342_implies_Equation4341 (G : Type*) [Magma G] (h : Equation4342 G) : Equation4341 G := λ x y z => h x y z z
theorem Equation4347_implies_Equation4346 (G : Type*) [Magma G] (h : Equation4347 G) : Equation4346 G := λ x y z => h x y z z
theorem Equation4363_implies_Equation4362 (G : Type*) [Magma G] (h : Equation4363 G) : Equation4362 G := λ x y z => h x y z z
theorem Equation4366_implies_Equation4364 (G : Type*) [Magma G] (h : Equation4366 G) : Equation4364 G := λ x y z => h x y z z
theorem Equation4394_implies_Equation4393 (G : Type*) [Magma G] (h : Equation4394 G) : Equation4393 G := λ x y z => h x y z z
theorem Equation4404_implies_Equation4403 (G : Type*) [Magma G] (h : Equation4404 G) : Equation4403 G := λ x y z => h x y z z
theorem Equation4414_implies_Equation4413 (G : Type*) [Magma G] (h : Equation4414 G) : Equation4413 G := λ x y z => h x y z z
theorem Equation4418_implies_Equation4417 (G : Type*) [Magma G] (h : Equation4418 G) : Equation4417 G := λ x y z => h x y z z
theorem Equation4422_implies_Equation4421 (G : Type*) [Magma G] (h : Equation4422 G) : Equation4421 G := λ x y z => h x y z z
theorem Equation4426_implies_Equation4425 (G : Type*) [Magma G] (h : Equation4426 G) : Equation4425 G := λ x y z => h x y z z
theorem Equation4427_implies_Equation4423 (G : Type*) [Magma G] (h : Equation4427 G) : Equation4423 G := λ x y z => h x y z z
theorem Equation4428_implies_Equation4424 (G : Type*) [Magma G] (h : Equation4428 G) : Equation4424 G := λ x y z => h x y z z
theorem Equation4429_implies_Equation4425 (G : Type*) [Magma G] (h : Equation4429 G) : Equation4425 G := λ x y z => h x y z z
theorem Equation4430_implies_Equation4425 (G : Type*) [Magma G] (h : Equation4430 G) : Equation4425 G := λ x y z => h x y z z
theorem Equation4441_implies_Equation4440 (G : Type*) [Magma G] (h : Equation4441 G) : Equation4440 G := λ x y z => h x y z z
theorem Equation4451_implies_Equation4450 (G : Type*) [Magma G] (h : Equation4451 G) : Equation4450 G := λ x y z => h x y z z
theorem Equation4455_implies_Equation4454 (G : Type*) [Magma G] (h : Equation4455 G) : Equation4454 G := λ x y z => h x y z z
theorem Equation4459_implies_Equation4458 (G : Type*) [Magma G] (h : Equation4459 G) : Equation4458 G := λ x y z => h x y z z
theorem Equation4463_implies_Equation4462 (G : Type*) [Magma G] (h : Equation4463 G) : Equation4462 G := λ x y z => h x y z z
theorem Equation4464_implies_Equation4460 (G : Type*) [Magma G] (h : Equation4464 G) : Equation4460 G := λ x y z => h x y z z
theorem Equation4465_implies_Equation4461 (G : Type*) [Magma G] (h : Equation4465 G) : Equation4461 G := λ x y z => h x y z z
theorem Equation4466_implies_Equation4462 (G : Type*) [Magma G] (h : Equation4466 G) : Equation4462 G := λ x y z => h x y z z
theorem Equation4467_implies_Equation4462 (G : Type*) [Magma G] (h : Equation4467 G) : Equation4462 G := λ x y z => h x y z z
theorem Equation4478_implies_Equation4477 (G : Type*) [Magma G] (h : Equation4478 G) : Equation4477 G := λ x y z => h x y z z
theorem Equation4488_implies_Equation4487 (G : Type*) [Magma G] (h : Equation4488 G) : Equation4487 G := λ x y z => h x y z z
theorem Equation4492_implies_Equation4491 (G : Type*) [Magma G] (h : Equation4492 G) : Equation4491 G := λ x y z => h x y z z
theorem Equation4496_implies_Equation4495 (G : Type*) [Magma G] (h : Equation4496 G) : Equation4495 G := λ x y z => h x y z z
theorem Equation4500_implies_Equation4499 (G : Type*) [Magma G] (h : Equation4500 G) : Equation4499 G := λ x y z => h x y z z
theorem Equation4501_implies_Equation4497 (G : Type*) [Magma G] (h : Equation4501 G) : Equation4497 G := λ x y z => h x y z z
theorem Equation4502_implies_Equation4498 (G : Type*) [Magma G] (h : Equation4502 G) : Equation4498 G := λ x y z => h x y z z
theorem Equation4503_implies_Equation4499 (G : Type*) [Magma G] (h : Equation4503 G) : Equation4499 G := λ x y z => h x y z z
theorem Equation4504_implies_Equation4499 (G : Type*) [Magma G] (h : Equation4504 G) : Equation4499 G := λ x y z => h x y z z
theorem Equation4509_implies_Equation4508 (G : Type*) [Magma G] (h : Equation4509 G) : Equation4508 G := λ x y z => h x y z z
theorem Equation4513_implies_Equation4512 (G : Type*) [Magma G] (h : Equation4513 G) : Equation4512 G := λ x y z => h x y z z
theorem Equation4517_implies_Equation4516 (G : Type*) [Magma G] (h : Equation4517 G) : Equation4516 G := λ x y z => h x y z z
theorem Equation4518_implies_Equation4514 (G : Type*) [Magma G] (h : Equation4518 G) : Equation4514 G := λ x y z => h x y z z
theorem Equation4519_implies_Equation4515 (G : Type*) [Magma G] (h : Equation4519 G) : Equation4515 G := λ x y z => h x y z z
theorem Equation4520_implies_Equation4516 (G : Type*) [Magma G] (h : Equation4520 G) : Equation4516 G := λ x y z => h x y z z
theorem Equation4521_implies_Equation4516 (G : Type*) [Magma G] (h : Equation4521 G) : Equation4516 G := λ x y z => h x y z z
theorem Equation4526_implies_Equation4525 (G : Type*) [Magma G] (h : Equation4526 G) : Equation4525 G := λ x y z => h x y z z
theorem Equation4530_implies_Equation4529 (G : Type*) [Magma G] (h : Equation4530 G) : Equation4529 G := λ x y z => h x y z z
theorem Equation4534_implies_Equation4533 (G : Type*) [Magma G] (h : Equation4534 G) : Equation4533 G := λ x y z => h x y z z
theorem Equation4535_implies_Equation4531 (G : Type*) [Magma G] (h : Equation4535 G) : Equation4531 G := λ x y z => h x y z z
theorem Equation4536_implies_Equation4532 (G : Type*) [Magma G] (h : Equation4536 G) : Equation4532 G := λ x y z => h x y z z
theorem Equation4537_implies_Equation4533 (G : Type*) [Magma G] (h : Equation4537 G) : Equation4533 G := λ x y z => h x y z z
theorem Equation4538_implies_Equation4533 (G : Type*) [Magma G] (h : Equation4538 G) : Equation4533 G := λ x y z => h x y z z
theorem Equation4543_implies_Equation4542 (G : Type*) [Magma G] (h : Equation4543 G) : Equation4542 G := λ x y z => h x y z z
theorem Equation4547_implies_Equation4546 (G : Type*) [Magma G] (h : Equation4547 G) : Equation4546 G := λ x y z => h x y z z
theorem Equation4551_implies_Equation4550 (G : Type*) [Magma G] (h : Equation4551 G) : Equation4550 G := λ x y z => h x y z z
theorem Equation4552_implies_Equation4548 (G : Type*) [Magma G] (h : Equation4552 G) : Equation4548 G := λ x y z => h x y z z
theorem Equation4553_implies_Equation4549 (G : Type*) [Magma G] (h : Equation4553 G) : Equation4549 G := λ x y z => h x y z z
theorem Equation4554_implies_Equation4550 (G : Type*) [Magma G] (h : Equation4554 G) : Equation4550 G := λ x y z => h x y z z
theorem Equation4555_implies_Equation4550 (G : Type*) [Magma G] (h : Equation4555 G) : Equation4550 G := λ x y z => h x y z z
theorem Equation4557_implies_Equation4540 (G : Type*) [Magma G] (h : Equation4557 G) : Equation4540 G := λ x y z => h x y z z
theorem Equation4558_implies_Equation4541 (G : Type*) [Magma G] (h : Equation4558 G) : Equation4541 G := λ x y z => h x y z z
theorem Equation4559_implies_Equation4542 (G : Type*) [Magma G] (h : Equation4559 G) : Equation4542 G := λ x y z => h x y z z
theorem Equation4560_implies_Equation4542 (G : Type*) [Magma G] (h : Equation4560 G) : Equation4542 G := λ x y z => h x y z z
theorem Equation4562_implies_Equation4544 (G : Type*) [Magma G] (h : Equation4562 G) : Equation4544 G := λ x y z => h x y z z
theorem Equation4563_implies_Equation4545 (G : Type*) [Magma G] (h : Equation4563 G) : Equation4545 G := λ x y z => h x y z z
theorem Equation4564_implies_Equation4546 (G : Type*) [Magma G] (h : Equation4564 G) : Equation4546 G := λ x y z => h x y z z
theorem Equation4565_implies_Equation4546 (G : Type*) [Magma G] (h : Equation4565 G) : Equation4546 G := λ x y z => h x y z z
theorem Equation4567_implies_Equation4548 (G : Type*) [Magma G] (h : Equation4567 G) : Equation4548 G := λ x y z => h x y z z
theorem Equation4568_implies_Equation4549 (G : Type*) [Magma G] (h : Equation4568 G) : Equation4549 G := λ x y z => h x y z z
theorem Equation4569_implies_Equation4550 (G : Type*) [Magma G] (h : Equation4569 G) : Equation4550 G := λ x y z => h x y z z
theorem Equation4570_implies_Equation4550 (G : Type*) [Magma G] (h : Equation4570 G) : Equation4550 G := λ x y z => h x y z z
theorem Equation4572_implies_Equation4548 (G : Type*) [Magma G] (h : Equation4572 G) : Equation4548 G := λ x y z => h x y z z
theorem Equation4573_implies_Equation4549 (G : Type*) [Magma G] (h : Equation4573 G) : Equation4549 G := λ x y z => h x y z z
theorem Equation4574_implies_Equation4550 (G : Type*) [Magma G] (h : Equation4574 G) : Equation4550 G := λ x y z => h x y z z
theorem Equation4575_implies_Equation4550 (G : Type*) [Magma G] (h : Equation4575 G) : Equation4550 G := λ x y z => h x y z z
theorem Equation4596_implies_Equation4595 (G : Type*) [Magma G] (h : Equation4596 G) : Equation4595 G := λ x y z => h x y z z
theorem Equation4604_implies_Equation4603 (G : Type*) [Magma G] (h : Equation4604 G) : Equation4603 G := λ x y z => h x y z z
theorem Equation4613_implies_Equation4612 (G : Type*) [Magma G] (h : Equation4613 G) : Equation4612 G := λ x y z => h x y z z
theorem Equation4617_implies_Equation4616 (G : Type*) [Magma G] (h : Equation4617 G) : Equation4616 G := λ x y z => h x y z z
theorem Equation4621_implies_Equation4620 (G : Type*) [Magma G] (h : Equation4621 G) : Equation4620 G := λ x y z => h x y z z
theorem Equation4625_implies_Equation4622 (G : Type*) [Magma G] (h : Equation4625 G) : Equation4622 G := λ x y z => h x y z z
theorem Equation4634_implies_Equation4633 (G : Type*) [Magma G] (h : Equation4634 G) : Equation4633 G := λ x y z => h x y z z
theorem Equation4641_implies_Equation4640 (G : Type*) [Magma G] (h : Equation4641 G) : Equation4640 G := λ x y z => h x y z z
theorem Equation4648_implies_Equation4647 (G : Type*) [Magma G] (h : Equation4648 G) : Equation4647 G := λ x y z => h x y z z
theorem Equation4657_implies_Equation4656 (G : Type*) [Magma G] (h : Equation4657 G) : Equation4656 G := λ x y z => h x y z z
theorem Equation4662_implies_Equation4661 (G : Type*) [Magma G] (h : Equation4662 G) : Equation4661 G := λ x y z => h x y z z
theorem Equation4678_implies_Equation4677 (G : Type*) [Magma G] (h : Equation4678 G) : Equation4677 G := λ x y z => h x y z z
theorem Equation4681_implies_Equation4679 (G : Type*) [Magma G] (h : Equation4681 G) : Equation4679 G := λ x y z => h x y z z