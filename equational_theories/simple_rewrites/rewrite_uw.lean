import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation97 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ w))
def Equation98 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ u))
def Equation149 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ w)
def Equation150 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ u)
def Equation201 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ w)
def Equation202 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ u)
def Equation253 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ w
def Equation254 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ u
def Equation305 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ w
def Equation306 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ u
def Equation357 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ w)
def Equation358 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ u)
def Equation409 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ w
def Equation410 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ u
def Equation461 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (w ∘ w)))
def Equation462 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (y ∘ (z ∘ (w ∘ u)))
def Equation498 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (w ∘ w)))
def Equation499 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (x ∘ (z ∘ (w ∘ u)))
def Equation535 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (w ∘ w)))
def Equation536 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (y ∘ (z ∘ (w ∘ u)))
def Equation552 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (w ∘ w)))
def Equation553 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (x ∘ (w ∘ u)))
def Equation569 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (w ∘ w)))
def Equation570 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (y ∘ (w ∘ u)))
def Equation586 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (w ∘ w)))
def Equation587 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (z ∘ (w ∘ u)))
def Equation591 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (x ∘ w)))
def Equation592 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (x ∘ u)))
def Equation596 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (y ∘ w)))
def Equation597 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (y ∘ u)))
def Equation601 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (z ∘ w)))
def Equation602 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (z ∘ u)))
def Equation603 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (w ∘ x)))
def Equation604 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (w ∘ y)))
def Equation605 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (w ∘ z)))
def Equation606 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (w ∘ w)))
def Equation607 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (w ∘ u)))
def Equation608 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (u ∘ x)))
def Equation609 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (u ∘ y)))
def Equation610 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (u ∘ z)))
def Equation611 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (u ∘ w)))
def Equation612 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (u ∘ u)))
def Equation664 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ w) ∘ w))
def Equation665 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (y ∘ ((z ∘ w) ∘ u))
def Equation701 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ w) ∘ w))
def Equation702 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (x ∘ ((z ∘ w) ∘ u))
def Equation738 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ w) ∘ w))
def Equation739 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (y ∘ ((z ∘ w) ∘ u))
def Equation755 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ w) ∘ w))
def Equation756 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((x ∘ w) ∘ u))
def Equation772 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ w) ∘ w))
def Equation773 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((y ∘ w) ∘ u))
def Equation789 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ w) ∘ w))
def Equation790 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((z ∘ w) ∘ u))
def Equation794 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ x) ∘ w))
def Equation795 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ x) ∘ u))
def Equation799 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ y) ∘ w))
def Equation800 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ y) ∘ u))
def Equation804 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ z) ∘ w))
def Equation805 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ z) ∘ u))
def Equation806 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ w) ∘ x))
def Equation807 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ w) ∘ y))
def Equation808 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ w) ∘ z))
def Equation809 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ w) ∘ w))
def Equation810 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ w) ∘ u))
def Equation811 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ u) ∘ x))
def Equation812 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ u) ∘ y))
def Equation813 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ u) ∘ z))
def Equation814 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ u) ∘ w))
def Equation815 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ u) ∘ u))
def Equation867 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (w ∘ w))
def Equation868 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ ((y ∘ z) ∘ (w ∘ u))
def Equation904 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (w ∘ w))
def Equation905 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((x ∘ z) ∘ (w ∘ u))
def Equation941 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (w ∘ w))
def Equation942 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((y ∘ z) ∘ (w ∘ u))
def Equation958 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (w ∘ w))
def Equation959 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ x) ∘ (w ∘ u))
def Equation975 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (w ∘ w))
def Equation976 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ y) ∘ (w ∘ u))
def Equation992 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (w ∘ w))
def Equation993 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ z) ∘ (w ∘ u))
def Equation997 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (x ∘ w))
def Equation998 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (x ∘ u))
def Equation1002 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (y ∘ w))
def Equation1003 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (y ∘ u))
def Equation1007 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (z ∘ w))
def Equation1008 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (z ∘ u))
def Equation1009 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (w ∘ x))
def Equation1010 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (w ∘ y))
def Equation1011 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (w ∘ z))
def Equation1012 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (w ∘ w))
def Equation1013 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (w ∘ u))
def Equation1014 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (u ∘ x))
def Equation1015 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (u ∘ y))
def Equation1016 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (u ∘ z))
def Equation1017 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (u ∘ w))
def Equation1018 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (u ∘ u))
def Equation1070 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ w)
def Equation1071 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ u)
def Equation1107 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ w)) ∘ w)
def Equation1108 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((x ∘ (z ∘ w)) ∘ u)
def Equation1144 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ w)) ∘ w)
def Equation1145 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((y ∘ (z ∘ w)) ∘ u)
def Equation1161 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ w)
def Equation1162 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ u)
def Equation1178 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ w)
def Equation1179 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ u)
def Equation1195 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ w)) ∘ w)
def Equation1196 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (z ∘ w)) ∘ u)
def Equation1200 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ x)) ∘ w)
def Equation1201 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ x)) ∘ u)
def Equation1205 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ y)) ∘ w)
def Equation1206 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ y)) ∘ u)
def Equation1210 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ z)) ∘ w)
def Equation1211 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ z)) ∘ u)
def Equation1212 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ w)) ∘ x)
def Equation1213 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ w)) ∘ y)
def Equation1214 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ w)) ∘ z)
def Equation1215 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ w)) ∘ w)
def Equation1216 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ w)) ∘ u)
def Equation1217 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ x)
def Equation1218 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ y)
def Equation1219 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ z)
def Equation1220 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ w)
def Equation1221 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ u)
def Equation1273 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ w) ∘ w)
def Equation1274 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (((y ∘ z) ∘ w) ∘ u)
def Equation1310 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ w) ∘ w)
def Equation1311 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((x ∘ z) ∘ w) ∘ u)
def Equation1347 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ w) ∘ w)
def Equation1348 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((y ∘ z) ∘ w) ∘ u)
def Equation1364 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ w) ∘ w)
def Equation1365 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ x) ∘ w) ∘ u)
def Equation1381 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ w) ∘ w)
def Equation1382 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ y) ∘ w) ∘ u)
def Equation1398 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ w) ∘ w)
def Equation1399 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ z) ∘ w) ∘ u)
def Equation1403 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ x) ∘ w)
def Equation1404 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ x) ∘ u)
def Equation1408 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ y) ∘ w)
def Equation1409 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ y) ∘ u)
def Equation1413 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ z) ∘ w)
def Equation1414 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ z) ∘ u)
def Equation1415 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ w) ∘ x)
def Equation1416 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ w) ∘ y)
def Equation1417 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ w) ∘ z)
def Equation1418 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ w) ∘ w)
def Equation1419 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ w) ∘ u)
def Equation1420 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ u) ∘ x)
def Equation1421 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ u) ∘ y)
def Equation1422 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ u) ∘ z)
def Equation1423 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ u) ∘ w)
def Equation1424 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ u) ∘ u)
def Equation1476 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (w ∘ w))
def Equation1477 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ y) ∘ (z ∘ (w ∘ u))
def Equation1513 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (w ∘ w))
def Equation1514 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ x) ∘ (z ∘ (w ∘ u))
def Equation1550 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (w ∘ w))
def Equation1551 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ y) ∘ (z ∘ (w ∘ u))
def Equation1567 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (w ∘ w))
def Equation1568 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (x ∘ (w ∘ u))
def Equation1584 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (w ∘ w))
def Equation1585 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (y ∘ (w ∘ u))
def Equation1601 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (w ∘ w))
def Equation1602 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (z ∘ (w ∘ u))
def Equation1606 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (x ∘ w))
def Equation1607 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (x ∘ u))
def Equation1611 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (y ∘ w))
def Equation1612 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (y ∘ u))
def Equation1616 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (z ∘ w))
def Equation1617 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (z ∘ u))
def Equation1618 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (w ∘ x))
def Equation1619 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (w ∘ y))
def Equation1620 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (w ∘ z))
def Equation1621 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (w ∘ w))
def Equation1622 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (w ∘ u))
def Equation1623 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (u ∘ x))
def Equation1624 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (u ∘ y))
def Equation1625 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (u ∘ z))
def Equation1626 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (u ∘ w))
def Equation1627 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (u ∘ u))
def Equation1679 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ w)
def Equation1680 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ u)
def Equation1716 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ w) ∘ w)
def Equation1717 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ x) ∘ ((z ∘ w) ∘ u)
def Equation1753 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ w) ∘ w)
def Equation1754 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ y) ∘ ((z ∘ w) ∘ u)
def Equation1770 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ w)
def Equation1771 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ u)
def Equation1787 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ w)
def Equation1788 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ u)
def Equation1804 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ w) ∘ w)
def Equation1805 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((z ∘ w) ∘ u)
def Equation1809 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ x) ∘ w)
def Equation1810 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ x) ∘ u)
def Equation1814 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ y) ∘ w)
def Equation1815 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ y) ∘ u)
def Equation1819 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ z) ∘ w)
def Equation1820 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ z) ∘ u)
def Equation1821 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ w) ∘ x)
def Equation1822 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ w) ∘ y)
def Equation1823 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ w) ∘ z)
def Equation1824 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ w) ∘ w)
def Equation1825 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ w) ∘ u)
def Equation1826 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ x)
def Equation1827 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ y)
def Equation1828 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ z)
def Equation1829 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ w)
def Equation1830 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ u)
def Equation1882 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ w)
def Equation1883 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ u)
def Equation1919 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (w ∘ w)
def Equation1920 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (x ∘ z)) ∘ (w ∘ u)
def Equation1956 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (w ∘ w)
def Equation1957 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (y ∘ z)) ∘ (w ∘ u)
def Equation1973 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ w)
def Equation1974 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ u)
def Equation1990 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ w)
def Equation1991 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ u)
def Equation2007 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (w ∘ w)
def Equation2008 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ z)) ∘ (w ∘ u)
def Equation2012 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (x ∘ w)
def Equation2013 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (x ∘ u)
def Equation2017 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (y ∘ w)
def Equation2018 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (y ∘ u)
def Equation2022 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (z ∘ w)
def Equation2023 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (z ∘ u)
def Equation2024 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (w ∘ x)
def Equation2025 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (w ∘ y)
def Equation2026 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (w ∘ z)
def Equation2027 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (w ∘ w)
def Equation2028 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (w ∘ u)
def Equation2029 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ x)
def Equation2030 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ y)
def Equation2031 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ z)
def Equation2032 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ w)
def Equation2033 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ u)
def Equation2085 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ w)
def Equation2086 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ u)
def Equation2122 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (w ∘ w)
def Equation2123 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ x) ∘ z) ∘ (w ∘ u)
def Equation2159 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (w ∘ w)
def Equation2160 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ y) ∘ z) ∘ (w ∘ u)
def Equation2176 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ w)
def Equation2177 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ u)
def Equation2193 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ w)
def Equation2194 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ u)
def Equation2210 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (w ∘ w)
def Equation2211 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ z) ∘ (w ∘ u)
def Equation2215 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (x ∘ w)
def Equation2216 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (x ∘ u)
def Equation2220 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (y ∘ w)
def Equation2221 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (y ∘ u)
def Equation2225 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (z ∘ w)
def Equation2226 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (z ∘ u)
def Equation2227 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (w ∘ x)
def Equation2228 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (w ∘ y)
def Equation2229 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (w ∘ z)
def Equation2230 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (w ∘ w)
def Equation2231 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (w ∘ u)
def Equation2232 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ x)
def Equation2233 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ y)
def Equation2234 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ z)
def Equation2235 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ w)
def Equation2236 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ u)
def Equation2288 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ w
def Equation2289 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ u
def Equation2325 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ w))) ∘ w
def Equation2326 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (x ∘ (z ∘ w))) ∘ u
def Equation2362 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ w))) ∘ w
def Equation2363 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (y ∘ (z ∘ w))) ∘ u
def Equation2379 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ w
def Equation2380 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ u
def Equation2396 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ w
def Equation2397 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ u
def Equation2413 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ w))) ∘ w
def Equation2414 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (z ∘ w))) ∘ u
def Equation2418 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ x))) ∘ w
def Equation2419 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ x))) ∘ u
def Equation2423 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ y))) ∘ w
def Equation2424 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ y))) ∘ u
def Equation2428 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ z))) ∘ w
def Equation2429 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ z))) ∘ u
def Equation2430 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ w))) ∘ x
def Equation2431 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ w))) ∘ y
def Equation2432 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ w))) ∘ z
def Equation2433 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ w))) ∘ w
def Equation2434 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ w))) ∘ u
def Equation2435 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ x
def Equation2436 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ y
def Equation2437 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ z
def Equation2438 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ w
def Equation2439 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ u
def Equation2491 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ w
def Equation2492 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ u
def Equation2528 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ w)) ∘ w
def Equation2529 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((x ∘ z) ∘ w)) ∘ u
def Equation2565 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ w)) ∘ w
def Equation2566 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((y ∘ z) ∘ w)) ∘ u
def Equation2582 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ w
def Equation2583 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ u
def Equation2599 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ w
def Equation2600 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ u
def Equation2616 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ w)) ∘ w
def Equation2617 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ z) ∘ w)) ∘ u
def Equation2621 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ x)) ∘ w
def Equation2622 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ x)) ∘ u
def Equation2626 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ y)) ∘ w
def Equation2627 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ y)) ∘ u
def Equation2631 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ z)) ∘ w
def Equation2632 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ z)) ∘ u
def Equation2633 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ w)) ∘ x
def Equation2634 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ w)) ∘ y
def Equation2635 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ w)) ∘ z
def Equation2636 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ w)) ∘ w
def Equation2637 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ w)) ∘ u
def Equation2638 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ x
def Equation2639 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ y
def Equation2640 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ z
def Equation2641 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ w
def Equation2642 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ u
def Equation2694 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ w
def Equation2695 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ u
def Equation2731 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ w)) ∘ w
def Equation2732 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ x) ∘ (z ∘ w)) ∘ u
def Equation2768 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ w)) ∘ w
def Equation2769 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ y) ∘ (z ∘ w)) ∘ u
def Equation2785 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ w
def Equation2786 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ u
def Equation2802 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ w
def Equation2803 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ u
def Equation2819 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ w)) ∘ w
def Equation2820 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (z ∘ w)) ∘ u
def Equation2824 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ x)) ∘ w
def Equation2825 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ x)) ∘ u
def Equation2829 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ y)) ∘ w
def Equation2830 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ y)) ∘ u
def Equation2834 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ z)) ∘ w
def Equation2835 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ z)) ∘ u
def Equation2836 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ w)) ∘ x
def Equation2837 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ w)) ∘ y
def Equation2838 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ w)) ∘ z
def Equation2839 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ w)) ∘ w
def Equation2840 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ w)) ∘ u
def Equation2841 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ x
def Equation2842 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ y
def Equation2843 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ z
def Equation2844 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ w
def Equation2845 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ u
def Equation2897 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ w
def Equation2898 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ u
def Equation2934 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ w) ∘ w
def Equation2935 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (x ∘ z)) ∘ w) ∘ u
def Equation2971 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ w) ∘ w
def Equation2972 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (y ∘ z)) ∘ w) ∘ u
def Equation2988 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ w
def Equation2989 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ u
def Equation3005 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ w
def Equation3006 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ u
def Equation3022 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ w) ∘ w
def Equation3023 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ z)) ∘ w) ∘ u
def Equation3027 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ x) ∘ w
def Equation3028 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ x) ∘ u
def Equation3032 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ y) ∘ w
def Equation3033 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ y) ∘ u
def Equation3037 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ z) ∘ w
def Equation3038 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ z) ∘ u
def Equation3039 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ w) ∘ x
def Equation3040 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ w) ∘ y
def Equation3041 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ w) ∘ z
def Equation3042 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ w) ∘ w
def Equation3043 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ w) ∘ u
def Equation3044 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ x
def Equation3045 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ y
def Equation3046 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ z
def Equation3047 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ w
def Equation3048 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ u
def Equation3100 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ w
def Equation3101 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ u
def Equation3137 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ w) ∘ w
def Equation3138 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ x) ∘ z) ∘ w) ∘ u
def Equation3174 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ w) ∘ w
def Equation3175 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ y) ∘ z) ∘ w) ∘ u
def Equation3191 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ w
def Equation3192 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ u
def Equation3208 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ w
def Equation3209 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ u
def Equation3225 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ w) ∘ w
def Equation3226 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ z) ∘ w) ∘ u
def Equation3230 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ x) ∘ w
def Equation3231 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ x) ∘ u
def Equation3235 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ y) ∘ w
def Equation3236 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ y) ∘ u
def Equation3240 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ z) ∘ w
def Equation3241 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ z) ∘ u
def Equation3242 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ w) ∘ x
def Equation3243 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ w) ∘ y
def Equation3244 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ w) ∘ z
def Equation3245 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ w) ∘ w
def Equation3246 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ w) ∘ u
def Equation3247 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ x
def Equation3248 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ y
def Equation3249 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ z
def Equation3250 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ w
def Equation3251 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ u
def Equation3303 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (w ∘ w))
def Equation3304 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = y ∘ (z ∘ (w ∘ u))
def Equation3340 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (w ∘ w))
def Equation3341 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = x ∘ (z ∘ (w ∘ u))
def Equation3377 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (w ∘ w))
def Equation3378 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = y ∘ (z ∘ (w ∘ u))
def Equation3394 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (w ∘ w))
def Equation3395 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (x ∘ (w ∘ u))
def Equation3411 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (w ∘ w))
def Equation3412 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (y ∘ (w ∘ u))
def Equation3428 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (w ∘ w))
def Equation3429 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (z ∘ (w ∘ u))
def Equation3433 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (x ∘ w))
def Equation3434 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (x ∘ u))
def Equation3438 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (y ∘ w))
def Equation3439 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (y ∘ u))
def Equation3443 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (z ∘ w))
def Equation3444 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (z ∘ u))
def Equation3445 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (w ∘ x))
def Equation3446 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (w ∘ y))
def Equation3447 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (w ∘ z))
def Equation3448 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (w ∘ w))
def Equation3449 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (w ∘ u))
def Equation3450 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (u ∘ x))
def Equation3451 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (u ∘ y))
def Equation3452 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (u ∘ z))
def Equation3453 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (u ∘ w))
def Equation3454 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (u ∘ u))
def Equation3506 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ w) ∘ w)
def Equation3507 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = y ∘ ((z ∘ w) ∘ u)
def Equation3543 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ w) ∘ w)
def Equation3544 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = x ∘ ((z ∘ w) ∘ u)
def Equation3580 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ w) ∘ w)
def Equation3581 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = y ∘ ((z ∘ w) ∘ u)
def Equation3597 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ w) ∘ w)
def Equation3598 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((x ∘ w) ∘ u)
def Equation3614 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ w) ∘ w)
def Equation3615 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((y ∘ w) ∘ u)
def Equation3631 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ w) ∘ w)
def Equation3632 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((z ∘ w) ∘ u)
def Equation3636 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ x) ∘ w)
def Equation3637 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ x) ∘ u)
def Equation3641 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ y) ∘ w)
def Equation3642 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ y) ∘ u)
def Equation3646 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ z) ∘ w)
def Equation3647 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ z) ∘ u)
def Equation3648 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ w) ∘ x)
def Equation3649 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ w) ∘ y)
def Equation3650 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ w) ∘ z)
def Equation3651 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ w) ∘ w)
def Equation3652 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ w) ∘ u)
def Equation3653 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ u) ∘ x)
def Equation3654 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ u) ∘ y)
def Equation3655 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ u) ∘ z)
def Equation3656 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ u) ∘ w)
def Equation3657 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ u) ∘ u)
def Equation3709 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (w ∘ w)
def Equation3710 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = (y ∘ z) ∘ (w ∘ u)
def Equation3746 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (w ∘ w)
def Equation3747 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (x ∘ z) ∘ (w ∘ u)
def Equation3783 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (w ∘ w)
def Equation3784 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (y ∘ z) ∘ (w ∘ u)
def Equation3800 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (w ∘ w)
def Equation3801 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ x) ∘ (w ∘ u)
def Equation3817 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (w ∘ w)
def Equation3818 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ y) ∘ (w ∘ u)
def Equation3834 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (w ∘ w)
def Equation3835 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ z) ∘ (w ∘ u)
def Equation3839 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (x ∘ w)
def Equation3840 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (x ∘ u)
def Equation3844 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (y ∘ w)
def Equation3845 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (y ∘ u)
def Equation3849 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (z ∘ w)
def Equation3850 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (z ∘ u)
def Equation3851 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (w ∘ x)
def Equation3852 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (w ∘ y)
def Equation3853 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (w ∘ z)
def Equation3854 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (w ∘ w)
def Equation3855 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (w ∘ u)
def Equation3856 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (u ∘ x)
def Equation3857 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (u ∘ y)
def Equation3858 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (u ∘ z)
def Equation3859 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (u ∘ w)
def Equation3860 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (u ∘ u)
def Equation3912 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ w)) ∘ w
def Equation3913 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = (y ∘ (z ∘ w)) ∘ u
def Equation3949 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ w)) ∘ w
def Equation3950 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (x ∘ (z ∘ w)) ∘ u
def Equation3986 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ w)) ∘ w
def Equation3987 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (y ∘ (z ∘ w)) ∘ u
def Equation4003 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ w)) ∘ w
def Equation4004 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (x ∘ w)) ∘ u
def Equation4020 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ w)) ∘ w
def Equation4021 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (y ∘ w)) ∘ u
def Equation4037 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ w)) ∘ w
def Equation4038 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (z ∘ w)) ∘ u
def Equation4042 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ x)) ∘ w
def Equation4043 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ x)) ∘ u
def Equation4047 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ y)) ∘ w
def Equation4048 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ y)) ∘ u
def Equation4052 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ z)) ∘ w
def Equation4053 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ z)) ∘ u
def Equation4054 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ w)) ∘ x
def Equation4055 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ w)) ∘ y
def Equation4056 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ w)) ∘ z
def Equation4057 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ w)) ∘ w
def Equation4058 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ w)) ∘ u
def Equation4059 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ u)) ∘ x
def Equation4060 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ u)) ∘ y
def Equation4061 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ u)) ∘ z
def Equation4062 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ u)) ∘ w
def Equation4063 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ u)) ∘ u
def Equation4115 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ w) ∘ w
def Equation4116 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = ((y ∘ z) ∘ w) ∘ u
def Equation4152 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ w) ∘ w
def Equation4153 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((x ∘ z) ∘ w) ∘ u
def Equation4189 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ w) ∘ w
def Equation4190 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((y ∘ z) ∘ w) ∘ u
def Equation4206 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ w) ∘ w
def Equation4207 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ x) ∘ w) ∘ u
def Equation4223 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ w) ∘ w
def Equation4224 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ y) ∘ w) ∘ u
def Equation4240 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ w) ∘ w
def Equation4241 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ z) ∘ w) ∘ u
def Equation4245 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ x) ∘ w
def Equation4246 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ x) ∘ u
def Equation4250 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ y) ∘ w
def Equation4251 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ y) ∘ u
def Equation4255 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ z) ∘ w
def Equation4256 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ z) ∘ u
def Equation4257 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ w) ∘ x
def Equation4258 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ w) ∘ y
def Equation4259 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ w) ∘ z
def Equation4260 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ w) ∘ w
def Equation4261 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ w) ∘ u
def Equation4262 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ u) ∘ x
def Equation4263 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ u) ∘ y
def Equation4264 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ u) ∘ z
def Equation4265 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ u) ∘ w
def Equation4266 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ u) ∘ u
def Equation4312 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (w ∘ w)
def Equation4313 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (x ∘ y) = z ∘ (w ∘ u)
def Equation4337 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = z ∘ (w ∘ w)
def Equation4338 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ x) = z ∘ (w ∘ u)
def Equation4355 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = z ∘ (w ∘ w)
def Equation4356 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ y) = z ∘ (w ∘ u)
def Equation4430 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ w) ∘ w
def Equation4431 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (x ∘ y) = (z ∘ w) ∘ u
def Equation4467 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ w) ∘ w
def Equation4468 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ x) = (z ∘ w) ∘ u
def Equation4504 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ w) ∘ w
def Equation4505 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ y) = (z ∘ w) ∘ u
def Equation4521 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ w) ∘ w
def Equation4522 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (x ∘ w) ∘ u
def Equation4538 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ w) ∘ w
def Equation4539 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (y ∘ w) ∘ u
def Equation4555 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ w) ∘ w
def Equation4556 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (z ∘ w) ∘ u
def Equation4560 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ x) ∘ w
def Equation4561 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ x) ∘ u
def Equation4565 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ y) ∘ w
def Equation4566 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ y) ∘ u
def Equation4570 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ z) ∘ w
def Equation4571 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ z) ∘ u
def Equation4572 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ w) ∘ x
def Equation4573 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ w) ∘ y
def Equation4574 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ w) ∘ z
def Equation4575 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ w) ∘ w
def Equation4576 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ w) ∘ u
def Equation4577 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ u) ∘ x
def Equation4578 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ u) ∘ y
def Equation4579 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ u) ∘ z
def Equation4580 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ u) ∘ w
def Equation4581 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ u) ∘ u
def Equation4627 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ w) ∘ w
def Equation4628 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ x) ∘ y = (z ∘ w) ∘ u
def Equation4652 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ x = (z ∘ w) ∘ w
def Equation4653 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ x = (z ∘ w) ∘ u
def Equation4670 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ y = (z ∘ w) ∘ w
def Equation4671 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ y = (z ∘ w) ∘ u
theorem Equation98_implies_Equation97 (G : Type*) [Magma G] (h : Equation98 G) : Equation97 G := λ x y z w => h x y z w w
theorem Equation150_implies_Equation149 (G : Type*) [Magma G] (h : Equation150 G) : Equation149 G := λ x y z w => h x y z w w
theorem Equation202_implies_Equation201 (G : Type*) [Magma G] (h : Equation202 G) : Equation201 G := λ x y z w => h x y z w w
theorem Equation254_implies_Equation253 (G : Type*) [Magma G] (h : Equation254 G) : Equation253 G := λ x y z w => h x y z w w
theorem Equation306_implies_Equation305 (G : Type*) [Magma G] (h : Equation306 G) : Equation305 G := λ x y z w => h x y z w w
theorem Equation358_implies_Equation357 (G : Type*) [Magma G] (h : Equation358 G) : Equation357 G := λ x y z w => h x y z w w
theorem Equation410_implies_Equation409 (G : Type*) [Magma G] (h : Equation410 G) : Equation409 G := λ x y z w => h x y z w w
theorem Equation462_implies_Equation461 (G : Type*) [Magma G] (h : Equation462 G) : Equation461 G := λ x y z w => h x y z w w
theorem Equation499_implies_Equation498 (G : Type*) [Magma G] (h : Equation499 G) : Equation498 G := λ x y z w => h x y z w w
theorem Equation536_implies_Equation535 (G : Type*) [Magma G] (h : Equation536 G) : Equation535 G := λ x y z w => h x y z w w
theorem Equation553_implies_Equation552 (G : Type*) [Magma G] (h : Equation553 G) : Equation552 G := λ x y z w => h x y z w w
theorem Equation570_implies_Equation569 (G : Type*) [Magma G] (h : Equation570 G) : Equation569 G := λ x y z w => h x y z w w
theorem Equation587_implies_Equation586 (G : Type*) [Magma G] (h : Equation587 G) : Equation586 G := λ x y z w => h x y z w w
theorem Equation592_implies_Equation591 (G : Type*) [Magma G] (h : Equation592 G) : Equation591 G := λ x y z w => h x y z w w
theorem Equation597_implies_Equation596 (G : Type*) [Magma G] (h : Equation597 G) : Equation596 G := λ x y z w => h x y z w w
theorem Equation602_implies_Equation601 (G : Type*) [Magma G] (h : Equation602 G) : Equation601 G := λ x y z w => h x y z w w
theorem Equation607_implies_Equation606 (G : Type*) [Magma G] (h : Equation607 G) : Equation606 G := λ x y z w => h x y z w w
theorem Equation608_implies_Equation603 (G : Type*) [Magma G] (h : Equation608 G) : Equation603 G := λ x y z w => h x y z w w
theorem Equation609_implies_Equation604 (G : Type*) [Magma G] (h : Equation609 G) : Equation604 G := λ x y z w => h x y z w w
theorem Equation610_implies_Equation605 (G : Type*) [Magma G] (h : Equation610 G) : Equation605 G := λ x y z w => h x y z w w
theorem Equation611_implies_Equation606 (G : Type*) [Magma G] (h : Equation611 G) : Equation606 G := λ x y z w => h x y z w w
theorem Equation612_implies_Equation606 (G : Type*) [Magma G] (h : Equation612 G) : Equation606 G := λ x y z w => h x y z w w
theorem Equation665_implies_Equation664 (G : Type*) [Magma G] (h : Equation665 G) : Equation664 G := λ x y z w => h x y z w w
theorem Equation702_implies_Equation701 (G : Type*) [Magma G] (h : Equation702 G) : Equation701 G := λ x y z w => h x y z w w
theorem Equation739_implies_Equation738 (G : Type*) [Magma G] (h : Equation739 G) : Equation738 G := λ x y z w => h x y z w w
theorem Equation756_implies_Equation755 (G : Type*) [Magma G] (h : Equation756 G) : Equation755 G := λ x y z w => h x y z w w
theorem Equation773_implies_Equation772 (G : Type*) [Magma G] (h : Equation773 G) : Equation772 G := λ x y z w => h x y z w w
theorem Equation790_implies_Equation789 (G : Type*) [Magma G] (h : Equation790 G) : Equation789 G := λ x y z w => h x y z w w
theorem Equation795_implies_Equation794 (G : Type*) [Magma G] (h : Equation795 G) : Equation794 G := λ x y z w => h x y z w w
theorem Equation800_implies_Equation799 (G : Type*) [Magma G] (h : Equation800 G) : Equation799 G := λ x y z w => h x y z w w
theorem Equation805_implies_Equation804 (G : Type*) [Magma G] (h : Equation805 G) : Equation804 G := λ x y z w => h x y z w w
theorem Equation810_implies_Equation809 (G : Type*) [Magma G] (h : Equation810 G) : Equation809 G := λ x y z w => h x y z w w
theorem Equation811_implies_Equation806 (G : Type*) [Magma G] (h : Equation811 G) : Equation806 G := λ x y z w => h x y z w w
theorem Equation812_implies_Equation807 (G : Type*) [Magma G] (h : Equation812 G) : Equation807 G := λ x y z w => h x y z w w
theorem Equation813_implies_Equation808 (G : Type*) [Magma G] (h : Equation813 G) : Equation808 G := λ x y z w => h x y z w w
theorem Equation814_implies_Equation809 (G : Type*) [Magma G] (h : Equation814 G) : Equation809 G := λ x y z w => h x y z w w
theorem Equation815_implies_Equation809 (G : Type*) [Magma G] (h : Equation815 G) : Equation809 G := λ x y z w => h x y z w w
theorem Equation868_implies_Equation867 (G : Type*) [Magma G] (h : Equation868 G) : Equation867 G := λ x y z w => h x y z w w
theorem Equation905_implies_Equation904 (G : Type*) [Magma G] (h : Equation905 G) : Equation904 G := λ x y z w => h x y z w w
theorem Equation942_implies_Equation941 (G : Type*) [Magma G] (h : Equation942 G) : Equation941 G := λ x y z w => h x y z w w
theorem Equation959_implies_Equation958 (G : Type*) [Magma G] (h : Equation959 G) : Equation958 G := λ x y z w => h x y z w w
theorem Equation976_implies_Equation975 (G : Type*) [Magma G] (h : Equation976 G) : Equation975 G := λ x y z w => h x y z w w
theorem Equation993_implies_Equation992 (G : Type*) [Magma G] (h : Equation993 G) : Equation992 G := λ x y z w => h x y z w w
theorem Equation998_implies_Equation997 (G : Type*) [Magma G] (h : Equation998 G) : Equation997 G := λ x y z w => h x y z w w
theorem Equation1003_implies_Equation1002 (G : Type*) [Magma G] (h : Equation1003 G) : Equation1002 G := λ x y z w => h x y z w w
theorem Equation1008_implies_Equation1007 (G : Type*) [Magma G] (h : Equation1008 G) : Equation1007 G := λ x y z w => h x y z w w
theorem Equation1013_implies_Equation1012 (G : Type*) [Magma G] (h : Equation1013 G) : Equation1012 G := λ x y z w => h x y z w w
theorem Equation1014_implies_Equation1009 (G : Type*) [Magma G] (h : Equation1014 G) : Equation1009 G := λ x y z w => h x y z w w
theorem Equation1015_implies_Equation1010 (G : Type*) [Magma G] (h : Equation1015 G) : Equation1010 G := λ x y z w => h x y z w w
theorem Equation1016_implies_Equation1011 (G : Type*) [Magma G] (h : Equation1016 G) : Equation1011 G := λ x y z w => h x y z w w
theorem Equation1017_implies_Equation1012 (G : Type*) [Magma G] (h : Equation1017 G) : Equation1012 G := λ x y z w => h x y z w w
theorem Equation1018_implies_Equation1012 (G : Type*) [Magma G] (h : Equation1018 G) : Equation1012 G := λ x y z w => h x y z w w
theorem Equation1071_implies_Equation1070 (G : Type*) [Magma G] (h : Equation1071 G) : Equation1070 G := λ x y z w => h x y z w w
theorem Equation1108_implies_Equation1107 (G : Type*) [Magma G] (h : Equation1108 G) : Equation1107 G := λ x y z w => h x y z w w
theorem Equation1145_implies_Equation1144 (G : Type*) [Magma G] (h : Equation1145 G) : Equation1144 G := λ x y z w => h x y z w w
theorem Equation1162_implies_Equation1161 (G : Type*) [Magma G] (h : Equation1162 G) : Equation1161 G := λ x y z w => h x y z w w
theorem Equation1179_implies_Equation1178 (G : Type*) [Magma G] (h : Equation1179 G) : Equation1178 G := λ x y z w => h x y z w w
theorem Equation1196_implies_Equation1195 (G : Type*) [Magma G] (h : Equation1196 G) : Equation1195 G := λ x y z w => h x y z w w
theorem Equation1201_implies_Equation1200 (G : Type*) [Magma G] (h : Equation1201 G) : Equation1200 G := λ x y z w => h x y z w w
theorem Equation1206_implies_Equation1205 (G : Type*) [Magma G] (h : Equation1206 G) : Equation1205 G := λ x y z w => h x y z w w
theorem Equation1211_implies_Equation1210 (G : Type*) [Magma G] (h : Equation1211 G) : Equation1210 G := λ x y z w => h x y z w w
theorem Equation1216_implies_Equation1215 (G : Type*) [Magma G] (h : Equation1216 G) : Equation1215 G := λ x y z w => h x y z w w
theorem Equation1217_implies_Equation1212 (G : Type*) [Magma G] (h : Equation1217 G) : Equation1212 G := λ x y z w => h x y z w w
theorem Equation1218_implies_Equation1213 (G : Type*) [Magma G] (h : Equation1218 G) : Equation1213 G := λ x y z w => h x y z w w
theorem Equation1219_implies_Equation1214 (G : Type*) [Magma G] (h : Equation1219 G) : Equation1214 G := λ x y z w => h x y z w w
theorem Equation1220_implies_Equation1215 (G : Type*) [Magma G] (h : Equation1220 G) : Equation1215 G := λ x y z w => h x y z w w
theorem Equation1221_implies_Equation1215 (G : Type*) [Magma G] (h : Equation1221 G) : Equation1215 G := λ x y z w => h x y z w w
theorem Equation1274_implies_Equation1273 (G : Type*) [Magma G] (h : Equation1274 G) : Equation1273 G := λ x y z w => h x y z w w
theorem Equation1311_implies_Equation1310 (G : Type*) [Magma G] (h : Equation1311 G) : Equation1310 G := λ x y z w => h x y z w w
theorem Equation1348_implies_Equation1347 (G : Type*) [Magma G] (h : Equation1348 G) : Equation1347 G := λ x y z w => h x y z w w
theorem Equation1365_implies_Equation1364 (G : Type*) [Magma G] (h : Equation1365 G) : Equation1364 G := λ x y z w => h x y z w w
theorem Equation1382_implies_Equation1381 (G : Type*) [Magma G] (h : Equation1382 G) : Equation1381 G := λ x y z w => h x y z w w
theorem Equation1399_implies_Equation1398 (G : Type*) [Magma G] (h : Equation1399 G) : Equation1398 G := λ x y z w => h x y z w w
theorem Equation1404_implies_Equation1403 (G : Type*) [Magma G] (h : Equation1404 G) : Equation1403 G := λ x y z w => h x y z w w
theorem Equation1409_implies_Equation1408 (G : Type*) [Magma G] (h : Equation1409 G) : Equation1408 G := λ x y z w => h x y z w w
theorem Equation1414_implies_Equation1413 (G : Type*) [Magma G] (h : Equation1414 G) : Equation1413 G := λ x y z w => h x y z w w
theorem Equation1419_implies_Equation1418 (G : Type*) [Magma G] (h : Equation1419 G) : Equation1418 G := λ x y z w => h x y z w w
theorem Equation1420_implies_Equation1415 (G : Type*) [Magma G] (h : Equation1420 G) : Equation1415 G := λ x y z w => h x y z w w
theorem Equation1421_implies_Equation1416 (G : Type*) [Magma G] (h : Equation1421 G) : Equation1416 G := λ x y z w => h x y z w w
theorem Equation1422_implies_Equation1417 (G : Type*) [Magma G] (h : Equation1422 G) : Equation1417 G := λ x y z w => h x y z w w
theorem Equation1423_implies_Equation1418 (G : Type*) [Magma G] (h : Equation1423 G) : Equation1418 G := λ x y z w => h x y z w w
theorem Equation1424_implies_Equation1418 (G : Type*) [Magma G] (h : Equation1424 G) : Equation1418 G := λ x y z w => h x y z w w
theorem Equation1477_implies_Equation1476 (G : Type*) [Magma G] (h : Equation1477 G) : Equation1476 G := λ x y z w => h x y z w w
theorem Equation1514_implies_Equation1513 (G : Type*) [Magma G] (h : Equation1514 G) : Equation1513 G := λ x y z w => h x y z w w
theorem Equation1551_implies_Equation1550 (G : Type*) [Magma G] (h : Equation1551 G) : Equation1550 G := λ x y z w => h x y z w w
theorem Equation1568_implies_Equation1567 (G : Type*) [Magma G] (h : Equation1568 G) : Equation1567 G := λ x y z w => h x y z w w
theorem Equation1585_implies_Equation1584 (G : Type*) [Magma G] (h : Equation1585 G) : Equation1584 G := λ x y z w => h x y z w w
theorem Equation1602_implies_Equation1601 (G : Type*) [Magma G] (h : Equation1602 G) : Equation1601 G := λ x y z w => h x y z w w
theorem Equation1607_implies_Equation1606 (G : Type*) [Magma G] (h : Equation1607 G) : Equation1606 G := λ x y z w => h x y z w w
theorem Equation1612_implies_Equation1611 (G : Type*) [Magma G] (h : Equation1612 G) : Equation1611 G := λ x y z w => h x y z w w
theorem Equation1617_implies_Equation1616 (G : Type*) [Magma G] (h : Equation1617 G) : Equation1616 G := λ x y z w => h x y z w w
theorem Equation1622_implies_Equation1621 (G : Type*) [Magma G] (h : Equation1622 G) : Equation1621 G := λ x y z w => h x y z w w
theorem Equation1623_implies_Equation1618 (G : Type*) [Magma G] (h : Equation1623 G) : Equation1618 G := λ x y z w => h x y z w w
theorem Equation1624_implies_Equation1619 (G : Type*) [Magma G] (h : Equation1624 G) : Equation1619 G := λ x y z w => h x y z w w
theorem Equation1625_implies_Equation1620 (G : Type*) [Magma G] (h : Equation1625 G) : Equation1620 G := λ x y z w => h x y z w w
theorem Equation1626_implies_Equation1621 (G : Type*) [Magma G] (h : Equation1626 G) : Equation1621 G := λ x y z w => h x y z w w
theorem Equation1627_implies_Equation1621 (G : Type*) [Magma G] (h : Equation1627 G) : Equation1621 G := λ x y z w => h x y z w w
theorem Equation1680_implies_Equation1679 (G : Type*) [Magma G] (h : Equation1680 G) : Equation1679 G := λ x y z w => h x y z w w
theorem Equation1717_implies_Equation1716 (G : Type*) [Magma G] (h : Equation1717 G) : Equation1716 G := λ x y z w => h x y z w w
theorem Equation1754_implies_Equation1753 (G : Type*) [Magma G] (h : Equation1754 G) : Equation1753 G := λ x y z w => h x y z w w
theorem Equation1771_implies_Equation1770 (G : Type*) [Magma G] (h : Equation1771 G) : Equation1770 G := λ x y z w => h x y z w w
theorem Equation1788_implies_Equation1787 (G : Type*) [Magma G] (h : Equation1788 G) : Equation1787 G := λ x y z w => h x y z w w
theorem Equation1805_implies_Equation1804 (G : Type*) [Magma G] (h : Equation1805 G) : Equation1804 G := λ x y z w => h x y z w w
theorem Equation1810_implies_Equation1809 (G : Type*) [Magma G] (h : Equation1810 G) : Equation1809 G := λ x y z w => h x y z w w
theorem Equation1815_implies_Equation1814 (G : Type*) [Magma G] (h : Equation1815 G) : Equation1814 G := λ x y z w => h x y z w w
theorem Equation1820_implies_Equation1819 (G : Type*) [Magma G] (h : Equation1820 G) : Equation1819 G := λ x y z w => h x y z w w
theorem Equation1825_implies_Equation1824 (G : Type*) [Magma G] (h : Equation1825 G) : Equation1824 G := λ x y z w => h x y z w w
theorem Equation1826_implies_Equation1821 (G : Type*) [Magma G] (h : Equation1826 G) : Equation1821 G := λ x y z w => h x y z w w
theorem Equation1827_implies_Equation1822 (G : Type*) [Magma G] (h : Equation1827 G) : Equation1822 G := λ x y z w => h x y z w w
theorem Equation1828_implies_Equation1823 (G : Type*) [Magma G] (h : Equation1828 G) : Equation1823 G := λ x y z w => h x y z w w
theorem Equation1829_implies_Equation1824 (G : Type*) [Magma G] (h : Equation1829 G) : Equation1824 G := λ x y z w => h x y z w w
theorem Equation1830_implies_Equation1824 (G : Type*) [Magma G] (h : Equation1830 G) : Equation1824 G := λ x y z w => h x y z w w
theorem Equation1883_implies_Equation1882 (G : Type*) [Magma G] (h : Equation1883 G) : Equation1882 G := λ x y z w => h x y z w w
theorem Equation1920_implies_Equation1919 (G : Type*) [Magma G] (h : Equation1920 G) : Equation1919 G := λ x y z w => h x y z w w
theorem Equation1957_implies_Equation1956 (G : Type*) [Magma G] (h : Equation1957 G) : Equation1956 G := λ x y z w => h x y z w w
theorem Equation1974_implies_Equation1973 (G : Type*) [Magma G] (h : Equation1974 G) : Equation1973 G := λ x y z w => h x y z w w
theorem Equation1991_implies_Equation1990 (G : Type*) [Magma G] (h : Equation1991 G) : Equation1990 G := λ x y z w => h x y z w w
theorem Equation2008_implies_Equation2007 (G : Type*) [Magma G] (h : Equation2008 G) : Equation2007 G := λ x y z w => h x y z w w
theorem Equation2013_implies_Equation2012 (G : Type*) [Magma G] (h : Equation2013 G) : Equation2012 G := λ x y z w => h x y z w w
theorem Equation2018_implies_Equation2017 (G : Type*) [Magma G] (h : Equation2018 G) : Equation2017 G := λ x y z w => h x y z w w
theorem Equation2023_implies_Equation2022 (G : Type*) [Magma G] (h : Equation2023 G) : Equation2022 G := λ x y z w => h x y z w w
theorem Equation2028_implies_Equation2027 (G : Type*) [Magma G] (h : Equation2028 G) : Equation2027 G := λ x y z w => h x y z w w
theorem Equation2029_implies_Equation2024 (G : Type*) [Magma G] (h : Equation2029 G) : Equation2024 G := λ x y z w => h x y z w w
theorem Equation2030_implies_Equation2025 (G : Type*) [Magma G] (h : Equation2030 G) : Equation2025 G := λ x y z w => h x y z w w
theorem Equation2031_implies_Equation2026 (G : Type*) [Magma G] (h : Equation2031 G) : Equation2026 G := λ x y z w => h x y z w w
theorem Equation2032_implies_Equation2027 (G : Type*) [Magma G] (h : Equation2032 G) : Equation2027 G := λ x y z w => h x y z w w
theorem Equation2033_implies_Equation2027 (G : Type*) [Magma G] (h : Equation2033 G) : Equation2027 G := λ x y z w => h x y z w w
theorem Equation2086_implies_Equation2085 (G : Type*) [Magma G] (h : Equation2086 G) : Equation2085 G := λ x y z w => h x y z w w
theorem Equation2123_implies_Equation2122 (G : Type*) [Magma G] (h : Equation2123 G) : Equation2122 G := λ x y z w => h x y z w w
theorem Equation2160_implies_Equation2159 (G : Type*) [Magma G] (h : Equation2160 G) : Equation2159 G := λ x y z w => h x y z w w
theorem Equation2177_implies_Equation2176 (G : Type*) [Magma G] (h : Equation2177 G) : Equation2176 G := λ x y z w => h x y z w w
theorem Equation2194_implies_Equation2193 (G : Type*) [Magma G] (h : Equation2194 G) : Equation2193 G := λ x y z w => h x y z w w
theorem Equation2211_implies_Equation2210 (G : Type*) [Magma G] (h : Equation2211 G) : Equation2210 G := λ x y z w => h x y z w w
theorem Equation2216_implies_Equation2215 (G : Type*) [Magma G] (h : Equation2216 G) : Equation2215 G := λ x y z w => h x y z w w
theorem Equation2221_implies_Equation2220 (G : Type*) [Magma G] (h : Equation2221 G) : Equation2220 G := λ x y z w => h x y z w w
theorem Equation2226_implies_Equation2225 (G : Type*) [Magma G] (h : Equation2226 G) : Equation2225 G := λ x y z w => h x y z w w
theorem Equation2231_implies_Equation2230 (G : Type*) [Magma G] (h : Equation2231 G) : Equation2230 G := λ x y z w => h x y z w w
theorem Equation2232_implies_Equation2227 (G : Type*) [Magma G] (h : Equation2232 G) : Equation2227 G := λ x y z w => h x y z w w
theorem Equation2233_implies_Equation2228 (G : Type*) [Magma G] (h : Equation2233 G) : Equation2228 G := λ x y z w => h x y z w w
theorem Equation2234_implies_Equation2229 (G : Type*) [Magma G] (h : Equation2234 G) : Equation2229 G := λ x y z w => h x y z w w
theorem Equation2235_implies_Equation2230 (G : Type*) [Magma G] (h : Equation2235 G) : Equation2230 G := λ x y z w => h x y z w w
theorem Equation2236_implies_Equation2230 (G : Type*) [Magma G] (h : Equation2236 G) : Equation2230 G := λ x y z w => h x y z w w
theorem Equation2289_implies_Equation2288 (G : Type*) [Magma G] (h : Equation2289 G) : Equation2288 G := λ x y z w => h x y z w w
theorem Equation2326_implies_Equation2325 (G : Type*) [Magma G] (h : Equation2326 G) : Equation2325 G := λ x y z w => h x y z w w
theorem Equation2363_implies_Equation2362 (G : Type*) [Magma G] (h : Equation2363 G) : Equation2362 G := λ x y z w => h x y z w w
theorem Equation2380_implies_Equation2379 (G : Type*) [Magma G] (h : Equation2380 G) : Equation2379 G := λ x y z w => h x y z w w
theorem Equation2397_implies_Equation2396 (G : Type*) [Magma G] (h : Equation2397 G) : Equation2396 G := λ x y z w => h x y z w w
theorem Equation2414_implies_Equation2413 (G : Type*) [Magma G] (h : Equation2414 G) : Equation2413 G := λ x y z w => h x y z w w
theorem Equation2419_implies_Equation2418 (G : Type*) [Magma G] (h : Equation2419 G) : Equation2418 G := λ x y z w => h x y z w w
theorem Equation2424_implies_Equation2423 (G : Type*) [Magma G] (h : Equation2424 G) : Equation2423 G := λ x y z w => h x y z w w
theorem Equation2429_implies_Equation2428 (G : Type*) [Magma G] (h : Equation2429 G) : Equation2428 G := λ x y z w => h x y z w w
theorem Equation2434_implies_Equation2433 (G : Type*) [Magma G] (h : Equation2434 G) : Equation2433 G := λ x y z w => h x y z w w
theorem Equation2435_implies_Equation2430 (G : Type*) [Magma G] (h : Equation2435 G) : Equation2430 G := λ x y z w => h x y z w w
theorem Equation2436_implies_Equation2431 (G : Type*) [Magma G] (h : Equation2436 G) : Equation2431 G := λ x y z w => h x y z w w
theorem Equation2437_implies_Equation2432 (G : Type*) [Magma G] (h : Equation2437 G) : Equation2432 G := λ x y z w => h x y z w w
theorem Equation2438_implies_Equation2433 (G : Type*) [Magma G] (h : Equation2438 G) : Equation2433 G := λ x y z w => h x y z w w
theorem Equation2439_implies_Equation2433 (G : Type*) [Magma G] (h : Equation2439 G) : Equation2433 G := λ x y z w => h x y z w w
theorem Equation2492_implies_Equation2491 (G : Type*) [Magma G] (h : Equation2492 G) : Equation2491 G := λ x y z w => h x y z w w
theorem Equation2529_implies_Equation2528 (G : Type*) [Magma G] (h : Equation2529 G) : Equation2528 G := λ x y z w => h x y z w w
theorem Equation2566_implies_Equation2565 (G : Type*) [Magma G] (h : Equation2566 G) : Equation2565 G := λ x y z w => h x y z w w
theorem Equation2583_implies_Equation2582 (G : Type*) [Magma G] (h : Equation2583 G) : Equation2582 G := λ x y z w => h x y z w w
theorem Equation2600_implies_Equation2599 (G : Type*) [Magma G] (h : Equation2600 G) : Equation2599 G := λ x y z w => h x y z w w
theorem Equation2617_implies_Equation2616 (G : Type*) [Magma G] (h : Equation2617 G) : Equation2616 G := λ x y z w => h x y z w w
theorem Equation2622_implies_Equation2621 (G : Type*) [Magma G] (h : Equation2622 G) : Equation2621 G := λ x y z w => h x y z w w
theorem Equation2627_implies_Equation2626 (G : Type*) [Magma G] (h : Equation2627 G) : Equation2626 G := λ x y z w => h x y z w w
theorem Equation2632_implies_Equation2631 (G : Type*) [Magma G] (h : Equation2632 G) : Equation2631 G := λ x y z w => h x y z w w
theorem Equation2637_implies_Equation2636 (G : Type*) [Magma G] (h : Equation2637 G) : Equation2636 G := λ x y z w => h x y z w w
theorem Equation2638_implies_Equation2633 (G : Type*) [Magma G] (h : Equation2638 G) : Equation2633 G := λ x y z w => h x y z w w
theorem Equation2639_implies_Equation2634 (G : Type*) [Magma G] (h : Equation2639 G) : Equation2634 G := λ x y z w => h x y z w w
theorem Equation2640_implies_Equation2635 (G : Type*) [Magma G] (h : Equation2640 G) : Equation2635 G := λ x y z w => h x y z w w
theorem Equation2641_implies_Equation2636 (G : Type*) [Magma G] (h : Equation2641 G) : Equation2636 G := λ x y z w => h x y z w w
theorem Equation2642_implies_Equation2636 (G : Type*) [Magma G] (h : Equation2642 G) : Equation2636 G := λ x y z w => h x y z w w
theorem Equation2695_implies_Equation2694 (G : Type*) [Magma G] (h : Equation2695 G) : Equation2694 G := λ x y z w => h x y z w w
theorem Equation2732_implies_Equation2731 (G : Type*) [Magma G] (h : Equation2732 G) : Equation2731 G := λ x y z w => h x y z w w
theorem Equation2769_implies_Equation2768 (G : Type*) [Magma G] (h : Equation2769 G) : Equation2768 G := λ x y z w => h x y z w w
theorem Equation2786_implies_Equation2785 (G : Type*) [Magma G] (h : Equation2786 G) : Equation2785 G := λ x y z w => h x y z w w
theorem Equation2803_implies_Equation2802 (G : Type*) [Magma G] (h : Equation2803 G) : Equation2802 G := λ x y z w => h x y z w w
theorem Equation2820_implies_Equation2819 (G : Type*) [Magma G] (h : Equation2820 G) : Equation2819 G := λ x y z w => h x y z w w
theorem Equation2825_implies_Equation2824 (G : Type*) [Magma G] (h : Equation2825 G) : Equation2824 G := λ x y z w => h x y z w w
theorem Equation2830_implies_Equation2829 (G : Type*) [Magma G] (h : Equation2830 G) : Equation2829 G := λ x y z w => h x y z w w
theorem Equation2835_implies_Equation2834 (G : Type*) [Magma G] (h : Equation2835 G) : Equation2834 G := λ x y z w => h x y z w w
theorem Equation2840_implies_Equation2839 (G : Type*) [Magma G] (h : Equation2840 G) : Equation2839 G := λ x y z w => h x y z w w
theorem Equation2841_implies_Equation2836 (G : Type*) [Magma G] (h : Equation2841 G) : Equation2836 G := λ x y z w => h x y z w w
theorem Equation2842_implies_Equation2837 (G : Type*) [Magma G] (h : Equation2842 G) : Equation2837 G := λ x y z w => h x y z w w
theorem Equation2843_implies_Equation2838 (G : Type*) [Magma G] (h : Equation2843 G) : Equation2838 G := λ x y z w => h x y z w w
theorem Equation2844_implies_Equation2839 (G : Type*) [Magma G] (h : Equation2844 G) : Equation2839 G := λ x y z w => h x y z w w
theorem Equation2845_implies_Equation2839 (G : Type*) [Magma G] (h : Equation2845 G) : Equation2839 G := λ x y z w => h x y z w w
theorem Equation2898_implies_Equation2897 (G : Type*) [Magma G] (h : Equation2898 G) : Equation2897 G := λ x y z w => h x y z w w
theorem Equation2935_implies_Equation2934 (G : Type*) [Magma G] (h : Equation2935 G) : Equation2934 G := λ x y z w => h x y z w w
theorem Equation2972_implies_Equation2971 (G : Type*) [Magma G] (h : Equation2972 G) : Equation2971 G := λ x y z w => h x y z w w
theorem Equation2989_implies_Equation2988 (G : Type*) [Magma G] (h : Equation2989 G) : Equation2988 G := λ x y z w => h x y z w w
theorem Equation3006_implies_Equation3005 (G : Type*) [Magma G] (h : Equation3006 G) : Equation3005 G := λ x y z w => h x y z w w
theorem Equation3023_implies_Equation3022 (G : Type*) [Magma G] (h : Equation3023 G) : Equation3022 G := λ x y z w => h x y z w w
theorem Equation3028_implies_Equation3027 (G : Type*) [Magma G] (h : Equation3028 G) : Equation3027 G := λ x y z w => h x y z w w
theorem Equation3033_implies_Equation3032 (G : Type*) [Magma G] (h : Equation3033 G) : Equation3032 G := λ x y z w => h x y z w w
theorem Equation3038_implies_Equation3037 (G : Type*) [Magma G] (h : Equation3038 G) : Equation3037 G := λ x y z w => h x y z w w
theorem Equation3043_implies_Equation3042 (G : Type*) [Magma G] (h : Equation3043 G) : Equation3042 G := λ x y z w => h x y z w w
theorem Equation3044_implies_Equation3039 (G : Type*) [Magma G] (h : Equation3044 G) : Equation3039 G := λ x y z w => h x y z w w
theorem Equation3045_implies_Equation3040 (G : Type*) [Magma G] (h : Equation3045 G) : Equation3040 G := λ x y z w => h x y z w w
theorem Equation3046_implies_Equation3041 (G : Type*) [Magma G] (h : Equation3046 G) : Equation3041 G := λ x y z w => h x y z w w
theorem Equation3047_implies_Equation3042 (G : Type*) [Magma G] (h : Equation3047 G) : Equation3042 G := λ x y z w => h x y z w w
theorem Equation3048_implies_Equation3042 (G : Type*) [Magma G] (h : Equation3048 G) : Equation3042 G := λ x y z w => h x y z w w
theorem Equation3101_implies_Equation3100 (G : Type*) [Magma G] (h : Equation3101 G) : Equation3100 G := λ x y z w => h x y z w w
theorem Equation3138_implies_Equation3137 (G : Type*) [Magma G] (h : Equation3138 G) : Equation3137 G := λ x y z w => h x y z w w
theorem Equation3175_implies_Equation3174 (G : Type*) [Magma G] (h : Equation3175 G) : Equation3174 G := λ x y z w => h x y z w w
theorem Equation3192_implies_Equation3191 (G : Type*) [Magma G] (h : Equation3192 G) : Equation3191 G := λ x y z w => h x y z w w
theorem Equation3209_implies_Equation3208 (G : Type*) [Magma G] (h : Equation3209 G) : Equation3208 G := λ x y z w => h x y z w w
theorem Equation3226_implies_Equation3225 (G : Type*) [Magma G] (h : Equation3226 G) : Equation3225 G := λ x y z w => h x y z w w
theorem Equation3231_implies_Equation3230 (G : Type*) [Magma G] (h : Equation3231 G) : Equation3230 G := λ x y z w => h x y z w w
theorem Equation3236_implies_Equation3235 (G : Type*) [Magma G] (h : Equation3236 G) : Equation3235 G := λ x y z w => h x y z w w
theorem Equation3241_implies_Equation3240 (G : Type*) [Magma G] (h : Equation3241 G) : Equation3240 G := λ x y z w => h x y z w w
theorem Equation3246_implies_Equation3245 (G : Type*) [Magma G] (h : Equation3246 G) : Equation3245 G := λ x y z w => h x y z w w
theorem Equation3247_implies_Equation3242 (G : Type*) [Magma G] (h : Equation3247 G) : Equation3242 G := λ x y z w => h x y z w w
theorem Equation3248_implies_Equation3243 (G : Type*) [Magma G] (h : Equation3248 G) : Equation3243 G := λ x y z w => h x y z w w
theorem Equation3249_implies_Equation3244 (G : Type*) [Magma G] (h : Equation3249 G) : Equation3244 G := λ x y z w => h x y z w w
theorem Equation3250_implies_Equation3245 (G : Type*) [Magma G] (h : Equation3250 G) : Equation3245 G := λ x y z w => h x y z w w
theorem Equation3251_implies_Equation3245 (G : Type*) [Magma G] (h : Equation3251 G) : Equation3245 G := λ x y z w => h x y z w w
theorem Equation3304_implies_Equation3303 (G : Type*) [Magma G] (h : Equation3304 G) : Equation3303 G := λ x y z w => h x y z w w
theorem Equation3341_implies_Equation3340 (G : Type*) [Magma G] (h : Equation3341 G) : Equation3340 G := λ x y z w => h x y z w w
theorem Equation3378_implies_Equation3377 (G : Type*) [Magma G] (h : Equation3378 G) : Equation3377 G := λ x y z w => h x y z w w
theorem Equation3395_implies_Equation3394 (G : Type*) [Magma G] (h : Equation3395 G) : Equation3394 G := λ x y z w => h x y z w w
theorem Equation3412_implies_Equation3411 (G : Type*) [Magma G] (h : Equation3412 G) : Equation3411 G := λ x y z w => h x y z w w
theorem Equation3429_implies_Equation3428 (G : Type*) [Magma G] (h : Equation3429 G) : Equation3428 G := λ x y z w => h x y z w w
theorem Equation3434_implies_Equation3433 (G : Type*) [Magma G] (h : Equation3434 G) : Equation3433 G := λ x y z w => h x y z w w
theorem Equation3439_implies_Equation3438 (G : Type*) [Magma G] (h : Equation3439 G) : Equation3438 G := λ x y z w => h x y z w w
theorem Equation3444_implies_Equation3443 (G : Type*) [Magma G] (h : Equation3444 G) : Equation3443 G := λ x y z w => h x y z w w
theorem Equation3449_implies_Equation3448 (G : Type*) [Magma G] (h : Equation3449 G) : Equation3448 G := λ x y z w => h x y z w w
theorem Equation3450_implies_Equation3445 (G : Type*) [Magma G] (h : Equation3450 G) : Equation3445 G := λ x y z w => h x y z w w
theorem Equation3451_implies_Equation3446 (G : Type*) [Magma G] (h : Equation3451 G) : Equation3446 G := λ x y z w => h x y z w w
theorem Equation3452_implies_Equation3447 (G : Type*) [Magma G] (h : Equation3452 G) : Equation3447 G := λ x y z w => h x y z w w
theorem Equation3453_implies_Equation3448 (G : Type*) [Magma G] (h : Equation3453 G) : Equation3448 G := λ x y z w => h x y z w w
theorem Equation3454_implies_Equation3448 (G : Type*) [Magma G] (h : Equation3454 G) : Equation3448 G := λ x y z w => h x y z w w
theorem Equation3507_implies_Equation3506 (G : Type*) [Magma G] (h : Equation3507 G) : Equation3506 G := λ x y z w => h x y z w w
theorem Equation3544_implies_Equation3543 (G : Type*) [Magma G] (h : Equation3544 G) : Equation3543 G := λ x y z w => h x y z w w
theorem Equation3581_implies_Equation3580 (G : Type*) [Magma G] (h : Equation3581 G) : Equation3580 G := λ x y z w => h x y z w w
theorem Equation3598_implies_Equation3597 (G : Type*) [Magma G] (h : Equation3598 G) : Equation3597 G := λ x y z w => h x y z w w
theorem Equation3615_implies_Equation3614 (G : Type*) [Magma G] (h : Equation3615 G) : Equation3614 G := λ x y z w => h x y z w w
theorem Equation3632_implies_Equation3631 (G : Type*) [Magma G] (h : Equation3632 G) : Equation3631 G := λ x y z w => h x y z w w
theorem Equation3637_implies_Equation3636 (G : Type*) [Magma G] (h : Equation3637 G) : Equation3636 G := λ x y z w => h x y z w w
theorem Equation3642_implies_Equation3641 (G : Type*) [Magma G] (h : Equation3642 G) : Equation3641 G := λ x y z w => h x y z w w
theorem Equation3647_implies_Equation3646 (G : Type*) [Magma G] (h : Equation3647 G) : Equation3646 G := λ x y z w => h x y z w w
theorem Equation3652_implies_Equation3651 (G : Type*) [Magma G] (h : Equation3652 G) : Equation3651 G := λ x y z w => h x y z w w
theorem Equation3653_implies_Equation3648 (G : Type*) [Magma G] (h : Equation3653 G) : Equation3648 G := λ x y z w => h x y z w w
theorem Equation3654_implies_Equation3649 (G : Type*) [Magma G] (h : Equation3654 G) : Equation3649 G := λ x y z w => h x y z w w
theorem Equation3655_implies_Equation3650 (G : Type*) [Magma G] (h : Equation3655 G) : Equation3650 G := λ x y z w => h x y z w w
theorem Equation3656_implies_Equation3651 (G : Type*) [Magma G] (h : Equation3656 G) : Equation3651 G := λ x y z w => h x y z w w
theorem Equation3657_implies_Equation3651 (G : Type*) [Magma G] (h : Equation3657 G) : Equation3651 G := λ x y z w => h x y z w w
theorem Equation3710_implies_Equation3709 (G : Type*) [Magma G] (h : Equation3710 G) : Equation3709 G := λ x y z w => h x y z w w
theorem Equation3747_implies_Equation3746 (G : Type*) [Magma G] (h : Equation3747 G) : Equation3746 G := λ x y z w => h x y z w w
theorem Equation3784_implies_Equation3783 (G : Type*) [Magma G] (h : Equation3784 G) : Equation3783 G := λ x y z w => h x y z w w
theorem Equation3801_implies_Equation3800 (G : Type*) [Magma G] (h : Equation3801 G) : Equation3800 G := λ x y z w => h x y z w w
theorem Equation3818_implies_Equation3817 (G : Type*) [Magma G] (h : Equation3818 G) : Equation3817 G := λ x y z w => h x y z w w
theorem Equation3835_implies_Equation3834 (G : Type*) [Magma G] (h : Equation3835 G) : Equation3834 G := λ x y z w => h x y z w w
theorem Equation3840_implies_Equation3839 (G : Type*) [Magma G] (h : Equation3840 G) : Equation3839 G := λ x y z w => h x y z w w
theorem Equation3845_implies_Equation3844 (G : Type*) [Magma G] (h : Equation3845 G) : Equation3844 G := λ x y z w => h x y z w w
theorem Equation3850_implies_Equation3849 (G : Type*) [Magma G] (h : Equation3850 G) : Equation3849 G := λ x y z w => h x y z w w
theorem Equation3855_implies_Equation3854 (G : Type*) [Magma G] (h : Equation3855 G) : Equation3854 G := λ x y z w => h x y z w w
theorem Equation3856_implies_Equation3851 (G : Type*) [Magma G] (h : Equation3856 G) : Equation3851 G := λ x y z w => h x y z w w
theorem Equation3857_implies_Equation3852 (G : Type*) [Magma G] (h : Equation3857 G) : Equation3852 G := λ x y z w => h x y z w w
theorem Equation3858_implies_Equation3853 (G : Type*) [Magma G] (h : Equation3858 G) : Equation3853 G := λ x y z w => h x y z w w
theorem Equation3859_implies_Equation3854 (G : Type*) [Magma G] (h : Equation3859 G) : Equation3854 G := λ x y z w => h x y z w w
theorem Equation3860_implies_Equation3854 (G : Type*) [Magma G] (h : Equation3860 G) : Equation3854 G := λ x y z w => h x y z w w
theorem Equation3913_implies_Equation3912 (G : Type*) [Magma G] (h : Equation3913 G) : Equation3912 G := λ x y z w => h x y z w w
theorem Equation3950_implies_Equation3949 (G : Type*) [Magma G] (h : Equation3950 G) : Equation3949 G := λ x y z w => h x y z w w
theorem Equation3987_implies_Equation3986 (G : Type*) [Magma G] (h : Equation3987 G) : Equation3986 G := λ x y z w => h x y z w w
theorem Equation4004_implies_Equation4003 (G : Type*) [Magma G] (h : Equation4004 G) : Equation4003 G := λ x y z w => h x y z w w
theorem Equation4021_implies_Equation4020 (G : Type*) [Magma G] (h : Equation4021 G) : Equation4020 G := λ x y z w => h x y z w w
theorem Equation4038_implies_Equation4037 (G : Type*) [Magma G] (h : Equation4038 G) : Equation4037 G := λ x y z w => h x y z w w
theorem Equation4043_implies_Equation4042 (G : Type*) [Magma G] (h : Equation4043 G) : Equation4042 G := λ x y z w => h x y z w w
theorem Equation4048_implies_Equation4047 (G : Type*) [Magma G] (h : Equation4048 G) : Equation4047 G := λ x y z w => h x y z w w
theorem Equation4053_implies_Equation4052 (G : Type*) [Magma G] (h : Equation4053 G) : Equation4052 G := λ x y z w => h x y z w w
theorem Equation4058_implies_Equation4057 (G : Type*) [Magma G] (h : Equation4058 G) : Equation4057 G := λ x y z w => h x y z w w
theorem Equation4059_implies_Equation4054 (G : Type*) [Magma G] (h : Equation4059 G) : Equation4054 G := λ x y z w => h x y z w w
theorem Equation4060_implies_Equation4055 (G : Type*) [Magma G] (h : Equation4060 G) : Equation4055 G := λ x y z w => h x y z w w
theorem Equation4061_implies_Equation4056 (G : Type*) [Magma G] (h : Equation4061 G) : Equation4056 G := λ x y z w => h x y z w w
theorem Equation4062_implies_Equation4057 (G : Type*) [Magma G] (h : Equation4062 G) : Equation4057 G := λ x y z w => h x y z w w
theorem Equation4063_implies_Equation4057 (G : Type*) [Magma G] (h : Equation4063 G) : Equation4057 G := λ x y z w => h x y z w w
theorem Equation4116_implies_Equation4115 (G : Type*) [Magma G] (h : Equation4116 G) : Equation4115 G := λ x y z w => h x y z w w
theorem Equation4153_implies_Equation4152 (G : Type*) [Magma G] (h : Equation4153 G) : Equation4152 G := λ x y z w => h x y z w w
theorem Equation4190_implies_Equation4189 (G : Type*) [Magma G] (h : Equation4190 G) : Equation4189 G := λ x y z w => h x y z w w
theorem Equation4207_implies_Equation4206 (G : Type*) [Magma G] (h : Equation4207 G) : Equation4206 G := λ x y z w => h x y z w w
theorem Equation4224_implies_Equation4223 (G : Type*) [Magma G] (h : Equation4224 G) : Equation4223 G := λ x y z w => h x y z w w
theorem Equation4241_implies_Equation4240 (G : Type*) [Magma G] (h : Equation4241 G) : Equation4240 G := λ x y z w => h x y z w w
theorem Equation4246_implies_Equation4245 (G : Type*) [Magma G] (h : Equation4246 G) : Equation4245 G := λ x y z w => h x y z w w
theorem Equation4251_implies_Equation4250 (G : Type*) [Magma G] (h : Equation4251 G) : Equation4250 G := λ x y z w => h x y z w w
theorem Equation4256_implies_Equation4255 (G : Type*) [Magma G] (h : Equation4256 G) : Equation4255 G := λ x y z w => h x y z w w
theorem Equation4261_implies_Equation4260 (G : Type*) [Magma G] (h : Equation4261 G) : Equation4260 G := λ x y z w => h x y z w w
theorem Equation4262_implies_Equation4257 (G : Type*) [Magma G] (h : Equation4262 G) : Equation4257 G := λ x y z w => h x y z w w
theorem Equation4263_implies_Equation4258 (G : Type*) [Magma G] (h : Equation4263 G) : Equation4258 G := λ x y z w => h x y z w w
theorem Equation4264_implies_Equation4259 (G : Type*) [Magma G] (h : Equation4264 G) : Equation4259 G := λ x y z w => h x y z w w
theorem Equation4265_implies_Equation4260 (G : Type*) [Magma G] (h : Equation4265 G) : Equation4260 G := λ x y z w => h x y z w w
theorem Equation4266_implies_Equation4260 (G : Type*) [Magma G] (h : Equation4266 G) : Equation4260 G := λ x y z w => h x y z w w
theorem Equation4313_implies_Equation4312 (G : Type*) [Magma G] (h : Equation4313 G) : Equation4312 G := λ x y z w => h x y z w w
theorem Equation4338_implies_Equation4337 (G : Type*) [Magma G] (h : Equation4338 G) : Equation4337 G := λ x y z w => h x y z w w
theorem Equation4356_implies_Equation4355 (G : Type*) [Magma G] (h : Equation4356 G) : Equation4355 G := λ x y z w => h x y z w w
theorem Equation4431_implies_Equation4430 (G : Type*) [Magma G] (h : Equation4431 G) : Equation4430 G := λ x y z w => h x y z w w
theorem Equation4468_implies_Equation4467 (G : Type*) [Magma G] (h : Equation4468 G) : Equation4467 G := λ x y z w => h x y z w w
theorem Equation4505_implies_Equation4504 (G : Type*) [Magma G] (h : Equation4505 G) : Equation4504 G := λ x y z w => h x y z w w
theorem Equation4522_implies_Equation4521 (G : Type*) [Magma G] (h : Equation4522 G) : Equation4521 G := λ x y z w => h x y z w w
theorem Equation4539_implies_Equation4538 (G : Type*) [Magma G] (h : Equation4539 G) : Equation4538 G := λ x y z w => h x y z w w
theorem Equation4556_implies_Equation4555 (G : Type*) [Magma G] (h : Equation4556 G) : Equation4555 G := λ x y z w => h x y z w w
theorem Equation4561_implies_Equation4560 (G : Type*) [Magma G] (h : Equation4561 G) : Equation4560 G := λ x y z w => h x y z w w
theorem Equation4566_implies_Equation4565 (G : Type*) [Magma G] (h : Equation4566 G) : Equation4565 G := λ x y z w => h x y z w w
theorem Equation4571_implies_Equation4570 (G : Type*) [Magma G] (h : Equation4571 G) : Equation4570 G := λ x y z w => h x y z w w
theorem Equation4576_implies_Equation4575 (G : Type*) [Magma G] (h : Equation4576 G) : Equation4575 G := λ x y z w => h x y z w w
theorem Equation4577_implies_Equation4572 (G : Type*) [Magma G] (h : Equation4577 G) : Equation4572 G := λ x y z w => h x y z w w
theorem Equation4578_implies_Equation4573 (G : Type*) [Magma G] (h : Equation4578 G) : Equation4573 G := λ x y z w => h x y z w w
theorem Equation4579_implies_Equation4574 (G : Type*) [Magma G] (h : Equation4579 G) : Equation4574 G := λ x y z w => h x y z w w
theorem Equation4580_implies_Equation4575 (G : Type*) [Magma G] (h : Equation4580 G) : Equation4575 G := λ x y z w => h x y z w w
theorem Equation4581_implies_Equation4575 (G : Type*) [Magma G] (h : Equation4581 G) : Equation4575 G := λ x y z w => h x y z w w
theorem Equation4628_implies_Equation4627 (G : Type*) [Magma G] (h : Equation4628 G) : Equation4627 G := λ x y z w => h x y z w w
theorem Equation4653_implies_Equation4652 (G : Type*) [Magma G] (h : Equation4653 G) : Equation4652 G := λ x y z w => h x y z w w
theorem Equation4671_implies_Equation4670 (G : Type*) [Magma G] (h : Equation4671 G) : Equation4670 G := λ x y z w => h x y z w w