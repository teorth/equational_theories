import Mathlib.Data.Nat.Defs
import Mathlib.Tactic


universe u

class Magma (α : Type u) where
  /-- `a ∘ b` computes a binary operation of `a` and `b`. -/
  op : α → α → α

@[inherit_doc] infixl:65 " ∘ "   => Magma.op


/- List of equational laws being studied -/
def Equation95 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ y))
def Equation98 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ u))
def Equation147 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ y)
def Equation150 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ u)
def Equation199 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ y)
def Equation202 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ u)
def Equation251 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ y
def Equation254 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ u
def Equation303 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ y
def Equation306 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ u
def Equation355 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ y)
def Equation358 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ u)
def Equation407 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ y
def Equation410 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ u
def Equation459 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (w ∘ y)))
def Equation462 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (y ∘ (z ∘ (w ∘ u)))
def Equation496 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (w ∘ y)))
def Equation499 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (x ∘ (z ∘ (w ∘ u)))
def Equation533 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (w ∘ y)))
def Equation536 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (y ∘ (z ∘ (w ∘ u)))
def Equation550 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (w ∘ y)))
def Equation553 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (x ∘ (w ∘ u)))
def Equation567 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (w ∘ y)))
def Equation570 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (y ∘ (w ∘ u)))
def Equation584 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (w ∘ y)))
def Equation587 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (z ∘ (w ∘ u)))
def Equation589 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (x ∘ y)))
def Equation592 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (x ∘ u)))
def Equation593 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (y ∘ x)))
def Equation594 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (y ∘ y)))
def Equation595 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (y ∘ z)))
def Equation596 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (y ∘ w)))
def Equation597 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (y ∘ u)))
def Equation599 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (z ∘ y)))
def Equation602 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (z ∘ u)))
def Equation604 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (w ∘ y)))
def Equation607 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (w ∘ u)))
def Equation608 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (u ∘ x)))
def Equation609 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (u ∘ y)))
def Equation610 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (u ∘ z)))
def Equation611 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (u ∘ w)))
def Equation612 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (u ∘ u)))
def Equation662 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ w) ∘ y))
def Equation665 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (y ∘ ((z ∘ w) ∘ u))
def Equation699 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ w) ∘ y))
def Equation702 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (x ∘ ((z ∘ w) ∘ u))
def Equation736 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ w) ∘ y))
def Equation739 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (y ∘ ((z ∘ w) ∘ u))
def Equation753 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ w) ∘ y))
def Equation756 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((x ∘ w) ∘ u))
def Equation770 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ w) ∘ y))
def Equation773 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((y ∘ w) ∘ u))
def Equation787 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ w) ∘ y))
def Equation790 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((z ∘ w) ∘ u))
def Equation792 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ x) ∘ y))
def Equation795 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ x) ∘ u))
def Equation796 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ y) ∘ x))
def Equation797 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ y) ∘ y))
def Equation798 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ y) ∘ z))
def Equation799 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ y) ∘ w))
def Equation800 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ y) ∘ u))
def Equation802 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ z) ∘ y))
def Equation805 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ z) ∘ u))
def Equation807 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ w) ∘ y))
def Equation810 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ w) ∘ u))
def Equation811 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ u) ∘ x))
def Equation812 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ u) ∘ y))
def Equation813 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ u) ∘ z))
def Equation814 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ u) ∘ w))
def Equation815 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ u) ∘ u))
def Equation865 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (w ∘ y))
def Equation868 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ ((y ∘ z) ∘ (w ∘ u))
def Equation902 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (w ∘ y))
def Equation905 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((x ∘ z) ∘ (w ∘ u))
def Equation939 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (w ∘ y))
def Equation942 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((y ∘ z) ∘ (w ∘ u))
def Equation956 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (w ∘ y))
def Equation959 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ x) ∘ (w ∘ u))
def Equation973 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (w ∘ y))
def Equation976 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ y) ∘ (w ∘ u))
def Equation990 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (w ∘ y))
def Equation993 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ z) ∘ (w ∘ u))
def Equation995 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (x ∘ y))
def Equation998 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (x ∘ u))
def Equation999 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (y ∘ x))
def Equation1000 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (y ∘ y))
def Equation1001 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (y ∘ z))
def Equation1002 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (y ∘ w))
def Equation1003 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (y ∘ u))
def Equation1005 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (z ∘ y))
def Equation1008 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (z ∘ u))
def Equation1010 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (w ∘ y))
def Equation1013 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (w ∘ u))
def Equation1014 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (u ∘ x))
def Equation1015 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (u ∘ y))
def Equation1016 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (u ∘ z))
def Equation1017 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (u ∘ w))
def Equation1018 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (u ∘ u))
def Equation1068 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ y)
def Equation1071 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ u)
def Equation1105 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ w)) ∘ y)
def Equation1108 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((x ∘ (z ∘ w)) ∘ u)
def Equation1142 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ w)) ∘ y)
def Equation1145 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((y ∘ (z ∘ w)) ∘ u)
def Equation1159 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ y)
def Equation1162 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ u)
def Equation1176 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ y)
def Equation1179 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ u)
def Equation1193 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ w)) ∘ y)
def Equation1196 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (z ∘ w)) ∘ u)
def Equation1198 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ x)) ∘ y)
def Equation1201 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ x)) ∘ u)
def Equation1202 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ y)) ∘ x)
def Equation1203 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ y)) ∘ y)
def Equation1204 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ y)) ∘ z)
def Equation1205 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ y)) ∘ w)
def Equation1206 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ y)) ∘ u)
def Equation1208 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ z)) ∘ y)
def Equation1211 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ z)) ∘ u)
def Equation1213 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ w)) ∘ y)
def Equation1216 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ w)) ∘ u)
def Equation1217 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ x)
def Equation1218 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ y)
def Equation1219 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ z)
def Equation1220 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ w)
def Equation1221 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ u)
def Equation1271 (G: Type*) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ w) ∘ y)
def Equation1274 (G: Type*) [Magma G] := ∀ x y z w u : G, x = x ∘ (((y ∘ z) ∘ w) ∘ u)
def Equation1308 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ w) ∘ y)
def Equation1311 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((x ∘ z) ∘ w) ∘ u)
def Equation1345 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ w) ∘ y)
def Equation1348 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((y ∘ z) ∘ w) ∘ u)
def Equation1362 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ w) ∘ y)
def Equation1365 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ x) ∘ w) ∘ u)
def Equation1379 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ w) ∘ y)
def Equation1382 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ y) ∘ w) ∘ u)
def Equation1396 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ w) ∘ y)
def Equation1399 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ z) ∘ w) ∘ u)
def Equation1401 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ x) ∘ y)
def Equation1404 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ x) ∘ u)
def Equation1405 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ y) ∘ x)
def Equation1406 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ y) ∘ y)
def Equation1407 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ y) ∘ z)
def Equation1408 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ y) ∘ w)
def Equation1409 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ y) ∘ u)
def Equation1411 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ z) ∘ y)
def Equation1414 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ z) ∘ u)
def Equation1416 (G: Type*) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ w) ∘ y)
def Equation1419 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ w) ∘ u)
def Equation1420 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ u) ∘ x)
def Equation1421 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ u) ∘ y)
def Equation1422 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ u) ∘ z)
def Equation1423 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ u) ∘ w)
def Equation1424 (G: Type*) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ u) ∘ u)
def Equation1474 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (w ∘ y))
def Equation1477 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ y) ∘ (z ∘ (w ∘ u))
def Equation1511 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (w ∘ y))
def Equation1514 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ x) ∘ (z ∘ (w ∘ u))
def Equation1548 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (w ∘ y))
def Equation1551 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ y) ∘ (z ∘ (w ∘ u))
def Equation1565 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (w ∘ y))
def Equation1568 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (x ∘ (w ∘ u))
def Equation1582 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (w ∘ y))
def Equation1585 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (y ∘ (w ∘ u))
def Equation1599 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (w ∘ y))
def Equation1602 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (z ∘ (w ∘ u))
def Equation1604 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (x ∘ y))
def Equation1607 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (x ∘ u))
def Equation1608 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (y ∘ x))
def Equation1609 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (y ∘ y))
def Equation1610 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (y ∘ z))
def Equation1611 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (y ∘ w))
def Equation1612 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (y ∘ u))
def Equation1614 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (z ∘ y))
def Equation1617 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (z ∘ u))
def Equation1619 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (w ∘ y))
def Equation1622 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (w ∘ u))
def Equation1623 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (u ∘ x))
def Equation1624 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (u ∘ y))
def Equation1625 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (u ∘ z))
def Equation1626 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (u ∘ w))
def Equation1627 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (u ∘ u))
def Equation1677 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ y)
def Equation1680 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ u)
def Equation1714 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ w) ∘ y)
def Equation1717 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ x) ∘ ((z ∘ w) ∘ u)
def Equation1751 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ w) ∘ y)
def Equation1754 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ y) ∘ ((z ∘ w) ∘ u)
def Equation1768 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ y)
def Equation1771 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ u)
def Equation1785 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ y)
def Equation1788 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ u)
def Equation1802 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ w) ∘ y)
def Equation1805 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((z ∘ w) ∘ u)
def Equation1807 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ x) ∘ y)
def Equation1810 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ x) ∘ u)
def Equation1811 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ y) ∘ x)
def Equation1812 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ y) ∘ y)
def Equation1813 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ y) ∘ z)
def Equation1814 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ y) ∘ w)
def Equation1815 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ y) ∘ u)
def Equation1817 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ z) ∘ y)
def Equation1820 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ z) ∘ u)
def Equation1822 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ w) ∘ y)
def Equation1825 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ w) ∘ u)
def Equation1826 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ x)
def Equation1827 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ y)
def Equation1828 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ z)
def Equation1829 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ w)
def Equation1830 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ u)
def Equation1880 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ y)
def Equation1883 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ u)
def Equation1917 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (w ∘ y)
def Equation1920 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (x ∘ z)) ∘ (w ∘ u)
def Equation1954 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (w ∘ y)
def Equation1957 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (y ∘ z)) ∘ (w ∘ u)
def Equation1971 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ y)
def Equation1974 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ u)
def Equation1988 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ y)
def Equation1991 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ u)
def Equation2005 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (w ∘ y)
def Equation2008 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ z)) ∘ (w ∘ u)
def Equation2010 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (x ∘ y)
def Equation2013 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (x ∘ u)
def Equation2014 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (y ∘ x)
def Equation2015 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (y ∘ y)
def Equation2016 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (y ∘ z)
def Equation2017 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (y ∘ w)
def Equation2018 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (y ∘ u)
def Equation2020 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (z ∘ y)
def Equation2023 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (z ∘ u)
def Equation2025 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (w ∘ y)
def Equation2028 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (w ∘ u)
def Equation2029 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ x)
def Equation2030 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ y)
def Equation2031 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ z)
def Equation2032 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ w)
def Equation2033 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ u)
def Equation2083 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ y)
def Equation2086 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ u)
def Equation2120 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (w ∘ y)
def Equation2123 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ x) ∘ z) ∘ (w ∘ u)
def Equation2157 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (w ∘ y)
def Equation2160 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ y) ∘ z) ∘ (w ∘ u)
def Equation2174 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ y)
def Equation2177 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ u)
def Equation2191 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ y)
def Equation2194 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ u)
def Equation2208 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (w ∘ y)
def Equation2211 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ z) ∘ (w ∘ u)
def Equation2213 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (x ∘ y)
def Equation2216 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (x ∘ u)
def Equation2217 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (y ∘ x)
def Equation2218 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (y ∘ y)
def Equation2219 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (y ∘ z)
def Equation2220 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (y ∘ w)
def Equation2221 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (y ∘ u)
def Equation2223 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (z ∘ y)
def Equation2226 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (z ∘ u)
def Equation2228 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (w ∘ y)
def Equation2231 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (w ∘ u)
def Equation2232 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ x)
def Equation2233 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ y)
def Equation2234 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ z)
def Equation2235 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ w)
def Equation2236 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ u)
def Equation2286 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ y
def Equation2289 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ u
def Equation2323 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ w))) ∘ y
def Equation2326 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (x ∘ (z ∘ w))) ∘ u
def Equation2360 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ w))) ∘ y
def Equation2363 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (y ∘ (z ∘ w))) ∘ u
def Equation2377 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ y
def Equation2380 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ u
def Equation2394 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ y
def Equation2397 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ u
def Equation2411 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ w))) ∘ y
def Equation2414 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (z ∘ w))) ∘ u
def Equation2416 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ x))) ∘ y
def Equation2419 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ x))) ∘ u
def Equation2420 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ y))) ∘ x
def Equation2421 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ y))) ∘ y
def Equation2422 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ y))) ∘ z
def Equation2423 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ y))) ∘ w
def Equation2424 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ y))) ∘ u
def Equation2426 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ z))) ∘ y
def Equation2429 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ z))) ∘ u
def Equation2431 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ w))) ∘ y
def Equation2434 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ w))) ∘ u
def Equation2435 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ x
def Equation2436 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ y
def Equation2437 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ z
def Equation2438 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ w
def Equation2439 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ u
def Equation2489 (G: Type*) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ y
def Equation2492 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ u
def Equation2526 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ w)) ∘ y
def Equation2529 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((x ∘ z) ∘ w)) ∘ u
def Equation2563 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ w)) ∘ y
def Equation2566 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((y ∘ z) ∘ w)) ∘ u
def Equation2580 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ y
def Equation2583 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ u
def Equation2597 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ y
def Equation2600 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ u
def Equation2614 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ w)) ∘ y
def Equation2617 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ z) ∘ w)) ∘ u
def Equation2619 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ x)) ∘ y
def Equation2622 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ x)) ∘ u
def Equation2623 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ y)) ∘ x
def Equation2624 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ y)) ∘ y
def Equation2625 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ y)) ∘ z
def Equation2626 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ y)) ∘ w
def Equation2627 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ y)) ∘ u
def Equation2629 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ z)) ∘ y
def Equation2632 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ z)) ∘ u
def Equation2634 (G: Type*) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ w)) ∘ y
def Equation2637 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ w)) ∘ u
def Equation2638 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ x
def Equation2639 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ y
def Equation2640 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ z
def Equation2641 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ w
def Equation2642 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ u
def Equation2692 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ y
def Equation2695 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ u
def Equation2729 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ w)) ∘ y
def Equation2732 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ x) ∘ (z ∘ w)) ∘ u
def Equation2766 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ w)) ∘ y
def Equation2769 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ y) ∘ (z ∘ w)) ∘ u
def Equation2783 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ y
def Equation2786 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ u
def Equation2800 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ y
def Equation2803 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ u
def Equation2817 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ w)) ∘ y
def Equation2820 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (z ∘ w)) ∘ u
def Equation2822 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ x)) ∘ y
def Equation2825 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ x)) ∘ u
def Equation2826 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ y)) ∘ x
def Equation2827 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ y)) ∘ y
def Equation2828 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ y)) ∘ z
def Equation2829 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ y)) ∘ w
def Equation2830 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ y)) ∘ u
def Equation2832 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ z)) ∘ y
def Equation2835 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ z)) ∘ u
def Equation2837 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ w)) ∘ y
def Equation2840 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ w)) ∘ u
def Equation2841 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ x
def Equation2842 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ y
def Equation2843 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ z
def Equation2844 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ w
def Equation2845 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ u
def Equation2895 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ y
def Equation2898 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ u
def Equation2932 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ w) ∘ y
def Equation2935 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (x ∘ z)) ∘ w) ∘ u
def Equation2969 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ w) ∘ y
def Equation2972 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (y ∘ z)) ∘ w) ∘ u
def Equation2986 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ y
def Equation2989 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ u
def Equation3003 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ y
def Equation3006 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ u
def Equation3020 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ w) ∘ y
def Equation3023 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ z)) ∘ w) ∘ u
def Equation3025 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ x) ∘ y
def Equation3028 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ x) ∘ u
def Equation3029 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ y) ∘ x
def Equation3030 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ y) ∘ y
def Equation3031 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ y) ∘ z
def Equation3032 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ y) ∘ w
def Equation3033 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ y) ∘ u
def Equation3035 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ z) ∘ y
def Equation3038 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ z) ∘ u
def Equation3040 (G: Type*) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ w) ∘ y
def Equation3043 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ w) ∘ u
def Equation3044 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ x
def Equation3045 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ y
def Equation3046 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ z
def Equation3047 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ w
def Equation3048 (G: Type*) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ u
def Equation3098 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ y
def Equation3101 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ u
def Equation3135 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ w) ∘ y
def Equation3138 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ x) ∘ z) ∘ w) ∘ u
def Equation3172 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ w) ∘ y
def Equation3175 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ y) ∘ z) ∘ w) ∘ u
def Equation3189 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ y
def Equation3192 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ u
def Equation3206 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ y
def Equation3209 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ u
def Equation3223 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ w) ∘ y
def Equation3226 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ z) ∘ w) ∘ u
def Equation3228 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ x) ∘ y
def Equation3231 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ x) ∘ u
def Equation3232 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ y) ∘ x
def Equation3233 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ y) ∘ y
def Equation3234 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ y) ∘ z
def Equation3235 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ y) ∘ w
def Equation3236 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ y) ∘ u
def Equation3238 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ z) ∘ y
def Equation3241 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ z) ∘ u
def Equation3243 (G: Type*) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ w) ∘ y
def Equation3246 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ w) ∘ u
def Equation3247 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ x
def Equation3248 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ y
def Equation3249 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ z
def Equation3250 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ w
def Equation3251 (G: Type*) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ u
def Equation3301 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (w ∘ y))
def Equation3304 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = y ∘ (z ∘ (w ∘ u))
def Equation3338 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (w ∘ y))
def Equation3341 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = x ∘ (z ∘ (w ∘ u))
def Equation3375 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (w ∘ y))
def Equation3378 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = y ∘ (z ∘ (w ∘ u))
def Equation3392 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (w ∘ y))
def Equation3395 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (x ∘ (w ∘ u))
def Equation3409 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (w ∘ y))
def Equation3412 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (y ∘ (w ∘ u))
def Equation3426 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (w ∘ y))
def Equation3429 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (z ∘ (w ∘ u))
def Equation3431 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (x ∘ y))
def Equation3434 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (x ∘ u))
def Equation3435 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (y ∘ x))
def Equation3436 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (y ∘ y))
def Equation3437 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (y ∘ z))
def Equation3438 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (y ∘ w))
def Equation3439 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (y ∘ u))
def Equation3441 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (z ∘ y))
def Equation3444 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (z ∘ u))
def Equation3446 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (w ∘ y))
def Equation3449 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (w ∘ u))
def Equation3450 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (u ∘ x))
def Equation3451 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (u ∘ y))
def Equation3452 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (u ∘ z))
def Equation3453 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (u ∘ w))
def Equation3454 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (u ∘ u))
def Equation3504 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ w) ∘ y)
def Equation3507 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = y ∘ ((z ∘ w) ∘ u)
def Equation3541 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ w) ∘ y)
def Equation3544 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = x ∘ ((z ∘ w) ∘ u)
def Equation3578 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ w) ∘ y)
def Equation3581 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = y ∘ ((z ∘ w) ∘ u)
def Equation3595 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ w) ∘ y)
def Equation3598 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((x ∘ w) ∘ u)
def Equation3612 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ w) ∘ y)
def Equation3615 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((y ∘ w) ∘ u)
def Equation3629 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ w) ∘ y)
def Equation3632 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((z ∘ w) ∘ u)
def Equation3634 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ x) ∘ y)
def Equation3637 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ x) ∘ u)
def Equation3638 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ y) ∘ x)
def Equation3639 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ y) ∘ y)
def Equation3640 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ y) ∘ z)
def Equation3641 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ y) ∘ w)
def Equation3642 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ y) ∘ u)
def Equation3644 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ z) ∘ y)
def Equation3647 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ z) ∘ u)
def Equation3649 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ w) ∘ y)
def Equation3652 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ w) ∘ u)
def Equation3653 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ u) ∘ x)
def Equation3654 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ u) ∘ y)
def Equation3655 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ u) ∘ z)
def Equation3656 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ u) ∘ w)
def Equation3657 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ u) ∘ u)
def Equation3707 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (w ∘ y)
def Equation3710 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = (y ∘ z) ∘ (w ∘ u)
def Equation3744 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (w ∘ y)
def Equation3747 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (x ∘ z) ∘ (w ∘ u)
def Equation3781 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (w ∘ y)
def Equation3784 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (y ∘ z) ∘ (w ∘ u)
def Equation3798 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (w ∘ y)
def Equation3801 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ x) ∘ (w ∘ u)
def Equation3815 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (w ∘ y)
def Equation3818 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ y) ∘ (w ∘ u)
def Equation3832 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (w ∘ y)
def Equation3835 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ z) ∘ (w ∘ u)
def Equation3837 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (x ∘ y)
def Equation3840 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (x ∘ u)
def Equation3841 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (y ∘ x)
def Equation3842 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (y ∘ y)
def Equation3843 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (y ∘ z)
def Equation3844 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (y ∘ w)
def Equation3845 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (y ∘ u)
def Equation3847 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (z ∘ y)
def Equation3850 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (z ∘ u)
def Equation3852 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (w ∘ y)
def Equation3855 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (w ∘ u)
def Equation3856 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (u ∘ x)
def Equation3857 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (u ∘ y)
def Equation3858 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (u ∘ z)
def Equation3859 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (u ∘ w)
def Equation3860 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (u ∘ u)
def Equation3910 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ w)) ∘ y
def Equation3913 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = (y ∘ (z ∘ w)) ∘ u
def Equation3947 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ w)) ∘ y
def Equation3950 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (x ∘ (z ∘ w)) ∘ u
def Equation3984 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ w)) ∘ y
def Equation3987 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (y ∘ (z ∘ w)) ∘ u
def Equation4001 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ w)) ∘ y
def Equation4004 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (x ∘ w)) ∘ u
def Equation4018 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ w)) ∘ y
def Equation4021 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (y ∘ w)) ∘ u
def Equation4035 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ w)) ∘ y
def Equation4038 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (z ∘ w)) ∘ u
def Equation4040 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ x)) ∘ y
def Equation4043 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ x)) ∘ u
def Equation4044 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ y)) ∘ x
def Equation4045 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ y)) ∘ y
def Equation4046 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ y)) ∘ z
def Equation4047 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ y)) ∘ w
def Equation4048 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ y)) ∘ u
def Equation4050 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ z)) ∘ y
def Equation4053 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ z)) ∘ u
def Equation4055 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ w)) ∘ y
def Equation4058 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ w)) ∘ u
def Equation4059 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ u)) ∘ x
def Equation4060 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ u)) ∘ y
def Equation4061 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ u)) ∘ z
def Equation4062 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ u)) ∘ w
def Equation4063 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ u)) ∘ u
def Equation4113 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ w) ∘ y
def Equation4116 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ x = ((y ∘ z) ∘ w) ∘ u
def Equation4150 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ w) ∘ y
def Equation4153 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((x ∘ z) ∘ w) ∘ u
def Equation4187 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ w) ∘ y
def Equation4190 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((y ∘ z) ∘ w) ∘ u
def Equation4204 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ w) ∘ y
def Equation4207 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ x) ∘ w) ∘ u
def Equation4221 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ w) ∘ y
def Equation4224 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ y) ∘ w) ∘ u
def Equation4238 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ w) ∘ y
def Equation4241 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ z) ∘ w) ∘ u
def Equation4243 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ x) ∘ y
def Equation4246 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ x) ∘ u
def Equation4247 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ y) ∘ x
def Equation4248 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ y) ∘ y
def Equation4249 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ y) ∘ z
def Equation4250 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ y) ∘ w
def Equation4251 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ y) ∘ u
def Equation4253 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ z) ∘ y
def Equation4256 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ z) ∘ u
def Equation4258 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ w) ∘ y
def Equation4261 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ w) ∘ u
def Equation4262 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ u) ∘ x
def Equation4263 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ u) ∘ y
def Equation4264 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ u) ∘ z
def Equation4265 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ u) ∘ w
def Equation4266 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ u) ∘ u
def Equation4310 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (w ∘ y)
def Equation4313 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (x ∘ y) = z ∘ (w ∘ u)
def Equation4335 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = z ∘ (w ∘ y)
def Equation4338 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ x) = z ∘ (w ∘ u)
def Equation4354 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = z ∘ (w ∘ y)
def Equation4356 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ y) = z ∘ (w ∘ u)
def Equation4372 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = z ∘ (w ∘ y)
def Equation4373 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = z ∘ (w ∘ u)
def Equation4374 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = w ∘ (y ∘ z)
def Equation4376 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = w ∘ (z ∘ y)
def Equation4377 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = w ∘ (z ∘ u)
def Equation4378 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = w ∘ (u ∘ z)
def Equation4428 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ w) ∘ y
def Equation4431 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (x ∘ y) = (z ∘ w) ∘ u
def Equation4465 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ w) ∘ y
def Equation4468 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ x) = (z ∘ w) ∘ u
def Equation4502 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ w) ∘ y
def Equation4505 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ y) = (z ∘ w) ∘ u
def Equation4519 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ w) ∘ y
def Equation4522 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (x ∘ w) ∘ u
def Equation4536 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ w) ∘ y
def Equation4539 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (y ∘ w) ∘ u
def Equation4553 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ w) ∘ y
def Equation4556 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (z ∘ w) ∘ u
def Equation4558 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ x) ∘ y
def Equation4561 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ x) ∘ u
def Equation4562 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ y) ∘ x
def Equation4563 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ y) ∘ y
def Equation4564 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ y) ∘ z
def Equation4565 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ y) ∘ w
def Equation4566 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ y) ∘ u
def Equation4568 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ z) ∘ y
def Equation4571 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ z) ∘ u
def Equation4573 (G: Type*) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ w) ∘ y
def Equation4576 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ w) ∘ u
def Equation4577 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ u) ∘ x
def Equation4578 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ u) ∘ y
def Equation4579 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ u) ∘ z
def Equation4580 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ u) ∘ w
def Equation4581 (G: Type*) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ u) ∘ u
def Equation4625 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ w) ∘ y
def Equation4628 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ x) ∘ y = (z ∘ w) ∘ u
def Equation4650 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ x = (z ∘ w) ∘ y
def Equation4653 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ x = (z ∘ w) ∘ u
def Equation4669 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ y = (z ∘ w) ∘ y
def Equation4671 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ y = (z ∘ w) ∘ u
def Equation4687 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (z ∘ w) ∘ y
def Equation4688 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (z ∘ w) ∘ u
def Equation4689 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (w ∘ y) ∘ z
def Equation4691 (G: Type*) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (w ∘ z) ∘ y
def Equation4692 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (w ∘ z) ∘ u
def Equation4693 (G: Type*) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (w ∘ u) ∘ z
theorem Equation98_implies_Equation95 (G : Type*) [Magma G] (h : Equation98 G) : Equation95 G := λ x y z w => h x y z w y
theorem Equation150_implies_Equation147 (G : Type*) [Magma G] (h : Equation150 G) : Equation147 G := λ x y z w => h x y z w y
theorem Equation202_implies_Equation199 (G : Type*) [Magma G] (h : Equation202 G) : Equation199 G := λ x y z w => h x y z w y
theorem Equation254_implies_Equation251 (G : Type*) [Magma G] (h : Equation254 G) : Equation251 G := λ x y z w => h x y z w y
theorem Equation306_implies_Equation303 (G : Type*) [Magma G] (h : Equation306 G) : Equation303 G := λ x y z w => h x y z w y
theorem Equation358_implies_Equation355 (G : Type*) [Magma G] (h : Equation358 G) : Equation355 G := λ x y z w => h x y z w y
theorem Equation410_implies_Equation407 (G : Type*) [Magma G] (h : Equation410 G) : Equation407 G := λ x y z w => h x y z w y
theorem Equation462_implies_Equation459 (G : Type*) [Magma G] (h : Equation462 G) : Equation459 G := λ x y z w => h x y z w y
theorem Equation499_implies_Equation496 (G : Type*) [Magma G] (h : Equation499 G) : Equation496 G := λ x y z w => h x y z w y
theorem Equation536_implies_Equation533 (G : Type*) [Magma G] (h : Equation536 G) : Equation533 G := λ x y z w => h x y z w y
theorem Equation553_implies_Equation550 (G : Type*) [Magma G] (h : Equation553 G) : Equation550 G := λ x y z w => h x y z w y
theorem Equation570_implies_Equation567 (G : Type*) [Magma G] (h : Equation570 G) : Equation567 G := λ x y z w => h x y z w y
theorem Equation587_implies_Equation584 (G : Type*) [Magma G] (h : Equation587 G) : Equation584 G := λ x y z w => h x y z w y
theorem Equation592_implies_Equation589 (G : Type*) [Magma G] (h : Equation592 G) : Equation589 G := λ x y z w => h x y z w y
theorem Equation597_implies_Equation594 (G : Type*) [Magma G] (h : Equation597 G) : Equation594 G := λ x y z w => h x y z w y
theorem Equation602_implies_Equation599 (G : Type*) [Magma G] (h : Equation602 G) : Equation599 G := λ x y z w => h x y z w y
theorem Equation607_implies_Equation604 (G : Type*) [Magma G] (h : Equation607 G) : Equation604 G := λ x y z w => h x y z w y
theorem Equation608_implies_Equation593 (G : Type*) [Magma G] (h : Equation608 G) : Equation593 G := λ x y z w => h x y z w y
theorem Equation609_implies_Equation594 (G : Type*) [Magma G] (h : Equation609 G) : Equation594 G := λ x y z w => h x y z w y
theorem Equation610_implies_Equation595 (G : Type*) [Magma G] (h : Equation610 G) : Equation595 G := λ x y z w => h x y z w y
theorem Equation611_implies_Equation596 (G : Type*) [Magma G] (h : Equation611 G) : Equation596 G := λ x y z w => h x y z w y
theorem Equation612_implies_Equation594 (G : Type*) [Magma G] (h : Equation612 G) : Equation594 G := λ x y z w => h x y z w y
theorem Equation665_implies_Equation662 (G : Type*) [Magma G] (h : Equation665 G) : Equation662 G := λ x y z w => h x y z w y
theorem Equation702_implies_Equation699 (G : Type*) [Magma G] (h : Equation702 G) : Equation699 G := λ x y z w => h x y z w y
theorem Equation739_implies_Equation736 (G : Type*) [Magma G] (h : Equation739 G) : Equation736 G := λ x y z w => h x y z w y
theorem Equation756_implies_Equation753 (G : Type*) [Magma G] (h : Equation756 G) : Equation753 G := λ x y z w => h x y z w y
theorem Equation773_implies_Equation770 (G : Type*) [Magma G] (h : Equation773 G) : Equation770 G := λ x y z w => h x y z w y
theorem Equation790_implies_Equation787 (G : Type*) [Magma G] (h : Equation790 G) : Equation787 G := λ x y z w => h x y z w y
theorem Equation795_implies_Equation792 (G : Type*) [Magma G] (h : Equation795 G) : Equation792 G := λ x y z w => h x y z w y
theorem Equation800_implies_Equation797 (G : Type*) [Magma G] (h : Equation800 G) : Equation797 G := λ x y z w => h x y z w y
theorem Equation805_implies_Equation802 (G : Type*) [Magma G] (h : Equation805 G) : Equation802 G := λ x y z w => h x y z w y
theorem Equation810_implies_Equation807 (G : Type*) [Magma G] (h : Equation810 G) : Equation807 G := λ x y z w => h x y z w y
theorem Equation811_implies_Equation796 (G : Type*) [Magma G] (h : Equation811 G) : Equation796 G := λ x y z w => h x y z w y
theorem Equation812_implies_Equation797 (G : Type*) [Magma G] (h : Equation812 G) : Equation797 G := λ x y z w => h x y z w y
theorem Equation813_implies_Equation798 (G : Type*) [Magma G] (h : Equation813 G) : Equation798 G := λ x y z w => h x y z w y
theorem Equation814_implies_Equation799 (G : Type*) [Magma G] (h : Equation814 G) : Equation799 G := λ x y z w => h x y z w y
theorem Equation815_implies_Equation797 (G : Type*) [Magma G] (h : Equation815 G) : Equation797 G := λ x y z w => h x y z w y
theorem Equation868_implies_Equation865 (G : Type*) [Magma G] (h : Equation868 G) : Equation865 G := λ x y z w => h x y z w y
theorem Equation905_implies_Equation902 (G : Type*) [Magma G] (h : Equation905 G) : Equation902 G := λ x y z w => h x y z w y
theorem Equation942_implies_Equation939 (G : Type*) [Magma G] (h : Equation942 G) : Equation939 G := λ x y z w => h x y z w y
theorem Equation959_implies_Equation956 (G : Type*) [Magma G] (h : Equation959 G) : Equation956 G := λ x y z w => h x y z w y
theorem Equation976_implies_Equation973 (G : Type*) [Magma G] (h : Equation976 G) : Equation973 G := λ x y z w => h x y z w y
theorem Equation993_implies_Equation990 (G : Type*) [Magma G] (h : Equation993 G) : Equation990 G := λ x y z w => h x y z w y
theorem Equation998_implies_Equation995 (G : Type*) [Magma G] (h : Equation998 G) : Equation995 G := λ x y z w => h x y z w y
theorem Equation1003_implies_Equation1000 (G : Type*) [Magma G] (h : Equation1003 G) : Equation1000 G := λ x y z w => h x y z w y
theorem Equation1008_implies_Equation1005 (G : Type*) [Magma G] (h : Equation1008 G) : Equation1005 G := λ x y z w => h x y z w y
theorem Equation1013_implies_Equation1010 (G : Type*) [Magma G] (h : Equation1013 G) : Equation1010 G := λ x y z w => h x y z w y
theorem Equation1014_implies_Equation999 (G : Type*) [Magma G] (h : Equation1014 G) : Equation999 G := λ x y z w => h x y z w y
theorem Equation1015_implies_Equation1000 (G : Type*) [Magma G] (h : Equation1015 G) : Equation1000 G := λ x y z w => h x y z w y
theorem Equation1016_implies_Equation1001 (G : Type*) [Magma G] (h : Equation1016 G) : Equation1001 G := λ x y z w => h x y z w y
theorem Equation1017_implies_Equation1002 (G : Type*) [Magma G] (h : Equation1017 G) : Equation1002 G := λ x y z w => h x y z w y
theorem Equation1018_implies_Equation1000 (G : Type*) [Magma G] (h : Equation1018 G) : Equation1000 G := λ x y z w => h x y z w y
theorem Equation1071_implies_Equation1068 (G : Type*) [Magma G] (h : Equation1071 G) : Equation1068 G := λ x y z w => h x y z w y
theorem Equation1108_implies_Equation1105 (G : Type*) [Magma G] (h : Equation1108 G) : Equation1105 G := λ x y z w => h x y z w y
theorem Equation1145_implies_Equation1142 (G : Type*) [Magma G] (h : Equation1145 G) : Equation1142 G := λ x y z w => h x y z w y
theorem Equation1162_implies_Equation1159 (G : Type*) [Magma G] (h : Equation1162 G) : Equation1159 G := λ x y z w => h x y z w y
theorem Equation1179_implies_Equation1176 (G : Type*) [Magma G] (h : Equation1179 G) : Equation1176 G := λ x y z w => h x y z w y
theorem Equation1196_implies_Equation1193 (G : Type*) [Magma G] (h : Equation1196 G) : Equation1193 G := λ x y z w => h x y z w y
theorem Equation1201_implies_Equation1198 (G : Type*) [Magma G] (h : Equation1201 G) : Equation1198 G := λ x y z w => h x y z w y
theorem Equation1206_implies_Equation1203 (G : Type*) [Magma G] (h : Equation1206 G) : Equation1203 G := λ x y z w => h x y z w y
theorem Equation1211_implies_Equation1208 (G : Type*) [Magma G] (h : Equation1211 G) : Equation1208 G := λ x y z w => h x y z w y
theorem Equation1216_implies_Equation1213 (G : Type*) [Magma G] (h : Equation1216 G) : Equation1213 G := λ x y z w => h x y z w y
theorem Equation1217_implies_Equation1202 (G : Type*) [Magma G] (h : Equation1217 G) : Equation1202 G := λ x y z w => h x y z w y
theorem Equation1218_implies_Equation1203 (G : Type*) [Magma G] (h : Equation1218 G) : Equation1203 G := λ x y z w => h x y z w y
theorem Equation1219_implies_Equation1204 (G : Type*) [Magma G] (h : Equation1219 G) : Equation1204 G := λ x y z w => h x y z w y
theorem Equation1220_implies_Equation1205 (G : Type*) [Magma G] (h : Equation1220 G) : Equation1205 G := λ x y z w => h x y z w y
theorem Equation1221_implies_Equation1203 (G : Type*) [Magma G] (h : Equation1221 G) : Equation1203 G := λ x y z w => h x y z w y
theorem Equation1274_implies_Equation1271 (G : Type*) [Magma G] (h : Equation1274 G) : Equation1271 G := λ x y z w => h x y z w y
theorem Equation1311_implies_Equation1308 (G : Type*) [Magma G] (h : Equation1311 G) : Equation1308 G := λ x y z w => h x y z w y
theorem Equation1348_implies_Equation1345 (G : Type*) [Magma G] (h : Equation1348 G) : Equation1345 G := λ x y z w => h x y z w y
theorem Equation1365_implies_Equation1362 (G : Type*) [Magma G] (h : Equation1365 G) : Equation1362 G := λ x y z w => h x y z w y
theorem Equation1382_implies_Equation1379 (G : Type*) [Magma G] (h : Equation1382 G) : Equation1379 G := λ x y z w => h x y z w y
theorem Equation1399_implies_Equation1396 (G : Type*) [Magma G] (h : Equation1399 G) : Equation1396 G := λ x y z w => h x y z w y
theorem Equation1404_implies_Equation1401 (G : Type*) [Magma G] (h : Equation1404 G) : Equation1401 G := λ x y z w => h x y z w y
theorem Equation1409_implies_Equation1406 (G : Type*) [Magma G] (h : Equation1409 G) : Equation1406 G := λ x y z w => h x y z w y
theorem Equation1414_implies_Equation1411 (G : Type*) [Magma G] (h : Equation1414 G) : Equation1411 G := λ x y z w => h x y z w y
theorem Equation1419_implies_Equation1416 (G : Type*) [Magma G] (h : Equation1419 G) : Equation1416 G := λ x y z w => h x y z w y
theorem Equation1420_implies_Equation1405 (G : Type*) [Magma G] (h : Equation1420 G) : Equation1405 G := λ x y z w => h x y z w y
theorem Equation1421_implies_Equation1406 (G : Type*) [Magma G] (h : Equation1421 G) : Equation1406 G := λ x y z w => h x y z w y
theorem Equation1422_implies_Equation1407 (G : Type*) [Magma G] (h : Equation1422 G) : Equation1407 G := λ x y z w => h x y z w y
theorem Equation1423_implies_Equation1408 (G : Type*) [Magma G] (h : Equation1423 G) : Equation1408 G := λ x y z w => h x y z w y
theorem Equation1424_implies_Equation1406 (G : Type*) [Magma G] (h : Equation1424 G) : Equation1406 G := λ x y z w => h x y z w y
theorem Equation1477_implies_Equation1474 (G : Type*) [Magma G] (h : Equation1477 G) : Equation1474 G := λ x y z w => h x y z w y
theorem Equation1514_implies_Equation1511 (G : Type*) [Magma G] (h : Equation1514 G) : Equation1511 G := λ x y z w => h x y z w y
theorem Equation1551_implies_Equation1548 (G : Type*) [Magma G] (h : Equation1551 G) : Equation1548 G := λ x y z w => h x y z w y
theorem Equation1568_implies_Equation1565 (G : Type*) [Magma G] (h : Equation1568 G) : Equation1565 G := λ x y z w => h x y z w y
theorem Equation1585_implies_Equation1582 (G : Type*) [Magma G] (h : Equation1585 G) : Equation1582 G := λ x y z w => h x y z w y
theorem Equation1602_implies_Equation1599 (G : Type*) [Magma G] (h : Equation1602 G) : Equation1599 G := λ x y z w => h x y z w y
theorem Equation1607_implies_Equation1604 (G : Type*) [Magma G] (h : Equation1607 G) : Equation1604 G := λ x y z w => h x y z w y
theorem Equation1612_implies_Equation1609 (G : Type*) [Magma G] (h : Equation1612 G) : Equation1609 G := λ x y z w => h x y z w y
theorem Equation1617_implies_Equation1614 (G : Type*) [Magma G] (h : Equation1617 G) : Equation1614 G := λ x y z w => h x y z w y
theorem Equation1622_implies_Equation1619 (G : Type*) [Magma G] (h : Equation1622 G) : Equation1619 G := λ x y z w => h x y z w y
theorem Equation1623_implies_Equation1608 (G : Type*) [Magma G] (h : Equation1623 G) : Equation1608 G := λ x y z w => h x y z w y
theorem Equation1624_implies_Equation1609 (G : Type*) [Magma G] (h : Equation1624 G) : Equation1609 G := λ x y z w => h x y z w y
theorem Equation1625_implies_Equation1610 (G : Type*) [Magma G] (h : Equation1625 G) : Equation1610 G := λ x y z w => h x y z w y
theorem Equation1626_implies_Equation1611 (G : Type*) [Magma G] (h : Equation1626 G) : Equation1611 G := λ x y z w => h x y z w y
theorem Equation1627_implies_Equation1609 (G : Type*) [Magma G] (h : Equation1627 G) : Equation1609 G := λ x y z w => h x y z w y
theorem Equation1680_implies_Equation1677 (G : Type*) [Magma G] (h : Equation1680 G) : Equation1677 G := λ x y z w => h x y z w y
theorem Equation1717_implies_Equation1714 (G : Type*) [Magma G] (h : Equation1717 G) : Equation1714 G := λ x y z w => h x y z w y
theorem Equation1754_implies_Equation1751 (G : Type*) [Magma G] (h : Equation1754 G) : Equation1751 G := λ x y z w => h x y z w y
theorem Equation1771_implies_Equation1768 (G : Type*) [Magma G] (h : Equation1771 G) : Equation1768 G := λ x y z w => h x y z w y
theorem Equation1788_implies_Equation1785 (G : Type*) [Magma G] (h : Equation1788 G) : Equation1785 G := λ x y z w => h x y z w y
theorem Equation1805_implies_Equation1802 (G : Type*) [Magma G] (h : Equation1805 G) : Equation1802 G := λ x y z w => h x y z w y
theorem Equation1810_implies_Equation1807 (G : Type*) [Magma G] (h : Equation1810 G) : Equation1807 G := λ x y z w => h x y z w y
theorem Equation1815_implies_Equation1812 (G : Type*) [Magma G] (h : Equation1815 G) : Equation1812 G := λ x y z w => h x y z w y
theorem Equation1820_implies_Equation1817 (G : Type*) [Magma G] (h : Equation1820 G) : Equation1817 G := λ x y z w => h x y z w y
theorem Equation1825_implies_Equation1822 (G : Type*) [Magma G] (h : Equation1825 G) : Equation1822 G := λ x y z w => h x y z w y
theorem Equation1826_implies_Equation1811 (G : Type*) [Magma G] (h : Equation1826 G) : Equation1811 G := λ x y z w => h x y z w y
theorem Equation1827_implies_Equation1812 (G : Type*) [Magma G] (h : Equation1827 G) : Equation1812 G := λ x y z w => h x y z w y
theorem Equation1828_implies_Equation1813 (G : Type*) [Magma G] (h : Equation1828 G) : Equation1813 G := λ x y z w => h x y z w y
theorem Equation1829_implies_Equation1814 (G : Type*) [Magma G] (h : Equation1829 G) : Equation1814 G := λ x y z w => h x y z w y
theorem Equation1830_implies_Equation1812 (G : Type*) [Magma G] (h : Equation1830 G) : Equation1812 G := λ x y z w => h x y z w y
theorem Equation1883_implies_Equation1880 (G : Type*) [Magma G] (h : Equation1883 G) : Equation1880 G := λ x y z w => h x y z w y
theorem Equation1920_implies_Equation1917 (G : Type*) [Magma G] (h : Equation1920 G) : Equation1917 G := λ x y z w => h x y z w y
theorem Equation1957_implies_Equation1954 (G : Type*) [Magma G] (h : Equation1957 G) : Equation1954 G := λ x y z w => h x y z w y
theorem Equation1974_implies_Equation1971 (G : Type*) [Magma G] (h : Equation1974 G) : Equation1971 G := λ x y z w => h x y z w y
theorem Equation1991_implies_Equation1988 (G : Type*) [Magma G] (h : Equation1991 G) : Equation1988 G := λ x y z w => h x y z w y
theorem Equation2008_implies_Equation2005 (G : Type*) [Magma G] (h : Equation2008 G) : Equation2005 G := λ x y z w => h x y z w y
theorem Equation2013_implies_Equation2010 (G : Type*) [Magma G] (h : Equation2013 G) : Equation2010 G := λ x y z w => h x y z w y
theorem Equation2018_implies_Equation2015 (G : Type*) [Magma G] (h : Equation2018 G) : Equation2015 G := λ x y z w => h x y z w y
theorem Equation2023_implies_Equation2020 (G : Type*) [Magma G] (h : Equation2023 G) : Equation2020 G := λ x y z w => h x y z w y
theorem Equation2028_implies_Equation2025 (G : Type*) [Magma G] (h : Equation2028 G) : Equation2025 G := λ x y z w => h x y z w y
theorem Equation2029_implies_Equation2014 (G : Type*) [Magma G] (h : Equation2029 G) : Equation2014 G := λ x y z w => h x y z w y
theorem Equation2030_implies_Equation2015 (G : Type*) [Magma G] (h : Equation2030 G) : Equation2015 G := λ x y z w => h x y z w y
theorem Equation2031_implies_Equation2016 (G : Type*) [Magma G] (h : Equation2031 G) : Equation2016 G := λ x y z w => h x y z w y
theorem Equation2032_implies_Equation2017 (G : Type*) [Magma G] (h : Equation2032 G) : Equation2017 G := λ x y z w => h x y z w y
theorem Equation2033_implies_Equation2015 (G : Type*) [Magma G] (h : Equation2033 G) : Equation2015 G := λ x y z w => h x y z w y
theorem Equation2086_implies_Equation2083 (G : Type*) [Magma G] (h : Equation2086 G) : Equation2083 G := λ x y z w => h x y z w y
theorem Equation2123_implies_Equation2120 (G : Type*) [Magma G] (h : Equation2123 G) : Equation2120 G := λ x y z w => h x y z w y
theorem Equation2160_implies_Equation2157 (G : Type*) [Magma G] (h : Equation2160 G) : Equation2157 G := λ x y z w => h x y z w y
theorem Equation2177_implies_Equation2174 (G : Type*) [Magma G] (h : Equation2177 G) : Equation2174 G := λ x y z w => h x y z w y
theorem Equation2194_implies_Equation2191 (G : Type*) [Magma G] (h : Equation2194 G) : Equation2191 G := λ x y z w => h x y z w y
theorem Equation2211_implies_Equation2208 (G : Type*) [Magma G] (h : Equation2211 G) : Equation2208 G := λ x y z w => h x y z w y
theorem Equation2216_implies_Equation2213 (G : Type*) [Magma G] (h : Equation2216 G) : Equation2213 G := λ x y z w => h x y z w y
theorem Equation2221_implies_Equation2218 (G : Type*) [Magma G] (h : Equation2221 G) : Equation2218 G := λ x y z w => h x y z w y
theorem Equation2226_implies_Equation2223 (G : Type*) [Magma G] (h : Equation2226 G) : Equation2223 G := λ x y z w => h x y z w y
theorem Equation2231_implies_Equation2228 (G : Type*) [Magma G] (h : Equation2231 G) : Equation2228 G := λ x y z w => h x y z w y
theorem Equation2232_implies_Equation2217 (G : Type*) [Magma G] (h : Equation2232 G) : Equation2217 G := λ x y z w => h x y z w y
theorem Equation2233_implies_Equation2218 (G : Type*) [Magma G] (h : Equation2233 G) : Equation2218 G := λ x y z w => h x y z w y
theorem Equation2234_implies_Equation2219 (G : Type*) [Magma G] (h : Equation2234 G) : Equation2219 G := λ x y z w => h x y z w y
theorem Equation2235_implies_Equation2220 (G : Type*) [Magma G] (h : Equation2235 G) : Equation2220 G := λ x y z w => h x y z w y
theorem Equation2236_implies_Equation2218 (G : Type*) [Magma G] (h : Equation2236 G) : Equation2218 G := λ x y z w => h x y z w y
theorem Equation2289_implies_Equation2286 (G : Type*) [Magma G] (h : Equation2289 G) : Equation2286 G := λ x y z w => h x y z w y
theorem Equation2326_implies_Equation2323 (G : Type*) [Magma G] (h : Equation2326 G) : Equation2323 G := λ x y z w => h x y z w y
theorem Equation2363_implies_Equation2360 (G : Type*) [Magma G] (h : Equation2363 G) : Equation2360 G := λ x y z w => h x y z w y
theorem Equation2380_implies_Equation2377 (G : Type*) [Magma G] (h : Equation2380 G) : Equation2377 G := λ x y z w => h x y z w y
theorem Equation2397_implies_Equation2394 (G : Type*) [Magma G] (h : Equation2397 G) : Equation2394 G := λ x y z w => h x y z w y
theorem Equation2414_implies_Equation2411 (G : Type*) [Magma G] (h : Equation2414 G) : Equation2411 G := λ x y z w => h x y z w y
theorem Equation2419_implies_Equation2416 (G : Type*) [Magma G] (h : Equation2419 G) : Equation2416 G := λ x y z w => h x y z w y
theorem Equation2424_implies_Equation2421 (G : Type*) [Magma G] (h : Equation2424 G) : Equation2421 G := λ x y z w => h x y z w y
theorem Equation2429_implies_Equation2426 (G : Type*) [Magma G] (h : Equation2429 G) : Equation2426 G := λ x y z w => h x y z w y
theorem Equation2434_implies_Equation2431 (G : Type*) [Magma G] (h : Equation2434 G) : Equation2431 G := λ x y z w => h x y z w y
theorem Equation2435_implies_Equation2420 (G : Type*) [Magma G] (h : Equation2435 G) : Equation2420 G := λ x y z w => h x y z w y
theorem Equation2436_implies_Equation2421 (G : Type*) [Magma G] (h : Equation2436 G) : Equation2421 G := λ x y z w => h x y z w y
theorem Equation2437_implies_Equation2422 (G : Type*) [Magma G] (h : Equation2437 G) : Equation2422 G := λ x y z w => h x y z w y
theorem Equation2438_implies_Equation2423 (G : Type*) [Magma G] (h : Equation2438 G) : Equation2423 G := λ x y z w => h x y z w y
theorem Equation2439_implies_Equation2421 (G : Type*) [Magma G] (h : Equation2439 G) : Equation2421 G := λ x y z w => h x y z w y
theorem Equation2492_implies_Equation2489 (G : Type*) [Magma G] (h : Equation2492 G) : Equation2489 G := λ x y z w => h x y z w y
theorem Equation2529_implies_Equation2526 (G : Type*) [Magma G] (h : Equation2529 G) : Equation2526 G := λ x y z w => h x y z w y
theorem Equation2566_implies_Equation2563 (G : Type*) [Magma G] (h : Equation2566 G) : Equation2563 G := λ x y z w => h x y z w y
theorem Equation2583_implies_Equation2580 (G : Type*) [Magma G] (h : Equation2583 G) : Equation2580 G := λ x y z w => h x y z w y
theorem Equation2600_implies_Equation2597 (G : Type*) [Magma G] (h : Equation2600 G) : Equation2597 G := λ x y z w => h x y z w y
theorem Equation2617_implies_Equation2614 (G : Type*) [Magma G] (h : Equation2617 G) : Equation2614 G := λ x y z w => h x y z w y
theorem Equation2622_implies_Equation2619 (G : Type*) [Magma G] (h : Equation2622 G) : Equation2619 G := λ x y z w => h x y z w y
theorem Equation2627_implies_Equation2624 (G : Type*) [Magma G] (h : Equation2627 G) : Equation2624 G := λ x y z w => h x y z w y
theorem Equation2632_implies_Equation2629 (G : Type*) [Magma G] (h : Equation2632 G) : Equation2629 G := λ x y z w => h x y z w y
theorem Equation2637_implies_Equation2634 (G : Type*) [Magma G] (h : Equation2637 G) : Equation2634 G := λ x y z w => h x y z w y
theorem Equation2638_implies_Equation2623 (G : Type*) [Magma G] (h : Equation2638 G) : Equation2623 G := λ x y z w => h x y z w y
theorem Equation2639_implies_Equation2624 (G : Type*) [Magma G] (h : Equation2639 G) : Equation2624 G := λ x y z w => h x y z w y
theorem Equation2640_implies_Equation2625 (G : Type*) [Magma G] (h : Equation2640 G) : Equation2625 G := λ x y z w => h x y z w y
theorem Equation2641_implies_Equation2626 (G : Type*) [Magma G] (h : Equation2641 G) : Equation2626 G := λ x y z w => h x y z w y
theorem Equation2642_implies_Equation2624 (G : Type*) [Magma G] (h : Equation2642 G) : Equation2624 G := λ x y z w => h x y z w y
theorem Equation2695_implies_Equation2692 (G : Type*) [Magma G] (h : Equation2695 G) : Equation2692 G := λ x y z w => h x y z w y
theorem Equation2732_implies_Equation2729 (G : Type*) [Magma G] (h : Equation2732 G) : Equation2729 G := λ x y z w => h x y z w y
theorem Equation2769_implies_Equation2766 (G : Type*) [Magma G] (h : Equation2769 G) : Equation2766 G := λ x y z w => h x y z w y
theorem Equation2786_implies_Equation2783 (G : Type*) [Magma G] (h : Equation2786 G) : Equation2783 G := λ x y z w => h x y z w y
theorem Equation2803_implies_Equation2800 (G : Type*) [Magma G] (h : Equation2803 G) : Equation2800 G := λ x y z w => h x y z w y
theorem Equation2820_implies_Equation2817 (G : Type*) [Magma G] (h : Equation2820 G) : Equation2817 G := λ x y z w => h x y z w y
theorem Equation2825_implies_Equation2822 (G : Type*) [Magma G] (h : Equation2825 G) : Equation2822 G := λ x y z w => h x y z w y
theorem Equation2830_implies_Equation2827 (G : Type*) [Magma G] (h : Equation2830 G) : Equation2827 G := λ x y z w => h x y z w y
theorem Equation2835_implies_Equation2832 (G : Type*) [Magma G] (h : Equation2835 G) : Equation2832 G := λ x y z w => h x y z w y
theorem Equation2840_implies_Equation2837 (G : Type*) [Magma G] (h : Equation2840 G) : Equation2837 G := λ x y z w => h x y z w y
theorem Equation2841_implies_Equation2826 (G : Type*) [Magma G] (h : Equation2841 G) : Equation2826 G := λ x y z w => h x y z w y
theorem Equation2842_implies_Equation2827 (G : Type*) [Magma G] (h : Equation2842 G) : Equation2827 G := λ x y z w => h x y z w y
theorem Equation2843_implies_Equation2828 (G : Type*) [Magma G] (h : Equation2843 G) : Equation2828 G := λ x y z w => h x y z w y
theorem Equation2844_implies_Equation2829 (G : Type*) [Magma G] (h : Equation2844 G) : Equation2829 G := λ x y z w => h x y z w y
theorem Equation2845_implies_Equation2827 (G : Type*) [Magma G] (h : Equation2845 G) : Equation2827 G := λ x y z w => h x y z w y
theorem Equation2898_implies_Equation2895 (G : Type*) [Magma G] (h : Equation2898 G) : Equation2895 G := λ x y z w => h x y z w y
theorem Equation2935_implies_Equation2932 (G : Type*) [Magma G] (h : Equation2935 G) : Equation2932 G := λ x y z w => h x y z w y
theorem Equation2972_implies_Equation2969 (G : Type*) [Magma G] (h : Equation2972 G) : Equation2969 G := λ x y z w => h x y z w y
theorem Equation2989_implies_Equation2986 (G : Type*) [Magma G] (h : Equation2989 G) : Equation2986 G := λ x y z w => h x y z w y
theorem Equation3006_implies_Equation3003 (G : Type*) [Magma G] (h : Equation3006 G) : Equation3003 G := λ x y z w => h x y z w y
theorem Equation3023_implies_Equation3020 (G : Type*) [Magma G] (h : Equation3023 G) : Equation3020 G := λ x y z w => h x y z w y
theorem Equation3028_implies_Equation3025 (G : Type*) [Magma G] (h : Equation3028 G) : Equation3025 G := λ x y z w => h x y z w y
theorem Equation3033_implies_Equation3030 (G : Type*) [Magma G] (h : Equation3033 G) : Equation3030 G := λ x y z w => h x y z w y
theorem Equation3038_implies_Equation3035 (G : Type*) [Magma G] (h : Equation3038 G) : Equation3035 G := λ x y z w => h x y z w y
theorem Equation3043_implies_Equation3040 (G : Type*) [Magma G] (h : Equation3043 G) : Equation3040 G := λ x y z w => h x y z w y
theorem Equation3044_implies_Equation3029 (G : Type*) [Magma G] (h : Equation3044 G) : Equation3029 G := λ x y z w => h x y z w y
theorem Equation3045_implies_Equation3030 (G : Type*) [Magma G] (h : Equation3045 G) : Equation3030 G := λ x y z w => h x y z w y
theorem Equation3046_implies_Equation3031 (G : Type*) [Magma G] (h : Equation3046 G) : Equation3031 G := λ x y z w => h x y z w y
theorem Equation3047_implies_Equation3032 (G : Type*) [Magma G] (h : Equation3047 G) : Equation3032 G := λ x y z w => h x y z w y
theorem Equation3048_implies_Equation3030 (G : Type*) [Magma G] (h : Equation3048 G) : Equation3030 G := λ x y z w => h x y z w y
theorem Equation3101_implies_Equation3098 (G : Type*) [Magma G] (h : Equation3101 G) : Equation3098 G := λ x y z w => h x y z w y
theorem Equation3138_implies_Equation3135 (G : Type*) [Magma G] (h : Equation3138 G) : Equation3135 G := λ x y z w => h x y z w y
theorem Equation3175_implies_Equation3172 (G : Type*) [Magma G] (h : Equation3175 G) : Equation3172 G := λ x y z w => h x y z w y
theorem Equation3192_implies_Equation3189 (G : Type*) [Magma G] (h : Equation3192 G) : Equation3189 G := λ x y z w => h x y z w y
theorem Equation3209_implies_Equation3206 (G : Type*) [Magma G] (h : Equation3209 G) : Equation3206 G := λ x y z w => h x y z w y
theorem Equation3226_implies_Equation3223 (G : Type*) [Magma G] (h : Equation3226 G) : Equation3223 G := λ x y z w => h x y z w y
theorem Equation3231_implies_Equation3228 (G : Type*) [Magma G] (h : Equation3231 G) : Equation3228 G := λ x y z w => h x y z w y
theorem Equation3236_implies_Equation3233 (G : Type*) [Magma G] (h : Equation3236 G) : Equation3233 G := λ x y z w => h x y z w y
theorem Equation3241_implies_Equation3238 (G : Type*) [Magma G] (h : Equation3241 G) : Equation3238 G := λ x y z w => h x y z w y
theorem Equation3246_implies_Equation3243 (G : Type*) [Magma G] (h : Equation3246 G) : Equation3243 G := λ x y z w => h x y z w y
theorem Equation3247_implies_Equation3232 (G : Type*) [Magma G] (h : Equation3247 G) : Equation3232 G := λ x y z w => h x y z w y
theorem Equation3248_implies_Equation3233 (G : Type*) [Magma G] (h : Equation3248 G) : Equation3233 G := λ x y z w => h x y z w y
theorem Equation3249_implies_Equation3234 (G : Type*) [Magma G] (h : Equation3249 G) : Equation3234 G := λ x y z w => h x y z w y
theorem Equation3250_implies_Equation3235 (G : Type*) [Magma G] (h : Equation3250 G) : Equation3235 G := λ x y z w => h x y z w y
theorem Equation3251_implies_Equation3233 (G : Type*) [Magma G] (h : Equation3251 G) : Equation3233 G := λ x y z w => h x y z w y
theorem Equation3304_implies_Equation3301 (G : Type*) [Magma G] (h : Equation3304 G) : Equation3301 G := λ x y z w => h x y z w y
theorem Equation3341_implies_Equation3338 (G : Type*) [Magma G] (h : Equation3341 G) : Equation3338 G := λ x y z w => h x y z w y
theorem Equation3378_implies_Equation3375 (G : Type*) [Magma G] (h : Equation3378 G) : Equation3375 G := λ x y z w => h x y z w y
theorem Equation3395_implies_Equation3392 (G : Type*) [Magma G] (h : Equation3395 G) : Equation3392 G := λ x y z w => h x y z w y
theorem Equation3412_implies_Equation3409 (G : Type*) [Magma G] (h : Equation3412 G) : Equation3409 G := λ x y z w => h x y z w y
theorem Equation3429_implies_Equation3426 (G : Type*) [Magma G] (h : Equation3429 G) : Equation3426 G := λ x y z w => h x y z w y
theorem Equation3434_implies_Equation3431 (G : Type*) [Magma G] (h : Equation3434 G) : Equation3431 G := λ x y z w => h x y z w y
theorem Equation3439_implies_Equation3436 (G : Type*) [Magma G] (h : Equation3439 G) : Equation3436 G := λ x y z w => h x y z w y
theorem Equation3444_implies_Equation3441 (G : Type*) [Magma G] (h : Equation3444 G) : Equation3441 G := λ x y z w => h x y z w y
theorem Equation3449_implies_Equation3446 (G : Type*) [Magma G] (h : Equation3449 G) : Equation3446 G := λ x y z w => h x y z w y
theorem Equation3450_implies_Equation3435 (G : Type*) [Magma G] (h : Equation3450 G) : Equation3435 G := λ x y z w => h x y z w y
theorem Equation3451_implies_Equation3436 (G : Type*) [Magma G] (h : Equation3451 G) : Equation3436 G := λ x y z w => h x y z w y
theorem Equation3452_implies_Equation3437 (G : Type*) [Magma G] (h : Equation3452 G) : Equation3437 G := λ x y z w => h x y z w y
theorem Equation3453_implies_Equation3438 (G : Type*) [Magma G] (h : Equation3453 G) : Equation3438 G := λ x y z w => h x y z w y
theorem Equation3454_implies_Equation3436 (G : Type*) [Magma G] (h : Equation3454 G) : Equation3436 G := λ x y z w => h x y z w y
theorem Equation3507_implies_Equation3504 (G : Type*) [Magma G] (h : Equation3507 G) : Equation3504 G := λ x y z w => h x y z w y
theorem Equation3544_implies_Equation3541 (G : Type*) [Magma G] (h : Equation3544 G) : Equation3541 G := λ x y z w => h x y z w y
theorem Equation3581_implies_Equation3578 (G : Type*) [Magma G] (h : Equation3581 G) : Equation3578 G := λ x y z w => h x y z w y
theorem Equation3598_implies_Equation3595 (G : Type*) [Magma G] (h : Equation3598 G) : Equation3595 G := λ x y z w => h x y z w y
theorem Equation3615_implies_Equation3612 (G : Type*) [Magma G] (h : Equation3615 G) : Equation3612 G := λ x y z w => h x y z w y
theorem Equation3632_implies_Equation3629 (G : Type*) [Magma G] (h : Equation3632 G) : Equation3629 G := λ x y z w => h x y z w y
theorem Equation3637_implies_Equation3634 (G : Type*) [Magma G] (h : Equation3637 G) : Equation3634 G := λ x y z w => h x y z w y
theorem Equation3642_implies_Equation3639 (G : Type*) [Magma G] (h : Equation3642 G) : Equation3639 G := λ x y z w => h x y z w y
theorem Equation3647_implies_Equation3644 (G : Type*) [Magma G] (h : Equation3647 G) : Equation3644 G := λ x y z w => h x y z w y
theorem Equation3652_implies_Equation3649 (G : Type*) [Magma G] (h : Equation3652 G) : Equation3649 G := λ x y z w => h x y z w y
theorem Equation3653_implies_Equation3638 (G : Type*) [Magma G] (h : Equation3653 G) : Equation3638 G := λ x y z w => h x y z w y
theorem Equation3654_implies_Equation3639 (G : Type*) [Magma G] (h : Equation3654 G) : Equation3639 G := λ x y z w => h x y z w y
theorem Equation3655_implies_Equation3640 (G : Type*) [Magma G] (h : Equation3655 G) : Equation3640 G := λ x y z w => h x y z w y
theorem Equation3656_implies_Equation3641 (G : Type*) [Magma G] (h : Equation3656 G) : Equation3641 G := λ x y z w => h x y z w y
theorem Equation3657_implies_Equation3639 (G : Type*) [Magma G] (h : Equation3657 G) : Equation3639 G := λ x y z w => h x y z w y
theorem Equation3710_implies_Equation3707 (G : Type*) [Magma G] (h : Equation3710 G) : Equation3707 G := λ x y z w => h x y z w y
theorem Equation3747_implies_Equation3744 (G : Type*) [Magma G] (h : Equation3747 G) : Equation3744 G := λ x y z w => h x y z w y
theorem Equation3784_implies_Equation3781 (G : Type*) [Magma G] (h : Equation3784 G) : Equation3781 G := λ x y z w => h x y z w y
theorem Equation3801_implies_Equation3798 (G : Type*) [Magma G] (h : Equation3801 G) : Equation3798 G := λ x y z w => h x y z w y
theorem Equation3818_implies_Equation3815 (G : Type*) [Magma G] (h : Equation3818 G) : Equation3815 G := λ x y z w => h x y z w y
theorem Equation3835_implies_Equation3832 (G : Type*) [Magma G] (h : Equation3835 G) : Equation3832 G := λ x y z w => h x y z w y
theorem Equation3840_implies_Equation3837 (G : Type*) [Magma G] (h : Equation3840 G) : Equation3837 G := λ x y z w => h x y z w y
theorem Equation3845_implies_Equation3842 (G : Type*) [Magma G] (h : Equation3845 G) : Equation3842 G := λ x y z w => h x y z w y
theorem Equation3850_implies_Equation3847 (G : Type*) [Magma G] (h : Equation3850 G) : Equation3847 G := λ x y z w => h x y z w y
theorem Equation3855_implies_Equation3852 (G : Type*) [Magma G] (h : Equation3855 G) : Equation3852 G := λ x y z w => h x y z w y
theorem Equation3856_implies_Equation3841 (G : Type*) [Magma G] (h : Equation3856 G) : Equation3841 G := λ x y z w => h x y z w y
theorem Equation3857_implies_Equation3842 (G : Type*) [Magma G] (h : Equation3857 G) : Equation3842 G := λ x y z w => h x y z w y
theorem Equation3858_implies_Equation3843 (G : Type*) [Magma G] (h : Equation3858 G) : Equation3843 G := λ x y z w => h x y z w y
theorem Equation3859_implies_Equation3844 (G : Type*) [Magma G] (h : Equation3859 G) : Equation3844 G := λ x y z w => h x y z w y
theorem Equation3860_implies_Equation3842 (G : Type*) [Magma G] (h : Equation3860 G) : Equation3842 G := λ x y z w => h x y z w y
theorem Equation3913_implies_Equation3910 (G : Type*) [Magma G] (h : Equation3913 G) : Equation3910 G := λ x y z w => h x y z w y
theorem Equation3950_implies_Equation3947 (G : Type*) [Magma G] (h : Equation3950 G) : Equation3947 G := λ x y z w => h x y z w y
theorem Equation3987_implies_Equation3984 (G : Type*) [Magma G] (h : Equation3987 G) : Equation3984 G := λ x y z w => h x y z w y
theorem Equation4004_implies_Equation4001 (G : Type*) [Magma G] (h : Equation4004 G) : Equation4001 G := λ x y z w => h x y z w y
theorem Equation4021_implies_Equation4018 (G : Type*) [Magma G] (h : Equation4021 G) : Equation4018 G := λ x y z w => h x y z w y
theorem Equation4038_implies_Equation4035 (G : Type*) [Magma G] (h : Equation4038 G) : Equation4035 G := λ x y z w => h x y z w y
theorem Equation4043_implies_Equation4040 (G : Type*) [Magma G] (h : Equation4043 G) : Equation4040 G := λ x y z w => h x y z w y
theorem Equation4048_implies_Equation4045 (G : Type*) [Magma G] (h : Equation4048 G) : Equation4045 G := λ x y z w => h x y z w y
theorem Equation4053_implies_Equation4050 (G : Type*) [Magma G] (h : Equation4053 G) : Equation4050 G := λ x y z w => h x y z w y
theorem Equation4058_implies_Equation4055 (G : Type*) [Magma G] (h : Equation4058 G) : Equation4055 G := λ x y z w => h x y z w y
theorem Equation4059_implies_Equation4044 (G : Type*) [Magma G] (h : Equation4059 G) : Equation4044 G := λ x y z w => h x y z w y
theorem Equation4060_implies_Equation4045 (G : Type*) [Magma G] (h : Equation4060 G) : Equation4045 G := λ x y z w => h x y z w y
theorem Equation4061_implies_Equation4046 (G : Type*) [Magma G] (h : Equation4061 G) : Equation4046 G := λ x y z w => h x y z w y
theorem Equation4062_implies_Equation4047 (G : Type*) [Magma G] (h : Equation4062 G) : Equation4047 G := λ x y z w => h x y z w y
theorem Equation4063_implies_Equation4045 (G : Type*) [Magma G] (h : Equation4063 G) : Equation4045 G := λ x y z w => h x y z w y
theorem Equation4116_implies_Equation4113 (G : Type*) [Magma G] (h : Equation4116 G) : Equation4113 G := λ x y z w => h x y z w y
theorem Equation4153_implies_Equation4150 (G : Type*) [Magma G] (h : Equation4153 G) : Equation4150 G := λ x y z w => h x y z w y
theorem Equation4190_implies_Equation4187 (G : Type*) [Magma G] (h : Equation4190 G) : Equation4187 G := λ x y z w => h x y z w y
theorem Equation4207_implies_Equation4204 (G : Type*) [Magma G] (h : Equation4207 G) : Equation4204 G := λ x y z w => h x y z w y
theorem Equation4224_implies_Equation4221 (G : Type*) [Magma G] (h : Equation4224 G) : Equation4221 G := λ x y z w => h x y z w y
theorem Equation4241_implies_Equation4238 (G : Type*) [Magma G] (h : Equation4241 G) : Equation4238 G := λ x y z w => h x y z w y
theorem Equation4246_implies_Equation4243 (G : Type*) [Magma G] (h : Equation4246 G) : Equation4243 G := λ x y z w => h x y z w y
theorem Equation4251_implies_Equation4248 (G : Type*) [Magma G] (h : Equation4251 G) : Equation4248 G := λ x y z w => h x y z w y
theorem Equation4256_implies_Equation4253 (G : Type*) [Magma G] (h : Equation4256 G) : Equation4253 G := λ x y z w => h x y z w y
theorem Equation4261_implies_Equation4258 (G : Type*) [Magma G] (h : Equation4261 G) : Equation4258 G := λ x y z w => h x y z w y
theorem Equation4262_implies_Equation4247 (G : Type*) [Magma G] (h : Equation4262 G) : Equation4247 G := λ x y z w => h x y z w y
theorem Equation4263_implies_Equation4248 (G : Type*) [Magma G] (h : Equation4263 G) : Equation4248 G := λ x y z w => h x y z w y
theorem Equation4264_implies_Equation4249 (G : Type*) [Magma G] (h : Equation4264 G) : Equation4249 G := λ x y z w => h x y z w y
theorem Equation4265_implies_Equation4250 (G : Type*) [Magma G] (h : Equation4265 G) : Equation4250 G := λ x y z w => h x y z w y
theorem Equation4266_implies_Equation4248 (G : Type*) [Magma G] (h : Equation4266 G) : Equation4248 G := λ x y z w => h x y z w y
theorem Equation4313_implies_Equation4310 (G : Type*) [Magma G] (h : Equation4313 G) : Equation4310 G := λ x y z w => h x y z w y
theorem Equation4338_implies_Equation4335 (G : Type*) [Magma G] (h : Equation4338 G) : Equation4335 G := λ x y z w => h x y z w y
theorem Equation4356_implies_Equation4354 (G : Type*) [Magma G] (h : Equation4356 G) : Equation4354 G := λ x y z w => h x y z w y
theorem Equation4373_implies_Equation4372 (G : Type*) [Magma G] (h : Equation4373 G) : Equation4372 G := λ x y z w => h x y z w y
theorem Equation4377_implies_Equation4376 (G : Type*) [Magma G] (h : Equation4377 G) : Equation4376 G := λ x y z w => h x y z w y
theorem Equation4378_implies_Equation4374 (G : Type*) [Magma G] (h : Equation4378 G) : Equation4374 G := λ x y z w => h x y z w y
theorem Equation4431_implies_Equation4428 (G : Type*) [Magma G] (h : Equation4431 G) : Equation4428 G := λ x y z w => h x y z w y
theorem Equation4468_implies_Equation4465 (G : Type*) [Magma G] (h : Equation4468 G) : Equation4465 G := λ x y z w => h x y z w y
theorem Equation4505_implies_Equation4502 (G : Type*) [Magma G] (h : Equation4505 G) : Equation4502 G := λ x y z w => h x y z w y
theorem Equation4522_implies_Equation4519 (G : Type*) [Magma G] (h : Equation4522 G) : Equation4519 G := λ x y z w => h x y z w y
theorem Equation4539_implies_Equation4536 (G : Type*) [Magma G] (h : Equation4539 G) : Equation4536 G := λ x y z w => h x y z w y
theorem Equation4556_implies_Equation4553 (G : Type*) [Magma G] (h : Equation4556 G) : Equation4553 G := λ x y z w => h x y z w y
theorem Equation4561_implies_Equation4558 (G : Type*) [Magma G] (h : Equation4561 G) : Equation4558 G := λ x y z w => h x y z w y
theorem Equation4566_implies_Equation4563 (G : Type*) [Magma G] (h : Equation4566 G) : Equation4563 G := λ x y z w => h x y z w y
theorem Equation4571_implies_Equation4568 (G : Type*) [Magma G] (h : Equation4571 G) : Equation4568 G := λ x y z w => h x y z w y
theorem Equation4576_implies_Equation4573 (G : Type*) [Magma G] (h : Equation4576 G) : Equation4573 G := λ x y z w => h x y z w y
theorem Equation4577_implies_Equation4562 (G : Type*) [Magma G] (h : Equation4577 G) : Equation4562 G := λ x y z w => h x y z w y
theorem Equation4578_implies_Equation4563 (G : Type*) [Magma G] (h : Equation4578 G) : Equation4563 G := λ x y z w => h x y z w y
theorem Equation4579_implies_Equation4564 (G : Type*) [Magma G] (h : Equation4579 G) : Equation4564 G := λ x y z w => h x y z w y
theorem Equation4580_implies_Equation4565 (G : Type*) [Magma G] (h : Equation4580 G) : Equation4565 G := λ x y z w => h x y z w y
theorem Equation4581_implies_Equation4563 (G : Type*) [Magma G] (h : Equation4581 G) : Equation4563 G := λ x y z w => h x y z w y
theorem Equation4628_implies_Equation4625 (G : Type*) [Magma G] (h : Equation4628 G) : Equation4625 G := λ x y z w => h x y z w y
theorem Equation4653_implies_Equation4650 (G : Type*) [Magma G] (h : Equation4653 G) : Equation4650 G := λ x y z w => h x y z w y
theorem Equation4671_implies_Equation4669 (G : Type*) [Magma G] (h : Equation4671 G) : Equation4669 G := λ x y z w => h x y z w y
theorem Equation4688_implies_Equation4687 (G : Type*) [Magma G] (h : Equation4688 G) : Equation4687 G := λ x y z w => h x y z w y
theorem Equation4692_implies_Equation4691 (G : Type*) [Magma G] (h : Equation4692 G) : Equation4691 G := λ x y z w => h x y z w y
theorem Equation4693_implies_Equation4689 (G : Type*) [Magma G] (h : Equation4693 G) : Equation4689 G := λ x y z w => h x y z w y