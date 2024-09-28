import equational_theories.Magma
import equational_theories.Equations

/-! List of equational laws being studied -/

/-
This files contains a small list of selected Equations. This way this file can be conveniently
viewed and edited, without having to open a very large files.

See `AllEquations.lean` for the remaining ones. Feel free to move individual equations here if
you do manual proofs about them and you want to import just this file.

The equations are marked as `abbrev` so that tactics like `decide` will look through the definition.
-/

universe u


-- abbrev Equation1 (G: Type u) [Magma G] := ∀ x : G, x = x
-- abbrev Equation2 (G: Type u) [Magma G] := ∀ x y : G, x = y
-- abbrev Equation3 (G: Type u) [Magma G] := ∀ x : G, x = x ∘ x
-- abbrev Equation4 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ y
-- abbrev Equation5 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ x
-- abbrev Equation6 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ y
-- abbrev Equation7 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ z
-- abbrev Equation8 (G: Type u) [Magma G] := ∀ x : G, x = x ∘ (x ∘ x)
abbrev Equation9 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ y)
abbrev Equation10 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ x)
abbrev Equation11 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ y)
abbrev Equation12 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ z)
abbrev Equation13 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ x)
abbrev Equation14 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ y)
abbrev Equation15 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ z)
abbrev Equation16 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ x)
abbrev Equation17 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ y)
abbrev Equation18 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ z)
abbrev Equation19 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ x)
abbrev Equation20 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ y)
abbrev Equation21 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ z)
abbrev Equation22 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ w)
abbrev Equation23 (G: Type u) [Magma G] := ∀ x : G, x = (x ∘ x) ∘ x
abbrev Equation24 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ y
abbrev Equation25 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ x
abbrev Equation26 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ y
abbrev Equation27 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ z
abbrev Equation28 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ x
abbrev Equation29 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ y
abbrev Equation30 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ z
abbrev Equation31 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ x
abbrev Equation32 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ y
abbrev Equation33 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ z
abbrev Equation34 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ x
abbrev Equation35 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ y
abbrev Equation36 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ z
abbrev Equation37 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ w
-- abbrev Equation38 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = x ∘ y
-- abbrev Equation39 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = y ∘ x
-- abbrev Equation40 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = y ∘ y
-- abbrev Equation41 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ z
-- abbrev Equation42 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ z
-- abbrev Equation43 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = y ∘ x
abbrev Equation44 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ z
abbrev Equation45 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ y
-- abbrev Equation46 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ w
abbrev Equation47 (G: Type u) [Magma G] := ∀ x : G, x = x ∘ (x ∘ (x ∘ x))
abbrev Equation48 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (x ∘ y))
abbrev Equation49 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (y ∘ x))
abbrev Equation50 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (y ∘ y))
abbrev Equation51 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ (y ∘ z))
abbrev Equation52 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (x ∘ x))
abbrev Equation53 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (x ∘ y))
abbrev Equation54 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (x ∘ z))
abbrev Equation55 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (y ∘ x))
abbrev Equation56 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (y ∘ y))
abbrev Equation57 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (y ∘ z))
abbrev Equation58 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ x))
abbrev Equation59 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ y))
abbrev Equation60 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ z))
abbrev Equation61 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ w))
abbrev Equation62 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (x ∘ x))
abbrev Equation63 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (x ∘ y))
abbrev Equation64 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (x ∘ z))
abbrev Equation65 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (y ∘ x))
abbrev Equation66 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (y ∘ y))
abbrev Equation67 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (y ∘ z))
abbrev Equation68 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ x))
abbrev Equation69 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ y))
abbrev Equation70 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ z))
abbrev Equation71 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ w))
abbrev Equation72 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (x ∘ x))
abbrev Equation73 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (x ∘ y))
abbrev Equation74 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (x ∘ z))
abbrev Equation75 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (y ∘ x))
abbrev Equation76 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (y ∘ y))
abbrev Equation77 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (y ∘ z))
abbrev Equation78 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ x))
abbrev Equation79 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ y))
abbrev Equation80 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ z))
abbrev Equation81 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ w))
abbrev Equation82 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ x))
abbrev Equation83 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ y))
abbrev Equation84 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ z))
abbrev Equation85 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ w))
abbrev Equation86 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ x))
abbrev Equation87 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ y))
abbrev Equation88 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ z))
abbrev Equation89 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ w))
abbrev Equation90 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ x))
abbrev Equation91 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ y))
abbrev Equation92 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ z))
abbrev Equation93 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ w))
abbrev Equation94 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ x))
abbrev Equation95 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ y))
abbrev Equation96 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ z))
abbrev Equation97 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ w))
abbrev Equation98 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ u))
abbrev Equation99 (G: Type u) [Magma G] := ∀ x : G, x = x ∘ ((x ∘ x) ∘ x)
abbrev Equation100 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ x) ∘ y)
abbrev Equation101 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ y) ∘ x)
abbrev Equation102 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ y) ∘ y)
abbrev Equation103 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ y) ∘ z)
abbrev Equation104 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ x) ∘ x)
abbrev Equation105 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ x) ∘ y)
abbrev Equation106 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ x) ∘ z)
abbrev Equation107 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ y) ∘ x)
abbrev Equation108 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ y) ∘ y)
abbrev Equation109 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ y) ∘ z)
abbrev Equation110 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ x)
abbrev Equation111 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ y)
abbrev Equation112 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ z)
abbrev Equation113 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ w)
abbrev Equation114 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ x) ∘ x)
abbrev Equation115 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ x) ∘ y)
abbrev Equation116 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ x) ∘ z)
abbrev Equation117 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ y) ∘ x)
abbrev Equation118 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ y) ∘ y)
abbrev Equation119 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ y) ∘ z)
abbrev Equation120 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ x)
abbrev Equation121 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ y)
abbrev Equation122 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ z)
abbrev Equation123 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ w)
abbrev Equation124 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ x) ∘ x)
abbrev Equation125 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ x) ∘ y)
abbrev Equation126 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ x) ∘ z)
abbrev Equation127 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ y) ∘ x)
abbrev Equation128 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ y) ∘ y)
abbrev Equation129 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ y) ∘ z)
abbrev Equation130 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ x)
abbrev Equation131 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ y)
abbrev Equation132 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ z)
abbrev Equation133 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ w)
abbrev Equation134 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ x)
abbrev Equation135 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ y)
abbrev Equation136 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ z)
abbrev Equation137 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ w)
abbrev Equation138 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ x)
abbrev Equation139 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ y)
abbrev Equation140 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ z)
abbrev Equation141 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ w)
abbrev Equation142 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ x)
abbrev Equation143 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ y)
abbrev Equation144 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ z)
abbrev Equation145 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ w)
abbrev Equation146 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ x)
abbrev Equation147 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ y)
abbrev Equation148 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ z)
abbrev Equation149 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ w)
abbrev Equation150 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ u)
abbrev Equation151 (G: Type u) [Magma G] := ∀ x : G, x = (x ∘ x) ∘ (x ∘ x)
abbrev Equation152 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ (x ∘ y)
abbrev Equation153 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ (y ∘ x)
abbrev Equation154 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ (y ∘ y)
abbrev Equation155 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ (y ∘ z)
abbrev Equation156 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (x ∘ x)
abbrev Equation157 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (x ∘ y)
abbrev Equation158 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (x ∘ z)
abbrev Equation159 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (y ∘ x)
abbrev Equation160 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (y ∘ y)
abbrev Equation161 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (y ∘ z)
abbrev Equation162 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ x)
abbrev Equation163 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ y)
abbrev Equation164 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ z)
abbrev Equation165 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ w)
abbrev Equation166 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (x ∘ x)
abbrev Equation167 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (x ∘ y)
-- abbrev Equation168 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (x ∘ z)
abbrev Equation169 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (y ∘ x)
abbrev Equation170 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (y ∘ y)
abbrev Equation171 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (y ∘ z)
abbrev Equation172 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ x)
abbrev Equation173 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ y)
abbrev Equation174 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ z)
abbrev Equation175 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ w)
abbrev Equation176 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (x ∘ x)
abbrev Equation177 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (x ∘ y)
abbrev Equation178 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (x ∘ z)
abbrev Equation179 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (y ∘ x)
abbrev Equation180 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (y ∘ y)
abbrev Equation181 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (y ∘ z)
abbrev Equation182 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ x)
abbrev Equation183 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ y)
abbrev Equation184 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ z)
abbrev Equation185 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ w)
abbrev Equation186 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ x)
abbrev Equation187 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ y)
abbrev Equation188 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ z)
abbrev Equation189 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ w)
abbrev Equation190 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ x)
abbrev Equation191 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ y)
abbrev Equation192 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ z)
abbrev Equation193 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ w)
abbrev Equation194 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ x)
abbrev Equation195 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ y)
abbrev Equation196 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ z)
abbrev Equation197 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ w)
abbrev Equation198 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ x)
abbrev Equation199 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ y)
abbrev Equation200 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ z)
abbrev Equation201 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ w)
abbrev Equation202 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ u)
abbrev Equation203 (G: Type u) [Magma G] := ∀ x : G, x = (x ∘ (x ∘ x)) ∘ x
abbrev Equation204 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ x)) ∘ y
abbrev Equation205 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ y)) ∘ x
abbrev Equation206 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ y)) ∘ y
abbrev Equation207 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ y)) ∘ z
abbrev Equation208 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ x)) ∘ x
abbrev Equation209 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ x)) ∘ y
abbrev Equation210 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ x)) ∘ z
abbrev Equation211 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ y)) ∘ x
abbrev Equation212 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ y)) ∘ y
abbrev Equation213 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ y)) ∘ z
abbrev Equation214 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ x
abbrev Equation215 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ y
abbrev Equation216 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ z
abbrev Equation217 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ w
abbrev Equation218 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ x)) ∘ x
abbrev Equation219 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ x)) ∘ y
abbrev Equation220 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ x)) ∘ z
abbrev Equation221 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ y)) ∘ x
abbrev Equation222 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ y)) ∘ y
abbrev Equation223 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ y)) ∘ z
abbrev Equation224 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ x
abbrev Equation225 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ y
abbrev Equation226 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ z
abbrev Equation227 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ w
abbrev Equation228 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ x)) ∘ x
abbrev Equation229 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ x)) ∘ y
abbrev Equation230 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ x)) ∘ z
abbrev Equation231 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ y)) ∘ x
abbrev Equation232 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ y)) ∘ y
abbrev Equation233 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ y)) ∘ z
abbrev Equation234 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ x
abbrev Equation235 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ y
abbrev Equation236 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ z
abbrev Equation237 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ w
abbrev Equation238 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ x
abbrev Equation239 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ y
abbrev Equation240 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ z
abbrev Equation241 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ w
abbrev Equation242 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ x
abbrev Equation243 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ y
abbrev Equation244 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ z
abbrev Equation245 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ w
abbrev Equation246 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ x
abbrev Equation247 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ y
abbrev Equation248 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ z
abbrev Equation249 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ w
abbrev Equation250 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ x
abbrev Equation251 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ y
abbrev Equation252 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ z
abbrev Equation253 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ w
abbrev Equation254 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ u
abbrev Equation255 (G: Type u) [Magma G] := ∀ x : G, x = ((x ∘ x) ∘ x) ∘ x
abbrev Equation256 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ x) ∘ y
abbrev Equation257 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ y) ∘ x
abbrev Equation258 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ y) ∘ y
abbrev Equation259 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ y) ∘ z
abbrev Equation260 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ x) ∘ x
abbrev Equation261 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ x) ∘ y
abbrev Equation262 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ x) ∘ z
abbrev Equation263 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ y) ∘ x
abbrev Equation264 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ y) ∘ y
abbrev Equation265 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ y) ∘ z
abbrev Equation266 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ x
abbrev Equation267 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ y
abbrev Equation268 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ z
abbrev Equation269 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ w
abbrev Equation270 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ x) ∘ x
abbrev Equation271 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ x) ∘ y
abbrev Equation272 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ x) ∘ z
abbrev Equation273 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ y) ∘ x
abbrev Equation274 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ y) ∘ y
abbrev Equation275 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ y) ∘ z
abbrev Equation276 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ x
abbrev Equation277 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ y
abbrev Equation278 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ z
abbrev Equation279 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ w
abbrev Equation280 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ x) ∘ x
abbrev Equation281 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ x) ∘ y
abbrev Equation282 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ x) ∘ z
abbrev Equation283 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ y) ∘ x
abbrev Equation284 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ y) ∘ y
abbrev Equation285 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ y) ∘ z
abbrev Equation286 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ x
abbrev Equation287 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ y
abbrev Equation288 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ z
abbrev Equation289 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ w
abbrev Equation290 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ x
abbrev Equation291 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ y
abbrev Equation292 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ z
abbrev Equation293 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ w
abbrev Equation294 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ x
abbrev Equation295 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ y
abbrev Equation296 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ z
abbrev Equation297 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ w
abbrev Equation298 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ x
abbrev Equation299 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ y
abbrev Equation300 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ z
abbrev Equation301 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ w
abbrev Equation302 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ x
abbrev Equation303 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ y
abbrev Equation304 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ z
abbrev Equation305 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ w
abbrev Equation306 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ u
abbrev Equation307 (G: Type u) [Magma G] := ∀ x : G, x ∘ x = x ∘ (x ∘ x)
abbrev Equation308 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = x ∘ (x ∘ y)
abbrev Equation309 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = x ∘ (y ∘ x)
abbrev Equation310 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = x ∘ (y ∘ y)
abbrev Equation311 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ (y ∘ z)
abbrev Equation312 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (x ∘ x)
abbrev Equation313 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (x ∘ y)
abbrev Equation314 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (x ∘ z)
abbrev Equation315 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (y ∘ x)
abbrev Equation316 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (y ∘ y)
abbrev Equation317 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (y ∘ z)
abbrev Equation318 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ x)
abbrev Equation319 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ y)
abbrev Equation320 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ z)
abbrev Equation321 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ w)
abbrev Equation322 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (x ∘ x)
abbrev Equation323 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (x ∘ y)
abbrev Equation324 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (x ∘ z)
abbrev Equation325 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (y ∘ x)
abbrev Equation326 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (y ∘ y)
abbrev Equation327 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (y ∘ z)
abbrev Equation328 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ x)
abbrev Equation329 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ y)
abbrev Equation330 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ z)
abbrev Equation331 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ w)
abbrev Equation332 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (x ∘ x)
abbrev Equation333 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (x ∘ y)
abbrev Equation334 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (x ∘ z)
abbrev Equation335 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (y ∘ x)
abbrev Equation336 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (y ∘ y)
abbrev Equation337 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (y ∘ z)
abbrev Equation338 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ x)
abbrev Equation339 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ y)
abbrev Equation340 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ z)
abbrev Equation341 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ w)
abbrev Equation342 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ x)
abbrev Equation343 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ y)
abbrev Equation344 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ z)
abbrev Equation345 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ w)
abbrev Equation346 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ x)
abbrev Equation347 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ y)
abbrev Equation348 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ z)
abbrev Equation349 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ w)
abbrev Equation350 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ x)
abbrev Equation351 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ y)
abbrev Equation352 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ z)
abbrev Equation353 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ w)
abbrev Equation354 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ x)
abbrev Equation355 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ y)
abbrev Equation356 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ z)
abbrev Equation357 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ w)
abbrev Equation358 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ u)
abbrev Equation359 (G: Type u) [Magma G] := ∀ x : G, x ∘ x = (x ∘ x) ∘ x
abbrev Equation360 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ x) ∘ y
abbrev Equation361 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ y) ∘ x
abbrev Equation362 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ y) ∘ y
abbrev Equation363 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ y) ∘ z
abbrev Equation364 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ x) ∘ x
abbrev Equation365 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ x) ∘ y
abbrev Equation366 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ x) ∘ z
abbrev Equation367 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ y) ∘ x
abbrev Equation368 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ y) ∘ y
abbrev Equation369 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ y) ∘ z
abbrev Equation370 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ x
abbrev Equation371 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ y
abbrev Equation372 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ z
abbrev Equation373 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ w
abbrev Equation374 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ x) ∘ x
abbrev Equation375 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ x) ∘ y
abbrev Equation376 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ x) ∘ z
abbrev Equation377 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ y) ∘ x
abbrev Equation378 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ y) ∘ y
abbrev Equation379 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ y) ∘ z
abbrev Equation380 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ x
abbrev Equation381 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ y
abbrev Equation382 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ z
abbrev Equation383 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ w
abbrev Equation384 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ x) ∘ x
abbrev Equation385 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ x) ∘ y
abbrev Equation386 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ x) ∘ z
-- abbrev Equation387 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ y) ∘ x
abbrev Equation388 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ y) ∘ y
abbrev Equation389 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ y) ∘ z
abbrev Equation390 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ x
abbrev Equation391 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ y
abbrev Equation392 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ z
abbrev Equation393 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ w
abbrev Equation394 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ x
abbrev Equation395 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ y
abbrev Equation396 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ z
abbrev Equation397 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ w
abbrev Equation398 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ x
abbrev Equation399 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ y
abbrev Equation400 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ z
abbrev Equation401 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ w
abbrev Equation402 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ x
abbrev Equation403 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ y
abbrev Equation404 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ z
abbrev Equation405 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ w
abbrev Equation406 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ x
abbrev Equation407 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ y
abbrev Equation408 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ z
abbrev Equation409 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ w
abbrev Equation410 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ u
abbrev Equation411 (G: Type u) [Magma G] := ∀ x : G, x = x ∘ (x ∘ (x ∘ (x ∘ x)))
abbrev Equation412 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (x ∘ (x ∘ y)))
abbrev Equation413 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (x ∘ (y ∘ x)))
abbrev Equation414 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (x ∘ (y ∘ y)))
abbrev Equation415 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ (x ∘ (y ∘ z)))
abbrev Equation416 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (y ∘ (x ∘ x)))
abbrev Equation417 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (y ∘ (x ∘ y)))
abbrev Equation418 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ (y ∘ (x ∘ z)))
abbrev Equation419 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (y ∘ (y ∘ x)))
abbrev Equation420 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ (y ∘ (y ∘ y)))
abbrev Equation421 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ (y ∘ (y ∘ z)))
abbrev Equation422 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ (y ∘ (z ∘ x)))
abbrev Equation423 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ (y ∘ (z ∘ y)))
abbrev Equation424 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ (y ∘ (z ∘ z)))
abbrev Equation425 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (x ∘ (y ∘ (z ∘ w)))
abbrev Equation426 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (x ∘ (x ∘ x)))
abbrev Equation427 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (x ∘ (x ∘ y)))
abbrev Equation428 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (x ∘ (x ∘ z)))
abbrev Equation429 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (x ∘ (y ∘ x)))
abbrev Equation430 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (x ∘ (y ∘ y)))
abbrev Equation431 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (x ∘ (y ∘ z)))
abbrev Equation432 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (x ∘ (z ∘ x)))
abbrev Equation433 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (x ∘ (z ∘ y)))
abbrev Equation434 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (x ∘ (z ∘ z)))
abbrev Equation435 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (x ∘ (z ∘ w)))
abbrev Equation436 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (y ∘ (x ∘ x)))
abbrev Equation437 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (y ∘ (x ∘ y)))
abbrev Equation438 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (y ∘ (x ∘ z)))
abbrev Equation439 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (y ∘ (y ∘ x)))
abbrev Equation440 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ (y ∘ (y ∘ y)))
abbrev Equation441 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (y ∘ (y ∘ z)))
abbrev Equation442 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (y ∘ (z ∘ x)))
abbrev Equation443 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (y ∘ (z ∘ y)))
abbrev Equation444 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (y ∘ (z ∘ z)))
abbrev Equation445 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (y ∘ (z ∘ w)))
abbrev Equation446 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ (x ∘ x)))
abbrev Equation447 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ (x ∘ y)))
abbrev Equation448 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ (x ∘ z)))
abbrev Equation449 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (x ∘ w)))
abbrev Equation450 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ (y ∘ x)))
abbrev Equation451 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ (y ∘ y)))
abbrev Equation452 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ (y ∘ z)))
abbrev Equation453 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (y ∘ w)))
abbrev Equation454 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ (z ∘ x)))
abbrev Equation455 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ (z ∘ y)))
abbrev Equation456 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ (z ∘ (z ∘ z)))
abbrev Equation457 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (z ∘ w)))
abbrev Equation458 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (w ∘ x)))
abbrev Equation459 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (w ∘ y)))
abbrev Equation460 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (w ∘ z)))
abbrev Equation461 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ (z ∘ (w ∘ w)))
abbrev Equation462 (G: Type u) [Magma G] := ∀ x y z w u : G, x = x ∘ (y ∘ (z ∘ (w ∘ u)))
abbrev Equation463 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (x ∘ (x ∘ x)))
abbrev Equation464 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (x ∘ (x ∘ y)))
abbrev Equation465 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (x ∘ (x ∘ z)))
abbrev Equation466 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (x ∘ (y ∘ x)))
abbrev Equation467 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (x ∘ (y ∘ y)))
abbrev Equation468 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (x ∘ (y ∘ z)))
abbrev Equation469 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (x ∘ (z ∘ x)))
abbrev Equation470 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (x ∘ (z ∘ y)))
abbrev Equation471 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (x ∘ (z ∘ z)))
abbrev Equation472 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (x ∘ (z ∘ w)))
abbrev Equation473 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (y ∘ (x ∘ x)))
abbrev Equation474 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (y ∘ (x ∘ y)))
abbrev Equation475 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (y ∘ (x ∘ z)))
abbrev Equation476 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (y ∘ (y ∘ x)))
abbrev Equation477 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ (y ∘ (y ∘ y)))
abbrev Equation478 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (y ∘ (y ∘ z)))
abbrev Equation479 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (y ∘ (z ∘ x)))
abbrev Equation480 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (y ∘ (z ∘ y)))
abbrev Equation481 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (y ∘ (z ∘ z)))
abbrev Equation482 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (y ∘ (z ∘ w)))
abbrev Equation483 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ (x ∘ x)))
abbrev Equation484 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ (x ∘ y)))
abbrev Equation485 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ (x ∘ z)))
abbrev Equation486 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (x ∘ w)))
abbrev Equation487 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ (y ∘ x)))
abbrev Equation488 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ (y ∘ y)))
abbrev Equation489 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ (y ∘ z)))
abbrev Equation490 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (y ∘ w)))
abbrev Equation491 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ (z ∘ x)))
abbrev Equation492 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ (z ∘ y)))
abbrev Equation493 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ (z ∘ (z ∘ z)))
abbrev Equation494 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (z ∘ w)))
abbrev Equation495 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (w ∘ x)))
abbrev Equation496 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (w ∘ y)))
abbrev Equation497 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (w ∘ z)))
abbrev Equation498 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ (z ∘ (w ∘ w)))
abbrev Equation499 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (x ∘ (z ∘ (w ∘ u)))
abbrev Equation500 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (x ∘ (x ∘ x)))
abbrev Equation501 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (x ∘ (x ∘ y)))
abbrev Equation502 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (x ∘ (x ∘ z)))
abbrev Equation503 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (x ∘ (y ∘ x)))
abbrev Equation504 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (x ∘ (y ∘ y)))
abbrev Equation505 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (x ∘ (y ∘ z)))
abbrev Equation506 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (x ∘ (z ∘ x)))
abbrev Equation507 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (x ∘ (z ∘ y)))
abbrev Equation508 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (x ∘ (z ∘ z)))
abbrev Equation509 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (x ∘ (z ∘ w)))
abbrev Equation510 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (y ∘ (x ∘ x)))
abbrev Equation511 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (y ∘ (x ∘ y)))
abbrev Equation512 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (y ∘ (x ∘ z)))
abbrev Equation513 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (y ∘ (y ∘ x)))
abbrev Equation514 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ (y ∘ (y ∘ y)))
abbrev Equation515 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (y ∘ (y ∘ z)))
abbrev Equation516 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (y ∘ (z ∘ x)))
abbrev Equation517 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (y ∘ (z ∘ y)))
abbrev Equation518 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (y ∘ (z ∘ z)))
abbrev Equation519 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (y ∘ (z ∘ w)))
abbrev Equation520 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ (x ∘ x)))
abbrev Equation521 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ (x ∘ y)))
abbrev Equation522 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ (x ∘ z)))
abbrev Equation523 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (x ∘ w)))
abbrev Equation524 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ (y ∘ x)))
abbrev Equation525 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ (y ∘ y)))
abbrev Equation526 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ (y ∘ z)))
abbrev Equation527 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (y ∘ w)))
abbrev Equation528 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ (z ∘ x)))
abbrev Equation529 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ (z ∘ y)))
abbrev Equation530 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ (z ∘ (z ∘ z)))
abbrev Equation531 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (z ∘ w)))
abbrev Equation532 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (w ∘ x)))
abbrev Equation533 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (w ∘ y)))
abbrev Equation534 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (w ∘ z)))
abbrev Equation535 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ (z ∘ (w ∘ w)))
abbrev Equation536 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (y ∘ (z ∘ (w ∘ u)))
abbrev Equation537 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ (x ∘ x)))
abbrev Equation538 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ (x ∘ y)))
abbrev Equation539 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ (x ∘ z)))
abbrev Equation540 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (x ∘ w)))
abbrev Equation541 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ (y ∘ x)))
abbrev Equation542 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ (y ∘ y)))
abbrev Equation543 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ (y ∘ z)))
abbrev Equation544 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (y ∘ w)))
abbrev Equation545 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ (z ∘ x)))
abbrev Equation546 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ (z ∘ y)))
abbrev Equation547 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (x ∘ (z ∘ z)))
abbrev Equation548 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (z ∘ w)))
abbrev Equation549 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (w ∘ x)))
abbrev Equation550 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (w ∘ y)))
abbrev Equation551 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (w ∘ z)))
abbrev Equation552 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (x ∘ (w ∘ w)))
abbrev Equation553 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (x ∘ (w ∘ u)))
abbrev Equation554 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ (x ∘ x)))
abbrev Equation555 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ (x ∘ y)))
abbrev Equation556 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ (x ∘ z)))
abbrev Equation557 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (x ∘ w)))
abbrev Equation558 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ (y ∘ x)))
abbrev Equation559 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ (y ∘ y)))
abbrev Equation560 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ (y ∘ z)))
abbrev Equation561 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (y ∘ w)))
abbrev Equation562 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ (z ∘ x)))
abbrev Equation563 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ (z ∘ y)))
abbrev Equation564 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (y ∘ (z ∘ z)))
abbrev Equation565 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (z ∘ w)))
abbrev Equation566 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (w ∘ x)))
abbrev Equation567 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (w ∘ y)))
abbrev Equation568 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (w ∘ z)))
abbrev Equation569 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (y ∘ (w ∘ w)))
abbrev Equation570 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (y ∘ (w ∘ u)))
abbrev Equation571 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (x ∘ x)))
abbrev Equation572 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (x ∘ y)))
abbrev Equation573 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (x ∘ z)))
abbrev Equation574 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (x ∘ w)))
abbrev Equation575 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (y ∘ x)))
abbrev Equation576 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (y ∘ y)))
abbrev Equation577 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (y ∘ z)))
abbrev Equation578 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (y ∘ w)))
abbrev Equation579 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (z ∘ x)))
abbrev Equation580 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (z ∘ y)))
abbrev Equation581 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ (z ∘ (z ∘ z)))
abbrev Equation582 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (z ∘ w)))
abbrev Equation583 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (w ∘ x)))
abbrev Equation584 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (w ∘ y)))
abbrev Equation585 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (w ∘ z)))
abbrev Equation586 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (z ∘ (w ∘ w)))
abbrev Equation587 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (z ∘ (w ∘ u)))
abbrev Equation588 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (x ∘ x)))
abbrev Equation589 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (x ∘ y)))
abbrev Equation590 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (x ∘ z)))
abbrev Equation591 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (x ∘ w)))
abbrev Equation592 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (x ∘ u)))
abbrev Equation593 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (y ∘ x)))
abbrev Equation594 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (y ∘ y)))
abbrev Equation595 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (y ∘ z)))
abbrev Equation596 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (y ∘ w)))
abbrev Equation597 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (y ∘ u)))
abbrev Equation598 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (z ∘ x)))
abbrev Equation599 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (z ∘ y)))
abbrev Equation600 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (z ∘ z)))
abbrev Equation601 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (z ∘ w)))
abbrev Equation602 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (z ∘ u)))
abbrev Equation603 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (w ∘ x)))
abbrev Equation604 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (w ∘ y)))
abbrev Equation605 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (w ∘ z)))
abbrev Equation606 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ (w ∘ (w ∘ w)))
abbrev Equation607 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (w ∘ u)))
abbrev Equation608 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (u ∘ x)))
abbrev Equation609 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (u ∘ y)))
abbrev Equation610 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (u ∘ z)))
abbrev Equation611 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (u ∘ w)))
abbrev Equation612 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ (w ∘ (u ∘ u)))
abbrev Equation613 (G: Type u) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ (w ∘ (u ∘ v)))
abbrev Equation614 (G: Type u) [Magma G] := ∀ x : G, x = x ∘ (x ∘ ((x ∘ x) ∘ x))
abbrev Equation615 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ ((x ∘ x) ∘ y))
abbrev Equation616 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ ((x ∘ y) ∘ x))
abbrev Equation617 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ ((x ∘ y) ∘ y))
abbrev Equation618 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ ((x ∘ y) ∘ z))
abbrev Equation619 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ ((y ∘ x) ∘ x))
abbrev Equation620 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ ((y ∘ x) ∘ y))
abbrev Equation621 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ ((y ∘ x) ∘ z))
abbrev Equation622 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ ((y ∘ y) ∘ x))
abbrev Equation623 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (x ∘ ((y ∘ y) ∘ y))
abbrev Equation624 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ ((y ∘ y) ∘ z))
abbrev Equation625 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ ((y ∘ z) ∘ x))
abbrev Equation626 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ ((y ∘ z) ∘ y))
abbrev Equation627 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (x ∘ ((y ∘ z) ∘ z))
abbrev Equation628 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (x ∘ ((y ∘ z) ∘ w))
abbrev Equation629 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ ((x ∘ x) ∘ x))
abbrev Equation630 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ ((x ∘ x) ∘ y))
abbrev Equation631 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((x ∘ x) ∘ z))
abbrev Equation632 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ ((x ∘ y) ∘ x))
abbrev Equation633 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ ((x ∘ y) ∘ y))
abbrev Equation634 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((x ∘ y) ∘ z))
abbrev Equation635 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((x ∘ z) ∘ x))
abbrev Equation636 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((x ∘ z) ∘ y))
abbrev Equation637 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((x ∘ z) ∘ z))
abbrev Equation638 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((x ∘ z) ∘ w))
abbrev Equation639 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ ((y ∘ x) ∘ x))
abbrev Equation640 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ ((y ∘ x) ∘ y))
abbrev Equation641 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((y ∘ x) ∘ z))
abbrev Equation642 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ ((y ∘ y) ∘ x))
abbrev Equation643 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (y ∘ ((y ∘ y) ∘ y))
abbrev Equation644 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((y ∘ y) ∘ z))
abbrev Equation645 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((y ∘ z) ∘ x))
abbrev Equation646 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((y ∘ z) ∘ y))
abbrev Equation647 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((y ∘ z) ∘ z))
abbrev Equation648 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((y ∘ z) ∘ w))
abbrev Equation649 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((z ∘ x) ∘ x))
abbrev Equation650 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((z ∘ x) ∘ y))
abbrev Equation651 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((z ∘ x) ∘ z))
abbrev Equation652 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ x) ∘ w))
abbrev Equation653 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((z ∘ y) ∘ x))
abbrev Equation654 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((z ∘ y) ∘ y))
abbrev Equation655 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((z ∘ y) ∘ z))
abbrev Equation656 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ y) ∘ w))
abbrev Equation657 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((z ∘ z) ∘ x))
abbrev Equation658 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((z ∘ z) ∘ y))
abbrev Equation659 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (y ∘ ((z ∘ z) ∘ z))
abbrev Equation660 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ z) ∘ w))
abbrev Equation661 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ w) ∘ x))
abbrev Equation662 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ w) ∘ y))
abbrev Equation663 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ w) ∘ z))
abbrev Equation664 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (y ∘ ((z ∘ w) ∘ w))
abbrev Equation665 (G: Type u) [Magma G] := ∀ x y z w u : G, x = x ∘ (y ∘ ((z ∘ w) ∘ u))
abbrev Equation666 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((x ∘ x) ∘ x))
abbrev Equation667 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((x ∘ x) ∘ y))
abbrev Equation668 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((x ∘ x) ∘ z))
abbrev Equation669 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((x ∘ y) ∘ x))
abbrev Equation670 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((x ∘ y) ∘ y))
abbrev Equation671 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((x ∘ y) ∘ z))
abbrev Equation672 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((x ∘ z) ∘ x))
abbrev Equation673 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((x ∘ z) ∘ y))
abbrev Equation674 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((x ∘ z) ∘ z))
abbrev Equation675 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((x ∘ z) ∘ w))
abbrev Equation676 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((y ∘ x) ∘ x))
abbrev Equation677 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((y ∘ x) ∘ y))
abbrev Equation678 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((y ∘ x) ∘ z))
abbrev Equation679 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((y ∘ y) ∘ x))
abbrev Equation680 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (x ∘ ((y ∘ y) ∘ y))
abbrev Equation681 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((y ∘ y) ∘ z))
abbrev Equation682 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((y ∘ z) ∘ x))
abbrev Equation683 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((y ∘ z) ∘ y))
abbrev Equation684 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((y ∘ z) ∘ z))
abbrev Equation685 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((y ∘ z) ∘ w))
abbrev Equation686 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((z ∘ x) ∘ x))
abbrev Equation687 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((z ∘ x) ∘ y))
abbrev Equation688 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((z ∘ x) ∘ z))
abbrev Equation689 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ x) ∘ w))
abbrev Equation690 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((z ∘ y) ∘ x))
abbrev Equation691 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((z ∘ y) ∘ y))
abbrev Equation692 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((z ∘ y) ∘ z))
abbrev Equation693 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ y) ∘ w))
abbrev Equation694 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((z ∘ z) ∘ x))
abbrev Equation695 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((z ∘ z) ∘ y))
abbrev Equation696 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (x ∘ ((z ∘ z) ∘ z))
abbrev Equation697 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ z) ∘ w))
abbrev Equation698 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ w) ∘ x))
abbrev Equation699 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ w) ∘ y))
abbrev Equation700 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ w) ∘ z))
abbrev Equation701 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (x ∘ ((z ∘ w) ∘ w))
abbrev Equation702 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (x ∘ ((z ∘ w) ∘ u))
abbrev Equation703 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ ((x ∘ x) ∘ x))
abbrev Equation704 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ ((x ∘ x) ∘ y))
abbrev Equation705 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((x ∘ x) ∘ z))
abbrev Equation706 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ ((x ∘ y) ∘ x))
abbrev Equation707 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ ((x ∘ y) ∘ y))
abbrev Equation708 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((x ∘ y) ∘ z))
abbrev Equation709 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((x ∘ z) ∘ x))
abbrev Equation710 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((x ∘ z) ∘ y))
abbrev Equation711 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((x ∘ z) ∘ z))
abbrev Equation712 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((x ∘ z) ∘ w))
abbrev Equation713 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ ((y ∘ x) ∘ x))
abbrev Equation714 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ ((y ∘ x) ∘ y))
abbrev Equation715 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((y ∘ x) ∘ z))
abbrev Equation716 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ ((y ∘ y) ∘ x))
abbrev Equation717 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (y ∘ ((y ∘ y) ∘ y))
abbrev Equation718 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((y ∘ y) ∘ z))
abbrev Equation719 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((y ∘ z) ∘ x))
abbrev Equation720 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((y ∘ z) ∘ y))
abbrev Equation721 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((y ∘ z) ∘ z))
abbrev Equation722 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((y ∘ z) ∘ w))
abbrev Equation723 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((z ∘ x) ∘ x))
abbrev Equation724 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((z ∘ x) ∘ y))
abbrev Equation725 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((z ∘ x) ∘ z))
abbrev Equation726 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ x) ∘ w))
abbrev Equation727 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((z ∘ y) ∘ x))
abbrev Equation728 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((z ∘ y) ∘ y))
abbrev Equation729 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((z ∘ y) ∘ z))
abbrev Equation730 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ y) ∘ w))
abbrev Equation731 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((z ∘ z) ∘ x))
abbrev Equation732 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((z ∘ z) ∘ y))
abbrev Equation733 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (y ∘ ((z ∘ z) ∘ z))
abbrev Equation734 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ z) ∘ w))
abbrev Equation735 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ w) ∘ x))
abbrev Equation736 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ w) ∘ y))
abbrev Equation737 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ w) ∘ z))
abbrev Equation738 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (y ∘ ((z ∘ w) ∘ w))
abbrev Equation739 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (y ∘ ((z ∘ w) ∘ u))
abbrev Equation740 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((x ∘ x) ∘ x))
abbrev Equation741 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((x ∘ x) ∘ y))
abbrev Equation742 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((x ∘ x) ∘ z))
abbrev Equation743 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ x) ∘ w))
abbrev Equation744 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((x ∘ y) ∘ x))
abbrev Equation745 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((x ∘ y) ∘ y))
abbrev Equation746 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((x ∘ y) ∘ z))
abbrev Equation747 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ y) ∘ w))
abbrev Equation748 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((x ∘ z) ∘ x))
abbrev Equation749 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((x ∘ z) ∘ y))
abbrev Equation750 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((x ∘ z) ∘ z))
abbrev Equation751 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ z) ∘ w))
abbrev Equation752 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ w) ∘ x))
abbrev Equation753 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ w) ∘ y))
abbrev Equation754 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ w) ∘ z))
abbrev Equation755 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((x ∘ w) ∘ w))
abbrev Equation756 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((x ∘ w) ∘ u))
abbrev Equation757 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((y ∘ x) ∘ x))
abbrev Equation758 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((y ∘ x) ∘ y))
abbrev Equation759 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((y ∘ x) ∘ z))
abbrev Equation760 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ x) ∘ w))
abbrev Equation761 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((y ∘ y) ∘ x))
abbrev Equation762 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((y ∘ y) ∘ y))
abbrev Equation763 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((y ∘ y) ∘ z))
abbrev Equation764 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ y) ∘ w))
abbrev Equation765 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((y ∘ z) ∘ x))
abbrev Equation766 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((y ∘ z) ∘ y))
abbrev Equation767 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((y ∘ z) ∘ z))
abbrev Equation768 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ z) ∘ w))
abbrev Equation769 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ w) ∘ x))
abbrev Equation770 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ w) ∘ y))
abbrev Equation771 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ w) ∘ z))
abbrev Equation772 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((y ∘ w) ∘ w))
abbrev Equation773 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((y ∘ w) ∘ u))
abbrev Equation774 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ x) ∘ x))
abbrev Equation775 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ x) ∘ y))
abbrev Equation776 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ x) ∘ z))
abbrev Equation777 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ x) ∘ w))
abbrev Equation778 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ y) ∘ x))
abbrev Equation779 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ y) ∘ y))
abbrev Equation780 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ y) ∘ z))
abbrev Equation781 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ y) ∘ w))
abbrev Equation782 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ z) ∘ x))
abbrev Equation783 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ z) ∘ y))
abbrev Equation784 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (z ∘ ((z ∘ z) ∘ z))
abbrev Equation785 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ z) ∘ w))
abbrev Equation786 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ w) ∘ x))
abbrev Equation787 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ w) ∘ y))
abbrev Equation788 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ w) ∘ z))
abbrev Equation789 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((z ∘ w) ∘ w))
abbrev Equation790 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((z ∘ w) ∘ u))
abbrev Equation791 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ x) ∘ x))
abbrev Equation792 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ x) ∘ y))
abbrev Equation793 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ x) ∘ z))
abbrev Equation794 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ x) ∘ w))
abbrev Equation795 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ x) ∘ u))
abbrev Equation796 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ y) ∘ x))
abbrev Equation797 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ y) ∘ y))
abbrev Equation798 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ y) ∘ z))
abbrev Equation799 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ y) ∘ w))
abbrev Equation800 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ y) ∘ u))
abbrev Equation801 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ z) ∘ x))
abbrev Equation802 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ z) ∘ y))
abbrev Equation803 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ z) ∘ z))
abbrev Equation804 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ z) ∘ w))
abbrev Equation805 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ z) ∘ u))
abbrev Equation806 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ w) ∘ x))
abbrev Equation807 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ w) ∘ y))
abbrev Equation808 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ w) ∘ z))
abbrev Equation809 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (z ∘ ((w ∘ w) ∘ w))
abbrev Equation810 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ w) ∘ u))
abbrev Equation811 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ u) ∘ x))
abbrev Equation812 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ u) ∘ y))
abbrev Equation813 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ u) ∘ z))
abbrev Equation814 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ u) ∘ w))
abbrev Equation815 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (z ∘ ((w ∘ u) ∘ u))
abbrev Equation816 (G: Type u) [Magma G] := ∀ x y z w u v : G, x = y ∘ (z ∘ ((w ∘ u) ∘ v))
abbrev Equation817 (G: Type u) [Magma G] := ∀ x : G, x = x ∘ ((x ∘ x) ∘ (x ∘ x))
abbrev Equation818 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ x) ∘ (x ∘ y))
abbrev Equation819 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ x) ∘ (y ∘ x))
abbrev Equation820 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ x) ∘ (y ∘ y))
abbrev Equation821 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ x) ∘ (y ∘ z))
abbrev Equation822 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ y) ∘ (x ∘ x))
abbrev Equation823 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ y) ∘ (x ∘ y))
abbrev Equation824 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ y) ∘ (x ∘ z))
abbrev Equation825 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ y) ∘ (y ∘ x))
abbrev Equation826 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ y) ∘ (y ∘ y))
abbrev Equation827 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ y) ∘ (y ∘ z))
abbrev Equation828 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ y) ∘ (z ∘ x))
abbrev Equation829 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ y) ∘ (z ∘ y))
abbrev Equation830 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ y) ∘ (z ∘ z))
abbrev Equation831 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ ((x ∘ y) ∘ (z ∘ w))
abbrev Equation832 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ x) ∘ (x ∘ x))
abbrev Equation833 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ x) ∘ (x ∘ y))
abbrev Equation834 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ x) ∘ (x ∘ z))
abbrev Equation835 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ x) ∘ (y ∘ x))
abbrev Equation836 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ x) ∘ (y ∘ y))
abbrev Equation837 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ x) ∘ (y ∘ z))
abbrev Equation838 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ x) ∘ (z ∘ x))
abbrev Equation839 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ x) ∘ (z ∘ y))
abbrev Equation840 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ x) ∘ (z ∘ z))
abbrev Equation841 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ x) ∘ (z ∘ w))
abbrev Equation842 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ y) ∘ (x ∘ x))
abbrev Equation843 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ y) ∘ (x ∘ y))
abbrev Equation844 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ y) ∘ (x ∘ z))
abbrev Equation845 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ y) ∘ (y ∘ x))
abbrev Equation846 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ y) ∘ (y ∘ y))
abbrev Equation847 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ y) ∘ (y ∘ z))
abbrev Equation848 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ y) ∘ (z ∘ x))
abbrev Equation849 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ y) ∘ (z ∘ y))
abbrev Equation850 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ y) ∘ (z ∘ z))
abbrev Equation851 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ y) ∘ (z ∘ w))
abbrev Equation852 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ (x ∘ x))
abbrev Equation853 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ (x ∘ y))
abbrev Equation854 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ (x ∘ z))
abbrev Equation855 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (x ∘ w))
abbrev Equation856 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ (y ∘ x))
abbrev Equation857 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ (y ∘ y))
abbrev Equation858 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ (y ∘ z))
abbrev Equation859 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (y ∘ w))
abbrev Equation860 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ (z ∘ x))
abbrev Equation861 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ (z ∘ y))
abbrev Equation862 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ z) ∘ (z ∘ z))
abbrev Equation863 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (z ∘ w))
abbrev Equation864 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (w ∘ x))
abbrev Equation865 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (w ∘ y))
abbrev Equation866 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (w ∘ z))
abbrev Equation867 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ z) ∘ (w ∘ w))
abbrev Equation868 (G: Type u) [Magma G] := ∀ x y z w u : G, x = x ∘ ((y ∘ z) ∘ (w ∘ u))
abbrev Equation869 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ x) ∘ (x ∘ x))
abbrev Equation870 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ x) ∘ (x ∘ y))
abbrev Equation871 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ x) ∘ (x ∘ z))
abbrev Equation872 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ x) ∘ (y ∘ x))
abbrev Equation873 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ x) ∘ (y ∘ y))
abbrev Equation874 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ x) ∘ (y ∘ z))
abbrev Equation875 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ x) ∘ (z ∘ x))
abbrev Equation876 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ x) ∘ (z ∘ y))
abbrev Equation877 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ x) ∘ (z ∘ z))
abbrev Equation878 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ x) ∘ (z ∘ w))
abbrev Equation879 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ y) ∘ (x ∘ x))
abbrev Equation880 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ y) ∘ (x ∘ y))
abbrev Equation881 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ y) ∘ (x ∘ z))
abbrev Equation882 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ y) ∘ (y ∘ x))
abbrev Equation883 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ y) ∘ (y ∘ y))
abbrev Equation884 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ y) ∘ (y ∘ z))
abbrev Equation885 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ y) ∘ (z ∘ x))
abbrev Equation886 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ y) ∘ (z ∘ y))
abbrev Equation887 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ y) ∘ (z ∘ z))
abbrev Equation888 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ y) ∘ (z ∘ w))
abbrev Equation889 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ (x ∘ x))
abbrev Equation890 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ (x ∘ y))
abbrev Equation891 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ (x ∘ z))
abbrev Equation892 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (x ∘ w))
abbrev Equation893 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ (y ∘ x))
abbrev Equation894 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ (y ∘ y))
abbrev Equation895 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ (y ∘ z))
abbrev Equation896 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (y ∘ w))
abbrev Equation897 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ (z ∘ x))
abbrev Equation898 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ (z ∘ y))
abbrev Equation899 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ z) ∘ (z ∘ z))
abbrev Equation900 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (z ∘ w))
abbrev Equation901 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (w ∘ x))
abbrev Equation902 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (w ∘ y))
abbrev Equation903 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (w ∘ z))
abbrev Equation904 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ z) ∘ (w ∘ w))
abbrev Equation905 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((x ∘ z) ∘ (w ∘ u))
abbrev Equation906 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ x) ∘ (x ∘ x))
abbrev Equation907 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ x) ∘ (x ∘ y))
abbrev Equation908 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ x) ∘ (x ∘ z))
abbrev Equation909 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ x) ∘ (y ∘ x))
abbrev Equation910 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ x) ∘ (y ∘ y))
abbrev Equation911 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ x) ∘ (y ∘ z))
abbrev Equation912 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ x) ∘ (z ∘ x))
abbrev Equation913 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ x) ∘ (z ∘ y))
abbrev Equation914 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ x) ∘ (z ∘ z))
abbrev Equation915 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ x) ∘ (z ∘ w))
abbrev Equation916 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ y) ∘ (x ∘ x))
abbrev Equation917 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ y) ∘ (x ∘ y))
abbrev Equation918 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ y) ∘ (x ∘ z))
abbrev Equation919 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ y) ∘ (y ∘ x))
abbrev Equation920 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ y) ∘ (y ∘ y))
abbrev Equation921 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ y) ∘ (y ∘ z))
abbrev Equation922 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ y) ∘ (z ∘ x))
abbrev Equation923 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ y) ∘ (z ∘ y))
abbrev Equation924 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ y) ∘ (z ∘ z))
abbrev Equation925 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ y) ∘ (z ∘ w))
abbrev Equation926 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ (x ∘ x))
abbrev Equation927 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ (x ∘ y))
abbrev Equation928 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ (x ∘ z))
abbrev Equation929 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (x ∘ w))
abbrev Equation930 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ (y ∘ x))
abbrev Equation931 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ (y ∘ y))
abbrev Equation932 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ (y ∘ z))
abbrev Equation933 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (y ∘ w))
abbrev Equation934 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ (z ∘ x))
abbrev Equation935 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ (z ∘ y))
abbrev Equation936 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ z) ∘ (z ∘ z))
abbrev Equation937 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (z ∘ w))
abbrev Equation938 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (w ∘ x))
abbrev Equation939 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (w ∘ y))
abbrev Equation940 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (w ∘ z))
abbrev Equation941 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ z) ∘ (w ∘ w))
abbrev Equation942 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((y ∘ z) ∘ (w ∘ u))
abbrev Equation943 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ (x ∘ x))
abbrev Equation944 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ (x ∘ y))
abbrev Equation945 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ (x ∘ z))
abbrev Equation946 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (x ∘ w))
abbrev Equation947 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ (y ∘ x))
abbrev Equation948 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ (y ∘ y))
abbrev Equation949 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ (y ∘ z))
abbrev Equation950 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (y ∘ w))
abbrev Equation951 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ (z ∘ x))
abbrev Equation952 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ (z ∘ y))
abbrev Equation953 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ x) ∘ (z ∘ z))
abbrev Equation954 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (z ∘ w))
abbrev Equation955 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (w ∘ x))
abbrev Equation956 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (w ∘ y))
abbrev Equation957 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (w ∘ z))
abbrev Equation958 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ x) ∘ (w ∘ w))
abbrev Equation959 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ x) ∘ (w ∘ u))
abbrev Equation960 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ (x ∘ x))
abbrev Equation961 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ (x ∘ y))
abbrev Equation962 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ (x ∘ z))
abbrev Equation963 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (x ∘ w))
abbrev Equation964 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ (y ∘ x))
abbrev Equation965 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ (y ∘ y))
abbrev Equation966 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ (y ∘ z))
abbrev Equation967 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (y ∘ w))
abbrev Equation968 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ (z ∘ x))
abbrev Equation969 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ (z ∘ y))
abbrev Equation970 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ y) ∘ (z ∘ z))
abbrev Equation971 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (z ∘ w))
abbrev Equation972 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (w ∘ x))
abbrev Equation973 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (w ∘ y))
abbrev Equation974 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (w ∘ z))
abbrev Equation975 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ y) ∘ (w ∘ w))
abbrev Equation976 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ y) ∘ (w ∘ u))
abbrev Equation977 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (x ∘ x))
abbrev Equation978 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (x ∘ y))
abbrev Equation979 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (x ∘ z))
abbrev Equation980 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (x ∘ w))
abbrev Equation981 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (y ∘ x))
abbrev Equation982 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (y ∘ y))
abbrev Equation983 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (y ∘ z))
abbrev Equation984 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (y ∘ w))
abbrev Equation985 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (z ∘ x))
abbrev Equation986 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (z ∘ y))
abbrev Equation987 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ z) ∘ (z ∘ z))
abbrev Equation988 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (z ∘ w))
abbrev Equation989 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (w ∘ x))
abbrev Equation990 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (w ∘ y))
abbrev Equation991 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (w ∘ z))
abbrev Equation992 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ z) ∘ (w ∘ w))
abbrev Equation993 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ z) ∘ (w ∘ u))
abbrev Equation994 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (x ∘ x))
abbrev Equation995 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (x ∘ y))
abbrev Equation996 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (x ∘ z))
abbrev Equation997 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (x ∘ w))
abbrev Equation998 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (x ∘ u))
abbrev Equation999 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (y ∘ x))
abbrev Equation1000 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (y ∘ y))
abbrev Equation1001 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (y ∘ z))
abbrev Equation1002 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (y ∘ w))
abbrev Equation1003 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (y ∘ u))
abbrev Equation1004 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (z ∘ x))
abbrev Equation1005 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (z ∘ y))
abbrev Equation1006 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (z ∘ z))
abbrev Equation1007 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (z ∘ w))
abbrev Equation1008 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (z ∘ u))
abbrev Equation1009 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (w ∘ x))
abbrev Equation1010 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (w ∘ y))
abbrev Equation1011 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (w ∘ z))
abbrev Equation1012 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ w) ∘ (w ∘ w))
abbrev Equation1013 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (w ∘ u))
abbrev Equation1014 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (u ∘ x))
abbrev Equation1015 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (u ∘ y))
abbrev Equation1016 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (u ∘ z))
abbrev Equation1017 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (u ∘ w))
abbrev Equation1018 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ w) ∘ (u ∘ u))
abbrev Equation1019 (G: Type u) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ w) ∘ (u ∘ v))
abbrev Equation1020 (G: Type u) [Magma G] := ∀ x : G, x = x ∘ ((x ∘ (x ∘ x)) ∘ x)
abbrev Equation1021 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ (x ∘ x)) ∘ y)
abbrev Equation1022 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ (x ∘ y)) ∘ x)
abbrev Equation1023 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ (x ∘ y)) ∘ y)
abbrev Equation1024 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ (x ∘ y)) ∘ z)
abbrev Equation1025 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ (y ∘ x)) ∘ x)
abbrev Equation1026 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ (y ∘ x)) ∘ y)
abbrev Equation1027 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ (y ∘ x)) ∘ z)
abbrev Equation1028 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ (y ∘ y)) ∘ x)
abbrev Equation1029 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((x ∘ (y ∘ y)) ∘ y)
abbrev Equation1030 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ (y ∘ y)) ∘ z)
abbrev Equation1031 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ (y ∘ z)) ∘ x)
abbrev Equation1032 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ (y ∘ z)) ∘ y)
abbrev Equation1033 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((x ∘ (y ∘ z)) ∘ z)
abbrev Equation1034 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ ((x ∘ (y ∘ z)) ∘ w)
abbrev Equation1035 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ (x ∘ x)) ∘ x)
abbrev Equation1036 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ (x ∘ x)) ∘ y)
abbrev Equation1037 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (x ∘ x)) ∘ z)
abbrev Equation1038 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ (x ∘ y)) ∘ x)
abbrev Equation1039 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ (x ∘ y)) ∘ y)
abbrev Equation1040 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (x ∘ y)) ∘ z)
abbrev Equation1041 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (x ∘ z)) ∘ x)
abbrev Equation1042 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (x ∘ z)) ∘ y)
abbrev Equation1043 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (x ∘ z)) ∘ z)
abbrev Equation1044 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (x ∘ z)) ∘ w)
abbrev Equation1045 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ (y ∘ x)) ∘ x)
abbrev Equation1046 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ (y ∘ x)) ∘ y)
abbrev Equation1047 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (y ∘ x)) ∘ z)
abbrev Equation1048 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ (y ∘ y)) ∘ x)
abbrev Equation1049 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ ((y ∘ (y ∘ y)) ∘ y)
abbrev Equation1050 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (y ∘ y)) ∘ z)
abbrev Equation1051 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (y ∘ z)) ∘ x)
abbrev Equation1052 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (y ∘ z)) ∘ y)
abbrev Equation1053 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (y ∘ z)) ∘ z)
abbrev Equation1054 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (y ∘ z)) ∘ w)
abbrev Equation1055 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (z ∘ x)) ∘ x)
abbrev Equation1056 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (z ∘ x)) ∘ y)
abbrev Equation1057 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (z ∘ x)) ∘ z)
abbrev Equation1058 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ x)) ∘ w)
abbrev Equation1059 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (z ∘ y)) ∘ x)
abbrev Equation1060 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (z ∘ y)) ∘ y)
abbrev Equation1061 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (z ∘ y)) ∘ z)
abbrev Equation1062 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ y)) ∘ w)
abbrev Equation1063 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (z ∘ z)) ∘ x)
abbrev Equation1064 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (z ∘ z)) ∘ y)
abbrev Equation1065 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ ((y ∘ (z ∘ z)) ∘ z)
abbrev Equation1066 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ z)) ∘ w)
abbrev Equation1067 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ x)
abbrev Equation1068 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ y)
abbrev Equation1069 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ z)
abbrev Equation1070 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ w)
abbrev Equation1071 (G: Type u) [Magma G] := ∀ x y z w u : G, x = x ∘ ((y ∘ (z ∘ w)) ∘ u)
abbrev Equation1072 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (x ∘ x)) ∘ x)
abbrev Equation1073 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (x ∘ x)) ∘ y)
abbrev Equation1074 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (x ∘ x)) ∘ z)
abbrev Equation1075 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (x ∘ y)) ∘ x)
abbrev Equation1076 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (x ∘ y)) ∘ y)
abbrev Equation1077 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (x ∘ y)) ∘ z)
abbrev Equation1078 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (x ∘ z)) ∘ x)
abbrev Equation1079 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (x ∘ z)) ∘ y)
abbrev Equation1080 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (x ∘ z)) ∘ z)
abbrev Equation1081 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (x ∘ z)) ∘ w)
abbrev Equation1082 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (y ∘ x)) ∘ x)
abbrev Equation1083 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (y ∘ x)) ∘ y)
abbrev Equation1084 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (y ∘ x)) ∘ z)
abbrev Equation1085 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (y ∘ y)) ∘ x)
abbrev Equation1086 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((x ∘ (y ∘ y)) ∘ y)
abbrev Equation1087 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (y ∘ y)) ∘ z)
abbrev Equation1088 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (y ∘ z)) ∘ x)
abbrev Equation1089 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (y ∘ z)) ∘ y)
abbrev Equation1090 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (y ∘ z)) ∘ z)
abbrev Equation1091 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (y ∘ z)) ∘ w)
abbrev Equation1092 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (z ∘ x)) ∘ x)
abbrev Equation1093 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (z ∘ x)) ∘ y)
abbrev Equation1094 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (z ∘ x)) ∘ z)
abbrev Equation1095 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ x)) ∘ w)
abbrev Equation1096 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (z ∘ y)) ∘ x)
abbrev Equation1097 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (z ∘ y)) ∘ y)
abbrev Equation1098 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (z ∘ y)) ∘ z)
abbrev Equation1099 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ y)) ∘ w)
abbrev Equation1100 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (z ∘ z)) ∘ x)
abbrev Equation1101 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (z ∘ z)) ∘ y)
abbrev Equation1102 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((x ∘ (z ∘ z)) ∘ z)
abbrev Equation1103 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ z)) ∘ w)
abbrev Equation1104 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ w)) ∘ x)
abbrev Equation1105 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ w)) ∘ y)
abbrev Equation1106 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ w)) ∘ z)
abbrev Equation1107 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((x ∘ (z ∘ w)) ∘ w)
abbrev Equation1108 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((x ∘ (z ∘ w)) ∘ u)
abbrev Equation1109 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ (x ∘ x)) ∘ x)
abbrev Equation1110 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ (x ∘ x)) ∘ y)
abbrev Equation1111 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (x ∘ x)) ∘ z)
abbrev Equation1112 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ (x ∘ y)) ∘ x)
abbrev Equation1113 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ (x ∘ y)) ∘ y)
abbrev Equation1114 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (x ∘ y)) ∘ z)
abbrev Equation1115 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (x ∘ z)) ∘ x)
abbrev Equation1116 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (x ∘ z)) ∘ y)
abbrev Equation1117 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (x ∘ z)) ∘ z)
abbrev Equation1118 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (x ∘ z)) ∘ w)
abbrev Equation1119 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ (y ∘ x)) ∘ x)
abbrev Equation1120 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ (y ∘ x)) ∘ y)
abbrev Equation1121 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (y ∘ x)) ∘ z)
abbrev Equation1122 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ (y ∘ y)) ∘ x)
abbrev Equation1123 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ ((y ∘ (y ∘ y)) ∘ y)
abbrev Equation1124 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (y ∘ y)) ∘ z)
abbrev Equation1125 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (y ∘ z)) ∘ x)
abbrev Equation1126 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (y ∘ z)) ∘ y)
abbrev Equation1127 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (y ∘ z)) ∘ z)
abbrev Equation1128 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (y ∘ z)) ∘ w)
abbrev Equation1129 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (z ∘ x)) ∘ x)
abbrev Equation1130 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (z ∘ x)) ∘ y)
abbrev Equation1131 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (z ∘ x)) ∘ z)
abbrev Equation1132 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ x)) ∘ w)
abbrev Equation1133 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (z ∘ y)) ∘ x)
abbrev Equation1134 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (z ∘ y)) ∘ y)
abbrev Equation1135 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (z ∘ y)) ∘ z)
abbrev Equation1136 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ y)) ∘ w)
abbrev Equation1137 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (z ∘ z)) ∘ x)
abbrev Equation1138 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (z ∘ z)) ∘ y)
abbrev Equation1139 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((y ∘ (z ∘ z)) ∘ z)
abbrev Equation1140 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ z)) ∘ w)
abbrev Equation1141 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ w)) ∘ x)
abbrev Equation1142 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ w)) ∘ y)
abbrev Equation1143 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ w)) ∘ z)
abbrev Equation1144 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((y ∘ (z ∘ w)) ∘ w)
abbrev Equation1145 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((y ∘ (z ∘ w)) ∘ u)
abbrev Equation1146 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (x ∘ x)) ∘ x)
abbrev Equation1147 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (x ∘ x)) ∘ y)
abbrev Equation1148 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (x ∘ x)) ∘ z)
abbrev Equation1149 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ x)) ∘ w)
abbrev Equation1150 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (x ∘ y)) ∘ x)
abbrev Equation1151 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (x ∘ y)) ∘ y)
abbrev Equation1152 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (x ∘ y)) ∘ z)
abbrev Equation1153 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ y)) ∘ w)
abbrev Equation1154 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (x ∘ z)) ∘ x)
abbrev Equation1155 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (x ∘ z)) ∘ y)
abbrev Equation1156 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (x ∘ z)) ∘ z)
abbrev Equation1157 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ z)) ∘ w)
abbrev Equation1158 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ x)
abbrev Equation1159 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ y)
abbrev Equation1160 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ z)
abbrev Equation1161 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ w)
abbrev Equation1162 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (x ∘ w)) ∘ u)
abbrev Equation1163 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (y ∘ x)) ∘ x)
abbrev Equation1164 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (y ∘ x)) ∘ y)
abbrev Equation1165 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (y ∘ x)) ∘ z)
abbrev Equation1166 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ x)) ∘ w)
abbrev Equation1167 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (y ∘ y)) ∘ x)
abbrev Equation1168 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (y ∘ y)) ∘ y)
abbrev Equation1169 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (y ∘ y)) ∘ z)
abbrev Equation1170 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ y)) ∘ w)
abbrev Equation1171 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (y ∘ z)) ∘ x)
abbrev Equation1172 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (y ∘ z)) ∘ y)
abbrev Equation1173 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (y ∘ z)) ∘ z)
abbrev Equation1174 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ z)) ∘ w)
abbrev Equation1175 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ x)
abbrev Equation1176 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ y)
abbrev Equation1177 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ z)
abbrev Equation1178 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ w)
abbrev Equation1179 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (y ∘ w)) ∘ u)
abbrev Equation1180 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ x)) ∘ x)
abbrev Equation1181 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ x)) ∘ y)
abbrev Equation1182 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ x)) ∘ z)
abbrev Equation1183 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ x)) ∘ w)
abbrev Equation1184 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ y)) ∘ x)
abbrev Equation1185 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ y)) ∘ y)
abbrev Equation1186 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ y)) ∘ z)
abbrev Equation1187 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ y)) ∘ w)
abbrev Equation1188 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ z)) ∘ x)
abbrev Equation1189 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ z)) ∘ y)
abbrev Equation1190 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ ((z ∘ (z ∘ z)) ∘ z)
abbrev Equation1191 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ z)) ∘ w)
abbrev Equation1192 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ w)) ∘ x)
abbrev Equation1193 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ w)) ∘ y)
abbrev Equation1194 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ w)) ∘ z)
abbrev Equation1195 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (z ∘ w)) ∘ w)
abbrev Equation1196 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (z ∘ w)) ∘ u)
abbrev Equation1197 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ x)) ∘ x)
abbrev Equation1198 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ x)) ∘ y)
abbrev Equation1199 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ x)) ∘ z)
abbrev Equation1200 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ x)) ∘ w)
abbrev Equation1201 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ x)) ∘ u)
abbrev Equation1202 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ y)) ∘ x)
abbrev Equation1203 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ y)) ∘ y)
abbrev Equation1204 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ y)) ∘ z)
abbrev Equation1205 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ y)) ∘ w)
abbrev Equation1206 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ y)) ∘ u)
abbrev Equation1207 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ z)) ∘ x)
abbrev Equation1208 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ z)) ∘ y)
abbrev Equation1209 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ z)) ∘ z)
abbrev Equation1210 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ z)) ∘ w)
abbrev Equation1211 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ z)) ∘ u)
abbrev Equation1212 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ w)) ∘ x)
abbrev Equation1213 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ w)) ∘ y)
abbrev Equation1214 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ w)) ∘ z)
abbrev Equation1215 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ ((z ∘ (w ∘ w)) ∘ w)
abbrev Equation1216 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ w)) ∘ u)
abbrev Equation1217 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ x)
abbrev Equation1218 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ y)
abbrev Equation1219 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ z)
abbrev Equation1220 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ w)
abbrev Equation1221 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ u)
abbrev Equation1222 (G: Type u) [Magma G] := ∀ x y z w u v : G, x = y ∘ ((z ∘ (w ∘ u)) ∘ v)
abbrev Equation1223 (G: Type u) [Magma G] := ∀ x : G, x = x ∘ (((x ∘ x) ∘ x) ∘ x)
abbrev Equation1224 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (((x ∘ x) ∘ x) ∘ y)
abbrev Equation1225 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (((x ∘ x) ∘ y) ∘ x)
abbrev Equation1226 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (((x ∘ x) ∘ y) ∘ y)
abbrev Equation1227 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (((x ∘ x) ∘ y) ∘ z)
abbrev Equation1228 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (((x ∘ y) ∘ x) ∘ x)
abbrev Equation1229 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (((x ∘ y) ∘ x) ∘ y)
abbrev Equation1230 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (((x ∘ y) ∘ x) ∘ z)
abbrev Equation1231 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (((x ∘ y) ∘ y) ∘ x)
abbrev Equation1232 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (((x ∘ y) ∘ y) ∘ y)
abbrev Equation1233 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (((x ∘ y) ∘ y) ∘ z)
abbrev Equation1234 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (((x ∘ y) ∘ z) ∘ x)
abbrev Equation1235 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (((x ∘ y) ∘ z) ∘ y)
abbrev Equation1236 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (((x ∘ y) ∘ z) ∘ z)
abbrev Equation1237 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (((x ∘ y) ∘ z) ∘ w)
abbrev Equation1238 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (((y ∘ x) ∘ x) ∘ x)
abbrev Equation1239 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (((y ∘ x) ∘ x) ∘ y)
abbrev Equation1240 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ x) ∘ x) ∘ z)
abbrev Equation1241 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (((y ∘ x) ∘ y) ∘ x)
abbrev Equation1242 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (((y ∘ x) ∘ y) ∘ y)
abbrev Equation1243 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ x) ∘ y) ∘ z)
abbrev Equation1244 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ x) ∘ z) ∘ x)
abbrev Equation1245 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ x) ∘ z) ∘ y)
abbrev Equation1246 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ x) ∘ z) ∘ z)
abbrev Equation1247 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ x) ∘ z) ∘ w)
abbrev Equation1248 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (((y ∘ y) ∘ x) ∘ x)
abbrev Equation1249 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (((y ∘ y) ∘ x) ∘ y)
abbrev Equation1250 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ y) ∘ x) ∘ z)
abbrev Equation1251 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (((y ∘ y) ∘ y) ∘ x)
abbrev Equation1252 (G: Type u) [Magma G] := ∀ x y : G, x = x ∘ (((y ∘ y) ∘ y) ∘ y)
abbrev Equation1253 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ y) ∘ y) ∘ z)
abbrev Equation1254 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ y) ∘ z) ∘ x)
abbrev Equation1255 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ y) ∘ z) ∘ y)
abbrev Equation1256 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ y) ∘ z) ∘ z)
abbrev Equation1257 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ y) ∘ z) ∘ w)
abbrev Equation1258 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ z) ∘ x) ∘ x)
abbrev Equation1259 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ z) ∘ x) ∘ y)
abbrev Equation1260 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ z) ∘ x) ∘ z)
abbrev Equation1261 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ x) ∘ w)
abbrev Equation1262 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ z) ∘ y) ∘ x)
abbrev Equation1263 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ z) ∘ y) ∘ y)
abbrev Equation1264 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ z) ∘ y) ∘ z)
abbrev Equation1265 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ y) ∘ w)
abbrev Equation1266 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ z) ∘ z) ∘ x)
abbrev Equation1267 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ z) ∘ z) ∘ y)
abbrev Equation1268 (G: Type u) [Magma G] := ∀ x y z : G, x = x ∘ (((y ∘ z) ∘ z) ∘ z)
abbrev Equation1269 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ z) ∘ w)
abbrev Equation1270 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ w) ∘ x)
abbrev Equation1271 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ w) ∘ y)
abbrev Equation1272 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ w) ∘ z)
abbrev Equation1273 (G: Type u) [Magma G] := ∀ x y z w : G, x = x ∘ (((y ∘ z) ∘ w) ∘ w)
abbrev Equation1274 (G: Type u) [Magma G] := ∀ x y z w u : G, x = x ∘ (((y ∘ z) ∘ w) ∘ u)
abbrev Equation1275 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ x) ∘ x) ∘ x)
abbrev Equation1276 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ x) ∘ x) ∘ y)
abbrev Equation1277 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ x) ∘ x) ∘ z)
abbrev Equation1278 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ x) ∘ y) ∘ x)
abbrev Equation1279 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ x) ∘ y) ∘ y)
abbrev Equation1280 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ x) ∘ y) ∘ z)
abbrev Equation1281 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ x) ∘ z) ∘ x)
abbrev Equation1282 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ x) ∘ z) ∘ y)
abbrev Equation1283 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ x) ∘ z) ∘ z)
abbrev Equation1284 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ x) ∘ z) ∘ w)
abbrev Equation1285 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ y) ∘ x) ∘ x)
abbrev Equation1286 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ y) ∘ x) ∘ y)
abbrev Equation1287 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ y) ∘ x) ∘ z)
abbrev Equation1288 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ y) ∘ y) ∘ x)
abbrev Equation1289 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (((x ∘ y) ∘ y) ∘ y)
abbrev Equation1290 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ y) ∘ y) ∘ z)
abbrev Equation1291 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ y) ∘ z) ∘ x)
abbrev Equation1292 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ y) ∘ z) ∘ y)
abbrev Equation1293 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ y) ∘ z) ∘ z)
abbrev Equation1294 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ y) ∘ z) ∘ w)
abbrev Equation1295 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ z) ∘ x) ∘ x)
abbrev Equation1296 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ z) ∘ x) ∘ y)
abbrev Equation1297 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ z) ∘ x) ∘ z)
abbrev Equation1298 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ x) ∘ w)
abbrev Equation1299 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ z) ∘ y) ∘ x)
abbrev Equation1300 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ z) ∘ y) ∘ y)
abbrev Equation1301 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ z) ∘ y) ∘ z)
abbrev Equation1302 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ y) ∘ w)
abbrev Equation1303 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ z) ∘ z) ∘ x)
abbrev Equation1304 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ z) ∘ z) ∘ y)
abbrev Equation1305 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((x ∘ z) ∘ z) ∘ z)
abbrev Equation1306 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ z) ∘ w)
abbrev Equation1307 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ w) ∘ x)
abbrev Equation1308 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ w) ∘ y)
abbrev Equation1309 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ w) ∘ z)
abbrev Equation1310 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((x ∘ z) ∘ w) ∘ w)
abbrev Equation1311 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (((x ∘ z) ∘ w) ∘ u)
abbrev Equation1312 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (((y ∘ x) ∘ x) ∘ x)
abbrev Equation1313 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (((y ∘ x) ∘ x) ∘ y)
abbrev Equation1314 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ x) ∘ x) ∘ z)
abbrev Equation1315 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (((y ∘ x) ∘ y) ∘ x)
abbrev Equation1316 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (((y ∘ x) ∘ y) ∘ y)
abbrev Equation1317 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ x) ∘ y) ∘ z)
abbrev Equation1318 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ x) ∘ z) ∘ x)
abbrev Equation1319 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ x) ∘ z) ∘ y)
abbrev Equation1320 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ x) ∘ z) ∘ z)
abbrev Equation1321 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ x) ∘ z) ∘ w)
abbrev Equation1322 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (((y ∘ y) ∘ x) ∘ x)
abbrev Equation1323 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (((y ∘ y) ∘ x) ∘ y)
abbrev Equation1324 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ y) ∘ x) ∘ z)
abbrev Equation1325 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (((y ∘ y) ∘ y) ∘ x)
abbrev Equation1326 (G: Type u) [Magma G] := ∀ x y : G, x = y ∘ (((y ∘ y) ∘ y) ∘ y)
abbrev Equation1327 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ y) ∘ y) ∘ z)
abbrev Equation1328 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ y) ∘ z) ∘ x)
abbrev Equation1329 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ y) ∘ z) ∘ y)
abbrev Equation1330 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ y) ∘ z) ∘ z)
abbrev Equation1331 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ y) ∘ z) ∘ w)
abbrev Equation1332 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ z) ∘ x) ∘ x)
abbrev Equation1333 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ z) ∘ x) ∘ y)
abbrev Equation1334 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ z) ∘ x) ∘ z)
abbrev Equation1335 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ x) ∘ w)
abbrev Equation1336 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ z) ∘ y) ∘ x)
abbrev Equation1337 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ z) ∘ y) ∘ y)
abbrev Equation1338 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ z) ∘ y) ∘ z)
abbrev Equation1339 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ y) ∘ w)
abbrev Equation1340 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ z) ∘ z) ∘ x)
abbrev Equation1341 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ z) ∘ z) ∘ y)
abbrev Equation1342 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((y ∘ z) ∘ z) ∘ z)
abbrev Equation1343 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ z) ∘ w)
abbrev Equation1344 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ w) ∘ x)
abbrev Equation1345 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ w) ∘ y)
abbrev Equation1346 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ w) ∘ z)
abbrev Equation1347 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((y ∘ z) ∘ w) ∘ w)
abbrev Equation1348 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (((y ∘ z) ∘ w) ∘ u)
abbrev Equation1349 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ x) ∘ x) ∘ x)
abbrev Equation1350 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ x) ∘ x) ∘ y)
abbrev Equation1351 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ x) ∘ x) ∘ z)
abbrev Equation1352 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ x) ∘ w)
abbrev Equation1353 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ x) ∘ y) ∘ x)
abbrev Equation1354 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ x) ∘ y) ∘ y)
abbrev Equation1355 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ x) ∘ y) ∘ z)
abbrev Equation1356 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ y) ∘ w)
abbrev Equation1357 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ x) ∘ z) ∘ x)
abbrev Equation1358 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ x) ∘ z) ∘ y)
abbrev Equation1359 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ x) ∘ z) ∘ z)
abbrev Equation1360 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ z) ∘ w)
abbrev Equation1361 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ w) ∘ x)
abbrev Equation1362 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ w) ∘ y)
abbrev Equation1363 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ w) ∘ z)
abbrev Equation1364 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ x) ∘ w) ∘ w)
abbrev Equation1365 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ x) ∘ w) ∘ u)
abbrev Equation1366 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ y) ∘ x) ∘ x)
abbrev Equation1367 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ y) ∘ x) ∘ y)
abbrev Equation1368 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ y) ∘ x) ∘ z)
abbrev Equation1369 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ x) ∘ w)
abbrev Equation1370 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ y) ∘ y) ∘ x)
abbrev Equation1371 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ y) ∘ y) ∘ y)
abbrev Equation1372 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ y) ∘ y) ∘ z)
abbrev Equation1373 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ y) ∘ w)
abbrev Equation1374 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ y) ∘ z) ∘ x)
abbrev Equation1375 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ y) ∘ z) ∘ y)
abbrev Equation1376 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ y) ∘ z) ∘ z)
abbrev Equation1377 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ z) ∘ w)
abbrev Equation1378 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ w) ∘ x)
abbrev Equation1379 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ w) ∘ y)
abbrev Equation1380 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ w) ∘ z)
abbrev Equation1381 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ y) ∘ w) ∘ w)
abbrev Equation1382 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ y) ∘ w) ∘ u)
abbrev Equation1383 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ x) ∘ x)
abbrev Equation1384 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ x) ∘ y)
abbrev Equation1385 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ x) ∘ z)
abbrev Equation1386 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ x) ∘ w)
abbrev Equation1387 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ y) ∘ x)
abbrev Equation1388 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ y) ∘ y)
abbrev Equation1389 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ y) ∘ z)
abbrev Equation1390 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ y) ∘ w)
abbrev Equation1391 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ z) ∘ x)
abbrev Equation1392 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ z) ∘ y)
abbrev Equation1393 (G: Type u) [Magma G] := ∀ x y z : G, x = y ∘ (((z ∘ z) ∘ z) ∘ z)
abbrev Equation1394 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ z) ∘ w)
abbrev Equation1395 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ w) ∘ x)
abbrev Equation1396 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ w) ∘ y)
abbrev Equation1397 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ w) ∘ z)
abbrev Equation1398 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ z) ∘ w) ∘ w)
abbrev Equation1399 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ z) ∘ w) ∘ u)
abbrev Equation1400 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ x) ∘ x)
abbrev Equation1401 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ x) ∘ y)
abbrev Equation1402 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ x) ∘ z)
abbrev Equation1403 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ x) ∘ w)
abbrev Equation1404 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ x) ∘ u)
abbrev Equation1405 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ y) ∘ x)
abbrev Equation1406 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ y) ∘ y)
abbrev Equation1407 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ y) ∘ z)
abbrev Equation1408 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ y) ∘ w)
abbrev Equation1409 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ y) ∘ u)
abbrev Equation1410 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ z) ∘ x)
abbrev Equation1411 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ z) ∘ y)
abbrev Equation1412 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ z) ∘ z)
abbrev Equation1413 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ z) ∘ w)
abbrev Equation1414 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ z) ∘ u)
abbrev Equation1415 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ w) ∘ x)
abbrev Equation1416 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ w) ∘ y)
abbrev Equation1417 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ w) ∘ z)
abbrev Equation1418 (G: Type u) [Magma G] := ∀ x y z w : G, x = y ∘ (((z ∘ w) ∘ w) ∘ w)
abbrev Equation1419 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ w) ∘ u)
abbrev Equation1420 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ u) ∘ x)
abbrev Equation1421 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ u) ∘ y)
abbrev Equation1422 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ u) ∘ z)
abbrev Equation1423 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ u) ∘ w)
abbrev Equation1424 (G: Type u) [Magma G] := ∀ x y z w u : G, x = y ∘ (((z ∘ w) ∘ u) ∘ u)
abbrev Equation1425 (G: Type u) [Magma G] := ∀ x y z w u v : G, x = y ∘ (((z ∘ w) ∘ u) ∘ v)
abbrev Equation1426 (G: Type u) [Magma G] := ∀ x : G, x = (x ∘ x) ∘ (x ∘ (x ∘ x))
abbrev Equation1427 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ (x ∘ (x ∘ y))
abbrev Equation1428 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ (x ∘ (y ∘ x))
abbrev Equation1429 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ (x ∘ (y ∘ y))
abbrev Equation1430 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ (x ∘ (y ∘ z))
abbrev Equation1431 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ (y ∘ (x ∘ x))
abbrev Equation1432 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ (y ∘ (x ∘ y))
abbrev Equation1433 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ (y ∘ (x ∘ z))
abbrev Equation1434 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ (y ∘ (y ∘ x))
abbrev Equation1435 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ (y ∘ (y ∘ y))
abbrev Equation1436 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ (y ∘ (y ∘ z))
abbrev Equation1437 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ (y ∘ (z ∘ x))
abbrev Equation1438 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ (y ∘ (z ∘ y))
abbrev Equation1439 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ (y ∘ (z ∘ z))
abbrev Equation1440 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ x) ∘ (y ∘ (z ∘ w))
abbrev Equation1441 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (x ∘ (x ∘ x))
abbrev Equation1442 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (x ∘ (x ∘ y))
abbrev Equation1443 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (x ∘ (x ∘ z))
abbrev Equation1444 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (x ∘ (y ∘ x))
abbrev Equation1445 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (x ∘ (y ∘ y))
abbrev Equation1446 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (x ∘ (y ∘ z))
abbrev Equation1447 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (x ∘ (z ∘ x))
abbrev Equation1448 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (x ∘ (z ∘ y))
abbrev Equation1449 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (x ∘ (z ∘ z))
abbrev Equation1450 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (x ∘ (z ∘ w))
abbrev Equation1451 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (y ∘ (x ∘ x))
abbrev Equation1452 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (y ∘ (x ∘ y))
abbrev Equation1453 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (y ∘ (x ∘ z))
abbrev Equation1454 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (y ∘ (y ∘ x))
abbrev Equation1455 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ (y ∘ (y ∘ y))
abbrev Equation1456 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (y ∘ (y ∘ z))
abbrev Equation1457 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (y ∘ (z ∘ x))
abbrev Equation1458 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (y ∘ (z ∘ y))
abbrev Equation1459 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (y ∘ (z ∘ z))
abbrev Equation1460 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (y ∘ (z ∘ w))
abbrev Equation1461 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ (x ∘ x))
abbrev Equation1462 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ (x ∘ y))
abbrev Equation1463 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ (x ∘ z))
abbrev Equation1464 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (x ∘ w))
abbrev Equation1465 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ (y ∘ x))
abbrev Equation1466 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ (y ∘ y))
abbrev Equation1467 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ (y ∘ z))
abbrev Equation1468 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (y ∘ w))
abbrev Equation1469 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ (z ∘ x))
abbrev Equation1470 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ (z ∘ y))
abbrev Equation1471 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ (z ∘ (z ∘ z))
abbrev Equation1472 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (z ∘ w))
abbrev Equation1473 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (w ∘ x))
abbrev Equation1474 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (w ∘ y))
abbrev Equation1475 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (w ∘ z))
abbrev Equation1476 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ (z ∘ (w ∘ w))
abbrev Equation1477 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (x ∘ y) ∘ (z ∘ (w ∘ u))
abbrev Equation1478 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (x ∘ (x ∘ x))
abbrev Equation1479 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (x ∘ (x ∘ y))
abbrev Equation1480 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (x ∘ (x ∘ z))
abbrev Equation1481 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (x ∘ (y ∘ x))
abbrev Equation1482 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (x ∘ (y ∘ y))
abbrev Equation1483 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (x ∘ (y ∘ z))
abbrev Equation1484 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (x ∘ (z ∘ x))
abbrev Equation1485 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (x ∘ (z ∘ y))
abbrev Equation1486 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (x ∘ (z ∘ z))
abbrev Equation1487 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (x ∘ (z ∘ w))
abbrev Equation1488 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (y ∘ (x ∘ x))
abbrev Equation1489 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (y ∘ (x ∘ y))
abbrev Equation1490 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (y ∘ (x ∘ z))
abbrev Equation1491 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (y ∘ (y ∘ x))
abbrev Equation1492 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ (y ∘ (y ∘ y))
abbrev Equation1493 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (y ∘ (y ∘ z))
abbrev Equation1494 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (y ∘ (z ∘ x))
abbrev Equation1495 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (y ∘ (z ∘ y))
abbrev Equation1496 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (y ∘ (z ∘ z))
abbrev Equation1497 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (y ∘ (z ∘ w))
abbrev Equation1498 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ (x ∘ x))
abbrev Equation1499 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ (x ∘ y))
abbrev Equation1500 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ (x ∘ z))
abbrev Equation1501 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (x ∘ w))
abbrev Equation1502 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ (y ∘ x))
abbrev Equation1503 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ (y ∘ y))
abbrev Equation1504 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ (y ∘ z))
abbrev Equation1505 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (y ∘ w))
abbrev Equation1506 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ (z ∘ x))
abbrev Equation1507 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ (z ∘ y))
abbrev Equation1508 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ (z ∘ (z ∘ z))
abbrev Equation1509 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (z ∘ w))
abbrev Equation1510 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (w ∘ x))
abbrev Equation1511 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (w ∘ y))
abbrev Equation1512 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (w ∘ z))
abbrev Equation1513 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ (z ∘ (w ∘ w))
abbrev Equation1514 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ x) ∘ (z ∘ (w ∘ u))
abbrev Equation1515 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (x ∘ (x ∘ x))
abbrev Equation1516 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (x ∘ (x ∘ y))
abbrev Equation1517 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (x ∘ (x ∘ z))
abbrev Equation1518 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (x ∘ (y ∘ x))
abbrev Equation1519 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (x ∘ (y ∘ y))
abbrev Equation1520 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (x ∘ (y ∘ z))
abbrev Equation1521 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (x ∘ (z ∘ x))
abbrev Equation1522 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (x ∘ (z ∘ y))
abbrev Equation1523 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (x ∘ (z ∘ z))
abbrev Equation1524 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (x ∘ (z ∘ w))
abbrev Equation1525 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (y ∘ (x ∘ x))
abbrev Equation1526 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (y ∘ (x ∘ y))
abbrev Equation1527 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (y ∘ (x ∘ z))
abbrev Equation1528 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (y ∘ (y ∘ x))
abbrev Equation1529 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ (y ∘ (y ∘ y))
abbrev Equation1530 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (y ∘ (y ∘ z))
abbrev Equation1531 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (y ∘ (z ∘ x))
abbrev Equation1532 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (y ∘ (z ∘ y))
abbrev Equation1533 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (y ∘ (z ∘ z))
abbrev Equation1534 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (y ∘ (z ∘ w))
abbrev Equation1535 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ (x ∘ x))
abbrev Equation1536 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ (x ∘ y))
abbrev Equation1537 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ (x ∘ z))
abbrev Equation1538 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (x ∘ w))
abbrev Equation1539 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ (y ∘ x))
abbrev Equation1540 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ (y ∘ y))
abbrev Equation1541 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ (y ∘ z))
abbrev Equation1542 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (y ∘ w))
abbrev Equation1543 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ (z ∘ x))
abbrev Equation1544 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ (z ∘ y))
abbrev Equation1545 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ (z ∘ (z ∘ z))
abbrev Equation1546 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (z ∘ w))
abbrev Equation1547 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (w ∘ x))
abbrev Equation1548 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (w ∘ y))
abbrev Equation1549 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (w ∘ z))
abbrev Equation1550 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ (z ∘ (w ∘ w))
abbrev Equation1551 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ y) ∘ (z ∘ (w ∘ u))
abbrev Equation1552 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ (x ∘ x))
abbrev Equation1553 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ (x ∘ y))
abbrev Equation1554 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ (x ∘ z))
abbrev Equation1555 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (x ∘ w))
abbrev Equation1556 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ (y ∘ x))
abbrev Equation1557 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ (y ∘ y))
abbrev Equation1558 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ (y ∘ z))
abbrev Equation1559 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (y ∘ w))
abbrev Equation1560 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ (z ∘ x))
abbrev Equation1561 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ (z ∘ y))
abbrev Equation1562 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (x ∘ (z ∘ z))
abbrev Equation1563 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (z ∘ w))
abbrev Equation1564 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (w ∘ x))
abbrev Equation1565 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (w ∘ y))
abbrev Equation1566 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (w ∘ z))
abbrev Equation1567 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (x ∘ (w ∘ w))
abbrev Equation1568 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (x ∘ (w ∘ u))
abbrev Equation1569 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ (x ∘ x))
abbrev Equation1570 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ (x ∘ y))
abbrev Equation1571 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ (x ∘ z))
abbrev Equation1572 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (x ∘ w))
abbrev Equation1573 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ (y ∘ x))
abbrev Equation1574 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ (y ∘ y))
abbrev Equation1575 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ (y ∘ z))
abbrev Equation1576 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (y ∘ w))
abbrev Equation1577 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ (z ∘ x))
abbrev Equation1578 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ (z ∘ y))
abbrev Equation1579 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (y ∘ (z ∘ z))
abbrev Equation1580 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (z ∘ w))
abbrev Equation1581 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (w ∘ x))
abbrev Equation1582 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (w ∘ y))
abbrev Equation1583 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (w ∘ z))
abbrev Equation1584 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (y ∘ (w ∘ w))
abbrev Equation1585 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (y ∘ (w ∘ u))
abbrev Equation1586 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (x ∘ x))
abbrev Equation1587 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (x ∘ y))
abbrev Equation1588 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (x ∘ z))
abbrev Equation1589 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (x ∘ w))
abbrev Equation1590 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (y ∘ x))
abbrev Equation1591 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (y ∘ y))
abbrev Equation1592 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (y ∘ z))
abbrev Equation1593 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (y ∘ w))
abbrev Equation1594 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (z ∘ x))
abbrev Equation1595 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (z ∘ y))
abbrev Equation1596 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ (z ∘ (z ∘ z))
abbrev Equation1597 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (z ∘ w))
abbrev Equation1598 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (w ∘ x))
abbrev Equation1599 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (w ∘ y))
abbrev Equation1600 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (w ∘ z))
abbrev Equation1601 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (z ∘ (w ∘ w))
abbrev Equation1602 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (z ∘ (w ∘ u))
abbrev Equation1603 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (x ∘ x))
abbrev Equation1604 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (x ∘ y))
abbrev Equation1605 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (x ∘ z))
abbrev Equation1606 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (x ∘ w))
abbrev Equation1607 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (x ∘ u))
abbrev Equation1608 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (y ∘ x))
abbrev Equation1609 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (y ∘ y))
abbrev Equation1610 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (y ∘ z))
abbrev Equation1611 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (y ∘ w))
abbrev Equation1612 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (y ∘ u))
abbrev Equation1613 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (z ∘ x))
abbrev Equation1614 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (z ∘ y))
abbrev Equation1615 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (z ∘ z))
abbrev Equation1616 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (z ∘ w))
abbrev Equation1617 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (z ∘ u))
abbrev Equation1618 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (w ∘ x))
abbrev Equation1619 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (w ∘ y))
abbrev Equation1620 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (w ∘ z))
abbrev Equation1621 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ (w ∘ (w ∘ w))
abbrev Equation1622 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (w ∘ u))
abbrev Equation1623 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (u ∘ x))
abbrev Equation1624 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (u ∘ y))
abbrev Equation1625 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (u ∘ z))
abbrev Equation1626 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (u ∘ w))
abbrev Equation1627 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ (w ∘ (u ∘ u))
abbrev Equation1628 (G: Type u) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ (w ∘ (u ∘ v))
abbrev Equation1629 (G: Type u) [Magma G] := ∀ x : G, x = (x ∘ x) ∘ ((x ∘ x) ∘ x)
abbrev Equation1630 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ ((x ∘ x) ∘ y)
abbrev Equation1631 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ ((x ∘ y) ∘ x)
abbrev Equation1632 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ ((x ∘ y) ∘ y)
abbrev Equation1633 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ ((x ∘ y) ∘ z)
abbrev Equation1634 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ ((y ∘ x) ∘ x)
abbrev Equation1635 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ ((y ∘ x) ∘ y)
abbrev Equation1636 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ ((y ∘ x) ∘ z)
abbrev Equation1637 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ ((y ∘ y) ∘ x)
abbrev Equation1638 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ x) ∘ ((y ∘ y) ∘ y)
abbrev Equation1639 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ ((y ∘ y) ∘ z)
abbrev Equation1640 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ ((y ∘ z) ∘ x)
abbrev Equation1641 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ ((y ∘ z) ∘ y)
abbrev Equation1642 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ x) ∘ ((y ∘ z) ∘ z)
abbrev Equation1643 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ x) ∘ ((y ∘ z) ∘ w)
abbrev Equation1644 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ ((x ∘ x) ∘ x)
abbrev Equation1645 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ ((x ∘ x) ∘ y)
abbrev Equation1646 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((x ∘ x) ∘ z)
abbrev Equation1647 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ ((x ∘ y) ∘ x)
abbrev Equation1648 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ ((x ∘ y) ∘ y)
abbrev Equation1649 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((x ∘ y) ∘ z)
abbrev Equation1650 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((x ∘ z) ∘ x)
abbrev Equation1651 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((x ∘ z) ∘ y)
abbrev Equation1652 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((x ∘ z) ∘ z)
abbrev Equation1653 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((x ∘ z) ∘ w)
abbrev Equation1654 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ ((y ∘ x) ∘ x)
abbrev Equation1655 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ ((y ∘ x) ∘ y)
abbrev Equation1656 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((y ∘ x) ∘ z)
abbrev Equation1657 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ ((y ∘ y) ∘ x)
abbrev Equation1658 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ y) ∘ ((y ∘ y) ∘ y)
abbrev Equation1659 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((y ∘ y) ∘ z)
abbrev Equation1660 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((y ∘ z) ∘ x)
abbrev Equation1661 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((y ∘ z) ∘ y)
abbrev Equation1662 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((y ∘ z) ∘ z)
abbrev Equation1663 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((y ∘ z) ∘ w)
abbrev Equation1664 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((z ∘ x) ∘ x)
abbrev Equation1665 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((z ∘ x) ∘ y)
abbrev Equation1666 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((z ∘ x) ∘ z)
abbrev Equation1667 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ x) ∘ w)
abbrev Equation1668 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((z ∘ y) ∘ x)
abbrev Equation1669 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((z ∘ y) ∘ y)
abbrev Equation1670 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((z ∘ y) ∘ z)
abbrev Equation1671 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ y) ∘ w)
abbrev Equation1672 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((z ∘ z) ∘ x)
abbrev Equation1673 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((z ∘ z) ∘ y)
abbrev Equation1674 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ y) ∘ ((z ∘ z) ∘ z)
abbrev Equation1675 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ z) ∘ w)
abbrev Equation1676 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ x)
abbrev Equation1677 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ y)
abbrev Equation1678 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ z)
abbrev Equation1679 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ w)
abbrev Equation1680 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (x ∘ y) ∘ ((z ∘ w) ∘ u)
abbrev Equation1681 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((x ∘ x) ∘ x)
abbrev Equation1682 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((x ∘ x) ∘ y)
abbrev Equation1683 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((x ∘ x) ∘ z)
abbrev Equation1684 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((x ∘ y) ∘ x)
abbrev Equation1685 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((x ∘ y) ∘ y)
abbrev Equation1686 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((x ∘ y) ∘ z)
abbrev Equation1687 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((x ∘ z) ∘ x)
abbrev Equation1688 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((x ∘ z) ∘ y)
abbrev Equation1689 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((x ∘ z) ∘ z)
abbrev Equation1690 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((x ∘ z) ∘ w)
abbrev Equation1691 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((y ∘ x) ∘ x)
abbrev Equation1692 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((y ∘ x) ∘ y)
abbrev Equation1693 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((y ∘ x) ∘ z)
abbrev Equation1694 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((y ∘ y) ∘ x)
abbrev Equation1695 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ x) ∘ ((y ∘ y) ∘ y)
abbrev Equation1696 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((y ∘ y) ∘ z)
abbrev Equation1697 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((y ∘ z) ∘ x)
abbrev Equation1698 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((y ∘ z) ∘ y)
abbrev Equation1699 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((y ∘ z) ∘ z)
abbrev Equation1700 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((y ∘ z) ∘ w)
abbrev Equation1701 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((z ∘ x) ∘ x)
abbrev Equation1702 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((z ∘ x) ∘ y)
abbrev Equation1703 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((z ∘ x) ∘ z)
abbrev Equation1704 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ x) ∘ w)
abbrev Equation1705 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((z ∘ y) ∘ x)
abbrev Equation1706 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((z ∘ y) ∘ y)
abbrev Equation1707 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((z ∘ y) ∘ z)
abbrev Equation1708 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ y) ∘ w)
abbrev Equation1709 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((z ∘ z) ∘ x)
abbrev Equation1710 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((z ∘ z) ∘ y)
abbrev Equation1711 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ x) ∘ ((z ∘ z) ∘ z)
abbrev Equation1712 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ z) ∘ w)
abbrev Equation1713 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ w) ∘ x)
abbrev Equation1714 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ w) ∘ y)
abbrev Equation1715 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ w) ∘ z)
abbrev Equation1716 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ x) ∘ ((z ∘ w) ∘ w)
abbrev Equation1717 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ x) ∘ ((z ∘ w) ∘ u)
abbrev Equation1718 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ ((x ∘ x) ∘ x)
abbrev Equation1719 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ ((x ∘ x) ∘ y)
abbrev Equation1720 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((x ∘ x) ∘ z)
abbrev Equation1721 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ ((x ∘ y) ∘ x)
abbrev Equation1722 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ ((x ∘ y) ∘ y)
abbrev Equation1723 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((x ∘ y) ∘ z)
abbrev Equation1724 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((x ∘ z) ∘ x)
abbrev Equation1725 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((x ∘ z) ∘ y)
abbrev Equation1726 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((x ∘ z) ∘ z)
abbrev Equation1727 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((x ∘ z) ∘ w)
abbrev Equation1728 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ ((y ∘ x) ∘ x)
abbrev Equation1729 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ ((y ∘ x) ∘ y)
abbrev Equation1730 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((y ∘ x) ∘ z)
abbrev Equation1731 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ ((y ∘ y) ∘ x)
abbrev Equation1732 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ y) ∘ ((y ∘ y) ∘ y)
abbrev Equation1733 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((y ∘ y) ∘ z)
abbrev Equation1734 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((y ∘ z) ∘ x)
abbrev Equation1735 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((y ∘ z) ∘ y)
abbrev Equation1736 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((y ∘ z) ∘ z)
abbrev Equation1737 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((y ∘ z) ∘ w)
abbrev Equation1738 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((z ∘ x) ∘ x)
abbrev Equation1739 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((z ∘ x) ∘ y)
abbrev Equation1740 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((z ∘ x) ∘ z)
abbrev Equation1741 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ x) ∘ w)
abbrev Equation1742 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((z ∘ y) ∘ x)
abbrev Equation1743 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((z ∘ y) ∘ y)
abbrev Equation1744 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((z ∘ y) ∘ z)
abbrev Equation1745 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ y) ∘ w)
abbrev Equation1746 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((z ∘ z) ∘ x)
abbrev Equation1747 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((z ∘ z) ∘ y)
abbrev Equation1748 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ y) ∘ ((z ∘ z) ∘ z)
abbrev Equation1749 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ z) ∘ w)
abbrev Equation1750 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ w) ∘ x)
abbrev Equation1751 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ w) ∘ y)
abbrev Equation1752 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ w) ∘ z)
abbrev Equation1753 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ y) ∘ ((z ∘ w) ∘ w)
abbrev Equation1754 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ y) ∘ ((z ∘ w) ∘ u)
abbrev Equation1755 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((x ∘ x) ∘ x)
abbrev Equation1756 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((x ∘ x) ∘ y)
abbrev Equation1757 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((x ∘ x) ∘ z)
abbrev Equation1758 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ x) ∘ w)
abbrev Equation1759 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((x ∘ y) ∘ x)
abbrev Equation1760 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((x ∘ y) ∘ y)
abbrev Equation1761 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((x ∘ y) ∘ z)
abbrev Equation1762 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ y) ∘ w)
abbrev Equation1763 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((x ∘ z) ∘ x)
abbrev Equation1764 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((x ∘ z) ∘ y)
abbrev Equation1765 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((x ∘ z) ∘ z)
abbrev Equation1766 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ z) ∘ w)
abbrev Equation1767 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ x)
abbrev Equation1768 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ y)
abbrev Equation1769 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ z)
abbrev Equation1770 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ w)
abbrev Equation1771 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((x ∘ w) ∘ u)
abbrev Equation1772 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((y ∘ x) ∘ x)
abbrev Equation1773 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((y ∘ x) ∘ y)
abbrev Equation1774 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((y ∘ x) ∘ z)
abbrev Equation1775 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ x) ∘ w)
abbrev Equation1776 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((y ∘ y) ∘ x)
abbrev Equation1777 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((y ∘ y) ∘ y)
abbrev Equation1778 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((y ∘ y) ∘ z)
abbrev Equation1779 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ y) ∘ w)
abbrev Equation1780 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((y ∘ z) ∘ x)
abbrev Equation1781 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((y ∘ z) ∘ y)
abbrev Equation1782 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((y ∘ z) ∘ z)
abbrev Equation1783 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ z) ∘ w)
abbrev Equation1784 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ x)
abbrev Equation1785 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ y)
abbrev Equation1786 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ z)
abbrev Equation1787 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ w)
abbrev Equation1788 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((y ∘ w) ∘ u)
abbrev Equation1789 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ x) ∘ x)
abbrev Equation1790 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ x) ∘ y)
abbrev Equation1791 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ x) ∘ z)
abbrev Equation1792 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ x) ∘ w)
abbrev Equation1793 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ y) ∘ x)
abbrev Equation1794 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ y) ∘ y)
abbrev Equation1795 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ y) ∘ z)
abbrev Equation1796 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ y) ∘ w)
abbrev Equation1797 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ z) ∘ x)
abbrev Equation1798 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ z) ∘ y)
abbrev Equation1799 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ z) ∘ ((z ∘ z) ∘ z)
abbrev Equation1800 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ z) ∘ w)
abbrev Equation1801 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ w) ∘ x)
abbrev Equation1802 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ w) ∘ y)
abbrev Equation1803 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ w) ∘ z)
abbrev Equation1804 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((z ∘ w) ∘ w)
abbrev Equation1805 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((z ∘ w) ∘ u)
abbrev Equation1806 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ x) ∘ x)
abbrev Equation1807 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ x) ∘ y)
abbrev Equation1808 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ x) ∘ z)
abbrev Equation1809 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ x) ∘ w)
abbrev Equation1810 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ x) ∘ u)
abbrev Equation1811 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ y) ∘ x)
abbrev Equation1812 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ y) ∘ y)
abbrev Equation1813 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ y) ∘ z)
abbrev Equation1814 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ y) ∘ w)
abbrev Equation1815 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ y) ∘ u)
abbrev Equation1816 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ z) ∘ x)
abbrev Equation1817 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ z) ∘ y)
abbrev Equation1818 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ z) ∘ z)
abbrev Equation1819 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ z) ∘ w)
abbrev Equation1820 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ z) ∘ u)
abbrev Equation1821 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ w) ∘ x)
abbrev Equation1822 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ w) ∘ y)
abbrev Equation1823 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ w) ∘ z)
abbrev Equation1824 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ z) ∘ ((w ∘ w) ∘ w)
abbrev Equation1825 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ w) ∘ u)
abbrev Equation1826 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ x)
abbrev Equation1827 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ y)
abbrev Equation1828 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ z)
abbrev Equation1829 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ w)
abbrev Equation1830 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ u)
abbrev Equation1831 (G: Type u) [Magma G] := ∀ x y z w u v : G, x = (y ∘ z) ∘ ((w ∘ u) ∘ v)
abbrev Equation1832 (G: Type u) [Magma G] := ∀ x : G, x = (x ∘ (x ∘ x)) ∘ (x ∘ x)
abbrev Equation1833 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ x)) ∘ (x ∘ y)
abbrev Equation1834 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ x)) ∘ (y ∘ x)
abbrev Equation1835 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ x)) ∘ (y ∘ y)
abbrev Equation1836 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ x)) ∘ (y ∘ z)
abbrev Equation1837 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ y)) ∘ (x ∘ x)
abbrev Equation1838 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ y)) ∘ (x ∘ y)
abbrev Equation1839 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ y)) ∘ (x ∘ z)
abbrev Equation1840 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ y)) ∘ (y ∘ x)
abbrev Equation1841 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ y)) ∘ (y ∘ y)
abbrev Equation1842 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ y)) ∘ (y ∘ z)
abbrev Equation1843 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ y)) ∘ (z ∘ x)
abbrev Equation1844 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ y)) ∘ (z ∘ y)
abbrev Equation1845 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ y)) ∘ (z ∘ z)
abbrev Equation1846 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ (x ∘ y)) ∘ (z ∘ w)
abbrev Equation1847 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ x)) ∘ (x ∘ x)
abbrev Equation1848 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ x)) ∘ (x ∘ y)
abbrev Equation1849 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ x)) ∘ (x ∘ z)
abbrev Equation1850 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ x)) ∘ (y ∘ x)
abbrev Equation1851 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ x)) ∘ (y ∘ y)
abbrev Equation1852 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ x)) ∘ (y ∘ z)
abbrev Equation1853 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ x)) ∘ (z ∘ x)
abbrev Equation1854 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ x)) ∘ (z ∘ y)
abbrev Equation1855 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ x)) ∘ (z ∘ z)
abbrev Equation1856 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ x)) ∘ (z ∘ w)
abbrev Equation1857 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ y)) ∘ (x ∘ x)
abbrev Equation1858 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ y)) ∘ (x ∘ y)
abbrev Equation1859 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ y)) ∘ (x ∘ z)
abbrev Equation1860 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ y)) ∘ (y ∘ x)
abbrev Equation1861 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ y)) ∘ (y ∘ y)
abbrev Equation1862 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ y)) ∘ (y ∘ z)
abbrev Equation1863 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ y)) ∘ (z ∘ x)
abbrev Equation1864 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ y)) ∘ (z ∘ y)
abbrev Equation1865 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ y)) ∘ (z ∘ z)
abbrev Equation1866 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ y)) ∘ (z ∘ w)
abbrev Equation1867 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ (x ∘ x)
abbrev Equation1868 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ (x ∘ y)
abbrev Equation1869 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ (x ∘ z)
abbrev Equation1870 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (x ∘ w)
abbrev Equation1871 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ (y ∘ x)
abbrev Equation1872 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ (y ∘ y)
abbrev Equation1873 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ (y ∘ z)
abbrev Equation1874 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (y ∘ w)
abbrev Equation1875 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ (z ∘ x)
abbrev Equation1876 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ (z ∘ y)
abbrev Equation1877 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ z)) ∘ (z ∘ z)
abbrev Equation1878 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (z ∘ w)
abbrev Equation1879 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ x)
abbrev Equation1880 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ y)
abbrev Equation1881 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ z)
abbrev Equation1882 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ w)
abbrev Equation1883 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (x ∘ (y ∘ z)) ∘ (w ∘ u)
abbrev Equation1884 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ x)) ∘ (x ∘ x)
abbrev Equation1885 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ x)) ∘ (x ∘ y)
abbrev Equation1886 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ x)) ∘ (x ∘ z)
abbrev Equation1887 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ x)) ∘ (y ∘ x)
abbrev Equation1888 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ x)) ∘ (y ∘ y)
abbrev Equation1889 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ x)) ∘ (y ∘ z)
abbrev Equation1890 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ x)) ∘ (z ∘ x)
abbrev Equation1891 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ x)) ∘ (z ∘ y)
abbrev Equation1892 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ x)) ∘ (z ∘ z)
abbrev Equation1893 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ x)) ∘ (z ∘ w)
abbrev Equation1894 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ y)) ∘ (x ∘ x)
abbrev Equation1895 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ y)) ∘ (x ∘ y)
abbrev Equation1896 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ y)) ∘ (x ∘ z)
abbrev Equation1897 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ y)) ∘ (y ∘ x)
abbrev Equation1898 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ y)) ∘ (y ∘ y)
abbrev Equation1899 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ y)) ∘ (y ∘ z)
abbrev Equation1900 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ y)) ∘ (z ∘ x)
abbrev Equation1901 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ y)) ∘ (z ∘ y)
abbrev Equation1902 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ y)) ∘ (z ∘ z)
abbrev Equation1903 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ y)) ∘ (z ∘ w)
abbrev Equation1904 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ (x ∘ x)
abbrev Equation1905 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ (x ∘ y)
abbrev Equation1906 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ (x ∘ z)
abbrev Equation1907 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (x ∘ w)
abbrev Equation1908 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ (y ∘ x)
abbrev Equation1909 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ (y ∘ y)
abbrev Equation1910 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ (y ∘ z)
abbrev Equation1911 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (y ∘ w)
abbrev Equation1912 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ (z ∘ x)
abbrev Equation1913 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ (z ∘ y)
abbrev Equation1914 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ z)) ∘ (z ∘ z)
abbrev Equation1915 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (z ∘ w)
abbrev Equation1916 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (w ∘ x)
abbrev Equation1917 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (w ∘ y)
abbrev Equation1918 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (w ∘ z)
abbrev Equation1919 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ z)) ∘ (w ∘ w)
abbrev Equation1920 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (x ∘ z)) ∘ (w ∘ u)
abbrev Equation1921 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ x)) ∘ (x ∘ x)
abbrev Equation1922 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ x)) ∘ (x ∘ y)
abbrev Equation1923 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ x)) ∘ (x ∘ z)
abbrev Equation1924 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ x)) ∘ (y ∘ x)
abbrev Equation1925 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ x)) ∘ (y ∘ y)
abbrev Equation1926 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ x)) ∘ (y ∘ z)
abbrev Equation1927 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ x)) ∘ (z ∘ x)
abbrev Equation1928 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ x)) ∘ (z ∘ y)
abbrev Equation1929 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ x)) ∘ (z ∘ z)
abbrev Equation1930 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ x)) ∘ (z ∘ w)
abbrev Equation1931 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ y)) ∘ (x ∘ x)
abbrev Equation1932 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ y)) ∘ (x ∘ y)
abbrev Equation1933 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ y)) ∘ (x ∘ z)
abbrev Equation1934 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ y)) ∘ (y ∘ x)
abbrev Equation1935 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ y)) ∘ (y ∘ y)
abbrev Equation1936 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ y)) ∘ (y ∘ z)
abbrev Equation1937 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ y)) ∘ (z ∘ x)
abbrev Equation1938 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ y)) ∘ (z ∘ y)
abbrev Equation1939 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ y)) ∘ (z ∘ z)
abbrev Equation1940 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ y)) ∘ (z ∘ w)
abbrev Equation1941 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ (x ∘ x)
abbrev Equation1942 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ (x ∘ y)
abbrev Equation1943 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ (x ∘ z)
abbrev Equation1944 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (x ∘ w)
abbrev Equation1945 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ (y ∘ x)
abbrev Equation1946 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ (y ∘ y)
abbrev Equation1947 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ (y ∘ z)
abbrev Equation1948 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (y ∘ w)
abbrev Equation1949 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ (z ∘ x)
abbrev Equation1950 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ (z ∘ y)
abbrev Equation1951 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ z)) ∘ (z ∘ z)
abbrev Equation1952 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (z ∘ w)
abbrev Equation1953 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (w ∘ x)
abbrev Equation1954 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (w ∘ y)
abbrev Equation1955 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (w ∘ z)
abbrev Equation1956 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ z)) ∘ (w ∘ w)
abbrev Equation1957 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (y ∘ z)) ∘ (w ∘ u)
abbrev Equation1958 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ (x ∘ x)
abbrev Equation1959 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ (x ∘ y)
abbrev Equation1960 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ (x ∘ z)
abbrev Equation1961 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (x ∘ w)
abbrev Equation1962 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ (y ∘ x)
abbrev Equation1963 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ (y ∘ y)
abbrev Equation1964 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ (y ∘ z)
abbrev Equation1965 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (y ∘ w)
abbrev Equation1966 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ (z ∘ x)
abbrev Equation1967 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ (z ∘ y)
abbrev Equation1968 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ x)) ∘ (z ∘ z)
abbrev Equation1969 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (z ∘ w)
abbrev Equation1970 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ x)
abbrev Equation1971 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ y)
abbrev Equation1972 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ z)
abbrev Equation1973 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ w)
abbrev Equation1974 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ x)) ∘ (w ∘ u)
abbrev Equation1975 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ (x ∘ x)
abbrev Equation1976 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ (x ∘ y)
abbrev Equation1977 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ (x ∘ z)
abbrev Equation1978 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (x ∘ w)
abbrev Equation1979 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ (y ∘ x)
abbrev Equation1980 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ (y ∘ y)
abbrev Equation1981 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ (y ∘ z)
abbrev Equation1982 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (y ∘ w)
abbrev Equation1983 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ (z ∘ x)
abbrev Equation1984 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ (z ∘ y)
abbrev Equation1985 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ y)) ∘ (z ∘ z)
abbrev Equation1986 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (z ∘ w)
abbrev Equation1987 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ x)
abbrev Equation1988 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ y)
abbrev Equation1989 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ z)
abbrev Equation1990 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ w)
abbrev Equation1991 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ y)) ∘ (w ∘ u)
abbrev Equation1992 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (x ∘ x)
abbrev Equation1993 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (x ∘ y)
abbrev Equation1994 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (x ∘ z)
abbrev Equation1995 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (x ∘ w)
abbrev Equation1996 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (y ∘ x)
abbrev Equation1997 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (y ∘ y)
abbrev Equation1998 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (y ∘ z)
abbrev Equation1999 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (y ∘ w)
abbrev Equation2000 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (z ∘ x)
abbrev Equation2001 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (z ∘ y)
abbrev Equation2002 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ z)) ∘ (z ∘ z)
abbrev Equation2003 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (z ∘ w)
abbrev Equation2004 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (w ∘ x)
abbrev Equation2005 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (w ∘ y)
abbrev Equation2006 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (w ∘ z)
abbrev Equation2007 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ z)) ∘ (w ∘ w)
abbrev Equation2008 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ z)) ∘ (w ∘ u)
abbrev Equation2009 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (x ∘ x)
abbrev Equation2010 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (x ∘ y)
abbrev Equation2011 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (x ∘ z)
abbrev Equation2012 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (x ∘ w)
abbrev Equation2013 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (x ∘ u)
abbrev Equation2014 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (y ∘ x)
abbrev Equation2015 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (y ∘ y)
abbrev Equation2016 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (y ∘ z)
abbrev Equation2017 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (y ∘ w)
abbrev Equation2018 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (y ∘ u)
abbrev Equation2019 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (z ∘ x)
abbrev Equation2020 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (z ∘ y)
abbrev Equation2021 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (z ∘ z)
abbrev Equation2022 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (z ∘ w)
abbrev Equation2023 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (z ∘ u)
abbrev Equation2024 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (w ∘ x)
abbrev Equation2025 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (w ∘ y)
abbrev Equation2026 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (w ∘ z)
abbrev Equation2027 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ w)) ∘ (w ∘ w)
abbrev Equation2028 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (w ∘ u)
abbrev Equation2029 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ x)
abbrev Equation2030 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ y)
abbrev Equation2031 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ z)
abbrev Equation2032 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ w)
abbrev Equation2033 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ u)
abbrev Equation2034 (G: Type u) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ w)) ∘ (u ∘ v)
abbrev Equation2035 (G: Type u) [Magma G] := ∀ x : G, x = ((x ∘ x) ∘ x) ∘ (x ∘ x)
abbrev Equation2036 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ x) ∘ (x ∘ y)
abbrev Equation2037 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ x) ∘ (y ∘ x)
abbrev Equation2038 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ x) ∘ (y ∘ y)
abbrev Equation2039 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ x) ∘ (y ∘ z)
abbrev Equation2040 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ y) ∘ (x ∘ x)
abbrev Equation2041 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ y) ∘ (x ∘ y)
abbrev Equation2042 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ y) ∘ (x ∘ z)
abbrev Equation2043 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ y) ∘ (y ∘ x)
abbrev Equation2044 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ y) ∘ (y ∘ y)
abbrev Equation2045 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ y) ∘ (y ∘ z)
abbrev Equation2046 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ y) ∘ (z ∘ x)
abbrev Equation2047 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ y) ∘ (z ∘ y)
abbrev Equation2048 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ y) ∘ (z ∘ z)
abbrev Equation2049 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ x) ∘ y) ∘ (z ∘ w)
abbrev Equation2050 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ x) ∘ (x ∘ x)
abbrev Equation2051 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ x) ∘ (x ∘ y)
abbrev Equation2052 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ x) ∘ (x ∘ z)
abbrev Equation2053 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ x) ∘ (y ∘ x)
abbrev Equation2054 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ x) ∘ (y ∘ y)
abbrev Equation2055 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ x) ∘ (y ∘ z)
abbrev Equation2056 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ x) ∘ (z ∘ x)
abbrev Equation2057 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ x) ∘ (z ∘ y)
abbrev Equation2058 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ x) ∘ (z ∘ z)
abbrev Equation2059 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ x) ∘ (z ∘ w)
abbrev Equation2060 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ y) ∘ (x ∘ x)
abbrev Equation2061 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ y) ∘ (x ∘ y)
abbrev Equation2062 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ y) ∘ (x ∘ z)
abbrev Equation2063 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ y) ∘ (y ∘ x)
abbrev Equation2064 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ y) ∘ (y ∘ y)
abbrev Equation2065 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ y) ∘ (y ∘ z)
abbrev Equation2066 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ y) ∘ (z ∘ x)
abbrev Equation2067 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ y) ∘ (z ∘ y)
abbrev Equation2068 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ y) ∘ (z ∘ z)
abbrev Equation2069 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ y) ∘ (z ∘ w)
abbrev Equation2070 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ (x ∘ x)
abbrev Equation2071 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ (x ∘ y)
abbrev Equation2072 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ (x ∘ z)
abbrev Equation2073 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (x ∘ w)
abbrev Equation2074 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ (y ∘ x)
abbrev Equation2075 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ (y ∘ y)
abbrev Equation2076 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ (y ∘ z)
abbrev Equation2077 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (y ∘ w)
abbrev Equation2078 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ (z ∘ x)
abbrev Equation2079 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ (z ∘ y)
abbrev Equation2080 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ z) ∘ (z ∘ z)
abbrev Equation2081 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (z ∘ w)
abbrev Equation2082 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ x)
abbrev Equation2083 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ y)
abbrev Equation2084 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ z)
abbrev Equation2085 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ w)
abbrev Equation2086 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((x ∘ y) ∘ z) ∘ (w ∘ u)
abbrev Equation2087 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ x) ∘ (x ∘ x)
abbrev Equation2088 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ x) ∘ (x ∘ y)
abbrev Equation2089 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ x) ∘ (x ∘ z)
abbrev Equation2090 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ x) ∘ (y ∘ x)
abbrev Equation2091 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ x) ∘ (y ∘ y)
abbrev Equation2092 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ x) ∘ (y ∘ z)
abbrev Equation2093 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ x) ∘ (z ∘ x)
abbrev Equation2094 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ x) ∘ (z ∘ y)
abbrev Equation2095 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ x) ∘ (z ∘ z)
abbrev Equation2096 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ x) ∘ (z ∘ w)
abbrev Equation2097 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ y) ∘ (x ∘ x)
abbrev Equation2098 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ y) ∘ (x ∘ y)
abbrev Equation2099 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ y) ∘ (x ∘ z)
abbrev Equation2100 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ y) ∘ (y ∘ x)
abbrev Equation2101 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ y) ∘ (y ∘ y)
abbrev Equation2102 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ y) ∘ (y ∘ z)
abbrev Equation2103 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ y) ∘ (z ∘ x)
abbrev Equation2104 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ y) ∘ (z ∘ y)
abbrev Equation2105 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ y) ∘ (z ∘ z)
abbrev Equation2106 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ y) ∘ (z ∘ w)
abbrev Equation2107 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ (x ∘ x)
abbrev Equation2108 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ (x ∘ y)
abbrev Equation2109 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ (x ∘ z)
abbrev Equation2110 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (x ∘ w)
abbrev Equation2111 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ (y ∘ x)
abbrev Equation2112 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ (y ∘ y)
abbrev Equation2113 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ (y ∘ z)
abbrev Equation2114 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (y ∘ w)
abbrev Equation2115 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ (z ∘ x)
abbrev Equation2116 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ (z ∘ y)
abbrev Equation2117 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ z) ∘ (z ∘ z)
abbrev Equation2118 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (z ∘ w)
abbrev Equation2119 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (w ∘ x)
abbrev Equation2120 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (w ∘ y)
abbrev Equation2121 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (w ∘ z)
abbrev Equation2122 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ z) ∘ (w ∘ w)
abbrev Equation2123 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ x) ∘ z) ∘ (w ∘ u)
abbrev Equation2124 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ x) ∘ (x ∘ x)
abbrev Equation2125 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ x) ∘ (x ∘ y)
abbrev Equation2126 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ x) ∘ (x ∘ z)
abbrev Equation2127 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ x) ∘ (y ∘ x)
abbrev Equation2128 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ x) ∘ (y ∘ y)
abbrev Equation2129 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ x) ∘ (y ∘ z)
abbrev Equation2130 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ x) ∘ (z ∘ x)
abbrev Equation2131 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ x) ∘ (z ∘ y)
abbrev Equation2132 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ x) ∘ (z ∘ z)
abbrev Equation2133 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ x) ∘ (z ∘ w)
abbrev Equation2134 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ y) ∘ (x ∘ x)
abbrev Equation2135 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ y) ∘ (x ∘ y)
abbrev Equation2136 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ y) ∘ (x ∘ z)
abbrev Equation2137 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ y) ∘ (y ∘ x)
abbrev Equation2138 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ y) ∘ (y ∘ y)
abbrev Equation2139 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ y) ∘ (y ∘ z)
abbrev Equation2140 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ y) ∘ (z ∘ x)
abbrev Equation2141 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ y) ∘ (z ∘ y)
abbrev Equation2142 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ y) ∘ (z ∘ z)
abbrev Equation2143 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ y) ∘ (z ∘ w)
abbrev Equation2144 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ (x ∘ x)
abbrev Equation2145 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ (x ∘ y)
abbrev Equation2146 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ (x ∘ z)
abbrev Equation2147 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (x ∘ w)
abbrev Equation2148 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ (y ∘ x)
abbrev Equation2149 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ (y ∘ y)
abbrev Equation2150 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ (y ∘ z)
abbrev Equation2151 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (y ∘ w)
abbrev Equation2152 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ (z ∘ x)
abbrev Equation2153 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ (z ∘ y)
abbrev Equation2154 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ z) ∘ (z ∘ z)
abbrev Equation2155 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (z ∘ w)
abbrev Equation2156 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (w ∘ x)
abbrev Equation2157 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (w ∘ y)
abbrev Equation2158 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (w ∘ z)
abbrev Equation2159 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ z) ∘ (w ∘ w)
abbrev Equation2160 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ y) ∘ z) ∘ (w ∘ u)
abbrev Equation2161 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ (x ∘ x)
abbrev Equation2162 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ (x ∘ y)
abbrev Equation2163 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ (x ∘ z)
abbrev Equation2164 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (x ∘ w)
abbrev Equation2165 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ (y ∘ x)
abbrev Equation2166 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ (y ∘ y)
abbrev Equation2167 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ (y ∘ z)
abbrev Equation2168 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (y ∘ w)
abbrev Equation2169 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ (z ∘ x)
abbrev Equation2170 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ (z ∘ y)
abbrev Equation2171 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ x) ∘ (z ∘ z)
abbrev Equation2172 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (z ∘ w)
abbrev Equation2173 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ x)
abbrev Equation2174 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ y)
abbrev Equation2175 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ z)
abbrev Equation2176 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ w)
abbrev Equation2177 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ x) ∘ (w ∘ u)
abbrev Equation2178 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ (x ∘ x)
abbrev Equation2179 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ (x ∘ y)
abbrev Equation2180 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ (x ∘ z)
abbrev Equation2181 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (x ∘ w)
abbrev Equation2182 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ (y ∘ x)
abbrev Equation2183 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ (y ∘ y)
abbrev Equation2184 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ (y ∘ z)
abbrev Equation2185 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (y ∘ w)
abbrev Equation2186 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ (z ∘ x)
abbrev Equation2187 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ (z ∘ y)
abbrev Equation2188 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ y) ∘ (z ∘ z)
abbrev Equation2189 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (z ∘ w)
abbrev Equation2190 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ x)
abbrev Equation2191 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ y)
abbrev Equation2192 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ z)
abbrev Equation2193 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ w)
abbrev Equation2194 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ y) ∘ (w ∘ u)
abbrev Equation2195 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (x ∘ x)
abbrev Equation2196 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (x ∘ y)
abbrev Equation2197 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (x ∘ z)
abbrev Equation2198 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (x ∘ w)
abbrev Equation2199 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (y ∘ x)
abbrev Equation2200 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (y ∘ y)
abbrev Equation2201 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (y ∘ z)
abbrev Equation2202 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (y ∘ w)
abbrev Equation2203 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (z ∘ x)
abbrev Equation2204 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (z ∘ y)
abbrev Equation2205 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ z) ∘ (z ∘ z)
abbrev Equation2206 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (z ∘ w)
abbrev Equation2207 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (w ∘ x)
abbrev Equation2208 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (w ∘ y)
abbrev Equation2209 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (w ∘ z)
abbrev Equation2210 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ z) ∘ (w ∘ w)
abbrev Equation2211 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ z) ∘ (w ∘ u)
abbrev Equation2212 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (x ∘ x)
abbrev Equation2213 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (x ∘ y)
abbrev Equation2214 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (x ∘ z)
abbrev Equation2215 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (x ∘ w)
abbrev Equation2216 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (x ∘ u)
abbrev Equation2217 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (y ∘ x)
abbrev Equation2218 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (y ∘ y)
abbrev Equation2219 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (y ∘ z)
abbrev Equation2220 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (y ∘ w)
abbrev Equation2221 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (y ∘ u)
abbrev Equation2222 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (z ∘ x)
abbrev Equation2223 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (z ∘ y)
abbrev Equation2224 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (z ∘ z)
abbrev Equation2225 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (z ∘ w)
abbrev Equation2226 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (z ∘ u)
abbrev Equation2227 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (w ∘ x)
abbrev Equation2228 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (w ∘ y)
abbrev Equation2229 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (w ∘ z)
abbrev Equation2230 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ w) ∘ (w ∘ w)
abbrev Equation2231 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (w ∘ u)
abbrev Equation2232 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ x)
abbrev Equation2233 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ y)
abbrev Equation2234 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ z)
abbrev Equation2235 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ w)
abbrev Equation2236 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ u)
abbrev Equation2237 (G: Type u) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ w) ∘ (u ∘ v)
abbrev Equation2238 (G: Type u) [Magma G] := ∀ x : G, x = (x ∘ (x ∘ (x ∘ x))) ∘ x
abbrev Equation2239 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ (x ∘ x))) ∘ y
abbrev Equation2240 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ (x ∘ y))) ∘ x
abbrev Equation2241 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ (x ∘ y))) ∘ y
abbrev Equation2242 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ (x ∘ y))) ∘ z
abbrev Equation2243 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ (y ∘ x))) ∘ x
abbrev Equation2244 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ (y ∘ x))) ∘ y
abbrev Equation2245 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ (y ∘ x))) ∘ z
abbrev Equation2246 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ (y ∘ y))) ∘ x
abbrev Equation2247 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (x ∘ (y ∘ y))) ∘ y
abbrev Equation2248 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ (y ∘ y))) ∘ z
abbrev Equation2249 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ (y ∘ z))) ∘ x
abbrev Equation2250 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ (y ∘ z))) ∘ y
abbrev Equation2251 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (x ∘ (y ∘ z))) ∘ z
abbrev Equation2252 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ (x ∘ (y ∘ z))) ∘ w
abbrev Equation2253 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ (x ∘ x))) ∘ x
abbrev Equation2254 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ (x ∘ x))) ∘ y
abbrev Equation2255 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (x ∘ x))) ∘ z
abbrev Equation2256 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ (x ∘ y))) ∘ x
abbrev Equation2257 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ (x ∘ y))) ∘ y
abbrev Equation2258 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (x ∘ y))) ∘ z
abbrev Equation2259 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (x ∘ z))) ∘ x
abbrev Equation2260 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (x ∘ z))) ∘ y
abbrev Equation2261 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (x ∘ z))) ∘ z
abbrev Equation2262 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (x ∘ z))) ∘ w
abbrev Equation2263 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ (y ∘ x))) ∘ x
abbrev Equation2264 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ (y ∘ x))) ∘ y
abbrev Equation2265 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (y ∘ x))) ∘ z
abbrev Equation2266 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ (y ∘ y))) ∘ x
abbrev Equation2267 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ (y ∘ (y ∘ y))) ∘ y
abbrev Equation2268 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (y ∘ y))) ∘ z
abbrev Equation2269 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (y ∘ z))) ∘ x
abbrev Equation2270 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (y ∘ z))) ∘ y
abbrev Equation2271 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (y ∘ z))) ∘ z
abbrev Equation2272 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (y ∘ z))) ∘ w
abbrev Equation2273 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (z ∘ x))) ∘ x
abbrev Equation2274 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (z ∘ x))) ∘ y
abbrev Equation2275 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (z ∘ x))) ∘ z
abbrev Equation2276 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ x))) ∘ w
abbrev Equation2277 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (z ∘ y))) ∘ x
abbrev Equation2278 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (z ∘ y))) ∘ y
abbrev Equation2279 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (z ∘ y))) ∘ z
abbrev Equation2280 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ y))) ∘ w
abbrev Equation2281 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (z ∘ z))) ∘ x
abbrev Equation2282 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (z ∘ z))) ∘ y
abbrev Equation2283 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ (y ∘ (z ∘ z))) ∘ z
abbrev Equation2284 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ z))) ∘ w
abbrev Equation2285 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ x
abbrev Equation2286 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ y
abbrev Equation2287 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ z
abbrev Equation2288 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ w
abbrev Equation2289 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (x ∘ (y ∘ (z ∘ w))) ∘ u
abbrev Equation2290 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (x ∘ x))) ∘ x
abbrev Equation2291 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (x ∘ x))) ∘ y
abbrev Equation2292 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (x ∘ x))) ∘ z
abbrev Equation2293 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (x ∘ y))) ∘ x
abbrev Equation2294 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (x ∘ y))) ∘ y
abbrev Equation2295 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (x ∘ y))) ∘ z
abbrev Equation2296 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (x ∘ z))) ∘ x
abbrev Equation2297 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (x ∘ z))) ∘ y
abbrev Equation2298 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (x ∘ z))) ∘ z
abbrev Equation2299 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (x ∘ z))) ∘ w
abbrev Equation2300 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (y ∘ x))) ∘ x
abbrev Equation2301 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (y ∘ x))) ∘ y
abbrev Equation2302 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (y ∘ x))) ∘ z
abbrev Equation2303 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (y ∘ y))) ∘ x
abbrev Equation2304 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (x ∘ (y ∘ y))) ∘ y
abbrev Equation2305 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (y ∘ y))) ∘ z
abbrev Equation2306 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (y ∘ z))) ∘ x
abbrev Equation2307 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (y ∘ z))) ∘ y
abbrev Equation2308 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (y ∘ z))) ∘ z
abbrev Equation2309 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (y ∘ z))) ∘ w
abbrev Equation2310 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (z ∘ x))) ∘ x
abbrev Equation2311 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (z ∘ x))) ∘ y
abbrev Equation2312 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (z ∘ x))) ∘ z
abbrev Equation2313 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ x))) ∘ w
abbrev Equation2314 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (z ∘ y))) ∘ x
abbrev Equation2315 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (z ∘ y))) ∘ y
abbrev Equation2316 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (z ∘ y))) ∘ z
abbrev Equation2317 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ y))) ∘ w
abbrev Equation2318 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (z ∘ z))) ∘ x
abbrev Equation2319 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (z ∘ z))) ∘ y
abbrev Equation2320 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (x ∘ (z ∘ z))) ∘ z
abbrev Equation2321 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ z))) ∘ w
abbrev Equation2322 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ w))) ∘ x
abbrev Equation2323 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ w))) ∘ y
abbrev Equation2324 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ w))) ∘ z
abbrev Equation2325 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (x ∘ (z ∘ w))) ∘ w
abbrev Equation2326 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (x ∘ (z ∘ w))) ∘ u
abbrev Equation2327 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ (x ∘ x))) ∘ x
abbrev Equation2328 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ (x ∘ x))) ∘ y
abbrev Equation2329 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (x ∘ x))) ∘ z
abbrev Equation2330 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ (x ∘ y))) ∘ x
abbrev Equation2331 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ (x ∘ y))) ∘ y
abbrev Equation2332 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (x ∘ y))) ∘ z
abbrev Equation2333 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (x ∘ z))) ∘ x
abbrev Equation2334 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (x ∘ z))) ∘ y
abbrev Equation2335 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (x ∘ z))) ∘ z
abbrev Equation2336 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (x ∘ z))) ∘ w
abbrev Equation2337 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ (y ∘ x))) ∘ x
abbrev Equation2338 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ (y ∘ x))) ∘ y
abbrev Equation2339 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (y ∘ x))) ∘ z
abbrev Equation2340 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ (y ∘ y))) ∘ x
abbrev Equation2341 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ (y ∘ (y ∘ y))) ∘ y
abbrev Equation2342 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (y ∘ y))) ∘ z
abbrev Equation2343 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (y ∘ z))) ∘ x
abbrev Equation2344 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (y ∘ z))) ∘ y
abbrev Equation2345 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (y ∘ z))) ∘ z
abbrev Equation2346 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (y ∘ z))) ∘ w
abbrev Equation2347 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (z ∘ x))) ∘ x
abbrev Equation2348 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (z ∘ x))) ∘ y
abbrev Equation2349 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (z ∘ x))) ∘ z
abbrev Equation2350 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ x))) ∘ w
abbrev Equation2351 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (z ∘ y))) ∘ x
abbrev Equation2352 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (z ∘ y))) ∘ y
abbrev Equation2353 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (z ∘ y))) ∘ z
abbrev Equation2354 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ y))) ∘ w
abbrev Equation2355 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (z ∘ z))) ∘ x
abbrev Equation2356 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (z ∘ z))) ∘ y
abbrev Equation2357 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (y ∘ (z ∘ z))) ∘ z
abbrev Equation2358 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ z))) ∘ w
abbrev Equation2359 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ w))) ∘ x
abbrev Equation2360 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ w))) ∘ y
abbrev Equation2361 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ w))) ∘ z
abbrev Equation2362 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (y ∘ (z ∘ w))) ∘ w
abbrev Equation2363 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (y ∘ (z ∘ w))) ∘ u
abbrev Equation2364 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (x ∘ x))) ∘ x
abbrev Equation2365 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (x ∘ x))) ∘ y
abbrev Equation2366 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (x ∘ x))) ∘ z
abbrev Equation2367 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ x))) ∘ w
abbrev Equation2368 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (x ∘ y))) ∘ x
abbrev Equation2369 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (x ∘ y))) ∘ y
abbrev Equation2370 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (x ∘ y))) ∘ z
abbrev Equation2371 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ y))) ∘ w
abbrev Equation2372 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (x ∘ z))) ∘ x
abbrev Equation2373 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (x ∘ z))) ∘ y
abbrev Equation2374 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (x ∘ z))) ∘ z
abbrev Equation2375 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ z))) ∘ w
abbrev Equation2376 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ x
abbrev Equation2377 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ y
abbrev Equation2378 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ z
abbrev Equation2379 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ w
abbrev Equation2380 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (x ∘ w))) ∘ u
abbrev Equation2381 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (y ∘ x))) ∘ x
abbrev Equation2382 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (y ∘ x))) ∘ y
abbrev Equation2383 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (y ∘ x))) ∘ z
abbrev Equation2384 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ x))) ∘ w
abbrev Equation2385 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (y ∘ y))) ∘ x
abbrev Equation2386 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (y ∘ y))) ∘ y
abbrev Equation2387 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (y ∘ y))) ∘ z
abbrev Equation2388 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ y))) ∘ w
abbrev Equation2389 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (y ∘ z))) ∘ x
abbrev Equation2390 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (y ∘ z))) ∘ y
abbrev Equation2391 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (y ∘ z))) ∘ z
abbrev Equation2392 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ z))) ∘ w
abbrev Equation2393 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ x
abbrev Equation2394 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ y
abbrev Equation2395 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ z
abbrev Equation2396 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ w
abbrev Equation2397 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (y ∘ w))) ∘ u
abbrev Equation2398 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ x))) ∘ x
abbrev Equation2399 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ x))) ∘ y
abbrev Equation2400 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ x))) ∘ z
abbrev Equation2401 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ x))) ∘ w
abbrev Equation2402 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ y))) ∘ x
abbrev Equation2403 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ y))) ∘ y
abbrev Equation2404 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ y))) ∘ z
abbrev Equation2405 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ y))) ∘ w
abbrev Equation2406 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ z))) ∘ x
abbrev Equation2407 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ z))) ∘ y
abbrev Equation2408 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ (z ∘ (z ∘ z))) ∘ z
abbrev Equation2409 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ z))) ∘ w
abbrev Equation2410 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ w))) ∘ x
abbrev Equation2411 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ w))) ∘ y
abbrev Equation2412 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ w))) ∘ z
abbrev Equation2413 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (z ∘ w))) ∘ w
abbrev Equation2414 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (z ∘ w))) ∘ u
abbrev Equation2415 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ x))) ∘ x
abbrev Equation2416 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ x))) ∘ y
abbrev Equation2417 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ x))) ∘ z
abbrev Equation2418 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ x))) ∘ w
abbrev Equation2419 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ x))) ∘ u
abbrev Equation2420 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ y))) ∘ x
abbrev Equation2421 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ y))) ∘ y
abbrev Equation2422 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ y))) ∘ z
abbrev Equation2423 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ y))) ∘ w
abbrev Equation2424 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ y))) ∘ u
abbrev Equation2425 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ z))) ∘ x
abbrev Equation2426 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ z))) ∘ y
abbrev Equation2427 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ z))) ∘ z
abbrev Equation2428 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ z))) ∘ w
abbrev Equation2429 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ z))) ∘ u
abbrev Equation2430 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ w))) ∘ x
abbrev Equation2431 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ w))) ∘ y
abbrev Equation2432 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ w))) ∘ z
abbrev Equation2433 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ (z ∘ (w ∘ w))) ∘ w
abbrev Equation2434 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ w))) ∘ u
abbrev Equation2435 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ x
abbrev Equation2436 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ y
abbrev Equation2437 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ z
abbrev Equation2438 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ w
abbrev Equation2439 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ u
abbrev Equation2440 (G: Type u) [Magma G] := ∀ x y z w u v : G, x = (y ∘ (z ∘ (w ∘ u))) ∘ v
abbrev Equation2441 (G: Type u) [Magma G] := ∀ x : G, x = (x ∘ ((x ∘ x) ∘ x)) ∘ x
abbrev Equation2442 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ ((x ∘ x) ∘ x)) ∘ y
abbrev Equation2443 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ ((x ∘ x) ∘ y)) ∘ x
abbrev Equation2444 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ ((x ∘ x) ∘ y)) ∘ y
abbrev Equation2445 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ ((x ∘ x) ∘ y)) ∘ z
abbrev Equation2446 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ ((x ∘ y) ∘ x)) ∘ x
abbrev Equation2447 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ ((x ∘ y) ∘ x)) ∘ y
abbrev Equation2448 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ ((x ∘ y) ∘ x)) ∘ z
abbrev Equation2449 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ ((x ∘ y) ∘ y)) ∘ x
abbrev Equation2450 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ ((x ∘ y) ∘ y)) ∘ y
abbrev Equation2451 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ ((x ∘ y) ∘ y)) ∘ z
abbrev Equation2452 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ ((x ∘ y) ∘ z)) ∘ x
abbrev Equation2453 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ ((x ∘ y) ∘ z)) ∘ y
abbrev Equation2454 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ ((x ∘ y) ∘ z)) ∘ z
abbrev Equation2455 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ ((x ∘ y) ∘ z)) ∘ w
abbrev Equation2456 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ ((y ∘ x) ∘ x)) ∘ x
abbrev Equation2457 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ ((y ∘ x) ∘ x)) ∘ y
abbrev Equation2458 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ x) ∘ x)) ∘ z
abbrev Equation2459 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ ((y ∘ x) ∘ y)) ∘ x
abbrev Equation2460 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ ((y ∘ x) ∘ y)) ∘ y
abbrev Equation2461 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ x) ∘ y)) ∘ z
abbrev Equation2462 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ x) ∘ z)) ∘ x
abbrev Equation2463 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ x) ∘ z)) ∘ y
abbrev Equation2464 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ x) ∘ z)) ∘ z
abbrev Equation2465 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ x) ∘ z)) ∘ w
abbrev Equation2466 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ ((y ∘ y) ∘ x)) ∘ x
abbrev Equation2467 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ ((y ∘ y) ∘ x)) ∘ y
abbrev Equation2468 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ y) ∘ x)) ∘ z
abbrev Equation2469 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ ((y ∘ y) ∘ y)) ∘ x
abbrev Equation2470 (G: Type u) [Magma G] := ∀ x y : G, x = (x ∘ ((y ∘ y) ∘ y)) ∘ y
abbrev Equation2471 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ y) ∘ y)) ∘ z
abbrev Equation2472 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ y) ∘ z)) ∘ x
abbrev Equation2473 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ y) ∘ z)) ∘ y
abbrev Equation2474 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ y) ∘ z)) ∘ z
abbrev Equation2475 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ y) ∘ z)) ∘ w
abbrev Equation2476 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ z) ∘ x)) ∘ x
abbrev Equation2477 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ z) ∘ x)) ∘ y
abbrev Equation2478 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ z) ∘ x)) ∘ z
abbrev Equation2479 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ x)) ∘ w
abbrev Equation2480 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ z) ∘ y)) ∘ x
abbrev Equation2481 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ z) ∘ y)) ∘ y
abbrev Equation2482 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ z) ∘ y)) ∘ z
abbrev Equation2483 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ y)) ∘ w
abbrev Equation2484 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ z) ∘ z)) ∘ x
abbrev Equation2485 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ z) ∘ z)) ∘ y
abbrev Equation2486 (G: Type u) [Magma G] := ∀ x y z : G, x = (x ∘ ((y ∘ z) ∘ z)) ∘ z
abbrev Equation2487 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ z)) ∘ w
abbrev Equation2488 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ x
abbrev Equation2489 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ y
abbrev Equation2490 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ z
abbrev Equation2491 (G: Type u) [Magma G] := ∀ x y z w : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ w
abbrev Equation2492 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (x ∘ ((y ∘ z) ∘ w)) ∘ u
abbrev Equation2493 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ x) ∘ x)) ∘ x
abbrev Equation2494 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ x) ∘ x)) ∘ y
abbrev Equation2495 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ x) ∘ x)) ∘ z
abbrev Equation2496 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ x) ∘ y)) ∘ x
abbrev Equation2497 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ x) ∘ y)) ∘ y
abbrev Equation2498 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ x) ∘ y)) ∘ z
abbrev Equation2499 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ x) ∘ z)) ∘ x
abbrev Equation2500 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ x) ∘ z)) ∘ y
abbrev Equation2501 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ x) ∘ z)) ∘ z
abbrev Equation2502 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ x) ∘ z)) ∘ w
abbrev Equation2503 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ y) ∘ x)) ∘ x
abbrev Equation2504 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ y) ∘ x)) ∘ y
abbrev Equation2505 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ y) ∘ x)) ∘ z
abbrev Equation2506 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ y) ∘ y)) ∘ x
abbrev Equation2507 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ ((x ∘ y) ∘ y)) ∘ y
abbrev Equation2508 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ y) ∘ y)) ∘ z
abbrev Equation2509 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ y) ∘ z)) ∘ x
abbrev Equation2510 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ y) ∘ z)) ∘ y
abbrev Equation2511 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ y) ∘ z)) ∘ z
abbrev Equation2512 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ y) ∘ z)) ∘ w
abbrev Equation2513 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ z) ∘ x)) ∘ x
abbrev Equation2514 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ z) ∘ x)) ∘ y
abbrev Equation2515 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ z) ∘ x)) ∘ z
abbrev Equation2516 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ x)) ∘ w
abbrev Equation2517 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ z) ∘ y)) ∘ x
abbrev Equation2518 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ z) ∘ y)) ∘ y
abbrev Equation2519 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ z) ∘ y)) ∘ z
abbrev Equation2520 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ y)) ∘ w
abbrev Equation2521 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ z) ∘ z)) ∘ x
abbrev Equation2522 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ z) ∘ z)) ∘ y
abbrev Equation2523 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((x ∘ z) ∘ z)) ∘ z
abbrev Equation2524 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ z)) ∘ w
abbrev Equation2525 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ w)) ∘ x
abbrev Equation2526 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ w)) ∘ y
abbrev Equation2527 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ w)) ∘ z
abbrev Equation2528 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((x ∘ z) ∘ w)) ∘ w
abbrev Equation2529 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((x ∘ z) ∘ w)) ∘ u
abbrev Equation2530 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ ((y ∘ x) ∘ x)) ∘ x
abbrev Equation2531 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ ((y ∘ x) ∘ x)) ∘ y
abbrev Equation2532 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ x) ∘ x)) ∘ z
abbrev Equation2533 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ ((y ∘ x) ∘ y)) ∘ x
abbrev Equation2534 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ ((y ∘ x) ∘ y)) ∘ y
abbrev Equation2535 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ x) ∘ y)) ∘ z
abbrev Equation2536 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ x) ∘ z)) ∘ x
abbrev Equation2537 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ x) ∘ z)) ∘ y
abbrev Equation2538 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ x) ∘ z)) ∘ z
abbrev Equation2539 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ x) ∘ z)) ∘ w
abbrev Equation2540 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ ((y ∘ y) ∘ x)) ∘ x
abbrev Equation2541 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ ((y ∘ y) ∘ x)) ∘ y
abbrev Equation2542 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ y) ∘ x)) ∘ z
abbrev Equation2543 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ ((y ∘ y) ∘ y)) ∘ x
abbrev Equation2544 (G: Type u) [Magma G] := ∀ x y : G, x = (y ∘ ((y ∘ y) ∘ y)) ∘ y
abbrev Equation2545 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ y) ∘ y)) ∘ z
abbrev Equation2546 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ y) ∘ z)) ∘ x
abbrev Equation2547 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ y) ∘ z)) ∘ y
abbrev Equation2548 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ y) ∘ z)) ∘ z
abbrev Equation2549 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ y) ∘ z)) ∘ w
abbrev Equation2550 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ z) ∘ x)) ∘ x
abbrev Equation2551 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ z) ∘ x)) ∘ y
abbrev Equation2552 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ z) ∘ x)) ∘ z
abbrev Equation2553 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ x)) ∘ w
abbrev Equation2554 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ z) ∘ y)) ∘ x
abbrev Equation2555 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ z) ∘ y)) ∘ y
abbrev Equation2556 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ z) ∘ y)) ∘ z
abbrev Equation2557 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ y)) ∘ w
abbrev Equation2558 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ z) ∘ z)) ∘ x
abbrev Equation2559 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ z) ∘ z)) ∘ y
abbrev Equation2560 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((y ∘ z) ∘ z)) ∘ z
abbrev Equation2561 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ z)) ∘ w
abbrev Equation2562 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ w)) ∘ x
abbrev Equation2563 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ w)) ∘ y
abbrev Equation2564 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ w)) ∘ z
abbrev Equation2565 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((y ∘ z) ∘ w)) ∘ w
abbrev Equation2566 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((y ∘ z) ∘ w)) ∘ u
abbrev Equation2567 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ x) ∘ x)) ∘ x
abbrev Equation2568 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ x) ∘ x)) ∘ y
abbrev Equation2569 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ x) ∘ x)) ∘ z
abbrev Equation2570 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ x)) ∘ w
abbrev Equation2571 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ x) ∘ y)) ∘ x
abbrev Equation2572 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ x) ∘ y)) ∘ y
abbrev Equation2573 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ x) ∘ y)) ∘ z
abbrev Equation2574 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ y)) ∘ w
abbrev Equation2575 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ x) ∘ z)) ∘ x
abbrev Equation2576 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ x) ∘ z)) ∘ y
abbrev Equation2577 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ x) ∘ z)) ∘ z
abbrev Equation2578 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ z)) ∘ w
abbrev Equation2579 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ x
abbrev Equation2580 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ y
abbrev Equation2581 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ z
abbrev Equation2582 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ w
abbrev Equation2583 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ x) ∘ w)) ∘ u
abbrev Equation2584 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ y) ∘ x)) ∘ x
abbrev Equation2585 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ y) ∘ x)) ∘ y
abbrev Equation2586 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ y) ∘ x)) ∘ z
abbrev Equation2587 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ x)) ∘ w
abbrev Equation2588 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ y) ∘ y)) ∘ x
abbrev Equation2589 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ y) ∘ y)) ∘ y
abbrev Equation2590 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ y) ∘ y)) ∘ z
abbrev Equation2591 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ y)) ∘ w
abbrev Equation2592 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ y) ∘ z)) ∘ x
abbrev Equation2593 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ y) ∘ z)) ∘ y
abbrev Equation2594 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ y) ∘ z)) ∘ z
abbrev Equation2595 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ z)) ∘ w
abbrev Equation2596 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ x
abbrev Equation2597 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ y
abbrev Equation2598 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ z
abbrev Equation2599 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ w
abbrev Equation2600 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ y) ∘ w)) ∘ u
abbrev Equation2601 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ x)) ∘ x
abbrev Equation2602 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ x)) ∘ y
abbrev Equation2603 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ x)) ∘ z
abbrev Equation2604 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ x)) ∘ w
abbrev Equation2605 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ y)) ∘ x
abbrev Equation2606 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ y)) ∘ y
abbrev Equation2607 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ y)) ∘ z
abbrev Equation2608 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ y)) ∘ w
abbrev Equation2609 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ z)) ∘ x
abbrev Equation2610 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ z)) ∘ y
abbrev Equation2611 (G: Type u) [Magma G] := ∀ x y z : G, x = (y ∘ ((z ∘ z) ∘ z)) ∘ z
abbrev Equation2612 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ z)) ∘ w
abbrev Equation2613 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ w)) ∘ x
abbrev Equation2614 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ w)) ∘ y
abbrev Equation2615 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ w)) ∘ z
abbrev Equation2616 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ z) ∘ w)) ∘ w
abbrev Equation2617 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ z) ∘ w)) ∘ u
abbrev Equation2618 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ x)) ∘ x
abbrev Equation2619 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ x)) ∘ y
abbrev Equation2620 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ x)) ∘ z
abbrev Equation2621 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ x)) ∘ w
abbrev Equation2622 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ x)) ∘ u
abbrev Equation2623 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ y)) ∘ x
abbrev Equation2624 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ y)) ∘ y
abbrev Equation2625 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ y)) ∘ z
abbrev Equation2626 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ y)) ∘ w
abbrev Equation2627 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ y)) ∘ u
abbrev Equation2628 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ z)) ∘ x
abbrev Equation2629 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ z)) ∘ y
abbrev Equation2630 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ z)) ∘ z
abbrev Equation2631 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ z)) ∘ w
abbrev Equation2632 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ z)) ∘ u
abbrev Equation2633 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ w)) ∘ x
abbrev Equation2634 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ w)) ∘ y
abbrev Equation2635 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ w)) ∘ z
abbrev Equation2636 (G: Type u) [Magma G] := ∀ x y z w : G, x = (y ∘ ((z ∘ w) ∘ w)) ∘ w
abbrev Equation2637 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ w)) ∘ u
abbrev Equation2638 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ x
abbrev Equation2639 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ y
abbrev Equation2640 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ z
abbrev Equation2641 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ w
abbrev Equation2642 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ u
abbrev Equation2643 (G: Type u) [Magma G] := ∀ x y z w u v : G, x = (y ∘ ((z ∘ w) ∘ u)) ∘ v
abbrev Equation2644 (G: Type u) [Magma G] := ∀ x : G, x = ((x ∘ x) ∘ (x ∘ x)) ∘ x
abbrev Equation2645 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ (x ∘ x)) ∘ y
abbrev Equation2646 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ (x ∘ y)) ∘ x
abbrev Equation2647 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ (x ∘ y)) ∘ y
abbrev Equation2648 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ (x ∘ y)) ∘ z
abbrev Equation2649 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ (y ∘ x)) ∘ x
abbrev Equation2650 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ (y ∘ x)) ∘ y
abbrev Equation2651 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ (y ∘ x)) ∘ z
abbrev Equation2652 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ (y ∘ y)) ∘ x
abbrev Equation2653 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ x) ∘ (y ∘ y)) ∘ y
abbrev Equation2654 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ (y ∘ y)) ∘ z
abbrev Equation2655 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ (y ∘ z)) ∘ x
abbrev Equation2656 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ (y ∘ z)) ∘ y
abbrev Equation2657 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ x) ∘ (y ∘ z)) ∘ z
abbrev Equation2658 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ x) ∘ (y ∘ z)) ∘ w
abbrev Equation2659 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ (x ∘ x)) ∘ x
abbrev Equation2660 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ (x ∘ x)) ∘ y
abbrev Equation2661 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (x ∘ x)) ∘ z
abbrev Equation2662 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ (x ∘ y)) ∘ x
abbrev Equation2663 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ (x ∘ y)) ∘ y
abbrev Equation2664 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (x ∘ y)) ∘ z
abbrev Equation2665 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (x ∘ z)) ∘ x
abbrev Equation2666 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (x ∘ z)) ∘ y
abbrev Equation2667 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (x ∘ z)) ∘ z
abbrev Equation2668 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (x ∘ z)) ∘ w
abbrev Equation2669 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ (y ∘ x)) ∘ x
abbrev Equation2670 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ (y ∘ x)) ∘ y
abbrev Equation2671 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (y ∘ x)) ∘ z
abbrev Equation2672 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ (y ∘ y)) ∘ x
abbrev Equation2673 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ y) ∘ (y ∘ y)) ∘ y
abbrev Equation2674 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (y ∘ y)) ∘ z
abbrev Equation2675 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (y ∘ z)) ∘ x
abbrev Equation2676 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (y ∘ z)) ∘ y
abbrev Equation2677 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (y ∘ z)) ∘ z
abbrev Equation2678 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (y ∘ z)) ∘ w
abbrev Equation2679 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (z ∘ x)) ∘ x
abbrev Equation2680 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (z ∘ x)) ∘ y
abbrev Equation2681 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (z ∘ x)) ∘ z
abbrev Equation2682 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ x)) ∘ w
abbrev Equation2683 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (z ∘ y)) ∘ x
abbrev Equation2684 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (z ∘ y)) ∘ y
abbrev Equation2685 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (z ∘ y)) ∘ z
abbrev Equation2686 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ y)) ∘ w
abbrev Equation2687 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (z ∘ z)) ∘ x
abbrev Equation2688 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (z ∘ z)) ∘ y
abbrev Equation2689 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ y) ∘ (z ∘ z)) ∘ z
abbrev Equation2690 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ z)) ∘ w
abbrev Equation2691 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ x
abbrev Equation2692 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ y
abbrev Equation2693 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ z
abbrev Equation2694 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ w
abbrev Equation2695 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((x ∘ y) ∘ (z ∘ w)) ∘ u
abbrev Equation2696 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (x ∘ x)) ∘ x
abbrev Equation2697 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (x ∘ x)) ∘ y
abbrev Equation2698 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (x ∘ x)) ∘ z
abbrev Equation2699 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (x ∘ y)) ∘ x
abbrev Equation2700 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (x ∘ y)) ∘ y
abbrev Equation2701 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (x ∘ y)) ∘ z
abbrev Equation2702 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (x ∘ z)) ∘ x
abbrev Equation2703 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (x ∘ z)) ∘ y
abbrev Equation2704 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (x ∘ z)) ∘ z
abbrev Equation2705 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (x ∘ z)) ∘ w
abbrev Equation2706 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (y ∘ x)) ∘ x
abbrev Equation2707 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (y ∘ x)) ∘ y
abbrev Equation2708 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (y ∘ x)) ∘ z
abbrev Equation2709 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (y ∘ y)) ∘ x
abbrev Equation2710 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ x) ∘ (y ∘ y)) ∘ y
abbrev Equation2711 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (y ∘ y)) ∘ z
abbrev Equation2712 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (y ∘ z)) ∘ x
abbrev Equation2713 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (y ∘ z)) ∘ y
abbrev Equation2714 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (y ∘ z)) ∘ z
abbrev Equation2715 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (y ∘ z)) ∘ w
abbrev Equation2716 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (z ∘ x)) ∘ x
abbrev Equation2717 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (z ∘ x)) ∘ y
abbrev Equation2718 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (z ∘ x)) ∘ z
abbrev Equation2719 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ x)) ∘ w
abbrev Equation2720 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (z ∘ y)) ∘ x
abbrev Equation2721 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (z ∘ y)) ∘ y
abbrev Equation2722 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (z ∘ y)) ∘ z
abbrev Equation2723 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ y)) ∘ w
abbrev Equation2724 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (z ∘ z)) ∘ x
abbrev Equation2725 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (z ∘ z)) ∘ y
abbrev Equation2726 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ x) ∘ (z ∘ z)) ∘ z
abbrev Equation2727 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ z)) ∘ w
abbrev Equation2728 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ w)) ∘ x
abbrev Equation2729 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ w)) ∘ y
abbrev Equation2730 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ w)) ∘ z
abbrev Equation2731 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ x) ∘ (z ∘ w)) ∘ w
abbrev Equation2732 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ x) ∘ (z ∘ w)) ∘ u
abbrev Equation2733 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ (x ∘ x)) ∘ x
abbrev Equation2734 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ (x ∘ x)) ∘ y
abbrev Equation2735 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (x ∘ x)) ∘ z
abbrev Equation2736 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ (x ∘ y)) ∘ x
abbrev Equation2737 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ (x ∘ y)) ∘ y
abbrev Equation2738 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (x ∘ y)) ∘ z
abbrev Equation2739 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (x ∘ z)) ∘ x
abbrev Equation2740 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (x ∘ z)) ∘ y
abbrev Equation2741 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (x ∘ z)) ∘ z
abbrev Equation2742 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (x ∘ z)) ∘ w
abbrev Equation2743 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ (y ∘ x)) ∘ x
abbrev Equation2744 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ (y ∘ x)) ∘ y
abbrev Equation2745 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (y ∘ x)) ∘ z
abbrev Equation2746 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ (y ∘ y)) ∘ x
abbrev Equation2747 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ y) ∘ (y ∘ y)) ∘ y
abbrev Equation2748 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (y ∘ y)) ∘ z
abbrev Equation2749 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (y ∘ z)) ∘ x
abbrev Equation2750 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (y ∘ z)) ∘ y
abbrev Equation2751 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (y ∘ z)) ∘ z
abbrev Equation2752 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (y ∘ z)) ∘ w
abbrev Equation2753 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (z ∘ x)) ∘ x
abbrev Equation2754 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (z ∘ x)) ∘ y
abbrev Equation2755 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (z ∘ x)) ∘ z
abbrev Equation2756 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ x)) ∘ w
abbrev Equation2757 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (z ∘ y)) ∘ x
abbrev Equation2758 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (z ∘ y)) ∘ y
abbrev Equation2759 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (z ∘ y)) ∘ z
abbrev Equation2760 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ y)) ∘ w
abbrev Equation2761 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (z ∘ z)) ∘ x
abbrev Equation2762 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (z ∘ z)) ∘ y
abbrev Equation2763 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ y) ∘ (z ∘ z)) ∘ z
abbrev Equation2764 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ z)) ∘ w
abbrev Equation2765 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ w)) ∘ x
abbrev Equation2766 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ w)) ∘ y
abbrev Equation2767 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ w)) ∘ z
abbrev Equation2768 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ y) ∘ (z ∘ w)) ∘ w
abbrev Equation2769 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ y) ∘ (z ∘ w)) ∘ u
abbrev Equation2770 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (x ∘ x)) ∘ x
abbrev Equation2771 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (x ∘ x)) ∘ y
abbrev Equation2772 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (x ∘ x)) ∘ z
abbrev Equation2773 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ x)) ∘ w
abbrev Equation2774 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (x ∘ y)) ∘ x
abbrev Equation2775 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (x ∘ y)) ∘ y
abbrev Equation2776 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (x ∘ y)) ∘ z
abbrev Equation2777 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ y)) ∘ w
abbrev Equation2778 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (x ∘ z)) ∘ x
abbrev Equation2779 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (x ∘ z)) ∘ y
abbrev Equation2780 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (x ∘ z)) ∘ z
abbrev Equation2781 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ z)) ∘ w
abbrev Equation2782 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ x
abbrev Equation2783 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ y
abbrev Equation2784 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ z
abbrev Equation2785 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ w
abbrev Equation2786 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (x ∘ w)) ∘ u
abbrev Equation2787 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (y ∘ x)) ∘ x
abbrev Equation2788 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (y ∘ x)) ∘ y
abbrev Equation2789 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (y ∘ x)) ∘ z
abbrev Equation2790 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ x)) ∘ w
abbrev Equation2791 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (y ∘ y)) ∘ x
abbrev Equation2792 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (y ∘ y)) ∘ y
abbrev Equation2793 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (y ∘ y)) ∘ z
abbrev Equation2794 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ y)) ∘ w
abbrev Equation2795 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (y ∘ z)) ∘ x
abbrev Equation2796 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (y ∘ z)) ∘ y
abbrev Equation2797 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (y ∘ z)) ∘ z
abbrev Equation2798 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ z)) ∘ w
abbrev Equation2799 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ x
abbrev Equation2800 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ y
abbrev Equation2801 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ z
abbrev Equation2802 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ w
abbrev Equation2803 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (y ∘ w)) ∘ u
abbrev Equation2804 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ x)) ∘ x
abbrev Equation2805 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ x)) ∘ y
abbrev Equation2806 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ x)) ∘ z
abbrev Equation2807 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ x)) ∘ w
abbrev Equation2808 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ y)) ∘ x
abbrev Equation2809 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ y)) ∘ y
abbrev Equation2810 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ y)) ∘ z
abbrev Equation2811 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ y)) ∘ w
abbrev Equation2812 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ z)) ∘ x
abbrev Equation2813 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ z)) ∘ y
abbrev Equation2814 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ z) ∘ (z ∘ z)) ∘ z
abbrev Equation2815 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ z)) ∘ w
abbrev Equation2816 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ w)) ∘ x
abbrev Equation2817 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ w)) ∘ y
abbrev Equation2818 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ w)) ∘ z
abbrev Equation2819 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (z ∘ w)) ∘ w
abbrev Equation2820 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (z ∘ w)) ∘ u
abbrev Equation2821 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ x)) ∘ x
abbrev Equation2822 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ x)) ∘ y
abbrev Equation2823 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ x)) ∘ z
abbrev Equation2824 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ x)) ∘ w
abbrev Equation2825 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ x)) ∘ u
abbrev Equation2826 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ y)) ∘ x
abbrev Equation2827 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ y)) ∘ y
abbrev Equation2828 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ y)) ∘ z
abbrev Equation2829 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ y)) ∘ w
abbrev Equation2830 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ y)) ∘ u
abbrev Equation2831 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ z)) ∘ x
abbrev Equation2832 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ z)) ∘ y
abbrev Equation2833 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ z)) ∘ z
abbrev Equation2834 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ z)) ∘ w
abbrev Equation2835 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ z)) ∘ u
abbrev Equation2836 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ w)) ∘ x
abbrev Equation2837 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ w)) ∘ y
abbrev Equation2838 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ w)) ∘ z
abbrev Equation2839 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ z) ∘ (w ∘ w)) ∘ w
abbrev Equation2840 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ w)) ∘ u
abbrev Equation2841 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ x
abbrev Equation2842 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ y
abbrev Equation2843 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ z
abbrev Equation2844 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ w
abbrev Equation2845 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ u
abbrev Equation2846 (G: Type u) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ z) ∘ (w ∘ u)) ∘ v
abbrev Equation2847 (G: Type u) [Magma G] := ∀ x : G, x = ((x ∘ (x ∘ x)) ∘ x) ∘ x
abbrev Equation2848 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ (x ∘ x)) ∘ x) ∘ y
abbrev Equation2849 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ (x ∘ x)) ∘ y) ∘ x
abbrev Equation2850 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ (x ∘ x)) ∘ y) ∘ y
abbrev Equation2851 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ (x ∘ x)) ∘ y) ∘ z
abbrev Equation2852 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ (x ∘ y)) ∘ x) ∘ x
abbrev Equation2853 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ (x ∘ y)) ∘ x) ∘ y
abbrev Equation2854 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ (x ∘ y)) ∘ x) ∘ z
abbrev Equation2855 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ (x ∘ y)) ∘ y) ∘ x
abbrev Equation2856 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ (x ∘ y)) ∘ y) ∘ y
abbrev Equation2857 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ (x ∘ y)) ∘ y) ∘ z
abbrev Equation2858 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ (x ∘ y)) ∘ z) ∘ x
abbrev Equation2859 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ (x ∘ y)) ∘ z) ∘ y
abbrev Equation2860 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ (x ∘ y)) ∘ z) ∘ z
abbrev Equation2861 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ (x ∘ y)) ∘ z) ∘ w
abbrev Equation2862 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ (y ∘ x)) ∘ x) ∘ x
abbrev Equation2863 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ (y ∘ x)) ∘ x) ∘ y
abbrev Equation2864 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ x)) ∘ x) ∘ z
abbrev Equation2865 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ (y ∘ x)) ∘ y) ∘ x
abbrev Equation2866 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ (y ∘ x)) ∘ y) ∘ y
abbrev Equation2867 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ x)) ∘ y) ∘ z
abbrev Equation2868 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ x)) ∘ z) ∘ x
abbrev Equation2869 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ x)) ∘ z) ∘ y
abbrev Equation2870 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ x)) ∘ z) ∘ z
abbrev Equation2871 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ x)) ∘ z) ∘ w
abbrev Equation2872 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ (y ∘ y)) ∘ x) ∘ x
abbrev Equation2873 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ (y ∘ y)) ∘ x) ∘ y
abbrev Equation2874 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ y)) ∘ x) ∘ z
abbrev Equation2875 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ (y ∘ y)) ∘ y) ∘ x
abbrev Equation2876 (G: Type u) [Magma G] := ∀ x y : G, x = ((x ∘ (y ∘ y)) ∘ y) ∘ y
abbrev Equation2877 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ y)) ∘ y) ∘ z
abbrev Equation2878 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ y)) ∘ z) ∘ x
abbrev Equation2879 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ y)) ∘ z) ∘ y
abbrev Equation2880 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ y)) ∘ z) ∘ z
abbrev Equation2881 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ y)) ∘ z) ∘ w
abbrev Equation2882 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ z)) ∘ x) ∘ x
abbrev Equation2883 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ z)) ∘ x) ∘ y
abbrev Equation2884 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ z)) ∘ x) ∘ z
abbrev Equation2885 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ x) ∘ w
abbrev Equation2886 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ z)) ∘ y) ∘ x
abbrev Equation2887 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ z)) ∘ y) ∘ y
abbrev Equation2888 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ z)) ∘ y) ∘ z
abbrev Equation2889 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ y) ∘ w
abbrev Equation2890 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ z)) ∘ z) ∘ x
abbrev Equation2891 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ z)) ∘ z) ∘ y
abbrev Equation2892 (G: Type u) [Magma G] := ∀ x y z : G, x = ((x ∘ (y ∘ z)) ∘ z) ∘ z
abbrev Equation2893 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ z) ∘ w
abbrev Equation2894 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ x
abbrev Equation2895 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ y
abbrev Equation2896 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ z
abbrev Equation2897 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ w
abbrev Equation2898 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((x ∘ (y ∘ z)) ∘ w) ∘ u
abbrev Equation2899 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ x)) ∘ x) ∘ x
abbrev Equation2900 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ x)) ∘ x) ∘ y
abbrev Equation2901 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ x)) ∘ x) ∘ z
abbrev Equation2902 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ x)) ∘ y) ∘ x
abbrev Equation2903 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ x)) ∘ y) ∘ y
abbrev Equation2904 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ x)) ∘ y) ∘ z
abbrev Equation2905 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ x)) ∘ z) ∘ x
abbrev Equation2906 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ x)) ∘ z) ∘ y
abbrev Equation2907 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ x)) ∘ z) ∘ z
abbrev Equation2908 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ x)) ∘ z) ∘ w
abbrev Equation2909 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ y)) ∘ x) ∘ x
abbrev Equation2910 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ y)) ∘ x) ∘ y
abbrev Equation2911 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ y)) ∘ x) ∘ z
abbrev Equation2912 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ y)) ∘ y) ∘ x
abbrev Equation2913 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ (x ∘ y)) ∘ y) ∘ y
abbrev Equation2914 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ y)) ∘ y) ∘ z
abbrev Equation2915 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ y)) ∘ z) ∘ x
abbrev Equation2916 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ y)) ∘ z) ∘ y
abbrev Equation2917 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ y)) ∘ z) ∘ z
abbrev Equation2918 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ y)) ∘ z) ∘ w
abbrev Equation2919 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ z)) ∘ x) ∘ x
abbrev Equation2920 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ z)) ∘ x) ∘ y
abbrev Equation2921 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ z)) ∘ x) ∘ z
abbrev Equation2922 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ x) ∘ w
abbrev Equation2923 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ z)) ∘ y) ∘ x
abbrev Equation2924 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ z)) ∘ y) ∘ y
abbrev Equation2925 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ z)) ∘ y) ∘ z
abbrev Equation2926 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ y) ∘ w
abbrev Equation2927 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ z)) ∘ z) ∘ x
abbrev Equation2928 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ z)) ∘ z) ∘ y
abbrev Equation2929 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (x ∘ z)) ∘ z) ∘ z
abbrev Equation2930 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ z) ∘ w
abbrev Equation2931 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ w) ∘ x
abbrev Equation2932 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ w) ∘ y
abbrev Equation2933 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ w) ∘ z
abbrev Equation2934 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (x ∘ z)) ∘ w) ∘ w
abbrev Equation2935 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (x ∘ z)) ∘ w) ∘ u
abbrev Equation2936 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ (y ∘ x)) ∘ x) ∘ x
abbrev Equation2937 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ (y ∘ x)) ∘ x) ∘ y
abbrev Equation2938 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ x)) ∘ x) ∘ z
abbrev Equation2939 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ (y ∘ x)) ∘ y) ∘ x
abbrev Equation2940 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ (y ∘ x)) ∘ y) ∘ y
abbrev Equation2941 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ x)) ∘ y) ∘ z
abbrev Equation2942 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ x)) ∘ z) ∘ x
abbrev Equation2943 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ x)) ∘ z) ∘ y
abbrev Equation2944 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ x)) ∘ z) ∘ z
abbrev Equation2945 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ x)) ∘ z) ∘ w
abbrev Equation2946 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ (y ∘ y)) ∘ x) ∘ x
abbrev Equation2947 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ (y ∘ y)) ∘ x) ∘ y
abbrev Equation2948 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ y)) ∘ x) ∘ z
abbrev Equation2949 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ (y ∘ y)) ∘ y) ∘ x
abbrev Equation2950 (G: Type u) [Magma G] := ∀ x y : G, x = ((y ∘ (y ∘ y)) ∘ y) ∘ y
abbrev Equation2951 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ y)) ∘ y) ∘ z
abbrev Equation2952 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ y)) ∘ z) ∘ x
abbrev Equation2953 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ y)) ∘ z) ∘ y
abbrev Equation2954 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ y)) ∘ z) ∘ z
abbrev Equation2955 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ y)) ∘ z) ∘ w
abbrev Equation2956 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ z)) ∘ x) ∘ x
abbrev Equation2957 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ z)) ∘ x) ∘ y
abbrev Equation2958 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ z)) ∘ x) ∘ z
abbrev Equation2959 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ x) ∘ w
abbrev Equation2960 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ z)) ∘ y) ∘ x
abbrev Equation2961 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ z)) ∘ y) ∘ y
abbrev Equation2962 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ z)) ∘ y) ∘ z
abbrev Equation2963 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ y) ∘ w
abbrev Equation2964 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ z)) ∘ z) ∘ x
abbrev Equation2965 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ z)) ∘ z) ∘ y
abbrev Equation2966 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (y ∘ z)) ∘ z) ∘ z
abbrev Equation2967 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ z) ∘ w
abbrev Equation2968 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ w) ∘ x
abbrev Equation2969 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ w) ∘ y
abbrev Equation2970 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ w) ∘ z
abbrev Equation2971 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (y ∘ z)) ∘ w) ∘ w
abbrev Equation2972 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (y ∘ z)) ∘ w) ∘ u
abbrev Equation2973 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ x)) ∘ x) ∘ x
abbrev Equation2974 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ x)) ∘ x) ∘ y
abbrev Equation2975 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ x)) ∘ x) ∘ z
abbrev Equation2976 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ x) ∘ w
abbrev Equation2977 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ x)) ∘ y) ∘ x
abbrev Equation2978 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ x)) ∘ y) ∘ y
abbrev Equation2979 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ x)) ∘ y) ∘ z
abbrev Equation2980 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ y) ∘ w
abbrev Equation2981 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ x)) ∘ z) ∘ x
abbrev Equation2982 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ x)) ∘ z) ∘ y
abbrev Equation2983 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ x)) ∘ z) ∘ z
abbrev Equation2984 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ z) ∘ w
abbrev Equation2985 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ x
abbrev Equation2986 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ y
abbrev Equation2987 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ z
abbrev Equation2988 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ w
abbrev Equation2989 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ x)) ∘ w) ∘ u
abbrev Equation2990 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ y)) ∘ x) ∘ x
abbrev Equation2991 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ y)) ∘ x) ∘ y
abbrev Equation2992 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ y)) ∘ x) ∘ z
abbrev Equation2993 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ x) ∘ w
abbrev Equation2994 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ y)) ∘ y) ∘ x
abbrev Equation2995 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ y)) ∘ y) ∘ y
abbrev Equation2996 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ y)) ∘ y) ∘ z
abbrev Equation2997 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ y) ∘ w
abbrev Equation2998 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ y)) ∘ z) ∘ x
abbrev Equation2999 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ y)) ∘ z) ∘ y
abbrev Equation3000 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ y)) ∘ z) ∘ z
abbrev Equation3001 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ z) ∘ w
abbrev Equation3002 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ x
abbrev Equation3003 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ y
abbrev Equation3004 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ z
abbrev Equation3005 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ w
abbrev Equation3006 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ y)) ∘ w) ∘ u
abbrev Equation3007 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ x) ∘ x
abbrev Equation3008 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ x) ∘ y
abbrev Equation3009 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ x) ∘ z
abbrev Equation3010 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ x) ∘ w
abbrev Equation3011 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ y) ∘ x
abbrev Equation3012 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ y) ∘ y
abbrev Equation3013 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ y) ∘ z
abbrev Equation3014 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ y) ∘ w
abbrev Equation3015 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ z) ∘ x
abbrev Equation3016 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ z) ∘ y
abbrev Equation3017 (G: Type u) [Magma G] := ∀ x y z : G, x = ((y ∘ (z ∘ z)) ∘ z) ∘ z
abbrev Equation3018 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ z) ∘ w
abbrev Equation3019 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ w) ∘ x
abbrev Equation3020 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ w) ∘ y
abbrev Equation3021 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ w) ∘ z
abbrev Equation3022 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ z)) ∘ w) ∘ w
abbrev Equation3023 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ z)) ∘ w) ∘ u
abbrev Equation3024 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ x) ∘ x
abbrev Equation3025 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ x) ∘ y
abbrev Equation3026 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ x) ∘ z
abbrev Equation3027 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ x) ∘ w
abbrev Equation3028 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ x) ∘ u
abbrev Equation3029 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ y) ∘ x
abbrev Equation3030 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ y) ∘ y
abbrev Equation3031 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ y) ∘ z
abbrev Equation3032 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ y) ∘ w
abbrev Equation3033 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ y) ∘ u
abbrev Equation3034 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ z) ∘ x
abbrev Equation3035 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ z) ∘ y
abbrev Equation3036 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ z) ∘ z
abbrev Equation3037 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ z) ∘ w
abbrev Equation3038 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ z) ∘ u
abbrev Equation3039 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ w) ∘ x
abbrev Equation3040 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ w) ∘ y
abbrev Equation3041 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ w) ∘ z
abbrev Equation3042 (G: Type u) [Magma G] := ∀ x y z w : G, x = ((y ∘ (z ∘ w)) ∘ w) ∘ w
abbrev Equation3043 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ w) ∘ u
abbrev Equation3044 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ x
abbrev Equation3045 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ y
abbrev Equation3046 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ z
abbrev Equation3047 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ w
abbrev Equation3048 (G: Type u) [Magma G] := ∀ x y z w u : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ u
abbrev Equation3049 (G: Type u) [Magma G] := ∀ x y z w u v : G, x = ((y ∘ (z ∘ w)) ∘ u) ∘ v
abbrev Equation3050 (G: Type u) [Magma G] := ∀ x : G, x = (((x ∘ x) ∘ x) ∘ x) ∘ x
abbrev Equation3051 (G: Type u) [Magma G] := ∀ x y : G, x = (((x ∘ x) ∘ x) ∘ x) ∘ y
abbrev Equation3052 (G: Type u) [Magma G] := ∀ x y : G, x = (((x ∘ x) ∘ x) ∘ y) ∘ x
abbrev Equation3053 (G: Type u) [Magma G] := ∀ x y : G, x = (((x ∘ x) ∘ x) ∘ y) ∘ y
abbrev Equation3054 (G: Type u) [Magma G] := ∀ x y z : G, x = (((x ∘ x) ∘ x) ∘ y) ∘ z
abbrev Equation3055 (G: Type u) [Magma G] := ∀ x y : G, x = (((x ∘ x) ∘ y) ∘ x) ∘ x
abbrev Equation3056 (G: Type u) [Magma G] := ∀ x y : G, x = (((x ∘ x) ∘ y) ∘ x) ∘ y
abbrev Equation3057 (G: Type u) [Magma G] := ∀ x y z : G, x = (((x ∘ x) ∘ y) ∘ x) ∘ z
abbrev Equation3058 (G: Type u) [Magma G] := ∀ x y : G, x = (((x ∘ x) ∘ y) ∘ y) ∘ x
abbrev Equation3059 (G: Type u) [Magma G] := ∀ x y : G, x = (((x ∘ x) ∘ y) ∘ y) ∘ y
abbrev Equation3060 (G: Type u) [Magma G] := ∀ x y z : G, x = (((x ∘ x) ∘ y) ∘ y) ∘ z
abbrev Equation3061 (G: Type u) [Magma G] := ∀ x y z : G, x = (((x ∘ x) ∘ y) ∘ z) ∘ x
abbrev Equation3062 (G: Type u) [Magma G] := ∀ x y z : G, x = (((x ∘ x) ∘ y) ∘ z) ∘ y
abbrev Equation3063 (G: Type u) [Magma G] := ∀ x y z : G, x = (((x ∘ x) ∘ y) ∘ z) ∘ z
abbrev Equation3064 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((x ∘ x) ∘ y) ∘ z) ∘ w
abbrev Equation3065 (G: Type u) [Magma G] := ∀ x y : G, x = (((x ∘ y) ∘ x) ∘ x) ∘ x
abbrev Equation3066 (G: Type u) [Magma G] := ∀ x y : G, x = (((x ∘ y) ∘ x) ∘ x) ∘ y
abbrev Equation3067 (G: Type u) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ x) ∘ x) ∘ z
abbrev Equation3068 (G: Type u) [Magma G] := ∀ x y : G, x = (((x ∘ y) ∘ x) ∘ y) ∘ x
abbrev Equation3069 (G: Type u) [Magma G] := ∀ x y : G, x = (((x ∘ y) ∘ x) ∘ y) ∘ y
abbrev Equation3070 (G: Type u) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ x) ∘ y) ∘ z
abbrev Equation3071 (G: Type u) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ x) ∘ z) ∘ x
abbrev Equation3072 (G: Type u) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ x) ∘ z) ∘ y
abbrev Equation3073 (G: Type u) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ x) ∘ z) ∘ z
abbrev Equation3074 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ x) ∘ z) ∘ w
abbrev Equation3075 (G: Type u) [Magma G] := ∀ x y : G, x = (((x ∘ y) ∘ y) ∘ x) ∘ x
abbrev Equation3076 (G: Type u) [Magma G] := ∀ x y : G, x = (((x ∘ y) ∘ y) ∘ x) ∘ y
abbrev Equation3077 (G: Type u) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ y) ∘ x) ∘ z
abbrev Equation3078 (G: Type u) [Magma G] := ∀ x y : G, x = (((x ∘ y) ∘ y) ∘ y) ∘ x
abbrev Equation3079 (G: Type u) [Magma G] := ∀ x y : G, x = (((x ∘ y) ∘ y) ∘ y) ∘ y
abbrev Equation3080 (G: Type u) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ y) ∘ y) ∘ z
abbrev Equation3081 (G: Type u) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ y) ∘ z) ∘ x
abbrev Equation3082 (G: Type u) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ y) ∘ z) ∘ y
abbrev Equation3083 (G: Type u) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ y) ∘ z) ∘ z
abbrev Equation3084 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ y) ∘ z) ∘ w
abbrev Equation3085 (G: Type u) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ z) ∘ x) ∘ x
abbrev Equation3086 (G: Type u) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ z) ∘ x) ∘ y
abbrev Equation3087 (G: Type u) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ z) ∘ x) ∘ z
abbrev Equation3088 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ x) ∘ w
abbrev Equation3089 (G: Type u) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ z) ∘ y) ∘ x
abbrev Equation3090 (G: Type u) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ z) ∘ y) ∘ y
abbrev Equation3091 (G: Type u) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ z) ∘ y) ∘ z
abbrev Equation3092 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ y) ∘ w
abbrev Equation3093 (G: Type u) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ z) ∘ z) ∘ x
abbrev Equation3094 (G: Type u) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ z) ∘ z) ∘ y
abbrev Equation3095 (G: Type u) [Magma G] := ∀ x y z : G, x = (((x ∘ y) ∘ z) ∘ z) ∘ z
abbrev Equation3096 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ z) ∘ w
abbrev Equation3097 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ x
abbrev Equation3098 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ y
abbrev Equation3099 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ z
abbrev Equation3100 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ w
abbrev Equation3101 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (((x ∘ y) ∘ z) ∘ w) ∘ u
abbrev Equation3102 (G: Type u) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ x) ∘ x) ∘ x
abbrev Equation3103 (G: Type u) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ x) ∘ x) ∘ y
abbrev Equation3104 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ x) ∘ x) ∘ z
abbrev Equation3105 (G: Type u) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ x) ∘ y) ∘ x
abbrev Equation3106 (G: Type u) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ x) ∘ y) ∘ y
abbrev Equation3107 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ x) ∘ y) ∘ z
abbrev Equation3108 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ x) ∘ z) ∘ x
abbrev Equation3109 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ x) ∘ z) ∘ y
abbrev Equation3110 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ x) ∘ z) ∘ z
abbrev Equation3111 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ x) ∘ z) ∘ w
abbrev Equation3112 (G: Type u) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ y) ∘ x) ∘ x
abbrev Equation3113 (G: Type u) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ y) ∘ x) ∘ y
abbrev Equation3114 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ y) ∘ x) ∘ z
abbrev Equation3115 (G: Type u) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ y) ∘ y) ∘ x
abbrev Equation3116 (G: Type u) [Magma G] := ∀ x y : G, x = (((y ∘ x) ∘ y) ∘ y) ∘ y
abbrev Equation3117 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ y) ∘ y) ∘ z
abbrev Equation3118 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ y) ∘ z) ∘ x
abbrev Equation3119 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ y) ∘ z) ∘ y
abbrev Equation3120 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ y) ∘ z) ∘ z
abbrev Equation3121 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ y) ∘ z) ∘ w
abbrev Equation3122 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ z) ∘ x) ∘ x
abbrev Equation3123 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ z) ∘ x) ∘ y
abbrev Equation3124 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ z) ∘ x) ∘ z
abbrev Equation3125 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ x) ∘ w
abbrev Equation3126 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ z) ∘ y) ∘ x
abbrev Equation3127 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ z) ∘ y) ∘ y
abbrev Equation3128 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ z) ∘ y) ∘ z
abbrev Equation3129 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ y) ∘ w
abbrev Equation3130 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ z) ∘ z) ∘ x
abbrev Equation3131 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ z) ∘ z) ∘ y
abbrev Equation3132 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ x) ∘ z) ∘ z) ∘ z
abbrev Equation3133 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ z) ∘ w
abbrev Equation3134 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ w) ∘ x
abbrev Equation3135 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ w) ∘ y
abbrev Equation3136 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ w) ∘ z
abbrev Equation3137 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ x) ∘ z) ∘ w) ∘ w
abbrev Equation3138 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (((y ∘ x) ∘ z) ∘ w) ∘ u
abbrev Equation3139 (G: Type u) [Magma G] := ∀ x y : G, x = (((y ∘ y) ∘ x) ∘ x) ∘ x
abbrev Equation3140 (G: Type u) [Magma G] := ∀ x y : G, x = (((y ∘ y) ∘ x) ∘ x) ∘ y
abbrev Equation3141 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ x) ∘ x) ∘ z
abbrev Equation3142 (G: Type u) [Magma G] := ∀ x y : G, x = (((y ∘ y) ∘ x) ∘ y) ∘ x
abbrev Equation3143 (G: Type u) [Magma G] := ∀ x y : G, x = (((y ∘ y) ∘ x) ∘ y) ∘ y
abbrev Equation3144 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ x) ∘ y) ∘ z
abbrev Equation3145 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ x) ∘ z) ∘ x
abbrev Equation3146 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ x) ∘ z) ∘ y
abbrev Equation3147 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ x) ∘ z) ∘ z
abbrev Equation3148 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ x) ∘ z) ∘ w
abbrev Equation3149 (G: Type u) [Magma G] := ∀ x y : G, x = (((y ∘ y) ∘ y) ∘ x) ∘ x
abbrev Equation3150 (G: Type u) [Magma G] := ∀ x y : G, x = (((y ∘ y) ∘ y) ∘ x) ∘ y
abbrev Equation3151 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ y) ∘ x) ∘ z
abbrev Equation3152 (G: Type u) [Magma G] := ∀ x y : G, x = (((y ∘ y) ∘ y) ∘ y) ∘ x
abbrev Equation3153 (G: Type u) [Magma G] := ∀ x y : G, x = (((y ∘ y) ∘ y) ∘ y) ∘ y
abbrev Equation3154 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ y) ∘ y) ∘ z
abbrev Equation3155 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ y) ∘ z) ∘ x
abbrev Equation3156 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ y) ∘ z) ∘ y
abbrev Equation3157 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ y) ∘ z) ∘ z
abbrev Equation3158 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ y) ∘ z) ∘ w
abbrev Equation3159 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ z) ∘ x) ∘ x
abbrev Equation3160 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ z) ∘ x) ∘ y
abbrev Equation3161 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ z) ∘ x) ∘ z
abbrev Equation3162 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ x) ∘ w
abbrev Equation3163 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ z) ∘ y) ∘ x
abbrev Equation3164 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ z) ∘ y) ∘ y
abbrev Equation3165 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ z) ∘ y) ∘ z
abbrev Equation3166 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ y) ∘ w
abbrev Equation3167 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ z) ∘ z) ∘ x
abbrev Equation3168 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ z) ∘ z) ∘ y
abbrev Equation3169 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ y) ∘ z) ∘ z) ∘ z
abbrev Equation3170 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ z) ∘ w
abbrev Equation3171 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ w) ∘ x
abbrev Equation3172 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ w) ∘ y
abbrev Equation3173 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ w) ∘ z
abbrev Equation3174 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ y) ∘ z) ∘ w) ∘ w
abbrev Equation3175 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (((y ∘ y) ∘ z) ∘ w) ∘ u
abbrev Equation3176 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ x) ∘ x) ∘ x
abbrev Equation3177 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ x) ∘ x) ∘ y
abbrev Equation3178 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ x) ∘ x) ∘ z
abbrev Equation3179 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ x) ∘ w
abbrev Equation3180 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ x) ∘ y) ∘ x
abbrev Equation3181 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ x) ∘ y) ∘ y
abbrev Equation3182 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ x) ∘ y) ∘ z
abbrev Equation3183 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ y) ∘ w
abbrev Equation3184 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ x) ∘ z) ∘ x
abbrev Equation3185 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ x) ∘ z) ∘ y
abbrev Equation3186 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ x) ∘ z) ∘ z
abbrev Equation3187 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ z) ∘ w
abbrev Equation3188 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ x
abbrev Equation3189 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ y
abbrev Equation3190 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ z
abbrev Equation3191 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ w
abbrev Equation3192 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ x) ∘ w) ∘ u
abbrev Equation3193 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ y) ∘ x) ∘ x
abbrev Equation3194 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ y) ∘ x) ∘ y
abbrev Equation3195 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ y) ∘ x) ∘ z
abbrev Equation3196 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ x) ∘ w
abbrev Equation3197 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ y) ∘ y) ∘ x
abbrev Equation3198 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ y) ∘ y) ∘ y
abbrev Equation3199 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ y) ∘ y) ∘ z
abbrev Equation3200 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ y) ∘ w
abbrev Equation3201 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ y) ∘ z) ∘ x
abbrev Equation3202 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ y) ∘ z) ∘ y
abbrev Equation3203 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ y) ∘ z) ∘ z
abbrev Equation3204 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ z) ∘ w
abbrev Equation3205 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ x
abbrev Equation3206 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ y
abbrev Equation3207 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ z
abbrev Equation3208 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ w
abbrev Equation3209 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ y) ∘ w) ∘ u
abbrev Equation3210 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ x) ∘ x
abbrev Equation3211 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ x) ∘ y
abbrev Equation3212 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ x) ∘ z
abbrev Equation3213 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ x) ∘ w
abbrev Equation3214 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ y) ∘ x
abbrev Equation3215 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ y) ∘ y
abbrev Equation3216 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ y) ∘ z
abbrev Equation3217 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ y) ∘ w
abbrev Equation3218 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ z) ∘ x
abbrev Equation3219 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ z) ∘ y
abbrev Equation3220 (G: Type u) [Magma G] := ∀ x y z : G, x = (((y ∘ z) ∘ z) ∘ z) ∘ z
abbrev Equation3221 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ z) ∘ w
abbrev Equation3222 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ w) ∘ x
abbrev Equation3223 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ w) ∘ y
abbrev Equation3224 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ w) ∘ z
abbrev Equation3225 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ z) ∘ w) ∘ w
abbrev Equation3226 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ z) ∘ w) ∘ u
abbrev Equation3227 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ x) ∘ x
abbrev Equation3228 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ x) ∘ y
abbrev Equation3229 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ x) ∘ z
abbrev Equation3230 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ x) ∘ w
abbrev Equation3231 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ x) ∘ u
abbrev Equation3232 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ y) ∘ x
abbrev Equation3233 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ y) ∘ y
abbrev Equation3234 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ y) ∘ z
abbrev Equation3235 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ y) ∘ w
abbrev Equation3236 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ y) ∘ u
abbrev Equation3237 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ z) ∘ x
abbrev Equation3238 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ z) ∘ y
abbrev Equation3239 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ z) ∘ z
abbrev Equation3240 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ z) ∘ w
abbrev Equation3241 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ z) ∘ u
abbrev Equation3242 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ w) ∘ x
abbrev Equation3243 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ w) ∘ y
abbrev Equation3244 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ w) ∘ z
abbrev Equation3245 (G: Type u) [Magma G] := ∀ x y z w : G, x = (((y ∘ z) ∘ w) ∘ w) ∘ w
abbrev Equation3246 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ w) ∘ u
abbrev Equation3247 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ x
abbrev Equation3248 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ y
abbrev Equation3249 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ z
abbrev Equation3250 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ w
abbrev Equation3251 (G: Type u) [Magma G] := ∀ x y z w u : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ u
abbrev Equation3252 (G: Type u) [Magma G] := ∀ x y z w u v : G, x = (((y ∘ z) ∘ w) ∘ u) ∘ v
abbrev Equation3253 (G: Type u) [Magma G] := ∀ x : G, x ∘ x = x ∘ (x ∘ (x ∘ x))
abbrev Equation3254 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = x ∘ (x ∘ (x ∘ y))
abbrev Equation3255 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = x ∘ (x ∘ (y ∘ x))
abbrev Equation3256 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = x ∘ (x ∘ (y ∘ y))
abbrev Equation3257 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ (x ∘ (y ∘ z))
abbrev Equation3258 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = x ∘ (y ∘ (x ∘ x))
abbrev Equation3259 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = x ∘ (y ∘ (x ∘ y))
abbrev Equation3260 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ (y ∘ (x ∘ z))
abbrev Equation3261 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = x ∘ (y ∘ (y ∘ x))
abbrev Equation3262 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = x ∘ (y ∘ (y ∘ y))
abbrev Equation3263 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ (y ∘ (y ∘ z))
abbrev Equation3264 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ (y ∘ (z ∘ x))
abbrev Equation3265 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ (y ∘ (z ∘ y))
abbrev Equation3266 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ (y ∘ (z ∘ z))
abbrev Equation3267 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = x ∘ (y ∘ (z ∘ w))
abbrev Equation3268 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (x ∘ (x ∘ x))
abbrev Equation3269 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (x ∘ (x ∘ y))
abbrev Equation3270 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (x ∘ (x ∘ z))
abbrev Equation3271 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (x ∘ (y ∘ x))
abbrev Equation3272 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (x ∘ (y ∘ y))
abbrev Equation3273 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (x ∘ (y ∘ z))
abbrev Equation3274 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (x ∘ (z ∘ x))
abbrev Equation3275 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (x ∘ (z ∘ y))
abbrev Equation3276 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (x ∘ (z ∘ z))
abbrev Equation3277 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (x ∘ (z ∘ w))
abbrev Equation3278 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (y ∘ (x ∘ x))
abbrev Equation3279 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (y ∘ (x ∘ y))
abbrev Equation3280 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (y ∘ (x ∘ z))
abbrev Equation3281 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (y ∘ (y ∘ x))
abbrev Equation3282 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = y ∘ (y ∘ (y ∘ y))
abbrev Equation3283 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (y ∘ (y ∘ z))
abbrev Equation3284 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (y ∘ (z ∘ x))
abbrev Equation3285 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (y ∘ (z ∘ y))
abbrev Equation3286 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (y ∘ (z ∘ z))
abbrev Equation3287 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (y ∘ (z ∘ w))
abbrev Equation3288 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ (x ∘ x))
abbrev Equation3289 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ (x ∘ y))
abbrev Equation3290 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ (x ∘ z))
abbrev Equation3291 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (x ∘ w))
abbrev Equation3292 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ (y ∘ x))
abbrev Equation3293 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ (y ∘ y))
abbrev Equation3294 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ (y ∘ z))
abbrev Equation3295 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (y ∘ w))
abbrev Equation3296 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ (z ∘ x))
abbrev Equation3297 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ (z ∘ y))
abbrev Equation3298 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ (z ∘ (z ∘ z))
abbrev Equation3299 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (z ∘ w))
abbrev Equation3300 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (w ∘ x))
abbrev Equation3301 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (w ∘ y))
abbrev Equation3302 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (w ∘ z))
abbrev Equation3303 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ (z ∘ (w ∘ w))
abbrev Equation3304 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ x = y ∘ (z ∘ (w ∘ u))
abbrev Equation3305 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (x ∘ (x ∘ x))
abbrev Equation3306 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (x ∘ (x ∘ y))
abbrev Equation3307 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (x ∘ (x ∘ z))
abbrev Equation3308 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (x ∘ (y ∘ x))
abbrev Equation3309 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (x ∘ (y ∘ y))
abbrev Equation3310 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (x ∘ (y ∘ z))
abbrev Equation3311 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (x ∘ (z ∘ x))
abbrev Equation3312 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (x ∘ (z ∘ y))
abbrev Equation3313 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (x ∘ (z ∘ z))
abbrev Equation3314 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (x ∘ (z ∘ w))
abbrev Equation3315 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (y ∘ (x ∘ x))
abbrev Equation3316 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (y ∘ (x ∘ y))
abbrev Equation3317 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (y ∘ (x ∘ z))
abbrev Equation3318 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (y ∘ (y ∘ x))
abbrev Equation3319 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = x ∘ (y ∘ (y ∘ y))
abbrev Equation3320 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (y ∘ (y ∘ z))
abbrev Equation3321 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (y ∘ (z ∘ x))
abbrev Equation3322 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (y ∘ (z ∘ y))
abbrev Equation3323 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (y ∘ (z ∘ z))
abbrev Equation3324 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (y ∘ (z ∘ w))
abbrev Equation3325 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ (x ∘ x))
abbrev Equation3326 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ (x ∘ y))
abbrev Equation3327 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ (x ∘ z))
abbrev Equation3328 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (x ∘ w))
abbrev Equation3329 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ (y ∘ x))
abbrev Equation3330 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ (y ∘ y))
abbrev Equation3331 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ (y ∘ z))
abbrev Equation3332 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (y ∘ w))
abbrev Equation3333 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ (z ∘ x))
abbrev Equation3334 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ (z ∘ y))
abbrev Equation3335 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ (z ∘ (z ∘ z))
abbrev Equation3336 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (z ∘ w))
abbrev Equation3337 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (w ∘ x))
abbrev Equation3338 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (w ∘ y))
abbrev Equation3339 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (w ∘ z))
abbrev Equation3340 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ (z ∘ (w ∘ w))
abbrev Equation3341 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = x ∘ (z ∘ (w ∘ u))
abbrev Equation3342 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (x ∘ (x ∘ x))
abbrev Equation3343 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (x ∘ (x ∘ y))
abbrev Equation3344 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (x ∘ (x ∘ z))
abbrev Equation3345 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (x ∘ (y ∘ x))
abbrev Equation3346 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (x ∘ (y ∘ y))
abbrev Equation3347 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (x ∘ (y ∘ z))
abbrev Equation3348 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (x ∘ (z ∘ x))
abbrev Equation3349 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (x ∘ (z ∘ y))
abbrev Equation3350 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (x ∘ (z ∘ z))
abbrev Equation3351 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (x ∘ (z ∘ w))
abbrev Equation3352 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (y ∘ (x ∘ x))
abbrev Equation3353 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (y ∘ (x ∘ y))
abbrev Equation3354 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (y ∘ (x ∘ z))
abbrev Equation3355 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (y ∘ (y ∘ x))
abbrev Equation3356 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = y ∘ (y ∘ (y ∘ y))
abbrev Equation3357 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (y ∘ (y ∘ z))
abbrev Equation3358 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (y ∘ (z ∘ x))
abbrev Equation3359 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (y ∘ (z ∘ y))
abbrev Equation3360 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (y ∘ (z ∘ z))
abbrev Equation3361 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (y ∘ (z ∘ w))
abbrev Equation3362 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ (x ∘ x))
abbrev Equation3363 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ (x ∘ y))
abbrev Equation3364 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ (x ∘ z))
abbrev Equation3365 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (x ∘ w))
abbrev Equation3366 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ (y ∘ x))
abbrev Equation3367 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ (y ∘ y))
abbrev Equation3368 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ (y ∘ z))
abbrev Equation3369 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (y ∘ w))
abbrev Equation3370 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ (z ∘ x))
abbrev Equation3371 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ (z ∘ y))
abbrev Equation3372 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ (z ∘ (z ∘ z))
abbrev Equation3373 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (z ∘ w))
abbrev Equation3374 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (w ∘ x))
abbrev Equation3375 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (w ∘ y))
abbrev Equation3376 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (w ∘ z))
abbrev Equation3377 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ (z ∘ (w ∘ w))
abbrev Equation3378 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = y ∘ (z ∘ (w ∘ u))
abbrev Equation3379 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ (x ∘ x))
abbrev Equation3380 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ (x ∘ y))
abbrev Equation3381 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ (x ∘ z))
abbrev Equation3382 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (x ∘ w))
abbrev Equation3383 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ (y ∘ x))
abbrev Equation3384 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ (y ∘ y))
abbrev Equation3385 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ (y ∘ z))
abbrev Equation3386 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (y ∘ w))
abbrev Equation3387 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ (z ∘ x))
abbrev Equation3388 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ (z ∘ y))
abbrev Equation3389 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (x ∘ (z ∘ z))
abbrev Equation3390 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (z ∘ w))
abbrev Equation3391 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (w ∘ x))
abbrev Equation3392 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (w ∘ y))
abbrev Equation3393 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (w ∘ z))
abbrev Equation3394 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (x ∘ (w ∘ w))
abbrev Equation3395 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (x ∘ (w ∘ u))
abbrev Equation3396 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ (x ∘ x))
abbrev Equation3397 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ (x ∘ y))
abbrev Equation3398 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ (x ∘ z))
abbrev Equation3399 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (x ∘ w))
abbrev Equation3400 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ (y ∘ x))
abbrev Equation3401 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ (y ∘ y))
abbrev Equation3402 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ (y ∘ z))
abbrev Equation3403 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (y ∘ w))
abbrev Equation3404 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ (z ∘ x))
abbrev Equation3405 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ (z ∘ y))
abbrev Equation3406 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (y ∘ (z ∘ z))
abbrev Equation3407 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (z ∘ w))
abbrev Equation3408 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (w ∘ x))
abbrev Equation3409 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (w ∘ y))
abbrev Equation3410 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (w ∘ z))
abbrev Equation3411 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (y ∘ (w ∘ w))
abbrev Equation3412 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (y ∘ (w ∘ u))
abbrev Equation3413 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (x ∘ x))
abbrev Equation3414 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (x ∘ y))
abbrev Equation3415 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (x ∘ z))
abbrev Equation3416 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (x ∘ w))
abbrev Equation3417 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (y ∘ x))
abbrev Equation3418 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (y ∘ y))
abbrev Equation3419 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (y ∘ z))
abbrev Equation3420 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (y ∘ w))
abbrev Equation3421 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (z ∘ x))
abbrev Equation3422 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (z ∘ y))
abbrev Equation3423 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ (z ∘ (z ∘ z))
abbrev Equation3424 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (z ∘ w))
abbrev Equation3425 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (w ∘ x))
abbrev Equation3426 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (w ∘ y))
abbrev Equation3427 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (w ∘ z))
abbrev Equation3428 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (z ∘ (w ∘ w))
abbrev Equation3429 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (z ∘ (w ∘ u))
abbrev Equation3430 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (x ∘ x))
abbrev Equation3431 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (x ∘ y))
abbrev Equation3432 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (x ∘ z))
abbrev Equation3433 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (x ∘ w))
abbrev Equation3434 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (x ∘ u))
abbrev Equation3435 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (y ∘ x))
abbrev Equation3436 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (y ∘ y))
abbrev Equation3437 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (y ∘ z))
abbrev Equation3438 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (y ∘ w))
abbrev Equation3439 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (y ∘ u))
abbrev Equation3440 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (z ∘ x))
abbrev Equation3441 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (z ∘ y))
abbrev Equation3442 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (z ∘ z))
abbrev Equation3443 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (z ∘ w))
abbrev Equation3444 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (z ∘ u))
abbrev Equation3445 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (w ∘ x))
abbrev Equation3446 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (w ∘ y))
abbrev Equation3447 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (w ∘ z))
abbrev Equation3448 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ (w ∘ (w ∘ w))
abbrev Equation3449 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (w ∘ u))
abbrev Equation3450 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (u ∘ x))
abbrev Equation3451 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (u ∘ y))
abbrev Equation3452 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (u ∘ z))
abbrev Equation3453 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (u ∘ w))
abbrev Equation3454 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ (w ∘ (u ∘ u))
abbrev Equation3455 (G: Type u) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ (w ∘ (u ∘ v))
abbrev Equation3456 (G: Type u) [Magma G] := ∀ x : G, x ∘ x = x ∘ ((x ∘ x) ∘ x)
abbrev Equation3457 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = x ∘ ((x ∘ x) ∘ y)
abbrev Equation3458 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = x ∘ ((x ∘ y) ∘ x)
abbrev Equation3459 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = x ∘ ((x ∘ y) ∘ y)
abbrev Equation3460 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ ((x ∘ y) ∘ z)
abbrev Equation3461 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = x ∘ ((y ∘ x) ∘ x)
abbrev Equation3462 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = x ∘ ((y ∘ x) ∘ y)
abbrev Equation3463 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ ((y ∘ x) ∘ z)
abbrev Equation3464 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = x ∘ ((y ∘ y) ∘ x)
abbrev Equation3465 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = x ∘ ((y ∘ y) ∘ y)
abbrev Equation3466 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ ((y ∘ y) ∘ z)
abbrev Equation3467 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ ((y ∘ z) ∘ x)
abbrev Equation3468 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ ((y ∘ z) ∘ y)
abbrev Equation3469 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = x ∘ ((y ∘ z) ∘ z)
abbrev Equation3470 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = x ∘ ((y ∘ z) ∘ w)
abbrev Equation3471 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = y ∘ ((x ∘ x) ∘ x)
abbrev Equation3472 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = y ∘ ((x ∘ x) ∘ y)
abbrev Equation3473 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((x ∘ x) ∘ z)
abbrev Equation3474 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = y ∘ ((x ∘ y) ∘ x)
abbrev Equation3475 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = y ∘ ((x ∘ y) ∘ y)
abbrev Equation3476 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((x ∘ y) ∘ z)
abbrev Equation3477 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((x ∘ z) ∘ x)
abbrev Equation3478 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((x ∘ z) ∘ y)
abbrev Equation3479 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((x ∘ z) ∘ z)
abbrev Equation3480 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((x ∘ z) ∘ w)
abbrev Equation3481 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = y ∘ ((y ∘ x) ∘ x)
abbrev Equation3482 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = y ∘ ((y ∘ x) ∘ y)
abbrev Equation3483 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((y ∘ x) ∘ z)
abbrev Equation3484 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = y ∘ ((y ∘ y) ∘ x)
abbrev Equation3485 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = y ∘ ((y ∘ y) ∘ y)
abbrev Equation3486 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((y ∘ y) ∘ z)
abbrev Equation3487 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((y ∘ z) ∘ x)
abbrev Equation3488 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((y ∘ z) ∘ y)
abbrev Equation3489 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((y ∘ z) ∘ z)
abbrev Equation3490 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((y ∘ z) ∘ w)
abbrev Equation3491 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((z ∘ x) ∘ x)
abbrev Equation3492 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((z ∘ x) ∘ y)
abbrev Equation3493 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((z ∘ x) ∘ z)
abbrev Equation3494 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ x) ∘ w)
abbrev Equation3495 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((z ∘ y) ∘ x)
abbrev Equation3496 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((z ∘ y) ∘ y)
abbrev Equation3497 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((z ∘ y) ∘ z)
abbrev Equation3498 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ y) ∘ w)
abbrev Equation3499 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((z ∘ z) ∘ x)
abbrev Equation3500 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((z ∘ z) ∘ y)
abbrev Equation3501 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = y ∘ ((z ∘ z) ∘ z)
abbrev Equation3502 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ z) ∘ w)
abbrev Equation3503 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ w) ∘ x)
abbrev Equation3504 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ w) ∘ y)
abbrev Equation3505 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ w) ∘ z)
abbrev Equation3506 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = y ∘ ((z ∘ w) ∘ w)
abbrev Equation3507 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ x = y ∘ ((z ∘ w) ∘ u)
abbrev Equation3508 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((x ∘ x) ∘ x)
abbrev Equation3509 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((x ∘ x) ∘ y)
abbrev Equation3510 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((x ∘ x) ∘ z)
abbrev Equation3511 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((x ∘ y) ∘ x)
abbrev Equation3512 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((x ∘ y) ∘ y)
abbrev Equation3513 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((x ∘ y) ∘ z)
abbrev Equation3514 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((x ∘ z) ∘ x)
abbrev Equation3515 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((x ∘ z) ∘ y)
abbrev Equation3516 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((x ∘ z) ∘ z)
abbrev Equation3517 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((x ∘ z) ∘ w)
abbrev Equation3518 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((y ∘ x) ∘ x)
abbrev Equation3519 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((y ∘ x) ∘ y)
abbrev Equation3520 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((y ∘ x) ∘ z)
abbrev Equation3521 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((y ∘ y) ∘ x)
abbrev Equation3522 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = x ∘ ((y ∘ y) ∘ y)
abbrev Equation3523 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((y ∘ y) ∘ z)
abbrev Equation3524 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((y ∘ z) ∘ x)
abbrev Equation3525 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((y ∘ z) ∘ y)
abbrev Equation3526 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((y ∘ z) ∘ z)
abbrev Equation3527 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((y ∘ z) ∘ w)
abbrev Equation3528 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((z ∘ x) ∘ x)
abbrev Equation3529 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((z ∘ x) ∘ y)
abbrev Equation3530 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((z ∘ x) ∘ z)
abbrev Equation3531 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ x) ∘ w)
abbrev Equation3532 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((z ∘ y) ∘ x)
abbrev Equation3533 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((z ∘ y) ∘ y)
abbrev Equation3534 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((z ∘ y) ∘ z)
abbrev Equation3535 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ y) ∘ w)
abbrev Equation3536 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((z ∘ z) ∘ x)
abbrev Equation3537 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((z ∘ z) ∘ y)
abbrev Equation3538 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = x ∘ ((z ∘ z) ∘ z)
abbrev Equation3539 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ z) ∘ w)
abbrev Equation3540 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ w) ∘ x)
abbrev Equation3541 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ w) ∘ y)
abbrev Equation3542 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ w) ∘ z)
abbrev Equation3543 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = x ∘ ((z ∘ w) ∘ w)
abbrev Equation3544 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = x ∘ ((z ∘ w) ∘ u)
abbrev Equation3545 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = y ∘ ((x ∘ x) ∘ x)
abbrev Equation3546 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = y ∘ ((x ∘ x) ∘ y)
abbrev Equation3547 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((x ∘ x) ∘ z)
abbrev Equation3548 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = y ∘ ((x ∘ y) ∘ x)
abbrev Equation3549 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = y ∘ ((x ∘ y) ∘ y)
abbrev Equation3550 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((x ∘ y) ∘ z)
abbrev Equation3551 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((x ∘ z) ∘ x)
abbrev Equation3552 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((x ∘ z) ∘ y)
abbrev Equation3553 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((x ∘ z) ∘ z)
abbrev Equation3554 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((x ∘ z) ∘ w)
abbrev Equation3555 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = y ∘ ((y ∘ x) ∘ x)
abbrev Equation3556 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = y ∘ ((y ∘ x) ∘ y)
abbrev Equation3557 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((y ∘ x) ∘ z)
abbrev Equation3558 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = y ∘ ((y ∘ y) ∘ x)
abbrev Equation3559 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = y ∘ ((y ∘ y) ∘ y)
abbrev Equation3560 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((y ∘ y) ∘ z)
abbrev Equation3561 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((y ∘ z) ∘ x)
abbrev Equation3562 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((y ∘ z) ∘ y)
abbrev Equation3563 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((y ∘ z) ∘ z)
abbrev Equation3564 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((y ∘ z) ∘ w)
abbrev Equation3565 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((z ∘ x) ∘ x)
abbrev Equation3566 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((z ∘ x) ∘ y)
abbrev Equation3567 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((z ∘ x) ∘ z)
abbrev Equation3568 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ x) ∘ w)
abbrev Equation3569 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((z ∘ y) ∘ x)
abbrev Equation3570 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((z ∘ y) ∘ y)
abbrev Equation3571 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((z ∘ y) ∘ z)
abbrev Equation3572 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ y) ∘ w)
abbrev Equation3573 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((z ∘ z) ∘ x)
abbrev Equation3574 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((z ∘ z) ∘ y)
abbrev Equation3575 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = y ∘ ((z ∘ z) ∘ z)
abbrev Equation3576 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ z) ∘ w)
abbrev Equation3577 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ w) ∘ x)
abbrev Equation3578 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ w) ∘ y)
abbrev Equation3579 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ w) ∘ z)
abbrev Equation3580 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = y ∘ ((z ∘ w) ∘ w)
abbrev Equation3581 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = y ∘ ((z ∘ w) ∘ u)
abbrev Equation3582 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((x ∘ x) ∘ x)
abbrev Equation3583 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((x ∘ x) ∘ y)
abbrev Equation3584 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((x ∘ x) ∘ z)
abbrev Equation3585 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ x) ∘ w)
abbrev Equation3586 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((x ∘ y) ∘ x)
abbrev Equation3587 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((x ∘ y) ∘ y)
abbrev Equation3588 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((x ∘ y) ∘ z)
abbrev Equation3589 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ y) ∘ w)
abbrev Equation3590 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((x ∘ z) ∘ x)
abbrev Equation3591 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((x ∘ z) ∘ y)
abbrev Equation3592 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((x ∘ z) ∘ z)
abbrev Equation3593 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ z) ∘ w)
abbrev Equation3594 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ w) ∘ x)
abbrev Equation3595 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ w) ∘ y)
abbrev Equation3596 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ w) ∘ z)
abbrev Equation3597 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((x ∘ w) ∘ w)
abbrev Equation3598 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((x ∘ w) ∘ u)
abbrev Equation3599 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((y ∘ x) ∘ x)
abbrev Equation3600 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((y ∘ x) ∘ y)
abbrev Equation3601 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((y ∘ x) ∘ z)
abbrev Equation3602 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ x) ∘ w)
abbrev Equation3603 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((y ∘ y) ∘ x)
abbrev Equation3604 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((y ∘ y) ∘ y)
abbrev Equation3605 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((y ∘ y) ∘ z)
abbrev Equation3606 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ y) ∘ w)
abbrev Equation3607 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((y ∘ z) ∘ x)
abbrev Equation3608 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((y ∘ z) ∘ y)
abbrev Equation3609 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((y ∘ z) ∘ z)
abbrev Equation3610 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ z) ∘ w)
abbrev Equation3611 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ w) ∘ x)
abbrev Equation3612 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ w) ∘ y)
abbrev Equation3613 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ w) ∘ z)
abbrev Equation3614 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((y ∘ w) ∘ w)
abbrev Equation3615 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((y ∘ w) ∘ u)
abbrev Equation3616 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ x) ∘ x)
abbrev Equation3617 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ x) ∘ y)
abbrev Equation3618 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ x) ∘ z)
abbrev Equation3619 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ x) ∘ w)
abbrev Equation3620 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ y) ∘ x)
abbrev Equation3621 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ y) ∘ y)
abbrev Equation3622 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ y) ∘ z)
abbrev Equation3623 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ y) ∘ w)
abbrev Equation3624 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ z) ∘ x)
abbrev Equation3625 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ z) ∘ y)
abbrev Equation3626 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = z ∘ ((z ∘ z) ∘ z)
abbrev Equation3627 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ z) ∘ w)
abbrev Equation3628 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ w) ∘ x)
abbrev Equation3629 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ w) ∘ y)
abbrev Equation3630 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ w) ∘ z)
abbrev Equation3631 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((z ∘ w) ∘ w)
abbrev Equation3632 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((z ∘ w) ∘ u)
abbrev Equation3633 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ x) ∘ x)
abbrev Equation3634 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ x) ∘ y)
abbrev Equation3635 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ x) ∘ z)
abbrev Equation3636 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ x) ∘ w)
abbrev Equation3637 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ x) ∘ u)
abbrev Equation3638 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ y) ∘ x)
abbrev Equation3639 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ y) ∘ y)
abbrev Equation3640 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ y) ∘ z)
abbrev Equation3641 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ y) ∘ w)
abbrev Equation3642 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ y) ∘ u)
abbrev Equation3643 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ z) ∘ x)
abbrev Equation3644 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ z) ∘ y)
abbrev Equation3645 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ z) ∘ z)
abbrev Equation3646 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ z) ∘ w)
abbrev Equation3647 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ z) ∘ u)
abbrev Equation3648 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ w) ∘ x)
abbrev Equation3649 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ w) ∘ y)
abbrev Equation3650 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ w) ∘ z)
abbrev Equation3651 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = z ∘ ((w ∘ w) ∘ w)
abbrev Equation3652 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ w) ∘ u)
abbrev Equation3653 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ u) ∘ x)
abbrev Equation3654 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ u) ∘ y)
abbrev Equation3655 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ u) ∘ z)
abbrev Equation3656 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ u) ∘ w)
abbrev Equation3657 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = z ∘ ((w ∘ u) ∘ u)
abbrev Equation3658 (G: Type u) [Magma G] := ∀ x y z w u v : G, x ∘ y = z ∘ ((w ∘ u) ∘ v)
abbrev Equation3659 (G: Type u) [Magma G] := ∀ x : G, x ∘ x = (x ∘ x) ∘ (x ∘ x)
abbrev Equation3660 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ x) ∘ (x ∘ y)
abbrev Equation3661 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ x) ∘ (y ∘ x)
abbrev Equation3662 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ x) ∘ (y ∘ y)
abbrev Equation3663 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ x) ∘ (y ∘ z)
abbrev Equation3664 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ y) ∘ (x ∘ x)
abbrev Equation3665 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ y) ∘ (x ∘ y)
abbrev Equation3666 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ y) ∘ (x ∘ z)
abbrev Equation3667 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ y) ∘ (y ∘ x)
abbrev Equation3668 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ y) ∘ (y ∘ y)
abbrev Equation3669 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ y) ∘ (y ∘ z)
abbrev Equation3670 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ y) ∘ (z ∘ x)
abbrev Equation3671 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ y) ∘ (z ∘ y)
abbrev Equation3672 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ y) ∘ (z ∘ z)
abbrev Equation3673 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = (x ∘ y) ∘ (z ∘ w)
abbrev Equation3674 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ x) ∘ (x ∘ x)
abbrev Equation3675 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ x) ∘ (x ∘ y)
abbrev Equation3676 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ x) ∘ (x ∘ z)
abbrev Equation3677 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ x) ∘ (y ∘ x)
abbrev Equation3678 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ x) ∘ (y ∘ y)
abbrev Equation3679 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ x) ∘ (y ∘ z)
abbrev Equation3680 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ x) ∘ (z ∘ x)
abbrev Equation3681 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ x) ∘ (z ∘ y)
abbrev Equation3682 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ x) ∘ (z ∘ z)
abbrev Equation3683 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ x) ∘ (z ∘ w)
abbrev Equation3684 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ y) ∘ (x ∘ x)
abbrev Equation3685 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ y) ∘ (x ∘ y)
abbrev Equation3686 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ y) ∘ (x ∘ z)
abbrev Equation3687 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ y) ∘ (y ∘ x)
abbrev Equation3688 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ y) ∘ (y ∘ y)
abbrev Equation3689 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ y) ∘ (y ∘ z)
abbrev Equation3690 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ y) ∘ (z ∘ x)
abbrev Equation3691 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ y) ∘ (z ∘ y)
abbrev Equation3692 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ y) ∘ (z ∘ z)
abbrev Equation3693 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ y) ∘ (z ∘ w)
abbrev Equation3694 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ (x ∘ x)
abbrev Equation3695 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ (x ∘ y)
abbrev Equation3696 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ (x ∘ z)
abbrev Equation3697 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (x ∘ w)
abbrev Equation3698 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ (y ∘ x)
abbrev Equation3699 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ (y ∘ y)
abbrev Equation3700 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ (y ∘ z)
abbrev Equation3701 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (y ∘ w)
abbrev Equation3702 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ (z ∘ x)
abbrev Equation3703 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ (z ∘ y)
abbrev Equation3704 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ z) ∘ (z ∘ z)
abbrev Equation3705 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (z ∘ w)
abbrev Equation3706 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (w ∘ x)
abbrev Equation3707 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (w ∘ y)
abbrev Equation3708 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (w ∘ z)
abbrev Equation3709 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ z) ∘ (w ∘ w)
abbrev Equation3710 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ x = (y ∘ z) ∘ (w ∘ u)
abbrev Equation3711 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ x) ∘ (x ∘ x)
abbrev Equation3712 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ x) ∘ (x ∘ y)
abbrev Equation3713 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ x) ∘ (x ∘ z)
abbrev Equation3714 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ x) ∘ (y ∘ x)
abbrev Equation3715 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ x) ∘ (y ∘ y)
abbrev Equation3716 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ x) ∘ (y ∘ z)
abbrev Equation3717 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ x) ∘ (z ∘ x)
abbrev Equation3718 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ x) ∘ (z ∘ y)
abbrev Equation3719 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ x) ∘ (z ∘ z)
abbrev Equation3720 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ x) ∘ (z ∘ w)
abbrev Equation3721 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ y) ∘ (x ∘ x)
abbrev Equation3722 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ y) ∘ (x ∘ y)
abbrev Equation3723 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ y) ∘ (x ∘ z)
abbrev Equation3724 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ y) ∘ (y ∘ x)
abbrev Equation3725 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ y) ∘ (y ∘ y)
abbrev Equation3726 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ y) ∘ (y ∘ z)
abbrev Equation3727 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ y) ∘ (z ∘ x)
abbrev Equation3728 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ y) ∘ (z ∘ y)
abbrev Equation3729 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ y) ∘ (z ∘ z)
abbrev Equation3730 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ y) ∘ (z ∘ w)
abbrev Equation3731 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ (x ∘ x)
abbrev Equation3732 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ (x ∘ y)
abbrev Equation3733 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ (x ∘ z)
abbrev Equation3734 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (x ∘ w)
abbrev Equation3735 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ (y ∘ x)
abbrev Equation3736 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ (y ∘ y)
abbrev Equation3737 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ (y ∘ z)
abbrev Equation3738 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (y ∘ w)
abbrev Equation3739 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ (z ∘ x)
abbrev Equation3740 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ (z ∘ y)
abbrev Equation3741 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ z) ∘ (z ∘ z)
abbrev Equation3742 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (z ∘ w)
abbrev Equation3743 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (w ∘ x)
abbrev Equation3744 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (w ∘ y)
abbrev Equation3745 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (w ∘ z)
abbrev Equation3746 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ z) ∘ (w ∘ w)
abbrev Equation3747 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (x ∘ z) ∘ (w ∘ u)
abbrev Equation3748 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ x) ∘ (x ∘ x)
abbrev Equation3749 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ x) ∘ (x ∘ y)
abbrev Equation3750 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ x) ∘ (x ∘ z)
abbrev Equation3751 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ x) ∘ (y ∘ x)
abbrev Equation3752 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ x) ∘ (y ∘ y)
abbrev Equation3753 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ x) ∘ (y ∘ z)
abbrev Equation3754 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ x) ∘ (z ∘ x)
abbrev Equation3755 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ x) ∘ (z ∘ y)
abbrev Equation3756 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ x) ∘ (z ∘ z)
abbrev Equation3757 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ x) ∘ (z ∘ w)
abbrev Equation3758 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ y) ∘ (x ∘ x)
abbrev Equation3759 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ y) ∘ (x ∘ y)
abbrev Equation3760 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ y) ∘ (x ∘ z)
abbrev Equation3761 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ y) ∘ (y ∘ x)
abbrev Equation3762 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ y) ∘ (y ∘ y)
abbrev Equation3763 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ y) ∘ (y ∘ z)
abbrev Equation3764 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ y) ∘ (z ∘ x)
abbrev Equation3765 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ y) ∘ (z ∘ y)
abbrev Equation3766 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ y) ∘ (z ∘ z)
abbrev Equation3767 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ y) ∘ (z ∘ w)
abbrev Equation3768 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ (x ∘ x)
abbrev Equation3769 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ (x ∘ y)
abbrev Equation3770 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ (x ∘ z)
abbrev Equation3771 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (x ∘ w)
abbrev Equation3772 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ (y ∘ x)
abbrev Equation3773 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ (y ∘ y)
abbrev Equation3774 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ (y ∘ z)
abbrev Equation3775 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (y ∘ w)
abbrev Equation3776 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ (z ∘ x)
abbrev Equation3777 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ (z ∘ y)
abbrev Equation3778 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ z) ∘ (z ∘ z)
abbrev Equation3779 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (z ∘ w)
abbrev Equation3780 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (w ∘ x)
abbrev Equation3781 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (w ∘ y)
abbrev Equation3782 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (w ∘ z)
abbrev Equation3783 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ z) ∘ (w ∘ w)
abbrev Equation3784 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (y ∘ z) ∘ (w ∘ u)
abbrev Equation3785 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ (x ∘ x)
abbrev Equation3786 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ (x ∘ y)
abbrev Equation3787 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ (x ∘ z)
abbrev Equation3788 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (x ∘ w)
abbrev Equation3789 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ (y ∘ x)
abbrev Equation3790 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ (y ∘ y)
abbrev Equation3791 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ (y ∘ z)
abbrev Equation3792 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (y ∘ w)
abbrev Equation3793 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ (z ∘ x)
abbrev Equation3794 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ (z ∘ y)
abbrev Equation3795 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ x) ∘ (z ∘ z)
abbrev Equation3796 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (z ∘ w)
abbrev Equation3797 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (w ∘ x)
abbrev Equation3798 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (w ∘ y)
abbrev Equation3799 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (w ∘ z)
abbrev Equation3800 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ x) ∘ (w ∘ w)
abbrev Equation3801 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ x) ∘ (w ∘ u)
abbrev Equation3802 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ (x ∘ x)
abbrev Equation3803 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ (x ∘ y)
abbrev Equation3804 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ (x ∘ z)
abbrev Equation3805 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (x ∘ w)
abbrev Equation3806 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ (y ∘ x)
abbrev Equation3807 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ (y ∘ y)
abbrev Equation3808 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ (y ∘ z)
abbrev Equation3809 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (y ∘ w)
abbrev Equation3810 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ (z ∘ x)
abbrev Equation3811 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ (z ∘ y)
abbrev Equation3812 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ y) ∘ (z ∘ z)
abbrev Equation3813 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (z ∘ w)
abbrev Equation3814 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (w ∘ x)
abbrev Equation3815 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (w ∘ y)
abbrev Equation3816 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (w ∘ z)
abbrev Equation3817 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ y) ∘ (w ∘ w)
abbrev Equation3818 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ y) ∘ (w ∘ u)
abbrev Equation3819 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (x ∘ x)
abbrev Equation3820 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (x ∘ y)
abbrev Equation3821 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (x ∘ z)
abbrev Equation3822 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (x ∘ w)
abbrev Equation3823 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (y ∘ x)
abbrev Equation3824 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (y ∘ y)
abbrev Equation3825 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (y ∘ z)
abbrev Equation3826 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (y ∘ w)
abbrev Equation3827 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (z ∘ x)
abbrev Equation3828 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (z ∘ y)
abbrev Equation3829 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ z) ∘ (z ∘ z)
abbrev Equation3830 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (z ∘ w)
abbrev Equation3831 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (w ∘ x)
abbrev Equation3832 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (w ∘ y)
abbrev Equation3833 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (w ∘ z)
abbrev Equation3834 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ z) ∘ (w ∘ w)
abbrev Equation3835 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ z) ∘ (w ∘ u)
abbrev Equation3836 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (x ∘ x)
abbrev Equation3837 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (x ∘ y)
abbrev Equation3838 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (x ∘ z)
abbrev Equation3839 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (x ∘ w)
abbrev Equation3840 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (x ∘ u)
abbrev Equation3841 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (y ∘ x)
abbrev Equation3842 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (y ∘ y)
abbrev Equation3843 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (y ∘ z)
abbrev Equation3844 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (y ∘ w)
abbrev Equation3845 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (y ∘ u)
abbrev Equation3846 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (z ∘ x)
abbrev Equation3847 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (z ∘ y)
abbrev Equation3848 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (z ∘ z)
abbrev Equation3849 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (z ∘ w)
abbrev Equation3850 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (z ∘ u)
abbrev Equation3851 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (w ∘ x)
abbrev Equation3852 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (w ∘ y)
abbrev Equation3853 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (w ∘ z)
abbrev Equation3854 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ w) ∘ (w ∘ w)
abbrev Equation3855 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (w ∘ u)
abbrev Equation3856 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (u ∘ x)
abbrev Equation3857 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (u ∘ y)
abbrev Equation3858 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (u ∘ z)
abbrev Equation3859 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (u ∘ w)
abbrev Equation3860 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ w) ∘ (u ∘ u)
abbrev Equation3861 (G: Type u) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ w) ∘ (u ∘ v)
abbrev Equation3862 (G: Type u) [Magma G] := ∀ x : G, x ∘ x = (x ∘ (x ∘ x)) ∘ x
abbrev Equation3863 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ (x ∘ x)) ∘ y
abbrev Equation3864 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ (x ∘ y)) ∘ x
abbrev Equation3865 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ (x ∘ y)) ∘ y
abbrev Equation3866 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ (x ∘ y)) ∘ z
abbrev Equation3867 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ (y ∘ x)) ∘ x
abbrev Equation3868 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ (y ∘ x)) ∘ y
abbrev Equation3869 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ (y ∘ x)) ∘ z
abbrev Equation3870 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ (y ∘ y)) ∘ x
abbrev Equation3871 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (x ∘ (y ∘ y)) ∘ y
abbrev Equation3872 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ (y ∘ y)) ∘ z
abbrev Equation3873 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ (y ∘ z)) ∘ x
abbrev Equation3874 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ (y ∘ z)) ∘ y
abbrev Equation3875 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (x ∘ (y ∘ z)) ∘ z
abbrev Equation3876 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = (x ∘ (y ∘ z)) ∘ w
abbrev Equation3877 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ (x ∘ x)) ∘ x
abbrev Equation3878 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ (x ∘ x)) ∘ y
abbrev Equation3879 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (x ∘ x)) ∘ z
abbrev Equation3880 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ (x ∘ y)) ∘ x
abbrev Equation3881 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ (x ∘ y)) ∘ y
abbrev Equation3882 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (x ∘ y)) ∘ z
abbrev Equation3883 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (x ∘ z)) ∘ x
abbrev Equation3884 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (x ∘ z)) ∘ y
abbrev Equation3885 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (x ∘ z)) ∘ z
abbrev Equation3886 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (x ∘ z)) ∘ w
abbrev Equation3887 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ (y ∘ x)) ∘ x
abbrev Equation3888 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ (y ∘ x)) ∘ y
abbrev Equation3889 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (y ∘ x)) ∘ z
abbrev Equation3890 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ (y ∘ y)) ∘ x
abbrev Equation3891 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = (y ∘ (y ∘ y)) ∘ y
abbrev Equation3892 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (y ∘ y)) ∘ z
abbrev Equation3893 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (y ∘ z)) ∘ x
abbrev Equation3894 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (y ∘ z)) ∘ y
abbrev Equation3895 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (y ∘ z)) ∘ z
abbrev Equation3896 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (y ∘ z)) ∘ w
abbrev Equation3897 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (z ∘ x)) ∘ x
abbrev Equation3898 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (z ∘ x)) ∘ y
abbrev Equation3899 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (z ∘ x)) ∘ z
abbrev Equation3900 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ x)) ∘ w
abbrev Equation3901 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (z ∘ y)) ∘ x
abbrev Equation3902 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (z ∘ y)) ∘ y
abbrev Equation3903 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (z ∘ y)) ∘ z
abbrev Equation3904 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ y)) ∘ w
abbrev Equation3905 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (z ∘ z)) ∘ x
abbrev Equation3906 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (z ∘ z)) ∘ y
abbrev Equation3907 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = (y ∘ (z ∘ z)) ∘ z
abbrev Equation3908 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ z)) ∘ w
abbrev Equation3909 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ w)) ∘ x
abbrev Equation3910 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ w)) ∘ y
abbrev Equation3911 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ w)) ∘ z
abbrev Equation3912 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = (y ∘ (z ∘ w)) ∘ w
abbrev Equation3913 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ x = (y ∘ (z ∘ w)) ∘ u
abbrev Equation3914 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (x ∘ x)) ∘ x
abbrev Equation3915 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (x ∘ x)) ∘ y
abbrev Equation3916 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (x ∘ x)) ∘ z
abbrev Equation3917 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (x ∘ y)) ∘ x
abbrev Equation3918 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (x ∘ y)) ∘ y
abbrev Equation3919 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (x ∘ y)) ∘ z
abbrev Equation3920 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (x ∘ z)) ∘ x
abbrev Equation3921 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (x ∘ z)) ∘ y
abbrev Equation3922 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (x ∘ z)) ∘ z
abbrev Equation3923 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (x ∘ z)) ∘ w
abbrev Equation3924 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (y ∘ x)) ∘ x
abbrev Equation3925 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (y ∘ x)) ∘ y
abbrev Equation3926 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (y ∘ x)) ∘ z
abbrev Equation3927 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (y ∘ y)) ∘ x
abbrev Equation3928 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (x ∘ (y ∘ y)) ∘ y
abbrev Equation3929 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (y ∘ y)) ∘ z
abbrev Equation3930 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (y ∘ z)) ∘ x
abbrev Equation3931 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (y ∘ z)) ∘ y
abbrev Equation3932 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (y ∘ z)) ∘ z
abbrev Equation3933 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (y ∘ z)) ∘ w
abbrev Equation3934 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (z ∘ x)) ∘ x
abbrev Equation3935 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (z ∘ x)) ∘ y
abbrev Equation3936 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (z ∘ x)) ∘ z
abbrev Equation3937 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ x)) ∘ w
abbrev Equation3938 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (z ∘ y)) ∘ x
abbrev Equation3939 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (z ∘ y)) ∘ y
abbrev Equation3940 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (z ∘ y)) ∘ z
abbrev Equation3941 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ y)) ∘ w
abbrev Equation3942 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (z ∘ z)) ∘ x
abbrev Equation3943 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (z ∘ z)) ∘ y
abbrev Equation3944 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (x ∘ (z ∘ z)) ∘ z
abbrev Equation3945 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ z)) ∘ w
abbrev Equation3946 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ w)) ∘ x
abbrev Equation3947 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ w)) ∘ y
abbrev Equation3948 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ w)) ∘ z
abbrev Equation3949 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (x ∘ (z ∘ w)) ∘ w
abbrev Equation3950 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (x ∘ (z ∘ w)) ∘ u
abbrev Equation3951 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ (x ∘ x)) ∘ x
abbrev Equation3952 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ (x ∘ x)) ∘ y
abbrev Equation3953 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (x ∘ x)) ∘ z
abbrev Equation3954 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ (x ∘ y)) ∘ x
abbrev Equation3955 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ (x ∘ y)) ∘ y
abbrev Equation3956 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (x ∘ y)) ∘ z
abbrev Equation3957 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (x ∘ z)) ∘ x
abbrev Equation3958 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (x ∘ z)) ∘ y
abbrev Equation3959 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (x ∘ z)) ∘ z
abbrev Equation3960 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (x ∘ z)) ∘ w
abbrev Equation3961 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ (y ∘ x)) ∘ x
abbrev Equation3962 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ (y ∘ x)) ∘ y
abbrev Equation3963 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (y ∘ x)) ∘ z
abbrev Equation3964 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ (y ∘ y)) ∘ x
abbrev Equation3965 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = (y ∘ (y ∘ y)) ∘ y
abbrev Equation3966 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (y ∘ y)) ∘ z
abbrev Equation3967 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (y ∘ z)) ∘ x
abbrev Equation3968 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (y ∘ z)) ∘ y
abbrev Equation3969 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (y ∘ z)) ∘ z
abbrev Equation3970 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (y ∘ z)) ∘ w
abbrev Equation3971 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (z ∘ x)) ∘ x
abbrev Equation3972 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (z ∘ x)) ∘ y
abbrev Equation3973 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (z ∘ x)) ∘ z
abbrev Equation3974 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ x)) ∘ w
abbrev Equation3975 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (z ∘ y)) ∘ x
abbrev Equation3976 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (z ∘ y)) ∘ y
abbrev Equation3977 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (z ∘ y)) ∘ z
abbrev Equation3978 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ y)) ∘ w
abbrev Equation3979 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (z ∘ z)) ∘ x
abbrev Equation3980 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (z ∘ z)) ∘ y
abbrev Equation3981 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (y ∘ (z ∘ z)) ∘ z
abbrev Equation3982 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ z)) ∘ w
abbrev Equation3983 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ w)) ∘ x
abbrev Equation3984 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ w)) ∘ y
abbrev Equation3985 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ w)) ∘ z
abbrev Equation3986 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (y ∘ (z ∘ w)) ∘ w
abbrev Equation3987 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (y ∘ (z ∘ w)) ∘ u
abbrev Equation3988 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (x ∘ x)) ∘ x
abbrev Equation3989 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (x ∘ x)) ∘ y
abbrev Equation3990 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (x ∘ x)) ∘ z
abbrev Equation3991 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ x)) ∘ w
abbrev Equation3992 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (x ∘ y)) ∘ x
abbrev Equation3993 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (x ∘ y)) ∘ y
abbrev Equation3994 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (x ∘ y)) ∘ z
abbrev Equation3995 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ y)) ∘ w
abbrev Equation3996 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (x ∘ z)) ∘ x
abbrev Equation3997 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (x ∘ z)) ∘ y
abbrev Equation3998 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (x ∘ z)) ∘ z
abbrev Equation3999 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ z)) ∘ w
abbrev Equation4000 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ w)) ∘ x
abbrev Equation4001 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ w)) ∘ y
abbrev Equation4002 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ w)) ∘ z
abbrev Equation4003 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (x ∘ w)) ∘ w
abbrev Equation4004 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (x ∘ w)) ∘ u
abbrev Equation4005 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (y ∘ x)) ∘ x
abbrev Equation4006 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (y ∘ x)) ∘ y
abbrev Equation4007 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (y ∘ x)) ∘ z
abbrev Equation4008 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ x)) ∘ w
abbrev Equation4009 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (y ∘ y)) ∘ x
abbrev Equation4010 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (y ∘ y)) ∘ y
abbrev Equation4011 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (y ∘ y)) ∘ z
abbrev Equation4012 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ y)) ∘ w
abbrev Equation4013 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (y ∘ z)) ∘ x
abbrev Equation4014 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (y ∘ z)) ∘ y
abbrev Equation4015 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (y ∘ z)) ∘ z
abbrev Equation4016 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ z)) ∘ w
abbrev Equation4017 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ w)) ∘ x
abbrev Equation4018 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ w)) ∘ y
abbrev Equation4019 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ w)) ∘ z
abbrev Equation4020 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (y ∘ w)) ∘ w
abbrev Equation4021 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (y ∘ w)) ∘ u
abbrev Equation4022 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ x)) ∘ x
abbrev Equation4023 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ x)) ∘ y
abbrev Equation4024 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ x)) ∘ z
abbrev Equation4025 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ x)) ∘ w
abbrev Equation4026 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ y)) ∘ x
abbrev Equation4027 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ y)) ∘ y
abbrev Equation4028 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ y)) ∘ z
abbrev Equation4029 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ y)) ∘ w
abbrev Equation4030 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ z)) ∘ x
abbrev Equation4031 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ z)) ∘ y
abbrev Equation4032 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = (z ∘ (z ∘ z)) ∘ z
abbrev Equation4033 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ z)) ∘ w
abbrev Equation4034 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ w)) ∘ x
abbrev Equation4035 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ w)) ∘ y
abbrev Equation4036 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ w)) ∘ z
abbrev Equation4037 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (z ∘ w)) ∘ w
abbrev Equation4038 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (z ∘ w)) ∘ u
abbrev Equation4039 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ x)) ∘ x
abbrev Equation4040 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ x)) ∘ y
abbrev Equation4041 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ x)) ∘ z
abbrev Equation4042 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ x)) ∘ w
abbrev Equation4043 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ x)) ∘ u
abbrev Equation4044 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ y)) ∘ x
abbrev Equation4045 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ y)) ∘ y
abbrev Equation4046 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ y)) ∘ z
abbrev Equation4047 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ y)) ∘ w
abbrev Equation4048 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ y)) ∘ u
abbrev Equation4049 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ z)) ∘ x
abbrev Equation4050 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ z)) ∘ y
abbrev Equation4051 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ z)) ∘ z
abbrev Equation4052 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ z)) ∘ w
abbrev Equation4053 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ z)) ∘ u
abbrev Equation4054 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ w)) ∘ x
abbrev Equation4055 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ w)) ∘ y
abbrev Equation4056 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ w)) ∘ z
abbrev Equation4057 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = (z ∘ (w ∘ w)) ∘ w
abbrev Equation4058 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ w)) ∘ u
abbrev Equation4059 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ u)) ∘ x
abbrev Equation4060 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ u)) ∘ y
abbrev Equation4061 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ u)) ∘ z
abbrev Equation4062 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ u)) ∘ w
abbrev Equation4063 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = (z ∘ (w ∘ u)) ∘ u
abbrev Equation4064 (G: Type u) [Magma G] := ∀ x y z w u v : G, x ∘ y = (z ∘ (w ∘ u)) ∘ v
abbrev Equation4065 (G: Type u) [Magma G] := ∀ x : G, x ∘ x = ((x ∘ x) ∘ x) ∘ x
abbrev Equation4066 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = ((x ∘ x) ∘ x) ∘ y
abbrev Equation4067 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = ((x ∘ x) ∘ y) ∘ x
abbrev Equation4068 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = ((x ∘ x) ∘ y) ∘ y
abbrev Equation4069 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = ((x ∘ x) ∘ y) ∘ z
abbrev Equation4070 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = ((x ∘ y) ∘ x) ∘ x
abbrev Equation4071 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = ((x ∘ y) ∘ x) ∘ y
abbrev Equation4072 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = ((x ∘ y) ∘ x) ∘ z
abbrev Equation4073 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = ((x ∘ y) ∘ y) ∘ x
abbrev Equation4074 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = ((x ∘ y) ∘ y) ∘ y
abbrev Equation4075 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = ((x ∘ y) ∘ y) ∘ z
abbrev Equation4076 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = ((x ∘ y) ∘ z) ∘ x
abbrev Equation4077 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = ((x ∘ y) ∘ z) ∘ y
abbrev Equation4078 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = ((x ∘ y) ∘ z) ∘ z
abbrev Equation4079 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = ((x ∘ y) ∘ z) ∘ w
abbrev Equation4080 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = ((y ∘ x) ∘ x) ∘ x
abbrev Equation4081 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = ((y ∘ x) ∘ x) ∘ y
abbrev Equation4082 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ x) ∘ x) ∘ z
abbrev Equation4083 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = ((y ∘ x) ∘ y) ∘ x
abbrev Equation4084 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = ((y ∘ x) ∘ y) ∘ y
abbrev Equation4085 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ x) ∘ y) ∘ z
abbrev Equation4086 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ x) ∘ z) ∘ x
abbrev Equation4087 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ x) ∘ z) ∘ y
abbrev Equation4088 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ x) ∘ z) ∘ z
abbrev Equation4089 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ x) ∘ z) ∘ w
abbrev Equation4090 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = ((y ∘ y) ∘ x) ∘ x
abbrev Equation4091 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = ((y ∘ y) ∘ x) ∘ y
abbrev Equation4092 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ y) ∘ x) ∘ z
abbrev Equation4093 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = ((y ∘ y) ∘ y) ∘ x
abbrev Equation4094 (G: Type u) [Magma G] := ∀ x y : G, x ∘ x = ((y ∘ y) ∘ y) ∘ y
abbrev Equation4095 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ y) ∘ y) ∘ z
abbrev Equation4096 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ y) ∘ z) ∘ x
abbrev Equation4097 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ y) ∘ z) ∘ y
abbrev Equation4098 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ y) ∘ z) ∘ z
abbrev Equation4099 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ y) ∘ z) ∘ w
abbrev Equation4100 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ z) ∘ x) ∘ x
abbrev Equation4101 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ z) ∘ x) ∘ y
abbrev Equation4102 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ z) ∘ x) ∘ z
abbrev Equation4103 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ x) ∘ w
abbrev Equation4104 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ z) ∘ y) ∘ x
abbrev Equation4105 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ z) ∘ y) ∘ y
abbrev Equation4106 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ z) ∘ y) ∘ z
abbrev Equation4107 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ y) ∘ w
abbrev Equation4108 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ z) ∘ z) ∘ x
abbrev Equation4109 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ z) ∘ z) ∘ y
abbrev Equation4110 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ x = ((y ∘ z) ∘ z) ∘ z
abbrev Equation4111 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ z) ∘ w
abbrev Equation4112 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ w) ∘ x
abbrev Equation4113 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ w) ∘ y
abbrev Equation4114 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ w) ∘ z
abbrev Equation4115 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ x = ((y ∘ z) ∘ w) ∘ w
abbrev Equation4116 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ x = ((y ∘ z) ∘ w) ∘ u
abbrev Equation4117 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ x) ∘ x) ∘ x
abbrev Equation4118 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ x) ∘ x) ∘ y
abbrev Equation4119 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ x) ∘ x) ∘ z
abbrev Equation4120 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ x) ∘ y) ∘ x
abbrev Equation4121 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ x) ∘ y) ∘ y
abbrev Equation4122 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ x) ∘ y) ∘ z
abbrev Equation4123 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ x) ∘ z) ∘ x
abbrev Equation4124 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ x) ∘ z) ∘ y
abbrev Equation4125 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ x) ∘ z) ∘ z
abbrev Equation4126 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ x) ∘ z) ∘ w
abbrev Equation4127 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ y) ∘ x) ∘ x
abbrev Equation4128 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ y) ∘ x) ∘ y
abbrev Equation4129 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ y) ∘ x) ∘ z
abbrev Equation4130 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ y) ∘ y) ∘ x
abbrev Equation4131 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = ((x ∘ y) ∘ y) ∘ y
abbrev Equation4132 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ y) ∘ y) ∘ z
abbrev Equation4133 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ y) ∘ z) ∘ x
abbrev Equation4134 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ y) ∘ z) ∘ y
abbrev Equation4135 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ y) ∘ z) ∘ z
abbrev Equation4136 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ y) ∘ z) ∘ w
abbrev Equation4137 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ z) ∘ x) ∘ x
abbrev Equation4138 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ z) ∘ x) ∘ y
abbrev Equation4139 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ z) ∘ x) ∘ z
abbrev Equation4140 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ x) ∘ w
abbrev Equation4141 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ z) ∘ y) ∘ x
abbrev Equation4142 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ z) ∘ y) ∘ y
abbrev Equation4143 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ z) ∘ y) ∘ z
abbrev Equation4144 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ y) ∘ w
abbrev Equation4145 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ z) ∘ z) ∘ x
abbrev Equation4146 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ z) ∘ z) ∘ y
abbrev Equation4147 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((x ∘ z) ∘ z) ∘ z
abbrev Equation4148 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ z) ∘ w
abbrev Equation4149 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ w) ∘ x
abbrev Equation4150 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ w) ∘ y
abbrev Equation4151 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ w) ∘ z
abbrev Equation4152 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((x ∘ z) ∘ w) ∘ w
abbrev Equation4153 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = ((x ∘ z) ∘ w) ∘ u
abbrev Equation4154 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = ((y ∘ x) ∘ x) ∘ x
abbrev Equation4155 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = ((y ∘ x) ∘ x) ∘ y
abbrev Equation4156 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ x) ∘ x) ∘ z
abbrev Equation4157 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = ((y ∘ x) ∘ y) ∘ x
abbrev Equation4158 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = ((y ∘ x) ∘ y) ∘ y
abbrev Equation4159 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ x) ∘ y) ∘ z
abbrev Equation4160 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ x) ∘ z) ∘ x
abbrev Equation4161 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ x) ∘ z) ∘ y
abbrev Equation4162 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ x) ∘ z) ∘ z
abbrev Equation4163 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ x) ∘ z) ∘ w
abbrev Equation4164 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = ((y ∘ y) ∘ x) ∘ x
abbrev Equation4165 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = ((y ∘ y) ∘ x) ∘ y
abbrev Equation4166 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ y) ∘ x) ∘ z
abbrev Equation4167 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = ((y ∘ y) ∘ y) ∘ x
abbrev Equation4168 (G: Type u) [Magma G] := ∀ x y : G, x ∘ y = ((y ∘ y) ∘ y) ∘ y
abbrev Equation4169 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ y) ∘ y) ∘ z
abbrev Equation4170 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ y) ∘ z) ∘ x
abbrev Equation4171 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ y) ∘ z) ∘ y
abbrev Equation4172 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ y) ∘ z) ∘ z
abbrev Equation4173 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ y) ∘ z) ∘ w
abbrev Equation4174 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ z) ∘ x) ∘ x
abbrev Equation4175 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ z) ∘ x) ∘ y
abbrev Equation4176 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ z) ∘ x) ∘ z
abbrev Equation4177 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ x) ∘ w
abbrev Equation4178 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ z) ∘ y) ∘ x
abbrev Equation4179 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ z) ∘ y) ∘ y
abbrev Equation4180 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ z) ∘ y) ∘ z
abbrev Equation4181 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ y) ∘ w
abbrev Equation4182 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ z) ∘ z) ∘ x
abbrev Equation4183 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ z) ∘ z) ∘ y
abbrev Equation4184 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((y ∘ z) ∘ z) ∘ z
abbrev Equation4185 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ z) ∘ w
abbrev Equation4186 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ w) ∘ x
abbrev Equation4187 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ w) ∘ y
abbrev Equation4188 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ w) ∘ z
abbrev Equation4189 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((y ∘ z) ∘ w) ∘ w
abbrev Equation4190 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = ((y ∘ z) ∘ w) ∘ u
abbrev Equation4191 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ x) ∘ x) ∘ x
abbrev Equation4192 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ x) ∘ x) ∘ y
abbrev Equation4193 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ x) ∘ x) ∘ z
abbrev Equation4194 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ x) ∘ w
abbrev Equation4195 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ x) ∘ y) ∘ x
abbrev Equation4196 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ x) ∘ y) ∘ y
abbrev Equation4197 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ x) ∘ y) ∘ z
abbrev Equation4198 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ y) ∘ w
abbrev Equation4199 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ x) ∘ z) ∘ x
abbrev Equation4200 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ x) ∘ z) ∘ y
abbrev Equation4201 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ x) ∘ z) ∘ z
abbrev Equation4202 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ z) ∘ w
abbrev Equation4203 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ w) ∘ x
abbrev Equation4204 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ w) ∘ y
abbrev Equation4205 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ w) ∘ z
abbrev Equation4206 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ x) ∘ w) ∘ w
abbrev Equation4207 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ x) ∘ w) ∘ u
abbrev Equation4208 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ y) ∘ x) ∘ x
abbrev Equation4209 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ y) ∘ x) ∘ y
abbrev Equation4210 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ y) ∘ x) ∘ z
abbrev Equation4211 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ x) ∘ w
abbrev Equation4212 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ y) ∘ y) ∘ x
abbrev Equation4213 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ y) ∘ y) ∘ y
abbrev Equation4214 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ y) ∘ y) ∘ z
abbrev Equation4215 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ y) ∘ w
abbrev Equation4216 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ y) ∘ z) ∘ x
abbrev Equation4217 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ y) ∘ z) ∘ y
abbrev Equation4218 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ y) ∘ z) ∘ z
abbrev Equation4219 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ z) ∘ w
abbrev Equation4220 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ w) ∘ x
abbrev Equation4221 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ w) ∘ y
abbrev Equation4222 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ w) ∘ z
abbrev Equation4223 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ y) ∘ w) ∘ w
abbrev Equation4224 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ y) ∘ w) ∘ u
abbrev Equation4225 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ x) ∘ x
abbrev Equation4226 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ x) ∘ y
abbrev Equation4227 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ x) ∘ z
abbrev Equation4228 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ x) ∘ w
abbrev Equation4229 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ y) ∘ x
abbrev Equation4230 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ y) ∘ y
abbrev Equation4231 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ y) ∘ z
abbrev Equation4232 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ y) ∘ w
abbrev Equation4233 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ z) ∘ x
abbrev Equation4234 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ z) ∘ y
abbrev Equation4235 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ y = ((z ∘ z) ∘ z) ∘ z
abbrev Equation4236 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ z) ∘ w
abbrev Equation4237 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ w) ∘ x
abbrev Equation4238 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ w) ∘ y
abbrev Equation4239 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ w) ∘ z
abbrev Equation4240 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ z) ∘ w) ∘ w
abbrev Equation4241 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ z) ∘ w) ∘ u
abbrev Equation4242 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ x) ∘ x
abbrev Equation4243 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ x) ∘ y
abbrev Equation4244 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ x) ∘ z
abbrev Equation4245 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ x) ∘ w
abbrev Equation4246 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ x) ∘ u
abbrev Equation4247 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ y) ∘ x
abbrev Equation4248 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ y) ∘ y
abbrev Equation4249 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ y) ∘ z
abbrev Equation4250 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ y) ∘ w
abbrev Equation4251 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ y) ∘ u
abbrev Equation4252 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ z) ∘ x
abbrev Equation4253 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ z) ∘ y
abbrev Equation4254 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ z) ∘ z
abbrev Equation4255 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ z) ∘ w
abbrev Equation4256 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ z) ∘ u
abbrev Equation4257 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ w) ∘ x
abbrev Equation4258 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ w) ∘ y
abbrev Equation4259 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ w) ∘ z
abbrev Equation4260 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ y = ((z ∘ w) ∘ w) ∘ w
abbrev Equation4261 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ w) ∘ u
abbrev Equation4262 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ u) ∘ x
abbrev Equation4263 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ u) ∘ y
abbrev Equation4264 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ u) ∘ z
abbrev Equation4265 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ u) ∘ w
abbrev Equation4266 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ y = ((z ∘ w) ∘ u) ∘ u
abbrev Equation4267 (G: Type u) [Magma G] := ∀ x y z w u v : G, x ∘ y = ((z ∘ w) ∘ u) ∘ v
abbrev Equation4268 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = x ∘ (x ∘ y)
abbrev Equation4269 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = x ∘ (y ∘ x)
abbrev Equation4270 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = x ∘ (y ∘ y)
abbrev Equation4271 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ x) = x ∘ (y ∘ z)
abbrev Equation4272 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = y ∘ (x ∘ x)
abbrev Equation4273 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = y ∘ (x ∘ y)
abbrev Equation4274 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ x) = y ∘ (x ∘ z)
abbrev Equation4275 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = y ∘ (y ∘ x)
abbrev Equation4276 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = y ∘ (y ∘ y)
abbrev Equation4277 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ x) = y ∘ (y ∘ z)
abbrev Equation4278 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ x) = y ∘ (z ∘ x)
abbrev Equation4279 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ x) = y ∘ (z ∘ y)
abbrev Equation4280 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ x) = y ∘ (z ∘ z)
abbrev Equation4281 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ x) = y ∘ (z ∘ w)
abbrev Equation4282 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = x ∘ (x ∘ z)
abbrev Equation4283 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = x ∘ (y ∘ x)
abbrev Equation4284 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = x ∘ (y ∘ y)
abbrev Equation4285 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = x ∘ (y ∘ z)
abbrev Equation4286 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = x ∘ (z ∘ x)
abbrev Equation4287 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = x ∘ (z ∘ y)
abbrev Equation4288 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = x ∘ (z ∘ z)
abbrev Equation4289 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = x ∘ (z ∘ w)
abbrev Equation4290 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = y ∘ (x ∘ x)
abbrev Equation4291 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = y ∘ (x ∘ y)
abbrev Equation4292 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = y ∘ (x ∘ z)
abbrev Equation4293 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = y ∘ (y ∘ x)
abbrev Equation4294 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = y ∘ (y ∘ z)
abbrev Equation4295 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = y ∘ (z ∘ x)
abbrev Equation4296 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = y ∘ (z ∘ y)
abbrev Equation4297 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = y ∘ (z ∘ z)
abbrev Equation4298 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = y ∘ (z ∘ w)
abbrev Equation4299 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = z ∘ (x ∘ x)
abbrev Equation4300 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = z ∘ (x ∘ y)
abbrev Equation4301 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = z ∘ (x ∘ z)
abbrev Equation4302 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (x ∘ w)
abbrev Equation4303 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = z ∘ (y ∘ x)
abbrev Equation4304 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = z ∘ (y ∘ y)
abbrev Equation4305 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = z ∘ (y ∘ z)
abbrev Equation4306 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (y ∘ w)
abbrev Equation4307 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = z ∘ (z ∘ y)
abbrev Equation4308 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (z ∘ w)
abbrev Equation4309 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (w ∘ x)
abbrev Equation4310 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (w ∘ y)
abbrev Equation4311 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (w ∘ z)
abbrev Equation4312 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = z ∘ (w ∘ w)
abbrev Equation4313 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ (x ∘ y) = z ∘ (w ∘ u)
abbrev Equation4314 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = x ∘ (y ∘ y)
abbrev Equation4315 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = x ∘ (y ∘ z)
abbrev Equation4316 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = x ∘ (z ∘ x)
abbrev Equation4317 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = x ∘ (z ∘ y)
abbrev Equation4318 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = x ∘ (z ∘ z)
abbrev Equation4319 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = x ∘ (z ∘ w)
abbrev Equation4320 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = y ∘ (x ∘ x)
abbrev Equation4321 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = y ∘ (x ∘ y)
abbrev Equation4322 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = y ∘ (x ∘ z)
abbrev Equation4323 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = y ∘ (z ∘ x)
abbrev Equation4324 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = y ∘ (z ∘ y)
abbrev Equation4325 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = y ∘ (z ∘ z)
abbrev Equation4326 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = y ∘ (z ∘ w)
abbrev Equation4327 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = z ∘ (x ∘ x)
abbrev Equation4328 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = z ∘ (x ∘ y)
abbrev Equation4329 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = z ∘ (x ∘ w)
abbrev Equation4330 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = z ∘ (y ∘ x)
abbrev Equation4331 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = z ∘ (y ∘ y)
abbrev Equation4332 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = z ∘ (y ∘ z)
abbrev Equation4333 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = z ∘ (y ∘ w)
abbrev Equation4334 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = z ∘ (w ∘ x)
abbrev Equation4335 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = z ∘ (w ∘ y)
abbrev Equation4336 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = z ∘ (w ∘ z)
abbrev Equation4337 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = z ∘ (w ∘ w)
abbrev Equation4338 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ x) = z ∘ (w ∘ u)
abbrev Equation4339 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = x ∘ (y ∘ z)
abbrev Equation4340 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = x ∘ (z ∘ y)
abbrev Equation4341 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = x ∘ (z ∘ z)
abbrev Equation4342 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = x ∘ (z ∘ w)
abbrev Equation4343 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = y ∘ (x ∘ x)
abbrev Equation4344 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = y ∘ (x ∘ z)
abbrev Equation4345 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = y ∘ (z ∘ x)
abbrev Equation4346 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = y ∘ (z ∘ z)
abbrev Equation4347 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = y ∘ (z ∘ w)
abbrev Equation4348 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = z ∘ (x ∘ y)
abbrev Equation4349 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = z ∘ (x ∘ w)
abbrev Equation4350 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = z ∘ (y ∘ x)
abbrev Equation4351 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = z ∘ (y ∘ y)
abbrev Equation4352 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = z ∘ (y ∘ w)
abbrev Equation4353 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = z ∘ (w ∘ x)
abbrev Equation4354 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = z ∘ (w ∘ y)
abbrev Equation4355 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = z ∘ (w ∘ w)
abbrev Equation4356 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ y) = z ∘ (w ∘ u)
abbrev Equation4357 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = x ∘ (y ∘ w)
abbrev Equation4358 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = x ∘ (z ∘ y)
abbrev Equation4359 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = x ∘ (z ∘ w)
abbrev Equation4360 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = x ∘ (w ∘ z)
abbrev Equation4361 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = x ∘ (w ∘ u)
abbrev Equation4362 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = y ∘ (x ∘ z)
abbrev Equation4363 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = y ∘ (x ∘ w)
abbrev Equation4364 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = y ∘ (z ∘ x)
abbrev Equation4365 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = y ∘ (z ∘ w)
abbrev Equation4366 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = y ∘ (w ∘ x)
abbrev Equation4367 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = y ∘ (w ∘ z)
abbrev Equation4368 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = y ∘ (w ∘ u)
abbrev Equation4369 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = z ∘ (y ∘ x)
abbrev Equation4370 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = z ∘ (y ∘ w)
abbrev Equation4371 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = z ∘ (w ∘ x)
abbrev Equation4372 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = z ∘ (w ∘ y)
abbrev Equation4373 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = z ∘ (w ∘ u)
abbrev Equation4374 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = w ∘ (y ∘ z)
abbrev Equation4375 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = w ∘ (y ∘ u)
abbrev Equation4376 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = w ∘ (z ∘ y)
abbrev Equation4377 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = w ∘ (z ∘ u)
abbrev Equation4378 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = w ∘ (u ∘ z)
abbrev Equation4379 (G: Type u) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = w ∘ (u ∘ v)
abbrev Equation4380 (G: Type u) [Magma G] := ∀ x : G, x ∘ (x ∘ x) = (x ∘ x) ∘ x
abbrev Equation4381 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = (x ∘ x) ∘ y
abbrev Equation4382 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = (x ∘ y) ∘ x
abbrev Equation4383 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = (x ∘ y) ∘ y
abbrev Equation4384 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ x) = (x ∘ y) ∘ z
abbrev Equation4385 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = (y ∘ x) ∘ x
abbrev Equation4386 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = (y ∘ x) ∘ y
abbrev Equation4387 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ x) = (y ∘ x) ∘ z
abbrev Equation4388 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = (y ∘ y) ∘ x
abbrev Equation4389 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ x) = (y ∘ y) ∘ y
abbrev Equation4390 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ x) = (y ∘ y) ∘ z
abbrev Equation4391 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ x) = (y ∘ z) ∘ x
abbrev Equation4392 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ x) = (y ∘ z) ∘ y
abbrev Equation4393 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ x) = (y ∘ z) ∘ z
abbrev Equation4394 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ x) = (y ∘ z) ∘ w
abbrev Equation4395 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = (x ∘ x) ∘ x
abbrev Equation4396 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = (x ∘ x) ∘ y
abbrev Equation4397 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (x ∘ x) ∘ z
abbrev Equation4398 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = (x ∘ y) ∘ x
abbrev Equation4399 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = (x ∘ y) ∘ y
abbrev Equation4400 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (x ∘ y) ∘ z
abbrev Equation4401 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (x ∘ z) ∘ x
abbrev Equation4402 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (x ∘ z) ∘ y
abbrev Equation4403 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (x ∘ z) ∘ z
abbrev Equation4404 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (x ∘ z) ∘ w
abbrev Equation4405 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = (y ∘ x) ∘ x
abbrev Equation4406 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = (y ∘ x) ∘ y
abbrev Equation4407 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (y ∘ x) ∘ z
abbrev Equation4408 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = (y ∘ y) ∘ x
abbrev Equation4409 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (x ∘ y) = (y ∘ y) ∘ y
abbrev Equation4410 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (y ∘ y) ∘ z
abbrev Equation4411 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (y ∘ z) ∘ x
abbrev Equation4412 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (y ∘ z) ∘ y
abbrev Equation4413 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (y ∘ z) ∘ z
abbrev Equation4414 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (y ∘ z) ∘ w
abbrev Equation4415 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (z ∘ x) ∘ x
abbrev Equation4416 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (z ∘ x) ∘ y
abbrev Equation4417 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (z ∘ x) ∘ z
abbrev Equation4418 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ x) ∘ w
abbrev Equation4419 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (z ∘ y) ∘ x
abbrev Equation4420 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (z ∘ y) ∘ y
abbrev Equation4421 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (z ∘ y) ∘ z
abbrev Equation4422 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ y) ∘ w
abbrev Equation4423 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (z ∘ z) ∘ x
abbrev Equation4424 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (z ∘ z) ∘ y
abbrev Equation4425 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (x ∘ y) = (z ∘ z) ∘ z
abbrev Equation4426 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ z) ∘ w
abbrev Equation4427 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ w) ∘ x
abbrev Equation4428 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ w) ∘ y
abbrev Equation4429 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ w) ∘ z
abbrev Equation4430 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (x ∘ y) = (z ∘ w) ∘ w
abbrev Equation4431 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ (x ∘ y) = (z ∘ w) ∘ u
abbrev Equation4432 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (x ∘ x) ∘ x
abbrev Equation4433 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (x ∘ x) ∘ y
abbrev Equation4434 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (x ∘ x) ∘ z
abbrev Equation4435 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (x ∘ y) ∘ x
abbrev Equation4436 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (x ∘ y) ∘ y
abbrev Equation4437 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (x ∘ y) ∘ z
abbrev Equation4438 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (x ∘ z) ∘ x
abbrev Equation4439 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (x ∘ z) ∘ y
abbrev Equation4440 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (x ∘ z) ∘ z
abbrev Equation4441 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (x ∘ z) ∘ w
abbrev Equation4442 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (y ∘ x) ∘ x
abbrev Equation4443 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (y ∘ x) ∘ y
abbrev Equation4444 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (y ∘ x) ∘ z
abbrev Equation4445 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (y ∘ y) ∘ x
abbrev Equation4446 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (y ∘ x) = (y ∘ y) ∘ y
abbrev Equation4447 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (y ∘ y) ∘ z
abbrev Equation4448 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (y ∘ z) ∘ x
abbrev Equation4449 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (y ∘ z) ∘ y
abbrev Equation4450 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (y ∘ z) ∘ z
abbrev Equation4451 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (y ∘ z) ∘ w
abbrev Equation4452 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (z ∘ x) ∘ x
abbrev Equation4453 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (z ∘ x) ∘ y
abbrev Equation4454 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (z ∘ x) ∘ z
abbrev Equation4455 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ x) ∘ w
abbrev Equation4456 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (z ∘ y) ∘ x
abbrev Equation4457 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (z ∘ y) ∘ y
abbrev Equation4458 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (z ∘ y) ∘ z
abbrev Equation4459 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ y) ∘ w
abbrev Equation4460 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (z ∘ z) ∘ x
abbrev Equation4461 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (z ∘ z) ∘ y
abbrev Equation4462 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ x) = (z ∘ z) ∘ z
abbrev Equation4463 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ z) ∘ w
abbrev Equation4464 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ w) ∘ x
abbrev Equation4465 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ w) ∘ y
abbrev Equation4466 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ w) ∘ z
abbrev Equation4467 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ x) = (z ∘ w) ∘ w
abbrev Equation4468 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ x) = (z ∘ w) ∘ u
abbrev Equation4469 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = (x ∘ x) ∘ x
abbrev Equation4470 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = (x ∘ x) ∘ y
abbrev Equation4471 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (x ∘ x) ∘ z
abbrev Equation4472 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = (x ∘ y) ∘ x
abbrev Equation4473 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = (x ∘ y) ∘ y
abbrev Equation4474 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (x ∘ y) ∘ z
abbrev Equation4475 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (x ∘ z) ∘ x
abbrev Equation4476 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (x ∘ z) ∘ y
abbrev Equation4477 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (x ∘ z) ∘ z
abbrev Equation4478 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (x ∘ z) ∘ w
abbrev Equation4479 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = (y ∘ x) ∘ x
abbrev Equation4480 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = (y ∘ x) ∘ y
abbrev Equation4481 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (y ∘ x) ∘ z
abbrev Equation4482 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = (y ∘ y) ∘ x
abbrev Equation4483 (G: Type u) [Magma G] := ∀ x y : G, x ∘ (y ∘ y) = (y ∘ y) ∘ y
abbrev Equation4484 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (y ∘ y) ∘ z
abbrev Equation4485 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (y ∘ z) ∘ x
abbrev Equation4486 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (y ∘ z) ∘ y
abbrev Equation4487 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (y ∘ z) ∘ z
abbrev Equation4488 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (y ∘ z) ∘ w
abbrev Equation4489 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (z ∘ x) ∘ x
abbrev Equation4490 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (z ∘ x) ∘ y
abbrev Equation4491 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (z ∘ x) ∘ z
abbrev Equation4492 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ x) ∘ w
abbrev Equation4493 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (z ∘ y) ∘ x
abbrev Equation4494 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (z ∘ y) ∘ y
abbrev Equation4495 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (z ∘ y) ∘ z
abbrev Equation4496 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ y) ∘ w
abbrev Equation4497 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (z ∘ z) ∘ x
abbrev Equation4498 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (z ∘ z) ∘ y
abbrev Equation4499 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ y) = (z ∘ z) ∘ z
abbrev Equation4500 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ z) ∘ w
abbrev Equation4501 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ w) ∘ x
abbrev Equation4502 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ w) ∘ y
abbrev Equation4503 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ w) ∘ z
abbrev Equation4504 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ y) = (z ∘ w) ∘ w
abbrev Equation4505 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ y) = (z ∘ w) ∘ u
abbrev Equation4506 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ x) ∘ x
abbrev Equation4507 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ x) ∘ y
abbrev Equation4508 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ x) ∘ z
abbrev Equation4509 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ x) ∘ w
abbrev Equation4510 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ y) ∘ x
abbrev Equation4511 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ y) ∘ y
-- abbrev Equation4512 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ y) ∘ z
-- abbrev Equation4513 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ y) ∘ w
abbrev Equation4514 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ z) ∘ x
abbrev Equation4515 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ z) ∘ y
abbrev Equation4516 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (x ∘ z) ∘ z
abbrev Equation4517 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ z) ∘ w
abbrev Equation4518 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ w) ∘ x
abbrev Equation4519 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ w) ∘ y
abbrev Equation4520 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ w) ∘ z
abbrev Equation4521 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (x ∘ w) ∘ w
-- abbrev Equation4522 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (x ∘ w) ∘ u
abbrev Equation4523 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (y ∘ x) ∘ x
abbrev Equation4524 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (y ∘ x) ∘ y
abbrev Equation4525 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (y ∘ x) ∘ z
abbrev Equation4526 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ x) ∘ w
abbrev Equation4527 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (y ∘ y) ∘ x
abbrev Equation4528 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (y ∘ y) ∘ y
abbrev Equation4529 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (y ∘ y) ∘ z
abbrev Equation4530 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ y) ∘ w
abbrev Equation4531 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (y ∘ z) ∘ x
abbrev Equation4532 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (y ∘ z) ∘ y
abbrev Equation4533 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (y ∘ z) ∘ z
abbrev Equation4534 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ z) ∘ w
abbrev Equation4535 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ w) ∘ x
abbrev Equation4536 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ w) ∘ y
abbrev Equation4537 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ w) ∘ z
abbrev Equation4538 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (y ∘ w) ∘ w
abbrev Equation4539 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (y ∘ w) ∘ u
abbrev Equation4540 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ x) ∘ x
abbrev Equation4541 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ x) ∘ y
abbrev Equation4542 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ x) ∘ z
abbrev Equation4543 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ x) ∘ w
abbrev Equation4544 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ y) ∘ x
abbrev Equation4545 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ y) ∘ y
abbrev Equation4546 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ y) ∘ z
abbrev Equation4547 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ y) ∘ w
abbrev Equation4548 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ z) ∘ x
abbrev Equation4549 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ z) ∘ y
abbrev Equation4550 (G: Type u) [Magma G] := ∀ x y z : G, x ∘ (y ∘ z) = (z ∘ z) ∘ z
abbrev Equation4551 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ z) ∘ w
abbrev Equation4552 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ w) ∘ x
abbrev Equation4553 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ w) ∘ y
abbrev Equation4554 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ w) ∘ z
abbrev Equation4555 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (z ∘ w) ∘ w
abbrev Equation4556 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (z ∘ w) ∘ u
abbrev Equation4557 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ x) ∘ x
abbrev Equation4558 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ x) ∘ y
abbrev Equation4559 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ x) ∘ z
abbrev Equation4560 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ x) ∘ w
abbrev Equation4561 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ x) ∘ u
abbrev Equation4562 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ y) ∘ x
abbrev Equation4563 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ y) ∘ y
abbrev Equation4564 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ y) ∘ z
abbrev Equation4565 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ y) ∘ w
abbrev Equation4566 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ y) ∘ u
abbrev Equation4567 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ z) ∘ x
abbrev Equation4568 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ z) ∘ y
abbrev Equation4569 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ z) ∘ z
abbrev Equation4570 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ z) ∘ w
abbrev Equation4571 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ z) ∘ u
abbrev Equation4572 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ w) ∘ x
abbrev Equation4573 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ w) ∘ y
abbrev Equation4574 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ w) ∘ z
abbrev Equation4575 (G: Type u) [Magma G] := ∀ x y z w : G, x ∘ (y ∘ z) = (w ∘ w) ∘ w
abbrev Equation4576 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ w) ∘ u
abbrev Equation4577 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ u) ∘ x
abbrev Equation4578 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ u) ∘ y
abbrev Equation4579 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ u) ∘ z
abbrev Equation4580 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ u) ∘ w
abbrev Equation4581 (G: Type u) [Magma G] := ∀ x y z w u : G, x ∘ (y ∘ z) = (w ∘ u) ∘ u
-- abbrev Equation4582 (G: Type u) [Magma G] := ∀ x y z w u v : G, x ∘ (y ∘ z) = (w ∘ u) ∘ v
abbrev Equation4583 (G: Type u) [Magma G] := ∀ x y : G, (x ∘ x) ∘ x = (x ∘ x) ∘ y
abbrev Equation4584 (G: Type u) [Magma G] := ∀ x y : G, (x ∘ x) ∘ x = (x ∘ y) ∘ x
abbrev Equation4585 (G: Type u) [Magma G] := ∀ x y : G, (x ∘ x) ∘ x = (x ∘ y) ∘ y
abbrev Equation4586 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ x = (x ∘ y) ∘ z
abbrev Equation4587 (G: Type u) [Magma G] := ∀ x y : G, (x ∘ x) ∘ x = (y ∘ x) ∘ x
abbrev Equation4588 (G: Type u) [Magma G] := ∀ x y : G, (x ∘ x) ∘ x = (y ∘ x) ∘ y
abbrev Equation4589 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ x = (y ∘ x) ∘ z
abbrev Equation4590 (G: Type u) [Magma G] := ∀ x y : G, (x ∘ x) ∘ x = (y ∘ y) ∘ x
abbrev Equation4591 (G: Type u) [Magma G] := ∀ x y : G, (x ∘ x) ∘ x = (y ∘ y) ∘ y
abbrev Equation4592 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ x = (y ∘ y) ∘ z
abbrev Equation4593 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ x = (y ∘ z) ∘ x
abbrev Equation4594 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ x = (y ∘ z) ∘ y
abbrev Equation4595 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ x = (y ∘ z) ∘ z
abbrev Equation4596 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ x = (y ∘ z) ∘ w
abbrev Equation4597 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (x ∘ x) ∘ z
abbrev Equation4598 (G: Type u) [Magma G] := ∀ x y : G, (x ∘ x) ∘ y = (x ∘ y) ∘ x
abbrev Equation4599 (G: Type u) [Magma G] := ∀ x y : G, (x ∘ x) ∘ y = (x ∘ y) ∘ y
abbrev Equation4600 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (x ∘ y) ∘ z
abbrev Equation4601 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (x ∘ z) ∘ x
abbrev Equation4602 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (x ∘ z) ∘ y
abbrev Equation4603 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (x ∘ z) ∘ z
abbrev Equation4604 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (x ∘ z) ∘ w
abbrev Equation4605 (G: Type u) [Magma G] := ∀ x y : G, (x ∘ x) ∘ y = (y ∘ x) ∘ x
abbrev Equation4606 (G: Type u) [Magma G] := ∀ x y : G, (x ∘ x) ∘ y = (y ∘ x) ∘ y
abbrev Equation4607 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (y ∘ x) ∘ z
abbrev Equation4608 (G: Type u) [Magma G] := ∀ x y : G, (x ∘ x) ∘ y = (y ∘ y) ∘ x
abbrev Equation4609 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (y ∘ y) ∘ z
abbrev Equation4610 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (y ∘ z) ∘ x
abbrev Equation4611 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (y ∘ z) ∘ y
abbrev Equation4612 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (y ∘ z) ∘ z
abbrev Equation4613 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (y ∘ z) ∘ w
abbrev Equation4614 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (z ∘ x) ∘ x
abbrev Equation4615 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (z ∘ x) ∘ y
abbrev Equation4616 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (z ∘ x) ∘ z
abbrev Equation4617 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ x) ∘ w
abbrev Equation4618 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (z ∘ y) ∘ x
abbrev Equation4619 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (z ∘ y) ∘ y
abbrev Equation4620 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (z ∘ y) ∘ z
abbrev Equation4621 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ y) ∘ w
abbrev Equation4622 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ x) ∘ y = (z ∘ z) ∘ y
abbrev Equation4623 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ z) ∘ w
abbrev Equation4624 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ w) ∘ x
abbrev Equation4625 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ w) ∘ y
abbrev Equation4626 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ w) ∘ z
abbrev Equation4627 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ x) ∘ y = (z ∘ w) ∘ w
abbrev Equation4628 (G: Type u) [Magma G] := ∀ x y z w u : G, (x ∘ x) ∘ y = (z ∘ w) ∘ u
abbrev Equation4629 (G: Type u) [Magma G] := ∀ x y : G, (x ∘ y) ∘ x = (x ∘ y) ∘ y
abbrev Equation4630 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (x ∘ y) ∘ z
abbrev Equation4631 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (x ∘ z) ∘ x
abbrev Equation4632 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (x ∘ z) ∘ y
abbrev Equation4633 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (x ∘ z) ∘ z
abbrev Equation4634 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ x = (x ∘ z) ∘ w
abbrev Equation4635 (G: Type u) [Magma G] := ∀ x y : G, (x ∘ y) ∘ x = (y ∘ x) ∘ x
abbrev Equation4636 (G: Type u) [Magma G] := ∀ x y : G, (x ∘ y) ∘ x = (y ∘ x) ∘ y
abbrev Equation4637 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (y ∘ x) ∘ z
abbrev Equation4638 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (y ∘ z) ∘ x
abbrev Equation4639 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (y ∘ z) ∘ y
abbrev Equation4640 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (y ∘ z) ∘ z
abbrev Equation4641 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ x = (y ∘ z) ∘ w
abbrev Equation4642 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (z ∘ x) ∘ x
abbrev Equation4643 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (z ∘ x) ∘ y
abbrev Equation4644 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ x = (z ∘ x) ∘ w
abbrev Equation4645 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (z ∘ y) ∘ x
abbrev Equation4646 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (z ∘ y) ∘ y
abbrev Equation4647 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ x = (z ∘ y) ∘ z
abbrev Equation4648 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ x = (z ∘ y) ∘ w
abbrev Equation4649 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ x = (z ∘ w) ∘ x
abbrev Equation4650 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ x = (z ∘ w) ∘ y
abbrev Equation4651 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ x = (z ∘ w) ∘ z
abbrev Equation4652 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ x = (z ∘ w) ∘ w
abbrev Equation4653 (G: Type u) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ x = (z ∘ w) ∘ u
abbrev Equation4654 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ y = (x ∘ y) ∘ z
abbrev Equation4655 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ y = (x ∘ z) ∘ y
abbrev Equation4656 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ y = (x ∘ z) ∘ z
abbrev Equation4657 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ y = (x ∘ z) ∘ w
abbrev Equation4658 (G: Type u) [Magma G] := ∀ x y : G, (x ∘ y) ∘ y = (y ∘ x) ∘ x
abbrev Equation4659 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ y = (y ∘ x) ∘ z
abbrev Equation4660 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ y = (y ∘ z) ∘ x
abbrev Equation4661 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ y = (y ∘ z) ∘ z
abbrev Equation4662 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ y = (y ∘ z) ∘ w
abbrev Equation4663 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ y = (z ∘ x) ∘ y
abbrev Equation4664 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ y = (z ∘ x) ∘ w
abbrev Equation4665 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ y = (z ∘ y) ∘ x
abbrev Equation4666 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ y = (z ∘ y) ∘ y
abbrev Equation4667 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ y = (z ∘ y) ∘ w
abbrev Equation4668 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ y = (z ∘ w) ∘ x
abbrev Equation4669 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ y = (z ∘ w) ∘ y
abbrev Equation4670 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ y = (z ∘ w) ∘ w
abbrev Equation4671 (G: Type u) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ y = (z ∘ w) ∘ u
abbrev Equation4672 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (x ∘ y) ∘ w
abbrev Equation4673 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ z = (x ∘ z) ∘ y
abbrev Equation4674 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (x ∘ z) ∘ w
abbrev Equation4675 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (x ∘ w) ∘ z
abbrev Equation4676 (G: Type u) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (x ∘ w) ∘ u
abbrev Equation4677 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ z = (y ∘ x) ∘ z
abbrev Equation4678 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (y ∘ x) ∘ w
abbrev Equation4679 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ z = (y ∘ z) ∘ x
abbrev Equation4680 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (y ∘ z) ∘ w
abbrev Equation4681 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (y ∘ w) ∘ x
abbrev Equation4682 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (y ∘ w) ∘ z
abbrev Equation4683 (G: Type u) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (y ∘ w) ∘ u
abbrev Equation4684 (G: Type u) [Magma G] := ∀ x y z : G, (x ∘ y) ∘ z = (z ∘ y) ∘ x
abbrev Equation4685 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (z ∘ y) ∘ w
abbrev Equation4686 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (z ∘ w) ∘ x
abbrev Equation4687 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (z ∘ w) ∘ y
abbrev Equation4688 (G: Type u) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (z ∘ w) ∘ u
abbrev Equation4689 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (w ∘ y) ∘ z
abbrev Equation4690 (G: Type u) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (w ∘ y) ∘ u
abbrev Equation4691 (G: Type u) [Magma G] := ∀ x y z w : G, (x ∘ y) ∘ z = (w ∘ z) ∘ y
abbrev Equation4692 (G: Type u) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (w ∘ z) ∘ u
abbrev Equation4693 (G: Type u) [Magma G] := ∀ x y z w u : G, (x ∘ y) ∘ z = (w ∘ u) ∘ z
abbrev Equation4694 (G: Type u) [Magma G] := ∀ x y z w u v : G, (x ∘ y) ∘ z = (w ∘ u) ∘ v
