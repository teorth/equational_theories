import equational_theories.Equations
import equational_theories.EquationalResult
import Egg
import Calcify

set_option egg.explosion true
set_option egg.timeLimit 1

set_option trace.egg true in
@[equational_result]
theorem Equation14_implies_Equation23 (G: Type _) [Magma G] (h: Equation14 G) : Equation23 G := by
 intro x
 calc
     x
     _ = (x ∘ x) ∘ (x ∘ (x ∘ x)) := (h x (x ∘ x))
     _ = (x ∘ x) ∘ x := by rw [← h x x] -- note: this rw was not easy to get from calcify

@[equational_result]
theorem Equation2_implies_Equation1689 (G: Type _) [Magma G] (h: Equation2 G) : Equation1689 G := by
intro x y z
calc
    x
    _ = (y ∘ x) ∘ ((x ∘ z) ∘ z) := Eq.symm (h ((y ∘ x) ∘ ((x ∘ z) ∘ z)) x)
    -- note: calcify worked great here!

@[equational_result]
theorem Equation14_implies_Equation8 (G: Type _) [Magma G] (h: Equation14 G) : Equation8 G := by
intro x
calc
    x
    _ = x ∘ (x ∘ x) := h x x
    -- note: calcify was great here!

@[equational_result]
theorem Equation2_implies_Equation14 (G: Type _) [Magma G] (h: Equation2 G) : Equation14 G := by
intro x y
calc
    x
    _ = y ∘ (x ∘ y) := Eq.symm (h (y ∘ (x ∘ y)) x)
    -- note: calcify was great here!

-- redundant: come through transitivity
@[equational_result]
theorem Equation29_implies_Equation23 (G: Type _) [Magma G] (h: Equation29 G) : Equation23 G := by egg [*]

@[equational_result]
theorem Equation29_implies_Equation8 (G: Type _) [Magma G] (h: Equation29 G) : Equation8 G := by egg [*]

-- Redundant: Equation 1 is tautology
@[equational_result]
theorem Equation2_implies_Equation1 (G: Type _) [Magma G] (_ : Equation2 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation1689_implies_Equation1 (G: Type _) [Magma G] (_ : Equation1689 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation168_implies_Equation1 (G: Type _) [Magma G] (_ : Equation168 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation23_implies_Equation1 (G: Type _) [Magma G] (_ : Equation23 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation28393_implies_Equation1 (G: Type _) [Magma G] (_ : Equation28393 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation29_implies_Equation1 (G: Type _) [Magma G] (_ : Equation29 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation14_implies_Equation1 (G: Type _) [Magma G] (_ : Equation14 G) : Equation1 G := by egg [*]

/-
TODO: sort through:

18,19d28
< Equation2 → Equation28393
< Equation2 → Equation29
21,23d29
< Equation2 → Equation3722
< Equation2 → Equation3744
< Equation2 → Equation374794
25d30
< Equation2 → Equation381
42d46
< Equation2 → Equation5105
46,47d49
< Equation3722 → Equation1
< Equation3744 → Equation1
50,53d51
< Equation3744 → Equation4512
< Equation374794 → Equation1
< Equation381 → Equation1
< Equation387 → Equation1
55d52
< Equation38 → Equation1
57,58d53
< Equation39 → Equation1
< Equation39 → Equation381
60d54
< Equation3 → Equation1
62d55
< Equation3 → Equation3722
64,67d56
< Equation40 → Equation1
< Equation41 → Equation1
< Equation41 → Equation3722
< Equation41 → Equation3744
69d57
< Equation41 → Equation381
83d70
< Equation42 → Equation1
85,87d71
< Equation43 → Equation1
< Equation4512 → Equation1
< Equation4513 → Equation1
89d72
< Equation4522 → Equation1
92,97d74
< Equation4564 → Equation1
< Equation4564 → Equation4512
< Equation4579 → Equation1
< Equation4579 → Equation4512
< Equation4579 → Equation4564
< Equation4582 → Equation1
103,104d79
< Equation45 → Equation1
< Equation45 → Equation381
106,108d80
< Equation46 → Equation1
< Equation46 → Equation3722
< Equation46 → Equation3744
110d81
< Equation46 → Equation381
124d94
< Equation4 → Equation1
126d95
< Equation4 → Equation28393
128,129d96
< Equation4 → Equation3722
< Equation4 → Equation3744
131d97
< Equation4 → Equation381
137,138d102
< Equation5105 → Equation1
< Equation5 → Equation1
141,143d104
< Equation5 → Equation3722
< Equation5 → Equation3744
< Equation5 → Equation381
147,148d107
< Equation5 → Equation4564
< Equation5 → Equation4579
150,151d108
< Equation6 → Equation1
< Equation6 → Equation14
153d109
< Equation6 → Equation1689
156,157d111
< Equation6 → Equation28393
< Equation6 → Equation29
159,161d112
< Equation6 → Equation3722
< Equation6 → Equation3744
< Equation6 → Equation374794
163d113
< Equation6 → Equation381
180d129
< Equation6 → Equation5105
183,184d131
< Equation7 → Equation1
< Equation7 → Equation14
186d132
< Equation7 → Equation1689
189,190d134
< Equation7 → Equation28393
< Equation7 → Equation29
192,194d135
< Equation7 → Equation3722
< Equation7 → Equation3744
< Equation7 → Equation374794
196d136
< Equation7 → Equation381
213d152
< Equation7 → Equation5105
216d154
-/

@[equational_result]
theorem Equation1_implies_Equation1 (G: Type _) [Magma G] (_ : Equation1 G) : Equation1 G := by egg [*]


@[equational_result]
theorem Equation2_implies_Equation2 (G: Type _) [Magma G] (h: Equation2 G) : Equation2 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation3 (G: Type _) [Magma G] (h: Equation2 G) : Equation3 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation4 (G: Type _) [Magma G] (h: Equation2 G) : Equation4 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation5 (G: Type _) [Magma G] (h: Equation2 G) : Equation5 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation6 (G: Type _) [Magma G] (h: Equation2 G) : Equation6 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation7 (G: Type _) [Magma G] (h: Equation2 G) : Equation7 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation8 (G: Type _) [Magma G] (h: Equation2 G) : Equation8 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation23 (G: Type _) [Magma G] (h: Equation2 G) : Equation23 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation29 (G: Type _) [Magma G] (h: Equation2 G) : Equation29 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation38 (G: Type _) [Magma G] (h: Equation2 G) : Equation38 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation39 (G: Type _) [Magma G] (h: Equation2 G) : Equation39 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation40 (G: Type _) [Magma G] (h: Equation2 G) : Equation40 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation41 (G: Type _) [Magma G] (h: Equation2 G) : Equation41 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation42 (G: Type _) [Magma G] (h: Equation2 G) : Equation42 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation43 (G: Type _) [Magma G] (h: Equation2 G) : Equation43 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation45 (G: Type _) [Magma G] (h: Equation2 G) : Equation45 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation46 (G: Type _) [Magma G] (h: Equation2 G) : Equation46 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation168 (G: Type _) [Magma G] (h: Equation2 G) : Equation168 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation381 (G: Type _) [Magma G] (h: Equation2 G) : Equation381 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation387 (G: Type _) [Magma G] (h: Equation2 G) : Equation387 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation3722 (G: Type _) [Magma G] (h: Equation2 G) : Equation3722 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation3744 (G: Type _) [Magma G] (h: Equation2 G) : Equation3744 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation4512 (G: Type _) [Magma G] (h: Equation2 G) : Equation4512 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation4513 (G: Type _) [Magma G] (h: Equation2 G) : Equation4513 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation4522 (G: Type _) [Magma G] (h: Equation2 G) : Equation4522 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation4564 (G: Type _) [Magma G] (h: Equation2 G) : Equation4564 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation4579 (G: Type _) [Magma G] (h: Equation2 G) : Equation4579 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation4582 (G: Type _) [Magma G] (h: Equation2 G) : Equation4582 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation5105 (G: Type _) [Magma G] (h: Equation2 G) : Equation5105 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation28393 (G: Type _) [Magma G] (h: Equation2 G) : Equation28393 G := by egg [*]

@[equational_result]
theorem Equation2_implies_Equation374794 (G: Type _) [Magma G] (h: Equation2 G) : Equation374794 G := by egg [*]

@[equational_result]
theorem Equation3_implies_Equation1 (G: Type _) [Magma G] (_ : Equation3 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation3_implies_Equation3 (G: Type _) [Magma G] (h: Equation3 G) : Equation3 G := by egg [*]

@[equational_result]
theorem Equation3_implies_Equation8 (G: Type _) [Magma G] (h: Equation3 G) : Equation8 G := by egg [*]

@[equational_result]
theorem Equation3_implies_Equation23 (G: Type _) [Magma G] (h: Equation3 G) : Equation23 G := by egg [*]

@[equational_result]
theorem Equation3_implies_Equation3722 (G: Type _) [Magma G] (h: Equation3 G) : Equation3722 G := by egg [*]

@[equational_result]
theorem Equation4_implies_Equation1 (G: Type _) [Magma G] (_ : Equation4 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation4_implies_Equation3 (G: Type _) [Magma G] (h: Equation4 G) : Equation3 G := by egg [*]

@[equational_result]
theorem Equation4_implies_Equation4 (G: Type _) [Magma G] (h: Equation4 G) : Equation4 G := by egg [*]

@[equational_result]
theorem Equation4_implies_Equation8 (G: Type _) [Magma G] (h: Equation4 G) : Equation8 G := by egg [*]

@[equational_result]
theorem Equation4_implies_Equation23 (G: Type _) [Magma G] (h: Equation4 G) : Equation23 G := by egg [*]

@[equational_result]
theorem Equation4_implies_Equation38 (G: Type _) [Magma G] (h: Equation4 G) : Equation38 G := by egg [*]

@[equational_result]
theorem Equation4_implies_Equation42 (G: Type _) [Magma G] (h: Equation4 G) : Equation42 G := by egg [*]

@[equational_result]
theorem Equation4_implies_Equation381 (G: Type _) [Magma G] (h: Equation4 G) : Equation381 G := by egg [*]

@[equational_result]
theorem Equation4_implies_Equation3722 (G: Type _) [Magma G] (h: Equation4 G) : Equation3722 G := by egg [*]

@[equational_result]
theorem Equation4_implies_Equation3744 (G: Type _) [Magma G] (h: Equation4 G) : Equation3744 G := by egg [*]

@[equational_result]
theorem Equation4_implies_Equation4512 (G: Type _) [Magma G] (h: Equation4 G) : Equation4512 G := by egg [*]

@[equational_result]
theorem Equation4_implies_Equation4513 (G: Type _) [Magma G] (h: Equation4 G) : Equation4513 G := by egg [*]

@[equational_result]
theorem Equation4_implies_Equation4522 (G: Type _) [Magma G] (h: Equation4 G) : Equation4522 G := by egg [*]

@[equational_result]
theorem Equation4_implies_Equation28393 (G: Type _) [Magma G] (h: Equation4 G) : Equation28393 G := by egg [*]

@[equational_result]
theorem Equation5_implies_Equation1 (G: Type _) [Magma G] (_ : Equation5 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation5_implies_Equation3 (G: Type _) [Magma G] (h: Equation5 G) : Equation3 G := by egg [*]

@[equational_result]
theorem Equation5_implies_Equation5 (G: Type _) [Magma G] (h: Equation5 G) : Equation5 G := by egg [*]

@[equational_result]
theorem Equation5_implies_Equation8 (G: Type _) [Magma G] (h: Equation5 G) : Equation8 G := by egg [*]

@[equational_result]
theorem Equation5_implies_Equation23 (G: Type _) [Magma G] (h: Equation5 G) : Equation23 G := by egg [*]

@[equational_result]
theorem Equation5_implies_Equation39 (G: Type _) [Magma G] (h: Equation5 G) : Equation39 G := by egg [*]

@[equational_result]
theorem Equation5_implies_Equation45 (G: Type _) [Magma G] (h: Equation5 G) : Equation45 G := by egg [*]

@[equational_result]
theorem Equation5_implies_Equation381 (G: Type _) [Magma G] (h: Equation5 G) : Equation381 G := by egg [*]

@[equational_result]
theorem Equation5_implies_Equation3722 (G: Type _) [Magma G] (h: Equation5 G) : Equation3722 G := by egg [*]

@[equational_result]
theorem Equation5_implies_Equation3744 (G: Type _) [Magma G] (h: Equation5 G) : Equation3744 G := by egg [*]

@[equational_result]
theorem Equation5_implies_Equation4512 (G: Type _) [Magma G] (h: Equation5 G) : Equation4512 G := by egg [*]

@[equational_result]
theorem Equation5_implies_Equation4564 (G: Type _) [Magma G] (h: Equation5 G) : Equation4564 G := by egg [*]

@[equational_result]
theorem Equation5_implies_Equation4579 (G: Type _) [Magma G] (h: Equation5 G) : Equation4579 G := by egg [*]

@[equational_result]
theorem Equation6_implies_Equation1 (G: Type _) [Magma G] (_ : Equation6 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation6_implies_Equation2 (G: Type _) [Magma G] (h: Equation6 G) : Equation2 G := by egg [*]

@[equational_result]
theorem Equation6_implies_Equation3 (G: Type _) [Magma G] (h: Equation6 G) : Equation3 G := by egg [*]

@[equational_result]
theorem Equation6_implies_Equation5 (G: Type _) [Magma G] (h: Equation6 G) : Equation5 G := by egg [*]

@[equational_result]
theorem Equation6_implies_Equation6 (G: Type _) [Magma G] (h: Equation6 G) : Equation6 G := by egg [*]

@[equational_result]
theorem Equation6_implies_Equation8 (G: Type _) [Magma G] (h: Equation6 G) : Equation8 G := by egg [*]

@[equational_result]
theorem Equation6_implies_Equation38 (G: Type _) [Magma G] (h: Equation6 G) : Equation38 G := by egg [*]

@[equational_result]
theorem Equation6_implies_Equation39 (G: Type _) [Magma G] (h: Equation6 G) : Equation39 G := by egg [*]

@[equational_result]
theorem Equation6_implies_Equation40 (G: Type _) [Magma G] (h: Equation6 G) : Equation40 G := by egg [*]

@[equational_result]
theorem Equation6_implies_Equation41 (G: Type _) [Magma G] (h: Equation6 G) : Equation41 G := by egg [*]

@[equational_result]
theorem Equation6_implies_Equation42 (G: Type _) [Magma G] (h: Equation6 G) : Equation42 G := by egg [*]

@[equational_result]
theorem Equation6_implies_Equation387 (G: Type _) [Magma G] (h: Equation6 G) : Equation387 G := by egg [*]

@[equational_result]
theorem Equation7_implies_Equation1 (G: Type _) [Magma G] (_ : Equation7 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation7_implies_Equation2 (G: Type _) [Magma G] (h: Equation7 G) : Equation2 G := by egg [*]

@[equational_result]
theorem Equation7_implies_Equation3 (G: Type _) [Magma G] (h: Equation7 G) : Equation3 G := by egg [*]

@[equational_result]
theorem Equation7_implies_Equation5 (G: Type _) [Magma G] (h: Equation7 G) : Equation5 G := by egg [*]

@[equational_result]
theorem Equation7_implies_Equation6 (G: Type _) [Magma G] (h: Equation7 G) : Equation6 G := by egg [*]

@[equational_result]
theorem Equation7_implies_Equation8 (G: Type _) [Magma G] (h: Equation7 G) : Equation8 G := by egg [*]

@[equational_result]
theorem Equation7_implies_Equation38 (G: Type _) [Magma G] (h: Equation7 G) : Equation38 G := by egg [*]

@[equational_result]
theorem Equation7_implies_Equation39 (G: Type _) [Magma G] (h: Equation7 G) : Equation39 G := by egg [*]

@[equational_result]
theorem Equation7_implies_Equation40 (G: Type _) [Magma G] (h: Equation7 G) : Equation40 G := by egg [*]

@[equational_result]
theorem Equation7_implies_Equation41 (G: Type _) [Magma G] (h: Equation7 G) : Equation41 G := by egg [*]

@[equational_result]
theorem Equation7_implies_Equation42 (G: Type _) [Magma G] (h: Equation7 G) : Equation42 G := by egg [*]

@[equational_result]
theorem Equation7_implies_Equation43 (G: Type _) [Magma G] (h: Equation7 G) : Equation43 G := by egg [*]

@[equational_result]
theorem Equation7_implies_Equation45 (G: Type _) [Magma G] (h: Equation7 G) : Equation45 G := by egg [*]

@[equational_result]
theorem Equation7_implies_Equation46 (G: Type _) [Magma G] (h: Equation7 G) : Equation46 G := by egg [*]

@[equational_result]
theorem Equation8_implies_Equation1 (G: Type _) [Magma G] (_ : Equation8 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation8_implies_Equation8 (G: Type _) [Magma G] (h: Equation8 G) : Equation8 G := by egg [*]


@[equational_result]
theorem Equation14_implies_Equation14 (G: Type _) [Magma G] (h: Equation14 G) : Equation14 G := by egg [*]


@[equational_result]
theorem Equation14_implies_Equation29 (G: Type _) [Magma G] (h: Equation14 G) : Equation29 G := by egg [*]

@[equational_result]
theorem Equation23_implies_Equation23 (G: Type _) [Magma G] (h: Equation23 G) : Equation23 G := by egg [*]

@[equational_result]
theorem Equation29_implies_Equation14 (G: Type _) [Magma G] (h: Equation29 G) : Equation14 G := by egg [*]

@[equational_result]
theorem Equation29_implies_Equation29 (G: Type _) [Magma G] (h: Equation29 G) : Equation29 G := by egg [*]

@[equational_result]
theorem Equation38_implies_Equation1 (G: Type _) [Magma G] (_ : Equation38 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation38_implies_Equation38 (G: Type _) [Magma G] (h: Equation38 G) : Equation38 G := by egg [*]

@[equational_result]
theorem Equation38_implies_Equation42 (G: Type _) [Magma G] (h: Equation38 G) : Equation42 G := by egg [*]

@[equational_result]
theorem Equation39_implies_Equation1 (G: Type _) [Magma G] (_ : Equation39 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation39_implies_Equation39 (G: Type _) [Magma G] (h: Equation39 G) : Equation39 G := by egg [*]

@[equational_result]
theorem Equation39_implies_Equation45 (G: Type _) [Magma G] (h: Equation39 G) : Equation45 G := by egg [*]

@[equational_result]
theorem Equation39_implies_Equation381 (G: Type _) [Magma G] (h: Equation39 G) : Equation381 G := by egg [*]

@[equational_result]
theorem Equation40_implies_Equation1 (G: Type _) [Magma G] (_ : Equation40 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation40_implies_Equation40 (G: Type _) [Magma G] (h: Equation40 G) : Equation40 G := by egg [*]

@[equational_result]
theorem Equation41_implies_Equation1 (G: Type _) [Magma G] (_ : Equation41 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation41_implies_Equation38 (G: Type _) [Magma G] (h: Equation41 G) : Equation38 G := by egg [*]

@[equational_result]
theorem Equation41_implies_Equation39 (G: Type _) [Magma G] (h: Equation41 G) : Equation39 G := by egg [*]

@[equational_result]
theorem Equation41_implies_Equation40 (G: Type _) [Magma G] (h: Equation41 G) : Equation40 G := by egg [*]

@[equational_result]
theorem Equation41_implies_Equation41 (G: Type _) [Magma G] (h: Equation41 G) : Equation41 G := by egg [*]

@[equational_result]
theorem Equation41_implies_Equation42 (G: Type _) [Magma G] (h: Equation41 G) : Equation42 G := by egg [*]

@[equational_result]
theorem Equation41_implies_Equation43 (G: Type _) [Magma G] (h: Equation41 G) : Equation43 G := by egg [*]

@[equational_result]
theorem Equation41_implies_Equation45 (G: Type _) [Magma G] (h: Equation41 G) : Equation45 G := by egg [*]

@[equational_result]
theorem Equation41_implies_Equation46 (G: Type _) [Magma G] (h: Equation41 G) : Equation46 G := by egg [*]

@[equational_result]
theorem Equation41_implies_Equation381 (G: Type _) [Magma G] (h: Equation41 G) : Equation381 G := by egg [*]

@[equational_result]
theorem Equation41_implies_Equation387 (G: Type _) [Magma G] (h: Equation41 G) : Equation387 G := by egg [*]

@[equational_result]
theorem Equation41_implies_Equation3722 (G: Type _) [Magma G] (h: Equation41 G) : Equation3722 G := by egg [*]

@[equational_result]
theorem Equation41_implies_Equation3744 (G: Type _) [Magma G] (h: Equation41 G) : Equation3744 G := by egg [*]

@[equational_result]
theorem Equation41_implies_Equation4512 (G: Type _) [Magma G] (h: Equation41 G) : Equation4512 G := by egg [*]

@[equational_result]
theorem Equation41_implies_Equation4513 (G: Type _) [Magma G] (h: Equation41 G) : Equation4513 G := by egg [*]

@[equational_result]
theorem Equation41_implies_Equation4522 (G: Type _) [Magma G] (h: Equation41 G) : Equation4522 G := by egg [*]

@[equational_result]
theorem Equation41_implies_Equation4564 (G: Type _) [Magma G] (h: Equation41 G) : Equation4564 G := by egg [*]

@[equational_result]
theorem Equation41_implies_Equation4579 (G: Type _) [Magma G] (h: Equation41 G) : Equation4579 G := by egg [*]

@[equational_result]
theorem Equation41_implies_Equation4582 (G: Type _) [Magma G] (h: Equation41 G) : Equation4582 G := by egg [*]

@[equational_result]
theorem Equation42_implies_Equation1 (G: Type _) [Magma G] (_ : Equation42 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation42_implies_Equation38 (G: Type _) [Magma G] (h: Equation42 G) : Equation38 G := by egg [*]

@[equational_result]
theorem Equation42_implies_Equation42 (G: Type _) [Magma G] (h: Equation42 G) : Equation42 G := by egg [*]

@[equational_result]
theorem Equation43_implies_Equation1 (G: Type _) [Magma G] (_ : Equation43 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation43_implies_Equation43 (G: Type _) [Magma G] (h: Equation43 G) : Equation43 G := by egg [*]

@[equational_result]
theorem Equation45_implies_Equation1 (G: Type _) [Magma G] (_ : Equation45 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation45_implies_Equation39 (G: Type _) [Magma G] (h: Equation45 G) : Equation39 G := by egg [*]

@[equational_result]
theorem Equation45_implies_Equation45 (G: Type _) [Magma G] (h: Equation45 G) : Equation45 G := by egg [*]

@[equational_result]
theorem Equation45_implies_Equation381 (G: Type _) [Magma G] (h: Equation45 G) : Equation381 G := by egg [*]

@[equational_result]
theorem Equation46_implies_Equation1 (G: Type _) [Magma G] (_ : Equation46 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation46_implies_Equation38 (G: Type _) [Magma G] (h: Equation46 G) : Equation38 G := by egg [*]

@[equational_result]
theorem Equation46_implies_Equation39 (G: Type _) [Magma G] (h: Equation46 G) : Equation39 G := by egg [*]

@[equational_result]
theorem Equation46_implies_Equation40 (G: Type _) [Magma G] (h: Equation46 G) : Equation40 G := by egg [*]

@[equational_result]
theorem Equation46_implies_Equation41 (G: Type _) [Magma G] (h: Equation46 G) : Equation41 G := by egg [*]

@[equational_result]
theorem Equation46_implies_Equation42 (G: Type _) [Magma G] (h: Equation46 G) : Equation42 G := by egg [*]

@[equational_result]
theorem Equation46_implies_Equation43 (G: Type _) [Magma G] (h: Equation46 G) : Equation43 G := by egg [*]

@[equational_result]
theorem Equation46_implies_Equation45 (G: Type _) [Magma G] (h: Equation46 G) : Equation45 G := by egg [*]

@[equational_result]
theorem Equation46_implies_Equation46 (G: Type _) [Magma G] (h: Equation46 G) : Equation46 G := by egg [*]

@[equational_result]
theorem Equation46_implies_Equation381 (G: Type _) [Magma G] (h: Equation46 G) : Equation381 G := by egg [*]

@[equational_result]
theorem Equation46_implies_Equation387 (G: Type _) [Magma G] (h: Equation46 G) : Equation387 G := by egg [*]

@[equational_result]
theorem Equation46_implies_Equation3722 (G: Type _) [Magma G] (h: Equation46 G) : Equation3722 G := by egg [*]

@[equational_result]
theorem Equation46_implies_Equation3744 (G: Type _) [Magma G] (h: Equation46 G) : Equation3744 G := by egg [*]

@[equational_result]
theorem Equation46_implies_Equation4512 (G: Type _) [Magma G] (h: Equation46 G) : Equation4512 G := by egg [*]

@[equational_result]
theorem Equation46_implies_Equation4513 (G: Type _) [Magma G] (h: Equation46 G) : Equation4513 G := by egg [*]

@[equational_result]
theorem Equation46_implies_Equation4522 (G: Type _) [Magma G] (h: Equation46 G) : Equation4522 G := by egg [*]

@[equational_result]
theorem Equation46_implies_Equation4564 (G: Type _) [Magma G] (h: Equation46 G) : Equation4564 G := by egg [*]

@[equational_result]
theorem Equation46_implies_Equation4579 (G: Type _) [Magma G] (h: Equation46 G) : Equation4579 G := by egg [*]

@[equational_result]
theorem Equation46_implies_Equation4582 (G: Type _) [Magma G] (h: Equation46 G) : Equation4582 G := by egg [*]

@[equational_result]
theorem Equation168_implies_Equation168 (G: Type _) [Magma G] (h: Equation168 G) : Equation168 G := by egg [*]

@[equational_result]
theorem Equation381_implies_Equation1 (G: Type _) [Magma G] (_ : Equation381 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation381_implies_Equation381 (G: Type _) [Magma G] (h: Equation381 G) : Equation381 G := by egg [*]

@[equational_result]
theorem Equation387_implies_Equation1 (G: Type _) [Magma G] (_ : Equation387 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation387_implies_Equation43 (G: Type _) [Magma G] (h: Equation387 G) : Equation43 G := by egg [*]

@[equational_result]
theorem Equation387_implies_Equation387 (G: Type _) [Magma G] (h: Equation387 G) : Equation387 G := by egg [*]


-- @[equational_result]
-- theorem Equation1689_implies_Equation2 (G: Type _) [Magma G] (h: Equation1689 G) : Equation2 G:= by
--   have : ∀ a b c : G, a ∘ (b ∘ ((b ∘ c) ∘ c)) = (a ∘ b) ∘ b := by egg [*, h _ (_ ∘ _) _; h]
--   egg [*]

@[equational_result]
theorem Equation1689_implies_Equation1689 (G: Type _) [Magma G] (h: Equation1689 G) : Equation1689 G := by egg [*]

@[equational_result]
theorem Equation3722_implies_Equation1 (G: Type _) [Magma G] (_ : Equation3722 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation3722_implies_Equation3722 (G: Type _) [Magma G] (h: Equation3722 G) : Equation3722 G := by egg [*]

@[equational_result]
theorem Equation3744_implies_Equation1 (G: Type _) [Magma G] (_ : Equation3744 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation3744_implies_Equation381 (G: Type _) [Magma G] (h: Equation3744 G) : Equation381 G := by egg [*]

@[equational_result]
theorem Equation3744_implies_Equation3722 (G: Type _) [Magma G] (h: Equation3744 G) : Equation3722 G := by egg [*]

@[equational_result]
theorem Equation3744_implies_Equation3744 (G: Type _) [Magma G] (h: Equation3744 G) : Equation3744 G := by egg [*]

@[equational_result]
theorem Equation3744_implies_Equation4512 (G: Type _) [Magma G] (h: Equation3744 G) : Equation4512 G := by egg [*]

@[equational_result]
theorem Equation4512_implies_Equation1 (G: Type _) [Magma G] (_ : Equation4512 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation4512_implies_Equation4512 (G: Type _) [Magma G] (h: Equation4512 G) : Equation4512 G := by egg [*]

@[equational_result]
theorem Equation4513_implies_Equation1 (G: Type _) [Magma G] (_ : Equation4513 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation4513_implies_Equation4512 (G: Type _) [Magma G] (h: Equation4513 G) : Equation4512 G := by egg [*]

@[equational_result]
theorem Equation4513_implies_Equation4513 (G: Type _) [Magma G] (h: Equation4513 G) : Equation4513 G := by egg [*]

@[equational_result]
theorem Equation4522_implies_Equation1 (G: Type _) [Magma G] (_ : Equation4522 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation4522_implies_Equation4512 (G: Type _) [Magma G] (h: Equation4522 G) : Equation4512 G := by egg [*]

@[equational_result]
theorem Equation4522_implies_Equation4513 (G: Type _) [Magma G] (h: Equation4522 G) : Equation4513 G := by egg [*]

@[equational_result]
theorem Equation4522_implies_Equation4522 (G: Type _) [Magma G] (h: Equation4522 G) : Equation4522 G := by egg [*]

@[equational_result]
theorem Equation4564_implies_Equation1 (G: Type _) [Magma G] (_ : Equation4564 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation4564_implies_Equation4512 (G: Type _) [Magma G] (h: Equation4564 G) : Equation4512 G := by egg [*]

@[equational_result]
theorem Equation4564_implies_Equation4564 (G: Type _) [Magma G] (h: Equation4564 G) : Equation4564 G := by egg [*]

@[equational_result]
theorem Equation4579_implies_Equation1 (G: Type _) [Magma G] (_ : Equation4579 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation4579_implies_Equation4512 (G: Type _) [Magma G] (h: Equation4579 G) : Equation4512 G := by egg [*]

@[equational_result]
theorem Equation4579_implies_Equation4564 (G: Type _) [Magma G] (h: Equation4579 G) : Equation4564 G := by egg [*]

@[equational_result]
theorem Equation4579_implies_Equation4579 (G: Type _) [Magma G] (h: Equation4579 G) : Equation4579 G := by egg [*]

@[equational_result]
theorem Equation4582_implies_Equation1 (G: Type _) [Magma G] (_ : Equation4582 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation4582_implies_Equation4512 (G: Type _) [Magma G] (h: Equation4582 G) : Equation4512 G := by egg [*]

@[equational_result]
theorem Equation4582_implies_Equation4513 (G: Type _) [Magma G] (h: Equation4582 G) : Equation4513 G := by egg [*]

@[equational_result]
theorem Equation4582_implies_Equation4522 (G: Type _) [Magma G] (h: Equation4582 G) : Equation4522 G := by egg [*]

@[equational_result]
theorem Equation4582_implies_Equation4564 (G: Type _) [Magma G] (h: Equation4582 G) : Equation4564 G := by egg [*]

@[equational_result]
theorem Equation4582_implies_Equation4579 (G: Type _) [Magma G] (h: Equation4582 G) : Equation4579 G := by egg [*]

@[equational_result]
theorem Equation4582_implies_Equation4582 (G: Type _) [Magma G] (h: Equation4582 G) : Equation4582 G := by egg [*]

@[equational_result]
theorem Equation5105_implies_Equation1 (G: Type _) [Magma G] (_ : Equation5105 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation5105_implies_Equation5105 (G: Type _) [Magma G] (h: Equation5105 G) : Equation5105 G := by egg [*]

@[equational_result]
theorem Equation28393_implies_Equation28393 (G: Type _) [Magma G] (h: Equation28393 G) : Equation28393 G := by egg [*]

@[equational_result]
theorem Equation374794_implies_Equation1 (G: Type _) [Magma G] (_ : Equation374794 G) : Equation1 G := by egg [*]

@[equational_result]
theorem Equation374794_implies_Equation374794 (G: Type _) [Magma G] (h: Equation374794 G) : Equation374794 G := by egg [*]
