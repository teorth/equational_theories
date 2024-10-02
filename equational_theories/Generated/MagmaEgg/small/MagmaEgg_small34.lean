import equational_theories.AllEquations
import equational_theories.Magma

private def congr_op {G: Type _} [Magma G] {a b c d: G} (h1: a = b) (h2: c = d): a ∘ c = b ∘ d := by
  rw [h1, h2]
private abbrev T := @Eq.trans
private abbrev S := @Eq.symm
private abbrev R := @Eq.refl
private abbrev M := @Magma.op
private abbrev C := @congr_op

@[equational_result]
theorem Equation1571_implies_Equation3740 (G: Type _) [Magma G] (h: Equation1571 G) : Equation3740 G := fun x y z =>
  let v0 := M z y
  let v1 := M x z
  let v2 := M v1 v0
  let v3 := M v2 v0
  have h4 := h v2 v1 v0
  have h5 := R v2
  let v6 := M v2 v2
  have h7 := S (h v1 v1 v0)
  have h8 := R v6
  have h9 := C h8 h7
  have h10 := h v1 v2 v2
  let v11 := M v1 v1
  let v12 := M x y
  have h13 := h v0 v0 (M z v12)
  have h14 := S h13
  have h15 := h x z y
  have h16 := R v0
  have h17 := C h15 (C h16 h15)
  have h18 := S (h x x z)
  have h19 := R v11
  have h20 := C h19 h18
  have h21 := h x v1 v1
  have h22 := S h15
  have h23 := S (h v0 x z)
  have h24 := R v12
  have h25 := S (h x v0 v12)
  let v26 := M v0 v12
  have h27 := S (h v12 z y)
  let v28 := M v12 v2
  have h29 := S (h v2 x y)
  T (T (T (T (h v12 v12 (M x (M v2 y))) (C h29 (C h24 h29))) (C h5 (T (T (h v28 v2 v0) (C (R v3) (C h5 (T (T (T (T (T (C (R v28) (T (T (h v0 v0 (M z (M v12 y))) (C h27 (T (T (C h16 h27) (h v26 v26 (M v0 (M x v12)))) (C h25 (T (C (R v26) (T h25 h15)) (S (h z v0 v12))))))) (C h24 (T (T (h v1 v1 (M x (M v0 z))) (C h23 (C (R v1) h23))) (C (T h13 (C h22 (C h16 h22))) h5))))) (S (h (M x (M v0 x)) v12 v2))) h17) h14) (h v0 x x)) (C (T (C (T h21 h20) (T h21 (C h19 (T (T h18 h21) h20)))) (S (h v11 v11 x))) (T h17 h14)))))) (S (h v11 v2 v0))))) (C h4 (T (T (C (T h10 h9) (T h10 (C h8 (T (T h7 h10) h9)))) (S (h v6 v6 v1))) (C h5 h4)))) (S (h v2 v2 (M v1 v3)))

@[equational_result]
theorem Equation492_implies_Equation1876 (G: Type _) [Magma G] (h: Equation492 G) : Equation1876 G := fun x y z =>
  let v0 := M z y
  let v1 := M y z
  have h2 := h y v1 v0
  have h3 := S h2
  have h4 := h v1 v1 x
  let v5 := M x v1
  have h6 := h v5 v0 y
  have h7 := h v0 z v0
  have h8 := h z y z
  have h9 := R v0
  have h10 := h y v0 z
  have h11 := R z
  have h12 := R y
  have h13 := C h12 (T (C h11 (C h9 (C h9 (T h10 (C h9 (S h8)))))) (S h7))
  have h14 := h z y v0
  have h15 := h v1 v5 x
  have h16 := h x v1 x
  have h17 := R v5
  have h18 := R x
  have h19 := C h18 (T (C h9 (C h17 (T (T (C h17 h16) (S h15)) (C h12 (T h14 h13))))) (S h6))
  have h20 := h v0 x v5
  have h21 := R v1
  have h22 := h v0 v0 v1
  have h23 := C h12 (T h22 (C h9 (C h9 (T (C h21 (C h21 (T h20 h19))) (S h4)))))
  have h24 := h z y v1
  have h25 := h v1 z v1
  have h26 := C h11 (T (C h21 (T (T (T (T (C h12 (T h25 (C h11 (C h21 (C h21 (T (C h21 (T (T h14 h13) h23)) h3)))))) (S h24)) h14) h13) h23)) h3)
  have h27 := h v1 z y
  have h28 := S h14
  have h29 := C h11 (C h9 (C h9 (T (C h9 h8) (S h10))))
  have h30 := S h20
  have h31 := C h9 (C h17 (T (T (C h12 (T (C h12 (T h7 h29)) h28)) h15) (C h17 (S h16))))
  have h32 := C h12 (T (T (T (C h9 (C h9 (T h4 (C h21 (C h21 (T (C h18 (T h6 h31)) h30)))))) (S h22)) h7) h29)
  T (T (h x v5 v5) (C h17 (T (T (T (C h18 (T (T (T (C h17 (C h17 (C h18 (T (T (T h27 h26) h20) h19)))) (S (h v5 v5 x))) h6) h31)) h30) (C h11 (T h2 (C h21 (T (T (T h32 h28) h24) (C h12 (T (C h11 (C h21 (C h21 (T h2 (C h21 (T h32 h28)))))) (S h25)))))))) (S h27)))) (C h17 (T h27 h26))

@[equational_result]
theorem Equation1301_implies_Equation1117 (G: Type _) [Magma G] (h: Equation1301 G) : Equation1117 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M v1 z
  have h3 := R v2
  let v4 := M (M v1 y) v0
  let v5 := M y v2
  let v6 := M v5 y
  let v7 := M v6 v2
  have h8 := h y v7 v4
  have h9 := S h8
  have h10 := R v4
  have h11 := R v7
  have h12 := h y y v0
  have h13 := h y y v2
  have h14 := C h11 (T h12 (C (T h13 (C h12 h11)) h10))
  have h15 := T h14 h9
  have h16 := C h15 h3
  have h17 := R y
  have h18 := h v6 y v2
  have h19 := S h12
  have h20 := C h11 (T (C (T (C h19 h11) (S h13)) h10) h19)
  have h21 := T h8 h20
  have h22 := R v5
  have h23 := C (T (C (C h21 h22) h3) (C (T (C h15 (C h21 h3)) (S h18)) h3)) h17
  have h24 := R z
  have h25 := R v0
  have h26 := C (T (C (T h18 (C h21 h16)) h3) (C (C h15 h22) h3)) h17
  have h27 := T (T h8 h20) h26
  let v28 := M (M v1 v1) v0
  have h29 := h y v1 v0
  let v30 := M (M (M z x) x) x
  let v31 := M (M v0 z) z
  have h32 := h x v31 v30
  have h33 := R v30
  have h34 := R v31
  have h35 := h z x x
  have h36 := h x z z
  have h37 := S h35
  T (T (T (T (T h32 (C h34 (T (C (T (C h37 h34) (S h36)) h33) h37))) (h (M v31 z) y z)) (C h27 (T (C (T (T (T (T (C (C (T (C h34 (T h35 (C (T h36 (C h35 h34)) h33))) (S h32)) h24) h17) (C h25 (T h29 (C (C h29 h25) (R v28))))) (S (h v1 v0 v28))) (C h27 h25)) (C h23 h25)) h24) (C (T (C h26 h25) (C (T (T h23 h14) h9) h25)) h24)))) (C h23 h3)) h16

@[equational_result]
theorem Equation2373_implies_Equation2992 (G: Type _) [Magma G] (h: Equation2373 G) : Equation2992 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  let v2 := M v1 x
  let v3 := M v2 z
  have h4 := h v3 v1 v1
  have h5 := R v1
  let v6 := M v1 (M v3 v1)
  have h7 := R v2
  have h8 := h (M v1 v3) v3 v1
  have h9 := S h8
  have h10 := R v3
  have h11 := h z v2 v0
  have h12 := C h7 (S h11)
  let v13 := M v2 (M v0 (M z v0))
  have h14 := h v13 v1 v2
  have h15 := h v13 x v2
  have h16 := R x
  have h17 := C h7 h11
  have h18 := h z v2 y
  let v19 := M v2 v1
  have h20 := h v19 x v2
  have h21 := h (M v3 (M v1 v19)) x v3
  have h22 := h v2 v3 v1
  have h23 := h v2 v3 z
  have h24 := S h23
  have h25 := h (M v3 (M z v3)) x v3
  have h26 := C (T (T (T h25 (C (C h16 (T (C h10 h24) (C h10 h22))) h16)) (S h21)) (C h10 (C h5 (T (T (T (T (T h20 (C (C h16 (C h7 (S h18))) h16)) (C (C h16 h17) h16)) (S h15)) h14) (C (C h5 h12) h5))))) h10
  have h27 := h x v1 v0
  let v28 := M v1 (M v0 (M x v0))
  have h29 := h x v1 v2
  T (T h29 (C (T (T (T (T (T (T (h (M v1 (M v2 (M x v2))) x v1) (C (T (C h16 (C h5 (S h29))) (C h16 (C h5 h27))) h16)) (S (h v28 x v1))) (h v28 v2 v1)) (C (T (T (C h7 (C h5 (S h27))) (C (T (T h23 h26) h9) h7)) (C (T (T h8 (C (T (T (T (C h10 (C h5 (T (T (T (T (T (C (C h5 h17) h5) (S h14)) h15) (C (C h16 h12) h16)) (C (C h16 (C h7 h18)) h16)) (S h20)))) h21) (C (C h16 (T (C h10 (S h22)) (C h10 h23))) h16)) (S h25)) h10)) h24) (T (T (T h23 h26) h9) (C h5 h4)))) h7)) (S (h (M v1 v6) v2 v1))) (C h5 (R v6))) h5)) (S h4)

@[equational_result]
theorem Equation2779_implies_Equation4362 (G: Type _) [Magma G] (h: Equation2779 G) : Equation4362 G := fun x y z =>
  let v0 := M x z
  let v1 := M y z
  let v2 := M y v0
  have h3 := h v2 v1 v0
  have h4 := R v1
  let v5 := M v1 v0
  have h6 := R x
  let v7 := M x v1
  have h8 := R v7
  let v9 := M v7 v2
  have h10 := h (M v9 x) v2 v7
  have h11 := R v2
  have h12 := h x v2 v2
  have h13 := S h12
  have h14 := R v9
  let v15 := M x v2
  let v16 := M v2 v2
  let v17 := M v16 v15
  have h18 := h v17 v7 v2
  have h19 := h v17 x v2
  have h20 := h x v2 v1
  have h21 := R v15
  let v22 := M v2 v1
  have h23 := h (M v22 v7) x v2
  have h24 := R (M v2 v7)
  have h25 := h v22 v2 v7
  let v26 := M v1 v2
  have h27 := h y y v2
  let v28 := M y v2
  let v29 := M v28 v28
  have h30 := h y v0 z
  let v31 := M (M v0 z) v1
  T (T (C (T (T (T (T (T (T (T (T (h x x v1) (C (C h8 (h v7 v1 v2)) h6)) (S (h (M v26 v9) x v1))) (C (R v26) (T (T (T (T (C (T (T (T (C (T (h x y z) (C (R v5) h30)) h4) (S (h v31 v1 v0))) (h v31 y v0)) (C (C h11 (S h30)) h27)) h11) (S (h v29 v2 y))) (h v29 x y)) (C (C (R (M x y)) (T (S h27) (h y y v0))) h6)) (S (h v16 x y))))) (h (M v26 v16) x v1)) (C (C h8 (S (h v2 v1 v2))) h6)) h10) (C (C h24 (T (T (T (T (C (C h14 h12) h8) (S h18)) h19) (C (C h21 (T h13 h20)) h6)) (S h23))) h11)) (S h25)) h4) (C (T (T (T (T h25 (C (C h24 (T (T (T (T h23 (C (C h21 (T (S h20) h12)) h6)) (S h19)) h18) (C (C h14 h13) h8))) h11)) (S h10)) (C (C h8 h3) h6)) (S (h (M v5 (M v2 v0)) x v1))) h4)) (S h3)

@[equational_result]
theorem Equation3591_implies_Equation3997 (G: Type _) [Magma G] (h: Equation3591 G) : Equation3997 G := fun x y z =>
  let v0 := M x z
  let v1 := M z v0
  have h2 := h v1 y x
  let v3 := M (M v1 x) y
  have h4 := h x v3 v0
  let v5 := M v0 v0
  let v6 := M x v0
  let v7 := M v6 v3
  have h8 := h x z v1
  have h9 := S h8
  let v10 := M z v1
  let v11 := M v10 v0
  let v12 := M (M x v1) z
  have h13 := h v1 v12 v11
  have h14 := S h13
  have h15 := R v12
  have h16 := h z v0 v1
  have h17 := R v11
  have h18 := C h17 (T h8 (C h16 h15))
  have h19 := R v0
  have h20 := C h19 (T (T h18 h14) h9)
  have h21 := h v10 v0 v0
  have h22 := T h21 h20
  have h23 := S h21
  have h24 := C h17 (T (C (S h16) h15) h9)
  have h25 := T (T h8 h13) h24
  have h26 := C h19 h25
  have h27 := h z v12 v0
  let v28 := M (M z z) v0
  have h29 := h z v12 v28
  have h30 := h z v0 z
  have h31 := R v28
  have h32 := C h22 h19
  have h33 := R v5
  let v34 := M v1 y
  T (T (T (T (T (T (T (h x y v0) (h v0 (M v6 y) v0)) (C h19 (T (T (T (C h33 (C (h x v0 z) (R y))) (S (h z y v5))) (h z y v0)) (C (T (T (T h8 h13) h24) h32) (R v34))))) (S (h v5 v34 v0))) (C h33 (T (T h2 h4) (C (T (T (T (T (T (T (T h8 h13) h24) h32) (h v5 v0 v0)) (C h19 (T (T (T (T (T (C (T (T (T (C (T h26 h23) h19) h18) h14) h9) h25) h20) (C h19 h8)) (S h27)) h29) (C h31 (T (C (S h30) h15) h9))))) (C h19 (T (T (T (T (T (C h31 (T h8 (C h30 h15))) (S h29)) h27) (C h19 h9)) h26) h23))) (C h19 h22)) (R v7))))) (S (h v0 v7 v5))) (S h4)) (S h2)

@[equational_result]
theorem Equation952_implies_Equation1152 (G: Type _) [Magma G] (h: Equation952 G) : Equation1152 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  let v2 := M v1 z
  let v3 := M y v2
  let v4 := M z x
  have h5 := h y v1 v3
  let v6 := M v3 y
  let v7 := M v6 (M v3 v1)
  have h8 := R x
  have h9 := h (M v4 v4) y x
  have h10 := R v0
  have h11 := h x x z
  have h12 := h y x v3
  have h13 := S h12
  let v14 := M x v0
  have h15 := R v14
  have h16 := h y x v0
  have h17 := R (M v0 x)
  have h18 := h y y x
  let v19 := M v0 v0
  have h20 := R v19
  have h21 := h y v0 v3
  have h22 := S h21
  let v23 := M v6 (M v3 v0)
  have h24 := h v23 v0 v0
  have h25 := h v23 x v0
  have h26 := h y v0 x
  have h27 := h (M v0 v14) x v0
  have h28 := h v14 x v0
  have h29 := h (M v14 v14) x v0
  have h30 := h v0 v0 x
  have h31 := h v0 v0 v0
  have h32 := h (M v19 v19) x v0
  T (T (T h11 (C h8 (T (T (T (T (T (T h9 (C (R y) (C (S h11) h10))) (C h12 h15)) (C (T (T (T h13 h16) (C h8 (C (T (T (T (T (C h10 (T h18 (C h21 h20))) (S h24)) h25) (C h8 (C (T h22 h26) h17))) (S h27)) h17))) (S h28)) h15)) h29) (C h8 (C (T (S h30) h31) h17))) (S h32)))) (C h8 (T (T (T (T (T (T h32 (C h8 (C (T (S h31) h30) h17))) (S h29)) (C (T (T (T h28 (C h8 (C (T (T (T (T h27 (C h8 (C (T (S h26) h21) h17))) (S h25)) h24) (C h10 (T (C h22 h20) (S h18)))) h17))) (S h16)) h12) h15)) (C h13 (C h11 h10))) (S h9)) (C (T (T (T (T (h v4 x v1) (C h8 (C (T (T (T (h (M v1 v4) x x) (C h8 (C (S (h v0 x z)) (R (M x x))))) (S (h y x x))) h5) (R (M v1 x))))) (S (h v7 x v1))) (h v7 z v1)) (C (R z) (C (S h5) (R v2)))) (R v4))))) (S (h v3 x z))

@[equational_result]
theorem Equation684_implies_Equation1507 (G: Type _) [Magma G] (h: Equation684 G) : Equation1507 G := fun x y z =>
  let v0 := M y x
  let v1 := M v0 x
  let v2 := M y v1
  let v3 := M z y
  have h4 := h y y x
  have h5 := R y
  let v6 := M x (M (M x v0) v0)
  have h7 := h x x v0
  have h8 := R x
  let v9 := M z v3
  let v10 := M v0 v9
  have h11 := S (h v0 v0 x)
  let v12 := M v0 (M v1 x)
  let v13 := M v10 v0
  have h14 := R v0
  let v15 := M v9 (M (M v9 v3) v3)
  have h16 := h v9 v9 v3
  have h17 := R v9
  have h18 := S (h v10 v10 y)
  let v19 := M v10 (M (M v10 y) y)
  have h20 := h v9 v0 v9
  have h21 := h v9 v9 x
  have h22 := S h21
  let v23 := M v9 (M (M v9 x) x)
  have h24 := R v23
  have h25 := R v10
  have h26 := h v10 v9 v23
  let v27 := M v10 (M (M v10 x) x)
  let v28 := M v0 v10
  have h29 := h v28 v10 v27
  have h30 := R v27
  have h31 := h v10 v10 x
  have h32 := R v28
  have h33 := S h31
  T (h x v0 v9) (C h14 (T (T (T (T (C h8 (T (C h25 (T (T (T (T (T (T (T h20 (C h14 (T (C h17 (C h25 (T h21 (C h21 h24)))) (S h26)))) h29) (C h25 (C h32 (T (C h33 h30) h33)))) (h (M v10 (M v28 v10)) v10 v19)) (C h25 (T (T (C (T (T (T (C h25 (C h32 (T h31 (C h31 h30)))) (S h29)) (C h14 (T h26 (C h17 (C h25 (T (C h22 h24) h22)))))) (S h20)) (T (C h18 (R v19)) h18)) (C h17 (C h14 (T h16 (C h16 (R v15)))))) (S (h v0 v9 v15))))) (h v13 v0 v12)) (C h14 (C (R v13) (T (C h11 (R v12)) h11))))) (S (h v0 v10 v0)))) (C h8 (C h5 (T h7 (C h7 (R v6)))))) (S (h y x v6))) (h y z y)) (C (R z) (T (C h5 (C (R v3) (T h4 (C h4 (R v2))))) (S (h v3 y v2))))))

@[equational_result]
theorem Equation711_implies_Equation14 (G: Type _) [Magma G] (h: Equation711 G) : Equation14 G := fun x y =>
  let v0 := M x y
  have h1 := R v0
  let v2 := M y (M (M y x) x)
  have h3 := h y x v2
  have h4 := S h3
  have h5 := R v2
  have h6 := h y y x
  have h7 := R x
  have h8 := C h7 (C h7 (T h6 (C h6 h5)))
  have h9 := T h8 h4
  have h10 := C h9 h1
  let v11 := M x v0
  have h12 := h (M v11 v0) v0 v0
  have h13 := S h12
  let v14 := M v0 (M (M v0 x) x)
  let v15 := M y v0
  have h16 := h v0 v15 v14
  have h17 := R v14
  have h18 := h v0 v0 x
  have h19 := T h18 (C h18 h17)
  have h20 := R v15
  have h21 := T (T (C h20 (C h10 h1)) (C h20 (C h20 h19))) (S h16)
  have h22 := S h6
  have h23 := C h7 (C h7 (T (C h22 h5) h22))
  have h24 := T h3 h23
  have h25 := C h24 h1
  have h26 := h v11 v15 v0
  have h27 := C (T h26 (C h25 h21)) h1
  have h28 := h v0 y v14
  have h29 := R y
  have h30 := h v11 v0 v15
  have h31 := C h1 (T (T (T h3 h23) h30) (C h1 (T (T (C h1 (C (T (T (C h9 h20) (C h29 (C h29 h19))) (S h28)) (T h25 h27))) h13) h27)))
  have h32 := S h18
  have h33 := T (C h32 h17) h32
  have h34 := C h10 (T (T h16 (C h20 (C h20 h33))) (C h20 (C h25 h1)))
  have h35 := C (T h34 (S h26)) h1
  T (T (T (T (T (h x v15 y) (C h20 (C h20 (T (T (T h31 h13) h27) (C (T h34 (C (T (T h25 h12) (C h1 (T (T (T (C h1 (T (T h35 h12) (C h1 (C (T (T h28 (C h29 (C h29 h33))) (C h24 h20)) (T h35 h10))))) (S h30)) h8) h4))) h21)) h1))))) (S (h (M v0 y) v15 v0))) h31) h13) h10

@[equational_result]
theorem Equation1090_implies_Equation3489 (G: Type _) [Magma G] (h: Equation1090 G) : Equation3489 G := fun x y z =>
  let v0 := M y z
  let v1 := M y (M v0 z)
  let v2 := M x x
  have h3 := h v1 v2 v1
  have h4 := S h3
  have h5 := h v1 v1 v0
  have h6 := S h5
  have h7 := R v0
  have h8 := R z
  have h9 := h y v0 z
  have h10 := R v1
  have h11 := C h10 (C (S h9) h8)
  have h12 := h v0 v1 z
  have h13 := C h10 (C (T (T h12 h11) (C h10 (T h12 h11))) h7)
  have h14 := S h12
  have h15 := C h10 (C h9 h8)
  have h16 := h v1 v0 v0
  let v17 := M v1 (M v2 v1)
  have h18 := R v17
  have h19 := C h18 (T (T (T (C h4 h10) (C h10 (T h16 (C h7 (T (T (C (T h13 h6) h7) h15) h14))))) h13) h6)
  have h20 := h v2 v17 v1
  have h21 := T h20 h19
  have h22 := S h20
  have h23 := C h10 (C (T (T (C h10 (T h15 h14)) h15) h14) h7)
  have h24 := C h18 (T (T (T h5 h23) (C h10 (T (C h7 (T (T h12 h11) (C (T h5 h23) h7))) (S h16)))) (C h3 h10))
  have h25 := T h24 h22
  have h26 := h (M v17 v1) v2 x
  have h27 := R x
  have h28 := h x v2 x
  have h29 := S h28
  let v30 := M (M x (M v2 x)) x
  have h31 := R v30
  have h32 := R v2
  have h33 := C h32 (T (C (C h27 h29) h31) h29)
  have h34 := h x v2 v30
  have h35 := S h34
  have h36 := C h32 (T h28 (C (C h27 h28) h31))
  have h37 := C (T (T (C h25 (T h36 h35)) h36) h35) h27
  T (T (T (T (T (T (T h20 h19) h26) (C h21 (T (T (T (T h37 h20) h19) h26) (C h32 h37)))) (C h25 (R (M v2 v2)))) (C h21 (T (T (T (C h32 (C (T (T h34 h33) (C h21 (T h34 h33))) h27)) (S h26)) h24) h22))) (C h25 h21)) h4

@[equational_result]
theorem Equation3385_implies_Equation3820 (G: Type _) [Magma G] (h: Equation3385 G) : Equation3820 G := fun x y z =>
  let v0 := M z z
  let v1 := M x y
  have h2 := h v0 v1 v0
  let v3 := M v1 v0
  have h4 := h v0 (M v0 v3) z
  have h5 := R z
  have h6 := S (h v1 v0 v0)
  have h7 := h z z z
  have h8 := R v0
  have h9 := h z z v0
  have h10 := T h9 (C h8 (S h7))
  have h11 := R v1
  have h12 := C h8 (C h11 h10)
  have h13 := h v1 z v0
  have h14 := S h13
  let v15 := M z v0
  have h16 := h x y v0
  let v17 := M v0 v1
  let v18 := M x (M y v0)
  have h19 := h v0 v18 v17
  have h20 := R v17
  have h21 := h y v0 v1
  have h22 := h v0 x y
  have h23 := R x
  have h24 := h v1 v0 x
  have h25 := S h24
  have h26 := C h23 (T h21 (C h11 (S h22)))
  have h27 := R v15
  have h28 := C h8 (T (C h11 (T (h v15 v0 v1) (C h11 (C h27 (T (T (T (h v0 v1 v17) (C h20 (C h8 (C (T (T (T (T (T (T (T h16 h19) (C h20 (C h8 (C (T h26 h25) h20)))) (S (h v0 v3 v17))) h12) h6) h24) (C h23 (T (C h11 h22) (S h21)))) h20)))) (S h19)) (S h16)))))) (S (h v1 v15 v1)))
  have h29 := h v1 v15 v0
  have h30 := h v0 v15 v0
  have h31 := C h27 h10
  T (T (T (T h16 (h v0 v18 z)) (C h5 (C h8 (C (T (T (T (T (T (T (T (T (T h26 h25) (h v1 v0 z)) (C h5 (T (T (T (C h11 (T (T (T (T (h v0 z v0) (C h8 (T (T h30 (C h8 (T (T (C h8 h31) (S (h v15 v0 v0))) h31))) (C h8 (C h27 (T (C h8 h7) (S h9))))))) (S h30)) (C h8 (C h5 h10))) (S (h z v0 v0)))) h29) h28) h14))) (C h5 (T h13 (C h8 (T (T h29 h28) h14))))) (S (h v0 v1 z))) h2) h4) (C h5 (C h8 (C (T h12 h6) h5)))) (S (h v0 v3 z))) h5)))) (S h4)) (S h2)

@[equational_result]
theorem Equation3404_implies_Equation4143 (G: Type _) [Magma G] (h: Equation3404 G) : Equation4143 G := fun x y z =>
  let v0 := M x y
  let v1 := M x z
  let v2 := M v1 y
  have h3 := S (h x y v2)
  let v4 := M v2 x
  have h5 := h v4 v2 z
  have h6 := h x z v2
  have h7 := R z
  have h8 := h z v1 x
  have h9 := R v1
  have h10 := C h9 (T (T (S h8) (C h7 h6)) (S h5))
  have h11 := h v1 x v1
  have h12 := R v2
  have h13 := C h12 (T (T h11 h10) (S (h y v4 v1)))
  have h14 := S h11
  have h15 := h x z y
  have h16 := S h15
  let v17 := M z (M y x)
  have h18 := S (h y v17 x)
  have h19 := R v0
  have h20 := R y
  have h21 := R x
  have h22 := C h21 (T (T (h x v1 y) (C h20 (T (T (C h9 (T (h y x v1) (C h9 (T (h x v2 v1) (C h9 (T h13 h3)))))) (S (h v0 v1 v1))) (C h19 h15)))) (S (h v17 v0 y)))
  let v23 := M v2 v1
  have h24 := S (h y v2 v1)
  T (T (h x y v0) (C h19 (T (T (T (C h20 (T (h v0 x v1) (C h9 (S (h y v1 x))))) (S (h v1 v1 y))) (h v1 v1 z)) (C h7 (T (T (T (T (C h9 h8) h14) (h v1 x x)) (C h21 (T (T (T (T (T (T (T (T h22 h18) (h y v17 v1)) (C h9 (T (T (T (h v17 v2 y) (C h20 (C h12 h16))) (C h20 (T (h v2 v1 v2) (C h12 h24)))) (S (h v2 v2 y))))) h24) (C h20 (h v1 y v2))) (S (h v23 v2 y))) (h v23 v2 v2)) (C h12 (T (T (S (h v1 v2 v2)) (h v1 v2 x)) (C h21 (T (T (C h12 (T (T (h x v1 v1) (C h9 (T (T (C h9 (T (T h11 h10) (C h9 (T (T (T (T h5 (C h7 (S h6))) (C h7 (h x z z))) (S (h (M z x) z z))) (C (T (T (T (h z x x) h22) h18) h16) h7))))) (S (h z v1 v1))) h8))) h14)) h13) h3))))))) (S (h v0 v2 x))))))) (S (h v2 z v0))

@[equational_result]
theorem Equation522_implies_Equation1171 (G: Type _) [Magma G] (h: Equation522 G) : Equation1171 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M v1 x
  let v3 := M y v2
  have h4 := S (h v2 x x)
  have h5 := h x v2 v2
  have h6 := h v1 v2 x
  have h7 := h v1 v3 z
  have h8 := S h7
  have h9 := h z v1 v0
  have h10 := R v1
  have h11 := h v0 v1 v1
  have h12 := R z
  have h13 := C h12 (T h11 (C h10 (S h9)))
  have h14 := R v3
  have h15 := C h14 (C h14 h13)
  have h16 := h y v3 z
  have h17 := h y y z
  have h18 := S h17
  have h19 := R (M y v1)
  have h20 := S h16
  have h21 := C h12 (T (C h10 h9) (S h11))
  have h22 := C h14 (C h14 h21)
  have h23 := T (T h7 h22) h20
  have h24 := C h23 h19
  have h25 := R v2
  have h26 := h y v2 v1
  have h27 := R x
  have h28 := C h27 (T (T (T h24 h18) h26) (C h25 (T (C h25 (T (T (T (T (T h24 h18) h16) h15) h8) h6)) (S h5))))
  have h29 := h y x v1
  have h30 := T (T h16 h15) h8
  have h31 := C h30 h19
  have h32 := S h6
  have h33 := C h27 (T (T (T (C h25 (T h5 (C h25 (T (T (T (T (T h32 h7) h22) h20) h17) h31)))) (S h26)) h29) (C h27 h28))
  have h34 := h v1 v1 z
  T (T (h x v3 x) (C h14 (C h14 (T (T (T (C h27 (C h27 (T h5 (C h25 (T (T (T (T (T h32 h7) h22) h20) h29) (C h27 (T (T h28 h33) h4))))))) (S (h x x v2))) (h x v3 y)) (C h14 (C h14 (C (R y) (T (T (T (T (T (C h27 (T (T (T (T h16 h15) h8) h34) (C h23 (C h23 (T (T (T h21 h7) h22) h20))))) (C h27 (T (T (C h30 (C h30 (T (T (T h16 h15) h8) h13))) (S h34)) h13))) (C h27 (T (T (T (T (T h21 h7) h22) h20) h17) h31))) h28) h33) h4)))))))) (S (h v3 v3 v3))

@[equational_result]
theorem Equation711_implies_Equation1304 (G: Type _) [Magma G] (h: Equation711 G) : Equation1304 G := fun x y z =>
  let v0 := M (M x z) z
  let v1 := M v0 y
  have h2 := R v1
  let v3 := M y v1
  have h4 := h y v3 v1
  have h5 := S h4
  have h6 := h v1 v1 x
  have h7 := S h6
  let v8 := M v1 (M (M v1 x) x)
  have h9 := R v8
  have h10 := T (C h7 h9) h7
  have h11 := R v3
  have h12 := h v1 v3 v8
  have h13 := T h12 (C h11 (C h11 h10))
  have h14 := C h11 h13
  have h15 := T h14 h5
  have h16 := C h15 h2
  let v17 := M v3 v1
  have h18 := h (M v17 v1) v1 v1
  have h19 := S h18
  have h20 := T h6 (C h6 h9)
  have h21 := T (C h11 (C h11 h20)) (S h12)
  have h22 := C h11 h21
  have h23 := T h4 h22
  have h24 := C h23 h2
  have h25 := C (T h14 (C h24 h21)) h2
  have h26 := h v1 y v8
  have h27 := R y
  have h28 := h v17 v1 v3
  have h29 := C h21 (T (T (T h4 h22) h28) (C h2 (T (T (C h2 (C (T (T (C h15 h11) (C h27 (C h27 h20))) (S h26)) (T h24 h25))) h19) h25)))
  have h30 := C h13 h27
  have h31 := C (T (C h16 h13) h22) h2
  let v32 := M v0 (M (M v0 x) x)
  have h33 := h v0 v0 x
  have h34 := R x
  T (T (T (T (T (T (T (T (T (h x x z) (C h34 (C h34 (T h33 (C h33 (R v32)))))) (S (h v0 x v32))) (h v0 v3 y)) (C h11 (C h11 (T (T (T (T h30 h29) h19) h25) (C (C (T (T h18 (C h13 (T (T (T (C h2 (T (T h31 h18) (C h2 (C (T (T h26 (C h27 (C h27 h10))) (C h23 h11)) (T h31 h16))))) (S h28)) h14) h5))) (C h21 h27)) h2) h2))))) (S (h (M v1 y) v3 v1))) h30) h29) h19) h16

@[equational_result]
theorem Equation492_implies_Equation2917 (G: Type _) [Magma G] (h: Equation492 G) : Equation2917 G := fun x y z =>
  let v0 := M x y
  let v1 := M y v0
  let v2 := M v1 z
  let v3 := M v2 z
  have h4 := h v3 v0 y
  have h5 := S h4
  have h6 := h v1 v1 v2
  have h7 := h v1 z v1
  have h8 := R v2
  have h9 := h z v2 v1
  have h10 := R v1
  have h11 := T (C h10 (C h10 (C h8 (T h9 (C h8 (S h7)))))) (S h6)
  have h12 := R y
  have h13 := R v3
  have h14 := h y v3 v1
  have h15 := R v0
  have h16 := C h15 (T h14 (C h13 (C h12 h11)))
  have h17 := h y v1 v3
  have h18 := S h17
  have h19 := h v3 v3 v1
  have h20 := C h12 (T h19 (C h13 (C h13 h11)))
  have h21 := h v3 v0 v3
  have h22 := h v0 y v0
  have h23 := S h22
  have h24 := T h6 (C h10 (C h10 (C h8 (T (C h8 h7) (S h9)))))
  have h25 := C h12 (C h15 (C h15 (T h4 (C h15 (T (C h13 (C h12 h24)) (S h14))))))
  have h26 := h y v3 v0
  have h27 := C h12 (T (C h15 (C h13 (C h13 (T h26 (C h13 (T h25 h23)))))) (S h21))
  have h28 := h v0 y v3
  have h29 := h v0 y v1
  have h30 := h v1 v0 v1
  have h31 := S h28
  have h32 := C h15 (C h13 (C h13 (T (C h13 (T h22 (C h12 (C h15 (C h15 (T h16 h5)))))) (S h26))))
  T (T (T (T (T (h x y y) (C h12 (C (R x) (T (C h12 (C h12 (T h26 (C h13 (T (T (T h25 h23) (h v0 v3 y)) (C h13 (T (C h15 (C h12 (T (T (T (C h12 (T h21 h32)) h31) h29) (C h12 (T (C h15 (C h10 (C h10 (T h17 (C h10 (T (C h12 (T (T (T (C h13 (C h13 h24)) (S h19)) h21) h32)) h31)))))) (S h30)))))) (S (h y v0 y))))))))) (S (h y y v3)))))) (h v1 v0 y)) (C h15 (T (C h10 (T (T (T (T (C h12 (T h30 (C h15 (C h10 (C h10 (T (C h10 (T (T h28 h27) h20)) h18)))))) (S h29)) h28) h27) h20)) h18))) h16) h5

@[equational_result]
theorem Equation3131_implies_Equation2199 (G: Type _) [Magma G] (h: Equation3131 G) : Equation2199 G := fun x y z =>
  let v0 := M y x
  let v1 := M y z
  let v2 := M v1 z
  let v3 := M v2 v0
  have h4 := R z
  have h5 := h v1 v2 v1
  have h6 := R v2
  have h7 := h z v1 v1
  have h8 := T (C h7 h6) (S h5)
  have h9 := h z v2 y
  have h10 := R y
  have h11 := h z y z
  have h12 := C h11 h10
  have h13 := h y z v2
  have h14 := T (T h13 (C (C (T (C h12 h6) (S h9)) h6) h4)) (C h8 h4)
  have h15 := R v0
  have h16 := R v3
  have h17 := C (S h7) h6
  have h18 := T h5 h17
  have h19 := C h18 h14
  have h20 := S h13
  have h21 := S h11
  have h22 := C h21 h10
  have h23 := C (C (T h9 (C h22 h6)) h6) h4
  have h24 := C h18 h4
  have h25 := T (T h24 h23) h20
  have h26 := C h8 h25
  have h27 := C (T h12 (C h21 h14)) h14
  have h28 := C h22 h25
  have h29 := R v1
  have h30 := C h8 h6
  T (T (h x y v0) (C (C (C (T (h v0 v3 z) (C (T (C (T (T (T (T (T (T (T (C (T (C (T (h v3 v0 v1) (C (T (T (T (T (T (C (C (T (C (h v0 v2 v2) h16) (S (h v2 v3 v2))) h29) h29) (C (C (T (T (h v2 v1 y) (C (T (T (T (T (T (T (C (T (C (C h18 h6) h14) (C h30 h6)) h14) (C (R (M (M v1 v2) v2)) h25)) (S (h z y v2))) h9) h28) h27) h26) h29)) (C (T h19 h30) h29)) h29) h29)) (S (h v2 v1 v1))) h24) h23) h20) h15)) h15) (C (C (T (h y v1 y) (C (S (h z y y)) h29)) h15) h15)) h4) (S (h v1 z v0))) h5) h17) (C (T h9 h28) h25)) (C (T h27 h26) h10)) (C (R (M v1 y)) h14)) (C h19 h6)) h4) (S (h v2 z v2))) h16)) h15) h15) h14)) (S (h v3 v2 v0))

@[equational_result]
theorem Equation3211_implies_Equation4182 (G: Type _) [Magma G] (h: Equation3211 G) : Equation4182 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M v1 x
  have h3 := R z
  have h4 := h v0 y z
  have h5 := S h4
  have h6 := R y
  have h7 := R v0
  have h8 := h v0 v0 z
  have h9 := h v1 v0 v1
  have h10 := R v1
  have h11 := h y y z
  have h12 := h z v1 y
  have h13 := h v0 z v1
  have h14 := h z v0 v0
  have h15 := S h14
  have h16 := S h13
  have h17 := C (T h9 (C (C (C (T (C (C h11 h3) h10) (S h12)) h10) h10) h7)) h3
  have h18 := C (C (T h17 h16) h7) h7
  have h19 := h z y z
  have h20 := C (T (T (T (C (C (T h19 (C (T (T (T h17 h16) h4) (C (T (C (C (T h8 h18) h3) h7) h15) h6)) h6)) h3) h3) (S (h z z y))) h14) (C (C (T (C (C (T h13 (C (T (C (C (C (T h12 (C (C (S h11) h3) h10)) h10) h10) h7) (S h9)) h3)) h7) h7) (S h8)) h3) h7)) h6
  have h21 := h y z z
  have h22 := T h21 (C (T h20 h5) h3)
  have h23 := R v2
  let v24 := M x y
  have h25 := R v24
  have h26 := h x y z
  have h27 := S h26
  have h28 := h y v0 z
  have h29 := S h28
  T (C (T (h x v2 y) (C (T (T (T (C (T (T (C h27 h6) (h v24 y v0)) (C (C (T (T (T (T (C (C (T h28 (C (S h19) h7)) h7) h7) (C (T (T (C (T (T (T (C h19 h7) h29) h21) (C (T (T (T h20 h5) h8) h18) h3)) h7) h15) h19) h7)) h29) (h y v24 v2)) (C (T (C (T (C (C (C h26 h6) h23) h23) (S (h v2 v2 y))) h6) h27) h25)) h25) h22)) (R x)) (S (h v1 x v24))) (h v1 y z)) (C (R (M v1 v1)) h22)) h23)) h22) (S (h v2 v1 v1))

@[equational_result]
theorem Equation4197_implies_Equation3350 (G: Type _) [Magma G] (h: Equation4197 G) : Equation3350 G := fun x y z =>
  let v0 := M z z
  let v1 := M x v0
  let v2 := M y v1
  have h3 := R v2
  have h4 := R v0
  have h5 := R v1
  have h6 := h z z x
  have h7 := S h6
  let v8 := M x z
  have h9 := h (M v8 z) x v2
  have h10 := S h9
  have h11 := R x
  have h12 := h v8 z v2
  have h13 := R z
  have h14 := h x z v0
  have h15 := h z x z
  have h16 := h (M (M z x) v0) z v2
  have h17 := h x v0 z
  have h18 := C (C (C h3 (T (T (T h17 h16) (C (C (C h3 (T (C h15 h4) (S h14))) h13) h3)) (S h12))) h11) h3
  have h19 := h v1 x v2
  have h20 := h v1 x v1
  have h21 := h x v0 v1
  have h22 := S h21
  let v23 := M v1 x
  have h24 := h (M v23 v0) v1 x
  have h25 := S h24
  have h26 := h v23 v0 v2
  have h27 := S h19
  have h28 := C (C (C h3 (T (T (T h12 (C (C (C h3 (T h14 (C (S h15) h4))) h13) h3)) (S h16)) (S h17))) h11) h3
  have h29 := h v0 v0 v2
  have h30 := h z z z
  have h31 := h z z v0
  have h32 := C h11 (T (T (T (T h31 (C (S h30) h4)) h29) (C (C (C h3 (T (T (T h6 h9) h28) h27)) h4) h3)) (S h26))
  let v33 := M v0 x
  T (T (T (T (h x y v0) (h (M v33 y) v0 v2)) (C (C (C h3 (T (h v33 y v1) (C (C (T (T (T (T (T (C (T (T h21 h24) (C (C (C h11 (T (T (T (T h26 (C (C (C h3 (T (T (T h19 h18) h10) h7)) h4) h3)) (S h29)) (C h30 h4)) (S h31))) h5) h11)) (T (T (C (T (T (T (T (T h6 h9) h28) h27) h20) (C (T (T (T (C (C h32 h5) h11) h25) h22) h32) h5)) h11) h25) h22)) (S h20)) h19) h18) h10) h7) (R y)) h5))) h4) h3)) (S (h (M (M v0 y) v1) v0 v2))) (S (h y v1 v0))

@[equational_result]
theorem Equation3131_implies_Equation2917 (G: Type _) [Magma G] (h: Equation3131 G) : Equation2917 G := fun x y z =>
  let v0 := M x y
  let v1 := M y v0
  let v2 := M (M v1 z) z
  have h3 := R v0
  have h4 := h y v2 v2
  have h5 := R v2
  have h6 := h v0 y z
  have h7 := C (C h6 h5) h5
  have h8 := h v2 v0 v2
  have h9 := T h8 (C (T (C h7 h5) (S h4)) h3)
  have h10 := R (M v0 v2)
  have h11 := S h6
  have h12 := C (C h11 h5) h5
  have h13 := T (C (T h4 (C h12 h5)) h3) (S h8)
  have h14 := C h10 h13
  have h15 := h v0 v2 v0
  have h16 := h v2 y y
  have h17 := R y
  have h18 := h y v1 y
  have h19 := S h18
  have h20 := R v1
  have h21 := h v0 y y
  have h22 := C h21 h20
  have h23 := C h11 h20
  have h24 := C (T (T h23 h22) h19) h13
  have h25 := C h6 h20
  have h26 := C (S h21) h20
  have h27 := h y v2 v1
  have h28 := S h27
  have h29 := C (T (T h18 h26) h25) h9
  have h30 := C h29 h13
  have h31 := h v2 y v1
  have h32 := h y v0 v0
  have h33 := C (T (T (T (T h23 h22) h19) h27) (C h24 h9)) h20
  have h34 := C (T (T h33 (C (T (T (T h30 h28) h32) (C (C (C (T (T (C h6 h17) (C (C (T h31 (C (T (C (T (T (T (T h30 h28) h18) h26) h25) h20) h24) h17)) h17) h17)) (S h16)) h3) h3) h3)) h13)) (S h15)) h5
  T (T (h x v0 v2) (C (T (C (T (T (C (T (T (T (C (T (T h15 (C (T (T (T (C (C (C (T (T h16 (C (C (T (C (T h29 h33) h17) (S h31)) h17) h17)) (C h11 h17)) h3) h3) h3) (S h32)) h27) h34) h9)) h14) (R x)) (S (h y x v2))) h27) h34) h9) h14) h7) h5) (C (T h12 (C h10 h9)) h9)) h3)) (S (h v2 v0 v1))

@[equational_result]
theorem Equation492_implies_Equation572 (G: Type _) [Magma G] (h: Equation492 G) : Equation572 G := fun x y z =>
  let v0 := M x y
  let v1 := M z v0
  have h2 := h v1 v0 z
  have h3 := S h2
  let v4 := M z v1
  have h5 := h v1 v1 v4
  have h6 := h v0 v0 z
  have h7 := S h6
  have h8 := R z
  have h9 := R v4
  have h10 := h z v4 v0
  have h11 := h z v1 z
  have h12 := h v1 v4 z
  have h13 := R v1
  have h14 := C h13 (C h8 (T (C h13 (C h13 (T (T h12 (C h9 (S h11))) (C h9 (T h10 (C h9 (C h8 h7))))))) (S h5)))
  have h15 := h z v1 v1
  have h16 := h z v0 v1
  have h17 := S h16
  have h18 := h v0 v1 z
  have h19 := h z v0 z
  have h20 := C h8 (C h13 (C h13 (T (C h13 h19) (S h18))))
  have h21 := h v1 z v1
  have h22 := R v0
  have h23 := C h22 (T h21 h20)
  have h24 := S h21
  have h25 := C h8 (C h13 (C h13 (T h18 (C h13 (S h19)))))
  have h26 := C h22 (T h25 h24)
  have h27 := h v0 z v0
  have h28 := S h15
  have h29 := C h13 (C h8 (T h5 (C h13 (C h13 (T (T (C h9 (T (C h9 (C h8 h6)) (S h10))) (C h9 h11)) (S h12))))))
  have h30 := R x
  have h31 := R y
  T (h x y y) (C h31 (T (T (C h30 (T (C h31 (C h31 (T (T (h y v0 x) (C h22 (S (h x y x)))) (C h22 (T (h x v0 y) (C h22 (T (C h30 (C h31 (C h31 (T (h v0 y x) (C h31 (T (C h22 (C h30 (T (h v0 v4 v0) (C (T (C h8 (T h2 (C h22 (T (T (T (T h29 h28) h16) (C h22 (T (T (T h25 h24) h2) (C h22 (T (T (T h29 h28) h16) h26))))) (C h22 (C h22 (T h23 h17))))))) (S h27)) (C h22 h7))))) (S (h x v0 v0)))))))) (S (h y x y))))))))) (S (h y y v0)))) h27) (C h8 (T (C h22 (T (T (T (T (C h22 (C h22 (T h16 h26))) (C h22 (T (T (T (C h22 (T (T (T h23 h17) h15) h14)) h3) h21) h20))) h17) h15) h14)) h3))))

@[equational_result]
theorem Equation492_implies_Equation4026 (G: Type _) [Magma G] (h: Equation492 G) : Equation4026 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M v1 x
  have h3 := h x y y
  have h4 := S h3
  have h5 := h y y z
  have h6 := S h5
  have h7 := R y
  have h8 := h y z z
  have h9 := S h8
  have h10 := h z y z
  have h11 := h v1 v0 v1
  have h12 := R z
  have h13 := R v1
  have h14 := h z v1 y
  have h15 := R v0
  have h16 := C h12 (T (C h15 (C h13 (C h13 (T h14 (C h13 (C h12 h6)))))) (S h11))
  have h17 := h v0 z v1
  have h18 := h v0 y z
  have h19 := S h18
  have h20 := h v0 v0 z
  have h21 := C h15 (C h12 (T (C h15 (C h15 (T h17 h16))) (S h20)))
  have h22 := h z v0 v0
  have h23 := h z z y
  have h24 := S h22
  have h25 := S h17
  have h26 := C h12 (T h11 (C h15 (C h13 (C h13 (T (C h13 (C h12 h5)) (S h14))))))
  have h27 := C h15 (C h12 (T h20 (C h15 (C h15 (T h26 h25)))))
  have h28 := C h12 (T h18 (C h7 (T (T (T h27 h24) h23) (C h12 (C h12 (T (C h7 (T (T (T (C h7 (T h22 h21)) h19) h17) h16)) (S h10)))))))
  have h29 := T h28 h9
  have h30 := h y v1 y
  have h31 := R x
  let v32 := M x y
  have h33 := R v32
  have h34 := C h7 (T (T (C h33 (C h33 (C h29 (T h3 (C h7 (C h31 (T (C (T h8 (C h12 (T (C h7 (T (T (T (C h12 (C h12 (T h10 (C h7 (T (T (T h26 h25) h18) (C h7 (T h27 h24))))))) (S h23)) h22) h21)) h19))) (C h7 h5)) (S h30)))))))) (S (h v32 v32 y))) (C h31 (T h30 (C h29 (C h7 h6)))))
  have h35 := R v2
  have h36 := h y v2 v32
  T (C h31 (T h36 (C h35 (T (T (T h34 h4) (h x v2 v1)) (C h35 (T (T (T (T (S (h v1 x v1)) h28) h9) h36) (C h35 (T h34 h4)))))))) (S (h v2 x v2))

@[equational_result]
theorem Equation4197_implies_Equation4013 (G: Type _) [Magma G] (h: Equation4197 G) : Equation4013 G := fun x y z =>
  let v0 := M x y
  let v1 := M y z
  let v2 := M z v1
  let v3 := M v2 x
  have h4 := R v3
  have h5 := R v0
  have h6 := h y v2 v3
  have h7 := h x y v2
  have h8 := h x y y
  have h9 := R y
  have h10 := h (M y x) y v3
  have h11 := h y x z
  have h12 := S h11
  have h13 := R z
  have h14 := R x
  have h15 := h z y v1
  have h16 := R v1
  have h17 := h z z y
  have h18 := h z z v2
  have h19 := R v2
  have h20 := h v1 z z
  have h21 := h z v2 v1
  have h22 := C (C (T (T h21 (C (T (T (C h20 h19) (S h18)) h17) h16)) (S h15)) h14) h13
  have h23 := h v2 x z
  have h24 := T (T h23 h22) h12
  have h25 := h v3 y v3
  have h26 := h y y v3
  have h27 := S h23
  have h28 := C (C (T (T h15 (C (T (T (S h17) h18) (C (S h20) h19)) h16)) (S h21)) h14) h13
  have h29 := h y x x
  let v30 := M v0 x
  T (T (T (T (h x y v0) (h (M v30 y) v0 v3)) (C (C (C h4 (T (T (T (T (T (T (h v30 y y) (C (C (T (T (T (C h9 (T (T (T (h v0 x v3) (C (C (T (C (T (T (T h23 h22) h12) h29) h5) (C (T (T (T (S h29) h11) h28) h27) (T (h x y v1) (C (T (C (T (h v1 x z) (C h24 h13)) h9) (S (h x z y))) h16)))) h14) h4)) (S (h (M (M x z) v1) x v3))) (S (h z v1 x)))) h6) (C (T (T (S h7) h8) (C (T (T h10 (C (C (C h4 (T (T h11 h28) h27)) h9) h4)) (S h25)) h9)) h4)) (S h26)) h9) h9)) (S (h y y y))) h26) (C (T (T (C (T (T h25 (C (C (C h4 h24) h9) h4)) (S h10)) h9) (S h8)) h7) h4)) (S h6)) (h y v2 x))) h5) h4)) (S (h (M (M v0 v2) x) v0 v3))) (S (h v2 x v0))

@[equational_result]
theorem Equation711_implies_Equation2349 (G: Type _) [Magma G] (h: Equation711 G) : Equation2349 G := fun x y z =>
  let v0 := M z x
  have h1 := h z v0 x
  have h2 := S h1
  have h3 := h x x x
  have h4 := S h3
  let v5 := M x (M (M x x) x)
  have h6 := R v5
  have h7 := R v0
  have h8 := h x v0 v5
  have h9 := T h8 (C h7 (C h7 (T (C h4 h6) h4)))
  have h10 := C h7 h9
  let v11 := M v0 x
  have h12 := T h3 (C h3 h6)
  have h13 := T (C h7 (C h7 h12)) (S h8)
  have h14 := R x
  have h15 := C h7 h13
  have h16 := C (T h1 h15) h14
  have h17 := C h16 h13
  have h18 := T h1 h17
  have h19 := T h10 h2
  have h20 := C h19 h14
  let v21 := M v11 x
  have h22 := S (h v21 x x)
  have h23 := C (T h10 h17) h14
  have h24 := R z
  let v25 := M v0 v21
  have h26 := h v0 y v25
  have h27 := R v25
  have h28 := h v0 v0 x
  have h29 := R y
  have h30 := T (C h29 (C h29 (T h28 (C h28 h27)))) (S h26)
  have h31 := S h28
  let v32 := M v0 v11
  let v33 := M y v0
  let v34 := M y v33
  have h35 := S (h x x v33)
  let v36 := M x (M (M x v33) v33)
  T (T (T (h x v0 v36) (C h7 (C h7 (T (C h35 (R v36)) h35)))) (h v32 v34 z)) (C (R v34) (T (T (T (T (C h30 (R (M (M v32 z) z))) (C h7 (C (T (T (T (C h13 h18) (C h14 (T (T (T (C h20 h9) h15) (h v11 x v0)) (C h14 (T (T (C h14 (C (T (T (T (C (R v11) (T h26 (C h29 (C h29 (T (C h31 h27) h31))))) (C h19 h30)) (C h24 (C h24 h12))) (S (h x z v5))) (T h16 h23))) h22) h23))))) h22) h20) h18))) (S (h v11 v0 x))) h10) h2))

@[equational_result]
theorem Equation2298_implies_Equation2 (G: Type _) [Magma G] (h: Equation2298 G) : Equation2 G := fun x y =>
  have h0 := h y y y
  have h1 := S h0
  have h2 := R y
  let v3 := M x y
  let v4 := M x v3
  let v5 := M x v4
  let v6 := M y (M y y)
  let v7 := M y v6
  have h8 := h v7 v5 y
  have h9 := S h8
  have h10 := R v7
  have h11 := T h0 (C h10 h0)
  have h12 := R v5
  have h13 := h x x y
  have h14 := C (T h13 (C h12 h11)) h2
  have h15 := C (T h14 h9) h2
  have h16 := T (C h10 h1) h1
  have h17 := R x
  have h18 := C h17 h16
  have h19 := C h18 h2
  have h20 := h v7 x y
  have h21 := h y x y
  have h22 := S h21
  have h23 := R (M x v6)
  have h24 := C h17 (T (C h23 h22) h22)
  have h25 := C h17 (T h21 (C h23 h21))
  have h26 := C (T (C h12 h16) (S h13)) h2
  have h27 := C (T (T h8 h26) h25) h2
  have h28 := S h20
  have h29 := C (T h24 (C h17 h11)) h2
  have h30 := C (T (T (T (T (T h0 h27) h29) h28) h8) h26) (T (T h0 h27) (C h24 h2))
  have h31 := C (T (C h10 h16) h1) h2
  have h32 := h v7 v7 y
  have h33 := h x y y
  let v34 := M y v4
  have h35 := S h32
  have h36 := C (T (T h24 h14) h9) h2
  have h37 := C (T h18 h25) h2
  have h38 := T h0 (C h10 h11)
  T (T (T (T (T (T (T (T h33 (C (T (T (T (T (C h38 (T (T (T (T (T (T (T (C h17 (T (T (T (T h14 h9) h32) h31) h30)) (C h17 (T (T (T (T (T (T (C (T (T (T (T (T h14 h9) h20) h19) h15) h1) (T h15 h1)) (C h38 h2)) h35) h20) h37) h36) h1))) h14) h9) h20) h37) h36) h1)) h35) (h v7 v34 y)) (C (T (C (R v34) h16) (S h33)) h2)) (C h17 (T (T (T (T (T (T h0 h27) h29) h28) h32) h31) h30))) h2)) (S (h v3 x y))) h14) h9) h20) h19) h15) h1

@[equational_result]
theorem Equation3404_implies_Equation4612 (G: Type _) [Magma G] (h: Equation3404 G) : Equation4612 G := fun x y z =>
  let v0 := M y z
  let v1 := M x x
  have h2 := S (h y z v1)
  have h3 := R z
  let v4 := M v1 y
  have h5 := h v4 v1 z
  have h6 := S (h v4 v1 y)
  have h7 := h y y v1
  have h8 := R y
  have h9 := h x x x
  have h10 := R x
  have h11 := C h8 (T (T h9 (C h10 (T (T (T (C h10 h9) (S (h v1 x x))) (h v1 x y)) (C h8 (S (h x y x)))))) (S (h y y x)))
  have h12 := h x x z
  have h13 := S h12
  let v14 := M x (M z x)
  have h15 := R v0
  have h16 := h z x v0
  let v17 := M v0 z
  have h18 := h v17 v0 x
  have h19 := h y z z
  have h20 := S h19
  have h21 := R v17
  let v22 := M z (M z y)
  have h23 := h v22 v17 z
  have h24 := C h15 (T (T h23 (C h3 (T (T (C h21 h20) h18) (C h10 (S h16))))) h13)
  have h25 := h z v22 v0
  T (T (T (T (T (h v1 y y) (C h8 (T (T (C h8 h11) (S (h y y y))) h7))) h6) h5) (C h3 (T (T (T (T (T h2 h19) h25) h24) (h v0 v1 z)) (C h3 (T (T (T (T (T (T (C (R v1) (T (T (C h3 (h y z v4)) (S (h (M v4 y) v4 z))) (C (T (T (T (h v4 y y) (C h8 (T (T (T (C h8 (T (C h8 (T (h v1 y v0) (C h15 (T (T (h y (M v0 v1) v17) (C h21 (C (T (T (C h15 (T (T h12 (C h3 (T (T (C h10 h16) (S h18)) (C h21 h19)))) (S h23))) (S h25)) h20) (R (M v17 y))))) (S (h y v0 v17)))))) (S (h v0 v0 y)))) (S (h z v0 y))) (C h3 (T (T (T h19 h25) h24) (C h15 h12)))) (S (h v14 v0 z))))) (S (h z v14 y))) h13) (R v4)))) (S (h y v1 v1))) h11) (C h8 h7)) h6) h5) (C h3 h2)))))) (S (h v0 z z))

@[equational_result]
theorem Equation684_implies_Equation4458 (G: Type _) [Magma G] (h: Equation684 G) : Equation4458 G := fun x y z =>
  let v0 := M z y
  let v1 := M v0 (M (M v0 y) y)
  have h2 := h v0 v0 y
  have h3 := R z
  let v4 := M y x
  let v5 := M v4 x
  let v6 := M y v5
  have h7 := h y y x
  have h8 := R v0
  have h9 := R y
  let v10 := M x (M (M x x) x)
  have h11 := h y x v10
  have h12 := S h11
  have h13 := R v10
  have h14 := h x x x
  have h15 := R x
  have h16 := C h15 (C h9 (T h14 (C h14 h13)))
  let v17 := M x v4
  have h18 := h v17 v4 v17
  have h19 := h v17 v17 x
  have h20 := S h19
  let v21 := M v17 (M (M v17 x) x)
  have h22 := R v21
  let v23 := M v4 v17
  have h24 := R v23
  have h25 := R v17
  have h26 := h v23 v17 v21
  have h27 := h v4 v4 x
  have h28 := S h27
  let v29 := M v4 (M v5 x)
  have h30 := R v29
  have h31 := R v4
  have h32 := h x v4 v29
  have h33 := T h19 (C h19 h22)
  have h34 := S h14
  let v35 := M v0 v17
  T (h v17 v0 v17) (C h8 (T (T (T (T (T (C h25 (C (R v35) h33)) (S (h v35 v17 v21))) (C h8 (T h18 (C (C (T h11 (C h15 (C h9 (T (C h34 h13) h34)))) h15) (T (T (T (C h25 (C h24 h33)) (S h26)) (C h31 (C h15 (T h27 (C h27 h30))))) (S h32)))))) (C h8 (C (C (T h16 h12) h15) h15))) (C h8 (T (T (T (T (T (T (C h31 (T (T (T h32 (C h31 (C h15 (T (C h28 h30) h28)))) h26) (C h25 (C h24 (T (C h20 h22) h20))))) (S h18)) h16) h12) (h y z y)) (C h3 (T (C h9 (C h8 (T h7 (C h7 (R v6))))) (S (h v0 y v6))))) (C h3 (T h2 (C h2 (R v1))))))) (S (h z v0 v1))))

