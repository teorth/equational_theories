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
theorem Equation3385_implies_Equation4369 (G: Type _) [Magma G] (h: Equation3385 G) : Equation4369 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  have h2 := R v1
  let v3 := M y z
  have h4 := h y x v3
  have h5 := S h4
  have h6 := h x v3 v0
  have h7 := h v3 y x
  let v8 := M x v3
  have h9 := h v3 y v8
  have h10 := S h9
  have h11 := R v8
  have h12 := C h11 h4
  have h13 := R v0
  have h14 := C h11 h5
  have h15 := R y
  have h16 := R v3
  have h17 := h v3 v8 v0
  have h18 := S h17
  have h19 := h v3 y z
  have h20 := h z v3 v3
  have h21 := C h13 (T h20 (C h16 (T (T (S h19) h9) h14)))
  have h22 := h v3 x v3
  have h23 := S h22
  have h24 := C h16 (T h21 h18)
  have h25 := h v0 z v3
  have h26 := R z
  T (T (T (T h6 (h v0 (M x (M v3 v0)) v1)) (C h2 (C h13 (C (T (T (S h7) h19) (C h26 (T (h v3 v3 v0) (C h13 (T (T (C h16 (T (T (h v3 v0 v8) (C h11 (T (T (S (h v0 x v3)) (h v0 x v0)) (C h13 (T (T (C h13 (T (C (R x) (T (T (T (T (h y x z) (h z (M y (M x z)) v1)) (C h2 (C h26 (T (C (T (T (T (T (C h15 (T (h x z v0) (C h13 (S (h z y x))))) (S (h v0 z y))) h25) h24) h23) h2) (C (T (T h22 (C h16 (T h17 (C h13 (T (C h16 (T (T h12 h10) h19)) (S h20)))))) (S h25)) h2))))) (S (h z (M v0 z) v1))) (C h26 (T (T h25 h24) h23)))) (S (h z v3 x)))) h21) h18))))) (S (h v0 v3 v8)))) (C h16 (T (h v0 v3 y) (C h15 (T (T (C h13 (T h9 h14)) (C h13 (T (T h12 h10) h7))) (S h6)))))) h5))))) h2)))) (S (h v0 (M z (M v0 v0)) v1))) (S (h z v0 v0))

@[equational_result]
theorem Equation2789_implies_Equation962 (G: Type _) [Magma G] (h: Equation2789 G) : Equation962 G := fun x y z =>
  let v0 := M x z
  let v1 := M z y
  let v2 := M v1 v0
  have h3 := R v2
  have h4 := R v1
  have h5 := S (h z x v1)
  let v6 := M x v1
  have h7 := h z x x
  have h8 := S h7
  have h9 := h x v0 v2
  have h10 := R (M v0 x)
  have h11 := h v0 v1 v0
  have h12 := h v0 v1 v1
  have h13 := h v1 x v2
  have h14 := S h13
  have h15 := h v2 (M (M x v2) v6) v2
  have h16 := R (M v2 v2)
  have h17 := h v1 v2 v2
  have h18 := R x
  have h19 := h v0 (M (M x v0) (M x x)) v0
  have h20 := R v0
  have h21 := h x x v0
  have h22 := T (C (C h21 h21) h20) (S h19)
  have h23 := S h21
  have h24 := T h19 (C (C h23 h23) h20)
  have h25 := T (C h24 (T (C (T (C h4 (T h7 (C h22 h18))) (C (T h17 (C (T (C h16 (T (C (T h15 (C (C h14 h14) h3)) h4) (S h12))) (S h11)) h3)) h10)) h3) (S h9))) h8
  have h26 := T (C (T h11 (C h16 (T h12 (C (T (C (C h13 h13) h3) (S h15)) h4)))) h3) (S h17)
  have h27 := h (M (M v1 z) v2) v0 v0
  have h28 := C (T (C h26 h10) (C h4 (T (C h24 h18) h8))) h3
  have h29 := R (M v0 v0)
  have h30 := h z x z
  T (T (T (T (T h9 h28) h27) (C (T (C h29 h25) (S h30)) h20)) (h (M z v0) v0 v2)) (C (T (T (T (C (R (M v0 v2)) (C h20 (T (C (T h30 (C h29 (T h7 (C h22 (T h9 h28))))) h20) (S h27)))) (C h26 h25)) (C (T (h v1 (M v6 v0) v1) (C (C h5 h5) h4)) (R z))) (S (h y z z))) h3)

@[equational_result]
theorem Equation3182_implies_Equation2779 (G: Type _) [Magma G] (h: Equation3182 G) : Equation2779 G := fun x y z =>
  let v0 := M x z
  let v1 := M y z
  let v2 := M (M v1 v0) y
  have h3 := R v2
  have h4 := R z
  have h5 := h z x z
  have h6 := R x
  have h7 := h v0 v2 v1
  have h8 := S h7
  have h9 := R v1
  have h10 := h y v1 v0
  have h11 := h y v2 z
  have h12 := R y
  have h13 := h v0 y z
  have h14 := h v1 y v2
  have h15 := C (C (T (T (C (T h14 (C (T (C (T (C (C h10 h3) h9) h8) h12) (C h13 h12)) h3)) h4) (S h11)) h10) h3) h9
  have h16 := h v2 v1 z
  have h17 := T h16 (C (T h15 h8) h4)
  have h18 := S h10
  have h19 := S h13
  have h20 := C (T h7 (C (C (T (T h18 h11) (C (T (C (T (C h19 h12) (C (T h7 (C (C h18 h3) h9)) h12)) h3) (S h14)) h4)) h3) h9)) h4
  have h21 := T h20 (S h16)
  have h22 := C (C h21 h6) h4
  have h23 := h v0 z v0
  have h24 := R v0
  have h25 := h z v0 z
  have h26 := C (C (T (C (C (T h13 (C h17 h4)) h24) h4) (S h25)) h24) h24
  have h27 := h z v0 v0
  have h28 := S h27
  have h29 := C (C (T h25 (C (C (T (C h21 h4) h19) h24) h4)) h24) h24
  T (T (h x z v2) (C (T (C (T (T (T (C (C (T h5 h22) h3) h6) (S (h z v2 x))) h27) h26) h4) (C (T (T (T h29 h28) (h z v2 v2)) (C (T (C (T (T (T (C (T (C h17 h3) (C (T (T h20 (C (T (T (T h15 h8) h23) (C (C (T h29 h28) h4) h24)) h4)) (C (T (T (C (C (T h27 h26) h4) h24) (S h23)) h13) h4)) h3)) h4) (S (h z v2 z))) h5) h22) h3) (C (T (C (C h17 h6) h4) (S h5)) h3)) h3)) h4)) h3)) (S (h v2 z v2))

@[equational_result]
theorem Equation492_implies_Equation2199 (G: Type _) [Magma G] (h: Equation492 G) : Equation2199 G := fun x y z =>
  let v0 := M y x
  let v1 := M y z
  let v2 := M v1 z
  let v3 := M v2 v0
  have h4 := h x x v2
  have h5 := h x v0 y
  have h6 := h y x y
  have h7 := h y z v1
  have h8 := S h7
  have h9 := h z v1 y
  have h10 := S h9
  have h11 := h y z y
  have h12 := R v1
  have h13 := R y
  have h14 := h v1 y v1
  have h15 := h v1 z v2
  have h16 := h z v2 v1
  have h17 := h v1 z v1
  have h18 := R v2
  have h19 := h v2 v1 v2
  have h20 := R z
  have h21 := C h20 (T (T (T (C h20 (T h19 (C h12 (C h18 (C h18 (T (C h18 h17) (S h16))))))) (S h15)) h14) (C h13 (C h12 (C h12 (T (C h12 h11) h10)))))
  have h22 := R v0
  have h23 := h v0 v2 z
  have h24 := R x
  have h25 := R v3
  have h26 := S h17
  have h27 := S h14
  have h28 := C h13 (C h12 (C h12 (T h9 (C h12 (S h11)))))
  have h29 := C h20 (T (T (T h28 h27) h15) (C h20 (T (C h12 (C h18 (C h18 (T h16 (C h18 h26))))) (S h19))))
  have h30 := C h12 (T (T h21 h8) h11)
  have h31 := h v1 v2 z
  T (h x v2 z) (C h18 (T (C h24 (T (T (T h21 h8) (h y v0 v3)) (C h22 (T (T (T (C (T (T h7 (C h20 (T (T (T h28 h27) h31) (C h18 (T (T (T h30 h10) h16) (C h18 (T (T h26 h31) (C h18 (T h30 h10))))))))) (S (h v2 z v2))) (C h25 (T (T (T (C h25 (C h13 (T h4 (C h24 (C h24 (C h18 (T (C h18 (T h5 (C h22 (T (T (S h6) h7) h29)))) (S h23)))))))) (S (h y v3 x))) h7) h29))) (S (h v3 v2 z))) (h v3 v3 x)) (C h25 (C h25 (T (C h24 (C h24 (C h18 (T h23 (C h18 (T (C h22 (T (T h21 h8) h6)) (S h5))))))) (S h4)))))))) (S (h v0 x v3))))

@[equational_result]
theorem Equation3211_implies_Equation2271 (G: Type _) [Magma G] (h: Equation3211 G) : Equation2271 G := fun x y z =>
  let v0 := M y z
  let v1 := M y v0
  let v2 := M x v1
  let v3 := M v2 z
  have h4 := R v3
  have h5 := R v1
  have h6 := R x
  have h7 := h v2 v3 z
  have h8 := h z v2 z
  have h9 := h z y v0
  have h10 := S h9
  have h11 := R y
  have h12 := R z
  have h13 := R v0
  have h14 := h y v0 z
  have h15 := S h14
  have h16 := h z y z
  have h17 := C h16 h13
  have h18 := h v0 z v0
  have h19 := h v0 y v1
  have h20 := h y v1 v0
  have h21 := S h20
  have h22 := h v0 y v0
  have h23 := h v1 v0 v1
  have h24 := C (T (T (T (C (T h23 (C (C (C (T (C h22 h5) h21) h5) h5) h13)) h11) (S h19)) h18) (C (C (C (T h17 h15) h13) h13) h12)) h11
  have h25 := C (T (C (C (T (h v3 v1 y) (C (T (C (T (T h24 h10) h8) h4) (S h7)) h5)) h6) h6) (S (h x x v1))) h5
  have h26 := h v0 v1 y
  have h27 := S h18
  have h28 := C (S h16) h13
  have h29 := C (C (C (T h14 h28) h13) h13) h12
  T (T (h x v2 v1) (C (T (T (S (h v1 x v1)) (h v1 v3 x)) (C (T (T h25 h7) (C (T (T (S h8) (h z v3 x)) (C (T (C (R (M (M v3 x) x)) (T (T h9 (C (T (T (T h29 h27) h26) (C (T (T (T (T (C (T h24 h10) h13) h17) h15) (h y y v1)) (C (C (T (C (T (T (C (T (T h14 h28) (C (T h9 (C (T (T (T h29 h27) h19) (C (T (C (C (C (T h20 (C (S h22) h5)) h5) h5) h13) (S h23)) h11)) h11)) h13)) h5) (S h26)) h22) h5) h21) h11) h11)) h5)) h11)) (S (h v1 y y)))) h25) h4)) h4)) h4)) (R v2))) (S (h v3 v2 v3))

@[equational_result]
theorem Equation1320_implies_Equation711 (G: Type _) [Magma G] (h: Equation1320 G) : Equation711 G := fun x y z =>
  let v0 := M (M x z) z
  let v1 := M y v0
  let v2 := M y v1
  have h3 := h v2 v2 x
  let v4 := M v2 v2
  have h5 := R x
  have h6 := h v2 v2 z
  have h7 := R v2
  let v8 := M (M v4 z) z
  have h9 := R v0
  have h10 := h (M (M v1 x) x) y y
  have h11 := R y
  have h12 := h v0 y x
  have h13 := h (M (M v0 y) y) x x
  have h14 := h v0 x v2
  have h15 := S h14
  let v16 := M (M (M x v0) v2) v2
  have h17 := h v16 x y
  have h18 := h v16 x v1
  have h19 := R v1
  have h20 := h (M (M v0 v1) v1) x x
  have h21 := R z
  have h22 := h x y x
  let v23 := M (M (M y x) x) x
  have h24 := h x v2 x
  T (T h24 (C h7 (T (T (T (T (T (T (h (M (M (M v2 x) x) x) v2 y) (C h7 (T (T (C (C (S h24) h11) h11) (h (M (M x y) y) y x)) (C h11 (T (T (C (C (T (T (T (C h11 (C (C h22 h11) h11)) (S (h v23 y y))) (h v23 y z)) (C h11 (C (C (S h22) h21) h21))) h5) h5) h10) (C h11 (T (T (T (C (C (S h12) h11) h11) h13) (C h5 (C (C (T (T (T (C h5 (C (C h14 h11) h11)) (S h17)) h18) (C h5 (C (C h15 h19) h19))) h5) h5))) (S h20)))))))) (C h7 (T (T (C h11 (T (T (C h11 (T (T (T h20 (C h5 (C (C (T (T (T (C h5 (C (C h14 h19) h19)) (S h18)) h17) (C h5 (C (C h15 h11) h11))) h5) h5))) (S h13)) (C (C h12 h11) h11))) (S h10)) (C (C (h v1 y v0) h5) h5))) (S (h (M (M v2 v0) v0) y x))) (C (C h6 h9) h9)))) (S (h v8 v2 v0))) (h v8 v2 x)) (C h7 (T (C (C (S h6) h5) h5) (C (C h3 h5) h5)))) (S (h (M (M v4 x) x) v2 x))))) (S h3)

@[equational_result]
theorem Equation2370_implies_Equation2928 (G: Type _) [Magma G] (h: Equation2370 G) : Equation2928 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M v1 z
  let v3 := M v2 y
  have h4 := h y v3 v1
  have h5 := S h4
  have h6 := R v1
  have h7 := h (M v3 (M v1 (M y v3))) v1 x
  have h8 := R x
  have h9 := h y v2 v1
  have h10 := S h9
  let v11 := M y v2
  let v12 := M v2 (M v1 v11)
  have h13 := h v12 v1 x
  have h14 := h v12 v1 y
  have h15 := R y
  have h16 := R v2
  have h17 := h y v2 x
  have h18 := h y v1 x
  have h19 := S h18
  let v20 := M v1 (M x (M y v1))
  have h21 := h v20 x x
  have h22 := h v20 x v3
  have h23 := R v3
  let v24 := M z (M v0 v2)
  have h25 := h x y x
  T (T (T (T h25 (C (T (T (T (h (M y (M x (M x y))) x x) (C (T (C h8 (C h8 (S h25))) (C h8 (C h8 (h x z x)))) h8)) (S (h (M z (M x v0)) x x))) (C (R z) (C h8 (h v0 v2 z)))) h8)) (S (h (M v2 v24) z x))) (C h16 (T (T (T (T (T (h v24 v0 x) (C (T (T (T (T (T (C (R v0) (C h8 (S (h v1 z v0)))) (h (M v0 (M x v1)) x x)) (C (T (C h8 (C h8 (S (h y v0 x)))) (C h8 (C h8 h18))) h8)) (S h21)) h22) (C (C h8 (C h23 h19)) h23)) h8)) (C (T (T (T (T (C (C h8 (C h23 h18)) h23) (S h22)) h21) (C (T (C h8 (C h8 h19)) (C h8 (C h8 h17))) h8)) (S (h (M v2 (M x v11)) x x))) h8)) (S h17)) h4) (C (T (T (T (T h7 (C (T (C h6 (C h8 h5)) (C h6 (C h8 h9))) h8)) (S h13)) h14) (C (C h6 (C h15 h10)) h15)) h6)))) (C h16 (T (C (T (T (T (T (C (C h6 (C h15 h9)) h15) (S h14)) h13) (C (T (C h6 (C h8 h10)) (C h6 (C h8 h4))) h8)) (S h7)) h6) h5))

@[equational_result]
theorem Equation3131_implies_Equation4013 (G: Type _) [Magma G] (h: Equation3131 G) : Equation4013 G := fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M v1 x
  have h3 := R y
  have h4 := R v2
  have h5 := h y z z
  have h6 := S h5
  have h7 := R z
  have h8 := h z y v1
  have h9 := R v1
  have h10 := h v0 z z
  have h11 := h z v1 z
  have h12 := C (C (T (C (C (T h11 (C (S h10) h9)) h9) h3) (S h8)) h3) h7
  have h13 := h v1 z y
  have h14 := h v1 v2 v1
  have h15 := S h14
  have h16 := h x v1 v1
  have h17 := h x y y
  have h18 := S h17
  have h19 := R x
  have h20 := C (C (T h13 h12) h7) h7
  have h21 := C (C (T (C h16 h4) h15) h7) h7
  have h22 := h v2 x z
  have h23 := C (C (C (T h22 (C (T (T h21 h20) h6) h19)) h3) h3) h3
  have h24 := h y v2 y
  have h25 := S h24
  have h26 := S h16
  have h27 := S h13
  have h28 := C (C (T h8 (C (C (T (C h10 h9) (S h11)) h9) h3)) h3) h7
  have h29 := C (T (T h26 h17) (C (C (C (T (C (T (T h5 (C (C (T h28 h27) h7) h7)) (C (C (T h14 (C h26 h4)) h7) h7)) h19) (S h22)) h3) h3) h3)) h4
  have h30 := C (C (T (T (T (T h28 h27) h14) h29) h25) h7) h7
  have h31 := R v0
  have h32 := C (T (C (C (T h22 (C (T (T h21 h20) h30) h19)) h19) h31) (S (h z v0 x))) h31
  have h33 := h x v2 v0
  T (C (T h33 (C (T (T (T (T h32 h14) h29) (C (T (T (T h23 h18) h33) (C (T (T (T (T (T h32 h14) h29) h25) h5) h30) h4)) h4)) (C (C (T (C (C (T (T (T (T h24 (C (T (T h23 h18) h16) h4)) h15) h13) h12) h7) h7) h6) h4) h4)) h4)) h3) (S (h v2 y v2))

@[equational_result]
theorem Equation3147_implies_Equation1726 (G: Type _) [Magma G] (h: Equation3147 G) : Equation1726 G := fun x y z =>
  let v0 := M x z
  let v1 := M v0 z
  have h2 := R v1
  let v3 := M y y
  have h4 := h v3 y v1
  have h5 := S h4
  have h6 := C h5 h2
  have h7 := h v1 v3 v1
  have h8 := R z
  have h9 := h x v3 x
  have h10 := R x
  have h11 := h v3 y x
  have h12 := R v3
  let v13 := M v3 v1
  have h14 := h v3 v13 v0
  have h15 := S h14
  have h16 := R v0
  have h17 := h v3 v3 v3
  have h18 := S h17
  have h19 := h v3 y v3
  have h20 := C (C (T (C h19 h12) h18) h2) (T h7 h6)
  have h21 := C (T h4 h20) h12
  have h22 := C (S h19) h12
  have h23 := C (C (T (T h17 h22) h21) h16) h16
  have h24 := h v3 y v0
  have h25 := h v0 v3 v0
  have h26 := C (T h25 (C (S h24) h16)) h16
  have h27 := C (R (M (M v3 v3) v1)) (T (C h4 h2) (S h7))
  have h28 := C (C (T h17 h22) h2) (R v13)
  have h29 := C (T (T (C (T (T h28 h27) h5) h16) (C h24 h16)) (S h25)) h16
  have h30 := C (C (T (T (T (C (T (T (T h28 h27) h5) h19) h12) h18) h4) h20) h16) h16
  T (T (T (h x x z) (C (C (T (C (T (T (C (T (T (T (T h9 (C (T (T (S h11) h17) h22) h10)) (C h21 h10)) (C (C (T (T (T (T (T h28 h27) h5) h14) h30) h29) h12) h10)) (C (C (T (T (T (T (T h26 h23) h15) (h v3 v0 z)) (C (C (T (T (T (T (C (T (T (T h26 h23) h15) h19) h12) h18) h14) h30) h29) h8) h8)) (C (T (C (T (T (T h26 h23) h15) (h v3 y z)) h8) (S (h z v3 z))) h8)) h12) h10)) h10) (S (h v3 z x))) h11) h10) (S h9)) h8) h8)) h7) h6

@[equational_result]
theorem Equation928_implies_Equation2552 (G: Type _) [Magma G] (h: Equation928 G) : Equation2552 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 x
  let v2 := M y v1
  let v3 := M v2 z
  have h4 := h z v3 v1
  have h5 := R v3
  let v6 := M z z
  have h7 := S (h z v3 x)
  let v8 := M z x
  have h9 := T (h v3 v3 (M (M v3 x) v8)) (C h5 (C h7 h7))
  let v10 := M v3 v3
  have h11 := R v2
  have h12 := T (C h11 h9) (S (h z v2 z))
  have h13 := R v0
  have h14 := h z v0 x
  have h15 := R y
  have h16 := T (h z y z) (C h15 (T (C h13 (C h14 h14)) (S (h v0 v0 (M v1 v8)))))
  let v17 := M v0 v0
  let v18 := M x x
  have h19 := S (h x v1 x)
  let v20 := M v0 v3
  let v21 := M v2 v3
  let v22 := M v2 x
  have h23 := R (M v22 v18)
  T (T (T (T (T (h x v2 x) (C h11 h23)) (C h11 (T h23 (C (T (T (T (h v22 y v1) (C h15 (S (h v0 v2 x)))) (C h15 (T (h v0 v2 v3) (C (h v2 y z) (R (M v21 v20)))))) (S (h v21 y v20))) (T (T (T (T (T (T (T (T (h v18 v0 v1) (C h13 (T (C (T (C h13 (T (h v1 v1 (M (M v1 x) v18)) (C (R v1) (C h19 h19)))) (S (h x v0 x))) (R (M v18 v1))) (S (h v0 x x))))) (h v17 y z)) (C h15 (T (C h13 (C (R v17) h16)) (S (h y v0 v0))))) (C h15 (T (h y z z) (C h16 (C (T (h v6 v2 v3) (C h11 (T (C h12 (R (M v6 v3))) (S (h v2 z z))))) h13))))) (S (h (M v2 v2) y v0))) (C h11 (T (h v2 v3 v3) (C h5 (C (R v10) h12))))) (S (h v10 v2 z))) (C h9 h5)))))) (S (h (M v3 v6) v2 v3))) (C h5 (C h4 h4))) (S (h v3 v3 (M (M v3 v1) (M z v1))))

@[equational_result]
theorem Equation2170_implies_Equation16 (G: Type _) [Magma G] (h: Equation2170 G) : Equation16 G := fun x y =>
  let v0 := M y x
  let v1 := M y v0
  have h2 := h v1 y x
  have h3 := S h2
  let v4 := M x y
  have h5 := h v4 v0 y
  have h6 := S h5
  have h7 := R v1
  have h8 := h y y x
  have h9 := C h8 h7
  let v10 := M v0 v1
  have h11 := h v10 y x
  have h12 := S h11
  have h13 := R v4
  have h14 := R v10
  have h15 := h v0 y v0
  let v16 := M v0 y
  have h17 := h v16 v1 v0
  have h18 := C (T h17 (C (S h15) h14)) h13
  have h19 := h y y v0
  have h20 := S h19
  have h21 := C (T (T (T h20 h8) h18) h12) (T h9 h6)
  have h22 := h v16 v1 y
  have h23 := S h17
  have h24 := R x
  have h25 := S h8
  have h26 := C (T (C h15 h14) h23) h13
  have h27 := T (T h11 h26) h25
  have h28 := R v16
  let v29 := M v1 y
  have h30 := R v0
  let v31 := M v10 v0
  have h32 := C (T (T h22 h21) h3) h30
  let v33 := M v16 v0
  have h34 := T (T h2 (C (T (T (T h11 h26) h25) h19) (T h5 (C h25 h7)))) (S h22)
  have h35 := R v33
  T (T (T (T (T (h x v1 v0) (C (T (T (C (T (T (T (T (T (T (C h34 h30) (h v33 y v0)) (C (T (T (T (T (T (T (C h34 h35) (C (T (T (T h22 h21) h3) (C (T (T h8 h18) h12) h30)) h32)) (S (h v0 v0 v1))) (h v0 v0 y)) (C h35 h34)) (C (T (h v33 y v1) (C (T (T (C (T (T (T h9 h6) (h v4 v0 v10)) (C h12 (R v31))) h32) (S (h v31 v0 v1))) (C h27 h30)) (R v29))) h28)) (S (h v29 y v0))) h28)) h20) h8) h18) h12) h24) (C h27 h24)) h15) h14)) h23) h22) h21) h3

@[equational_result]
theorem Equation3385_implies_Equation4450 (G: Type _) [Magma G] (h: Equation3385 G) : Equation4450 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  have h2 := R z
  have h3 := h z v1 v1
  have h4 := S h3
  have h5 := R v1
  have h6 := h v0 z y
  have h7 := h y (M v0 (M z y)) v1
  have h8 := h z y z
  have h9 := R v0
  have h10 := h z z v0
  have h11 := R y
  let v12 := M z z
  have h13 := h y v12 v1
  have h14 := C h5 (C h2 (C (T (T (T h13 (C h5 (C h11 (C (T h10 (C h9 (S h8))) h5)))) (S h7)) (S h6)) h5))
  have h15 := h z (M y v12) v1
  have h16 := h y z z
  have h17 := h y z x
  have h18 := h x (M y (M z x)) v1
  have h19 := h z x v1
  have h20 := h x v0 z
  have h21 := T (T (T h3 (C h5 (C h2 (C (T (T (T h6 h7) (C h5 (C h11 (C (T (C h9 h8) (S h10)) h5)))) (S h13)) h5)))) (S h15)) (S h16)
  have h22 := R x
  have h23 := h x z v1
  let v24 := M y x
  have h25 := h x z v24
  have h26 := h z y x
  have h27 := R v24
  have h28 := h v24 z y
  let v29 := M v24 z
  have h30 := h x v29 v1
  have h31 := T (T (T (T (T (T (T h30 (C h5 (C h22 (C (T h28 (C h11 (T (T (T (T (C h27 h26) (S h25)) h23) (C h5 (T (C h22 h21) h20))) (S h19)))) h5)))) (S h18)) (S h17)) h16) h15) h14) h4
  T (T (T (h x v24 z) (h z (M x v29) v1)) (C h5 (T (C h2 (T (C h31 h5) (C h21 (T (C (T (T (T h17 h18) (C h5 (C h22 (C (T (C h11 (T (T (T (T h19 (C h5 (T (S h20) (C h22 (T (T (T h16 h15) h14) h4))))) (S h23)) h25) (C h27 (S h26)))) (S h28)) h5)))) (S h30)) h2) (C h31 h2))))) (S (h v0 (M z v1) z))))) (S (h v0 z v1))

@[equational_result]
theorem Equation3404_implies_Equation4673 (G: Type _) [Magma G] (h: Equation3404 G) : Equation4673 G := fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M x z
  have h3 := h x z x
  have h4 := R x
  have h5 := h v1 v0 v2
  have h6 := S h5
  have h7 := h z v2 v0
  have h8 := R v2
  have h9 := C h8 h7
  have h10 := R z
  have h11 := R y
  have h12 := C h11 (S (h x y x))
  let v13 := M x x
  have h14 := h v13 x y
  have h15 := S (h v13 x z)
  have h16 := C h10 h3
  have h17 := h z v2 x
  have h18 := S h17
  have h19 := h v2 x v2
  have h20 := h x y v2
  have h21 := R v0
  let v22 := M v2 x
  have h23 := h v22 v2 y
  have h24 := S h19
  have h25 := C h8 h17
  have h26 := C h8 (S h7)
  have h27 := R v1
  let v28 := M v0 x
  T (T (h v0 z v1) (C h27 (T (T (T (T (C h10 (T (T (T h5 h26) h25) h24)) (h z v22 x)) (C h4 (T (T (T h23 (C h11 (S h20))) (C h11 (h x y v0))) (S (h v28 v0 y))))) (S (h y v28 x))) (C h11 (T (h v0 x v1) (C h27 (T (C h4 (T (T (T (T (T h5 h26) h25) h24) (h v2 x z)) (C h10 (T (T (T (T (T (T (T (T (C h4 (T (T (T (T (T (T h16 h15) h14) h12) (C h11 h20)) (S h23)) (C (T (T (T h19 (C h8 h18)) h9) h6) h8))) (S (h z (M v1 v0) x))) (C h10 (T (h v1 v0 v0) (C h21 (S (h z v0 v0)))))) (S (h v0 v0 z))) (C h21 (T h20 (C h8 (T (C h11 (T h19 (C h8 (T (T (T (T h18 h16) h15) h14) h12)))) (S (h v0 v2 y))))))) (S (h v2 v2 v0))) (h v2 v2 z)) (C h10 (T (T (T h9 h6) (h v1 v0 x)) (C h4 (S (h z x v0)))))) (S (h x x z)))))) (S h3)))))))) (S (h v2 y v1))

@[equational_result]
theorem Equation4176_implies_Equation3740 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3740 G := fun x y z =>
  let v0 := M x z
  let v1 := M z y
  have h2 := R v0
  have h3 := S (h z y v0)
  let v4 := M y v0
  let v5 := M v4 z
  have h6 := R z
  have h7 := S (h y v0 v0)
  have h8 := R y
  have h9 := S (h x z z)
  have h10 := R x
  have h11 := S (h z z y)
  let v12 := M y v1
  have h13 := C (T (h v1 v12 z) (C (S (h z y v1)) h6)) h8
  have h14 := h v12 z y
  have h15 := C (T (h z v0 x) (C (T (T (T (C (T (C (h x z y) h10) (S (h y v1 x))) h6) h14) h13) h11) h10)) h6
  have h16 := R v1
  have h17 := h v1 z y
  have h18 := C (T h17 (C (T (T (T (T (T (T (h v1 v1 z) (C (T (C h17 h16) (S (h y v1 v1))) h6)) h14) h13) h11) (h z z v0)) (C (T h15 h9) h2)) h8)) h2
  have h19 := T (h v0 v1 z) (C (T h18 h7) h6)
  let v20 := M v0 v1
  have h21 := R v20
  have h22 := S (h z v0 v1)
  have h23 := C h3 h6
  T (T (h x y v0) (C (T (T (T (T (T (T (T (T (T (h v4 x z) (C (T (h v0 v4 z) h23) h6)) (C (T h17 (C (T (T (T (h v1 v1 x) (C (T (T (C (h v1 x z) h16) (R (M (M v20 z) v1))) h22) h10)) (C (T (h z v0 z) (C (S (h z x z)) h6)) h10)) (S (h z z x))) h8)) h6)) (S (h y z z))) (h y z v20)) (C (T (T (C (T (T (T (T (C h6 h19) (h z v5 v0)) (C h23 h2)) h18) h7) h8) (C (h y v0 v1) h8)) (S (h v1 v20 y))) h21)) (C (T (T (T (h v1 v20 z) (C h22 h6)) h15) h9) h21)) (C h2 h19)) (h v0 v5 v0)) (C (C h3 h2) h2)) h2)) (S (h v0 v1 v0))

@[equational_result]
theorem Equation914_implies_Equation1053 (G: Type _) [Magma G] (h: Equation914 G) : Equation1053 G := fun x y z =>
  let v0 := M y z
  let v1 := M y v0
  let v2 := M v1 z
  let v3 := M x v2
  have h4 := h v3 v2 v3
  let v5 := M v3 v3
  let v6 := M y y
  let v7 := M x x
  have h8 := R v7
  have h9 := h v0 x x
  have h10 := S h9
  have h11 := R x
  let v12 := M (M x v0) v7
  have h13 := h v12 x v1
  let v14 := M v1 v1
  have h15 := R v14
  let v16 := M v0 v14
  have h17 := h v16 x x
  have h18 := h v16 y x
  have h19 := h z y v1
  have h20 := h z y v3
  have h21 := R y
  have h22 := h (M v0 v5) y x
  have h23 := R v0
  let v24 := M v0 v0
  let v25 := M v2 v2
  have h26 := h x v2 z
  have h27 := R v2
  T (T h26 (C h27 (T (T (h (M (M v2 x) (M z z)) v2 v2) (C h27 (T (T (C (S h26) (T (T (T (h v25 v1 x) (C (R v1) (T (C (T (T (h (M v1 v25) y x) (C h21 (C (S (h v0 y v2)) h8))) (S (h z y x))) h8) (C (h z v1 v2) h8)))) (S (h (M v2 v25) v1 x))) (C (h v2 x v0) (R v25)))) (S (h (M v3 v24) x v2))) (C h4 (T (T (T (h v24 v0 x) (C h23 (C (T (T (T (T (T (h (M v0 v24) x x) (C h11 (C (T (T (T (C h11 (C h9 (R v24))) (S (h v12 x v0))) h13) (C h11 (C h10 h15))) h8))) (S h17)) h18) (C h21 (C (T (S h19) h20) h8))) (S h22)) h8))) (C h23 (C (T (T (T (T (T h22 (C h21 (C (T (S h20) h19) h8))) (S h18)) h17) (C h11 (C (T (T (T (C h11 (C h9 h15)) (S h13)) (h v12 x y)) (C h11 (C h10 (R v6)))) h8))) (S (h (M v0 v6) x x))) h8))) (S (h v6 v0 x))))))) (S (h (M (M v2 v3) v5) v2 y))))) (S h4)

@[equational_result]
theorem Equation2399_implies_Equation2199 (G: Type _) [Magma G] (h: Equation2399 G) : Equation2199 G := fun x y z =>
  let v0 := M y x
  let v1 := M y z
  let v2 := M v1 z
  let v3 := M v2 v0
  let v4 := M y (M x (M x y))
  let v5 := M y (M y v1)
  have h6 := h y v5 v4
  have h7 := S h6
  have h8 := R v5
  have h9 := h y y x
  have h10 := R v4
  have h11 := h z y y
  have h12 := C (T h11 (C h8 (T h9 (C h10 h9)))) h8
  have h13 := h (M z v5) v3 v1
  have h14 := R v3
  have h15 := S h9
  have h16 := T h6 (C (T (C h8 (T (C h10 h15) h15)) (S h11)) h8)
  have h17 := R v1
  have h18 := R y
  have h19 := h z z x
  have h20 := S h19
  let v21 := M z (M x (M x z))
  have h22 := R v21
  have h23 := h z y v21
  have h24 := R v2
  have h25 := h v0 v0 x
  have h26 := S h25
  let v27 := M v0 (M x (M x v0))
  have h28 := R v27
  have h29 := h v0 v2 v27
  have h30 := R v0
  have h31 := C h30 (T h13 (C (T (T (C h14 (C h17 (T (T (C h17 (T h12 h7)) (C (C h18 (T h19 (C h22 h19))) h18)) (S h23)))) (C (C h24 (T h25 (C h28 h25))) h24)) (S h29)) h14))
  have h32 := C h30 h16
  have h33 := S (h x x x)
  let v34 := M x (M x (M x x))
  have h35 := C (C h18 (T (C (R v34) h33) h33)) h18
  have h36 := h x y v34
  T (T (T (T (T h36 h35) h32) h31) (C (C h18 (T (T (T h36 h35) h32) h31)) (T (T (T (C (T (T h29 (C (C h24 (T (C h28 h26) h26)) h24)) (C h14 (C h17 (T (T h23 (C (C h18 (T (C h22 h20) h20)) h18)) (C h17 h16))))) h14) (S h13)) h12) h7))) (S (h v3 y v0))

@[equational_result]
theorem Equation2917_implies_Equation2349 (G: Type _) [Magma G] (h: Equation2917 G) : Equation2349 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  let v2 := M y v1
  let v3 := M v2 z
  have h4 := h v3 v2 z
  have h5 := R z
  have h6 := R x
  let v7 := M z v3
  let v8 := M v2 (M v2 v2)
  have h9 := R y
  have h10 := h v2 v1 y
  have h11 := h (M (M v1 (M v2 v1)) y) y x
  let v12 := M v3 (M v2 v3)
  have h13 := R v1
  have h14 := h v0 z y
  let v15 := M (M z (M v0 z)) y
  let v16 := M v1 (M v0 v1)
  have h17 := h x y v0
  have h18 := R v0
  have h19 := h x v2 z
  T (T h19 (C (T (T (T (h (M (M v2 (M x v2)) z) z x) (C (T (C (C h5 (S h19)) h6) (C h18 h17)) h6)) (C (T (C h18 (S h17)) (C (T (T (T (T (T (T (T (T (T (C (T (T (T (h z x x) (C (C (C h6 (h v0 v1 x)) h6) h6)) (S (h (M v16 x) x x))) (C (T (T (T (T (h v16 y x) (C (C (C h9 (T (T (h (M v16 y) y x) (C (T (C (C h9 (S (h v0 v1 y))) h6) (C (C h9 h14) h6)) h6)) (S (h v15 y x)))) h6) h6)) (C (C (C h9 (T (h v15 y y) (C (C (C h9 (S h14)) h9) h9))) h6) h6)) (S (h (M v1 y) y x))) (C h13 (T (T (h y v1 x) (C (C (C h13 (h v2 v3 v1)) h6) h6)) (S (h (M v12 v1) v1 x))))) h6)) h6) (S (h v12 v1 x))) (h v12 y x)) (C (C (C h9 (T (T (h (M v12 y) y x) (C (C (T (C h9 (S (h v2 v3 y))) (C h9 h10)) h6) h6)) (S h11))) h6) h6)) (C (C (C h9 (T (T h11 (C (C (T (C h9 (S h10)) (C h9 (h v2 v2 y))) h6) h6)) (S (h (M v8 y) y x)))) h6) h6)) (S (h v8 y x))) (h v8 x x)) (C (C (C h6 (T (T (h (M v8 x) x x) (C (C (T (C h6 (S (h v2 v2 x))) (C h6 (h v2 z x))) h6) h6)) (S (h (M v7 x) x x)))) h6) h6)) (S (h v7 x x))) (C h5 h4)) h6)) h6)) (S (h (M (M v2 (M v3 v2)) z) z x))) h5)) (S h4)

@[equational_result]
theorem Equation3211_implies_Equation1340 (G: Type _) [Magma G] (h: Equation3211 G) : Equation1340 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M v1 x
  let v3 := M y v2
  have h4 := R y
  have h5 := h y v0 z
  have h6 := R v0
  have h7 := h z y z
  have h8 := h z v0 y
  have h9 := R z
  have h10 := h v0 y z
  have h11 := S h10
  have h12 := h v1 z v1
  have h13 := R v1
  have h14 := h z v0 z
  have h15 := h v0 v1 z
  have h16 := C (T (C (C (C (T h15 (C (S h14) h13)) h13) h13) h9) (S h12)) h6
  have h17 := h z v0 v1
  have h18 := C (T h17 h16) h4
  have h19 := h y z y
  have h20 := C (C (T (T (C (T (C (T h19 (C (C (C (T h18 h11) h4) h4) h9)) h6) (S h8)) h6) (C h7 h6)) (S h5)) h4) h4
  have h21 := h y y v0
  have h22 := S h19
  have h23 := S h17
  have h24 := C (T h12 (C (C (C (T (C h14 h13) (S h15)) h13) h13) h9)) h6
  have h25 := C (T h24 h23) h4
  have h26 := h z y y
  have h27 := h v1 v2 x
  have h28 := R v2
  have h29 := h x v1 x
  have h30 := R x
  T (T (h x y z) (C (T (h v2 v3 x) (C (T (T (T (T (T (T (C (T (C (C (C (T (T (T h19 (C (T (C (T (T (T (C (T (T h18 h11) (C (T h21 h20) h9)) h4) (S h26)) h17) h16) h4) h11) h9)) h27) (C (S h29) h28)) h28) h30) h30) (S (h x x v2))) h28) (C h29 h28)) (S h27)) (C (T h10 (C (T (T (T h24 h23) h26) (C (T (T (C (T (C (C (T (T h5 (C (S h7) h6)) (C (T h8 (C (T (C (C (C (T h10 h25) h4) h4) h9) h22) h6)) h6)) h4) h4) (S h21)) h9) h10) h25) h4)) h4)) h9)) h22) h21) h20) (R v3))) h4)) (S (h v3 y y))

@[equational_result]
theorem Equation1304_implies_Equation1561 (G: Type _) [Magma G] (h: Equation1304 G) : Equation1561 G := fun x y z =>
  let v0 := M z y
  let v1 := M x v0
  have h2 := R v1
  have h3 := R z
  let v4 := M (M (M y x) x) y
  let v5 := M (M v0 y) y
  have h6 := h y v5 v4
  have h7 := R v5
  have h8 := R v4
  have h9 := h y y x
  have h10 := h z y y
  have h11 := C (C (T (C h7 (T h10 (C (T h9 (C h9 h8)) h7))) (S h6)) h3) h2
  have h12 := S h9
  have h13 := C (T h6 (C h7 (T (C (T (C h12 h8) h12) h7) (S h10)))) h3
  let v14 := M y z
  let v15 := M (M (M v14 x) x) v14
  have h16 := S (h v14 v1 v15)
  have h17 := h v14 v14 x
  have h18 := C h2 (C (T h17 (C h17 (R v15))) h2)
  have h19 := C h2 h11
  have h20 := h v5 v1 z
  let v21 := M v14 v1
  have h22 := R v21
  have h23 := R y
  let v24 := M (M (M v0 x) x) v0
  let v25 := M (M v1 v0) v0
  have h26 := h v0 v25 v24
  have h27 := R v25
  have h28 := R v24
  have h29 := h v0 v0 x
  have h30 := h x v0 v0
  have h31 := S h29
  have h32 := R v0
  have h33 := S (h x x x)
  let v34 := M (M (M x x) x) x
  T (T (T (T (h x v0 v34) (C h32 (C (T (C h33 (R v34)) h33) h32))) (C (T h26 (C h27 (T (C (T (C h31 h28) h31) h27) (S h30)))) h2)) (C (T (T (T (T (T (T (T (h (M v25 x) v21 y) (C h22 (C (T (T (T (T (T (C (C (T (C h27 (T h30 (C (T h29 (C h29 h28)) h27))) (S h26)) h23) h23) h20) h19) h18) h16) h13) h22))) (S (h v5 v21 z))) h20) h19) h18) h16) h13) h2)) h11

@[equational_result]
theorem Equation2334_implies_Equation2 (G: Type _) [Magma G] (h: Equation2334 G) : Equation2 G := fun x y =>
  have h0 := h y y x
  have h1 := R y
  let v2 := M y (M y (M x x))
  let v3 := M y x
  let v4 := M y (M y v3)
  have h5 := R x
  have h6 := h y y y
  have h7 := S h6
  have h8 := C h5 (C h5 h7)
  let v9 := M y (M y y)
  let v10 := M y v9
  have h11 := h v10 x y
  have h12 := h v10 y y
  have h13 := S h12
  have h14 := C h1 (C h1 h6)
  have h15 := h y x x
  have h16 := S h15
  have h17 := h (M x (M x v3)) x x
  let v18 := M x y
  let v19 := M x v18
  have h20 := h v19 x x
  have h21 := h v9 x y
  have h22 := h v2 x y
  have h23 := h x y x
  have h24 := h x y y
  have h25 := C h5 (C h5 (S h24))
  have h26 := h (M y (M y v18)) x y
  have h27 := T (T h26 (C (T h25 (C h5 (C h5 h23))) h5)) (S h22)
  have h28 := h x x y
  have h29 := S h23
  have h30 := T (T h22 (C (T (C h5 (C h5 h29)) (C h5 (C h5 h24))) h5)) (S h26)
  T (T h23 (C (T (T (h v2 v2 y) (C (T (C h30 (T (T (C h30 h29) (C (T (T h26 (C (T h25 (C h5 (C h5 h28))) h5)) (S (h (M x v19) x x))) h5)) (S h28))) (C h27 (T h24 (C h27 (T (T h15 (C (T h17 (C (T (T (T (C h5 (C h5 h16)) h20) (C (C h5 (C h5 (T (T (T (C (C h5 (C h5 h6)) h5) (S h11)) h12) (C (C h1 (C h1 h7)) h1)))) h5)) (S h21)) h5)) h5)) (C (T (T (T (T (T (h (M v9 x) y x) (C (T (C h1 (C h1 (T (C (T (C (T (T (T h21 (C (C h5 (C h5 (T (T (T (C h14 h1) h13) h11) (C h8 h5)))) h5)) (S h20)) (C h5 (C h5 h15))) h5) (S h17)) h5) h16))) h14) h1)) h13) h11) (C (T h8 (C h5 (C h5 h0))) h5)) (S (h v4 x y))) h5)))))) (R v2))) (S (h v4 v2 x))) h1)) (S h0)

@[equational_result]
theorem Equation1943_implies_Equation492 (G: Type _) [Magma G] (h: Equation1943 G) : Equation492 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M x v1
  have h3 := R v2
  let v4 := M y v2
  let v5 := M y v4
  have h6 := h x x v1
  have h7 := S h6
  let v8 := M x v2
  have h9 := h v8 v1 v2
  have h10 := S h9
  let v11 := M v1 (M v1 v2)
  have h12 := R v11
  have h13 := C h12 h6
  have h14 := R (M x (M x x))
  have h15 := h v11 x x
  have h16 := h v1 z v0
  have h17 := h z z y
  have h18 := h z z v0
  let v19 := M z v1
  have h20 := R v19
  have h21 := C (T (C h20 (T (S h18) h17)) (S h16)) h3
  have h22 := h x v19 v1
  have h23 := T h22 h21
  have h24 := R v1
  have h25 := C h24 h23
  let v26 := M v0 (M v0 v4)
  let v27 := M v4 (M v4 v2)
  have h28 := h v27 x x
  have h29 := R v27
  have h30 := h v8 v4 v2
  have h31 := T (C (T h16 (C h20 (T (S h17) h18))) h3) (S h22)
  let v32 := M v4 (M v4 x)
  have h33 := R (M x v8)
  T (T h22 h21) (C (T (T (h v1 v4 x) (C (T (T (T (h v32 x v1) (C (T (T (T (h v8 x v2) (C h33 h7)) (C h33 h23)) (S (h v1 x v2))) (T (T (T (T (T (C (R v32) (T (h v1 v4 v2) (C h29 h31))) (S (h v27 v4 x))) h28) (C h14 (T (T (T (C h29 h6) (S h30)) h9) (C h12 h7)))) (S h15)) (C h24 h31)))) (C h24 (T (T (T (T (T h25 h15) (C h14 (T (T (T h13 h10) h30) (C h29 h7)))) (S h28)) (h v27 v0 v4)) (C (R v26) (S (h y v4 v2)))))) (S (h v26 z y))) (T (T (T h25 h15) (C h14 (T (T (T h13 h10) (h v8 y v2)) (C (R v5) h7)))) (S (h v5 x x))))) (S (h y v0 v4))) h3)

@[equational_result]
theorem Equation2170_implies_Equation2349 (G: Type _) [Magma G] (h: Equation2170 G) : Equation2349 G := fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  let v2 := M y v1
  let v3 := M v2 z
  have h4 := R v3
  let v5 := M v2 v3
  have h6 := h v5 x z
  have h7 := R v0
  have h8 := R v5
  let v9 := M x z
  have h10 := h v9 v0 y
  have h11 := S h10
  have h12 := R v1
  have h13 := h y z x
  have h14 := C h13 h12
  have h15 := h v2 v2 z
  have h16 := S h15
  let v17 := M z v2
  have h18 := h v17 v3 v2
  have h19 := C (T (C (T h18 (C (T (T h16 h14) h11) h8)) h7) (S h6)) h4
  have h20 := h v0 z v2
  have h21 := R z
  let v22 := M v1 y
  have h23 := h v2 v22 v3
  have h24 := S h23
  have h25 := h z y v1
  have h26 := h v3 v1 y
  have h27 := C h26 h25
  have h28 := R (M v3 v0)
  have h29 := S h18
  have h30 := C (T (C (T (T h10 (C (S h13) h12)) h15) h8) h29) h7
  let v31 := M z v3
  T (T (h x v2 v3) (C (T (T (C (T (T (T h6 h30) (C (T (T (h v17 v3 v0) (C (T (T (T (T (T (T (T (S (h v0 v2 z)) h20) h19) (C (T (h v5 v3 z) (C (T (C (T (T h27 h24) h15) h8) h29) (R v31))) h4)) (S (h v31 z v2))) (C (T h25 (C h4 (T (T (T (h v22 z v2) (C (T (C (T h18 (C h16 h8)) (R v22)) (S (h v5 y v1))) h4)) (C (T h6 h30) h4)) (S h20)))) h4)) (C h28 (C (T h23 (C (S h26) (S h25))) h21))) (C h28 (T (C (T h27 h24) h21) (C (T h14 h11) h21)))) (R (M v0 v3)))) (S (h (M v9 z) v3 v0))) h7)) (S (h z x z))) (R x)) h20) h19) (R (M v3 v2)))) (S (h v3 v2 v3))

@[equational_result]
theorem Equation3404_implies_Equation4007 (G: Type _) [Magma G] (h: Equation3404 G) : Equation4007 G := fun x y z =>
  let v0 := M y x
  let v1 := M z v0
  let v2 := M v1 z
  have h3 := h v0 v2 z
  have h4 := R v2
  have h5 := h y x x
  have h6 := R x
  let v7 := M x y
  have h8 := h v7 x x
  have h9 := h v7 x y
  have h10 := h y y x
  have h11 := R y
  have h12 := h y y v0
  have h13 := S h12
  have h14 := h v0 y z
  have h15 := h v1 z y
  have h16 := R v0
  have h17 := C h16 (T h15 (C h11 (S h14)))
  have h18 := S h3
  have h19 := R v1
  have h20 := R z
  have h21 := h v0 y x
  let v22 := M v0 v2
  have h23 := T (T (T (C h11 (T h9 (C h11 (S h10)))) (S (h y y y))) h12) (C h16 (T (C h11 h14) (S h15)))
  let v24 := M y (M v7 x)
  T (T (T (T (T (T (T (T (h x y v7) (h v7 v24 y)) (C h11 (T (T (T (T (C (R v24) (T (C h11 (h x y y)) (S (h v0 y y)))) (C h23 (T (T (T h21 (C h6 (C h11 (T (C h6 h5) (S h8))))) (C h6 h23)) (h x v22 y)))) (S (h v0 y v22))) h21) (C h6 (T (T (T (S (h x x y)) (h x x z)) (C h20 (T (C h6 (h z x v1)) (S (h v2 v1 x))))) h18))))) (C h11 (C h6 (T h17 h13)))) (S (h y x y))) (h y x v2)) (C h4 (T (C h6 (T (h v2 y v2) (C h4 (T (T (T (T (C h11 (T (T (T (T (T (T (C h4 (T (h v1 z v1) (C h19 (T (T (S (h v0 v1 z)) (C h16 (h z v0 v1))) (S (h v2 v1 v0)))))) (S (h v1 v1 v2))) (h v1 v1 z)) (C h20 (T (C h19 (h z v1 v1)) (S (h v2 v1 v1))))) h18) h17) h13)) (C h11 h10)) (S h9)) h8) (C h6 (S h5)))))) (S (h v0 v2 x))))) (C h4 h3)) (S (h v1 z v2))

@[equational_result]
theorem Equation1304_implies_Equation3131 (G: Type _) [Magma G] (h: Equation1304 G) : Equation3131 G := fun x y z =>
  let v0 := M y x
  let v1 := M (M v0 z) z
  let v2 := M v1 y
  let v3 := M (M (M v2 x) x) v2
  let v4 := M (M v0 v2) v2
  have h5 := h v2 v4 v3
  have h6 := R v2
  have h7 := h v0 y z
  have h8 := S h7
  have h9 := R v3
  have h10 := h v2 v2 x
  have h11 := h y v2 v2
  have h12 := R v4
  have h13 := R v1
  let v14 := M (M (M v1 x) x) v1
  have h15 := h v1 x v14
  have h16 := R x
  have h17 := R v14
  have h18 := h v1 v1 x
  have h19 := h v0 x z
  have h20 := S h10
  have h21 := h y y x
  have h22 := S h21
  let v23 := M v0 x
  let v24 := M v23 y
  have h25 := R v24
  have h26 := S h18
  let v27 := M (M (M x x) x) x
  let v28 := M v23 x
  have h29 := h x v28 v27
  have h30 := R v28
  have h31 := R v27
  have h32 := h x x x
  have h33 := h y x x
  have h34 := S h32
  T (T (T (T (T (T h29 (C h30 (T (C (T (C h34 h31) h34) h30) (S h33)))) (h (M v28 y) v2 v1)) (C h6 (C (T (C (C (T (C h30 (T h33 (C (T h32 (C h32 h31)) h30))) (S h29)) (T (T h15 (C h16 (C (T (C h26 h17) h26) h16))) (S h19))) h13) (C (T (T (T (T (C h16 (C (T h21 (C h21 h25)) h16)) (S (h y x v24))) (h y v2 v24)) (C h6 (T (C (T (C h22 h25) h22) h6) h8))) (C (T h5 (C h12 (T (C (T (C h20 h9) h20) (C (C h7 h6) h6)) (S h11)))) (T (T h19 (C h16 (C (T h18 (C h18 h17)) h16))) (S h15)))) h13)) h6))) (S (h (M v4 y) v2 v1))) (C h12 (T h11 (C (T h10 (C h10 h9)) (C (C h8 h6) h6))))) (S h5)

@[equational_result]
theorem Equation4176_implies_Equation4297 (G: Type _) [Magma G] (h: Equation4176 G) : Equation4297 G := fun x y z =>
  let v0 := M z z
  let v1 := M z v0
  have h2 := R v1
  have h3 := R y
  have h4 := R z
  let v5 := M x y
  let v6 := M y v5
  have h7 := h v5 v6 x
  have h8 := S h7
  have h9 := R x
  have h10 := h x y v5
  have h11 := C h10 h9
  have h12 := R v5
  let v13 := M x v5
  let v14 := M y v13
  let v15 := M y v0
  have h16 := h v6 x y
  have h17 := h y v5 z
  have h18 := h z x y
  have h19 := h z x v5
  have h20 := h v5 v13 z
  have h21 := h v5 v13 y
  have h22 := h y x v5
  have h23 := h y y x
  T (T (T (T (T (T (T (T (h x v5 y) (C (T (C (T (T (T (h v5 y x) (C (T (C (T (h y x y) (C (T (h v5 y v5) (C (T (C (T (T (T (T (h y v5 x) (C (T (T (T (C (T h11 h8) h3) (S h16)) (C (T (T (T (T (T h17 (C (S h18) h4)) (C h19 h4)) (S h20)) h21) (C (S h22) h3)) h9)) (S h23)) h9)) (h (M y y) x v15)) (C (C (R (M x v15)) (T (T (T (T (T h23 (C (T (T (T (T (T (C h22 h3) (S h21)) h20) (C (S h19) h4)) (C h18 h4)) (S h17)) h9)) h16) (C (T h7 (C (S h10) h9)) h3)) (C (T (T (T (C (h x y v0) h9) (S (h v0 v15 x))) (h v0 v15 v5)) (C (S (h v5 y v0)) h12)) h3)) (S (h v5 v5 y)))) (R v15))) (S (h (M v5 v5) x v15))) h12) (S (h x v5 v5))) h12)) h3)) h12) (S (h y v13 v5))) h9)) (h v14 x v5)) (C (T (h v13 v14 x) (C (S (h x y v13)) h9)) h12)) h9) (S (h v5 v5 x))) h3)) (S (h v5 x y))) h11) h8) (h v5 v6 v1)) (C (S (h v1 y v5)) h2)) (C (C (T (T (T (h z v0 z) (C (S (h z z z)) h4)) (C (h z z v0) h4)) (S (h v0 v1 z))) h3) h2)) (S (h y v0 v1))

@[equational_result]
theorem Equation914_implies_Equation1746 (G: Type _) [Magma G] (h: Equation914 G) : Equation1746 G := fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  let v2 := M y y
  let v3 := M v2 v1
  have h4 := h v3 v3 z
  let v5 := M v3 v3
  let v6 := M x x
  have h7 := R v6
  have h8 := h v3 v3 v0
  have h9 := S h8
  have h10 := R v3
  let v11 := M v0 v0
  let v12 := M v5 v11
  have h13 := h v12 v3 v2
  let v14 := M v2 v2
  have h15 := R v14
  have h16 := R v2
  have h17 := h v2 v3 x
  have h18 := S h17
  let v19 := M (M v3 v2) v6
  have h20 := h v19 v3 y
  have h21 := R y
  have h22 := S h20
  have h23 := C h10 (C h17 h16)
  have h24 := h x y v2
  let v25 := M (M y x) v14
  have h26 := R v0
  let v27 := M v3 v0
  have h28 := h v0 v3 v0
  T (T (T (T (T (T (T (T (T (h x v0 v3) (C (T (T (T (T (T h28 (C h10 (T (T (h (M v27 v11) v3 z) (C h10 (C (S h28) h26))) (C h8 (R v11))))) (S (h v12 v3 v0))) h13) (C h10 (T (T (C h9 h15) h23) h22))) h18) (C (h v1 v2 z) (R v5)))) (S (h v27 v2 v3))) (C h10 (T (T (h v0 x y) (C (R x) (C (T (T (T (h (M x v0) y x) (C h21 (C (T (T (C h21 (C h24 h26)) (S (h v25 y z))) (h v25 y v2)) h7))) (S (h (M (M y v25) v14) y x))) (C (S h24) h15)) h16))) (S (h v14 x y))))) h23) h22) (h v19 v3 v2)) (C h10 (T (T (C h18 h15) (h (M v2 v14) y v2)) (C h21 (T (C (S (h y y v2)) h15) (S (h y y y))))))) (C h10 (T (T (T (T (T h17 (C h10 (T (T h20 (C h10 (C h18 h16))) (C h8 h15)))) (S h13)) (h v12 v3 x)) (C h10 (T (C h9 h7) (C h4 h7)))) (S (h (M v5 v0) v3 x))))) (S h4)

@[equational_result]
theorem Equation952_implies_Equation1929 (G: Type _) [Magma G] (h: Equation952 G) : Equation1929 G := fun x y z =>
  let v0 := M z z
  let v1 := M y x
  let v2 := M y v1
  let v3 := M v2 v0
  let v4 := M v3 v3
  have h5 := R v3
  have h6 := h v0 v2 v2
  have h7 := R v0
  let v8 := M v3 (M v2 v2)
  let v9 := M y v0
  let v10 := M x x
  have h11 := R v10
  have h12 := h v0 x x
  have h13 := R x
  let v14 := M (M x v0) v10
  have h15 := h v14 x x
  let v16 := M v1 x
  let v17 := M v1 v0
  have h18 := h x v1 v0
  let v19 := M v0 x
  have h20 := h v1 z x
  let v21 := M (M x v1) (M x z)
  have h22 := h v21 z z
  have h23 := h z v1 v2
  let v24 := M (M v2 z) (M v2 v1)
  have h25 := R v16
  let v26 := M z v1
  T (T (T (T (T (T (T h18 (C (T (T (h v1 x z) (C h13 (C (T (T (T (T (h v26 x v0) (C h13 (C (T (T (T (T (h (M v0 v26) x v1) (C h13 (T (C (S (h z v1 z)) h25) (C h23 h25)))) (S (h v24 x v1))) (h v24 v0 v1)) (C h7 (T (C (S h23) (C h20 h7)) (S h22)))) (R v19)))) (S (h v21 x v0))) h22) (C (R z) (C (S h20) h7))) (R (M z x))))) (S (h v17 x z))) (T (h (M v19 (M v0 v1)) v1 v1) (C (R v1) (T (C (S h18) (R (M v1 v1))) (S (h x x y))))))) (h (M v17 v16) x x)) (C h13 (T (C (S (h v0 x v1)) h11) (C h12 h11)))) (S h15)) (h v14 v3 v3)) (C h5 (C (T (T (C h5 (T (T (T (T h15 (C h13 (T (C (S h12) h11) (C (h v0 x y) h11)))) (S (h (M v9 v1) x x))) (C (R v9) (T (h v1 v0 y) (C h6 (R (M v2 v9)))))) (S (h v8 v9 v2)))) (C h5 (T (T (h v8 v0 v2) (C h7 (C (S h6) h5))) (C (h v0 v0 v2) (R (M v0 v3)))))) (S (h v4 v3 v0))) (R v4)))) (S (h v3 v3 v3))

@[equational_result]
theorem Equation1699_implies_Equation3211 (G: Type _) [Magma G] (h: Equation1699 G) : Equation3211 G := fun x y z =>
  let v0 := M y z
  let v1 := M v0 z
  let v2 := M v1 x
  let v3 := M v2 y
  let v4 := M (M v3 v1) v1
  have h5 := R v1
  let v6 := M (M v2 v3) v3
  have h7 := h v6 x x
  have h8 := R (M (M x x) x)
  have h9 := R v6
  have h10 := h x v1 v3
  have h11 := S h10
  let v12 := M (M v1 v3) v3
  have h13 := h v12 v2 v3
  have h14 := h v12 v2 v1
  have h15 := S h14
  let v16 := M (M v2 v1) v1
  have h17 := R v16
  have h18 := C h10 h17
  have h19 := h v16 x x
  have h20 := h v1 v0 z
  have h21 := S h20
  let v22 := M v1 z
  have h23 := R v22
  have h24 := h z y z
  have h25 := h z v0 z
  have h26 := C (T (S h25) h24) h23
  have h27 := R v2
  have h28 := h x v1 v22
  have h29 := C (T h28 (C h27 (T h26 h21))) h5
  have h30 := T h20 (C (T (S h24) h25) h23)
  have h31 := T (C h27 h30) (S h28)
  let v32 := M (M x v3) v3
  let v33 := M v3 y
  T h28 (C h27 (T (T (T (T h26 h21) (h v1 x v3)) (C (T (T (T h29 h19) (C (T (T (T h18 h15) (h v12 v2 y)) (C h11 (R v33))) h8)) (S (h v33 x x))) (T (T (T (h v32 v1 v1) (C (T (T (T (T (T (C (T (h v1 v2 v3) (C h31 h9)) (R v32)) (S (h v6 x v3))) h7) (C (T (T (T (C h10 h9) (S h13)) h14) (C h11 h17)) h8)) (S h19)) (C h31 h5)) (T (C (R (M v1 v1)) h30) (S (h v1 v1 v22))))) (C (T (T (T (T (T h29 h19) (C (T (T (T h18 h15) h13) (C h11 h9)) h8)) (S h7)) (h v6 v3 v1)) (C (S (h y v2 v3)) (R v4))) h5)) (S (h v4 y z))))) (S (h y v3 v1))))

@[equational_result]
theorem Equation3131_implies_Equation1507 (G: Type _) [Magma G] (h: Equation3131 G) : Equation1507 G := fun x y z =>
  let v0 := M z y
  let v1 := M z v0
  let v2 := M y x
  let v3 := M v2 v1
  have h4 := h v1 v0 v0
  have h5 := S h4
  have h6 := R v0
  have h7 := R v1
  have h8 := h v0 z z
  have h9 := C (S h8) h7
  have h10 := h z v1 z
  have h11 := T h10 h9
  have h12 := C h11 h6
  have h13 := C h12 h6
  have h14 := C (T (T (C h13 h6) h5) h12) h6
  have h15 := T (C h8 h7) (S h10)
  have h16 := C h15 h6
  have h17 := C h16 h6
  have h18 := C h17 h6
  have h19 := h y z v1
  have h20 := S h19
  have h21 := R z
  have h22 := S (h z v1 y)
  have h23 := R y
  have h24 := h v1 z z
  have h25 := h z y z
  have h26 := C (T h25 (C (C (T (C (C (T h19 (C (C h15 h7) h21)) h21) h21) (S h24)) h21) h23)) h23
  have h27 := h v0 v1 v0
  have h28 := C (T (T (C (T h13 (C (T (T h16 h4) h18) h6)) h7) (S h27)) h26) h7
  have h29 := C (T (T (T (C (T (T (T (T (C (T (C (T (h v0 v1 v1) (C (T (T (T h28 h22) h10) h9) h7)) h21) h20) h6) (C (h y z z) h6)) (S (h z v0 z))) h10) h9) h6) h16) h4) h18) h6
  have h30 := h z v0 v0
  have h31 := R v3
  T (T (h x y v3) (C (C (C (T (h v2 v3 v2) (C (S (h v1 v2 v2)) h31)) h31) h31) (T (T (h y v0 v1) (C (T (T (T (T (T (C (T (T (T (C (C (T h26 (C (T (T (T (T (T (C (C (T h24 (C (C (T (C (C h11 h7) h21) h20) h21) h21)) h21) h23) (S h25)) h30) h29) h14) h17) h23)) h23) h7) (S (h v0 v1 y))) h27) (C (T h14 h17) h7)) h7) h28) h22) h30) h29) h14) h6)) h5))) (S (h v3 v1 v3))

