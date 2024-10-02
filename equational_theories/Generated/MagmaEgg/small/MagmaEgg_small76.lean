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
theorem Equation4176_implies_Equation3385 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3385 G := fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  have h2 := R z
  have h3 := R v0
  let v4 := M x y
  have h5 := h v1 z v4
  have h6 := S h5
  have h7 := R v4
  have h8 := R v1
  have h9 := h z v4 v1
  have h10 := S h9
  have h11 := h x y v0
  have h12 := R x
  have h13 := h y z v1
  have h14 := S h13
  let v15 := M z v1
  have h16 := h v15 y z
  have h17 := S h16
  have h18 := R v15
  have h19 := h y z x
  have h20 := S h19
  let v21 := M (M z x) y
  have h22 := h v21 x y
  have h23 := R y
  have h24 := h v4 v21 x
  let v25 := M v0 v4
  have h26 := h v25 x y
  have h27 := h v4 v25 x
  have h28 := S h27
  have h29 := h x v0 v4
  have h30 := C h29 h12
  have h31 := h v1 x v0
  have h32 := S h31
  have h33 := h v1 v1 x
  have h34 := S h33
  have h35 := C (T (h y v4 v1) (C (S (h v1 x y)) h8)) h12
  have h36 := h y v4 v0
  have h37 := S h36
  have h38 := h v0 x y
  have h39 := C h38 h3
  have h40 := h v0 x v0
  have h41 := C (S h40) h3
  have h42 := h v0 v1 v0
  have h43 := h v1 v21 x
  have h44 := C (T (T (T h43 (C (T (T (T (T (C h20 h8) h42) h41) h39) h37) h12)) h35) h34) h3
  have h45 := h v21 x v0
  have h46 := C (T (T (T (T (T h19 h45) h44) h32) h30) h28) h23
  have h47 := C h14 h23
  have h48 := h v1 v15 y
  have h49 := h y v1 v15
  have h50 := C (T (C (T h49 (C (T (T (C (T (T (T (T (T h48 h47) h46) (S h26)) (C (C h19 h7) h12)) (S h24)) h23) (S h22)) h20) h18)) h2) h17) h8
  have h51 := h z y v1
  have h52 := T (T h51 h50) h14
  have h53 := C h23 h52
  let v54 := M z y
  have h55 := h y v54 y
  have h56 := S h55
  have h57 := h y z y
  have h58 := C h57 h23
  have h59 := S h45
  have h60 := S h38
  have h61 := C (T (T (T (T (T (C h31 h8) (S (h v0 v1 v1))) h42) h41) h39) h37) h12
  have h62 := C (T (T (T h33 h61) (C (T (T (T (T h36 (C h60 h3)) (C h40 h3)) (S h42)) (C h19 h8)) h12)) (S h43)) h3
  have h63 := C (S h29) h12
  have h64 := C (T (T (T (T (T h27 h63) h31) h62) h59) h20) h23
  have h65 := h y v1 x
  have h66 := h v0 y v1
  have h67 := h x v0 z
  have h68 := S h67
  let v69 := M v0 z
  let v70 := M v69 x
  have h71 := h v15 v70 z
  have h72 := C (T (T h71 (C (T (T (C h68 h18) h48) h47) h2)) (C (T h66 (C (T (C (T h65 (C (T (T (T (T (C (T h30 h28) h23) h64) h58) h56) h53) h12)) h3) (S h11)) h8)) h2)) h8
  have h73 := h v70 z v1
  have h74 := T (T (T h67 h73) h72) h10
  have h75 := C (T (T h35 h34) (C h74 h8)) h7
  have h76 := h x y v4
  have h77 := S h48
  have h78 := C h13 h23
  have h79 := h y z v0
  have h80 := h v0 (M z v0) y
  have h81 := C (S h57) h23
  have h82 := C h23 (T (T h13 (C (T h16 (C (T (C (T (T h19 h22) (C (T (T (T (T (T h24 (C (C h20 h7) h12)) h26) h64) h78) h77) h23)) h18) (S h49)) h2)) h8)) (S h51))
  have h83 := T (T (T h9 (C (T (T (T (T (C (T (T (T (T (C (T h11 (C (T (C (T (T (T (T h82 h55) h81) h46) (C (T h27 h63) h23)) h12) (S h65)) h3)) h8) (S h66)) h58) h56) h53) h2) (C (T (T (T (T h82 h55) h81) (C h79 h23)) (S h80)) h2)) (C (T (T (T h80 (C (S h79) h23)) h78) h77) h2)) (C (C h67 h18) h2)) (S h71)) h8)) (S h73)) h68
  let v84 := M z v4
  have h85 := h x v0 x
  have h86 := C (S h85) h12
  have h87 := h x (M v0 x) x
  have h88 := T (T (T h31 h62) h59) h20
  let v89 := M v1 x
  T (T (T (T h76 h75) h6) (C (T (T (T (T (T h85 (C (T (T (T (T (C (C h19 h12) h12) (S (h x v21 x))) (C h12 (T (C (T (h z x v0) (C (T (T h5 (C (T (T (C h83 h8) h33) h61) h7)) (S h76)) h3)) h23) h60))) h87) h86) h12)) (C h88 h12)) h40) (C (T (h v1 v0 v4) (C (T (T (C (T (T (T (T (C (T (T (T (T (T h19 h45) h44) h32) (h v1 x v1)) (C (T (T (T (T (T (C (T (T (T (T (T (T (C h12 (T (T (T (T (T h67 h73) h72) h10) (h z v4 x)) (C (T (T (T (T (T (C (T (C (h x y z) h12) (S (h z v0 x))) h2) (C (T (T (h z v0 v15) (C (T (T h17 (h v15 y v0)) (C (T (C (T (T (T (T h82 h55) h81) (h v0 y z)) (C (T (T (T (C (T h57 (C (T (T (T (T (T (h v54 y v0) (C (C (R (M y v0)) h52) h3)) (S (h v0 y v0))) h58) h56) h53) h23)) h3) (S (h y y v0))) (h y y v15)) (C (T (C (T (T (C h23 (T (T (T (h z v1 x) (h (M v89 z) x v15)) (C (C (R (M x v15)) (T (T (h v89 z v4) (C (C (R v84) h88) h7)) (S (h v0 z v4)))) h18)) (S (h v69 x v15)))) (h y v70 z)) (C (C h68 h23) h2)) h23) (S (h z v1 y))) h18)) h2)) h18) (S (h z v15 v15))) h3)) h18)) (S (h v0 z v15))) h2)) (S (h z y z))) h51) h50) h14) h12))) h87) h86) h31) h62) h59) h20) h74) (C h3 h83)) h42) h41) h39) h37) h74)) h7) (S (h v84 y v4))) (h v84 y v15)) (C (C (R (M y v15)) h83) h18)) (S (h v1 y v15))) h8) (C (h v1 y z) h8)) (S (h z v0 v1))) (T (T h76 h75) h6))) h3)) (S (h (M v1 z) z v0))) h2)) (S (h z v1 z))

