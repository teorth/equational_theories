import equational_theories.EndToEnd.Basic

/-!
# The certificate, its checker, and the decision procedure

The certificate is untrusted data: `checkCert` validates it, and `resolve` uses it only to
*find* a witness, which is then checked by `checkImplication`/`checkRefutation` from `Basic.lean`.

Everything is done on the ~1415 strongly connected components rather than on the 4694
equations, because the rank induction that justifies the forward walk has nowhere to descend
inside an SCC. Each SCC's reachability set is one `Nat` used as a bitset over SCCs; the
Lean kernel has GMP fast paths for `Nat.testBit`, `|||` and `<<<`, so these are cheap.

Both directions get their own fixpoint and rank:

* `reaches`/`out`/`rank`   -- forward:  `reaches[i]` is the set of SCCs `i` implies
* `reachedBy`/`rout`/`rrank` -- reverse: `reachedBy[c]` is the set of SCCs implying `c`

The reverse copy is not a convenience. A refutation needs a *forward* implication `m ⟹ b`, while the
refuters supply the reverse fact that `b` is implied by `m`. Deriving one from the other means
checking that `reachedBy` is the transpose of `reaches`, which is Θ(K²); walking the reverse
graph and emitting it in forward order avoids the transpose entirely.
-/

namespace EndToEnd

/-- Untrusted data guiding the search. Validated by `checkCert`. -/
structure Certificate where
  /-- number of equations covered; 4694 for the real instance -/
  numEq : Nat
  numSccs : Nat
  numNeg : Nat
  /-- equation index (0-based) → SCC id -/
  scc : RArray Nat
  /-- SCC id → a representative equation index -/
  rep : RArray Nat
  /-- SCC id → bitset of SCCs it implies -/
  reaches : RArray Nat
  /-- SCC id → bitset of SCCs implying it -/
  reachedBy : RArray Nat
  /-- Position of an SCC in a topological sort of the condensation: strictly decreasing
  along every edge, so it is a well-founded measure for the induction in `walkFwd_correct`
  and a certificate that the condensation really is acyclic. Any linear extension works;
  Tarjan already emits SCCs in reverse topological order, so the SCC id itself is used, and
  this is `id`.

  A function rather than an `RArray`, because that is all it ever was: as a table it cost
  1415 stored naturals and a 13-step tree descent per edge check, where `id` costs one
  unfolding. It stays a certificate field, and stays untrusted, because `checkFwd` still has
  to verify that it really does decrease along every edge. -/
  rank : Nat → Nat
  /-- The same for the reversed graph, so `fun i => numSccs - 1 - i`. -/
  rrank : Nat → Nat
  /-- SCC id → indices into `pos` of cross-SCC edges *out of* it -/
  out : RArray (List Nat)
  /-- SCC id → indices into `pos` of cross-SCC edges *into* it -/
  rout : RArray (List Nat)
  /-- equation index → implication from it to its SCC representative -/
  sccUp : RArray Implication
  /-- equation index → implication from its SCC representative to it -/
  sccDn : RArray Implication
  /-- SCC id → indices into `neg`: witnesses whose `fmask`s, together with `reaches[i]`,
  cover every SCC. Chosen by greedy set cover; `checkRefuters` is the covering condition. -/
  refuters : RArray (List Nat)
  /-- `neg` index → the set of SCCs that witness refutes. Tied to its own `refutes` list by
  `checkFmask`. -/
  fmask : RArray Nat

variable (C : Certificate) (pos : RArray PosFact) (neg : RArray NegFact)

/-- SCC of the source of base fact `k`. -/
abbrev srcScc (k : Nat) : Nat := C.scc.get (pos.get k).hyp
/-- SCC of the target of base fact `k`. -/
abbrev tgtScc (k : Nat) : Nat := C.scc.get (pos.get k).conc

/-- All-ones over `numSccs` bits. -/
abbrev fullMask : Nat := (1 <<< C.numSccs) - 1

/-- Forward fixpoint plus strictly decreasing rank, for one SCC. -/
def checkFwd (i : Nat) : Bool :=
  ((C.out.get i).all fun k =>
      (srcScc C pos k == i) && Nat.blt (tgtScc C pos k) C.numSccs &&
      Nat.blt (pos.get k).hyp C.numEq && Nat.blt (pos.get k).conc C.numEq &&
      Nat.blt (C.rank (tgtScc C pos k)) (C.rank i)) &&
  Nat.blt (C.rank i) C.numSccs &&
  (C.reaches.get i ==
     ((1 <<< i) ||| (C.out.get i).foldl (fun acc k => acc ||| C.reaches.get (tgtScc C pos k)) 0))

/-- Reverse fixpoint plus strictly decreasing reverse rank, for one SCC. -/
def checkRev (c : Nat) : Bool :=
  ((C.rout.get c).all fun k =>
      (tgtScc C pos k == c) && Nat.blt (srcScc C pos k) C.numSccs &&
      Nat.blt (pos.get k).hyp C.numEq && Nat.blt (pos.get k).conc C.numEq &&
      Nat.blt (C.rrank (srcScc C pos k)) (C.rrank c)) &&
  Nat.blt (C.rrank c) C.numSccs &&
  (C.reachedBy.get c ==
     ((1 <<< c) ||| (C.rout.get c).foldl (fun acc k => acc ||| C.reachedBy.get (srcScc C pos k)) 0))

/-- Each equation is inter-implicable with its SCC representative. -/
def checkScc (e : Nat) : Bool :=
  checkImplication pos e (C.rep.get (C.scc.get e)) (C.sccUp.get e) &&
  checkImplication pos (C.rep.get (C.scc.get e)) e (C.sccDn.get e)

/-- `fmask k` really is the set of SCCs witness `k` refutes. -/
def checkFmask (k : Nat) : Bool :=
  (neg.get k).satisfies.all (fun a => Nat.blt a C.numEq) &&
  (neg.get k).refutes.all (fun b => Nat.blt b C.numEq) &&
  (C.fmask.get k == (neg.get k).refutes.foldl (fun acc b => acc ||| C.reachedBy.get (C.scc.get b)) 0)

/-- Witness `k` satisfies some law of SCC `i`. -/
def satAt (k i : Nat) : Bool :=
  (neg.get k).satisfies.any fun a => Nat.testBit (C.reaches.get (C.scc.get a)) i

/-- Every SCC `i` does not imply is refuted by one of `refuters i`, each of which satisfies `i`. -/
def checkRefuters (i : Nat) : Bool :=
  ((C.refuters.get i).all fun k => Nat.blt k C.numNeg && satAt C neg k i) &&
  ((C.reaches.get i ||| (C.refuters.get i).foldl (fun acc k => acc ||| C.fmask.get k) 0)
      == fullMask C)

/-- The whole certificate check. -/
def checkCert : Bool :=
  (List.range C.numEq).all (fun e => Nat.blt (C.scc.get e) C.numSccs && checkScc C pos e) &&
  (List.range C.numNeg).all (fun k => checkFmask C neg k) &&
  (List.range C.numSccs).all
    (fun i => checkFwd C pos i && checkRev C pos i && checkRefuters C neg i)

/-- Implication from `rep i` to `rep j`, following forward edges whose target still reaches `j`.
Each cross-SCC step `a ⟹ b` is padded to run between representatives:
`rep i ⟹ a` by `sccDn a`, the edge itself, then `b ⟹ rep (scc b)` by `sccUp b`. -/
def walkFwd : Nat → Nat → Nat → Implication
  | 0, _, _ => []
  | fuel + 1, i, j =>
      if i == j then [] else
      match (C.out.get i).find? (fun k => Nat.testBit (C.reaches.get (tgtScc C pos k)) j) with
      | none => []
      | some k =>
          C.sccDn.get (pos.get k).hyp ++ k :: (C.sccUp.get (pos.get k).conc ++
            walkFwd fuel (tgtScc C pos k) j)

/-- Implication from `rep j` to `rep c`, found by walking the reverse graph down from `c` but
emitted in forward order. -/
def walkRev : Nat → Nat → Nat → Implication
  | 0, _, _ => []
  | fuel + 1, c, j =>
      if c == j then [] else
      match (C.rout.get c).find? (fun k => Nat.testBit (C.reachedBy.get (srcScc C pos k)) j) with
      | none => []
      | some k =>
          walkRev fuel (srcScc C pos k) j ++
            (C.sccDn.get (pos.get k).hyp ++ k :: C.sccUp.get (pos.get k).conc)

/-- Decide `lawOf n ⟹ lawOf m`, returning a checkable witness either way.

Not named `resolve`: `Superposition.lean:172` declares a *term-level* elaborator
`resolve e₁ e₂`, which would silently capture the first two arguments.

The `.inl []` fallbacks are unreachable once `checkCert C pos neg = true`; they are there only
to make the function total, and would be rejected by `checkImplication` if they ever fired. -/
def resolveImplication (n m : Nat) : Implication ⊕ Refutation :=
  let i := C.scc.get n
  let j := C.scc.get m
  if Nat.testBit (C.reaches.get i) j then
    .inl (C.sccUp.get n ++ (walkFwd C pos C.numSccs i j ++ C.sccDn.get m))
  else
    match (C.refuters.get i).find? (fun k => Nat.testBit (C.fmask.get k) j) with
    | none => .inl []
    | some k =>
        let f := neg.get k
        match f.satisfies.find? (fun a => Nat.testBit (C.reaches.get (C.scc.get a)) i),
              f.refutes.find? (fun b => Nat.testBit (C.reachedBy.get (C.scc.get b)) j) with
        | some a, some b =>
            .inr { fact := k, a := a, b := b,
                   up := C.sccUp.get a ++ (walkFwd C pos C.numSccs (C.scc.get a) i ++
                           C.sccDn.get n),
                   down := C.sccUp.get m ++ (walkRev C pos C.numSccs (C.scc.get b) j ++
                             C.sccDn.get b) }
        | _, _ => .inl []

end EndToEnd
