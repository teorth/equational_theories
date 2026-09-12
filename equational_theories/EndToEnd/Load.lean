import equational_theories.EndToEnd.Certificate
import equational_theories.EndToEnd.Dual
import equational_theories.ParseImplications

/-!
# Loading the certificate tables at elaboration time

The tables are JSON in `Generated/EndToEndCertificate/json/`; these elaborators read a file and
assemble the `RArray` `Expr` directly, leaving only the kernel's check of the finished term.

The JSON is untrusted: `checkCert` validates the numeric tables and the fact tables are
proof-carrying, so a wrong entry can only cause a build failure. Lake cannot see that an
`.olean` depends on a file read during elaboration, so each module records the FNV-1a hash of
the file it expects and `readTable` checks it.

`RArray.ofFn` must never appear in a term the kernel reduces -- it is well-founded recursion
and will not unfold -- but here it runs in the elaborator and produces a `.leaf`/`.branch`
literal.
-/

namespace EndToEnd

open Lean Elab Term

/-- `[a, b, c]` as an `Expr` of type `List ty`, for `ty : Type 0`. -/
private def listExpr (ty : Expr) (xs : Array Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (.const ``List.cons [0]) ty x acc) (mkApp (.const ``List.nil [0]) ty)

/-- `[a, b, c]` as an `Expr` of type `List Nat`. -/
private def natListExpr (xs : Array Nat) : Expr :=
  listExpr (.const ``Nat []) (xs.map mkRawNatLit)

/-- View `e` as `@Exists α p`. -/
private def asExists (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``Exists 2 then some (e.appFn!.appArg!, e.appArg!) else none

/-- Flatten a right-nested `mkAndN` conjunction into its components, left to right.

Written iteratively: the largest `Facts` statements have hundreds of conjuncts, and
`parseFacts` documents that naive recursion here blows the stack. -/
private def flattenAndN (e : Expr) : Array Expr := Id.run do
  let mut out : Array Expr := #[]
  let mut cur := e
  while cur.isAppOfArity ``And 2 do
    out := out.push cur.appFn!.appArg!
    cur := cur.appArg!
  if cur.isConstOf ``True then return out
  return out.push cur

/-- The nested `And.intro` chain terminated by `True.intro`, with its type. This matches how
`Law.SatisfiesAll`/`Law.RefutesAll` unfold, so the result is definitionally at the intended
type. -/
private def mkNestedAnd (comps : Array (Expr × Expr)) : Expr × Expr := Id.run do
  let mut accTy := Lean.mkConst ``True
  let mut accPf := Lean.mkConst ``True.intro
  for (t, p) in comps.reverse do
    accPf := mkApp4 (Lean.mkConst ``And.intro) t accTy p accPf
    accTy := mkApp2 (Lean.mkConst ``And) t accTy
  return (accTy, accPf)

/-- Peel a chain of `∃` binders off `ty`, running `k` on the collected witnesses and the
innermost hypothesis, then rebuild the result with `Exists.elim`. -/
private partial def elimExists (h ty : Expr) (acc : Array Expr)
    (k : Array Expr → Expr → MetaM Expr) : MetaM Expr := do
  match asExists ty with
  | none => k acc h
  | some (α, p) =>
    Meta.withLocalDeclD `x α fun x => do
      let body := p.beta #[x]
      Meta.withLocalDeclD `hx body fun hx => do
        let inner ← elimExists hx body (acc.push x) k
        let f ← Meta.mkLambdaFVars #[x, hx] inner
        Meta.mkAppM ``Exists.elim #[h, f]

/-- The deep-embedded companion of the `Facts` theorem `thm`, as a proof term.

`thm` states one flat conjunction (`FactsSyntax`), while `NegFact.h` wants the same content
over `Law.MagmaLaw ℕ`:

```
∃ (G : Type) (_ : Magma G) [(_ : Finite G)], Eq a₁ G ∧ … ∧ ¬ Eq b₁ G ∧ …
∃ (G : Type) (_ : Magma G), Law.SatisfiesAll G [Law a₁, …] ∧ Law.RefutesAll G [Law b₁, …]
```

Each conjunct is converted through `models_iff`. The `Finite` binder is dropped; the
certificate only needs the general statement. -/
def factsProof (thm : Name) : MetaM Expr := do
  let some info := (← getEnv).find? thm
    | throwError "`{thm}` does not exist -- is the module that proves it imported here?"
  unless info.levelParams.isEmpty do
    throwError "`{thm}` is universe-polymorphic, but the certificate is stated at `Type 0`"
  -- The largest `Facts` statements have >600 conjuncts, and both the nested `And.intro` chain
  -- and the `isDefEq` against `SatisfiesAll`/`RefutesAll` recurse to that depth.
  withAtLeastMaxRecDepth 100000 do
  let natTy := Lean.mkConst ``Nat
  let lawTy := mkApp (Lean.mkConst ``Law.MagmaLaw [levelZero]) natTy

  let proof ← elimExists (Lean.mkConst thm) info.type #[] fun ws h => do
    -- `ws` is `#[G, inst]`, or `#[G, inst, finiteInst]` when the statement carries `Finite G`.
    if ws.size < 2 then throwError "`{thm}`: expected at least two existential binders"
    let G := ws[0]!
    let inst := ws[1]!
    let conjTy ← Meta.inferType h
    let comps := flattenAndN conjTy

    let mut satPairs : Array (Expr × Expr) := #[]
    let mut refPairs : Array (Expr × Expr) := #[]
    let mut satLaws : Array Expr := #[]
    let mut refLaws : Array Expr := #[]
    let mut cur := h
    let mut curTy := conjTy
    let n := comps.size
    for i in [0:n] do
      let compTy := comps[i]!
      -- Project the `i`-th conjunct out of the right-nested chain.
      let mut compPf := cur
      if i + 1 != n then
        let restTy := curTy.appArg!
        compPf := mkApp3 (Lean.mkConst ``And.left) compTy restTy cur
        cur := mkApp3 (Lean.mkConst ``And.right) compTy restTy cur
        curTy := restTy
      -- Classify as satisfied or refuted and convert through `models_iff`.
      let negated := compTy.isAppOfArity ``Not 1
      let eqTy := if negated then compTy.appArg! else compTy
      let some num := getEquationNumber eqTy
        | throwError "`{thm}`: could not read an equation number from {eqTy}"
      let lawName := Name.mkSimple s!"Law{num}"
      let lawE := Lean.mkConst lawName
      let satTy := mkApp4 (Lean.mkConst ``satisfies [levelZero, levelZero]) natTy G inst lawE
      let mi := mkApp2 (Lean.mkConst (lawName.str "models_iff") [levelZero]) G inst
      if negated then
        -- `fun hh => compPf (mi.mp hh)`
        let pf ← Meta.withLocalDeclD `hh satTy fun hh =>
          Meta.mkLambdaFVars #[hh] (mkApp compPf (mkApp4 (Lean.mkConst ``Iff.mp) satTy eqTy mi hh))
        refPairs := refPairs.push (mkApp (Lean.mkConst ``Not) satTy, pf)
        refLaws := refLaws.push lawE
      else
        satPairs := satPairs.push (satTy, mkApp4 (Lean.mkConst ``Iff.mpr) satTy eqTy mi compPf)
        satLaws := satLaws.push lawE

    let (satAllTy, satAllPf) := mkNestedAnd satPairs
    let (refAllTy, refAllPf) := mkNestedAnd refPairs
    let pairPf := mkApp4 (Lean.mkConst ``And.intro) satAllTy refAllTy satAllPf refAllPf

    -- `Law.SatisfiesAll G satList ∧ Law.RefutesAll G refList`, definitionally the above.
    let satListE := listExpr lawTy satLaws
    let refListE := listExpr lawTy refLaws
    let satAll := mkApp3 (Lean.mkConst ``Law.SatisfiesAll) G inst satListE
    let refAll := mkApp3 (Lean.mkConst ``Law.RefutesAll) G inst refListE
    let innerTy := mkApp2 (Lean.mkConst ``And) satAll refAll

    let tyI ← Meta.inferType inst
    let tyG ← Meta.inferType G
    let pInst ← Meta.mkLambdaFVars #[inst] innerTy
    let introInst := mkApp4 (Lean.mkConst ``Exists.intro [levelOne]) tyI pInst inst pairPf
    let existsInst := mkApp2 (Lean.mkConst ``Exists [levelOne]) tyI pInst
    let pG ← Meta.mkLambdaFVars #[G] existsInst
    let tyGG := mkApp2 (Lean.mkConst ``Exists [mkLevelSucc levelOne]) tyG pG
    let _ := tyGG
    return mkApp4 (Lean.mkConst ``Exists.intro [mkLevelSucc levelOne]) tyG pG G introInst

  Meta.check proof
  return proof

/-- FNV-1a, 64-bit; the generator computes the same value. Not cryptographic and does not need
to be -- it guards against a data file drifting out of step with the module that names it. -/
def fnv1a (bytes : ByteArray) : UInt64 := Id.run do
  let mut h : UInt64 := 0xcbf29ce484222325
  for b in bytes do
    h := (h ^^^ b.toUInt64) * 0x100000001b3
  return h

/-- Read a data file named relative to the directory of the Lean source being elaborated -- the
same way `include_str` resolves its argument -- and check it against the expected hash. -/
private def readTable (path : StrLit) (hash : Nat) : TermElabM String := do
  let src := System.FilePath.mk (← readThe Core.Context).fileName
  let some dir := src.parent | throwError "cannot compute the parent directory of `{src}`"
  let file := dir / path.getString
  unless ← file.pathExists do
    throwError "no such data file: `{file}`"
  let bytes ← IO.FS.readBinFile file
  let actual := fnv1a bytes
  unless actual.toNat == hash do
    throwError "`{file}` does not match the hash recorded here \
      (expected {hash}, found {actual.toNat}). Regenerate with \
      equational_theories/Generated/EndToEndCertificate/src/generate.py."
  return String.fromUTF8! bytes

/-- The JSON array in `s`. -/
private def parseArray (path : StrLit) (s : String) : TermElabM (Array Json) := do
  match Json.parse s >>= (·.getArr?) with
  | .ok a => return a
  | .error e => throwErrorAt path "`{path.getString}` is not a JSON array: {e}"

private def toNat (path : StrLit) (j : Json) : TermElabM Nat := do
  match j.getNat? with
  | .ok n => return n
  | .error e => throwErrorAt path "`{path.getString}`: {e}"

/-- A balanced `.leaf`/`.branch` literal over `xs`, as an `Expr` of type `RArray ty`. -/
private def rarrayExpr (path : StrLit) (ty : Expr) (xs : Array Expr) : TermElabM Expr := do
  if h : 0 < xs.size then
    return (RArray.ofFn (fun i => xs[i]) h).toExpr ty id
  else
    throwErrorAt path "`{path.getString}` is empty"

/-- The half-open range of entries one module takes from a data file. -/
syntax entrySlice := " entries " num " to " num

/-- `js[lo:hi)`, or all of `js` if no slice is given. Tables are split across modules for the
code generator's sake: compiling a `List Nat` literal is superlinear in its size. -/
private def sliceOf (path : StrLit) (js : Array Json) : Option (TSyntax ``entrySlice) →
    TermElabM (Array Json)
  | none => return js
  | some s => do
    let `(entrySlice| entries $lo to $hi) := s | throwUnsupportedSyntax
    let (lo, hi) := (lo.getNat, hi.getNat)
    unless lo ≤ hi && hi ≤ js.size do
      throwErrorAt s "`{path.getString}` has {js.size} entries, so {lo} to {hi} is out of range"
    return js.extract lo hi

/-- The `Nat` with exactly the bits in `xs` set. -/
private def bitsetOf (xs : Array Nat) : Nat := xs.foldl (fun acc i => acc ||| (1 <<< i)) 0

/-- Read a JSON array of arrays of bit positions as bitsets. -/
private def bitsetRows (path : StrLit) (js : Array Json) : TermElabM (Array Nat) :=
  js.mapM fun j => do
    let .ok row := j.getArr? | throwErrorAt path "`{path.getString}`: entry is not a list"
    return bitsetOf (← row.mapM (toNat path))

/-- `loadNatTable% "f.json" h` is the `RArray Nat` holding the JSON array of naturals in
`f.json`, whose path is relative to the directory of the file being elaborated and whose
contents must hash to `h`. -/
elab "loadNatTable% " path:str hash:num : term => do
  let js ← parseArray path (← readTable path hash.getNat)
  rarrayExpr path (.const ``Nat []) (← js.mapM fun j => return mkRawNatLit (← toNat path j))

/-- `loadNatListTable% "f.json" h` is the same for a JSON array of arrays of naturals, giving an
`RArray (List Nat)`. A trailing `entries lo to hi` takes only that half-open range, so one file
can back several modules. -/
elab "loadNatListTable% " path:str hash:num slice:(entrySlice)? : term => do
  let js ← sliceOf path (← parseArray path (← readTable path hash.getNat)) slice
  let rows ← js.mapM fun j => do
    let .ok row := j.getArr? | throwErrorAt path "`{path.getString}`: entry is not a list"
    return natListExpr (← row.mapM (toNat path))
  rarrayExpr path (mkApp (.const ``List [0]) (.const ``Nat [])) rows

/-- `loadBitsetTable% "f.json" h` reads an array of arrays of *bit positions* and gives the
`RArray Nat` of the corresponding bitsets. The tables it is used for are sparse -- `reaches`
and `reachedBy` average 21 set bits out of 1415 -- so positions are smaller and more legible
than the number they denote. -/
elab "loadBitsetTable% " path:str hash:num : term => do
  let js ← parseArray path (← readTable path hash.getNat)
  let rows ← bitsetRows path js
  rarrayExpr path (.const ``Nat []) (rows.map mkRawNatLit)

/-- `loadUnionTable% "f.json" h "g.json" h'` reads an array of arrays of *row indices into
`g.json`*, and gives the `RArray Nat` whose entry `i` is the union of the rows `f.json` names.

`fmask k` is by definition `⋃ reachedBy[scc b]` over the laws witness `k` refutes, so naming
those rows says what the entry is rather than restating it. `checkFmask` re-derives it in the
kernel either way. -/
elab "loadUnionTable% " path:str hash:num src:str srcHash:num : term => do
  let base ← bitsetRows src (← parseArray src (← readTable src srcHash.getNat))
  let js ← parseArray path (← readTable path hash.getNat)
  let rows ← js.mapM fun j => do
    let .ok row := j.getArr? | throwErrorAt path "`{path.getString}`: entry is not a list"
    let mut acc := 0
    for e in row do
      let i ← toNat path e
      unless i < base.size do
        throwErrorAt path "`{path.getString}` names row {i} of `{src.getString}`, which has \
          only {base.size}"
      acc := acc ||| base[i]!
    return mkRawNatLit acc
  rarrayExpr path (.const ``Nat []) rows

/-! ## The proof-carrying tables

These cite theorems by name. A name that does not resolve is an error; one that resolves to the
wrong theorem fails to typecheck, since the indices stored beside it appear in the type the
kernel checks the proof against. -/

/-- Resolve a cited theorem, with an error that says where the citation came from. -/
private def factConst (path : StrLit) (n : Name) : TermElabM Expr := do
  let some info := (← getEnv).find? n
    | throwErrorAt path "`{path.getString}` cites `{n}`, which does not exist -- is the module \
        that proves it imported by this one?"
  unless info.levelParams.isEmpty do
    throwErrorAt path "`{n}` is universe-polymorphic, but the certificate is stated at `Type 0`"
  return .const n []

/-- `[i, j, "thm"]` rows as `mk i j thm`, the shape both `PosFact` and `DualFact` have. -/
private def indexedFactRows (path : StrLit) (mk : Name) (js : Array Json) :
    TermElabM (Array Expr) :=
  js.mapM fun j => do
    let .ok row := j.getArr? | throwErrorAt path "`{path.getString}`: entry is not a triple"
    unless row.size == 3 do
      throwErrorAt path "`{path.getString}`: entry is not `[i, j, \"thm\"]`"
    let .ok nm := row[2]!.getStr?
      | throwErrorAt path "`{path.getString}`: third field is not a theorem name"
    return mkApp3 (.const mk []) (mkRawNatLit (← toNat path row[0]!))
      (mkRawNatLit (← toNat path row[1]!)) (← factConst path (.mkSimple nm))

/-- `loadPosTable% "f.json" h` reads `[hyp, conc, "Law{a}_implies_Law{b}"]` rows as `PosFact`s. -/
elab "loadPosTable% " path:str hash:num slice:(entrySlice)? : term => do
  let js ← sliceOf path (← parseArray path (← readTable path hash.getNat)) slice
  rarrayExpr path (.const ``PosFact []) (← indexedFactRows path ``PosFact.mk js)

/-- `loadDualTable% "f.json" h` reads `[law, dual, "dual_{n}"]` rows as `DualFact`s. -/
elab "loadDualTable% " path:str hash:num slice:(entrySlice)? : term => do
  let js ← sliceOf path (← parseArray path (← readTable path hash.getNat)) slice
  rarrayExpr path (.const ``DualFact []) (← indexedFactRows path ``DualFact.mk js)

/-- `decide!`'s proof term for a closed decidable proposition: hand the kernel a
`decide p = true` to evaluate, without evaluating it here as well. -/
private def decideProof (p : Expr) : TermElabM Expr := do
  let inst := (← Meta.mkDecide p).appArg!
  return mkApp3 (.const ``of_decide_eq_true []) p inst (← Meta.mkEqRefl (toExpr true))

/-- `loadNegTable% "f.json" h` reads the model witnesses.

An entry is `{"sat": [...], "ref": [...], "thm": [...]}`, where `thm` names the `Facts` theorem
it cites, which `factsProof` restates over `Law.MagmaLaw ℕ`. The name is given as its
components rather than a dotted string, because a `Facts` theorem's name has spaces in it and
may or may not be namespaced — `["ThreeC2", "Fact2"]` and
`["Facts from All4x4Tables [[0,1],[1,0]]"]` are both real.

An entry that also has `"dualOf"` stores the *dual* of what its theorem proves, and `dualOf`
gives the lists the theorem is actually about; `negFact_dual_table` bridges the two. Its four
side conditions are read off the type of the partial application rather than built by hand. -/
elab "loadNegTable% " path:str hash:num slice:(entrySlice)? : term => do
  let js ← sliceOf path (← parseArray path (← readTable path hash.getNat)) slice
  -- `dualtable_ok`'s statement fixes both implicit arguments of `negFact_dual_table`. It is
  -- downstream of this module, so it is named unchecked and resolved at elaboration.
  let okName := `EndToEnd.dualtable_ok
  let mut dual : Option (Expr × Expr × Expr) := none
  let jsonList (j : Json) (k : String) : TermElabM Expr := do
    let .ok v := j.getObjVal? k
      | throwErrorAt path "`{path.getString}`: entry has no `{k}` field"
    let .ok arr := v.getArr? | throwErrorAt path "`{path.getString}`: `{k}` is not a list"
    return natListExpr (← arr.mapM (toNat path))
  let mut rows := Array.mkEmpty js.size
  for j in js do
    let sat ← jsonList j "sat"
    let ref ← jsonList j "ref"
    let .ok parts := (j.getObjVal? "thm").toOption.getD .null |>.getArr?
      | throwErrorAt path "`{path.getString}`: entry has no `thm` name components"
    let mut nm := Name.anonymous
    for c in parts do
      let .ok cs := c.getStr?
        | throwErrorAt path "`{path.getString}`: `thm` component is not a string"
      nm := nm.str cs
    let fact ← factsProof nm
    let proof ← match (j.getObjVal? "dualOf").toOption with
      | none => pure fact
      | some d =>
        let (hdt, dt, numEq) ← match dual with
          | some x => pure x
          | none =>
            let ok ← factConst path okName
            let args := (← Meta.inferType ok).getAppArgs
            let some lhs := args[1]? | throwErrorAt path "`{okName}` is not an equation"
            let dargs := lhs.getAppArgs
            unless lhs.isAppOf ``checkDualTable && dargs.size == 2 do
              throwErrorAt path "`{okName}` does not state `checkDualTable _ _ = true`"
            let x := (ok, dargs[0]!, dargs[1]!)
            dual := some x
            pure x
        let mut e := mkAppN (.const ``negFact_dual_table [])
          #[dt, numEq, hdt, ← jsonList d "sat", ← jsonList d "ref", sat, ref]
        -- the four side conditions, in the order `negFact_dual_table` asks for them
        for _ in [0:4] do
          let .forallE _ p body _ ← Meta.whnf (← Meta.inferType e)
            | throwErrorAt path "`negFact_dual_table` has fewer arguments than expected"
          let prf ← decideProof p
          e := mkApp e prf
          _ := body
        pure (mkApp e fact)
    rows := rows.push (mkApp3 (.const ``NegFact.mk []) sat ref proof)
  rarrayExpr path (.const ``NegFact []) rows

end EndToEnd
