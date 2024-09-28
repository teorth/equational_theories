import equational_theories.ParseImplications

unsafe def main (_args : List String) : IO Unit := do
  println! (Lean.toJson (← generateOutput)).pretty
