import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import equational_theories.EquationalResult

private def ofMatrix {n : Nat} [Inhabited (Fin n)]
  (table : Array (Array (Fin n))) (x y : Fin n) : Fin n :=
  table[x.val]![y.val]!


def Magma5_105173830064189634 : Magma (Fin 5) where op := memoFinOp (ofMatrix #[ #[4,1,0,2,3], #[0,3,1,4,2], #[3,4,2,1,0], #[1,2,3,0,4], #[2,0,4,3,1] ])

def Magma5_251973412367525970 : Magma (Fin 5) where op := memoFinOp (ofMatrix #[ #[0,4,3,2,1], #[3,1,4,0,2], #[1,0,2,4,3], #[4,2,1,3,0], #[2,3,0,1,4] ])

def Magma5_34939223192751922 : Magma (Fin 5) where op := memoFinOp (ofMatrix #[ #[2,4,1,0,3], #[0,1,2,3,4], #[4,0,3,1,2], #[3,2,0,4,1], #[1,3,4,2,0] ])

def Magma5_264961675455413970 : Magma (Fin 5) where op := memoFinOp (ofMatrix #[ #[0,4,3,1,2], #[2,1,4,0,3], #[1,3,2,4,0], #[4,2,0,3,1], #[3,0,1,2,4] ])

def Magma5_242073754161201490 : Magma (Fin 5) where op := memoFinOp (ofMatrix #[ #[0,3,4,1,2], #[4,1,3,2,0], #[1,0,2,4,3], #[2,4,0,3,1], #[3,2,1,0,4] ])

def Magma5_252013434551827410 : Magma (Fin 5) where op := memoFinOp (ofMatrix #[ #[0,2,1,4,3], #[4,1,3,2,0], #[3,4,2,0,1], #[1,0,4,3,2], #[2,3,0,1,4] ])

def Magma5_264980963810414610 : Magma (Fin 5) where op := memoFinOp (ofMatrix #[ #[0,2,4,1,3], #[2,1,3,4,0], #[4,3,2,0,1], #[1,4,0,3,2], #[3,0,1,2,4] ])

def Magma5_263836793931976210 : Magma (Fin 5) where op := memoFinOp (ofMatrix #[ #[0,2,3,4,1], #[2,1,4,0,3], #[3,4,2,1,0], #[4,0,1,3,2], #[1,3,0,2,4] ])

def Magma5_257697638618777170 : Magma (Fin 5) where op := memoFinOp (ofMatrix #[ #[0,4,1,2,3], #[3,1,0,4,2], #[4,3,2,0,1], #[1,2,4,3,0], #[2,0,3,1,4] ])

def Magma5_242095216745725970 : Magma (Fin 5) where op := memoFinOp (ofMatrix #[ #[0,4,3,2,1], #[2,1,0,4,3], #[4,3,2,1,0], #[1,0,4,3,2], #[3,2,1,0,4] ])

def Magma5_251629779747913490 : Magma (Fin 5) where op := memoFinOp (ofMatrix #[ #[0,3,4,2,1], #[2,1,3,4,0], #[1,4,2,0,3], #[4,0,1,3,2], #[3,2,0,1,4] ])

def Magma5_140226095066537986 : Magma (Fin 5) where op := memoFinOp (ofMatrix #[ #[1,2,4,3,0], #[2,3,1,0,4], #[4,1,0,2,3], #[3,0,2,4,1], #[0,4,3,1,2] ])
