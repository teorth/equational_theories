import Lean
import equational_theories.FreeMagma
#check FreeMagma.Leaf
open Lean Elab Parser Meta

declare_syntax_cat magma_term

syntax ident:magma_term

syntax magma_term "∘" magma_term : magma_term
syntax "(" magma_term ")" : magma_term

declare_syntax_cat magma_law

syntax magma_term "=" magma_term : magma_law

structure MagmaLaw (α : Type) where
  lhs : FreeMagma α
  rhs : FreeMagma α

partial def elabMagmaTerm : Syntax → MetaM Expr
  | `(magma_term| $n:ident) => do

    mkAppM ``FreeMagma.Leaf #[mkStrLit n.getId.toString]
  | `(magma_term| $l:magma_term ∘ $r:magma_term) => do
    mkAppM ``FreeMagma.Fork #[← elabMagmaTerm l, ← elabMagmaTerm r]
  | `(magma_term| ($t:magma_term)) => elabMagmaTerm t
  | _ => throwUnsupportedSyntax

partial def elabMagmaLaw : Syntax → MetaM Expr
  | `(magma_law| $l:magma_term = $r:magma_term) => do
    mkAppM ``Prod.mk #[← elabMagmaTerm l, ← elabMagmaTerm r]
  | _ => throwUnsupportedSyntax


elab "law{" l:magma_law "}" : term => elabMagmaLaw l

#check law{x ∘ y ∘ z = z}
