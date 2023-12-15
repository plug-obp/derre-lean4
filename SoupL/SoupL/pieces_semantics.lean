import Lean
import «SoupL».expressions
import «SoupL».expressions_semantics
import «SoupL».statements
import «SoupL».statements_semantics
import «SoupL».pieces
import «Gamine»

namespace soup

namespace semantics
open soup.syntx
open soup.expressions.semantics
open soup.statements.semantics

def mkInitialEnvironment (s: Soup) : Environment :=
("code", .vcode s)::
s.vars.foldr
  (λ (var, exp) ρ =>
    match evaluate exp ρ with
    | none => ρ
    | some dv => (var, dv)::ρ)
  ([])

def SoupSemantics (s : Soup) : Semantics Environment Piece :=
{
  initial := [ mkInitialEnvironment s ]
  actions := λ ρ =>
    s.pieces.filter λ p =>
      match evaluate p.guard ρ with
      | some (.vb True) => True
      | _ => False
  execute := λ piece ρ =>
    match execute piece.effect ρ with
    | none => []
    | some ρ₁ => [ρ₁]
}

def xx := [soup|
  my_soup
  vars a=2;

  | piece1   ≜ [a=2]/ a := a + 1 ;
]

def ss := SoupSemantics xx

#reduce xx
#eval ss.initial
#eval ss.initial.bind λ ρ => ss.actions ρ
#eval ss.initial.bind λ ρ => (ss.actions ρ).bind λ p => ss.execute p ρ

end semantics

end soup
