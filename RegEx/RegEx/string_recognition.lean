import «Gamine»
import «LString»
import «RegEx».syntax
import «RegEx».brzozowski

-- http://www.ucombinator.org/projects/parsing/

namespace regex
open regex.syntx
open regex.semantics.brzozowski
open regex.semantics.brzozowski.gamine

instance : ToString (derivativeT Char (Option Config)) where toString := λ _ => "D"

instance : HasEval Char (Option Config) where eval := λ t c => match c with
  | none => false
  | some c => t = c.s.data[c.index]!

unsafe def recognizes? (r: RExp Char) (s: String) : Bool :=
  let stringSemantics := LStringSemantics s
  let rExpSemantics   := BrzozowskiSemantics Char Config r
  let composition := stringSemantics ⨂ rExpSemantics
  let final := run composition
  match final with
  | none => nullable? r
  | some c => nullable? c.2.e

#eval recognizes? (τ 'a' ⋅ τ 'b') "" = false
#eval recognizes? (τ 'a' ⋅ τ 'b') "ab" = true
#eval recognizes? (τ 'a' ⋅ τ 'b') "abcdef" = false
#eval recognizes? (τ 'a' ★) "" = true
#eval recognizes? ((((τ 'x' ★) ⋅ (τ 'x' ★)) ★) ⋅ τ 'y') "xxxxy" = true
#eval recognizes? ((((τ 'x' ★) ⋅ (τ 'x' ★)) ★) ⋅ τ 'y') "xxxxx" = false
end regex
