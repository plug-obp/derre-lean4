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



unsafe def recognizes? (r: RExp Char) (s: String) : Bool :=
  let stringSemantics := LStringSemantics s
  let rExpSemantics   := BrzozowskiSemantics Char Config r
  let composition := stringSemantics ⨂ rExpSemantics
  let final := run composition
  match final with
  | none => nullable? r
  | some c => nullable? c.2.e

instance: ToString (ActionOrInit A × derivativeT T C) where toString := λ _ => "action"
def regex_check_bridge[ToString C]
  [ToString T]
  [DecidableEq T] [DecidableEq C] [Inhabited T] [Inhabited C]
  [HasEval T C]
  (r: RExp T)
  (s: Semantics C A) :=
  let rExpSemantics  := BrzozowskiSemantics₁ T C r
  let inputSemantics := DeterministicInput2InputSemantics rExpSemantics
  let composition    := SynchronousComposition s inputSemantics
  let accepting      := AcceptingSemantics composition
                            λ (c₁, c₂) =>
                              match c₁ with
                              | none => false
                              | some _ =>
                              dbg_trace s!" {c₁}, {c₂.e} is nullable = {nullable? c₂.e}"
                              nullable? c₂.e
  let accepting      := TracingSemantics accepting
  let deterministic  := BFSSearchSemantics accepting λ (atEnd, _) => atEnd
  deterministic

unsafe def regex_check?
  [ToString C]
  [ToString T]
  [DecidableEq T] [DecidableEq C] [Inhabited T] [Inhabited C]
  [HasEval T C]
  (r: RExp T)
  (s: Semantics C A) : Bool :=
  let deterministic := regex_check_bridge r s
  let endConfiguration := run deterministic
  dbg_trace s!"end end end {endConfiguration}"
  match (endConfiguration.bind λ c => c.found) with
  | some _ => False
  | none => True

unsafe def string_regex_check?
  (r: RExp Char)
  (s: String)
:=
let stringSem := LStringSemantics s
let semantics := DeterministicSemantics2Semantics stringSem
regex_check? r semantics


#eval recognizes? (τ 'a' ⋅ τ 'b') "" = false
#eval recognizes? (τ 'a' ⋅ τ 'b') "ab" = true
#eval recognizes? (τ 'a' ⋅ τ 'b') "abcdef" = false
#eval recognizes? (τ 'a' ★) "" = true
#eval recognizes? ((((τ 'x' ★) ⋅ (τ 'x' ★)) ★) ⋅ τ 'y') "xxxxy" = true
#eval recognizes? ((((τ 'x' ★) ⋅ (τ 'x' ★)) ★) ⋅ τ 'y') "xxxxx" = false
end regex
