import «RegEx»
import «SoupL».expressions_semantics
import «SoupL».pieces_semantics

open soup.expressions.syntx
open soup.expressions.semantics
open soup.syntx soup.semantics
open regex.syntx
open regex.semantics.brzozowski
open regex.semantics.brzozowski.gamine

instance : HasEval (Expression) (Environment)
  where eval := λ e ρ =>
    let isDeadlock: Option Bool :=
      (lookup "code" ρ).bind
        (λ code =>
          match code with
          | .vcode code =>
            some $ ((SoupSemantics code).actions ρ).length = 0
          | _ => none
        )
    let ρ :=
      match isDeadlock with
      | some isDeadlock => ("deadlock", .vb isDeadlock)::ρ
      | none => ρ
    match evaluate e ρ with
    | some (.vb True) => True
    | _ => False

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
                            λ (_, c₂) => nullable? c₂.e
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
  let endConfiguration := run₁ deterministic
  match (endConfiguration.bind λ c => c.found) with
  | some _ => False
  | none => True

unsafe def soup_regex_check?
  (r: RExp Expression)
  (s: Soup)
:= regex_check? r $ SoupSemantics s
