import «Gamine»
import «RegEx»
import «SoupL».expressions
import «SoupL».expressions_semantics
import «SoupL».pieces
import «SoupL».pieces_semantics

open soup.expressions.syntx
open soup.expressions.semantics

instance : regex.HasEval (Expression) (Environment)
  where eval := λ e ρ =>
    let isDeadlock: Option Bool :=
      (lookup "code" ρ).bind
        (λ code =>
          match code with
          | .vcode code => some $ ((soup.semantics.SoupSemantics code).actions ρ).length = 0
          | _ => none
        )
    let ρ :=
      match isDeadlock with
      | some isDeadlock => ("deadlock", .vb isDeadlock)::ρ
      | none => ρ
    match evaluate e ρ with
    | some (.vb True) => True
    | _ => False

instance: ToString (ActionOrInit A × regex.Gamine.derivativeT T C) where toString := λ _ => "action"

unsafe def check?
  [ToString C]
  [ToString T]
  [DecidableEq T] [DecidableEq C] [Inhabited T] [Inhabited C]
  [regex.HasEval T C]
  (r: regex.RExp T)
  (s: Semantics C A) :=
  let rExpSemantics  := regex.Gamine.BrzozowskiSemantics₁ T C r
  let inputSemantics := DeterministicInput2InputSemantics rExpSemantics
  let composition    := SynchronousComposition s inputSemantics
  let accepting      := AcceptingSemantics composition
                            λ (_, c₂) => regex.nullable? c₂.e
  let deterministic  := BFSTraversal accepting λ (atEnd, _) => atEnd
  run deterministic

def alicebob₀ := [soup|
  my_soup
  vars a=0 b=0;

  | a_i2w   ≜ [a=0]/a←1 ;
  | b_i2w   ≜ [b=0]/b←1 ;
  | a_w2c   ≜ [a=1]/a←2 ;
  | b_w2c   ≜ [b=1]/b←2 ;
  | a_c2i   ≜ [a=2]/a←0 ;
  | b_c2i   ≜ [b=2]/b←0 ;
]

def notBothIn := [exp| ¬((a = 2) ∧ (b = 2))]
def bothIn :=    [exp|   (a = 2) ∧ (b = 2) ]
def exclusion:= (τ (notBothIn) ★) ⋅ (τ bothIn)

-- mutual exclusion doesn't pass on alicebob₀
#eval check? exclusion (soup.semantics.SoupSemantics alicebob₀)

-- a regular expression that forces full state-space exploration
#eval check? ((τ [exp| true]★) ⋅ τ [exp| false]) (soup.semantics.SoupSemantics alicebob₀)


def alicebob₁ := [soup|
  my_soup
  vars a=0 b=0 fA=false fB=false;

  | a_i2w   ≜ [a=0      ]/ a←1; fA←true ;
  | b_i2w   ≜ [b=0      ]/ b←1; fB←true ;
  | a_w2c   ≜ [a=1 ∧ ¬fB]/ a←2 ;
  | b_w2c   ≜ [b=1 ∧ ¬fA]/ b←2 ;
  | a_c2i   ≜ [a=2      ]/ a←0; fA←false ;
  | b_c2i   ≜ [b=2      ]/ b←0; fB←false ;
]
-- mutual exclusion passes on alicebob₁
#eval check? exclusion (soup.semantics.SoupSemantics alicebob₁)

--deadlock verification doesn't pass on alicebob₁
#eval check? ((τ [exp| true]★) ⋅ τ [exp| deadlock]) (soup.semantics.SoupSemantics alicebob₁)

/-!
 some tests
-/

def ss := soup.semantics.SoupSemantics alicebob₀
#eval ss.initial
#eval ss.initial.bind λ ρ => ss.actions ρ
#eval ss.initial.bind λ ρ => (ss.actions ρ).bind λ p => ss.execute p ρ
#eval ss.initial.bind
        λ ρ => (ss.actions ρ).bind λ p => (ss.execute p ρ).bind
        λ ρ => (ss.actions ρ).bind λ p => (ss.execute p ρ).bind
        λ ρ => (ss.actions ρ).bind λ p => ss.execute p ρ

def env0: Environment := ([("a", Value.vn 0), ("b", Value.vn 0)]: Environment)
#eval regex.D env0 (τ notBothIn)
#eval regex.D env0 exclusion

def env1: Environment := ([("a", Value.vn 2), ("b", Value.vn 2)]: Environment)
#eval (regex.D₀ env1 exclusion)
#eval regex.nullable? (regex.D₀ env1 exclusion)
