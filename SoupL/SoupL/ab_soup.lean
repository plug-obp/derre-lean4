import «SoupL».checker
import «RegEx»
import «SoupL».expressions_semantics

open soup.expressions.syntx
open soup.expressions.semantics
open regex.semantics.brzozowski

unsafe def check? := soup_regex_check?

def alicebob₀ := [soup|
  alicebob₀
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
def exclusion:= (τ (notBothIn) ★) ⋅ (τ bothIn) -- simple embedding, might with other syntax
def exclusion₁ := [regex: Expression | (τ notBothIn) * ∘ τ bothIn] -- isolated embedding

-- mutual exclusion doesn't pass on alicebob₀
#eval False =  check? exclusion₁ alicebob₀

-- a regular expression that forces full state-space exploration
#eval True = check? ((τ [exp| true]★) ⋅ τ [exp| false]) alicebob₀

def alicebob₁ := [soup|
  alicebob₁
  vars a=0 b=0 fA=false fB=false;

  | a_i2w   ≜ [a=0      ]/ a←1; fA←true ;
  | b_i2w   ≜ [b=0      ]/ b←1; fB←true ;
  | a_w2c   ≜ [a=1 ∧ ¬fB]/ a←2 ;
  | b_w2c   ≜ [b=1 ∧ ¬fA]/ b←2 ;
  | a_c2i   ≜ [a=2      ]/ a←0; fA←false ;
  | b_c2i   ≜ [b=2      ]/ b←0; fB←false ;
]
-- mutual exclusion passes on alicebob₁
#eval True = check? exclusion alicebob₁

--deadlock verification doesn't pass on alicebob₁
#eval False = check? ((τ [exp| true]★) ⋅ τ [exp| deadlock]) alicebob₁

def alicebob₂ := [soup|
  alicebob₂
  vars a=0 b=0 fA=false fB=false;

  | a_i2w   ≜ [a=0      ]/ a←1; fA←true ;
  | b_i2w   ≜ [b=0      ]/ b←1; fB←true ;
  | a_w2c   ≜ [a=1 ∧ ¬fB]/ a←2 ;
  | b_w2c   ≜ [b=1 ∧ ¬fA]/ b←2 ;
  | b_w2i   ≜ [(b=1)∧ fA]/ b←0; fB←false ;
  | a_c2i   ≜ [a=2      ]/ a←0; fA←false ;
  | b_c2i   ≜ [b=2      ]/ b←0; fB←false ;
]
-- mutual exclusion passes on alicebob₁
#eval True = check? exclusion alicebob₂

--deadlock verification doesn't pass on alicebob₁
#eval True = check? ((τ [exp| true]★) ⋅ τ [exp| deadlock]) alicebob₂


/-!
 some tests
-/

open Value
def e := [("a", vn 1), ("b", vn 1), ("fA", vb True), ("fB", vb True)]
def s₂ := soup.semantics.SoupSemantics alicebob₂

def ex := [exp|  (b=1) ∧ fA]

#eval evaluate ex e

#eval s₂.actions e

def ss := soup.semantics.SoupSemantics alicebob₀
#eval ss.initial
#eval ss.initial.bind λ ρ => ss.actions ρ
#eval ss.initial.bind λ ρ => (ss.actions ρ).bind λ p => ss.execute p ρ
#eval ss.initial.bind
        λ ρ => (ss.actions ρ).bind λ p => (ss.execute p ρ).bind
        λ ρ => (ss.actions ρ).bind λ p => (ss.execute p ρ).bind
        λ ρ => (ss.actions ρ).bind λ p => ss.execute p ρ

def env0: Environment := ([("a", Value.vn 0), ("b", Value.vn 0)]: Environment)
#eval D env0 (τ notBothIn)
#eval D env0 exclusion

def env1: Environment := ([("a", Value.vn 2), ("b", Value.vn 2)]: Environment)
#eval (D₀ env1 exclusion)
#eval nullable? (D₀ env1 exclusion)
