import Mathlib.Tactic.Basic
import Lean
namespace regex.syntx
variable {T: Type*} [DecidableEq T] [Repr T] [ToString T]

inductive RExp T :=
| empty                         -- empty set
| epsilon                       -- empty string
| token         (v: T)          -- terminal token
| union         (e₁ e₂: RExp T) -- language union (alternative)
| concatenation (e₁ e₂: RExp T) -- concatenation
| star          (e: RExp T)     -- repetition
deriving DecidableEq, Inhabited

-- section
open RExp
def union_smart (e₁ e₂: RExp T) : RExp T :=
match e₁, e₂ with
| empty, e | e, empty => e
| e₁, e₂ => if e₁ = e₂ then e₁ else RExp.union e₁ e₂

def concatenation_smart (e₁ e₂: RExp T) : RExp T :=
match e₁, e₂ with
| empty, _ | _, empty => empty
| epsilon, e₂ => e₂
| e₁, epsilon => e₁
| e₁, e₂ => RExp.concatenation e₁ e₂

def star_smart : RExp T → RExp T
| RExp.star e => RExp.star e
| e => RExp.star e
-- end

notation:100 "∅" => RExp.empty
notation:100 "Φ" => RExp.empty
notation:65  "ε" => RExp.epsilon
prefix:80    "τ" => RExp.token
infixl:65    " ⋃ " => union
infixl:65    " ⋃ₛ " => union_smart
infixl:70    "∘" => concatenation
infixl:70    "⋅" => concatenation
infixl:70    "∘ₛ" => concatenation_smart
postfix:65   "★" => star
postfix:65   "★ₛ" => star_smart

def toString : RExp T → String
  | Φ => "∅"
  | ε  => "ε"
  | τ t => s!"τ({t})"
  | e₁ ⋃ e₂ => s!"{toString e₁} ⋃ {toString e₂}"
  | e₁ ⋅ e₂ => s!"{toString e₁} ∘  {toString e₂}"
  | e ★ => s!"{toString e}*"

instance : ToString (RExp T) where toString := toString

namespace embedding
open Lean Elab Meta
open Lean.Elab.Term
open regex.syntx

declare_syntax_cat        regex
syntax "∅"              : regex -- empty set
syntax "ε"              : regex -- empty string
syntax "τ " term         : regex -- terminal token
syntax regex "∪" regex  : regex -- language union (alternative)
syntax regex "|" regex  : regex -- language union (alternative)
syntax regex "∘" regex  : regex -- concatenation
syntax regex "*"        : regex -- repetition
syntax "(" regex ")"    : regex -- parens

-- open Lean.Elab.Command.elabDeclaration

-- #check RExp String
 #check ((RExp.token) '3': RExp Char)

partial def elab_regex (ty: Syntax) (re: Syntax) : TermElabM Expr :=
do
let typ ← Term.elabTerm ty $ Expr.sort (.succ (.param `u))
match re with
| `(regex| ∅ ) => mkAppOptM ``RExp.empty #[ typ ]
| `(regex| ε ) => mkAppOptM ``RExp.epsilon #[ typ ]
| `(regex| τ $t:term ) => do
  let term ← Term.elabTerm t typ
  mkAppM ``RExp.token #[ term ]
| `(regex| $e₁:regex | $e₂:regex )
| `(regex| $e₁:regex ∪ $e₂:regex ) => do
  let re₁ ← elab_regex ty e₁
  let re₂ ← elab_regex ty e₂
  mkAppM ``RExp.union #[ re₁, re₂ ]
| `(regex| $e₁:regex ∘ $e₂:regex ) => do
  let re₁ ← elab_regex ty e₁
  let re₂ ← elab_regex ty e₂
  mkAppM ``RExp.concatenation #[ re₁, re₂ ]
| `(regex| $e:regex *) => do
  let re ← elab_regex ty e
  mkAppM ``RExp.star #[ re ]
| `(regex| ($e:regex)) => elab_regex ty e
| _ => Lean.Elab.throwUnsupportedSyntax

elab "[regex:" ty:term "|" e:regex "]": term => elab_regex ty e

#reduce Expr.const `Array.map [.zero, .zero]

#reduce Expr.const `Array.map

def empty := [regex: Char | ∅ ]
#check empty
#reduce empty

def eps := [regex: String | ε ]
#check eps
#reduce eps

#check (@RExp.token Char ) '|'

def tc := [regex:Prop| τ (1=2) ]
#check tc
#reduce tc

def t2:= [regex: Nat| (τ 2) ]
#check t2
#reduce t2

def tx:= [regex: Char| (τ 'x') ]
#check tx
-- #reduce tx


def t3:= [regex:Bool | (τ true)* ]
#check t3
#reduce t3

def t4:= [regex:Nat| (τ 2) | ε ∪ ∅ ∘ (τ 34)]
#reduce t4

end embedding

end regex.syntx
