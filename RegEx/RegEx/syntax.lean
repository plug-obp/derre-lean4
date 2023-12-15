namespace regex
namespace syntx
variable {T: Type u} [DecidableEq T] [Repr T] [ToString T]

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

notation:100 "Φ" => RExp.empty
notation:65  "ε" => RExp.epsilon
prefix:80    "τ" => RExp.token
infixl:65    "⋃" => union
infixl:65    "⋃ₛ" => union_smart
infixl:70    "⋅" => concatenation
infixl:70    "⋅ₛ" => concatenation_smart
postfix:65   "★" => star
postfix:65   "★ₛ" => star_smart

def toString : RExp T → String
  | Φ => "Φ"
  | ε  => "ε"
  | τ t => s!"τ({t})"
  | e₁ ⋃ e₂ => s!"{toString e₁} ⋃ {toString e₂}"
  | e₁ ⋅ e₂ => s!"{toString e₁} ⋅ {toString e₂}"
  | e ★ => s!"{toString e}★"

instance : ToString (RExp T) where toString := toString
end syntx
end regex
