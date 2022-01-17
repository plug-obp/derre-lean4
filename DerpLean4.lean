-- http://www.ucombinator.org/projects/parsing/

variable {T: Type u} [DecidableEq T]

inductive rexp T :=
| epty : rexp T                       -- empty set
| epsilon : rexp T                    -- empty string
| token : T → rexp T                   -- terminal token
| union : rexp T → rexp T → rexp T         -- language union (alternative)
| concatenation : rexp T → rexp T → rexp T  -- concatenation
| star : rexp T → rexp T                  -- repetition

open rexp
notation:100 "Φ" => epty
notation:65 "ε" => epsilon
prefix:80   "τ" => token
infix:65 "⋃" => union
infix:70 "⋅" => concatenation
postfix:65  "★" => star

def nullable? : rexp T → Bool 
| Φ => false
| ε => true
| τ c => false
| (e₁ ⋃ e₂) => nullable? e₁ ∨ nullable? e₂
| (e₁ ⋅ e₂) => nullable? e₁ ∧ nullable? e₂
| e ★ => true

def δ (e : rexp T) : rexp T :=
if nullable? e then ε else Φ

def D (x:T) : rexp T → rexp T
| Φ         => Φ
| ε         => Φ
| τ c       => if (c = x) then ε else Φ
| (e₁ ⋃ e₂) => (D x e₁) ⋃ (D x e₂)
| (e₁ ⋅ e₂) => ((δ e₁) ⋅ D x e₂) ⋃ ( D x e₁ ⋅ e₂)
| (e ★)     => (D x e) ⋅ (e ★)

def recognizes? (L : rexp T) : List T → Bool
| [] => nullable? L
| c::w => recognizes? (D c L) w

#check (τ 'c')

set_option maxRecDepth 10000
#reduce recognizes? (τ 'c' ⋅ τ 'y') ['c' 'y']