-- http://www.ucombinator.org/projects/parsing/
import «Gamine»
import «LString»

namespace regex
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


def nullable? : RExp T → Bool
| Φ => false
| ε => true
| τ _ => false
| (e₁ ⋃  e₂) => nullable? e₁ ∨ nullable? e₂
| (e₁ ⋅ e₂) => nullable? e₁ ∧ nullable? e₂
| _ ★ => true

def δ (e : RExp T) : RExp T :=
  if nullable? e then ε else Φ

def inhabited? : RExp T → Bool
| Φ => false
| ε => true
| τ _ => true
| (e₁ ⋃  e₂) => inhabited? e₁ ∨ inhabited? e₂
| (e₁ ⋅ e₂) => inhabited? e₁ ∧ inhabited? e₂
| _ ★ => true

universe v w t
class HasEval (α β: Type*) := (eval: α → β → Bool)

/--
  **Brzozowski** derivative
-/
def D {T α:Type*}[DecidableEq T][h: HasEval T α] (i: α) : RExp T → RExp T
| Φ         => Φ
| ε         => Φ
| τ c       => if (h.eval c i) then ε else Φ
| (e₁ ⋃ e₂) => (D i e₁) ⋃ₛ (D i e₂)
| (e₁ ⋅ e₂) => ((δ e₁) ⋅ₛ D i e₂) ⋃ₛ ( D i e₁ ⋅ₛ e₂)
| (e ★)     => (D i e) ⋅ₛ (e ★ₛ)

def D₀ {T α:Type*}[h: HasEval T α] (i: α) : RExp T → RExp T
| Φ         => Φ
| ε         => Φ
| τ c       => if (h.eval c i) then ε else Φ
| (e₁ ⋃ e₂) => (D₀ i e₁) ⋃ (D₀ i e₂)
| (e₁ ⋅ e₂) => ((δ e₁) ⋅ D₀ i e₂) ⋃ ( D₀ i e₁ ⋅ e₂)
| (e ★)     => (D₀ i e) ⋅ (e ★)

instance : HasEval T T where eval := (λ t i => t = i)
def D₁ (x:T) (e: RExp T) : RExp T :=
  D x e


def recognizes (L : RExp T) : List T → Bool
| [] => nullable? L
| c::w => recognizes (D c L) w

def name := τ "name" ⋅ τ "surname"

def address := τ "addr"

def nameoraddress := name ⋃ address

#reduce recognizes nameoraddress ["name", "surname"]

-- #check (τ 'c')

-- def x : String := "toto"

-- #check "cz"
-- #check String.mk ['c', 'z']

-- set_option maxRecDepth 10000
-- #reduce recognizes? (τ 'c' ⋅ τ 'y' ⋅ τ 'c' ⋅ τ 'y') ['c', 'z']
-- #reduce recognizes? (τ 1 ⋅ τ 2 ⋅ τ 3 ⋅ τ 4) [1, 2, 3, 4]

namespace Gamine


structure REConfig (T: Type*) :=
  (e: RExp T)
deriving DecidableEq, Inhabited

instance {T: Type*} [ToString T]: ToString (REConfig T) where toString := λ c =>
  s!"{c.e}"

def derivativeT (T V: Type*) := (i : V) → (e : RExp T) → RExp T

instance{T V: Type*}: ToString $ derivativeT T V where toString := λ _ => "derT"

def injectBrzozowski (T V: Type*)[DecidableEq T][ToString T] (e: RExp T) [HasEval T (Option V)] :
  DeterministicInputSemantics (REConfig T) (derivativeT T (Option V)) V:=
{
  initial := Option.some ⟨ e ⟩
  action  := λ _ c => if (inhabited? c.e) then Option.some D else Option.none
  execute := λ d i c => Option.some ⟨ d i c.e ⟩
}

def injectBrzozowski₀ (T V: Type*) (e: RExp T) [HasEval T V] :
  DeterministicInputSemantics₀ (REConfig T) (derivativeT T V) V:=
{
  initial := Option.some ⟨ e ⟩
  action  := λ _ c => if (inhabited? c.e) then Option.some D₀ else Option.none
  execute := λ d i c => Option.some ⟨ d i c.e ⟩
}

def injectBrzozowski₁ (T V: Type*) [DecidableEq T] (e: RExp T) [HasEval T V] :
  DeterministicInputSemantics₀ (REConfig T) (derivativeT T V) V:=
{
  initial := Option.some ⟨ e ⟩
  action  := λ _ c => if (inhabited? c.e) then Option.some D else Option.none
  execute := λ d i c => Option.some ⟨ d i c.e ⟩
}

end Gamine

instance : ToString (Gamine.derivativeT Char (Option Config)) where toString := λ _ => "D"

instance : HasEval Char (Option Config) where eval := λ t c => match c with
  | none => false
  | some c => t = c.s.data[c.index]!

unsafe def recognizes? (r: RExp Char) (s: String) : Bool :=
  let stringSemantics := inject s
  let rExpSemantics   := Gamine.injectBrzozowski Char Config r
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
