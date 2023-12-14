import Lean
namespace soup
namespace expressions
namespace syntx

inductive Literal
  | n : Nat → Literal
  | b : Bool → Literal
deriving Inhabited, DecidableEq, Repr

def toStringLiteral: Literal → String
| .n v => s!"{v}"
| .b v => s!"{v}"
instance: ToString Literal where toString := toStringLiteral

inductive UnaryOperator
| not
deriving Inhabited, DecidableEq, Repr

inductive BinaryOperator
-- arithmetic
| plus
-- boolean
| and
-- relational
| eq
| leq
deriving Inhabited, DecidableEq, Repr

def toStringBinaryOperator: BinaryOperator → String
| .plus =>"+"
| .and => "∧"
| .eq => "="
| .leq => "<="
instance: ToString BinaryOperator where toString := toStringBinaryOperator

inductive Expression
| l : Literal → Expression
| ref : String → Expression
| u (operator: UnaryOperator) (e: Expression)
| bin (operator: BinaryOperator) (e₁ e₂: Expression)
deriving Inhabited, DecidableEq, Repr

def toString[ToString Literal] [ToString BinaryOperator]: Expression → String
| .l lit => s!"{lit}"
| .ref s => s!"{s}"
| .u _ e => s!"¬({toString e})"
| .bin op e₁ e₂ => s! "({toString e₁} {op} {toString e₂})"

instance: ToString Expression where toString := toString

namespace embedding
open Lean Elab Meta

/-
Elaborating Literals
-/
declare_syntax_cat  literal
syntax num        : literal
syntax "true"     : literal
syntax "false"    : literal

def elab_literal: Syntax → MetaM Expr
| `(literal| $n: num) => mkAppM ``Literal.n #[mkNatLit n.getNat]  -- TODO: how to get an int here?
| `(literal| true)    => mkAppM ``Literal.b #[.const ``Bool.true []]
| `(literal| false)   => mkAppM ``Literal.b #[.const ``Bool.false []]
| _ => Lean.Elab.throwUnsupportedSyntax

elab "test_elabLiteral " l:literal : term => elab_literal l

#reduce test_elabLiteral 4
-- #reduce test_elabLiteral true
-- #reduce test_elabLiteral false

/-
Elaborating Expressions
-/

-- Unary operators

declare_syntax_cat  unary_operator
syntax "not"      : unary_operator
syntax "¬"        : unary_operator
syntax "!"        : unary_operator

def elab_unary_operator: Syntax → MetaM Expr
| `(unary_operator| not) => return .const ``UnaryOperator.not []
| `(unary_operator| ¬) => return .const ``UnaryOperator.not []
| `(unary_operator| !) => return .const ``UnaryOperator.not []
| _ => Lean.Elab.throwUnsupportedSyntax

elab "test_elabUnary " l:unary_operator : term => elab_unary_operator l

-- #reduce test_elabUnary not
-- #reduce test_elabUnary !
-- #reduce test_elabUnary ¬

-- Binary operators

declare_syntax_cat  binary_operator
syntax "+"        : binary_operator
syntax "and"      : binary_operator
syntax "∧"        : binary_operator
syntax "<="       : binary_operator
syntax "≤"        : binary_operator
syntax "="        : binary_operator

def elab_binary_operator: Syntax → MetaM Expr
| `(binary_operator| +)   => return .const ``BinaryOperator.plus []
| `(binary_operator| and) => return .const ``BinaryOperator.and []
| `(binary_operator| ∧)   => return .const ``BinaryOperator.and []
| `(binary_operator| <=)  => return .const ``BinaryOperator.leq []
| `(binary_operator| ≤)   => return .const ``BinaryOperator.leq []
| `(binary_operator| =)   => return .const ``BinaryOperator.eq []
| _ => Lean.Elab.throwUnsupportedSyntax

elab "test_elabBinary " l:binary_operator : term => elab_binary_operator l

-- #reduce test_elabBinary +
-- #reduce test_elabBinary and
-- #reduce test_elabBinary ∧
-- #reduce test_elabBinary <=
-- #reduce test_elabBinary ≤
-- #reduce test_elabBinary =

-- Expressions

declare_syntax_cat                                expression
syntax literal                                  : expression
syntax ident                                    : expression
syntax unary_operator expression                : expression
syntax expression binary_operator expression    : expression
syntax "(" expression ")"                       : expression

partial def elab_expression: Syntax → MetaM Expr
| `(expression| $l:literal) => do
  let l ← elab_literal l
  mkAppM ``Expression.l #[l]
| `(expression| $i:ident) => mkAppM ``Expression.ref #[mkStrLit i.getId.toString]
| `(expression| $o:unary_operator $e:expression) => do
  let o ← elab_unary_operator o
  let e ← elab_expression e
  mkAppM ``Expression.u #[o, e]
| `(expression| $e₁: expression $o: binary_operator $e₂: expression) => do
  let e₁ ← elab_expression e₁
  let o ← elab_binary_operator o
  let e₂ ← elab_expression e₂
  mkAppM ``Expression.bin #[o, e₁, e₂]
| `(expression| ($e: expression)) => elab_expression e
| _ => Lean.Elab.throwUnsupportedSyntax


elab "[exp|" e:expression "]": term => elab_expression e

#reduce [exp| 2 + 23]
#reduce  [exp|a + 4]
#reduce  [exp|a ≤ 4]
#reduce  [exp|1 + true]
#reduce  [exp|1 + !true]

end embedding
end syntx

namespace semantics

inductive Value
| vn: Nat → Value
| vb: Bool → Value
deriving Inhabited, DecidableEq, Repr

def Environment := List (String × Value)
deriving Inhabited, DecidableEq, Repr

instance: ToString Value where toString := λ v =>
  match v with
  | .vn n => s!"v:{n}"
  | .vb b => s!"v:{b}"
instance: ToString Environment where toString := λ ρ =>
  ρ.toString

open Value
#eval ([("toot", vn 3)]: Environment)

def lookup (s: String) (ρ: Environment) :=
  (ρ.find? λ (k, _)  => k = s).bind λ (_, v) => some v

open soup.expressions.syntx
open soup.expressions.syntx.Literal
open soup.expressions.syntx.Expression

def evaluate (expression: Expression) (ρ: Environment) : Option Value :=
match expression with
| l (n e)                       => vn e
| l (b e)                       => vb e
| ref var                       => lookup var ρ
| u UnaryOperator.not e         =>
  let v := evaluate e ρ
  match v with
  | none => none
  | some (vn _) => none
  | some (vb e) => some (vb ¬e)
| bin BinaryOperator.plus e₁ e₂ =>
  let v₁ := evaluate e₁ ρ
  let v₂ := evaluate e₂ ρ
  match v₁, v₂ with
  | some (vn v₁), some (vn v₂) => some (vn $ v₁ + v₂)
  | _, _ => none
| bin BinaryOperator.and e₁ e₂  =>
  let v₁ := evaluate e₁ ρ
  let v₂ := evaluate e₂ ρ
  match v₁, v₂ with
  | some (vb v₁), some (vb v₂) => some (vb $ v₁ ∧ v₂)
  | _, _ => none
| bin BinaryOperator.eq e₁ e₂   =>
  let v₁ := evaluate e₁ ρ
  let v₂ := evaluate e₂ ρ
  some (vb $ if v₁ = v₂ then True else False)
| bin BinaryOperator.leq e₁ e₂  =>
  let v₁ := evaluate e₁ ρ
  let v₂ := evaluate e₂ ρ
  match v₁, v₂ with
  | some (vn v₁), some (vn v₂) => some (vb $ v₁ <= v₂)
  | _, _ => none

def notBothIn₀ := [exp| ¬((sA = crit) ∧ (sB = crit))]
def bothIn₀ :=    [exp|   (sA = crit) ∧ (sB = crit) ]
#reduce notBothIn₀
#reduce bothIn₀

def testEnv : Environment := [
   ("init", vn 0)
  ,("wait", vn 1)
  ,("crit", vn 2)
  ,("sA", vn 2)
  ,("sB", vn 2)
]

#reduce evaluate bothIn₀ testEnv

end semantics

end expressions
end soup
