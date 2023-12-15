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
#reduce [exp|a + 4]
#reduce [exp|a ≤ 4]
#reduce [exp|1 + true]
#reduce [exp|1 + !true]
-- we don't have priority, so right associative by default
#reduce [exp| b=1 ∧ fA] != [exp| (b=1) ∧ fA]
#eval [exp| b=1 ∧ fA] != [exp| (b=1) ∧ fA]

end embedding
end syntx



end expressions
end soup
