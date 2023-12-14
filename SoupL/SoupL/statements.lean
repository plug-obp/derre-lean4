import Lean
import Mathlib.Tactic.Basic
import «SoupL».expressions

namespace soup
namespace statements
namespace syntx

open soup.expressions.syntx
inductive Statement
| skip
| assign (target: String) (e: Expression)
| seq (s₁ s₂: Statement)
| if (e: Expression) (s₁ s₂: Statement)
deriving Inhabited, DecidableEq, Repr


namespace embedding
open Lean Elab Meta
open soup.expressions.syntx.embedding

/-
Elaborating Statements
-/

declare_syntax_cat statement
syntax "skip" : statement
syntax ident ":=" expression : statement
syntax ident "←" expression: statement
syntax statement ";" statement: statement
syntax "if" expression "then" statement "else" statement: statement
syntax "if" expression "{" statement "}" "else" "{" statement "}" : statement
syntax "if" expression "then" statement : statement
syntax "if" expression "{" statement "}" : statement
syntax statement ";" : statement

partial def elab_statement: Syntax → MetaM Expr
| `(statement| skip) => return .const ``Statement.skip []
| `(statement| $i:ident := $e)
| `(statement| $i:ident ← $e) => do
  let i := mkStrLit i.getId.toString
  let e ← elab_expression e
  mkAppM ``Statement.assign #[i, e]
| `(statement| $s₁ ; $s₂ ) => do
  let s₁ ← elab_statement s₁
  let s₂ ← elab_statement s₂
  mkAppM ``Statement.seq #[s₁, s₂]
| `(statement| if $e then $s₁ else $s₂)
| `(statement| if $e { $s₁ } else { $s₂ }) => do
  let e ← elab_expression e
  let s₁ ← elab_statement s₁
  let s₂ ← elab_statement s₂
  mkAppM ``Statement.if #[e, s₁, s₂]
| `(statement| if $e then $s)
| `(statement| if $e { $s }) => do
  let e ← elab_expression e
  let s₁ ← elab_statement s
  let s₂ := .const ``Statement.skip []
  mkAppM ``Statement.if #[e, s₁, s₂]
| `(statement| $s ;) => elab_statement s
| _ => Lean.Elab.throwUnsupportedSyntax

elab "[stmt|" s:statement "]" : term => elab_statement s

#reduce [stmt|
  a := 4;
  b ← 5;
  if ((not a) and 3 <= 4) then
    c := 4;

  if a {
    b ← 4;
    c ← 5;
  };
  x := 4;
]

end embedding
end syntx

namespace semantics
open soup.expressions.semantics
open soup.statements.syntx
open Statement

def update (s: String) (v: Value) (ρ: Environment): Environment :=
  ρ.bind λ (k, v₀) => if k = s then [(k, v)] else [(k, v₀)]

def testEnv := ([("x", .vb True), ("a", .vn 2), ("b", .vn 5)]:Environment)
#eval update "a" (.vn 3) ([("a", .vn 2), ("b", .vn 5)]:Environment)
#eval update "a" (.vn 100) testEnv

def execute (stmt: Statement) (ρ: Environment): Option Environment :=
match stmt with
| .skip  => some ρ
| .assign target e =>
  (evaluate e ρ).bind λ v => some (update target v ρ)
| .seq s₁ s₂ =>
  (execute s₁ ρ).bind λ ρ₁ => execute s₂ ρ₁
| .if e s₁ s₂ =>
  match (evaluate e ρ) with
  | some (.vb v) => if v then execute s₁ ρ else execute s₂ ρ
  | _ => none


def s₁ := [stmt|
  a ← 100;
  if ¬ x then
    b ← 40
  else
    b ← 10
]

#eval execute s₁ testEnv


end semantics

end statements
end soup
