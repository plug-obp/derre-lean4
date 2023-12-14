import Lean
import Mathlib.Tactic.Basic
import «SoupL».expressions
import «SoupL».expressions_semantics
import «SoupL».statements

namespace soup
namespace statements

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
