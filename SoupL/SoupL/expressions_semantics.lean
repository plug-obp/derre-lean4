import Lean
import «SoupL».expressions
import «SoupL».pieces

namespace soup
namespace expressions
namespace semantics

inductive Value
| vn: Nat → Value
| vb: Bool → Value
| vcode: soup.syntx.Soup → Value
deriving Inhabited, DecidableEq, Repr

def Environment := List (String × Value)
deriving Inhabited, DecidableEq, Repr

instance: ToString Value where toString := λ v =>
  match v with
  | .vn n => s!"v:{n}"
  | .vb b => s!"v:{b}"
  | .vcode _ => s!"v:code}"
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
| .u UnaryOperator.not e         =>
  let v := evaluate e ρ
  match v with
  | none => none
  | some (vn _) => none
  | some (vb e) => some (vb ¬e)
  | some (vcode _) => none
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
