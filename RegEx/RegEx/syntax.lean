import Mathlib.Tactic.Basic --for Type*

-- The 𝒜lphabet
variable
  { 𝒜 : Type* } -- 𝒜 because we cannot use Σ

/-!
  # Regular Expressions
  A regular expression is a symbolic representation of a set of strings.
  The set of strings represented by a regular expression 𝓇 is denoted by L(𝓇).
  The set of all regular expressions over an alphabet 𝒜 is denoted by ℛ(𝒜).
-/
inductive Regex 𝒜 :=
| empty
| token         (c: 𝒜)
| concatenation (e₁ e₂ : Regex 𝒜)
| union         (e₁ e₂ : Regex 𝒜)
| star          (e : Regex 𝒜)
deriving DecidableEq, Inhabited

instance: EmptyCollection (Regex 𝒜) := ⟨ .empty ⟩

-- open Regex

notation:100 "Φ"    => Regex.empty
prefix:80    "τ"    => Regex.token
infixl:65    " ⋃ "  => Regex.union
infixl:70    "⋅"    => Regex.concatenation
postfix:65   "★"    => Regex.star

-- ε is a derived regex that matches only the empty string
def ε: Regex 𝒜 := .star .empty
