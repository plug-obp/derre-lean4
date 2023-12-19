import Mathlib.Init.Set
import Mathlib.Tactic.Basic --for Type*
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.PushNeg
import Mathlib.Tactic.LibrarySearch

/-!
# Inspired by
https://github.com/tchajed/regex-derivative/blob/master/regex.v


-/

-- The 𝒜lphabet
variable
  { 𝒜 : Type* } -- 𝒜 because we cannot use Σ
  --[DecidableEq E] TODO: see if we require it

/-!
  # Standard names
  These simple definitions give standard names from the theory of computation to
  the analogues in this setting.
-/

/-!
  A word takes elements from the (arbitrary) alphabet above. *)
  **TODO**: I think that list is too restrictive,
    we need LinearOrder here or something similar
  Basically a word should be a linear order on a subset of 𝒜
    LinearOrder X, where X ⊆ 𝒜
  Since 𝒜 is a type, X might be a subtype
-/
alias Word := List
instance: HAppend (Word 𝒜) (Word 𝒜) (Word 𝒜) := ⟨ List.append ⟩
instance: EmptyCollection (Word 𝒜) := ⟨ [] ⟩

-- set_option quotPrecheck false
-- notation "ε"     => ([]:Word 𝒜)

/-!
A language is a set of words over an alphabet 𝒜.
As usual a set is a T → Prop, so in our case  (Word 𝒜) → Prop
-/

def Language 𝒜 := Set $ Word 𝒜
instance: Membership (Word 𝒜) (Language 𝒜) := ⟨Set.Mem⟩
instance: EmptyCollection (Language 𝒜) := ⟨ λ _ => False ⟩
instance: Union (Language 𝒜) := ⟨Set.union⟩

inductive Regex 𝒜 :=
| empty
| token         (c: 𝒜)
| concatenation (e₁ e₂ : Regex 𝒜)
| union         (e₁ e₂ : Regex 𝒜)
| star          (e : Regex 𝒜)
deriving DecidableEq, Inhabited

-- open Regex

notation:100 "Φ"    => Regex.empty
prefix:80    "τ"    => Regex.token
infixl:65    " ⋃ "  => Regex.union
infixl:70    "⋅"    => Regex.concatenation
postfix:65   "★"    => Regex.star

-- ε is a derived regex that matches only the empty string
def ε: Regex 𝒜 := .star .empty

-- Denotational definition of star
inductive star (l: Language 𝒜) : Language 𝒜
| star_empty: star l ∅
| star_iter:
      (w₁ ∈ l) → star l w₂
      →------------------
      star l (w₁ ++ w₂)

-- The denotational semantics of a regex is a language
def L: Regex 𝒜 → Language 𝒜
| Φ       => ∅
| τ c     => { w | w = c::[] }
| e₁ ⋅ e₂ => { w | ∃ w₁ w₂, w = w₁ ++ w₂ ∧ L e₁ w₁ ∧ L e₂ w₂ }
| e₁ ⋃ e₂ => L e₁ ∪ L e₂
| e★      => { w | star (L e) w }

lemma star_false: ∀ w: Word 𝒜, star ∅ w → w = [] := by {
  intros w
  induction w with
  | nil => tauto
  | cons h t ih =>
    intros H
    simp
    sorry
}
-- Eps indeed represents the language consisting only of the empty string. *)
lemma eps_denotation : L ε w ↔ w = ([]:Word 𝒜) := by {
  sorry
}
