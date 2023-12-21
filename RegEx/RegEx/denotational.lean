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
-- instance: EmptyCollection (Word 𝒜) := ⟨ [] ⟩

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
def singleLetter (w: 𝒜) : Language 𝒜 := {b | b = [w]}
instance: Singleton 𝒜 (Language 𝒜) := ⟨singleLetter⟩

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

/-!
  # Denotational definition of star
  We need this inductive definition to side-step the termination checker
  for the denotational semantics.
  The language of ★ is defined as:
  `L e★ = {[]} ∪ L (e · e★)`
  but this does not work as a recursive definition because `L e★` needs `L e★`
  which diverges, which is normal since a regular expression
  can represent languages with infinitely many words
-/
inductive star (l: Language 𝒜) : Language 𝒜
| star_empty: star l []
| star_iter: ∀ w₁ w₂,
      (w₁ ∈ l) → star l w₂
      →------------------
      star l (w₁ ++ w₂)

/-!
  # The denotational semantics of a regex is a language
-/
def L: Regex 𝒜 → Language 𝒜
| Φ       => ∅
| τ c     => { c }
| e₁ ⋅ e₂ => { w | ∃ w₁ w₂, w₁ ∈ L e₁ ∧ w₂ ∈ L e₂ ∧ w = w₁ ++ w₂}
| e₁ ⋃ e₂ => L e₁ ∪ L e₂
| e★      => { w | w ∈ star (L e) }

lemma star_emptyL: star ∅ w → w = [] := by {
  intro H
  cases H with
  | star_empty => rfl
  | star_iter w₁ w₂ w₁_in_empty _ =>
    exfalso
    apply w₁_in_empty
}


-- ε represents the language consisting only of the empty word.
lemma words_in_L_ε (w: Word 𝒜): w ∈ L ε ↔ w = [] := by {
  constructor
  . apply star_emptyL
  . intro wH
    rw [wH]
    simp [L]
    apply star.star_empty
}

def Lε  := { w:Word 𝒜 | w = [] }

-- The language of ε is the singleton set { [] }
--  L ε = { [] }
lemma eps_denotation: @L 𝒜 ε = Lε := by {
  apply funext
  intro w
  apply propext
  apply words_in_L_ε
}

/-!
  Nullable
-/
def δ: Regex 𝒜 → Regex 𝒜
| Φ       => Φ
| τ _     => Φ
| e₁ ⋅ e₂ => δ e₁ ⋅ δ e₂
| e₁ ⋃ e₂ => δ e₁ ⋃ δ e₂
| _★      => ε

lemma δ₁: ∀ w: Word 𝒜, w ∈ L (δ r) → w = [] := by {
  induction r with
  | empty | token _ =>
    simp [δ, L]
    intros w H
    contradiction
  | concatenation e₁ e₂ ih₁ ih₂ =>
    intro w
    intro concatenation
    cases w with
    | nil => rfl
    | cons w₁ w₂ =>
      cases concatenation with
      | intro xx Hxx =>
        cases Hxx with
        | intro yy Hyy =>
          cases Hyy with
          | intro zz Hzz =>
            cases Hzz with
            | intro tt Htt =>
            rw [Htt]
            specialize ih₁ xx
            specialize ih₂ yy
            simp [*] at *
            rw [ih₁]
            rw [ih₂]
            rfl
  | union e₁ e₂ ih₁ ih₂ =>
    intro w
    simp [δ, L]
    specialize ih₁ w
    specialize ih₂ w
    intro union
    cases union with
    | inl h =>
      apply ih₁
      exact h
    | inr h =>
      apply ih₂
      exact h
  | star e _ =>
    simp [δ]
    intros w h
    rw [←words_in_L_ε]
    exact h
}
lemma δ₂: [] ∈ @L 𝒜 (δ r) → [] ∈ (L r) := by {
  induction r with
  | empty =>
    simp [L]
  | token _ =>
    simp [L]
    intro h
    exfalso
    contradiction
  | concatenation e₁ e₂ ihe₁ ihe₂ =>
    intro H
    simp [L] at *
    cases H with
    | intro x Hx =>
      cases Hx with
      | intro y Hy =>
        cases Hy with
        | intro z Hz =>
          exists []
          constructor
          . apply ihe₁
            have hx : x = [] := by {
              apply δ₁
              exact y
            }
            rw [←hx]
            exact y
          . exists []
            constructor
            . apply ihe₂
              have hz : z = [] := by {
                apply δ₁
                exact Hz.left
              }
              rw [←hz]
              exact Hz.left
            . rfl
  | union e₁ e₂ ihe₁ ihe₂ =>
    intro H
    simp [L] at *
    cases H with
    | inl hl =>
      apply Or.inl
      apply ihe₁
      exact hl
    | inr hr =>
      apply Or.inr
      apply ihe₂
      exact hr
  | star e _ =>
    intro _
    apply star.star_empty
 }
lemma δε: w ∈ L (δ r) → w = [] ∧ [] ∈ (L r) := by {
  intro H
  constructor
  . apply δ₁
    exact H
  . apply δ₂
    have hw : w = [] := by {
      apply δ₁
      exact H
    }
    rw [←hw]
    exact H
}

lemma he1 : ∀ x z : Word 𝒜, [] = x ++ z → x = [] ∧ z = [] := by {
  intros x y
  cases x with
  | nil => tauto
  | cons h t =>
    tauto
}

lemma δ_holds: [] ∈ L r → [] ∈ L (δ r) := by {
  induction r with
  | empty => simp [L]
  | token c =>
    simp [L]
    intro H
    exfalso
    contradiction
  | concatenation e₁ e₂ ihe₁ ihe₂ =>
    intro H
    simp [L] at *
    cases H with
    | intro x Hx =>
      cases Hx with
      | intro y Hy =>
        cases Hy with
        | intro z Hz =>
          have hx : x = [] ∧ z = [] := by {
            cases Hz with
            | intro lh rh =>
              apply he1
              exact rh
          }
          exists []
          constructor
          . apply ihe₁
            rw [hx.left] at y
            exact y
          . exists []
            constructor
            . apply ihe₂
              cases Hz with
              | intro hl hr =>
                rw [hx.right] at hl
                exact hl
            . rfl
  | union e₁ e₂ ihe₁ ihe₂ =>
    intro H
    simp [δ, L] at *
    cases H with
    | inl hl =>
      apply Or.inl
      apply ihe₁
      exact hl
    | inr hr =>
      apply Or.inr
      apply ihe₂
      exact hr
  | star e ihe =>
    intro H
    apply star.star_empty
}
