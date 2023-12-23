import Mathlib.Init.Set
import Mathlib.Tactic.Basic --for Type*
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.PushNeg
import Mathlib.Tactic.LibrarySearch

/-!
# Inspired by

- [Regular-expression derivatives reexamined](https://www.khoury.northeastern.edu/home/turon/re-deriv.pdf)
- [regex-derivative @ Tej Chajed](https://github.com/tchajed/regex-derivative/blob/master/regex.v)
-/

-- The 𝒜lphabet
variable
  { 𝒜 : Type* } -- 𝒜 because we cannot use Σ

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
instance: HAppend (Word 𝒜) (List 𝒜) (Word 𝒜) := ⟨ List.append ⟩
instance: HAppend (List 𝒜) (Word 𝒜) (Word 𝒜) := ⟨ List.append ⟩

@[simp]
lemma word_append_nil: ∀ w: Word 𝒜, w ++ ([]: List 𝒜) = w := by {
  intro w
  apply List.append_nil w
}

@[simp]
lemma nil_append_word: ∀ w: Word 𝒜, ([]: List 𝒜) ++ w = w := by {
  intro w
  apply List.nil_append w
}

/-!
A language is a set of words over an alphabet 𝒜.
As usual a set is a T → Prop, so in our case  (Word 𝒜) → Prop
-/

def Language 𝒜 := Set $ Word 𝒜
instance: Membership (Word 𝒜) (Language 𝒜) := ⟨Set.Mem⟩
instance: EmptyCollection (Language 𝒜) := ⟨ λ _ => False ⟩
instance: Union (Language 𝒜) := ⟨Set.union⟩

def singleWord (w: Word 𝒜) : Language 𝒜 := {b : Word 𝒜 | b = w}
instance: Singleton (Word 𝒜) (Language 𝒜) := ⟨singleWord⟩
def singleLetter[Singleton (Word 𝒜) (Language 𝒜)] (w: 𝒜) : Language 𝒜 := {[w]}
instance [Singleton (Word 𝒜) (Language 𝒜)]: Singleton 𝒜 (Language 𝒜) := ⟨singleLetter⟩


instance: HasSubset $ Language 𝒜 := ⟨Set.Subset⟩

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

/--!
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

/--!
  # The denotational semantics of a regex is a language
-/
def L: Regex 𝒜 → Language 𝒜
| Φ       => ∅
| τ c     => { [c] }
| e₁ ⋅ e₂ => { w | ∃ w₁ w₂, w₁ ∈ L e₁ ∧ w₂ ∈ L e₂ ∧ w = w₁ ++ w₂}
| e₁ ⋃ e₂ => L e₁ ∪ L e₂
| e★      => { w | w ∈ star (L e) }

/--!
To write the correctness of the regex derivatiev, `DerL` defines derivative for a language (denotation side).
The derivative of a language L wrt a character c is the set of all words w for which c⋅w is in L
-/
def DerL (c: 𝒜) (L: Language 𝒜) : Language 𝒜 := { w | (c :: w) ∈ L }

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

-- The language of ε is the singleton set { [] }
--  L ε = { [] }
def Lε : Language 𝒜  := { [] }

lemma eps_denotation: @L 𝒜 ε = {[]} := by {
  apply funext
  intro w
  apply propext
  apply words_in_L_ε
}

/--!

Equalities

-/

@[simp]
lemma L_empty: L (Φ: Regex 𝒜) = ∅ := by {
  apply funext
  intro w
  apply propext
  simp [L]
}

@[simp]
lemma L_token: ∀ c: 𝒜, L (τ c) = {[c]} := by {
  intro c
  apply funext
  intro w
  apply propext
  simp [L]
}

@[simp]
lemma L_union: ∀ e₁ e₂: Regex 𝒜, L (e₁ ⋃ e₂) = L e₁ ∪ L e₂ := by {
  intros e₁ e₂
  apply funext
  intro w
  apply propext
  simp [L]
}

lemma L_concatenation: ∀ e₁ e₂: Regex 𝒜, L (e₁ ⋅ e₂) = { w | ∃ w₁ w₂, w₁ ∈ L e₁ ∧ w₂ ∈ L e₂ ∧ w = w₁ ++ w₂} := by {
  intros e₁ e₂
  apply funext
  intro w
  apply propext
  simp [L]
}

lemma L_star: ∀ e: Regex 𝒜, L (e★) = { w | w ∈ star (L e) } := by {
  intro e
  apply funext
  intro w
  apply propext
  simp [L]
}

@[simp]
lemma Lε_star: @L 𝒜 (ε★) = Lε := by {
  apply funext
  intro w
  apply propext
  simp [L]
  sorry
}

@[simp]
lemma ε_concatenation: ∀ e: Regex 𝒜, L (ε ⋅ e) = L e := by {
  intro e
  apply funext
  intro w
  apply propext
  simp [L]
  sorry
}

@[simp]
lemma concatenation_ε: ∀ e: Regex 𝒜, L (e ⋅ ε) = L e := by {
  sorry
}

@[simp]
lemma Φ_concatenation: ∀ e: Regex 𝒜, L (Φ ⋅ e) = ∅ := by {
  intro e
  apply funext
  intro w
  apply propext
  simp [L]
  sorry
}

@[simp]
lemma concatenation_Φ: ∀ e: Regex 𝒜, L (e ⋅ Φ) = ∅ := by {
  intro e
  apply funext
  intro w
  apply propext
  simp [L]
  sorry
}

lemma concatenation_assoc: ∀ e₁ e₂ e₃: Regex 𝒜, L ((e₁ ⋅ e₂) ⋅ e₃) = L (e₁ ⋅ (e₂ ⋅ e₃)) := by {
  intros e₁ e₂ e₃
  apply funext
  intro w
  apply propext
  sorry
}

@[simp]
lemma empty_union_e: ∀ e: Regex 𝒜, L (Φ ⋃ e) = L e := by {
  intro e
  apply funext
  intro w
  apply propext
  simp [L]
  constructor
  . intro H
    cases H with
    | inl Hl => exfalso; exact Hl
    | inr Hr => exact Hr
  . intro H
    apply Or.inr
    exact H
}

@[simp]
lemma union_idempotent: ∀ e: Regex 𝒜, L (e ⋃ e) = L e := by {
  intro e
  apply funext
  intro w
  apply propext
  simp [*]
  constructor
  . intro H
    cases H with
    | inl Hl => exact Hl
    | inr Hr => exact Hr
  . intro H
    apply Or.inr
    exact H
}

lemma union_comm: ∀ r₁ r₂: Regex 𝒜, L (r₁ ⋃ r₂) = L (r₂ ⋃ r₁) := by {
  intros r₁ r₂
  apply funext
  intro w
  apply propext
  simp [L]
  constructor
  . intro H
    cases H with
    | inl Hl => apply Or.inr; exact Hl
    | inr Hr => apply Or.inl; exact Hr
  . intro H
    cases H with
    | inl Hl => apply Or.inr; exact Hl
    | inr Hr => apply Or.inl; exact Hr
}

lemma union_assoc: ∀ r₁ r₂ r₃: Regex 𝒜, L ((r₁ ⋃ r₂) ⋃ r₃) = L (r₁ ⋃ (r₂ ⋃ r₃)) := by {
  intros r₁ r₂ r₃
  apply funext
  intro w
  apply propext
  simp [L]
  sorry
}

@[simp]
lemma union_empty: ∀ r: Regex 𝒜, L (r ⋃ Φ) = L r := by {
  intro r
  apply funext
  intro w
  apply propext
  simp [L]
  constructor
  . intro H
    cases H with
    | inl Hl => exact Hl
    | inr Hr => exfalso; exact Hr
  . intro H
    apply Or.inl
    exact H
}

@[simp]
lemma union_empty': ∀ r: Regex 𝒜, L (Φ ⋃ r) = L r := by {
  intro r
  rw [union_comm]
  apply union_empty
}

@[simp]
lemma star_star: ∀ e: Regex 𝒜, L (e★★) = L (e★) := by {
  intro e
  apply funext
  intro w
  apply propext
  simp [L]
  constructor
  . intro H
    cases H with
    | star_empty =>
      apply star.star_empty
    | star_iter w₁ w₂ w₁_in_e hw₂ =>
      cases hw₂ with
      | star_empty =>
        conv in (w₁ ++ []) => apply word_append_nil
        exact w₁_in_e
      | star_iter w₃ w₄ w₃_in_e hw₄ =>
        apply star.star_iter
        . sorry
        . sorry
  . intro H
    cases H with
    | star_empty =>
      apply star.star_empty
    | star_iter w₁ w₂ w₁_in_e hw₂ =>
      apply star.star_iter
      . sorry
      . sorry
}


/--!
  # Nullability
  The nullability (`δ`) maps a Regex re to ε if the empty word [] is in the language of r

  `δ re =`
  - `ε if ε ∈ L re`
  - `Φ otherwise`
-/
def δ: Regex 𝒜 → Regex 𝒜
| Φ       => Φ
| τ _     => Φ
| e₁ ⋅ e₂ => δ e₁ ⋅ δ e₂
| e₁ ⋃ e₂ => δ e₁ ⋃ δ e₂
| _★      => ε

/-
  For any Regex re, the language of (δ re) contains only the empty Word [].
-/
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

/-
  If the empty word is in the language of δ re, then the empty word is in the language of the re
  `[] ∈ L (δ r) → [] ∈ (L r)`
-/
lemma δ₂: [] ∈ L (δ r) → [] ∈ (L r) := by {
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

/-
  The compilation of δ₁ and δ₂.
  The language of δ r is the singleton { [] } and [] is in the languare of r.
-/
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

/-!
  If the empty word is in the language of r, then the empty word is in the language of δ r
-/
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
  | star e _ =>
    intro _
    apply star.star_empty
}

theorem δ_empty: [] ∈ L (δ r) ↔ [] ∈ L r := by {
  constructor
  . apply δ₂
  . apply δ_holds
}

/-
 We require decidable equality for 𝒜 (`DecidableEq 𝒜`).
 Technically, the only thing needed is a function that checks
 if a character `c` is in the set `t` captured by the token constructor `τ t`
 Equality is a particular case, in which the set `t` is a singleton.
 **TODO**:
 - I keep DecidableEq initially to have the first run at the proofs,
 - then I'll try to remove this constraint.
 - So in the end we will require of a letter 𝒜 in the token-type 𝒯 `Membership 𝓐 𝒯`,
`Membership 𝓐 𝒯` will give us symbolic Regex, where the token will encode a set of letters, with equality as a particular case.
-/
variable [deq𝒜: DecidableEq 𝒜]
/-!
# Derivative of a Regular Expression
-/
def D (c: 𝒜): Regex 𝒜 → Regex 𝒜
| Φ => Φ
| τ t => if t = c then ε else Φ
| e₁ ⋅ e₂ => (D c e₁ ⋅ e₂) ⋃ (δ e₁ ⋅ D c e₂)
| e₁ ⋃ e₂ => D c e₁ ⋃ D c e₂
| e★ => D c e ⋅ e★

/-
 The correctness theorem has the form that
  The language of the derivative (`L (D c re)`) and the derivative of the language (`D c (L re)`) are the same.
  That is `∀ w, w ∈ L (D c re) ↔ w ∈ D c (L re)`

  We will approach this proof by stating and proving separate lemmas for each direction of the bi-implication
  This will get us:
  1. L (D c re) ⊆ D c (L re)
  2. D c (L re) ⊆ L (D c re)
  3. thus L (D c re) = D c (L re)
-/

theorem LD_imp_DL: ∀ w: Word 𝒜,  w ∈ L (D c re) → w ∈ DerL c (L re) := by {
  intro w₁

  induction re with
  | empty =>
    simp [L]
    tauto
  | token t =>
    simp [D, L, DerL]
    intro Hw₁
    sorry

  | concatenation e₁ e₂ ihe₁ ihe₂ => sorry
  | union e₁ e₂ ihe₁ ihe₂ =>
    simp [L, DerL] at *
    intro H
    cases H with
    | inl Hw =>
      apply Or.inl
      apply ihe₁
      exact Hw
    | inr Hw =>
      apply Or.inr
      apply ihe₂
      exact Hw
  | star e ihe =>
    simp [DerL] at *
    intro Hw
    cases Hw with
    | star_empty => sorry
    | star_iter w₁ w₂ w₁_in_e hw₂ =>
      sorry
}

theorem DL_imp_LD: ∀ w: Word 𝒜, w ∈ DerL c (L re) → w ∈ L (D c re) := by {
  intros w₁ hw₁
  simp [DerL] at *
  induction re with
  | empty =>
    simp [L, D]
    tauto
  | token t =>
    simp [L, D]
    cases hw₁
    simp [*]
    rw [words_in_L_ε]
  | concatenation e₁ e₂ ihe₁ ihe₂ => sorry
  | union e₁ e₂ ihe₁ ihe₂ =>
    simp [L, D] at *
    cases hw₁ with
    | inl hw =>
      apply Or.inl
      apply ihe₁
      exact hw
    | inr hw =>
      apply Or.inr
      apply ihe₂
      exact hw
  | star e ihe =>
    simp [D] at *
    sorry
}

theorem LD_iff_DL: ∀ w: Word 𝒜,  w ∈ L (D c re) ↔ w ∈ DerL c (L re) := by {
  intro w
  constructor
  apply LD_imp_DL
  apply DL_imp_LD
}

theorem LD_sseq_DL (c: 𝒜): L (D c re) ⊆ DerL c (L re) := by {
  apply LD_imp_DL
}

theorem DL_sseq_LD (c: 𝒜): DerL c (L re) ⊆ L (D c re) := by {
  apply DL_imp_LD
}

theorem LD_eq_DL (c: 𝒜): L (D c re) = DerL c (L re) := by {
  apply Set.ext
  apply LD_iff_DL
}
