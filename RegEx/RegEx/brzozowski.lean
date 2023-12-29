import Mathlib.Tactic.Basic --for Type*
import «RegEx».Language.language
import «RegEx».Language.derivative
import «RegEx».denotational

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

lemma δ_empty: δ (Φ: Regex 𝒜) = Φ := by {
  simp [δ]
}

lemma δ_token: ∀ c: 𝒜, δ (τ c) = Φ := by {
  simp [δ]
}

lemma δ_union: ∀ e₁ e₂: Regex 𝒜, δ (e₁ ⋃ e₂) = δ e₁ ⋃ δ e₂ := by {
  simp [δ]
}

lemma δ_concatenation: ∀ e₁ e₂: Regex 𝒜, δ (e₁ ⋅ e₂) = δ e₁ ⋅ δ e₂ := by {
  simp [δ]
}

lemma δ_star: ∀ e: Regex 𝒜, δ (e★) = ε := by {
  simp [δ]
}

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
            rw [←Htt]
            specialize ih₁ xx
            specialize ih₂ yy
            rw [ih₂]
            rw [ih₁]
            rfl
            exact zz
            exact tt
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
    apply eps_in_each_eps_in_concat
    . apply ihe₁
      exact (eps_in_concat_eps_in_both (δ e₁) (δ e₂) H) |>.1
    . apply ihe₂
      exact (eps_in_concat_eps_in_both (δ e₁) (δ e₂) H) |>.2
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
    apply ε_mem_star
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

/-!
  If the empty word is in the language of r, then the empty word is in the language of δ r
-/
lemma δ_holds(r: Regex 𝒜): [] ∈ L r → [] ∈ L (δ r) := by {
  induction r with
  | empty => simp [L]
  | token c =>
    simp [L]
    intro H
    exfalso
    contradiction
  | concatenation e₁ e₂ ihe₁ ihe₂ =>
    intro H
    simp [δ_concatenation, L_concatenation] at *
    exists []
    exists []
    constructor
    . apply ihe₁
      apply eps_in_both_eps_in_e₁ _ e₂
      exact H
    . constructor
      . apply ihe₂
        apply eps_in_both_eps_in_e₂ e₁ _
        exact H
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
    simp [δ, L]
    rfl
}

theorem ε_in_δ_ε_in_r: [] ∈ L (δ r) ↔ [] ∈ L r := by {
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
| τ t => if c = t then ε else Φ
| e₁ ⋅ e₂ => (D c e₁ ⋅ e₂) ⋃ (δ e₁ ⋅ D c e₂)
| e₁ ⋃ e₂ => D c e₁ ⋃ D c e₂
| e★ => D c e ⋅ e★

@[simp]
lemma D_empty: ∀ c: 𝒜, D c (Φ: Regex 𝒜) = Φ := by {
  simp [D]
}

@[simp]
lemma D_token: ∀ c: 𝒜, ∀ t: 𝒜, D c (τ t) = if c = t then ε else Φ := by {
  simp [D]
}

lemma D_concatenation: ∀ c: 𝒜, ∀ e₁ e₂: Regex 𝒜, D c (e₁ ⋅ e₂) = (D c e₁ ⋅ e₂) ⋃ (δ e₁ ⋅ D c e₂) := by {
  simp [D]
}

lemma D_union: ∀ c: 𝒜, ∀ e₁ e₂: Regex 𝒜, D c (e₁ ⋃ e₂) = D c e₁ ⋃ D c e₂ := by {
  simp [D]
}

lemma D_star: ∀ c: 𝒜, ∀ e: Regex 𝒜, D c (e★) = D c e ⋅ e★ := by {
  simp [D]
}

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

theorem LD_imp_DL_token: ∀ w: Word 𝒜, w ∈ L (D c (τ t)) → w ∈ DerL c (L (τ t)) := by {
  intros w Hw
  simp [DerL_singleton, D_token] at *
  split
  next heq =>
    rw [←heq] at Hw
    simp [L] at Hw
    exact Hw
  next hneq =>
    simp [*] at Hw
    exact Hw
}

theorem LD_imp_DL_concat {w: Word 𝒜}
(ihe₁: w ∈ L (D c e₁) → w ∈ DerL c (L e₁))
(ihe₂: w ∈ L (D c e₂) → w ∈ DerL c (L e₂))
: w ∈ L (D c (e₁⋅e₂)) → w ∈ DerL c (L (e₁⋅e₂)) := by {
  sorry
}

theorem LD_imp_DL: ∀ w: Word 𝒜,  w ∈ L (D c re) → w ∈ DerL c (L re) := by {
  intro w
  induction re with
  | empty =>
    simp [L]
    tauto
  | token t =>
    apply LD_imp_DL_token
  | concatenation e₁ e₂ ihe₁ ihe₂ =>
    apply (LD_imp_DL_concat ihe₁ ihe₂)
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
    simp [L, D] at *
    sorry
}

lemma DL_imp_LD_concat
{w: Word 𝒜}
(ihe₁: w ∈ DerL c (L e₁) → w ∈ L (D c e₁))
(ihe₂: w ∈ DerL c (L e₂) → w ∈ L (D c e₂))
: w ∈ DerL c (L (e₁⋅e₂)) → w ∈ L (D c (e₁⋅e₂)) := by {
  sorry
}

theorem DL_imp_LD: ∀ w: Word 𝒜, w ∈ DerL c (L re) → w ∈ L (D c re) := by {
  intros w
  induction re with
  | empty =>
    simp [L, D]
    tauto
  | token t =>
    intro hw
    simp [L, D]
    cases hw
    simp [*]
    rw [words_in_L_ε]
  | concatenation e₁ e₂ ihe₁ ihe₂ =>
    apply DL_imp_LD_concat ihe₁ ihe₂
  | union e₁ e₂ ihe₁ ihe₂ =>
    intro hw
    simp [L, D] at *
    cases hw with
    | inl hw =>
      apply Or.inl
      apply ihe₁
      exact hw
    | inr hw =>
      apply Or.inr
      apply ihe₂
      exact hw
  | star e ihe =>
    intro hw
    simp [L, D] at *
    induction w with
    | nil =>
      apply nil_mem_star
    | cons h t ihw =>
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
