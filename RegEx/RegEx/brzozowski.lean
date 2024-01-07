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

lemma δ_empty: δ (Φ: Regex 𝒜) = Φ := by simp [δ]
lemma δ_token: ∀ c: 𝒜, δ (τ c) = Φ := by simp [δ]
lemma δ_union: ∀ e₁ e₂: Regex 𝒜, δ (e₁ ⋃ e₂) = δ e₁ ⋃ δ e₂ := by simp [δ]
lemma δ_concatenation: ∀ e₁ e₂: Regex 𝒜, δ (e₁ ⋅ e₂) = δ e₁ ⋅ δ e₂ := by simp [δ]
lemma δ_star: ∀ e: Regex 𝒜, δ (e★) = ε := by simp [δ]

/-
  For any Regex re, the language of (δ re) contains only the empty Word [].
-/
lemma δ₁: ∀ w: Word 𝒜, w ∈ ℒ (δ r) → w = [] := by {
  induction r with
  | empty | token _ =>
    simp [δ, ℒ]
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
    simp [δ, ℒ]
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
  | star _ _ => simp [δ]
}

/-
  If the empty word is in the language of δ re, then the empty word is in the language of the re
  `[] ∈ L (δ r) → [] ∈ (L r)`
-/
lemma δ₂: [] ∈ ℒ (δ r) → [] ∈ (ℒ r) := by {
  induction r with
  | empty =>
    simp [ℒ]
  | token _ =>
    simp [ℒ]
    intro h
    exfalso
    contradiction
  | concatenation e₁ e₂ ihe₁ ihe₂ =>
    intro H
    simp [ℒ] at *
    apply eps_in_each_eps_in_concat
    . apply ihe₁
      exact (eps_in_concat_eps_in_both (δ e₁) (δ e₂) H) |>.1
    . apply ihe₂
      exact (eps_in_concat_eps_in_both (δ e₁) (δ e₂) H) |>.2
  | union e₁ e₂ ihe₁ ihe₂ =>
    intro H
    simp [ℒ] at *
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
lemma δε: w ∈ ℒ (δ r) → w = [] ∧ [] ∈ (ℒ r) := by {
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
lemma δ_holds(r: Regex 𝒜): [] ∈ ℒ r → [] ∈ ℒ (δ r) := by {
  induction r with
  | empty => simp [ℒ]
  | token c =>
    simp [ℒ]
    intro H
    exfalso
    contradiction
  | concatenation e₁ e₂ ihe₁ ihe₂ =>
    intro H
    simp [δ_concatenation] at *
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
    simp [δ, ℒ] at *
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
    simp [δ, ℒ]
    rfl
}

theorem ε_in_δ_ε_in_r: [] ∈ ℒ (δ r) ↔ [] ∈ ℒ r := by {
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
| e★ => (D c e) ⋅ (e★)

instance: Derivative 𝒜 (Regex 𝒜):= ⟨D⟩

@[simp]
lemma D_empty: ∀ c: 𝒜, 𝒟 c (Φ: Regex 𝒜) = Φ := λ _ => rfl

@[simp]
lemma D_token: ∀ c: 𝒜, ∀ t: 𝒜, 𝒟 c (τ t) = if c = t then ε else Φ := λ _ _ => rfl

@[simp]
lemma D_concatenation: ∀ c: 𝒜, ∀ e₁ e₂: Regex 𝒜,
  𝒟 c (e₁ ⋅ e₂) = (𝒟 c e₁ ⋅ e₂) ⋃ (δ e₁ ⋅ 𝒟 c e₂) := λ _ _ _ => rfl

@[simp]
lemma D_union: ∀ c: 𝒜, ∀ e₁ e₂: Regex 𝒜, 𝒟 c (e₁ ⋃ e₂) = 𝒟 c e₁ ⋃ 𝒟 c e₂ := λ _ _ _ => rfl

@[simp]
lemma D_star: ∀ c: 𝒜, ∀ e: Regex 𝒜, 𝒟 c (e★) = (𝒟 c e) ⋅ (e★) := λ _ _ => rfl

@[simp]
lemma D_eps: ∀ (c: 𝒜), 𝒟 c ε = (Φ: Regex 𝒜)⋅(Φ★) := λ _ => rfl

theorem LD_imp_DL_token: ∀ (c: 𝒜) (w: Word 𝒜), w ∈ ℒ (𝒟 c (τ t)) → w ∈ 𝒟 c (ℒ (τ t)) := by {
  intros c w Hw
  simp [DerL_singleton, D_token] at *
  split
  next heq =>
    rw [←heq] at Hw
    simp [ℒ] at Hw
    exact Hw
  next hneq =>
    simp [*] at Hw
    exact Hw
}

lemma δ_eq_ν(e: Regex 𝒜):  ℒ (δ e) = ν (ℒ e) := by {
  induction e with
  | empty =>
    simp [δ, ℒ, ν]
    ext w
    constructor
    . intro H
      exfalso
      exact H
    . intro H
      exfalso
      let ⟨ hl, _ ⟩ := H
      exact hl
  | token t =>
    simp [δ, ℒ, ν]
    ext w
    constructor <;> intro H
    . exfalso; exact H
    . exfalso; let ⟨ hl, hr ⟩ := H
      rw [hl] at hr
      contradiction
  | concatenation e₁ e₂ ihe₁ ihe₂ =>
    simp [δ, ℒ, ν_concat] at *
    rw [ihe₁, ihe₂]
  | union e₁ e₂ ihe₁ ihe₂ =>
    simp [δ, ℒ, ν_union] at *
    rw [ihe₁, ihe₂]
  | star _ _ => simp [δ, ℒ, ν_star] at *

}

/-
 The correctness theorem has the form that
  The language of the derivative (`L (D c r)`) and the derivative of the language (`D c (L r)`) are the same.
  We will approach the proof by induction on the structure of the Regex r.
  Then for each case we unfold the derivative and retrieve the denotation from ℒ.
  Now in the language world we simply use the lemmas defined for languages.
-/
theorem LD_eq_DL (c: 𝒜) (r: Regex 𝒜):
  ℒ (𝒟 c r) = 𝒟 c (ℒ r)
:= by {
  induction r with
  | empty =>
    simp [ℒ, D]
    rfl
  | token t =>
    simp [ℒ, D]
    simp [DerL_singleton]
    split <;> simp
  | concatenation e₁ e₂ ihe₁ ihe₂ =>
    simp [ℒ, D]
    simp [DerL_concat, ←δ_eq_ν]
    rw [←ihe₁, ←ihe₂]
    rfl
  | union e₁ e₂ ihe₁ ihe₂ =>
    simp [ℒ, D]
    simp [DerL_union]
    rw [←ihe₁, ←ihe₂]
    rfl
  | star e ihe =>
    simp [ℒ, D]
    simp [DerL_star]
    rw [←ihe]
    rfl
}

/--!
# Membership is nullable derivative
-/
def D_chain(w: Word 𝒜) (r: Regex 𝒜): Regex 𝒜 := w.foldl (λ r c => 𝒟 c r) r
def brzozowski_mem(w: Word 𝒜) (r: Regex 𝒜): Prop := δ (D_chain w r) = ε       -- this is nice, but it does not work, because of structural equality
instance brzozowski_membership: Membership (Word 𝒜) (Regex 𝒜) := ⟨brzozowski_mem⟩

example (w: Word 𝒜) (r: Regex 𝒜): w ∈ r ↔ δ (D_chain w r) = ε := by {
  constructor
  . intro H
    exact H
  . intro H
    exact H
}

example (w: Word ℕ) (r: Regex 𝒜): w ∈ ((τ 5 ⋅ ε): Regex ℕ) := by {
  simp [Membership.mem]
  sorry
}

def ℒ_equiv (e₁ e₂: Regex 𝒜): Prop := ∀ w: Word 𝒜, w ∈ ℒ e₁ ↔ w ∈ ℒ e₂
infix:50 " ~ " => ℒ_equiv

lemma ℒ_equiv_refl:
  ∀ e: Regex 𝒜, e ~ e
:= by simp [ℒ_equiv]
lemma ℒ_equiv_symm:
  ∀ {e₁ e₂: Regex 𝒜}, e₁ ~ e₂ → e₂ ~ e₁
:= by {
    simp [ℒ_equiv]
    intros e₁ e₂ h w
    specialize h w
    rw [h]
}
lemma ℒ_equiv_trans:
  ∀ {e₁ e₂ e₃: Regex 𝒜}, e₁ ~ e₂ → e₂ ~ e₃ → e₁ ~ e₃
:= by {
    simp [ℒ_equiv]
    intros e₁ e₂ e₃ h₁₂ h₂₃ w
    specialize h₁₂ w
    specialize h₂₃ w
    rw [h₁₂, h₂₃]
}
theorem ℒ_equiv_is_equivalence: Equivalence (@ℒ_equiv 𝒜) := ⟨ℒ_equiv_refl, ℒ_equiv_symm, ℒ_equiv_trans⟩

instance Regex.toℒSetoid: Setoid (Regex 𝒜) := ⟨ℒ_equiv, ℒ_equiv_is_equivalence ⟩

def RegexℒSetoid (α : Type u) : Type u := Quotient (@Regex.toℒSetoid α)

def concat(e₁ e₂: Regex 𝒜): RegexℒSetoid 𝒜 := Quotient.mk' (e₁ ⋅ e₂)

lemma δ_concatenation_eq_eps : δ e₁ ⋅ δ e₂ ≈ ε ↔ δ e₁ ≈ ε ∧ δ e₂ ≈ ε := by {
  constructor
  . intro H
    simp [δ] at H
    sorry
  . intro H
    simp [δ]
    sorry
    -- this does not work because they are not definitionally equal
    -- they are equal modulo the equivalence relation generated by the language
    -- but I don't know how to use that
}

lemma ε_in_e_then_δ_eq_ε(e: Regex 𝒜): [] ∈ ℒ e → ℒ (δ e) = 1 := by {
  intro H
  rw [δ_eq_ν]
  rwa [ν_eq_one_iff]
}

lemma mem_eq_delta_der(w: Word 𝒜): w ∈ ℒ r → ℒ (δ (D_chain w r)) = 1 := by {
  induction r with
  | empty =>
    simp [ℒ, D_chain, δ]
    intro H
    contradiction
  | token t =>
    simp [ℒ, D_chain]
    intro H
    rw [H]
    simp [*] at *
    rw [δ_eq_ν, ν_eq_one_iff, star_denotes]
    apply one_in_kstar
    rfl
  | concatenation e₁ e₂ ih₁ ih₂ =>
    simp [ℒ, D_chain, δ]
    intro H
    sorry
  | union e₁ e₂ ih₁ ih₂ =>
    simp [ℒ, union_denotes]
    sorry
  | star e ih =>
    sorry
}
