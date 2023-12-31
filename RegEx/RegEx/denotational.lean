import «RegEx».syntax
import «RegEx».Language.language

-- The 𝒜lphabet
variable
  { 𝒜 : Type* } -- 𝒜 because we cannot use Σ

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
def ℒ: Regex 𝒜 → Language 𝒜
| Φ       => ∅
| τ c     => { [c] }
| 𝓇₁ ⋅ 𝓇₂ => (ℒ 𝓇₁) * (ℒ 𝓇₂)
| 𝓇₁ ⋃ 𝓇₂ => ℒ 𝓇₁ ∪ ℒ 𝓇₂
| 𝓇★      => (ℒ 𝓇)∗

-- lemma star_emptyL: star ∅ w → w = [] := by {
--   intro H
--   cases H with
--   | star_empty => rfl
--   | star_iter w₁ w₂ w₁_in_empty _ =>
--     exfalso
--     apply w₁_in_empty
-- }


-- ε represents the language consisting only of the empty word.
lemma words_in_L_ε (w: Word 𝒜): w ∈ ℒ ε ↔ w = [] := by {
  simp [ℒ, Lε]
  exact Iff.rfl
}

lemma eps_denotes: @ℒ 𝒜 ε = 1 := by {
  simp [ℒ]
  rfl
}

/--!

Equalities

-/

@[simp]
lemma empty_denotes: ℒ (Φ: Regex 𝒜) = ∅ := rfl

@[simp]
lemma token_denotes: ∀ c: 𝒜, ℒ (τ c) = {[c]} := λ _ => rfl

@[simp]
lemma union_denotes: ∀ e₁ e₂: Regex 𝒜, ℒ (e₁ ⋃ e₂) = ℒ e₁ ∪ ℒ e₂ := λ _ _ => rfl

@[simp]
lemma concatenation_denotes: ∀ e₁ e₂: Regex 𝒜, ℒ (e₁ ⋅ e₂) = ℒ e₁ * ℒ e₂ := λ _ _ => rfl

@[simp]
lemma pow_denotes: ∀ e: Regex 𝒜, ℒ (e^n) = (ℒ e)^n := by {
  intro e
  induction n with
  | zero => simp [ℒ]; rfl
  | succ n ih => simp [ℒ]; rw [←ih]; rfl
}

@[simp]
lemma star_denotes: ∀ e: Regex 𝒜, ℒ (e★) = (ℒ e)∗ := λ _ => rfl

@[simp]
lemma eps_star_denotes: @ℒ 𝒜 (ε★) = Lε := by simp [ℒ]

@[simp]
lemma re_ε_concatenation: ∀ e: Regex 𝒜, ℒ (ε ⋅ e) = ℒ e := by {
  simp [ℒ]
  intro _
  apply one_mul
}

@[simp]
lemma re_concatenation_ε: ∀ e: Regex 𝒜, ℒ (e ⋅ ε) = ℒ e := by {
  simp [ℒ]
  intro e
  apply mul_one
}

@[simp]
lemma Φ_concatenation: ∀ e: Regex 𝒜, ℒ (Φ ⋅ e) = ∅ := by {
  simp [ℒ]
  intro e
  apply zero_mul
}

@[simp]
lemma concatenation_Φ: ∀ e: Regex 𝒜, ℒ (e ⋅ Φ) = ∅ := by {
  simp [ℒ]
  intro e
  apply mul_zero
}

lemma concatenation_assoc: ∀ e₁ e₂ e₃: Regex 𝒜, ℒ ((e₁ ⋅ e₂) ⋅ e₃) = ℒ (e₁ ⋅ (e₂ ⋅ e₃)) := by {
  simp [ℒ]
  intros e₁ e₂ e₃
  apply mul_assoc
}

@[simp]
lemma empty_union_e: ∀ e: Regex 𝒜, ℒ (Φ ⋃ e) = ℒ e := by {
  intro e
  apply funext
  intro w
  apply propext
  simp [ℒ]
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
lemma union_idempotent: ∀ e: Regex 𝒜, ℒ (e ⋃ e) = ℒ e := by {
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

lemma union_comm: ∀ r₁ r₂: Regex 𝒜, ℒ (r₁ ⋃ r₂) = ℒ (r₂ ⋃ r₁) := by {
  intros r₁ r₂
  apply funext
  intro w
  apply propext
  simp [ℒ]
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

lemma union_assoc: ∀ r₁ r₂ r₃: Regex 𝒜, ℒ ((r₁ ⋃ r₂) ⋃ r₃) = ℒ (r₁ ⋃ (r₂ ⋃ r₃)) := by {
  simp [ℒ]
  intros r₁ r₂ r₃
  apply add_assoc
}

@[simp]
lemma union_empty: ∀ r: Regex 𝒜, ℒ (r ⋃ Φ) = ℒ r := by {
  intro r
  apply funext
  intro w
  apply propext
  simp [ℒ]
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
lemma empty_union: ∀ r: Regex 𝒜, ℒ (Φ ⋃ r) = ℒ r := by {
  intro r
  rw [union_comm]
  apply union_empty
}

@[simp]
lemma ε_mem_star: ∀ e: Regex 𝒜, [] ∈ ℒ (e★) := by {
  intro e
  simp [ℒ]
  exists 0
}

@[simp]
lemma star_star: ∀ e: Regex 𝒜, ℒ (e★★) = ℒ (e★) := by {
  simp [ℒ]
}

lemma eps_in_each_eps_in_concat (e₁ e₂: Regex 𝒜): [] ∈ ℒ e₁ → [] ∈ ℒ e₂ → [] ∈ ℒ (e₁ ⋅ e₂) := by {
  intros h₁ h₂
  simp [ℒ]
  exists []
  exists []
}

lemma eps_in_concat_eps_in_both (e₁ e₂: Regex 𝒜): [] ∈ (ℒ e₁ * ℒ e₂) → ([] ∈ ℒ e₁ ∧ [] ∈ ℒ e₂) := by {
  intro H
  let ⟨_, _, hx, hy, hxy⟩ := H
  simp [*] at *
  simp [nil_append_nil] at *
  rw [hxy.1] at hx
  rw [hxy.2] at hy
  exact ⟨hx, hy⟩
}

lemma eps_in_both_eps_in_e₁ (e₁ e₂: Regex 𝒜): [] ∈ (ℒ e₁ * ℒ e₂) → [] ∈ ℒ e₁ :=
  λ H ↦ eps_in_concat_eps_in_both e₁ e₂ H |>.1

lemma eps_in_both_eps_in_e₂ (e₁ e₂: Regex 𝒜): [] ∈ (ℒ e₁ * ℒ e₂) → [] ∈ ℒ e₂ :=
  λ H ↦ eps_in_concat_eps_in_both e₁ e₂ H |>.2
