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
def L: Regex 𝒜 → Language 𝒜
| Φ       => ∅
| τ c     => { [c] }
| e₁ ⋅ e₂ => { w | w ∈ (L e₁) * (L e₂)}
| e₁ ⋃ e₂ => L e₁ ∪ L e₂
| e★      => { w | w ∈ (L e)∗ }

-- lemma star_emptyL: star ∅ w → w = [] := by {
--   intro H
--   cases H with
--   | star_empty => rfl
--   | star_iter w₁ w₂ w₁_in_empty _ =>
--     exfalso
--     apply w₁_in_empty
-- }


-- ε represents the language consisting only of the empty word.
lemma words_in_L_ε (w: Word 𝒜): w ∈ L ε ↔ w = [] := by {
  simp [L, Lε]
  exact Iff.rfl
}

lemma eps_denotation: @L 𝒜 ε = 1 := by {
  simp [L]
  rfl
}

/--!

Equalities

-/

@[simp]
lemma L_empty: L (Φ: Regex 𝒜) = ∅ := by {
  simp [L]
}

@[simp]
lemma L_token: ∀ c: 𝒜, L (τ c) = {[c]} := by {
  simp [L]
}

@[simp]
lemma L_union: ∀ e₁ e₂: Regex 𝒜, L (e₁ ⋃ e₂) = L e₁ ∪ L e₂ := by {
  simp [L]
}

lemma L_concatenation: ∀ e₁ e₂: Regex 𝒜, L (e₁ ⋅ e₂) = { w | w ∈ L e₁ * L e₂} := by {
  simp [L]
}

lemma L_star: ∀ e: Regex 𝒜, L (e★) = { w | w ∈ (L e)∗ } := by {
  simp [L]
}

@[simp]
lemma Lε_star: @L 𝒜 (ε★) = Lε := by {
  simp [L]
}

@[simp]
lemma re_ε_concatenation: ∀ e: Regex 𝒜, L (ε ⋅ e) = L e := by {
  simp [L]
  intro e
  apply one_mul
}

@[simp]
lemma re_concatenation_ε: ∀ e: Regex 𝒜, L (e ⋅ ε) = L e := by {
  simp [L]
  intro e
  apply mul_one
}

@[simp]
lemma Φ_concatenation: ∀ e: Regex 𝒜, L (Φ ⋅ e) = ∅ := by {
  simp [L]
  intro e
  apply zero_mul
}

@[simp]
lemma concatenation_Φ: ∀ e: Regex 𝒜, L (e ⋅ Φ) = ∅ := by {
  simp [L]
  intro e
  apply mul_zero
}

lemma concatenation_assoc: ∀ e₁ e₂ e₃: Regex 𝒜, L ((e₁ ⋅ e₂) ⋅ e₃) = L (e₁ ⋅ (e₂ ⋅ e₃)) := by {
  simp [L]
  intros e₁ e₂ e₃
  apply mul_assoc
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
  simp [L]
  intros r₁ r₂ r₃
  apply add_assoc
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
lemma empty_union: ∀ r: Regex 𝒜, L (Φ ⋃ r) = L r := by {
  intro r
  rw [union_comm]
  apply union_empty
}

@[simp]
lemma ε_mem_star: ∀ e: Regex 𝒜, [] ∈ L (e★) := by {
  intro e
  simp [L]
  exists 0
}

@[simp]
lemma star_star: ∀ e: Regex 𝒜, L (e★★) = L (e★) := by {
  simp [L]
}

lemma eps_in_each_eps_in_concat (e₁ e₂: Regex 𝒜): [] ∈ L e₁ → [] ∈ L e₂ → [] ∈ L (e₁ ⋅ e₂) := by {
  intros h₁ h₂
  simp [L]
  exists []
  exists []
}

lemma eps_in_concat_eps_in_both (e₁ e₂: Regex 𝒜): [] ∈ (L e₁ * L e₂) → ([] ∈ L e₁ ∧ [] ∈ L e₂) := by {
  intro H
  let ⟨_, _, hx, hy, hxy⟩ := H
  simp [*] at *
  simp [nil_append_nil] at *
  rw [hxy.1] at hx
  rw [hxy.2] at hy
  exact ⟨hx, hy⟩
}

lemma eps_in_both_eps_in_e₁ (e₁ e₂: Regex 𝒜): [] ∈ (L e₁ * L e₂) → [] ∈ L e₁ :=
  λ H ↦ eps_in_concat_eps_in_both e₁ e₂ H |>.1

lemma eps_in_both_eps_in_e₂ (e₁ e₂: Regex 𝒜): [] ∈ (L e₁ * L e₂) → [] ∈ L e₂ :=
  λ H ↦ eps_in_concat_eps_in_both e₁ e₂ H |>.2


instance: HAdd (Regex 𝒜) (Regex 𝒜) (Regex 𝒜) := ⟨ Regex.union ⟩
instance: Zero (Regex 𝒜) := ⟨Regex.empty⟩
instance: One (Regex 𝒜) := ⟨ε⟩
instance: HMul (Regex 𝒜) (Regex 𝒜) (Regex 𝒜) := ⟨ Regex.concatenation ⟩
