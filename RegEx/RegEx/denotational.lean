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
| 𝓇₁ ⋃ 𝓇₂ => ℒ 𝓇₁ + ℒ 𝓇₂
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
lemma mem_l_eps (w: Word 𝒜): w ∈ ℒ ε ↔ w = [] := by simp [ℒ]

lemma eps_denotes: @ℒ 𝒜 ε = 1 := by simp [ℒ]

/--!

Equalities

-/

@[simp]
lemma empty_denotes: ℒ (Φ: Regex 𝒜) = ∅ := rfl

@[simp]
lemma token_denotes: ∀ c: 𝒜, ℒ (τ c) = {[c]} := λ _ => rfl

@[simp]
lemma union_denotes: ∀ e₁ e₂: Regex 𝒜, ℒ (e₁ ⋃ e₂) = ℒ e₁ + ℒ e₂ := λ _ _ => rfl

@[simp]
lemma concatenation_denotes: ∀ e₁ e₂: Regex 𝒜, ℒ (e₁ ⋅ e₂) = ℒ e₁ * ℒ e₂ := λ _ _ => rfl

@[simp]
lemma pow_denotes: ∀ e: Regex 𝒜, ℒ (e^n) = (ℒ e)^n := by {
  intro e
  induction n with
  | zero => simp [ℒ];
  | succ n ih => simp [ℒ]; rw [←ih]; rfl
}

@[simp]
lemma star_denotes: ∀ e: Regex 𝒜, ℒ (e★) = (ℒ e)∗ := λ _ => rfl

@[simp]
lemma eps_star_denotes: @ℒ 𝒜 (ε★) = 1 := by simp [ℒ]

@[simp]
lemma re_ε_concatenation: ∀ e: Regex 𝒜, ℒ (ε ⋅ e) = ℒ e := by {
  simp [ℒ]
}

@[simp]
lemma re_concatenation_ε: ∀ e: Regex 𝒜, ℒ (e ⋅ ε) = ℒ e := by {
  simp [ℒ]
}

@[simp]
lemma Φ_concatenation: ∀ e: Regex 𝒜, ℒ (Φ ⋅ e) = ∅ := by {
  simp [ℒ]
}

@[simp]
lemma concatenation_Φ: ∀ e: Regex 𝒜, ℒ (e ⋅ Φ) = ∅ := by {
  simp [ℒ]
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

lemma eps_mem_union_iff (e₁ e₂: Regex 𝒜): [] ∈ (ℒ e₁ + ℒ e₂) ↔ ([] ∈ ℒ e₁ ∨ [] ∈ ℒ e₂) := by {
  apply Iff.intro
  . intro H
    cases H with
    | inl Hl => apply Or.inl; exact Hl
    | inr Hr => apply Or.inr; exact Hr
  . intro H
    cases H with
    | inl Hl => apply Or.inl; exact Hl
    | inr Hr => apply Or.inr; exact Hr
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
  tauto
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

lemma eps_in_each_eps_in_concat' (e₁ e₂: Regex 𝒜): [] ∈ ℒ e₁ ∧ [] ∈ ℒ e₂ → [] ∈ ℒ (e₁ ⋅ e₂) := by {
  rintro ⟨ h₁, h₂⟩
  simp [ℒ]
  tauto
}

lemma eps_mem_concat_iff (e₁ e₂: Regex 𝒜): [] ∈ (ℒ e₁ * ℒ e₂) ↔ ([] ∈ ℒ e₁ ∧ [] ∈ ℒ e₂) := by {
  apply Iff.intro
  . apply eps_in_concat_eps_in_both
  . apply eps_in_each_eps_in_concat'
}

/--!
  ℒ induces a denotation-based (set-based) equivalence relation, so we can get a quotient type
-/

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

def Regexℒ (α : Type u) : Type u := Quotient (@Regex.toℒSetoid α)

@[simp]
def rL(e: Regex 𝒜): Regexℒ 𝒜 := Quotient.mk' e
@[simp ]
def concat: Regexℒ 𝒜 → Regexℒ 𝒜 → Regexℒ 𝒜 :=
  Quotient.lift₂
    (λ e₁ e₂ => rL (e₁ ⋅ e₂))
    (λ e₁ e₂ e₃ e₄ e₁e₃ e₂e₄ =>
      by {
        apply Quotient.sound
        intro w
        dsimp
        have he₁e₃: ℒ e₁ = ℒ e₃ := by ext ww; exact e₁e₃ ww
        have he₂e₄: ℒ e₂ = ℒ e₄ := by ext ww; exact e₂e₄ ww
        rw [he₁e₃, he₂e₄]
      })

lemma δ_concatenation_eq_eps(e₁ e₂: Regexℒ 𝒜) : concat (e₁) (e₂) = (rL ε) ↔ e₁ = rL ε ∧ e₂ = rL ε := by {
  sorry
}
