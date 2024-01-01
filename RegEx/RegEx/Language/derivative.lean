import «RegEx».Language.language

class Derivative (α: Type*) (β: Type*) where
  der: α → β → β
prefix:1024 "𝒟" => Derivative.der

/--!
To write the correctness of the regex derivatiev, `DerL` defines derivative for a language (denotation side).
The derivative of a language L wrt a character c is the set of all words w for which c⋅w is in L
-/
def derL (c: 𝒜) (L: Language 𝒜) : Language 𝒜 := { w | (c :: w) ∈ L }
instance : Derivative 𝒜 (Language 𝒜) := ⟨derL⟩

lemma DerL_def (c: 𝒜) (L: Language 𝒜) : 𝒟 c L = { w | (c :: w) ∈ L } := rfl
lemma DerL_empty (c: 𝒜) : 𝒟 c (∅: Language 𝒜) = ∅ := by {
  simp [DerL_def]
  rfl
}
lemma DerL_epsilon (c: 𝒜) : 𝒟 c Lε = (∅: Language 𝒜) := by {
  ext w₁
  constructor <;> (intro _; contradiction)
}

lemma DerL_singleton_eq(c: 𝒜): 𝒟 c {[c]} = Lε := by {
  ext w₁
  simp [DerL_def, Lε]
  constructor
  . intro H
    apply H
  . intro H
    simp [*] at *
    rfl
}

lemma DerL_singleton_neq(c: 𝒜) (d: 𝒜)(hne: c ≠ d) :
  𝒟 c {[d]} = (∅: Language 𝒜) := by {
  ext w₁
  simp [DerL_def]
  constructor
  . intro H
    let ⟨ _, _ ⟩ := H
    exfalso
    contradiction
  . intro H
    contradiction
}

lemma DerL_singleton(c: 𝒜) (d: 𝒜)[hdeq: Decidable (c = d)] :
  𝒟 c {[d]} = (if c = d then Lε else ∅) := by {
  ext w₁
  split
  next cd => simp [cd, DerL_singleton_eq]
  next cnd => simp [DerL_singleton_neq _ _ cnd]
}

lemma der_head_single(w: Word 𝒜): c = x → w ∈ 𝒟 c ({[x]}: Language 𝒜) → w = [] := by {
  intro H Hw
  rw [H] at Hw
  simp [DerL_singleton_eq] at *
  exact Hw
}

def hasEmpty? (L: Language 𝒜): Language 𝒜 := { x | x ∈ L ∧ x = [] }

lemma hasEmpty?_def (L: Language 𝒜): hasEmpty? L = { x | x ∈ L ∧ x = [] } := rfl

lemma hasEmpty?_empty: hasEmpty? (∅: Language 𝒜) = ∅ := by {
  simp [hasEmpty?_def]
  ext w
  constructor
  . intro H
    let ⟨ _, _ ⟩ := H
    exfalso
    contradiction
  . intro H
    contradiction
}

lemma hasEmpty?_epsilon: hasEmpty? Lε = (1: Language 𝒜) := by {
  simp [hasEmpty?_def, Lε]
  rfl
}

lemma hasEmpty?_concat (L₁ L₂: Language 𝒜): hasEmpty? (L₁ * L₂) = (hasEmpty? L₁ * hasEmpty? L₂) := by {
  simp [hasEmpty?_def]
  ext w
  constructor
  . intro H
    simp [*] at *
    let ⟨ left, we ⟩ := H
    let ⟨ w₁, w₂, hw₁, hw₂, hw ⟩ := left
    exists []
    exists []
    simp []
    rw [we] at left
    simp at hw
    rw [we] at hw
    rw [append_nil_iff_both_nil] at hw
    let ⟨ w₁e, w₂e ⟩ := hw
    rw [w₁e] at hw₁
    rw [w₂e] at hw₂
    rw [we]
    exact ⟨ hw₁, hw₂, rfl ⟩
  . intro H
    simp [*] at *
    let ⟨ w₁, w₂, ⟨ hw₁, w₁e⟩ , ⟨ hw₂, w₂e ⟩, hconc ⟩ := H
    simp [*] at *
    constructor
    . exists []
      exists []
    . rw [List.append_nil] at hconc
      exact (Eq.symm hconc)
}

lemma hasEmpty?_union (L₁ L₂: Language 𝒜): hasEmpty? (L₁ + L₂) = (hasEmpty? L₁ + hasEmpty? L₂) := by {
  simp [hasEmpty?_def]
  ext w
  constructor
  . intro H
    simp [*] at *
    let ⟨ left, we ⟩ := H
    sorry
  . intro H
    simp [*] at *
    sorry
}

lemma hasEmpty?_star (L: Language 𝒜): hasEmpty? (L∗) = (1: Language 𝒜) := by {
  simp [hasEmpty?_def, Lε]
  ext w
  constructor
  . intro H
    simp [*] at *
    let ⟨ _, we ⟩ := H
    exact we
  . intro H
    simp [*] at *
    constructor
    . rw [H]
      exists 0
    . exact H
}


lemma hasEmpty?_empty_in (L: Language 𝒜): hasEmpty? L = 1 ↔ [] ∈ L := by {
  simp [hasEmpty?_def, one_def]
  constructor
  . intro H
    sorry
  . intro H
    ext w
    constructor
    . intro hw
      simp [*] at *
      rw [mem_one']
      let ⟨ _, hw₂ ⟩ := hw
      exact hw₂
    . intro hw
      simp [*] at *
      rw [mem_one'] at hw
      rw [hw]
      apply And.intro; assumption; rfl
}

lemma der_concat_l₁ (c: 𝒜) (L₁ L₂: Language 𝒜) : [] ∈ L₁ → 𝒟 c (L₁ * L₂) = ((𝒟 c L₁) * L₂) + (𝒟 c L₂) := by {
  sorry
}

lemma der_concat_l₂ (c: 𝒜) (L₁ L₂: Language 𝒜) : [] ∉ L₁ → 𝒟 c (L₁ * L₂) = (𝒟 c L₁) * L₂ := by {
  sorry
}

lemma DerL_concat (c: 𝒜) (L₁ L₂: Language 𝒜) : 𝒟 c (L₁ * L₂) = (𝒟 c L₁) * L₂ + (hasEmpty? L₁ * 𝒟 c L₂) := by {
  sorry
}

lemma DerL_union (c: 𝒜) (L₁ L₂: Language 𝒜) : 𝒟 c (L₁ + L₂) = 𝒟 c L₁ + 𝒟 c L₂ := by {
  ext w₁
  simp [DerL_def]
  sorry
}

lemma DerL_star (c: 𝒜) (L: Language 𝒜) : 𝒟 c (L∗) = 𝒟 c L * L∗ := by {
  ext w₁
  simp [DerL_def]
  sorry
}
