import «RegEx».Language.language

lemma append_with_empty_star_eq_star (L: Language 𝒜): L * L∗ = L∗ ↔ [] ∈ L := by {
  sorry
}

@[simp]
lemma powL_n_right (L: Language 𝒜): L ^ (n+1) = (L ^ n) * L := by {
  rw [powL_n]
  ext wx
  constructor
  . rintro ⟨ w₁, ⟨ w₂, ⟨ hw₁, ⟨ hw₂, hwx ⟩  ⟩  ⟩  ⟩
    simp [*] at *
    exists w₂
    exists w₁
    simp [*] at *
    induction n with
    | zero =>
      simp [*] at *
      rw [mem_one] at hw₂
      rw [hw₂]
      rw [hw₂] at hwx
      rw [nil_append_word, word_append_nil] at *
      exact hwx
    | succ n ihe =>
      simp [*] at *
      apply ihe
      sorry
  . sorry
}

lemma pow_comm (L: Language 𝒜): L^n * L = L * (L^n) := by {
  rw [←powL_n]
  rw [powL_n_right]
}
