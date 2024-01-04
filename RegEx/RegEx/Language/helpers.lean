import «RegEx».Language.language
import Mathlib.Algebra.GroupPower.Basic

lemma append_with_empty_star_eq_star (L: Language 𝒜): L * L∗ = L∗ ↔ [] ∈ L := by {
  constructor
  . intro h
    simp [*] at *
    have h₂ : [] ∈ L * L∗ := by {
      rw [h]
      apply eps_in_star
     }
    simp [mul_def, Set.image2] at h₂
    rcases h₂ with ⟨ w₁, hw₁, w₂, hw₂, hwx⟩
    simp [nil_append_nil] at hwx
    rw [hwx.1] at hw₁
    exact hw₁
  . intro h
    ext wx
    constructor
    . intro hwx
      simp [mul_def, Set.image2] at hwx
      rcases hwx with ⟨ w₁, hw₁, w₂, hw₂, hwx⟩
      sorry
    . intro hwx
      simp [mul_def, Set.image2]
      exists []
      constructor
      . exact h
      . exists wx
}
