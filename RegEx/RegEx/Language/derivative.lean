
import «RegEx».Language.language

/--!
To write the correctness of the regex derivatiev, `DerL` defines derivative for a language (denotation side).
The derivative of a language L wrt a character c is the set of all words w for which c⋅w is in L
-/
def DerL (c: 𝒜) (L: Language 𝒜) : Language 𝒜 := { w | (c :: w) ∈ L }

lemma DerL_def (c: 𝒜) (L: Language 𝒜) : DerL c L = { w | (c :: w) ∈ L } := rfl
lemma DerL_empty (c: 𝒜) : DerL c ∅ = ∅ := by {
  simp [DerL_def]
  rfl
}
lemma DerL_epsilon (c: 𝒜) : DerL c Lε = ∅ := by {
  ext w₁
  constructor <;> (intro _; contradiction)
}

lemma DerL_singleton_eq(c: 𝒜): DerL c {[c]} = Lε := by {
  ext w₁
  simp [DerL_def, Lε]
}

lemma DerL_singleton_neq(c: 𝒜) (d: 𝒜)(hne: c ≠ d) :
  DerL c {[d]} = ∅ := by {
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
  DerL c {[d]} = (if c = d then Lε else ∅) := by {
  ext w₁
  split
  next cd => simp [cd, DerL_singleton_eq]
  next cnd => simp [DerL_singleton_neq _ _ cnd]
}

lemma der_head_single(w: Word 𝒜): c = x → w ∈ DerL c {[x]} → w = [] := by {
  intro H Hw
  rw [H] at Hw
  simp [DerL_singleton_eq] at *
  exact Hw
}
