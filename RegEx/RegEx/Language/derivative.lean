import «RegEx».Language.language
import Mathlib.Data.Set.UnionLift

class Derivative (α: Type*) (β: Type*) where
  der: α → β → β
prefix:1024 "𝒟" => Derivative.der

/--!
To write the correctness of the regex derivatiev, `DerL` defines derivative for a language (denotation side).
The derivative of a language L wrt a character c is the set of all words w for which c⋅w is in L
-/
def derL (c: 𝒜) (L: Language 𝒜) : Language 𝒜 := { w | (c :: w) ∈ L }
instance : Derivative 𝒜 (Language 𝒜) := ⟨derL⟩
instance : Derivative 𝒜 (Set (Word 𝒜)) := ⟨derL⟩

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

/--!
# Has Empty (_nu_llability)
Maps a language to 1 or 0 depending on whether the language contains the empty word or not.
-/
def ν (L: Language 𝒜): Language 𝒜 := { x | x ∈ L ∧ x = [] }

lemma ν_def (L: Language 𝒜): ν L = { x | x ∈ L ∧ x = [] } := rfl

lemma ν_empty: ν (∅: Language 𝒜) = ∅ := by {
  simp [ν_def]
  ext w
  constructor
  . intro H
    let ⟨ _, _ ⟩ := H
    exfalso
    contradiction
  . intro H
    contradiction
}

lemma ν_epsilon: ν Lε = (1: Language 𝒜) := by {
  simp [ν_def, Lε]
  rfl
}

lemma ν_concat (L₁ L₂: Language 𝒜): ν (L₁ * L₂) = (ν L₁ * ν L₂) := by {
  simp [ν_def]
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

lemma ν_union (L₁ L₂: Language 𝒜): ν (L₁ + L₂) = (ν L₁ + ν L₂) := by {
  ext w
  constructor
  . rintro ⟨ ⟨ l ⟩ | ⟨ r ⟩  , we ⟩
    . left
      simp [ν_def, *] at *
      exact l
    . right
      simp [ν_def, *] at *
      exact r
  . rintro  (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    . simp [ν_def, *] at *
      simp [add_def, Set.union_def, Set.mem_def]
      constructor
      . left
        exact h₁
      . rfl
    . simp [ν_def, *] at *
      simp [add_def, Set.union_def, Set.mem_def]
      constructor
      . right
        exact h₁
      .rfl
}

lemma ν_star (L: Language 𝒜): ν (L∗) = (1: Language 𝒜) := by {
  simp [ν_def, Lε]
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


lemma ν_empty_in (L: Language 𝒜): ν L = 1 ↔ [] ∈ L := by {
  constructor
  . intro h
    simp [ν_def, one_def] at *
    sorry
  . intro H
    simp [ν_def, one_def]
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

lemma der_concat_to_union(c: 𝒜) (L₁ L₂: Language 𝒜): w ∈ 𝒟 c (L₁ * L₂) → w ∈ 𝒟 c L₁ * L₂ + 𝒟 c L₂ := by {
  rintro ⟨ w₁, ⟨ w₂, ⟨ hw₁, hw₂, hw ⟩  ⟩  ⟩
  dsimp [] at *
  induction w₁ with
  | nil =>
    right
    rw [nil_append_word] at hw
    rw [hw] at hw₂
    exact hw₂
  | cons h t ihe =>
    left
    exists t
    exists w₂
    rw [Word.cons_append] at *
    rw [Word.cons_eq_cons_iff] at hw
    let ⟨ hc, ht ⟩ := hw
    simp [*] at *
    exact hw₁
}

lemma der_concat_to_union'(c: 𝒜) (L₁ L₂: Language 𝒜): w ∈ 𝒟 c (L₁ * L₂) → w ∈ 𝒟 c L₁ * L₂ + ν L₁ * (𝒟 c L₂) := by {
  rintro ⟨ w₁, ⟨ w₂, ⟨ hw₁, hw₂, hw ⟩ ⟩ ⟩
  dsimp [] at *
  induction w₁ with
  | nil =>
    right
    rw [nil_append_word] at hw
    rw [hw] at hw₂
    simp [ν_def] at *
    exists []
    exists w
  | cons h t ihe =>
    left
    exists t
    exists w₂
    rw [Word.cons_append] at *
    rw [Word.cons_eq_cons_iff] at hw
    let ⟨ hc, ht ⟩ := hw
    simp [*] at *
    exact hw₁
}

lemma der_union_to_concat(c: 𝒜) (L₁ L₂: Language 𝒜): wx ∈ 𝒟 c L₁ * L₂ + ν L₁ * 𝒟 c L₂ → wx ∈ 𝒟 c (L₁ * L₂) := by {
  rintro ( ⟨ w₁ , ⟨ w₂, ⟨hw₁, hw₂, hwx⟩ ⟩ ⟩ | ⟨ w₁, ⟨ w₂, ⟨ ⟨ w₁inL₁, w₁ε ⟩ , ⟨ hw₂ , hwx ⟩ ⟩ ⟩ ⟩ )
  . simp [*] at *
    dsimp [DerL_def, mul_def, Set.image2]
    exists c::w₁
    exists w₂
    simp [*] at *
    constructor
    . exact hw₁
    . rw [Word.cons_append]
      rw [Word.cons_inj]
      exact hwx
  . simp [*] at *
    dsimp [DerL_def, mul_def, Set.image2]
    exists []
    exists c::w₂
    constructor
    . exact w₁inL₁
    . constructor
      . exact hw₂
      . rw [nil_append_word] at *
        rw [Word.cons_inj]
        exact hwx
}

lemma DerL_concat (c: 𝒜) (L₁ L₂: Language 𝒜) : 𝒟 c (L₁ * L₂) = (𝒟 c L₁) * L₂ + (ν L₁ * 𝒟 c L₂) := by {
  ext wx
  constructor
  . apply der_concat_to_union'
  . apply der_union_to_concat
}

lemma DerL_concat_self (c: 𝒜) (L: Language 𝒜): 𝒟 c (L * L) = (𝒟 c L) * L := calc
  𝒟 c (L * L) = 𝒟 c L * L + (ν L * 𝒟 c L) := by rw [DerL_concat]
          _ = 𝒟 c L * L                   := by {
            rw [add_eq_self_iff]
            rintro (wx ⟨ w₁, ⟨ w₂, ⟨ ⟨ hw₁, w₁e ⟩ , ⟨ hw₂, hwx ⟩ ⟩ ⟩ ⟩ )
            simp [*] at *
            rw [nil_append_word] at hwx
            exists w₂
            exists []
            constructor
            . exact hw₂
            . constructor
              . exact hw₁
              . simp [*] at *
                apply word_append_nil
          }

lemma DerL_union (c: 𝒜) (L₁ L₂: Language 𝒜) : 𝒟 c (L₁ + L₂) = 𝒟 c L₁ + 𝒟 c L₂ := by {
  ext w₁
  simp [DerL_def]
  constructor
  . rintro (H₁ | H₂)
    . left
      exact H₁
    . right
      exact H₂
  . intro H
    cases H
    . left
      next H₁ => exact H₁
    . right
      next H₂ => exact H₂
}

lemma DerL_pow₀ (c: 𝒜) (L: Language 𝒜): 𝒟 c (L ^ (n+1)) = 𝒟 c L * (L ^ n) + ν L * 𝒟 c (L ^ n) := by {
  rw [←DerL_concat c L (L ^ n)]
  rw [←powL_n]
}

lemma DerL_pow (c: 𝒜) (L: Language 𝒜)(n: ℕ): 𝒟 c (L ^ (n+1)) = 𝒟 c L * (L ^ n) := by {
  induction n with
  | zero =>
    rw [powL_zero]
    rw [powL_one]
    rw [mul_one]
  | succ n ihe =>
    simp [*] at *
    rw [←powL_n]
    rw [DerL_concat]
    rw [add_eq_self_iff]
    sorry
}

lemma DerL_star (c: 𝒜) (L: Language 𝒜): 𝒟 c (L∗) = (𝒟 c L) * (L∗) :=
  calc
    (𝒟 c L∗) = 𝒟 c (1 + (L⊕)) := by rw [star_is_eps_union_plus]
    _ = 𝒟 c 1 + 𝒟 c (L⊕)      := by rw [DerL_union]
    _ = ∅ + 𝒟 c (L⊕)          := by rw [one_eq_eps, DerL_epsilon]
    _ = 𝒟 c (L⊕)              := by rw [←zero_eq_empty, zero_add]
    _ = 𝒟 c (L * (L∗))        := by rw [mul_eq_append, positive_closure]
    _ = (𝒟 c L) * (L∗) + ν L * 𝒟 c (L∗) := by rw [DerL_concat]
    _ = (𝒟 c L) * (L∗) := by {
      rw [add_eq_self_iff]
      rintro (wx ⟨ w₁, ⟨ w₂, ⟨ ⟨ hw₁, w₁e ⟩ , ⟨ hw₂, hwx ⟩ ⟩ ⟩ ⟩ )
      simp [*] at *
      rw [nil_append_word] at hwx
      exists w₂
      exists []
      constructor
      . simp [kleene_closure_def] at *
        rcases hw₂ with ⟨ n, powN ⟩
        induction n with
        | zero =>
          exfalso
          contradiction
        | succ n ihe =>
          apply ihe
          simp [*] at *
          rw [← powL_n] at powN
          sorry
      . constructor
        . apply eps_in_star
        . simp [*] at *
          apply word_append_nil
    }


lemma DerL_star_to' (c: 𝒜) (L: Language 𝒜): 𝒟 c (L∗) ⊆ (𝒟 c L) * (L∗) := by {
  intros wx hwx
  rcases hwx with ⟨ n, m ⟩
  exists wx
  exists []
  simp [*] at *
  constructor
  . sorry
  . constructor
    . apply eps_in_star
    . apply word_append_nil
}
lemma DerL_star' (c: 𝒜) (L: Language 𝒜): 𝒟 c (L∗) = (𝒟 c L) * (L∗) :=
  calc
    (𝒟 c L∗) = 𝒟 c (1 + (L⊕)) := by rw [star_is_eps_union_plus]
    _ = 𝒟 c 1 + 𝒟 c (L⊕)      := by rw [DerL_union]
    _ = ∅ + 𝒟 c (L⊕)          := by rw [one_eq_eps, DerL_epsilon]
    _ = 𝒟 c (L⊕)              := by rw [←zero_eq_empty, zero_add]
    _ = 𝒟 c (L * (L∗))        := by rw [mul_eq_append, positive_closure]
    _ = (𝒟 c L) * (L∗) + ν L * 𝒟 c (L∗) := by rw [DerL_concat]
    _ = (𝒟 c L) * (L∗) := by {
      rw [add_eq_self_iff]
      intros wx hwx
      rcases hwx with ⟨ w₁, ⟨w₂, ⟨ w₁L, w₁ε ⟩ , hw₂, hwx₂⟩⟩
      simp [*] at *
      rw [nil_append_word] at hwx₂
      rw [←hwx₂]
      apply DerL_star_to' c L hw₂
    }

lemma DerL_star'' (c: 𝒜) (L: Language 𝒜): 𝒟 c (L∗) = (𝒟 c L) * (L∗) :=
  calc
    (𝒟 c L∗) = 𝒟 c { w | ∃ n: ℕ, w ∈ (L ^ n)} := by rw [kleene_closure_def] -- this is equivalent to a big sum Σ₀∞
    _ = 𝒟 c (L^0) + { w | ∃ n: ℕ, n > 0 → w ∈ 𝒟 c (L ^ n)} := by sorry -- extract one from the sum L^0 ∪ Σ₁∞
    _ = 𝒟 c (1:Language 𝒜) + { w | ∃ n: ℕ, n > 0 → w ∈ 𝒟 c (L ^ n)} := by rw [pow_zero] -- L^0 = 1
    _ = ∅ + { w | ∃ n: ℕ, n > 0 → w ∈ 𝒟 c (L ^ n)} := by rw [one_eq_eps, DerL_epsilon]   -- 𝒟 c 1 = ∅
    _ = { w | ∃ n: ℕ, n > 0 → w ∈ 𝒟 c (L ^ n)} := by rw [←zero_eq_empty, zero_add]       -- ∅ + L = L
    _ = { w | ∃ n: ℕ, n > 0 → w ∈ 𝒟 c L * (L ^ (n-1)) } := by sorry                       -- 𝒟 c (L^n) = 𝒟 c L * L^(n-1) DerL_pow
    _ = 𝒟 c L * { w | ∃ n: ℕ, n > 0 → w ∈ (L ^ (n-1)) } := by sorry                       -- Σ₁∞ (D c L) * L^n = (D c L) * Σ₁∞ L^n --- factor out (D c L)
    _ = 𝒟 c L * { w | ∃ m: ℕ, w ∈ (L ^ m) } := by sorry                                   -- n ∈ ℕ, n > 0 <=> m = n-1, m ∈ ℕ       --- reindex
    _ = 𝒟 c L * (L∗) := by rw [←kleene_closure_def]                                       -- we get back a kleene closure


lemma star_is_iunion (L: Language 𝒜): L∗ = ⋃ n, L ^ n := by {
  ext wx
  rw [kleene_closure_def, Set.mem_iUnion]
  rfl
}

lemma powL_n' (L: Language 𝒜) (hn: n≥1): L ^ (n) = L * (L ^ (n-1)) := by {
  induction n with
  | zero =>
    exfalso
    exact Nat.lt_asymm hn hn
  | succ n _ =>
    simp [*] at *
}

example {α I : Type*} (A B : I → Set α) (s : Set α) : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨ xs, ⟨ i, xAi ⟩ ⟩
    exact ⟨ i, xAi, xs ⟩
  . rintro ⟨ i, xAi, xs ⟩
    exact ⟨ xs, ⟨ i, xAi ⟩ ⟩

lemma dd (wx: Word 𝒜) (L: Language 𝒜) (hwx: wx ∈ L ^ (n + 1)) : wx ∈ L ^ n → wx ∈ L ^ 0 ∨ wx ∈ L ^ (n + 1) := by {
  tauto
}

lemma union_split_l0 (L: Language 𝒜): ⋃ n, L ^ n = ⋃ m ≥ 1, L^0 ∪ L^m := by {
  ext wx
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  . intro H
    exists 1
    exists Nat.zero_lt_one
    sorry
  . rintro ⟨ m, ⟨ hm, ( h₁ | h₂ ) ⟩ ⟩
    . exists 0
    . exists m
}

lemma union_factor_out (L: Language 𝒜): ⋃ n ≥ 1, L^0 ∪ L ^ n = L^0 ∪ ⋃ n ≥ 1,  L^n := by {
  ext wx
  simp only [Set.mem_union, Set.mem_iUnion]
  constructor
  . rintro ⟨ n, ⟨ hn, ⟨ h₀, h₁ ⟩ ⟩ ⟩
    . apply Or.inl
      rfl
    . apply Or.inr
      exists n
      exists hn
  . rintro (H₁ | ⟨ m, ⟨hm, hwx ⟩ ⟩ )
    . exists 1
      exists Nat.zero_lt_one
      apply Or.inl
      exact H₁
    . exists m
      exists hm
      apply Or.inr
      exact hwx
}

lemma union_eq_plus (L₁ L₂: Language 𝒜): L₁ ∪ L₂ = L₁ + L₂ := rfl

lemma derL_factor_in(c: 𝒜) (L: Language 𝒜): 𝒟 c (⋃ n ≥ 1, L ^ n) = ⋃ n ≥ 1, 𝒟 c (L ^ n) := by {
  ext wx
  simp [Set.mem_iUnion, DerL_def, Set.univ] at *
  sorry
}

lemma derL_factor_out(c: 𝒜) (L: Language 𝒜) : ⋃ n ≥ 1, 𝒟 c L * (L ^ (n-1)) = 𝒟 c L * ⋃ n ≥ 1, (L ^ (n-1)) := by {
  sorry
}

lemma lsub_add_cancel (c: 𝒜) (L: Language 𝒜): ⋃ n ≥ 1, 𝒟 c (L ^ n) = ⋃ n ≥ 1, 𝒟 c (L ^ (n - 1 + 1)) := by {
  ext wx
  simp [Set.mem_iUnion] at *
  constructor
  . rintro ⟨ n, ⟨ hn, hwx ⟩ ⟩
    exists n
    exists hn
    rw [Nat.sub_add_cancel]
    exact hwx
    exact hn
  . rintro ⟨ n, ⟨ hn, hwx ⟩ ⟩
    exists n
    exists hn
    rw [Nat.sub_add_cancel] at hwx
    exact hwx
    exact hn
}

lemma pow_iUnion (c: 𝒜) (L: Language 𝒜) : ⋃ n ≥ 1, 𝒟 c (L ^ ((n-1)+1)) = ⋃ n ≥ 1, 𝒟 c L * (L ^ (n-1)) := by {
  ext wx
  simp [Set.mem_iUnion] at *
  constructor
  . rintro ⟨ n, ⟨ hn, hwx ⟩ ⟩
    exists n
    exists hn
    rw [DerL_pow] at hwx
    exact hwx
  . rintro ⟨ n, ⟨ hn, hwx ⟩ ⟩
    exists n
    exists hn
    rw [DerL_pow]
    exact hwx
}

lemma reindex(L: Language 𝒜): ⋃ n ≥ 1, (L ^ (n-1)) = ⋃ m, (L ^ m) := by {
  ext wx
  simp [Set.mem_iUnion] at *
  constructor
  . rintro ⟨ n, ⟨ _, hwx ⟩ ⟩
    exists (n-1)
  . rintro ⟨ m, hwx ⟩
    exists (m+1)
    rw [Nat.add_sub_cancel]
    simp [*] at *
}

-- D c L∗
--        = D c (L⁰ + L¹ + L² + L³ + ...)
--        = D c L⁰ + D c L¹ + D c L² + D c L³ + ...
--        = D c ε + D c L¹ + D c L² + D c L³ + ...
--        = ∅ + D c L¹ + D c L² + D c L³ + ...
--        = D c L¹ + D c L² + D c L³ + ...
--        = D c L * L⁰ + D c L * L¹ + D c L * L² + D c L * L³ + ...
--        = D c L * (L⁰ + L¹ + L² + L³ + ...)
--        = D c L * L∗

lemma DerL_star''' (c: 𝒜) (L: Language 𝒜): 𝒟 c (L∗) = (𝒟 c L) * (L∗) :=
  calc
    (𝒟 c L∗) = 𝒟 c (⋃ n, L ^ n)                   := by rw [star_is_iunion] -- this is equivalent to a big union       L∗ = ⋃ n, L^n
    _ = 𝒟 c (⋃ n ≥ 1, L^0 ∪ L ^ n)                 := by rw [union_split_l0] -- split the big union inside ⋃ n, L^n = ⋃ n>0, L^0 ∪ L^(n-1)
    _ = 𝒟 c (L^0 + (⋃ n ≥ 1, L ^ n))               := by rw [union_factor_out, union_eq_plus] -- factor out  ⋃ n>0, L^0 ∪ L^(n-1) = L^0 + ⋃ n>0, L^(n-1)
    _ = 𝒟 c (L^0) + 𝒟 c (⋃ n ≥ 1, L ^ n)           := by rw [DerL_union] -- apply derivative to the union
    _ = 𝒟 c (1:Language 𝒜) + 𝒟 c (⋃ n ≥ 1, L ^ n) := by rw [pow_zero] -- L^0 = 1
    _ = ∅ + 𝒟 c (⋃ n ≥ 1, L ^ n)                   := by rw [one_eq_eps, DerL_epsilon]   -- 𝒟 c 1 = ∅
    _ = 𝒟 c (⋃ n ≥ 1, L ^ n)                       := by rw [←zero_eq_empty, zero_add]       -- ∅ + L = L
    _ = ⋃ n ≥ 1, 𝒟 c (L ^ n)                       := by exact derL_factor_in c L -- push 𝒟 inside the union
    _ = ⋃ n ≥ 1, 𝒟 c (L ^ ((n - 1) + 1))           := by rw [lsub_add_cancel] -- n > 0 => n-1+1 = n
    _ = ⋃ n ≥ 1, 𝒟 c L * (L ^ (n-1))               := by rw [pow_iUnion] -- 𝒟 c (L^n+1) = 𝒟 c L * L^n DerL_pow
    _ = 𝒟 c L * ⋃ n ≥ 1, (L ^ (n-1))               := by rw [derL_factor_out] -- factor out (D c L)
    _ = 𝒟 c L * ⋃ m, L ^ m                         := by rw [reindex] -- n ∈ ℕ, n > 0 <=> m = n-1, m ∈ ℕ       --- reindex
    _ = 𝒟 c L * (L∗)                               := by rw [←star_is_iunion] -- rw [←kleene_closure_def] -- we get back a kleene closure
