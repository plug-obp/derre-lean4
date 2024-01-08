import Mathlib.Tactic.Basic --for Type*
import Mathlib.Data.List.Basic
import «RegEx».Language.language
import «RegEx».Language.derivative
import «RegEx».denotational
import «RegEx».brzozowski

variable [deq𝒜: DecidableEq 𝒜]

/--!
# Boolean nullability

- `δ` is nice however it produces regexes which are complex: ε ⋅ ε, ε ⋃ ε,
  which is fine denotationally, but they are not structurally equal to ε.

- νB is a boolean version of ν, maps a regex to true if the empty word is in the language of the regex.
  This allows us to define the membership function w ∈ R, without quotient types on the regexes (equality modulo an equivance relation).
  Of course this approch is not at all economical, but it is a first step towards the Brzozowski derivative.
-/
@[simp]
def νB: Regex 𝒜 → Bool
| Φ => false
| τ _ => false
| e₁ ⋅ e₂ => νB e₁ && νB e₂
| e₁ ⋃ e₂ => νB e₁ || νB e₂
| _★ => true

theorem νB_correct(e: Regex 𝒜): νB e = true ↔ [] ∈ ℒ e := by {
  induction e with
  | empty | token t =>
    simp [ℒ, νB]
    intro H
    contradiction
  | concatenation e₁ e₂ ihe₁ ihe₂ =>
    simp [ℒ, νB]
    rw [ihe₁, ihe₂]
    exact Iff.symm (eps_mem_concat_iff _ _)
  | union e₁ e₂ ihe₁ ihe₂ =>
    simp [ℒ, νB]
    rw [ihe₁, ihe₂, add_def]
    exact Iff.symm (eps_mem_union_iff _ _)
  | star e _ =>
    simp [ℒ, νB, eps_mem_kstar]
}
/--!
# Membership is nullable derivative
-/
def D_chain(w: Word 𝒜) (r: Regex 𝒜): Regex 𝒜 := w.foldl (λ r c => 𝒟 c r) r
def brzozowski_mem(w: Word 𝒜) (r: Regex 𝒜): Prop := νB (D_chain w r)
instance brzozowski_membership: Membership (Word 𝒜) (Regex 𝒜) := ⟨brzozowski_mem⟩

def brzozowski_mem' : List 𝒜 → Regex 𝒜 → Bool
  | [], R => νB R
  | h :: t, R => brzozowski_mem' t (𝒟 h R)

/--! the fold version is definitionally equal to the recursive version -/
lemma brzozowski_mem'_correct: ∀ (w: Word 𝒜) (r: Regex 𝒜), brzozowski_mem' w r = brzozowski_mem w r := by {
  intro w
  induction w with
  | nil => intro H; rfl
  | cons c w ih =>
    intro r
    simp [brzozowski_mem', brzozowski_mem, D_chain]
    rw [ih]
    rfl
}

lemma brzozowski_mem_empty(w: Word 𝒜):
  w ∉ (Φ: Regex 𝒜)
:= by {
  induction w with
  | nil => simp [Membership.mem, brzozowski_mem] at *
  | cons _ _ ih =>
    simp [ brzozowski_mem, νB] at *
    exact ih
}

lemma brzozowski_mem'_delta_iff(w: Word 𝒜)(R: Regex 𝒜):
  brzozowski_mem' w₁ (δ R) = true ↔ w₁ = [] ∧ [] ∈ ℒ R
:= by {
  sorry
}
lemma brzozowski_mem'_empty(w: Word 𝒜): brzozowski_mem' w (Φ: Regex 𝒜) = false := by {
  induction w with
  | nil => simp [brzozowski_mem'] at *
  | cons c w ih =>
    simp [ brzozowski_mem', νB] at *
    exact ih
}

lemma brzozowski_mem'_char_iff(w: Word 𝒜):
  brzozowski_mem' w (τ c: Regex 𝒜) ↔ w = [c]
:= by {
  cases' w with h t
  . simp [brzozowski_mem']
  cases' t with h t
  . simp [brzozowski_mem']
    split_ifs
    . tauto
    . rw [List.singleton_inj]; tauto
  . rw [brzozowski_mem', brzozowski_mem', D_token]
    split_ifs
    . rw [List.cons.injEq]
      simp [D_eps, brzozowski_mem'_empty]
      sorry
    . rw [List.cons.injEq]
      simp [D_empty, brzozowski_mem'_empty, and_false]
}

lemma brzozowski_mem'_union_iff(R₁ R₂ : Regex 𝒜) (w : Word 𝒜):
  brzozowski_mem' w (R₁ ⋃ R₂) ↔ brzozowski_mem' w R₁ ∨ brzozowski_mem' w R₂
:= by {
  induction' w with a x ih generalizing R₁ R₂
  case nil =>
    simp [brzozowski_mem'_empty, brzozowski_mem', D_union]
  . simp [brzozowski_mem', D_union]
    rw [ih]
}

lemma brzozowski_mem'_concat_iff(R₁ R₂ : Regex 𝒜) (w : Word 𝒜) :
    brzozowski_mem' w (R₁ ⋅ R₂) ↔ ∃ w₁ w₂, w₁ ++ w₂ = w ∧ brzozowski_mem' w₁ R₁ ∧ brzozowski_mem' w₂ R₂ := by
  induction' w with a x ih generalizing R₁ R₂
  case nil =>
    simp [brzozowski_mem'_empty, brzozowski_mem', D_concatenation]
    constructor
    . intro H
      exists []
      exists []
    . rintro ⟨ w₁, w₂, hw, hm₁, hm₂⟩
      simp [nil_append_nil] at hw
      rw [hw.1] at hm₁
      rw [hw.2] at hm₂
      simp [brzozowski_mem'] at *
      exact And.intro hm₁ hm₂
  . simp [brzozowski_mem', D_concatenation, brzozowski_mem'_union_iff]
    constructor
    . intro H
      rw [ih, ih] at H
      rcases H with ⟨w₁, w₂, hw, hm₁, hm₂⟩ | ⟨w₁, w₂, hw, hm₁, hm₂⟩
      . exists a::w₁
        exists w₂
        rw [brzozowski_mem']
        exact ⟨by rw [←hw, List.cons_append], hm₁, hm₂⟩
      . exists []
        exists (a::w₂)
        simp [brzozowski_mem']
        rw [brzozowski_mem'_delta_iff w₁ R₁] at hm₁
        constructor
        . rw [hm₁.1] at hw
          rw [nil_append_word, List.cons_inj] at *
          exact hw
        . constructor
          . rw [νB_correct]
            exact hm₁.2
          . exact hm₂
    . intro H
      rw [ih, ih]
      rcases H with ⟨w₁, w₂, hw, hm₁, hm₂⟩
      . left
        induction R₁ with
        | empty =>
          exfalso
          rw [brzozowski_mem'_empty] at hm₁
          contradiction
        | token t =>
          exists []
          simp [brzozowski_mem'_char_iff] at hm₁
          rw [hm₁] at hw
          injection hw with hw₁ hw₂
          simp [*] at *
          exists w₂
        | concatenation e₁ e₂ ih₁ ih₂ => sorry
        | union e₁ e₂ ih₁ ih₂ => sorry
        | star e ih => sorry




lemma brzozowski_mem_eps_iff(w: Word 𝒜): brzozowski_mem w ε ↔ w = [] := by {
  induction w with
  | nil => simp [brzozowski_mem, νB]
  | cons c w ih =>
    simp [brzozowski_mem, νB] at *
    sorry
}

lemma brzozowski_mem'_eps(w: Word 𝒜): brzozowski_mem' w ε ↔ w ∈ (ℒ ε) := by {
  induction w with
  | nil => simp [brzozowski_mem', νB]
  | cons c w ih =>
    simp [brzozowski_mem',  νB] at *
    sorry
}



instance mem.decidable : ∀ (w : Word 𝒜) (R : Regex 𝒜), Decidable (w ∈ R)
  | w, Φ => isFalse $ by {
    simp [Membership.mem, brzozowski_mem, D_chain];
    induction w with
    | nil => simp [D]
    | cons c w ih => simp [D]; exact ih
  }
  | w, τ t => by {
    induction w with
    | nil => exact Decidable.isFalse $ by simp [Membership.mem, brzozowski_mem, D_token]
    | cons c w ih =>
      simp [Membership.mem, brzozowski_mem, D_chain, D_token]
      by_cases h: c = t
      . simp [*] at *
        exact Decidable.isTrue $ by {
          rw [←h] at ih
          sorry
        }
      . simp [*] at *
        exact isFalse $ by {
          simp [*] at *
          sorry
        }
  }
  | w, e₁ ⋅ e₂ => by {
    simp [Membership.mem, brzozowski_mem, D_chain, D_concatenation]
    sorry
  }
  | w, e₁ ⋃ e₂ => by {
    simp [Membership.mem, brzozowski_mem, D_chain, D_union]
    sorry
  }
  | w, e★ => by {
    simp [Membership.mem, brzozowski_mem, D_chain, D_star]
    sorry
  }

example (w: Word 𝒜) (r: Regex 𝒜): w ∈ r ↔ νB (D_chain w r) := by {
  constructor
  . intro H
    exact H
  . intro H
    exact H
}

example: [2, 3] ∈ ((τ 2 ⋅ τ 3): Regex ℕ) := rfl


lemma ε_in_e_then_δ_eq_ε(e: Regex 𝒜): [] ∈ ℒ e → ℒ (δ e) = 1 := by {
  intro H
  rw [δ_eq_ν]
  rwa [ν_eq_one_iff]
}

lemma mem_eq_delta_der(w: Word 𝒜): w ∈ ℒ r → νB (D_chain w r) := by {
  induction r with
  | empty =>
    simp [ℒ, D_chain, δ]
    intro H
    contradiction
  | token t =>
    simp [ℒ, D_chain]
    intro H
    rw [H]
    --simp [*] at *
    sorry
  | concatenation e₁ e₂ ih₁ ih₂ =>
    simp [ℒ, D_chain] at *
    intro H
    sorry
  | union e₁ e₂ ih₁ ih₂ =>
    simp [ℒ, union_denotes]
    sorry
  | star e ih =>
    simp [ℒ, D_chain, D_star] at *
    intro H
    sorry
}

@[simp]
theorem mem_regex_iff_mem_language_regex (R : Regex 𝒜):
  ∀ w : Word 𝒜, w ∈ R ↔ w ∈ ℒ R
:= by {
  intro wx
  induction R --generalizing wx
  case empty => {
    constructor
    . intro H
      exfalso
      have H': wx ∉ Φ := brzozowski_mem_empty wx
      contradiction
    . intro H
      contradiction
  }
  case token => {
    simp [ℒ]
    sorry
  }
  case concatenation => {
    simp [ℒ]
    sorry
  }
  case union => {
    simp [ℒ]
    sorry
  }
  case star => {
    simp [ℒ]
    sorry
  }
}

noncomputable instance (r: Regex 𝒜): DecidablePred (· ∈ ℒ r) := fun _ ↦
  decidable_of_iff _ (mem_regex_iff_mem_language_regex _ _)

-- #eval ([2, 3] ∈ ((τ 2 ⋅ τ 3): Regex ℕ))
