import Mathlib.Tactic.Basic --for Type*
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic
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
  | empty | token t => tauto
  | concatenation e₁ e₂ ihe₁ ihe₂ =>
    simp [ℒ, νB]
    rw [ihe₁, ihe₂]
  | union e₁ e₂ ihe₁ ihe₂ =>
    simp [ℒ, νB]
    rw [ihe₁, ihe₂]
  | star e _ =>
    simp [ℒ, νB, eps_mem_kstar]
}

theorem νB_false(e: Regex 𝒜): νB e = false ↔ [] ∉ ℒ e := by {
  rw [←νB_correct]
  --exact not_iff_not_of_iff (νB_correct e)
  constructor
  . intro H
    rw [H]
    tauto
  . induction e with
    | empty | token t => tauto
    | concatenation e₁ e₂ ihe₁ ihe₂ =>
      simp [νB]; tauto
    | union e₁ e₂ ihe₁ ihe₂ => simp [νB]; tauto
    | star _ _ => simp [νB]
}
/--!
# Membership is nullable derivative
-/
def D_chain(w: Word 𝒜) (r: Regex 𝒜): Regex 𝒜 := w.foldl (λ r c => 𝒟 c r) r
def brzozowski_mem(w: Word 𝒜) (r: Regex 𝒜): Prop := νB (D_chain w r)


def brzozowski_mem' : Word 𝒜 → Regex 𝒜 → Bool
  | [], R => νB R
  | h :: t, R => brzozowski_mem' t (𝒟 h R)

instance brzozowski_membership': Membership (Word 𝒜) (Regex 𝒜) := ⟨brzozowski_mem⟩

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

lemma brzozowski_mem'_empty(w: Word 𝒜): brzozowski_mem' w (Φ: Regex 𝒜) = false := by {
  induction w with
  | nil => simp [brzozowski_mem'] at *
  | cons c w ih =>
    simp [ brzozowski_mem', νB] at *
    exact ih
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

lemma brzozowski_not_mem'_union_iff(R₁ R₂ : Regex 𝒜) (w : Word 𝒜):
  brzozowski_mem' w (R₁ ⋃ R₂)=false ↔ brzozowski_mem' w R₁=false ∧ brzozowski_mem' w R₂=false
:= by {
  induction w generalizing R₁ R₂
  case nil =>
    simp [brzozowski_mem']
  case cons c w ih =>
    simp [brzozowski_mem']
    apply ih
}

lemma brzozowski_not_mem'_empty_concat (w : Word 𝒜):
  brzozowski_mem' w (Φ ⋅ R) = false
:= by {
  induction w generalizing R
  case nil => simp [brzozowski_mem']
  case cons c w ih =>
    simp [brzozowski_mem', δ]
    rw [brzozowski_not_mem'_union_iff]
    constructor
    . exact ih
    . exact ih
}

lemma brzozowski_not_mem'_empty_concat_right (w : Word 𝒜):
  brzozowski_mem' w (R ⋅ Φ) = false
:= by {
  induction w generalizing R
  case nil => simp [brzozowski_mem']
  case cons c w ih =>
    simp [brzozowski_mem', δ]
    rw [brzozowski_not_mem'_union_iff]
    constructor
    . exact ih
    . exact ih
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
      apply brzozowski_not_mem'_empty_concat
    . rw [List.cons.injEq]
      simp [D_empty, brzozowski_mem'_empty, and_false]
}

lemma brzozowski_mem'_char_delta_regex_iff(c: 𝒜):
  brzozowski_mem' [c] (δ r) = false
:= by {
  simp [brzozowski_mem', νB_false]
  intro H
  sorry
}

lemma brzozowski_mem'_eps(w: Word 𝒜):
  brzozowski_mem' w (ε: Regex 𝒜) ↔ w = []
:= by {
  induction w with
  | nil => simp [brzozowski_mem'] at *
  | cons c w =>
    simp [ brzozowski_mem', νB] at *
    apply brzozowski_not_mem'_empty_concat
}

lemma brzozowski_mem'_d_delta (c: 𝒜)(r₁ r₂: Regex 𝒜):
  brzozowski_mem' w (𝒟 c (δ r₁)) = false → brzozowski_mem' w (𝒟 c (δ r₁)⋅r₂) = false
:= by {
  intro _
  have hd: δ r₁ ≠ τ c := delta_ne_token r₁
  have h₂: 𝒟 c (δ r₁) = Φ := by {
    sorry
  }
  rw [h₂]
  apply brzozowski_not_mem'_empty_concat
}

lemma brzozowski_not_mem'_delta (c: 𝒜)(r: Regex 𝒜) :
  brzozowski_mem' w (𝒟 c (δ r)) = false
:= by {
  induction r with
  | empty | token _ =>
    simp [δ, brzozowski_mem'_empty]
  | concatenation e₁ e₂ ih₁ _ =>
    rw [δ_concatenation]
    simp [D_concatenation]
    rw [brzozowski_not_mem'_union_iff]
    simp [brzozowski_mem'] at *
    constructor
    . apply brzozowski_mem'_d_delta c e₁ (δ e₂)
      exact ih₁
    . have hd: δ e₂ ≠ τ c := delta_ne_token e₂
      have h₂: 𝒟 c (δ e₂) = Φ := by {
        sorry
      }
      rw [h₂]
      apply brzozowski_not_mem'_empty_concat_right
  | union e₁ e₂ ih₁ ih₂ =>
    rw [δ_union, D_union]
    rw [brzozowski_not_mem'_union_iff]
    tauto
  | star e _ =>
    rw [δ_star]
    rw [D_eps]
    rw [brzozowski_not_mem'_empty_concat]
}

lemma brzozowski_mem'_delta_iff(w: Word 𝒜)(R: Regex 𝒜):
  brzozowski_mem' w (δ R) = true ↔ w = [] ∧ [] ∈ ℒ R
:= by {
  induction w generalizing R
  case nil =>
    simp [brzozowski_mem']
    induction R with
    | empty | token c => tauto
    | concatenation e₁ e₂ ih₁ ih₂ =>
      simp [δ_concatenation]
      rw [ih₁, ih₂]
    | union e₁ e₂ ih₁ ih₂ =>
      simp [δ_union]
      rw [ih₁, ih₂]
    | star e _ =>
      simp [δ_star]
      apply eps_mem_kstar
  case cons h t _ =>
    constructor
    . intro H
      exfalso
      simp [brzozowski_mem'] at *
      induction R --generalizing t
      case empty =>
        simp [δ_empty, brzozowski_mem',brzozowski_mem'_empty] at *
      case token ch =>
        simp [δ_token, brzozowski_mem', brzozowski_mem'_empty] at *
      case concatenation e₁ e₂ ih₁ ih₂ =>
        simp [δ_concatenation, brzozowski_mem'_union_iff] at H
        rcases H with H₁ | H₂
        . sorry
        . sorry
      case union e₁ e₂ ih₁ ih₂ =>
        simp [δ_union, brzozowski_mem', brzozowski_mem'_union_iff,  brzozowski_mem'_empty] at *
        rcases  H with H₁ | H₂
        . apply ih₁ H₁
        . apply ih₂ H₂
      case star e _ =>
        simp [δ_star, brzozowski_mem', brzozowski_mem'_empty] at *
        simp [brzozowski_not_mem'_empty_concat] at *
    . intro H
      exfalso
      simp [List.cons_inj] at H
}

lemma brzozowski_mem'_concat_iff(R₁ R₂ : Regex 𝒜) (w : Word 𝒜) :
  brzozowski_mem' w (R₁ ⋅ R₂) ↔ ∃ w₁ w₂, w₁ ++ w₂ = w ∧ brzozowski_mem' w₁ R₁ ∧ brzozowski_mem' w₂ R₂
:= by {
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
      by_cases h: [] ∈ ℒ R₁
      . --[] ∈ ℒ R₁
        cases' w₁ with b t
        . --w₂ = []
          right
          rw [List.nil_append] at hw
          rw [hw] at hm₂
          exists []
          exists x
          constructor
          . tauto
          . constructor
            . -- this disappears since [] in ℒ R₁ -> [] ∈ νB δ R₁
              simp [brzozowski_mem', νB_correct]
              apply δ_holds
              exact h
            . exact hm₂
        . --w₂ = b::t
          left
          rw [List.cons_append, List.cons_eq_cons] at hw
          refine' ⟨t, w₂, hw.2, _, hm₂⟩
          rw [←hw.1]
          exact hm₁
      . --[] ∉ ℒ R₁
        left
        cases' w₁ with b t
        · rw [brzozowski_mem', νB_correct] at hm₁
          contradiction
        · rw [List.cons_append, List.cons_eq_cons] at hw
          refine' ⟨t, w₂, hw.2, _, hm₂⟩
          rw [←hw.1]
          exact hm₁
}

lemma brzozowski_mem'_star_iff(w: Word 𝒜) (R: Regex 𝒜):
  brzozowski_mem' w (R★) ↔ ∃ a w₁, a::w₁ = w ∧ (brzozowski_mem' [a] R) ∧ (brzozowski_mem' w₁ (R★))
:= by {
  simp [brzozowski_mem']

  induction R with
  | empty =>
    sorry

  | token ch => sorry
  | concatenation e₁ e₂ ih₁ ih₂ => sorry
  | union e₁ e₂ ih₁ ih₂ => sorry
  | star e ih => sorry
}

lemma brzozowski_mem_eps_iff(w: Word 𝒜): brzozowski_mem w ε ↔ w = [] := by {
  induction w with
  | nil => simp [brzozowski_mem, νB]
  | cons c w ih =>
    simp [brzozowski_mem, νB] at *
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

-- #reduce ([2, 3] ∈ ((τ 2 ⋅ τ 3): Regex ℕ))
-- #eval ([2, 3] ∈ ((τ 2 ⋅ τ 3): Regex ℕ))
