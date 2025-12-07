import Mathlib.Tactic.Basic --for Type*
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic
import «RegEx».Language.language
import «RegEx».Language.derivative
import «RegEx».denotational
import «RegEx».brzozowski

variable [deq𝒜: DecidableEq 𝒜]
namespace regex_mem
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
def brzozowski_mem' : Word 𝒜 → Regex 𝒜 → Prop
  | [], R => νB R
  | h :: t, R => brzozowski_mem' t (𝒟 h R)

instance brzozowski_membership': Membership (Word 𝒜) (Regex 𝒜) := ⟨brzozowski_mem'⟩

lemma brzozowski_mem'_cons(c: 𝒜)(w: Word 𝒜)(R: Regex 𝒜):
  (c::w) ∈ R ↔ w ∈ (𝒟 c R)
:= by rfl

lemma brzozowski_mem'_empty(w: Word 𝒜):
  w ∉ (Φ: Regex 𝒜)
:= by {
  induction w with
  | nil => simp [Membership.mem, brzozowski_mem'] at *
  | cons _ _ ih =>
    simp [ brzozowski_mem', νB] at *
    exact ih
}

lemma brzozowski_mem'_union_iff(R₁ R₂ : Regex 𝒜) (w : Word 𝒜):
  w ∈ (R₁ ⋃ R₂) ↔ w ∈ R₁ ∨ w ∈ R₂
:= by {
  induction' w with a x ih generalizing R₁ R₂
  case nil =>
    simp [Membership.mem, brzozowski_mem', D_union] at *
  . simp [Membership.mem, brzozowski_mem', D_union] at *
    rw [ih]
}

lemma brzozowski_not_mem'_union_iff(R₁ R₂ : Regex 𝒜) (w : Word 𝒜):
  w ∉ (R₁ ⋃ R₂) ↔ w ∉ R₁ ∧ w ∉ R₂
:= by simp [brzozowski_mem'_union_iff]; tauto

lemma brzozowski_not_mem'_empty_concat (w : Word 𝒜) (R: Regex 𝒜):
  w ∉ (Φ ⋅ R)
:= by {
  induction w generalizing R
  case nil => simp [Membership.mem, brzozowski_mem']
  case cons c w ih =>
    rw [brzozowski_mem'_cons, D_concatenation]
    rw [brzozowski_not_mem'_union_iff]
    constructor
    . rw [D_empty]
      apply ih
    . rw [δ_empty]
      apply ih
}

lemma brzozowski_not_mem'_empty_concat_right (w : Word 𝒜) (R: Regex 𝒜):
  w ∉ (R ⋅ Φ)
:= by {
  induction w generalizing R
  case nil => simp [Membership.mem, brzozowski_mem']
  case cons c w ih =>
    simp [] at *
    rw [brzozowski_mem'_cons, D_concatenation]
    rw [D_empty]
    rw [brzozowski_not_mem'_union_iff]
    constructor
    . apply ih
    . apply ih
}


lemma brzozowski_mem'_eps(w: Word 𝒜):
  w ∈ (ε: Regex 𝒜) ↔ w = []
:= by {
  induction w with
  | nil => simp [Membership.mem, brzozowski_mem'] at *
  | cons c w =>
    simp [ brzozowski_mem', νB] at *
    apply brzozowski_not_mem'_empty_concat
}

lemma brzozowski_mem'_char_iff(w: Word 𝒜):
  w ∈ (τ c: Regex 𝒜) ↔ w = [c]
:= by {
  cases' w with h t
  . simp [Membership.mem, brzozowski_mem']
  cases' t with h₁ t
  . simp [Membership.mem, brzozowski_mem']
    split_ifs
    . tauto
    . rw [List.singleton_inj]; tauto
  . constructor
    . rw [List.cons.injEq]
      intro H
      exfalso
      rw [brzozowski_mem'_cons, brzozowski_mem'_cons] at H
      rw [D_token] at H
      split_ifs at H
      . rw [D_eps] at H
        simp [brzozowski_not_mem'_empty_concat] at H
      . rw [D_empty] at H
        simp [brzozowski_mem'_empty] at H
    . rw [List.cons.injEq]
      simp [*]
}

lemma brzozowski_mem'_empty_not_in_D_delta(c: 𝒜)(R: Regex 𝒜):
  [] ∉ 𝒟 c (δ R)
:= by {
  simp [Membership.mem, brzozowski_mem', νB_correct]
  simp [D_delta_language]
  tauto
}

lemma brzozowski_mem'_char_delta_regex_iff(c: 𝒜)(R: Regex 𝒜):
  [c] ∉ (δ R)
:= by {
  simp [brzozowski_mem'_cons]
  apply brzozowski_mem'_empty_not_in_D_delta
}

lemma brzozowski_not_mem'_D_delta (c: 𝒜)(w: Word 𝒜) (R: Regex 𝒜):
  w ∉ 𝒟 c (δ R)
:= by {
  induction' w with b x ih generalizing R
  case nil =>
    exact brzozowski_mem'_empty_not_in_D_delta c R
  . rw [brzozowski_mem'_cons]
    have hdl: ℒ (𝒟 c (δ R)) = ∅ := D_delta_language c R
    sorry
}

lemma cons_not_mem_delta (R: Regex 𝒜)(a: 𝒜)(x: Word 𝒜):
  a :: x ∉ δ R
:= by {
  induction' R with b r₁ r₂ ih₁ ih₂ r₁ r₂ ih₁ ih₂ r ih generalizing x
  . simp [δ]
    apply brzozowski_mem'_empty
  . simp [δ]
    apply brzozowski_mem'_empty
  . simp [brzozowski_mem'_cons] at *
    simp [δ_concatenation, brzozowski_mem'_union_iff]
    push_neg
    constructor
    . sorry
    . sorry
  . simp [δ]
    rw [brzozowski_mem'_union_iff]
    push_neg
    constructor
    . apply ih₁
    . apply ih₂
  . simp [δ]
    rw [←ε]
    rw [brzozowski_mem'_eps]
    tauto
}

lemma brzozowski_mem'_delta(R: Regex 𝒜) (w: Word 𝒜):
  w ∈ δ R ↔ w = [] ∧ [] ∈ R
:= by {
  induction' w with a x ih generalizing R
  case nil =>
    simp [Membership.mem, brzozowski_mem'] at *
    induction R with
    | empty | token _ => tauto
    | concatenation e₁ e₂ ih₁ ih₂ =>
      simp [D_concatenation, brzozowski_mem'_union_iff] at *
      tauto
    | union e₁ e₂ ih₁ ih₂ =>
      simp [D_union, brzozowski_mem'_union_iff] at *
      tauto
    | star e ih =>
      simp [D_star, brzozowski_mem'_union_iff] at *
  .
    -- simp []
    -- rw [brzozowski_mem'_cons]
    -- induction x with
    -- | nil => exact brzozowski_mem'_empty_not_in_D_delta a R
    -- | cons h t ih =>
    --   simp [brzozowski_mem'_cons, D_concatenation, brzozowski_mem'_union_iff] at *

    --   sorry
    constructor
    . rw [brzozowski_mem'_cons]
      intro H
      exfalso
      have hx: x ∉ 𝒟 a (δ R) := sorry
      contradiction
    . intro H
      exfalso
      tauto
}

lemma brzozowski_mem'_concat_iff(R₁ R₂ : Regex 𝒜) (w : Word 𝒜) :
  w ∈ (R₁ ⋅ R₂) ↔ ∃ w₁ w₂, w₁ ++ w₂ = w ∧ w₁ ∈ R₁ ∧ w₂ ∈ R₂
:= by {
  induction' w with a x ih generalizing R₁ R₂
  case nil =>
    simp [Membership.mem, brzozowski_mem'_empty, brzozowski_mem', D_concatenation]
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
  . rw [brzozowski_mem'_cons, D_concatenation]
    rw [brzozowski_mem'_union_iff]
    constructor
    . rw [ih, ih]
      rintro (⟨w₁, w₂, hw, hm₁, hm₂⟩ | ⟨w₁, w₂, hw, hm₁, hm₂⟩)
      . exists a::w₁
        exists w₂
        exact ⟨by rw [←hw, List.cons_append], hm₁, hm₂⟩
      . exists []
        exists (a::w₂)
        have hδ: w₁ ∈ δ R₁ ↔ w₁ = [] ∧ [] ∈ R₁ := by {
          exact brzozowski_mem'_delta R₁ w₁
        }
        rw [hδ] at hm₁
        constructor
        . rw [hm₁.1] at hw
          rw [nil_append_word, List.cons_inj] at *
          exact hw
        . constructor
          . exact hm₁.2
          . exact hm₂
    . intro H
      rw [ih, ih]
      rcases H with ⟨w₁, w₂, hw, hm₁, hm₂⟩
      by_cases h: [] ∈ R₁
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
              have hδ: [] ∈ δ R₁ ↔ [] ∈ R₁ := by {
                rw [brzozowski_mem'_delta]
                tauto
              }
              exact hδ.2 hm₁
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
        · --rw [Membership.mem, brzozowski_mem', νB_correct] at hm₁
          contradiction
        · rw [List.cons_append, List.cons_eq_cons] at hw
          refine' ⟨t, w₂, hw.2, _, hm₂⟩
          rw [←hw.1]
          exact hm₁
}









lemma brzozowski_mem'_d_delta (c: 𝒜)(w: Word 𝒜)(r₁ r₂: Regex 𝒜):
  w ∉ (𝒟 c (δ r₁)) → w ∉ (𝒟 c (δ r₁)⋅r₂)
:= by {
  intro H
  induction' w generalizing r₁ r₂
  case nil =>
    simp [Membership.mem, brzozowski_mem', brzozowski_mem'_empty, νB_correct] at *
    rw [D_delta_language] at *
    intro H₁
    exfalso
    contradiction
  case cons c₁ w ih =>
    rw [brzozowski_mem'_cons] at *
    sorry
}



lemma brzozowski_mem'_delta_iff(w: Word 𝒜)(R: Regex 𝒜):
  w ∈ (δ R) ↔ w = [] ∧ [] ∈ ℒ R
:= by {
  induction w generalizing R
  case nil =>
    simp [Membership.mem, brzozowski_mem', νB_correct]
    exact ε_in_δ_ε_in_r
  case cons h t ih =>
    simp
    rw [brzozowski_mem'_cons]
    intro H
    exfalso
    -- simp [brzozowski_mem'] at *
    induction R --generalizing t
    case empty =>
      simp [δ_empty,brzozowski_mem'_empty] at *
    case token ch =>
      simp [δ_token, brzozowski_mem'_empty] at *
    case concatenation e₁ e₂ ih₁ ih₂ =>
      sorry
    case union e₁ e₂ ih₁ ih₂ =>
      simp [δ_union, brzozowski_mem'_union_iff,  brzozowski_mem'_empty] at *
      rcases  H with H₁ | H₂
      . apply ih₁ H₁
      . apply ih₂ H₂
    case star e _ =>
      simp [δ_star, brzozowski_mem'_empty] at *
      simp [brzozowski_not_mem'_empty_concat] at *
}



lemma brzozowski_mem'_star_iff(w: Word 𝒜) (R: Regex 𝒜):
  w ∈ (R★) ↔ ∃ a w₁, a::w₁ = w ∧ ([a] ∈ R) ∧ (w₁ ∈ (R★))
:= by {
  simp [brzozowski_mem'_cons]
  induction R with
  | empty =>
    sorry

  | token ch => sorry
  | concatenation e₁ e₂ ih₁ ih₂ => sorry
  | union e₁ e₂ ih₁ ih₂ => sorry
  | star e ih => sorry
}

-- it should be computable when we remove all the sorrys
noncomputable instance mem.decidable : ∀ (w : Word 𝒜) (R : Regex 𝒜), Decidable (w ∈ R)
  | w, Φ => isFalse $ brzozowski_mem'_empty w
  | w, τ t => by rw [brzozowski_mem'_char_iff]; tauto
  | w, e₁ ⋅ e₂ => by rw [brzozowski_mem'_concat_iff]; tauto
  | w, e₁ ⋃ e₂ => by rw [brzozowski_mem'_union_iff]; tauto
  | w, e★ => by rw [brzozowski_mem'_star_iff]; tauto

example: [2, 3] ∈ ((τ 2 ⋅ τ 3): Regex ℕ) := rfl

lemma ε_in_e_then_δ_eq_ε(e: Regex 𝒜): [] ∈ ℒ e → ℒ (δ e) = 1 := by {
  intro H
  rw [δ_eq_ν]
  rwa [ν_eq_one_iff]
}

-- @[simp]
theorem mem_regex_iff_mem_language_regex (w : Word 𝒜)(R : Regex 𝒜):
  w ∈ R ↔ w ∈ ℒ R
:= by {
  induction R --generalizing wx
  case empty => simp [brzozowski_mem'_empty]; tauto
  case token => simp [brzozowski_mem'_char_iff]
  case concatenation r₁ r₂ ih₁ ih₂ =>
    simp [brzozowski_mem'_concat_iff];
    sorry
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

end regex_mem
