-- import Mathlib.Init.Data.Nat.Notation
-- import Mathlib.Init.Set
-- import Mathlib.Data.Set.NAry
-- import Mathlib.Data.Set.Lattice
-- import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.GroupPower.Ring
import Mathlib.Algebra.Order.Kleene

-- import Mathlib.Tactic.Basic --for Type*

/-!
# Inspired by

- [Regular-expression derivatives reexamined](https://www.khoury.northeastern.edu/home/turon/re-deriv.pdf)
- [regex-derivative @ Tej Chajed](https://github.com/tchajed/regex-derivative/blob/master/regex.v)

- Matlib.Computability.Language
  A language is a Kleene Algebra:
    an idempotent semiring with a star operation.
-/

/-!
  # Standard names
  These simple definitions give standard names from the theory of computation.
-/

-- The 𝒜lphabet
variable
  { 𝒜 : Type* } -- 𝒜 because we cannot use Σ

/-!
  A word takes elements from the (arbitrary) alphabet above. *)
  **TODO**: I think that list is too restrictive,
    we need LinearOrder here or something similar
  Basically a word is a linear order on a subset of 𝒜
    LinearOrder X, where X ⊆ 𝒜
  Since 𝒜 is a type, X might be a subtype.
  List 𝒜 is just a particular case, where in fact we want 𝒞 = (ℕ, 𝒜).
  For instance a word is: (1, a), (2, b), (3, c), (4, a), (5, b), (6, c)
  where the linear order is given by ℕ, and 𝒜 is the alphabet.
-/
alias Word := List
instance: Append (Word 𝒜) := ⟨ List.append ⟩
instance: HAppend (Word 𝒜) (List 𝒜) (Word 𝒜) := ⟨ List.append ⟩
instance: HAppend (List 𝒜) (Word 𝒜) (Word 𝒜) := ⟨ List.append ⟩

/-
  Lift some list lemmas to words
-/
@[simp]
lemma word_append_nil: ∀ w: Word 𝒜, w ++ ([]: List 𝒜) = w := by {
  intro w
  apply List.append_nil w
}

@[simp]
lemma nil_append_word: ∀ w: Word 𝒜, ([]: List 𝒜) ++ w = w := by {
  intro w
  apply List.nil_append w
}

lemma word_append_assoc: ∀ w₁ w₂ w₃: Word 𝒜, w₁ ++ w₂ ++ w₃ = w₁ ++ (w₂ ++ w₃) := by {
  intros w₁ w₂ w₃
  apply List.append_assoc
}

/-!
A language is a set of words over an alphabet 𝒜.
As usual a set is a T → Prop, so in our case  (Word 𝒜) → Prop
-/

def Language 𝒜 := Set $ Word 𝒜
instance: Membership (Word 𝒜) (Language 𝒜) := ⟨Set.Mem⟩
instance: EmptyCollection (Language 𝒜) := ⟨ λ _ => False ⟩
instance: Union (Language 𝒜) := ⟨Set.union⟩
instance: Insert (Word 𝒜) (Language 𝒜) := ⟨Set.insert⟩

def singleWord (w: Word 𝒜) : Language 𝒜 := {b : Word 𝒜 | b = w}
instance: Singleton (Word 𝒜) (Language 𝒜) := ⟨singleWord⟩
def singleLetter[Singleton (Word 𝒜) (Language 𝒜)] (w: 𝒜) : Language 𝒜 := {[w]}
instance [Singleton (Word 𝒜) (Language 𝒜)]: Singleton 𝒜 (Language 𝒜) := ⟨singleLetter⟩
instance: HasSubset $ Language 𝒜 := ⟨Set.Subset⟩

@[ext]
theorem ext {l m : Language 𝒜} (h : ∀ (x : Word 𝒜), x ∈ l ↔ x ∈ m) : l = m :=
  Set.ext h

def concatenationL(L₁ L₂: Language 𝒜): Language 𝒜 :=
  Set.image2 (. ++ .) L₁ L₂
instance: Append (Language 𝒜) := ⟨concatenationL⟩

lemma concat_nil: ∀ L: Language 𝒜, L ++ {} = {} := by {
  intro L
  apply Set.image2_empty_right
}

lemma nil_concat: ∀ L: Language 𝒜, {} ++ L = {} := by {
  intro L
  apply Set.image2_empty_left
}

instance Language.toCompleteAtomicBooleanAlgebra: CompleteAtomicBooleanAlgebra (Language 𝒜) := inferInstanceAs (CompleteAtomicBooleanAlgebra (Set (Word 𝒜)))

instance Language.zero: Zero (Language 𝒜) := ⟨ ∅ ⟩
instance Language.one: One (Language 𝒜) := ⟨ { [] } ⟩
instance Language.inhabited: Inhabited (Language 𝒜) := ⟨ ∅ ⟩
instance Language.add: Add (Language 𝒜) := ⟨ Set.union ⟩
instance Language.mul: Mul (Language 𝒜) := ⟨ concatenationL ⟩

theorem zero_def : (0 : Language α) = (∅ : Set _) :=
  rfl

theorem one_def : (1 : Language α) = ({[]} : Set (List α)) :=
  rfl

theorem add_def (l m : Language α) : l + m = (l ∪ m : Set (List α)) :=
  rfl

theorem mul_def (l m : Language α) : l * m = Set.image2 (· ++ ·) l m :=
  rfl

@[simp]
theorem not_mem_zero (x : List α) : x ∉ (0 : Language α) :=
  id

@[simp]
theorem mem_one (x : List α) : x ∈ (1 : Language α) ↔ x = [] := by rfl

instance Language.toSemiring : Semiring (Language 𝒜) where
  add := (· + ·)
  add_assoc := Set.union_assoc
  zero := 0
  zero_add := Set.empty_union
  add_zero := Set.union_empty
  add_comm := Set.union_comm
  mul := (· * ·)
  mul_assoc _ _ _ := Set.image2_assoc List.append_assoc
  zero_mul _ := Set.image2_empty_left
  mul_zero _ := Set.image2_empty_right
  one := 1
  one_mul l := by {
    simp [mul_def, one_def, Set.image]
    conv in ([] ++ _) => rw [List.nil_append]
    simp [Set.image]
  }
  mul_one l := by {
    simp [mul_def, one_def, Set.image]
    conv in (_ ++ []) => rw [List.append_nil]
    simp [Set.image]
  }
  natCast n := if n = 0 then 0 else 1
  natCast_zero := rfl
  natCast_succ n := by cases n <;> simp [Nat.cast, add_def, zero_def]
  left_distrib _ _ _ := Set.image2_union_right
  right_distrib _ _ _ := Set.image2_union_left

/-
If L is a formal language, then Lⁱ, the iᵗʰ power of L, is the concatenation of L with itself i times.
That is, Lⁱ can be understood to be the set of all strings that can be represented as the concatenation of i strings in L.
This operation comes from free from the Monoid instance induced by the Semiring instance.
-/
-- def powL (L: Language 𝒜): ℕ → Language 𝒜
-- | 0 => { [] }
-- | (n+1) => L * (powL L n)
-- instance: HPow (Language 𝒜) ℕ (Language 𝒜) := ⟨powL⟩

@[simp]
lemma powL_zero (L: Language 𝒜): L ^ 0 = 1 := rfl

lemma powL_n (L: Language 𝒜): L ^ (n+1) = L * (L ^ n) := by apply pow_succ

@[simp]
lemma powL_one (L: Language 𝒜): L ^ 1 = L := by apply pow_one

/-
The free monoid L^* is called the "Kleene star of A". Also known as Kleene closure.
-/
def kleene_closure(L: Language 𝒜): Language 𝒜 :=
  { w | ∃ n: ℕ, w ∈ (L ^ n)}
instance Language.kstar: KStar (Language 𝒜) := ⟨kleene_closure⟩
postfix:1024 "∗" => KStar.kstar

lemma kleene_closure_def(L: Language 𝒜): L∗ = { w | ∃ n: ℕ, w ∈ (L ^ n)} := rfl

lemma one_in_l_star: ∀ L: Language 𝒜, 1 ⊆ L∗ := λ L w hw ↦ by { exists 0 }

theorem mem_iSup {ι : Sort v} {L : ι → Language 𝒜} {x: Word 𝒜} : (x ∈ ⨆ i, L i) ↔ ∃ i, x ∈ L i :=
  Set.mem_iUnion

theorem mem_kstar(L: Language 𝒜): w ∈ L∗ ↔ ∃ n: ℕ, w ∈ (L ^ n) := by {
  constructor <;> (rintro ⟨n, hw⟩; exact ⟨n, hw⟩)
}

theorem kstar_eq_iSup_pow (l : Language α) : l∗ = ⨆ i : ℕ, l ^ i := by
  ext x
  simp only [mem_iSup, mem_kstar]

theorem iSup_mul {ι : Sort v} (l : ι → Language 𝒜) (m : Language 𝒜) :
    (⨆ i, l i) * m = ⨆ i, l i * m :=
  Set.image2_iUnion_left _ _ _

theorem mul_iSup {ι : Sort v} (l : ι → Language 𝒜) (m : Language 𝒜) :
    (m * ⨆ i, l i) = ⨆ i, m * l i :=
  Set.image2_iUnion_right _ _ _

theorem le_mul_congr {l₁ l₂ m₁ m₂ : Language 𝒜} : l₁ ≤ m₁ → l₂ ≤ m₂ → l₁ * l₂ ≤ m₁ * m₂ := by
  intro h₁ h₂ x hx
  simp only [mul_def, exists_and_left, Set.mem_image2, Set.image_prod] at hx ⊢
  tauto

@[simp]
theorem one_add_self_mul_kstar_eq_kstar (l : Language 𝒜) : 1 + l * l∗ = l∗ := by
  simp only [kstar_eq_iSup_pow, mul_iSup, ← pow_succ, ← pow_zero l]
  exact sup_iSup_nat_succ _

theorem mul_self_kstar_comm (l : Language α) : l∗ * l = l * l∗ := by
  simp only [kstar_eq_iSup_pow, mul_iSup, iSup_mul, ← pow_succ, ← pow_succ']

@[simp]
theorem one_add_kstar_mul_self_eq_kstar (l : Language α) : 1 + l∗ * l = l∗ := by
  rw [mul_self_kstar_comm, one_add_self_mul_kstar_eq_kstar]

noncomputable instance Language.toKleeneAlgebra: KleeneAlgebra (Language 𝒜) :=
  { Language.toSemiring, Language.toCompleteAtomicBooleanAlgebra, Language.kstar with
    one_le_kstar := λ L w hw ↦ (by exists 0),
    mul_kstar_le_kstar := fun L ↦ (one_add_self_mul_kstar_eq_kstar L).le.trans' le_sup_right,
    kstar_mul_le_kstar := fun L ↦ (one_add_kstar_mul_self_eq_kstar L).le.trans' le_sup_right,
    kstar_mul_le_self := fun l m h ↦ by
      rw [kstar_eq_iSup_pow, iSup_mul]
      refine' iSup_le (fun n ↦ _)
      induction' n with n ih
      · simp
      rw [pow_succ', mul_assoc (l^n) l m]
      exact le_trans (le_mul_congr le_rfl h) ih,
    mul_kstar_le_self := fun l m h ↦ by
      rw [kstar_eq_iSup_pow, mul_iSup]
      refine' iSup_le (fun n ↦ _)
      induction' n with n ih
      · simp
      rw [pow_succ, ← mul_assoc m l (l^n)]
      exact le_trans (le_mul_congr h le_rfl) ih }

lemma zero_in_l_star: ∀ L: Language 𝒜, { [] } ⊆ L∗ := by {
  intro L
  simp [kleene_closure_def]
  intro w
  intro w_in_empty
  exists 0
}

theorem nil_mem_star (l : Language α) : [] ∈ l∗ := by {
  simp [kleene_closure_def]
  exists 0
}

lemma l_mem_l_star (L: Language 𝒜): ∀ w: Word 𝒜, w ∈ L → w ∈ L∗ := by {
  intro w
  intro w_in_L
  exists 1
  rw [powL_one]
  exact w_in_L
}

lemma star_to_star_star (L: Language 𝒜): w ∈ L∗ → w ∈ L∗∗ := by simp [kstar_mul_kstar]

lemma star_in_star_star (L: Language 𝒜): L∗ ⊆ L∗∗ := by {
  simp [kstar_mul_kstar]
  rintro ⟨⟩ <;> simp
}

lemma star_star_to_star (L: Language 𝒜): w ∈ L∗∗ → w ∈ L∗ := by simp [kstar_mul_kstar]

lemma star_star_in_star(L: Language 𝒜): L∗∗ ⊆ L∗ := by {
  simp [kstar_mul_kstar]
  rintro ⟨⟩ <;> simp
}

@[simp]
theorem kleene_closure_idempotent: ∀ L: Language 𝒜, L∗∗ = L∗ := λ _ ↦ by apply kstar_idem

@[simp]
lemma concat_kleene_closure_idem (L: Language 𝒜): L∗ * L∗ = L∗  := by apply kstar_mul_kstar

def positive_closure(L: Language 𝒜): Language 𝒜 := L ++ (L∗)
postfix:65   "⊕"    => positive_closure

def sigma (𝒜: Type*): Language 𝒜 := { [a] | a : 𝒜 }
-- notation "Σ" => sigma

-- The language of ε is the singleton set { [] }
--  L ε = { [] }
def Lε : Language 𝒜  := { [] }

@[simp]
lemma empty_concatenation: ∀ L: Language 𝒜, ∅ ++ L = ∅ := by apply zero_mul

@[simp]
lemma concatenation_empty: ∀ L: Language 𝒜, L ++ ∅ = ∅ := by apply mul_zero

@[simp]
lemma empty_pow: n > 0 → (∅: Language 𝒜) ^ n = ∅ := by apply zero_pow

@[simp]
lemma empty_star_is_ε: (∅: Language 𝒜)∗ = Lε := by {
  apply kstar_zero
}

@[simp]
lemma ε_concatenation: ∀ L: Language 𝒜, Lε ++ L = L := by apply one_mul

@[simp]
lemma concatenation_ε: ∀ L: Language 𝒜, L ++ Lε = L := by apply mul_one

lemma ε_pow: ∀ n: ℕ, (Lε: Language 𝒜) ^ n = Lε := by apply one_pow

@[simp]
lemma ε_star: (Lε: Language 𝒜)∗ = Lε := by apply kstar_one

@[simp]
lemma ε_positive_closure: (Lε: Language 𝒜) ⊕ = Lε := by simp [positive_closure, ε_star]

@[simp]
lemma ε_pow_positive_closure: ∀ n: ℕ, (Lε: Language 𝒜) ^ n ⊕ = Lε := by {
  intro n
  simp [positive_closure, ε_pow, ε_concatenation, ε_star]
}

/-!
  # Regular Expressions
  A regular expression is a symbolic representation of a set of strings.
  The set of strings represented by a regular expression 𝓇 is denoted by L(𝓇).
  The set of all regular expressions over an alphabet 𝒜 is denoted by ℛ(𝒜).
-/
inductive Regex 𝒜 :=
| empty
| token         (c: 𝒜)
| concatenation (e₁ e₂ : Regex 𝒜)
| union         (e₁ e₂ : Regex 𝒜)
| star          (e : Regex 𝒜)
deriving DecidableEq, Inhabited

 instance: EmptyCollection (Regex 𝒜) := ⟨ .empty ⟩

-- open Regex

notation:100 "Φ"    => Regex.empty
prefix:80    "τ"    => Regex.token
infixl:65    " ⋃ "  => Regex.union
infixl:70    "⋅"    => Regex.concatenation
postfix:65   "★"    => Regex.star

-- ε is a derived regex that matches only the empty string
def ε: Regex 𝒜 := .star .empty

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
| e₁ ⋅ e₂ => { w | ∃ w₁ w₂, w₁ ∈ L e₁ ∧ w₂ ∈ L e₂ ∧ w = w₁ ++ w₂}
| e₁ ⋃ e₂ => L e₁ ∪ L e₂
| e★      => { w | w ∈ star (L e) }

/--!
To write the correctness of the regex derivatiev, `DerL` defines derivative for a language (denotation side).
The derivative of a language L wrt a character c is the set of all words w for which c⋅w is in L
-/
def DerL (c: 𝒜) (L: Language 𝒜) : Language 𝒜 := { w | (c :: w) ∈ L }

lemma star_emptyL: star ∅ w → w = [] := by {
  intro H
  cases H with
  | star_empty => rfl
  | star_iter w₁ w₂ w₁_in_empty _ =>
    exfalso
    apply w₁_in_empty
}


-- ε represents the language consisting only of the empty word.
lemma words_in_L_ε (w: Word 𝒜): w ∈ L ε ↔ w = [] := by {
  constructor
  . apply star_emptyL
  . intro wH
    rw [wH]
    simp [L]
    apply star.star_empty
}

lemma eps_denotation: @L 𝒜 ε = {[]} := by {
  apply funext
  intro w
  apply propext
  apply words_in_L_ε
}

/--!

Equalities

-/

@[simp]
lemma L_empty: L (Φ: Regex 𝒜) = ∅ := by {
  apply funext
  intro w
  apply propext
  simp [L]
}

@[simp]
lemma L_token: ∀ c: 𝒜, L (τ c) = {[c]} := by {
  intro c
  apply funext
  intro w
  apply propext
  simp [L]
}

@[simp]
lemma L_union: ∀ e₁ e₂: Regex 𝒜, L (e₁ ⋃ e₂) = L e₁ ∪ L e₂ := by {
  intros e₁ e₂
  apply funext
  intro w
  apply propext
  simp [L]
}

lemma L_concatenation: ∀ e₁ e₂: Regex 𝒜, L (e₁ ⋅ e₂) = { w | ∃ w₁ w₂, w₁ ∈ L e₁ ∧ w₂ ∈ L e₂ ∧ w = w₁ ++ w₂} := by {
  intros e₁ e₂
  apply funext
  intro w
  apply propext
  simp [L]
}

lemma L_star: ∀ e: Regex 𝒜, L (e★) = { w | w ∈ star (L e) } := by {
  intro e
  apply funext
  intro w
  apply propext
  simp [L]
}

@[simp]
lemma Lε_star: @L 𝒜 (ε★) = Lε := by {
  apply funext
  intro w
  apply propext
  simp [L]
  sorry
}

@[simp]
lemma re_ε_concatenation: ∀ e: Regex 𝒜, L (ε ⋅ e) = L e := by {
  intro e
  apply funext
  intro w
  apply propext
  simp [L]
  sorry
}

@[simp]
lemma re_concatenation_ε: ∀ e: Regex 𝒜, L (e ⋅ ε) = L e := by {
  sorry
}

@[simp]
lemma Φ_concatenation: ∀ e: Regex 𝒜, L (Φ ⋅ e) = ∅ := by {
  intro e
  apply funext
  intro w
  apply propext
  simp [L]
  sorry
}

@[simp]
lemma concatenation_Φ: ∀ e: Regex 𝒜, L (e ⋅ Φ) = ∅ := by {
  intro e
  apply funext
  intro w
  apply propext
  simp [L]
  sorry
}

lemma concatenation_assoc: ∀ e₁ e₂ e₃: Regex 𝒜, L ((e₁ ⋅ e₂) ⋅ e₃) = L (e₁ ⋅ (e₂ ⋅ e₃)) := by {
  intros e₁ e₂ e₃
  apply funext
  intro w
  apply propext
  sorry
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
  intros r₁ r₂ r₃
  apply funext
  intro w
  apply propext
  simp [L]
  sorry
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
lemma union_empty': ∀ r: Regex 𝒜, L (Φ ⋃ r) = L r := by {
  intro r
  rw [union_comm]
  apply union_empty
}

@[simp]
lemma star_star: ∀ e: Regex 𝒜, L (e★★) = L (e★) := by {
  intro e
  apply funext
  intro w
  apply propext
  simp [L]
  constructor
  . intro H
    cases H with
    | star_empty =>
      apply star.star_empty
    | star_iter w₁ w₂ w₁_in_e hw₂ =>
      cases hw₂ with
      | star_empty =>
        conv in (w₁ ++ []) => apply word_append_nil
        exact w₁_in_e
      | star_iter w₃ w₄ w₃_in_e hw₄ =>
        apply star.star_iter
        . sorry
        . sorry
  . intro H
    cases H with
    | star_empty =>
      apply star.star_empty
    | star_iter w₁ w₂ w₁_in_e hw₂ =>
      apply star.star_iter
      . sorry
      . sorry
}


/--!
  # Nullability
  The nullability (`δ`) maps a Regex re to ε if the empty word [] is in the language of r

  `δ re =`
  - `ε if ε ∈ L re`
  - `Φ otherwise`
-/
def δ: Regex 𝒜 → Regex 𝒜
| Φ       => Φ
| τ _     => Φ
| e₁ ⋅ e₂ => δ e₁ ⋅ δ e₂
| e₁ ⋃ e₂ => δ e₁ ⋃ δ e₂
| _★      => ε

/-
  For any Regex re, the language of (δ re) contains only the empty Word [].
-/
lemma δ₁: ∀ w: Word 𝒜, w ∈ L (δ r) → w = [] := by {
  induction r with
  | empty | token _ =>
    simp [δ, L]
    intros w H
    contradiction
  | concatenation e₁ e₂ ih₁ ih₂ =>
    intro w
    intro concatenation
    cases w with
    | nil => rfl
    | cons w₁ w₂ =>
      cases concatenation with
      | intro xx Hxx =>
        cases Hxx with
        | intro yy Hyy =>
          cases Hyy with
          | intro zz Hzz =>
            cases Hzz with
            | intro tt Htt =>
            rw [Htt]
            specialize ih₁ xx
            specialize ih₂ yy
            simp [*] at *
            rw [ih₁]
            rw [ih₂]
            rfl
  | union e₁ e₂ ih₁ ih₂ =>
    intro w
    simp [δ, L]
    specialize ih₁ w
    specialize ih₂ w
    intro union
    cases union with
    | inl h =>
      apply ih₁
      exact h
    | inr h =>
      apply ih₂
      exact h
  | star e _ =>
    simp [δ]
    intros w h
    rw [←words_in_L_ε]
    exact h
}

/-
  If the empty word is in the language of δ re, then the empty word is in the language of the re
  `[] ∈ L (δ r) → [] ∈ (L r)`
-/
lemma δ₂: [] ∈ L (δ r) → [] ∈ (L r) := by {
  induction r with
  | empty =>
    simp [L]
  | token _ =>
    simp [L]
    intro h
    exfalso
    contradiction
  | concatenation e₁ e₂ ihe₁ ihe₂ =>
    intro H
    simp [L] at *
    cases H with
    | intro x Hx =>
      cases Hx with
      | intro y Hy =>
        cases Hy with
        | intro z Hz =>
          exists []
          constructor
          . apply ihe₁
            have hx : x = [] := by {
              apply δ₁
              exact y
            }
            rw [←hx]
            exact y
          . exists []
            constructor
            . apply ihe₂
              have hz : z = [] := by {
                apply δ₁
                exact Hz.left
              }
              rw [←hz]
              exact Hz.left
            . rfl
  | union e₁ e₂ ihe₁ ihe₂ =>
    intro H
    simp [L] at *
    cases H with
    | inl hl =>
      apply Or.inl
      apply ihe₁
      exact hl
    | inr hr =>
      apply Or.inr
      apply ihe₂
      exact hr
  | star e _ =>
    intro _
    apply star.star_empty
}

/-
  The compilation of δ₁ and δ₂.
  The language of δ r is the singleton { [] } and [] is in the languare of r.
-/
lemma δε: w ∈ L (δ r) → w = [] ∧ [] ∈ (L r) := by {
  intro H
  constructor
  . apply δ₁
    exact H
  . apply δ₂
    have hw : w = [] := by {
      apply δ₁
      exact H
    }
    rw [←hw]
    exact H
}

lemma he1 : ∀ x z : Word 𝒜, [] = x ++ z → x = [] ∧ z = [] := by {
  intros x y
  cases x with
  | nil => tauto
  | cons h t =>
    tauto
}

/-!
  If the empty word is in the language of r, then the empty word is in the language of δ r
-/
lemma δ_holds: [] ∈ L r → [] ∈ L (δ r) := by {
  induction r with
  | empty => simp [L]
  | token c =>
    simp [L]
    intro H
    exfalso
    contradiction
  | concatenation e₁ e₂ ihe₁ ihe₂ =>
    intro H
    simp [L] at *
    cases H with
    | intro x Hx =>
      cases Hx with
      | intro y Hy =>
        cases Hy with
        | intro z Hz =>
          have hx : x = [] ∧ z = [] := by {
            cases Hz with
            | intro lh rh =>
              apply he1
              exact rh
          }
          exists []
          constructor
          . apply ihe₁
            rw [hx.left] at y
            exact y
          . exists []
            constructor
            . apply ihe₂
              cases Hz with
              | intro hl hr =>
                rw [hx.right] at hl
                exact hl
            . rfl
  | union e₁ e₂ ihe₁ ihe₂ =>
    intro H
    simp [δ, L] at *
    cases H with
    | inl hl =>
      apply Or.inl
      apply ihe₁
      exact hl
    | inr hr =>
      apply Or.inr
      apply ihe₂
      exact hr
  | star e _ =>
    intro _
    apply star.star_empty
}

theorem δ_empty: [] ∈ L (δ r) ↔ [] ∈ L r := by {
  constructor
  . apply δ₂
  . apply δ_holds
}

/-
 We require decidable equality for 𝒜 (`DecidableEq 𝒜`).
 Technically, the only thing needed is a function that checks
 if a character `c` is in the set `t` captured by the token constructor `τ t`
 Equality is a particular case, in which the set `t` is a singleton.
 **TODO**:
 - I keep DecidableEq initially to have the first run at the proofs,
 - then I'll try to remove this constraint.
 - So in the end we will require of a letter 𝒜 in the token-type 𝒯 `Membership 𝓐 𝒯`,
`Membership 𝓐 𝒯` will give us symbolic Regex, where the token will encode a set of letters, with equality as a particular case.
-/
variable [deq𝒜: DecidableEq 𝒜]
/-!
# Derivative of a Regular Expression
-/
def D (c: 𝒜): Regex 𝒜 → Regex 𝒜
| Φ => Φ
| τ t => if t = c then ε else Φ
| e₁ ⋅ e₂ => (D c e₁ ⋅ e₂) ⋃ (δ e₁ ⋅ D c e₂)
| e₁ ⋃ e₂ => D c e₁ ⋃ D c e₂
| e★ => D c e ⋅ e★

/-
 The correctness theorem has the form that
  The language of the derivative (`L (D c re)`) and the derivative of the language (`D c (L re)`) are the same.
  That is `∀ w, w ∈ L (D c re) ↔ w ∈ D c (L re)`

  We will approach this proof by stating and proving separate lemmas for each direction of the bi-implication
  This will get us:
  1. L (D c re) ⊆ D c (L re)
  2. D c (L re) ⊆ L (D c re)
  3. thus L (D c re) = D c (L re)
-/

theorem LD_imp_DL: ∀ w: Word 𝒜,  w ∈ L (D c re) → w ∈ DerL c (L re) := by {
  intro w₁

  induction re with
  | empty =>
    simp [L]
    tauto
  | token t =>
    simp [D, L, DerL]
    intro Hw₁
    sorry

  | concatenation e₁ e₂ ihe₁ ihe₂ => sorry
  | union e₁ e₂ ihe₁ ihe₂ =>
    simp [L, DerL] at *
    intro H
    cases H with
    | inl Hw =>
      apply Or.inl
      apply ihe₁
      exact Hw
    | inr Hw =>
      apply Or.inr
      apply ihe₂
      exact Hw
  | star e ihe =>
    simp [DerL] at *
    intro Hw
    cases Hw with
    | star_empty => sorry
    | star_iter w₁ w₂ w₁_in_e hw₂ =>
      sorry
}

theorem DL_imp_LD: ∀ w: Word 𝒜, w ∈ DerL c (L re) → w ∈ L (D c re) := by {
  intros w₁ hw₁
  simp [DerL] at *
  induction re with
  | empty =>
    simp [L, D]
    tauto
  | token t =>
    simp [L, D]
    cases hw₁
    simp [*]
    rw [words_in_L_ε]
  | concatenation e₁ e₂ ihe₁ ihe₂ => sorry
  | union e₁ e₂ ihe₁ ihe₂ =>
    simp [L, D] at *
    cases hw₁ with
    | inl hw =>
      apply Or.inl
      apply ihe₁
      exact hw
    | inr hw =>
      apply Or.inr
      apply ihe₂
      exact hw
  | star e ihe =>
    simp [D] at *
    sorry
}

theorem LD_iff_DL: ∀ w: Word 𝒜,  w ∈ L (D c re) ↔ w ∈ DerL c (L re) := by {
  intro w
  constructor
  apply LD_imp_DL
  apply DL_imp_LD
}

theorem LD_sseq_DL (c: 𝒜): L (D c re) ⊆ DerL c (L re) := by {
  apply LD_imp_DL
}

theorem DL_sseq_LD (c: 𝒜): DerL c (L re) ⊆ L (D c re) := by {
  apply DL_imp_LD
}

theorem LD_eq_DL (c: 𝒜): L (D c re) = DerL c (L re) := by {
  apply Set.ext
  apply LD_iff_DL
}
