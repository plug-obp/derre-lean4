-- import Mathlib.Init.Data.Nat.Notation
-- import Mathlib.Init.Set
-- import Mathlib.Data.Set.NAry
-- import Mathlib.Data.Set.Lattice
-- import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.GroupPower.Ring
import Mathlib.Algebra.Order.Kleene
import Mathlib.Tactic.Ring

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
lemma cons_nil (h: 𝒜): ∀ t: Word 𝒜, h :: t = [h] ↔ t = [] := by {
  intros t
  constructor
  . intros H
    simp [*] at *
    exact H
  . intros H
    simp [*] at *
}

lemma cons_ne_nil (h: 𝒜): ∀ t: Word 𝒜, h :: t ≠ [] := by {
  intro t
  apply List.cons_ne_nil h t
}

@[simp]
lemma word_append_nil: ∀ w: Word 𝒜, w ++ ([]: Word 𝒜) = w := by {
  intro w
  apply List.append_nil w
}

@[simp]
lemma nil_append_word: ∀ w: Word 𝒜, ([]: Word 𝒜) ++ w = w := by {
  intro w
  apply List.nil_append w
}

lemma nil_append_nil (w₁ w₂: Word 𝒜): w₁ ++ w₂ = [] ↔ w₁ = [] ∧ w₂ = [] := by {
  constructor
  . intro H
    cases w₁ with
    | nil =>
      rw [nil_append_word] at H
      simp [H]
    | cons h t =>
      exfalso
      contradiction
  . intro H
    rw [H.left, H.right]
    rfl
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

theorem one_def : (1 : Language α) = ({[]} : Set (Word α)) :=
  rfl

theorem add_def (l m : Language α) : l + m = (l ∪ m : Set (List α)) :=
  rfl

theorem mul_def (l m : Language α) : l * m = Set.image2 (· ++ ·) l m :=
  rfl

@[simp]
theorem not_mem_zero (x : Word α) : x ∉ (0 : Language α) :=
  id

@[simp]
theorem mem_one (x : Word α) : x ∈ (1 : Language α) ↔ x = [] := by rfl

@[simp]
theorem mem_letter (w : Word 𝒜) : w ∈ ({[a]}: Language 𝒜) ↔ w = [a] := by rfl

@[simp]
theorem mem_cons (h: 𝒜)(w : Word 𝒜) : h::w ∈ ({[h]}: Language 𝒜) ↔ w = [] := by {
  constructor
  . intro H
    rw [mem_letter] at H
    apply (cons_nil h w).mp
    exact H
  . intro H
    rw [mem_letter]
    rw [H]
}

@[simp]
theorem cons_not_mem (h a: 𝒜)(w : Word 𝒜) : h::w ∈ ({[a]}: Language 𝒜) ↔ h = a ∧ w = [] := by {
  constructor
  . intro H
    rw [mem_letter] at H
    injection H with hh ht
    exact ⟨hh, ht⟩
  . intro H
    rw [mem_letter]
    rw [H.1]
    rw [H.2]
}

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

@[simp]
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

theorem mem_iSup {ι : Sort v} {s : ι → Language 𝒜} {x: Word 𝒜} : (x ∈ ⨆ i, s i) ↔ ∃ i, x ∈ s i :=
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

instance Language.toKleeneAlgebra: KleeneAlgebra (Language 𝒜) :=
  { Language.toSemiring, Language.toCompleteAtomicBooleanAlgebra with
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
lemma ε_concatenation: ∀ L: Language 𝒜, 1 * L = L := by apply one_mul

@[simp]
lemma concatenation_ε: ∀ L: Language 𝒜, L ++ Lε = L := by apply mul_one

lemma word_inε_is_ε (w: Word 𝒜): w ∈ (1: Language 𝒜) ↔ w = [] := by {
  constructor
  . simp [one_def]
    intro Hw
    apply Hw
  . intro Hw
    rw [Hw]
    simp [one_def]
    rfl
}

lemma one_mul_one: ∀ L: Language 𝒜, 1 * L = 1 ↔ L = 1 := by {
  intro L
  constructor
  . intro H
    rw [← H]
    rw [ε_concatenation]
  . intro H
    rw [H]
    simp
}

lemma append_nil_iff_both_nil: ∀ s₁ s₂: Word 𝒜, s₁ ++ s₂ = [] ↔ s₁ = [] ∧ s₂ = [] := by {
  intros s₁ s₂
  constructor
  . intro H
    cases s₁ with
    | nil =>
      rw [nil_append_word] at H
      simp [H]
    | cons h t =>
      exfalso
      contradiction
  . intro H
    rw [H.left, H.right]
    rfl
}

@[simp]
lemma one_mul_one': ∀ L₁ L₂: Language 𝒜, L₁ * L₂ = 1 ↔ L₁ = 1 ∧ L₂ = 1 := by {
  intros L₁ L₂
  constructor
  . sorry
  . intro H
    rw [H.left, H.right]
    apply ε_concatenation
}

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

lemma tail_empty_singleton: {w: Word 𝒜 | (c :: w) ∈ ( {[c]}: Language 𝒜)} = Lε := by {
  ext _
  simp [Lε]
  constructor
  . intro H
    rw [H]
    rfl
  . intro H
    tauto
}

lemma empty_singleton (hne: c ≠ d): {w: Word 𝒜 | (c :: w) ∈ ( {[d]}: Language 𝒜)} = ∅ := by {
  ext w
  constructor
  . intro H
    simp at H
    exfalso
    tauto
  . intro H
    contradiction
}
