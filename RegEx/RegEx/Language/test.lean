-- Import relevant Lean libraries


-- Define the regular expression data type
inductive regex (α : Type) : Type
| empty : regex α
| eps : regex α
| char : α → regex α
| union : regex α → regex α → regex α
| concat : regex α → regex α → regex α
| star : regex α → regex α

-- Define is_nullable function to check if a regular expression can produce an empty string
def is_nullable {α : Type} : regex α → Bool
| regex.empty => false
| regex.eps => true
| (regex.char _) => false
| (regex.union r1 r2) => is_nullable r1 || is_nullable r2
| (regex.concat r1 r2) => is_nullable r1 && is_nullable r2
| (regex.star _) => true

-- Define the derivative function
def derivative {α : Type} [DecidableEq α ] : regex α → α → regex α
| regex.empty => λ _ => regex.empty
| regex.eps => λ _ => regex.empty
| (regex.char a) => λ c => if a = c then regex.eps else regex.empty
| (regex.union r1 r2) => λ c => regex.union (derivative r1 c) (derivative r2 c)
| (regex.concat r1 r2) => λ c => if is_nullable r1 then regex.union (regex.concat (derivative r1 c) r2) (derivative r2 c) else regex.concat (derivative r1 c) r2
| (regex.star r) => λ c => regex.concat (derivative r c) (regex.star r)



-- Define the Kleene star of a regular expression
def star {α : Type} : regex α → regex α
| r := regex.star r

-- Prove the lemma using Lean tactics
lemma derivative_concat {α : Type} (L : regex α) (c : α) (n : ℕ) :
  derivative (list.foldr regex.concat (regex.char c) (list.repeat L n)) c =
  list.foldr regex.concat (derivative L c) (list.repeat L (n-1)) :=
begin
  -- Use induction on n
  induction n with k ih,
  { -- Base case
    simp only [list.foldr, list.repeat, derivative],
    refl
  },
  { -- Inductive step
    simp only [list.foldr, list.repeat, derivative],
    cases is_nullable L,
    { -- Case where L is nullable
      simp only [if_true, ih],
      refl
    },
    { -- Case where L is not nullable
      simp only [if_false],
      exact ih
    }
  }
end
