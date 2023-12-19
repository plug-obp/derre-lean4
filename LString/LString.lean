import «Gamine»

structure Config :=
  (s: String)
  (index: Nat)
deriving DecidableEq, Inhabited

instance : ToString Config where toString := λ c =>
  s!"\"{c.s}\"[{c.index}]"

instance : HasEval Char (Option Config) where eval := λ t c => match c with
  | none => false
  | some c => t = c.s.data[c.index]!

instance : HasEval Char Config where eval := λ t c =>
  t = c.s.data[c.index]!

def LStringSemantics (s: String): DeterministicSemantics Config Unit :=
{
  initial := if (s.length = 0) then Option.none else Option.some ⟨ s, 0 ⟩,
  action  := λ c => if (c.index + 1 < c.s.length) then Option.some Unit.unit else Option.none,
  execute := λ _ c => Option.some ⟨ c.s, c.index + 1 ⟩ ,
}

#eval (run (LStringSemantics "moo"))
#eval (run (LStringSemantics ""))
