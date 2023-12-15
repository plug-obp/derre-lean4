import «Gamine»

structure Config :=
  (s: String)
  (index: Nat)

instance : ToString Config where toString := λ c =>
  s!"\"{c.s}\"[{c.index}]"

def LStringSemantics (s: String): DeterministicSemantics Config Unit :=
{
  initial := if (s.length = 0) then Option.none else Option.some ⟨ s, 0 ⟩,
  action  := λ c => if (c.index + 1 < c.s.length) then Option.some Unit.unit else Option.none,
  execute := λ _ c => Option.some ⟨ c.s, c.index + 1 ⟩ ,
}

#eval (run (LStringSemantics "moo"))
#eval (run (LStringSemantics ""))
