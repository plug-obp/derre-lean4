import Mathlib.Tactic.Basic


variable {C A : Type*} [ToString C] [ToString A]

/-
I use list for now because I want to get an implementation quickly.
We should use sets, however if the semantics is good enough there should not be many duplicates
-/
class Semantics (C A: Type*) :=
  (initial: List C)
  (actions: C → List A)
  (execute: A → C → List C)

class InputSemantics (C A I: Type*) :=
  (initial: List C)
  (actions: I → C → List A)
  (execute: A → I → C → List C)

def AsynchronousComposition{C₁ A₁ C₂ A₂}
  (l: Semantics C₁ A₁)
  (r: Semantics C₂ A₂)
: Semantics (C₁ × C₂) (A₁ ⊕ A₂) :=
{
  initial := List.product l.initial r.initial
  actions := λ (c₁, c₂) =>
    let las := (l.actions c₁).map λ a => Sum.inl a
    let ras := (r.actions c₂).map λ a => Sum.inr a
    las ++ ras
  execute := λ a (c₁, c₂) =>
    match a with
    | Sum.inl a => (l.execute a c₁).map λ t₁ => ⟨ t₁, c₂ ⟩
    | Sum.inr a => (r.execute a c₂).map λ t₂ => ⟨ c₁, t₂ ⟩
}

inductive ActionOrInit (A: Type*)
| init
| action (a: A)
open ActionOrInit

--l₁.bind fun a => l₂.map (Prod.mk a)
def SynchronousComposition{C₁ A₁ C₂ A₂}
  (l: Semantics C₁ A₁)
  (r: InputSemantics C₂ A₂ C₁)
: Semantics (Option C₁ × C₂) ((ActionOrInit A₁) × A₂) :=
{
  initial := List.product [none] r.initial
  actions := λ (c₁, c₂) =>
    match c₁ with
    | none =>
      l.initial.bind λ t₁ => (r.actions t₁ c₂).map (Prod.mk init)
    | some c₁ =>
      (l.actions c₁).bind λ a₁ =>
        (l.execute a₁ c₁).bind λ t₁ =>
          (r.actions t₁ c₂).map (Prod.mk (action a₁))

  execute := λ (a₁, a₂) (c₁, c₂) =>
    match a₁, c₁ with
    | init, _ =>
      l.initial.bind λ t₁ =>
        (r.execute a₂ t₁ c₂).map (Prod.mk t₁)
    | action a₁, some c₁ =>
      (l.execute a₁ c₁).bind λ t₁ =>
        (r.execute a₂ t₁ c₂).map (Prod.mk t₁)
    -- other cases should be impossible
    | _, _ => []
}

class DeterministicSemantics (C A: Type*) :=
  (initial: Option C)
  (action: C → Option A)
  (execute: A → C → Option C)

class DeterministicInputSemantics (C A I: Type*) :=
  (initial: Option C)
  (action: Option I → C → Option A)
  (execute: A → Option I → C → Option C)


class DeterministicInputSemantics₀ (C A I: Type*) :=
  (initial: Option C)
  (action: I → C → Option A)
  (execute: A → I → C → Option C)

def DeterministicInput2InputSemantics{C A I: Type*}
  (o: DeterministicInputSemantics₀ C A I)
: InputSemantics C A I :=
{
  initial := match o.initial with
    | none => []
    | some c => [c]
  actions := λ i c => match o.action i c with
    | none => []
    | some a => [a]
  execute := λ a i c => match o.execute a i c with
    | none => []
    | some t => [t]
}

structure DeterministicOutputSemantics (C A O: Type*) :=
  (initial: Option C)
  (action: C → Option A)
  (execute: A → C → Option (O × C))

def DeterministicSourceOutputSemantics {C A: Type*} (o: DeterministicSemantics C A) : DeterministicOutputSemantics C A C := {
  initial := o.initial,
  action := o.action,
  execute := λ a c =>
    match o.execute a c with
    | none => none
    | some t => some ⟨c, t⟩
}

def DeterministicActionOutputSemantics {C A: Type*} (o: DeterministicSemantics C A) : DeterministicOutputSemantics C A A := {
  initial := o.initial,
  action := o.action,
  execute := λ a c =>
    match o.execute a c with
    | none => none
    | some t => some ⟨a, t⟩
}

def Step (C A: Type*) := C × A × C
def DeterministicStepOutputSemantics {C A: Type*} (o: DeterministicSemantics C A) : DeterministicOutputSemantics C A (Step C A) := {
  initial := o.initial,
  action := o.action,
  execute := λ a c =>
    match o.execute a c with
    | none => none
    | some t => some ⟨⟨c, a, t⟩ , t⟩
}

structure BFSConfiguration (C: Type*)[ToString C] :=
  (atStart: Bool)
  (found: Option C)
  (frontier: List C)
  (known: List C)
deriving Repr

instance {C: Type*} [ToString C]: ToString (BFSConfiguration C) where
  toString := λ c => s!"bfs I={c.atStart}, found={c.found}, |F|={c.frontier.length}, |K|={c.known.length}"

inductive BFSAction
| next
| witness
deriving Repr

instance: ToString BFSAction where
  toString := λ a =>
    match a with
    | .next => "bfs_next"
    | .witness => "bfs_witness"

def AcceptingSemantics{C A: Type*}
  (o: Semantics C A)
  (accepting: C → Bool)
: Semantics (Bool × C) A :=
{
  initial := o.initial.map λ c => (accepting c, c)
  actions := λ (_, c) => o.actions c
  execute := λ a (_, c) =>
    (o.execute a c).map λ c => (accepting c, c)
}

def BFSSearchSemantics{C A: Type*}
[ToString C] [ToString A]
[BEq C][Inhabited C]
(o: Semantics C A)
(stopCondition: C → Bool)
: DeterministicSemantics (BFSConfiguration C) BFSAction :=
{
  initial := some ⟨ true, none,  [], [] ⟩
  action := λ c =>
    match c.found with
    | some _ =>
        if ¬c.atStart
        then some BFSAction.witness
        else none
    | none =>
        if (c.atStart ∨ c.frontier.length>0)
        then some BFSAction.next
        else none
  execute := λ a c =>
    match a with
    | .next =>
      if c.atStart
        then
          let neighbors := o.initial
          some ⟨false, neighbors.find? stopCondition,c.frontier ++ neighbors, c.known ++ neighbors⟩
        else
          let s := c.frontier.head!
          let actions := o.actions s
          -- dbg_trace s!"-->As{as}"
          let neighbors := actions.bind λ a => o.execute a s
          -- dbg_trace s!"-->source:{s} \n targets:{news}"
          let newNeighbors := neighbors.filter (λ conf => ¬ c.known.contains conf)
          -- dbg_trace s!"-->F{c.frontier}"
          some ⟨false, newNeighbors.find? stopCondition, c.frontier.tail! ++ newNeighbors, c.known ++ newNeighbors⟩
    | .witness =>
      dbg_trace s!"TODO: Compute counter-example"
      some ⟨ true, c.found, c.frontier, c.known ⟩
}


unsafe def runEx (s: DeterministicSemantics C A) (c : C) : C :=
Id.run do
  dbg_trace s!"C:{c}->A: {s.action c}"
  match (s.action c) with
  | none => c
  | some a => match s.execute a c with
    | none => c
    | some c₁ => runEx s c₁


unsafe def run (s: DeterministicSemantics C A) : Option C :=
  Id.run do
    let x := s.initial
    dbg_trace s!"iC: {x}"
    match x with
    | none => none
    | some c => some (runEx s c)




namespace composition



open ActionOrInit
def toString{A: Type*} [ToString A] : ActionOrInit A → String
| init => "init"
| action a => s!"{a}"
instance {A: Type*} [ToString A]: ToString (ActionOrInit A) where toString := toString


def ConfigurationBasedSynchronousComposition
  {C₁ A₁ C₂ A₂ : Type*}
  [ToString C₁]
  [ToString A₁]
  [ToString C₂]
  [ToString A₂]
  (l: DeterministicSemantics C₁ A₁)
  (r: DeterministicInputSemantics C₂ A₂ C₁)
  : DeterministicSemantics ((Option C₁) × C₂) ((ActionOrInit A₁) × A₂) :=
{
  initial:= match r.initial with
    | none => none
    | some c₂ => some ⟨ none, c₂ ⟩
  action := λ ⟨ c₁, c₂ ⟩ =>
    -- Id.run do
    -- dbg_trace s!"{l.initial} --> {r.action (l.initial) c₂}"
    match c₁ with
    | none =>
      let ini := l.initial
      match ini with
      | none => none
      | some t₁ =>
        match r.action t₁ c₂ with
                | none => none
                | some a₂ => some ⟨ init, a₂ ⟩
    | some c₁ =>
      match l.action c₁ with
      | none => none
      | some a₁ =>
        let t₁ := l.execute a₁ c₁
        match r.action t₁ c₂ with
        | none => none
        | some a₂ => some ⟨ action a₁, a₂ ⟩
  execute := λ ⟨a₁, a₂⟩ ⟨c₁, c₂⟩ =>
    let makeTarget (t₁: Option C₁) (t₂: Option C₂) : Option ((Option C₁) × C₂) :=
      match t₁, t₂ with
        | none, none => none
        | none, some t₂ => some ⟨ none, t₂ ⟩
        | some _, none => none
        | some t₁, some t₂ => some ⟨t₁, t₂⟩
    match a₁, c₁ with
    | init, none =>
      let t₁ := l.initial
      let t₂ := r.execute a₂ t₁ c₂
      makeTarget t₁ t₂
    | action a₁, some c₁ =>
      let t₁ := l.execute a₁ c₁
      let t₂ := r.execute a₂ t₁ c₂
      makeTarget t₁ t₂
    -- impossible cases
    | init, some _ => none
    | action _, none => none
}

end composition

infixl:70 "⨂" => composition.ConfigurationBasedSynchronousComposition
