import Mathlib.Tactic.Basic

variable {C A : Type*} [ToString C] [ToString A]

class DeterministicSemantics (C A : Type*) :=
  (initial: Option C)
  (action: C → Option A)
  (execute: A → C → Option C)

class DeterministicInputSemantics (C A I : Type*) :=
  (initial: Option C)
  (action: Option I → C → Option A)
  (execute: A → Option I → C → Option C)

structure DeterministicOutputSemantics (C A O : Type*) :=
  (initial: Option C)
  (action: C → Option A)
  (execute: A → C → Option (O × C))

def ConfigurationOutputSemantics {C A: Type*} (o: DeterministicSemantics C A) : DeterministicOutputSemantics C A C := {
  initial := o.initial,
  action := o.action,
  execute := λ a c =>
    match o.execute a c with
    | none => none
    | some t => some ⟨t, t⟩

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

inductive ActionOrInit (A: Type*)
| init
| action (a: A)

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
