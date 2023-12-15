import «RegEx».syntax
import «Gamine»

/-!
J.A. Brzozowski
**Derivatives of regular expressions**, *J. ACM*, 11 (1964), pp. 481-494

Brzozowski derivatives give a deterministic interpretation of regular expressions.
The Brzozowski construction is a DFA-like symbolic interpretation of regular expressions.
-/

namespace regex
namespace semantics
namespace brzozowski

variable {T: Type u} [DecidableEq T] [Repr T] [ToString T]
open regex.syntx

def nullable? : RExp T → Bool
| Φ => false
| ε => true
| τ _ => false
| (e₁ ⋃  e₂) => nullable? e₁ ∨ nullable? e₂
| (e₁ ⋅ e₂) => nullable? e₁ ∧ nullable? e₂
| _ ★ => true

def δ (e : RExp T) : RExp T :=
  if nullable? e then ε else Φ

def inhabited? : RExp T → Bool
| Φ => false
| ε => true
| τ _ => true
| (e₁ ⋃  e₂) => inhabited? e₁ ∨ inhabited? e₂
| (e₁ ⋅ e₂) => inhabited? e₁ ∧ inhabited? e₂
| _ ★ => true

universe v w t
class HasEval (α β: Type*) := (eval: α → β → Bool)

/--
  **Brzozowski** derivative
-/
def D {T α:Type*}[DecidableEq T][h: HasEval T α] (i: α) : RExp T → RExp T
| Φ         => Φ
| ε         => Φ
| τ c       => if (h.eval c i) then ε else Φ
| (e₁ ⋃ e₂) => (D i e₁) ⋃ₛ (D i e₂)
| (e₁ ⋅ e₂) => ((δ e₁) ⋅ₛ D i e₂) ⋃ₛ ( D i e₁ ⋅ₛ e₂)
| (e ★)     => (D i e) ⋅ₛ (e ★ₛ)

def D₀ {T α:Type*}[h: HasEval T α] (i: α) : RExp T → RExp T
| Φ         => Φ
| ε         => Φ
| τ c       => if (h.eval c i) then ε else Φ
| (e₁ ⋃ e₂) => (D₀ i e₁) ⋃ (D₀ i e₂)
| (e₁ ⋅ e₂) => ((δ e₁) ⋅ D₀ i e₂) ⋃ ( D₀ i e₁ ⋅ e₂)
| (e ★)     => (D₀ i e) ⋅ (e ★)

instance : HasEval T T where eval := (λ t i => t = i)
def D₁ (x:T) (e: RExp T) : RExp T :=
  D x e


def recognizes (L : RExp T) : List T → Bool
| [] => nullable? L
| c::w => recognizes (D c L) w

def name := τ "name" ⋅ τ "surname"

def address := τ "addr"

def nameoraddress := name ⋃ address

#reduce recognizes nameoraddress ["name", "surname"]

-- #check (τ 'c')

-- def x : String := "toto"

-- #check "cz"
-- #check String.mk ['c', 'z']

-- set_option maxRecDepth 10000
-- #reduce recognizes? (τ 'c' ⋅ τ 'y' ⋅ τ 'c' ⋅ τ 'y') ['c', 'z']
-- #reduce recognizes? (τ 1 ⋅ τ 2 ⋅ τ 3 ⋅ τ 4) [1, 2, 3, 4]

namespace gamine


structure REConfig (T: Type*) :=
  (e: RExp T)
deriving DecidableEq, Inhabited

instance {T: Type*} [ToString T]: ToString (REConfig T) where toString := λ c =>
  s!"{c.e}"

def derivativeT (T V: Type*) := (i : V) → (e : RExp T) → RExp T

instance{T V: Type*}: ToString $ derivativeT T V where toString := λ _ => "derT"

def BrzozowskiSemantics (T V: Type*)[DecidableEq T][ToString T] (e: RExp T) [HasEval T (Option V)] :
  DeterministicInputSemantics (REConfig T) (derivativeT T (Option V)) V:=
{
  initial := Option.some ⟨ e ⟩
  action  := λ _ c => if (inhabited? c.e) then Option.some D else Option.none
  execute := λ d i c => Option.some ⟨ d i c.e ⟩
}

def BrzozowskiSemantics₀ (T V: Type*) (e: RExp T) [HasEval T V] :
  DeterministicInputSemantics₀ (REConfig T) (derivativeT T V) V:=
{
  initial := Option.some ⟨ e ⟩
  action  := λ _ c => if (inhabited? c.e) then Option.some D₀ else Option.none
  execute := λ d i c => Option.some ⟨ d i c.e ⟩
}

def BrzozowskiSemantics₁ (T V: Type*) [DecidableEq T] (e: RExp T) [HasEval T V] :
  DeterministicInputSemantics₀ (REConfig T) (derivativeT T V) V:=
{
  initial := Option.some ⟨ e ⟩
  action  := λ _ c => if (inhabited? c.e) then Option.some D else Option.none
  execute := λ d i c => Option.some ⟨ d i c.e ⟩
}

end gamine

end brzozowski
end semantics
end regex
