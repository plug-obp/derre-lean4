
import Lean
import «SoupL».expressions
import «SoupL».statements
import «Gamine»

namespace soup
namespace syntx

open soup.expressions.syntx
open soup.statements.syntx

inductive Direction
| in
| out
deriving Inhabited, DecidableEq, Repr

structure Channel :=
  (name: String)
  (direction: Direction)
deriving Inhabited, DecidableEq, Repr

structure Piece :=
  (name: String)
  (urgent: Bool)
  (channel: Option Channel)
  (guard: Expression)
  (effect: Statement)
deriving Inhabited, DecidableEq, Repr

structure Soup :=
  (name: String)
  (vars: List (String × Expression))
  (pieces: List Piece)
deriving Inhabited, DecidableEq, Repr

namespace embedding
open Lean Elab Meta
open soup.expressions.syntx.embedding
open soup.statements.syntx.embedding

/-
Elaborating Soup
-/

declare_syntax_cat  direction
syntax "out"      : direction
syntax "!"        : direction
syntax "in"       : direction
syntax "?"        : direction


def elab_direction: Syntax → MetaM Expr
| `(direction| out)
| `(direction| !) => return .const ``Direction.out []
| `(direction| in)
| `(direction| ?) => return .const ``Direction.in []
| _ => Lean.Elab.throwUnsupportedSyntax

declare_syntax_cat channel
syntax ident direction : channel

def elab_channel: Syntax → MetaM Expr
| `(channel| $i:ident $d:direction) => do
  let i := mkStrLit i.getId.toString
  let d  ← elab_direction d
  mkAppM ``Channel.mk #[i, d]
| _ => Lean.Elab.throwUnsupportedSyntax

elab "chan " c:channel : term => elab_channel c

-- #reduce chan toot ?
-- #reduce chan toot !
-- #reduce chan toot out
-- #reduce chan toot in

syntax DEF := "≜" <|> "=="

declare_syntax_cat piece
syntax ident DEF "u"? (channel)? ("[" expression "]")? "/" statement : piece

def toPiece
  (i: TSyntax `ident)
  (urgent: Bool)
  (c: Option (TSyntax `channel))
  (e : Option (TSyntax `expression))
  (s : TSyntax `statement) : MetaM Expr := do
  let i := mkStrLit i.getId.toString
  let x := if urgent
    then .const ``Bool.true []
    else .const ``Bool.false []
  let c ← match c with
    | some c => mkAppM ``Option.some #[ ← elab_channel c ]
    | none => mkAppOptM ``Option.none #[ (Expr.const ``Channel []) ]
  let e ← match e with
    | some e => elab_expression e
    | none => mkAppM ``Expression.l #[← mkAppM ``Literal.b #[.const ``Bool.true []]]
  let s ← elab_statement s
  mkAppM ``Piece.mk #[i, x, c, e, s]

def elab_piece: Syntax → MetaM Expr
| `(piece| $i:ident $_ u $[ $c:channel ]? $[ [ $e ] ]? / $s) => toPiece i Bool.true  c e s
| `(piece| $i:ident $_   $[ $c:channel ]? $[ [ $e ] ]? / $s) => toPiece i Bool.false c e s
| _ => Lean.Elab.throwUnsupportedSyntax

elab "[piece| " p:piece "]" : term => elab_piece p

-- #reduce piece toto ≜ c ! [a] / b := a
-- #reduce [piece| toto ≜ u c ! [a] / b := a ]
-- #reduce [piece| ti ≜ c ! [a] / b := a ]

-- #reduce [piece| toto ≜  / b := a ]
-- #reduce [piece| toto ≜ [false] / b := a ]
-- #reduce [piece| toto ≜ u [false] / b := a ]
-- #reduce [piece| toto ≜ u  / b := a ]
-- #reduce [piece| toto ≜ u c ? / b := a ]

def soup0 := [
  [piece| xx ≜  / b := a ],
  [piece| yy ≜ [false] / b := a ]
]

-- #reduce soup0


declare_syntax_cat soup
syntax ident "vars" (ident "=" expression)* ";" ("|")? sepBy(piece, "|", "|", allowTrailingSep) : soup

def elab_soup: Syntax → MetaM Expr
| `(soup| $name:ident vars $[$vs:ident = $de]* ; $[ | ]? $pieces|*) => do
  let name := mkStrLit name.getId.toString
  let filtered :=
    Array.filter
      (fun pos => pos.getKind ≠ `«|» )
      pieces.elemsAndSeps
  let pcs :=
    Array.map
      (fun p => (elab_piece p))
      filtered
  let pcs ←
    Array.foldr
      (fun p ac => do mkAppM ``List.cons #[ ← p, ← ac ])
      (mkAppOptM ``List.nil #[ (Expr.const ``Piece []) ])
      pcs
  let arrayVars := Array.map (fun v:TSyntax `ident =>
    mkStrLit v.getId.toString) vs
  let arrayDefaultExp := Array.map elab_expression de
  let arrayVarDeafault := Array.zip arrayVars arrayDefaultExp
  let stringTy := Expr.const ``String []
  let expressionTy := Expr.const ``Expression []
  let productTy ← mkAppM ``Prod #[stringTy, expressionTy]

  let exprVarDefault ← Array.foldr
    (λ (v, d) ac => do
      let vr := v
      let de ← d
      let prod ←  mkAppM ``Prod.mk #[vr, de]
      mkAppM ``List.cons #[ prod, ← ac ])
    (mkAppOptM ``List.nil #[ productTy ])
    arrayVarDeafault
  mkAppM ``Soup.mk #[name, exprVarDefault, pcs]
| _ => Lean.Elab.throwUnsupportedSyntax

elab "[soup|" s:soup "]": term => elab_soup s

#check
[soup|
  my_soup
  vars a=2 b=3 c=a+b ;

  | xx ≜ / b := a ;
  | toto ≜ u c ? / b := a;
  |
]

def xx := [soup|
  my_soup
  vars a=2 b=true c=4;

  | xx ≜ / b := a ;
  | toto ≜ u c ? / b := a;
  |
]

def readExprFromFileName(fileName: String): TermElabM (Expr×Expr) := do
  let code ← IO.FS.readFile ⟨ fileName ⟩
  initSearchPath (← Lean.findSysroot) ["build/lib"]
  let env ← importModules #[ `ActionLanguageL4 ] {}
  let estx := Lean.Parser.runParserCategory env `term code
  match estx with
    | Except.ok stx =>
      let ty := Expr.const ``Soup []
      let expr ← Term.elabTerm stx (some ty)
      return (expr, ty)
    | Except.error e => throwError f!"parse error: {e}"

open Elab Tactic

syntax "soupFromFileName" str : tactic
elab_rules : tactic
| `(tactic| soupFromFileName $i:str) => withMainContext do
  let et ← readExprFromFileName i.getString
  closeMainGoal et.1


-- def xz : Soup := by {soupFromFileName "soup0.soup"}
-- #reduce xz

end embedding

end syntx



end soup
