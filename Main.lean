import  «SoupL»
import «SoupL».expressions
import «SoupL».checker
import  «RegEx»
import Lean
open Lean

open Lean Elab Meta Command soup.syntx soup.expressions.syntx regex.syntx

def runCommandElabM (env : Environment) (x : CommandElabM α) : IO α := do
  let cmdCtx := {
    fileName     := "<empty>"
    fileMap      := .ofString ""
    tacticCache? := none
  }
  match (← liftM <| EIO.toIO' <| (x cmdCtx).run { env, maxRecDepth := maxRecDepth.defValue }) with
  | .ok (a, _) => return a
  | .error e =>
    throw <| IO.Error.userError s!"unexpected internal error: {← e.toMessageData.toString}"

def readExprFromFileName(fileName: String) (ty: Expr): TermElabM (Expr×Expr) := do
  let code ← IO.FS.readFile ⟨ fileName ⟩
  let env ← importModules #[ `SoupL, `RegEx ] {}
  let estx := Lean.Parser.runParserCategory env `term code
  match estx with
    | Except.ok stx =>
      let expr ← Term.elabTerm stx (some ty)
      return (expr, ty)
    | Except.error e => throwError f!"parse error: {e}"

unsafe def readSoupFromFileName (fileName : String) : IO Soup := do
  let env ← importModules #[ `SoupL ] {}
  runCommandElabM env <| runTermElabM fun _ => do
    let et ← readExprFromFileName fileName (Expr.const ``Soup [])
    Meta.evalExpr Soup et.2 et.1

unsafe def readRExpFromFileName (fileName : String) : IO $ RExp Expression:= do
  let env ← importModules #[ `RegEx, `SoupL ] {}
  runCommandElabM env <| runTermElabM fun _ => do
    let ty₁ := Expr.const ``Expression []
    let ty₀ :=  .app (Expr.const ``RExp [ (.succ .zero) ]) ty₁

    let et ← readExprFromFileName fileName ty₀
    Meta.evalExpr (RExp Expression) et.2 et.1

unsafe def check (s: Soup) (re: RExp Expression): IO Unit :=
  if  soup_regex_check? re s
  then IO.println s!"The soup `{s.name}` satisfies the property: `{re}`"
  else IO.println s!"The soup `{s.name}` does not satisfy the property: `{re}`"

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← Lean.findSysroot) [
      "build/lib"
    , "lake-packages/std/build/lib"
    , "SoupL/build/lib"
    , "Gamine/build/lib"
    , "RegEx/build/lib"
    , "lake-packages/mathlib/build/lib"]
  let fileName := args.head!
  let s : Soup ← timeit "time to read the soup:" $ readSoupFromFileName fileName
  let re: RExp Expression ← timeit "time to read the regex:" $ readRExpFromFileName (args.get! 1)
  IO.println s!"Hello, {s.name} vars {s.vars}"
  IO.println s!"RExp = {re}"
  timeit "time to check: " $ check s re
