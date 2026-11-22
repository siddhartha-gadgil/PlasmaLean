/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Lean
public import PlasmaLean.ResponseExt
public meta import PlasmaLean.ResponseExt

/-!
# Elaborating code from strings

Functions that parse and elaborate Lean code given as strings: sequences of commands, terms, and
whole inputs run through the frontend, returning the new declarations, their values and the
messages. The handlers `elab_term` and `elab_defs` expose some of them as tasks of the
`theory_loop` executable (see `PlasmaLean.ResponseExt`). Much of the frontend code is adapted
from LeanAide.
-/

public section

open Lean Meta Elab Parser Term Command

declare_syntax_cat command_seq

syntax command : command_seq

syntax command command_seq : command_seq

namespace PlasmaLean

def eg2 :=
"def a := 1
def b := 2 + a"

meta def parseCommandSeqBlock (s: String) : MetaM Syntax := do
  let .ok result := runParserCategory (← getEnv) `command_seq s | throwError "could not parse"
  return result

meta partial def getCommands (stx: Syntax) : List Syntax :=
  match stx with
  | `(command_seq| $cmd:command) => [cmd]
  | `(command_seq| $head:command $tail: command_seq) => head :: getCommands tail
  | _ => []

meta partial def viewCommandSeq (s: Syntax) : MetaM <| List Format := do
  match s with
  | `(command_seq| $cmd:command) => return [← PrettyPrinter.ppCommand cmd]
  | `(command_seq| $head:command $tail: command_seq) =>
    return [← PrettyPrinter.ppCommand head] ++ (← viewCommandSeq tail)
  | _ => throwUnsupportedSyntax

meta def viewParseCommandSeq (s: String) : MetaM <| List Format := do
  let stx ← parseCommandSeqBlock s
  viewCommandSeq stx


-- #eval viewParseCommandSeq eg2

meta def runCommandSeq (s: String) : TermElabM Unit := do
  let state ← saveState
  try
  let stx ← parseCommandSeqBlock s
  let cmds := getCommands stx
  for cmd in cmds do
    liftCommandElabM <| elabCommand cmd
  catch e =>
    restoreState state
    throw e

-- #eval runCommandSeq eg2

-- #eval b

elab "run_command_seq " s:str : command => liftTermElabM do
  let s' ← match s with
    | `(str | $s) => pure s.getString
  runCommandSeq s'

-- run_command_seq "def c := 2
-- def x := 3 + c
-- #eval x"

-- #eval c

def viewElabTerm (s: String) : TermElabM Format := do
  let .ok stx := runParserCategory (← getEnv) `term s | throwError "could not parse term"
  let e ←
    withoutErrToSorry do
      elabTerm stx none
  let e ← instantiateMVars e
  Term.synthesizeSyntheticMVarsNoPostponing
  -- if e.hasMVar then
  --   throwError "elabTerm produced a term with metavariables"
  -- else
    unsafe evalExpr Format (mkConst ``Format) (← mkAppM ``repr #[e])

@[response "elab_term"] def responseElabTerm (source: Json) : TermElabM Json := do
  let .ok s := source.getObjValAs? String "term" | throwError "Missing 'term' field in JSON"
  let fmt ← viewElabTerm s
  return Json.mkObj [("result", "ok"), ("output", fmt.pretty)]

-- Copied from LeanAide and modified

def univLine : String := "universe u"

def defaultTop : String := s!"{univLine}
set_option maxHeartbeats 10000000
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
"

def simpleRunFrontend
    (input : String)
    (env: Environment)
    (opts : Options := {}) (top : String := defaultTop)
    (fileName : String := "<input>")
    : IO (Environment × MessageLog) := unsafe do
  let inputCtx := Parser.mkInputContext (top ++ input) fileName
  let commandState := Command.mkState env (opts := opts)
  let parserState: ModuleParserState := {}
  let s ← IO.processCommands inputCtx parserState commandState
  pure (s.commandState.env, s.commandState.messages)

def hasNoErrors (msgs: MessageLog) : Bool :=
  msgs.toList.all fun msg => msg.severity != MessageSeverity.error

def runFrontendM (input: String) (modifyEnv: MessageLog → Bool := hasNoErrors)
    (top : String := defaultTop) : MetaM (Environment × MessageLog) := do
  let (env, msgs) ← simpleRunFrontend input (← getEnv) (top := top)
  if modifyEnv msgs then setEnv env
  return (env, msgs)

def runFrontEndForMessages (input: String) (modifyEnv: MessageLog → Bool := hasNoErrors)
    (top : String := defaultTop) : MetaM MessageLog := do
  let (_, msgs) ← runFrontendM input modifyEnv (top := top)
  return msgs

def elabFrontDefExprM (s: String) (n: Name) (modifyEnv: MessageLog → Bool := hasNoErrors)
    (top : String := defaultTop) : MetaM Expr := do
  let (env, _) ← runFrontendM s modifyEnv (top := top)
  let seek? : Option ConstantInfo :=  env.find? n
  match seek? with
  | none => throwError "Definition not found"
  | some seek => match seek.value? with
    | none => throwError "Definition has no value"
    | some val => return val

def elabFrontDefTypeValExprM (s: String) (n: Name) (modifyEnv: MessageLog → Bool := hasNoErrors)
    (top : String := defaultTop) : MetaM <| Expr × Expr := do
  let (env, _) ← runFrontendM s modifyEnv (top := top)
  let seek? : Option ConstantInfo :=  env.find? n
  match seek? with
  | none => throwError "Definition not found"
  | some seek => match seek.value? with
    | none => throwError "Definition has no value"
    | some val => return (seek.type, val)


def elabFrontThmExprM (s: String) (n: Name) (modifyEnv: MessageLog → Bool := hasNoErrors)
    (top : String := defaultTop) : MetaM Expr := do
  let (env, msgs) ← runFrontendM s modifyEnv (top := top)
  logInfo "Messages"
  for msg in msgs.toList do
    logInfo msg.data
  let seek? : Option ConstantInfo :=  env.find? n
  match seek? with
  | none => throwError "Definition not found"
  | some seek => return seek.type

def elabFrontDefsExprM (s: String) (ns: List Name) (modifyEnv: MessageLog → Bool := hasNoErrors)
    (top : String := defaultTop) : MetaM <| List (Name × Expr) × MessageLog := do
  let (env, msgs) ← runFrontendM s modifyEnv (top := top)
  let nameDefs := ns.filterMap fun n =>
    match env.find? n with
    | none => none
    | some c => c.value?.map (n, ·)
  return (nameDefs, msgs)

def elabFrontDefsViewM (s: String) (ns: List Name) (modifyEnv: MessageLog → Bool := hasNoErrors)
    (top : String := defaultTop) : MetaM <| List (Name × Format) × MessageLog := do
  let (ns, msgs) ← elabFrontDefsExprM s ns modifyEnv (top := top)
  let nameViews ← ns.mapM fun (n, e) => do
    let e ← mkAppM ``repr #[e]
    let s ← unsafe evalExpr Format (mkConst ``Format) e
    return (n, s)
  return (nameViews, msgs)

def elabPrintCmd (str : String) (top : String := defaultTop) : TermElabM Format := do
  let s := s!"#print {str}"
  let msgs ← runFrontEndForMessages s (modifyEnv := fun _ => false)  (top := top)
  logInfo "Messages"
  let msgs := msgs.toList.filter (·.severity == .information)
  let [msg] := msgs | throwError s!"Expected exactly one information message, got {msgs.length}"
  msg.data.format

-- #eval elabPrintCmd "Nat"

@[response "elab_defs"] def responseElabFrontDefsView (source: Json) : TermElabM Json := do
  let .ok ns := source.getObjValAs? (List Name) "names" | throwError "Missing 'names' field in JSON"
  let .ok code := source.getObjValAs? String "code" | throwError "Missing 'code' field in JSON"
  let (nameViews, msgs) ← elabFrontDefsViewM code ns
  let viewsJson := nameViews.map fun (n, fmt) =>
    Json.mkObj [("name", Json.str n.toString), ("view", Json.str fmt.pretty)]
  return Json.mkObj [("result", "ok"), ("definitions", toJson viewsJson),
    ("messages", toJson (← msgs.toList.mapM (fun msg => msg.data.toString)))]

def egVals : MetaM (List (Name × Format)) := do
  let (ns, _) ←  elabFrontDefsViewM eg2 [`a, `b]
  return ns

-- #eval egVals

def dropPrefixes : Name → Name
| .anonymous => .anonymous
| .str _ s => .str .anonymous s
| .num _ n => .num .anonymous n

  ---   #eval dropPrefixes `LeanAideCore.SimpleFrontend.elabFrontDefsExprAtM


def elabFrontDefsExprAtM (s: String) (pfx: Name) (modifyEnv: MessageLog → Bool := hasNoErrors)
    (top : String := defaultTop) : MetaM <| Array (Name × Expr) × MessageLog := do
  let (env, msgs) ← runFrontendM s modifyEnv (top := top)
  let decls := env.constants.map₁.toArray
  let ns := decls.filterMap (fun (n, _) => if pfx.isPrefixOf n then some n else none)
  logInfo "Looking for declarations with suffix `eg"
  for d in decls do
    if (`eg).isSuffixOf d.1 then
      logInfo s!"Found declaration: {d.1} with type {d.2.type}"
  let nameDefs := ns.filterMap fun n =>
    match env.find? n with
    | none => none
    | some c => c.value?.map (n, ·)
  logInfo "Messages"
  for msg in msgs.toList do
    logInfo msg.data
  logInfo s!"Found {ns.size} definitions with prefix {pfx}"
  return (nameDefs, msgs)

def elabFrontDefViewM (s: String) (n: Name) (modifyEnv: MessageLog → Bool := hasNoErrors)
    (top : String := defaultTop) : MetaM String := do
  let val ← elabFrontDefExprM s n modifyEnv (top := top)
  let fmt ←  ppExpr val
  return fmt.pretty


def elabFrontTheoremExprMStrict (type: String) (top : String := defaultTop) :
    MetaM <| Except (List String) Expr := do
  let n := `my_shiny_new_theorem
  let s := s!"set_option autoImplicit true in\ntheorem {n} : {type} := by sorry"
  let (env, logs) ←  runFrontendM s (top := top)
  let errors := logs.toList.filter (·.severity == MessageSeverity.error)
  let errorStrings ←  errors.mapM (·.data.toString)
  if errors.isEmpty then
    let seek? : Option ConstantInfo :=  env.find? n
    match seek? with
    | none => return Except.error ["Could not find theorem after elaboration"]
    | some seek => return Except.ok seek.type
  else
    return Except.error errorStrings

def elabFrontTheoremExprM (type: String) (top : String := defaultTop) :
    MetaM <| Except (List String) Expr := do
  let n := `my_shiny_new_theorem
  let s := s!"set_option autoImplicit true in\nnoncomputable def {n} : {type} := by sorry"
  let (env, logs) ←  runFrontendM s (top := top)
  let errors := logs.toList.filter (·.severity == MessageSeverity.error)
  let errorStrings ←  errors.mapM (·.data.toString)
  if errors.isEmpty then
    let seek? : Option ConstantInfo :=  env.find? n
    match seek? with
    | none => return Except.error ["Could not find theorem after elaboration"]
    | some seek => return Except.ok seek.type
  else
    return Except.error errorStrings


--    #eval elabFrontTheoremExprM "∀ n: Nat, n ≤ n + 1"

def elabFrontTypeExprM (type: String) (top : String := defaultTop) :
    MetaM <| Except (List String) Expr := do
  let n := `my_shiny_new_theorem
  let s := s!"def {n} : {type} := by sorry"
  let (env, logs) ←  runFrontendM s (top := top)
  let errors := logs.toList.filter (·.severity == MessageSeverity.error)
  let errorStrings ←  errors.mapM (·.data.toString)
  if errors.isEmpty then
    let seek? : Option ConstantInfo :=  env.find? n
    match seek? with
    | none => return Except.error ["Could not find theorem after elaboration"]
    | some seek => return Except.ok seek.type
  else
    return Except.error errorStrings

def checkElabFrontM(s: String) (top : String := defaultTop) : MetaM <| List String := do
  let log ← runFrontEndForMessages  s (top := top)
  let mut l := []
  for msg in log.toList do
    if msg.severity == MessageSeverity.error then
      let x ← msg.data.toString
      l := l.append [x]
  return l

def checkTypeElabFrontM(s: String) (top : String := defaultTop) : MetaM <| List String := do
  checkElabFrontM s!"example : {s} := by sorry" (top := top)

def checkTermElabFrontM(s: String) (top : String := defaultTop) : MetaM <| List String := do
  checkElabFrontM s!"example := {s}" (top := top)



--    #eval checkTermElabFrontM "(fun n => 3 : Nat → Nat)"

def newDeclarations (s: String) (top : String := defaultTop) : MetaM <| Array Name := do
  let constants := (← getEnv).constants
  let (env, _) ← runFrontendM s (top := top)
  let mut newConstants := #[]
  for (n, _) in env.constants do
    unless n.isInternal do
    if  !constants.contains n then
      newConstants := newConstants.push n
  return newConstants


def elabFrontDefsNewExprM (s: String) (top : String := defaultTop) :
    MetaM <| List (Name × Expr) × MessageLog := do
  let constants := (← getEnv).constants
  let (env, msgs) ← runFrontendM s (top := top)
  let mut nameDefs := #[]
  for (n, d) in env.constants do
    unless n.isInternal do
    if  !constants.contains n then
      match d.value? with
      | none => continue
      | some v => --    logToStdErr `leanaide.translate.info s!"Found new definition: {n} with
        nameDefs := nameDefs.push (n, v)
  return (nameDefs.toList, msgs)



end PlasmaLean
