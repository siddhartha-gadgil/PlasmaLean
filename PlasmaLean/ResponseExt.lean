/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Lean

/-!
# Task responses

The attribute `@[response "task"]` registers a function `Json → TermElabM Json` as the handler of
the task named `task`. The functions below dispatch a task, given as a name and a JSON request, to
its handler. They are used by the `theory_loop` executable, which reads tasks as JSON lines and
prints the responses.
-/

public section

open Lean Meta Elab Term

namespace PlasmaLean

/-- `@[response "task"]` registers a function `Json → TermElabM Json` as the handler of `task`. -/
syntax (name := response) "response" str : attr

/-- Environment extension mapping task names to the names of their handler functions. -/
initialize responseExt :
    SimpleScopedEnvExtension (Name × String) (Std.HashMap String Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (n, key) =>
        m.insert key n
    initial := {}
  }

/-- The task name given in a `response` attribute. -/
def responseKeyM : Syntax → CoreM String
  | `(attr| response $str) => return str.getString
  | _ => throwError "invalid response attribute"

initialize registerBuiltinAttribute {
  name := `response
  descr := "Lean response given task name"
  add := fun decl stx kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let expectedType : Expr ← mkArrow (mkConst ``Json) (← mkAppM ``TermElabM #[Lean.mkConst ``Json])
    unless ← isDefEq declTy expectedType do
      throwError
        s!"response: {decl} has type {declTy}, but expected {expectedType}"
    let key ← responseKeyM stx
    responseExt.add (decl, key) kind
}

/-- The handler registered for a task name, or an error listing the available tasks. -/
def responseMatches (key : String) : CoreM Name := do
  let allKeys := (responseExt.getState (← getEnv)).toArray.map (fun (k, _) => k)
  let some fn :=
    (responseExt.getState (← getEnv)).get? key | throwError
      s!"response: no function found for task '{key}'; available tasks are {allKeys.toList}"
  return fn

/-- Run the handler named `f` on a request. -/
def responseFromFunc (f : Name) (source : Json) : TermElabM Json := do
  let response ←
    unsafe evalConst (Json → TermElabM Json) f
  response source

/-- Run the handler registered for `task` on a request. -/
def responseFromTask (task : String) (source : Json) : TermElabM Json := do
  let f ← responseMatches task
  responseFromFunc f source

/-- Run the handler registered for `task`, turning any error into an error response. -/
def responseFromTaskSafe (task : String) (source : Json) : TermElabM Json := do
  try
    let f ← responseMatches task
    responseFromFunc f source
  catch e =>
    logError m!"Error in responseFromTaskSafe: {e.toMessageData}"
    return Json.mkObj [("result", "error"),
      ("error", s!"failed to get response for task '{task}': {← e.toMessageData.toString}")]

/-- `responseFromTaskSafe` in `CoreM`. -/
def responseFromTaskSafeCore (task : String) (source : Json) : CoreM Json :=
  (responseFromTaskSafe task source).run' {} |>.run' {}

/-- Run a task in a given environment, returning the response and the updated environment. -/
def responseFromTaskIO (task : String) (source : Json) (env : Environment) :
    IO (Json × Environment) := do
  let coreM := responseFromTaskSafeCore task source
  let eio := coreM.run {fileName := "<theory_loop>", fileMap := {source := "", positions := #[]}}
    {env}
  match ← eio.toIO' with
  | Except.ok (result, state) => return (result, state.env)
  | Except.error e => IO.throwServerError <| ← e.toMessageData.toString

end PlasmaLean
