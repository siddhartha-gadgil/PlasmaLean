/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Lean
public import PlasmaLean.Elaborate
public meta import PlasmaLean.ResponseExt

/-!
# Tasks for checking and evaluating code

Two tasks for the `theory_loop` and `theory_server` executables, meant for automated use such as
evolutionary search, where many candidates are tried in turn:

* `check`: does the `"code"` compile? Reports structured messages, the new declarations and those
  using `sorry`;
* `eval`: elaborate the optional `"code"`, then evaluate the `"term"` in the environment it
  produces.

Both leave the shared environment unchanged unless the request sets `"modify_env": true`. They use
the frontend functions of `PlasmaLean.Elaborate`, passing `modifyEnv` accordingly.
-/

public section

open Lean Meta Elab Term

namespace PlasmaLean

/-- The optional field `"modify_env"` of a `check` or `eval` request (default `false`): whether the
definitions of the code are kept in the shared environment when the code has no errors. -/
def keepEnvField (source : Json) : Bool :=
  (source.getObjValAs? Bool "modify_env").toOption.getD false

/-- The number of lines of a prefix such as `defaultTop`, to report positions in submitted code. -/
def lineOffset (top : String) : Nat := (top.toList.filter (· == '\n')).length

/-- A message as JSON: severity, line and column in the submitted code (after `top`), and text. -/
def messageJson (msg : Message) (top : String := defaultTop) : IO Json := do
  let severity := match msg.severity with
    | .error => "error"
    | .warning => "warning"
    | .information => "info"
  return Json.mkObj [("severity", severity), ("line", toJson (msg.pos.line - lineOffset top)),
    ("column", toJson msg.pos.column), ("text", ← msg.data.toString)]

/-- The fields of a compilation report for code that took the environment from `oldEnv` to `env`
with messages `msgs`: `compiles` (no errors and no `sorry`), the number of `errors`, the new
`declarations` (without auxiliary ones such as `f.match_1`), those whose type or value uses
`sorry`, and the `messages`. -/
def compileFields (oldEnv env : Environment) (msgs : MessageLog) (top : String := defaultTop) :
    IO (List (String × Json)) := do
  let messages ← msgs.toList.mapM (messageJson · top)
  let errors := msgs.toList.filter (·.severity == .error)
  let newDecls := env.constants.map₂.toList.filter fun (n, _) => !oldEnv.contains n
  let sorryDecls := newDecls.filterMap fun (n, c) =>
    if c.type.hasSorry || ((c.value? (allowOpaque := true)).map Expr.hasSorry).getD false then
      some n
    else none
  return [("result", "ok"),
    ("compiles", toJson (errors.isEmpty && sorryDecls.isEmpty)),
    ("errors", toJson errors.length),
    ("declarations",
      toJson ((newDecls.map (·.1)).filter (!·.isInternalDetail) |>.map toString)),
    ("sorry", toJson (sorryDecls.map toString)),
    ("messages", toJson messages)]

/-- Elaborate `code` and report whether it compiles: the messages, the new declarations (without
auxiliary ones such as `f.match_1`), and the declarations whose type or value uses `sorry`.
Code compiles when there are no errors and no `sorry`. The new declarations are kept only if
`keep` is true and there are no errors. -/
def checkCodeM (code : String) (keep : Bool := false) (top : String := defaultTop) :
    MetaM Json := do
  let oldEnv ← getEnv
  let (env, msgs) ←
    runFrontendM code (modifyEnv := fun m => keep && hasNoErrors m) (top := top)
  return Json.mkObj (← compileFields oldEnv env msgs top)

/-- Task `check`: does the `"code"` compile? -/
@[response "check"] def responseCheck (source : Json) : TermElabM Json := do
  let .ok code := source.getObjValAs? String "code" | throwError "Missing 'code' field in JSON"
  checkCodeM code (keep := keepEnvField source)

/-- Elaborate `code`, then evaluate the `repr` of `term` in the environment it produces. If the
code has errors, nothing is evaluated. The definitions of the code are kept only if `keep` is true
and there are no errors; whatever elaborating the term adds is always discarded. -/
def evalWithCodeM (code term : String) (keep : Bool := false) (top : String := defaultTop) :
    TermElabM Json := do
  let (env, msgs) ←
    runFrontendM code (modifyEnv := fun m => keep && hasNoErrors m) (top := top)
  let messages ← msgs.toList.mapM (messageJson · top)
  unless hasNoErrors msgs do
    return Json.mkObj [("result", "error"), ("error", "the code has errors"),
      ("messages", toJson messages)]
  let fmt ← withoutModifyingEnv do
    setEnv env
    viewElabTerm term
  return Json.mkObj [("result", "ok"), ("output", fmt.pretty), ("messages", toJson messages)]

/-- Task `eval`: elaborate the optional `"code"`, then evaluate the `"term"`. -/
@[response "eval"] def responseEval (source : Json) : TermElabM Json := do
  let .ok term := source.getObjValAs? String "term" | throwError "Missing 'term' field in JSON"
  let code := (source.getObjValAs? String "code").toOption.getD ""
  evalWithCodeM code term (keep := keepEnvField source)

/-- The axioms a declaration of `env` depends on, transitively, or `none` if `env` has no such
declaration. A `sorry` anywhere in its proof or value shows up as the axiom `sorryAx`. -/
def axiomsIn (env : Environment) (n : Name) : MetaM (Option (List Name)) := do
  unless env.contains n do return none
  withoutModifyingEnv do
    setEnv env
    return some (← collectAxioms n).toList

/-- Elaborate `code` once and report: the compilation fields of `compileFields`; the axioms each
declaration in `axiomNames` depends on (`null` if it is missing); and, if `term?` is given and
every declaration in `require` exists without `sorry`, the `repr` of the term evaluated in the
environment produced by the code. The term is evaluated even if other parts of the code fail, so
that, for example, a candidate's measure can be computed when only its proofs fail. The new
declarations are kept only if `keep` is true and there are no errors. -/
def assessM (code : String) (axiomNames require : List Name) (term? : Option String)
    (keep : Bool := false) (top : String := defaultTop) : TermElabM Json := do
  let oldEnv ← getEnv
  let (env, msgs) ←
    runFrontendM code (modifyEnv := fun m => keep && hasNoErrors m) (top := top)
  let fields ← compileFields oldEnv env msgs top
  let axioms ← axiomNames.mapM fun n => do
    return (n.toString, toJson ((← axiomsIn env n).map (·.map toString)))
  let ready ← require.allM fun n => do
    return match ← axiomsIn env n with
      | none => false
      | some axs => !axs.contains ``sorryAx
  let evalFields ← match term? with
    | none => pure []
    | some t =>
      if !ready then
        pure [("evaluated", toJson false),
          ("eval_error", toJson "a required declaration is missing or uses sorry")]
      else
        try
          let fmt ← withoutModifyingEnv do
            setEnv env
            viewElabTerm t
          pure [("evaluated", toJson true), ("output", toJson fmt.pretty)]
        catch e =>
          pure [("evaluated", toJson false), ("eval_error", toJson (← e.toMessageData.toString))]
  return Json.mkObj (fields ++ [("axioms", Json.mkObj axioms)] ++ evalFields)

/-- Task `assess`: elaborate the `"code"` once, report compilation, the axioms of the declarations
named in `"axioms"`, and the value of the optional `"term"` when the declarations in `"require"`
exist without `sorry`. Used to evaluate candidates of an evolutionary search in one request. -/
@[response "assess"] def responseAssess (source : Json) : TermElabM Json := do
  let .ok code := source.getObjValAs? String "code" | throwError "Missing 'code' field in JSON"
  let axiomNames := (source.getObjValAs? (List Name) "axioms").toOption.getD []
  let require := (source.getObjValAs? (List Name) "require").toOption.getD []
  let term? := (source.getObjValAs? String "term").toOption
  assessM code axiomNames require term? (keep := keepEnvField source)

end PlasmaLean
