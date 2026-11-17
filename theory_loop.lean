import Lean.Meta
import PlasmaLean.TaskHandlers

/-!
# The `theory_loop` executable

Reads tasks as JSON objects, one per line, from standard input, runs each with the handler
registered for its `"task"` field by `@[response "task"]` (see `PlasmaLean.ResponseExt`), and
prints the response as a JSON line on standard output. An empty line ends the loop. Tasks run in
an environment importing `Mathlib` and `PlasmaLean`, which is updated by each task.
-/

open Lean Meta PlasmaLean

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false


partial def process_loop (env: Environment) (getLine : Unit →  IO String)
  (putStrLn : String → IO Unit) : IO UInt32 := do
  IO.eprintln "Ready to run PlasmaLean tasks."
  let inp ← getLine ()
  if inp.isEmpty then
    pure 0
  else if inp.trimAscii.toString.isEmpty then
    process_loop env getLine putStrLn
  else
  match Json.parse inp with
  | Except.error e =>
    let output :=
      Json.mkObj [("status", Json.str "error"), ("message", Json.str s!"Failed to parse JSON: {e}")]
    putStrLn output.compress
    process_loop env getLine putStrLn
  | Except.ok js =>
    IO.eprintln s!"Received JSON: {js.pretty}"
    match js.getObjValAs? String "task" with
    | Except.error e =>
      let output :=
        Json.mkObj
          [("status", Json.str "error"),
          ("message", Json.str s!"Missing 'task' field in JSON: {e}")]
      putStrLn output.compress
      process_loop env getLine putStrLn
    | Except.ok task =>
      IO.eprintln "Running PlasmaLean task..."
      let (response, env) ←  responseFromTaskIO task js env
      let output := Json.mkObj [("status", Json.str "ok"), ("response", response)]
      putStrLn output.compress
      process_loop env getLine putStrLn

unsafe def main (_ : List String) : IO UInt32 := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ←
    importModules (loadExts := true) #[
    {module := `Mathlib},
    {module := `PlasmaLean}] {}
  let stdin ←  IO.getStdin
  let stdout ← IO.getStdout
  let getLine : Unit → IO String := fun _ => stdin.getLine
  let putStrLn : String → IO Unit := fun s => do
    stdout.putStrLn s
    stdout.flush
  process_loop env getLine putStrLn
