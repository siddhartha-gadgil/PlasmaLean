import Std.Http
import Lean.Meta
import PlasmaLean.TaskHandlers

/-!
# The `theory_server` executable

An HTTP version of `theory_loop`, built on the HTTP/1.1 server in `Std.Http`.

* `POST /` with a JSON task as the body, such as `{"task": "elab_term", "term": "2 + 3"}`, runs
  the handler registered for the task by `@[response "task"]` (see `PlasmaLean.ResponseExt`) and
  answers with the same JSON as `theory_loop`: `{"status": "ok", "response": …}`.
* `POST /reset` restores the starting environment.
* `GET /` serves a web page for writing tasks, with examples, and showing the responses.

Usage: `lake exe theory_server [port]` (default port 8080). Tasks run in an environment importing
`Mathlib` and `PlasmaLean`. As in `theory_loop`, the environment is shared and updated by each task
(definitions persist), and tasks run one at a time. Tasks can run arbitrary Lean code, including
`#eval` of `IO` actions, so the server only listens on `127.0.0.1`.
-/

open Lean Meta PlasmaLean
open Std Async Http Server

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

/-- The web page served on `GET /`; `%%TASKS%%` is replaced by the list of available tasks. -/
def pageTemplate : String := r##"<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>PlasmaLean Tasks</title>
<style>
:root {
  --ink: #172033; --muted: #5b6578; --line: #dfe2e8; --paper: #fbfaf6; --card: #ffffff;
  --accent: #0b7285; --accent-soft: #e6f4f6; --bad: #c92a2a; --bad-soft: #fdecec;
  --good: #2b8a3e; --good-soft: #ebf7ee; --code: #0f1626; --code-ink: #e6ebf5;
  color-scheme: light;
}
@media (prefers-color-scheme: dark) {
  :root:not([data-theme="light"]) {
    --ink: #e6eaf2; --muted: #a3adbf; --line: #2a3448; --paper: #0e1525; --card: #152035;
    --accent: #3bc9db; --accent-soft: #11313a; --bad: #ff8787; --bad-soft: #3a1a1a;
    --good: #69db7c; --good-soft: #13301b; --code: #080d18; --code-ink: #e6ebf5;
    color-scheme: dark;
  }
}
* { box-sizing: border-box; }
body { margin: 0; background: var(--paper); color: var(--ink);
  font: 16px/1.5 system-ui, -apple-system, "Segoe UI", sans-serif; }
main { max-width: 1180px; margin: 0 auto; padding: 28px 20px 48px; }
h1 { font-size: 28px; margin: 0 0 4px; }
.lead { color: var(--muted); margin: 0 0 22px; max-width: 70ch; }
.grid { display: grid; grid-template-columns: minmax(0, 1fr) minmax(0, 1fr); gap: 22px; }
@media (max-width: 860px) { .grid { grid-template-columns: minmax(0, 1fr); } }
.panel { background: var(--card); border: 1px solid var(--line); border-radius: 12px; padding: 16px; }
h2 { font-size: 15px; letter-spacing: .08em; text-transform: uppercase; color: var(--muted); margin: 0 0 10px; }
.examples { display: flex; flex-wrap: wrap; gap: 8px; margin-bottom: 12px; }
button { font: 600 14px system-ui, sans-serif; border-radius: 8px; padding: 7px 12px; cursor: pointer;
  border: 1px solid var(--line); background: var(--paper); color: var(--ink); }
button:hover { border-color: var(--accent); }
button.primary { background: var(--accent); border-color: var(--accent); color: var(--paper); }
button:focus-visible, textarea:focus-visible { outline: 2px solid var(--accent); outline-offset: 1px; }
textarea { width: 100%; min-height: 260px; resize: vertical; font: 14px/1.5 ui-monospace, "JetBrains Mono", Menlo, monospace;
  color: var(--ink); background: var(--paper); border: 1px solid var(--line); border-radius: 8px; padding: 10px; }
.actions { display: flex; flex-wrap: wrap; gap: 10px; align-items: center; margin-top: 10px; }
.status { font-size: 14px; color: var(--muted); }
.tasks code, .hint code { background: var(--accent-soft); padding: 1px 6px; border-radius: 5px; font-size: 13px; }
.hint { font-size: 14px; color: var(--muted); margin: 10px 0 0; }
pre { background: var(--code); color: var(--code-ink); border-radius: 8px; padding: 12px; overflow: auto;
  font: 13px/1.5 ui-monospace, Menlo, monospace; margin: 8px 0 0; max-height: 360px; white-space: pre-wrap; }
.badge { display: inline-block; font-weight: 700; font-size: 13px; padding: 2px 9px; border-radius: 999px; }
.badge.ok { background: var(--good-soft); color: var(--good); }
.badge.err { background: var(--bad-soft); color: var(--bad); }
.result { margin-top: 4px; }
.result table { border-collapse: collapse; width: 100%; font-size: 14px; margin-top: 8px; }
.result td, .result th { text-align: left; padding: 6px 8px; border-bottom: 1px solid var(--line); vertical-align: top; }
.result th { color: var(--muted); font-size: 12px; text-transform: uppercase; letter-spacing: .06em; }
.msg { border-left: 4px solid var(--bad); background: var(--bad-soft); padding: 6px 10px; border-radius: 0 8px 8px 0;
  margin-top: 8px; white-space: pre-wrap; font: 13px/1.5 ui-monospace, Menlo, monospace; }
.value { font: 14px/1.5 ui-monospace, Menlo, monospace; }
details { margin-top: 10px; }
summary { cursor: pointer; color: var(--accent); font-weight: 600; font-size: 14px; }
</style>
</head>
<body>
<main>
  <h1>PlasmaLean tasks</h1>
  <p class="lead">Send tasks to Lean, with Mathlib and the PlasmaLean library loaded. Each task is a
  JSON object with a <code>"task"</code> field, posted to this server. Definitions persist across
  requests until you reset the environment.</p>
  <div class="grid">
    <section class="panel" aria-labelledby="req-h">
      <h2 id="req-h">Request</h2>
      <div class="examples" id="examples" aria-label="Examples"></div>
      <label for="req" class="status">Task as JSON</label>
      <textarea id="req" spellcheck="false"></textarea>
      <div class="actions">
        <button class="primary" id="send">Send <span aria-hidden="true">(Ctrl+Enter)</span></button>
        <button id="reset">Reset environment</button>
        <span class="status" id="status" role="status" aria-live="polite"></span>
      </div>
      <p class="hint tasks">Available tasks: %%TASKS%%.</p>
      <p class="hint">From a terminal:
        <code id="curl">curl -X POST --data '{"task": "elab_term", "term": "2 + 3"}' http://127.0.0.1:8080/</code></p>
    </section>
    <section class="panel" aria-labelledby="res-h">
      <h2 id="res-h">Response</h2>
      <div class="result" id="result"><p class="status">Choose an example or write a task, then send it.</p></div>
      <details id="rawbox"><summary>Raw JSON</summary><pre id="raw"></pre></details>
    </section>
  </div>
</main>
<script>
(function () {
  "use strict";
  var examples = [
    { label: "Evaluate a term", task: { task: "elab_term", term: "(2 : Nat) + 3" } },
    { label: "PlasmaLean function", task: { task: "elab_term", term: "PlasmaLean.Transport.svFloorF 10" } },
    { label: "Subset sum", task: { task: "elab_term", term: "ConcLean.SubsetSum.subsetSum [3, 5, 7] [0, 2]" } },
    { label: "Define on the library", task: { task: "elab_defs", names: ["p", "lb"],
      code: "open PlasmaLean.Certificates.QPoly in\ndef p : List ℚ := [1, -1, 1]\nopen PlasmaLean.Certificates.QPoly in\ndef lb : ℚ := lowerBound (1/2) p" } },
    { label: "Check a theorem", task: { task: "elab_defs", names: [],
      code: "open PlasmaLean.Certificates.QPoly in\ntheorem lb_le (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1/2) :\n    ((lowerBound (1/2) [1, -1, 1] : ℚ) : ℝ) ≤ eval [1, -1, 1] t :=\n  lowerBound_le _ h0 (by push_cast; exact h1)" } },
    { label: "A false statement", task: { task: "elab_defs", names: [],
      code: "theorem wrong : PlasmaLean.Certificates.QPoly.lowerBound (1/2) [1, 0, 1] = 2 := by\n  norm_num [PlasmaLean.Certificates.QPoly.lowerBound]" } },
    { label: "Check compilation", task: { task: "check", modify_env: false,
      code: "def fib : Nat → Nat\n  | 0 => 0\n  | 1 => 1\n  | n + 2 => fib n + fib (n + 1)\n\ntheorem fib_five : fib 5 = 5 := by\n  sorry" } },
    { label: "Evaluate with code", task: { task: "eval", modify_env: false,
      code: "def fib : Nat → Nat\n  | 0 => 0\n  | 1 => 1\n  | n + 2 => fib n + fib (n + 1)",
      term: "(List.range 12).map fib" } },
    { label: "Unknown task", task: { task: "nope" } }
  ];
  var req = document.getElementById("req"), result = document.getElementById("result");
  var raw = document.getElementById("raw"), status = document.getElementById("status");
  document.getElementById("curl").textContent =
    "curl -X POST --data '{\"task\": \"elab_term\", \"term\": \"2 + 3\"}' " + location.origin + "/";
  var box = document.getElementById("examples");
  examples.forEach(function (ex) {
    var b = document.createElement("button");
    b.type = "button"; b.textContent = ex.label;
    b.addEventListener("click", function () { req.value = JSON.stringify(ex.task, null, 2); req.focus(); });
    box.appendChild(b);
  });
  req.value = JSON.stringify(examples[0].task, null, 2);
  function el(tag, cls, text) { var e = document.createElement(tag); if (cls) e.className = cls; if (text != null) e.textContent = text; return e; }
  function show(data) {
    raw.textContent = JSON.stringify(data, null, 2);
    result.innerHTML = "";
    var r = data.response || {};
    var failed = data.status !== "ok" || r.result === "error" || r.compiles === false ||
      (r.messages && r.messages.some(function (m) { return typeof m === "string" ? /error|unsolved|unknown|failed/i.test(m) : m.severity === "error"; }));
    result.appendChild(el("span", "badge " + (failed ? "err" : "ok"), failed ? "error" : "ok"));
    if (data.message) result.appendChild(el("div", "msg", data.message));
    if (r.error) result.appendChild(el("div", "msg", r.error));
    if (r.compiles != null) {
      var c = el("p", null, r.compiles ? "Compiles." : "Does not compile.");
      if (r.declarations && r.declarations.length) c.appendChild(el("span", null, " Declarations: " + r.declarations.join(", ") + "."));
      if (r.sorry && r.sorry.length) c.appendChild(el("span", null, " Uses sorry: " + r.sorry.join(", ") + "."));
      result.appendChild(c);
    }
    if (r.output != null) { var p = el("p", null, "Value: "); p.appendChild(el("span", "value", r.output)); result.appendChild(p); }
    if (r.definitions && r.definitions.length) {
      var t = el("table"); var h = el("tr"); h.appendChild(el("th", null, "Name")); h.appendChild(el("th", null, "Value")); t.appendChild(h);
      r.definitions.forEach(function (d) { var tr = el("tr"); tr.appendChild(el("td", "value", d.name)); tr.appendChild(el("td", "value", d.view)); t.appendChild(tr); });
      result.appendChild(t);
    }
    if (r.messages) {
      if (r.messages.length === 0) result.appendChild(el("p", "status", "Lean reported no messages: the code elaborated."));
      r.messages.forEach(function (m) {
        result.appendChild(el("div", "msg", typeof m === "string" ? m : m.severity + " at line " + m.line + ", column " + m.column + ": " + m.text));
      });
    }
  }
  function post(path, body) {
    status.textContent = "Running…";
    var t0 = performance.now();
    return fetch(path, { method: "POST", headers: { "Content-Type": "application/json" }, body: body })
      .then(function (res) { return res.text(); })
      .then(function (txt) {
        var data; try { data = JSON.parse(txt); } catch (e) { data = { status: "error", message: txt }; }
        show(data); status.textContent = "Done in " + Math.round(performance.now() - t0) + " ms.";
      })
      .catch(function (e) { status.textContent = "Request failed: " + e; });
  }
  document.getElementById("send").addEventListener("click", function () { post("/", req.value); });
  document.getElementById("reset").addEventListener("click", function () { post("/reset", "{}"); });
  req.addEventListener("keydown", function (e) { if ((e.ctrlKey || e.metaKey) && e.key === "Enter") { e.preventDefault(); post("/", req.value); } });
})();
</script>
</body>
</html>
"##

/-- The state of the server: the starting environment and the current, shared one. -/
structure TheoryServer where
  /-- The environment after importing `Mathlib` and `PlasmaLean`, restored by `POST /reset`. -/
  initialEnv : Environment
  /-- The environment in which tasks run, updated by each task; the lock serializes tasks. -/
  env : Std.Mutex Environment
  /-- The web page, with the available tasks filled in. -/
  page : String

/-- Run a JSON task in the shared environment, as `theory_loop` does for one line of input. -/
def runTask (srv : TheoryServer) (input : String) : IO Json := do
  match Json.parse input with
  | .error e =>
    return Json.mkObj [("status", "error"), ("message", s!"Failed to parse JSON: {e}")]
  | .ok js =>
    match js.getObjValAs? String "task" with
    | .error e =>
      return Json.mkObj [("status", "error"), ("message", s!"Missing 'task' field in JSON: {e}")]
    | .ok task =>
      IO.eprintln s!"Running PlasmaLean task {task}"
      srv.env.atomically do
        let (response, env) ← responseFromTaskIO task js (← get)
        set env
        return Json.mkObj [("status", "ok"), ("response", response)]

/-- The path of a request target, without the query. -/
def requestPath (req : Request Body.Stream) : String :=
  ((toString req.line.uri).splitOn "?").headD "/"

instance : Handler TheoryServer where
  ResponseBody := Body.Full
  onRequest srv req := do
    let path := requestPath req
    if req.line.method == .get then
      if path == "/" || path == "/index.html" then
        Response.ok |>.html srv.page
      else
        Response.notFound |>.text "Not found. The task page is at /."
    else if req.line.method == .post then
      let body : String ← req.body.readAll (maximumSize := some 4000000)
      if path == "/reset" then
        srv.env.atomically (set srv.initialEnv)
        let reply := Json.mkObj [("status", "ok"), ("response", Json.mkObj [("result", "reset")])]
        Response.ok |>.json reply.compress
      else
        let reply ← runTask srv body
        Response.ok |>.json reply.compress
    else
      Response.withStatus .methodNotAllowed |>.text "Use GET for the page and POST for tasks."
  onFailure _ err := do
    IO.eprintln s!"theory_server: {err}"

unsafe def main (args : List String) : IO UInt32 := do
  let port : UInt16 := (args.head? >>= String.toNat?).map (·.toUInt16) |>.getD 8080
  enableInitializersExecution
  initSearchPath (← findSysroot)
  IO.eprintln "Importing Mathlib and PlasmaLean..."
  let env ← importModules (loadExts := true) #[{module := `Mathlib}, {module := `PlasmaLean}] {}
  let tasks := (responseExt.getState env).toList.map (·.1) |>.mergeSort
  let tasksHtml := ", ".intercalate (tasks.map fun t => s!"<code>{t}</code>")
  let srv : TheoryServer :=
    { initialEnv := env, env := ← Std.Mutex.new env,
      page := pageTemplate.replace "%%TASKS%%" tasksHtml }
  let addr : Net.SocketAddress := .v4 ⟨.ofParts 127 0 0 1, port⟩
  Async.block do
    let server ← Server.serve addr srv
    IO.eprintln s!"Serving PlasmaLean tasks at http://127.0.0.1:{port}/"
    server.waitShutdown
  return 0
