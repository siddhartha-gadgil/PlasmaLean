---
name: plasmalean-lean-proofs
description: Write and repair Lean 4 proofs in PlasmaLean efficiently. Use whenever writing or editing Lean code, choosing tactics, proving concrete numerical/finite facts, or building certificate checkers — covers grind/fun_induction automation, decide_cbv for medium concrete checks, and how to build large proofs as explicit proof terms (the SubsetSum pattern) instead of decide.
---

# Lean proofs in PlasmaLean

Toolchain: Lean `v4.34.1`, Mathlib `v4.34.1` (see `lean-toolchain`, `lakefile.toml`). Check a file with `lake env lean <path>` and the library with `lake build`. Before finishing, run `lake env lean scripts/check_axioms.lean`. It **fails** on any axiom other than `propext`, `Classical.choice` and `Quot.sound`, so `sorry`, `native_decide`, `Lean.ofReduceBool` and native `bv_decide` proofs are all rejected.

## 1. Prefer automation that gives short, clean proofs

- **`grind`** is the default finisher for goals that follow from hypotheses by equalities, linear arithmetic, case splits and constructor/injectivity reasoning. Pass definitions to unfold, and lemmas to use, as hints: `grind [subsetSum]`, `grind [List.mem_cons]`. It often closes all the cases of an induction at once: `induction h <;> grind`.
- **`fun_induction f args`** is the right induction whenever the goal mentions a recursive function `f`. It produces one case per branch of `f` (including `if`/`match` branches) with the branch hypotheses and induction hypotheses already in place. Name the cases with `with | case1 … | case2 x xs ih => …`, or use `rename_i`. Combine it with `grind`/`simp [f]` per case.
- Other standard tactics: `simp`/`simp only [...]`, `norm_num [defs]`, `positivity`, `linarith`/`nlinarith [hints]`, `gcongr`, `field_simp`, `ring`, `bound`, `fun_prop` (continuity and differentiability), `exact?`/`apply?` for searching.
- Before unfolding definitions by brute force, search for a conceptual lemma (`rg` in `.lake/packages/mathlib`, `exact?`). Keep proofs readable: a short `have` chain is better than a long opaque `simp` call that breaks easily.

Worked example (`PlasmaLean/SubsetSum.lean`):

```lean
theorem subsetSum_correct (l : List Int) (indices : List Nat) :
    HasSubsetSum l (subsetSum l indices) := by
  fun_induction subsetSum
  · apply HasSubsetSum.nil
  · rename_i indices' a bs h₁ h₂; apply HasSubsetSum.take a; assumption
  · rename_i indices' a bs h₁ h₂; apply HasSubsetSum.skip a; assumption
```

## 2. Concrete computations: choose by size

| Size of the check | Use | Do not use |
| --- | --- | --- |
| A few closed numeric facts (`(37:ℚ)/5 < 8`, an explicit polynomial value) | `norm_num`, `simp`, `rfl` | `decide`, `decide +kernel` |
| Medium concrete checks: a Boolean checker on ℚ/ℕ/lists with up to a few hundred evaluation steps (a `QPoly.checkOn` fixture on 32 pieces, a 100–400 element list, a finite case split) | **`decide_cbv`** | plain `decide` |
| Large certificates (many pieces, long lists, high-degree polynomial interval checks, many modes) | an explicit proof term built step by step: **the SubsetSum pattern (§3)** | one monolithic `decide_cbv`; `decide +kernel` (legacy only, see below) |

**Plain `decide` is inefficient.** It evaluates the `Decidable` instance in the elaborator, and on ℚ arithmetic it typically just fails ("did not reduce to `isTrue`"). Do not use it for anything nontrivial.

**`decide_cbv`** (core Lean, `Lean.Meta.Tactic.Cbv`, no import needed) applies `of_decide_eq_true` and then reduces `decide p` by proof-producing call-by-value simplification: it rewrites with equation/unfold lemmas and matcher reductions, and the result is an `Eq` proof chain checked by the kernel. Its relatives are `cbv` / `cbv at h` (non-terminal) and `conv => cbv`. Properties measured on this toolchain:
- **Axioms:** only `propext`, `Classical.choice`, `Quot.sound` (often just `propext`). No `Lean.ofReduceBool`, no code-generator trust, so it passes `check_axioms.lean`.
- **It works where `decide +kernel` gets stuck.** Because it unfolds through equation lemmas, it evaluates functions defined by **well-founded recursion** (`termination_by`) and **`partial_fixpoint`**. A merge sort on 10 elements took 50 ms, while `decide +kernel` failed with "did not reduce".
- **Error messages are clear:** "the proposition evaluates to `false`", or "got stuck at: …" with the stuck subterm.
- **Cost:** on structurally recursive ℚ checkers it is slower than `decide +kernel` and builds a large proof term. Measured times: `tightQuartic_check` 5 s vs 0.4 s; `dipQuadratic_reject` 2 s vs 0.06 s; `allGeB (1/3)` on 400 rationals 5.6 s vs 0.35 s. The 64-piece Ballooning residual check took 58 s vs 2.5 s and needed `maxHeartbeats 0`. That is past "medium": use §3.
- **Limits:** long lists and deep recursion hit `maxRecDepth` (raise it, e.g. `set_option maxRecDepth 100000 in`), and large checks hit `cbv.maxSteps` (default 100 000). If you need both raised, the check belongs in §3. Use `@[cbv_opaque]` to stop it unfolding a definition and `@[cbv_eval]` to give it a rewrite rule instead. It does not enter binders.

**`decide +kernel` is not for new code** (policy of 25 October 2026). It is fast on structurally recursive checkers, but a failure gives only "did not reduce to `isTrue`", it re-evaluates the whole checker on every call, and it hides the computation in one opaque kernel evaluation. New code and **generators** (Python emitters) use:
- `norm_num` / `rfl` for a few closed facts, including single bound checks such as `B 5 + E 5 ≤ 1623/10000` (unfold the defs with `norm_num [B, E]`, or prove `B 5 + E 5 = q` by `decide_cbv` and finish with `norm_num`);
- `decide_cbv` for medium checks;
- the SubsetSum proof-term pattern (§3) for large certificates, with leaf steps that are small `Nat`/`ℚ` facts closed by `rfl`, `norm_num` or `decide_cbv`. The kernel's `Nat` arithmetic is GMP-backed, so a leaf `a * b = c` on big literals closed by `rfl` is cheap.

The existing `decide +kernel` checks (the `QPoly.checkOn` fixtures, the KAM-family Kronecker checks `…Check*`, and the `…Adm` bound checks) are legacy: migrate them when a generator is touched. **Generators must validate every emitted bound with exact rational arithmetic before writing it** (round outward, recompute in `Fraction`, assert), so that a wrong constant fails in Python, not in a Lean build hours later.

**`bv_decide` (niche):** use it only for genuine SAT problems over `Bool` / `BitVec n` / fixed-width integers. It does not compute with `ℚ`, `ℝ` or lists. When the SAT solver is actually used, the proof depends on a native axiom such as `foo._native.bv_decide.ax_1_5`, which `check_axioms.lean` rejects. Always run `#print axioms`, and never leave such a proof in the library.

## 3. Large proofs: build the proof term (SubsetSum pattern)

Reference: `PlasmaLean/SubsetSum.lean`. The idea is to keep computation outside the trusted proof. An untrusted search (Python, a solver oracle, or a `meta` function) finds a **witness**, and a `meta` function turns it into an explicit proof term. The kernel then checks only small local steps.

Ingredients:

1. **Inductive certificate predicate.** There is one constructor per kind of local step, and its arguments are **explicit** so that `mkAppM` can supply them (`HasSubsetSum.skip (x : Int) (xs : List Int) (s : Int)`).
2. **Computable function and characterization theorems.** A plain `def` computes the same thing as the predicate. Prove that they agree with `fun_induction` and `grind` (`subsetSum_correct`, `exists_indices_for_subset_sum`). Also prove the **semantic soundness** theorem that design code uses, e.g. "certificate ⇒ the bound holds for every real x ∈ [a,b]".
3. **`meta def` proof builder.** It recurses over the witness and applies the constructors with `mkAppM ``Pred.ctor #[toExpr a, …, subproof]`. Tail data are computed by a `meta` copy of the function (`computeSubsetSum`).
4. **Local side conditions become goals**, not hidden computations. Create them with `mkFreshExprMVar q(...)` and return them through `replaceMainGoal`, then close them with `all_goals norm_num` (or `linarith`, `positivity`). Do **not** run tactics inside a fresh `TermElabM` in the builder: that leaks free variables into the term.
5. **Tactic or command front end.** An `elab` matches the goal with `let_expr`, evaluates the data (`unsafe evalExpr`), calls the builder and assigns the goal. Use `mkExpectedTypeHint pf goalType` so that the generated `toExpr` data are checked against the stated data by one definitional-equality check.
6. **Keep large data in `def`s** generated by functions or by an oracle. Large literal lists of rationals elaborate very slowly.

Tested template (≈400 local steps in about 4 s, standard axioms only):

```lean
open Lean Meta Elab Tactic Qq

/-- Every entry of the list is at least `m`. -/
inductive AllGe (m : ℚ) : List ℚ → Prop where
  | nil : AllGe m []
  | cons (x : ℚ) (xs : List ℚ) : m ≤ x → AllGe m xs → AllGe m (x :: xs)

theorem AllGe.mem {m : ℚ} {l : List ℚ} (h : AllGe m l) : ∀ x ∈ l, m ≤ x := by
  induction h <;> grind

/-- Build the proof term; each local inequality becomes a side goal. -/
meta def mkAllGe (m : Q(ℚ)) : List ℚ → MetaM (Expr × List MVarId)
  | [] => return (← mkAppOptM ``AllGe.nil #[m], [])
  | x :: xs => do
    let xe : Q(ℚ) := toExpr x
    let mv ← mkFreshExprMVar q($m ≤ $xe)
    let (tl, gs) ← mkAllGe m xs
    return (← mkAppM ``AllGe.cons #[xe, toExpr xs, mv, tl], mv.mvarId! :: gs)

elab "all_ge_cert" : tactic => do
  let g ← getMainGoal
  let_expr AllGe m l := (← instantiateMVars (← g.getType)) | throwError "expected AllGe m l"
  let lv ← unsafe evalExpr (List ℚ) q(List ℚ) l
  let (pf, gs) ← mkAllGe m lv
  g.assign (← mkExpectedTypeHint pf (← g.getType))
  replaceMainGoal gs

def bigList : List ℚ := (List.range 400).map (fun n : ℕ => (2 * (n : ℚ) + 1) / 2)

theorem big : AllGe (1/3) bigList := by
  all_ge_cert
  all_goals norm_num
```

For PlasmaLean certificates, the predicate's constructors are the mathematical steps: "on piece [xᵢ, xᵢ₊₁] the lower bound holds" (polynomial interval checks), "mode (m,n) has a Picone witness" (Newcomb/ballooning), "box Bᵢ satisfies the barrier inequality" (transport barriers), "the radii-polynomial bounds Y₀, Z₁, Z₂ hold on this block". The soundness theorem is proved once by induction on the predicate. Each instance then only requires small `norm_num` facts.

## 4. Module system and hygiene

- Files start with `module`. Mark the API with `public section` and `@[expose]` where downstream proofs must unfold a definition. Imports used only by `meta` code are `public meta import Lean` / `public meta import Qq`.
- `meta def` code is not part of the trusted proof. Never let a theorem's truth depend on it except through the term it produces, which the kernel checks.
- Every definition and theorem needs a docstring, and every module needs a module docstring (see `notes/domain-libraries.md`). Every new definition or certificate format needs sanity theorems: a degenerate case, a special case, an accepted fixture and a rejected fixture.
- Forbidden in the library: `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` proofs, and `bv_decide` results that depend on a `_native` axiom.

## 5. Debugging checklist

1. If a goal is slow, find out which step: `set_option trace.profiler true`, or split it with `have`.
2. If `grind` fails, add the definition or lemma names as hints, or `simp only [f] at *` first. Use `grind?`/`simp?` to get a stable call.
3. If `fun_induction` gives awkward cases, check that the goal mentions `f` applied to variables, not to concrete data, and generalize first if needed.
4. On a heartbeat timeout during elaboration of data, move the data into a `def` and generate it with a function.
5. At the end: `#print axioms` for each certificate entry point, then `lake build`, then `scripts/check_axioms.lean`.
