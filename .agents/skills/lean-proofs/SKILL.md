---
name: lean-proofs
description: Write and repair Lean 4 proofs efficiently in a LeanTheory-based formalization. Use whenever writing or editing Lean code, choosing tactics, proving concrete numerical/finite facts, or building certificate checkers; covers grind/fun_induction automation, the certificate tactics kernel_fact/bool_cert/eval_cert for concrete checks, and building large proofs as explicit proof terms (the SubsetSum pattern). No decide of any kind.
---

# Lean proofs in LeanTheory

Toolchain: see `lean-toolchain` and `lakefile.toml` (Lean and Mathlib are pinned together). Check a file with `lake env lean <path>` and the library with `lake build`. Before finishing, run `lake env lean scripts/check_axioms.lean`. It **fails** on any axiom other than `propext`, `Classical.choice` and `Quot.sound`, so `sorry`, `native_decide`, `Lean.ofReduceBool` and native `bv_decide` proofs are all rejected. Builds must have zero warnings.

## 1. Prefer automation that gives short, clean proofs

- **`grind`** is the default finisher for goals that follow from hypotheses by equalities, linear arithmetic, case splits and constructor/injectivity reasoning. Pass definitions to unfold, and lemmas to use, as hints: `grind [subsetSum]`, `grind [List.mem_cons]`. It often closes all the cases of an induction at once: `induction h <;> grind`.
- **`fun_induction f args`** is the right induction whenever the goal mentions a recursive function `f`. It produces one case per branch of `f` (including `if`/`match` branches) with the branch hypotheses and induction hypotheses already in place. Name the cases with `with | case1 … | case2 x xs ih => …`, or use `rename_i`. Combine it with `grind`/`simp [f]` per case.
- Other standard tactics: `simp`/`simp only [...]`, `norm_num [defs]`, `positivity`, `linarith`/`nlinarith [hints]`, `gcongr`, `field_simp`, `ring`, `bound`, `fun_prop` (continuity and differentiability), `exact?`/`apply?` for searching.
- Before unfolding definitions by brute force, search for a conceptual lemma (`rg` in `.lake/packages/mathlib`, `exact?`). Keep proofs readable: a short `have` chain is better than a long opaque `simp` call that breaks easily.

Worked example (`LeanTheory/SubsetSum.lean`):

```lean
theorem subsetSum_correct (l : List Int) (indices : List Nat) :
    HasSubsetSum l (subsetSum l indices) := by
  fun_induction subsetSum
  · apply HasSubsetSum.nil
  · rename_i indices' a bs h₁ h₂; apply HasSubsetSum.take a; assumption
  · rename_i indices' a bs h₁ h₂; apply HasSubsetSum.skip a; assumption
```

## 2. Concrete computations: choose by size

**Policy: no `decide` of any kind** anywhere in the library: not plain `decide`, not its kernel or call-by-value variants, not `native_decide`. Every concrete check is either a short tactic proof or an explicit proof term whose leaves only the kernel evaluates. `scripts/audit_kernel_fact.py` audits the remaining kernel-evaluated leaves.

| Size of the check | Use |
| --- | --- |
| A few closed numeric facts (`(37:ℚ)/5 < 8`, an explicit polynomial value, `B 5 + E 5 ≤ 1623/10000`) | `norm_num [defs]`, `simp`, `rfl` |
| Closed side conditions and finite quantifiers: conjunctions, `∀ x ∈ l`, `∀ i ≤ n`, `∀ i < n`, `∀ i : Fin n` over rational/natural comparisons | **`kernel_fact`** (`Certificates/KernelFact`); example: `initialStates_energy_le` in `Certificates/Example` |
| A Boolean checker `check data = true` recursing over cells/rows with `&&`, `\|\|`, `if` and comparison leaves | **`bool_cert`** (`Certificates/BoolCert`; `bool_cert?` reports collapsed leaves) |
| A closed evaluation of ball, interval or polynomial terms (`FIv` operations, records, structural recursion) | **`eval_cert`** (`Certificates/EvalCert`, builder natively compiled in `LeanTheoryMeta/EvalCert.lean`); **`fiv_cert`** (`Certificates/EvalCertFIv`) for fixed-point interval checkers |
| Families of such checks, digit/mask extractions, Kronecker or Chebyshev ball chains | the existing certificate predicates: `IccListCert`, `DigitSumCert`, `FamPackCert`, `kron_proof` / `kron2_proof` / `kron_lt` |
| A new kind of large certificate (many pieces, long lists, high-degree interval checks, many modes) | a new inductive certificate predicate with a `meta` proof builder: **the SubsetSum pattern (§3)**, with `Nat`/`ℚ` leaves checked by the kernel |

Why not `decide`: plain `decide` evaluates the `Decidable` instance in the elaborator and typically fails on ℚ arithmetic ("did not reduce to `isTrue`"); kernel and native variants leave a whole evaluation opaque (or add trust), and are slow and memory-hungry at scale. Explicit certificates are checked step by step, give precise failure locations, and split across declarations.

**Building on kernel `Nat`.** The kernel evaluates `Nat` literals with GMP (`Nat.add`, `sub`, `mul`, `div`, `mod`, `gcd`, `beq`, `ble`, `land`, `lor`, `xor`, `shiftLeft`, `shiftRight`, `pow`, `log2`). So the leaves of a large proof should be `Nat` facts such as `a * b + c = d`, `Nat.ble x y = true` or `x >>> k &&& m = y` on literals or on `def`s that unfold to them. A `meta` builder creates each leaf proof directly as `Eq.refl _` with `mkApp`/`mkExpectedTypeHint`: it is checked by the kernel alone, while the elaborator never evaluates it (writing `Nat.le_of_ble_eq_true rfl` in source is markedly slower). Each constructor of the certificate predicate is one local step, for example "row block i sums to s", "mask m extracts digit d" or "piece k satisfies the bound". Its soundness theorem is proved once by induction. Keep big intermediates out of the term: refer to them through `def`s computed in the kernel, not `toExpr` literals. Split very large certificates over several declarations, since the kernel's caches are per declaration; this also bounds peak memory.

**Generators must validate every emitted bound with exact rational arithmetic before writing it** (round outward, recompute in `Fraction`, assert), so that a wrong constant fails in Python, not in a Lean build hours later.

**`bv_decide` (niche):** use it only for genuine SAT problems over `Bool` / `BitVec n` / fixed-width integers. It does not compute with `ℚ`, `ℝ` or lists. When the SAT solver is actually used, the proof depends on a native axiom such as `foo._native.bv_decide.ax_1_5`, which `check_axioms.lean` rejects. Always run `#print axioms`, and never leave such a proof in the library.

## 3. Large proofs: build the proof term (SubsetSum pattern)

Reference: `LeanTheory/SubsetSum.lean`. The idea is to keep computation outside the trusted proof. An untrusted search (Python, a solver oracle, or a `meta` function) finds a **witness**, and a `meta` function turns it into an explicit proof term. The kernel then checks only small local steps. `kernel_fact`, `bool_cert` and `eval_cert` are instances of this pattern.

Ingredients:

1. **Inductive certificate predicate.** There is one constructor per kind of local step, and its arguments are **explicit** so that `mkAppM` can supply them (`HasSubsetSum.skip (x : Int) (xs : List Int) (s : Int)`).
2. **Computable function and characterization theorems.** A plain `def` computes the same thing as the predicate. Prove that they agree with `fun_induction` and `grind` (`subsetSum_correct`, `exists_indices_for_subset_sum`). Also prove the **semantic soundness** theorem that downstream code uses, e.g. "certificate ⇒ the bound holds for every real x ∈ [a,b]".
3. **`meta def` proof builder.** It recurses over the witness and applies the constructors with `mkAppM ``Pred.ctor #[toExpr a, …, subproof]`. Tail data are computed by a `meta` copy of the function (`computeSubsetSum`).
4. **Local side conditions become goals**, not hidden computations. Create them with `mkFreshExprMVar q(...)` and return them through `replaceMainGoal`, then close them with `all_goals norm_num` (or `linarith`, `positivity`). Do **not** run tactics inside a fresh `TermElabM` in the builder: that leaks free variables into the term.
5. **Tactic or command front end.** An `elab` matches the goal with `let_expr`, evaluates the data (`unsafe evalExpr`), calls the builder and assigns the goal. Use `mkExpectedTypeHint pf goalType` so that the generated `toExpr` data are checked against the stated data by one definitional-equality check.
6. **Keep large data in `def`s** generated by functions or by an oracle. Large literal lists of rationals elaborate very slowly.
7. **Heavy builders** can live in `LeanTheoryMeta` (precompiled to native code, see `lakefile.toml`); the builder is untrusted either way.

Tested template (≈400 local steps in a few seconds, standard axioms only):

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

For domain certificates, the predicate's constructors are the mathematical steps: "on piece [xᵢ, xᵢ₊₁] the lower bound holds" (polynomial interval checks), "mode k has a positivity witness" (stability by modes), "box Bᵢ satisfies the barrier inequality" (invariant regions), "the radii-polynomial bounds Y₀, Z₁, Z₂ hold on this block". The soundness theorem is proved once by induction on the predicate. Each instance then only requires small kernel or `norm_num` facts.

## 4. Module system and hygiene

- Files start with `module`. Mark the API with `public section` and `@[expose]` where downstream proofs must unfold a definition. Imports used only by `meta` code are `public meta import Lean` / `public meta import Qq`.
- `meta def` code is not part of the trusted proof. Never let a theorem's truth depend on it except through the term it produces, which the kernel checks.
- Every definition and theorem needs a docstring, and every module needs a module docstring (see `notes/domain-libraries.md`). Every new definition or certificate format needs sanity theorems: a degenerate case, a concrete instance, an accepted fixture and a rejected fixture (see `LeanTheory/Sanity/Example.lean`, `LeanTheory/Certificates/Example.lean`).
- Forbidden in the library: `sorry`, `admit`, `axiom`, any `decide` variant, `native_decide`, `unsafe` proofs, and `bv_decide` results that depend on a `_native` axiom.

## 5. Debugging checklist

1. If a goal is slow, find out which step: `set_option trace.profiler true`, or split it with `have`.
2. If `grind` fails, add the definition or lemma names as hints, or `simp only [f] at *` first. Use `grind?`/`simp?` to get a stable call.
3. If `fun_induction` gives awkward cases, check that the goal mentions `f` applied to variables, not to concrete data, and generalize first if needed.
4. On a heartbeat timeout during elaboration of data, move the data into a `def` and generate it with a function.
5. If a certificate tactic refuses a goal, use its diagnostic variant (`bool_cert?`) or reduce the goal to a smaller fixture; a stuck leaf usually means a definition needs `@[expose]` or a missing operation must be named (`eval_cert [f]`).
6. At the end: `#print axioms` for each certificate entry point, then `lake build`, then `scripts/check_axioms.lean`.
7. **Memory: never let Lake rebuild many heavy modules at once.** `lake build Top` rebuilds every stale dependency in parallel, and a dozen heavy certificate modules at once can exhaust RAM plus swap. Keep each Lean process within 6 GB. When dependencies are stale (find them with `lake build --no-build Top`), build them one at a time or in small groups first, then `Top`. Check `memory_pressure` before heavy steps and wait if free memory is low. Very heavy first builds belong on the workstation (`workstation-update`).
