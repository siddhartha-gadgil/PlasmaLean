/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Kernel.Fusion
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Topology.Algebra.Order.Field
public meta import Lean
public meta import Qq

/-!
# A concrete instance of the supplied Bosch–Hale reactivity class

The kernel class `PlasmaLean.Fusion.BoschHaleDT` bundles *supplied* empirical facts about
the D-T reactivity (61 rational enclosures, continuity, monotonicity). A bundle of
supplied facts could in principle be contradictory, which would make every theorem
assuming it vacuous. This module rules that out by constructing an explicit function
`bhSv : ℝ → ℝ` and proving `BoschHaleDT bhSv` (`bhSv_boschHaleDT`).

## Construction

`bhSv` is the piecewise-linear interpolant of the rational node values `bhNodes` at the
temperatures `T = 1, 2, …, 60` keV, extended by constants below 1 keV and above 60 keV.
The node at `T = k ≤ 59` is the lower enclosure `svLo` of the window `[k, k+1]`, and the
node at `T = 60` is `8.9e-22 m³/s`. It is written in *increment form*
`pl v T = v₀ + Σᵢ (vᵢ₊₁ − vᵢ) · clamp₀₁(T − 1 − i)` (`pl`, `inc`), which makes
continuity and (for nondecreasing nodes) global monotonicity immediate.

## Window certificate (proof-term pattern)

Because `bhSv` is monotone, a window `[lo, hi]` holds as soon as
`svLo ≤ bhSv(i+1)` for a node `i + 1 ≤ lo` and `bhSv(j+1) ≤ svHi` for a node
`j + 1 ≥ hi`, and `bhSv(k+1)` is the `k`-th node (`pl_natCast`). The inductive predicate
`WindowsCert` has one constructor per window recording exactly these four rational facts;
`WindowsCert.sound` proves once that a certificate implies `∀ w ∈ ws, w.Holds (pl v)`.
The tactic `windows_cert` peels the list `boschHaleWindows` and builds the certificate
term, leaving 4 × 61 small rational side goals, closed by `norm_num` (the SubsetSum
pattern of `.claude/skills/plasmalean-lean-proofs`). No `decide` is used.

This is an *existence* (consistency) check only: `bhSv` is not the Bosch–Hale function and
carries no physical authority beyond the supplied enclosures.
-/

public section
noncomputable section

namespace PlasmaLean.Sanity.BoschHaleInstance

open PlasmaLean.Fusion

/-- The clamp of `x` to `[0, 1]`. -/
@[expose] def clamp01 (x : ℝ) : ℝ := max 0 (min 1 x)

/-- The clamp is continuous. -/
theorem clamp01_continuous : Continuous clamp01 :=
  continuous_const.max (continuous_const.min continuous_id)

/-- The clamp is monotone. -/
theorem clamp01_monotone : Monotone clamp01 := fun _ _ h =>
  max_le_max le_rfl (min_le_min le_rfl h)

/-- The clamp is nonnegative. -/
theorem clamp01_nonneg (x : ℝ) : 0 ≤ clamp01 x := le_max_left _ _

/-- The clamp is at most one. -/
theorem clamp01_le_one (x : ℝ) : clamp01 x ≤ 1 := max_le zero_le_one (min_le_left _ _)

/-- The clamp vanishes on `x ≤ 0`. -/
theorem clamp01_of_nonpos {x : ℝ} (h : x ≤ 0) : clamp01 x = 0 := by
  unfold clamp01; rw [max_eq_left]; exact (min_le_right _ _).trans h

/-- The clamp equals one on `x ≥ 1`. -/
theorem clamp01_of_one_le {x : ℝ} (h : 1 ≤ x) : clamp01 x = 1 := by
  unfold clamp01; rw [min_eq_left h]; norm_num

/-- Increment part of the piecewise-linear interpolant with nodes at `x = 0, 1, 2, …`:
`inc (v₀ :: v₁ :: …) x = Σᵢ (vᵢ₊₁ − vᵢ) clamp₀₁(x − i)`. -/
@[expose] def inc : List ℚ → ℝ → ℝ
  | v :: w :: rest, x => ((w : ℝ) - v) * clamp01 x + inc (w :: rest) (x - 1)
  | _, _ => 0

/-- Last entry of a list of rationals (`0` for the empty list). -/
@[expose] def lastD : List ℚ → ℚ
  | [] => 0
  | [v] => v
  | _ :: w :: rest => lastD (w :: rest)

/-- The list is nondecreasing. -/
@[expose] def NonDecr : List ℚ → Prop
  | v :: w :: rest => v ≤ w ∧ NonDecr (w :: rest)
  | _ => True

/-- Piecewise-linear interpolant of the node values `v` at `T = 1, 2, …, length v`,
constant outside `[1, length v]`. -/
@[expose] def pl (v : List ℚ) (T : ℝ) : ℝ := (v.headD 0 : ℝ) + inc v (T - 1)

/-- The increment sum is continuous. -/
theorem inc_continuous (v : List ℚ) : Continuous (inc v) := by
  induction v with
  | nil => exact continuous_const
  | cons a rest ih =>
    match rest, ih with
    | [], _ => exact continuous_const
    | b :: rest', ih =>
      exact (continuous_const.mul clamp01_continuous).add
        (ih.comp (continuous_id.sub continuous_const))

/-- The increment sum vanishes for `x ≤ 0`. -/
theorem inc_of_nonpos (v : List ℚ) {x : ℝ} (hx : x ≤ 0) : inc v x = 0 := by
  fun_induction inc v x with
  | case1 a b rest x ih =>
    rw [clamp01_of_nonpos hx, mul_zero, zero_add]; exact ih (by linarith)
  | case2 => rfl

/-- For nondecreasing nodes the increment sum is monotone. -/
theorem inc_monotone (v : List ℚ) (hv : NonDecr v) : Monotone (inc v) := by
  induction v with
  | nil => exact fun _ _ _ => le_rfl
  | cons a rest ih =>
    match rest, ih, hv with
    | [], _, _ => exact fun _ _ _ => le_rfl
    | b :: rest', ih, hv =>
      have hab : (0 : ℝ) ≤ (b : ℝ) - a := by
        have : (a : ℝ) ≤ b := by exact_mod_cast hv.1
        linarith
      intro x y hxy
      simp only [inc]
      have h1 := mul_le_mul_of_nonneg_left (clamp01_monotone hxy) hab
      have h2 := ih hv.2 (by linarith : x - 1 ≤ y - 1)
      linarith

/-- For nondecreasing nodes the increment sum is nonnegative. -/
theorem inc_nonneg (v : List ℚ) (hv : NonDecr v) (x : ℝ) : 0 ≤ inc v x := by
  fun_induction inc v x with
  | case1 a b rest x ih =>
    have hab : (0 : ℝ) ≤ (b : ℝ) - a := by
      have : (a : ℝ) ≤ b := by exact_mod_cast hv.1
      linarith
    exact add_nonneg (mul_nonneg hab (clamp01_nonneg x)) (ih hv.2)
  | case2 => exact le_rfl

/-- **Node evaluation.** At the integer `k`, the increment sum telescopes to the `k`-th
node minus the first one (the last node beyond the end of the list). -/
theorem inc_natCast (a : ℚ) (rest : List ℚ) (k : ℕ) :
    inc (a :: rest) k = ((a :: rest).getD k (lastD (a :: rest)) : ℝ) - a := by
  induction rest generalizing a k with
  | nil => cases k <;> simp [inc, lastD]
  | cons b rest' ih =>
    cases k with
    | zero =>
      simp only [inc, Nat.cast_zero, clamp01_of_nonpos le_rfl, mul_zero, zero_add,
        inc_of_nonpos _ (by norm_num : (0 : ℝ) - 1 ≤ 0), List.getD_cons_zero, sub_self]
    | succ m =>
      have hc : clamp01 ((m + 1 : ℕ) : ℝ) = 1 := clamp01_of_one_le (by push_cast; linarith
        [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
      have hm : ((m + 1 : ℕ) : ℝ) - 1 = m := by push_cast; ring
      simp only [inc, hc, hm, ih b m, List.getD_cons_succ, lastD, mul_one]
      ring

/-- `pl v (k + 1)` is the `k`-th node (or the last node if `k` is past the end). -/
theorem pl_natCast (a : ℚ) (rest : List ℚ) (k : ℕ) :
    pl (a :: rest) ((k : ℝ) + 1) = ((a :: rest).getD k (lastD (a :: rest)) : ℝ) := by
  simp only [pl, List.headD_cons, add_sub_cancel_right, inc_natCast]; ring

/-- The interpolant is continuous on all of `ℝ`. -/
theorem pl_continuous (v : List ℚ) : Continuous (pl v) :=
  continuous_const.add ((inc_continuous v).comp (continuous_id.sub continuous_const))

/-- For nondecreasing nodes the interpolant is monotone on all of `ℝ`. -/
theorem pl_monotone (v : List ℚ) (hv : NonDecr v) : Monotone (pl v) := fun x y h => by
  unfold pl; have := inc_monotone v hv (by linarith : x - 1 ≤ y - 1); linarith

/-- For nondecreasing nodes the interpolant is at least the first node. -/
theorem pl_ge_head (v : List ℚ) (hv : NonDecr v) (T : ℝ) : (v.headD 0 : ℝ) ≤ pl v T := by
  unfold pl; linarith [inc_nonneg v hv (T - 1)]

/-- **Window certificate.** One constructor step per window `w`: node indices `i, j` with
`i + 1 ≤ w.lo`, `w.hi ≤ j + 1`, `w.svLo ≤ v[i]` and `v[j] ≤ w.svHi` (nodes read with
`getD`, defaulting to the last node). All arguments are explicit for the proof builder. -/
inductive WindowsCert (v : List ℚ) : List ReactivityWindow → Prop where
  | nil : WindowsCert v []
  | cons (i j : ℕ) (w : ReactivityWindow) (ws : List ReactivityWindow) :
      (i : ℚ) + 1 ≤ w.lo → w.hi ≤ (j : ℚ) + 1 →
      w.svLo ≤ v.getD i (lastD v) → v.getD j (lastD v) ≤ w.svHi →
      WindowsCert v ws → WindowsCert v (w :: ws)

/-- **Soundness of window certificates** for a nondecreasing node list: every
certified window holds for the interpolant `pl v`. -/
theorem WindowsCert.sound {a : ℚ} {rest : List ℚ} (hv : NonDecr (a :: rest))
    {ws : List ReactivityWindow} (h : WindowsCert (a :: rest) ws) :
    ∀ w ∈ ws, w.Holds (pl (a :: rest)) := by
  induction h with
  | nil => simp
  | cons i j w ws hi hj hlo hhi _ ih =>
    intro w' hw' T h1 h2
    rcases List.mem_cons.mp hw' with rfl | hw'
    · have hm := pl_monotone _ hv
      have hi' : (i : ℝ) + 1 ≤ w'.lo := by exact_mod_cast hi
      have hj' : (w'.hi : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast hj
      have hlo' : (w'.svLo : ℝ) ≤ ((a :: rest).getD i (lastD (a :: rest)) : ℝ) := by
        exact_mod_cast hlo
      have hhi' : (((a :: rest).getD j (lastD (a :: rest)) : ℚ) : ℝ) ≤ w'.svHi := by
        exact_mod_cast hhi
      rw [← pl_natCast] at hlo' hhi'
      exact ⟨hlo'.trans (hm (hi'.trans h1)), (hm (h2.trans hj')).trans hhi'⟩
    · exact ih w' hw' T h1 h2

open Lean Meta Elab Tactic Qq in
/-- Read a natural-number literal `OfNat.ofNat n` (at any type). -/
meta def natLitOf? (e : Expr) : Option ℕ :=
  if e.isAppOfArity ``OfNat.ofNat 3 then (e.getArg! 1).rawNatLit? else none

open Lean Meta Elab Tactic Qq in
/-- Build a `WindowsCert v ws` proof term by peeling the list expression `ws`. Window
endpoints must be natural-number literals; node indices are `i = lo − 1`, `j = hi − 1`.
The four rational side conditions of each window are returned as new goals. -/
meta partial def mkWindowsCert (v : Expr) (ws : Expr) : MetaM (Expr × List MVarId) := do
  let ws ← whnfD ws
  if ws.isAppOfArity ``List.nil 1 then
    return (mkApp (mkConst ``WindowsCert.nil) v, [])
  else if ws.isAppOfArity ``List.cons 3 then
    let w := ws.getArg! 1
    let rest := ws.getArg! 2
    let w' ← whnfD w
    unless w'.isAppOfArity ``ReactivityWindow.mk 4 do
      throwError "window is not a literal structure: {w'}"
    let some lo := natLitOf? (w'.getArg! 0) | throwError "lo is not a literal: {w'}"
    let some hi := natLitOf? (w'.getArg! 1) | throwError "hi is not a literal: {w'}"
    let f := mkAppN (mkConst ``WindowsCert.cons) #[v, toExpr (lo - 1), toExpr (hi - 1), w, rest]
    let (mvs, _, _) ← forallMetaTelescopeReducing (← inferType f) (some 4)
    let (tl, gs) ← mkWindowsCert v rest
    return (mkAppN f (mvs.push tl), mvs.toList.map (·.mvarId!) ++ gs)
  else throwError "expected a list literal, got {ws}"

open Lean Meta Elab Tactic Qq in
/-- Tactic: close `WindowsCert v ws` by building the certificate term; leaves the
rational side conditions as goals. -/
elab "windows_cert" : tactic => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let_expr WindowsCert v ws := ty | throwError "expected WindowsCert v ws"
  let ws' := (← unfoldDefinition? ws).getD ws
  let (pf, gs) ← mkWindowsCert v ws'
  g.assign (← mkExpectedTypeHint pf ty)
  replaceMainGoal gs

/-- Node values (m³/s) at `T = 1, …, 60` keV: the lower enclosure of window `[k, k+1]` for
`k ≤ 59`, and `8.9e-22` at 60 keV (inside `[59,60]`, `[60,80]` and `[80,100]`). -/
@[expose] def bhNodes : List ℚ := [
  6.788e-27, 2.947e-25, 1.848e-24, 5.914e-24, 1.352e-23, 2.528e-23, 4.137e-23, 6.160e-23,
  8.550e-23, 1.124e-22, 1.418e-22, 1.729e-22, 2.052e-22, 2.381e-22, 2.712e-22, 3.041e-22,
  3.365e-22, 3.681e-22, 3.989e-22, 4.286e-22, 4.573e-22, 4.847e-22, 5.110e-22, 5.360e-22,
  5.598e-22, 5.824e-22, 6.038e-22, 6.241e-22, 6.433e-22, 6.613e-22, 6.784e-22, 6.944e-22,
  7.095e-22, 7.237e-22, 7.370e-22, 7.494e-22, 7.611e-22, 7.720e-22, 7.822e-22, 7.917e-22,
  8.006e-22, 8.088e-22, 8.165e-22, 8.236e-22, 8.302e-22, 8.363e-22, 8.419e-22, 8.471e-22,
  8.519e-22, 8.562e-22, 8.602e-22, 8.638e-22, 8.671e-22, 8.700e-22, 8.727e-22, 8.750e-22,
  8.771e-22, 8.789e-22, 8.805e-22, 8.9e-22]

/-- The explicit interpolated reactivity (m³/s, `T` in keV). -/
@[expose] def bhSv : ℝ → ℝ := pl bhNodes

/-- There are 60 nodes (`T = 1, …, 60` keV). -/
theorem bhNodes_length : bhNodes.length = 60 := rfl

/-- The last node is `8.9e-22 m³/s`. -/
theorem bhNodes_lastD : lastD bhNodes = 8.9e-22 := rfl

/-- The node values are nondecreasing. -/
theorem bhNodes_nonDecr : NonDecr bhNodes := by
  simp only [bhNodes, NonDecr]; norm_num

/-- The certificate for all 61 supplied windows, built as an explicit proof term. -/
theorem bhNodes_cert : WindowsCert bhNodes boschHaleWindows := by
  windows_cert
  all_goals first
    | (norm_num; done)
    | (rw [bhNodes_lastD]
       simp only [bhNodes, List.getD_cons_succ, List.getD_cons_zero, List.getD_nil]
       norm_num)

/-- **Non-vacuity of `BoschHaleDT`.** The explicit interpolant `bhSv` satisfies every
supplied Bosch–Hale fact: nonnegativity, continuity, monotonicity on `[1, 60]` keV and
all 61 rational enclosures. -/
instance bhSv_boschHaleDT : BoschHaleDT bhSv where
  nonneg T _ := by
    have h := pl_ge_head bhNodes bhNodes_nonDecr T
    have h0 : (0 : ℝ) ≤ (bhNodes.headD 0 : ℚ) := by norm_num [bhNodes]
    exact h0.trans h
  continuousOn := (pl_continuous bhNodes).continuousOn
  monotoneOn := (pl_monotone bhNodes bhNodes_nonDecr).monotoneOn _
  windows := by
    have h := WindowsCert.sound (a := 6.788e-27) (rest := bhNodes.tail) bhNodes_nonDecr
      bhNodes_cert
    exact h

/-- Sanity (accepted fixture): `bhSv` at 10 keV is the node value `1.124e-22`. -/
theorem bhSv_ten : bhSv 10 = 1.124e-22 := by
  have h := pl_natCast 6.788e-27 bhNodes.tail 9
  rw [show ((9 : ℕ) : ℝ) + 1 = 10 by norm_num] at h
  rw [bhSv, show bhNodes = 6.788e-27 :: bhNodes.tail from rfl, h]
  norm_num [bhNodes, lastD]

/-- Sanity (degenerate case): a single node gives a constant function. -/
theorem pl_singleton (a : ℚ) (T : ℝ) : pl [a] T = a := by simp [pl, inc]

/-- Rejected fixture: the zero function is not a Bosch–Hale reactivity (it violates the
`[10, 11]` keV enclosure `⟨σv⟩ ≥ 1.124e-22`). -/
theorem zero_not_boschHaleDT : ¬ BoschHaleDT (fun _ => 0) := by
  intro h
  have := (h.windows ⟨10, 11, 1.124e-22, 1.448e-22⟩ (by simp [boschHaleWindows]) 10
    (by norm_num) (by norm_num)).1
  norm_num at this

/-- Rejected fixture: a certificate cannot claim a window whose lower enclosure exceeds
the node value (here `svLo = 1e-21 > v[9] = 1.124e-22`). -/
theorem cert_rejects_bad_window :
    ¬ WindowsCert bhNodes [⟨10, 11, 1e-21, 1.448e-22⟩] := by
  intro h
  have hs := WindowsCert.sound (a := 6.788e-27) (rest := bhNodes.tail) bhNodes_nonDecr h
    _ List.mem_cons_self 10 (by norm_num) (by norm_num)
  have h10 : bhSv 10 = 1.124e-22 := bhSv_ten
  simp only [bhSv] at h10
  rw [show (6.788e-27 : ℚ) :: bhNodes.tail = bhNodes from rfl, h10] at hs
  norm_num at hs

end PlasmaLean.Sanity.BoschHaleInstance
