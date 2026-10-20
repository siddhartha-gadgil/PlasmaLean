/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Transport.BoschHaleFine
public import PlasmaLean.Sanity.BoschHaleInstance
public meta import Lean
public meta import Qq

/-!
# A concrete instance of the fine Bosch–Hale reactivity class

`PlasmaLean.Transport.BoschHaleFine` adds 100 supplied quarter-keV enclosures to the 61
kernel enclosures of `BoschHaleDT`. This module shows that the combined supplied facts are
**jointly consistent** by constructing an explicit function `bhFineSv` and proving
`BoschHaleFine bhFineSv` (`bhFineSv_boschHaleFine`).

## Construction

`bhFineSv = pl4 bhFineNodes`: the piecewise-linear interpolant of 237 rational node values at
`T = 1, 5/4, 3/2, …, 60` keV, constant outside `[1, 60]` (`pl4 v T = pl v (4T − 3)`, with `pl`
the increment-form interpolant of `Sanity.BoschHaleInstance`). The node at `T` is the largest
lower enclosure `svLo` among all (coarse and fine) windows with `lo ≤ T`; the nodes are
nondecreasing, so the interpolant is continuous and monotone.

## Window certificate (proof-term pattern)

`QWindowsCert` has one constructor step per window `w`: node indices `i, j` with
`i/4 + 1 ≤ w.lo`, `w.hi ≤ j/4 + 1`, the node values `a = v[i]`, `b = v[j]` (checked by the
kernel as definitional unfoldings of `List.getD`), and the two rational facts
`w.svLo ≤ a`, `b ≤ w.svHi`. `QWindowsCert.sound` proves once that a certificate gives
`∀ w ∈ ws, w.Holds (pl4 v)`. The tactic `qwindows_cert` peels the window list, reads the
endpoints (`n` or `n/4`), builds the certificate term and leaves `4` small rational goals per
window, closed by `norm_num` (161 windows). No `decide` is used for the windows.

This is an existence (consistency) check only; `bhFineSv` carries no physical authority.
-/

public section
noncomputable section

namespace PlasmaLean.Sanity.BoschHaleFineInstance

open PlasmaLean.Fusion PlasmaLean.Transport PlasmaLean.Sanity.BoschHaleInstance

/-- Piecewise-linear interpolant with nodes at `T = 1 + k/4` keV (`k = 0, 1, …`), constant
outside the node range: `pl4 v T = pl v (4T − 3)`. -/
@[expose] def pl4 (v : List ℚ) (T : ℝ) : ℝ := pl v (4 * T - 3)

/-- `pl4` is continuous. -/
theorem pl4_continuous (v : List ℚ) : Continuous (pl4 v) :=
  (pl_continuous v).comp (by fun_prop)

/-- For nondecreasing nodes `pl4` is monotone. -/
theorem pl4_monotone (v : List ℚ) (hv : NonDecr v) : Monotone (pl4 v) := fun x y h =>
  pl_monotone v hv (by linarith)

/-- `pl4` is at least the first node for nondecreasing nodes. -/
theorem pl4_ge_head (v : List ℚ) (hv : NonDecr v) (T : ℝ) : (v.headD 0 : ℝ) ≤ pl4 v T :=
  pl_ge_head v hv _

/-- Node evaluation: `pl4 v (k/4 + 1)` is the `k`-th node (the last node past the end). -/
theorem pl4_node (a : ℚ) (rest : List ℚ) (k : ℕ) :
    pl4 (a :: rest) ((k : ℝ) / 4 + 1) = ((a :: rest).getD k (lastD (a :: rest)) : ℝ) := by
  rw [pl4, show 4 * ((k : ℝ) / 4 + 1) - 3 = (k : ℝ) + 1 by ring, pl_natCast]

/-- **Quarter-keV window certificate.** One step per window `w`: node indices `i, j` with
`i/4 + 1 ≤ w.lo`, `w.hi ≤ j/4 + 1`, node values `a = v[i]`, `b = v[j]` (read with `getD`,
defaulting to the last node), `w.svLo ≤ a` and `b ≤ w.svHi`. All arguments are explicit for
the proof builder. -/
inductive QWindowsCert (v : List ℚ) : List ReactivityWindow → Prop where
  | nil : QWindowsCert v []
  | cons (i j : ℕ) (a b : ℚ) (w : ReactivityWindow) (ws : List ReactivityWindow) :
      (i : ℚ) / 4 + 1 ≤ w.lo → w.hi ≤ (j : ℚ) / 4 + 1 →
      v.getD i (lastD v) = a → v.getD j (lastD v) = b →
      w.svLo ≤ a → b ≤ w.svHi → QWindowsCert v ws → QWindowsCert v (w :: ws)

/-- **Soundness of quarter-keV window certificates** for nondecreasing nodes: every
certified window holds for `pl4 v`. -/
theorem QWindowsCert.sound {a0 : ℚ} {rest : List ℚ} (hv : NonDecr (a0 :: rest))
    {ws : List ReactivityWindow} (h : QWindowsCert (a0 :: rest) ws) :
    ∀ w ∈ ws, w.Holds (pl4 (a0 :: rest)) := by
  induction h with
  | nil => simp
  | cons i j a b w ws hi hj ha hb hlo hhi _ ih =>
    intro w' hw' T h1 h2
    rcases List.mem_cons.mp hw' with rfl | hw'
    · have hm := pl4_monotone _ hv
      have hi' : (i : ℝ) / 4 + 1 ≤ w'.lo := by
        have := (Rat.cast_le (K := ℝ)).2 hi; push_cast at this; exact this
      have hj' : (w'.hi : ℝ) ≤ (j : ℝ) / 4 + 1 := by
        have := (Rat.cast_le (K := ℝ)).2 hj; push_cast at this; exact this
      have hlo' : (w'.svLo : ℝ) ≤ ((a0 :: rest).getD i (lastD (a0 :: rest)) : ℝ) := by
        rw [ha]; exact_mod_cast hlo
      have hhi' : (((a0 :: rest).getD j (lastD (a0 :: rest)) : ℚ) : ℝ) ≤ w'.svHi := by
        rw [hb]; exact_mod_cast hhi
      rw [← pl4_node] at hlo' hhi'
      exact ⟨hlo'.trans (hm (hi'.trans h1)), (hm (h2.trans hj')).trans hhi'⟩
    · exact ih w' hw' T h1 h2

open Lean Meta Elab Tactic Qq in
/-- Read a window endpoint in quarter-keV units: a literal `n` gives `4n`, a literal
quotient `n / 4` gives `n`. -/
meta def quarterOf? (e : Expr) : Option ℕ :=
  if e.isAppOfArity ``OfNat.ofNat 3 then (e.getArg! 1).rawNatLit?.map (4 * ·)
  else if e.isAppOfArity ``HDiv.hDiv 6 then
    match natLitOf? (e.getArg! 4), natLitOf? (e.getArg! 5) with
    | some n, some 4 => some n
    | _, _ => none
  else none

open Lean Meta Elab Tactic Qq in
/-- The elements of a list literal (after unfolding definitions at the head). -/
meta partial def listElems (e : Expr) : MetaM (Array Expr) := do
  let e ← whnfD e
  if e.isAppOfArity ``List.nil 1 then return #[]
  else if e.isAppOfArity ``List.cons 3 then
    return #[e.getArg! 1] ++ (← listElems (e.getArg! 2))
  else throwError "expected a list literal, got {e}"

open Lean Meta Elab Tactic Qq in
/-- Build a `QWindowsCert v ws` proof term by peeling the window list `ws`. Node indices are
`i = 4·lo − 4`, `j = 4·hi − 4`; the node values are read off the literal node list (the
`getD` equations are closed by `Eq.refl`, i.e. checked by kernel unfolding). The four
rational side conditions of each window are returned as goals. -/
meta partial def mkQWindowsCert (v : Expr) (nodes : Array Expr) (ws : Expr) :
    MetaM (Expr × List MVarId) := do
  let ws ← whnfD ws
  if ws.isAppOfArity ``List.nil 1 then
    return (mkApp (mkConst ``QWindowsCert.nil) v, [])
  else if ws.isAppOfArity ``List.cons 3 then
    let w := ws.getArg! 1
    let rest := ws.getArg! 2
    let w' ← whnfD w
    unless w'.isAppOfArity ``ReactivityWindow.mk 4 do
      throwError "window is not a literal structure: {w'}"
    let some lo4 := quarterOf? (w'.getArg! 0) | throwError "bad lo: {w'}"
    let some hi4 := quarterOf? (w'.getArg! 1) | throwError "bad hi: {w'}"
    let i := lo4 - 4
    let j := hi4 - 4
    let a := nodes.getD i nodes.back!
    let b := nodes.getD j nodes.back!
    let f := mkAppN (mkConst ``QWindowsCert.cons) #[v, toExpr i, toExpr j, a, b, w, rest]
    let (mvs, _, _) ← forallMetaTelescopeReducing (← inferType f) (some 6)
    mvs[2]!.mvarId!.assign (← mkEqRefl a)
    mvs[3]!.mvarId!.assign (← mkEqRefl b)
    let (tl, gs) ← mkQWindowsCert v nodes rest
    return (mkAppN f (mvs.push tl),
      [mvs[0]!.mvarId!, mvs[1]!.mvarId!, mvs[4]!.mvarId!, mvs[5]!.mvarId!] ++ gs)
  else throwError "expected a list literal, got {ws}"

open Lean Meta Elab Tactic Qq in
/-- Tactic: close `QWindowsCert v ws` by building the certificate term; leaves the rational
side conditions as goals. -/
elab "qwindows_cert" : tactic => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let_expr QWindowsCert v ws := ty | throwError "expected QWindowsCert v ws"
  let nodes ← listElems v
  let ws' := (← unfoldDefinition? ws).getD ws
  let (pf, gs) ← mkQWindowsCert v nodes ws'
  g.assign (← mkExpectedTypeHint pf ty)
  replaceMainGoal gs

set_option maxRecDepth 10000 in
/-- Node values (m³/s) at `T = 1 + k/4` keV, `k = 0, …, 236`: the largest lower enclosure
among the coarse and fine windows starting at or below `T`. -/
@[expose] def bhFineNodes : List ℚ := [
  6.788e-27, 6.788e-27, 6.788e-27, 6.788e-27, 2.947e-25, 2.947e-25, 2.947e-25, 2.947e-25,
  1.848e-24, 1.848e-24, 1.848e-24, 1.848e-24, 5.914e-24, 5.914e-24, 5.914e-24, 5.914e-24,
  1.352e-23, 1.605e-23, 1.886e-23, 2.193e-23, 2.528e-23, 2.890e-23, 3.279e-23, 3.695e-23,
  4.137e-23, 4.605e-23, 5.099e-23, 5.617e-23, 6.160e-23, 6.725e-23, 7.312e-23, 7.921e-23,
  8.550e-23, 9.198e-23, 9.865e-23, 1.054e-22, 1.124e-22, 1.196e-22, 1.269e-22, 1.343e-22,
  1.418e-22, 1.495e-22, 1.572e-22, 1.650e-22, 1.729e-22, 1.809e-22, 1.890e-22, 1.971e-22,
  2.052e-22, 2.134e-22, 2.216e-22, 2.299e-22, 2.381e-22, 2.464e-22, 2.547e-22, 2.629e-22,
  2.712e-22, 2.795e-22, 2.877e-22, 2.959e-22, 3.041e-22, 3.122e-22, 3.204e-22, 3.284e-22,
  3.365e-22, 3.445e-22, 3.524e-22, 3.603e-22, 3.681e-22, 3.759e-22, 3.836e-22, 3.913e-22,
  3.989e-22, 4.064e-22, 4.139e-22, 4.213e-22, 4.286e-22, 4.359e-22, 4.431e-22, 4.502e-22,
  4.573e-22, 4.642e-22, 4.711e-22, 4.780e-22, 4.847e-22, 4.914e-22, 4.980e-22, 5.045e-22,
  5.110e-22, 5.173e-22, 5.236e-22, 5.299e-22, 5.360e-22, 5.421e-22, 5.481e-22, 5.540e-22,
  5.598e-22, 5.656e-22, 5.713e-22, 5.769e-22, 5.824e-22, 5.879e-22, 5.933e-22, 5.986e-22,
  6.038e-22, 6.090e-22, 6.141e-22, 6.192e-22, 6.241e-22, 6.290e-22, 6.338e-22, 6.386e-22,
  6.433e-22, 6.479e-22, 6.524e-22, 6.569e-22, 6.613e-22, 6.613e-22, 6.613e-22, 6.613e-22,
  6.784e-22, 6.784e-22, 6.784e-22, 6.784e-22, 6.944e-22, 6.944e-22, 6.944e-22, 6.944e-22,
  7.095e-22, 7.095e-22, 7.095e-22, 7.095e-22, 7.237e-22, 7.237e-22, 7.237e-22, 7.237e-22,
  7.370e-22, 7.370e-22, 7.370e-22, 7.370e-22, 7.494e-22, 7.494e-22, 7.494e-22, 7.494e-22,
  7.611e-22, 7.611e-22, 7.611e-22, 7.611e-22, 7.720e-22, 7.720e-22, 7.720e-22, 7.720e-22,
  7.822e-22, 7.822e-22, 7.822e-22, 7.822e-22, 7.917e-22, 7.917e-22, 7.917e-22, 7.917e-22,
  8.006e-22, 8.006e-22, 8.006e-22, 8.006e-22, 8.088e-22, 8.088e-22, 8.088e-22, 8.088e-22,
  8.165e-22, 8.165e-22, 8.165e-22, 8.165e-22, 8.236e-22, 8.236e-22, 8.236e-22, 8.236e-22,
  8.302e-22, 8.302e-22, 8.302e-22, 8.302e-22, 8.363e-22, 8.363e-22, 8.363e-22, 8.363e-22,
  8.419e-22, 8.419e-22, 8.419e-22, 8.419e-22, 8.471e-22, 8.471e-22, 8.471e-22, 8.471e-22,
  8.519e-22, 8.519e-22, 8.519e-22, 8.519e-22, 8.562e-22, 8.562e-22, 8.562e-22, 8.562e-22,
  8.602e-22, 8.602e-22, 8.602e-22, 8.602e-22, 8.638e-22, 8.638e-22, 8.638e-22, 8.638e-22,
  8.671e-22, 8.671e-22, 8.671e-22, 8.671e-22, 8.700e-22, 8.700e-22, 8.700e-22, 8.700e-22,
  8.727e-22, 8.727e-22, 8.727e-22, 8.727e-22, 8.750e-22, 8.750e-22, 8.750e-22, 8.750e-22,
  8.771e-22, 8.771e-22, 8.771e-22, 8.771e-22, 8.789e-22, 8.789e-22, 8.789e-22, 8.789e-22,
  8.805e-22, 8.805e-22, 8.805e-22, 8.805e-22, 8.805e-22
]

/-- The explicit interpolated reactivity (m³/s, `T` in keV). -/
@[expose] def bhFineSv : ℝ → ℝ := pl4 bhFineNodes

/-- There are 237 nodes (`T = 1, …, 60` keV in steps of `1/4`). -/
theorem bhFineNodes_length : bhFineNodes.length = 237 := by decide +kernel

/-- Boolean test that a list is nondecreasing. -/
@[expose] def nonDecrB : List ℚ → Bool
  | v :: w :: rest => decide (v ≤ w) && nonDecrB (w :: rest)
  | _ => true

/-- The Boolean test is sound. -/
theorem nonDecr_of_nonDecrB : ∀ v : List ℚ, nonDecrB v = true → NonDecr v
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: rest, h => by
    simp only [nonDecrB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, nonDecr_of_nonDecrB (b :: rest) h.2⟩

/-- The node values are nondecreasing (one kernel evaluation of the Boolean test). -/
theorem bhFineNodes_nonDecr : NonDecr bhFineNodes :=
  nonDecr_of_nonDecrB _ (by decide +kernel)

/-- The certificate for the 61 coarse kernel windows, built as an explicit proof term. -/
theorem bhFineNodes_coarse_cert : QWindowsCert bhFineNodes boschHaleWindows := by
  qwindows_cert
  all_goals norm_num

/-- The certificate for the 100 fine windows, built as an explicit proof term. -/
theorem bhFineNodes_fine_cert : QWindowsCert bhFineNodes boschHaleFineWindows := by
  qwindows_cert
  all_goals norm_num

/-- `bhFineNodes` as an explicit cons cell (for the soundness theorem). -/
theorem bhFineNodes_cons : bhFineNodes = 6.788e-27 :: bhFineNodes.tail := by decide +kernel

/-- **Non-vacuity of `BoschHaleFine`.** The explicit interpolant `bhFineSv` satisfies every
supplied Bosch–Hale fact: nonnegativity, continuity, monotonicity on `[1, 60]` keV, the 61
coarse and the 100 fine rational enclosures. In particular the fine and coarse supplied data
are jointly consistent. -/
instance bhFineSv_boschHaleFine : BoschHaleFine bhFineSv where
  nonneg T _ := by
    have h := pl4_ge_head bhFineNodes bhFineNodes_nonDecr T
    have e : bhFineNodes.headD 0 = 6.788e-27 := by decide +kernel
    have h0 : (0 : ℝ) ≤ (bhFineNodes.headD 0 : ℚ) := by rw [e]; norm_num
    exact h0.trans h
  continuousOn := (pl4_continuous bhFineNodes).continuousOn
  monotoneOn := (pl4_monotone bhFineNodes bhFineNodes_nonDecr).monotoneOn _
  windows := by
    have hv := bhFineNodes_nonDecr
    rw [bhFineNodes_cons] at hv
    have h := bhFineNodes_coarse_cert
    rw [bhFineNodes_cons] at h
    have := QWindowsCert.sound hv h
    rwa [← bhFineNodes_cons] at this
  fine := by
    have hv := bhFineNodes_nonDecr
    rw [bhFineNodes_cons] at hv
    have h := bhFineNodes_fine_cert
    rw [bhFineNodes_cons] at h
    have := QWindowsCert.sound hv h
    rwa [← bhFineNodes_cons] at this

/-- Sanity (accepted fixture): `bhFineSv` at `15 keV` is the node value `2.712e-22`. -/
theorem bhFineSv_fifteen : bhFineSv 15 = 2.712e-22 := by
  have h := pl4_node 6.788e-27 bhFineNodes.tail 56
  rw [show ((56 : ℕ) : ℝ) / 4 + 1 = 15 by norm_num, ← bhFineNodes_cons] at h
  have e : bhFineNodes.getD 56 (lastD bhFineNodes) = 2.712e-22 := by decide +kernel
  rw [bhFineSv, h, e]
  norm_num

/-- Rejected fixture: the zero function is not a fine Bosch–Hale reactivity (it violates the
fine window `[15, 61/4]` keV, `⟨σv⟩ ≥ 2.712e-22`). -/
theorem zero_not_boschHaleFine : ¬ BoschHaleFine (fun _ => 0) := by
  intro h
  have := (h.fine ⟨60 / 4, 61 / 4, 2.712e-22, 2.852e-22⟩ (by simp [boschHaleFineWindows]) 15
    (by norm_num) (by norm_num)).1
  norm_num at this

end PlasmaLean.Sanity.BoschHaleFineInstance
