/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Kernel.Fusion
public import PlasmaLean.Certificates.KernelFact

/-!
# Finer supplied Bosch–Hale reactivity windows (quarter-keV on `[5, 30]` keV)

The kernel class `PlasmaLean.Fusion.BoschHaleDT` supplies D-T reactivity enclosures on
windows of width `1 keV`. Near ignition temperatures (`10–20 keV`) such a window leaves a
≈ 10 % uncertainty in the alpha heating, which is larger than the margin of an ignited or
high-`Q` transport band (see `Design.SolovevBand`). This module adds **finer supplied data**
without touching the kernel file.

## Data (supplied, not proved)

`boschHaleFineWindows`: the 100 windows `[k/4, (k+1)/4]` keV for `k = 20, …, 119`, i.e. width
`1/4 keV` covering `[5, 30]` keV. Source and tolerance are **exactly those of the kernel
table**: the Bosch–Hale D-T parametrization (H.-S. Bosch and G. M. Hale, *Improved formulas
for fusion cross-sections and thermal reactivities*, Nucl. Fusion **32** (1992) 611,
Table VII and eqs. (12)–(14), D-T fit valid on 0.2–100 keV), evaluated with 50-digit Python
`decimal` arithmetic; on `[5, 30]` the fit is increasing, so
`svLo = ⌊0.99 · BH(lo)⌋₄` and `svHi = ⌈1.01 · BH(hi)⌉₄` (a relative ±1 % margin for fit
accuracy, four significant digits rounded outward). The same script reproduces the 61
kernel windows digit for digit (oracle `/tmp/k4/bhfine.py`, untrusted).

## Contents

* `BoschHaleFine sv`: `BoschHaleDT sv` (nonnegativity, continuity, monotonicity on `[1,60]`,
  the coarse windows) **plus** the fine windows.
* `fine_refines_coarse`: every fine window lies inside a coarse window and has tighter
  enclosures (consistency of the two data sets where they overlap). Joint satisfiability of
  all supplied facts is the non-vacuity instance of `Sanity.BoschHaleFineInstance`.
* Label maps for barrier certificates: `svFloorF` (lower enclosure of the fine, else coarse,
  window starting at `k`) and `svCeilF` (upper enclosure of the window ending at `K`), with
  `svFloorF_le` and `sv_le_svCeilF`.
-/

public section
noncomputable section

namespace PlasmaLean.Transport

open PlasmaLean.Fusion

/-- **Supplied fine Bosch–Hale D-T enclosures** (Nucl. Fusion 32 (1992) 611): the windows
`[k/4, (k+1)/4]` keV, `k = 20, …, 119`, with `svLo = ⌊0.99·BH(lo)⌋₄`, `svHi = ⌈1.01·BH(hi)⌉₄`
(m³/s, four significant digits rounded outward, 50-digit decimal evaluation).
**Supplied data, not proved in Lean.** -/
@[expose] def boschHaleFineWindows : List ReactivityWindow := [
  ⟨20/4, 21/4, 1.352e-23, 1.639e-23⟩,
  ⟨21/4, 22/4, 1.605e-23, 1.925e-23⟩,
  ⟨22/4, 23/4, 1.886e-23, 2.238e-23⟩,
  ⟨23/4, 24/4, 2.193e-23, 2.580e-23⟩,
  ⟨24/4, 25/4, 2.528e-23, 2.949e-23⟩,
  ⟨25/4, 26/4, 2.890e-23, 3.346e-23⟩,
  ⟨26/4, 27/4, 3.279e-23, 3.770e-23⟩,
  ⟨27/4, 28/4, 3.695e-23, 4.222e-23⟩,
  ⟨28/4, 29/4, 4.137e-23, 4.699e-23⟩,
  ⟨29/4, 30/4, 4.605e-23, 5.203e-23⟩,
  ⟨30/4, 31/4, 5.099e-23, 5.732e-23⟩,
  ⟨31/4, 32/4, 5.617e-23, 6.285e-23⟩,
  ⟨32/4, 33/4, 6.160e-23, 6.862e-23⟩,
  ⟨33/4, 34/4, 6.725e-23, 7.461e-23⟩,
  ⟨34/4, 35/4, 7.312e-23, 8.082e-23⟩,
  ⟨35/4, 36/4, 7.921e-23, 8.724e-23⟩,
  ⟨36/4, 37/4, 8.550e-23, 9.385e-23⟩,
  ⟨37/4, 38/4, 9.198e-23, 1.007e-22⟩,
  ⟨38/4, 39/4, 9.865e-23, 1.077e-22⟩,
  ⟨39/4, 40/4, 1.054e-22, 1.148e-22⟩,
  ⟨40/4, 41/4, 1.124e-22, 1.221e-22⟩,
  ⟨41/4, 42/4, 1.196e-22, 1.295e-22⟩,
  ⟨42/4, 43/4, 1.269e-22, 1.371e-22⟩,
  ⟨43/4, 44/4, 1.343e-22, 1.448e-22⟩,
  ⟨44/4, 45/4, 1.418e-22, 1.526e-22⟩,
  ⟨45/4, 46/4, 1.495e-22, 1.605e-22⟩,
  ⟨46/4, 47/4, 1.572e-22, 1.685e-22⟩,
  ⟨47/4, 48/4, 1.650e-22, 1.765e-22⟩,
  ⟨48/4, 49/4, 1.729e-22, 1.847e-22⟩,
  ⟨49/4, 50/4, 1.809e-22, 1.929e-22⟩,
  ⟨50/4, 51/4, 1.890e-22, 2.012e-22⟩,
  ⟨51/4, 52/4, 1.971e-22, 2.095e-22⟩,
  ⟨52/4, 53/4, 2.052e-22, 2.178e-22⟩,
  ⟨53/4, 54/4, 2.134e-22, 2.262e-22⟩,
  ⟨54/4, 55/4, 2.216e-22, 2.346e-22⟩,
  ⟨55/4, 56/4, 2.299e-22, 2.430e-22⟩,
  ⟨56/4, 57/4, 2.381e-22, 2.515e-22⟩,
  ⟨57/4, 58/4, 2.464e-22, 2.599e-22⟩,
  ⟨58/4, 59/4, 2.547e-22, 2.684e-22⟩,
  ⟨59/4, 60/4, 2.629e-22, 2.768e-22⟩,
  ⟨60/4, 61/4, 2.712e-22, 2.852e-22⟩,
  ⟨61/4, 62/4, 2.795e-22, 2.936e-22⟩,
  ⟨62/4, 63/4, 2.877e-22, 3.020e-22⟩,
  ⟨63/4, 64/4, 2.959e-22, 3.103e-22⟩,
  ⟨64/4, 65/4, 3.041e-22, 3.186e-22⟩,
  ⟨65/4, 66/4, 3.122e-22, 3.269e-22⟩,
  ⟨66/4, 67/4, 3.204e-22, 3.352e-22⟩,
  ⟨67/4, 68/4, 3.284e-22, 3.434e-22⟩,
  ⟨68/4, 69/4, 3.365e-22, 3.515e-22⟩,
  ⟨69/4, 70/4, 3.445e-22, 3.596e-22⟩,
  ⟨70/4, 71/4, 3.524e-22, 3.677e-22⟩,
  ⟨71/4, 72/4, 3.603e-22, 3.757e-22⟩,
  ⟨72/4, 73/4, 3.681e-22, 3.836e-22⟩,
  ⟨73/4, 74/4, 3.759e-22, 3.915e-22⟩,
  ⟨74/4, 75/4, 3.836e-22, 3.993e-22⟩,
  ⟨75/4, 76/4, 3.913e-22, 4.071e-22⟩,
  ⟨76/4, 77/4, 3.989e-22, 4.147e-22⟩,
  ⟨77/4, 78/4, 4.064e-22, 4.224e-22⟩,
  ⟨78/4, 79/4, 4.139e-22, 4.299e-22⟩,
  ⟨79/4, 80/4, 4.213e-22, 4.374e-22⟩,
  ⟨80/4, 81/4, 4.286e-22, 4.448e-22⟩,
  ⟨81/4, 82/4, 4.359e-22, 4.521e-22⟩,
  ⟨82/4, 83/4, 4.431e-22, 4.594e-22⟩,
  ⟨83/4, 84/4, 4.502e-22, 4.666e-22⟩,
  ⟨84/4, 85/4, 4.573e-22, 4.737e-22⟩,
  ⟨85/4, 86/4, 4.642e-22, 4.808e-22⟩,
  ⟨86/4, 87/4, 4.711e-22, 4.877e-22⟩,
  ⟨87/4, 88/4, 4.780e-22, 4.946e-22⟩,
  ⟨88/4, 89/4, 4.847e-22, 5.014e-22⟩,
  ⟨89/4, 90/4, 4.914e-22, 5.082e-22⟩,
  ⟨90/4, 91/4, 4.980e-22, 5.148e-22⟩,
  ⟨91/4, 92/4, 5.045e-22, 5.214e-22⟩,
  ⟨92/4, 93/4, 5.110e-22, 5.279e-22⟩,
  ⟨93/4, 94/4, 5.173e-22, 5.343e-22⟩,
  ⟨94/4, 95/4, 5.236e-22, 5.407e-22⟩,
  ⟨95/4, 96/4, 5.299e-22, 5.469e-22⟩,
  ⟨96/4, 97/4, 5.360e-22, 5.531e-22⟩,
  ⟨97/4, 98/4, 5.421e-22, 5.592e-22⟩,
  ⟨98/4, 99/4, 5.481e-22, 5.653e-22⟩,
  ⟨99/4, 100/4, 5.540e-22, 5.712e-22⟩,
  ⟨100/4, 101/4, 5.598e-22, 5.771e-22⟩,
  ⟨101/4, 102/4, 5.656e-22, 5.829e-22⟩,
  ⟨102/4, 103/4, 5.713e-22, 5.886e-22⟩,
  ⟨103/4, 104/4, 5.769e-22, 5.943e-22⟩,
  ⟨104/4, 105/4, 5.824e-22, 5.999e-22⟩,
  ⟨105/4, 106/4, 5.879e-22, 6.054e-22⟩,
  ⟨106/4, 107/4, 5.933e-22, 6.108e-22⟩,
  ⟨107/4, 108/4, 5.986e-22, 6.161e-22⟩,
  ⟨108/4, 109/4, 6.038e-22, 6.214e-22⟩,
  ⟨109/4, 110/4, 6.090e-22, 6.266e-22⟩,
  ⟨110/4, 111/4, 6.141e-22, 6.318e-22⟩,
  ⟨111/4, 112/4, 6.192e-22, 6.368e-22⟩,
  ⟨112/4, 113/4, 6.241e-22, 6.418e-22⟩,
  ⟨113/4, 114/4, 6.290e-22, 6.467e-22⟩,
  ⟨114/4, 115/4, 6.338e-22, 6.516e-22⟩,
  ⟨115/4, 116/4, 6.386e-22, 6.564e-22⟩,
  ⟨116/4, 117/4, 6.433e-22, 6.611e-22⟩,
  ⟨117/4, 118/4, 6.479e-22, 6.657e-22⟩,
  ⟨118/4, 119/4, 6.524e-22, 6.703e-22⟩,
  ⟨119/4, 120/4, 6.569e-22, 6.748e-22⟩
]

/-- **Fine supplied Bosch–Hale reactivity**: the kernel facts `BoschHaleDT` (including
monotonicity on `[1, 60]` keV) together with the 100 quarter-keV enclosures
`boschHaleFineWindows` on `[5, 30]` keV. **Supplied data, not proved.** -/
class BoschHaleFine (sv : ℝ → ℝ) : Prop extends BoschHaleDT sv where
  /-- The fine enclosures hold. -/
  fine : ∀ w ∈ boschHaleFineWindows, w.Holds sv

/-- There are 100 fine windows. -/
theorem boschHaleFineWindows_length : boschHaleFineWindows.length = 100 := rfl

/-- Boolean refinement test: the fine window `wf` lies in the coarse window `wc` and has
tighter enclosures. -/
@[expose] def windowRefines (wf wc : ReactivityWindow) : Bool :=
  decide (wc.lo ≤ wf.lo) && decide (wf.hi ≤ wc.hi) && decide (wc.svLo ≤ wf.svLo) &&
    decide (wf.svHi ≤ wc.svHi)

/-- The refinement check over all fine windows (evaluated once). -/
theorem fine_refines_check :
    boschHaleFineWindows.all (fun wf => boschHaleWindows.any (windowRefines wf)) = true := by
  kernel_fact

/-- **Consistency with the coarse kernel data.** Every fine window lies inside a coarse
window `[k, k+1]` and its enclosure is contained in the coarse one: the fine data refine the
coarse data where they overlap. -/
theorem fine_refines_coarse : ∀ wf ∈ boschHaleFineWindows, ∃ wc ∈ boschHaleWindows,
    wc.lo ≤ wf.lo ∧ wf.hi ≤ wc.hi ∧ wc.svLo ≤ wf.svLo ∧ wf.svHi ≤ wc.svHi := by
  intro wf hwf
  obtain ⟨wc, hwc, h⟩ := List.any_eq_true.1 (List.all_eq_true.1 fine_refines_check wf hwf)
  simp only [windowRefines, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨wc, hwc, h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- Well-formedness of a window list: `1 ≤ lo ≤ hi`. -/
@[expose] def windowsWF (ws : List ReactivityWindow) : Bool :=
  ws.all (fun w => decide (1 ≤ w.lo) && decide (w.lo ≤ w.hi))

/-- Both supplied window lists are well formed. -/
theorem windows_wf_check :
    (windowsWF boschHaleWindows && windowsWF boschHaleFineWindows) = true := by
  kernel_fact

/-- **Floor from one window.** If `w` holds, `1 ≤ w.lo ≤ w.hi`, `w.lo = k ≤ T ≤ 60` and `sv`
is increasing on `[1,60]`, then `w.svLo ≤ sv T`. -/
theorem window_floor_le (sv : ℝ → ℝ) [BoschHaleDT sv] {w : ReactivityWindow} (hw : w.Holds sv)
    (h1 : 1 ≤ w.lo) (h2 : w.lo ≤ w.hi) {T : ℝ} (hkT : (w.lo : ℝ) ≤ T) (hT : T ≤ 60) :
    (w.svLo : ℝ) ≤ sv T := by
  have h1' : (1 : ℝ) ≤ w.lo := by exact_mod_cast h1
  have hw' := (hw (w.lo : ℝ) le_rfl (by exact_mod_cast h2)).1
  have hm := BoschHaleDT.monotoneOn (sv := sv) ⟨h1', hkT.trans hT⟩ ⟨h1'.trans hkT, hT⟩ hkT
  linarith

/-- **Ceiling from one window.** If `w` holds, `w.lo ≤ w.hi ≤ 60` and `1 ≤ T ≤ w.hi`,
then `sv T ≤ w.svHi`. -/
theorem window_ceil_le (sv : ℝ → ℝ) [BoschHaleDT sv] {w : ReactivityWindow} (hw : w.Holds sv)
    (h2 : w.lo ≤ w.hi) (h60 : w.hi ≤ 60) {T : ℝ} (hT1 : 1 ≤ T)
    (hTK : T ≤ w.hi) : sv T ≤ (w.svHi : ℝ) := by
  have h60' : (w.hi : ℝ) ≤ 60 := by exact_mod_cast h60
  have hw' := (hw (w.hi : ℝ) (by exact_mod_cast h2) le_rfl).2
  have hm := BoschHaleDT.monotoneOn (sv := sv) ⟨hT1, hTK.trans h60'⟩
    ⟨hT1.trans hTK, h60'⟩ hTK
  linarith

/-- Reactivity floor for the label `k` (keV): the lower enclosure of the fine window starting
at `k`, else of the coarse window starting at `k`, else `0`. -/
@[expose] def svFloorF (k : ℚ) : ℚ :=
  match boschHaleFineWindows.find? (fun w => w.lo == k) with
  | some w => w.svLo
  | none =>
    match boschHaleWindows.find? (fun w => w.lo == k) with
    | some w => w.svLo
    | none => 0

/-- Reactivity ceiling for the label `K` (keV): the upper enclosure of the fine window ending
at `K`, else of the coarse window ending at `K`, else `0`. -/
@[expose] def svCeilF (K : ℚ) : ℚ :=
  match boschHaleFineWindows.find? (fun w => w.hi == K) with
  | some w => w.svHi
  | none =>
    match boschHaleWindows.find? (fun w => w.hi == K) with
    | some w => w.svHi
    | none => 0

/-- `K` ends a supplied (fine or coarse) window. -/
@[expose] def ceilOK (K : ℚ) : Bool :=
  (boschHaleFineWindows.find? (fun w => w.hi == K)).isSome ||
    (boschHaleWindows.find? (fun w => w.hi == K)).isSome

/-- Members of a well-formed list satisfy `1 ≤ lo ≤ hi`. -/
theorem windowsWF_mem {ws : List ReactivityWindow} (h : windowsWF ws = true)
    {w : ReactivityWindow}
    (hw : w ∈ ws) : 1 ≤ w.lo ∧ w.lo ≤ w.hi := by
  have := List.all_eq_true.1 h w hw
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using this

/-- **Fine reactivity floor.** If `0 ≤ k ≤ T ≤ 60` keV then `svFloorF k ≤ ⟨σv⟩(T)`. -/
theorem svFloorF_le (sv : ℝ → ℝ) [hs : BoschHaleFine sv] {k : ℚ} (hk : 0 ≤ k) {T : ℝ}
    (hkT : (k : ℝ) ≤ T) (hT : T ≤ 60) : (svFloorF k : ℝ) ≤ sv T := by
  have hwf := windows_wf_check
  simp only [Bool.and_eq_true] at hwf
  unfold svFloorF
  split
  · rename_i w h
    have hmem := List.mem_of_find?_eq_some h
    have hlo : w.lo = k := by simpa using List.find?_some h
    obtain ⟨h1, h2⟩ := windowsWF_mem hwf.2 hmem
    exact window_floor_le sv (hs.fine w hmem) h1 h2 (by rw [hlo]; exact hkT) hT
  · split
    · rename_i w h
      have hmem := List.mem_of_find?_eq_some h
      have hlo : w.lo = k := by simpa using List.find?_some h
      obtain ⟨h1, h2⟩ := windowsWF_mem hwf.1 hmem
      exact window_floor_le sv (BoschHaleDT.windows w hmem) h1 h2 (by rw [hlo]; exact hkT) hT
    · simp only [Rat.cast_zero]
      exact BoschHaleDT.nonneg T ((by exact_mod_cast hk : (0 : ℝ) ≤ k).trans hkT)

/-- **Fine reactivity ceiling.** If `K` ends a supplied window, `K ≤ 60` and `1 ≤ T ≤ K`,
then `⟨σv⟩(T) ≤ svCeilF K`. -/
theorem sv_le_svCeilF (sv : ℝ → ℝ) [hs : BoschHaleFine sv] {K : ℚ} (hK : ceilOK K = true)
    (hK60 : K ≤ 60) {T : ℝ} (h1 : 1 ≤ T) (hTK : T ≤ K) : sv T ≤ (svCeilF K : ℝ) := by
  have hwf := windows_wf_check
  simp only [Bool.and_eq_true] at hwf
  unfold svCeilF
  split
  · rename_i w h
    have hmem := List.mem_of_find?_eq_some h
    have hhi : w.hi = K := by simpa using List.find?_some h
    obtain ⟨-, h2'⟩ := windowsWF_mem hwf.2 hmem
    exact window_ceil_le sv (hs.fine w hmem) h2' (by rw [hhi]; exact hK60) h1
      (by rw [hhi]; exact hTK)
  · rename_i hnone
    have hK' : (boschHaleWindows.find? (fun w => w.hi == K)).isSome = true := by
      simpa [ceilOK, hnone] using hK
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hK'
    rw [hw]
    have hmem := List.mem_of_find?_eq_some hw
    have hhi : w.hi = K := by simpa using List.find?_some hw
    obtain ⟨-, h2'⟩ := windowsWF_mem hwf.1 hmem
    exact window_ceil_le sv (BoschHaleDT.windows w hmem) h2' (by rw [hhi]; exact hK60) h1
      (by rw [hhi]; exact hTK)

/-- Sanity (accepted fixture): the floor at `61/4 keV` is the fine value `2.795e-22`, larger
than the coarse floor `2.712e-22` at `15 keV`. -/
theorem svFloorF_fixture : svFloorF (61 / 4) = 2.795e-22 := by kernel_fact

/-- Sanity (rejected fixture): `61/8 keV` is not a window end, so it is not a valid ceiling
label. -/
theorem ceilOK_reject : ceilOK (61 / 8) = false := by kernel_fact

end PlasmaLean.Transport
