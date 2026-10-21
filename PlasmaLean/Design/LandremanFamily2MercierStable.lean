/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2Cert1
public import PlasmaLean.Design.LandremanFamily2Cert2
public import PlasmaLean.Design.LandremanFamily2Cert3
public import PlasmaLean.Design.LandremanFamily2Cert4
public import PlasmaLean.Design.LandremanFamily2Cert5
public import PlasmaLean.Design.LandremanFamily2Cert6
public import PlasmaLean.Design.LandremanFamily2Cert7
public import PlasmaLean.Design.LandremanFamily2MercierData

/-!
# A certified Mercier-stable band of Landreman's family 2 (`ε = 1/4`, `S = 4`, `λ = 200`)

**Main result** (`family2_mercier_stable`): for Landreman's explicit finite-β,
non-axisymmetric MHS equilibrium of family 2 (arXiv:2609.26742 v2, §3) with `ε = 1/4`,
`S = 4`, `λ = 200`, every flux surface `ψ = k²/2` with `k ∈ [7/10, 9/10]` is **Mercier stable**:
`D_Merc > 0` for both signs `s_G = ±1` and every `μ₀ > 0`, `p_a`, where `D_Merc` is the general
Mercier index of `PlasmaLean.Stability.MercierGeneral` (Landreman–Jorge 2020, eq. (3.1)) of the
surface data `LandremanFamily2MercierData.family2Data`. Its pointwise inputs come from the actual
field, current and pressure; the flux labels (ψ_t, ψ_p, V, I) and the area element are hand-derived
formulas from the paper (eq. 3.18), not derived from the field in Lean (an unformalized change of
variables). The stabilizing shear term ι′ rests on them; they were checked numerically.

**Proof.** `mercierIndex_family2_eq` rewrites `(2π)⁶ D_Merc` exactly as the closed form `D6R`.
The validated checker `LandremanFamily2Quad.cellCheck` (fixed-point interval arithmetic,
rigorous `arcsin`/`arctan`/`cosh`/`sinh` enclosures, product integration of the sharp
`1/|∇ψ|²` ridge with an exact Lorentzian kernel in a ridge-aligned poloidal angle, outward
rounding throughout) is run by `decide +kernel` on 34 `k`-cells covering `[7/10, 9/10]`
(`LandremanFamily2Cert1` … `Cert7`); `cellCheck_sound` turns each run into `D6R > 0` on the
cell, and `CoveredF2.sound` assembles the cover. No numerical value enters as a hypothesis.

**Physics.** The band `k ∈ [0.7, 0.9]` is the outer part of the plasma `ψ ≤ 81/200` whose field
lines are confined for all time (`LandremanFamily2.fieldLine_confined`); the equilibrium,
with pressure `p = (81/200 - ψ)/(λ² μ₀) > 0` inside and `0` on the boundary, satisfies the
kernel force balance (`family2_lam200_equilibrium`). Numerically the surfaces have a magnetic hill
(`V'' > 0`; only `μ₀ p' < 0` is proved); stability comes from the magnetic shear, which beats
the hill
because `λ = 200` makes `β` small (on-axis `β ≈ 3·10⁻⁴`). The untrusted map
(`scripts/landreman_family2_map.py`) gives the Mercier-stable region `k ≳ k_c(λ)` with
`k_c ≈ 0.91, 0.82, 0.68, 0.53` for `λ = 30, 50, 100, 200` (none for `λ ≤ 15`, the paper-scale
`β ≈ 5%` instance of `LandremanFamily2.realistic_instance`).

**Scope.** Local interchange (Mercier) criterion only, via the SUPPLIED Landreman–Jorge formula
(its derivation from `δW` is not formalized); no ballooning, global, resistive or kinetic
statement. The identification of the one-dimensional flux/volume/current integrals and of the
coordinate area element with the physical ones rests on the (unformalized) change of variables
to the paper's coordinates `(ψ, χ, ζ)`; all pointwise identities are proved.
-/

public section

namespace PlasmaLean.Design.LandremanFamily2Cert

open PlasmaLean.Design.LandremanFamily2Quad PlasmaLean.Design.LandremanFamily2MercierData
open PlasmaLean.Stability.MercierGeneral PlasmaLean.Design.LandremanFamily2

/-- Cover of a `k`-interval by accepted checker cells (`λ = 200`). -/
inductive CoveredF2 : ℚ → ℚ → Prop where
  /-- A single accepted cell. -/
  | cell (a b : ℚ) (N1 nt ns n2 : ℕ) : cellCheck 200 N1 nt ns n2 a b = true → CoveredF2 a b
  /-- Two adjacent covered intervals. -/
  | join (a b c : ℚ) : CoveredF2 a b → CoveredF2 b c → CoveredF2 a c

/-- **Soundness of a cover**: `(2π)⁶ D_Merc > 0` for both signs on every surface of the
covered interval. -/
theorem CoveredF2.sound {a b : ℚ} (h : CoveredF2 a b) :
    ∀ k : ℝ, (a : ℝ) ≤ k → k ≤ b → 0 < D6R 200 k 1 ∧ 0 < D6R 200 k (-1) := by
  induction h with
  | cell a b N1 nt ns n2 hc =>
    intro k h1 h2
    have := cellCheck_sound hc h1 h2
    push_cast at this
    exact this
  | join a b c _ _ ih1 ih2 =>
    intro k h1 h2
    rcases le_total k b with hk | hk
    · exact ih1 k h1 hk
    · exact ih2 k hk h2

/-- **The cover of `[7/10, 9/10]`** by 34 kernel-checked cells. -/
theorem family2_cover : CoveredF2 (7 / 10) (9 / 10) :=
  CoveredF2.join _ _ _ (CoveredF2.cell (7/10) (45/64) 128 12 12 6 cell0)
    (CoveredF2.join _ _ _ (CoveredF2.cell (45/64) (113/160) 128 12 12 6 cell1)
    (CoveredF2.join _ _ _ (CoveredF2.cell (113/160) (227/320) 128 12 12 6 cell2)
    (CoveredF2.join _ _ _ (CoveredF2.cell (227/320) (57/80) 128 8 8 4 cell3)
    (CoveredF2.join _ _ _ (CoveredF2.cell (57/80) (23/32) 128 12 12 6 cell4)
    (CoveredF2.join _ _ _ (CoveredF2.cell (23/32) (29/40) 128 12 12 6 cell5)
    (CoveredF2.join _ _ _ (CoveredF2.cell (29/40) (117/160) 128 12 12 6 cell6)
    (CoveredF2.join _ _ _ (CoveredF2.cell (117/160) (59/80) 128 12 12 6 cell7)
    (CoveredF2.join _ _ _ (CoveredF2.cell (59/80) (119/160) 128 12 12 6 cell8)
    (CoveredF2.join _ _ _ (CoveredF2.cell (119/160) (3/4) 128 12 12 6 cell9)
    (CoveredF2.join _ _ _ (CoveredF2.cell (3/4) (121/160) 128 12 12 6 cell10)
    (CoveredF2.join _ _ _ (CoveredF2.cell (121/160) (61/80) 128 12 12 6 cell11)
    (CoveredF2.join _ _ _ (CoveredF2.cell (61/80) (123/160) 128 12 12 6 cell12)
    (CoveredF2.join _ _ _ (CoveredF2.cell (123/160) (31/40) 128 12 12 6 cell13)
    (CoveredF2.join _ _ _ (CoveredF2.cell (31/40) (25/32) 128 12 12 6 cell14)
    (CoveredF2.join _ _ _ (CoveredF2.cell (25/32) (63/80) 128 8 8 4 cell15)
    (CoveredF2.join _ _ _ (CoveredF2.cell (63/80) (127/160) 128 8 8 4 cell16)
    (CoveredF2.join _ _ _ (CoveredF2.cell (127/160) (4/5) 128 8 8 4 cell17)
    (CoveredF2.join _ _ _ (CoveredF2.cell (4/5) (129/160) 128 8 8 4 cell18)
    (CoveredF2.join _ _ _ (CoveredF2.cell (129/160) (13/16) 128 8 8 4 cell19)
    (CoveredF2.join _ _ _ (CoveredF2.cell (13/16) (131/160) 128 8 8 4 cell20)
    (CoveredF2.join _ _ _ (CoveredF2.cell (131/160) (33/40) 128 8 8 4 cell21)
    (CoveredF2.join _ _ _ (CoveredF2.cell (33/40) (133/160) 128 8 8 4 cell22)
    (CoveredF2.join _ _ _ (CoveredF2.cell (133/160) (67/80) 128 8 8 4 cell23)
    (CoveredF2.join _ _ _ (CoveredF2.cell (67/80) (27/32) 128 8 8 4 cell24)
    (CoveredF2.join _ _ _ (CoveredF2.cell (27/32) (17/20) 128 8 8 4 cell25)
    (CoveredF2.join _ _ _ (CoveredF2.cell (17/20) (137/160) 128 12 12 6 cell26)
    (CoveredF2.join _ _ _ (CoveredF2.cell (137/160) (69/80) 128 12 12 6 cell27)
    (CoveredF2.join _ _ _ (CoveredF2.cell (69/80) (139/160) 128 12 12 6 cell28)
    (CoveredF2.join _ _ _ (CoveredF2.cell (139/160) (7/8) 128 12 12 6 cell29)
    (CoveredF2.join _ _ _ (CoveredF2.cell (7/8) (141/160) 128 12 12 6 cell30)
    (CoveredF2.join _ _ _ (CoveredF2.cell (141/160) (71/80) 128 12 12 6 cell31)
    (CoveredF2.join _ _ _ (CoveredF2.cell (71/80) (143/160) 128 12 12 6 cell32)
    ((CoveredF2.cell (143/160) (9/10) 128 12 12 6 cell33))))))))))))))))))))))))))))))))))

/-- **Family 2 (`ε = 1/4`, `S = 4`, `λ = 200`) is Mercier stable on every flux surface
`ψ = k²/2`, `7/10 ≤ k ≤ 9/10`**, for both signs `s_G = ±1`, every `μ₀ > 0` and every `p_a`
(general Mercier index, Landreman–Jorge 2020, eq. (3.1), supplied; `D_Merc > 0`; local interchange
only). Caveat: the flux labels and area element in `family2Data` are not derived from the field in
Lean (see the module docstring). -/
theorem family2_mercier_stable {μ₀ : ℝ} (hμ : 0 < μ₀) (pa : ℝ) {sG : ℝ} (hsG : sG = 1 ∨ sG = -1)
    {k : ℝ} (hk : k ∈ Set.Icc (7 / 10 : ℝ) (9 / 10)) :
    MercierStable (family2Data μ₀ pa 200 sG k) := by
  unfold MercierStable
  rw [mercierIndex_family2_eq (by norm_num) hμ.ne' pa sG (by linarith [hk.1])
    (by linarith [hk.2])]
  obtain ⟨h1, h2⟩ := family2_cover.sound k (by push_cast; linarith [hk.1])
    (by push_cast; linarith [hk.2])
  have hpi : 0 < (2 * Real.pi) ^ 6 := by positivity
  rcases hsG with rfl | rfl
  · exact div_pos h1 hpi
  · exact div_pos h2 hpi

/-- **The certified equilibrium** (`ε = 1/4`, `S = 4`, `λ = 200`, `μ₀ > 0`, pressure
`p = (81/200 - ψ)/(λ² μ₀)`): force balance `J × B = ∇p` holds on the smooth region, the
pressure is positive inside the plasma `ψ < 81/200` and vanishes on its boundary, and field
lines starting in the confinement region with `ψ ≤ 81/200` stay there on their flux surface
for all time. -/
theorem family2_lam200_equilibrium {μ₀ : ℝ} (hμ : 0 < μ₀) :
    (∀ x ∈ U (1 / 4), PlasmaLean.ForceBalance
      (WithLp.ofLp (field (1 / 4) 4 200 x)) (WithLp.ofLp (current μ₀ (1 / 4) 4 200 x))
      (WithLp.ofLp (pressureGrad μ₀ (1 / 4) 4 200 x))) ∧
    (∀ x, psi (1 / 4) 4 200 x < 81 / 200 →
      0 < pressure μ₀ ((81 / 200) / 200 ^ 2) (1 / 4) 4 200 x) ∧
    (∀ x, psi (1 / 4) 4 200 x = 81 / 200 →
      pressure μ₀ ((81 / 200) / 200 ^ 2) (1 / 4) 4 200 x = 0) := by
  refine ⟨fun x hx => force_balance (by norm_num : (200 : ℝ) ≠ 0) μ₀ hx, fun x hx =>
    pressure_pos hμ (by norm_num : (200 : ℝ) ≠ 0) hx, fun x hx => pressure_boundary hx⟩

set_option maxRecDepth 100000 in
/-- Rejected fixture (non-vacuity of the checker): a near-axis cell `k ∈ [1/10, 11/100]`,
where the surfaces are Mercier unstable (hill-dominated), is not accepted. -/
theorem cellCheck_rejects_axis : cellCheck 200 128 8 8 4 (1 / 10) (11 / 100) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Rejected fixture: at the paper-scale `λ = 15` (on-axis `β ≈ 5%`) an outer cell
`k ∈ [0.85, 0.86]` is not accepted (numerically those surfaces are Mercier unstable). -/
theorem cellCheck_rejects_lam15 : cellCheck 15 128 8 8 4 (85 / 100) (86 / 100) = false := by
  decide +kernel

end PlasmaLean.Design.LandremanFamily2Cert
