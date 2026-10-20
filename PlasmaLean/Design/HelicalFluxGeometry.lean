/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.HelicalEquilibrium
public import PlasmaLean.Theory.Transport.FluxGeometry
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Flux-surface geometry of the exact helical equilibrium, for radial transport

Equilibrium: `HelicalEquilibrium` with ellipticity `a = 1/4` (so `b = 2a/3 = 1/6`),
`ψ̂ = r² + (1/4 + r²/6) P`, `P = r² cos 2(θ − z)`, in dimensionless coordinates `x = X/L`.
The plasma is the axis component of `{ψ̂ ≤ ψ_b}`, `ψ_b = p₀/4 = 2/25` (where `p ≥ 0` for the
reactor choice `p₀ = 8/25` of `HelicalReactorScale`); it lies in `r² < 1/8`
(`HelicalReactorScale.inner_shell_bound`: `ψ̂ ≥ 35/384 > ψ_b` on `r² = 1/8`). The transport
label is `s = ψ̂/ψ_b ∈ [0,1]` and its flux surfaces are `surf s = {r² ≤ 1/8, ψ̂ = s ψ_b}`.
Physical scale (`pitchLength`): `L = 8 m` (helical period `πL ≈ 25 m`; a periodic straight
device of length `ℓ = 2πL = 16π m`, two helical periods, `periodLength`). With `B_u = 5/4 T`
the axial field on the axis is 5 T (`HelicalReactorScale.reactor_axis_field` is scale-free in
`L`); `scaled_force_balance` holds for every `L`.

## Exact pointwise facts (proved)

* `lapPsi`: the Laplacian of `ψ̂` (trace of the actual derivatives `dG0, dG1, dG2` of the
  gradient components, see `HelicalFamily.hasFDerivAt_G0` …) equals
  `4 + 4P(1/4 − r²/6)` (`lapPsi_eq`).
* On `surf s`: `r² ≤ (48/35) s ψ_b` (`r2_le_of_mem_surf`), `4·0.97 ≤ Δψ̂ ≤ 4·1.03`
  (`lapPsi_bounds`), and the log-Jacobian derivative `κ_V` satisfies `|κ_V| ≤ 3/50` for
  `s > 0` (`kappaV_bound`).
* Disk containments: `r² ≤ (48/61) s ψ_b ⇒ ψ̂ ≤ s ψ_b` (`eqPsi_le_of_r2_le`).
* `surf s` is nonempty (`diagPoint_mem_surf`).

## The supplied link (`IsHelicalGeometry`)

In the coordinates `(s, u = θ − z, z)`, a cross-section of `surf s` is the curve
`r²(s,u) (1 + (1/4 + r²/6) cos 2u) = s ψ_b`, with Jacobian `J = (L²/2) ∂ₛ r²` and
`∂ₛ r² = ψ_b / (1 + k₁ cos 2u)`, `k₁ = 1/4 + r²/3`. Hence (exact calculus, not formalized):
* `V'(s) = ℓ ∫ J du`, and the flux-surface average is `⟨f⟩ = ∫ f J du / ∫ J du`;
* `V''/V' = ⟨∂ₛ log J⟩` with `∂ₛ log J = −(ψ_b/3) cos 2u / (1 + k₁ cos 2u)² = κ_V`;
* `⟨Δs⟩ = ⟨Δψ̂⟩ / (L² ψ_b)` and `(V'⟨|∇s|²⟩)' = V'⟨Δs⟩` (Gauss);
* at the axis the curve is the ellipse limit and `V'(0) = πψ_bL²ℓ/√(1 − a²)`, `a = 1/4`.
The class `IsHelicalGeometry G` records exactly these facts as hypotheses on a
`FluxGeometry`: the Gauss laws, `⟨Δs⟩` and `V''/V'` are *mean values* (`IsMeanValue`) of the
pointwise functions over `surf s`, and the axis value of `V'`. Every average against a
probability measure on `surf s` is a mean value (`isMeanValue_integral`,
`isMeanValue_ratio_integral`), so the true helical coefficients belong to the class; this
membership (coarea formula and the parametrization) is the **supplied, unformalized** step.

## Consequences (proved)

`h_bounds`, `dlogV_bounds`, and from the Gauss identity the tight enclosures
`0.97 A s (1 − s/25) ≤ ⟨|∇s|²⟩ ≤ 1.03 A s (1 + s/25)` with `A = 4/(L²ψ_b) = 25/32 m⁻²`
(`g_bounds`) and `V'(0)(1 − s/15) ≤ V'(s) ≤ V'(0)(1 + s/15)` (`Vp_bounds`). Pointwise,
`|∇s|²` varies by a factor ≈ 1.7 around a surface; the Gauss identity is what makes the
average sharp. Non-vacuity: `witnessGeometry` is a member of the class.
-/

public section

noncomputable section

namespace PlasmaLean.Design.HelicalFluxGeometry

open PlasmaLean.Fields PlasmaLean.Design.HelicalFamily PlasmaLean.Design.HelicalEquilibrium
  PlasmaLean.Transport Set WithLp

/-! ### Constants -/

/-- Boundary flux `ψ_b = p₀/4 = 2/25` of the pressure-positive plasma (reactor `p₀ = 8/25`). -/
@[expose] def psiB : ℝ := 2 / 25

/-- Pitch length `L = 8 m` (physical coordinates `X = L x`). -/
@[expose] def pitchLength : ℝ := 8

/-- Length `ℓ = 2πL = 16π m` of the periodic straight device (two helical periods `πL`). -/
@[expose] def periodLength : ℝ := 16 * Real.pi

/-- Geometric scale `A = 4/(L²ψ_b)` (m⁻²): `⟨|∇s|²⟩ ≈ A s` and `⟨Δs⟩ ≈ A`. -/
@[expose] def geomA : ℝ := 4 / (pitchLength ^ 2 * psiB)

/-- `A = 25/32 m⁻²`. -/
theorem geomA_eq : geomA = 25 / 32 := by norm_num [geomA, pitchLength, psiB]

/-- Axis value of the volume derivative, `V'(0) = π ψ_b L² ℓ / √(1 − 1/16) = 4πψ_bL²ℓ/√15`
(m³ per unit `s`; ≈ 835 m³). -/
@[expose] def Vaxis : ℝ := 4 * Real.pi * psiB * pitchLength ^ 2 * periodLength / Real.sqrt 15

/-- `V'(0) > 0`. -/
theorem Vaxis_pos : 0 < Vaxis := by
  unfold Vaxis psiB pitchLength periodLength
  have := Real.pi_pos
  have : 0 < Real.sqrt 15 := Real.sqrt_pos.2 (by norm_num)
  positivity

/-! ### Flux surfaces and pointwise functions -/

/-- The flux surface `s` of the plasma: `{x : r² ≤ 1/8, ψ̂(x) = s ψ_b}` (dimensionless `x`). -/
@[expose] def surf (s : ℝ) : Set Space := {x | r2 x ≤ 1 / 8 ∧ eqPsi (1 / 4) x = s * psiB}

/-- The Laplacian of `ψ̂`: `∂₀G₀ + ∂₁G₁ + ∂₂G₂`, using the actual derivatives `dGᵢ` of the
gradient components `Gᵢ` (`HelicalFamily.hasFDerivAt_G0`, …; `gPsi` is the actual gradient of
`ψ̂` by `HelicalFamily.psi_hasFDerivAt`). -/
@[expose] def lapPsi (x : Space) : ℝ :=
  dG0 (1 / 4) (1 / 6) x (basis 0) + dG1 (1 / 4) (1 / 6) x (basis 1) +
    dG2 (1 / 4) (1 / 6) x (basis 2)

/-- `Δs = Δψ̂ / (L² ψ_b)` in physical units (m⁻²). -/
@[expose] def lapS (x : Space) : ℝ := lapPsi x / (pitchLength ^ 2 * psiB)

/-- The log-Jacobian derivative `κ_V = ∂ₛ log J = −(2bψ_b) c / (1 + k₁ c)²`, `b = 1/6`,
`c = P/r² = cos 2(θ − z)`, `k₁ = 1/4 + r²/3`. Its flux-surface average is `V''/V'`. -/
@[expose] def kappaV (x : Space) : ℝ :=
  -(2 * (1 / 6) * psiB) * (P x / r2 x) / (1 + (1 / 4 + 2 * (1 / 6) * r2 x) * (P x / r2 x)) ^ 2

/-- The equilibrium flux function in the `(r², P)` form: `ψ̂ = r² + (1/4 + r²/6) P`. -/
theorem eqPsi_eq (x : Space) : eqPsi (1 / 4) x = r2 x + (1 / 4 + 1 / 6 * r2 x) * P x := by
  simp only [eqPsi, psi, amp]; norm_num

/-- **Exact Laplacian**: `Δψ̂ = 4 + 4 P (1/4 − r²/6)`. -/
theorem lapPsi_eq (x : Space) : lapPsi x = 4 + 4 * P x * (1 / 4 - 1 / 6 * r2 x) := by
  simp only [lapPsi, dG0, dG1, dG2, dP, dP0, dP1, dQ, dA, dR, dC, dS, basis,
    add_apply, smul_apply, sub_apply, PiLp.proj_apply, smul_eq_mul, Fin.isValue,
    PiLp.single_eq_same, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true,
    PiLp.single_eq_of_ne, Fin.reduceEq, mul_one, mul_zero, add_zero, zero_add, sub_zero]
  simp only [P, P0, P1, amp, r2, C, S]
  ring

/-! ### Pointwise bounds on the flux surfaces -/

/-- `r² ≥ 0`. -/
theorem r2_nonneg (x : Space) : 0 ≤ r2 x := by unfold r2; positivity

/-- **Size of the surfaces**: on `surf s` (`s ≥ 0`), `(35/48) r² ≤ s ψ_b`, i.e.
`r² ≤ (48/35) s ψ_b` (`≤ 96/875 ≈ 0.11` for `s ≤ 1`). -/
theorem r2_le_of_mem_surf {s : ℝ} {x : Space} (hx : x ∈ surf s) : 35 / 48 * r2 x ≤ s * psiB := by
  obtain ⟨h8, hψ⟩ := hx
  rw [← hψ, eqPsi_eq]
  have hP := abs_P_le x
  have h0 := r2_nonneg x
  have hl := neg_abs_le (P x)
  nlinarith [mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℝ) ≤ 1 / 4 + 1 / 6 * r2 x),
    mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 1 / 8 - r2 x)]

/-- On `surf s` with `s ≤ 1`: `r² ≤ 96/875`. -/
theorem r2_le_of_mem_surf' {s : ℝ} (hs : s ≤ 1) {x : Space} (hx : x ∈ surf s) :
    r2 x ≤ 96 / 875 := by
  have := r2_le_of_mem_surf hx
  have hp : s * psiB ≤ 2 / 25 := by unfold psiB; nlinarith
  linarith

/-- **Disk containment**: inside the disk `r² ≤ (48/61) s ψ_b` (with `r² ≤ 1/8`) the flux is
at most `s ψ_b`, so the region `{ψ̂ ≤ s ψ_b}` contains that disk. -/
theorem eqPsi_le_of_r2_le {s : ℝ} {x : Space} (h8 : r2 x ≤ 1 / 8)
    (hr : 61 / 48 * r2 x ≤ s * psiB) : eqPsi (1 / 4) x ≤ s * psiB := by
  rw [eqPsi_eq]
  have hP := abs_P_le x
  have h0 := r2_nonneg x
  have hu := le_abs_self (P x)
  nlinarith [mul_le_mul_of_nonneg_left hu (by positivity : (0 : ℝ) ≤ 1 / 4 + 1 / 6 * r2 x),
    mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 1 / 8 - r2 x)]

/-- **Laplacian bounds**: for `r² ≤ 96/875`, `4·(97/100) ≤ Δψ̂ ≤ 4·(103/100)`. -/
theorem lapPsi_bounds {x : Space} (hr : r2 x ≤ 96 / 875) :
    4 * (97 / 100) ≤ lapPsi x ∧ lapPsi x ≤ 4 * (103 / 100) := by
  rw [lapPsi_eq]
  have hP := abs_le.1 (abs_P_le x)
  have h0 := r2_nonneg x
  have hc0 : 0 ≤ 1 / 4 - 1 / 6 * r2 x := by linarith
  have hc1 : 1 / 4 - 1 / 6 * r2 x ≤ 1 / 4 := by linarith
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hP.1 hc0, mul_le_mul_of_nonneg_left hc1 h0]
  · nlinarith [mul_le_mul_of_nonneg_right hP.2 hc0, mul_le_mul_of_nonneg_left hc1 h0]

/-- **Log-Jacobian bound**: for `0 < r² ≤ 96/875`, `|κ_V| ≤ 3/50`. -/
theorem kappaV_bound {x : Space} (hr0 : 0 < r2 x) (hr : r2 x ≤ 96 / 875) :
    -(3 / 50) ≤ kappaV x ∧ kappaV x ≤ 3 / 50 := by
  set c := P x / r2 x with hc
  have hP := abs_le.1 (abs_P_le x)
  have hc1 : c ≤ 1 := by rw [hc, div_le_one hr0]; exact hP.2
  have hc2 : -1 ≤ c := by rw [hc, le_div_iff₀ hr0]; linarith [hP.1]
  set k := 1 / 4 + 2 * (1 / 6) * r2 x with hk
  have hk0 : 0 ≤ k := by rw [hk]; positivity
  have hk1 : k ≤ 3 / 10 := by rw [hk]; linarith
  have hden : 7 / 10 ≤ 1 + k * c := by nlinarith [mul_le_mul_of_nonneg_left hc2 hk0]
  have hden2 : (49 / 100 : ℝ) ≤ (1 + k * c) ^ 2 := by nlinarith
  have hpos : 0 < (1 + k * c) ^ 2 := by linarith
  unfold kappaV
  rw [← hc, ← hk]
  unfold psiB
  constructor
  · rw [le_div_iff₀ hpos]; nlinarith
  · rw [div_le_iff₀ hpos]; nlinarith

/-! ### A point on every surface -/

/-- The point `(t, t, 0)` with `2t² = s ψ_b`, where `P = 0` (`cos 2(θ − z) = 0`). -/
@[expose] def diagPoint (s : ℝ) : Space :=
  toLp 2 ![Real.sqrt (s * psiB / 2), Real.sqrt (s * psiB / 2), 0]

/-- At `diagPoint s`: `r² = s ψ_b` (for `s ≥ 0`) and `P = 0`. -/
theorem diagPoint_values {s : ℝ} (hs : 0 ≤ s) :
    r2 (diagPoint s) = s * psiB ∧ P (diagPoint s) = 0 := by
  have h : 0 ≤ s * psiB / 2 := by unfold psiB; positivity
  have hsq := Real.sq_sqrt h
  constructor
  · simp only [r2, diagPoint, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hsq]; ring
  · simp [P, C, S, diagPoint]

/-- `diagPoint s ∈ surf s` for `s ∈ [0,1]`: every flux surface is nonempty. -/
theorem diagPoint_mem_surf {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : diagPoint s ∈ surf s := by
  obtain ⟨hr, hP⟩ := diagPoint_values hs.1
  refine ⟨?_, ?_⟩
  · rw [hr]; unfold psiB; nlinarith [hs.2]
  · rw [eqPsi_eq, hr, hP, mul_zero, add_zero]

/-- At `diagPoint s`: `Δψ̂ = 4`. -/
theorem lapPsi_diag {s : ℝ} (hs : 0 ≤ s) : lapPsi (diagPoint s) = 4 := by
  rw [lapPsi_eq, (diagPoint_values hs).2]; ring

/-- At `diagPoint s`: `κ_V = 0`. -/
theorem kappaV_diag {s : ℝ} (hs : 0 ≤ s) : kappaV (diagPoint s) = 0 := by
  simp [kappaV, (diagPoint_values hs).2]

/-! ### The helical flux geometry class -/

/-- **Supplied link between the helical equilibrium and its flux-surface averages.** A flux
geometry `G` of the label `s = ψ̂/ψ_b` is *helical* if it obeys the flux-geometry laws (Gauss
identity), `⟨Δs⟩ = G.h` is a mean value of `Δs` over `surf s`, `V''/V'` is a mean value of the
log-Jacobian derivative `κ_V` over `surf s` (for `0 < s < 1`), and `V'(0) = Vaxis`. The true
coefficients satisfy this by the coarea formula and the `(s, u, z)` parametrization (see the
module documentation); that step is not formalized. -/
class IsHelicalGeometry (G : FluxGeometry) : Prop extends G.Laws where
  /-- `⟨Δs⟩` is a mean value of `Δs` over the surface. -/
  h_mean : ∀ s ∈ Icc (0 : ℝ) 1, IsMeanValue lapS (surf s) (G.h s)
  /-- `V''/V' = ⟨∂ₛ log J⟩` is a mean value of `κ_V` over the surface. -/
  dlogV_mean : ∀ s ∈ Ioo (0 : ℝ) 1, IsMeanValue kappaV (surf s) (G.dVp s / G.Vp s)
  /-- Axis value of the volume derivative (ellipse limit). -/
  Vp_axis : G.Vp 0 = Vaxis

namespace IsHelicalGeometry

variable (G : FluxGeometry) [hG : IsHelicalGeometry G]

/-- `0.97 A ≤ ⟨Δs⟩ ≤ 1.03 A` on `[0,1]`, `A = 25/32 m⁻²`. -/
theorem h_bounds : ∀ s ∈ Icc (0 : ℝ) 1,
    geomA * (97 / 100) ≤ G.h s ∧ G.h s ≤ geomA * (103 / 100) := fun s hs =>
  (hG.h_mean s hs).bounds fun x hx => by
    have hb := lapPsi_bounds (r2_le_of_mem_surf' hs.2 hx)
    have hd : 0 < pitchLength ^ 2 * psiB := by norm_num [pitchLength, psiB]
    unfold lapS geomA
    constructor
    · rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hd]; linarith
    · rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hd]; linarith

/-- `|V''/V'| ≤ 3/50` on `(0,1)`, in the form `−λV' ≤ V'' ≤ λV'`. -/
theorem dlogV_bounds : ∀ s ∈ Ioo (0 : ℝ) 1,
    -(3 / 50) * G.Vp s ≤ G.dVp s ∧ G.dVp s ≤ 3 / 50 * G.Vp s := by
  intro s hs
  have hV := hG.Vp_pos s (Ioo_subset_Icc_self hs)
  have hb := (hG.dlogV_mean s hs).bounds (lo := -(3 / 50)) (hi := 3 / 50) fun x hx => by
    have hr := r2_le_of_mem_surf' hs.2.le hx
    have hr0 : 0 < r2 x := by
      have hψ := hx.2
      rw [eqPsi_eq] at hψ
      have hP := abs_P_le x
      have h0 := r2_nonneg x
      have hspos : 0 < s * psiB := by unfold psiB; nlinarith [hs.1]
      by_contra hcon
      have hz : r2 x = 0 := le_antisymm (not_lt.1 hcon) h0
      have : P x = 0 := abs_nonpos_iff.1 (hz ▸ hP)
      rw [hz, this] at hψ
      linarith
    exact kappaV_bound hr0 hr
  rw [le_div_iff₀ hV, div_le_iff₀ hV] at hb
  exact ⟨by linarith [hb.1], by linarith [hb.2]⟩

/-- **Tight enclosure of `⟨|∇s|²⟩`** from the Gauss identity:
`0.97 A s (1 − s/25) ≤ ⟨|∇s|²⟩ ≤ 1.03 A s (1 + s/25)`. -/
theorem g_bounds : ∀ s ∈ Icc (0 : ℝ) 1,
    geomA * (97 / 100) * s * (1 - 1 / 25 * s) ≤ G.g s ∧
      G.g s ≤ geomA * (103 / 100) * s * (1 + 1 / 25 * s) := by
  have hA : 0 ≤ geomA := by rw [geomA_eq]; norm_num
  intro s hs
  exact ⟨G.le_g (lam := 3 / 50) (by positivity) (by norm_num) (by norm_num) (by norm_num)
      (fun s hs => (h_bounds G s hs).1) (fun s hs => (dlogV_bounds G s hs).2) s hs,
    G.g_le (lam := 3 / 50) (by positivity) (by norm_num) (by norm_num)
      (fun s hs => (h_bounds G s hs).2) (fun s hs => (dlogV_bounds G s hs).1) s hs⟩

/-- `⟨|∇s|²⟩ ≥ 0` on `[0,1]`. -/
theorem g_nonneg : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ G.g s := fun s hs => by
  have := (g_bounds G s hs).1
  have hA : 0 ≤ geomA := by rw [geomA_eq]; norm_num
  have : 0 ≤ 1 - 1 / 25 * s := by linarith [hs.2]
  have := mul_nonneg (mul_nonneg (mul_nonneg hA (by norm_num : (0 : ℝ) ≤ 97 / 100)) hs.1) this
  linarith

/-- **Volume derivative enclosure**: `V'(0)(1 − s/15) ≤ V'(s) ≤ V'(0)(1 + s/15)`. -/
theorem Vp_bounds : ∀ s ∈ Icc (0 : ℝ) 1,
    Vaxis * (1 - 1 / 15 * s) ≤ G.Vp s ∧ G.Vp s ≤ Vaxis * (1 + 1 / 15 * s) := by
  intro s hs
  rw [← hG.Vp_axis]
  exact ⟨G.le_Vp (lam := 3 / 50) (by norm_num) (by norm_num)
      (fun s hs => (dlogV_bounds G s hs).1) s hs,
    G.Vp_le (lam := 3 / 50) (by norm_num) (by norm_num)
      (fun s hs => (dlogV_bounds G s hs).2) s hs⟩

end IsHelicalGeometry

/-! ### Non-vacuity -/

/-- A witness geometry: `V' ≡ V'(0)`, `⟨|∇s|²⟩ = A s`, `⟨Δs⟩ = A` (the values at the points
`diagPoint s`, where `cos 2(θ − z) = 0`). It only shows that the class is non-empty: these are
**not** the true helical averages (e.g. the true `⟨κ_V⟩ = V''/V'` is nonzero). -/
@[expose] def witnessGeometry : FluxGeometry :=
  ⟨fun _ => Vaxis, fun _ => 0, fun s => geomA * s, fun _ => geomA, fun _ => geomA⟩

/-- **Non-vacuity of `IsHelicalGeometry`.** -/
instance : IsHelicalGeometry witnessGeometry where
  Vp_pos := fun _ _ => Vaxis_pos
  Vp_deriv := fun _ _ => hasDerivWithinAt_const _ _ _
  g_deriv := fun s _ => by
    simpa [witnessGeometry] using ((hasDerivAt_id s).const_mul geomA).hasDerivWithinAt
  g_zero := by simp [witnessGeometry]
  gauss := fun _ _ => by simp [witnessGeometry]
  h_mean := fun s hs => by
    have h := IsMeanValue.of_mem (g := lapS) (diagPoint_mem_surf hs)
    have hv : lapS (diagPoint s) = geomA := by
      rw [lapS, lapPsi_diag hs.1, geomA]
    rwa [hv] at h
  dlogV_mean := fun s hs => by
    have h := IsMeanValue.of_mem (g := kappaV) (diagPoint_mem_surf (Ioo_subset_Icc_self hs))
    rw [kappaV_diag hs.1.le] at h
    simpa [witnessGeometry] using h
  Vp_axis := rfl

end PlasmaLean.Design.HelicalFluxGeometry
