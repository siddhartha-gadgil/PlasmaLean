/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.QuasilinearBarrier
public import PlasmaLean.Design.SolovevOnePlasma

/-!
# A quasilinear two-sided transport band on the Solov'ev geometry, and `solovev_one_plasma`

Labels: *supplied geometry enclosures* (`IsSolovevGeometry`), *synthetic reactor-scale data*,
Bosch–Hale reactivity as *supplied data*, quasilinear transport law *supplied* (rational
stand-in `χ₀ (1/10 + T²/100)`; it is stiffer than the gyro-Bohm-like `χ₀ (1/10 + (T/10)^{3/2})`
of the note above `10 keV`, and only this stand-in is certified).

## Model

* **Geometry.** `IsSolovevGeometry G`: a `FluxGeometry` of the transport label `s = ψ̃/ψ̃_b`
  (`SolovevOnePlasma.label`) with its laws (Gauss identity), the enclosures
  `0.49 s ≤ ⟨|∇s|²⟩ ≤ 0.525 s`, `0.49 ≤ ⟨Δs⟩ ≤ 0.525` and continuity of `⟨Δs⟩` on `[0,1]`.
  **Supplied, not proved:** the coarea/divergence link to the explicit Solov'ev surfaces and
  the enclosures, which come from the adaptive-quadrature table of
  `notes/theory/transport-mhd-coupling.md` §3.1 (`g/s ∈ [0.4953, 0.5236]`,
  `h ∈ [0.4914, 0.5236]`, widened). Non-vacuity: `modelGeometry` (a cylinder-like geometry with
  `g = s/2`, `h = 1/2`) is an instance — it shows consistency, not that the Solov'ev field
  satisfies the class.
* **Density** `n(s) = 0.9·10²⁰ (1 − 4s/5)/(1 − 3s/10)` m⁻³ (`dens`, relative to `10²⁰`):
  decreasing, `n(1) = 2.6·10¹⁹`. (The note's `(1 − 11s/12)/(1 − 0.7s)` vanishes just outside
  the domain, at `s = 12/11`; its logarithmic derivative then has a pole at distance `1/11`,
  which defeated polynomial barrier certificates. The zero of this profile is at `s = 5/4`.)
  The energy equation divided by the local heat capacity is the kernel equation on the
  **weighted geometry** `G.weight n n'` (`FluxGeometry.weight_laws`).
* **Source** `R(s,T) = (n/10²⁰)(α ⟨σv⟩(T) − b √T) + q_aux(s)` keV/s (`solSource`), with the M2
  rates `α = alphaRate`, `b = bremsRate` (`f_fuel = 0.86`, `Z_eff = 1.7`, from the kernel 0-D
  formulas at `n = 10²⁰`, both scale like `n² / n`), and auxiliary heating rate
  `q_aux = 14 (1 − s)⁶` keV/s (`auxSol`), i.e. `p_aux = (3/2) n (1+r_i) keV · q_aux`, about
  `120 MW` with `V' ≈ 1600–1680 m³` (oracle).
* **Transport** `χ = χ₀ χ̂(T)`, `χ₀ ∈ [8/5, 33/20]` m²/s (`solCoeffs`, built with
  `FluxGeometry.qcoeffs`, degenerate axis). Kirchhoff form (`solCoeffs_op_kProf`):
  `N[Φ⁻¹ ∘ F] = χ₀ (g F'' + h_w F') + R`, `h_w = h + (n'/n) g`.

## Certificates

Multiplying by `P(s) = (1 − 4s/5)(1 − 3s/10) ∈ (0,1]` makes everything polynomial. The
operator is bilinear in `(χ₀, γ)` with `g = γ s`, so the four corners
`χ₀ ∈ {8/5, 33/20}`, `γ ∈ {0.49, 0.525}` suffice (`bilin_lower`, `bilin_upper`); `h` enters with
the known sign of `F' ≤ 0`. Each barrier: four label-dependent piece checks (`pieceCheckL`,
34 resp. 17 pieces); pressure: one check on 66 pieces with `T_sup ≤ K` labels in `1/8 keV`.

## Results

* `solovev_band`: every kernel solution on all horizons with edge temperature in `[1, 3/2]`
  keV and initial data in the band stays in `[T_sub, T_sup]` for all `t ≥ 0`; `T ≥ 10 keV` on
  `s ≤ 3/10`; `T ≤ 18 keV`. Profiles (oracle): `T_sub(0) ≈ 13.4`, `T_sub(3/10) ≈ 10.8`;
  `T_sup(0) ≈ 17.8`, `T_sup(3/10) ≈ 15.3` keV.
* `tsup_pressure`: `n(s)(1 + 53/60) T_sup(s) keV ≤ p_eq(s) + 40 kPa` on `[0,1]`.
* `solovev_one_plasma` (rung C2): one field `B` (reactor Solov'ev), pressure `p_eq + Δ`,
  `Δ = 40 kPa`, kernel `ForceBalance` on the transport domain; 3.5 MeV alphas born at
  `s ≤ 3/11` stay in `s ≤ 1` for all time; the transport band, hot core and plasma pressure
  `≤ p_eq + Δ` on the whole transport domain for all `t ≥ 0`.

## What the parameter search found (Python oracle, untrusted; `/tmp/k3`)

The note's C2 set (20 MW, ignited, `Q ≈ 30–47`) does **not** certify: the Bosch–Hale windows
are 1 keV wide, so a certified alpha floor/ceiling is uncertain by ≈ 10 % at 15 keV, and the
lower barrier (`T ≥ 10 keV` at `s = 3/10`) and the pressure ceiling `n c T_sup keV ≤ p_eq + Δ`
cannot both hold near ignition. More auxiliary heating makes the band narrower. The set used
here is driven: `P_aux ≈ 122 MW`, `P_α ≈ 131–136 MW`, `Q ≈ 5.5`, steady states `T(0) ≈ 15.3–15.5
keV` and `max p/(p_eq + Δ) ≈ 0.85` (nominal geometry). `Q ≈ 5.5` is within the fixed-`χ`
two-sided bound (`Q ≲ 6`), so this certified set does **not** demonstrate the lifting of that
obstruction on the Solov'ev geometry (the cylinder module `QuasilinearBarrier` does, at
`Q ≈ 9.5–17`); the ignited C2 band would need finer reactivity windows.

## Honest limitations

* The coarea link and the geometry enclosures are supplied (`IsSolovevGeometry`).
* `χ` is a prescribed rational stand-in; density, composition and auxiliary deposition are
  prescribed; solutions are supplied (no existence theorem).
* The offset `Δ = 40 kPa` is an edge pedestal: a sharp boundary needs a current sheet outside
  the kernel's pointwise `ForceBalance`; the layer `ψ̃_b < ψ̃ < ψ̃_e` and the exterior are not
  modelled.
* Axisymmetric tokamak-like equilibrium, static fields, not a stellarator; no MHD stability.
-/

public section

noncomputable section

namespace PlasmaLean.Design.SolovevBand

open Set Filter Topology PlasmaLean.Transport PlasmaLean.Fusion PlasmaLean.Certificates
  PlasmaLean.Design.TransportBarrier PlasmaLean.Design.QuasilinearBarrier
  PlasmaLean.Design.SolovevOnePlasma PlasmaLean.Fields PlasmaLean.Kinetic
  PlasmaLean.Design.Solovev PlasmaLean.Design.SolovevAlpha WithLp

/-! ### Geometry -/

/-- **Supplied Solov'ev transport geometry** (coarea link and enclosures supplied, see the
module documentation): flux-geometry laws, `0.49 s ≤ ⟨|∇s|²⟩ ≤ 0.525 s`,
`0.49 ≤ ⟨Δs⟩ ≤ 0.525` and `⟨Δs⟩` continuous on `[0,1]`. -/
class IsSolovevGeometry (G : FluxGeometry) : Prop extends G.Laws where
  /-- Lower enclosure of `⟨|∇s|²⟩`. -/
  g_lower : ∀ s ∈ Icc (0 : ℝ) 1, 49 / 100 * s ≤ G.g s
  /-- Upper enclosure of `⟨|∇s|²⟩`. -/
  g_upper : ∀ s ∈ Icc (0 : ℝ) 1, G.g s ≤ 21 / 40 * s
  /-- Lower enclosure of `⟨Δs⟩`. -/
  h_lower : ∀ s ∈ Icc (0 : ℝ) 1, 49 / 100 ≤ G.h s
  /-- Upper enclosure of `⟨Δs⟩`. -/
  h_upper : ∀ s ∈ Icc (0 : ℝ) 1, G.h s ≤ 21 / 40
  /-- `⟨Δs⟩` is continuous on `[0,1]` (analytic for the Solov'ev surfaces). -/
  h_cont : ContinuousOn G.h (Icc 0 1)

/-- A cylinder-like model geometry: `V' = 1600`, `g = s/2`, `h = 1/2`. -/
@[expose] def modelGeometry : FluxGeometry :=
  ⟨fun _ => 1600, fun _ => 0, fun s => s / 2, fun _ => 1 / 2, fun _ => 1 / 2⟩

/-- **Non-vacuity of the class**: the model geometry satisfies it (consistency only; not the
Solov'ev field). -/
instance : IsSolovevGeometry modelGeometry where
  Vp_pos := fun _ _ => by norm_num [modelGeometry]
  Vp_deriv := fun _ _ => hasDerivWithinAt_const _ _ _
  g_deriv := fun s _ => by
    have := (hasDerivAt_id s).div_const (2 : ℝ)
    simpa [modelGeometry] using this.hasDerivWithinAt
  g_zero := by simp [modelGeometry]
  gauss := fun _ _ => by simp [modelGeometry]
  g_lower := fun s hs => by simp only [modelGeometry]; linarith [hs.1]
  g_upper := fun s hs => by simp only [modelGeometry]; linarith [hs.1]
  h_lower := fun _ _ => by norm_num [modelGeometry]
  h_upper := fun _ _ => by norm_num [modelGeometry]
  h_cont := continuousOn_const

/-- `⟨|∇s|²⟩ ≥ 0`. -/
theorem IsSolovevGeometry.g_nonneg (G : FluxGeometry) [hG : IsSolovevGeometry G] :
    ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ G.g s := fun s hs => by
  have := hG.g_lower s hs; nlinarith [hs.1]

/-! ### Density, source and coefficients -/

/-- The weight `P(s) = (1 − 4s/5)(1 − 3s/10)`. -/
@[expose] def Pw (s : ℝ) : ℝ := (1 - 4 / 5 * s) * (1 - 3 / 10 * s)

/-- Density relative to `10²⁰ m⁻³`: `n(s)/10²⁰ = 0.9 (1 − 4s/5)/(1 − 3s/10)`. -/
@[expose] def dens (s : ℝ) : ℝ := 9 / 10 * (1 - 4 / 5 * s) / (1 - 3 / 10 * s)

/-- `n'(s)/10²⁰ = −0.45/(1 − 3s/10)²`. -/
@[expose] def ddens (s : ℝ) : ℝ := -(9 / 20) / (1 - 3 / 10 * s) ^ 2

/-- `0 < P ≤ 1` on `[0,1]`. -/
theorem Pw_bounds {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : 0 < Pw s ∧ Pw s ≤ 1 := by
  obtain ⟨h0, h1⟩ := hs
  unfold Pw; constructor <;> nlinarith

/-- `1 − 3s/10 > 0` on `[0,1]`. -/
theorem w2_pos {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : 0 < 1 - 3 / 10 * s := by linarith [hs.2]

/-- The density is positive on `[0,1]`. -/
theorem dens_pos {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : 0 < dens s := by
  have := w2_pos hs; unfold dens
  exact div_pos (by nlinarith [hs.2]) this

/-- `ddens` is the derivative of `dens` on `[0,1]`. -/
theorem hasDerivAt_dens {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : HasDerivAt dens (ddens s) s := by
  have hw := (w2_pos hs).ne'
  have h1 : HasDerivAt (fun x : ℝ => 9 / 10 * (1 - 4 / 5 * x)) (9 / 10 * (-(4 / 5))) s := by
    simpa using (((hasDerivAt_id s).const_mul (4 / 5 : ℝ)).const_sub 1).const_mul (9 / 10 : ℝ)
  have h2 : HasDerivAt (fun x : ℝ => 1 - 3 / 10 * x) (-(3 / 10)) s := by
    simpa using ((hasDerivAt_id s).const_mul (3 / 10 : ℝ)).const_sub 1
  have := h1.div h2 hw
  rw [show dens = fun x : ℝ => 9 / 10 * (1 - 4 / 5 * x) / (1 - 3 / 10 * x) from rfl]
  convert this using 1
  have h10 : (10 : ℝ) - s * 3 ≠ 0 := by intro h; linarith [hs.2]
  unfold ddens; field_simp; ring

/-- `P · n'/n = −1/2` on `[0,1]`. -/
theorem Pw_dlog {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : Pw s * (ddens s / dens s) = -(1 / 2) := by
  have hw := (w2_pos hs).ne'
  have hw1 : (1 - 4 / 5 * s) ≠ 0 := by intro h; linarith [hs.2]
  have e : ddens s / dens s = -(1 / 2) / ((1 - 4 / 5 * s) * (1 - 3 / 10 * s)) := by
    unfold ddens dens
    rw [div_div_eq_mul_div, div_mul_eq_mul_div, div_div, div_eq_div_iff (by positivity)
      (mul_ne_zero hw1 hw)]
    ring
  rw [e, Pw, mul_div_assoc', mul_comm, mul_div_assoc, div_self (mul_ne_zero hw1 hw), mul_one]

/-- `n'/n = −1/(2P)` on `[0,1]`. -/
theorem dlog_eq {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : ddens s / dens s = -(1 / 2) / Pw s := by
  have h := Pw_dlog hs
  have hP := (Pw_bounds hs).1.ne'
  rw [eq_div_iff hP, mul_comm]; exact h

/-- `P · n/10²⁰ = 0.9 (1 − 4s/5)²` on `[0,1]`. -/
theorem Pw_dens {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Pw s * dens s = 9 / 10 * (1 - 4 / 5 * s) ^ 2 := by
  have hw := (w2_pos hs).ne'
  unfold Pw dens
  rw [mul_div_assoc', div_eq_iff hw]; ring

/-- Auxiliary heating rate `q_aux(s) = 14 (1 − s)⁶` keV/s. -/
@[expose] def auxSol : List ℚ := [14, -84, 210, -280, 210, -84, 14]

/-- Explicit form of `q_aux`. -/
theorem auxSol_eval (s : ℝ) : QPoly.eval auxSol s = 14 * (1 - s) ^ 6 := by
  simp [auxSol]; ring

/-- Net source per unit heat capacity (keV/s):
`R(s,T) = (n/10²⁰)(α ⟨σv⟩(T) − b √T) + q_aux(s)`. -/
@[expose] def solSource (sv : ℝ → ℝ) (s T : ℝ) : ℝ :=
  dens s * (alphaRate * sv T - bremsRate * Real.sqrt T) + QPoly.eval auxSol s

/-- The source is continuous on `[0,1] × (0,∞)`. -/
theorem solSource_continuousOn (sv : ℝ → ℝ) [BoschHaleDT sv] :
    ContinuousOn (fun p : ℝ × ℝ => solSource sv p.1 p.2) (Icc 0 1 ×ˢ Ioi 0) := by
  have hd : ContinuousOn (fun p : ℝ × ℝ => dens p.1) (Icc 0 1 ×ˢ Ioi 0) := by
    unfold dens
    refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun p hp => (w2_pos hp.1).ne')
  have hsv : ContinuousOn (fun p : ℝ × ℝ => sv p.2) (Icc 0 1 ×ˢ Ioi 0) :=
    (BoschHaleDT.continuousOn (sv := sv)).comp continuous_snd.continuousOn (fun p hp => hp.2)
  have hsq : Continuous (fun p : ℝ × ℝ => Real.sqrt p.2) := by fun_prop
  exact (hd.mul ((continuousOn_const.mul hsv).sub (continuous_const.mul hsq).continuousOn)).add
    ((QPoly.continuous_eval _).comp continuous_fst).continuousOn

/-- **Solov'ev band coefficients**: the quasilinear flux-geometry coefficients on the
density-weighted geometry `G.weight n n'` with `χ = χ₀ χ̂(T)`, `∂Tχ = χ₀ T/50`, source
`solSource sv` posed for `T > 0`. -/
@[expose] def solCoeffs (G : FluxGeometry) (sv : ℝ → ℝ) (χ₀ : ℝ) : RadialCoefficients :=
  (G.weight dens ddens).qcoeffs (fun _ T => χ₀ * chiHat T) (fun _ _ => 0)
    (fun _ T => χ₀ * (T / 50)) (solSource sv) (Ioi 0)

/-- The weighted geometry satisfies the flux-geometry laws. -/
theorem weighted_laws (G : FluxGeometry) [hG : IsSolovevGeometry G] :
    (G.weight dens ddens).Laws :=
  G.weight_laws (fun _ hs => dens_pos hs) (fun _ hs => (hasDerivAt_dens hs).hasDerivWithinAt)

/-- **The Solov'ev band coefficients are a kernel instance** (K2 laws) for `χ₀ ≥ 0`. -/
theorem solCoeffs_transportLaws (G : FluxGeometry) [hG : IsSolovevGeometry G] (sv : ℝ → ℝ)
    [BoschHaleDT sv] {χ₀ : ℝ} (hχ : 0 ≤ χ₀) : TransportLaws (solCoeffs G sv χ₀) := by
  have := weighted_laws G
  exact (G.weight dens ddens).qcoeffs_transportLaws
    (fun _ _ T => mul_nonneg hχ (chiHat_pos T).le)
    (fun _ _ _ => hasDerivWithinAt_const _ _ _)
    (fun _ _ T => (hasDerivAt_chiHat T).const_mul χ₀)
    (IsSolovevGeometry.g_nonneg G) isOpen_Ioi (solSource_continuousOn sv)

/-- `χ̂(T) T' = F'` on a Kirchhoff profile. -/
theorem chiHat_mul_kProf' (F : List ℚ) (s : ℝ) :
    chiHat (kProf F s) * kProf' F s = QPoly.eval (QPoly.deriv F) s := by
  have := (chiHat_pos (kProf F s)).ne'
  unfold kProf'; field_simp

/-- `χ̂(T) T'' + χ̂'(T) T'² = F''` on a Kirchhoff profile. -/
theorem chiHat_mul_kProf'' (F : List ℚ) (s : ℝ) :
    chiHat (kProf F s) * kProf'' F s + kProf F s / 50 * kProf' F s ^ 2 =
      QPoly.eval (QPoly.deriv (QPoly.deriv F)) s := by
  have := (chiHat_pos (kProf F s)).ne'
  unfold kProf''; field_simp; ring

/-- **Kirchhoff form of the Solov'ev band operator**:
`N[Φ⁻¹ ∘ F] = χ₀ (g F'' + (h + (n'/n) g) F') + R` on `[0,1]`. -/
theorem solCoeffs_op_kProf (G : FluxGeometry) [hG : IsSolovevGeometry G] (sv : ℝ → ℝ)
    (χ₀ : ℝ) (F : List ℚ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (solCoeffs G sv χ₀).op s (kProf F s) (kProf' F s) (kProf'' F s) =
      χ₀ * (G.g s * QPoly.eval (QPoly.deriv (QPoly.deriv F)) s +
        (G.h s + ddens s / dens s * G.g s) * QPoly.eval (QPoly.deriv F) s) +
        solSource sv s (kProf F s) := by
  have := weighted_laws G
  rw [solCoeffs, FluxGeometry.qcoeffs_op _ _ _ _ _ _ hs, ← chiHat_mul_kProf'' F s,
    ← chiHat_mul_kProf' F s]
  simp only [FluxGeometry.weight]
  ring

/-- **Shift control** along Kirchhoff profiles (the operator is jointly continuous on
`[0,1] × (0,∞)` along the profile, using continuity of `g`, `h`, `n`, `n'`). -/
theorem sol_opShiftControl (G : FluxGeometry) [hG : IsSolovevGeometry G] (sv : ℝ → ℝ)
    [BoschHaleDT sv] (χ₀ : ℝ) (F : List ℚ) (hpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < kProf F s) :
    OpShiftControl (solCoeffs G sv χ₀) (kProf F) (kProf' F) (kProf'' F) := by
  have := weighted_laws G
  refine opShiftControl_of_continuousOn (kProf_continuous F).continuousOn isOpen_Ioi hpos ?_
  have hg : ContinuousOn G.g (Icc 0 1) := fun s hs =>
    (hG.g_deriv s hs).continuousWithinAt
  have hgp : ContinuousOn (fun p : ℝ × ℝ => G.g p.1) (Icc 0 1 ×ˢ Ioi 0) :=
    hg.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hhp : ContinuousOn (fun p : ℝ × ℝ => G.h p.1) (Icc 0 1 ×ˢ Ioi 0) :=
    hG.h_cont.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hPc : Continuous fun p : ℝ × ℝ => Pw p.1 := by unfold Pw; fun_prop
  have hdd : ContinuousOn (fun p : ℝ × ℝ => ddens p.1 / dens p.1) (Icc 0 1 ×ˢ Ioi 0) :=
    (continuousOn_const.div hPc.continuousOn (fun p hp => (Pw_bounds hp.1).1.ne')).congr
      (fun p hp => dlog_eq hp.1)
  have h1 := (kProf'_continuous F).comp (continuous_fst : Continuous (Prod.fst : ℝ × ℝ → ℝ))
  have h2 := (kProf''_continuous F).comp (continuous_fst : Continuous (Prod.fst : ℝ × ℝ → ℝ))
  have hch : Continuous fun p : ℝ × ℝ => chiHat p.2 := by unfold chiHat; fun_prop
  have hA : ContinuousOn (fun p : ℝ × ℝ =>
      χ₀ * chiHat p.2 * G.g p.1 * kProf'' F p.1 +
        (0 * G.g p.1 + χ₀ * chiHat p.2 * (G.h p.1 + ddens p.1 / dens p.1 * G.g p.1) +
          χ₀ * (p.2 / 50) * G.g p.1 * kProf' F p.1) * kProf' F p.1 +
        solSource sv p.1 p.2) (Icc 0 1 ×ˢ Ioi 0) := by
    have hc : Continuous fun p : ℝ × ℝ => χ₀ * chiHat p.2 := continuous_const.mul hch
    have hT : Continuous fun p : ℝ × ℝ => χ₀ * (p.2 / 50) := by fun_prop
    refine ((((hc.continuousOn.mul hgp).mul h2.continuousOn).add
      ((((continuousOn_const.mul hgp).add (hc.continuousOn.mul
        (hhp.add (hdd.mul hgp)))).add ((hT.continuousOn.mul hgp).mul
          h1.continuousOn)).mul h1.continuousOn)).add (solSource_continuousOn sv))
  refine hA.congr (fun p hp => ?_)
  simp only
  rw [solCoeffs, FluxGeometry.qcoeffs_op _ _ _ _ _ _ hp.1]
  simp only [FluxGeometry.weight]

/-! ### Certificate polynomials -/

/-- `1 − 4s/5`. -/
@[expose] def w1 : List ℚ := [1, -4 / 5]
/-- `1 − 3s/10`. -/
@[expose] def w2 : List ℚ := [1, -3 / 10]
/-- `1 − 11s/12` (equilibrium pressure shape). -/
@[expose] def wp : List ℚ := [1, -11 / 12]
/-- `P = (1 − 4s/5)(1 − 3s/10)`. -/
@[expose] def Ppoly : List ℚ := QPoly.mul w1 w2
/-- `P · n'/n = −1/2` written as `−(4/5) w₂ + (3/10) w₁`. -/
@[expose] def Pdl : List ℚ := QPoly.add (QPoly.scale (-4 / 5) w2) (QPoly.scale (3 / 10) w1)
/-- `P · n/10²⁰ = 0.9 w₁²`. -/
@[expose] def Pnu : List ℚ := QPoly.scale (9 / 10) (QPoly.mul w1 w1)

/-- Weighted conduction at a corner: `χ (γ s (P F'' + Pdl F') + h P F')`. -/
@[expose] def condS (F : List ℚ) (χ γ h : ℚ) : List ℚ :=
  QPoly.scale χ (QPoly.add (QPoly.scale γ (QPoly.mul [0, 1]
    (QPoly.add (QPoly.mul Ppoly (QPoly.deriv (QPoly.deriv F))) (QPoly.mul Pdl (QPoly.deriv F)))))
    (QPoly.scale h (QPoly.mul Ppoly (QPoly.deriv F))))

/-- Lower-barrier polynomial at a corner, labels `(k, K)`:
`condS(χ, γ, 0.525) + P q_aux + Pnu · lowBonus k K`. -/
@[expose] def lowS (F : List ℚ) (χ γ : ℚ) (k K : ℚ) : List ℚ :=
  QPoly.add (QPoly.add (condS F χ γ (21 / 40)) (QPoly.mul Ppoly auxSol))
    (QPoly.scale (lowBonus k K) Pnu)

/-- Upper-barrier polynomial at a corner, labels `(k, K)`:
`−(condS(χ, γ, 0.49) + P q_aux + Pnu · 2.291·10²² svCeil K)`. -/
@[expose] def upS (F : List ℚ) (χ γ : ℚ) (_k K : ℚ) : List ℚ :=
  QPoly.scale (-1) (QPoly.add (QPoly.add (condS F χ γ (49 / 100)) (QPoly.mul Ppoly auxSol))
    (QPoly.scale (2291 / 100 * 10 ^ 21 * svCeil K) Pnu))

/-- `keV` in joules as a rational. -/
@[expose] def keVQ : ℚ := 1602176634 / 10 ^ 25

/-- Pressure polynomial for the label `K`:
`(40000 + 456900 (1 − 11s/12))(1 − 3s/10) − 0.9·10²⁰ (113/60) K keV (1 − 4s/5)`. -/
@[expose] def presS (_k K : ℚ) : List ℚ :=
  QPoly.add (QPoly.mul (QPoly.add [40000] (QPoly.scale 456900 wp)) w2)
    (QPoly.scale (-(9 / 10 * 10 ^ 20 * (113 / 60) * K * keVQ)) w1)

/-- Evaluation of the corner conduction. -/
theorem condS_eval (F : List ℚ) (χ γ h : ℚ) (s : ℝ) : QPoly.eval (condS F χ γ h) s =
    χ * (γ * (s * (Pw s * QPoly.eval (QPoly.deriv (QPoly.deriv F)) s -
      1 / 2 * QPoly.eval (QPoly.deriv F) s)) + h * (Pw s * QPoly.eval (QPoly.deriv F) s)) := by
  simp only [condS, QPoly.eval_scale, QPoly.eval_add, QPoly.eval_mul, Ppoly, Pdl, w1, w2,
    QPoly.eval_cons, QPoly.eval_nil, Pw]
  push_cast; ring

/-- Evaluation of `P q_aux`. -/
theorem Paux_eval (s : ℝ) : QPoly.eval (QPoly.mul Ppoly auxSol) s = Pw s * QPoly.eval auxSol s := by
  simp only [QPoly.eval_mul, Ppoly, w1, w2, QPoly.eval_cons, QPoly.eval_nil, Pw]
  push_cast; ring

/-- Evaluation of `Pnu`. -/
theorem Pnu_eval (s : ℝ) : QPoly.eval Pnu s = 9 / 10 * (1 - 4 / 5 * s) ^ 2 := by
  simp [Pnu, w1]; ring

/-- Evaluation of the pressure polynomial. -/
theorem presS_eval (k K : ℚ) (s : ℝ) : QPoly.eval (presS k K) s =
    (40000 + 456900 * (1 - 11 / 12 * s)) * (1 - 3 / 10 * s) -
      9 / 10 * 10 ^ 20 * (113 / 60) * K * (1602176634 / 10 ^ 25) * (1 - 4 / 5 * s) := by
  simp [presS, wp, w1, w2, keVQ]; ring

/-! ### Barrier data (Python oracle, untrusted; checked below) -/

/-- Level function of the lower barrier, `F_sub = Φ(T_sub)`. -/
@[expose] def fsS : List ℚ :=
  [27950239/3000000, -4705503/250000, 1539219/62500, -32527191/1000000, 978513/15625,
   -3195034/15625, 584199857/1000000, -1176425193/1000000, 404295001/250000, -1486436797/1000000,
   435679651/500000, -293357141/1000000, 21422799/500000]

/-- Level function of the upper barrier, `F_sup = Φ(T_sup)`. -/
@[expose] def fuS : List ℚ :=
  [2578977/125000, -29612277/1000000, 26899603/1000000, -37541701/1000000, 83179871/1000000,
   -302953457/1000000, 90584123/100000, -117496877/62500, 2642586349/1000000, -616648869/250000,
   728253351/500000, -97779/200, 35031811/500000]

/-- Pieces of the lower-barrier certificates. -/
@[expose] def subP : List (ℚ × ℚ × ℚ) :=
  [(387/10000, 13, 67/5), (1499/10000, 12, 261/20), (2731/10000, 11, 241/20),
   (809/2000, 10, 221/20), (2679/5000, 9, 201/20), (6561/10000, 8, 181/20),
   (1893/2500, 7, 161/20), (8361/10000, 6, 141/20), (559/625, 5, 121/20), (9359/10000, 4, 101/20),
   (4701/5000, 3, 81/20), (4721/5000, 3, 39/10), (9481/10000, 3, 19/5), (4759/5000, 3, 73/20),
   (9553/10000, 3, 71/20), (9587/10000, 3, 17/5), (9619/10000, 3, 33/10), (193/200, 3, 63/20),
   (9679/10000, 2, 61/20), (9707/10000, 2, 29/10), (4867/5000, 2, 14/5), (122/125, 2, 53/20),
   (1223/1250, 2, 51/20), (613/625, 2, 12/5), (983/1000, 2, 23/10), (2463/2500, 2, 43/20),
   (9873/10000, 1, 41/20), (9893/10000, 1, 19/10), (1239/1250, 1, 9/5), (9931/10000, 1, 33/20),
   (9949/10000, 1, 31/20), (4983/5000, 1, 7/5), (9983/10000, 1, 13/10), (1, 1, 23/20)]

/-- Pieces of the upper-barrier certificates (upper labels end Bosch–Hale windows). -/
@[expose] def supP : List (ℚ × ℚ × ℚ) :=
  [(467/5000, 16, 18), (2141/10000, 15, 17), (3371/10000, 14, 16), (57/125, 13, 15),
   (5649/10000, 12, 14), (6603/10000, 11, 13), (1481/2000, 10, 12), (8059/10000, 9, 11),
   (4289/5000, 8, 10), (8983/10000, 7, 9), (2323/2500, 6, 8), (2381/2500, 5, 7), (606/625, 4, 6),
   (9821/10000, 3, 5), (9911/10000, 2, 4), (399/400, 1, 3), (1, 1, 2)]

/-- Pieces of the pressure certificate (upper labels in `1/8 keV`). -/
@[expose] def presP : List (ℚ × ℚ × ℚ) :=
  [(37/5000, 17, 143/8), (71/2000, 17, 71/4), (321/5000, 17, 35/2), (467/5000, 16, 69/4),
   (123/1000, 16, 17), (1531/10000, 16, 67/4), (367/2000, 16, 33/2), (2141/10000, 15, 65/4),
   (2449/10000, 15, 16), (2757/10000, 15, 63/4), (613/2000, 15, 31/2), (3371/10000, 14, 61/4),
   (147/400, 14, 15), (159/400, 14, 59/4), (427/1000, 14, 29/2), (57/125, 13, 57/4),
   (4843/10000, 13, 14), (64/125, 13, 55/4), (5389/10000, 13, 27/2), (5649/10000, 12, 53/4),
   (2951/5000, 12, 13), (1229/2000, 12, 51/4), (6379/10000, 12, 25/2), (6603/10000, 11, 49/4),
   (3409/5000, 11, 12), (7023/10000, 11, 47/4), (7219/10000, 11, 23/2), (1481/2000, 10, 45/4),
   (3791/5000, 10, 11), (31/40, 10, 43/4), (7909/10000, 10, 21/2), (8059/10000, 9, 41/4),
   (8201/10000, 9, 10), (4167/5000, 9, 39/4), (423/500, 9, 19/2), (4289/5000, 8, 37/4),
   (8689/10000, 8, 9), (4397/5000, 8, 35/4), (8891/10000, 8, 17/2), (8983/10000, 7, 33/4),
   (2267/2500, 7, 8), (2287/2500, 7, 31/4), (4611/5000, 7, 15/2), (2323/2500, 6, 29/4),
   (2339/2500, 6, 7), (1177/1250, 6, 27/4), (592/625, 6, 13/2), (2381/2500, 5, 25/4),
   (2393/2500, 5, 6), (9617/10000, 5, 23/4), (4829/5000, 5, 11/2), (606/625, 4, 21/4),
   (9731/10000, 4, 5), (2441/2500, 4, 19/4), (9793/10000, 4, 9/2), (9821/10000, 3, 17/4),
   (4923/5000, 3, 4), (987/1000, 3, 15/4), (9891/10000, 3, 7/2), (9911/10000, 2, 13/4),
   (9929/10000, 2, 3), (1989/2000, 2, 11/4), (9961/10000, 2, 5/2), (399/400, 1, 9/4),
   (2497/2500, 1, 2), (1, 1, 7/4)]

/-- The lower barrier `T_sub = Φ⁻¹ ∘ F_sub`. -/
@[expose] def Tsub (s : ℝ) : ℝ := kProf fsS s

/-- The upper barrier `T_sup = Φ⁻¹ ∘ F_sup`. -/
@[expose] def Tsup (s : ℝ) : ℝ := kProf fuS s

/-! ### The certificates (each evaluated once) -/

/-- Lower barrier, corner `χ₀ = 8/5`, `γ = 0.49`. -/
theorem sub_check_ll : pieceCheckL (lowS fsS (8 / 5) (49 / 100)) fsS kirchhoffQ (1 / 20) 0 subP
    = true := by decide +kernel
/-- Lower barrier, corner `χ₀ = 8/5`, `γ = 0.525`. -/
theorem sub_check_lu : pieceCheckL (lowS fsS (8 / 5) (21 / 40)) fsS kirchhoffQ (1 / 20) 0 subP
    = true := by decide +kernel
/-- Lower barrier, corner `χ₀ = 33/20`, `γ = 0.49`. -/
theorem sub_check_hl :
    pieceCheckL (lowS fsS (33 / 20) (49 / 100)) fsS kirchhoffQ (1 / 20) 0 subP = true := by
  decide +kernel
/-- Lower barrier, corner `χ₀ = 33/20`, `γ = 0.525`. -/
theorem sub_check_hu :
    pieceCheckL (lowS fsS (33 / 20) (21 / 40)) fsS kirchhoffQ (1 / 20) 0 subP = true := by
  decide +kernel
/-- Upper barrier, corner `χ₀ = 8/5`, `γ = 0.49`. -/
theorem sup_check_ll : pieceCheckL (upS fuS (8 / 5) (49 / 100)) fuS kirchhoffQ (1 / 20) 0 supP
    = true := by decide +kernel
/-- Upper barrier, corner `χ₀ = 8/5`, `γ = 0.525`. -/
theorem sup_check_lu : pieceCheckL (upS fuS (8 / 5) (21 / 40)) fuS kirchhoffQ (1 / 20) 0 supP
    = true := by decide +kernel
/-- Upper barrier, corner `χ₀ = 33/20`, `γ = 0.49`. -/
theorem sup_check_hl :
    pieceCheckL (upS fuS (33 / 20) (49 / 100)) fuS kirchhoffQ (1 / 20) 0 supP = true := by
  decide +kernel
/-- Upper barrier, corner `χ₀ = 33/20`, `γ = 0.525`. -/
theorem sup_check_hu :
    pieceCheckL (upS fuS (33 / 20) (21 / 40)) fuS kirchhoffQ (1 / 20) 0 supP = true := by
  decide +kernel
/-- Pressure certificate. -/
theorem pres_check : pieceCheckL presS fuS kirchhoffQ 0 0 presP = true := by decide +kernel

/-- Monotonicity: `−F_sub' ≥ 0` on `[0,1]`. -/
theorem fsS_deriv_check :
    QPoly.checkOn (QPoly.scale (-1) (QPoly.deriv fsS)) 0 0 1 (gridN 8) = true := by
  decide +kernel
/-- Monotonicity: `−F_sup' ≥ 0` on `[0,1]`. -/
theorem fuS_deriv_check :
    QPoly.checkOn (QPoly.scale (-1) (QPoly.deriv fuS)) 0 0 1 (gridN 8) = true := by
  decide +kernel
/-- Ordering: `F_sup − F_sub ≥ 0` on `[0,1]`. -/
theorem gapS_check :
    QPoly.checkOn (QPoly.add fuS (QPoly.scale (-1) fsS)) 0 0 1 (gridN 16) = true := by
  decide +kernel

/-- Label and endpoint facts, checked once. -/
theorem labelsS_check :
    (subP.all (fun p => decide (0 ≤ p.2.1)) &&
      supP.all (fun p => (boschHaleWindows.find? (fun w => w.hi == p.2.2)).isSome &&
        decide (p.2.2 ≤ 60)) &&
      decide (pieceEnd2 0 subP = 1) && decide (pieceEnd2 0 supP = 1) &&
      decide (pieceEnd2 0 presP = 1) &&
      decide (QPoly.evalQ fsS 1 = kirchhoffQ 1) &&
      decide (QPoly.evalQ fuS 1 = kirchhoffQ (3 / 2)) &&
      decide (QPoly.evalQ fsS 0 ≤ kirchhoffQ 60) &&
      decide (kirchhoffQ 10 ≤ QPoly.evalQ fsS (3 / 10)) &&
      decide (QPoly.evalQ fuS 0 ≤ kirchhoffQ 18) &&
      presP.all (fun p => decide (0 ≤ p.2.2))) = true := by
  decide +kernel

/-- Unpacked label and endpoint facts. -/
theorem labelsS_facts :
    (∀ p ∈ subP, 0 ≤ p.2.1) ∧
      (∀ p ∈ supP, (boschHaleWindows.find? (fun w => w.hi == p.2.2)).isSome = true ∧
        p.2.2 ≤ 60) ∧
      pieceEnd2 0 subP = 1 ∧ pieceEnd2 0 supP = 1 ∧ pieceEnd2 0 presP = 1 ∧
      QPoly.evalQ fsS 1 = kirchhoffQ 1 ∧ QPoly.evalQ fuS 1 = kirchhoffQ (3 / 2) ∧
      QPoly.evalQ fsS 0 ≤ kirchhoffQ 60 ∧ kirchhoffQ 10 ≤ QPoly.evalQ fsS (3 / 10) ∧
      QPoly.evalQ fuS 0 ≤ kirchhoffQ 18 ∧ (∀ p ∈ presP, 0 ≤ p.2.2) := by
  have h := labelsS_check
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  exact ⟨h1, fun p hp => h2 p hp, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-! ### Consequences -/

/-- `F_sub` is antitone on `[0,1]`. -/
theorem fsS_antitone : AntitoneOn (QPoly.eval fsS) (Icc 0 1) := by
  have := antitoneOn_eval_of_check fsS_deriv_check
  intro a ha b hb hab; exact this (by simpa using ha) (by simpa using hb) hab

/-- `F_sup` is antitone on `[0,1]`. -/
theorem fuS_antitone : AntitoneOn (QPoly.eval fuS) (Icc 0 1) := by
  have := antitoneOn_eval_of_check fuS_deriv_check
  intro a ha b hb hab; exact this (by simpa using ha) (by simpa using hb) hab

/-- `F' ≤ 0` pointwise from a monotonicity certificate. -/
theorem deriv_nonpos_of_check {F : List ℚ}
    (h : QPoly.checkOn (QPoly.scale (-1) (QPoly.deriv F)) 0 0 1 (gridN 8) = true) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : QPoly.eval (QPoly.deriv F) s ≤ 0 := by
  have := QPoly.checkOn_sound h s (by simpa using hs)
  simp only [QPoly.eval_scale] at this; push_cast at this; linarith

/-- Edge values `T_sub(1) = 1`, `T_sup(1) = 3/2`. -/
theorem barrierS_edges : Tsub 1 = 1 ∧ Tsup 1 = 3 / 2 := by
  obtain ⟨-, -, -, -, -, h6, h7, -⟩ := labelsS_facts
  constructor
  · have : QPoly.eval fsS ((1 : ℚ) : ℝ) = kirchhoff ((1 : ℚ) : ℝ) := by
      rw [eval_ratCast, h6, kirchhoffQ_cast]
    simp only [Tsub, kProf]; push_cast at this; rw [this, kirchhoffInv_kirchhoff]
  · have : QPoly.eval fuS ((1 : ℚ) : ℝ) = kirchhoff ((3 / 2 : ℚ) : ℝ) := by
      rw [eval_ratCast, h7, kirchhoffQ_cast]
    simp only [Tsup, kProf]; push_cast at this; rw [this, kirchhoffInv_kirchhoff]

/-- `1 ≤ T_sub ≤ 60` on `[0,1]`. -/
theorem tsub_boundsS {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : 1 ≤ Tsub s ∧ Tsub s ≤ 60 := by
  obtain ⟨-, -, -, -, -, h6, -, h8, -⟩ := labelsS_facts
  have hm1 := fsS_antitone hs ⟨zero_le_one, le_rfl⟩ hs.2
  have hm0 := fsS_antitone ⟨le_rfl, zero_le_one⟩ hs hs.1
  rw [show (1 : ℝ) = ((1 : ℚ) : ℝ) by norm_num, eval_ratCast, h6, kirchhoffQ_cast] at hm1
  rw [show (0 : ℝ) = ((0 : ℚ) : ℝ) by norm_num, eval_ratCast] at hm0
  have h8' : ((QPoly.evalQ fsS 0 : ℚ) : ℝ) ≤ kirchhoff 60 := by
    rw [← show ((60 : ℚ) : ℝ) = 60 by norm_num, ← kirchhoffQ_cast]; exact_mod_cast h8
  exact ⟨le_kirchhoffInv_iff.2 (by simpa using hm1), kirchhoffInv_le_iff.2 (hm0.trans h8')⟩

/-- `1 ≤ T_sup ≤ 18` on `[0,1]`. -/
theorem tsup_boundsS {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : 1 ≤ Tsup s ∧ Tsup s ≤ 18 := by
  obtain ⟨-, -, -, -, -, -, h7, -, -, h10, -⟩ := labelsS_facts
  have hm1 := fuS_antitone hs ⟨zero_le_one, le_rfl⟩ hs.2
  have hm0 := fuS_antitone ⟨le_rfl, zero_le_one⟩ hs hs.1
  rw [show (1 : ℝ) = ((1 : ℚ) : ℝ) by norm_num, eval_ratCast, h7, kirchhoffQ_cast] at hm1
  rw [show (0 : ℝ) = ((0 : ℚ) : ℝ) by norm_num, eval_ratCast] at hm0
  have h10' : ((QPoly.evalQ fuS 0 : ℚ) : ℝ) ≤ kirchhoff 18 := by
    rw [← show ((18 : ℚ) : ℝ) = 18 by norm_num, ← kirchhoffQ_cast]; exact_mod_cast h10
  refine ⟨?_, kirchhoffInv_le_iff.2 (hm0.trans h10')⟩
  have : (1 : ℝ) ≤ 3 / 2 := by norm_num
  exact this.trans (le_kirchhoffInv_iff.2 (by push_cast at hm1; exact hm1))

/-- **Core temperature.** `T_sub ≥ 10 keV` on `s ≤ 3/10`. -/
theorem tsub_coreS {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 3 / 10) : 10 ≤ Tsub s := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := labelsS_facts
  have hm := fsS_antitone ⟨h0, h1.trans (by norm_num)⟩ ⟨by norm_num, by norm_num⟩ h1
  rw [show ((3 : ℝ) / 10) = ((3 / 10 : ℚ) : ℝ) by norm_num, eval_ratCast] at hm
  have h9' : kirchhoff 10 ≤ ((QPoly.evalQ fsS (3 / 10) : ℚ) : ℝ) := by
    rw [← show ((10 : ℚ) : ℝ) = 10 by norm_num, ← kirchhoffQ_cast]; exact_mod_cast h9
  exact le_kirchhoffInv_iff.2 (h9'.trans hm)

/-- Sanity: the band is not empty, `T_sub ≤ T_sup` on `[0,1]`. -/
theorem solovev_band_nonempty {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : Tsub s ≤ Tsup s := by
  have := QPoly.checkOn_sound gapS_check s (by simpa using hs)
  simp only [QPoly.eval_add, QPoly.eval_scale] at this
  push_cast at this
  exact kirchhoffIso.symm.monotone (by linarith)

/-- Label-dependent piece soundness at a point of `[0,1]`. -/
theorem pieceL_at {Qf : ℚ → ℚ → List ℚ} {F : List ℚ} {κ : ℚ} {ps : List (ℚ × ℚ × ℚ)}
    (hc : pieceCheckL Qf F kirchhoffQ κ 0 ps = true) (hne : ps ≠ [])
    (hend : pieceEnd2 0 ps = 1) (hF : AntitoneOn (QPoly.eval F) (Icc 0 1)) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ k K : ℚ, (∃ d, (d, k, K) ∈ ps) ∧ (k : ℝ) ≤ kProf F s ∧ kProf F s ≤ K ∧
      (κ : ℝ) ≤ QPoly.eval (Qf k K) s := by
  obtain ⟨k, K, hmem, h1, h2, h3⟩ := pieceCheckL_sound 0 ps hc hne
    (fun a ha b hb hab => hF (by simpa [hend] using ha) (by simpa [hend] using hb) hab) s
    (by simpa [hend] using hs)
  rw [kirchhoffQ_cast] at h1 h2
  exact ⟨k, K, hmem, le_kirchhoffInv_iff.2 h1, kirchhoffInv_le_iff.2 h2, h3⟩

/-! ### Bilinear corner bounds -/

/-- **Lower corner bound.** For `γ_L s ≤ g ≤ γ_U s`, `h ≤ h_U`, `Y ≤ 0` and
`0 ≤ χ_L ≤ χ₀ ≤ χ_H`, the bilinear form `χ₀ (g X + h Y)` is at least the minimum of its four
corner values `χ (γ s X + h_U Y)`. -/
theorem bilin_lower {s g h X Y χ₀ χL χH γL γU hU : ℝ} (hg1 : γL * s ≤ g)
    (hg2 : g ≤ γU * s) (hh : h ≤ hU) (hY : Y ≤ 0) (hχ0 : 0 ≤ χL) (hχ1 : χL ≤ χ₀)
    (hχ2 : χ₀ ≤ χH) :
    min (min (χL * (γL * (s * X) + hU * Y)) (χL * (γU * (s * X) + hU * Y)))
        (min (χH * (γL * (s * X) + hU * Y)) (χH * (γU * (s * X) + hU * Y))) ≤
      χ₀ * (g * X + h * Y) := by
  have hhY : hU * Y ≤ h * Y := mul_le_mul_of_nonpos_right hh hY
  have key : ∀ γ : ℝ, γ * (s * X) ≤ g * X →
      min (χL * (γ * (s * X) + hU * Y)) (χH * (γ * (s * X) + hU * Y)) ≤
        χ₀ * (g * X + h * Y) := by
    intro γ hγ
    have hA : γ * (s * X) + hU * Y ≤ g * X + h * Y := by linarith
    have hc0 : 0 ≤ χ₀ := hχ0.trans hχ1
    rcases le_total 0 (γ * (s * X) + hU * Y) with hA0 | hA0
    · exact (min_le_left _ _).trans ((mul_le_mul_of_nonneg_right hχ1 hA0).trans
        (mul_le_mul_of_nonneg_left hA hc0))
    · exact (min_le_right _ _).trans ((mul_le_mul_of_nonpos_right hχ2 hA0).trans
        (mul_le_mul_of_nonneg_left hA hc0))
  rcases le_total 0 X with hX | hX
  · have := key γL (by nlinarith [mul_le_mul_of_nonneg_right hg1 hX])
    refine le_trans ?_ this
    exact le_min ((min_le_left _ _).trans (min_le_left _ _))
      ((min_le_right _ _).trans (min_le_left _ _))
  · have := key γU (by nlinarith [mul_le_mul_of_nonpos_right hg2 hX])
    refine le_trans ?_ this
    exact le_min ((min_le_left _ _).trans (min_le_right _ _))
      ((min_le_right _ _).trans (min_le_right _ _))

/-- **Upper corner bound.** For `γ_L s ≤ g ≤ γ_U s`, `h_L ≤ h`, `Y ≤ 0` and
`0 ≤ χ_L ≤ χ₀ ≤ χ_H`, `χ₀ (g X + h Y)` is at most the maximum of the four corner values
`χ (γ s X + h_L Y)`. -/
theorem bilin_upper {s g h X Y χ₀ χL χH γL γU hL : ℝ} (hg1 : γL * s ≤ g)
    (hg2 : g ≤ γU * s) (hh : hL ≤ h) (hY : Y ≤ 0) (hχ0 : 0 ≤ χL) (hχ1 : χL ≤ χ₀)
    (hχ2 : χ₀ ≤ χH) :
    χ₀ * (g * X + h * Y) ≤
      max (max (χL * (γL * (s * X) + hL * Y)) (χL * (γU * (s * X) + hL * Y)))
        (max (χH * (γL * (s * X) + hL * Y)) (χH * (γU * (s * X) + hL * Y))) := by
  have hhY : h * Y ≤ hL * Y := mul_le_mul_of_nonpos_right hh hY
  have key : ∀ γ : ℝ, g * X ≤ γ * (s * X) →
      χ₀ * (g * X + h * Y) ≤
        max (χL * (γ * (s * X) + hL * Y)) (χH * (γ * (s * X) + hL * Y)) := by
    intro γ hγ
    have hA : g * X + h * Y ≤ γ * (s * X) + hL * Y := by linarith
    have hc0 : 0 ≤ χ₀ := hχ0.trans hχ1
    rcases le_total 0 (γ * (s * X) + hL * Y) with hA0 | hA0
    · exact ((mul_le_mul_of_nonneg_left hA hc0).trans
        (mul_le_mul_of_nonneg_right hχ2 hA0)).trans (le_max_right _ _)
    · exact ((mul_le_mul_of_nonneg_left hA hc0).trans
        (mul_le_mul_of_nonpos_right hχ1 hA0)).trans (le_max_left _ _)
  rcases le_total 0 X with hX | hX
  · refine (key γU (by nlinarith [mul_le_mul_of_nonneg_right hg2 hX])).trans ?_
    exact max_le ((le_max_right _ _).trans (le_max_left _ _))
      ((le_max_right _ _).trans (le_max_right _ _))
  · refine (key γL (by nlinarith [mul_le_mul_of_nonpos_right hg1 hX])).trans ?_
    exact max_le ((le_max_left _ _).trans (le_max_left _ _))
      ((le_max_left _ _).trans (le_max_right _ _))

/-! ### Margins -/

/-- `P · N` on a Kirchhoff profile, in corner form. -/
theorem Pw_op (G : FluxGeometry) [hG : IsSolovevGeometry G] (sv : ℝ → ℝ) (χ₀ : ℝ)
    (F : List ℚ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Pw s * (solCoeffs G sv χ₀).op s (kProf F s) (kProf' F s) (kProf'' F s) =
      χ₀ * (G.g s * (Pw s * QPoly.eval (QPoly.deriv (QPoly.deriv F)) s -
        1 / 2 * QPoly.eval (QPoly.deriv F) s) + G.h s * (Pw s * QPoly.eval (QPoly.deriv F) s)) +
      Pw s * QPoly.eval auxSol s + 9 / 10 * (1 - 4 / 5 * s) ^ 2 *
        (alphaRate * sv (kProf F s) - bremsRate * Real.sqrt (kProf F s)) := by
  rw [solCoeffs_op_kProf G sv χ₀ F hs, solSource]
  have h1 := Pw_dlog hs
  have h2 := Pw_dens hs
  linear_combination (χ₀ * G.g s * QPoly.eval (QPoly.deriv F) s) * h1 +
    (alphaRate * sv (kProf F s) - bremsRate * Real.sqrt (kProf F s)) * h2

/-- **Lower-barrier margin.** For every geometry in `IsSolovevGeometry`, every supplied
reactivity and every `χ₀ ∈ [8/5, 33/20]`, `N[T_sub] ≥ 1/20 keV/s` on `[0,1]`. -/
theorem tsubS_margin (G : FluxGeometry) [hG : IsSolovevGeometry G] (sv : ℝ → ℝ)
    [BoschHaleDT sv] {χ₀ : ℝ} (h1 : 8 / 5 ≤ χ₀) (h2 : χ₀ ≤ 33 / 20) :
    ∀ s ∈ Icc (0 : ℝ) 1, (1 / 20 : ℝ) ≤
      (solCoeffs G sv χ₀).op s (Tsub s) (kProf' fsS s) (kProf'' fsS s) := by
  intro s hs
  obtain ⟨hl, -, hend, -⟩ := labelsS_facts
  have hne : subP ≠ [] := by simp [subP]
  obtain ⟨hP0, hP1⟩ := Pw_bounds hs
  set X := Pw s * QPoly.eval (QPoly.deriv (QPoly.deriv fsS)) s -
    1 / 2 * QPoly.eval (QPoly.deriv fsS) s with hX
  set Y := Pw s * QPoly.eval (QPoly.deriv fsS) s with hY
  have hY0 : Y ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hP0.le (deriv_nonpos_of_check fsS_deriv_check hs)
  set src := alphaRate * sv (Tsub s) - bremsRate * Real.sqrt (Tsub s) with hsrc
  set L := 1 / 20 - Pw s * QPoly.eval auxSol s - 9 / 10 * (1 - 4 / 5 * s) ^ 2 * src with hL
  have hw0 : 0 ≤ 9 / 10 * (1 - 4 / 5 * s) ^ 2 := by positivity
  have corner : ∀ χ γ : ℚ, pieceCheckL (lowS fsS χ γ) fsS kirchhoffQ (1 / 20) 0 subP = true →
      L ≤ (χ : ℝ) * ((γ : ℝ) * (s * X) + 21 / 40 * Y) := by
    intro χ γ hc
    obtain ⟨k, K, ⟨d, hmem⟩, hk, hK, hQ⟩ := pieceL_at hc hne hend fsS_antitone hs
    obtain ⟨hT1, hT60⟩ := tsub_boundsS hs
    change (k : ℝ) ≤ Tsub s at hk
    change Tsub s ≤ K at hK
    have hfl := svFloor_le sv (hl _ hmem) hk hT60
    have hsv0 : 0 ≤ sv (Tsub s) := BoschHaleDT.nonneg _ (by linarith)
    have hα : (229 / 10 * 10 ^ 21 : ℝ) * svFloor k ≤ alphaRate * sv (Tsub s) :=
      (mul_le_mul_of_nonneg_left hfl (by norm_num)).trans
        (mul_le_mul_of_nonneg_right alphaRate_ge hsv0)
    have hsq := sqrt_le_quarter (T := Tsub s) (by linarith)
    have hbr : bremsRate * Real.sqrt (Tsub s) ≤ 201 / 1000 * ((K + 4) / 4) :=
      mul_le_mul bremsRate_le (hsq.trans (by linarith)) (Real.sqrt_nonneg _) (by norm_num)
    have hb : ((lowBonus k K : ℚ) : ℝ) ≤ src := by
      simp only [lowBonus]; push_cast; rw [hsrc]; linarith
    have hQ' := hQ
    simp only [lowS, QPoly.eval_add, QPoly.eval_scale, condS_eval, Paux_eval, Pnu_eval] at hQ'
    push_cast at hQ'
    rw [← hX, ← hY] at hQ'
    have := mul_le_mul_of_nonneg_left hb hw0
    nlinarith
  have hmin := bilin_lower (s := s) (g := G.g s) (h := G.h s) (X := X) (Y := Y) (χ₀ := χ₀)
    (χL := 8 / 5) (χH := 33 / 20) (γL := 49 / 100) (γU := 21 / 40) (hU := 21 / 40)
    (hG.g_lower s hs) (hG.g_upper s hs) (hG.h_upper s hs) hY0 (by norm_num) h1 h2
  have c1 := corner (8 / 5) (49 / 100) sub_check_ll
  have c2 := corner (8 / 5) (21 / 40) sub_check_lu
  have c3 := corner (33 / 20) (49 / 100) sub_check_hl
  have c4 := corner (33 / 20) (21 / 40) sub_check_hu
  push_cast at c1 c2 c3 c4
  have hcon : L ≤ χ₀ * (G.g s * X + G.h s * Y) :=
    (le_min (le_min c1 c2) (le_min c3 c4)).trans hmin
  have hPop := Pw_op G sv χ₀ fsS hs
  change Pw s * (solCoeffs G sv χ₀).op s (Tsub s) (kProf' fsS s) (kProf'' fsS s) = _ at hPop
  rw [← hX, ← hY] at hPop
  set N := (solCoeffs G sv χ₀).op s (Tsub s) (kProf' fsS s) (kProf'' fsS s)
  have hPN : 1 / 20 ≤ Pw s * N := by rw [hPop]; change _ ≤ _ + _ + _ * src; linarith
  nlinarith

/-- **Upper-barrier margin.** For every geometry in `IsSolovevGeometry`, every supplied
reactivity and every `χ₀ ∈ [8/5, 33/20]`, `N[T_sup] ≤ −1/20 keV/s` on `[0,1]`. -/
theorem tsupS_margin (G : FluxGeometry) [hG : IsSolovevGeometry G] (sv : ℝ → ℝ)
    [BoschHaleDT sv] {χ₀ : ℝ} (h1 : 8 / 5 ≤ χ₀) (h2 : χ₀ ≤ 33 / 20) :
    ∀ s ∈ Icc (0 : ℝ) 1,
      (solCoeffs G sv χ₀).op s (Tsup s) (kProf' fuS s) (kProf'' fuS s) ≤ -(1 / 20) := by
  intro s hs
  obtain ⟨-, hu, -, hend, -⟩ := labelsS_facts
  have hne : supP ≠ [] := by simp [supP]
  obtain ⟨hP0, hP1⟩ := Pw_bounds hs
  set X := Pw s * QPoly.eval (QPoly.deriv (QPoly.deriv fuS)) s -
    1 / 2 * QPoly.eval (QPoly.deriv fuS) s with hX
  set Y := Pw s * QPoly.eval (QPoly.deriv fuS) s with hY
  have hY0 : Y ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hP0.le (deriv_nonpos_of_check fuS_deriv_check hs)
  set src := alphaRate * sv (Tsup s) - bremsRate * Real.sqrt (Tsup s) with hsrc
  set U := -(1 / 20) - Pw s * QPoly.eval auxSol s - 9 / 10 * (1 - 4 / 5 * s) ^ 2 * src with hU
  have hw0 : 0 ≤ 9 / 10 * (1 - 4 / 5 * s) ^ 2 := by positivity
  have corner : ∀ χ γ : ℚ, pieceCheckL (upS fuS χ γ) fuS kirchhoffQ (1 / 20) 0 supP = true →
      (χ : ℝ) * ((γ : ℝ) * (s * X) + 49 / 100 * Y) ≤ U := by
    intro χ γ hc
    obtain ⟨k, K, ⟨d, hmem⟩, -, hK, hQ⟩ := pieceL_at hc hne hend fuS_antitone hs
    obtain ⟨hT1, -⟩ := tsup_boundsS hs
    change Tsup s ≤ K at hK
    obtain ⟨hw, hK60⟩ := hu _ hmem
    have hsv := sv_le_svCeil sv hw hK60 hT1 hK
    have hsv0 : 0 ≤ sv (Tsup s) := BoschHaleDT.nonneg _ (by linarith)
    have hα : alphaRate * sv (Tsup s) ≤ 2291 / 100 * 10 ^ 21 * svCeil K :=
      mul_le_mul alphaRate_le hsv hsv0 (by norm_num)
    have hbr : 0 ≤ bremsRate * Real.sqrt (Tsup s) :=
      mul_nonneg bremsRate_nonneg (Real.sqrt_nonneg _)
    have hb : src ≤ 2291 / 100 * 10 ^ 21 * (svCeil K : ℝ) := by rw [hsrc]; linarith
    have hQ' := hQ
    simp only [upS, QPoly.eval_add, QPoly.eval_scale, condS_eval, Paux_eval, Pnu_eval] at hQ'
    push_cast at hQ'
    rw [← hX, ← hY] at hQ'
    have := mul_le_mul_of_nonneg_left hb hw0
    nlinarith
  have hmax := bilin_upper (s := s) (g := G.g s) (h := G.h s) (X := X) (Y := Y) (χ₀ := χ₀)
    (χL := 8 / 5) (χH := 33 / 20) (γL := 49 / 100) (γU := 21 / 40) (hL := 49 / 100)
    (hG.g_lower s hs) (hG.g_upper s hs) (hG.h_lower s hs) hY0 (by norm_num) h1 h2
  have c1 := corner (8 / 5) (49 / 100) sup_check_ll
  have c2 := corner (8 / 5) (21 / 40) sup_check_lu
  have c3 := corner (33 / 20) (49 / 100) sup_check_hl
  have c4 := corner (33 / 20) (21 / 40) sup_check_hu
  push_cast at c1 c2 c3 c4
  have hcon : χ₀ * (G.g s * X + G.h s * Y) ≤ U :=
    hmax.trans (max_le (max_le c1 c2) (max_le c3 c4))
  have hPop := Pw_op G sv χ₀ fuS hs
  change Pw s * (solCoeffs G sv χ₀).op s (Tsup s) (kProf' fuS s) (kProf'' fuS s) = _ at hPop
  rw [← hX, ← hY] at hPop
  set N := (solCoeffs G sv χ₀).op s (Tsup s) (kProf' fuS s) (kProf'' fuS s)
  have hPN : Pw s * N ≤ -(1 / 20) := by rw [hPop]; change _ + _ + _ * src ≤ _; linarith
  nlinarith

/-! ### Pressure -/

/-- Plasma density `n(s) = 10²⁰ · dens s` (m⁻³). -/
@[expose] def nProf (s : ℝ) : ℝ := 1e20 * dens s

/-- **Pressure certificate.** `n(s) (1 + 53/60) T_sup(s) keV ≤ p_eq(s) + 40 kPa` on `[0,1]`
for reactor `μ₀ ∈ [1.2566·10⁻⁶, 1.2567·10⁻⁶]`. -/
theorem tsup_pressure {μ₀ : ℝ} (hμ1 : 1.2566e-6 ≤ μ₀) (hμ2 : μ₀ ≤ 1.2567e-6) :
    ∀ s ∈ Icc (0 : ℝ) 1, nProf s * (1 + 53 / 60) * Tsup s * keV ≤ peqLabel μ₀ 40000 s := by
  intro s hs
  obtain ⟨-, -, -, -, hend, -, -, -, -, -, hpl⟩ := labelsS_facts
  have hne : presP ≠ [] := by simp [presP]
  obtain ⟨k, K, ⟨d, hmem⟩, -, hK, hQ⟩ := pieceL_at pres_check hne hend fuS_antitone hs
  change Tsup s ≤ K at hK
  rw [presS_eval] at hQ
  push_cast at hQ
  have hpeq := (peqLabel_bounds hμ1 hμ2 40000 hs).1
  have hw2 := w2_pos hs
  have hT0 : 0 ≤ Tsup s := by linarith [(tsup_boundsS hs).1]
  have hw1 : 0 ≤ 1 - 4 / 5 * s := by linarith [hs.2]
  have hc : (0 : ℝ) ≤ 9 / 10 * 10 ^ 20 * (113 / 60) * (1602176634 / 10 ^ 25) * (1 - 4 / 5 * s) :=
    by positivity
  have hmono := mul_le_mul_of_nonneg_left hK hc
  have hkeV : keV = 1602176634 / 10 ^ 25 := by norm_num [keV]
  have e : nProf s * (1 + 53 / 60) * Tsup s * keV * (1 - 3 / 10 * s) =
      9 / 10 * 10 ^ 20 * (113 / 60) * (1602176634 / 10 ^ 25) * (1 - 4 / 5 * s) * Tsup s := by
    rw [hkeV]; unfold nProf dens
    have h10 : (10 : ℝ) - s * 3 ≠ 0 := by intro h; linarith [hs.2]
    field_simp
    ring
  have : nProf s * (1 + 53 / 60) * Tsup s * keV * (1 - 3 / 10 * s) ≤
      (40000 + 456900 * (1 - 11 / 12 * s)) * (1 - 3 / 10 * s) := by
    rw [e]; nlinarith
  have := le_of_mul_le_mul_right this hw2
  linarith

/-! ### The band for all time -/

/-- **Two-sided quasilinear band on the Solov'ev geometry.** For every geometry in
`IsSolovevGeometry`, every reactivity satisfying the supplied Bosch–Hale enclosures, every
`χ₀ ∈ [8/5, 33/20]` m²/s, and every kernel solution on all horizons of the band coefficients
`solCoeffs G sv χ₀` with edge temperature in `[1, 3/2]` keV and initial profile in
`[T_sub, T_sup]`: for all `t ≥ 0`, `T_sub ≤ T ≤ T_sup`, `T ≥ 10 keV` on `s ≤ 3/10`, and
`T ≤ 18 keV`. -/
theorem solovev_band (G : FluxGeometry) [hG : IsSolovevGeometry G] (sv : ℝ → ℝ)
    [BoschHaleDT sv] {χ₀ : ℝ} (h1 : 8 / 5 ≤ χ₀) (h2 : χ₀ ≤ 33 / 20) {Tedge : ℝ → ℝ}
    {u : RadialField}
    (hu : ∀ τ, 0 ≤ τ → ClassicalRadialSolution (solCoeffs G sv χ₀) Tedge τ u)
    (h0 : ∀ s ∈ Icc (0 : ℝ) 1, Tsub s ≤ u.T s 0 ∧ u.T s 0 ≤ Tsup s)
    (hedge : ∀ t, 0 ≤ t → 1 ≤ Tedge t ∧ Tedge t ≤ 3 / 2) :
    (∀ s ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → Tsub s ≤ u.T s t ∧ u.T s t ≤ Tsup s) ∧
      (∀ s, 0 ≤ s → s ≤ 3 / 10 → ∀ t, 0 ≤ t → 10 ≤ u.T s t) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → u.T s t ≤ 18) := by
  have hL := solCoeffs_transportLaws G sv (by linarith : (0 : ℝ) ≤ χ₀)
  have hk : (solCoeffs G sv χ₀).axis = .regular → False := fun h => by
    simp [solCoeffs, FluxGeometry.qcoeffs] at h
  have hlow : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → Tsub s ≤ u.T s t :=
    le_of_lowerMargin_shift_forall_time (fun τ hτ => { hL, hu τ hτ with })
      (kProf_regular fsS) (fun h => (hk h).elim)
      (sol_opShiftControl G sv χ₀ fsS (fun s hs => by
        linarith [(tsub_boundsS hs).1, show Tsub s = kProf fsS s from rfl]))
      (by norm_num) (tsubS_margin G sv h1 h2) (fun s hs => (h0 s hs).1)
      (fun t ht => by rw [barrierS_edges.1]; exact (hedge t ht).1)
  have hup : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → u.T s t ≤ Tsup s :=
    le_of_upperMargin_shift_forall_time (fun τ hτ => { hL, hu τ hτ with })
      (kProf_regular fuS) (fun h => (hk h).elim)
      (sol_opShiftControl G sv χ₀ fuS (fun s hs => by
        linarith [(tsup_boundsS hs).1, show Tsup s = kProf fuS s from rfl]))
      (by norm_num) (tsupS_margin G sv h1 h2) (fun s hs => (h0 s hs).2)
      (fun t ht => by rw [barrierS_edges.2]; exact (hedge t ht).2)
  refine ⟨fun s hs t ht => ⟨hlow s hs t ht, hup s hs t ht⟩, fun s h0' h1' t ht => ?_,
    fun s hs t ht => (hup s hs t ht).trans (tsup_boundsS hs).2⟩
  exact (tsub_coreS h0' h1').trans (hlow s ⟨h0', h1'.trans (by norm_num)⟩ t ht)

/-! ### One plasma -/

/-- **`solovev_one_plasma` (rung C2 of `notes/theory/transport-mhd-coupling.md`).** One
field: the reactor Solov'ev field `B` with Ampère current `J` and pressure `p_eq + Δ`,
`Δ = 40 kPa`.

1. *(equilibrium)* the kernel law `ForceBalance B J ∇(p_eq + Δ)` holds at every point of the
   transport domain `s ≤ 1`;
2. *(alphas)* every 3.5 MeV alpha born at `s ≤ 3/11` stays in `0 ≤ s ≤ 1` for all real time;
3. *(transport)* for every geometry in `IsSolovevGeometry` (coarea link and enclosures
   supplied), every supplied reactivity, every `χ₀ ∈ [8/5, 33/20]` (prescribed stand-in
   `χ₀ (1/10 + T²/100)`), and every supplied classical solution on all horizons with edge
   temperature in `[1, 3/2]` keV starting in the band: for all `t ≥ 0`,
   `T_sub ≤ T ≤ T_sup` on `[0,1]`, `T ≥ 10 keV` on `s ≤ 3/10`, and the plasma pressure
   `n(s)(1 + r_i) T keV` at every point `x` of the transport domain is at most `p_eq(x) + Δ`.

Caveats: axisymmetric (tokamak-like), not a stellarator; static field; the offset `Δ` is an
edge pedestal whose current sheet lies outside the kernel; the layer `ψ̃_b < ψ̃ < ψ̃_e` and the
exterior are unmodelled; no MHD stability claim; driven (`Q ≈ 5.5`, oracle), not ignited. -/
theorem solovev_one_plasma {μ₀ : ℝ} (hμ1 : 1.2566e-6 ≤ μ₀) (hμ2 : μ₀ ≤ 1.2567e-6) :
    (∀ x : Space, label x ≤ 1 →
      ForceBalance (ofLp (reactorField x)) (ofLp (current μ₀ (7 / 4) 10 50 x))
        (ofLp (gradient (offsetPressure μ₀ 40000) x))) ∧
    (∀ {m e : ℝ} {x v : ℝ → Space}, 6.6446e-27 ≤ m → m ≤ 6.6448e-27 → 1.6021e-19 ≤ e →
      e ≤ 1.6023e-19 → LorentzOrbit m (2 * e) (fun _ => 0) reactorField x v →
      m * ‖v 0‖ ^ 2 ≤ 2 * (3.5e6 * e) → label (x 0) ≤ 3 / 11 →
      ∀ t, label (x t) ∈ Icc (0 : ℝ) 1) ∧
    (∀ (G : FluxGeometry) [IsSolovevGeometry G] (sv : ℝ → ℝ) [BoschHaleDT sv] {χ₀ : ℝ},
      8 / 5 ≤ χ₀ → χ₀ ≤ 33 / 20 → ∀ {Tedge : ℝ → ℝ} {u : RadialField},
      (∀ τ, 0 ≤ τ → ClassicalRadialSolution (solCoeffs G sv χ₀) Tedge τ u) →
      (∀ s ∈ Icc (0 : ℝ) 1, Tsub s ≤ u.T s 0 ∧ u.T s 0 ≤ Tsup s) →
      (∀ t, 0 ≤ t → 1 ≤ Tedge t ∧ Tedge t ≤ 3 / 2) →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → Tsub s ≤ u.T s t ∧ u.T s t ≤ Tsup s) ∧
      (∀ s, 0 ≤ s → s ≤ 3 / 10 → ∀ t, 0 ≤ t → 10 ≤ u.T s t) ∧
      (∀ x : Space, label x ≤ 1 → ∀ t, 0 ≤ t →
        nProf (label x) * (1 + 53 / 60) * u.T (label x) t * keV ≤
          reactorPressure μ₀ x + 40000)) := by
  have hμ : μ₀ ≠ 0 := by intro h; rw [h] at hμ1; norm_num at hμ1
  refine ⟨fun x hx => offset_force_balance_domain hμ 40000 hx,
    fun hm1 hm2 he1 he2 h hK hs0 t =>
      (alpha_stays_in_transport_domain hm1 hm2 he1 he2 h hK hs0 t).1, ?_⟩
  intro G _ sv _ χ₀ h1 h2 Tedge u hu h0 hedge
  obtain ⟨hband, hcore, -⟩ := solovev_band G sv h1 h2 hu h0 hedge
  refine ⟨hband, hcore, fun x hx t ht => ?_⟩
  exact plasma_pressure_le_offset (c := 1 + 53 / 60) (n := nProf) (Tsup := Tsup)
    (T := u.T) hμ (by norm_num)
    (fun s hs => by unfold nProf; have := dens_pos hs; positivity)
    (fun s hs t ht => (hband s hs t ht).2) (tsup_pressure hμ1 hμ2) hx ht

end PlasmaLean.Design.SolovevBand
