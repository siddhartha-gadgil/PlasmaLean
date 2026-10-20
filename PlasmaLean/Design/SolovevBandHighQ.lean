/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevBand
public import PlasmaLean.Theory.Transport.BoschHaleFine
public import PlasmaLean.Sanity.BoschHaleFineInstance
public import PlasmaLean.Design.SolovevFluxGeometry

/-!
# A high-`Q` two-sided transport band on the Solov'ev geometry, and `solovev_one_plasma_highQ`

Labels: *geometry class* `IsSolovevGeometry` (reused unchanged from `Design.SolovevBand`;
**proved for the actual reactor Solov'ev field** by
`SolovevFluxGeometry.solovevFluxGeometry_isSolovev`, see the `_actual` theorem; the remaining
unformalized link is the coarea formula / change of variables stated in
`Design.SolovevFluxGeometry`), *synthetic reactor-scale data*, Bosch–Hale reactivity as
*supplied data*
(the **fine** class `Transport.BoschHaleFine`: kernel windows plus quarter-keV windows on
`[5, 30]` keV), quasilinear transport law *supplied* (rational stand-in `χ₀ (1/10 + T²/100)`,
as in `SolovevBand`; only this stand-in is certified).

## What changes compared with `SolovevBand.solovev_one_plasma`

* **Auxiliary heating** `q_aux = 2 (1 − s)⁶` keV/s (`highQ_aux`) instead of `14 (1 − s)⁶`: about
  **17.5 MW** instead of ≈ 120 MW (oracle, `V' ≈ 1600–1680 m³`).
* **Transport window** `χ₀ ∈ [39 / 50, 21 / 25]` m²/s (width `0.06`, ±3.7 %) instead of
  `[8/5, 33/20]`.
* **Reactivity bounds.** Lower barrier: fine floors `svFloorF k` (quarter-keV labels on
  `[5, 30]` keV) and bremsstrahlung `√T ≤ sqB K` (tangent-line bound, `sqrt_le_sqB`). Upper
  barrier: fine ceilings `svCeilF K` and, new, a bremsstrahlung **lower** bound
  `√T ≥ sqL k` (`sqL_le_sqrt`) with `bremsRate ≥ 0.2009` (`bremsRate_ge`); the coarse module
  dropped bremsstrahlung from the upper barrier.
* **Margin** `κ = 1/200` keV/s (any positive margin feeds the comparison theorem).
* Unchanged: density `n(s) = 0.9·10²⁰ (1 − 4s/5)/(1 − 3s/10)` m⁻³, geometry class, edge
  temperature in `[1, 3/2]` keV, `Δ = 40000 Pa`, `T ≥ 10 keV` on `s ≤ 3/10`.

## Structure

* *Generic machinery* (any auxiliary heating polynomial `aux`): source `srcA aux`,
  coefficients `coeffsA aux` (kernel instance `coeffsA_transportLaws`, Kirchhoff form
  `coeffsA_op_kProf`), corner polynomials `lowA`, `upA`, `presD`, and the generic theorems
  `tsub_margin_gen`, `tsup_margin_gen`, `pressure_gen`, `band_gen`, which turn passing
  certificates into margins, the pressure ceiling and the band. `Design.SolovevBandIgnited`
  reuses them with `aux = 0`.
* *High-`Q` instance* (prefix `highQ_`): data, certificates and the theorems below.

## Certificates (each evaluated once by the kernel)

Same structure as `SolovevBand`: multiply by `P(s) = (1 − 4s/5)(1 − 3s/10)`; four bilinear
corners `χ₀ ∈ {39 / 50, 21 / 25}`, `γ ∈ {0.49, 0.525}`; label-dependent piece checks
`pieceCheckL` for the lower barrier, the upper barrier and the pressure ceiling
(labels in `1/8 keV`).

## Results

* `highQ_band`: every kernel solution on all horizons with edge temperature in `[1, 3/2]` keV
  and initial data in `[T_sub, T_sup]` stays there for all `t ≥ 0`; `T ≥ 10 keV` on
  `s ≤ 3/10`; `T ≤ 19 keV`. Profiles (oracle): `T_sub(0) ≈ 12.2`, `T_sub(3/10) ≈ 10.2`;
  `T_sup(0) ≈ 18.2`, `T_sup(3/10) ≈ 16.0` keV.
* `highQ_pressure`: `n(s)(1 + 53/60) T_sup(s) keV ≤ p_eq(s) + Δ` on `[0,1]`.
* `solovev_one_plasma_highQ`: same structure as `SolovevBand.solovev_one_plasma`.
* `highQ_hypotheses_inhabited`: the fine reactivity class and the geometry class are
  inhabited.

## Oracle numbers (Python, untrusted; `/tmp/k4`)

Steady states of the nominal problem (`g = 0.51 s`, `h = 0.51`, Bosch–Hale fit, finite
differences, 200 cells, `V' = 1599 (1 + s/20) m³`):

| `χ₀` | `T(0)` | `T(3/10)` | `P_α` | `P_aux` | `Q = 5 P_α/P_aux` | `max p/(p_eq + Δ)` |
| --- | --- | --- | --- | --- | --- | --- |
| 0.78 | 16.4 keV | 14.3 keV | 161 MW | 17.5 MW | 46 | 0.90 |
| 0.81 | 15.8 keV | 13.7 keV | 149 MW | 17.5 MW | 43 | 0.86 |
| 0.84 | 15.2 keV | 13.1 keV | 137 MW | 17.5 MW | 39 | 0.83 |

`Q` and `P_α` are **not** formalized; they are oracle values for the steady states that the
certified band brackets.

**Ignition** (`q_aux = 0`) is treated in `Design.SolovevBandIgnited`; it needs a much narrower
transport window (`χ₀ ∈ [0.63, 0.64]`) and a larger pressure offset (`Δ = 90 kPa`).

## Honest limitations

The geometry enclosures are proved for the actual field (`solovevFluxGeometry_isSolovev`);
the coarea / change-of-variables link is stated, not formalized
(`Design.SolovevFluxGeometry`); the fine Bosch–Hale windows are supplied data (non-vacuity:
`Sanity.BoschHaleFineInstance`); `χ` is a prescribed stand-in; density, composition and
auxiliary deposition are prescribed; solutions are supplied; `Δ` is an unmodelled edge
pedestal; axisymmetric tokamak-like equilibrium, static fields, no MHD stability claim.
-/

public section

noncomputable section

namespace PlasmaLean.Design.SolovevBandHighQ

open Set Filter Topology PlasmaLean.Transport PlasmaLean.Fusion PlasmaLean.Certificates
  PlasmaLean.Design.TransportBarrier PlasmaLean.Design.QuasilinearBarrier
  PlasmaLean.Design.SolovevOnePlasma PlasmaLean.Fields PlasmaLean.Kinetic
  PlasmaLean.Design.Solovev PlasmaLean.Design.SolovevAlpha PlasmaLean.Design.SolovevBand
  PlasmaLean.Design.SolovevFluxGeometry WithLp

/-! ### Generic machinery: source and coefficients for an auxiliary heating profile `aux` -/

/-- Net source per unit heat capacity (keV/s) for the auxiliary heating rate
`q_aux = aux(s)` (a polynomial, keV/s): `R(s,T) = (n/10²⁰)(α ⟨σv⟩(T) − b √T) + q_aux(s)`. -/
@[expose] def srcA (aux : List ℚ) (sv : ℝ → ℝ) (s T : ℝ) : ℝ :=
  dens s * (alphaRate * sv T - bremsRate * Real.sqrt T) + QPoly.eval aux s

/-- The source is continuous on `[0,1] × (0,∞)`. -/
theorem srcA_continuousOn (aux : List ℚ) (sv : ℝ → ℝ) [BoschHaleDT sv] :
    ContinuousOn (fun p : ℝ × ℝ => srcA aux sv p.1 p.2) (Icc 0 1 ×ˢ Ioi 0) := by
  have hd : ContinuousOn (fun p : ℝ × ℝ => dens p.1) (Icc 0 1 ×ˢ Ioi 0) := by
    unfold dens
    refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun p hp => (w2_pos hp.1).ne')
  have hsv : ContinuousOn (fun p : ℝ × ℝ => sv p.2) (Icc 0 1 ×ˢ Ioi 0) :=
    (BoschHaleDT.continuousOn (sv := sv)).comp continuous_snd.continuousOn (fun p hp => hp.2)
  have hsq : Continuous (fun p : ℝ × ℝ => Real.sqrt p.2) := by fun_prop
  exact (hd.mul ((continuousOn_const.mul hsv).sub (continuous_const.mul hsq).continuousOn)).add
    ((QPoly.continuous_eval _).comp continuous_fst).continuousOn

/-- **Band coefficients with auxiliary heating `aux`**: the quasilinear flux-geometry
coefficients on the density-weighted geometry `G.weight n n'` with `χ = χ₀ χ̂(T)`,
`∂Tχ = χ₀ T/50` and source `srcA aux sv`, posed for `T > 0`. (`coeffsA auxSol` is
`SolovevBand.solCoeffs` up to the name of the source.) -/
@[expose] def coeffsA (aux : List ℚ) (G : FluxGeometry) (sv : ℝ → ℝ) (χ₀ : ℝ) :
    RadialCoefficients :=
  (G.weight dens ddens).qcoeffs (fun _ T => χ₀ * chiHat T) (fun _ _ => 0)
    (fun _ T => χ₀ * (T / 50)) (srcA aux sv) (Ioi 0)

/-- **The band coefficients are a kernel instance** (K2 laws) for `χ₀ ≥ 0`. -/
theorem coeffsA_transportLaws (aux : List ℚ) (G : FluxGeometry) [hG : IsSolovevGeometry G]
    (sv : ℝ → ℝ) [BoschHaleDT sv] {χ₀ : ℝ} (hχ : 0 ≤ χ₀) : TransportLaws (coeffsA aux G sv χ₀) := by
  have := weighted_laws G
  exact (G.weight dens ddens).qcoeffs_transportLaws
    (fun _ _ T => mul_nonneg hχ (chiHat_pos T).le)
    (fun _ _ _ => hasDerivWithinAt_const _ _ _)
    (fun _ _ T => (hasDerivAt_chiHat T).const_mul χ₀)
    (IsSolovevGeometry.g_nonneg G) isOpen_Ioi (srcA_continuousOn aux sv)

/-- **Kirchhoff form of the operator**:
`N[Φ⁻¹ ∘ F] = χ₀ (g F'' + (h + (n'/n) g) F') + R` on `[0,1]`. -/
theorem coeffsA_op_kProf (aux : List ℚ) (G : FluxGeometry) [hG : IsSolovevGeometry G] (sv : ℝ → ℝ)
    (χ₀ : ℝ) (F : List ℚ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (coeffsA aux G sv χ₀).op s (kProf F s) (kProf' F s) (kProf'' F s) =
      χ₀ * (G.g s * QPoly.eval (QPoly.deriv (QPoly.deriv F)) s +
        (G.h s + ddens s / dens s * G.g s) * QPoly.eval (QPoly.deriv F) s) +
        srcA aux sv s (kProf F s) := by
  have := weighted_laws G
  rw [coeffsA, FluxGeometry.qcoeffs_op _ _ _ _ _ _ hs, ← chiHat_mul_kProf'' F s,
    ← chiHat_mul_kProf' F s]
  simp only [FluxGeometry.weight]
  ring

/-- **Shift control** along Kirchhoff profiles (joint continuity of the operator on
`[0,1] × (0,∞)` along the profile). -/
theorem coeffsA_opShiftControl (aux : List ℚ) (G : FluxGeometry) [hG : IsSolovevGeometry G]
    (sv : ℝ → ℝ) [BoschHaleDT sv] (χ₀ : ℝ) (F : List ℚ)
    (hpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < kProf F s) :
    OpShiftControl (coeffsA aux G sv χ₀) (kProf F) (kProf' F) (kProf'' F) := by
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
        srcA aux sv p.1 p.2) (Icc 0 1 ×ˢ Ioi 0) := by
    have hc : Continuous fun p : ℝ × ℝ => χ₀ * chiHat p.2 := continuous_const.mul hch
    have hT : Continuous fun p : ℝ × ℝ => χ₀ * (p.2 / 50) := by fun_prop
    refine ((((hc.continuousOn.mul hgp).mul h2.continuousOn).add
      ((((continuousOn_const.mul hgp).add (hc.continuousOn.mul
        (hhp.add (hdd.mul hgp)))).add ((hT.continuousOn.mul hgp).mul
          h1.continuousOn)).mul h1.continuousOn)).add (srcA_continuousOn aux sv))
  refine hA.congr (fun p hp => ?_)
  simp only
  rw [coeffsA, FluxGeometry.qcoeffs_op _ _ _ _ _ _ hp.1]
  simp only [FluxGeometry.weight]

/-- `P · N` on a Kirchhoff profile, in corner form. -/
theorem Pw_opA (aux : List ℚ) (G : FluxGeometry) [hG : IsSolovevGeometry G] (sv : ℝ → ℝ) (χ₀ : ℝ)
    (F : List ℚ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Pw s * (coeffsA aux G sv χ₀).op s (kProf F s) (kProf' F s) (kProf'' F s) =
      χ₀ * (G.g s * (Pw s * QPoly.eval (QPoly.deriv (QPoly.deriv F)) s -
        1 / 2 * QPoly.eval (QPoly.deriv F) s) + G.h s * (Pw s * QPoly.eval (QPoly.deriv F) s)) +
      Pw s * QPoly.eval aux s + 9 / 10 * (1 - 4 / 5 * s) ^ 2 *
        (alphaRate * sv (kProf F s) - bremsRate * Real.sqrt (kProf F s)) := by
  rw [coeffsA_op_kProf aux G sv χ₀ F hs, srcA]
  have h1 := Pw_dlog hs
  have h2 := Pw_dens hs
  linear_combination (χ₀ * G.g s * QPoly.eval (QPoly.deriv F) s) * h1 +
    (alphaRate * sv (kProf F s) - bremsRate * Real.sqrt (kProf F s)) * h2

/-! ### Bremsstrahlung bounds -/

/-- `bremsRate ≥ 0.2009` (exact value `≈ 0.20094`). -/
theorem bremsRate_ge : (2009 / 10000 : ℝ) ≤ bremsRate := by
  rw [bremsRate, heatCap_eq, le_div_iff₀ (by norm_num)]; norm_num

/-- Tangent point for the square-root bounds: `1, 2, 3, 4, 5` on `[0,2]`, `(2,6]`, `(6,12]`,
`(12,20]`, `(20,∞)`. -/
@[expose] def sqM (K : ℚ) : ℚ :=
  if K ≤ 2 then 1 else if K ≤ 6 then 2 else if K ≤ 12 then 3 else if K ≤ 20 then 4 else 5

/-- The tangent point is positive. -/
theorem sqM_pos (K : ℚ) : 0 < sqM K := by
  unfold sqM; split_ifs <;> norm_num

/-- Upper bound for `√T` on `T ≤ K`: the tangent line `(K + m²)/(2m)`, `m = sqM K`. -/
@[expose] def sqB (K : ℚ) : ℚ := (K + sqM K ^ 2) / (2 * sqM K)

/-- Lower bound for `√T` on `T ≥ k ≥ 0`: `2mk/(k + m²)`, `m = sqM k`. -/
@[expose] def sqL (k : ℚ) : ℚ := 2 * sqM k * k / (k + sqM k ^ 2)

/-- AM–GM: `2 m √T ≤ T + m²`. -/
theorem two_mul_sqrt_le {T m : ℝ} (hT : 0 ≤ T) : 2 * m * Real.sqrt T ≤ T + m ^ 2 := by
  nlinarith [sq_nonneg (Real.sqrt T - m), Real.sq_sqrt hT]

/-- **Square-root ceiling.** `0 ≤ T ≤ K ⇒ √T ≤ sqB K`. -/
theorem sqrt_le_sqB {T : ℝ} {K : ℚ} (h0 : 0 ≤ T) (hTK : T ≤ K) :
    Real.sqrt T ≤ (sqB K : ℝ) := by
  have hm : (0 : ℝ) < sqM K := by exact_mod_cast sqM_pos K
  have h := two_mul_sqrt_le (m := (sqM K : ℝ)) h0
  unfold sqB; push_cast
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- **Square-root floor.** `0 ≤ k ≤ T ⇒ sqL k ≤ √T`. -/
theorem sqL_le_sqrt {T : ℝ} {k : ℚ} (h0 : 0 ≤ k) (hkT : (k : ℝ) ≤ T) :
    (sqL k : ℝ) ≤ Real.sqrt T := by
  have hm : (0 : ℝ) < sqM k := by exact_mod_cast sqM_pos k
  have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast h0
  have h := two_mul_sqrt_le (m := (sqM k : ℝ)) hk0
  have hs := Real.sq_sqrt hk0
  have hsk : Real.sqrt k ≤ Real.sqrt T := Real.sqrt_le_sqrt hkT
  have hsq0 := Real.sqrt_nonneg (k : ℝ)
  unfold sqL; push_cast
  rw [div_le_iff₀ (by positivity)]
  have : 2 * (sqM k : ℝ) * k ≤ Real.sqrt k * (k + (sqM k : ℝ) ^ 2) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hsk (by positivity : (0 : ℝ) ≤ k + (sqM k : ℝ) ^ 2)]

/-- `sqL k ≥ 0` for `k ≥ 0`. -/
theorem sqL_nonneg {k : ℚ} (h0 : 0 ≤ k) : 0 ≤ sqL k := by
  have := sqM_pos k
  unfold sqL; positivity

/-! ### Certificate polynomials -/

/-- Lower-barrier bonus: fine alpha floor at `k` minus the bremsstrahlung ceiling
`0.201 sqB K`. -/
@[expose] def lowBonusF (k K : ℚ) : ℚ := 229 / 10 * 10 ^ 21 * svFloorF k - 201 / 1000 * sqB K

/-- Upper-barrier bonus: fine alpha ceiling at `K` minus the bremsstrahlung floor
`0.2009 sqL k`. -/
@[expose] def upBonusF (k K : ℚ) : ℚ := 2291 / 100 * 10 ^ 21 * svCeilF K - 2009 / 10000 * sqL k

/-- Lower-barrier polynomial at a corner, labels `(k, K)`:
`condS(χ, γ, 0.525) + P q_aux + Pnu · lowBonusF k K`. -/
@[expose] def lowA (aux : List ℚ) (F : List ℚ) (χ γ : ℚ) (k K : ℚ) : List ℚ :=
  QPoly.add (QPoly.add (condS F χ γ (21 / 40)) (QPoly.mul Ppoly aux))
    (QPoly.scale (lowBonusF k K) Pnu)

/-- Upper-barrier polynomial at a corner, labels `(k, K)`:
`−(condS(χ, γ, 0.49) + P q_aux + Pnu · upBonusF k K)`. -/
@[expose] def upA (aux : List ℚ) (F : List ℚ) (χ γ : ℚ) (k K : ℚ) : List ℚ :=
  QPoly.scale (-1) (QPoly.add (QPoly.add (condS F χ γ (49 / 100)) (QPoly.mul Ppoly aux))
    (QPoly.scale (upBonusF k K) Pnu))

/-- Pressure polynomial for the label `K` and offset `Δ`:
`(Δ + 456900 (1 − 11s/12))(1 − 3s/10) − 0.9·10²⁰ (113/60) K keV (1 − 4s/5)`. -/
@[expose] def presD (Δ : ℚ) (_k K : ℚ) : List ℚ :=
  QPoly.add (QPoly.mul (QPoly.add [Δ] (QPoly.scale 456900 wp)) w2)
    (QPoly.scale (-(9 / 10 * 10 ^ 20 * (113 / 60) * K * keVQ)) w1)

/-- Evaluation of `P q_aux`. -/
theorem PauxA_eval (aux : List ℚ) (s : ℝ) :
    QPoly.eval (QPoly.mul Ppoly aux) s = Pw s * QPoly.eval aux s := by
  simp only [QPoly.eval_mul, Ppoly, w1, w2, QPoly.eval_cons, QPoly.eval_nil, Pw]
  push_cast; ring

/-- Evaluation of the pressure polynomial. -/
theorem presD_eval (Δ k K : ℚ) (s : ℝ) : QPoly.eval (presD Δ k K) s =
    (Δ + 456900 * (1 - 11 / 12 * s)) * (1 - 3 / 10 * s) -
      9 / 10 * 10 ^ 20 * (113 / 60) * K * (1602176634 / 10 ^ 25) * (1 - 4 / 5 * s) := by
  simp [presD, wp, w1, w2, keVQ]; ring

/-! ### Generic profile facts -/

/-- A monotonicity certificate makes `F` antitone on `[0,1]`. -/
theorem antitone_of_deriv_check {F : List ℚ}
    (h : QPoly.checkOn (QPoly.scale (-1) (QPoly.deriv F)) 0 0 1 (gridN 8) = true) :
    AntitoneOn (QPoly.eval F) (Icc 0 1) := by
  have := antitoneOn_eval_of_check h
  intro a ha b hb hab; exact this (by simpa using ha) (by simpa using hb) hab

/-- Edge value: `F(1) = Φ(a)` gives `Φ⁻¹(F(1)) = a`. -/
theorem kProf_one {F : List ℚ} {a : ℚ} (h : QPoly.evalQ F 1 = kirchhoffQ a) :
    kProf F 1 = a := by
  have : QPoly.eval F ((1 : ℚ) : ℝ) = kirchhoff ((a : ℚ) : ℝ) := by
    rw [eval_ratCast, h, kirchhoffQ_cast]
  simp only [kProf]; push_cast at this; rw [this, kirchhoffInv_kirchhoff]

/-- Lower bound: for antitone `F` with `F(1) = Φ(a)`, `a ≤ Φ⁻¹(F(s))` on `[0,1]`. -/
theorem le_kProf_of_edge {F : List ℚ} (hF : AntitoneOn (QPoly.eval F) (Icc 0 1)) {a : ℚ}
    (h : QPoly.evalQ F 1 = kirchhoffQ a) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (a : ℝ) ≤ kProf F s := by
  have hm := hF hs ⟨zero_le_one, le_rfl⟩ hs.2
  rw [show (1 : ℝ) = ((1 : ℚ) : ℝ) by norm_num, eval_ratCast, h, kirchhoffQ_cast] at hm
  exact le_kirchhoffInv_iff.2 hm

/-- Upper bound: for antitone `F` with `F(0) ≤ Φ(b)`, `Φ⁻¹(F(s)) ≤ b` on `[0,1]`. -/
theorem kProf_le_of_axis {F : List ℚ} (hF : AntitoneOn (QPoly.eval F) (Icc 0 1)) {b : ℚ}
    (h : QPoly.evalQ F 0 ≤ kirchhoffQ b) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    kProf F s ≤ b := by
  have hm := hF ⟨le_rfl, zero_le_one⟩ hs hs.1
  rw [show (0 : ℝ) = ((0 : ℚ) : ℝ) by norm_num, eval_ratCast] at hm
  have h' : ((QPoly.evalQ F 0 : ℚ) : ℝ) ≤ kirchhoff b := by
    rw [← kirchhoffQ_cast]; exact_mod_cast h
  exact kirchhoffInv_le_iff.2 (hm.trans h')

/-- Core bound: for antitone `F` with `Φ(c) ≤ F(x₀)`, `c ≤ Φ⁻¹(F(s))` on `[0, x₀] ⊆ [0,1]`. -/
theorem le_kProf_of_core {F : List ℚ} (hF : AntitoneOn (QPoly.eval F) (Icc 0 1)) {c x₀ : ℚ}
    (hx : (x₀ : ℝ) ≤ 1) (h : kirchhoffQ c ≤ QPoly.evalQ F x₀) {s : ℝ} (h0 : 0 ≤ s)
    (h1 : s ≤ x₀) : (c : ℝ) ≤ kProf F s := by
  have hm := hF ⟨h0, h1.trans hx⟩ ⟨h0.trans h1, hx⟩ h1
  rw [eval_ratCast] at hm
  have h' : kirchhoff c ≤ ((QPoly.evalQ F x₀ : ℚ) : ℝ) := by
    rw [← kirchhoffQ_cast]; exact_mod_cast h
  exact le_kirchhoffInv_iff.2 (h'.trans hm)

/-! ### Generic margins -/

/-- **Generic lower-barrier margin.** If the four corner certificates of `lowA aux F`
(`χ ∈ {χL, χH}`, `γ ∈ {0.49, 0.525}`, margin `κ ≥ 0`) pass on the pieces `ps`, the lower
labels are `≥ 0`, `F` is certified antitone and `1 ≤ Φ⁻¹ ∘ F ≤ 60`, then for every geometry in
`IsSolovevGeometry`, every fine supplied reactivity and every `χ₀ ∈ [χL, χH]`,
`N[Φ⁻¹ ∘ F] ≥ κ` on `[0,1]`. -/
theorem tsub_margin_gen (aux F : List ℚ) (ps : List (ℚ × ℚ × ℚ)) {χL χH κ : ℚ}
    (hκ : 0 ≤ κ) (hχL : 0 ≤ χL)
    (c1 : pieceCheckL (lowA aux F χL (49 / 100)) F kirchhoffQ κ 0 ps = true)
    (c2 : pieceCheckL (lowA aux F χL (21 / 40)) F kirchhoffQ κ 0 ps = true)
    (c3 : pieceCheckL (lowA aux F χH (49 / 100)) F kirchhoffQ κ 0 ps = true)
    (c4 : pieceCheckL (lowA aux F χH (21 / 40)) F kirchhoffQ κ 0 ps = true)
    (hne : ps ≠ []) (hl : ∀ p ∈ ps, 0 ≤ p.2.1) (hend : pieceEnd2 0 ps = 1)
    (hd : QPoly.checkOn (QPoly.scale (-1) (QPoly.deriv F)) 0 0 1 (gridN 8) = true)
    (hT : ∀ s ∈ Icc (0 : ℝ) 1, 1 ≤ kProf F s ∧ kProf F s ≤ 60)
    (G : FluxGeometry) [hG : IsSolovevGeometry G] (sv : ℝ → ℝ) [BoschHaleFine sv] {χ₀ : ℝ}
    (h1 : (χL : ℝ) ≤ χ₀) (h2 : χ₀ ≤ χH) :
    ∀ s ∈ Icc (0 : ℝ) 1, (κ : ℝ) ≤
      (coeffsA aux G sv χ₀).op s (kProf F s) (kProf' F s) (kProf'' F s) := by
  intro s hs
  have hF := antitone_of_deriv_check hd
  obtain ⟨hP0, hP1⟩ := Pw_bounds hs
  set X := Pw s * QPoly.eval (QPoly.deriv (QPoly.deriv F)) s -
    1 / 2 * QPoly.eval (QPoly.deriv F) s with hX
  set Y := Pw s * QPoly.eval (QPoly.deriv F) s with hY
  have hY0 : Y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hP0.le (deriv_nonpos_of_check hd hs)
  set src := alphaRate * sv (kProf F s) - bremsRate * Real.sqrt (kProf F s) with hsrc
  set L := (κ : ℝ) - Pw s * QPoly.eval aux s - 9 / 10 * (1 - 4 / 5 * s) ^ 2 * src with hL
  have hw0 : 0 ≤ 9 / 10 * (1 - 4 / 5 * s) ^ 2 := by positivity
  have corner : ∀ χ γ : ℚ, pieceCheckL (lowA aux F χ γ) F kirchhoffQ κ 0 ps = true →
      L ≤ (χ : ℝ) * ((γ : ℝ) * (s * X) + 21 / 40 * Y) := by
    intro χ γ hc
    obtain ⟨k, K, ⟨d, hmem⟩, hk, hK, hQ⟩ := pieceL_at hc hne hend hF hs
    obtain ⟨hT1, hT60⟩ := hT s hs
    have hfl := svFloorF_le sv (hl _ hmem) hk hT60
    have hsv0 : 0 ≤ sv (kProf F s) := BoschHaleDT.nonneg _ (by linarith)
    have hα : (229 / 10 * 10 ^ 21 : ℝ) * svFloorF k ≤ alphaRate * sv (kProf F s) :=
      (mul_le_mul_of_nonneg_left hfl (by norm_num)).trans
        (mul_le_mul_of_nonneg_right alphaRate_ge hsv0)
    have hsq := sqrt_le_sqB (T := kProf F s) (K := K) (by linarith) hK
    have hbr : bremsRate * Real.sqrt (kProf F s) ≤ 201 / 1000 * (sqB K : ℝ) :=
      mul_le_mul bremsRate_le hsq (Real.sqrt_nonneg _) (by norm_num)
    have hb : ((lowBonusF k K : ℚ) : ℝ) ≤ src := by
      simp only [lowBonusF]; push_cast; rw [hsrc]; linarith
    have hQ' := hQ
    simp only [lowA, QPoly.eval_add, QPoly.eval_scale, condS_eval, PauxA_eval, Pnu_eval] at hQ'
    push_cast at hQ'
    rw [← hX, ← hY] at hQ'
    have := mul_le_mul_of_nonneg_left hb hw0
    nlinarith
  have hmin := bilin_lower (s := s) (g := G.g s) (h := G.h s) (X := X) (Y := Y) (χ₀ := χ₀)
    (χL := χL) (χH := χH) (γL := 49 / 100) (γU := 21 / 40) (hU := 21 / 40)
    (hG.g_lower s hs) (hG.g_upper s hs) (hG.h_upper s hs) hY0 (by exact_mod_cast hχL) h1 h2
  have e1 := corner χL (49 / 100) c1
  have e2 := corner χL (21 / 40) c2
  have e3 := corner χH (49 / 100) c3
  have e4 := corner χH (21 / 40) c4
  push_cast at e1 e2 e3 e4
  have hcon : L ≤ χ₀ * (G.g s * X + G.h s * Y) :=
    (le_min (le_min e1 e2) (le_min e3 e4)).trans hmin
  have hPop := Pw_opA aux G sv χ₀ F hs
  rw [← hX, ← hY] at hPop
  set N := (coeffsA aux G sv χ₀).op s (kProf F s) (kProf' F s) (kProf'' F s)
  have hPN : (κ : ℝ) ≤ Pw s * N := by rw [hPop]; change _ ≤ _ + _ + _ * src; linarith
  have hκ' : (0 : ℝ) ≤ κ := by exact_mod_cast hκ
  nlinarith

/-- **Generic upper-barrier margin.** If the four corner certificates of `upA aux F` pass on
the pieces `ps`, every upper label ends a supplied window with `K ≤ 60` and every lower
label is `≥ 0`, `F` is certified antitone and `Φ⁻¹ ∘ F ≥ 1`, then for every geometry in
`IsSolovevGeometry`, every fine supplied reactivity and every `χ₀ ∈ [χL, χH]`,
`N[Φ⁻¹ ∘ F] ≤ −κ` on `[0,1]`. -/
theorem tsup_margin_gen (aux F : List ℚ) (ps : List (ℚ × ℚ × ℚ)) {χL χH κ : ℚ}
    (hκ : 0 ≤ κ) (hχL : 0 ≤ χL)
    (c1 : pieceCheckL (upA aux F χL (49 / 100)) F kirchhoffQ κ 0 ps = true)
    (c2 : pieceCheckL (upA aux F χL (21 / 40)) F kirchhoffQ κ 0 ps = true)
    (c3 : pieceCheckL (upA aux F χH (49 / 100)) F kirchhoffQ κ 0 ps = true)
    (c4 : pieceCheckL (upA aux F χH (21 / 40)) F kirchhoffQ κ 0 ps = true)
    (hne : ps ≠ []) (hu : ∀ p ∈ ps, ceilOK p.2.2 = true ∧ p.2.2 ≤ 60 ∧ 0 ≤ p.2.1)
    (hend : pieceEnd2 0 ps = 1)
    (hd : QPoly.checkOn (QPoly.scale (-1) (QPoly.deriv F)) 0 0 1 (gridN 8) = true)
    (hT : ∀ s ∈ Icc (0 : ℝ) 1, 1 ≤ kProf F s)
    (G : FluxGeometry) [hG : IsSolovevGeometry G] (sv : ℝ → ℝ) [BoschHaleFine sv] {χ₀ : ℝ}
    (h1 : (χL : ℝ) ≤ χ₀) (h2 : χ₀ ≤ χH) :
    ∀ s ∈ Icc (0 : ℝ) 1,
      (coeffsA aux G sv χ₀).op s (kProf F s) (kProf' F s) (kProf'' F s) ≤ -(κ : ℝ) := by
  intro s hs
  have hF := antitone_of_deriv_check hd
  obtain ⟨hP0, hP1⟩ := Pw_bounds hs
  set X := Pw s * QPoly.eval (QPoly.deriv (QPoly.deriv F)) s -
    1 / 2 * QPoly.eval (QPoly.deriv F) s with hX
  set Y := Pw s * QPoly.eval (QPoly.deriv F) s with hY
  have hY0 : Y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hP0.le (deriv_nonpos_of_check hd hs)
  set src := alphaRate * sv (kProf F s) - bremsRate * Real.sqrt (kProf F s) with hsrc
  set U := -(κ : ℝ) - Pw s * QPoly.eval aux s - 9 / 10 * (1 - 4 / 5 * s) ^ 2 * src with hU
  have hw0 : 0 ≤ 9 / 10 * (1 - 4 / 5 * s) ^ 2 := by positivity
  have corner : ∀ χ γ : ℚ, pieceCheckL (upA aux F χ γ) F kirchhoffQ κ 0 ps = true →
      (χ : ℝ) * ((γ : ℝ) * (s * X) + 49 / 100 * Y) ≤ U := by
    intro χ γ hc
    obtain ⟨k, K, ⟨d, hmem⟩, hk, hK, hQ⟩ := pieceL_at hc hne hend hF hs
    have hT1 := hT s hs
    obtain ⟨hw, hK60, hk0⟩ := hu _ hmem
    have hsv := sv_le_svCeilF sv hw hK60 hT1 hK
    have hsv0 : 0 ≤ sv (kProf F s) := BoschHaleDT.nonneg _ (by linarith)
    have hα : alphaRate * sv (kProf F s) ≤ 2291 / 100 * 10 ^ 21 * svCeilF K :=
      mul_le_mul alphaRate_le hsv hsv0 (by norm_num)
    have hsq := sqL_le_sqrt (T := kProf F s) hk0 hk
    have hbr : 2009 / 10000 * (sqL k : ℝ) ≤ bremsRate * Real.sqrt (kProf F s) :=
      mul_le_mul bremsRate_ge hsq (by exact_mod_cast sqL_nonneg hk0) bremsRate_nonneg
    have hb : src ≤ ((upBonusF k K : ℚ) : ℝ) := by
      simp only [upBonusF]; push_cast; rw [hsrc]; linarith
    have hQ' := hQ
    simp only [upA, QPoly.eval_add, QPoly.eval_scale, condS_eval, PauxA_eval, Pnu_eval] at hQ'
    push_cast at hQ'
    rw [← hX, ← hY] at hQ'
    have := mul_le_mul_of_nonneg_left hb hw0
    nlinarith
  have hmax := bilin_upper (s := s) (g := G.g s) (h := G.h s) (X := X) (Y := Y) (χ₀ := χ₀)
    (χL := χL) (χH := χH) (γL := 49 / 100) (γU := 21 / 40) (hL := 49 / 100)
    (hG.g_lower s hs) (hG.g_upper s hs) (hG.h_lower s hs) hY0 (by exact_mod_cast hχL) h1 h2
  have e1 := corner χL (49 / 100) c1
  have e2 := corner χL (21 / 40) c2
  have e3 := corner χH (49 / 100) c3
  have e4 := corner χH (21 / 40) c4
  push_cast at e1 e2 e3 e4
  have hcon : χ₀ * (G.g s * X + G.h s * Y) ≤ U :=
    hmax.trans (max_le (max_le e1 e2) (max_le e3 e4))
  have hPop := Pw_opA aux G sv χ₀ F hs
  rw [← hX, ← hY] at hPop
  set N := (coeffsA aux G sv χ₀).op s (kProf F s) (kProf' F s) (kProf'' F s)
  have hPN : Pw s * N ≤ -(κ : ℝ) := by rw [hPop]; change _ + _ + _ * src ≤ _; linarith
  have hκ' : (0 : ℝ) ≤ κ := by exact_mod_cast hκ
  nlinarith

/-! ### Generic pressure ceiling and band -/

/-- **Generic pressure certificate.** If `pieceCheckL (presD Δ)` passes for `F` on `ps`, `F`
is certified antitone and `Φ⁻¹ ∘ F ≥ 0`, then
`n(s) (1 + 53/60) Φ⁻¹(F(s)) keV ≤ p_eq(s) + Δ` on `[0,1]` for reactor `μ₀`. -/
theorem pressure_gen (Δ : ℚ) (F : List ℚ) (ps : List (ℚ × ℚ × ℚ))
    (hc : pieceCheckL (presD Δ) F kirchhoffQ 0 0 ps = true) (hne : ps ≠ [])
    (hend : pieceEnd2 0 ps = 1)
    (hd : QPoly.checkOn (QPoly.scale (-1) (QPoly.deriv F)) 0 0 1 (gridN 8) = true)
    (hT : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ kProf F s) {μ₀ : ℝ} (hμ1 : 1.2566e-6 ≤ μ₀)
    (hμ2 : μ₀ ≤ 1.2567e-6) :
    ∀ s ∈ Icc (0 : ℝ) 1, nProf s * (1 + 53 / 60) * kProf F s * keV ≤ peqLabel μ₀ Δ s := by
  intro s hs
  obtain ⟨k, K, ⟨d, hmem⟩, -, hK, hQ⟩ := pieceL_at hc hne hend (antitone_of_deriv_check hd) hs
  rw [presD_eval] at hQ
  push_cast at hQ
  have hpeq := (peqLabel_bounds hμ1 hμ2 Δ hs).1
  have hw2 := w2_pos hs
  have hT0 := hT s hs
  have hw1 : 0 ≤ 1 - 4 / 5 * s := by linarith [hs.2]
  have hc : (0 : ℝ) ≤ 9 / 10 * 10 ^ 20 * (113 / 60) * (1602176634 / 10 ^ 25) * (1 - 4 / 5 * s) :=
    by positivity
  have hmono := mul_le_mul_of_nonneg_left hK hc
  have hkeV : keV = 1602176634 / 10 ^ 25 := by norm_num [keV]
  have e : nProf s * (1 + 53 / 60) * kProf F s * keV * (1 - 3 / 10 * s) =
      9 / 10 * 10 ^ 20 * (113 / 60) * (1602176634 / 10 ^ 25) * (1 - 4 / 5 * s) * kProf F s := by
    rw [hkeV]; unfold nProf dens
    have h10 : (10 : ℝ) - s * 3 ≠ 0 := by intro h; linarith [hs.2]
    field_simp
    ring
  have : nProf s * (1 + 53 / 60) * kProf F s * keV * (1 - 3 / 10 * s) ≤
      ((Δ : ℝ) + 456900 * (1 - 11 / 12 * s)) * (1 - 3 / 10 * s) := by
    rw [e]; nlinarith
  have := le_of_mul_le_mul_right this hw2
  linarith

/-- **Generic two-sided band for all time.** If `Φ⁻¹ ∘ F_sub` and `Φ⁻¹ ∘ F_sup` are positive on
`[0,1]`, take the edge values `1` and `3/2`, and satisfy the margins `N ≥ κ`, `N ≤ −κ`
(`κ > 0`) for the coefficients `coeffsA aux G sv χ₀`, `χ₀ ≥ 0`, then every kernel solution on
all horizons with edge temperature in `[1, 3/2]` keV starting between them stays between them
for all `t ≥ 0`. -/
theorem band_gen (aux fs fu : List ℚ) {κ : ℝ} (hκ : 0 < κ) (G : FluxGeometry)
    [hG : IsSolovevGeometry G] (sv : ℝ → ℝ) [BoschHaleDT sv] {χ₀ : ℝ} (hχ : 0 ≤ χ₀)
    (hpl : ∀ s ∈ Icc (0 : ℝ) 1, 0 < kProf fs s) (hpu : ∀ s ∈ Icc (0 : ℝ) 1, 0 < kProf fu s)
    (hel : kProf fs 1 = 1) (heu : kProf fu 1 = 3 / 2)
    (hml : ∀ s ∈ Icc (0 : ℝ) 1, κ ≤ (coeffsA aux G sv χ₀).op s (kProf fs s) (kProf' fs s)
      (kProf'' fs s))
    (hmu : ∀ s ∈ Icc (0 : ℝ) 1, (coeffsA aux G sv χ₀).op s (kProf fu s) (kProf' fu s)
      (kProf'' fu s) ≤ -κ)
    {Tedge : ℝ → ℝ} {u : RadialField}
    (hu : ∀ τ, 0 ≤ τ → ClassicalRadialSolution (coeffsA aux G sv χ₀) Tedge τ u)
    (h0 : ∀ s ∈ Icc (0 : ℝ) 1, kProf fs s ≤ u.T s 0 ∧ u.T s 0 ≤ kProf fu s)
    (hedge : ∀ t, 0 ≤ t → 1 ≤ Tedge t ∧ Tedge t ≤ 3 / 2) :
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → kProf fs s ≤ u.T s t ∧ u.T s t ≤ kProf fu s := by
  have hL := coeffsA_transportLaws aux G sv hχ
  have hk : (coeffsA aux G sv χ₀).axis = .regular → False := fun h => by
    simp [coeffsA, FluxGeometry.qcoeffs] at h
  have hlow : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → kProf fs s ≤ u.T s t :=
    le_of_lowerMargin_shift_forall_time (fun τ hτ => { hL, hu τ hτ with })
      (kProf_regular fs) (fun h => (hk h).elim)
      (coeffsA_opShiftControl aux G sv χ₀ fs hpl) hκ hml (fun s hs => (h0 s hs).1)
      (fun t ht => by rw [hel]; exact (hedge t ht).1)
  have hup : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → u.T s t ≤ kProf fu s :=
    le_of_upperMargin_shift_forall_time (fun τ hτ => { hL, hu τ hτ with })
      (kProf_regular fu) (fun h => (hk h).elim)
      (coeffsA_opShiftControl aux G sv χ₀ fu hpu) hκ hmu (fun s hs => (h0 s hs).2)
      (fun t ht => by rw [heu]; exact (hedge t ht).2)
  exact fun s hs t ht => ⟨hlow s hs t ht, hup s hs t ht⟩

/-! ### high Q: barrier data (Python oracle `/tmp/k4/run2.py`, untrusted; checked below) -/

/-- Auxiliary heating rate `q_aux(s) = 2 (1 − s)⁶` keV/s (≈ 17.5 MW, oracle). -/
@[expose] def highQ_aux : List ℚ := [2, -12, 30, -40, 30, -12, 2]

/-- Level function of the lower barrier, `F_sub = Φ(T_sub)`. -/
@[expose] def highQ_fs : List ℚ :=
  [10802573/1500000, -11005303/1000000, 9586573/1000000, -14059579/1000000, 8658799/200000,
   -83027191/500000, 117656279/250000, -913600881/1000000, 239699923/200000, -1039628131/1000000,
   70757429/125000, -21591867/125000, 21920099/1000000]

/-- Level function of the upper barrier, `F_sup = Φ(T_sup)`. -/
@[expose] def highQ_fu : List ℚ :=
  [10888117/500000, -24297659/1000000, 10294873/1000000, -18702091/1000000, 40949531/500000,
   -190209713/500000, 122009729/100000, -330873419/125000, 968447601/250000, -3763630051/1000000,
   579621957/250000, -408140083/500000, 7758269/62500]

/-- Pieces of the lower-barrier certificates (lower labels on the fine grid). -/
@[expose] def highQ_subP : List (ℚ × ℚ × ℚ) :=
  [(223/10000, 12, 61/5), (59/1000, 47/4, 241/20), (241/2500, 23/2, 59/5), (1343/10000, 45/4,
   231/20), (1727/10000, 11, 113/10), (2113/10000, 43/4, 221/20), (1251/5000, 21/2, 54/5),
   (2891/10000, 41/4, 211/20), (3279/10000, 10, 103/10), (229/625, 39/4, 201/20), (1011/2500,
   19/2, 49/5), (4419/10000, 37/4, 191/20), (957/2000, 9, 93/10), (2571/5000, 35/4, 181/20),
   (5487/10000, 17/2, 44/5), (5821/10000, 33/4, 171/20), (3071/5000, 8, 83/10), (403/625, 31/4,
   161/20), (337/500, 15/2, 39/5), (877/1250, 29/4, 151/20), (1819/2500, 7, 73/10), (7521/10000,
   27/4, 141/20), (31/40, 13/2, 34/5), (1991/2500, 25/4, 131/20), (4081/5000, 6, 63/10),
   (4173/5000, 23/4, 121/20), (8517/10000, 11/2, 29/5), (8673/10000, 21/4, 111/20), (4409/5000, 5,
   53/10), (2321/2500, 4, 101/20), (9609/10000, 3, 81/20), (2459/2500, 2, 61/20), (1, 1, 41/20)]

/-- Pieces of the upper-barrier certificates (upper labels end supplied windows). -/
@[expose] def highQ_supP : List (ℚ × ℚ × ℚ) :=
  [(223/10000, 359/20, 73/4), (573/10000, 177/10, 18), (461/5000, 349/20, 71/4), (1269/10000,
   86/5, 35/2), (1613/10000, 339/20, 69/4), (977/5000, 167/10, 17), (2291/10000, 329/20, 67/4),
   (2623/10000, 81/5, 33/2), (59/200, 319/20, 65/4), (3271/10000, 157/10, 16), (1793/5000, 309/20,
   63/4), (3893/10000, 76/5, 31/2), (4193/10000, 299/20, 61/4), (897/2000, 147/10, 15), (298/625,
   289/20, 59/4), (1261/2500, 71/5, 29/2), (531/1000, 279/20, 57/4), (348/625, 137/10, 14),
   (727/1250, 269/20, 55/4), (1211/2000, 66/5, 27/2), (1257/2000, 259/20, 53/4), (1301/2000,
   127/10, 13), (6717/10000, 249/20, 51/4), (6919/10000, 61/5, 25/2), (7111/10000, 239/20, 49/4),
   (1459/2000, 117/10, 12), (747/1000, 229/20, 47/4), (7637/10000, 56/5, 23/2), (1559/2000,
   219/20, 45/4), (1589/2000, 107/10, 11), (8087/10000, 209/20, 43/4), (8221/10000, 51/5, 21/2),
   (8347/10000, 199/20, 41/4), (8467/10000, 97/10, 10), (429/500, 189/20, 39/4), (4343/5000, 46/5,
   19/2), (4393/5000, 179/20, 37/4), (111/125, 87/10, 9), (1121/1250, 169/20, 35/4), (181/200,
   41/5, 17/2), (1141/1250, 159/20, 33/4), (23/25, 77/10, 8), (2317/2500, 149/20, 31/4),
   (9331/10000, 36/5, 15/2), (939/1000, 139/20, 29/4), (4723/5000, 67/10, 7), (9497/10000, 129/20,
   27/4), (1909/2000, 31/5, 13/2), (9589/10000, 119/20, 25/4), (963/1000, 57/10, 6), (9669/10000,
   109/20, 23/4), (1213/1250, 26/5, 11/2), (9737/10000, 99/20, 21/4), (1969/2000, 79/20, 5),
   (4961/5000, 59/20, 4), (4989/5000, 39/20, 3), (1, 3/2, 2)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
-- The literal list of rationals is long; its elaboration exceeds the default heartbeats.
/-- Pieces of the pressure certificate (upper labels in `1/8 keV`). -/
@[expose] def highQ_presP : List (ℚ × ℚ × ℚ) :=
  [(3/625, 0, 73/4), (223/10000, 0, 145/8), (199/5000, 0, 18), (573/10000, 0, 143/8), (187/2500,
   0, 71/4), (461/5000, 0, 141/8), (219/2000, 0, 35/2), (1269/10000, 0, 139/8), (1441/10000, 0,
   69/4), (1613/10000, 0, 137/8), (223/1250, 0, 17), (977/5000, 0, 135/8), (2123/10000, 0, 67/4),
   (2291/10000, 0, 133/8), (1229/5000, 0, 33/2), (2623/10000, 0, 131/8), (697/2500, 0, 65/4),
   (59/200, 0, 129/8), (389/1250, 0, 16), (3271/10000, 0, 127/8), (3429/10000, 0, 63/4),
   (1793/5000, 0, 125/8), (187/500, 0, 31/2), (3893/10000, 0, 123/8), (1011/2500, 0, 61/4),
   (4193/10000, 0, 121/8), (217/500, 0, 15), (897/2000, 0, 119/8), (1157/2500, 0, 59/4), (298/625,
   0, 117/8), (4907/10000, 0, 29/2), (1261/2500, 0, 115/8), (2589/5000, 0, 57/4), (531/1000, 0,
   113/8), (68/125, 0, 14), (348/625, 0, 111/8), (5693/10000, 0, 55/4), (727/1250, 0, 109/8),
   (5937/10000, 0, 27/2), (1211/2000, 0, 107/8), (6171/10000, 0, 53/4), (1257/2000, 0, 105/8),
   (1599/2500, 0, 13), (1301/2000, 0, 103/8), (1653/2500, 0, 51/4), (6717/10000, 0, 101/8),
   (6819/10000, 0, 25/2), (6919/10000, 0, 99/8), (877/1250, 0, 49/4), (7111/10000, 0, 97/8),
   (1441/2000, 0, 12), (1459/2000, 0, 95/8), (923/1250, 0, 47/4), (747/1000, 0, 93/8), (1511/2000,
   0, 23/2), (7637/10000, 0, 91/8), (7717/10000, 0, 45/4), (1559/2000, 0, 89/8), (7871/10000, 0,
   11), (1589/2000, 0, 87/8), (8017/10000, 0, 43/4), (8087/10000, 0, 85/8), (1631/2000, 0, 21/2),
   (8221/10000, 0, 83/8), (1657/2000, 0, 41/4), (8347/10000, 0, 81/8), (1051/1250, 0, 10),
   (8467/10000, 0, 79/8), (2131/2500, 0, 39/4), (429/500, 0, 77/8), (4317/5000, 0, 19/2),
   (4343/5000, 0, 75/8), (8737/10000, 0, 37/4), (4393/5000, 0, 73/8), (8833/10000, 0, 9),
   (111/125, 0, 71/8), (2231/2500, 0, 35/4), (1121/1250, 0, 69/8), (901/1000, 0, 17/2), (181/200,
   0, 67/8), (909/1000, 0, 33/4), (1141/1250, 0, 65/8), (1833/2000, 0, 8), (23/25, 0, 63/8),
   (1847/2000, 0, 31/4), (2317/2500, 0, 61/8), (93/100, 0, 15/2), (9331/10000, 0, 59/8),
   (9361/10000, 0, 29/4), (939/1000, 0, 57/8), (4709/5000, 0, 7), (4723/5000, 0, 55/8), (592/625,
   0, 27/4), (9497/10000, 0, 53/8), (9521/10000, 0, 13/2), (1909/2000, 0, 51/8), (9567/10000, 0,
   25/4), (9589/10000, 0, 49/8), (961/1000, 0, 6), (963/1000, 0, 47/8), (193/200, 0, 23/4),
   (9669/10000, 0, 45/8), (9687/10000, 0, 11/2), (1213/1250, 0, 43/8), (9721/10000, 0, 21/4),
   (9737/10000, 0, 41/8), (1219/1250, 0, 5), (9767/10000, 0, 39/8), (9781/10000, 0, 19/4),
   (1959/2000, 0, 37/8), (613/625, 0, 9/2), (9821/10000, 0, 35/8), (9833/10000, 0, 17/4),
   (1969/2000, 0, 33/8), (616/625, 0, 4), (9867/10000, 0, 31/8), (9877/10000, 0, 15/4),
   (9887/10000, 0, 29/8), (1237/1250, 0, 7/2), (1981/2000, 0, 27/8), (4957/5000, 0, 13/4),
   (4961/5000, 0, 25/8), (993/1000, 0, 3), (4969/5000, 0, 23/8), (4973/5000, 0, 11/4),
   (9953/10000, 0, 21/8), (9959/10000, 0, 5/2), (4983/5000, 0, 19/8), (2493/2500, 0, 9/4),
   (4989/5000, 0, 17/8), (624/625, 0, 2), (999/1000, 0, 15/8), (1999/2000, 0, 7/4), (1, 0, 13/8)]

/-- The lower barrier `T_sub = Φ⁻¹ ∘ F_sub`. -/
@[expose] def highQ_Tsub (s : ℝ) : ℝ := kProf highQ_fs s

/-- The upper barrier `T_sup = Φ⁻¹ ∘ F_sup`. -/
@[expose] def highQ_Tsup (s : ℝ) : ℝ := kProf highQ_fu s

/-! ### high Q: certificates (each evaluated once) -/

/-- Lower barrier, corner `χ₀ = 39 / 50`, `γ = 0.49`. -/
theorem highQ_sub_check_ll :
    pieceCheckL (lowA highQ_aux highQ_fs (39 / 50) (49 / 100)) highQ_fs
      kirchhoffQ (1 / 200) 0 highQ_subP = true := by
  decide +kernel
/-- Lower barrier, corner `χ₀ = 39 / 50`, `γ = 0.525`. -/
theorem highQ_sub_check_lu :
    pieceCheckL (lowA highQ_aux highQ_fs (39 / 50) (21 / 40)) highQ_fs
      kirchhoffQ (1 / 200) 0 highQ_subP = true := by
  decide +kernel
/-- Lower barrier, corner `χ₀ = 21 / 25`, `γ = 0.49`. -/
theorem highQ_sub_check_hl :
    pieceCheckL (lowA highQ_aux highQ_fs (21 / 25) (49 / 100)) highQ_fs
      kirchhoffQ (1 / 200) 0 highQ_subP = true := by
  decide +kernel
/-- Lower barrier, corner `χ₀ = 21 / 25`, `γ = 0.525`. -/
theorem highQ_sub_check_hu :
    pieceCheckL (lowA highQ_aux highQ_fs (21 / 25) (21 / 40)) highQ_fs
      kirchhoffQ (1 / 200) 0 highQ_subP = true := by
  decide +kernel
/-- Upper barrier, corner `χ₀ = 39 / 50`, `γ = 0.49`. -/
theorem highQ_sup_check_ll :
    pieceCheckL (upA highQ_aux highQ_fu (39 / 50) (49 / 100)) highQ_fu
      kirchhoffQ (1 / 200) 0 highQ_supP = true := by
  decide +kernel
/-- Upper barrier, corner `χ₀ = 39 / 50`, `γ = 0.525`. -/
theorem highQ_sup_check_lu :
    pieceCheckL (upA highQ_aux highQ_fu (39 / 50) (21 / 40)) highQ_fu
      kirchhoffQ (1 / 200) 0 highQ_supP = true := by
  decide +kernel
/-- Upper barrier, corner `χ₀ = 21 / 25`, `γ = 0.49`. -/
theorem highQ_sup_check_hl :
    pieceCheckL (upA highQ_aux highQ_fu (21 / 25) (49 / 100)) highQ_fu
      kirchhoffQ (1 / 200) 0 highQ_supP = true := by
  decide +kernel
/-- Upper barrier, corner `χ₀ = 21 / 25`, `γ = 0.525`. -/
theorem highQ_sup_check_hu :
    pieceCheckL (upA highQ_aux highQ_fu (21 / 25) (21 / 40)) highQ_fu
      kirchhoffQ (1 / 200) 0 highQ_supP = true := by
  decide +kernel
/-- Pressure certificate (`Δ = 40000 Pa`). -/
theorem highQ_pres_check :
    pieceCheckL (presD 40000) highQ_fu kirchhoffQ 0 0 highQ_presP = true := by
  decide +kernel

/-- Monotonicity: `−F_sub' ≥ 0` on `[0,1]`. -/
theorem highQ_fs_deriv_check :
    QPoly.checkOn (QPoly.scale (-1) (QPoly.deriv highQ_fs)) 0 0 1 (gridN 8) = true := by
  decide +kernel
/-- Monotonicity: `−F_sup' ≥ 0` on `[0,1]`. -/
theorem highQ_fu_deriv_check :
    QPoly.checkOn (QPoly.scale (-1) (QPoly.deriv highQ_fu)) 0 0 1 (gridN 8) = true := by
  decide +kernel
/-- Ordering: `F_sup − F_sub ≥ 0` on `[0,1]`. -/
theorem highQ_gap_check :
    QPoly.checkOn (QPoly.add highQ_fu (QPoly.scale (-1) highQ_fs)) 0 0 1 (gridN 8) = true := by
  decide +kernel

/-- Label and endpoint facts, checked once. -/
theorem highQ_labels_check :
    (highQ_subP.all (fun p => decide (0 ≤ p.2.1)) &&
      highQ_supP.all (fun p => ceilOK p.2.2 && decide (p.2.2 ≤ 60) && decide (0 ≤ p.2.1)) &&
      decide (pieceEnd2 0 highQ_subP = 1) && decide (pieceEnd2 0 highQ_supP = 1) &&
      decide (pieceEnd2 0 highQ_presP = 1) &&
      decide (QPoly.evalQ highQ_fs 1 = kirchhoffQ 1) &&
      decide (QPoly.evalQ highQ_fu 1 = kirchhoffQ (3 / 2)) &&
      decide (QPoly.evalQ highQ_fs 0 ≤ kirchhoffQ 60) &&
      decide (kirchhoffQ 10 ≤ QPoly.evalQ highQ_fs (3 / 10)) &&
      decide (QPoly.evalQ highQ_fu 0 ≤ kirchhoffQ 19)) = true := by
  decide +kernel

/-- Unpacked label and endpoint facts. -/
theorem highQ_labels_facts :
    (∀ p ∈ highQ_subP, 0 ≤ p.2.1) ∧
      (∀ p ∈ highQ_supP, ceilOK p.2.2 = true ∧ p.2.2 ≤ 60 ∧ 0 ≤ p.2.1) ∧
      pieceEnd2 0 highQ_subP = 1 ∧ pieceEnd2 0 highQ_supP = 1 ∧ pieceEnd2 0 highQ_presP = 1 ∧
      QPoly.evalQ highQ_fs 1 = kirchhoffQ 1 ∧ QPoly.evalQ highQ_fu 1 = kirchhoffQ (3 / 2) ∧
      QPoly.evalQ highQ_fs 0 ≤ kirchhoffQ 60 ∧ kirchhoffQ 10 ≤ QPoly.evalQ highQ_fs (3 / 10) ∧
      QPoly.evalQ highQ_fu 0 ≤ kirchhoffQ 19 := by
  have h := highQ_labels_check
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, fun p hp => ⟨(h2 p hp).1.1, (h2 p hp).1.2, (h2 p hp).2⟩, h3, h4, h5, h6, h7, h8,
    h9, h10⟩

/-! ### high Q: consequences -/

/-- `1 ≤ T_sub ≤ 60` on `[0,1]`. -/
theorem highQ_tsub_bounds {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    1 ≤ highQ_Tsub s ∧ highQ_Tsub s ≤ 60 := by
  obtain ⟨-, -, -, -, -, h6, -, h8, -⟩ := highQ_labels_facts
  have hF := antitone_of_deriv_check highQ_fs_deriv_check
  have a := le_kProf_of_edge hF h6 hs
  have b := kProf_le_of_axis hF h8 hs
  push_cast at a b
  exact ⟨a, b⟩

/-- `1 ≤ T_sup ≤ 19` on `[0,1]`. -/
theorem highQ_tsup_bounds {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    1 ≤ highQ_Tsup s ∧ highQ_Tsup s ≤ 19 := by
  obtain ⟨-, -, -, -, -, -, h7, -, -, h10⟩ := highQ_labels_facts
  have hF := antitone_of_deriv_check highQ_fu_deriv_check
  have a := le_kProf_of_edge hF h7 hs
  have b := kProf_le_of_axis hF h10 hs
  push_cast at a b
  exact ⟨le_trans (by norm_num) a, b⟩

/-- **Core temperature.** `T_sub ≥ 10 keV` on `s ≤ 3/10`. -/
theorem highQ_tsub_core {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 3 / 10) : 10 ≤ highQ_Tsub s := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := highQ_labels_facts
  have := le_kProf_of_core (antitone_of_deriv_check highQ_fs_deriv_check) (by norm_num) h9 h0
    (by push_cast; exact h1)
  push_cast at this
  exact this

/-- Edge values `T_sub(1) = 1`, `T_sup(1) = 3/2`. -/
theorem highQ_barrier_edges : highQ_Tsub 1 = 1 ∧ highQ_Tsup 1 = 3 / 2 := by
  obtain ⟨-, -, -, -, -, h6, h7, -⟩ := highQ_labels_facts
  have a := kProf_one h6
  have b := kProf_one h7
  push_cast at a b
  exact ⟨a, b⟩

/-- Sanity: the band is not empty, `T_sub ≤ T_sup` on `[0,1]`. -/
theorem highQ_band_nonempty {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    highQ_Tsub s ≤ highQ_Tsup s := by
  have := QPoly.checkOn_sound highQ_gap_check s (by simpa using hs)
  simp only [QPoly.eval_add, QPoly.eval_scale] at this
  push_cast at this
  exact kirchhoffIso.symm.monotone (by linarith)

/-- **Lower-barrier margin.** For every geometry in `IsSolovevGeometry`, every fine supplied
reactivity and every `χ₀ ∈ [39 / 50, 21 / 25]`, `N[T_sub] ≥ 1/200 keV/s` on `[0,1]`. -/
theorem highQ_tsub_margin (G : FluxGeometry) [IsSolovevGeometry G] (sv : ℝ → ℝ)
    [BoschHaleFine sv] {χ₀ : ℝ} (h1 : 39 / 50 ≤ χ₀) (h2 : χ₀ ≤ 21 / 25) :
    ∀ s ∈ Icc (0 : ℝ) 1, (1 / 200 : ℝ) ≤ (coeffsA highQ_aux G sv χ₀).op s (highQ_Tsub s)
      (kProf' highQ_fs s) (kProf'' highQ_fs s) := by
  obtain ⟨hl, -, hend, -⟩ := highQ_labels_facts
  have := tsub_margin_gen highQ_aux highQ_fs highQ_subP (χL := 39 / 50) (χH := 21 / 25)
    (κ := 1 / 200) (by norm_num) (by norm_num) highQ_sub_check_ll highQ_sub_check_lu
    highQ_sub_check_hl highQ_sub_check_hu (by simp [highQ_subP]) hl hend
    highQ_fs_deriv_check
    (fun s hs => highQ_tsub_bounds hs) G sv (χ₀ := χ₀) (by push_cast; linarith)
    (by push_cast; linarith)
  push_cast at this
  exact this

/-- **Upper-barrier margin.** For every geometry in `IsSolovevGeometry`, every fine supplied
reactivity and every `χ₀ ∈ [39 / 50, 21 / 25]`, `N[T_sup] ≤ −1/200 keV/s` on `[0,1]`. -/
theorem highQ_tsup_margin (G : FluxGeometry) [IsSolovevGeometry G] (sv : ℝ → ℝ)
    [BoschHaleFine sv] {χ₀ : ℝ} (h1 : 39 / 50 ≤ χ₀) (h2 : χ₀ ≤ 21 / 25) :
    ∀ s ∈ Icc (0 : ℝ) 1, (coeffsA highQ_aux G sv χ₀).op s (highQ_Tsup s) (kProf' highQ_fu s)
      (kProf'' highQ_fu s) ≤ -(1 / 200) := by
  obtain ⟨-, hu, -, hend, -⟩ := highQ_labels_facts
  have := tsup_margin_gen highQ_aux highQ_fu highQ_supP (χL := 39 / 50) (χH := 21 / 25)
    (κ := 1 / 200) (by norm_num) (by norm_num) highQ_sup_check_ll highQ_sup_check_lu
    highQ_sup_check_hl highQ_sup_check_hu (by simp [highQ_supP]) hu hend
    highQ_fu_deriv_check
    (fun s hs => (highQ_tsup_bounds hs).1) G sv (χ₀ := χ₀) (by push_cast; linarith)
    (by push_cast; linarith)
  push_cast at this
  exact this

/-- **Pressure ceiling.** `n(s) (1 + 53/60) T_sup(s) keV ≤ p_eq(s) + Δ` on `[0,1]`,
`Δ = 40000 Pa`, for reactor `μ₀ ∈ [1.2566·10⁻⁶, 1.2567·10⁻⁶]`. -/
theorem highQ_pressure {μ₀ : ℝ} (hμ1 : 1.2566e-6 ≤ μ₀) (hμ2 : μ₀ ≤ 1.2567e-6) :
    ∀ s ∈ Icc (0 : ℝ) 1,
      nProf s * (1 + 53 / 60) * highQ_Tsup s * keV ≤ peqLabel μ₀ 40000 s := by
  obtain ⟨-, -, -, -, hend, -⟩ := highQ_labels_facts
  have := pressure_gen 40000 highQ_fu highQ_presP highQ_pres_check
    (by simp [highQ_presP]) hend highQ_fu_deriv_check
    (fun s hs => le_trans (by norm_num) (highQ_tsup_bounds hs).1) hμ1 hμ2
  push_cast at this
  exact this

/-- **Two-sided band on the Solov'ev geometry (high Q).** For every geometry in
`IsSolovevGeometry`, every reactivity satisfying the fine supplied Bosch–Hale enclosures,
every `χ₀ ∈ [39 / 50, 21 / 25]` m²/s, and every kernel solution on all horizons of
`coeffsA highQ_aux G sv χ₀`
(auxiliary heating `2 (1 − s)⁶` keV/s (≈ 17.5 MW, oracle))
with edge temperature in `[1, 3/2]` keV and initial profile in `[T_sub, T_sup]`: for all
`t ≥ 0`, `T_sub ≤ T ≤ T_sup`, `T ≥ 10 keV` on `s ≤ 3/10`, and `T ≤ 19 keV`. -/
theorem highQ_band (G : FluxGeometry) [IsSolovevGeometry G] (sv : ℝ → ℝ)
    [BoschHaleFine sv] {χ₀ : ℝ} (h1 : 39 / 50 ≤ χ₀) (h2 : χ₀ ≤ 21 / 25) {Tedge : ℝ → ℝ}
    {u : RadialField}
    (hu : ∀ τ, 0 ≤ τ → ClassicalRadialSolution (coeffsA highQ_aux G sv χ₀) Tedge τ u)
    (h0 : ∀ s ∈ Icc (0 : ℝ) 1, highQ_Tsub s ≤ u.T s 0 ∧ u.T s 0 ≤ highQ_Tsup s)
    (hedge : ∀ t, 0 ≤ t → 1 ≤ Tedge t ∧ Tedge t ≤ 3 / 2) :
    (∀ s ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → highQ_Tsub s ≤ u.T s t ∧ u.T s t ≤ highQ_Tsup s) ∧
      (∀ s, 0 ≤ s → s ≤ 3 / 10 → ∀ t, 0 ≤ t → 10 ≤ u.T s t) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → u.T s t ≤ 19) := by
  have hb := band_gen highQ_aux highQ_fs highQ_fu (κ := 1 / 200) (by norm_num) G sv
    (by linarith : (0 : ℝ) ≤ χ₀)
    (fun s hs => lt_of_lt_of_le (by norm_num) (highQ_tsub_bounds hs).1)
    (fun s hs => lt_of_lt_of_le (by norm_num) (highQ_tsup_bounds hs).1)
    highQ_barrier_edges.1 highQ_barrier_edges.2 (highQ_tsub_margin G sv h1 h2)
    (highQ_tsup_margin G sv h1 h2) hu h0 hedge
  refine ⟨hb, fun s h0' h1' t ht => ?_, fun s hs t ht => (hb s hs t ht).2.trans
    (highQ_tsup_bounds hs).2⟩
  exact (highQ_tsub_core h0' h1').trans (hb s ⟨h0', h1'.trans (by norm_num)⟩ t ht).1

/-- **`solovev_one_plasma_highQ`** (rung C2, high Q). One field: the reactor Solov'ev field `B`
with Ampère current `J` and pressure `p_eq + Δ`, `Δ = 40000 Pa`.

1. *(equilibrium)* the kernel law `ForceBalance B J ∇(p_eq + Δ)` holds at every point of the
   transport domain `s ≤ 1`;
2. *(alphas)* every 3.5 MeV alpha born at `s ≤ 3/11` stays in `0 ≤ s ≤ 1` for all real time;
3. *(transport)* for every geometry in `IsSolovevGeometry` (instantiated for the actual
   field in `solovev_one_plasma_highQ_actual`),
   every reactivity in the fine supplied Bosch–Hale class, every
   `χ₀ ∈ [39 / 50, 21 / 25]` (stand-in `χ₀ (1/10 + T²/100)`),
   auxiliary heating `2 (1 − s)⁶` keV/s (≈ 17.5 MW, oracle),
   and every supplied classical solution on all horizons with edge temperature in `[1, 3/2]`
   keV starting in the band: for all `t ≥ 0`, `T_sub ≤ T ≤ T_sup` on `[0,1]`, `T ≥ 10 keV`
   on `s ≤ 3/10`, and the plasma pressure `n(s)(1 + r_i) T keV` at every point of the
   transport domain is at most `p_eq(x) + Δ`.

Oracle steady states over the window: `P_α ≈ 137–161 MW`,
`Q = 5 P_α/P_aux ≈ 39–46` (not formalized); driven at high `Q`, not ignited.
Caveats as for `SolovevBand.solovev_one_plasma`. -/
theorem solovev_one_plasma_highQ {μ₀ : ℝ} (hμ1 : 1.2566e-6 ≤ μ₀) (hμ2 : μ₀ ≤ 1.2567e-6) :
    (∀ x : Space, label x ≤ 1 →
      ForceBalance (ofLp (reactorField x)) (ofLp (current μ₀ (7 / 4) 10 50 x))
        (ofLp (gradient (offsetPressure μ₀ 40000) x))) ∧
    (∀ {m e : ℝ} {x v : ℝ → Space}, 6.6446e-27 ≤ m → m ≤ 6.6448e-27 → 1.6021e-19 ≤ e →
      e ≤ 1.6023e-19 → LorentzOrbit m (2 * e) (fun _ => 0) reactorField x v →
      m * ‖v 0‖ ^ 2 ≤ 2 * (3.5e6 * e) → label (x 0) ≤ 3 / 11 →
      ∀ t, label (x t) ∈ Icc (0 : ℝ) 1) ∧
    (∀ (G : FluxGeometry) [IsSolovevGeometry G] (sv : ℝ → ℝ) [BoschHaleFine sv] {χ₀ : ℝ},
      39 / 50 ≤ χ₀ → χ₀ ≤ 21 / 25 → ∀ {Tedge : ℝ → ℝ} {u : RadialField},
      (∀ τ, 0 ≤ τ → ClassicalRadialSolution (coeffsA highQ_aux G sv χ₀) Tedge τ u) →
      (∀ s ∈ Icc (0 : ℝ) 1, highQ_Tsub s ≤ u.T s 0 ∧ u.T s 0 ≤ highQ_Tsup s) →
      (∀ t, 0 ≤ t → 1 ≤ Tedge t ∧ Tedge t ≤ 3 / 2) →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → highQ_Tsub s ≤ u.T s t ∧ u.T s t ≤ highQ_Tsup s) ∧
      (∀ s, 0 ≤ s → s ≤ 3 / 10 → ∀ t, 0 ≤ t → 10 ≤ u.T s t) ∧
      (∀ x : Space, label x ≤ 1 → ∀ t, 0 ≤ t →
        nProf (label x) * (1 + 53 / 60) * u.T (label x) t * keV ≤
          reactorPressure μ₀ x + 40000)) := by
  have hμ : μ₀ ≠ 0 := by intro h; rw [h] at hμ1; norm_num at hμ1
  refine ⟨fun x hx => offset_force_balance_domain hμ 40000 hx,
    fun hm1 hm2 he1 he2 h hK hs0 t =>
      (alpha_stays_in_transport_domain hm1 hm2 he1 he2 h hK hs0 t).1, ?_⟩
  intro G _ sv _ χ₀ h1 h2 Tedge u hu h0 hedge
  obtain ⟨hband, hcore, -⟩ := highQ_band G sv h1 h2 hu h0 hedge
  refine ⟨hband, hcore, fun x hx t ht => ?_⟩
  exact plasma_pressure_le_offset (c := 1 + 53 / 60) (n := nProf) (Tsup := highQ_Tsup)
    (T := u.T) hμ (by norm_num)
    (fun s hs => by unfold nProf; have := dens_pos hs; positivity)
    (fun s hs t ht => (hband s hs t ht).2) (highQ_pressure hμ1 hμ2) hx ht

/-- **`solovev_one_plasma_highQ` for the actual Solov'ev transport geometry**: the geometry
hypothesis is discharged by `SolovevFluxGeometry.solovevFluxGeometry_isSolovev`
(validated enclosures for the reactor Solov'ev field). Remaining unformalized link: the
coarea formula and the measure-theoretic change of variables identifying the flux-surface
averages, as stated in `Design.SolovevFluxGeometry`. -/
theorem solovev_one_plasma_highQ_actual {μ₀ : ℝ} (hμ1 : 1.2566e-6 ≤ μ₀) (hμ2 : μ₀ ≤ 1.2567e-6) :
    (∀ x : Space, label x ≤ 1 →
      ForceBalance (ofLp (reactorField x)) (ofLp (current μ₀ (7 / 4) 10 50 x))
        (ofLp (gradient (offsetPressure μ₀ 40000) x))) ∧
    (∀ {m e : ℝ} {x v : ℝ → Space}, 6.6446e-27 ≤ m → m ≤ 6.6448e-27 → 1.6021e-19 ≤ e →
      e ≤ 1.6023e-19 → LorentzOrbit m (2 * e) (fun _ => 0) reactorField x v →
      m * ‖v 0‖ ^ 2 ≤ 2 * (3.5e6 * e) → label (x 0) ≤ 3 / 11 →
      ∀ t, label (x t) ∈ Icc (0 : ℝ) 1) ∧
    (∀ (sv : ℝ → ℝ) [BoschHaleFine sv] {χ₀ : ℝ},
      39 / 50 ≤ χ₀ → χ₀ ≤ 21 / 25 → ∀ {Tedge : ℝ → ℝ} {u : RadialField},
      (∀ τ, 0 ≤ τ →
        ClassicalRadialSolution (coeffsA highQ_aux solovevFluxGeometry sv χ₀) Tedge τ u) →
      (∀ s ∈ Icc (0 : ℝ) 1, highQ_Tsub s ≤ u.T s 0 ∧ u.T s 0 ≤ highQ_Tsup s) →
      (∀ t, 0 ≤ t → 1 ≤ Tedge t ∧ Tedge t ≤ 3 / 2) →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → highQ_Tsub s ≤ u.T s t ∧ u.T s t ≤ highQ_Tsup s) ∧
      (∀ s, 0 ≤ s → s ≤ 3 / 10 → ∀ t, 0 ≤ t → 10 ≤ u.T s t) ∧
      (∀ x : Space, label x ≤ 1 → ∀ t, 0 ≤ t →
        nProf (label x) * (1 + 53 / 60) * u.T (label x) t * keV ≤
          reactorPressure μ₀ x + 40000)) :=
  ⟨(solovev_one_plasma_highQ hμ1 hμ2).1, (solovev_one_plasma_highQ hμ1 hμ2).2.1,
    fun sv _ _ h1 h2 _ _ => (solovev_one_plasma_highQ hμ1 hμ2).2.2 solovevFluxGeometry sv h1 h2⟩

/-- **Non-vacuity of the hypotheses**: the fine Bosch–Hale class used by
`solovev_one_plasma_highQ` has a member (`Sanity.BoschHaleFineInstance.bhFineSv`), and the
geometry class has the model member `SolovevBand.modelGeometry`. -/
theorem highQ_hypotheses_inhabited :
    (∃ sv : ℝ → ℝ, BoschHaleFine sv) ∧ IsSolovevGeometry modelGeometry :=
  ⟨⟨_, PlasmaLean.Sanity.BoschHaleFineInstance.bhFineSv_boschHaleFine⟩, inferInstance⟩

end PlasmaLean.Design.SolovevBandHighQ
