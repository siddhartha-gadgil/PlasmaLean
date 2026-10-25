/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Transport.BarrierCheck
public import PlasmaLean.Kernel.Fusion
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Real.Pi.Bounds
public import PlasmaLean.Certificates.KernelFact

/-!
# Model rung M2: an all-time core-temperature barrier for radial heat transport

Labels: *idealized geometry*, *synthetic reactor-scale data*, Bosch–Hale reactivity as
*supplied data* (kernel class `BoschHaleDT`).

## Geometry and the flux-surface-averaged coefficients

Straight screw-pinch cylinder (the geometry of `Design.ScrewPinchExample`, rescaled): minor
radius `a = 5/2 m`, periodic length `2πR₀` with `R₀ = 13/2 m`; the flux surfaces are the
cylinders `r = const`. The radial label is the normalized area (toroidal-flux) coordinate
`ψ = r²/a² ∈ [0,1]`, which equals the normalized toroidal flux when `B_z` is uniform (for the
screw pinch of `ScrewPinchExample`, `B_z` varies by about 5%; any flux label works for the
transport model). Exact facts (`volume_eq`, `gradPsi_sq`):

* volume inside `ψ`: `V(ψ) = π (a√ψ)² · 2πR₀ = 2π²R₀a² ψ`, so `V' = 2π²R₀a² ≈ 802 m³` is
  constant and `V'' = 0`;
* `|∇ψ|² = (2r/a²)² = 4ψ/a²` (exact, constant on each surface, so `⟨|∇ψ|²⟩ = 4ψ/a²`).

With a prescribed temperature diffusivity `χ` (m²/s; heat flux `q = −(3/2)(n_e+n_i) χ ∇T`;
**unit convention:** this `χ` includes the `3/2` heat-capacity factor, so the conventional
per-species diffusivity `χ_conv` of `q = −(n_e+n_i) χ_conv ∇T` is `χ_conv = (3/2) χ`; the
range `χ ≤ 1/2` below means `χ_conv ≤ 3/4 m²/s`, and `χ ≥ 9/20` means `χ_conv ≥ 0.675`),
the energy equation `(3/2)(n_e+n_i) ∂ₜT = −∇·q + p_α + p_aux − p_br`, flux-surface averaged,
becomes the kernel equation `∂ₜT = (1/V') ∂ψ (V' D ∂ψT) + R(ψ,T)` with

* `D(ψ) = χ ⟨|∇ψ|²⟩ = 4χψ/a²` (s⁻¹), `D'(ψ) = 4χ/a²` (`cylCoeffs`), so
  `N[T] = (4χ/a²)(ψ T'' + T') + R` (`cylCoeffs_op`), the cylindrical Laplacian;
* `R(ψ,T) = (p_α(T) + p_aux(ψ) − p_br(T)) / ((3/2) n (1+r_i) keV)` in keV/s
  (`netSource`), with the kernel's 0-D formulas evaluated per unit volume
  (`m2Plasma` has `V = 1 m³`): `p_α = (E_α/4)(f_fuel n)² ⟨σv⟩(T)`,
  `p_br = C_br n² Z_eff √T`, `n = 10²⁰ m⁻³`, `Z_eff = 1.7` from carbon, so `f_fuel = 0.86`,
  `r_i = 53/60` (fuel dilution exactly as in the M1 burn window).
* Auxiliary heating `p_aux(ψ) = (3/2) n (1+r_i) keV · q_aux(ψ)` with heating rate
  `q_aux(ψ) = 134 ψ(1−ψ)⁸ + 0.43` keV/s (`auxRateCoeffs`): a central deposition peaked at
  `ψ = 1/9` (`r ≈ 0.83 m`) plus a uniform floor. Total auxiliary power
  `(3/2) n (1+r_i) keV · V' · ∫₀¹ q_aux ∈ [69.5, 69.7] MW` (`totalAuxPower_bounds`).

`D(0) = 0`: the axis is degenerate. Since the kernel change of 2026-10-20 (`D ≥ 0`, axis
kind `degenerate`, source domain `T > 0`) the cylinder coefficients are a genuine kernel
instance (`cylCoeffs_transportLaws`), and the kernel solutions are exactly the axis-free
solutions (`AxisFreeSolution.classical`). `m2_core_barrier_kernel` is proved directly from
the kernel-level barrier theorem `le_of_isStrictLowerBarrier_margin_forall_time`;
`m2_core_barrier` is the same statement for axis-free solutions, via the degenerate-axis
comparison of `PlasmaLean.Theory.Transport.BarrierCheck`. (Before the change, the kernel
demanded `D ≥ Dmin > 0` and a Neumann axis condition, and the cylinder was not an instance.)

## Results

* `m2_core_barrier` (**goal G2, rung M2**): for every reactivity `sv` satisfying the supplied
  Bosch–Hale enclosures, every diffusivity `χ ∈ [0, 1/2]` m²/s, and every axis-free classical
  solution on all horizons with `T(ψ,0) ≥ T_sub(ψ)` and edge temperature `T_edge(t) ≥ 1 keV`,
  `T(ψ,t) ≥ T_sub(ψ)` for all `ψ ∈ [0,1]`, `t ≥ 0`; and `T_sub ≥ 10 keV` on `ψ ≤ 3/10`
  (`r ≤ 1.37 m`). `T_sub` is an explicit degree-10 rational polynomial with
  `T_sub(0) = 5176/315 ≈ 16.4 keV`, `T_sub(1) = 1 keV`, `T_sub'(0) = 0`.
  `m2_core_barrier_kernel` is the same statement for kernel solutions
  (`ClassicalRadialSolution`, degenerate axis), proved from the kernel-level theorem with the
  instance `cylCoeffs_transportLaws`.
* Margin: `N[T_sub] ≥ κ = 1/20 keV/s` on `[0,1]` for every `χ ∈ [0, 1/2]`
  (`tsub_margin`), from a 16-piece exact rational certificate (`tsub_pieceCheck`) using the
  Bosch–Hale lower windows at `T_sub ≥ 15, 14, …, 2` keV, the bound `√T ≤ (T+4)/4` on
  bremsstrahlung and `(4χ/a²) G ≥ (8/25) G` for `G = ψT_sub'' + T_sub' = −720ψ(1−ψ)⁸ ≤ 0`.
* Upper barrier (`m2_upper_barrier`): for `χ ∈ [9/20, 1/2]`, `T ≤ 1 + 96(1−ψ)` keV, using
  `⟨σv⟩ ≤ 9.037·10⁻²² m³/s` on `[1,100]` keV. This is crude (axis bound 97 keV) but honest:
  with fixed `χ` the alpha heating is only bounded through the reactivity ceiling.
* Exhaust power (`m2_exhaust_power`): with `T_edge ≡ 1 keV` and both barriers, the edge slope
  satisfies `−96 ≤ ∂ψT(1,t) ≤ −8`, so the conductive power to the wall
  `P = (3/2) n (1+r_i) keV · V' D(1) |∂ψT(1,t)| = (3/2) n (1+r_i) keV · 8π²R₀χ |∂ψT(1,t)|`
  lies between `8` and `96` times `(3/2) n (1+r_i) keV · 8π²R₀χ`; at `χ ∈ [9/20, 1/2]`,
  `83 MW ≤ P ≤ 1.12 GW` (`m2_exhaust_power_numeric`).
* Inequality hypotheses only (`m2_barrier_hypotheses_satisfiable`): `T_sub` with edge data
  `1 keV` satisfies the *inequality* initial/edge hypotheses of both barriers
  (`T_sub ≤ 1 + 96(1−ψ)`). It is **not** admissible initial data: classical solutions need
  the corner compatibility `N[T(·,0)](1) = T_edge'(0)`
  (`AxisFreeSolution.corner_compatibility`), and `N[T_sub](1) ≥ 1/20 > 0`
  (`tsub_not_initial_data`). `m2_compatible_initial_profile` supplies, for every `sv` and
  `χ ∈ (0, 1/2]`, a profile `T₀ = T_sub + c(1−ψ) ≥ T_sub` with `T₀(1) = 1` and `N[T₀](1) = 0`,
  so the lower-barrier hypotheses together with corner compatibility for `T_edge ≡ 1` are
  jointly satisfiable (still no solution is constructed).

## Honest limitations

* `χ` is prescribed (constant in space and time), the density and composition are fixed, and
  the model is the flux-surface-averaged single-temperature equation in a straight cylinder:
  no toroidal geometry, no pedestal, no profile stiffness, no alpha slowing-down or ash.
* Classical solutions are **supplied**: existence/regularity for the nonlinear equation with
  the Bosch–Hale source is not proved, and no explicit solution is exhibited (the class could
  in principle be empty; the theorem is a statement about every member).
* The reactivity enters only through the supplied rational windows and monotonicity on
  `[1,60]` keV; the lower barrier uses no information beyond that.
* The lower barrier requires `T_edge ≥ 1 keV`, a central auxiliary deposition of ≈ 70 MW,
  and `χ ≤ 0.5 m²/s`; the upper barrier and exhaust bounds only hold for `χ ≥ 0.45 m²/s`.
-/

public section

noncomputable section

namespace PlasmaLean.Design.TransportBarrier

open Set PlasmaLean.Transport PlasmaLean.Fusion PlasmaLean.Certificates

/-! ### Geometry -/

/-- Minor radius `a = 5/2 m`. -/
@[expose] def minorRadius : ℝ := 5 / 2

/-- Major radius `R₀ = 13/2 m` (the cylinder has periodic length `2πR₀`). -/
@[expose] def majorRadius : ℝ := 13 / 2

/-- Volume derivative `V' = 2π²R₀a²` (m³ per unit `ψ`), constant for `ψ = r²/a²`. -/
@[expose] def volumeDeriv : ℝ := 2 * Real.pi ^ 2 * majorRadius * minorRadius ^ 2

/-- Exact geometry: the volume of the cylinder `r ≤ a√ψ` of length `2πR₀` is `V' ψ`. -/
theorem volume_eq {ψ : ℝ} (hψ : 0 ≤ ψ) :
    Real.pi * (minorRadius * Real.sqrt ψ) ^ 2 * (2 * Real.pi * majorRadius) = volumeDeriv * ψ := by
  rw [mul_pow, Real.sq_sqrt hψ]; unfold volumeDeriv; ring

/-- Exact geometry: `ψ(r) = r²/a²` has `ψ'(r) = 2r/a²` and `|∇ψ|² = ψ'(r)² = 4ψ/a²`. -/
theorem gradPsi_sq (r : ℝ) :
    HasDerivAt (fun x => x ^ 2 / minorRadius ^ 2) (2 * r / minorRadius ^ 2) r ∧
      (2 * r / minorRadius ^ 2) ^ 2 = 4 * (r ^ 2 / minorRadius ^ 2) / minorRadius ^ 2 := by
  refine ⟨?_, by unfold minorRadius; ring⟩
  have := (hasDerivAt_pow 2 r).div_const (minorRadius ^ 2)
  convert this using 1; ring

/-- `V' > 0`. -/
theorem volumeDeriv_pos : 0 < volumeDeriv := by
  unfold volumeDeriv majorRadius minorRadius; positivity

/-! ### Plasma, heating and the net source -/

/-- The M2 plasma per unit volume (`V = 1 m³`, so kernel powers are W/m³): `n = 10²⁰ m⁻³`,
`Z_eff = 1.7` from carbon, `f_fuel = 0.86`, `r_i = 53/60` (as in the M1 burn window). -/
@[expose] def m2Plasma : DTPlasma := ⟨1e20, 1, 1.7, 0.86, 53 / 60⟩

/-- Thermal capacity per unit volume `(3/2) n (1+r_i) keV` (J m⁻³ keV⁻¹). -/
@[expose] def heatCap : ℝ := m2Plasma.thermalEnergy 1

/-- `heatCap = (3/2)·10²⁰·(113/60)·1.602176634·10⁻¹⁶ ≈ 45261 J m⁻³ keV⁻¹`. -/
theorem heatCap_eq : heatCap = 3 / 2 * 1e20 * (1 + 53 / 60) * 1.602176634e-16 := by
  simp only [heatCap, DTPlasma.thermalEnergy, m2Plasma, keV]; ring

/-- `heatCap > 0`. -/
theorem heatCap_pos : 0 < heatCap := by rw [heatCap_eq]; norm_num

/-- Auxiliary heating rate `q_aux(ψ) = 134 ψ (1−ψ)⁸ + 43/100` keV/s (coefficients, constant
term first). -/
@[expose] def auxRateCoeffs : List ℚ :=
  [43 / 100, 134, -1072, 3752, -7504, 9380, -7504, 3752, -1072, 134]

/-- The coefficient list is the stated deposition profile. -/
theorem auxRate_eq (ψ : ℝ) :
    QPoly.eval auxRateCoeffs ψ = 134 * ψ * (1 - ψ) ^ 8 + 43 / 100 := by
  simp [auxRateCoeffs]; ring

/-- Auxiliary heating power density `p_aux(ψ) = heatCap · q_aux(ψ)` (W/m³). -/
@[expose] def auxPower (ψ : ℝ) : ℝ := heatCap * QPoly.eval auxRateCoeffs ψ

/-- Net source `R(ψ,T) = (p_α + p_aux − p_br)/heatCap` in keV/s, for a supplied reactivity. -/
@[expose] def netSource (sv : ℝ → ℝ) (ψ T : ℝ) : ℝ :=
  (m2Plasma.alphaPower sv T + auxPower ψ - m2Plasma.bremsPower T) / heatCap

/-- Alpha heating rate coefficient `(E_α/4) f² n² / heatCap = 3500 f² n /(6(1+r_i))`
(keV/s per m³/s); `keV` cancels. -/
@[expose] def alphaRate : ℝ := 3500 * 1.602176634e-16 / 4 * (0.86 * 1e20) ^ 2 / heatCap

/-- Bremsstrahlung rate coefficient `C_br n² Z_eff / heatCap` (keV/s per √keV). -/
@[expose] def bremsRate : ℝ := 5.35e-37 * (1e20 : ℝ) ^ 2 * 1.7 / heatCap

/-- Explicit form of the net source. -/
theorem netSource_eq (sv : ℝ → ℝ) (ψ T : ℝ) :
    netSource sv ψ T = alphaRate * sv T + QPoly.eval auxRateCoeffs ψ
      - bremsRate * Real.sqrt T := by
  have h := heatCap_pos.ne'
  simp only [netSource, alphaRate, bremsRate, auxPower, DTPlasma.alphaPower,
    DTPlasma.bremsPower, m2Plasma, alphaEnergy, keV, bremsCoeff]
  field_simp

/-- `alphaRate ≥ 2.29·10²² ` (exact value `≈ 2.2908·10²²`). -/
theorem alphaRate_ge : (229 / 10 * 10 ^ 21 : ℝ) ≤ alphaRate := by
  rw [alphaRate, heatCap_eq, le_div_iff₀ (by norm_num)]; norm_num

/-- `alphaRate ≤ 2.291·10²²`. -/
theorem alphaRate_le : alphaRate ≤ (2291 / 100 * 10 ^ 21 : ℝ) := by
  rw [alphaRate, heatCap_eq, div_le_iff₀ (by norm_num)]; norm_num

/-- `bremsRate ≤ 0.201` (exact value `≈ 0.20094`). -/
theorem bremsRate_le : bremsRate ≤ (201 / 1000 : ℝ) := by
  rw [bremsRate, heatCap_eq, div_le_iff₀ (by norm_num)]; norm_num

/-- `bremsRate ≥ 0`. -/
theorem bremsRate_nonneg : 0 ≤ bremsRate := by
  rw [bremsRate, heatCap_eq]; norm_num

/-- Antiderivative coefficients of `q_aux` (vanishing at `0`). -/
@[expose] def auxAntiCoeffs : List ℚ :=
  [0, 43 / 100, 67, -1072 / 3, 938, -7504 / 5, 9380 / 6, -1072, 469, -1072 / 9, 67 / 5]

/-- `∫₀¹ q_aux(ψ) dψ = 134/90 + 43/100 ≈ 1.919` keV/s. -/
theorem auxRate_integral :
    ∫ x in (0 : ℝ)..1, QPoly.eval auxRateCoeffs x = 134 / 90 + 43 / 100 := by
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (QPoly.eval auxAntiCoeffs) (QPoly.eval auxRateCoeffs x) x := by
    intro x _
    convert QPoly.hasDerivAt_eval auxAntiCoeffs x using 1
    simp only [auxAntiCoeffs, auxRateCoeffs, QPoly.deriv, QPoly.add, QPoly.eval_cons,
      QPoly.eval_nil]
    push_cast; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((QPoly.continuous_eval _).intervalIntegrable _ _)]
  simp [auxAntiCoeffs]; norm_num

/-- Total auxiliary heating power (W): `∫ p_aux dV = heatCap · V' · ∫₀¹ q_aux dψ`. -/
@[expose] def totalAuxPower : ℝ :=
  heatCap * volumeDeriv * ∫ x in (0 : ℝ)..1, QPoly.eval auxRateCoeffs x

/-- The auxiliary heating budget is `69.5–69.7 MW`. -/
theorem totalAuxPower_bounds : (69.5e6 : ℝ) ≤ totalAuxPower ∧ totalAuxPower ≤ 69.7e6 := by
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  have hpp1 : (3.1415 : ℝ) ^ 2 ≤ Real.pi ^ 2 := by gcongr
  have hpp2 : Real.pi ^ 2 ≤ (3.1416 : ℝ) ^ 2 := by gcongr
  unfold totalAuxPower
  rw [auxRate_integral, heatCap_eq]
  unfold volumeDeriv majorRadius minorRadius
  constructor <;> nlinarith

/-! ### Transport coefficients -/

/-- Flux-surface-averaged coefficients on the cylinder for reactivity `sv` and diffusivity
`χ`: `V' = 2π²R₀a²`, `V'' = 0`, `D = 4χψ/a²`, `D' = 4χ/a²`, `R = netSource sv` posed for
`T > 0`, and a `degenerate` axis (`D(0) = 0`, no axis condition). -/
@[expose] def cylCoeffs (sv : ℝ → ℝ) (χ : ℝ) : RadialCoefficients where
  Vp := fun _ => volumeDeriv
  dVp := fun _ => 0
  D := fun ψ _ => 4 * χ * ψ / minorRadius ^ 2
  dD := fun _ _ => 4 * χ / minorRadius ^ 2
  dDT := fun _ _ => 0
  R := netSource sv
  Tdom := Ioi 0
  axis := .degenerate

/-- The supplied coefficient derivatives are genuine: `V'' = 0` and `D' = 4χ/a²` (at every
temperature; the cylinder coefficients are semilinear). -/
theorem cylCoeffs_derivs (sv : ℝ → ℝ) (χ ψ T : ℝ) :
    HasDerivAt (cylCoeffs sv χ).Vp ((cylCoeffs sv χ).dVp ψ) ψ ∧
      HasDerivAt (fun x => (cylCoeffs sv χ).D x T) ((cylCoeffs sv χ).dD ψ T) ψ := by
  refine ⟨hasDerivAt_const _ _, ?_⟩
  have := ((hasDerivAt_id ψ).const_mul (4 * χ)).div_const (minorRadius ^ 2)
  convert this using 1
  · funext x; simp [cylCoeffs]
  · simp [cylCoeffs]

/-- The cylinder operator: `N[T] = (4χ/a²)(ψ T'' + T') + R(ψ,T)`, i.e. the cylindrical
Laplacian `χ r⁻¹ ∂r(r ∂r T)` in the variable `ψ = r²/a²`. -/
theorem cylCoeffs_op (sv : ℝ → ℝ) (χ ψ u uψ uψψ : ℝ) :
    (cylCoeffs sv χ).op ψ u uψ uψψ =
      4 * χ / minorRadius ^ 2 * (ψ * uψψ + uψ) + netSource sv ψ u := by
  simp only [RadialCoefficients.op, cylCoeffs, mul_zero, zero_div, add_zero, zero_mul]; ring

/-- The cylinder coefficients with constant `χ` are semilinear (temperature-independent
`D`). -/
theorem cylCoeffs_isSemilinear (sv : ℝ → ℝ) (χ : ℝ) : (cylCoeffs sv χ).IsSemilinear :=
  fun _ _ _ _ => ⟨rfl, rfl, rfl⟩

/-- `D ≥ 0` on `[0,1]` for `χ ≥ 0`. -/
theorem cylCoeffs_D_nonneg (sv : ℝ → ℝ) {χ : ℝ} (hχ : 0 ≤ χ) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ T : ℝ, 0 ≤ (cylCoeffs sv χ).D ψ T := fun ψ hψ _ => by
  simp only [cylCoeffs, minorRadius]; have := hψ.1; positivity

/-- The axis is degenerate: `D(0) = 0` and `D'(0) = 4χ/a² ≥ 0`. -/
theorem cylCoeffs_degenerateAxis (sv : ℝ → ℝ) {χ : ℝ} (hχ : 0 ≤ χ) :
    DegenerateAxis (cylCoeffs sv χ) :=
  ⟨fun _ => by simp [cylCoeffs], fun _ => by simp only [cylCoeffs, minorRadius]; positivity,
    fun _ => rfl⟩

/-- The net source is jointly continuous on `[0,1] × (0,∞)` (continuity of the supplied
reactivity on `T > 0`, of `√T` and of the polynomial deposition). -/
theorem netSource_continuousOn (sv : ℝ → ℝ) [BoschHaleDT sv] :
    ContinuousOn (fun p : ℝ × ℝ => (cylCoeffs sv 0).R p.1 p.2) (Icc 0 1 ×ˢ Ioi 0) := by
  have hsv : ContinuousOn (fun p : ℝ × ℝ => sv p.2) (Icc 0 1 ×ˢ Ioi 0) :=
    (BoschHaleDT.continuousOn (sv := sv)).comp continuous_snd.continuousOn
      (fun p hp => hp.2)
  have hrest : Continuous (fun p : ℝ × ℝ =>
      QPoly.eval auxRateCoeffs p.1 - bremsRate * Real.sqrt p.2) :=
    ((QPoly.continuous_eval _).comp continuous_fst).sub
      (continuous_const.mul (Real.continuous_sqrt.comp continuous_snd))
  have : ContinuousOn (fun p : ℝ × ℝ => alphaRate * sv p.2 +
      (QPoly.eval auxRateCoeffs p.1 - bremsRate * Real.sqrt p.2)) (Icc 0 1 ×ˢ Ioi 0) :=
    (continuousOn_const.mul hsv).add hrest.continuousOn
  refine this.congr (fun p _ => ?_)
  simp only [cylCoeffs, netSource_eq]; ring

/-- The source does not depend on `χ`. -/
theorem cylCoeffs_R (sv : ℝ → ℝ) (χ : ℝ) : (cylCoeffs sv χ).R = (cylCoeffs sv 0).R := rfl

/-- **The cylinder is a kernel instance** (kernel change 2026-10-20): for `χ ≥ 0` the
coefficients satisfy `TransportLaws` with `D ≥ 0`, `D(0) = 0` at the degenerate axis, and the
source continuous on `[0,1] × (0,∞)`. -/
theorem cylCoeffs_transportLaws (sv : ℝ → ℝ) [BoschHaleDT sv] {χ : ℝ} (hχ : 0 ≤ χ) :
    TransportLaws (cylCoeffs sv χ) where
  Vp_pos := fun _ _ => volumeDeriv_pos
  Vp_deriv := fun ψ _ => (cylCoeffs_derivs sv χ ψ 0).1.hasDerivWithinAt
  D_deriv := fun ψ _ T => (cylCoeffs_derivs sv χ ψ T).2.hasDerivWithinAt
  DT_deriv := fun _ _ T => hasDerivAt_const T _
  D_nonneg := cylCoeffs_D_nonneg sv hχ
  D_axis := fun _ _ => by simp [cylCoeffs]
  D_axis_regular := fun h => absurd h (by simp [cylCoeffs])
  Tdom_open := isOpen_Ioi
  R_cont := netSource_continuousOn sv

/-! ### Reactivity floors from the Bosch–Hale windows -/

/-- Reactivity floor for the label `k` (keV): the lower enclosure `svLo` of the Bosch–Hale
window starting at `k`, or `0` if there is none. -/
@[expose] def svFloor (k : ℚ) : ℚ :=
  match boschHaleWindows.find? (fun w => w.lo == k) with
  | some w => w.svLo
  | none => 0

/-- Every supplied window starts at `≥ 1 keV` and is nondegenerate. -/
theorem boschHaleWindows_wf :
    boschHaleWindows.all (fun w => decide (1 ≤ w.lo) && decide (w.lo ≤ w.hi)) = true := by
  kernel_fact

/-- **Reactivity floor.** If `0 ≤ k ≤ T ≤ 60` keV then `svFloor k ≤ ⟨σv⟩(T)`: the window at
`k` bounds `⟨σv⟩(k)` below, and `⟨σv⟩` is increasing on `[1,60]` keV. -/
theorem svFloor_le (sv : ℝ → ℝ) [BoschHaleDT sv] {k : ℚ} (hk : 0 ≤ k) {T : ℝ}
    (hkT : (k : ℝ) ≤ T) (hT : T ≤ 60) : (svFloor k : ℝ) ≤ sv T := by
  unfold svFloor
  split
  · rename_i w h
    have hmem := List.mem_of_find?_eq_some h
    have hlo : w.lo = k := by simpa using List.find?_some h
    have hwf := List.all_eq_true.1 boschHaleWindows_wf w hmem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hwf
    have h1 : (1 : ℝ) ≤ k := by rw [← hlo]; exact_mod_cast hwf.1
    have hw := (BoschHaleDT.windows (sv := sv) w hmem (k : ℝ) (by rw [hlo]) (by
      rw [← hlo]; exact_mod_cast hwf.2)).1
    have hmono := BoschHaleDT.monotoneOn (sv := sv) ⟨h1, hkT.trans hT⟩
      ⟨h1.trans hkT, hT⟩ hkT
    linarith
  · simp only [Rat.cast_zero]
    exact BoschHaleDT.nonneg T ((by exact_mod_cast hk : (0 : ℝ) ≤ k).trans hkT)

/-- **Reactivity ceiling.** `⟨σv⟩(T) ≤ 9.037·10⁻²² m³/s` for `T ∈ [1,100]` keV
(monotone up to 60 keV, then the windows `[60,80]` and `[80,100]`). -/
theorem sv_le_ceiling (sv : ℝ → ℝ) [BoschHaleDT sv] {T : ℝ} (h1 : 1 ≤ T) (h2 : T ≤ 100) :
    sv T ≤ (9.037e-22 : ℝ) := by
  have w60 := (BoschHaleDT.windows (sv := sv) ⟨59, 60, 8.805e-22, 8.997e-22⟩
    (by simp [boschHaleWindows]) 60 (by norm_num) (by norm_num)).2
  have w80 := BoschHaleDT.windows (sv := sv) ⟨60, 80, 8.749e-22, 9.037e-22⟩
    (by simp [boschHaleWindows])
  have w100 := BoschHaleDT.windows (sv := sv) ⟨80, 100, 8.363e-22, 8.927e-22⟩
    (by simp [boschHaleWindows])
  norm_num at w60
  rcases le_or_gt T 60 with h | h
  · have := BoschHaleDT.monotoneOn (sv := sv) ⟨h1, h⟩ ⟨by norm_num, le_rfl⟩ h
    linarith
  rcases le_or_gt T 80 with h' | h'
  · have := (w80 T (by norm_num; exact h.le) (by norm_num; exact h')).2
    norm_num at this ⊢; linarith
  · have := (w100 T (by norm_num; exact h'.le) (by norm_num; exact h2)).2
    norm_num at this ⊢; linarith

/-! ### The lower barrier profile and its certificate -/

/-- Coefficients of the lower barrier `T_sub(ψ) = T₀ − 8 ∫₀^ψ s(x)/x dx` with
`s(x) = 1 − (1−x)¹⁰ − 10x(1−x)⁹`, `T₀ = 5176/315`, so that `T_sub(1) = 1`,
`T_sub'(0) = 0` and `ψ T_sub'' + T_sub' = −720 ψ (1−ψ)⁸`. Found by a Python search. -/
@[expose] def tsubCoeffs : List ℚ :=
  [5176 / 315, 0, -180, 640, -1260, 8064 / 5, -1400, 5760 / 7, -315, 640 / 9, -36 / 5]

/-- The lower barrier profile `T_sub` (keV). -/
@[expose] def Tsub (ψ : ℝ) : ℝ := QPoly.eval tsubCoeffs ψ

/-- `T_sub'`. -/
@[expose] def Tsub' (ψ : ℝ) : ℝ := QPoly.eval (QPoly.deriv tsubCoeffs) ψ

/-- `T_sub''`. -/
@[expose] def Tsub'' (ψ : ℝ) : ℝ := QPoly.eval (QPoly.deriv (QPoly.deriv tsubCoeffs)) ψ

/-- `T_sub` is a regular profile with derivatives `T_sub'`, `T_sub''`. -/
theorem tsub_regular : ProfileRegular Tsub Tsub' Tsub'' :=
  ⟨fun ψ _ => (QPoly.hasDerivAt_eval _ ψ).hasDerivWithinAt,
    fun ψ _ => (QPoly.hasDerivAt_eval _ ψ).hasDerivWithinAt⟩

/-- Boundary values: `T_sub(0) = 5176/315 ≈ 16.43 keV`, `T_sub'(0) = 0`, `T_sub(1) = 1 keV`,
`T_sub'(1) = −8`. -/
theorem tsub_values :
    Tsub 0 = 5176 / 315 ∧ Tsub' 0 = 0 ∧ Tsub 1 = 1 ∧ Tsub' 1 = -8 := by
  simp only [Tsub, Tsub']
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [tsubCoeffs, QPoly.evalQ, QPoly.deriv, QPoly.add]

/-- The conductive part: `ψ T_sub'' + T_sub' = −720 ψ (1−ψ)⁸ ≤ 0`. -/
theorem tsub_flux_div (ψ : ℝ) : ψ * Tsub'' ψ + Tsub' ψ = -720 * ψ * (1 - ψ) ^ 8 := by
  simp [Tsub', Tsub'', tsubCoeffs, QPoly.deriv, QPoly.add]; ring

/-- Monotonicity certificate: `−T_sub' ≥ 0` on `[0,1]` (6 pieces). -/
theorem tsub_deriv_check :
    QPoly.checkOn (QPoly.scale (-1) (QPoly.deriv tsubCoeffs)) 0 0 1
      [1 / 6, 2 / 6, 3 / 6, 4 / 6, 5 / 6, 1] = true := by
  kernel_fact

/-- `T_sub` is decreasing on `[0,1]`. -/
theorem tsub_antitone : AntitoneOn Tsub (Icc 0 1) := by
  have := antitoneOn_eval_of_check tsub_deriv_check
  intro a ha b hb hab
  exact this (by simpa using ha) (by simpa using hb) hab

/-- `1 ≤ T_sub ≤ 5176/315 < 60` on `[0,1]`. -/
theorem tsub_bounds {ψ : ℝ} (hψ : ψ ∈ Icc (0 : ℝ) 1) : 1 ≤ Tsub ψ ∧ Tsub ψ ≤ 5176 / 315 := by
  obtain ⟨h0, -, h1, -⟩ := tsub_values
  refine ⟨h1 ▸ tsub_antitone hψ ⟨zero_le_one, le_rfl⟩ hψ.2,
    h0 ▸ tsub_antitone ⟨le_rfl, zero_le_one⟩ hψ hψ.1⟩

/-- **Core temperature.** `T_sub ≥ 10 keV` on the core `ψ ≤ 3/10` (`r ≤ 1.37 m`). -/
theorem tsub_core {ψ : ℝ} (h0 : 0 ≤ ψ) (h1 : ψ ≤ 3 / 10) : 10 ≤ Tsub ψ := by
  have hc : (10 : ℝ) ≤ Tsub (3 / 10) := by
    have : (10 : ℚ) ≤ QPoly.evalQ tsubCoeffs (3 / 10) := by kernel_fact
    simp only [Tsub]
    rw [show ((3 : ℝ) / 10) = ((3 / 10 : ℚ) : ℝ) by norm_num, QPoly.eval_cast]
    exact_mod_cast this
  exact hc.trans (tsub_antitone ⟨h0, h1.trans (by norm_num)⟩ ⟨by norm_num, by norm_num⟩ h1)

/-- Upper limit `χ_max = 1/2 m²/s` of the diffusivity range; `4χ_max/a² = 8/25` s⁻¹. -/
@[expose] def chiMax : ℝ := 1 / 2

/-- Polynomial lower bound for `N[T_sub]` **without** alpha heating, at `χ = χ_max`:
`(8/25)(ψT'' + T') + q_aux − (201/1000)(T + 4)/4` (bremsstrahlung via `√T ≤ (T+4)/4`). -/
@[expose] def residualLB : List ℚ :=
  QPoly.add (QPoly.add (QPoly.scale (8 / 25)
      (QPoly.add (QPoly.mul [0, 1] (QPoly.deriv (QPoly.deriv tsubCoeffs)))
        (QPoly.deriv tsubCoeffs))) auxRateCoeffs)
    (QPoly.scale (-(201 / 1000) / 4) (QPoly.add tsubCoeffs [4]))

/-- Explicit form of `residualLB`. -/
theorem residualLB_eval (ψ : ℝ) : QPoly.eval residualLB ψ =
    8 / 25 * (ψ * Tsub'' ψ + Tsub' ψ) + QPoly.eval auxRateCoeffs ψ
      - 201 / 1000 / 4 * (Tsub ψ + 4) := by
  simp [residualLB, Tsub, Tsub', Tsub'']; ring

/-- Alpha-heating bonus for the label `k`: `2.29·10²² · svFloor k` keV/s. -/
@[expose] def alphaBonus (k : ℚ) : ℚ := 229 / 10 * 10 ^ 21 * svFloor k

/-- The pieces `(right end, temperature label)` of the lower-barrier certificate: `T_sub`
crosses `15, 14, …, 2` keV at the right ends (rounded down to `10⁻⁴`); the last piece uses
no alpha heating. -/
@[expose] def tsubPieces : List (ℚ × ℚ) :=
  [(537 / 10000, 15), (537 / 5000, 15), (94 / 625, 14), (477 / 2500, 13), (2311 / 10000, 12),
    (109 / 400, 11), (1581 / 5000, 10), (3633 / 10000, 9), (2073 / 5000, 8), (2357 / 5000, 7),
    (5349 / 10000, 6), (379 / 625, 5), (859 / 1250, 4), (1947 / 2500, 3), (1103 / 1250, 2),
    (1, 0)]

/-- The certificate pieces cover `[0,1]`. -/
theorem tsubPieces_end : pieceEnd 0 tsubPieces = 1 := by
  simp [pieceEnd, tsubPieces]

/-- **The exact rational certificate** (16 pieces, kernel-checked): on each piece the
alpha-free lower bound plus the alpha bonus at the piece label is at least `κ = 1/20`. -/
theorem tsub_pieceCheck :
    pieceCheck residualLB tsubCoeffs (1 / 20) alphaBonus 0 tsubPieces = true := by
  kernel_fact

/-- All piece labels are nonnegative. -/
theorem tsubPieces_labels : tsubPieces.all (fun p => decide (0 ≤ p.2)) = true := by
  kernel_fact

/-- `√T ≤ (T+4)/4` for `T ≥ 0` (AM–GM). -/
theorem sqrt_le_quarter {T : ℝ} (hT : 0 ≤ T) : Real.sqrt T ≤ (T + 4) / 4 := by
  nlinarith [Real.sq_sqrt hT, sq_nonneg (Real.sqrt T - 2)]

/-- **Barrier margin.** For every supplied reactivity and every `χ ≤ 1/2` m²/s,
`N[T_sub](ψ) ≥ 1/20 keV/s` on `[0,1]` (smaller `χ` only helps, since `ψT'' + T' ≤ 0`; the
inequality even holds formally for `χ < 0`, though only `χ ≥ 0` is physical and the
comparison theorems require it). -/
theorem tsub_margin (sv : ℝ → ℝ) [BoschHaleDT sv] {χ : ℝ} (hχ : χ ≤ chiMax) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, (1 / 20 : ℝ) ≤ (cylCoeffs sv χ).op ψ (Tsub ψ) (Tsub' ψ) (Tsub'' ψ) := by
  intro ψ hψ
  obtain ⟨k, ⟨d, hmem⟩, hkT, hQ⟩ := pieceCheck_sound 0 tsubPieces tsub_pieceCheck
    (by simp [tsubPieces])
    (fun a ha b hb hab => tsub_antitone (by simpa [tsubPieces_end] using ha)
      (by simpa [tsubPieces_end] using hb) hab) ψ
    (by simpa [tsubPieces_end] using hψ)
  change (k : ℝ) ≤ Tsub ψ at hkT
  have hk0 : (0 : ℚ) ≤ k := by
    have := List.all_eq_true.1 tsubPieces_labels (d, k) hmem
    simpa using this
  obtain ⟨hT1, hT2⟩ := tsub_bounds hψ
  have hfl := svFloor_le sv hk0 hkT (by linarith)
  have hsv0 : 0 ≤ sv (Tsub ψ) := BoschHaleDT.nonneg _ (by linarith)
  have hfl0 : (0 : ℝ) ≤ 229 / 10 * 10 ^ 21 := by norm_num
  have hα : (229 / 10 * 10 ^ 21 : ℝ) * svFloor k ≤ alphaRate * sv (Tsub ψ) :=
    (mul_le_mul_of_nonneg_left hfl hfl0).trans
      (mul_le_mul_of_nonneg_right alphaRate_ge hsv0)
  have hsq := sqrt_le_quarter (T := Tsub ψ) (by linarith)
  have hbr : bremsRate * Real.sqrt (Tsub ψ) ≤ 201 / 1000 * ((Tsub ψ + 4) / 4) :=
    mul_le_mul bremsRate_le hsq (Real.sqrt_nonneg _) (by norm_num)
  have hG : ψ * Tsub'' ψ + Tsub' ψ ≤ 0 := by
    rw [tsub_flux_div]
    have : 0 ≤ ψ * (1 - ψ) ^ 8 := mul_nonneg hψ.1 (pow_nonneg (by linarith [hψ.2]) _)
    nlinarith
  have hd : 4 * χ / minorRadius ^ 2 ≤ 8 / 25 := by
    unfold minorRadius; unfold chiMax at hχ; rw [div_le_iff₀ (by norm_num)]; nlinarith
  have hcond : 8 / 25 * (ψ * Tsub'' ψ + Tsub' ψ) ≤
      4 * χ / minorRadius ^ 2 * (ψ * Tsub'' ψ + Tsub' ψ) :=
    mul_le_mul_of_nonpos_right hd hG
  have hQ' := hQ
  rw [residualLB_eval] at hQ'
  simp only [alphaBonus, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_one] at hQ'
  rw [cylCoeffs_op, netSource_eq]
  linarith

/-! ### The all-time lower barrier (goal G2, rung M2) -/

/-- **M2 core-temperature barrier (goal G2).** For every reactivity satisfying the supplied
Bosch–Hale enclosures, every prescribed diffusivity `χ ∈ [0, 1/2]` m²/s, and every axis-free
classical solution of the cylinder transport law on all horizons, if initially
`T(ψ,0) ≥ T_sub(ψ)` and the edge temperature stays `≥ 1 keV`, then `T(ψ,t) ≥ T_sub(ψ)` for
all `ψ ∈ [0,1]`, `t ≥ 0`; in particular the core `ψ ≤ 3/10` stays at `T ≥ 10 keV` forever. -/
theorem m2_core_barrier (sv : ℝ → ℝ) [BoschHaleDT sv] {χ : ℝ} (hχ0 : 0 ≤ χ)
    (hχ : χ ≤ chiMax) {Tedge : ℝ → ℝ} {u : RadialField}
    (hu : ∀ τ, 0 ≤ τ → AxisFreeSolution (cylCoeffs sv χ) Tedge τ u)
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, Tsub ψ ≤ u.T ψ 0) (hedge : ∀ t, 0 ≤ t → 1 ≤ Tedge t) :
    (∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → Tsub ψ ≤ u.T ψ t) ∧
      ∀ ψ, 0 ≤ ψ → ψ ≤ 3 / 10 → ∀ t, 0 ≤ t → 10 ≤ u.T ψ t := by
  have hlow : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → Tsub ψ ≤ u.T ψ t :=
    le_of_lowerMargin_axisFree_forall_time (cylCoeffs_D_nonneg sv hχ0)
      (cylCoeffs_degenerateAxis sv hχ0) (cylCoeffs_isSemilinear sv χ) hu tsub_regular
      (netSource_continuousOn sv)
      (fun ψ hψ => by linarith [(tsub_bounds hψ).1]) (by norm_num) (tsub_margin sv hχ) h0
      (fun t ht => by rw [tsub_values.2.2.1]; exact hedge t ht)
  refine ⟨hlow, fun ψ h0' h1' t ht => ?_⟩
  exact (tsub_core h0' h1').trans (hlow ψ ⟨h0', h1'.trans (by norm_num)⟩ t ht)

/-- **M2 as a kernel theorem.** The same barrier for solutions of the kernel law
`ClassicalRadialSolution` (since the 2026-10-20 kernel change the cylinder has a `degenerate`
axis, so no axis condition is imposed). Proved directly from the kernel-level theorem
`le_of_isStrictLowerBarrier_margin_forall_time` and the instance `cylCoeffs_transportLaws`. -/
theorem m2_core_barrier_kernel (sv : ℝ → ℝ) [BoschHaleDT sv] {χ : ℝ} (hχ0 : 0 ≤ χ)
    (hχ : χ ≤ chiMax) {Tedge : ℝ → ℝ} {u : RadialField}
    (hu : ∀ τ, 0 ≤ τ → ClassicalRadialSolution (cylCoeffs sv χ) Tedge τ u)
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, Tsub ψ ≤ u.T ψ 0) (hedge : ∀ t, 0 ≤ t → 1 ≤ Tedge t) :
    (∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → Tsub ψ ≤ u.T ψ t) ∧
      ∀ ψ, 0 ≤ ψ → ψ ≤ 3 / 10 → ∀ t, 0 ≤ t → 10 ≤ u.T ψ t := by
  have hL := cylCoeffs_transportLaws sv hχ0
  have hlow : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → Tsub ψ ≤ u.T ψ t :=
    le_of_isStrictLowerBarrier_margin_forall_time
      (fun τ hτ => { hL, hu τ hτ with }) (cylCoeffs_isSemilinear sv χ) tsub_regular
      (fun h => absurd h (by simp [cylCoeffs]))
      (fun ψ hψ => show 0 < Tsub ψ by linarith [(tsub_bounds hψ).1]) (by norm_num)
      (tsub_margin sv hχ) h0 (fun t ht => by rw [tsub_values.2.2.1]; exact hedge t ht)
  refine ⟨hlow, fun ψ h0' h1' t ht => ?_⟩
  exact (tsub_core h0' h1').trans (hlow ψ ⟨h0', h1'.trans (by norm_num)⟩ t ht)

/-- The kernel and axis-free formulations of M2 agree: for the cylinder, axis-free solutions
are kernel solutions (`AxisFreeSolution.classical`), so `m2_core_barrier` also follows from the
kernel theorem. -/
theorem m2_core_barrier_of_kernel (sv : ℝ → ℝ) [BoschHaleDT sv] {χ : ℝ} (hχ0 : 0 ≤ χ)
    (hχ : χ ≤ chiMax) {Tedge : ℝ → ℝ} {u : RadialField}
    (hu : ∀ τ, 0 ≤ τ → AxisFreeSolution (cylCoeffs sv χ) Tedge τ u)
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, Tsub ψ ≤ u.T ψ 0) (hedge : ∀ t, 0 ≤ t → 1 ≤ Tedge t) :
    (∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → Tsub ψ ≤ u.T ψ t) ∧
      ∀ ψ, 0 ≤ ψ → ψ ≤ 3 / 10 → ∀ t, 0 ≤ t → 10 ≤ u.T ψ t :=
  m2_core_barrier_kernel sv hχ0 hχ (fun τ hτ => (hu τ hτ).classical rfl) h0 hedge

/-! ### A crude but honest upper barrier and the exhaust power -/

/-- Lower limit `χ_min = 9/20 m²/s` for the upper barrier; `4χ_min/a² = 36/125` s⁻¹. -/
@[expose] def chiMin : ℝ := 9 / 20

/-- Upper barrier `g(ψ) = 1 + 96 (1 − ψ)` keV (axis value 97 keV). -/
@[expose] def gUp (ψ : ℝ) : ℝ := 1 + 96 * (1 - ψ)

/-- `g` is a regular profile with `g' = −96`, `g'' = 0`. -/
theorem gUp_regular : ProfileRegular gUp (fun _ => -96) (fun _ => 0) := by
  refine ⟨fun ψ _ => ?_, fun ψ _ => hasDerivWithinAt_const _ _ _⟩
  have h : HasDerivAt (fun x : ℝ => 97 + -96 * x) (-96) ψ := by
    simpa using ((hasDerivAt_id ψ).const_mul (-96 : ℝ)).const_add 97
  have he : gUp = fun x : ℝ => 97 + -96 * x := by funext x; unfold gUp; ring
  rw [he]; exact h.hasDerivWithinAt

/-- Grid with 42 equal steps on `[0,1]`. -/
@[expose] def grid42 : List ℚ := (List.range 42).map (fun i : ℕ => ((i : ℚ) + 1) / 42)

/-- Certificate: `q_aux ≤ 32/5` keV/s on `[0,1]` (42 pieces). -/
theorem auxRate_check :
    QPoly.checkOn (QPoly.add [32 / 5] (QPoly.scale (-1) auxRateCoeffs)) 0 0 1 grid42 = true := by
  kernel_fact

/-- `q_aux ≤ 6.4` keV/s on `[0,1]` (maximum ≈ 6.23 at `ψ = 1/9`). -/
theorem auxRate_le {ψ : ℝ} (hψ : ψ ∈ Icc (0 : ℝ) 1) : QPoly.eval auxRateCoeffs ψ ≤ 32 / 5 := by
  have := QPoly.checkOn_sound auxRate_check ψ (by simpa using hψ)
  simp only [QPoly.eval_add, QPoly.eval_scale, QPoly.eval_cons, QPoly.eval_nil] at this
  push_cast at this; linarith

/-- **Upper-barrier margin.** For `χ ≥ 9/20` m²/s, `N[g] ≤ −1/2 keV/s` on `[0,1]`:
conduction `(4χ/a²)·96 ≥ 27.6` beats alpha heating `≤ 2.291·10²² · 9.037·10⁻²² ≈ 20.7`
plus auxiliary heating `≤ 6.4` (bremsstrahlung is dropped). -/
theorem gUp_margin (sv : ℝ → ℝ) [BoschHaleDT sv] {χ : ℝ} (hχ : chiMin ≤ χ) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, (cylCoeffs sv χ).op ψ (gUp ψ) (-96) 0 ≤ -(1 / 2) := by
  intro ψ hψ
  have hg1 : 1 ≤ gUp ψ := by unfold gUp; linarith [hψ.2]
  have hg2 : gUp ψ ≤ 100 := by unfold gUp; linarith [hψ.1]
  have hsv := sv_le_ceiling sv hg1 hg2
  have hsv0 : 0 ≤ sv (gUp ψ) := BoschHaleDT.nonneg _ (by linarith)
  have hα : alphaRate * sv (gUp ψ) ≤ 2291 / 100 * 10 ^ 21 * 9.037e-22 :=
    mul_le_mul alphaRate_le hsv hsv0 (by norm_num)
  have hbr : 0 ≤ bremsRate * Real.sqrt (gUp ψ) :=
    mul_nonneg bremsRate_nonneg (Real.sqrt_nonneg _)
  have haux := auxRate_le hψ
  have hd : 36 / 125 ≤ 4 * χ / minorRadius ^ 2 := by
    unfold minorRadius; unfold chiMin at hχ; rw [le_div_iff₀ (by norm_num)]; nlinarith
  rw [cylCoeffs_op, netSource_eq]
  nlinarith

/-- **M2 upper barrier.** For every `χ ≥ 9/20` m²/s: if
`T(ψ,0) ≤ 1 + 96(1−ψ)` and `T_edge ≤ 1 keV`, then `T(ψ,t) ≤ 1 + 96(1−ψ)` for all `t ≥ 0`
(so `T ≤ 97 keV` everywhere). -/
theorem m2_upper_barrier (sv : ℝ → ℝ) [BoschHaleDT sv] {χ : ℝ} (hχ : chiMin ≤ χ)
    {Tedge : ℝ → ℝ} {u : RadialField}
    (hu : ∀ τ, 0 ≤ τ → AxisFreeSolution (cylCoeffs sv χ) Tedge τ u)
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, u.T ψ 0 ≤ gUp ψ) (hedge : ∀ t, 0 ≤ t → Tedge t ≤ 1) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → u.T ψ t ≤ gUp ψ := by
  have hχ0 : 0 ≤ χ := le_trans (by norm_num [chiMin]) hχ
  exact le_of_upperMargin_axisFree_forall_time (cylCoeffs_D_nonneg sv hχ0)
    (cylCoeffs_degenerateAxis sv hχ0) (cylCoeffs_isSemilinear sv χ) hu gUp_regular
    (netSource_continuousOn sv)
    (fun ψ hψ => by unfold gUp; linarith [hψ.2]) (κ := 1 / 2) (by norm_num)
    (fun ψ hψ => by simpa using gUp_margin sv hχ ψ hψ) h0
    (fun t ht => by simpa [gUp] using hedge t ht)

/-- Conductive power to the wall (W) at time `t`:
`P = heatCap · V' · D(1) · (−∂ψT(1,t)) = heatCap · 8π²R₀χ · (−∂ψT(1,t))`. -/
@[expose] def exhaustPower (χ : ℝ) (u : RadialField) (t : ℝ) : ℝ :=
  heatCap * volumeDeriv * (4 * χ * 1 / minorRadius ^ 2) * -u.Tψ 1 t

/-- **Edge slope from touching barriers.** If at time `t` the field lies between `T_sub` and
`g` on `[0,1]` and `T(1,t) = 1 keV` (where both barriers equal `1`), then
`−96 ≤ ∂ψT(1,t) ≤ T_sub'(1) = −8`. -/
theorem edge_slope_bounds {τ t : ℝ} {u : RadialField} (hreg : u.Regular τ) (ht : t ∈ Icc 0 τ)
    (hlow : ∀ ψ ∈ Icc (0 : ℝ) 1, Tsub ψ ≤ u.T ψ t)
    (hup : ∀ ψ ∈ Icc (0 : ℝ) 1, u.T ψ t ≤ gUp ψ) (h1 : u.T 1 t = 1) :
    -96 ≤ u.Tψ 1 t ∧ u.Tψ 1 t ≤ -8 := by
  have hT1 : Tsub 1 = 1 := tsub_values.2.2.1
  have hd := hreg.deriv_ψ t ht 1 ⟨zero_le_one, le_rfl⟩
  constructor
  · have := deriv_nonpos_of_leftMin (g := fun x => gUp x - u.T x t) zero_lt_one le_rfl
      ((gUp_regular.deriv 1 ⟨zero_le_one, le_rfl⟩).sub hd)
      (fun x hx => by
        have := hup x ⟨hx.1, hx.2.le⟩
        simp only [gUp, h1] at this ⊢
        linarith)
    linarith
  · have := deriv_nonpos_of_leftMin (g := fun x => u.T x t - Tsub x) zero_lt_one le_rfl
      (hd.sub (tsub_regular.deriv 1 ⟨zero_le_one, le_rfl⟩))
      (fun x hx => by
        simp only [h1, hT1, sub_self]
        linarith [hlow x ⟨hx.1, hx.2.le⟩])
    linarith [tsub_values.2.2.2]

/-- **M2 exhaust power.** For `χ ∈ [9/20, 1/2]`, edge temperature `≡ 1 keV` and initial data
between the barriers, the conductive power to the wall satisfies, for all `t ≥ 0`,
`8 · heatCap·V'·4χ/a² ≤ P(t) ≤ 96 · heatCap·V'·4χ/a²`. -/
theorem m2_exhaust_power (sv : ℝ → ℝ) [BoschHaleDT sv] {χ : ℝ} (hχ1 : chiMin ≤ χ)
    (hχ2 : χ ≤ chiMax) {u : RadialField}
    (hu : ∀ τ, 0 ≤ τ → AxisFreeSolution (cylCoeffs sv χ) (fun _ => 1) τ u)
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, Tsub ψ ≤ u.T ψ 0 ∧ u.T ψ 0 ≤ gUp ψ) {t : ℝ} (ht : 0 ≤ t) :
    8 * (heatCap * volumeDeriv * (4 * χ / minorRadius ^ 2)) ≤ exhaustPower χ u t ∧
      exhaustPower χ u t ≤ 96 * (heatCap * volumeDeriv * (4 * χ / minorRadius ^ 2)) := by
  have hχ0 : 0 ≤ χ := le_trans (by norm_num [chiMin]) hχ1
  have hlow := (m2_core_barrier sv hχ0 hχ2 hu (fun ψ hψ => (h0 ψ hψ).1)
    (fun _ _ => le_rfl)).1
  have hup := m2_upper_barrier sv hχ1 hu (fun ψ hψ => (h0 ψ hψ).2) (fun _ _ => le_rfl)
  obtain ⟨hs1, hs2⟩ := edge_slope_bounds (hu t ht).regular ⟨ht, le_rfl⟩
    (fun ψ hψ => hlow ψ hψ t ht) (fun ψ hψ => hup ψ hψ t ht) ((hu t ht).edge t ⟨ht, le_rfl⟩)
  have hX : 0 ≤ heatCap * volumeDeriv * (4 * χ / minorRadius ^ 2) := by
    have := heatCap_pos; have := volumeDeriv_pos
    unfold minorRadius; positivity
  unfold exhaustPower
  rw [mul_one]
  constructor <;> nlinarith

/-- Numeric form: for `χ ∈ [9/20, 1/2]` the exhaust power lies in `[83 MW, 1.12 GW]`. -/
theorem m2_exhaust_power_numeric (sv : ℝ → ℝ) [BoschHaleDT sv] {χ : ℝ} (hχ1 : chiMin ≤ χ)
    (hχ2 : χ ≤ chiMax) {u : RadialField}
    (hu : ∀ τ, 0 ≤ τ → AxisFreeSolution (cylCoeffs sv χ) (fun _ => 1) τ u)
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, Tsub ψ ≤ u.T ψ 0 ∧ u.T ψ 0 ≤ gUp ψ) {t : ℝ} (ht : 0 ≤ t) :
    (8.3e7 : ℝ) ≤ exhaustPower χ u t ∧ exhaustPower χ u t ≤ 1.12e9 := by
  obtain ⟨h1, h2⟩ := m2_exhaust_power sv hχ1 hχ2 hu h0 ht
  have hp1 := Real.pi_gt_d2
  have hp2 := Real.pi_lt_d4
  have hpp1 : (3.14 : ℝ) ^ 2 ≤ Real.pi ^ 2 := by gcongr
  have hpp2 : Real.pi ^ 2 ≤ (3.1416 : ℝ) ^ 2 := by gcongr
  unfold chiMin at hχ1; unfold chiMax at hχ2
  have hprod1 : (3.14 : ℝ) ^ 2 * (9 / 20) ≤ Real.pi ^ 2 * χ :=
    mul_le_mul hpp1 hχ1 (by norm_num) (by positivity)
  have hprod2 : Real.pi ^ 2 * χ ≤ (3.1416 : ℝ) ^ 2 * (1 / 2) :=
    mul_le_mul hpp2 hχ2 (by linarith) (by norm_num)
  have key : heatCap * volumeDeriv * (4 * χ / minorRadius ^ 2) =
      (3 / 2 * 1e20 * (1 + 53 / 60) * 1.602176634e-16 * 2 * (13 / 2) * 4) *
        (Real.pi ^ 2 * χ) := by
    rw [heatCap_eq]; unfold volumeDeriv majorRadius minorRadius; ring
  rw [key] at h1 h2
  constructor
  · nlinarith
  · nlinarith

/-! ### Non-vacuity of the barrier hypotheses -/

/-- Coefficients of `g − T_sub`. -/
@[expose] def gapCoeffs : List ℚ := QPoly.add [97, -96] (QPoly.scale (-1) tsubCoeffs)

/-- Certificate: `g − T_sub` is decreasing on `[0,1]` (4 pieces). -/
theorem gap_deriv_check :
    QPoly.checkOn (QPoly.scale (-1) (QPoly.deriv gapCoeffs)) 0 0 1
      [1 / 4, 2 / 4, 3 / 4, 1] = true := by
  kernel_fact

/-- The barriers are ordered: `T_sub ≤ g` on `[0,1]` (they meet at the edge). -/
theorem tsub_le_gUp {ψ : ℝ} (hψ : ψ ∈ Icc (0 : ℝ) 1) : Tsub ψ ≤ gUp ψ := by
  have hanti := antitoneOn_eval_of_check gap_deriv_check
  have hev : ∀ x, QPoly.eval gapCoeffs x = gUp x - Tsub x := fun x => by
    simp [gapCoeffs, gUp, Tsub]; ring
  have := hanti (by simpa using hψ) (by simp) hψ.2
  rw [hev, hev, tsub_values.2.2.1] at this
  simp only [gUp] at this ⊢
  linarith

/-- **Inequality hypotheses only.** The profile `T_sub` with constant edge temperature
`1 keV` satisfies the *inequality* initial and edge hypotheses of the lower barrier, the
upper barrier and the exhaust-power theorem simultaneously. This does not make `T_sub`
admissible initial data (see `tsub_not_initial_data`; corner compatibility fails), and
existence of solutions is not proved. -/
theorem m2_barrier_hypotheses_satisfiable :
    (∀ ψ ∈ Icc (0 : ℝ) 1, Tsub ψ ≤ Tsub ψ ∧ Tsub ψ ≤ gUp ψ) ∧
      (∀ t : ℝ, 0 ≤ t → (1 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1) ∧ chiMin ≤ chiMax ∧ Tsub 1 = 1 ∧ gUp 1 = 1 :=
  ⟨fun ψ hψ => ⟨le_rfl, tsub_le_gUp hψ⟩, fun _ _ => ⟨le_rfl, le_rfl⟩,
    by norm_num [chiMin, chiMax], tsub_values.2.2.1, by norm_num [gUp]⟩


/-- `R(1, 1) > 0`: at the edge temperature `1 keV` the uniform auxiliary floor `0.43 keV/s`
exceeds bremsstrahlung `≤ 0.201 keV/s`. -/
theorem netSource_edge_pos (sv : ℝ → ℝ) [BoschHaleDT sv] : 0 < netSource sv 1 1 := by
  rw [netSource_eq, auxRate_eq, Real.sqrt_one]
  have := mul_nonneg (le_trans (by norm_num) alphaRate_ge)
    (BoschHaleDT.nonneg (sv := sv) 1 zero_le_one)
  nlinarith [bremsRate_le]

/-- **`T_sub` is not admissible initial data for constant edge data.** No axis-free classical
solution on `[0,τ]`, `τ > 0`, with `T_edge ≡ 1 keV` has `T(·,0) = T_sub`: corner
compatibility would force `N[T_sub](1) = 0`, but `N[T_sub](1) = R(1,1) > 0`. -/
theorem tsub_not_initial_data (sv : ℝ → ℝ) [BoschHaleDT sv] {χ τ : ℝ} (hτ : 0 < τ)
    {u : RadialField} (hu : AxisFreeSolution (cylCoeffs sv χ) (fun _ => 1) τ u)
    (hinit : ∀ ψ ∈ Icc (0 : ℝ) 1, u.T ψ 0 = Tsub ψ) : False := by
  have h0 : (0 : ℝ) ∈ Icc 0 τ := ⟨le_rfl, hτ.le⟩
  have hU := uniqueDiffOn_Icc (zero_lt_one' ℝ)
  have hψ : ∀ ψ ∈ Icc (0 : ℝ) 1, u.Tψ ψ 0 = Tsub' ψ := fun ψ hψ =>
    (hU ψ hψ).eq_deriv _ (hu.regular.deriv_ψ 0 h0 ψ hψ)
      ((tsub_regular.deriv ψ hψ).congr (fun x hx => hinit x hx) (hinit ψ hψ))
  have h1 : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hψψ : u.Tψψ 1 0 = Tsub'' 1 :=
    (hU 1 h1).eq_deriv _ (hu.regular.deriv_ψψ 0 h0 1 h1)
      ((tsub_regular.deriv2 1 h1).congr (fun x hx => hψ x hx) (hψ 1 h1))
  have hc := hu.corner_compatibility hτ (hasDerivWithinAt_const _ _ (1 : ℝ))
  rw [hinit 1 h1, hψ 1 h1, hψψ, cylCoeffs_op, tsub_flux_div, tsub_values.2.2.1] at hc
  have := netSource_edge_pos sv
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_add] at hc
  linarith

/-- **A compatible initial profile.** For every supplied reactivity and `χ ∈ (0, 1/2]` there
is `c ≥ 0` such that `T₀ = T_sub + c(1−ψ)` satisfies `T₀ ≥ T_sub` on `[0,1]`, `T₀(1) = 1`
and the corner compatibility `N[T₀](1) = 0 = T_edge'(0)` for `T_edge ≡ 1 keV` (with
`T₀' = T_sub' − c`, `T₀'' = T_sub''`). So the lower-barrier hypotheses and corner
compatibility are jointly satisfiable; existence of the solution itself is not proved. -/
theorem m2_compatible_initial_profile (sv : ℝ → ℝ) [BoschHaleDT sv] {χ : ℝ} (hχ : 0 < χ) :
    ∃ c : ℝ, 0 ≤ c ∧ (∀ ψ ∈ Icc (0 : ℝ) 1, Tsub ψ ≤ Tsub ψ + c * (1 - ψ)) ∧
      Tsub 1 + c * (1 - 1) = 1 ∧
      ProfileRegular (fun ψ => Tsub ψ + c * (1 - ψ)) (fun ψ => Tsub' ψ - c) Tsub'' ∧
      (cylCoeffs sv χ).op 1 (Tsub 1 + c * (1 - 1)) (Tsub' 1 - c) (Tsub'' 1) = 0 := by
  have hd : 0 < 4 * χ / minorRadius ^ 2 := by unfold minorRadius; positivity
  refine ⟨netSource sv 1 1 / (4 * χ / minorRadius ^ 2),
    (div_pos (netSource_edge_pos sv) hd).le, fun ψ hψ => ?_, ?_, ?_, ?_⟩
  · have : 0 ≤ netSource sv 1 1 / (4 * χ / minorRadius ^ 2) * (1 - ψ) :=
      mul_nonneg (div_pos (netSource_edge_pos sv) hd).le (by linarith [hψ.2])
    linarith
  · rw [sub_self, mul_zero, add_zero, tsub_values.2.2.1]
  · refine ⟨fun ψ hψ => ?_, fun ψ hψ => (tsub_regular.deriv2 ψ hψ).sub_const _⟩
    have := (tsub_regular.deriv ψ hψ).add
      ((((hasDerivAt_id ψ).const_sub 1).const_mul
        (netSource sv 1 1 / (4 * χ / minorRadius ^ 2))).hasDerivWithinAt)
    convert this using 1
    · funext y; simp
    · ring
  · rw [sub_self, mul_zero, add_zero, tsub_values.2.2.1, cylCoeffs_op]
    have hG := tsub_flux_div 1
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      at hG
    rw [show 1 * Tsub'' 1 + (Tsub' 1 - netSource sv 1 1 / (4 * χ / minorRadius ^ 2)) =
      (1 * Tsub'' 1 + Tsub' 1) - netSource sv 1 1 / (4 * χ / minorRadius ^ 2) by ring, hG,
      zero_sub, mul_neg, mul_div_cancel₀ _ hd.ne']
    ring

end PlasmaLean.Design.TransportBarrier
