/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.HelicalFluxGeometry
public import PlasmaLean.Design.TransportBarrier
public import PlasmaLean.Design.HelicalReactorScale

/-!
# M2 on helical geometry: an all-time core-temperature barrier with an edge χ drop

Labels: *exact helically symmetric equilibrium* (straight stellarator model, infinite aspect
ratio), *supplied flux-surface-average link* (`IsHelicalGeometry`), *synthetic reactor-scale
heating data*, Bosch–Hale reactivity as *supplied data* (kernel class `BoschHaleDT`).

## Setting

* Geometry (`HelicalFluxGeometry`): the exact helical equilibrium of `HelicalEquilibrium`
  (`a = 1/4`) scaled to `L = 8 m`, `B_axis = 5 T`, `β_axis = 4 %`, periodic length
  `ℓ = 16π m` (two helical periods); plasma `ψ̂ ≤ ψ_b = 2/25` (where `p ≥ 0`), label
  `s = ψ̂/ψ_b`, minor radius `r ∈ [2.0, 2.65] m` on the boundary (`r² ∈ [(48/61), (48/35)]·ψ_bL²`),
  volume `≈ 835 m³`. The flux geometry `G` (`V'`, `⟨|∇s|²⟩`, `⟨Δs⟩`) is **any** member of the
  class `IsHelicalGeometry`; the true helical averages are members (supplied step, see
  `HelicalFluxGeometry`). Only the proved enclosures enter:
  `⟨|∇s|²⟩ ∈ [0.97, 1.03]·A s(1 ∓ s/25)`, `⟨Δs⟩ ≤ 1.03 A`, `A = 25/32 m⁻²`.
* Plasma and source (as in the cylinder M2, `TransportBarrier.m2Plasma`): `n = 10²⁰ m⁻³`,
  `Z_eff = 1.7` (carbon), `f_fuel = 0.86`; alpha heating with the supplied reactivity,
  bremsstrahlung, and auxiliary heating `q_aux(s) = 2/5 + 40 s²(1−s)² keV/s`
  (`hAuxCoeffs`, peak `2.9 keV/s` at mid-radius) — total `63–67.8 MW` (`helAuxPower_bounds`).
* Diffusivity with an **edge drop** (pedestal-like): `χ(s) = χ₀ w(s)`, `w(s) = 1 − (19/20)s⁴`
  (`pedCoeffs`): `χ` falls to 5 % of its core value at the edge (to ≈ 61 % at `s = 0.8`), for
  every core level `χ₀ ∈ [0, 2/5] m²/s` (same 3/2-normalization as the cylinder M2:
  `χ_conv = (3/2)χ ≤ 0.6 m²/s`). The decrease of `χ` enters through the drift term `χ' g T'`
  (`≥ 0` since `χ' ≤ 0`, `T' ≤ 0`), with the lower enclosure of `⟨|∇s|²⟩`.
  **Optimistic assumption:** `χ₀ ≤ 0.4 m²/s` in the core and `χ(1) ≤ 0.02 m²/s` at the edge
  are design hypotheses, not derived from a confinement scaling law (gyro-Bohm, ISS04, …);
  the certificate already fails at `χ₀ = 1/2` (`hTsub_check_reject`).

## Results

* `helCoeffs_transportLaws`: the helical coefficients are a **kernel instance** (`D ≥ 0`,
  degenerate axis, source continuous for `T > 0`).
* `helical_margin`: `N[T_sub] ≥ 1/20 keV/s` on `[0,1]` for every `χ₀ ∈ [0, 2/5]`, every
  supplied reactivity and every geometry in the class, from two 12-piece exact rational
  certificates (`hTsub_check_max` at `χ₀ = 2/5`, `hTsub_check_zero` at `χ₀ = 0`; the operator
  is affine in `χ₀`).
* `helical_core_barrier` (**rung M2 on stellarator-like geometry**): every kernel solution on
  all horizons with `T(s,0) ≥ T_sub(s)` and `T_edge ≥ 1 keV` satisfies `T ≥ T_sub` for all
  `t ≥ 0`, and `T ≥ 10 keV` on the core `s ≤ 3/10`, which contains the tube
  `r ≤ 1.09 m` (`core_contains_tube`). `T_sub = 13 − 7.6 s − 2.8 s² − 1.6 s¹²` keV
  (`T_sub(0) = 13`, `T_sub(1) = 1`).
* `tsub_axis_pressure`: on the axis the barrier pressure `n(1+r_i)T_sub(0) ≈ 0.392 MPa` is
  below the equilibrium pressure `≈ 0.398 MPa`.

## Honest limitations

* The transport model is the flux-surface-averaged single-temperature equation with fixed
  density and prescribed `χ`; the link between the true helical averages and the class
  `IsHelicalGeometry` (coarea formula, Gauss identity, axis limit of `V'`) is supplied, not
  formalized; existence of solutions is not proved.
* Straight helical geometry, no toroidal curvature, no coils.
* MHD/transport consistency holds **only on the axis** (`tsub_axis_pressure`). The
  equilibrium pressure `0.398 (1 − s)` MPa vanishes on the boundary, whereas every covered
  solution has `T ≥ T_sub` and edge temperature `≥ 1 keV`, so its pressure exceeds the
  equilibrium pressure near the edge (already at `s = 0.1` for `T = T_sub`). **No covered
  solution is pressure-consistent with this equilibrium on the whole plasma**; a
  self-consistent treatment needs an equilibrium with a finite edge pressure (or a
  transport model with an edge temperature tending to 0), not available here.
* The barrier `T_sub` itself is not admissible initial data for constant edge data (corner
  compatibility, as for the cylinder); compatible profiles above `T_sub` exist but are not
  constructed here.
-/

public section

noncomputable section

namespace PlasmaLean.Design.HelicalTransportBarrier

open Set PlasmaLean.Transport PlasmaLean.Fusion PlasmaLean.Certificates
  PlasmaLean.Design.HelicalFluxGeometry
open PlasmaLean.Design.TransportBarrier (heatCap heatCap_pos heatCap_eq alphaRate bremsRate
  alphaRate_ge bremsRate_le bremsRate_nonneg svFloor svFloor_le alphaBonus sqrt_le_quarter
  m2Plasma)

/-! ### Heating, source and diffusivity profile -/

/-- Auxiliary heating rate `q_aux(s) = 2/5 + 40 s² (1−s)²` keV/s (coefficients, constant
term first). -/
@[expose] def hAuxCoeffs : List ℚ := [2 / 5, 0, 40, -80, 40]

/-- The coefficient list is the stated deposition profile. -/
theorem hAux_eq (s : ℝ) : QPoly.eval hAuxCoeffs s = 2 / 5 + 40 * s ^ 2 * (1 - s) ^ 2 := by
  simp [hAuxCoeffs]; ring

/-- Net source in keV/s for a supplied reactivity:
`R(s,T) = α_rate ⟨σv⟩(T) + q_aux(s) − br_rate √T`, i.e. `(p_α + p_aux − p_br)/heatCap` for the
M2 plasma (`helSource_eq`). -/
@[expose] def helSource (sv : ℝ → ℝ) (s T : ℝ) : ℝ :=
  alphaRate * sv T + QPoly.eval hAuxCoeffs s - bremsRate * Real.sqrt T

/-- The source is the per-unit-volume power balance of the M2 plasma divided by the heat
capacity, with auxiliary power density `heatCap · q_aux(s)`. -/
theorem helSource_eq (sv : ℝ → ℝ) (s T : ℝ) :
    helSource sv s T = (m2Plasma.alphaPower sv T + heatCap * QPoly.eval hAuxCoeffs s -
      m2Plasma.bremsPower T) / heatCap := by
  have h := heatCap_pos.ne'
  simp only [helSource, alphaRate, bremsRate, DTPlasma.alphaPower, DTPlasma.bremsPower,
    m2Plasma, alphaEnergy, keV, bremsCoeff]
  field_simp

/-- The source is jointly continuous on `[0,1] × (0,∞)`. -/
theorem helSource_continuousOn (sv : ℝ → ℝ) [BoschHaleDT sv] :
    ContinuousOn (fun p : ℝ × ℝ => helSource sv p.1 p.2) (Icc 0 1 ×ˢ Ioi 0) := by
  have hsv : ContinuousOn (fun p : ℝ × ℝ => sv p.2) (Icc 0 1 ×ˢ Ioi 0) :=
    (BoschHaleDT.continuousOn (sv := sv)).comp continuous_snd.continuousOn
      (fun p hp => hp.2)
  have hrest : Continuous (fun p : ℝ × ℝ =>
      QPoly.eval hAuxCoeffs p.1 - bremsRate * Real.sqrt p.2) :=
    ((QPoly.continuous_eval _).comp continuous_fst).sub
      (continuous_const.mul (Real.continuous_sqrt.comp continuous_snd))
  have : ContinuousOn (fun p : ℝ × ℝ => alphaRate * sv p.2 +
      (QPoly.eval hAuxCoeffs p.1 - bremsRate * Real.sqrt p.2)) (Icc 0 1 ×ˢ Ioi 0) :=
    (continuousOn_const.mul hsv).add hrest.continuousOn
  refine this.congr (fun p _ => ?_)
  simp only [helSource]; ring

/-- Edge-drop shape `w(s) = 1 − (19/20) s⁴` of the diffusivity. -/
@[expose] def pedCoeffs : List ℚ := [1, 0, 0, 0, -19 / 20]

/-- `w(s) = 1 − (19/20)s⁴` and `w'(s) = −(19/5) s³`. -/
theorem ped_eval (s : ℝ) : QPoly.eval pedCoeffs s = 1 - 19 / 20 * s ^ 4 ∧
    QPoly.eval (QPoly.deriv pedCoeffs) s = -(19 / 5) * s ^ 3 := by
  constructor <;> simp [pedCoeffs, QPoly.deriv, QPoly.add] <;> ring

/-- Diffusivity profile `χ(s) = χ₀ w(s)` (m²/s, including the 3/2 heat-capacity factor). -/
@[expose] def chiProfile (χ₀ s : ℝ) : ℝ := χ₀ * QPoly.eval pedCoeffs s

/-- Its derivative `χ'(s) = χ₀ w'(s)`. -/
@[expose] def chiProfile' (χ₀ s : ℝ) : ℝ := χ₀ * QPoly.eval (QPoly.deriv pedCoeffs) s

/-- Sanity: the diffusivity at the edge is 5 % of the core value. -/
theorem chiProfile_edge (χ₀ : ℝ) : chiProfile χ₀ 1 = χ₀ / 20 ∧ chiProfile χ₀ 0 = χ₀ := by
  simp only [chiProfile, (ped_eval _).1]; constructor <;> ring

/-- Transport coefficients on the helical geometry `G` for reactivity `sv` and core
diffusivity `χ₀`: `D = χ(s)⟨|∇s|²⟩`, source `helSource sv` posed for `T > 0`, degenerate
axis. -/
@[expose] def helCoeffs (G : FluxGeometry) (sv : ℝ → ℝ) (χ₀ : ℝ) : RadialCoefficients :=
  G.coeffs (chiProfile χ₀) (chiProfile' χ₀) (helSource sv) (Ioi 0)

/-- **The helical coefficients are a kernel instance** for `χ₀ ≥ 0`. -/
theorem helCoeffs_transportLaws (G : FluxGeometry) [hG : IsHelicalGeometry G] (sv : ℝ → ℝ)
    [BoschHaleDT sv] {χ₀ : ℝ} (hχ : 0 ≤ χ₀) : TransportLaws (helCoeffs G sv χ₀) :=
  G.coeffs_transportLaws
    (fun s hs => by
      simp only [chiProfile, (ped_eval s).1]
      have : s ^ 4 ≤ 1 := pow_le_one₀ hs.1 hs.2
      nlinarith)
    (fun s _ => ((QPoly.hasDerivAt_eval _ s).const_mul χ₀).hasDerivWithinAt)
    (IsHelicalGeometry.g_nonneg G) isOpen_Ioi (helSource_continuousOn sv)

/-! ### The barrier profile and its certificates -/

/-- Coefficients of `T_sub(s) = 13 − (38/5) s − (14/5) s² − (8/5) s¹²` keV. -/
@[expose] def hTsubCoeffs : List ℚ :=
  [13, -38 / 5, -14 / 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8 / 5]

/-- The barrier profile `T_sub` (keV). -/
@[expose] def hTsub (s : ℝ) : ℝ := QPoly.eval hTsubCoeffs s

/-- `T_sub'`. -/
@[expose] def hTsub' (s : ℝ) : ℝ := QPoly.eval (QPoly.deriv hTsubCoeffs) s

/-- `T_sub''`. -/
@[expose] def hTsub'' (s : ℝ) : ℝ := QPoly.eval (QPoly.deriv (QPoly.deriv hTsubCoeffs)) s

/-- `T_sub` is a regular profile. -/
theorem hTsub_regular : ProfileRegular hTsub hTsub' hTsub'' :=
  ⟨fun s _ => (QPoly.hasDerivAt_eval _ s).hasDerivWithinAt,
    fun s _ => (QPoly.hasDerivAt_eval _ s).hasDerivWithinAt⟩

/-- Explicit forms of `T_sub`, `T_sub'`, `T_sub''`. -/
theorem hTsub_eval (s : ℝ) :
    hTsub s = 13 - 38 / 5 * s - 14 / 5 * s ^ 2 - 8 / 5 * s ^ 12 ∧
      hTsub' s = -(38 / 5) - 28 / 5 * s - 96 / 5 * s ^ 11 ∧
      hTsub'' s = -(28 / 5) - 1056 / 5 * s ^ 10 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [hTsub, hTsub', hTsub'', hTsubCoeffs, QPoly.deriv, QPoly.add] <;> ring

/-- `T_sub' ≤ 0` and `T_sub'' ≤ 0` on `[0,1]` (decreasing and concave). -/
theorem hTsub_signs {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : hTsub' s ≤ 0 ∧ hTsub'' s ≤ 0 := by
  obtain ⟨-, h1, h2⟩ := hTsub_eval s
  have := hs.1
  constructor
  · rw [h1]; have : 0 ≤ s ^ 11 := by positivity
    nlinarith
  · rw [h2]; have : 0 ≤ s ^ 10 := by positivity
    nlinarith

/-- `T_sub` is decreasing on `[0,1]`. -/
theorem hTsub_antitone : AntitoneOn hTsub (Icc 0 1) :=
  antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hTsub_regular.continuousOn
    (fun x _ => (QPoly.hasDerivAt_eval _ x).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [interior_Icc] at hx
      change deriv (QPoly.eval hTsubCoeffs) x ≤ 0
      rw [(QPoly.hasDerivAt_eval _ x).deriv]
      exact (hTsub_signs (Ioo_subset_Icc_self hx)).1)

/-- Values: `T_sub(0) = 13`, `T_sub(1) = 1`. -/
theorem hTsub_values : hTsub 0 = 13 ∧ hTsub 1 = 1 := by
  refine ⟨?_, ?_⟩ <;> norm_num [(hTsub_eval _).1]

/-- `1 ≤ T_sub ≤ 13` on `[0,1]`. -/
theorem hTsub_bounds {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : 1 ≤ hTsub s ∧ hTsub s ≤ 13 :=
  ⟨hTsub_values.2 ▸ hTsub_antitone hs ⟨zero_le_one, le_rfl⟩ hs.2,
    hTsub_values.1 ▸ hTsub_antitone ⟨le_rfl, zero_le_one⟩ hs hs.1⟩

/-- **Core temperature**: `T_sub ≥ 10 keV` on `s ≤ 3/10`. -/
theorem hTsub_core {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 3 / 10) : 10 ≤ hTsub s := by
  have hc : (10 : ℝ) ≤ hTsub (3 / 10) := by rw [(hTsub_eval _).1]; norm_num
  exact hc.trans (hTsub_antitone ⟨h0, h1.trans (by norm_num)⟩ ⟨by norm_num, by norm_num⟩ h1)

/-- The conduction lower-bound polynomial
`B(s) = w (1.03 s(1 + s/25)) T'' + w (1.03) T' + w' (0.97 s(1 − s/25)) T'`
(the bracket of `N[T_sub]` divided by `A χ₀`, with the geometric enclosures inserted). -/
@[expose] def condLB : List ℚ :=
  QPoly.add (QPoly.add
    (QPoly.mul (QPoly.mul (QPoly.scale (103 / 100) pedCoeffs) [0, 1, 1 / 25])
      (QPoly.deriv (QPoly.deriv hTsubCoeffs)))
    (QPoly.mul (QPoly.scale (103 / 100) pedCoeffs) (QPoly.deriv hTsubCoeffs)))
    (QPoly.mul (QPoly.mul (QPoly.scale (97 / 100) (QPoly.deriv pedCoeffs)) [0, 1, -1 / 25])
      (QPoly.deriv hTsubCoeffs))

/-- Explicit form of `condLB`. -/
theorem condLB_eval (s : ℝ) : QPoly.eval condLB s =
    QPoly.eval pedCoeffs s * (103 / 100 * (s * (1 + 1 / 25 * s))) * hTsub'' s +
      QPoly.eval pedCoeffs s * (103 / 100) * hTsub' s +
      QPoly.eval (QPoly.deriv pedCoeffs) s * (97 / 100 * (s * (1 - 1 / 25 * s))) * hTsub' s := by
  simp only [condLB, QPoly.eval_add, QPoly.eval_mul, QPoly.eval_scale, hTsub', hTsub'',
    QPoly.eval_cons, QPoly.eval_nil]
  push_cast; ring

/-- Alpha-free source lower bound `q_aux − (201/1000)(T_sub + 4)/4` (bremsstrahlung via
`√T ≤ (T+4)/4`). -/
@[expose] def srcLB : List ℚ :=
  QPoly.add hAuxCoeffs (QPoly.scale (-(201 / 1000) / 4) (QPoly.add hTsubCoeffs [4]))

/-- Lower bound for `N[T_sub]` at the largest core diffusivity `χ₀ = 2/5`:
`(2/5)(25/32) B + srcLB`. -/
@[expose] def resMax : List ℚ := QPoly.add (QPoly.scale (2 / 5 * (25 / 32)) condLB) srcLB

/-- The certificate pieces `(right end, temperature label)`: `T_sub` crosses
`12, 11, …, 2` keV at the right ends (rounded down to `10⁻⁴`). -/
@[expose] def hPieces : List (ℚ × ℚ) :=
  [(1257 / 10000, 12), (151 / 625, 11), (437 / 1250, 10), (282 / 625, 9), (5473 / 10000, 8),
    (6383 / 10000, 7), (7237 / 10000, 6), (8013 / 10000, 5), (217 / 250, 4), (1153 / 1250, 3),
    (1931 / 2000, 2), (1, 0)]

/-- The pieces cover `[0,1]`. -/
theorem hPieces_end : pieceEnd 0 hPieces = 1 := by simp [pieceEnd, hPieces]

/-- All labels are nonnegative. -/
theorem hPieces_labels : hPieces.all (fun p => decide (0 ≤ p.2)) = true := by decide +kernel

/-- **Certificate at `χ₀ = 2/5`** (12 pieces, kernel-checked). -/
theorem hTsub_check_max :
    pieceCheck resMax hTsubCoeffs (1 / 20) alphaBonus 0 hPieces = true := by
  decide +kernel

/-- **Certificate at `χ₀ = 0`** (12 pieces, kernel-checked). -/
theorem hTsub_check_zero :
    pieceCheck srcLB hTsubCoeffs (1 / 20) alphaBonus 0 hPieces = true := by
  decide +kernel

/-- Sanity (rejected fixture): the same pieces do **not** certify the margin at the larger core
diffusivity `χ₀ = 1/2`, so the accepted certificate is not vacuous. -/
theorem hTsub_check_reject :
    pieceCheck (QPoly.add (QPoly.scale (1 / 2 * (25 / 32)) condLB) srcLB) hTsubCoeffs (1 / 20)
      alphaBonus 0 hPieces = false := by
  decide +kernel

/-- Explicit form of `srcLB`. -/
theorem srcLB_eval (s : ℝ) :
    QPoly.eval srcLB s = QPoly.eval hAuxCoeffs s - 201 / 1000 / 4 * (hTsub s + 4) := by
  simp [srcLB, hTsub]; ring

/-- Explicit form of `resMax`. -/
theorem resMax_eval (s : ℝ) :
    QPoly.eval resMax s = 2 / 5 * (25 / 32) * QPoly.eval condLB s + QPoly.eval srcLB s := by
  simp [resMax]

/-! ### The margin -/

/-- Source lower bound on the barrier: for a label `0 ≤ k ≤ T_sub(s)`,
`R(s, T_sub(s)) ≥ alphaBonus k + srcLB(s)` (Bosch–Hale floor at `k`, `√T ≤ (T+4)/4`). -/
theorem helSource_ge (sv : ℝ → ℝ) [BoschHaleDT sv] {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {k : ℚ}
    (hk0 : 0 ≤ k) (hkT : (k : ℝ) ≤ hTsub s) :
    ((alphaBonus k : ℚ) : ℝ) + QPoly.eval srcLB s ≤ helSource sv s (hTsub s) := by
  obtain ⟨hT1, hT2⟩ := hTsub_bounds hs
  have hfl := svFloor_le sv hk0 hkT (by linarith)
  have hsv0 : 0 ≤ sv (hTsub s) := BoschHaleDT.nonneg _ (by linarith)
  have hα : (229 / 10 * 10 ^ 21 : ℝ) * svFloor k ≤ alphaRate * sv (hTsub s) :=
    (mul_le_mul_of_nonneg_left hfl (by norm_num)).trans
      (mul_le_mul_of_nonneg_right alphaRate_ge hsv0)
  have hsq := sqrt_le_quarter (T := hTsub s) (by linarith)
  have hbr : bremsRate * Real.sqrt (hTsub s) ≤ 201 / 1000 * ((hTsub s + 4) / 4) :=
    mul_le_mul bremsRate_le hsq (Real.sqrt_nonneg _) (by norm_num)
  rw [srcLB_eval, helSource]
  simp only [alphaBonus, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
  linarith

/-- **Barrier margin on helical geometry.** For every geometry in `IsHelicalGeometry`, every
supplied reactivity and every core diffusivity `χ₀ ∈ [0, 2/5]` m²/s,
`N[T_sub](s) ≥ 1/20 keV/s` on `[0,1]`. -/
theorem helical_margin (G : FluxGeometry) [hG : IsHelicalGeometry G] (sv : ℝ → ℝ)
    [BoschHaleDT sv] {χ₀ : ℝ} (hχ0 : 0 ≤ χ₀) (hχ : χ₀ ≤ 2 / 5) :
    ∀ s ∈ Icc (0 : ℝ) 1,
      (1 / 20 : ℝ) ≤ (helCoeffs G sv χ₀).op s (hTsub s) (hTsub' s) (hTsub'' s) := by
  intro s hs
  rw [helCoeffs, G.coeffs_op _ _ _ _ hs]
  obtain ⟨hgL, hgU⟩ := IsHelicalGeometry.g_bounds G s hs
  obtain ⟨-, hhU⟩ := IsHelicalGeometry.h_bounds G s hs
  rw [geomA_eq] at hgL hgU hhU
  obtain ⟨hT1, hT2⟩ := hTsub_signs hs
  obtain ⟨hw, hw'⟩ := ped_eval s
  have hW : 0 ≤ QPoly.eval pedCoeffs s := by
    rw [hw]; have : s ^ 4 ≤ 1 := pow_le_one₀ hs.1 hs.2
    linarith
  have hW' : QPoly.eval (QPoly.deriv pedCoeffs) s ≤ 0 := by
    rw [hw']; have : 0 ≤ s ^ 3 := pow_nonneg hs.1 3
    linarith
  set W := QPoly.eval pedCoeffs s
  set W' := QPoly.eval (QPoly.deriv pedCoeffs) s
  -- the conduction bracket is bounded below by `A · B(s)`
  have hbr : 25 / 32 * QPoly.eval condLB s ≤
      W * G.g s * hTsub'' s + (W' * G.g s + W * G.h s) * hTsub' s := by
    rw [condLB_eval]
    have e1 := mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hW hT2)
      (by linarith : G.g s - 25 / 32 * (103 / 100) * s * (1 + 1 / 25 * s) ≤ 0)
    have e2 := mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hW hT1)
      (by linarith : G.h s - 25 / 32 * (103 / 100) ≤ 0)
    have e3 := mul_nonneg (mul_nonneg_of_nonpos_of_nonpos hW' hT1)
      (by linarith : 0 ≤ G.g s - 25 / 32 * (97 / 100) * s * (1 - 1 / 25 * s))
    nlinarith [e1, e2, e3]
  have hop : χ₀ * (W * G.g s * hTsub'' s + (W' * G.g s + W * G.h s) * hTsub' s) =
      chiProfile χ₀ s * G.g s * hTsub'' s +
        (chiProfile' χ₀ s * G.g s + chiProfile χ₀ s * G.h s) * hTsub' s := by
    simp only [chiProfile, chiProfile', W, W']; ring
  rw [← hop]
  have hanti : AntitoneOn (QPoly.eval hTsubCoeffs) (Icc ((0 : ℚ) : ℝ) (pieceEnd 0 hPieces)) :=
    fun a ha b hb hab => hTsub_antitone (by simpa [hPieces_end] using ha)
      (by simpa [hPieces_end] using hb) hab
  have hx : s ∈ Icc ((0 : ℚ) : ℝ) (pieceEnd 0 hPieces) := by simpa [hPieces_end] using hs
  have hlab : ∀ d k, (d, k) ∈ hPieces → (0 : ℚ) ≤ k := fun d k hmem => by
    simpa using List.all_eq_true.1 hPieces_labels (d, k) hmem
  rcases le_or_gt 0 (QPoly.eval condLB s) with hB | hB
  · -- conduction helps: use the `χ₀ = 0` certificate
    obtain ⟨k, ⟨d, hmem⟩, hkT, hQ⟩ :=
      pieceCheck_sound 0 hPieces hTsub_check_zero (by simp [hPieces]) hanti s hx
    have hR := helSource_ge sv hs (hlab d k hmem) hkT
    have hc : 0 ≤ χ₀ * (W * G.g s * hTsub'' s + (W' * G.g s + W * G.h s) * hTsub' s) :=
      mul_nonneg hχ0 (le_trans (by positivity) hbr)
    push_cast at hQ
    linarith
  · -- conduction hurts: use the `χ₀ = 2/5` certificate
    obtain ⟨k, ⟨d, hmem⟩, hkT, hQ⟩ :=
      pieceCheck_sound 0 hPieces hTsub_check_max (by simp [hPieces]) hanti s hx
    have hR := helSource_ge sv hs (hlab d k hmem) hkT
    rw [resMax_eval] at hQ
    have hc : 2 / 5 * (25 / 32 * QPoly.eval condLB s) ≤
        χ₀ * (W * G.g s * hTsub'' s + (W' * G.g s + W * G.h s) * hTsub' s) :=
      (mul_le_mul_of_nonpos_right hχ (by linarith)).trans
        (mul_le_mul_of_nonneg_left hbr hχ0)
    push_cast at hQ
    linarith

/-! ### The all-time barrier -/

/-- **M2 on helical geometry.** For every flux geometry in `IsHelicalGeometry` (in particular
the true averages of the exact helical equilibrium), every reactivity satisfying the supplied
Bosch–Hale enclosures, every core diffusivity `χ₀ ∈ [0, 2/5]` m²/s with the edge drop
`χ = χ₀(1 − 0.95 s⁴)`, and every kernel solution on all horizons with `T(s,0) ≥ T_sub(s)`
and edge temperature `≥ 1 keV`: `T(s,t) ≥ T_sub(s)` for all `s ∈ [0,1]`, `t ≥ 0`, and
`T ≥ 10 keV` on the core `s ≤ 3/10` for all time. Caveat: the covered solutions are
pressure-consistent with the equilibrium only on the axis (`tsub_axis_pressure`); near the
edge their pressure exceeds the equilibrium pressure, which vanishes on the boundary. -/
theorem helical_core_barrier (G : FluxGeometry) [hG : IsHelicalGeometry G] (sv : ℝ → ℝ)
    [BoschHaleDT sv] {χ₀ : ℝ} (hχ0 : 0 ≤ χ₀) (hχ : χ₀ ≤ 2 / 5) {Tedge : ℝ → ℝ}
    {u : RadialField} (hu : ∀ τ, 0 ≤ τ → ClassicalRadialSolution (helCoeffs G sv χ₀) Tedge τ u)
    (h0 : ∀ s ∈ Icc (0 : ℝ) 1, hTsub s ≤ u.T s 0) (hedge : ∀ t, 0 ≤ t → 1 ≤ Tedge t) :
    (∀ s ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → hTsub s ≤ u.T s t) ∧
      ∀ s, 0 ≤ s → s ≤ 3 / 10 → ∀ t, 0 ≤ t → 10 ≤ u.T s t := by
  have hL := helCoeffs_transportLaws G sv hχ0
  have hlow : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → hTsub s ≤ u.T s t :=
    le_of_isStrictLowerBarrier_margin_forall_time (fun τ hτ => { hL, hu τ hτ with })
      (G.coeffs_isSemilinear _ _ _ _) hTsub_regular
      (fun h => absurd h (by simp [helCoeffs, FluxGeometry.coeffs, RadialCoefficients.semilinear]))
      (fun s hs => show 0 < hTsub s by linarith [(hTsub_bounds hs).1]) (by norm_num)
      (helical_margin G sv hχ0 hχ) h0 (fun t ht => by rw [hTsub_values.2]; exact hedge t ht)
  refine ⟨hlow, fun s h0' h1' t ht => ?_⟩
  exact (hTsub_core h0' h1').trans (hlow s ⟨h0', h1'.trans (by norm_num)⟩ t ht)

/-- Sanity (non-vacuity of the geometry hypothesis): the theorem applies to the witness
geometry of `HelicalFluxGeometry`, for the largest core diffusivity. -/
theorem helical_core_barrier_witness (sv : ℝ → ℝ) [BoschHaleDT sv] {Tedge : ℝ → ℝ}
    {u : RadialField}
    (hu : ∀ τ, 0 ≤ τ → ClassicalRadialSolution (helCoeffs witnessGeometry sv (2 / 5)) Tedge τ u)
    (h0 : ∀ s ∈ Icc (0 : ℝ) 1, hTsub s ≤ u.T s 0) (hedge : ∀ t, 0 ≤ t → 1 ≤ Tedge t) :
    ∀ s, 0 ≤ s → s ≤ 3 / 10 → ∀ t, 0 ≤ t → 10 ≤ u.T s t :=
  (helical_core_barrier witnessGeometry sv (by norm_num) le_rfl hu h0 hedge).2

/-- **The core contains a tube.** A point with `r² ≤ 3/160` (dimensionless; physically
`r ≤ L·√(3/160) ≈ 1.09 m`) has label `s = ψ̂/ψ_b ≤ 3/10`, so the core bound `T ≥ 10 keV`
covers it. -/
theorem core_contains_tube {x : PlasmaLean.Fields.Space}
    (hx : PlasmaLean.Design.HelicalFamily.r2 x ≤ 3 / 160) :
    PlasmaLean.Design.HelicalEquilibrium.eqPsi (1 / 4) x / psiB ≤ 3 / 10 := by
  have h := eqPsi_le_of_r2_le (s := 3 / 10) (x := x) (by linarith) (by unfold psiB; linarith)
  rw [div_le_iff₀ (by norm_num [psiB] : (0 : ℝ) < psiB)]
  linarith

/-! ### Auxiliary power and pressure -/

/-- `∫₀¹ q_aux = 26/15` keV/s. -/
theorem hAux_integral : ∫ x in (0 : ℝ)..1, QPoly.eval hAuxCoeffs x = 26 / 15 := by
  have hd : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (QPoly.eval [0, 2 / 5, 0, 40 / 3, -20, 8]) (QPoly.eval hAuxCoeffs x) x := by
    intro x _
    convert QPoly.hasDerivAt_eval [0, 2 / 5, 0, 40 / 3, -20, 8] x using 1
    simp only [hAuxCoeffs, QPoly.deriv, QPoly.add, QPoly.eval_cons, QPoly.eval_nil]
    push_cast; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((QPoly.continuous_eval _).intervalIntegrable _ _)]
  simp; norm_num

/-- `∫₀¹ s q_aux(s) ds = 13/15` keV/s. -/
theorem hAux_moment : ∫ x in (0 : ℝ)..1, QPoly.eval hAuxCoeffs x * x = 13 / 15 := by
  have hd : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (QPoly.eval [0, 0, 1 / 5, 0, 10, -16, 20 / 3])
      (QPoly.eval hAuxCoeffs x * x) x := by
    intro x _
    convert QPoly.hasDerivAt_eval [0, 0, 1 / 5, 0, 10, -16, 20 / 3] x using 1
    simp only [hAuxCoeffs, QPoly.deriv, QPoly.add, QPoly.eval_cons, QPoly.eval_nil]
    push_cast; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((QPoly.continuous_eval _).mul continuous_id).intervalIntegrable _ _)]
  simp; norm_num

/-- `q_aux ≥ 0` on `[0,1]`. -/
theorem hAux_nonneg {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : 0 ≤ QPoly.eval hAuxCoeffs s := by
  rw [hAux_eq]
  have : 0 ≤ 1 - s := by linarith [hs.2]
  have := hs.1
  positivity

/-- Total auxiliary heating power (W): `P_aux = heatCap · ∫₀¹ q_aux(s) V'(s) ds`. -/
@[expose] def helAuxPower (G : FluxGeometry) : ℝ :=
  heatCap * ∫ s in (0 : ℝ)..1, QPoly.eval hAuxCoeffs s * G.Vp s

/-- **Auxiliary power budget**: `63 MW ≤ P_aux ≤ 67.8 MW` for every geometry in the class
(nominally `heatCap · V'(0) · 26/15 ≈ 65.5 MW`; the spread is the proved `V'` enclosure). -/
theorem helAuxPower_bounds (G : FluxGeometry) [hG : IsHelicalGeometry G] :
    (63e6 : ℝ) ≤ helAuxPower G ∧ helAuxPower G ≤ 67.8e6 := by
  have hVc : ContinuousOn G.Vp (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact fun s hs => (hG.Vp_deriv s hs).continuousWithinAt
  have hqc : Continuous (QPoly.eval hAuxCoeffs) := QPoly.continuous_eval _
  have hint : IntervalIntegrable (fun s => QPoly.eval hAuxCoeffs s * G.Vp s) MeasureTheory.volume
      0 1 := (hqc.continuousOn.mul hVc).intervalIntegrable
  have hlin : ∀ c : ℝ, ∫ s in (0 : ℝ)..1, QPoly.eval hAuxCoeffs s * (Vaxis * (1 + c * s)) =
      Vaxis * (26 / 15 + c * (13 / 15)) := by
    intro c
    have e : (fun s => QPoly.eval hAuxCoeffs s * (Vaxis * (1 + c * s))) =
        fun s => Vaxis * QPoly.eval hAuxCoeffs s + (Vaxis * c) * (QPoly.eval hAuxCoeffs s * s) := by
      funext s; ring
    rw [e, intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hAux_integral, hAux_moment]
    · ring
    · exact (continuous_const.mul hqc).intervalIntegrable _ _
    · exact (continuous_const.mul (hqc.mul continuous_id)).intervalIntegrable _ _
  have hlo : Vaxis * (26 / 15 + -(1 / 15) * (13 / 15)) ≤
      ∫ s in (0 : ℝ)..1, QPoly.eval hAuxCoeffs s * G.Vp s := by
    rw [← hlin]
    refine intervalIntegral.integral_mono_on zero_le_one
      ((hqc.mul (continuous_const.mul (continuous_const.add
        (continuous_const.mul continuous_id)))).intervalIntegrable _ _) hint (fun s hs => ?_)
    have := (IsHelicalGeometry.Vp_bounds G s hs).1
    exact mul_le_mul_of_nonneg_left (by linarith) (hAux_nonneg hs)
  have hhi : ∫ s in (0 : ℝ)..1, QPoly.eval hAuxCoeffs s * G.Vp s ≤
      Vaxis * (26 / 15 + 1 / 15 * (13 / 15)) := by
    rw [← hlin]
    refine intervalIntegral.integral_mono_on zero_le_one hint
      ((hqc.mul (continuous_const.mul (continuous_const.add
        (continuous_const.mul continuous_id)))).intervalIntegrable _ _) (fun s hs => ?_)
    exact mul_le_mul_of_nonneg_left (IsHelicalGeometry.Vp_bounds G s hs).2 (hAux_nonneg hs)
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  have hpp1 : (3.1415 : ℝ) ^ 2 ≤ Real.pi ^ 2 := by gcongr
  have hpp2 : Real.pi ^ 2 ≤ (3.1416 : ℝ) ^ 2 := by gcongr
  have hs15 : (3.8729 : ℝ) ≤ Real.sqrt 15 ∧ Real.sqrt 15 ≤ 3.873 := by
    constructor
    · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    · rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hVeq : Vaxis = 327.68 * Real.pi ^ 2 / Real.sqrt 15 := by
    unfold Vaxis psiB pitchLength periodLength; ring
  have hsq : 0 < Real.sqrt 15 := by linarith [hs15.1]
  have hV1 : 327.68 * 3.1415 ^ 2 / 3.873 ≤ Vaxis := by
    rw [hVeq, div_le_div_iff₀ (by norm_num) hsq]; nlinarith [hs15.2]
  have hV2 : Vaxis ≤ 327.68 * 3.1416 ^ 2 / 3.8729 := by
    rw [hVeq, div_le_div_iff₀ hsq (by norm_num)]; nlinarith [hs15.1]
  have hH := heatCap_eq
  have hHpos := heatCap_pos
  unfold helAuxPower
  constructor
  · calc (63e6 : ℝ) ≤ heatCap * (Vaxis * (26 / 15 + -(1 / 15) * (13 / 15))) := by
          rw [hH]; nlinarith [hV1]
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo hHpos.le
  · calc _ ≤ heatCap * (Vaxis * (26 / 15 + 1 / 15 * (13 / 15))) :=
          mul_le_mul_of_nonneg_left hhi hHpos.le
      _ ≤ 67.8e6 := by rw [hH]; nlinarith [hV2]

/-- **Pressure consistency on the axis.** The thermal pressure of the barrier on the axis,
`n(1+r_i) T_sub(0) keV = (2/3) heatCap · 13 ≈ 0.392 MPa`, is below the equilibrium's axis
pressure `B_u² p₀/μ₀ = 1/(2μ₀) ≈ 0.398 MPa` (5 T, `β = 4 %`; independent of the scale `L`).
So the barrier is compatible with the equilibrium on the axis. Off the axis it is not: the
equilibrium pressure `0.398 (1 − s)` MPa falls linearly to `0` at the boundary, while
`T_sub(1) = 1 keV` gives `≈ 30 kPa` there (and already at `s = 0.1` the barrier pressure
`≈ 0.37 MPa` exceeds `≈ 0.36 MPa`); transport and MHD are not coupled in this model. -/
theorem tsub_axis_pressure (μ₀ z : ℝ) (h1 : 1.2566e-6 ≤ μ₀) (h2 : μ₀ ≤ 1.2567e-6) :
    2 / 3 * heatCap * hTsub 0 ≤
      PlasmaLean.Design.HelicalReactorScale.physPressure μ₀ (8 / 25) (5 / 4) 2
        (WithLp.toLp 2 ![0, 0, z]) := by
  have := (PlasmaLean.Design.HelicalReactorScale.reactor_peak_pressure μ₀ z h1 h2).1
  have hv : 2 / 3 * heatCap * hTsub 0 ≤ 393000 := by
    rw [hTsub_values.1, heatCap_eq]; norm_num
  linarith

end PlasmaLean.Design.HelicalTransportBarrier
