/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.VacuumDerivative
public import PlasmaLean.Sanity.FilamentVacuum
public import PlasmaLean.Theory.Fields.Subharmonic
public import PlasmaLean.Theory.Geometry.SurfaceCover

/-!
# Volume field-error certificates from boundary certificates (vacuum pair)

First application of the T1 boundary-to-interior theorem
`Vacuum.VacuumField.error_le_of_frontier` to a coil fixture (milestone M5).

Region. `Ω = openCube`, the open cube `|xₖ| < 1/40` (2.5 cm half-width) about the
midpoint of the two-loop fixture `VacuumPair`. Its closure `closedCube` lies in the open
ball `U` of radius `1/20`, which avoids both nominal coils by `3/20` and every
manufactured coil (`WithinTolerance`, 1 mm position error) by `7/50`.

Main results.
* `manufactured_vacuumField`: the nominal field and every manufactured field are
  `VacuumField`s on `U`, an open neighbourhood of `closure Ω`; hence `C²` and continuous
  on `closure Ω` (via `Sanity.filamentField_vacuumField'`, i.e. the source-free Maxwell
  identities for closed `C¹` filaments).
* `volume_error_of_frontier`: any bound `δ` on the error `B_actual − B_nominal` on the
  **frontier** of the cube holds throughout the closed cube.
* `combined_volume_error`: the existing pointwise budget (`combined_field_error`), used
  only on the frontier, yields `‖B_actual − B_nominal‖ ≤ μ₀I/4` in the whole cube.
* `volume_error_of_boundary_samples`: bounds `‖ΔB‖ ≤ m` at the `6 (N+1)²` grid points of
  the six faces (e.g. measured or separately certified data) give
  `‖ΔB‖ ≤ m + L/(20N)` in the whole closed cube, where `L` is the certified Lipschitz
  constant of `ΔB` (actual-field derivative bound plus nominal Lipschitz bound). The
  surface cover is `Geometry.patch_norm_le_of_grid`.
* `calibrated_volume_error_of_boundary_samples`: under the 1% current budget,
  `‖ΔB‖ ≤ m + 14 μ₀ I / N` in the cube.

Comparison with the pointwise route. For this fixture the pointwise bound
`combined_field_error` already holds on the entire 5 cm ball, so `combined_volume_error`
reproduces (does not improve) the `μ₀I/4` budget on the cube; what is new is that only
frontier values are used. The sample theorem genuinely transfers a two-dimensional
boundary computation (`6(N+1)²` points) to the three-dimensional volume, where a
direct volume cover would need `O(N³)` samples, and it accepts boundary data that are
not derived from the coil model. Interpolation costs `≈ 13.4 μ₀I/N` per the stated
Lipschitz constants, so e.g. `N = 1340` per face is needed for `0.01 μ₀I` resolution.

Not covered: measurement error models for the samples, finite-conductor fields, and
regions whose frontier meets a coil.
-/

public section
noncomputable section

namespace PlasmaLean.Design.VacuumPair
open Fields Geometry Vacuum

/-! ### The region -/

/-- Half-width of the cube, `1/40` m. -/
@[expose] def cubeHalf : ℝ := 1 / 40

/-- The open cube `Ω = {x | |xₖ| < 1/40 for k = 0,1,2}`. -/
@[expose] def openCube : Set Space := {x | ∀ k : Fin 3, |x k| < cubeHalf}

/-- The closed cube `{x | |xₖ| ≤ 1/40}`. -/
@[expose] def closedCube : Set Space := {x | ∀ k : Fin 3, |x k| ≤ cubeHalf}

/-- The open neighbourhood `U` (open ball of radius `1/20`) on which the fields are
shown to be vacuum fields. -/
@[expose] def nbhd : Set Space := Metric.ball 0 (1 / 20)

/-- The origin (the probe point) lies in the open cube. -/
theorem zero_mem_openCube : (0 : Space) ∈ openCube := by
  intro k; norm_num [cubeHalf]

/-- The open cube is open. -/
theorem isOpen_openCube : IsOpen openCube := by
  have : openCube = ⋂ k : Fin 3, {x : Space | |x k| < cubeHalf} := by
    ext x; simp [openCube]
  rw [this]
  exact isOpen_iInter_of_finite fun k =>
    isOpen_lt (by fun_prop) continuous_const

/-- The closed cube is closed. -/
theorem isClosed_closedCube : IsClosed closedCube := by
  have : closedCube = ⋂ k : Fin 3, {x : Space | |x k| ≤ cubeHalf} := by
    ext x; simp [closedCube]
  rw [this]
  exact isClosed_iInter fun k => isClosed_le (by fun_prop) continuous_const

/-- `closure Ω ⊆ closedCube`. -/
theorem closure_openCube_subset : closure openCube ⊆ closedCube :=
  closure_minimal (fun _ hx k => (hx k).le) isClosed_closedCube

/-- `closedCube ⊆ closure Ω`: each point of the closed cube is the limit of `r • x`,
`r → 1⁻`, which lie in the open cube. -/
theorem closedCube_subset_closure : closedCube ⊆ closure openCube := by
  intro x hx
  have ht : Filter.Tendsto (fun r : ℝ => r • x) (nhdsWithin 1 (Set.Iio 1)) (nhds x) := by
    have : Filter.Tendsto (fun r : ℝ => r • x) (nhds 1) (nhds ((1 : ℝ) • x)) :=
      (continuous_id.smul continuous_const).tendsto 1
    rw [one_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr k
  have hk := hx k
  have hc : (0 : ℝ) < cubeHalf := by norm_num [cubeHalf]
  simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hr.1]
  nlinarith [mul_le_mul_of_nonneg_left hk hr.1.le, mul_pos hc (sub_pos.2 hr.2)]

/-- The closure of the cube is the closed cube. -/
theorem closure_openCube : closure openCube = closedCube :=
  Set.Subset.antisymm closure_openCube_subset closedCube_subset_closure

/-- Points of the closed cube have norm below `1/20` (`√3/40 < 1/20`). -/
theorem norm_lt_of_mem_closedCube {x : Space} (hx : x ∈ closedCube) : ‖x‖ < 1 / 20 := by
  have hsq : ‖x‖ ^ 2 < (1 / 20) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    have h0 := hx 0; have h1 := hx 1; have h2 := hx 2
    simp only [cubeHalf, Real.norm_eq_abs] at *
    have a0 : |x 0| ^ 2 ≤ (1 / 40) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h0 2
    have a1 : |x 1| ^ 2 ≤ (1 / 40) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    have a2 : |x 2| ^ 2 ≤ (1 / 40) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq

/-- The closed cube lies in the observation ball. -/
theorem closedCube_subset_region {x : Space} (hx : x ∈ closedCube) : ObservationRegion x :=
  (norm_lt_of_mem_closedCube hx).le

/-- The closed cube lies in the open neighbourhood `U`. -/
theorem closedCube_subset_nbhd : closedCube ⊆ nbhd := fun x hx => by
  simpa [nbhd] using norm_lt_of_mem_closedCube hx

/-- The open cube is bounded. -/
theorem isBounded_openCube : Bornology.IsBounded openCube :=
  Metric.isBounded_ball.subset fun _ hx =>
    closedCube_subset_nbhd (fun k => (hx k).le)

/-- Frontier points of the cube lie in the closed cube with some coordinate `±1/40`. -/
theorem frontier_openCube {y : Space} (hy : y ∈ frontier openCube) :
    y ∈ closedCube ∧ ∃ k : Fin 3, |y k| = cubeHalf := by
  rw [isOpen_openCube.frontier_eq] at hy
  obtain ⟨hc, hno⟩ := hy
  have hcl := closure_openCube_subset hc
  refine ⟨hcl, ?_⟩
  by_contra h
  push Not at h
  exact hno fun k => lt_of_le_of_ne (hcl k) (h k)

/-! ### Face parametrizations -/

/-- Affine coordinate `[0,1] → [-1/40, 1/40]` on a face. -/
@[expose] def faceCoord (s : ℝ) : ℝ := (2 * s - 1) / 40

/-- The face `xₖ = e` of the cube (`|e| = 1/40` for the six faces), parametrized by the
unit square through the two remaining coordinates in increasing order. -/
@[expose] def facePoint (k : Fin 3) (e s t : ℝ) : Space :=
  (![WithLp.toLp 2 ![e, faceCoord s, faceCoord t], WithLp.toLp 2 ![faceCoord s, e, faceCoord t],
    WithLp.toLp 2 ![faceCoord s, faceCoord t, e]] : Fin 3 → Space) k

/-- Each face patch has modulus `(1/20)|s - s'| + (1/20)|t - t'|`. -/
theorem facePoint_modulus (k : Fin 3) (e s t s' t' : ℝ) :
    ‖facePoint k e s t - facePoint k e s' t'‖ ≤ 1 / 20 * |s - s'| + 1 / 20 * |t - t'| := by
  have key : ∀ a b : ℝ, Real.sqrt (a ^ 2 + b ^ 2) ≤ |a| + |b| := fun a b => by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_abs a, sq_abs b, abs_nonneg a, abs_nonneg b, mul_nonneg (abs_nonneg a)
      (abs_nonneg b)]
  have hs : faceCoord s - faceCoord s' = (s - s') / 20 := by unfold faceCoord; ring
  have ht : faceCoord t - faceCoord t' = (t - t') / 20 := by unfold faceCoord; ring
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  fin_cases k <;> simpa [facePoint, Real.norm_eq_abs, hs, ht, abs_div, div_eq_inv_mul] using
    key (|s - s'| / 20) (|t - t'| / 20)

/-- Face points with parameters in `[0,1]` lie in the closed cube. -/
theorem facePoint_mem {k : Fin 3} {e s t : ℝ} (he : |e| = cubeHalf)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) : facePoint k e s t ∈ closedCube := by
  have hcs : |faceCoord s| ≤ cubeHalf := by
    unfold faceCoord cubeHalf; rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  have hct : |faceCoord t| ≤ cubeHalf := by
    unfold faceCoord cubeHalf; rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  intro i
  fin_cases k <;> fin_cases i <;> simp [facePoint, he.le, hcs, hct]

/-- Every frontier point lies on one of the six face patches. -/
theorem exists_facePoint {y : Space} (hy : y ∈ closedCube) (k : Fin 3) :
    ∃ s ∈ Set.Icc (0 : ℝ) 1, ∃ t ∈ Set.Icc (0 : ℝ) 1, y = facePoint k (y k) s t := by
  have par : ∀ i : Fin 3, (40 * y i + 1) / 2 ∈ Set.Icc (0 : ℝ) 1 := fun i => by
    have := abs_le.mp (hy i); simp only [cubeHalf] at this
    constructor <;> linarith [this.1, this.2]
  have inv : ∀ i : Fin 3, faceCoord ((40 * y i + 1) / 2) = y i := fun i => by
    unfold faceCoord; ring
  fin_cases k
  · refine ⟨_, par 1, _, par 2, ?_⟩
    ext i; fin_cases i <;> simp [facePoint, inv]
  · refine ⟨_, par 0, _, par 2, ?_⟩
    ext i; fin_cases i <;> simp [facePoint, inv]
  · refine ⟨_, par 0, _, par 1, ?_⟩
    ext i; fin_cases i <;> simp [facePoint, inv]

/-! ### Vacuum fields on a neighbourhood of the closed cube -/

/-- `divOp` is additive. -/
private theorem divOp_add' (L₁ L₂ : Euclid3 →L[ℝ] Euclid3) :
    divOp (L₁ + L₂) = divOp L₁ + divOp L₂ := by
  simp [divOp, Finset.sum_add_distrib]

/-- `curlOp` is additive. -/
private theorem curlOp_add' (L₁ L₂ : Euclid3 →L[ℝ] Euclid3) :
    curlOp (L₁ + L₂) = curlOp L₁ + curlOp L₂ := by
  ext k
  fin_cases k <;> simp [curlOp] <;> ring

/-- The sum of two vacuum fields on the same region is a vacuum field (superposition). -/
theorem vacuumField_add {Ω : Set Euclid3} {B₁ B₂ : Euclid3 → Euclid3}
    (h₁ : VacuumField Ω B₁) (h₂ : VacuumField Ω B₂) : VacuumField Ω (B₁ + B₂) := by
  have hd : ∀ x ∈ Ω, fderiv ℝ (B₁ + B₂) x = fderiv ℝ B₁ x + fderiv ℝ B₂ x := fun x hx =>
    fderiv_add ((h₁.contDiffOn.contDiffAt (h₁.isOpen.mem_nhds hx)).differentiableAt
      (by norm_num)) ((h₂.contDiffOn.contDiffAt (h₁.isOpen.mem_nhds hx)).differentiableAt
      (by norm_num))
  refine ⟨h₁.isOpen, h₁.contDiffOn.add h₂.contDiffOn, fun x hx => ?_, fun x hx => ?_⟩
  · rw [fieldDiv, hd x hx, divOp_add', ← fieldDiv, ← fieldDiv, h₁.div_eq_zero x hx,
      h₂.div_eq_zero x hx, add_zero]
  · rw [fieldCurl, hd x hx, curlOp_add', ← fieldCurl, ← fieldCurl, h₁.curl_eq_zero x hx,
      h₂.curl_eq_zero x hx, add_zero]

/-- One manufactured (or nominal) coil gives a vacuum field on `U`: closed `C¹` curve,
and `U` stays at distance `≥ 7/50` from the actual coil. -/
private theorem one_vacuumField (μ₀ J : ℝ) (c actual : ℝ → Space)
    (h : WithinTolerance c actual) (sep : ∀ x ∈ nbhd, ∀ t, 3 / 20 ≤ ‖x - c t‖) :
    VacuumField nbhd (filamentField μ₀ J actual 0 (2 * Real.pi)) := by
  refine Sanity.filamentField_vacuumField' μ₀ J actual 0 (2 * Real.pi) Metric.isOpen_ball
    (fun t _ => h.differentiable t) h.tangent_continuous.continuousOn ?_ ?_
  · intro x hx t _
    have he : (x - actual t) - (x - c t) = -(actual t - c t) := by abel
    have hs : 7 / 50 ≤ ‖x - actual t‖ :=
      perturbed_norm_lower (x - c t) (x - actual t) (ε := 1 / 1000)
        (by linarith [sep x hx t]) (by simpa only [he, norm_neg] using h.position t)
    exact norm_pos_iff.mp (by linarith)
  · simpa using (h.closed 0).symm

/-- **Both fields are vacuum fields near the closed cube.** For every pair of
manufactured coils within tolerance and all currents, the manufactured field is a
`VacuumField` on the open ball `U ⊇ closure Ω`. The nominal field is the special case
`upper = upperCoil`, `lower = lowerCoil` (`nominal_vacuumField`). -/
theorem manufactured_vacuumField (μ₀ J₁ J₂ : ℝ) (upper lower : ℝ → Space)
    (hu : WithinTolerance upperCoil upper) (hl : WithinTolerance lowerCoil lower) :
    VacuumField nbhd (manufacturedField μ₀ J₁ J₂ upper lower) := by
  have hreg : ∀ x ∈ nbhd, ObservationRegion x := fun x hx => by
    simp only [nbhd, Metric.mem_ball, dist_zero_right] at hx
    exact hx.le
  exact vacuumField_add
    (one_vacuumField μ₀ J₁ upperCoil upper hu fun x hx t => (source_clearance x (hreg x hx) t).1)
    (one_vacuumField μ₀ J₂ lowerCoil lower hl fun x hx t => (source_clearance x (hreg x hx) t).2)

/-- The nominal field is a vacuum field on `U`. -/
theorem nominal_vacuumField (μ₀ I J : ℝ) : VacuumField nbhd (field μ₀ I J) :=
  manufactured_vacuumField μ₀ I J upperCoil lowerCoil nominal_within_tolerance.1
    nominal_within_tolerance.2

/-- Continuity of the manufactured field on `closure Ω` (needed by the maximum
principle), from `C²` regularity on the neighbourhood `U`. -/
theorem manufactured_continuousOn_closure (μ₀ J₁ J₂ : ℝ) (upper lower : ℝ → Space)
    (hu : WithinTolerance upperCoil upper) (hl : WithinTolerance lowerCoil lower) :
    ContinuousOn (manufacturedField μ₀ J₁ J₂ upper lower) (closure openCube) :=
  (manufactured_vacuumField μ₀ J₁ J₂ upper lower hu hl).contDiffOn.continuousOn.mono
    (closure_openCube_subset.trans closedCube_subset_nbhd)

/-! ### Boundary-to-volume transfer -/

/-- **Volume error from frontier error.** For manufactured coils within tolerance and
any currents, a bound `δ` on `‖B_actual − B_nominal‖` over the frontier of the cube holds
at every point of the closed cube. -/
theorem volume_error_of_frontier {μ₀ I J₁ J₂ δ : ℝ} (upper lower : ℝ → Space)
    (hu : WithinTolerance upperCoil upper) (hl : WithinTolerance lowerCoil lower)
    (hδ : 0 ≤ δ)
    (hM : ∀ y ∈ frontier openCube,
      ‖manufacturedField μ₀ J₁ J₂ upper lower y - field μ₀ I I y‖ ≤ δ) :
    ∀ x ∈ closedCube, ‖manufacturedField μ₀ J₁ J₂ upper lower x - field μ₀ I I x‖ ≤ δ := by
  have hsub : openCube ⊆ nbhd := fun x hx => closedCube_subset_nbhd fun k => (hx k).le
  have h₁ := (manufactured_vacuumField μ₀ J₁ J₂ upper lower hu hl).mono isOpen_openCube hsub
  have h₂ := (nominal_vacuumField μ₀ I I).mono isOpen_openCube hsub
  have hc₂ : ContinuousOn (field μ₀ I I) (closure openCube) :=
    manufactured_continuousOn_closure μ₀ I I upperCoil lowerCoil
      nominal_within_tolerance.1 nominal_within_tolerance.2
  intro x hx
  exact VacuumField.error_le_of_frontier h₁ h₂ isBounded_openCube
    (manufactured_continuousOn_closure μ₀ J₁ J₂ upper lower hu hl) hc₂ hδ hM x
    (closedCube_subset_closure hx)

/-- **Pointwise budget used on the frontier only.** Combined manufacturing and 1% current
errors, bounded on the frontier by `combined_field_error`, give `‖ΔB‖ ≤ μ₀I/4` throughout
the closed cube. -/
theorem combined_volume_error {μ₀ I J₁ J₂ : ℝ} (hμ : 0 < μ₀) (hI : 0 < I)
    (upper lower : ℝ → Space) (hu : WithinTolerance upperCoil upper)
    (hl : WithinTolerance lowerCoil lower)
    (hJ₁ : |J₁ - I| ≤ I / 100) (hJ₂ : |J₂ - I| ≤ I / 100) :
    ∀ x ∈ closedCube,
      ‖manufacturedField μ₀ J₁ J₂ upper lower x - field μ₀ I I x‖ ≤ (μ₀ * I) / 4 :=
  volume_error_of_frontier upper lower hu hl (by positivity) fun y hy =>
    combined_field_error hμ hI upper lower hu hl hJ₁ hJ₂ y
      (closedCube_subset_region (frontier_openCube hy).1)

/-- The certified Lipschitz constant of `ΔB = B_actual(J₁,J₂) − B_nominal(I,I)` on the
observation ball: actual-field derivative bound plus nominal Lipschitz bound. -/
@[expose] def errorLip (μ₀ I J₁ J₂ : ℝ) : ℝ :=
  25250 / 343 * (|μ₀ * J₁| + |μ₀ * J₂|) + 1600 / 27 * (|μ₀ * I| + |μ₀ * I|)

/-- The Lipschitz constant is nonnegative. -/
theorem errorLip_nonneg (μ₀ I J₁ J₂ : ℝ) : 0 ≤ errorLip μ₀ I J₁ J₂ := by
  unfold errorLip; positivity

/-- `ΔB` is `errorLip`-Lipschitz on the observation ball. -/
theorem error_lipschitz (μ₀ I J₁ J₂ : ℝ) (upper lower : ℝ → Space)
    (hu : WithinTolerance upperCoil upper) (hl : WithinTolerance lowerCoil lower)
    {x y : Space} (hx : ObservationRegion x) (hy : ObservationRegion y) :
    ‖(manufacturedField μ₀ J₁ J₂ upper lower x - field μ₀ I I x) -
      (manufacturedField μ₀ J₁ J₂ upper lower y - field μ₀ I I y)‖ ≤
      errorLip μ₀ I J₁ J₂ * ‖x - y‖ := by
  have hs : Convex ℝ {z : Space | ObservationRegion z} := by
    simpa only [Metric.closedBall, dist_zero_right, ObservationRegion] using
      convex_closedBall (0 : Space) (1 / 20)
  have ha := hs.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (manufactured_field_derivative μ₀ J₁ J₂ upper lower hu hl z hz).1)
    (fun z hz => (manufactured_field_derivative μ₀ J₁ J₂ upper lower hu hl z hz).2) hy hx
  have hn := field_difference μ₀ I I x y hx hy
  have he : (manufacturedField μ₀ J₁ J₂ upper lower x - field μ₀ I I x) -
      (manufacturedField μ₀ J₁ J₂ upper lower y - field μ₀ I I y) =
      (manufacturedField μ₀ J₁ J₂ upper lower x - manufacturedField μ₀ J₁ J₂ upper lower y) -
        (field μ₀ I I x - field μ₀ I I y) := by abel
  rw [he]
  refine (norm_sub_le _ _).trans ?_
  unfold errorLip
  linarith

/-- **Volume error from boundary samples (surface cover + maximum principle).** If
`‖ΔB‖ ≤ m` at the grid points `facePoint k e (i/N) (j/N)` (`i, j ≤ N`) of the six faces
`xₖ = e`, `|e| = 1/40`, then `‖ΔB‖ ≤ m + errorLip/(20N)` throughout the closed cube. -/
theorem volume_error_of_boundary_samples {μ₀ I J₁ J₂ m : ℝ} (upper lower : ℝ → Space)
    (hu : WithinTolerance upperCoil upper) (hl : WithinTolerance lowerCoil lower)
    {N : ℕ} (hN : 0 < N)
    (samples : ∀ k : Fin 3, ∀ e : ℝ, |e| = cubeHalf → ∀ i ≤ N, ∀ j ≤ N,
      ‖manufacturedField μ₀ J₁ J₂ upper lower (facePoint k e (i / N) (j / N)) -
        field μ₀ I I (facePoint k e (i / N) (j / N))‖ ≤ m) :
    ∀ x ∈ closedCube, ‖manufacturedField μ₀ J₁ J₂ upper lower x - field μ₀ I I x‖ ≤
      m + errorLip μ₀ I J₁ J₂ / (20 * N) := by
  set ΔB : Space → Space := fun z => manufacturedField μ₀ J₁ J₂ upper lower z - field μ₀ I I z
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hL := errorLip_nonneg μ₀ I J₁ J₂
  have hm : 0 ≤ m := (norm_nonneg _).trans (samples 0 cubeHalf (abs_of_pos (by
    norm_num [cubeHalf])) 0 (Nat.zero_le _) 0 (Nat.zero_le _))
  have hr : errorLip μ₀ I J₁ J₂ * (1 / 20 / (2 * N) + 1 / 20 / (2 * N)) =
      errorLip μ₀ I J₁ J₂ / (20 * N) := by field_simp; ring
  refine volume_error_of_frontier upper lower hu hl (by positivity) fun y hy => ?_
  obtain ⟨hyc, k, hk⟩ := frontier_openCube hy
  obtain ⟨s, hs, t, ht, hyeq⟩ := exists_facePoint hyc k
  rw [hyeq]
  have key := patch_norm_le_of_grid (facePoint k (y k)) ΔB
    (A := 1 / 20) (B := 1 / 20) (by norm_num) (by norm_num) hL hN hN
    (fun s _ t _ s' _ t' _ => facePoint_modulus k _ s t s' t')
    (fun s hs t ht s' hs' t' ht' => error_lipschitz μ₀ I J₁ J₂ upper lower hu hl
      (closedCube_subset_region (facePoint_mem hk hs ht))
      (closedCube_subset_region (facePoint_mem hk hs' ht')))
    (fun i hi j hj => samples k _ hk i hi j hj) s hs t ht
  rw [hr] at key
  exact key

/-- **Calibrated sample certificate.** Under the 1% current budget, boundary samples
`‖ΔB‖ ≤ m` on the six face grids give `‖ΔB‖ ≤ m + 14 μ₀ I / N` in the whole cube. -/
theorem calibrated_volume_error_of_boundary_samples {μ₀ I J₁ J₂ m : ℝ} (hμ : 0 < μ₀)
    (hI : 0 < I) (upper lower : ℝ → Space)
    (hu : WithinTolerance upperCoil upper) (hl : WithinTolerance lowerCoil lower)
    (hJ₁ : |J₁ - I| ≤ I / 100) (hJ₂ : |J₂ - I| ≤ I / 100) {N : ℕ} (hN : 0 < N)
    (samples : ∀ k : Fin 3, ∀ e : ℝ, |e| = cubeHalf → ∀ i ≤ N, ∀ j ≤ N,
      ‖manufacturedField μ₀ J₁ J₂ upper lower (facePoint k e (i / N) (j / N)) -
        field μ₀ I I (facePoint k e (i / N) (j / N))‖ ≤ m) :
    ∀ x ∈ closedCube, ‖manufacturedField μ₀ J₁ J₂ upper lower x - field μ₀ I I x‖ ≤
      m + 14 * (μ₀ * I) / N := by
  intro x hx
  have h := volume_error_of_boundary_samples upper lower hu hl hN samples x hx
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hJ : ∀ J : ℝ, |J - I| ≤ I / 100 → |μ₀ * J| ≤ 101 / 100 * (μ₀ * I) := fun J hJ => by
    have ha : |J| ≤ 101 / 100 * I := by
      have ht := abs_add_le (J - I) I
      rw [sub_add_cancel, abs_of_pos hI] at ht
      linarith
    rw [abs_mul, abs_of_pos hμ]
    nlinarith
  have hLb : errorLip μ₀ I J₁ J₂ ≤ 280 * (μ₀ * I) := by
    unfold errorLip
    rw [abs_of_pos (mul_pos hμ hI)]
    nlinarith [hJ J₁ hJ₁, hJ J₂ hJ₂, mul_pos hμ hI]
  have hq : errorLip μ₀ I J₁ J₂ / (20 * N) ≤ 14 * (μ₀ * I) / N := by
    rw [div_le_div_iff₀ (by positivity) hNr]
    nlinarith
  linarith

/-! ### Sanity checks -/

/-- Degenerate case: nominal coils and nominal currents have zero error, so zero samples
certify zero volume error (with `m = 0` the interpolation term remains, as it must for
a sample-only argument). -/
theorem nominal_zero_samples (μ₀ I : ℝ) (k : Fin 3) (e s t : ℝ) :
    ‖manufacturedField μ₀ I I upperCoil lowerCoil (facePoint k e s t) -
      field μ₀ I I (facePoint k e s t)‖ = 0 := by
  simp [manufacturedField, field]

/-- Special case: the sample theorem at the origin (the probe point) for the nominal
configuration gives the bound `0 + errorLip/(20N)` with `N = 1`. -/
theorem nominal_origin_coarse (μ₀ I : ℝ) :
    ‖manufacturedField μ₀ I I upperCoil lowerCoil 0 - field μ₀ I I 0‖ ≤
      0 + errorLip μ₀ I I I / (20 * (1 : ℕ)) :=
  volume_error_of_boundary_samples (m := 0) upperCoil lowerCoil nominal_within_tolerance.1
    nominal_within_tolerance.2 Nat.one_pos
    (fun k e _ _ _ _ _ => (nominal_zero_samples μ₀ I k e _ _).le) 0
    (fun k => (zero_mem_openCube k).le)

end PlasmaLean.Design.VacuumPair
