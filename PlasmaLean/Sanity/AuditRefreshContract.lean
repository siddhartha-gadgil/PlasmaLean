/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Contract.StellaratorContract

/-!
# Audit refresh (31 October 2026): regression for the C1 current clause (finding AR-H1)

Record: `notes/audit/2026-10-31-refresh-audit.md`, finding AR-H1.

**The finding.** Before the fix, the C1 current clause bounded the flux `netToroidalCurrent` of
the Ampère current through an existentially chosen coordinate section, constrained only by the
weak spanning condition `SectionSpans` (outer edge the poloidal loop, inner edge a point). The
pinched section `X(k, χ) = loop(−π + (χ + π) k/k₀)` (`pinchSection`) satisfies it (`pinch_spans`),
but its image is the loop itself (a curve), so `∂_k X ∥ ∂_χ X` and the flux of **every** field
through it is zero (`netToroidalCurrent_pinch`). So every field with suitable invariant tori
satisfied the old clause with `I_max = 0`. These two facts remain true of the section flux,
which is now only an auxiliary notion.

**After the fix.** C1 bounds `loopCurrent μ₀ B R z φ₀ = μ₀⁻¹ ∮ B · dl` around the torus's own
poloidal loop; no section is chosen. Regression fixtures:
* non-vacuity: the field `rotY = (−z, 0, x − 1)` (uniform current `μ₀ J = −2 e_y`) has
  circulation exactly `2π a²` around the circular poloidal loop `R = 1 + a cos θ`, `z = a sin θ`
  at `φ₀ = 0` (`rotY_poloidalCirculation`), so a nonzero loop current
  (`rotY_loopCurrent_ne_zero`);
* the pinch no longer helps: the pinched section of the same loop carries zero flux of `rotY`
  (`rotY_pinch_flux_zero`), yet `rotY` fails the C1 current clause with `I_max = 0` on every
  family containing that surface (`rotY_not_currentFreeTransform`), whatever `ι_min`;
* `CurrentFreeTransform.circulation_eq_zero`: C1 with `I_max = 0` forces zero circulation around
  every poloidal loop of the family.
-/

open scoped RealInnerProductSpace

public section
noncomputable section

namespace PlasmaLean.Sanity.AuditRefresh

open Real Set PlasmaLean.Fields PlasmaLean.Contract

/-! ## The pinched section (facts about the auxiliary section flux) -/

/-- The reparametrization `(k, χ) ↦ −π + (χ + π) k/k₀`. -/
@[expose] def pinchArg (k₀ : ℝ) (v : Space) : ℝ := -π + (v 1 + π) * v 0 / k₀

/-- The **pinched section** `X(k, χ, ζ) = loop(−π + (χ + π) k/k₀)`: its image is the poloidal
loop. -/
@[expose] def pinchSection (R z : ℝ → ℝ → ℝ) (φ₀ k₀ : ℝ) (v : Space) : Space :=
  poloidalLoop R z φ₀ (pinchArg k₀ v)

/-- The flux density through two parallel vectors vanishes. -/
theorem tripleFlux_smul_smul (V w : Space) (a b : ℝ) : tripleFlux V (a • w) (b • w) = 0 := by
  simp [tripleFlux, cross_self]

/-- **The pinched section carries zero section flux for every field.** -/
theorem netToroidalCurrent_pinch (μ₀ : ℝ) (B : Space → Space) {R z : ℝ → ℝ → ℝ} {φ₀ k₀ : ℝ}
    (ζ₀ : ℝ) (hd : ∀ t, DifferentiableAt ℝ (poloidalLoop R z φ₀) t) :
    netToroidalCurrent μ₀ B (pinchSection R z φ₀ k₀) ζ₀ k₀ = 0 := by
  have hg : ∀ v : Space, DifferentiableAt ℝ (pinchArg k₀) v := fun v => by
    unfold pinchArg
    fun_prop
  have hX : ∀ v : Space, ∀ u : Space, fderiv ℝ (pinchSection R z φ₀ k₀) v u =
      (fderiv ℝ (pinchArg k₀) v u) • deriv (poloidalLoop R z φ₀) (pinchArg k₀ v) := fun v u => by
    have h := ((hd (pinchArg k₀ v)).hasDerivAt.hasFDerivAt).comp v (hg v).hasFDerivAt
    rw [show pinchSection R z φ₀ k₀ = poloidalLoop R z φ₀ ∘ pinchArg k₀ from rfl, h.fderiv]
    simp
  unfold netToroidalCurrent
  simp only [hX, tripleFlux_smul_smul, intervalIntegral.integral_zero]

/-- The pinched section spans the poloidal loop in the weak sense `SectionSpans`. -/
theorem pinch_spans {R z : ℝ → ℝ → ℝ} {φ₀ k₀ ζ₀ : ℝ} (hk : 0 < k₀) :
    SectionSpans (pinchSection R z φ₀ k₀) ζ₀ k₀ (poloidalLoop R z φ₀) := by
  refine ⟨hk.le, fun χ => ?_, fun χ χ' => ?_⟩
  · simp only [pinchSection, pinchArg, coordPt, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    congr 1
    field_simp
    ring
  · simp [pinchSection, pinchArg, coordPt]

/-- Concrete instance: the uniform-current field `B = e_z × x` (`μ₀ J = 2 e_z`) has zero section
flux through the pinched section of the circular loop `R = 1 + cos θ/2`, `z = sin θ/2` at
`φ₀ = 0`. -/
theorem rotation_pinch_current_zero (μ₀ : ℝ) :
    netToroidalCurrent μ₀ (crossBilinear (basis 2))
      (pinchSection (fun θ _ => 1 + cos θ / 2) (fun θ _ => sin θ / 2) 0 1) 0 1 = 0 :=
  netToroidalCurrent_pinch μ₀ _ 0 fun t => by
    refine (differentiableAt_piLp 2).2 fun i => ?_
    fin_cases i <;> simp [poloidalLoop, cylPoint]

/-! ## The intrinsic loop current is not vacuous -/

/-- The circular torus profile `R = 1 + a cos θ`. -/
@[expose] def circR (a : ℝ) (θ _φ : ℝ) : ℝ := 1 + a * cos θ

/-- The circular torus profile `z = a sin θ`. -/
@[expose] def circZ (a : ℝ) (θ _φ : ℝ) : ℝ := a * sin θ

/-- The uniform-current field `rotY(x, y, z) = (−z, 0, x − 1)`, a rigid rotation about the line
`x = 1, z = 0` (`∇ × rotY = −2 e_y`). -/
@[expose] def rotY (x : Space) : Space := WithLp.toLp 2 ![-x 2, 0, x 0 - 1]

/-- The velocity of the circular poloidal loop at `φ₀ = 0`. -/
theorem hasDerivAt_circLoop (a θ : ℝ) :
    HasDerivAt (poloidalLoop (circR a) (circZ a) 0)
      (WithLp.toLp 2 ![-(a * sin θ) * cos 0, -(a * sin θ) * sin 0, a * cos θ]) θ := by
  refine hasDerivAt_poloidalLoop (R' := -(a * sin θ)) (z' := a * cos θ) ?_ ?_
  · simpa [circR] using ((hasDerivAt_cos θ).const_mul a).const_add 1
  · simpa [circZ] using (hasDerivAt_sin θ).const_mul a

/-- **Non-vacuity**: the circulation of `rotY` around the circular poloidal loop of minor radius
`a` is exactly `2π a²`. -/
theorem rotY_poloidalCirculation (a : ℝ) :
    poloidalCirculation rotY (circR a) (circZ a) 0 = 2 * π * a ^ 2 := by
  have hI : ∀ θ, ⟪rotY (poloidalLoop (circR a) (circZ a) 0 θ),
      deriv (poloidalLoop (circR a) (circZ a) 0) θ⟫ = a ^ 2 := fun θ => by
    rw [(hasDerivAt_circLoop a θ).deriv]
    simp [rotY, poloidalLoop, cylPoint, circR, circZ, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_three]
    linear_combination a ^ 2 * sin_sq_add_cos_sq θ
  simp only [poloidalCirculation, lineIntegral, hI, intervalIntegral.integral_const,
    smul_eq_mul]
  ring

/-- The loop current of `rotY` around the circular loop: `2π a²/μ₀`. -/
theorem rotY_loopCurrent (μ₀ a : ℝ) :
    loopCurrent μ₀ rotY (circR a) (circZ a) 0 = 2 * π * a ^ 2 / μ₀ := by
  rw [loopCurrent, rotY_poloidalCirculation]

/-- **Non-vacuity of the C1 current**: there is a field with nonzero loop current. -/
theorem rotY_loopCurrent_ne_zero {μ₀ a : ℝ} (hμ : μ₀ ≠ 0) (ha : a ≠ 0) :
    loopCurrent μ₀ rotY (circR a) (circZ a) 0 ≠ 0 := by
  rw [rotY_loopCurrent]
  have := pi_pos
  have : 0 < a ^ 2 := by positivity
  exact div_ne_zero (by positivity) hμ

/-- The pinched section of the circular loop carries zero flux of `rotY`. -/
theorem rotY_pinch_flux_zero (μ₀ a : ℝ) :
    netToroidalCurrent μ₀ rotY (pinchSection (circR a) (circZ a) 0 1) 0 1 = 0 :=
  netToroidalCurrent_pinch μ₀ _ 0 fun t => (hasDerivAt_circLoop a t).differentiableAt

/-- The C1 surface data of the circular loop (the transform value is irrelevant here). -/
@[expose] def circSurface (a ι : ℝ) : SurfaceData where
  R := circR a
  z := circZ a
  iota := ι
  φ₀ := 0

/-- **Regression (AR-H1 fixed): the pinch no longer helps.** Although the pinched section of the
circular loop has zero flux of `rotY` (`rotY_pinch_flux_zero`), `rotY` fails the C1 current
clause with `I_max = 0` on every family containing the circular surface, for every `ι_min`. -/
theorem rotY_not_currentFreeTransform {μ₀ a ι ιmin : ℝ} (hμ : 0 < μ₀) (ha : a ≠ 0)
    {S : Set SurfaceData} (hs : circSurface a ι ∈ S) :
    ¬ CurrentFreeTransform μ₀ rotY S 0 ιmin :=
  not_currentFreeTransform_of_current hs (abs_pos.2 (rotY_loopCurrent_ne_zero hμ.ne' ha))

/-- C1 with `I_max = 0` forces zero circulation around every poloidal loop of the family. -/
theorem CurrentFreeTransform.circulation_eq_zero {μ₀ ιmin : ℝ} {B : Space → Space}
    {S : Set SurfaceData} (h : CurrentFreeTransform μ₀ B S 0 ιmin) {s : SurfaceData}
    (hs : s ∈ S) : poloidalCirculation B s.R s.z s.φ₀ = 0 := by
  have h0 := abs_nonpos_iff.1 (h.current_le s hs)
  rw [SurfaceData.current, loopCurrent, div_eq_zero_iff] at h0
  exact h0.resolve_right h.mu0_pos.ne'

end PlasmaLean.Sanity.AuditRefresh
