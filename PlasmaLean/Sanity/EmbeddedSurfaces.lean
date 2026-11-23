/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Contract.EmbeddedSurfaces
public import PlasmaLean.Sanity.FormFluxSurfaceEmbedded

/-!
# Sanity checks for the embeddedness clause of C1 (`Theory/Contract/EmbeddedSurfaces`)

* Accepted: a family consisting of circular tori satisfies `EmbeddedSurfaces`
  (`circ_embeddedSurfaces`).
* Rejected: a family containing the doubly covered torus does not (`dbl_not_embeddedSurfaces`),
  and no field satisfies clause C1 with embeddedness on such a family
  (`dbl_not_embeddedCurrentFreeTransform`); likewise for the torus collapsed to a circle
  (`circle_not_embeddedCurrentFreeTransform`).
* Degenerate: the empty family satisfies `EmbeddedSurfaces` but not the contract clause, which
  needs a surface (`empty_embeddedSurfaces`, `empty_not_embeddedCurrentFreeTransform`).

* Rational return: the wire field has a smooth winding-one parametrization with transform zero
  and a stationary poloidal tangent (`stationary_iotaOnTorus`, `stationary_not_embeddedTorus`).
  Its section is a circle with lifted angle `θ − sin θ`.

The rational stellarator supplies a nonzero-transform witness in
`Design/RationalStellaratorEmbedded` (`rationalStellarator_embeddedCurrentFreeTransform`).
-/

public section
noncomputable section

namespace PlasmaLean.Sanity.EmbeddedSurfaces

open PlasmaLean.Vacuum PlasmaLean.Fields PlasmaLean.Contract PlasmaLean.Forms
open PlasmaLean.Design.RationalStellaratorContract
open PlasmaLean.Sanity.FormFluxSurfaceEmbedded

/-- **Accepted**: circular tori with `0 < a < 1` form a family of embedded surfaces, for any
recorded transform and loop angle. -/
theorem circ_embeddedSurfaces {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (ι φ₀ : ℝ) :
    EmbeddedSurfaces {(⟨circR a, circZ a, ι, φ₀⟩ : SurfaceData)} := by
  intro s hs
  rw [Set.mem_singleton_iff.1 hs]
  exact circ_embeddedTorus ha ha1

/-- **Rejected**: a family containing the doubly covered torus is not a family of embedded
surfaces. -/
theorem dbl_not_embeddedSurfaces (a ι φ₀ : ℝ) :
    ¬ EmbeddedSurfaces {(⟨dblR a, dblZ a, ι, φ₀⟩ : SurfaceData)} :=
  fun h => dbl_not_embeddedTorus a (h _ rfl)

/-- **Rejected**: no field satisfies clause C1 with embeddedness on a family containing the
doubly covered torus. -/
theorem dbl_not_embeddedCurrentFreeTransform (μ₀ : ℝ) (B : Space → Space) (a ι φ₀ Imax ιmin : ℝ) :
    ¬ EmbeddedCurrentFreeTransform μ₀ B {(⟨dblR a, dblZ a, ι, φ₀⟩ : SurfaceData)} Imax ιmin :=
  not_embeddedCurrentFreeTransform_of_not_embedded (s := ⟨dblR a, dblZ a, ι, φ₀⟩) rfl
    (dbl_not_embeddedTorus a)

/-- **Rejected**: no field satisfies clause C1 with embeddedness on a family containing the
torus collapsed to a circle. -/
theorem circle_not_embeddedCurrentFreeTransform (μ₀ : ℝ) (B : Space → Space)
    (ι φ₀ Imax ιmin : ℝ) :
    ¬ EmbeddedCurrentFreeTransform μ₀ B {(⟨circR 0, circZ 0, ι, φ₀⟩ : SurfaceData)} Imax ιmin :=
  not_embeddedCurrentFreeTransform_of_not_embedded (s := ⟨circR 0, circZ 0, ι, φ₀⟩) rfl
    circle_not_embeddedTorus

/-- **Degenerate**: the empty family satisfies the embeddedness clause vacuously. -/
theorem empty_embeddedSurfaces : EmbeddedSurfaces ∅ := fun _ hs => absurd hs (Set.notMem_empty _)

/-- **Degenerate**: the empty family does not satisfy clause C1 with embeddedness, because
clause C1 needs at least one surface. -/
theorem empty_not_embeddedCurrentFreeTransform (μ₀ : ℝ) (B : Space → Space) (Imax ιmin : ℝ) :
    ¬ EmbeddedCurrentFreeTransform μ₀ B ∅ Imax ιmin :=
  fun h => Set.not_nonempty_empty h.nonempty

/-! ## Winding one with a rational return and a stationary tangent -/

open Real PlasmaLean.Design.RationalStellarator

/-- The angular reparametrization advances one turn and has zero derivative at the origin. -/
def stationaryAngle (θ : ℝ) : ℝ := θ - sin θ

/-- Radial coordinate of the reparametrized circular section. -/
def stationaryR (a θ φ : ℝ) : ℝ := circR a (stationaryAngle θ) φ

/-- Height of the reparametrized circular section. -/
def stationaryZ (a θ φ : ℝ) : ℝ := circZ a (stationaryAngle θ) φ

private theorem stationaryAngle_turn (θ : ℝ) :
    stationaryAngle (θ + 2 * π) = stationaryAngle θ + 2 * π := by
  simp only [stationaryAngle, sin_add_two_pi]
  ring

/-- The reparametrized sections have smooth, doubly periodic profiles. -/
theorem stationary_periodicC2Torus (a : ℝ) : PeriodicC2Torus (stationaryR a) (stationaryZ a) := by
  have hθ : ContDiff ℝ 2 (fun p : ℝ × ℝ => stationaryAngle p.1) :=
    contDiff_fst.sub contDiff_fst.sin
  refine ⟨contDiff_const.add (contDiff_const.mul hθ.cos), contDiff_const.mul hθ.sin, ?_, ?_,
    fun _ _ => rfl, fun _ _ => rfl⟩
  · intro θ φ
    simp [stationaryR, circR, stationaryAngle_turn]
  · intro θ φ
    simp [stationaryZ, circZ, stationaryAngle_turn]

/-- The wire field has transform zero on this winding-one parametrization. -/
theorem stationary_iotaOnTorus {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    IotaOnTorus toroidal (stationaryR a) (stationaryZ a) 0 := by
  have h := stationary_periodicC2Torus a
  have hc := (circTorus_iotaOnTorus ha ha1).1
  constructor
  · refine ⟨h.contDiff_R.continuous, h.contDiff_z.continuous,
      fun θ φ => hc.R_pos (stationaryAngle θ) φ, h.per_θ_R, h.per_θ_z, h.per_φ_R, h.per_φ_z, ?_⟩
    intro θ φ
    simpa only [stationaryR, stationaryZ, mul_zero, add_zero] using hc.flow (stationaryAngle θ) φ
  · refine ⟨fun _ => 1, fun _ => 0, fun θ _ => stationaryAngle θ, continuous_const,
      continuous_const, fun _ => rfl, fun _ => rfl, ?_, ?_, fun θ _ => stationaryAngle_turn θ,
      fun _ _ => rfl⟩
    · exact continuous_fst.sub (Real.continuous_sin.comp continuous_fst)
    · intro θ φ
      exact ⟨a, ha, by simp [stationaryR, circR], by simp [stationaryZ, circZ]⟩

/-- Winding one and smooth profiles still allow a stationary tangent at rational transform. -/
theorem stationary_not_embeddedTorus {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ¬ EmbeddedTorus (stationaryR a) (stationaryZ a) := by
  intro he
  have hd : HasDerivAt stationaryAngle 0 0 := by
    change HasDerivAt (id - Real.sin) 0 0
    simpa using (hasDerivAt_id (0 : ℝ)).sub (hasDerivAt_sin 0)
  have hR : deriv (fun t => stationaryR a t 0) 0 = 0 := by
    simpa [stationaryR, circR] using ((hd.cos.const_mul a).const_add 1).deriv
  have hz : deriv (fun t => stationaryZ a t 0) 0 = 0 := by
    simpa [stationaryZ, circZ] using (hd.sin.const_mul a).deriv
  exact ((he.toPeriodicC2Torus.injective_fderiv_torusMap_iff (θ := 0) (φ := 0)
    ((stationary_iotaOnTorus ha ha1).1.R_pos 0 0)).mp (he.immersion (0, 0))) ⟨hR, hz⟩

end PlasmaLean.Sanity.EmbeddedSurfaces
