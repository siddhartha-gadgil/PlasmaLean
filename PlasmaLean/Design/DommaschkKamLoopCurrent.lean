/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamNested
public import PlasmaLean.Theory.Fields.FormConvexRegion

/-!
# Stokes on the planar cross-section, for the certified Dommaschk tori

On-demand module (not imported by `PlasmaLean.lean`). Build:
`lake build PlasmaLean.Design.DommaschkKamLoopCurrent` after `DommaschkKamNested` (build stale
dependencies one at a time).

`Theory/Fields/FormConvexRegion` proves the corollary of contract clause C1 "Stokes on the planar
poloidal cross-section": a field that is a vacuum field on the meridian half-space of a poloidal
loop has zero circulation around that loop. `Sanity/ContractLoopCurrentFixture` instantiates it
for the rational stellarator field. The certified Dommaschk tori C and A live in on-demand
modules and were not covered there. This module instantiates the same corollary for the
Dommaschk candidate `DommaschkQA2R.field DommaschkQA2R.candidate`.

## What is proved

* `meridianHalfSpace_subset_domain`, `candidate_vacuum_meridian`: every meridian half-space
  misses the `z`-axis, so the candidate (a vacuum field off the `z`-axis, a region that is not
  simply connected) is a vacuum field on every meridian half-space, a convex region.
* Clause C1, any family and any allowance (the clause is a hypothesis):
  `candidate_current_eq_zero`, `candidate_circulation_eq_zero` (each surface has zero net
  current and zero poloidal circulation), `candidate_imax_zero` (the clause holds with allowance
  `0`).
* Any `FieldTorus` of the candidate with a `C¹` poloidal loop, any rotation number:
  `fieldTorus_loopCurrent`, `fieldTorus_period` (the de Rham period of `B♭` on the class of the
  poloidal loop in the meridian half-space is `0`).
* The certified tori: for every `ExactTorusC` and every `ExactTorusA`, zero loop current at every
  toroidal angle `φ₀` and every `μ₀` (`exactTorusC_loopCurrent`, `exactTorusA_loopCurrent`), zero
  period (`exactTorusC_period`, `exactTorusA_period`), with `ι_C ≠ 0`, `ι_A ≠ 0`
  (`dkIotaC_ne_zero`, `dkIotaA_ne_zero`). Such tori exist, unconditionally
  (`exists_fieldTorus_loopCurrent_eq_zero`), and the two-surface nested family of
  `DommaschkKamNested.dommaschk_nested_C1` has zero current on both surfaces by the topological
  corollary (`dommaschk_nested_current_eq_zero`).
* The two routes agree: `exactTorusC_routes_agree`, `exactTorusA_routes_agree`.

## What this does and does not mean

1. **A second proof of a known fact, not new information about the device.**
   `DommaschkQA2R.field_poloidalCirculation_eq_zero` and
   `DommaschkQA2R.candidate_loopCurrent_eq_zero` already prove zero poloidal circulation for
   every closed `C¹` poloidal loop with `R > 0`, by an elementary route: the field is
   `∇φ + ∇Φ` with `Φ` single-valued off the axis, the toroidal part is orthogonal to the loop
   and the gradient part integrates to zero. Every instance of `CurrentFreeTransform` for this
   field in the build (`dommaschk_C1_of_exact`, `dommaschkA_C1_of_exact`,
   `dommaschk_nested_C1`) is already proved with allowance `I_max = 0` by that route. The
   statements here reach the same value `0` by a different, topological argument (the loop lies
   in a convex region on which the field is curl-free; the fundamental group of that region is
   trivial). They are a consistency check of the two routes and a check that the hypotheses of
   the corollary are satisfiable together with a non-zero rotational transform. No allowance is
   improved: there is no instance whose current bound was proved by an estimate.
2. **Staging.** `candidate_imax_zero` takes the clause with an arbitrary allowance and returns
   allowance `0`; applied to the instances of the build it returns what they already state.
   `dommaschk_nested_current_eq_zero` weakens the allowance of `dommaschk_nested_C1` from `0` to
   `1` with `CurrentFreeTransform.mono` and recovers `0` by the corollary: a staged fixture in
   the sense of `Sanity/ContractLoopCurrentFixture` (audit AV-M2), nothing more.
3. **It is Stokes' theorem, not a property of a stellarator.** The poloidal loop bounds a planar
   disc through which the field has no current. For such a field the current clause of C1
   carries no information; all the content of C1 is in the torus and transform clauses, which
   are proved elsewhere (the KAM certificates) and are hypotheses here (`hC`, `hT`, or the
   structures `ExactTorusC`, `ExactTorusA`).
4. **Idealised field.** The meridian half-space hypothesis holds because the Dommaschk candidate
   is singular only on the `z`-axis. For a closed filament field one can check whether the
   source avoids the chosen meridian half-space, as in `Sanity/MeridianCoil`.

What is not proved: nothing about loops that are not poloidal loops of constant toroidal angle,
nothing about the quasi-symmetry statements of `DommaschkKamQ16` (not imported), and no
statement for a bounded convex region around the cross-sections of tori C and A (the half-space
suffices for this field; a ball would need explicit bounds on the cross-sections).
-/

@[expose] public section

namespace PlasmaLean.Design.DommaschkKamLoopCurrent

open PlasmaLean PlasmaLean.Vacuum PlasmaLean.Forms PlasmaLean.Fields PlasmaLean.Contract
open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton
open PlasmaLean.Design.DommaschkKamC (RofC ExactTorusC surfaceC)
open PlasmaLean.Design.DommaschkKamA (ExactTorusA surfaceA)
open TauCeti TopologicalSpace Topology
open scoped RealInnerProductSpace Manifold

/-! ## The off-axis region and the meridian half-spaces -/

/-- Every meridian half-space lies in the vacuum region of the Dommaschk fields, the complement
of the `z`-axis. -/
theorem meridianHalfSpace_subset_domain (φ₀ : ℝ) :
    (meridianHalfSpace φ₀ : Set Space) ⊆ CylAlgebra.domain :=
  fun _ hx => r2_pos_of_mem_meridianHalfSpace hx

/-- The Dommaschk candidate is a vacuum field on every meridian half-space, a convex region. -/
theorem candidate_vacuum_meridian (φ₀ : ℝ) :
    VacuumField (meridianHalfSpace φ₀ : Set Space)
      (DommaschkQA2R.field DommaschkQA2R.candidate) :=
  DommaschkQA2R.candidate_vacuum.restrict_meridianHalfSpace (meridianHalfSpace_subset_domain φ₀)

/-! ## Clause C1: any family, any allowance -/

section C1

variable {μ₀ Imax ιmin : ℝ} {S : Set SurfaceData}

/-- **Clause C1 for the Dommaschk candidate: zero current on every surface.** For every family
`S` and all `I_max`, `ι_min` such that the clause holds (`hC`, a hypothesis), each surface has
zero net current. This is `CurrentFreeTransform.current_eq_zero_of_meridianHalfSpace`: Stokes'
theorem on the planar poloidal cross-section. The same value follows from
`DommaschkQA2R.candidate_loopCurrent_eq_zero` (elementary route); this is a second proof. -/
theorem candidate_current_eq_zero
    (hC : CurrentFreeTransform μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate) S Imax ιmin)
    {s : SurfaceData} (hs : s ∈ S) :
    s.current μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate) = 0 :=
  hC.current_eq_zero_of_meridianHalfSpace DommaschkQA2R.candidate_vacuum hs
    (meridianHalfSpace_subset_domain s.φ₀)

/-- **Clause C1 for the Dommaschk candidate: zero poloidal circulation on every surface**, for
any allowance `I_max`. The clause is assumed. Stokes on the planar cross-section; a second proof
of the value given by `DommaschkQA2R.field_poloidalCirculation_eq_zero`. -/
theorem candidate_circulation_eq_zero
    (hC : CurrentFreeTransform μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate) S Imax ιmin)
    {s : SurfaceData} (hs : s ∈ S) :
    poloidalCirculation (DommaschkQA2R.field DommaschkQA2R.candidate) s.R s.z s.φ₀ = 0 :=
  hC.poloidalCirculation_eq_zero_of_meridianHalfSpace DommaschkQA2R.candidate_vacuum hs
    (meridianHalfSpace_subset_domain s.φ₀)

/-- **Clause C1 for the Dommaschk candidate: the allowance may be taken to be zero.** A family
assumed to satisfy the clause with some allowance `I_max` satisfies it with `I_max = 0`. Only
the allowance changes; the tori and the bound on the rotational transform are copied from `hC`.
For this field the current clause carries no information. The instances of the build
(`dommaschk_C1_of_exact`, `dommaschkA_C1_of_exact`, `dommaschk_nested_C1`) already have
`I_max = 0`, proved from the potential of the field, so nothing is improved in practice. -/
theorem candidate_imax_zero
    (hC : CurrentFreeTransform μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate) S Imax ιmin) :
    CurrentFreeTransform μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate) S 0 ιmin :=
  hC.imax_zero_of_meridianHalfSpace DommaschkQA2R.candidate_vacuum
    fun s _ => meridianHalfSpace_subset_domain s.φ₀

end C1

/-! ## Invariant tori of the candidate -/

section Torus

variable {R z : ℝ → ℝ → ℝ} {ι : ℝ}

/-- The poloidal loop of a `FieldTorus` at `φ₀` lies in the meridian half-space of `φ₀`. -/
theorem fieldTorus_mem
    (hT : FieldTorus (DommaschkQA2R.field DommaschkQA2R.candidate) R z ι) (φ₀ : ℝ) :
    ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, poloidalLoop R z φ₀ θ ∈ meridianHalfSpace φ₀ :=
  fun θ _ => poloidalLoop_mem_meridianHalfSpace (hT.R_pos θ φ₀)

/-- **Any invariant torus of the Dommaschk candidate carries zero loop current**, whatever its
rotation number, at a toroidal angle `φ₀` where its poloidal loop is `C¹`. The torus is assumed
(`hT`). By `FieldTorus.loopCurrent_eq_zero_of_simplyConnected` in the meridian half-space. -/
theorem fieldTorus_loopCurrent
    (hT : FieldTorus (DommaschkQA2R.field DommaschkQA2R.candidate) R z ι) (μ₀ : ℝ) {φ₀ : ℝ}
    (hγ : ContDiff ℝ 1 (poloidalLoop R z φ₀)) :
    loopCurrent μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate) R z φ₀ = 0 :=
  hT.loopCurrent_eq_zero_of_simplyConnected μ₀ (candidate_vacuum_meridian φ₀)
    (fieldTorus_mem hT φ₀) hγ.contDiffOn

/-- **Period check for any invariant torus of the candidate**: the de Rham period of `B♭` on the
class of the poloidal loop in the meridian half-space is `0`, by
`FieldTorus.loopCurrent_eq_periodHom_div` (with `μ₀ = 1`). -/
theorem fieldTorus_period
    (hT : FieldTorus (DommaschkQA2R.field DommaschkQA2R.candidate) R z ι) {φ₀ : ℝ}
    (hγ : ContDiff ℝ 1 (poloidalLoop R z φ₀)) :
    periodHom (onOpens (meridianHalfSpace φ₀)
        fun y => flat (DommaschkQA2R.field DommaschkQA2R.candidate y))
      (intervalCurve (poloidalLoop R z φ₀) neg_pi_lt_pi.le (fieldTorus_mem hT φ₀) 0)
      (Additive.ofMul (.of (.mk (intervalPath neg_pi_lt_pi.le (fieldTorus_mem hT φ₀)
        hγ.contDiffOn.continuousOn (hT.poloidalLoop_closed φ₀)))))
      = 0 := by
  have h := hT.loopCurrent_eq_periodHom_div (U := meridianHalfSpace φ₀) 1
    ((candidate_vacuum_meridian φ₀).contDiffOn.of_le (by norm_num))
    (candidate_vacuum_meridian φ₀).curl_eq_zero (fieldTorus_mem hT φ₀) hγ.contDiffOn
  rw [fieldTorus_loopCurrent hT 1 hγ, div_one] at h
  exact h.symm

end Torus

/-! ## The certified tori C and A -/

/-- `ι_C = −(85 + √5)/361 ≠ 0`. -/
theorem dkIotaC_ne_zero : DommaschkKamDio.dkIotaC ≠ 0 := fun h => by
  have := DommaschkKamC.iotaC_ge
  rw [h, abs_zero] at this
  norm_num at this

/-- `ι_A = −(19 + √5)/89 ≠ 0`. -/
theorem dkIotaA_ne_zero : DommaschkKamDio.dkIotaA ≠ 0 := fun h => by
  have := DommaschkKamA.iotaA_ge
  rw [h, abs_zero] at this
  norm_num at this

section Exact

variable {u z : FA}

/-- The `R`-coordinate of a poloidal loop of an analytic torus is `C¹`. -/
theorem contDiff_R (hu : Ana u) (φ₀ : ℝ) : ContDiff ℝ 1 fun θ => RofC u θ φ₀ :=
  ((DommaschkKamC.contDiff_RofC hu).comp (contDiff_id.prodMk contDiff_const)).of_le
    (by norm_num)

/-- The `z`-coordinate of a poloidal loop of an analytic torus is `C¹`. -/
theorem contDiff_Z (hz : Ana z) (φ₀ : ℝ) : ContDiff ℝ 1 fun θ => Zof z θ φ₀ :=
  ((contDiff_Zof hz).comp (contDiff_id.prodMk contDiff_const)).of_le (by norm_num)

/-- The poloidal loops of the exact torus C are `C¹`, at every toroidal angle. -/
theorem exactTorusC_contDiff (h : ExactTorusC u z) (φ₀ : ℝ) :
    ContDiff ℝ 1 (poloidalLoop (RofC u) (Zof z) φ₀) :=
  contDiff_poloidalLoop (contDiff_R h.ana_u φ₀) (contDiff_Z h.ana_z φ₀)

/-- The poloidal loops of the exact torus A are `C¹`, at every toroidal angle. -/
theorem exactTorusA_contDiff (h : ExactTorusA u z) (φ₀ : ℝ) :
    ContDiff ℝ 1 (poloidalLoop (RofC u) (Zof z) φ₀) :=
  contDiff_poloidalLoop (contDiff_R h.ana_u φ₀) (contDiff_Z h.ana_z φ₀)

/-- **The certified torus C carries zero loop current**, for every `μ₀` and every toroidal angle
`φ₀`, by the topological corollary in the meridian half-space. Its rotation number is
`ι_C ≠ 0` (`dkIotaC_ne_zero`). A second proof: `DommaschkQA2R.candidate_loopCurrent_eq_zero`
gives the same value (`exactTorusC_routes_agree`). -/
theorem exactTorusC_loopCurrent (h : ExactTorusC u z) (μ₀ φ₀ : ℝ) :
    loopCurrent μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC u) (Zof z) φ₀ = 0 :=
  fieldTorus_loopCurrent h.fieldTorus μ₀ (exactTorusC_contDiff h φ₀)

/-- **The certified torus A carries zero loop current**, for every `μ₀` and every toroidal angle
`φ₀`, by the topological corollary in the meridian half-space. Its rotation number is
`ι_A ≠ 0` (`dkIotaA_ne_zero`). A second proof: `DommaschkQA2R.candidate_loopCurrent_eq_zero`
gives the same value (`exactTorusA_routes_agree`). -/
theorem exactTorusA_loopCurrent (h : ExactTorusA u z) (μ₀ φ₀ : ℝ) :
    loopCurrent μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC u) (Zof z) φ₀ = 0 :=
  fieldTorus_loopCurrent h.fieldTorus μ₀ (exactTorusA_contDiff h φ₀)

/-- **Period check, torus C**: the de Rham period of `B♭` on the class of the poloidal loop of
the exact torus C in the meridian half-space of `φ₀` is `0`. -/
theorem exactTorusC_period (h : ExactTorusC u z) (φ₀ : ℝ) :
    periodHom (onOpens (meridianHalfSpace φ₀)
        fun y => flat (DommaschkQA2R.field DommaschkQA2R.candidate y))
      (intervalCurve (poloidalLoop (RofC u) (Zof z) φ₀) neg_pi_lt_pi.le
        (fieldTorus_mem h.fieldTorus φ₀) 0)
      (Additive.ofMul (.of (.mk (intervalPath neg_pi_lt_pi.le (fieldTorus_mem h.fieldTorus φ₀)
        (exactTorusC_contDiff h φ₀).contDiffOn.continuousOn
        (h.fieldTorus.poloidalLoop_closed φ₀)))))
      = 0 :=
  fieldTorus_period h.fieldTorus (exactTorusC_contDiff h φ₀)

/-- **Period check, torus A**: the de Rham period of `B♭` on the class of the poloidal loop of
the exact torus A in the meridian half-space of `φ₀` is `0`. -/
theorem exactTorusA_period (h : ExactTorusA u z) (φ₀ : ℝ) :
    periodHom (onOpens (meridianHalfSpace φ₀)
        fun y => flat (DommaschkQA2R.field DommaschkQA2R.candidate y))
      (intervalCurve (poloidalLoop (RofC u) (Zof z) φ₀) neg_pi_lt_pi.le
        (fieldTorus_mem h.fieldTorus φ₀) 0)
      (Additive.ofMul (.of (.mk (intervalPath neg_pi_lt_pi.le (fieldTorus_mem h.fieldTorus φ₀)
        (exactTorusA_contDiff h φ₀).contDiffOn.continuousOn
        (h.fieldTorus.poloidalLoop_closed φ₀)))))
      = 0 :=
  fieldTorus_period h.fieldTorus (exactTorusA_contDiff h φ₀)

/-! ## The two routes agree -/

/-- **The elementary route on torus C.** `DommaschkQA2R.candidate_loopCurrent_eq_zero` (toroidal
part orthogonal to the loop, single-valued potential) applies to the poloidal loops of the exact
torus C: its hypotheses (`C¹`, `R > 0`, closure) hold. -/
theorem exactTorusC_loopCurrent_elementary (h : ExactTorusC u z) (μ₀ φ₀ : ℝ) :
    loopCurrent μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC u) (Zof z) φ₀ = 0 :=
  DommaschkQA2R.candidate_loopCurrent_eq_zero μ₀ (contDiff_R h.ana_u φ₀) (contDiff_Z h.ana_z φ₀)
    (fun θ => h.R_pos θ φ₀) (h.fieldTorus.closed φ₀).1 (h.fieldTorus.closed φ₀).2

/-- **The elementary route on torus A.** `DommaschkQA2R.candidate_loopCurrent_eq_zero` applies to
the poloidal loops of the exact torus A. -/
theorem exactTorusA_loopCurrent_elementary (h : ExactTorusA u z) (μ₀ φ₀ : ℝ) :
    loopCurrent μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC u) (Zof z) φ₀ = 0 :=
  DommaschkQA2R.candidate_loopCurrent_eq_zero μ₀ (contDiff_R h.ana_u φ₀) (contDiff_Z h.ana_z φ₀)
    (fun θ => h.R_pos θ φ₀) (h.fieldTorus.closed φ₀).1 (h.fieldTorus.closed φ₀).2

/-- **The two routes give the same number on torus C.** For the same poloidal loop of the exact
torus C, the circulation computed by the elementary route
(`DommaschkQA2R.field_poloidalCirculation_eq_zero`) equals the de Rham period of `B♭` on the
class of the loop in the meridian half-space (topological route), and both are `0`. A
consistency check: neither proof uses the other, and the statement adds no information about
the field. -/
theorem exactTorusC_routes_agree (h : ExactTorusC u z) (φ₀ : ℝ) :
    poloidalCirculation (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC u) (Zof z) φ₀
      = periodHom (onOpens (meridianHalfSpace φ₀)
          fun y => flat (DommaschkQA2R.field DommaschkQA2R.candidate y))
        (intervalCurve (poloidalLoop (RofC u) (Zof z) φ₀) neg_pi_lt_pi.le
          (fieldTorus_mem h.fieldTorus φ₀) 0)
        (Additive.ofMul (.of (.mk (intervalPath neg_pi_lt_pi.le
          (fieldTorus_mem h.fieldTorus φ₀)
          (exactTorusC_contDiff h φ₀).contDiffOn.continuousOn
          (h.fieldTorus.poloidalLoop_closed φ₀))))) ∧
    poloidalCirculation (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC u) (Zof z) φ₀
      = 0 := by
  have he := DommaschkQA2R.field_poloidalCirculation_eq_zero DommaschkQA2R.candidate
    (contDiff_R h.ana_u φ₀) (contDiff_Z h.ana_z φ₀) (fun θ => h.R_pos θ φ₀)
    (h.fieldTorus.closed φ₀).1 (h.fieldTorus.closed φ₀).2
  exact ⟨by rw [he, exactTorusC_period h φ₀], he⟩

/-- **The two routes give the same number on torus A.** As `exactTorusC_routes_agree`, for the
exact torus A. -/
theorem exactTorusA_routes_agree (h : ExactTorusA u z) (φ₀ : ℝ) :
    poloidalCirculation (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC u) (Zof z) φ₀
      = periodHom (onOpens (meridianHalfSpace φ₀)
          fun y => flat (DommaschkQA2R.field DommaschkQA2R.candidate y))
        (intervalCurve (poloidalLoop (RofC u) (Zof z) φ₀) neg_pi_lt_pi.le
          (fieldTorus_mem h.fieldTorus φ₀) 0)
        (Additive.ofMul (.of (.mk (intervalPath neg_pi_lt_pi.le
          (fieldTorus_mem h.fieldTorus φ₀)
          (exactTorusA_contDiff h φ₀).contDiffOn.continuousOn
          (h.fieldTorus.poloidalLoop_closed φ₀))))) ∧
    poloidalCirculation (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC u) (Zof z) φ₀
      = 0 := by
  have he := DommaschkQA2R.field_poloidalCirculation_eq_zero DommaschkQA2R.candidate
    (contDiff_R h.ana_u φ₀) (contDiff_Z h.ana_z φ₀) (fun θ => h.R_pos θ φ₀)
    (h.fieldTorus.closed φ₀).1 (h.fieldTorus.closed φ₀).2
  exact ⟨by rw [he, exactTorusA_period h φ₀], he⟩

end Exact

/-! ## Unconditional statements -/

/-- **The exact torus C exists** (the residual chain of `DommaschkKamCFinal`). -/
theorem exists_exactTorusC : ∃ u z : FA, ExactTorusC u z := by
  obtain ⟨u, z, hu, hz, hur, hzr, hR, hZ, hC⟩ :=
    DommaschkKamC.dk_exact_of_res
      (DommaschkKamC.Bd_weaken DommaschkKamC.dk_e0R DommaschkKamC.e0q_le_budget)
      (DommaschkKamC.Bd_weaken DommaschkKamC.dk_e0Z DommaschkKamC.e0q_le_budget)
  exact ⟨u, z, hu, hz, hur, hzr, hR, hZ, hC⟩

/-- **The fixtures exist, unconditionally**: the Dommaschk candidate has two invariant tori,
with rotational transforms `ι_C ≠ 0` and `ι_A ≠ 0` in the sense of the contract, whose loop
currents vanish for every `μ₀` and every toroidal angle. The tori come from the KAM
certificates; the vanishing is Stokes on the planar cross-section and was already known by the
elementary route. -/
theorem exists_fieldTorus_loopCurrent_eq_zero :
    ∃ RC zC RA zA : ℝ → ℝ → ℝ,
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) RC zC DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) RA zA DommaschkKamDio.dkIotaA ∧
      DommaschkKamDio.dkIotaC ≠ 0 ∧ DommaschkKamDio.dkIotaA ≠ 0 ∧
      (∀ μ₀ φ₀,
        loopCurrent μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate) RC zC φ₀ = 0) ∧
      ∀ μ₀ φ₀, loopCurrent μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate) RA zA φ₀ = 0 := by
  obtain ⟨uC, zC, hC⟩ := exists_exactTorusC
  obtain ⟨uA, zA, hA⟩ := DommaschkKamA.exists_exactTorusA
  exact ⟨_, _, _, _, hC.iotaOnTorus, hA.iotaOnTorus, dkIotaC_ne_zero, dkIotaA_ne_zero,
    exactTorusC_loopCurrent hC, exactTorusA_loopCurrent hA⟩

/-- **The nested family `{C, A}`: a satisfiability and consistency check.** For every `μ₀ > 0`
the two surfaces of `DommaschkKamNested.dommaschk_nested_C1` satisfy clause C1 with the
allowance `I_max = 1` and `ι_min = 0.2386`; the topological corollary gives zero net current on
both and the clause with `I_max = 0`.

The fixture is staged: `dommaschk_nested_C1` is already proved with `I_max = 0` from the
potential of the field; the proof here forgets that with `CurrentFreeTransform.mono` and the
corollary recovers it. What is checked is that the hypotheses of the corollary hold together
with `|ι| ≥ 0.2386 > 0` on a two-surface family, and that the two proofs of zero current agree.
It is not an improved allowance. -/
theorem dommaschk_nested_current_eq_zero {μ₀ : ℝ} (hμ : 0 < μ₀) :
    ∃ sC sA : SurfaceData,
      sC.iota = DommaschkKamDio.dkIotaC ∧ sA.iota = DommaschkKamDio.dkIotaA ∧
      CurrentFreeTransform μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate) {sC, sA} 1
        (1193 / 5000) ∧
      CurrentFreeTransform μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate) {sC, sA} 0
        (1193 / 5000) ∧
      ∀ s ∈ ({sC, sA} : Set SurfaceData),
        s.current μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate) = 0 := by
  obtain ⟨sC, sA, _, _, _, _, hιC, hιA, h0, -⟩ := DommaschkKamNested.dommaschk_nested_C1 hμ
  have h1 := h0.mono zero_le_one le_rfl (by norm_num)
  exact ⟨sC, sA, hιC, hιA, h1, candidate_imax_zero h1,
    fun s hs => candidate_current_eq_zero h1 hs⟩

end PlasmaLean.Design.DommaschkKamLoopCurrent
