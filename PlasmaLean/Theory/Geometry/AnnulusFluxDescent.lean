/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Geometry.AnnulusFibreFlux
public import PlasmaLean.Theory.Geometry.PeriodicOrbitCorrector

/-!
# Descent of annular flux under changes of fibre phase

A normalized phase on a family of oriented periodic orbits is determined up to a
rotation depending on the base point. The horizontal velocity and volume density
transform by composition with this rotation. The vertical velocity may acquire a
derivative of the phase change. Its only role here is in the local continuity equation.

On an open cover of the angular covering strip, local invariant-volume equations
produce closed flux forms. Integration over a complete phase turn identifies these
forms on overlaps and across the angular deck translation. All conclusions on the
annulus, including the normalized invariant and the winding obstruction, therefore
allow a different choice of phase origin on every patch. The same rotation identifies
the zero-mean physical correctors when the local periods agree.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.AnnulusFluxDescent

open Set Filter MeasureTheory AnnulusFibreFlux AnnulusStream
open scoped ContDiff Topology Interval

private theorem integral_phase_shift {f : ℝ → ℝ} (hp : Function.Periodic f 1) (δ : ℝ) :
    (∫ s in (0 : ℝ)..1, f (s + δ)) = ∫ s in (0 : ℝ)..1, f s := by
  rw [intervalIntegral.integral_comp_add_right f δ]
  simpa only [zero_add, add_comm 1 δ] using hp.intervalIntegral_add_eq δ 0

/-- A full normalized-time integral is independent of the origin of phase. -/
theorem fibreMean_eq_of_shift {f g : Field} {p q : Base} {δ : ℝ}
    (hper : Function.Periodic (fun s => f (p, s)) 1)
    (h : ∀ s, g (q, s) = f (p, s + δ)) : fibreMean g q = fibreMean f p := by
  unfold fibreMean
  simp_rw [h]
  exact integral_phase_shift hper δ

open PeriodicOrbit.Lifted

/-- The zero-mean physical-time corrector transforms by the same rotation as its
input, including when the two parameter spaces differ. The equality holds for
each base point and hence allows the rotation to vary over the base. -/
theorem corrector_eq_of_phase_shift {P Q : Type*} {T : P → ℝ} {S : Q → ℝ}
    {f : P × ℝ → ℝ} {g : Q × ℝ → ℝ} {p : P} {q : Q} {δ : ℝ}
    (hc : Continuous fun s => f (p, s)) (hp : Function.Periodic (fun s => f (p, s)) 1)
    (hT : S q = T p) (h : ∀ s, g (q, s) = f (p, s + δ)) (s : ℝ) :
    corrector S g (q, s) = corrector T f (p, s + δ) := by
  have hg : Continuous fun s => g (q, s) := by
    simp_rw [h]
    exact hc.comp (continuous_id.add continuous_const)
  have hm : mean g q = mean f p := by
    unfold mean
    simp_rw [h]
    exact integral_phase_shift hp δ
  let d (s : ℝ) := corrector S g (q, s) - corrector T f (p, s + δ)
  have hd (t : ℝ) : HasDerivAt d 0 t := by
    have ha := hasDerivAt_corrector S g q hg t
    have hb := (hasDerivAt_corrector T f p hc (t + δ)).comp_add_const t δ
    simpa only [d, Pi.sub_def, hT, hm, h, sub_self] using ha.sub hb
  have hconst (t : ℝ) : d t = d s := is_const_of_deriv_eq_zero
    (fun v => (hd v).differentiableAt) (fun v => (hd v).deriv) t s
  have ha : Continuous (fun t => corrector S g (q, t)) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_corrector S g q hg t).continuousAt
  have hb : Continuous (fun t => corrector T f (p, t + δ)) :=
    continuous_iff_continuousAt.mpr fun t =>
      ((hasDerivAt_corrector T f p hc (t + δ)).comp_add_const t δ).continuousAt
  have hz : (∫ t in (0 : ℝ)..1, d t) = 0 := by
    unfold d
    rw [intervalIntegral.integral_sub (ha.intervalIntegrable _ _) (hb.intervalIntegrable _ _),
      integral_phase_shift (periodic_corrector T f p hc hp) δ]
    exact sub_eq_zero.mpr ((mean_corrector S g q hg).trans (mean_corrector T f p hc).symm)
  simp only [hconst, intervalIntegral.integral_const, sub_zero, one_smul] at hz
  exact sub_eq_zero.mp hz

/-- Volume density, physical perturbation and leading period in a local phase chart.
The period depends on the base alone. Smoothness and invariance are local. -/
structure VolumePatch where
  domain : Set Base
  isOpen : IsOpen domain
  density : Field
  Y : Base × ℝ → Base × ℝ
  T : Base → ℝ
  density_pos : ∀ p ∈ domain, ∀ s, 0 < density (p, s)
  period_pos : ∀ p ∈ domain, 0 < T p
  density_smooth : ContDiffOn ℝ ∞ density (domain ×ˢ univ)
  Y_smooth : ContDiffOn ℝ ∞ Y (domain ×ˢ univ)
  Y_phase : ∀ p ∈ domain, Function.Periodic (fun s => Y (p, s)) 1
  leading_preserves : ∀ p ∈ domain, ∀ s, HasDerivAt (fun t => density (p, t) / T p) 0 s
  perturbation_preserves : ∀ p ∈ domain, ∀ s,
    HasDerivAt (fun t => density (p, t) * (Y (p, t)).2)
      (-(fderiv ℝ (fun x => density (x, s) * (Y (x, s)).1.1) p (1, 0) +
         fderiv ℝ (fun x => density (x, s) * (Y (x, s)).1.2) p (0, 1))) s

namespace VolumePatch

variable (C : VolumePatch)

/-- Local physical-time average of the projected perturbation. -/
def meanField (p : Base) : Base :=
  (fibreMean (fun z => (C.Y z).1.1) p, fibreMean (fun z => (C.Y z).1.2) p)

/-- Local volume flux as a one-form on the base. -/
def form := baseForm (fun z => C.density z * (C.Y z).1.1) (fun z => C.density z * (C.Y z).1.2)

theorem density_fibre {p : Base} (hp : p ∈ C.domain) (s : ℝ) :
    C.density (p, s) = C.density (p, 0) :=
  density_eq_of_invariant C.density C.T p (C.period_pos _ hp) (C.leading_preserves _ hp) s

theorem smooth_form : ContDiffOn ℝ ∞ C.form C.domain :=
  smooth_baseForm C.isOpen (C.density_smooth.mul C.Y_smooth.fst.fst)
    (C.density_smooth.mul C.Y_smooth.fst.snd)

theorem closed_form {p : Base} (hp : p ∈ C.domain) (v w : Base) :
    fderiv ℝ C.form p v w = fderiv ℝ C.form p w v := by
  apply baseForm_closed (c := fun z => C.density z * (C.Y z).2) C.isOpen
    (C.density_smooth.mul C.Y_smooth.fst.fst) (C.density_smooth.mul C.Y_smooth.fst.snd) hp
  · rw [C.density_fibre hp 1, show C.Y (p, 1) = C.Y (p, 0) by simpa using C.Y_phase p hp 0]
  · exact C.perturbation_preserves p hp

theorem form_apply {p : Base} (hp : p ∈ C.domain) (v : Base) :
    C.form p v = C.density (p, 0) * ((C.meanField p).1 * v.2 - (C.meanField p).2 * v.1) := by
  unfold form
  rw [baseForm_apply]
  simp only [fibreMean, meanField, C.density_fibre hp, intervalIntegral.integral_const_mul]
  ring

/-- Instantaneous drift of a base label in a local phase chart. -/
def labelDrift (ψ : Base → ℝ) (z : Base × ℝ) := fderiv ℝ ψ z.1 (C.Y z).1

/-- Along a single fibre the projected velocity is continuous. -/
theorem continuous_velocity {p : Base} (hp : p ∈ C.domain) :
    Continuous fun s : ℝ => (C.Y (p, s)).1 :=
  C.Y_smooth.fst.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
    (fun s => ⟨hp, mem_univ s⟩)

/-- Averaging a label drift equals its differential applied to the mean field. -/
theorem mean_labelDrift (ψ : Base → ℝ) {p : Base} (hp : p ∈ C.domain) :
    mean (C.labelDrift ψ) p = fderiv ℝ ψ p (C.meanField p) := by
  have hInt := (C.continuous_velocity hp).intervalIntegrable (μ := volume) 0 1
  have hv : (∫ s in (0 : ℝ)..1, (C.Y (p, s)).1) = C.meanField p := by
    apply Prod.ext
    · exact ((ContinuousLinearMap.fst ℝ ℝ ℝ).intervalIntegral_comp_comm hInt).symm
    · exact ((ContinuousLinearMap.snd ℝ ℝ ℝ).intervalIntegral_comp_comm hInt).symm
  exact ((fderiv ℝ ψ p).intervalIntegral_comp_comm hInt).trans (congrArg (fderiv ℝ ψ p) hv)

/-- If the label is a first integral of the mean field, its local corrector cancels the
entire instantaneous first-order drift at every phase. -/
theorem corrector_labelDrift_deriv (ψ : Base → ℝ) {p : Base} (hp : p ∈ C.domain)
    (hψ : fderiv ℝ ψ p (C.meanField p) = 0) (s : ℝ) :
    HasDerivAt (fun u => corrector C.T (C.labelDrift ψ) (p, u))
      (-(C.T p * C.labelDrift ψ (p, s))) s := by
  have hc := (fderiv ℝ ψ p).continuous.comp (C.continuous_velocity hp)
  simpa only [C.mean_labelDrift ψ hp, hψ, zero_sub, mul_neg] using
    hasDerivAt_corrector C.T (C.labelDrift ψ) p hc s

/-- A change of normalized phase from patch C at p to patch D at q. Only the density
and the projected perturbation are involved, so the vertical shear induced by a
base-dependent rotation is unrestricted. The points may differ by an angular deck turn. -/
def PhaseMatch (p : Base) (D : VolumePatch) (q : Base) : Prop :=
  ∃ δ : ℝ, ∀ s, D.density (q, s) = C.density (p, s + δ) ∧ (D.Y (q, s)).1 = (C.Y (p, s + δ)).1

variable {C} {D : VolumePatch} {p q : Base}

/-- Means in two phase coordinates agree after a rotation of the fibre. -/
theorem PhaseMatch.mean_eq (h : C.PhaseMatch p D q) (hp : p ∈ C.domain) :
    D.meanField q = C.meanField p := by
  obtain ⟨δ, hδ⟩ := h
  apply Prod.ext
  · apply fibreMean_eq_of_shift (p := p) (q := q) (δ := δ)
      (f := fun z => (C.Y z).1.1) (g := fun z => (D.Y z).1.1)
    · exact fun s => congrArg (fun z : Base × ℝ => z.1.1) (C.Y_phase p hp s)
    · exact fun s => congrArg Prod.fst (hδ s).2
  · apply fibreMean_eq_of_shift (p := p) (q := q) (δ := δ)
      (f := fun z => (C.Y z).1.2) (g := fun z => (D.Y z).1.2)
    · exact fun s => congrArg (fun z : Base × ℝ => z.1.2) (C.Y_phase p hp s)
    · exact fun s => congrArg Prod.snd (hδ s).2

theorem PhaseMatch.density_eq (h : C.PhaseMatch p D q) (hp : p ∈ C.domain) :
    D.density (q, 0) = C.density (p, 0) := by
  obtain ⟨δ, hδ⟩ := h
  exact (hδ 0).1.trans (C.density_fibre hp _)

/-- The flux covector is independent of the local choice of phase origin. -/
theorem PhaseMatch.form_eq (h : C.PhaseMatch p D q) (hp : p ∈ C.domain) (hq : q ∈ D.domain) :
    D.form q = C.form p := by
  apply ContinuousLinearMap.ext
  intro v
  rw [D.form_apply hq, C.form_apply hp, h.mean_eq hp, h.density_eq hp]

/-- Matching projected velocities, equal physical periods and matching label differentials
produce the same corrected label term in rotated coordinates. -/
theorem PhaseMatch.corrector_labelDrift_eq (h : C.PhaseMatch p D q) (hp : p ∈ C.domain)
    {ψ φ : Base → ℝ} (hψ : fderiv ℝ φ q = fderiv ℝ ψ p) (hT : D.T q = C.T p) :
    ∃ δ : ℝ, (∀ s, (D.Y (q, s)).1 = (C.Y (p, s + δ)).1) ∧
      ∀ s, corrector D.T (D.labelDrift φ) (q, s) =
        corrector C.T (C.labelDrift ψ) (p, s + δ) := by
  obtain ⟨δ, hδ⟩ := h
  refine ⟨δ, fun s => (hδ s).2, ?_⟩
  apply corrector_eq_of_phase_shift (f := C.labelDrift ψ) (g := D.labelDrift φ)
    (p := p) (q := q) (δ := δ) ((fderiv ℝ ψ p).continuous.comp (C.continuous_velocity hp))
  · exact fun s => congrArg (fun y : Base × ℝ => fderiv ℝ ψ p y.1) (C.Y_phase p hp s)
  · exact hT
  · intro s
    simp only [labelDrift, hψ, (hδ s).2]

end VolumePatch

/-- An atlas on the angular cover with compatible normalized fibre phases.
Chart domains may be bounded in angle. The transition over one deck turn may
have its own phase shift. -/
structure VolumeAtlas (ι : Type*) (lo hi : ℝ) where
  patch : ι → VolumePatch
  cover : ∀ p ∈ collar lo hi, ∃ i, p ∈ (patch i).domain
  overlap : ∀ i j p, p ∈ (patch i).domain → p ∈ (patch j).domain →
    (patch i).PhaseMatch p (patch j) p
  deck : ∀ i j p, p ∈ collar lo hi → p ∈ (patch i).domain →
    p + (1, 0) ∈ (patch j).domain → (patch i).PhaseMatch p (patch j) (p + (1, 0))

namespace VolumeAtlas

variable {ι : Type*} {lo hi : ℝ} (A : VolumeAtlas ι lo hi)

/-- Choose a local value on the cover and extend by zero off the collar. -/
def select {E : Type*} [Zero E] (localValue : ι → Base → E) (p : Base) : E := by
  classical
  exact if h : p ∈ collar lo hi then localValue (A.cover p h).choose p else 0

private theorem select_eq {E : Type*} [Zero E] {f : ι → Base → E}
    (compat : ∀ i j p, p ∈ (A.patch i).domain → p ∈ (A.patch j).domain → f j p = f i p)
    {p : Base} (hp : p ∈ collar lo hi) {i : ι} (hi : p ∈ (A.patch i).domain) :
    A.select f p = f i p := by
  classical
  simp only [select, dite_eq_left hp]
  exact compat i _ p hi (A.cover p hp).choose_spec

/-- The projected time average obtained using a phase chart at each base point. -/
def meanField := A.select fun i => (A.patch i).meanField

theorem meanField_eq {p : Base} (hp : p ∈ collar lo hi) {i : ι} (hi : p ∈ (A.patch i).domain) :
    A.meanField p = (A.patch i).meanField p :=
  A.select_eq (fun i j p hi hj => (A.overlap i j p hi hj).mean_eq hi) hp hi

/-- The pointwise glued local flux forms. -/
def fluxForm := A.select fun i => (A.patch i).form

private theorem fluxForm_eq {p : Base} (hp : p ∈ collar lo hi) {i : ι}
    (hi : p ∈ (A.patch i).domain) : A.fluxForm p = (A.patch i).form p :=
  A.select_eq (fun i j p hi hj => (A.overlap i j p hi hj).form_eq hi hj) hp hi

/-- Smoothness of the time average across changes of local fibre coordinates. -/
theorem smooth_meanField : ContDiffOn ℝ ∞ A.meanField (collar lo hi) := by
  intro p hp
  obtain ⟨i, hi⟩ := A.cover p hp
  let C := A.patch i
  have hs : ContDiffOn ℝ ∞ C.meanField C.domain :=
    (contDiffOn_fibreMean C.isOpen C.Y_smooth.fst.fst).prodMk
      (contDiffOn_fibreMean C.isOpen C.Y_smooth.fst.snd)
  have hsp := hs.contDiffAt (C.isOpen.mem_nhds hi)
  apply ContDiffAt.contDiffWithinAt (hsp.congr_of_eventuallyEq ?_)
  filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds hp,
    (A.patch i).isOpen.mem_nhds hi] with q hq hqi
  exact A.meanField_eq hq hqi

/-- The projected mean descends from the angular cover to the annulus. -/
theorem meanField_deck {p : Base} (hp : p ∈ collar lo hi) :
    A.meanField (p + (1, 0)) = A.meanField p := by
  have hq : p + (1, 0) ∈ collar lo hi := ⟨trivial, by simpa using hp.2⟩
  obtain ⟨i, hi⟩ := A.cover p hp
  obtain ⟨j, hj⟩ := A.cover _ hq
  rw [A.meanField_eq hp hi, A.meanField_eq hq hj]
  exact (A.deck i j p hp hi hj).mean_eq hi

private theorem fluxForm_eventuallyEq {p : Base} (hp : p ∈ collar lo hi) {i : ι}
    (hi : p ∈ (A.patch i).domain) : A.fluxForm =ᶠ[𝓝 p] (A.patch i).form := by
  filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds hp,
    (A.patch i).isOpen.mem_nhds hi] with q hq hqi
  exact A.fluxForm_eq hq hqi

/-- The closed periodic form assembled from arbitrary local phase charts. -/
def closedFlux : ClosedFlux lo hi where
  form := A.fluxForm
  smoothOn := by
    intro p hp
    obtain ⟨i, hi⟩ := A.cover p hp
    have hs := (A.patch i).smooth_form.contDiffAt ((A.patch i).isOpen.mem_nhds hi)
    exact (hs.congr_of_eventuallyEq (A.fluxForm_eventuallyEq hp hi)).contDiffWithinAt
  closed := by
    intro p hp v w
    obtain ⟨i, hi⟩ := A.cover p hp
    rw [(A.fluxForm_eventuallyEq hp hi).fderiv_eq]
    exact (A.patch i).closed_form hi v w
  periodic := by
    intro p hp
    have hq : p + (1, 0) ∈ collar lo hi := ⟨trivial, by simpa using hp.2⟩
    obtain ⟨i, hi⟩ := A.cover p hp
    obtain ⟨j, hj⟩ := A.cover _ hq
    rw [A.fluxForm_eq hp hi, A.fluxForm_eq hq hj]
    exact (A.deck i j p hp hi hj).form_eq hi hj

/-- The descended covector recovers the fibre integral in every chart that contains the point. -/
theorem closedFlux_eq {p : Base} (hp : p ∈ collar lo hi) {i : ι} (hi : p ∈ (A.patch i).domain) :
    A.closedFlux.form p = (A.patch i).form p := A.fluxForm_eq hp hi

/-- Compatible atlases, possibly with different covers and choices of section, give
the same flux covector and projected mean at every point of their common collar. -/
theorem eqOn_of_phaseMatch {κ : Type*} (B : VolumeAtlas κ lo hi)
    (h : ∀ p ∈ collar lo hi, ∃ i j, p ∈ (A.patch i).domain ∧ p ∈ (B.patch j).domain ∧
      (A.patch i).PhaseMatch p (B.patch j) p) :
    EqOn B.closedFlux.form A.closedFlux.form (collar lo hi) ∧
      EqOn B.meanField A.meanField (collar lo hi) := by
  constructor
  · intro p hp
    obtain ⟨i, j, hi, hj, hij⟩ := h p hp
    rw [A.closedFlux_eq hp hi, B.closedFlux_eq hp hj]
    exact hij.form_eq hi hj
  · intro p hp
    obtain ⟨i, j, hi, hj, hij⟩ := h p hp
    rw [A.meanField_eq hp hi, B.meanField_eq hp hj]
    exact hij.mean_eq hi

/-- Evaluation using the local base density and the descended physical-time average. -/
theorem closedFlux_apply {p : Base} (hp : p ∈ collar lo hi) {i : ι}
    (hi : p ∈ (A.patch i).domain) (v : Base) :
    A.closedFlux.form p v = (A.patch i).density (p, 0) *
      ((A.meanField p).1 * v.2 - (A.meanField p).2 * v.1) := by
  rw [A.closedFlux_eq hp hi, (A.patch i).form_apply hi, A.meanField_eq hp hi]

/-- The winding-one obstruction also holds for a reparametrized integral curve of the
mean field. -/
theorem period_zero_of_winding {γ : ℝ → Base} {k : ℝ → ℝ}
    (hγ : ∀ t ∈ Icc 0 1, HasDerivAt γ (k t • A.meanField (γ t)) t)
    (hc : ∀ t ∈ Icc 0 1, γ t ∈ collar lo hi)
    (hwind : γ 1 = γ 0 + (1, 0)) {r : ℝ} (hr : r ∈ Ioo lo hi) :
    A.closedFlux.period r = 0 := by
  apply A.closedFlux.period_zero_of_winding_tangent hγ hc _ hwind hr
  intro t ht
  obtain ⟨i, hi⟩ := A.cover _ (hc t ht)
  rw [A.closedFlux_apply (hc t ht) hi]
  change (A.patch i).density (γ t, 0) * (_ * (k t * _) - _ * (k t * _)) = 0
  ring

/-- Physical flux through the torus at radius r, expressed with independently chosen
local phases at each angle. The integrand is smooth after phase integration. -/
theorem period_eq_torusFlux {r : ℝ} (hr : r ∈ Ioo lo hi) (i : ℝ → ι)
    (h : ∀ θ ∈ Icc (0 : ℝ) 1, (θ, r) ∈ (A.patch (i θ)).domain) :
    A.closedFlux.period r = ∫ θ in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1,
      -((A.patch (i θ)).density ((θ, r), s) * ((A.patch (i θ)).Y ((θ, r), s)).1.2) := by
  unfold ClosedFlux.period
  apply intervalIntegral.integral_congr
  intro θ hθ
  dsimp only
  rw [A.closedFlux_eq (p := (θ, r)) ⟨trivial, hr⟩ (h θ (by simpa using hθ))]
  simp [VolumePatch.form, baseForm_apply, fibreMean, intervalIntegral.integral_neg]

/-- A nonsingular mean field tangent to both annular boundaries admits a smooth
periodic radial label with nonvanishing differential, for an arbitrary phase atlas. -/
theorem exists_normalized_invariant (hlo : lo < 0) (hhi : 1 < hi)
    (h₀ : ∀ θ, (A.meanField (θ, 0)).2 = 0) (h₁ : ∀ θ, (A.meanField (θ, 1)).2 = 0)
    (hn : ∀ p : Base, p.2 ∈ Icc (0 : ℝ) 1 → A.meanField p ≠ 0) :
    ∃ ψ : Base → ℝ, ContDiffOn ℝ ∞ ψ (collar lo hi) ∧
      (∀ r ∈ Ioo lo hi, Function.Periodic (fun θ => ψ (θ, r)) 1) ∧
      (∀ θ, ψ (θ, 0) = 0) ∧ (∀ θ, ψ (θ, 1) = 1) ∧
      (∀ p : Base, p.2 ∈ Icc (0 : ℝ) 1 → ψ p ∈ Icc (0 : ℝ) 1 ∧ fderiv ℝ ψ p ≠ 0) ∧
      ∀ p ∈ collar lo hi, fderiv ℝ ψ p (A.meanField p) = 0 := by
  have inside {p : Base} (hp : p.2 ∈ Icc (0 : ℝ) 1) : p ∈ collar lo hi :=
    ⟨trivial, lt_of_lt_of_le hlo hp.1, lt_of_le_of_lt hp.2 hhi⟩
  have tangent (p : Base) (hp : p ∈ collar lo hi) (h : (A.meanField p).2 = 0) :
      A.closedFlux.form p (1, 0) = 0 := by
    obtain ⟨i, hi⟩ := A.cover _ hp
    simp [A.closedFlux_apply hp hi, h]
  have nonzero (p : Base) (hp : p.2 ∈ Icc (0 : ℝ) 1) : A.closedFlux.form p ≠ 0 := by
    obtain ⟨i, hi⟩ := A.cover _ (inside hp)
    intro hzero
    have hx := A.closedFlux_apply (inside hp) hi (0, 1)
    have hy := A.closedFlux_apply (inside hp) hi (1, 0)
    apply hn p hp
    apply Prod.ext
    · simpa [hzero, ((A.patch i).density_pos p hi 0).ne'] using hx
    · simpa [hzero, ((A.patch i).density_pos p hi 0).ne'] using hy
  obtain ⟨ψ, c, hc, hs, hd, hper, hb₀, hb₁, hr⟩ := A.closedFlux.exists_normalized_stream hlo hhi
    (fun θ => tangent (θ, 0) (inside (by simp)) (h₀ θ))
    (fun θ => tangent (θ, 1) (inside (by simp)) (h₁ θ)) nonzero
  refine ⟨ψ, hs, hper, hb₀, hb₁, ?_, ?_⟩
  · intro p hp
    refine ⟨hr p hp, ?_⟩
    rw [(hd p (inside hp)).fderiv]
    exact smul_ne_zero hc (nonzero p hp)
  · intro p hp
    obtain ⟨i, hi⟩ := A.cover _ hp
    rw [(hd p hp).fderiv]
    simp [A.closedFlux_apply hp hi, mul_comm]

/-- The drift of an invariant of the descended field has zero local time mean. Its
zero-mean corrector solves the physical-time homological equation in every chart. -/
theorem local_corrector_of_invariant {ψ : Base → ℝ}
    (hψ : ∀ p ∈ collar lo hi, fderiv ℝ ψ p (A.meanField p) = 0)
    {i : ι} {p : Base} (hp : p ∈ collar lo hi) (hi : p ∈ (A.patch i).domain) :
    mean ((A.patch i).labelDrift ψ) p = 0 ∧ ∀ s,
      HasDerivAt (fun u => corrector (A.patch i).T ((A.patch i).labelDrift ψ) (p, u))
        (-((A.patch i).T p * (A.patch i).labelDrift ψ (p, s))) s := by
  have hz := hψ p hp
  rw [A.meanField_eq hp hi] at hz
  exact ⟨((A.patch i).mean_labelDrift ψ hi).trans hz,
    (A.patch i).corrector_labelDrift_deriv ψ hi hz⟩

/-- At an overlap, the corrected scalar transforms by the same rotation as the
velocity in two local normalized phases with a common physical period. -/
theorem corrector_overlap (ψ : Base → ℝ) {i j : ι} {p : Base}
    (hi : p ∈ (A.patch i).domain) (hj : p ∈ (A.patch j).domain)
    (hT : (A.patch j).T p = (A.patch i).T p) :
    ∃ δ : ℝ, (∀ s, ((A.patch j).Y (p, s)).1 = ((A.patch i).Y (p, s + δ)).1) ∧
      ∀ s, corrector (A.patch j).T ((A.patch j).labelDrift ψ) (p, s) =
        corrector (A.patch i).T ((A.patch i).labelDrift ψ) (p, s + δ) :=
  (A.overlap i j p hi hj).corrector_labelDrift_eq hi rfl hT

/-- The corrector of an angular-periodic label also agrees across the angular deck
turn, allowing independent choices of chart and phase on each side. -/
theorem corrector_deck {ψ : Base → ℝ}
    (hψ : ∀ r ∈ Ioo lo hi, Function.Periodic (fun θ => ψ (θ, r)) 1)
    {i j : ι} {p : Base} (hp : p ∈ collar lo hi) (hi : p ∈ (A.patch i).domain)
    (hj : p + (1, 0) ∈ (A.patch j).domain) (hT : (A.patch j).T (p + (1, 0)) = (A.patch i).T p) :
    ∃ δ : ℝ, (∀ s, ((A.patch j).Y (p + (1, 0), s)).1 = ((A.patch i).Y (p, s + δ)).1) ∧
      ∀ s, corrector (A.patch j).T ((A.patch j).labelDrift ψ) (p + (1, 0), s) =
        corrector (A.patch i).T ((A.patch i).labelDrift ψ) (p, s + δ) := by
  have hs : (fun q : Base => ψ (q + (1, 0))) =ᶠ[𝓝 p] ψ := by
    filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds hp] with q hq
    rcases q with ⟨θ, r⟩
    change ψ (θ + 1, r + 0) = ψ (θ, r)
    simpa only [add_zero] using hψ r hq.2 θ
  have hd : fderiv ℝ ψ (p + (1, 0)) = fderiv ℝ ψ p := by
    rw [← fderiv_comp_add_right]
    exact hs.fderiv_eq
  exact (A.deck i j p hp hi hj).corrector_labelDrift_eq hi hd hT

/-- A global phase chart induces the one-patch atlas. -/
def ofVolumeChart (C : VolumeChart lo hi) : VolumeAtlas Unit lo hi where
  patch _ :=
    { domain := collar lo hi
      isOpen := isOpen_univ.prod isOpen_Ioo
      density := C.density
      Y := C.Y
      T := C.T
      density_pos := C.density_pos
      period_pos := C.period_pos
      density_smooth := C.density_smooth
      Y_smooth := C.Y_smooth
      Y_phase := C.Y_phase
      leading_preserves := C.leading_preserves
      perturbation_preserves := C.perturbation_preserves }
  cover _ hp := ⟨(), hp⟩
  overlap _ _ _ _ _ := ⟨0, fun s => by simp⟩
  deck _ _ p hp _ _ := ⟨0, fun s => by simp [C.density_turn p hp, C.Y_turn p hp]⟩

/-- Descent agrees with the original global-chart construction on its entire domain. -/
theorem ofVolumeChart_eq (C : VolumeChart lo hi) :
    EqOn (ofVolumeChart C).closedFlux.form C.closedFlux.form (collar lo hi) := by
  intro p hp
  exact (ofVolumeChart C).closedFlux_eq hp (i := ()) hp

end VolumeAtlas

end PlasmaLean.AnnulusFluxDescent
