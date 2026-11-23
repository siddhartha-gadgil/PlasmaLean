/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic
public import PlasmaLean.Theory.Geometry.AnnulusStream

/-!
# Fibre flux of an invariant volume in normalized circle-bundle coordinates

Use angular-first base coordinates `(θ, r)` and phase `s` in turns. The leading
motion has velocity `1/T(θ, r)` in phase; hence its invariant volume density is
constant on each fibre. Integrating the continuity equation for the perturbation
removes the phase derivative and yields the closed flux form on the base.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.AnnulusFibreFlux

open Set MeasureTheory Filter
open scoped ContDiff Topology Interval

/-- Coordinates on the angular cover of the base. -/
abbrev Base := ℝ × ℝ

/-- A scalar field in base and normalized phase coordinates. -/
abbrev Field := Base × ℝ → ℝ

/-- Integral over one full phase turn, equal to normalized orbit time. -/
def fibreMean (f : Field) (p : Base) : ℝ := ∫ s in (0 : ℝ)..1, f (p, s)

/-- Invariance of the volume under the vertical generator has coordinate equation
`∂s(ρ/T)=0`. Since the period depends only on the base, the density itself is constant. -/
theorem density_eq_of_invariant (density : Field) (T : Base → ℝ) (p : Base)
    (hT : 0 < T p)
    (hInv : ∀ s, HasDerivAt (fun t => density (p, t) / T p) 0 s) (s : ℝ) :
    density (p, s) = density (p, 0) := by
  have h := is_const_of_deriv_eq_zero (fun s => (hInv s).differentiableAt)
    (fun s => (hInv s).deriv) s 0
  exact (div_left_inj₀ (ne_of_gt hT)).1 h

/-- Smoothness of the fibre integral, local in the base. -/
theorem contDiffOn_fibreMean {f : Field} {u : Set Base} (hu : IsOpen u)
    (hf : ContDiffOn ℝ ∞ f (u ×ˢ univ)) : ContDiffOn ℝ ∞ (fibreMean f) u :=
  ContDiffOn.parametric_intervalIntegral hu (hf.mono (prod_mono_right (subset_univ _)))

private theorem cont_partial {f : Field} {u : Set Base} (hu : IsOpen u)
    (hf : ContDiffOn ℝ ∞ f (u ×ˢ univ)) {p : Base} (hp : p ∈ u) :
    Continuous (fun s : ℝ => fderiv ℝ (fun x : Base => f (x, s)) p) := by
  have h₁ : ContDiffOn ℝ (0+1) (Function.uncurry (fun (q : Base) (s : ℝ) => f (q, s)))
      (u ×ˢ univ) := hf.of_le (by simp)
  have hc := (h₁.fderiv_left hu (n := 0)).continuousOn
  exact hc.comp_continuous (continuous_const.prodMk continuous_id)
    (fun s => ⟨hp, mem_univ s⟩)

/-- Differentiate a fibre integral in any base direction. -/
theorem fderiv_fibreMean_apply {f : Field} {u : Set Base} (hu : IsOpen u)
    (hf : ContDiffOn ℝ ∞ f (u ×ˢ univ)) {p : Base} (hp : p ∈ u) (v : Base) :
    fderiv ℝ (fibreMean f) p v = ∫ s in (0 : ℝ)..1, fderiv ℝ (fun x => f (x, s)) p v := by
  have h := intervalIntegral.hasFDerivAt_integral_of_contDiffOn (μ := volume)
    (f := fun x s => f (x, s)) (a := (0:ℝ)) (b := 1) (hu.mem_nhds hp)
    ((hf.of_le (m := 1) (by simp)).mono (prod_mono_right (subset_univ _)))
  rw [show fderiv ℝ (fibreMean f) p = _ from h.fderiv]
  exact ContinuousLinearMap.intervalIntegral_apply
    ((cont_partial hu hf hp).intervalIntegrable _ _) v

/-- Integrating the density-weighted three-dimensional divergence leaves zero
two-dimensional divergence, because the vertical flux is periodic. -/
theorem divergence_fibreMean {a b c : Field} {u : Set Base} (hu : IsOpen u)
    (ha : ContDiffOn ℝ ∞ a (u ×ˢ univ)) (hb : ContDiffOn ℝ ∞ b (u ×ˢ univ))
    {p : Base} (hp : p ∈ u) (hperiod : c (p, 1) = c (p, 0))
    (hdiv : ∀ s : ℝ, HasDerivAt (fun t => c (p, t))
      (-(fderiv ℝ (fun x => a (x, s)) p (1, 0) + fderiv ℝ (fun x => b (x, s)) p (0, 1))) s) :
    fderiv ℝ (fibreMean a) p (1, 0) + fderiv ℝ (fibreMean b) p (0, 1) = 0 := by
  have hA := (cont_partial hu ha hp).clm_apply (continuous_const (y := ((1, 0) : Base)))
  have hB := (cont_partial hu hb hp).clm_apply (continuous_const (y := ((0, 1) : Base)))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (_ : s ∈ [[(0:ℝ), 1]]) => hdiv s) ((hA.add hB).neg.intervalIntegrable 0 1)
  rw [hperiod, sub_self, intervalIntegral.integral_neg,
    intervalIntegral.integral_add (hA.intervalIntegrable _ _) (hB.intervalIntegrable _ _)] at hi
  rw [fderiv_fibreMean_apply hu ha hp, fderiv_fibreMean_apply hu hb hp]
  linarith

/-- The reduced flux one-form; its angular coefficient is minus radial flux. -/
def baseForm (a b : Field) (p : Base) : Base →L[ℝ] ℝ :=
  fibreMean a p • ContinuousLinearMap.snd ℝ ℝ ℝ -
  fibreMean b p • ContinuousLinearMap.fst ℝ ℝ ℝ

/-- Evaluation on a base velocity, with orientation dθ ∧ dr. -/
theorem baseForm_apply (a b : Field) (p v : Base) :
    baseForm a b p v = fibreMean a p * v.2 - fibreMean b p * v.1 := by
  simp [baseForm]

/-- Smoothness of the integrated one-form on the open base chart. -/
theorem smooth_baseForm {a b : Field} {u : Set Base} (hu : IsOpen u)
    (ha : ContDiffOn ℝ ∞ a (u ×ˢ univ)) (hb : ContDiffOn ℝ ∞ b (u ×ˢ univ)) :
    ContDiffOn ℝ ∞ (baseForm a b) u :=
  ((contDiffOn_fibreMean hu ha).smul contDiffOn_const).sub
    ((contDiffOn_fibreMean hu hb).smul contDiffOn_const)

private theorem clm_basis (L : Base →L[ℝ] ℝ) (v : Base) :
    L v = v.1 * L (1, 0) + v.2 * L (0, 1) := by
  have he : v = v.1 • ((1, 0) : Base) + v.2 • ((0, 1) : Base) := by ext <;> simp
  calc L v = L (v.1 • ((1, 0) : Base) + v.2 • ((0, 1) : Base)) := congrArg L he
       _ = _ := by rw [map_add, map_smul, map_smul]; rfl

/-- The integrated perturbation flux is a closed one-form on the base. -/
theorem baseForm_closed {a b c : Field} {u : Set Base} (hu : IsOpen u)
    (ha : ContDiffOn ℝ ∞ a (u ×ˢ univ)) (hb : ContDiffOn ℝ ∞ b (u ×ˢ univ))
    {p : Base} (hp : p ∈ u) (hperiod : c (p, 1) = c (p, 0))
    (hdiv : ∀ s : ℝ, HasDerivAt (fun t => c (p, t))
      (-(fderiv ℝ (fun x => a (x, s)) p (1, 0) + fderiv ℝ (fun x => b (x, s)) p (0, 1))) s)
    (v w : Base) :
    fderiv ℝ (baseForm a b) p v w = fderiv ℝ (baseForm a b) p w v := by
  have div := divergence_fibreMean hu ha hb hp hperiod hdiv
  have hA := ((contDiffOn_fibreMean hu ha).contDiffAt (hu.mem_nhds hp)).differentiableAt (by simp)
  have hB := ((contDiffOn_fibreMean hu hb).contDiffAt (hu.mem_nhds hp)).differentiableAt (by simp)
  have hF := ((smooth_baseForm hu ha hb).contDiffAt (hu.mem_nhds hp)).differentiableAt (by simp)
  have formula (v w : Base) : fderiv ℝ (baseForm a b) p v w =
      fderiv ℝ (fibreMean a) p v * w.2 - fderiv ℝ (fibreMean b) p v * w.1 := by
    have he : (fun q => baseForm a b q w) = fun q => fibreMean a q * w.2 - fibreMean b q * w.1 :=
      funext fun q => baseForm_apply a b q w
    have h := (hA.hasFDerivAt.mul_const w.2).sub (hB.hasFDerivAt.mul_const w.1)
    have hd := h.fderiv
    change fderiv ℝ (fun q => fibreMean a q * w.2 - fibreMean b q * w.1) p = _ at hd
    rw [← he, fderiv_clm_apply hF (differentiableAt_const w)] at hd
    have hv := congrArg (fun D : Base →L[ℝ] ℝ => D v) hd
    simpa [mul_comm] using hv
  rw [formula, formula, clm_basis (fderiv ℝ (fibreMean a) p) v,
    clm_basis (fderiv ℝ (fibreMean a) p) w, clm_basis (fderiv ℝ (fibreMean b) p) v,
    clm_basis (fderiv ℝ (fibreMean b) p) w]
  linear_combination (v.1 * w.2 - v.2 * w.1) * div

open AnnulusStream

/-- Data on the lifted collar in a circle-bundle trivialization. The leading flow has
phase velocity `1/T(p)`. The two infinitesimal volume-preservation hypotheses are
the continuity equations for its density and for the physical perturbation `Y`. -/
structure VolumeChart (lo hi : ℝ) where
  density : Field
  Y : Base × ℝ → Base × ℝ
  T : Base → ℝ
  density_pos : ∀ p ∈ collar lo hi, ∀ s, 0 < density (p, s)
  period_pos : ∀ p ∈ collar lo hi, 0 < T p
  density_smooth : ContDiffOn ℝ ∞ density (collar lo hi ×ˢ univ)
  Y_smooth : ContDiffOn ℝ ∞ Y (collar lo hi ×ˢ univ)
  T_smooth : ContDiffOn ℝ ∞ T (collar lo hi)
  density_turn : ∀ p ∈ collar lo hi, ∀ s, density (p+(1, 0), s) = density (p, s)
  Y_turn : ∀ p ∈ collar lo hi, ∀ s, Y (p+(1, 0), s) = Y (p, s)
  T_turn : ∀ p ∈ collar lo hi, T (p+(1, 0)) = T p
  Y_phase : ∀ p ∈ collar lo hi, Function.Periodic (fun s => Y (p, s)) 1
  leading_preserves : ∀ p ∈ collar lo hi, ∀ s,
    HasDerivAt (fun t => density (p, t) / T p) 0 s
  perturbation_preserves : ∀ p ∈ collar lo hi, ∀ s,
    HasDerivAt (fun t => density (p, t) * (Y (p, t)).2)
      (-(fderiv ℝ (fun x => density (x, s) * (Y (x, s)).1.1) p (1, 0) +
         fderiv ℝ (fun x => density (x, s) * (Y (x, s)).1.2) p (0, 1))) s

namespace VolumeChart

variable {lo hi : ℝ} (C : VolumeChart lo hi)

/-- The radial collar is open on the covering plane. -/
theorem isOpen_collar : IsOpen (collar lo hi) := isOpen_univ.prod isOpen_Ioo

/-- Projected time average over a full orbit in normalized phase. -/
def meanField (p : Base) : Base :=
  (fibreMean (fun z => (C.Y z).1.1) p, fibreMean (fun z => (C.Y z).1.2) p)

/-- The unit-phase integral is the physical-time average along the vertical leading
orbit starting at phase zero. -/
theorem fibreMean_eq_timeAverage (f : Field) (p : Base) (hp : p ∈ collar lo hi) :
    fibreMean f p = (∫ t in (0 : ℝ)..C.T p, f (p, t / C.T p)) / C.T p := by
  have hT := (C.period_pos p hp).ne'
  rw [intervalIntegral.integral_comp_div (fun s => f (p, s)) hT]
  simp [fibreMean, hT]

/-- The two density-weighted components of the perturbation in the base. -/
def angularCurrent (z : Base × ℝ) : ℝ := C.density z * (C.Y z).1.1

/-- Density-weighted radial component; with a minus sign it gives flux in the core orientation. -/
def radialCurrent (z : Base × ℝ) : ℝ := C.density z * (C.Y z).1.2

/-- Smoothness of the angular current density. -/
theorem angular_smooth : ContDiffOn ℝ ∞ C.angularCurrent (collar lo hi ×ˢ univ) :=
  C.density_smooth.mul C.Y_smooth.fst.fst

/-- Smoothness of the radial current density. -/
theorem radial_smooth : ContDiffOn ℝ ∞ C.radialCurrent (collar lo hi ×ˢ univ) :=
  C.density_smooth.mul C.Y_smooth.fst.snd

/-- The invariant density agrees with the base density at every phase. -/
theorem density_fibre {p : Base} (hp : p ∈ collar lo hi) (s : ℝ) :
    C.density (p, s) = C.density (p, 0) :=
  density_eq_of_invariant C.density C.T p (C.period_pos _ hp) (C.leading_preserves _ hp) s

/-- The physical hypotheses produce a smooth closed angular-periodic base form. -/
def closedFlux : ClosedFlux lo hi where
  form := baseForm C.angularCurrent C.radialCurrent
  smoothOn := smooth_baseForm isOpen_collar C.angular_smooth C.radial_smooth
  closed := by
    intro p hp v w
    apply baseForm_closed (a := C.angularCurrent) (b := C.radialCurrent)
      (c := fun z => C.density z * (C.Y z).2) isOpen_collar
      C.angular_smooth C.radial_smooth hp
    · rw [C.density_fibre hp 1, show C.Y (p, 1) = C.Y (p, 0) by
        simpa using C.Y_phase p hp 0]
    · exact C.perturbation_preserves p hp
  periodic := by
    intro p hp
    simp [baseForm, fibreMean, angularCurrent, radialCurrent, C.density_turn p hp, C.Y_turn p hp]

/-- Physical-time averaging of the projected velocity commutes with contraction
by the base area form with density `ρ(p, 0)`. -/
theorem closedFlux_apply (p v : Base) (hp : p ∈ collar lo hi) :
    C.closedFlux.form p v = C.density (p, 0) *
      ((C.meanField p).1 * v.2 - (C.meanField p).2 * v.1) := by
  change baseForm C.angularCurrent C.radialCurrent p v = _
  rw [baseForm_apply]
  simp only [fibreMean, angularCurrent, radialCurrent, meanField, C.density_fibre hp,
    intervalIntegral.integral_const_mul]
  ring

/-- The core period is the flux of the original perturbation across the lifted
torus parametrized by increasing base angle and then increasing phase. -/
theorem period_eq_torusFlux (r : ℝ) :
    C.closedFlux.period r =
      ∫ θ in (0:ℝ)..1, ∫ s in (0:ℝ)..1, -(C.density ((θ, r), s) * (C.Y ((θ, r), s)).1.2) := by
  unfold ClosedFlux.period
  apply intervalIntegral.integral_congr
  intro θ _
  change baseForm C.angularCurrent C.radialCurrent (θ, r) (1, 0) = _
  simp [baseForm_apply, radialCurrent, fibreMean, intervalIntegral.integral_neg]

/-- A lifted winding-one curve with velocity proportional to the projected mean
has zero physical flux. The multiplier permits arbitrary smooth reparametrization. -/
theorem torusFlux_zero_of_winding {γ : ℝ → Base} {k : ℝ → ℝ}
    (hγ : ∀ t ∈ Icc 0 1, HasDerivAt γ (k t • C.meanField (γ t)) t)
    (hc : ∀ t ∈ Icc 0 1, γ t ∈ collar lo hi)
    (hwind : γ 1 = γ 0 + (1, 0)) {r : ℝ} (hr : r ∈ Ioo lo hi) :
    (∫ θ in (0:ℝ)..1, ∫ s in (0:ℝ)..1, -(C.density ((θ, r), s) * (C.Y ((θ, r), s)).1.2)) = 0 := by
  rw [← C.period_eq_torusFlux]
  apply C.closedFlux.period_zero_of_winding_tangent hγ hc _ hwind hr
  intro t ht
  rw [C.closedFlux_apply _ _ (hc _ ht)]
  change C.density (γ t, 0) * (_ * (k t * _) - _ * (k t * _)) = 0
  ring

/-- Full normalized radial label from shared invariant volume, nonvanishing
projected mean, and averaged tangency at both boundaries. -/
theorem exists_normalized_invariant (hlo : lo < 0) (hhi : 1 < hi)
    (h₀ : ∀ θ, (C.meanField (θ, 0)).2 = 0) (h₁ : ∀ θ, (C.meanField (θ, 1)).2 = 0)
    (hn : ∀ p : Base, p.2 ∈ Icc (0:ℝ) 1 → C.meanField p ≠ 0) :
    ∃ ψ : Base → ℝ, ContDiffOn ℝ ∞ ψ (collar lo hi) ∧
      (∀ r ∈ Ioo lo hi, Function.Periodic (fun θ => ψ (θ, r)) 1) ∧
      (∀ θ, ψ (θ, 0) = 0) ∧ (∀ θ, ψ (θ, 1) = 1) ∧
      (∀ p : Base, p.2 ∈ Icc (0:ℝ) 1 → ψ p ∈ Icc (0:ℝ) 1 ∧ fderiv ℝ ψ p ≠ 0) ∧
      ∀ p ∈ collar lo hi, fderiv ℝ ψ p (C.meanField p) = 0 := by
  have inside {p : Base} (hp : p.2 ∈ Icc (0:ℝ) 1) : p ∈ collar lo hi :=
    ⟨trivial, lt_of_lt_of_le hlo hp.1, lt_of_le_of_lt hp.2 hhi⟩
  have hb₀ (θ : ℝ) : C.closedFlux.form (θ, 0) (1, 0) = 0 := by
    rw [C.closedFlux_apply _ _ (inside (p := (θ, 0)) (by simp))]
    simp [h₀]
  have hb₁ (θ : ℝ) : C.closedFlux.form (θ, 1) (1, 0) = 0 := by
    rw [C.closedFlux_apply _ _ (inside (p := (θ, 1)) (by simp))]
    simp [h₁]
  have hnonzero (p : Base) (hp : p.2 ∈ Icc (0:ℝ) 1) : C.closedFlux.form p ≠ 0 := by
    intro hzero
    have hx := C.closedFlux_apply p (0, 1) (inside hp)
    have hy := C.closedFlux_apply p (1, 0) (inside hp)
    apply hn p hp
    apply Prod.ext
    · simpa [hzero, (C.density_pos p (inside hp) 0).ne'] using hx
    · simpa [hzero, (C.density_pos p (inside hp) 0).ne'] using hy
  obtain ⟨ψ, c, hc, hs, hd, hper, hb₀', hb₁', hr⟩ :=
    C.closedFlux.exists_normalized_stream hlo hhi hb₀ hb₁ hnonzero
  refine ⟨ψ, hs, hper, hb₀', hb₁', ?_, ?_⟩
  · intro p hp
    refine ⟨hr p hp, ?_⟩
    rw [(hd p (inside hp)).fderiv]
    exact smul_ne_zero hc (hnonzero p hp)
  · intro p hp
    rw [(hd p hp).fderiv]
    simp [C.closedFlux_apply p _ hp, mul_comm]

/-- Instantaneous radial drift of a base label under the perturbation. -/
def labelDrift (ψ : Base → ℝ) (z : Base × ℝ) : ℝ := fderiv ℝ ψ z.1 (C.Y z).1

/-- Smoothness of the physical observable which is averaged to build the corrector. -/
theorem labelDrift_smooth {ψ : Base → ℝ} (hψ : ContDiffOn ℝ ∞ ψ (collar lo hi)) :
    ContDiffOn ℝ ∞ (C.labelDrift ψ) (collar lo hi ×ˢ univ) := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ ψ) (collar lo hi) := by
    apply hψ.fderiv_of_isOpen isOpen_collar
    simp
  have hbase := hd.comp contDiffOn_fst (fun z (hz : z ∈ collar lo hi ×ˢ (univ : Set ℝ)) => hz.1)
  exact hbase.clm_apply C.Y_smooth.fst

/-- The average of the perturbation of a base label is its derivative on the mean field. -/
theorem mean_labelDrift (ψ : Base → ℝ) (p : Base) (hp : p ∈ collar lo hi) :
    fibreMean (C.labelDrift ψ) p = fderiv ℝ ψ p (C.meanField p) := by
  let L := fderiv ℝ ψ p
  have hcont : Continuous (fun s : ℝ => C.Y (p, s)) :=
    C.Y_smooth.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun s => ⟨hp, mem_univ s⟩)
  change (∫ s in (0 : ℝ)..1, L (C.Y (p, s)).1) = L (C.meanField p)
  simp_rw [clm_basis L (C.Y (p, _)).1]
  rw [clm_basis L (C.meanField p), intervalIntegral.integral_add
    (f := fun s : ℝ => (C.Y (p, s)).1.1 * L (1, 0))
    (g := fun s : ℝ => (C.Y (p, s)).1.2 * L (0, 1))
    ((hcont.fst.fst.mul (continuous_const (y := L (1, 0)))).intervalIntegrable _ _)
    ((hcont.fst.snd.mul (continuous_const (y := L (0, 1)))).intervalIntegrable _ _),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
  rfl

/-- Constant perturbations of the unit-density unit-period flow. -/
def uniformDrift (lo hi u v w : ℝ) : VolumeChart lo hi where
  density := fun _ => 1
  Y := fun _ => ((u, v), w)
  T := fun _ => 1
  density_pos := by intros; exact zero_lt_one
  period_pos := by intros; exact zero_lt_one
  density_smooth := contDiffOn_const
  Y_smooth := contDiffOn_const
  T_smooth := contDiffOn_const
  density_turn := by intros; rfl
  Y_turn := by intros; rfl
  T_turn := by intros; rfl
  Y_phase := by intros; exact fun _ => rfl
  leading_preserves := by intros; exact hasDerivAt_const _ _
  perturbation_preserves := by
    intro p _ s
    change HasDerivAt (fun _ : ℝ => 1 * w)
      (-(fderiv ℝ (fun _ : Base => 1 * u) p (1, 0) +
         fderiv ℝ (fun _ : Base => 1 * v) p (0, 1))) s
    simpa using (hasDerivAt_const s (1 * w))

/-- A uniform base perturbation survives averaging with both components intact. -/
theorem uniformDrift_mean (lo hi u v w : ℝ) (p : Base) :
    (uniformDrift lo hi u v w).meanField p = (u, v) := by
  simp [meanField, uniformDrift, fibreMean]

/-- A unit radial perturbation has signed torus flux minus one in our orientation. -/
theorem uniformDrift_period (lo hi u v w r : ℝ) :
    (uniformDrift lo hi u v w).closedFlux.period r = -v := by
  rw [period_eq_torusFlux]
  simp [uniformDrift]

/-- A unit-density shear with a nonzero, oscillating radial velocity. -/
def oscillatoryShear (lo hi : ℝ) : VolumeChart lo hi where
  density := fun _ => 1
  Y := fun z => ((1, Real.cos (2 * Real.pi * z.2)), 0)
  T := fun _ => 1
  density_pos := by intros; exact zero_lt_one
  period_pos := by intros; exact zero_lt_one
  density_smooth := contDiffOn_const
  Y_smooth := by fun_prop
  T_smooth := contDiffOn_const
  density_turn := by intros; rfl
  Y_turn := by intros; rfl
  T_turn := by intros; rfl
  Y_phase := by
    intro p hp s
    simp [mul_add, Real.cos_add_two_pi]
  leading_preserves := by intros; exact hasDerivAt_const _ _
  perturbation_preserves := by
    intro p _ s
    change HasDerivAt (fun _ : ℝ => (1 : ℝ) * 0)
      (-(fderiv ℝ (fun _ : Base => (1 : ℝ) * 1) p (1, 0) +
         fderiv ℝ (fun _ : Base => 1 * Real.cos (2 * Real.pi * s)) p (0, 1))) s
    simpa using (hasDerivAt_const s (0 : ℝ))

/-- At phase zero the shear has unit radial velocity. -/
theorem oscillatoryShear_instantaneous (lo hi : ℝ) (p : Base) :
    ((oscillatoryShear lo hi).Y (p, 0)).1.2 = 1 := by simp [oscillatoryShear]

/-- The surviving mean is tangential with unit angular velocity. -/
theorem oscillatoryShear_mean (lo hi : ℝ) (p : Base) :
    (oscillatoryShear lo hi).meanField p = (1, 0) := by
  have hc : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  simp [meanField, fibreMean, oscillatoryShear, intervalIntegral.integral_comp_mul_left, hc,
    integral_cos]

/-- The corrected radius of the shear stays exactly constant along its perturbed
trajectories. Here phase advances at unit speed and the perturbation amplitude is ε. -/
theorem oscillatoryShear_corrected_constant (ε : ℝ) (r s : ℝ → ℝ)
    (hr : ∀ t, HasDerivAt r (ε * Real.cos (2 * Real.pi * s t)) t)
    (hs : ∀ t, HasDerivAt s 1 t) (t : ℝ) :
    r t - ε * Real.sin (2 * Real.pi * s t) / (2 * Real.pi) =
      r 0 - ε * Real.sin (2 * Real.pi * s 0) / (2 * Real.pi) := by
  have hd (t : ℝ) : HasDerivAt (fun x => r x - ε * Real.sin (2 * Real.pi * s x) / (2 * Real.pi))
      0 t := by
    convert (hr t).sub ((((hs t).const_mul (2 * Real.pi)).sin.const_mul ε).div_const
      (2 * Real.pi)) using 1
    field_simp
    ring
  exact is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) t 0

end VolumeChart

end PlasmaLean.AnnulusFibreFlux
