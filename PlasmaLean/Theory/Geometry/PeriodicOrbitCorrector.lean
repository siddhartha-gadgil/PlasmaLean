/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Scalar averaging along a periodic flow

An action is parametrized in turns. The inverse of differentiation along a circle
on zero-mean data is a weighted orbit integral, with the additive constant fixed
by subtracting its fibre mean. The formulas use no basepoint on an orbit.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped ContDiff Interval

namespace PlasmaLean.PeriodicOrbit

/-- A globally defined normalized periodic flow. Freeness is unnecessary. -/
structure PhaseAction (M : Type*) where
  flow : ℝ → M → M
  zero : ∀ z, flow 0 z = z
  add : ∀ s t z, flow s (flow t z) = flow (s + t) z
  turn : ∀ t z, flow (t + 1) z = flow t z

namespace PhaseAction

variable {M : Type*} (A : PhaseAction M)

/-- Time average in turns, independent of the starting phase. -/
def mean (f : M → ℝ) (z : M) : ℝ := ∫ s in (0 : ℝ)..1, f (A.flow s z)

/-- A primitive of mean minus data along the normalized flow. -/
def primitive (f : M → ℝ) (z : M) : ℝ := -(∫ s in (0 : ℝ)..1, s * f (A.flow s z))

/-- The physical-time corrector, in the gauge with zero mean on each fibre. -/
def corrector (T f : M → ℝ) (z : M) : ℝ :=
  T z * (A.primitive f z - A.mean (A.primitive f) z)

/-- Rechoosing the starting point on a fibre preserves the period integral. -/
theorem mean_flow (f : M → ℝ) (t : ℝ) (z : M) : A.mean f (A.flow t z) = A.mean f z := by
  have hp : Function.Periodic (fun s ↦ f (A.flow s z)) 1 := fun s ↦ congrArg f (A.turn s z)
  simp only [mean, A.add]
  rw [intervalIntegral.integral_comp_add_right (fun s ↦ f (A.flow s z))]
  simpa [add_comm] using hp.intervalIntegral_add_eq t 0

private theorem primitive_flow_eq (f : M → ℝ) (z : M)
    (hf : Continuous fun s ↦ f (A.flow s z)) (t : ℝ) :
    A.primitive f (A.flow t z) =
      t * A.mean f z - ∫ u in t..(1 + t), u * f (A.flow u z) := by
  let F := fun s ↦ f (A.flow s z)
  have hF : Continuous F := hf
  have hshift : Continuous (fun s : ℝ ↦ F (s + t)) := hF.comp (continuous_id.add continuous_const)
  have heq : (fun s : ℝ ↦ s * F (s + t)) =
      fun s : ℝ ↦ (s + t) * F (s + t) - t * F (s + t) := by funext s; ring
  have hav : (∫ s in (0 : ℝ)..1, F (s + t)) = A.mean f z := by
    simpa [mean, F, A.add] using A.mean_flow f t z
  change -(∫ s in (0 : ℝ)..1, s * f (A.flow s (A.flow t z))) = _
  simp_rw [A.add]
  change -(∫ s in (0 : ℝ)..1, s * F (s + t)) = _
  have h1 : Continuous (fun s : ℝ ↦ (s + t) * F (s + t)) :=
    (continuous_id.add continuous_const).mul hshift
  have h2 : Continuous (fun s : ℝ ↦ t * F (s + t)) := continuous_const.mul hshift
  rw [heq, intervalIntegral.integral_sub (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, hav,
    intervalIntegral.integral_comp_add_right (fun u ↦ u * F u)]
  simp only [zero_add, F]
  ring

/-- The normalized generator applied to the primitive is the mean minus the point value. -/
theorem hasDerivAt_primitive_flow (f : M → ℝ) (z : M)
    (hf : Continuous fun s ↦ f (A.flow s z)) (t : ℝ) :
    HasDerivAt (fun s ↦ A.primitive f (A.flow s z)) (A.mean f z - f (A.flow t z)) t := by
  let F := fun u : ℝ ↦ u * f (A.flow u z)
  have hF : Continuous F := continuous_id.mul hf
  let Q := fun x : ℝ ↦ ∫ u in (0 : ℝ)..x, F u
  have hQ (x : ℝ) : HasDerivAt Q (F x) x := intervalIntegral.integral_hasDerivAt_right
    (hF.intervalIntegrable _ _) hF.aestronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt
  have hQadd : HasDerivAt (fun s : ℝ ↦ Q (1 + s)) (F (1 + t)) t := by
    simpa [Function.comp_def] using (hQ (1 + t)).comp t ((hasDerivAt_id t).const_add 1)
  have heq : (fun s ↦ A.primitive f (A.flow s z)) =
      fun s ↦ s * A.mean f z - (Q (1 + s) - Q s) := by
    funext s
    rw [A.primitive_flow_eq f z hf s]
    congr 1
    exact (intervalIntegral.integral_interval_sub_left (hF.intervalIntegrable _ _)
      (hF.intervalIntegrable _ _)).symm
  rw [heq]
  apply (((hasDerivAt_id t).mul_const (A.mean f z)).sub (hQadd.sub (hQ t))).congr_deriv
  simp only [F, add_comm (1 : ℝ) t, A.turn]
  ring

/-- The gauge-fixed physical-time corrector has mean zero on each orbit. -/
theorem mean_corrector (T f : M → ℝ) (z : M)
    (hT : ∀ s, T (A.flow s z) = T z)
    (hf : Continuous fun s ↦ f (A.flow s z)) : A.mean (A.corrector T f) z = 0 := by
  have hc : Continuous (fun s ↦ A.primitive f (A.flow s z)) :=
    continuous_iff_continuousAt.mpr fun s ↦ (A.hasDerivAt_primitive_flow f z hf s).continuousAt
  unfold mean
  simp only [corrector, hT, A.mean_flow]
  change (∫ s in (0 : ℝ)..1, T z * (A.primitive f (A.flow s z) - A.mean (A.primitive f) z)) = 0
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    (hc.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)]
  simp [mean]

/-- Along the physical flow with period `T z`, the correction differentiates to the
fibre mean minus the original drift. Only continuity of the drift along the orbit
is needed for this directional identity. -/
theorem hasDerivAt_corrector_physical (T f : M → ℝ) (z : M) (hpos : 0 < T z)
    (hT : ∀ s, T (A.flow s z) = T z) (hf : Continuous fun s ↦ f (A.flow s z)) :
    HasDerivAt (fun t ↦ A.corrector T f (A.flow (t / T z) z)) (A.mean f z - f z) 0 := by
  have hd := (A.hasDerivAt_primitive_flow f z hf (0 / T z)).comp 0
    ((hasDerivAt_id (0 : ℝ)).div_const (T z))
  simp only [zero_div, A.zero] at hd
  simp only [corrector, hT, A.mean_flow]
  apply ((hd.sub_const (A.mean (A.primitive f) z)).const_mul (T z)).congr_deriv
  field_simp [ne_of_gt hpos]

section Smooth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (B : PhaseAction E)
variable {n : ℕ∞}

/-- Smoothness of the average in a normed-space phase model. -/
theorem contDiff_mean {f : E → ℝ} (hflow : ContDiff ℝ n (fun p : E × ℝ ↦ B.flow p.2 p.1))
    (hf : ContDiff ℝ n f) : ContDiff ℝ n (B.mean f) :=
  (hf.comp hflow).parametric_intervalIntegral

/-- Smoothness in all phase-space directions of the corrected scalar, with a smooth
physical period. -/
theorem contDiff_corrector {T f : E → ℝ}
    (hflow : ContDiff ℝ n (fun p : E × ℝ ↦ B.flow p.2 p.1))
    (hT : ContDiff ℝ n T) (hf : ContDiff ℝ n f) : ContDiff ℝ n (B.corrector T f) := by
  have hraw : ContDiff ℝ n (B.primitive f) :=
    ((contDiff_snd.mul (hf.comp hflow)).parametric_intervalIntegral).neg
  exact hT.mul (hraw.sub (B.contDiff_mean hflow hraw))

/-- In a differentiable phase model the physical generator applied to the corrector is
the orbit mean minus the drift. The velocity is needed only at the initial phase. -/
theorem fderiv_corrector_generator {T f : E → ℝ} (z X₀ : E) (hpos : 0 < T z)
    (hT : ∀ s, T (B.flow s z) = T z) (hf : Continuous fun s ↦ f (B.flow s z))
    (hg : DifferentiableAt ℝ (B.corrector T f) z)
    (hX : HasDerivAt (fun t ↦ B.flow (t / T z) z) X₀ 0) :
    fderiv ℝ (B.corrector T f) z X₀ = B.mean f z - f z := by
  have hinit : B.flow (0 / T z) z = z := by simp [B.zero]
  have hg' : HasFDerivAt (B.corrector T f) (fderiv ℝ (B.corrector T f) z)
      (B.flow (0 / T z) z) := hinit.symm ▸ hg.hasFDerivAt
  have hchain : HasDerivAt (fun t ↦ B.corrector T f (B.flow (t / T z) z))
      (fderiv ℝ (B.corrector T f) z X₀) 0 :=
    HasFDerivAt.comp_hasDerivAt (l := B.corrector T f)
      (f := fun t ↦ B.flow (t / T z) z) 0 hg' hX
  exact hchain.unique (B.hasDerivAt_corrector_physical T f z hpos hT hf)

end Smooth

section Manifold
open Set Function
open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞} [IsManifold I n M]

/-- Integrating a smooth family over a fixed phase interval preserves smoothness in
the manifold variable. This chart argument also applies on an ambient extension of
a compact band with boundary. -/
theorem contMDiff_phaseIntegral {F : M × ℝ → ℝ}
    (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) n F) :
    ContMDiff I 𝓘(ℝ, ℝ) n (fun z ↦ ∫ s in (0 : ℝ)..1, F (z, s)) := by
  refine contMDiff_iff.2 ⟨intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun z s ↦ F (z, s)) hF.continuous 0 1, ?_⟩
  intro x y
  have hh := (contMDiff_iff.1 hF).2 (x, 0) y
  simp only [extChartAt_prod, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    PartialEquiv.prod_target, PartialEquiv.prod_symm, PartialEquiv.refl_source,
    preimage_univ, inter_univ] at hh ⊢
  apply ContDiffOn.parametric_intervalIntegral (isOpen_extChartAt_target x)
  exact hh.mono (Set.prod_mono_right (Set.subset_univ _))

/-- The normalized average is smooth on a boundaryless manifold, including interior
charts or an ambient extension of the flow beyond a band. -/
theorem contMDiff_mean {f : M → ℝ}
    (hflow : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I n (fun p : M × ℝ ↦ A.flow p.2 p.1))
    (hf : ContMDiff I 𝓘(ℝ, ℝ) n f) : ContMDiff I 𝓘(ℝ, ℝ) n (A.mean f) :=
  contMDiff_phaseIntegral (hf.comp hflow)

/-- The global zero-mean corrector is smooth whenever the normalized action, physical
period and scalar data are smooth. No trivialization of the circle bundle is used. -/
theorem contMDiff_corrector {T f : M → ℝ}
    (hflow : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I n (fun p : M × ℝ ↦ A.flow p.2 p.1))
    (hT : ContMDiff I 𝓘(ℝ, ℝ) n T) (hf : ContMDiff I 𝓘(ℝ, ℝ) n f) :
    ContMDiff I 𝓘(ℝ, ℝ) n (A.corrector T f) := by
  have hraw : ContMDiff I 𝓘(ℝ, ℝ) n (A.primitive f) :=
    (contMDiff_phaseIntegral (contMDiff_snd.mul (hf.comp hflow))).neg
  exact hT.mul (hraw.sub (A.contMDiff_mean hflow hraw))

end Manifold
end PhaseAction

/-! ## Lifted coordinates for an open collar -/

namespace Lifted

variable {P : Type*}

/-- Mean in the real lift of a normalized circle coordinate. -/
def mean (f : P × ℝ → ℝ) (p : P) : ℝ := ∫ s in (0 : ℝ)..1, f (p, s)

/-- A primitive on the phase lift, fixed to zero at phase zero. -/
def primitive (f : P × ℝ → ℝ) (q : P × ℝ) : ℝ :=
  q.2 * mean f q.1 - ∫ s in (0 : ℝ)..q.2, f (q.1, s)

/-- Physical-period-scaled correction with zero fibre mean in lifted coordinates. -/
def corrector (T : P → ℝ) (f : P × ℝ → ℝ) (q : P × ℝ) : ℝ :=
  T q.1 * (primitive f q - mean (primitive f) q.1)

private theorem hasDerivAt_primitive (f : P × ℝ → ℝ) (p : P)
    (hf : Continuous fun u ↦ f (p, u)) (s : ℝ) :
    HasDerivAt (fun v ↦ primitive f (p, v)) (mean f p - f (p, s)) s := by
  have hInt := intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 s)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  simpa [primitive, Pi.sub_def] using ((hasDerivAt_id s).mul_const (mean f p)).sub hInt

/-- Phase derivative of the corrector, ready for a pushed-forward vector field in a
lifted collar chart. The fibre data need only be continuous. -/
theorem hasDerivAt_corrector (T : P → ℝ) (f : P × ℝ → ℝ) (p : P)
    (hf : Continuous fun u ↦ f (p, u)) (s : ℝ) :
    HasDerivAt (fun v ↦ corrector T f (p, v)) (T p * (mean f p - f (p, s))) s :=
  ((hasDerivAt_primitive f p hf s).sub_const (mean (primitive f) p)).const_mul (T p)

/-- Periodic data produce a periodic correction on the real lift. -/
theorem periodic_corrector (T : P → ℝ) (f : P × ℝ → ℝ) (p : P)
    (hf : Continuous fun u ↦ f (p, u)) (hp : Function.Periodic (fun u ↦ f (p, u)) 1) :
    Function.Periodic (fun s ↦ corrector T f (p, s)) 1 := by
  intro s
  have hperiod : (∫ u in s..(s + 1), f (p, u)) = mean f p := by
    simpa [mean] using hp.intervalIntegral_add_eq s 0
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) 0 s) (hf.intervalIntegrable s (s + 1))
  rw [hperiod] at hsplit
  simp only [corrector, primitive]
  rw [← hsplit]
  ring

/-- The real-coordinate corrector is normalized to zero mean over a turn. -/
theorem mean_corrector (T : P → ℝ) (f : P × ℝ → ℝ) (p : P)
    (hf : Continuous fun u ↦ f (p, u)) : mean (corrector T f) p = 0 := by
  have hprim : Continuous (fun u ↦ primitive f (p, u)) :=
    continuous_iff_continuousAt.mpr fun u ↦ (hasDerivAt_primitive f p hf u).continuousAt
  unfold mean
  simp only [corrector, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub (hprim.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _)]
  simp [mean]

/-- A periodic correction preserves the phase mean of a continuous residual. It is enough
that the correcting function returns to its starting value after a single turn. -/
theorem integral_residual_eq_mean (f : P × ℝ → ℝ) (p : P) {T : ℝ} (hT : T ≠ 0)
    (hf : Continuous fun s ↦ f (p, s)) {g r : ℝ → ℝ} (hr : Continuous r) (hg : g 1 = g 0)
    (hd : ∀ s, HasDerivAt g (T * (r s - f (p, s))) s) : ∫ s in (0 : ℝ)..1, r s = mean f p := by
  have hc : Continuous (fun s ↦ T * (r s - f (p, s))) := continuous_const.mul (hr.sub hf)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hd s)
    (hc.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    (hr.intervalIntegrable _ _) (hf.intervalIntegrable _ _), hg, sub_self] at hi
  exact sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left hT)

/-- The least achievable uniform absolute residual of any periodic scalar correction is
the absolute fibre mean. The lower bound is attained by the zero-mean corrector. -/
theorem exists_periodic_residual_bound_iff (f : P × ℝ → ℝ) (p : P) {T δ : ℝ} (hT : T ≠ 0)
    (hf : Continuous fun s ↦ f (p, s)) (hp : Function.Periodic (fun s ↦ f (p, s)) 1) :
    (∃ g r : ℝ → ℝ, Function.Periodic g 1 ∧ Continuous r ∧
      (∀ s, HasDerivAt g (T * (r s - f (p, s))) s) ∧ (∀ s, |r s| ≤ δ)) ↔ |mean f p| ≤ δ := by
  constructor
  · rintro ⟨g, r, hg, hr, hd, hδ⟩
    have hclose : g 1 = g 0 := by simpa using hg 0
    rw [← integral_residual_eq_mean f p hT hf hr hclose hd]
    simpa [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_of_norm_le_const
      (f := r) (a := 0) (b := 1) (fun s _ ↦ (Real.norm_eq_abs _).trans_le (hδ s))
  · intro hδ
    exact ⟨fun s ↦ corrector (fun _ ↦ T) f (p, s), fun _ ↦ mean f p,
      periodic_corrector _ _ _ hf hp, continuous_const, hasDerivAt_corrector _ _ _ hf, fun _ ↦ hδ⟩

/-- A nonzero constant drift cannot be cancelled around even one phase circle. -/
theorem no_periodic_primitive_const {c : ℝ} (hc : c ≠ 0) :
    ¬ ∃ g : ℝ → ℝ, Function.Periodic g 1 ∧ ∀ s, HasDerivAt g c s := by
  rintro ⟨g, hg, hd⟩
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hd s)
    (continuous_const.intervalIntegrable (μ := volume) 0 1)
  have hclose : g 1 = g 0 := by simpa using hg 0
  exact hc (by simpa [hclose] using hi)

/-- The constant drift is exactly the remaining mean for a nonconstant sinusoidal
mode, including the zero-drift and nonzero-drift cases. -/
theorem mean_constant_add_cosine (a b : ℝ) (p : P) :
    mean (fun q : P × ℝ ↦ a + b * (2 * Real.pi) * Real.cos (2 * Real.pi * q.2)) p = a := by
  let f : P × ℝ → ℝ := fun q ↦ a + b * (2 * Real.pi) * Real.cos (2 * Real.pi * q.2)
  have hf : Continuous fun s ↦ f (p, s) := by dsimp [f]; fun_prop
  let g : ℝ → ℝ := fun s ↦ -b * Real.sin (2 * Real.pi * s)
  have hg : g 1 = g 0 := by simp [g]
  have hd (s : ℝ) : HasDerivAt g (1 * (a - f (p, s))) s := by
    apply ((((hasDerivAt_id s).const_mul (2 * Real.pi)).sin).const_mul (-b)).congr_deriv
    dsimp [f]
    ring
  simpa [f] using (integral_residual_eq_mean f p one_ne_zero hf continuous_const hg hd).symm

section Smooth
open Set
variable [NormedAddCommGroup P] [NormedSpace ℝ P] {n : ℕ∞} {U : Set P}

/-- Smooth dependence of a phase mean on the base of an open collar. -/
theorem contDiffOn_mean {f : P × ℝ → ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ n f (U ×ˢ univ)) : ContDiffOn ℝ n (mean f) U :=
  ContDiffOn.parametric_intervalIntegral hU (hf.mono (Set.prod_mono_right (Set.subset_univ _)))

/-- Joint regularity of the lifted corrector on an open parameter set and the entire
real phase line, with no assumptions on data away from the collar. -/
theorem contDiffOn_corrector {T : P → ℝ} {f : P × ℝ → ℝ} (hU : IsOpen U)
    (hT : ContDiffOn ℝ n T U) (hf : ContDiffOn ℝ n f (U ×ˢ univ)) :
    ContDiffOn ℝ n (corrector T f) (U ×ˢ univ) := by
  let V : Set (P × ℝ) := U ×ˢ univ
  have hV : IsOpen V := hU.prod isOpen_univ
  have proj : MapsTo Prod.fst V U := fun _ h ↦ h.1
  have hrescale : ContDiff ℝ n (fun q : (P × ℝ) × ℝ ↦ (q.1.1, q.2 * q.1.2)) :=
    (contDiff_fst.comp contDiff_fst).prodMk (contDiff_snd.mul (contDiff_snd.comp contDiff_fst))
  have hInt : ContDiffOn ℝ n (fun q : P × ℝ ↦ ∫ v in (0 : ℝ)..1, f (q.1, v * q.2)) V :=
    ContDiffOn.parametric_intervalIntegral hV
      (hf.comp hrescale.contDiffOn fun _ h ↦ ⟨h.1.1, trivial⟩)
  have hInt' : ContDiffOn ℝ n (fun q : P × ℝ ↦ ∫ u in (0 : ℝ)..q.2, f (q.1, u)) V := by
    convert contDiffOn_snd.mul hInt using 1
    funext q
    simpa [smul_eq_mul] using
      (intervalIntegral.smul_integral_comp_mul_right (fun u ↦ f (q.1, u))
        (a := 0) (b := 1) q.2).symm
  have hraw : ContDiffOn ℝ n (primitive f) V :=
    (contDiffOn_snd.mul ((contDiffOn_mean hU hf).comp contDiffOn_fst proj)).sub hInt'
  exact (hT.comp contDiffOn_fst proj).mul
    (hraw.sub ((contDiffOn_mean hU hraw).comp contDiffOn_fst proj))

/-- The Fréchet derivative on a lifted collar, evaluated on the unit phase tangent. -/
theorem fderiv_corrector_phase {T : P → ℝ} {f : P × ℝ → ℝ} {p : P} (s : ℝ)
    (hU : IsOpen U) (hp : p ∈ U) (hT : ContDiffOn ℝ 1 T U)
    (hf : ContDiffOn ℝ 1 f (U ×ˢ univ)) :
    fderiv ℝ (corrector T f) (p, s) (0, 1) = T p * (mean f p - f (p, s)) := by
  have hV : IsOpen (U ×ˢ (univ : Set ℝ)) := hU.prod isOpen_univ
  have hg := ((contDiffOn_corrector hU hT hf).contDiffAt
    (hV.mem_nhds (x := (p, s)) ⟨hp, trivial⟩)).differentiableAt one_ne_zero
  have hcurve : HasDerivAt (fun v ↦ (p, v)) (0, 1) s :=
    (hasDerivAt_const s p).prodMk (hasDerivAt_id s)
  have hchain := HasFDerivAt.comp_hasDerivAt (l := corrector T f) (f := fun v ↦ (p, v)) s
    hg.hasFDerivAt hcurve
  have hc : Continuous (fun v ↦ f (p, v)) := continuous_iff_continuousAt.mpr fun v ↦
    (hf.contDiffAt (hV.mem_nhds (x := (p, v)) ⟨hp, trivial⟩)).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt
  exact hchain.unique (hasDerivAt_corrector T f p hc s)

end Smooth
end Lifted
end PlasmaLean.PeriodicOrbit
