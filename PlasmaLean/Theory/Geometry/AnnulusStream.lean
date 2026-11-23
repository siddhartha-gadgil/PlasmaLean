/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The stream function and the flux obstruction on an annulus

Use the angular cover with coordinates (angle in turns, radius). A smooth closed flux form on an
open radial collar has a primitive on the cover. Its jump under one turn is the flux through any
winding-one loop. Boundary tangency kills that period. If the form has no zeros on the compact
physical annulus, its normalized primitive separates the boundary circles.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.AnnulusStream

open Set Function Filter
open scoped ContDiff Topology Interval

/-- The angular covering plane of a smooth collar of a closed annulus. -/
abbrev collar (a b : ℝ) : Set (ℝ × ℝ) := univ ×ˢ Ioo a b

/-- A closed angular-periodic one-form on the collar. Closedness is symmetry of the derivative. -/
structure ClosedFlux (a b : ℝ) where
  form : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ)
  smoothOn : ContDiffOn ℝ ∞ form (collar a b)
  closed : ∀ p ∈ collar a b, ∀ v w, fderiv ℝ form p v w = fderiv ℝ form p w v
  periodic : ∀ p ∈ collar a b, form (p + (1, 0)) = form p

variable {a b : ℝ}

private theorem collar_open : IsOpen (collar a b) := isOpen_univ.prod isOpen_Ioo
private theorem collar_convex : Convex ℝ (collar a b) := convex_univ.prod (convex_Ioo _ _)
private theorem collar_shift {p : ℝ × ℝ} (hp : p ∈ collar a b) :
    p + (1, 0) ∈ collar a b := ⟨trivial, by simpa using hp.2⟩

/-- Flux through one turn at radius r, oriented by increasing angle. -/
def ClosedFlux.period (F : ClosedFlux a b) (r : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..1, F.form (θ, r) (1, 0)

/-- A primitive of the lifted form, with its derivative prescribed on the entire open collar. -/
theorem ClosedFlux.exists_primitive (F : ClosedFlux a b) :
    ∃ J : ℝ × ℝ → ℝ, ∀ p ∈ collar a b, HasFDerivAt J (F.form p) p :=
  collar_convex.exists_forall_hasFDerivAt_of_fderiv_symmetric collar_open
    (F.smoothOn.differentiableOn (by norm_num)) F.closed

private theorem horizontal_deriv {F : ClosedFlux a b} {J : ℝ × ℝ → ℝ}
    (hJ : ∀ p ∈ collar a b, HasFDerivAt J (F.form p) p)
    {r : ℝ} (hr : r ∈ Ioo a b) (θ : ℝ) :
    HasDerivAt (fun s => J (s, r)) (F.form (θ, r) (1, 0)) θ :=
  (hJ (θ, r) ⟨trivial, hr⟩).comp_hasDerivAt θ ((hasDerivAt_id θ).prodMk (hasDerivAt_const θ r))

/-- The increment of any primitive under the deck translation is the same flux at every radius. -/
theorem ClosedFlux.primitive_jump (F : ClosedFlux a b) {J : ℝ × ℝ → ℝ}
    (hJ : ∀ p ∈ collar a b, HasFDerivAt J (F.form p) p)
    {p : ℝ × ℝ} (hp : p ∈ collar a b) {r : ℝ} (hr : r ∈ Ioo a b) :
    J (p + (1, 0)) - J p = F.period r := by
  let D := fun p : ℝ × ℝ => J (p + (1, 0)) - J p
  have hd (p : ℝ × ℝ) (hp : p ∈ collar a b) : HasFDerivAt D (0 : ℝ × ℝ →L[ℝ] ℝ) p := by
    have h := ((hasFDerivAt_comp_add_right ((1, 0) : ℝ × ℝ)).2
      (hJ _ (collar_shift hp))).sub (hJ p hp)
    rw [F.periodic p hp, sub_self] at h
    exact h
  have heq := (collar_convex (a := a) (b := b)).is_const_of_fderivWithin_eq_zero
    (fun p hp => (hd p hp).differentiableAt.differentiableWithinAt)
    (fun p hp => (hd p hp).hasFDerivWithinAt.fderivWithin (collar_open.uniqueDiffOn p hp))
    hp (show ((0, r) : ℝ × ℝ) ∈ collar a b from ⟨trivial, hr⟩)
  have hcont : Continuous (fun s : ℝ => F.form (s, r) (1, 0)) :=
    (F.smoothOn.continuousOn.comp_continuous (by fun_prop : Continuous (fun s : ℝ => (s, r)))
      (fun s => ⟨trivial, hr⟩)).clm_apply continuous_const
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (_ : s ∈ [[(0 : ℝ), 1]]) => horizontal_deriv hJ hr s) (hcont.intervalIntegrable 0 1)
  rw [ClosedFlux.period, hi]
  simpa [D] using heq

/-- Flux through horizontal core circles is independent of radius. -/
theorem ClosedFlux.period_eq (F : ClosedFlux a b) {r s : ℝ} (hr : r ∈ Ioo a b)
    (hs : s ∈ Ioo a b) : F.period r = F.period s := by
  obtain ⟨J, hJ⟩ := F.exists_primitive
  have h0 : ((0, r) : ℝ × ℝ) ∈ collar a b := ⟨trivial, hr⟩
  exact (F.primitive_jump hJ h0 hr).symm.trans (F.primitive_jump hJ h0 hs)

/-- A winding-one curve has the core flux, independently of its shape and its starting radius.
The scalar line integrand along the lift is assumed integrable. -/
theorem ClosedFlux.integral_eq_period_of_winding (F : ClosedFlux a b)
    {γ dγ : ℝ → ℝ × ℝ} (hγ : ∀ t ∈ Icc 0 1, HasDerivAt γ (dγ t) t)
    (hc : ∀ t ∈ Icc 0 1, γ t ∈ collar a b)
    (hint : IntervalIntegrable (fun t => F.form (γ t) (dγ t)) MeasureTheory.volume 0 1)
    (hwind : γ 1 = γ 0 + (1, 0)) {r : ℝ} (hr : r ∈ Ioo a b) :
    ∫ t in (0 : ℝ)..1, F.form (γ t) (dγ t) = F.period r := by
  obtain ⟨J, hJ⟩ := F.exists_primitive
  have hd (t : ℝ) (ht : t ∈ [[(0 : ℝ), 1]]) := by
    rw [uIcc_of_le zero_le_one] at ht
    exact (hJ _ (hc t ht)).comp_hasDerivAt t (hγ t ht)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [hi, Function.comp_apply, Function.comp_apply, hwind]
  exact F.primitive_jump hJ (hc 0 (by simp)) hr

/-- A differentiable lifted curve tangent to the kernel of a closed flux form cannot wind once
when the core flux is nonzero. The endpoint condition is the winding number in turns. -/
theorem ClosedFlux.period_zero_of_winding_tangent (F : ClosedFlux a b)
    {γ dγ : ℝ → ℝ × ℝ} (hγ : ∀ t ∈ Icc 0 1, HasDerivAt γ (dγ t) t)
    (hc : ∀ t ∈ Icc 0 1, γ t ∈ collar a b)
    (htan : ∀ t ∈ Icc 0 1, F.form (γ t) (dγ t) = 0)
    (hwind : γ 1 = γ 0 + (1, 0)) {r : ℝ} (hr : r ∈ Ioo a b) : F.period r = 0 := by
  obtain ⟨J, hJ⟩ := F.exists_primitive
  have hd (t : ℝ) (ht : t ∈ Icc 0 1) : HasDerivAt (fun t => J (γ t)) 0 t := by
    have h := (hJ _ (hc t ht)).comp_hasDerivAt t (hγ t ht)
    rw [htan t ht] at h
    exact h
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (ht : t ∈ [[(0 : ℝ), 1]]) => hd t (by simpa [uIcc_of_le zero_le_one] using ht))
    (intervalIntegrable_const (a := 0) (b := 1) (c := (0 : ℝ)))
  have hj := F.primitive_jump hJ (hc 0 (by simp)) hr
  rw [← hwind] at hj
  simpa [← hj] using hi.symm

private theorem upper_of_boundary {J : ℝ × ℝ → ℝ} {dJ : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ)}
    {k : ℝ} (hd : ∀ p, p.2 ∈ Icc (0 : ℝ) 1 → HasFDerivAt J (dJ p) p)
    (hn : ∀ p, p.2 ∈ Ioo (0 : ℝ) 1 → dJ p ≠ 0)
    (hper : ∀ r ∈ Icc (0 : ℝ) 1, Periodic (fun θ : ℝ => J (θ, r)) 1)
    (hb₀ : ∀ θ, J (θ, 0) ≤ k) (hb₁ : ∀ θ, J (θ, 1) ≤ k)
    (p : ℝ × ℝ) (hp : p.2 ∈ Icc (0 : ℝ) 1) : J p ≤ k := by
  let box : Set (ℝ × ℝ) := Icc 0 1 ×ˢ Icc 0 1
  have hcompact : IsCompact box := isCompact_Icc.prod isCompact_Icc
  have hne : box.Nonempty := ⟨(0, 0), by simp [box]⟩
  have hcont : ContinuousOn J box := fun z hz => (hd z hz.2).continuousAt.continuousWithinAt
  obtain ⟨z, hz, hmax⟩ := hcompact.exists_isMaxOn hne hcont
  have hall (q : ℝ × ℝ) (hq : q.2 ∈ Icc (0 : ℝ) 1) : J q ≤ J z := by
    let θ := Int.fract q.1
    have heq := (hper q.2 hq).sub_int_mul_eq (x := q.1) ⌊q.1⌋
    have he : J (θ, q.2) = J q := by simpa only [θ, Int.fract, mul_one, Prod.mk.eta] using heq
    rw [← he]
    exact hmax ⟨⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, hq⟩
  apply (hall p hp).trans
  rcases eq_or_lt_of_le hz.2.1 with h0 | h0
  · change J (z.1, z.2) ≤ k
    rw [← h0]
    exact hb₀ z.1
  rcases eq_or_lt_of_le hz.2.2 with h1 | h1
  · change J (z.1, z.2) ≤ k
    rw [h1]
    exact hb₁ z.1
  have hloc : IsLocalMax J z := by
    filter_upwards [continuous_snd.continuousAt (Ioo_mem_nhds h0 h1)] with q hq
    exact hall q ⟨hq.1.le, hq.2.le⟩
  exact (hn z ⟨h0, h1⟩ (hloc.hasFDerivAt_eq_zero (hd z hz.2))).elim

private theorem boundary_const {F : ClosedFlux a b} {J : ℝ × ℝ → ℝ}
    (hJ : ∀ p ∈ collar a b, HasFDerivAt J (F.form p) p)
    {r : ℝ} (hr : r ∈ Ioo a b) (ht : ∀ θ, F.form (θ, r) (1, 0) = 0)
    (θ : ℝ) : J (θ, r) = J (0, r) := by
  have h (s : ℝ) : HasDerivAt (fun t : ℝ => J (t, r)) 0 s := by
    rw [← ht s]
    exact horizontal_deriv hJ hr s
  exact is_const_of_deriv_eq_zero (fun s => (h s).differentiableAt) (fun s => (h s).deriv) θ 0

/-- A nonsingular closed flux form tangent to the kernel's two boundary circles yields a smooth
radial label on the annulus (presented by its period-one lift). Its differential is a single
nonzero scalar multiple of the input form everywhere. -/
theorem ClosedFlux.exists_normalized_stream (F : ClosedFlux a b)
    (ha : a < 0) (hb : 1 < b)
    (h₀ : ∀ θ, F.form (θ, 0) (1, 0) = 0) (h₁ : ∀ θ, F.form (θ, 1) (1, 0) = 0)
    (hn : ∀ p : ℝ × ℝ, p.2 ∈ Icc (0 : ℝ) 1 → F.form p ≠ 0) :
    ∃ (ψ : ℝ × ℝ → ℝ) (c : ℝ), c ≠ 0 ∧ ContDiffOn ℝ ∞ ψ (collar a b) ∧
      (∀ p ∈ collar a b, HasFDerivAt ψ (c • F.form p) p) ∧
      (∀ r ∈ Ioo a b, Periodic (fun θ : ℝ => ψ (θ, r)) 1) ∧
      (∀ θ, ψ (θ, 0) = 0) ∧ (∀ θ, ψ (θ, 1) = 1) ∧
      ∀ p : ℝ × ℝ, p.2 ∈ Icc (0 : ℝ) 1 → ψ p ∈ Icc (0 : ℝ) 1 := by
  have incl {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) : r ∈ Ioo a b :=
    ⟨ha.trans_le hr.1, hr.2.trans_lt hb⟩
  have r₀ : (0 : ℝ) ∈ Ioo a b := incl (by simp)
  have r₁ : (1 : ℝ) ∈ Ioo a b := incl (by simp)
  obtain ⟨J, hJ⟩ := F.exists_primitive
  have j₀ := boundary_const hJ r₀ h₀
  have j₁ := boundary_const hJ r₁ h₁
  have flux₀ : F.period 0 = 0 := by simp [ClosedFlux.period, h₀]
  have jp (r : ℝ) (hr : r ∈ Ioo a b) : Periodic (fun θ : ℝ => J (θ, r)) 1 := by
    intro θ
    have h := F.primitive_jump hJ (p := (θ, r)) ⟨trivial, hr⟩ r₀
    simpa [flux₀, sub_eq_zero] using h
  have jdiff (p : ℝ × ℝ) (hp : p.2 ∈ Icc (0 : ℝ) 1) :=
    hJ p ⟨trivial, incl hp⟩
  have hjne : J (0, 1) ≠ J (0, 0) := by
    intro heq
    have hu := upper_of_boundary jdiff (fun p hp => hn p (Ioo_subset_Icc_self hp))
      (fun r hr => jp r (incl hr)) (fun θ => (j₀ θ).le) (fun θ => ((j₁ θ).trans heq).le)
    have hl := upper_of_boundary (J := fun p => -J p) (k := -J (0, 0))
      (fun p hp => (jdiff p hp).neg)
      (fun p hp => neg_ne_zero.mpr (hn p (Ioo_subset_Icc_self hp)))
      (fun r hr θ => congrArg Neg.neg (jp r (incl hr) θ))
      (fun θ => by simp [j₀ θ]) (fun θ => by simp [j₁ θ, heq])
    let m : ℝ × ℝ := (0, 1 / 2)
    have hm : m.2 ∈ Ioo (0 : ℝ) 1 := by norm_num [m, mem_Ioo]
    have hv : J m = J (0, 0) := le_antisymm (hu m (Ioo_subset_Icc_self hm))
      (neg_le_neg_iff.mp (hl m (Ioo_subset_Icc_self hm)))
    have hmax : IsLocalMax J m := by
      filter_upwards [continuous_snd.continuousAt (Ioo_mem_nhds hm.1 hm.2)] with p hp
      exact (hu p (Ioo_subset_Icc_self hp)).trans hv.ge
    exact hn m (Ioo_subset_Icc_self hm)
      (hmax.hasFDerivAt_eq_zero (jdiff m (Ioo_subset_Icc_self hm)))
  let c := (J (0, 1) - J (0, 0))⁻¹
  let ψ := fun p => c * (J p - J (0, 0))
  have hc : c ≠ 0 := inv_ne_zero (sub_ne_zero.mpr hjne)
  have hψ (p : ℝ × ℝ) (hp : p ∈ collar a b) : HasFDerivAt ψ (c • F.form p) p :=
    ((hJ p hp).sub_const _).const_mul c
  have hψper (r : ℝ) (hr : r ∈ Ioo a b) : Periodic (fun θ : ℝ => ψ (θ, r)) 1 :=
    fun θ => by simp [ψ, jp r hr θ]
  have hψ₀ (θ : ℝ) : ψ (θ, 0) = 0 := by simp [ψ, j₀ θ]
  have hψ₁ (θ : ℝ) : ψ (θ, 1) = 1 := by
    simp [ψ, c, j₁ θ, sub_ne_zero.mpr hjne]
  have hψn (p : ℝ × ℝ) (hp : p.2 ∈ Ioo (0 : ℝ) 1) : c • F.form p ≠ 0 :=
    smul_ne_zero hc (hn p (Ioo_subset_Icc_self hp))
  refine ⟨ψ, c, hc, ?_, hψ, hψper, hψ₀, hψ₁, ?_⟩
  · refine (contDiffOn_infty_iff_fderiv_of_isOpen collar_open).2
      ⟨fun p hp => (hψ p hp).differentiableAt.differentiableWithinAt, ?_⟩
    exact ((contDiffOn_const (c := c)).smul F.smoothOn).congr (fun p hp => (hψ p hp).fderiv)
  · intro p hp
    have hu := upper_of_boundary (fun q hq => hψ q ⟨trivial, incl hq⟩) hψn
      (fun r hr => hψper r (incl hr)) (fun θ => by simp [hψ₀]) (fun θ => (hψ₁ θ).le) p hp
    have hl := upper_of_boundary (J := fun p => -ψ p) (k := 0)
      (fun q hq => (hψ q ⟨trivial, incl hq⟩).neg)
      (fun q hq => neg_ne_zero.mpr (hψn q hq))
      (fun r hr θ => congrArg Neg.neg (hψper r (incl hr) θ))
      (fun θ => by simp [hψ₀]) (fun θ => by simp [hψ₁]) p hp
    exact ⟨by simpa using hl, hu⟩

/-- Constant coefficient fluxes on a collar. These include tangential and transverse uniform
drifts for the area form on the orbit space. -/
def constantFlux (a b : ℝ) (L : ℝ × ℝ →L[ℝ] ℝ) : ClosedFlux a b where
  form := fun _ => L
  smoothOn := contDiffOn_const
  closed := by simp
  periodic := by simp

/-- A constant flux measures exactly its angular coefficient. -/
@[simp] theorem constantFlux_period (a b r : ℝ) (L : ℝ × ℝ →L[ℝ] ℝ) :
    (constantFlux a b L).period r = L (1, 0) := by
  simp [ClosedFlux.period, constantFlux]

/-- For a uniform tangential drift, radius is an exact, normalized first integral. -/
theorem uniform_tangent_stream (a b : ℝ) (p : ℝ × ℝ) :
    HasFDerivAt Prod.snd ((constantFlux a b (ContinuousLinearMap.snd ℝ ℝ ℝ)).form p) p :=
  hasFDerivAt_snd

/-- Uniform transverse drift has flux one, excluding even a single winding-one trajectory
tangent to its kernel. -/
theorem uniform_transverse_no_winding {γ dγ : ℝ → ℝ × ℝ}
    (hγ : ∀ t ∈ Icc 0 1, HasDerivAt γ (dγ t) t)
    (hc : ∀ t ∈ Icc 0 1, γ t ∈ collar (-1) 2)
    (htan : ∀ t ∈ Icc 0 1, (dγ t).1 = 0) : γ 1 ≠ γ 0 + (1, 0) := by
  intro hwind
  have h := (constantFlux (-1) 2 (ContinuousLinearMap.fst ℝ ℝ ℝ)).period_zero_of_winding_tangent
    hγ hc htan hwind (r := 0) (by norm_num [mem_Ioo])
  simp at h

end PlasmaLean.AnnulusStream
