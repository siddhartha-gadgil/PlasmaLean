/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Kernel.Transport
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.DenselyOrdered

/-!
# Parabolic comparison for radial heat transport

Source: the classical first-touching (Nagumo) argument for parabolic comparison, as specified
in `notes/pde-bounds-and-verification-roadmap.md` §4 (Stage 3), applied to the (since kernel
change K2, quasilinear) radial operator of `PlasmaLean.Kernel.Transport`. All solutions are
*supplied* classical solutions; no existence theorem is claimed.

## Quasilinear diffusivity (kernel change K2)

For `N[T] = (1/V')∂ψ(V' D(ψ,T) ∂ψT) + R` the expanded operator is
`D(ψ,u) uψψ + (∂ψD(ψ,u) + ∂TD(ψ,u) uψ + D(ψ,u) V''/V') uψ + R(ψ,u)`. At a first touching point
of `u` and `S` (interior zero minimum of `u − S`) the values and slopes coincide, so
`D(ψ,u)`, `∂ψD(ψ,u)` and the quasilinear term `∂TD(ψ,u)·uψ` are *the same* for both, and
`N[u] − N[S] = D(ψ,u)(uψψ − Sψψ) ≥ 0` (`first_crossing`, `op_le_op_of_touch_interior`). At a
regular axis the Neumann condition makes both slopes `0`; at a degenerate axis `D(0,·) ≡ 0`
forces `∂TD(0,·) = 0` and only the drift `∂ψD(0,u)(uψ − Sψ) ≥ 0` remains
(`op_le_op_of_touch_axis`). Hence the strict comparison theorems hold verbatim with `D ≥ 0`
at every temperature.

What does change is the margin argument (non-strict data): it shifts the barrier by a
constant `δ`, which changes the value argument of `D`, `∂ψD`, `∂TD` as well as of `R`. The
margin theorems therefore assume `OpShiftControl` (continuity of the operator along the
profile in the value argument), which holds automatically for semilinear coefficients
(`IsSemilinear.opShiftControl`) and for quasilinear ones whenever `(ψ,T) ↦ N` along the
profile is jointly continuous (`opShiftControl_of_continuousOn`). The lower and **upper**
margin theorems `le_of_lowerMargin_shift`, `le_of_upperMargin_shift` are proved *directly*
from the kernel-level residual comparison `lt_of_residual_lt_kernel` (both axis kinds), not
through the mirror `T ↦ −T` (which nevertheless survives K2: `∂TD` flips sign,
`RadialCoefficients.neg`).

## Main results

* `first_crossing`: the pointwise Nagumo lemma. At a zero minimum of `e = T − S` in `ψ`
  (`e = 0`, `e_ψ = 0`, `e_ψψ ≥ 0`), `D ≥ 0` and a strict subsolution force `∂ₜT > ∂ₜS`.
  `first_crossing_axis` and `first_crossing_interior` derive the hypotheses `e_ψ = 0`,
  `e_ψψ ≥ 0` from minimality, using the Neumann condition at a `regular` axis.
  `op_le_op_of_touch_axis` handles a `degenerate` axis (`D(0) = 0`, `D'(0) ≥ 0`) without any
  axis condition.
* `lt_of_strictSubsolution`: strict comparison with a time-dependent strict subsolution, a
  strict edge margin and a strict initial margin, for both axis kinds. Only `D ≥ 0` (and, for
  a degenerate axis, `DegenerateAxis`) is used.
* Stationary lower barriers: `lt_of_isStrictLowerBarrier` (strict data),
  `le_of_isStrictLowerBarrier_margin` (strict subsolution with a uniform margin; edge and initial
  data only non-strict; uses only continuity of `R`), and `le_of_isLowerBarrier` (non-strict
  subsolution; needs a one-sided Lipschitz bound on `R`, via an `ε e^{λt}` perturbation).
* Mirror upper-barrier theorems (by the symmetry `T ↦ −T`, `R(ψ,v) ↦ −R(ψ,−v)`,
  `D(ψ,v) ↦ D(ψ,−v)`) and the two-sided corollaries `mem_Icc_of_barriers*`. The theorems that
  shift by constants or use the one-sided Lipschitz bound on `R` take an `IsSemilinear`
  hypothesis; their quasilinear counterparts are the `*_shift` theorems.
* Sanity: constant barriers, the degenerate case `D ≡ 0`, a formal counterexample showing that
  the sign `D ≥ 0` cannot be dropped, and a non-vacuous explicit barrier with an explicit
  decaying solution. The explicit separable solutions use `modeField` (defined here; the
  sanity module `PlasmaLean.Sanity.Transport` re-exports it as `Sanity.modeField`, and this
  theory module does not import any sanity module).

## Remarks on hypotheses

* A floor `D ≥ Dmin > 0` is **not** needed for the comparison of classical solutions: only
  `D ≥ 0` enters (see `lt_of_strictSubsolution`). This is why the kernel law was relaxed to
  `D ≥ 0` on 2026-10-20. A floor matters for existence, regularity and strong maximum
  principles, which are not formalized here.
* The non-strict barrier theorems with a margin need `R` continuous only near the barrier:
  the barrier must take values in the kernel's open source domain `Tdom`.
* The non-strict version needs more than continuity of `R`: for the ODE `T' = −√|T|`, both
  `T ≡ 0` and `T = −t²/4` start at `0`, so `S ≡ 0` (with `N[S] = 0`) is not a lower barrier.
  This is why `le_of_isLowerBarrier` assumes the one-sided Lipschitz bound
  `R(ψ,b) − R(ψ,a) ≤ K (b − a)` for `a ≤ b`. (The counterexample is recorded here as a remark
  only: it is spatially constant, so it violates the edge hypothesis of the PDE theorem.)
-/

public section

noncomputable section

namespace PlasmaLean.Transport

open Set Filter Topology

/-! ### One-variable calculus lemmas -/

/-- Right-sided second-derivative test: if `f` attains its minimum over `[a,b]` at `a`,
`f'(a) = 0` and `f'` has derivative `f''` at `a` (within `[a,b]`), then `f'' ≥ 0`. -/
theorem secondDeriv_nonneg_of_rightMin {f f' : ℝ → ℝ} {a b f'' : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (hf' : HasDerivWithinAt f' f'' (Icc a b) a)
    (hmin : ∀ x ∈ Icc a b, f a ≤ f x) (hzero : f' a = 0) : 0 ≤ f'' := by
  by_contra hneg
  push Not at hneg
  rw [hasDerivWithinAt_iff_tendsto_slope] at hf'
  have hev : ∀ᶠ x in 𝓝[Icc a b \ {a}] a, slope f' a x < 0 :=
    hf'.eventually (gt_mem_nhds hneg)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  set x := a + min (b - a) (ε / 2) with hxdef
  have hm : 0 < min (b - a) (ε / 2) := lt_min (by linarith) (by linarith)
  have hax : a < x := by linarith
  have hxb : x ≤ b := by linarith [min_le_left (b - a) (ε / 2)]
  have hxε : x - a < ε := by linarith [min_le_right (b - a) (ε / 2)]
  have hneg' : ∀ y ∈ Ioo a x, f' y < 0 := by
    intro y hy
    have hdist : dist y a < ε := by
      rw [Real.dist_eq, abs_of_pos (by linarith [hy.1])]; linarith [hy.2]
    have h := hball hdist ⟨⟨hy.1.le, by linarith [hy.2]⟩, by
      simp only [mem_singleton_iff]; exact hy.1.ne'⟩
    rw [slope_def_field, hzero, sub_zero] at h
    by_contra hy'
    push Not at hy'
    exact absurd h (not_lt.2 (div_nonneg hy' (by linarith [hy.1])))
  have hcont : ContinuousOn f (Icc a x) := fun y hy =>
    (hf y ⟨hy.1, hy.2.trans hxb⟩).continuousWithinAt.mono (Icc_subset_Icc le_rfl hxb)
  have hderiv : ∀ y ∈ Ioo a x, HasDerivAt f (f' y) y := fun y hy =>
    (hf y ⟨hy.1.le, hy.2.le.trans hxb⟩).hasDerivAt (Icc_mem_nhds hy.1 (hy.2.trans_le hxb))
  obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f f' hax hcont hderiv
  have h1 : 0 ≤ (f x - f a) / (x - a) :=
    div_nonneg (by linarith [hmin x ⟨hax.le, hxb⟩]) (by linarith)
  linarith [hneg' c hc]

/-- Left-sided first-derivative test in time: if `g(s) ≤ g(t)` for all `t ∈ [0,s)` and `g` has
derivative `g'` at `s ∈ (0,τ]` within `[0,τ]`, then `g' ≤ 0`. -/
theorem deriv_nonpos_of_leftMin {g : ℝ → ℝ} {g' s τ : ℝ} (hs : 0 < s) (hsτ : s ≤ τ)
    (hg : HasDerivWithinAt g g' (Icc 0 τ) s) (hmin : ∀ t ∈ Ico 0 s, g s ≤ g t) : g' ≤ 0 := by
  have h1 : HasDerivWithinAt g g' (Ico 0 s) s :=
    hg.mono (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl hsτ))
  rw [hasDerivWithinAt_iff_tendsto_slope, sdiff_singleton_eq_self (by simp)] at h1
  have : (𝓝[Ico 0 s] s).NeBot := mem_closure_iff_nhdsWithin_neBot.1
    (by rw [closure_Ico hs.ne]; exact ⟨hs.le, le_rfl⟩)
  refine le_of_tendsto h1 ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (by linarith [hmin t ht]) (by linarith [ht.2])

/-- Left limits preserve positivity: if `g` is continuous at `s ∈ (0,τ]` within `[0,τ]` and
`g > 0` on `[0,s)`, then `g(s) ≥ 0`. -/
theorem nonneg_of_leftPos {g : ℝ → ℝ} {s τ : ℝ} (hs : 0 < s) (hsτ : s ≤ τ)
    (hg : ContinuousWithinAt g (Icc 0 τ) s) (hpos : ∀ t ∈ Ico 0 s, 0 < g t) : 0 ≤ g s := by
  have hg' : ContinuousWithinAt g (Ico 0 s) s :=
    hg.mono (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl hsτ))
  have hmem : s ∈ closure (Ico 0 s) := by rw [closure_Ico hs.ne]; exact ⟨hs.le, le_rfl⟩
  exact ContinuousWithinAt.closure_le hmem continuousWithinAt_const hg'
    (fun t ht => (hpos t ht).le)

/-! ### The pointwise first-crossing (Nagumo) lemma -/

/-- **First-crossing lemma** (PDE note §4.2). At a point where the solution value, slope and
curvature `(uT, uψ, uψψ)` touch a strict subsolution `(sT, sψ, sψψ)` from above (equal value
and slope, larger curvature), nonnegative diffusivity forces the solution's time derivative to
exceed the subsolution's. Only `D ≥ 0` at the touching value is used: since value and slope
coincide, `D(ψ,u)`, `∂ψD(ψ,u)` and the quasilinear term `∂TD(ψ,u) uψ` are the same for both
(kernel change K2). -/
theorem first_crossing (c : RadialCoefficients) {ψ uT uψ uψψ ut sT sψ sψψ st : ℝ}
    (hD : 0 ≤ c.D ψ uT) (hval : sT = uT) (hslope : sψ = uψ) (hcurv : sψψ ≤ uψψ)
    (hpde : ut = c.op ψ uT uψ uψψ) (hstrict : st < c.op ψ sT sψ sψψ) : st < ut := by
  subst hval hslope hpde
  unfold RadialCoefficients.op at *
  nlinarith [mul_le_mul_of_nonneg_left hcurv hD]

/-- First-crossing lemma at the **magnetic axis** `ψ = 0`. If `e = T − S` (at a fixed time) has
a zero minimum over `[0,1]` at `ψ = 0` and both slopes vanish there (Neumann condition), then
`e_ψψ(0) ≥ 0`, so `∂ₜT(0) > ∂ₜS(0)` for a strict subsolution. -/
theorem first_crossing_axis (c : RadialCoefficients) {uT uψ uψψ sT sψ sψψ : ℝ → ℝ} {ut st : ℝ}
    (hD : 0 ≤ c.D 0 (uT 0))
    (hu : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt uT (uψ x) (Icc 0 1) x)
    (hu' : HasDerivWithinAt uψ (uψψ 0) (Icc 0 1) 0)
    (hs : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt sT (sψ x) (Icc 0 1) x)
    (hs' : HasDerivWithinAt sψ (sψψ 0) (Icc 0 1) 0)
    (hmin : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ uT x - sT x) (hzero : uT 0 = sT 0)
    (huaxis : uψ 0 = 0) (hsaxis : sψ 0 = 0)
    (hpde : ut = c.op 0 (uT 0) (uψ 0) (uψψ 0)) (hstrict : st < c.op 0 (sT 0) (sψ 0) (sψψ 0)) :
    st < ut := by
  have hcurv : 0 ≤ uψψ 0 - sψψ 0 :=
    secondDeriv_nonneg_of_rightMin (f := fun x => uT x - sT x) (f' := fun x => uψ x - sψ x)
      zero_lt_one (fun x hx => (hu x hx).sub (hs x hx)) (hu'.sub hs')
      (fun x hx => by simp only [hzero, sub_self]; exact hmin x hx) (by simp [huaxis, hsaxis])
  exact first_crossing c hD hzero.symm (by rw [huaxis, hsaxis]) (by linarith) hpde hstrict

/-- First-crossing lemma at an **interior** point `ψ₀ ∈ (0,1)`: a zero minimum of `e = T − S`
over `[0,1]` at `ψ₀` gives `e_ψ(ψ₀) = 0` and `e_ψψ(ψ₀) ≥ 0`, hence `∂ₜT > ∂ₜS` for a strict
subsolution. -/
theorem first_crossing_interior (c : RadialCoefficients) {uT uψ uψψ sT sψ sψψ : ℝ → ℝ}
    {ψ₀ ut st : ℝ} (h0 : 0 < ψ₀) (h1 : ψ₀ < 1) (hD : 0 ≤ c.D ψ₀ (uT ψ₀))
    (hu : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt uT (uψ x) (Icc 0 1) x)
    (hu' : HasDerivWithinAt uψ (uψψ ψ₀) (Icc 0 1) ψ₀)
    (hs : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt sT (sψ x) (Icc 0 1) x)
    (hs' : HasDerivWithinAt sψ (sψψ ψ₀) (Icc 0 1) ψ₀)
    (hmin : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ uT x - sT x) (hzero : uT ψ₀ = sT ψ₀)
    (hpde : ut = c.op ψ₀ (uT ψ₀) (uψ ψ₀) (uψψ ψ₀))
    (hstrict : st < c.op ψ₀ (sT ψ₀) (sψ ψ₀) (sψψ ψ₀)) : st < ut := by
  have hmem : ψ₀ ∈ Icc (0 : ℝ) 1 := ⟨h0.le, h1.le⟩
  have hloc : IsLocalMin (fun x => uT x - sT x) ψ₀ :=
    Filter.mem_of_superset (Icc_mem_nhds h0 h1) (fun x hx => by
      change uT ψ₀ - sT ψ₀ ≤ uT x - sT x
      rw [hzero, sub_self]; exact hmin x hx)
  have hslope : uψ ψ₀ - sψ ψ₀ = 0 :=
    hloc.hasDerivAt_eq_zero (((hu ψ₀ hmem).sub (hs ψ₀ hmem)).hasDerivAt (Icc_mem_nhds h0 h1))
  have hcurv : 0 ≤ uψψ ψ₀ - sψψ ψ₀ :=
    secondDeriv_nonneg_of_rightMin (f := fun x => uT x - sT x) (f' := fun x => uψ x - sψ x)
      h1 (fun x hx => ((hu x ⟨h0.le.trans hx.1, hx.2⟩).sub
        (hs x ⟨h0.le.trans hx.1, hx.2⟩)).mono (Icc_subset_Icc h0.le le_rfl))
      ((hu'.sub hs').mono (Icc_subset_Icc h0.le le_rfl))
      (fun x hx => by
        simp only [hzero, sub_self]; exact hmin x ⟨h0.le.trans hx.1, hx.2⟩) hslope
  exact first_crossing c hD hzero.symm (by linarith) (by linarith) hpde hstrict

/-! ### Degenerate axis -/

/-- **Degenerate (Fichera) axis condition**: the diffusivity vanishes at the axis (at every
temperature), the drift coefficient `∂ψD(0,T)` there is nonnegative, and the quasilinear
coefficient `∂TD(0,T)` vanishes, so that no axis boundary condition is needed. Holds for
`D(ψ,T) = χ(T) ⟨|∇ψ|²⟩` in the normalized toroidal flux coordinate. -/
structure DegenerateAxis (c : RadialCoefficients) : Prop where
  /-- `D(0,T) = 0`. -/
  D_zero : ∀ T : ℝ, c.D 0 T = 0
  /-- `∂ψD(0,T) ≥ 0`. -/
  drift_nonneg : ∀ T : ℝ, 0 ≤ c.dD 0 T
  /-- `∂TD(0,T) = 0` (K2; automatic when `D(0,·) ≡ 0` is differentiable). -/
  DT_zero : ∀ T : ℝ, c.dDT 0 T = 0

/-- First-derivative test at a left endpoint: if `f` attains its minimum over `[a,b]` at `a`
and has derivative `f'` there within `[a,b]`, then `f' ≥ 0`. -/
theorem deriv_nonneg_of_leftEndMin {f : ℝ → ℝ} {f' a b : ℝ} (hab : a < b)
    (hf : HasDerivWithinAt f f' (Icc a b) a) (hmin : ∀ x ∈ Icc a b, f a ≤ f x) : 0 ≤ f' := by
  have h1 : HasDerivWithinAt f f' (Ioc a b) a := hf.mono Ioc_subset_Icc_self
  rw [hasDerivWithinAt_iff_tendsto_slope, sdiff_singleton_eq_self (by simp)] at h1
  have : (𝓝[Ioc a b] a).NeBot := mem_closure_iff_nhdsWithin_neBot.1
    (by rw [closure_Ioc hab.ne]; exact ⟨le_rfl, hab.le⟩)
  refine ge_of_tendsto h1 ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [slope_def_field]
  exact div_nonneg (by linarith [hmin x (Ioc_subset_Icc_self hx)]) (by linarith [hx.1])

/-- Under the kernel laws a `degenerate` axis satisfies `DegenerateAxis`: `D(0,·) = 0` is a
law, `∂ψD(0,T) ≥ 0` follows because `D(·,T) ≥ 0` attains its minimum `0` at the left end
`ψ = 0`, and `∂TD(0,T) = 0` is the derivative of the zero function `D(0,·)`. -/
theorem TransportLaws.degenerateAxis (c : RadialCoefficients) [h : TransportLaws c]
    (hk : c.axis = .degenerate) : DegenerateAxis c := by
  refine ⟨h.D_axis hk, fun T => deriv_nonneg_of_leftEndMin zero_lt_one
    (h.D_deriv 0 ⟨le_rfl, zero_le_one⟩ T)
    (fun x hx => by rw [h.D_axis hk]; exact h.D_nonneg x hx T), fun T => ?_⟩
  have h0 : c.D 0 = fun _ => 0 := funext (h.D_axis hk)
  have hd := h.DT_deriv 0 ⟨le_rfl, zero_le_one⟩ T
  rw [h0] at hd
  exact hd.unique (hasDerivAt_const T 0)

/-- **Touching at a degenerate axis.** If `u − S` has a zero minimum over `[0,1]` at `ψ = 0`,
then `N[S](0) ≤ N[u](0)`: the curvature term is switched off by `D(0,·) = 0`, the
quasilinear term by `∂TD(0,·) = 0`, and the drift term has the right sign because the
one-sided slope of `u − S` is `≥ 0`. -/
theorem op_le_op_of_touch_axis (c : RadialCoefficients) (hax : DegenerateAxis c)
    {uT sT : ℝ → ℝ} {uψ sψ uψψ sψψ : ℝ}
    (hu : HasDerivWithinAt uT uψ (Icc 0 1) 0) (hs : HasDerivWithinAt sT sψ (Icc 0 1) 0)
    (hmin : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ uT x - sT x) (hzero : uT 0 = sT 0) :
    c.op 0 (sT 0) sψ sψψ ≤ c.op 0 (uT 0) uψ uψψ := by
  have hslope : 0 ≤ uψ - sψ :=
    deriv_nonneg_of_leftEndMin (f := fun x => uT x - sT x) zero_lt_one (hu.sub hs)
      (fun x hx => by simp only [hzero, sub_self]; exact hmin x hx)
  unfold RadialCoefficients.op
  rw [hzero, hax.D_zero, hax.DT_zero]
  simp only [zero_mul, zero_div, add_zero, zero_add]
  nlinarith [mul_nonneg (hax.drift_nonneg (sT 0)) hslope]

/-! ### Strict comparison with a time-dependent strict subsolution -/

/-- A classical **strict subsolution** on `[0,1] × [0,τ]`: regular, satisfying the axis
Neumann condition `∂ψS(0,t) = 0` when the axis is `regular`, and `∂ₜS < N[S]` pointwise. -/
structure StrictSubsolution (c : RadialCoefficients) (τ : ℝ) (S : RadialField) : Prop where
  /-- Classical regularity on the closed rectangle. -/
  regular : S.Regular τ
  /-- Axis Neumann condition (regular axis only). -/
  axis : c.axis = .regular → ∀ t ∈ Icc 0 τ, S.Tψ 0 t = 0
  /-- Strict differential inequality `∂ₜS < N[S]`. -/
  strict : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ,
    S.Tt ψ t < c.op ψ (S.T ψ t) (S.Tψ ψ t) (S.Tψψ ψ t)

/-- **Strict parabolic comparison** (first-touching-time argument). A supplied classical
solution that starts strictly above a strict subsolution and stays strictly above it at the
edge stays strictly above it on all of `[0,1] × [0,τ]`. Only `D ≥ 0` on `[0,1]` is assumed
(degenerate diffusion is allowed), plus `DegenerateAxis` if the axis is `degenerate`. -/
theorem lt_of_strictSubsolution {c : RadialCoefficients} {Tedge : ℝ → ℝ} {τ : ℝ}
    {u S : RadialField} (hD : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ T : ℝ, 0 ≤ c.D ψ T)
    (hax : c.axis = .degenerate → DegenerateAxis c)
    (hu : ClassicalRadialSolution c Tedge τ u) (hS : StrictSubsolution c τ S)
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, S.T ψ 0 < u.T ψ 0)
    (h1 : ∀ t ∈ Icc 0 τ, S.T 1 t < Tedge t) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ, S.T ψ t < u.T ψ t := by
  set e : ℝ × ℝ → ℝ := fun p => u.T p.1 p.2 - S.T p.1 p.2 with he
  have hecont : ContinuousOn e (Icc 0 1 ×ˢ Icc 0 τ) := hu.regular.cont.sub hS.regular.cont
  set bad := (Icc (0 : ℝ) 1 ×ˢ Icc 0 τ) ∩ e ⁻¹' Iic 0 with hbad
  have hbadc : IsCompact bad :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
      (hecont.preimage_isClosed_of_isClosed (isClosed_Icc.prod isClosed_Icc) isClosed_Iic)
      inter_subset_left
  by_contra hcon
  push Not at hcon
  obtain ⟨ψ0, hψ0, t0, ht0, hle⟩ := hcon
  have hB : IsCompact (Prod.snd '' bad) := hbadc.image continuous_snd
  have hBne : (Prod.snd '' bad).Nonempty :=
    ⟨t0, (ψ0, t0), ⟨⟨hψ0, ht0⟩, by simp only [he, mem_preimage, mem_Iic]; linarith⟩, rfl⟩
  obtain ⟨⟨ψs, ts⟩, ⟨⟨hψs, hts⟩, hes⟩, hsnd⟩ := hB.sInf_mem hBne
  simp only at hsnd
  simp only [he, mem_preimage, mem_Iic] at hes
  -- before the first bad time the solution is strictly above
  have hgood : ∀ t ∈ Icc 0 τ, t < ts → ∀ ψ ∈ Icc (0 : ℝ) 1, S.T ψ t < u.T ψ t := by
    intro t ht hlt ψ hψ
    by_contra h
    push Not at h
    have : ts ≤ t := hsnd ▸ csInf_le hB.bddBelow
      ⟨(ψ, t), ⟨⟨hψ, ht⟩, by simp only [he, mem_preimage, mem_Iic]; linarith⟩, rfl⟩
    linarith
  have hts0 : 0 < ts := by
    rcases hts.1.lt_or_eq with h | h
    · exact h
    · subst h; linarith [h0 ψs hψs]
  -- at the first bad time the difference is still nonnegative
  have hnonneg : ∀ ψ ∈ Icc (0 : ℝ) 1, S.T ψ ts ≤ u.T ψ ts := by
    intro ψ hψ
    have hcw : ContinuousWithinAt (fun t => u.T ψ t - S.T ψ t) (Icc 0 τ) ts :=
      ((hu.regular.deriv_t ψ hψ ts hts).sub (hS.regular.deriv_t ψ hψ ts hts)).continuousWithinAt
    have := nonneg_of_leftPos hts0 hts.2 hcw (fun t ht =>
      sub_pos.2 (hgood t ⟨ht.1, ht.2.le.trans hts.2⟩ ht.2 ψ hψ))
    linarith
  have hzero : u.T ψs ts = S.T ψs ts := le_antisymm (by linarith) (hnonneg ψs hψs)
  have hψs1 : ψs < 1 := by
    rcases hψs.2.lt_or_eq with h | h
    · exact h
    · subst h; have := h1 ts hts; rw [hu.edge ts hts] at hzero; linarith
  have hmin : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ u.T x ts - S.T x ts := fun x hx =>
    sub_nonneg.2 (hnonneg x hx)
  -- the spatial first-crossing lemma gives a positive time derivative of `e`
  have hcross : S.Tt ψs ts < u.Tt ψs ts := by
    rcases hψs.1.lt_or_eq with h | h
    · exact first_crossing_interior c (uψψ := fun x => u.Tψψ x ts)
        (sψψ := fun x => S.Tψψ x ts) h hψs1 (hD ψs hψs _) (hu.regular.deriv_ψ ts hts)
        (hu.regular.deriv_ψψ ts hts ψs hψs) (hS.regular.deriv_ψ ts hts)
        (hS.regular.deriv_ψψ ts hts ψs hψs) hmin hzero (hu.pde ψs hψs ts hts)
        (hS.strict ψs hψs ts hts)
    · subst h
      cases hk : c.axis with
      | regular =>
        exact first_crossing_axis c (uψψ := fun x => u.Tψψ x ts)
          (sψψ := fun x => S.Tψψ x ts) (hD 0 hψs _) (hu.regular.deriv_ψ ts hts)
          (hu.regular.deriv_ψψ ts hts 0 hψs) (hS.regular.deriv_ψ ts hts)
          (hS.regular.deriv_ψψ ts hts 0 hψs) hmin hzero (hu.axis hk ts hts) (hS.axis hk ts hts)
          (hu.pde 0 hψs ts hts) (hS.strict 0 hψs ts hts)
      | degenerate =>
        have hop := op_le_op_of_touch_axis c (hax hk) (uψψ := u.Tψψ 0 ts)
          (sψψ := S.Tψψ 0 ts) (hu.regular.deriv_ψ ts hts 0 hψs)
          (hS.regular.deriv_ψ ts hts 0 hψs) hmin hzero
        rw [hu.pde 0 hψs ts hts]
        exact (hS.strict 0 hψs ts hts).trans_le hop
  -- but `e(ψs, ·)` attains a left minimum at `ts`, so its time derivative is nonpositive
  have htd : u.Tt ψs ts - S.Tt ψs ts ≤ 0 :=
    deriv_nonpos_of_leftMin hts0 hts.2
      ((hu.regular.deriv_t ψs hψs ts hts).sub (hS.regular.deriv_t ψs hψs ts hts))
      (fun t ht => by
        change u.T ψs ts - S.T ψs ts ≤ u.T ψs t - S.T ψs t
        rw [hzero, sub_self]
        exact (sub_pos.2 (hgood t ⟨ht.1, ht.2.le.trans hts.2⟩ ht.2 ψs hψs)).le)
  linarith

/-- Specialization of `lt_of_strictSubsolution` to a kernel solution: the transport laws give
`D ≥ 0`, and `DegenerateAxis` for a degenerate axis. -/
theorem RadialHeatTransport.lt_of_strictSubsolution {c : RadialCoefficients} {Tedge : ℝ → ℝ}
    {τ : ℝ} {u S : RadialField} [hu : RadialHeatTransport c Tedge τ u]
    (hS : StrictSubsolution c τ S) (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, S.T ψ 0 < u.T ψ 0)
    (h1 : ∀ t ∈ Icc 0 τ, S.T 1 t < Tedge t) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ, S.T ψ t < u.T ψ t :=
  Transport.lt_of_strictSubsolution TransportLaws.D_nonneg (TransportLaws.degenerateAxis c)
    hu.toClassicalRadialSolution hS h0 h1

/-! ### Stationary barriers -/

/-- The stationary field of a profile `f` with supplied derivatives `f'`, `f''` (and zero time
derivative). -/
@[expose] def RadialField.stationary (f f' f'' : ℝ → ℝ) : RadialField :=
  ⟨fun ψ _ => f ψ, fun ψ _ => f' ψ, fun ψ _ => f'' ψ, fun _ _ => 0⟩

/-- A radial profile on `[0,1]` that is twice differentiable (one-sided at the ends) with
supplied derivatives `f'` and `f''`. -/
structure ProfileRegular (f f' f'' : ℝ → ℝ) : Prop where
  /-- `f'` is the derivative of `f` on `[0,1]`. -/
  deriv : ∀ ψ ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' ψ) (Icc 0 1) ψ
  /-- `f''` is the derivative of `f'` on `[0,1]`. -/
  deriv2 : ∀ ψ ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f' (f'' ψ) (Icc 0 1) ψ

/-- A regular profile is continuous on `[0,1]`. -/
theorem ProfileRegular.continuousOn {f f' f'' : ℝ → ℝ} (h : ProfileRegular f f' f'') :
    ContinuousOn f (Icc 0 1) := fun ψ hψ => (h.deriv ψ hψ).continuousWithinAt

/-- The stationary field of a regular profile is regular on every rectangle. -/
theorem ProfileRegular.stationary_regular {f f' f'' : ℝ → ℝ} (h : ProfileRegular f f' f'')
    (τ : ℝ) : (RadialField.stationary f f' f'').Regular τ where
  cont := h.continuousOn.comp continuousOn_fst (fun _ hp => hp.1)
  deriv_ψ := fun _ _ ψ hψ => h.deriv ψ hψ
  deriv_ψψ := fun _ _ ψ hψ => h.deriv2 ψ hψ
  deriv_t := fun _ _ _ _ => hasDerivWithinAt_const _ _ _

/-- A **strict stationary lower barrier** (PDE note §4.2): a regular profile with the axis
Neumann condition `f'(0) = 0` (only for a `regular` axis) and `N[f] > 0` on `[0,1]`. -/
structure IsStrictLowerBarrier (c : RadialCoefficients) (f f' f'' : ℝ → ℝ) : Prop
    extends ProfileRegular f f' f'' where
  /-- Axis Neumann condition (regular axis only). -/
  axis : c.axis = .regular → f' 0 = 0
  /-- Strict subsolution `N[f] > 0`. -/
  strict : ∀ ψ ∈ Icc (0 : ℝ) 1, 0 < c.op ψ (f ψ) (f' ψ) (f'' ψ)

/-- A (non-strict) stationary lower barrier: `N[f] ≥ 0` on `[0,1]`, `f'(0) = 0` for a regular
axis. -/
structure IsLowerBarrier (c : RadialCoefficients) (f f' f'' : ℝ → ℝ) : Prop
    extends ProfileRegular f f' f'' where
  /-- Axis Neumann condition (regular axis only). -/
  axis : c.axis = .regular → f' 0 = 0
  /-- Subsolution `N[f] ≥ 0`. -/
  nonneg : ∀ ψ ∈ Icc (0 : ℝ) 1, 0 ≤ c.op ψ (f ψ) (f' ψ) (f'' ψ)

/-- A strict stationary upper barrier: `N[f] < 0` on `[0,1]`, `f'(0) = 0` for a regular
axis. -/
structure IsStrictUpperBarrier (c : RadialCoefficients) (f f' f'' : ℝ → ℝ) : Prop
    extends ProfileRegular f f' f'' where
  /-- Axis Neumann condition (regular axis only). -/
  axis : c.axis = .regular → f' 0 = 0
  /-- Strict supersolution `N[f] < 0`. -/
  strict : ∀ ψ ∈ Icc (0 : ℝ) 1, c.op ψ (f ψ) (f' ψ) (f'' ψ) < 0

/-- A (non-strict) stationary upper barrier: `N[f] ≤ 0` on `[0,1]`, `f'(0) = 0` for a regular
axis. -/
structure IsUpperBarrier (c : RadialCoefficients) (f f' f'' : ℝ → ℝ) : Prop
    extends ProfileRegular f f' f'' where
  /-- Axis Neumann condition (regular axis only). -/
  axis : c.axis = .regular → f' 0 = 0
  /-- Supersolution `N[f] ≤ 0`. -/
  nonpos : ∀ ψ ∈ Icc (0 : ℝ) 1, c.op ψ (f ψ) (f' ψ) (f'' ψ) ≤ 0

/-- A strict stationary lower barrier is a strict subsolution on every rectangle. -/
theorem IsStrictLowerBarrier.strictSubsolution {c : RadialCoefficients} {f f' f'' : ℝ → ℝ}
    (hf : IsStrictLowerBarrier c f f' f'') (τ : ℝ) :
    StrictSubsolution c τ (RadialField.stationary f f' f'') :=
  ⟨hf.toProfileRegular.stationary_regular τ, fun hk _ _ => hf.axis hk,
    fun ψ hψ _ _ => hf.strict ψ hψ⟩

/-- **Strict stationary lower-barrier theorem.** If `N[f] > 0`, `f'(0) = 0` (regular axis), the
edge data stay
strictly above `f(1)` and the initial profile is strictly above `f`, then `T > f` on
`[0,1] × [0,τ]`. -/
theorem lt_of_isStrictLowerBarrier {c : RadialCoefficients} {Tedge : ℝ → ℝ} {τ : ℝ}
    {u : RadialField} [hu : RadialHeatTransport c Tedge τ u] {f f' f'' : ℝ → ℝ}
    (hf : IsStrictLowerBarrier c f f' f'') (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, f ψ < u.T ψ 0)
    (h1 : ∀ t ∈ Icc 0 τ, f 1 < Tedge t) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ, f ψ < u.T ψ t :=
  RadialHeatTransport.lt_of_strictSubsolution (hf.strictSubsolution τ) h0 h1

/-- A positive lower bound for a continuous positive function on `[0,1]` (compactness). Use it
to obtain the margin required by `le_of_isStrictLowerBarrier_margin` when `ψ ↦ N[f](ψ)` is
known to be continuous. -/
theorem exists_margin_of_continuousOn {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 1))
    (hpos : ∀ ψ ∈ Icc (0 : ℝ) 1, 0 < g ψ) : ∃ κ > 0, ∀ ψ ∈ Icc (0 : ℝ) 1, κ ≤ g ψ := by
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one) hg
  exact ⟨g x, hpos x hx, fun ψ hψ => hmin hψ⟩

/-- Compactness step for the margin theorems, for an arbitrary function `Φ(ψ,T)`: a profile
`f` continuous on `[0,1]` with values in an open set `U`, and `Φ` continuous on `[0,1] × U`,
give `δ₀ > 0` such that every shift `f ψ + s` with `|s| < δ₀` stays in `U` and changes
`Φ(ψ, f ψ)` by less than `κ`. -/
theorem exists_shift_control_fun {f : ℝ → ℝ} (hfc : ContinuousOn f (Icc 0 1)) {U : Set ℝ}
    (hU : IsOpen U) {Φ : ℝ → ℝ → ℝ}
    (hΦ : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) (Icc 0 1 ×ˢ U))
    (hfU : ∀ ψ ∈ Icc (0 : ℝ) 1, f ψ ∈ U) {κ : ℝ} (hκ : 0 < κ) :
    ∃ δ₀ > 0, ∀ s : ℝ, |s| < δ₀ → ∀ ψ ∈ Icc (0 : ℝ) 1,
      f ψ + s ∈ U ∧ |Φ ψ (f ψ + s) - Φ ψ (f ψ)| < κ := by
  have hK : IsCompact (f '' Icc 0 1) := isCompact_Icc.image_of_continuousOn hfc
  obtain ⟨γ, hγ, hγU⟩ := hK.exists_cthickening_subset_open hU (by
    rintro _ ⟨ψ, hψ, rfl⟩; exact hfU ψ hψ)
  have hC : IsCompact (Metric.cthickening γ (f '' Icc 0 1)) := hK.cthickening
  have hRuc : UniformContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ Metric.cthickening γ (f '' Icc 0 1)) :=
    (isCompact_Icc.prod hC).uniformContinuousOn_of_continuous
      (hΦ.mono (prod_mono subset_rfl hγU))
  rw [Metric.uniformContinuousOn_iff] at hRuc
  obtain ⟨δ0, hδ0, hδ⟩ := hRuc κ hκ
  have hmem : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ s : ℝ, |s| ≤ γ →
      f ψ + s ∈ Metric.cthickening γ (f '' Icc 0 1) := fun ψ hψ s hs =>
    Metric.mem_cthickening_of_dist_le _ (f ψ) _ _ ⟨ψ, hψ, rfl⟩
      (by rw [Real.dist_eq, show f ψ + s - f ψ = s by ring]; exact hs)
  refine ⟨min δ0 γ, lt_min hδ0 hγ, fun s hs ψ hψ => ⟨hγU (hmem ψ hψ s (lt_min_iff.1 hs).2.le),
    ?_⟩⟩
  have hs1 := lt_min_iff.1 hs
  have hd := hδ (ψ, f ψ + s) ⟨hψ, hmem ψ hψ s hs1.2.le⟩ (ψ, f ψ)
    ⟨hψ, by simpa using hmem ψ hψ 0 (by simp [hγ.le])⟩
    (by
      rw [Prod.dist_eq, dist_self, Real.dist_eq, show f ψ + s - f ψ = s by ring,
        max_eq_right (abs_nonneg s)]
      exact hs1.1)
  rwa [Real.dist_eq] at hd

/-- Compactness step for the margin theorems: a regular profile `f` with values in an open set
`U`, and `R` continuous on `[0,1] × U`, give `δ₀ > 0` such that shifting the value argument by
any `|s| < δ₀` changes `R(ψ, f ψ)` by less than `κ` (and stays in `U`). -/
theorem exists_shift_control_open {c : RadialCoefficients} {f f' f'' : ℝ → ℝ}
    (hf : ProfileRegular f f' f'') {U : Set ℝ} (hU : IsOpen U)
    (hRc : ContinuousOn (fun p : ℝ × ℝ => c.R p.1 p.2) (Icc 0 1 ×ˢ U))
    (hfU : ∀ ψ ∈ Icc (0 : ℝ) 1, f ψ ∈ U) {κ : ℝ} (hκ : 0 < κ) :
    ∃ δ₀ > 0, ∀ s : ℝ, |s| < δ₀ → ∀ ψ ∈ Icc (0 : ℝ) 1,
      |c.R ψ (f ψ + s) - c.R ψ (f ψ)| < κ := by
  obtain ⟨δ₀, hδ₀, h⟩ := exists_shift_control_fun hf.continuousOn hU hRc hfU hκ
  exact ⟨δ₀, hδ₀, fun s hs ψ hψ => (h s hs ψ hψ).2⟩

/-! ### Continuity of the operator in the value argument (needed by the margin theorems) -/

/-- **Shift control along a profile**: small shifts `f + s` of the value argument change the
operator `N` along the profile (slope `f'`, curvature `f''` fixed) uniformly little. This is
what the margin theorems need besides the touching argument. For semilinear coefficients it
follows from continuity of `R` (`IsSemilinear.opShiftControl`); for quasilinear coefficients
(kernel change K2) it follows from joint continuity of `(ψ,T) ↦ N` along the profile
(`opShiftControl_of_continuousOn`), e.g. for polynomial profiles and continuous `D`, `∂D`. -/
def OpShiftControl (c : RadialCoefficients) (f f' f'' : ℝ → ℝ) : Prop :=
  ∀ κ > 0, ∃ δ₀ > 0, ∀ s : ℝ, |s| < δ₀ → ∀ ψ ∈ Icc (0 : ℝ) 1,
    |c.op ψ (f ψ + s) (f' ψ) (f'' ψ) - c.op ψ (f ψ) (f' ψ) (f'' ψ)| < κ

/-- Shift control from a decomposition `N(ψ,T) = A(ψ) + Φ(ψ,T)` along the profile on
`[0,1] × U`, with `Φ` jointly continuous, `U` open and `f ∈ U`. (`A` is arbitrary: it absorbs
terms that need not be continuous in `ψ`.) -/
theorem opShiftControl_of_decomp {c : RadialCoefficients} {f f' f'' : ℝ → ℝ}
    (hfc : ContinuousOn f (Icc 0 1)) {U : Set ℝ} (hU : IsOpen U)
    (hfU : ∀ ψ ∈ Icc (0 : ℝ) 1, f ψ ∈ U) (A : ℝ → ℝ) {Φ : ℝ → ℝ → ℝ}
    (hΦ : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) (Icc 0 1 ×ˢ U))
    (hdec : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ T ∈ U, c.op ψ T (f' ψ) (f'' ψ) = A ψ + Φ ψ T) :
    OpShiftControl c f f' f'' := fun κ hκ => by
  obtain ⟨δ₀, hδ₀, h⟩ := exists_shift_control_fun hfc hU hΦ hfU hκ
  refine ⟨δ₀, hδ₀, fun s hs ψ hψ => ?_⟩
  obtain ⟨hmem, hlt⟩ := h s hs ψ hψ
  rw [hdec ψ hψ _ hmem, hdec ψ hψ _ (hfU ψ hψ)]
  simpa using hlt

/-- **Quasilinear shift control**: if `(ψ,T) ↦ N(ψ, T, f'(ψ), f''(ψ))` is jointly continuous on
`[0,1] × U` (`U` open, containing the values of `f`), the operator has shift control along
`f`. -/
theorem opShiftControl_of_continuousOn {c : RadialCoefficients} {f f' f'' : ℝ → ℝ}
    (hfc : ContinuousOn f (Icc 0 1)) {U : Set ℝ} (hU : IsOpen U)
    (hfU : ∀ ψ ∈ Icc (0 : ℝ) 1, f ψ ∈ U)
    (hN : ContinuousOn (fun p : ℝ × ℝ => c.op p.1 p.2 (f' p.1) (f'' p.1)) (Icc 0 1 ×ˢ U)) :
    OpShiftControl c f f' f'' :=
  opShiftControl_of_decomp (Φ := fun ψ T => c.op ψ T (f' ψ) (f'' ψ)) hfc hU hfU (fun _ => 0) hN
    (fun _ _ _ _ => by simp)

/-- **Semilinear shift control**: for semilinear coefficients with `R` continuous on
`[0,1] × U` and `f ∈ U`, the operator has shift control along every regular profile. -/
theorem RadialCoefficients.IsSemilinear.opShiftControl {c : RadialCoefficients}
    (hsl : c.IsSemilinear) {f f' f'' : ℝ → ℝ} (hf : ProfileRegular f f' f'') {U : Set ℝ}
    (hU : IsOpen U) (hRc : ContinuousOn (fun p : ℝ × ℝ => c.R p.1 p.2) (Icc 0 1 ×ˢ U))
    (hfU : ∀ ψ ∈ Icc (0 : ℝ) 1, f ψ ∈ U) : OpShiftControl c f f' f'' :=
  opShiftControl_of_decomp hf.continuousOn hU hfU
    (fun ψ => c.op ψ (f ψ) (f' ψ) (f'' ψ) - c.R ψ (f ψ)) hRc (fun ψ hψ T _ => by
      have := hsl.op_sub_op hψ T (f ψ) (f' ψ) (f'' ψ)
      linarith)

/-! ### Comparison by residuals at the kernel level (both axis kinds, direct upper barriers) -/

/-- **Touching at an interior point.** If `u − S` has a zero minimum over `[0,1]` at
`ψ₀ ∈ (0,1)` and `D(ψ₀, u(ψ₀)) ≥ 0`, then `N[S](ψ₀) ≤ N[u](ψ₀)`. Quasilinear coefficients are
allowed: value and slope coincide at the touching point, so only the curvature term differs. -/
theorem op_le_op_of_touch_interior (c : RadialCoefficients) {uT uψ uψψ sT sψ sψψ : ℝ → ℝ}
    {ψ₀ : ℝ} (h0 : 0 < ψ₀) (h1 : ψ₀ < 1) (hD : 0 ≤ c.D ψ₀ (uT ψ₀))
    (hu : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt uT (uψ x) (Icc 0 1) x)
    (hu' : HasDerivWithinAt uψ (uψψ ψ₀) (Icc 0 1) ψ₀)
    (hs : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt sT (sψ x) (Icc 0 1) x)
    (hs' : HasDerivWithinAt sψ (sψψ ψ₀) (Icc 0 1) ψ₀)
    (hmin : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ uT x - sT x) (hzero : uT ψ₀ = sT ψ₀) :
    c.op ψ₀ (sT ψ₀) (sψ ψ₀) (sψψ ψ₀) ≤ c.op ψ₀ (uT ψ₀) (uψ ψ₀) (uψψ ψ₀) := by
  have hmem : ψ₀ ∈ Icc (0 : ℝ) 1 := ⟨h0.le, h1.le⟩
  have hloc : IsLocalMin (fun x => uT x - sT x) ψ₀ :=
    Filter.mem_of_superset (Icc_mem_nhds h0 h1) (fun x hx => by
      change uT ψ₀ - sT ψ₀ ≤ uT x - sT x
      rw [hzero, sub_self]; exact hmin x hx)
  have hslope : uψ ψ₀ - sψ ψ₀ = 0 :=
    hloc.hasDerivAt_eq_zero (((hu ψ₀ hmem).sub (hs ψ₀ hmem)).hasDerivAt (Icc_mem_nhds h0 h1))
  have hcurv : 0 ≤ uψψ ψ₀ - sψψ ψ₀ :=
    secondDeriv_nonneg_of_rightMin (f := fun x => uT x - sT x) (f' := fun x => uψ x - sψ x)
      h1 (fun x hx => ((hu x ⟨h0.le.trans hx.1, hx.2⟩).sub
        (hs x ⟨h0.le.trans hx.1, hx.2⟩)).mono (Icc_subset_Icc h0.le le_rfl))
      ((hu'.sub hs').mono (Icc_subset_Icc h0.le le_rfl))
      (fun x hx => by
        simp only [hzero, sub_self]; exact hmin x ⟨h0.le.trans hx.1, hx.2⟩) hslope
  have hs2 : sψ ψ₀ = uψ ψ₀ := by linarith
  rw [hzero] at hD
  unfold RadialCoefficients.op
  rw [hzero, hs2]
  nlinarith [mul_le_mul_of_nonneg_left hcurv hD]

/-- **Touching at a regular axis.** If `u − S` has a zero minimum over `[0,1]` at `ψ = 0` and
both slopes vanish there (Neumann condition), then `N[S](0) ≤ N[u](0)`. -/
theorem op_le_op_of_touch_axis_regular (c : RadialCoefficients) {uT uψ uψψ sT sψ sψψ : ℝ → ℝ}
    (hD : 0 ≤ c.D 0 (uT 0))
    (hu : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt uT (uψ x) (Icc 0 1) x)
    (hu' : HasDerivWithinAt uψ (uψψ 0) (Icc 0 1) 0)
    (hs : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt sT (sψ x) (Icc 0 1) x)
    (hs' : HasDerivWithinAt sψ (sψψ 0) (Icc 0 1) 0)
    (hmin : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ uT x - sT x) (hzero : uT 0 = sT 0)
    (huaxis : uψ 0 = 0) (hsaxis : sψ 0 = 0) :
    c.op 0 (sT 0) (sψ 0) (sψψ 0) ≤ c.op 0 (uT 0) (uψ 0) (uψψ 0) := by
  have hcurv : 0 ≤ uψψ 0 - sψψ 0 :=
    secondDeriv_nonneg_of_rightMin (f := fun x => uT x - sT x) (f' := fun x => uψ x - sψ x)
      zero_lt_one (fun x hx => (hu x hx).sub (hs x hx)) (hu'.sub hs')
      (fun x hx => by simp only [hzero, sub_self]; exact hmin x hx) (by simp [huaxis, hsaxis])
  rw [hzero] at hD
  unfold RadialCoefficients.op
  rw [hzero, huaxis, hsaxis]
  nlinarith [mul_le_mul_of_nonneg_left hcurv hD]

/-- **Comparison by residuals, kernel level** (first-touching-time argument, both axis kinds,
quasilinear coefficients). Let `S`, `u` be regular fields on `[0,1] × [0,τ]` with
`∂ₜS − N[S] < ∂ₜu − N[u]` pointwise, both satisfying the Neumann condition if the axis is
`regular`. If `S < u` initially and at the edge, then `S < u` on the whole rectangle. Lower
barriers take `S` a subsolution and `u` a solution; **upper barriers** take `S` the solution
and `u` a supersolution, with no mirror symmetry needed. -/
theorem lt_of_residual_lt_kernel {c : RadialCoefficients} {τ : ℝ} {u S : RadialField}
    (hD : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ T : ℝ, 0 ≤ c.D ψ T)
    (hax : c.axis = .degenerate → DegenerateAxis c)
    (hu : u.Regular τ) (hS : S.Regular τ)
    (huax : c.axis = .regular → ∀ t ∈ Icc 0 τ, u.Tψ 0 t = 0)
    (hSax : c.axis = .regular → ∀ t ∈ Icc 0 τ, S.Tψ 0 t = 0)
    (hres : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ,
      S.Tt ψ t - c.op ψ (S.T ψ t) (S.Tψ ψ t) (S.Tψψ ψ t) <
        u.Tt ψ t - c.op ψ (u.T ψ t) (u.Tψ ψ t) (u.Tψψ ψ t))
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, S.T ψ 0 < u.T ψ 0)
    (h1 : ∀ t ∈ Icc 0 τ, S.T 1 t < u.T 1 t) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ, S.T ψ t < u.T ψ t := by
  set e : ℝ × ℝ → ℝ := fun p => u.T p.1 p.2 - S.T p.1 p.2 with he
  have hecont : ContinuousOn e (Icc 0 1 ×ˢ Icc 0 τ) := hu.cont.sub hS.cont
  set bad := (Icc (0 : ℝ) 1 ×ˢ Icc 0 τ) ∩ e ⁻¹' Iic 0 with hbad
  have hbadc : IsCompact bad :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset
      (hecont.preimage_isClosed_of_isClosed (isClosed_Icc.prod isClosed_Icc) isClosed_Iic)
      inter_subset_left
  by_contra hcon
  push Not at hcon
  obtain ⟨ψ0, hψ0, t0, ht0, hle⟩ := hcon
  have hB : IsCompact (Prod.snd '' bad) := hbadc.image continuous_snd
  have hBne : (Prod.snd '' bad).Nonempty :=
    ⟨t0, (ψ0, t0), ⟨⟨hψ0, ht0⟩, by simp only [he, mem_preimage, mem_Iic]; linarith⟩, rfl⟩
  obtain ⟨⟨ψs, ts⟩, ⟨⟨hψs, hts⟩, hes⟩, hsnd⟩ := hB.sInf_mem hBne
  simp only at hsnd
  simp only [he, mem_preimage, mem_Iic] at hes
  have hgood : ∀ t ∈ Icc 0 τ, t < ts → ∀ ψ ∈ Icc (0 : ℝ) 1, S.T ψ t < u.T ψ t := by
    intro t ht hlt ψ hψ
    by_contra h
    push Not at h
    have : ts ≤ t := hsnd ▸ csInf_le hB.bddBelow
      ⟨(ψ, t), ⟨⟨hψ, ht⟩, by simp only [he, mem_preimage, mem_Iic]; linarith⟩, rfl⟩
    linarith
  have hts0 : 0 < ts := by
    rcases hts.1.lt_or_eq with h | h
    · exact h
    · subst h; linarith [h0 ψs hψs]
  have hnonneg : ∀ ψ ∈ Icc (0 : ℝ) 1, S.T ψ ts ≤ u.T ψ ts := by
    intro ψ hψ
    have hcw : ContinuousWithinAt (fun t => u.T ψ t - S.T ψ t) (Icc 0 τ) ts :=
      ((hu.deriv_t ψ hψ ts hts).sub (hS.deriv_t ψ hψ ts hts)).continuousWithinAt
    have := nonneg_of_leftPos hts0 hts.2 hcw (fun t ht =>
      sub_pos.2 (hgood t ⟨ht.1, ht.2.le.trans hts.2⟩ ht.2 ψ hψ))
    linarith
  have hzero : u.T ψs ts = S.T ψs ts := le_antisymm (by linarith) (hnonneg ψs hψs)
  have hψs1 : ψs < 1 := by
    rcases hψs.2.lt_or_eq with h | h
    · exact h
    · subst h; linarith [h1 ts hts]
  have hmin : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ u.T x ts - S.T x ts := fun x hx =>
    sub_nonneg.2 (hnonneg x hx)
  have hop : c.op ψs (S.T ψs ts) (S.Tψ ψs ts) (S.Tψψ ψs ts) ≤
      c.op ψs (u.T ψs ts) (u.Tψ ψs ts) (u.Tψψ ψs ts) := by
    rcases hψs.1.lt_or_eq with h | h
    · exact op_le_op_of_touch_interior c (uψψ := fun x => u.Tψψ x ts)
        (sψψ := fun x => S.Tψψ x ts) h hψs1 (hD ψs hψs _) (hu.deriv_ψ ts hts)
        (hu.deriv_ψψ ts hts ψs hψs) (hS.deriv_ψ ts hts) (hS.deriv_ψψ ts hts ψs hψs) hmin hzero
    · subst h
      cases hk : c.axis with
      | regular =>
        exact op_le_op_of_touch_axis_regular c (uψψ := fun x => u.Tψψ x ts)
          (sψψ := fun x => S.Tψψ x ts) (hD 0 hψs _) (hu.deriv_ψ ts hts)
          (hu.deriv_ψψ ts hts 0 hψs) (hS.deriv_ψ ts hts) (hS.deriv_ψψ ts hts 0 hψs) hmin hzero
          (huax hk ts hts) (hSax hk ts hts)
      | degenerate =>
        exact op_le_op_of_touch_axis c (hax hk) (hu.deriv_ψ ts hts 0 hψs)
          (hS.deriv_ψ ts hts 0 hψs) hmin hzero
  have hcross : S.Tt ψs ts < u.Tt ψs ts := by linarith [hres ψs hψs ts hts]
  have htd : u.Tt ψs ts - S.Tt ψs ts ≤ 0 :=
    deriv_nonpos_of_leftMin hts0 hts.2
      ((hu.deriv_t ψs hψs ts hts).sub (hS.deriv_t ψs hψs ts hts))
      (fun t ht => by
        change u.T ψs ts - S.T ψs ts ≤ u.T ψs t - S.T ψs t
        rw [hzero, sub_self]
        exact (sub_pos.2 (hgood t ⟨ht.1, ht.2.le.trans hts.2⟩ ht.2 ψs hψs)).le)
  linarith

/-! ### Stationary barriers with a margin (quasilinear coefficients) -/

/-- **Lower barrier with margin, quasilinear kernel.** If `N[f] ≥ κ > 0` on `[0,1]`, the
operator has shift control along `f` (`OpShiftControl`), `f'(0) = 0` for a regular axis,
`f(1) ≤ T_edge(t)` and `f ≤ T(·,0)`, then `f ≤ T` on `[0,1] × [0,τ]`: `f − δ` is a strict
barrier with strict data for all small `δ > 0`. -/
theorem le_of_lowerMargin_shift {c : RadialCoefficients} {Tedge : ℝ → ℝ} {τ : ℝ}
    {u : RadialField} [hu : RadialHeatTransport c Tedge τ u] {f f' f'' : ℝ → ℝ}
    (hf : ProfileRegular f f' f'') (haxis : c.axis = .regular → f' 0 = 0)
    (hctrl : OpShiftControl c f f' f'') {κ : ℝ} (hκ : 0 < κ)
    (hmargin : ∀ ψ ∈ Icc (0 : ℝ) 1, κ ≤ c.op ψ (f ψ) (f' ψ) (f'' ψ))
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, f ψ ≤ u.T ψ 0) (h1 : ∀ t ∈ Icc 0 τ, f 1 ≤ Tedge t) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ, f ψ ≤ u.T ψ t := by
  obtain ⟨δ₀, hδ₀, hctl⟩ := hctrl κ hκ
  have key : ∀ δ, 0 < δ → δ < δ₀ →
      ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ, f ψ - δ < u.T ψ t := by
    intro δ hδpos hδlt
    have hb : IsStrictLowerBarrier c (fun x => f x - δ) f' f'' :=
      { deriv := fun ψ hψ => (hf.deriv ψ hψ).sub_const δ
        deriv2 := hf.deriv2
        axis := haxis
        strict := by
          intro ψ hψ
          have hc := abs_lt.1 (hctl (-δ) (by rw [abs_neg, abs_of_pos hδpos]; exact hδlt) ψ hψ)
          have h3 := hmargin ψ hψ
          change 0 < c.op ψ (f ψ - δ) (f' ψ) (f'' ψ)
          rw [show f ψ - δ = f ψ + -δ by ring]
          linarith }
    exact lt_of_isStrictLowerBarrier (Tedge := Tedge) (u := u) hb
      (fun ψ hψ => by linarith [h0 ψ hψ]) (fun t ht => by linarith [h1 t ht])
  intro ψ hψ t ht
  refine le_of_forall_pos_lt_add (fun ε hε => ?_)
  have := key (min ε δ₀ / 2) (by positivity) (by linarith [min_le_right ε δ₀]) ψ hψ t ht
  linarith [min_le_left ε δ₀]

/-- **Upper barrier with margin, quasilinear kernel (direct proof).** If `N[g] ≤ −κ < 0` on
`[0,1]`, the operator has shift control along `g`, `g'(0) = 0` for a regular axis,
`T_edge(t) ≤ g(1)` and `T(·,0) ≤ g`, then `T ≤ g` on `[0,1] × [0,τ]`. Proved directly from
`lt_of_residual_lt_kernel` with the solution below the strict supersolution `g + δ`. -/
theorem le_of_upperMargin_shift {c : RadialCoefficients} {Tedge : ℝ → ℝ} {τ : ℝ}
    {u : RadialField} [hu : RadialHeatTransport c Tedge τ u] {g g' g'' : ℝ → ℝ}
    (hg : ProfileRegular g g' g'') (haxis : c.axis = .regular → g' 0 = 0)
    (hctrl : OpShiftControl c g g' g'') {κ : ℝ} (hκ : 0 < κ)
    (hmargin : ∀ ψ ∈ Icc (0 : ℝ) 1, c.op ψ (g ψ) (g' ψ) (g'' ψ) ≤ -κ)
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, u.T ψ 0 ≤ g ψ) (h1 : ∀ t ∈ Icc 0 τ, Tedge t ≤ g 1) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ, u.T ψ t ≤ g ψ := by
  obtain ⟨δ₀, hδ₀, hctl⟩ := hctrl κ hκ
  have key : ∀ δ, 0 < δ → δ < δ₀ →
      ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ, u.T ψ t < g ψ + δ := by
    intro δ hδ hδlt
    have hreg : (RadialField.stationary (fun x => g x + δ) g' g'').Regular τ :=
      (ProfileRegular.stationary_regular
        ⟨fun ψ hψ => (hg.deriv ψ hψ).add_const δ, hg.deriv2⟩ τ)
    refine lt_of_residual_lt_kernel (u := RadialField.stationary (fun x => g x + δ) g' g'')
      TransportLaws.D_nonneg (TransportLaws.degenerateAxis c) hreg hu.regular
      (fun hk _ _ => haxis hk) hu.axis (fun ψ hψ t ht => ?_)
      (fun ψ hψ => by change u.T ψ 0 < g ψ + δ; linarith [h0 ψ hψ])
      (fun t ht => by change u.T 1 t < g 1 + δ; rw [hu.edge t ht]; linarith [h1 t ht])
    have hc := abs_lt.1 (hctl δ (by rw [abs_of_pos hδ]; exact hδlt) ψ hψ)
    have h3 := hmargin ψ hψ
    rw [hu.pde ψ hψ t ht]
    change _ < 0 - c.op ψ (g ψ + δ) (g' ψ) (g'' ψ)
    linarith
  intro ψ hψ t ht
  refine le_of_forall_pos_lt_add (fun ε hε => ?_)
  have := key (min ε δ₀ / 2) (by positivity) (by linarith [min_le_right ε δ₀]) ψ hψ t ht
  linarith [min_le_left ε δ₀]

/-- **Lower barrier with margin, quasilinear kernel, for all time.** -/
theorem le_of_lowerMargin_shift_forall_time {c : RadialCoefficients} {Tedge : ℝ → ℝ}
    {u : RadialField} (hu : ∀ τ, 0 ≤ τ → RadialHeatTransport c Tedge τ u)
    {f f' f'' : ℝ → ℝ} (hf : ProfileRegular f f' f'') (haxis : c.axis = .regular → f' 0 = 0)
    (hctrl : OpShiftControl c f f' f'') {κ : ℝ} (hκ : 0 < κ)
    (hmargin : ∀ ψ ∈ Icc (0 : ℝ) 1, κ ≤ c.op ψ (f ψ) (f' ψ) (f'' ψ))
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, f ψ ≤ u.T ψ 0) (h1 : ∀ t, 0 ≤ t → f 1 ≤ Tedge t) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → f ψ ≤ u.T ψ t := fun ψ hψ t ht => by
  have := hu t ht
  exact le_of_lowerMargin_shift (τ := t) hf haxis hctrl hκ hmargin h0
    (fun s hs => h1 s hs.1) ψ hψ t ⟨ht, le_rfl⟩

/-- **Upper barrier with margin, quasilinear kernel, for all time.** -/
theorem le_of_upperMargin_shift_forall_time {c : RadialCoefficients} {Tedge : ℝ → ℝ}
    {u : RadialField} (hu : ∀ τ, 0 ≤ τ → RadialHeatTransport c Tedge τ u)
    {g g' g'' : ℝ → ℝ} (hg : ProfileRegular g g' g'') (haxis : c.axis = .regular → g' 0 = 0)
    (hctrl : OpShiftControl c g g' g'') {κ : ℝ} (hκ : 0 < κ)
    (hmargin : ∀ ψ ∈ Icc (0 : ℝ) 1, c.op ψ (g ψ) (g' ψ) (g'' ψ) ≤ -κ)
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, u.T ψ 0 ≤ g ψ) (h1 : ∀ t, 0 ≤ t → Tedge t ≤ g 1) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → u.T ψ t ≤ g ψ := fun ψ hψ t ht => by
  have := hu t ht
  exact le_of_upperMargin_shift (τ := t) hg haxis hctrl hκ hmargin h0
    (fun s hs => h1 s hs.1) ψ hψ t ⟨ht, le_rfl⟩

/-- **Lower-barrier theorem with non-strict data** (semilinear coefficients). If `N[f] ≥ κ > 0`
on `[0,1]` (a strict subsolution with uniform margin), `f` takes values in the source domain
`Tdom`, `f'(0) = 0` for a regular axis, `f(1) ≤ T_edge(t)` and `f ≤ T(·,0)`, then `f ≤ T` on
`[0,1] × [0,τ]`. Only the kernel's continuity of `R` is used (via
`IsSemilinear.opShiftControl`); for quasilinear coefficients use `le_of_lowerMargin_shift`. -/
theorem le_of_isStrictLowerBarrier_margin {c : RadialCoefficients} {Tedge : ℝ → ℝ} {τ : ℝ}
    {u : RadialField} [hu : RadialHeatTransport c Tedge τ u] {f f' f'' : ℝ → ℝ}
    (hsl : c.IsSemilinear)
    (hf : ProfileRegular f f' f'') (haxis : c.axis = .regular → f' 0 = 0)
    (hdom : ∀ ψ ∈ Icc (0 : ℝ) 1, f ψ ∈ c.Tdom) {κ : ℝ} (hκ : 0 < κ)
    (hmargin : ∀ ψ ∈ Icc (0 : ℝ) 1, κ ≤ c.op ψ (f ψ) (f' ψ) (f'' ψ))
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, f ψ ≤ u.T ψ 0) (h1 : ∀ t ∈ Icc 0 τ, f 1 ≤ Tedge t) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ, f ψ ≤ u.T ψ t :=
  le_of_lowerMargin_shift hf haxis
    (hsl.opShiftControl hf TransportLaws.Tdom_open TransportLaws.R_cont hdom) hκ hmargin h0 h1

/-- **Lower barrier with margin, for all time** (semilinear coefficients). If the supplied
field is a kernel solution on every horizon `[0,τ]`, the conclusion of
`le_of_isStrictLowerBarrier_margin` holds for all `t ≥ 0`. -/
theorem le_of_isStrictLowerBarrier_margin_forall_time {c : RadialCoefficients}
    {Tedge : ℝ → ℝ} {u : RadialField} (hu : ∀ τ, 0 ≤ τ → RadialHeatTransport c Tedge τ u)
    (hsl : c.IsSemilinear)
    {f f' f'' : ℝ → ℝ} (hf : ProfileRegular f f' f'') (haxis : c.axis = .regular → f' 0 = 0)
    (hdom : ∀ ψ ∈ Icc (0 : ℝ) 1, f ψ ∈ c.Tdom) {κ : ℝ} (hκ : 0 < κ)
    (hmargin : ∀ ψ ∈ Icc (0 : ℝ) 1, κ ≤ c.op ψ (f ψ) (f' ψ) (f'' ψ))
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, f ψ ≤ u.T ψ 0) (h1 : ∀ t, 0 ≤ t → f 1 ≤ Tedge t) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → f ψ ≤ u.T ψ t := fun ψ hψ t ht => by
  have := hu t ht
  exact le_of_isStrictLowerBarrier_margin (τ := t) hsl hf haxis hdom hκ hmargin h0
    (fun s hs => h1 s hs.1) ψ hψ t ⟨ht, le_rfl⟩

/-- One-sided Lipschitz bound for the net source on `[0,1]`:
`R(ψ,b) − R(ψ,a) ≤ K (b − a)` whenever `a ≤ b`, i.e. `v ↦ R(ψ,v) − K v` is nonincreasing.
It holds for any `R` that is `K`-Lipschitz in the temperature. -/
def OneSidedLipschitz (c : RadialCoefficients) (K : ℝ) : Prop :=
  ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ a b : ℝ, a ≤ b → c.R ψ b - c.R ψ a ≤ K * (b - a)

/-- The exponentially receding perturbation `f(ψ) − ε e^{μt}` of a stationary profile. -/
@[expose] def RadialField.expShift (f f' f'' : ℝ → ℝ) (ε μ : ℝ) : RadialField :=
  ⟨fun ψ t => f ψ - ε * Real.exp (μ * t), fun ψ _ => f' ψ, fun ψ _ => f'' ψ,
    fun _ t => -(ε * (μ * Real.exp (μ * t)))⟩

/-- The perturbation `f − ε e^{μt}` of a regular profile is regular on every rectangle. -/
theorem ProfileRegular.expShift_regular {f f' f'' : ℝ → ℝ} (h : ProfileRegular f f' f'')
    (ε μ τ : ℝ) : (RadialField.expShift f f' f'' ε μ).Regular τ where
  cont := (h.continuousOn.comp continuousOn_fst (fun _ hp => hp.1)).sub
    (by fun_prop : Continuous fun p : ℝ × ℝ => ε * Real.exp (μ * p.2)).continuousOn
  deriv_ψ := fun _ _ ψ hψ => (h.deriv ψ hψ).sub_const _
  deriv_ψψ := fun _ _ ψ hψ => h.deriv2 ψ hψ
  deriv_t := fun ψ _ t _ => by
    have := (((hasDerivAt_id' t).const_mul μ).exp.const_mul ε).const_sub (f ψ)
    convert this.hasDerivWithinAt using 1
    · rfl
    change -(ε * (μ * Real.exp (μ * t))) = _
    ring

/-- **Non-strict lower-barrier theorem** (`ε e^{μt}` argument, semilinear coefficients). If
`R` is one-sided Lipschitz, `N[f] ≥ 0`, `f'(0) = 0`, `f(1) ≤ T_edge(t)` and `f ≤ T(·,0)`, then
`f ≤ T` on `[0,1] × [0,τ]`. -/
theorem le_of_isLowerBarrier {c : RadialCoefficients} {Tedge : ℝ → ℝ} {τ : ℝ}
    {u : RadialField} [hu : RadialHeatTransport c Tedge τ u] {f f' f'' : ℝ → ℝ} {K : ℝ}
    (hsl : c.IsSemilinear) (hK : OneSidedLipschitz c K) (hf : IsLowerBarrier c f f' f'')
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, f ψ ≤ u.T ψ 0) (h1 : ∀ t ∈ Icc 0 τ, f 1 ≤ Tedge t) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ, f ψ ≤ u.T ψ t := by
  intro ψ hψ t ht
  set μ := |K| + 1 with hμ
  have hKμ : K < μ := by linarith [le_abs_self K]
  have key : ∀ ε > 0, f ψ - ε * Real.exp (μ * t) < u.T ψ t := by
    intro ε hε
    have hS : StrictSubsolution c τ (RadialField.expShift f f' f'' ε μ) :=
      { regular := hf.toProfileRegular.expShift_regular ε μ τ
        axis := fun hk _ _ => hf.axis hk
        strict := by
          intro x hx s _
          change -(ε * (μ * Real.exp (μ * s))) <
            c.op x (f x - ε * Real.exp (μ * s)) (f' x) (f'' x)
          have hE := Real.exp_pos (μ * s)
          have hεE : 0 < ε * Real.exp (μ * s) := mul_pos hε hE
          have hL := hK x hx (f x - ε * Real.exp (μ * s)) (f x) (by linarith)
          rw [show f x - (f x - ε * Real.exp (μ * s)) = ε * Real.exp (μ * s) by ring] at hL
          have hop := hsl.op_sub_op hx (f x - ε * Real.exp (μ * s)) (f x) (f' x) (f'' x)
          have hn := hf.nonneg x hx
          have hlt : K * (ε * Real.exp (μ * s)) < μ * (ε * Real.exp (μ * s)) :=
            mul_lt_mul_of_pos_right hKμ hεE
          have heq : ε * (μ * Real.exp (μ * s)) = μ * (ε * Real.exp (μ * s)) := by ring
          linarith }
    refine RadialHeatTransport.lt_of_strictSubsolution (Tedge := Tedge) hS
      (fun x hx => ?_) (fun s hs => ?_)
      ψ hψ t ht
    · change f x - ε * Real.exp (μ * 0) < u.T x 0
      simp only [mul_zero, Real.exp_zero, mul_one]
      linarith [h0 x hx]
    · change f 1 - ε * Real.exp (μ * s) < Tedge s
      linarith [h1 s hs, mul_pos hε (Real.exp_pos (μ * s))]
  refine le_of_forall_pos_lt_add (fun δ hδ => ?_)
  have := key (δ / Real.exp (μ * t)) (div_pos hδ (Real.exp_pos _))
  rw [div_mul_cancel₀ _ (Real.exp_pos _).ne'] at this
  linarith

/-! ### Upper barriers by the symmetry `T ↦ −T`

The mirror trick survives kernel change K2: under `T ↦ −T` the diffusivity becomes
`D(ψ,−v)`, `∂ψD(ψ,−v)`, and the quasilinear coefficient flips sign, `−∂TD(ψ,−v)`, so the
operator stays odd (`RadialCoefficients.op_neg`). The margin upper-barrier theorems are
nevertheless proved directly (`le_of_upperMargin_shift`), without the mirror. -/

/-- Mirrored coefficients: `D(ψ,v)` becomes `D(ψ,−v)` (with `∂ψD(ψ,−v)` and `−∂TD(ψ,−v)`), the
net source `R(ψ,v)` becomes `−R(ψ,−v)` and the source domain `Tdom` becomes `−Tdom`; all other
data are unchanged. `T` solves the problem for `c` iff `−T` solves it for `c.neg`. -/
@[expose] def RadialCoefficients.neg (c : RadialCoefficients) : RadialCoefficients :=
  ⟨c.Vp, c.dVp, fun ψ v => c.D ψ (-v), fun ψ v => c.dD ψ (-v), fun ψ v => -c.dDT ψ (-v),
    fun ψ v => -c.R ψ (-v), Neg.neg ⁻¹' c.Tdom, c.axis⟩

/-- The mirror of semilinear coefficients is semilinear. -/
theorem RadialCoefficients.IsSemilinear.neg {c : RadialCoefficients} (h : c.IsSemilinear) :
    c.neg.IsSemilinear := fun ψ hψ T T' => by
  obtain ⟨h1, h2, h3⟩ := h ψ hψ (-T) (-T')
  exact ⟨h1, h2, by simp [RadialCoefficients.neg, h3]⟩

/-- The negated field `−T`, with negated derivatives. -/
@[expose] def RadialField.neg (u : RadialField) : RadialField :=
  ⟨fun ψ t => -u.T ψ t, fun ψ t => -u.Tψ ψ t, fun ψ t => -u.Tψψ ψ t, fun ψ t => -u.Tt ψ t⟩

/-- The mirrored operator is odd: `N_{c.neg}[−f] = −N_c[f]`. -/
theorem RadialCoefficients.op_neg (c : RadialCoefficients) (ψ a b d : ℝ) :
    c.neg.op ψ (-a) (-b) (-d) = -c.op ψ a b d := by
  simp only [RadialCoefficients.op, RadialCoefficients.neg, neg_neg]; ring

/-- Negation preserves classical regularity. -/
theorem RadialField.Regular.neg {τ : ℝ} {u : RadialField} (h : u.Regular τ) :
    u.neg.Regular τ where
  cont := h.cont.neg
  deriv_ψ := fun t ht ψ hψ => (h.deriv_ψ t ht ψ hψ).neg
  deriv_ψψ := fun t ht ψ hψ => (h.deriv_ψψ t ht ψ hψ).neg
  deriv_t := fun ψ hψ t ht => (h.deriv_t ψ hψ t ht).neg

/-- The mirrored coefficients satisfy the transport laws. -/
instance TransportLaws.neg (c : RadialCoefficients) [h : TransportLaws c] :
    TransportLaws c.neg where
  Vp_pos := h.Vp_pos
  Vp_deriv := h.Vp_deriv
  D_deriv := fun ψ hψ T => h.D_deriv ψ hψ (-T)
  DT_deriv := fun ψ hψ T => by
    have := (h.DT_deriv ψ hψ (-T)).comp T (hasDerivAt_neg T)
    have h2 : HasDerivAt (fun v => c.D ψ (-v)) (c.dDT ψ (-T) * -1) T := this
    change HasDerivAt (fun v => c.D ψ (-v)) (-c.dDT ψ (-T)) T
    convert h2 using 1; ring
  D_nonneg := fun ψ hψ T => h.D_nonneg ψ hψ (-T)
  D_axis := fun hk T => h.D_axis hk (-T)
  D_axis_regular := fun hk T => h.D_axis_regular hk (-T)
  Tdom_open := h.Tdom_open.preimage continuous_neg
  R_cont := (h.R_cont.comp (continuous_fst.prodMk continuous_snd.neg).continuousOn
    (fun _ hp => ⟨hp.1, hp.2⟩)).neg

/-- `−T` is a classical solution for the mirrored coefficients and negated edge data. -/
theorem ClassicalRadialSolution.neg {c : RadialCoefficients} {Tedge : ℝ → ℝ} {τ : ℝ}
    {u : RadialField} (h : ClassicalRadialSolution c Tedge τ u) :
    ClassicalRadialSolution c.neg (fun t => -Tedge t) τ u.neg where
  tau_nonneg := h.tau_nonneg
  regular := h.regular.neg
  pde := fun ψ hψ t ht => by
    change -u.Tt ψ t = c.neg.op ψ (-u.T ψ t) (-u.Tψ ψ t) (-u.Tψψ ψ t)
    rw [c.op_neg, h.pde ψ hψ t ht]
  axis := fun hk t ht => by change -u.Tψ 0 t = 0; rw [h.axis hk t ht, neg_zero]
  edge := fun t ht => by change -u.T 1 t = -Tedge t; rw [h.edge t ht]

/-- The mirror of a radial heat transport solution. -/
theorem RadialHeatTransport.neg {c : RadialCoefficients} {Tedge : ℝ → ℝ} {τ : ℝ}
    {u : RadialField} [h : RadialHeatTransport c Tedge τ u] :
    RadialHeatTransport c.neg (fun t => -Tedge t) τ u.neg :=
  { TransportLaws.neg c, h.toClassicalRadialSolution.neg with }

/-- Negation preserves profile regularity. -/
theorem ProfileRegular.neg {f f' f'' : ℝ → ℝ} (h : ProfileRegular f f' f'') :
    ProfileRegular (fun x => -f x) (fun x => -f' x) (fun x => -f'' x) :=
  ⟨fun ψ hψ => (h.deriv ψ hψ).neg, fun ψ hψ => (h.deriv2 ψ hψ).neg⟩

/-- A strict upper barrier for `c` is, after negation, a strict lower barrier for `c.neg`. -/
theorem IsStrictUpperBarrier.neg {c : RadialCoefficients} {f f' f'' : ℝ → ℝ}
    (hf : IsStrictUpperBarrier c f f' f'') :
    IsStrictLowerBarrier c.neg (fun x => -f x) (fun x => -f' x) (fun x => -f'' x) :=
  { toProfileRegular := hf.toProfileRegular.neg
    axis := fun hk => by simp [hf.axis hk]
    strict := fun ψ hψ => by
      rw [c.op_neg]; linarith [hf.strict ψ hψ] }

/-- An upper barrier for `c` is, after negation, a lower barrier for `c.neg`. -/
theorem IsUpperBarrier.neg {c : RadialCoefficients} {f f' f'' : ℝ → ℝ}
    (hf : IsUpperBarrier c f f' f'') :
    IsLowerBarrier c.neg (fun x => -f x) (fun x => -f' x) (fun x => -f'' x) :=
  { toProfileRegular := hf.toProfileRegular.neg
    axis := fun hk => by simp [hf.axis hk]
    nonneg := fun ψ hψ => by
      rw [c.op_neg]; linarith [hf.nonpos ψ hψ] }

/-- The one-sided Lipschitz bound is invariant under the mirror symmetry. -/
theorem OneSidedLipschitz.neg {c : RadialCoefficients} {K : ℝ} (hK : OneSidedLipschitz c K) :
    OneSidedLipschitz c.neg K := fun ψ hψ a b hab => by
  change -c.R ψ (-b) - -c.R ψ (-a) ≤ K * (b - a)
  have h := hK ψ hψ (-b) (-a) (by linarith)
  rw [show -a - -b = b - a by ring] at h
  linarith

/-- **Strict stationary upper-barrier theorem.** If `N[f] < 0`, `f'(0) = 0`, the edge data stay
strictly below `f(1)` and the initial profile is strictly below `f`, then `T < f` on
`[0,1] × [0,τ]`. -/
theorem gt_of_isStrictUpperBarrier {c : RadialCoefficients} {Tedge : ℝ → ℝ} {τ : ℝ}
    {u : RadialField} [hu : RadialHeatTransport c Tedge τ u] {f f' f'' : ℝ → ℝ}
    (hf : IsStrictUpperBarrier c f f' f'') (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, u.T ψ 0 < f ψ)
    (h1 : ∀ t ∈ Icc 0 τ, Tedge t < f 1) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ, u.T ψ t < f ψ := by
  have := RadialHeatTransport.neg (c := c) (Tedge := Tedge) (τ := τ) (u := u)
  intro ψ hψ t ht
  have h := lt_of_isStrictLowerBarrier (Tedge := fun t => -Tedge t) (u := u.neg) hf.neg
    (fun x hx => by change -f x < -u.T x 0; linarith [h0 x hx])
    (fun s hs => by linarith [h1 s hs]) ψ hψ t ht
  change -f ψ < -u.T ψ t at h
  linarith

/-- **Upper-barrier theorem with uniform margin** (semilinear coefficients; direct proof via
`le_of_upperMargin_shift`): `N[f] ≤ −κ < 0`, `f` in `Tdom`, `f'(0) = 0` (regular axis),
`T_edge ≤ f(1)` and `T(·,0) ≤ f` give `T ≤ f`. -/
theorem le_of_isStrictUpperBarrier_margin {c : RadialCoefficients} {Tedge : ℝ → ℝ} {τ : ℝ}
    {u : RadialField} [hu : RadialHeatTransport c Tedge τ u] {f f' f'' : ℝ → ℝ}
    (hsl : c.IsSemilinear)
    (hf : ProfileRegular f f' f'') (haxis : c.axis = .regular → f' 0 = 0)
    (hdom : ∀ ψ ∈ Icc (0 : ℝ) 1, f ψ ∈ c.Tdom) {κ : ℝ} (hκ : 0 < κ)
    (hmargin : ∀ ψ ∈ Icc (0 : ℝ) 1, c.op ψ (f ψ) (f' ψ) (f'' ψ) ≤ -κ)
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, u.T ψ 0 ≤ f ψ) (h1 : ∀ t ∈ Icc 0 τ, Tedge t ≤ f 1) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ, u.T ψ t ≤ f ψ :=
  le_of_upperMargin_shift hf haxis
    (hsl.opShiftControl hf TransportLaws.Tdom_open TransportLaws.R_cont hdom) hκ hmargin h0 h1

/-- **Non-strict upper-barrier theorem** (mirror of `le_of_isLowerBarrier`, semilinear
coefficients): with a one-sided Lipschitz source, `N[f] ≤ 0`, `f'(0) = 0`, `T_edge ≤ f(1)` and
`T(·,0) ≤ f` give `T ≤ f`. -/
theorem le_of_isUpperBarrier {c : RadialCoefficients} {Tedge : ℝ → ℝ} {τ : ℝ}
    {u : RadialField} [hu : RadialHeatTransport c Tedge τ u] {f f' f'' : ℝ → ℝ} {K : ℝ}
    (hsl : c.IsSemilinear) (hK : OneSidedLipschitz c K) (hf : IsUpperBarrier c f f' f'')
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, u.T ψ 0 ≤ f ψ) (h1 : ∀ t ∈ Icc 0 τ, Tedge t ≤ f 1) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ, u.T ψ t ≤ f ψ := by
  have := RadialHeatTransport.neg (c := c) (Tedge := Tedge) (τ := τ) (u := u)
  intro ψ hψ t ht
  have h := le_of_isLowerBarrier (Tedge := fun t => -Tedge t) (u := u.neg) hsl.neg hK.neg
    hf.neg
    (fun x hx => by change -f x ≤ -u.T x 0; linarith [h0 x hx])
    (fun s hs => by linarith [h1 s hs]) ψ hψ t ht
  change -f ψ ≤ -u.T ψ t at h
  linarith

/-! ### Two-sided barriers -/

/-- **Two-sided strict barrier corollary**: strict lower and upper stationary barriers with
strict initial and edge data trap the temperature in the open band `(f, g)`. -/
theorem mem_Ioo_of_strictBarriers {c : RadialCoefficients} {Tedge : ℝ → ℝ} {τ : ℝ}
    {u : RadialField} [hu : RadialHeatTransport c Tedge τ u] {f f' f'' g g' g'' : ℝ → ℝ}
    (hf : IsStrictLowerBarrier c f f' f'') (hg : IsStrictUpperBarrier c g g' g'')
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, f ψ < u.T ψ 0 ∧ u.T ψ 0 < g ψ)
    (h1 : ∀ t ∈ Icc 0 τ, f 1 < Tedge t ∧ Tedge t < g 1) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ, u.T ψ t ∈ Ioo (f ψ) (g ψ) := fun ψ hψ t ht =>
  ⟨lt_of_isStrictLowerBarrier hf (fun x hx => (h0 x hx).1) (fun s hs => (h1 s hs).1) ψ hψ t ht,
    gt_of_isStrictUpperBarrier hg (fun x hx => (h0 x hx).2) (fun s hs => (h1 s hs).2) ψ hψ t ht⟩

/-- **Two-sided barrier corollary** (non-strict, one-sided Lipschitz source): `T` stays in
`[f, g]` for lower barrier `f` and upper barrier `g`. -/
theorem mem_Icc_of_barriers {c : RadialCoefficients} {Tedge : ℝ → ℝ} {τ : ℝ}
    {u : RadialField} [hu : RadialHeatTransport c Tedge τ u] {f f' f'' g g' g'' : ℝ → ℝ}
    {K : ℝ} (hsl : c.IsSemilinear) (hK : OneSidedLipschitz c K)
    (hf : IsLowerBarrier c f f' f'') (hg : IsUpperBarrier c g g' g'')
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, f ψ ≤ u.T ψ 0 ∧ u.T ψ 0 ≤ g ψ)
    (h1 : ∀ t ∈ Icc 0 τ, f 1 ≤ Tedge t ∧ Tedge t ≤ g 1) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ, u.T ψ t ∈ Icc (f ψ) (g ψ) := fun ψ hψ t ht =>
  ⟨le_of_isLowerBarrier hsl hK hf (fun x hx => (h0 x hx).1) (fun s hs => (h1 s hs).1) ψ hψ t
      ht,
    le_of_isUpperBarrier hsl hK hg (fun x hx => (h0 x hx).2) (fun s hs => (h1 s hs).2) ψ hψ t
      ht⟩

/-- **For all time.** If the supplied field is a solution on every horizon `[0,τ]`, a lower
barrier (non-strict, one-sided Lipschitz source) bounds it for all `t ≥ 0`. -/
theorem le_of_isLowerBarrier_forall_time {c : RadialCoefficients} {Tedge : ℝ → ℝ}
    {u : RadialField} (hu : ∀ τ, 0 ≤ τ → RadialHeatTransport c Tedge τ u)
    {f f' f'' : ℝ → ℝ} {K : ℝ} (hsl : c.IsSemilinear) (hK : OneSidedLipschitz c K)
    (hf : IsLowerBarrier c f f' f'')
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, f ψ ≤ u.T ψ 0) (h1 : ∀ t, 0 ≤ t → f 1 ≤ Tedge t) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → f ψ ≤ u.T ψ t := fun ψ hψ t ht => by
  have := hu t ht
  exact le_of_isLowerBarrier (τ := t) hsl hK hf h0 (fun s hs => h1 s hs.1) ψ hψ t
    ⟨ht, le_rfl⟩

/-! ### Sanity corollaries -/

section ModeField

open Real

/-- The separable mode `a + b e^{μt} cos(kψ)` with its exact partial derivatives (used for
explicit solutions in the sanity corollaries below). -/
@[expose] def modeField (a b μ k : ℝ) : RadialField where
  T ψ t := a + b * exp (μ * t) * cos (k * ψ)
  Tψ ψ t := -(b * exp (μ * t) * k * sin (k * ψ))
  Tψψ ψ t := -(b * exp (μ * t) * k ^ 2 * cos (k * ψ))
  Tt ψ t := b * μ * exp (μ * t) * cos (k * ψ)

/-- The separable mode is regular on every rectangle. -/
theorem modeField_regular (a b μ k τ : ℝ) : (modeField a b μ k).Regular τ where
  cont := by
    apply Continuous.continuousOn
    simp only [modeField]
    fun_prop
  deriv_ψ := fun t _ ψ _ => by
    have := (((hasDerivAt_id' ψ).const_mul k).cos.const_mul (b * exp (μ * t))).const_add a
    convert this.hasDerivWithinAt using 1
    · rfl
    change -(b * exp (μ * t) * k * sin (k * ψ)) = _
    ring
  deriv_ψψ := fun t _ ψ _ => by
    have := (((hasDerivAt_id' ψ).const_mul k).sin.const_mul (b * exp (μ * t) * k)).neg
    convert this.hasDerivWithinAt using 1
    · rfl
    · change -(b * exp (μ * t) * k ^ 2 * cos (k * ψ)) = _
      ring
  deriv_t := fun ψ _ t _ => by
    have := ((((hasDerivAt_id' t).const_mul μ).exp.const_mul b).mul_const
      (cos (k * ψ))).const_add a
    convert this.hasDerivWithinAt using 1
    · rfl
    change b * μ * exp (μ * t) * cos (k * ψ) = _
    ring

end ModeField

/-- A constant level `m` at which heating strictly exceeds losses everywhere is a strict lower
barrier. -/
theorem constant_isStrictLowerBarrier (c : RadialCoefficients) {m : ℝ}
    (hR : ∀ ψ ∈ Icc (0 : ℝ) 1, 0 < c.R ψ m) :
    IsStrictLowerBarrier c (fun _ => m) (fun _ => 0) (fun _ => 0) :=
  { deriv := fun _ _ => hasDerivWithinAt_const _ _ _
    deriv2 := fun _ _ => hasDerivWithinAt_const _ _ _
    axis := fun _ => rfl
    strict := fun ψ hψ => by simpa [RadialCoefficients.op] using hR ψ hψ }

/-- **Constant barrier.** If heating strictly exceeds losses at the level `m` on every surface,
and the initial and edge temperatures exceed `m`, the temperature stays above `m`. -/
theorem lt_of_heating_exceeds_losses {c : RadialCoefficients} {Tedge : ℝ → ℝ} {τ : ℝ}
    {u : RadialField} [hu : RadialHeatTransport c Tedge τ u] {m : ℝ}
    (hR : ∀ ψ ∈ Icc (0 : ℝ) 1, 0 < c.R ψ m) (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, m < u.T ψ 0)
    (h1 : ∀ t ∈ Icc 0 τ, m < Tedge t) : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ, m < u.T ψ t :=
  lt_of_isStrictLowerBarrier (constant_isStrictLowerBarrier c hR) h0 h1

/-- **Constant barrier, non-strict.** With a one-sided Lipschitz source and heating at least
balancing losses at level `m`, initial and edge temperatures `≥ m` stay `≥ m`. -/
theorem le_of_heating_balances_losses {c : RadialCoefficients} {Tedge : ℝ → ℝ} {τ : ℝ}
    {u : RadialField} [hu : RadialHeatTransport c Tedge τ u] {m K : ℝ}
    (hsl : c.IsSemilinear) (hK : OneSidedLipschitz c K)
    (hR : ∀ ψ ∈ Icc (0 : ℝ) 1, 0 ≤ c.R ψ m) (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, m ≤ u.T ψ 0)
    (h1 : ∀ t ∈ Icc 0 τ, m ≤ Tedge t) : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ, m ≤ u.T ψ t :=
  le_of_isLowerBarrier (f := fun _ => m) (f' := fun _ => 0) (f'' := fun _ => 0) hsl hK
    { deriv := fun _ _ => hasDerivWithinAt_const _ _ _
      deriv2 := fun _ _ => hasDerivWithinAt_const _ _ _
      axis := fun _ => rfl
      nonneg := fun ψ hψ => by simpa [RadialCoefficients.op] using hR ψ hψ } h0 h1

/-- **Degenerate diffusion.** The strict comparison needs no diffusivity floor: it holds for a
pure reaction model `D ≡ 0` (each surface evolving as an ODE) with a regular axis. (A
diffusivity floor `Dmin > 0`, removed from the kernel on 2026-10-20, matters for
existence/regularity theory, not for this comparison.) -/
theorem lt_of_strictSubsolution_pureReaction {c : RadialCoefficients} {Tedge : ℝ → ℝ} {τ : ℝ}
    {u S : RadialField} (hD0 : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ T : ℝ, c.D ψ T = 0)
    (hk : c.axis = .regular)
    (hu : ClassicalRadialSolution c Tedge τ u) (hS : StrictSubsolution c τ S)
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, S.T ψ 0 < u.T ψ 0) (h1 : ∀ t ∈ Icc 0 τ, S.T 1 t < Tedge t) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ, S.T ψ t < u.T ψ t :=
  lt_of_strictSubsolution (fun ψ hψ T => (hD0 ψ hψ T).ge) (fun h => absurd (hk.symm.trans h)
    (by decide)) hu hS h0 h1

/-- Backward-diffusion coefficients (`D = −1`, `V' = 1`, no sources, regular axis): ellipticity
fails. -/
@[expose] def backwardCoefficients : RadialCoefficients :=
  .semilinear (fun _ => 1) (fun _ => 0) (fun _ => -1) (fun _ => 0) (fun _ _ => 0) univ .regular

/-- **The sign `D ≥ 0` cannot be dropped.** For backward diffusion `∂ₜT = −∂ψψT` the solution
`T = 2 − e^{π²t/4} cos(πψ/2)` starts above the strict subsolution `S = −ψ²` (`N[S] = 2 > 0`,
`S'(0) = 0`), stays above it at the edge, yet `T(0,1) = 2 − e^{π²/4} < 0 = S(0)`. -/
theorem backward_diffusion_counterexample :
    ∃ (c : RadialCoefficients) (Tedge : ℝ → ℝ) (u S : RadialField),
      ClassicalRadialSolution c Tedge 1 u ∧ StrictSubsolution c 1 S ∧
      (∀ ψ ∈ Icc (0 : ℝ) 1, S.T ψ 0 < u.T ψ 0) ∧ (∀ t ∈ Icc (0 : ℝ) 1, S.T 1 t < Tedge t) ∧
      ¬ (∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, S.T ψ t < u.T ψ t) := by
  have hS : ProfileRegular (fun ψ => -ψ ^ 2) (fun ψ => -(2 * ψ)) (fun _ => -2) :=
    ⟨fun ψ _ => by
      convert ((hasDerivAt_pow 2 ψ).neg).hasDerivWithinAt using 1
      simp,
     fun ψ _ => by
      convert (((hasDerivAt_id' ψ).const_mul 2).neg).hasDerivWithinAt using 1
      · ring⟩
  refine ⟨backwardCoefficients, fun _ => 2, modeField 2 (-1) (Real.pi ^ 2 / 4)
    (Real.pi / 2), RadialField.stationary _ _ _, ?_, ⟨hS.stationary_regular 1, ?_, ?_⟩,
    ?_, ?_, ?_⟩
  · exact
    { tau_nonneg := zero_le_one
      regular := modeField_regular _ _ _ _ _
      pde := fun ψ _ t _ => by
        simp only [modeField, backwardCoefficients, RadialCoefficients.semilinear_op]
        ring
      axis := fun _ t _ => by simp [modeField]
      edge := fun t _ => by simp [modeField, Real.cos_pi_div_two] }
  · intro _ t _
    change -(2 * (0 : ℝ)) = 0
    simp
  · intro ψ _ t _
    change (0 : ℝ) < backwardCoefficients.op ψ (-ψ ^ 2) (-(2 * ψ)) (-2)
    simp only [backwardCoefficients, RadialCoefficients.semilinear_op]
    norm_num
  · intro ψ _
    change -ψ ^ 2 < 2 + -1 * Real.exp (Real.pi ^ 2 / 4 * 0) * Real.cos (Real.pi / 2 * ψ)
    simp only [mul_zero, Real.exp_zero, mul_one]
    nlinarith [Real.cos_le_one (Real.pi / 2 * ψ), sq_nonneg ψ]
  · intro t _
    change -(1 : ℝ) ^ 2 < 2
    norm_num
  · intro h
    have h' := h 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩
    change -(0 : ℝ) ^ 2 < 2 + -1 * Real.exp (Real.pi ^ 2 / 4 * 1) * Real.cos (Real.pi / 2 * 0)
      at h'
    simp only [mul_zero, Real.cos_zero, mul_one] at h'
    have hpi := Real.two_le_pi
    have hexp := Real.add_one_lt_exp (x := Real.pi ^ 2 / 4) (by positivity)
    nlinarith

/-- Relaxation coefficients: `V' = 1`, `D = 1`, `R(ψ,v) = 1 − v` (unit heating, linear loss),
source posed for all temperatures, regular axis. -/
@[expose] def relaxCoefficients : RadialCoefficients :=
  .semilinear (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 0) (fun _ v => 1 - v) univ .regular

/-- The relaxation coefficients satisfy the transport laws. -/
instance : TransportLaws relaxCoefficients where
  Vp_pos := fun _ _ => one_pos
  Vp_deriv := fun _ _ => hasDerivWithinAt_const _ _ _
  D_deriv := fun _ _ _ => hasDerivWithinAt_const _ _ _
  DT_deriv := fun _ _ T => hasDerivAt_const T _
  D_nonneg := fun _ _ _ => zero_le_one
  D_axis := fun h => absurd h (by decide)
  D_axis_regular := fun _ _ => one_pos
  Tdom_open := isOpen_univ
  R_cont := (continuous_const.sub continuous_snd).continuousOn

/-- The relaxation source `1 − v` is one-sided Lipschitz with constant `0` (it is
nonincreasing in the temperature). -/
theorem relaxCoefficients_oneSidedLipschitz : OneSidedLipschitz relaxCoefficients 0 :=
  fun _ _ a b hab => by
    change (1 - b) - (1 - a) ≤ 0 * (b - a)
    linarith

/-- The explicit decaying mode `T = 1 + e^{−(1+π²/4)t} cos(πψ/2)` solves the relaxation problem
with edge temperature `1` on every horizon. -/
theorem relaxMode_radialHeatTransport {τ : ℝ} (hτ : 0 ≤ τ) :
    RadialHeatTransport relaxCoefficients (fun _ => 1) τ
      (modeField 1 1 (-(1 + Real.pi ^ 2 / 4)) (Real.pi / 2)) where
  tau_nonneg := hτ
  regular := modeField_regular _ _ _ _ _
  pde := fun ψ _ t _ => by
    simp only [modeField, relaxCoefficients, RadialCoefficients.semilinear_op]
    ring
  axis := fun _ t _ => by simp [modeField]
  edge := fun t _ => by simp [modeField, Real.cos_pi_div_two]

/-- The explicit non-constant profile `f = 1/4 − ψ²/8` is a strict lower barrier for the
relaxation problem: `N[f] = 1/2 + ψ²/8 > 0` and `f'(0) = 0`. -/
theorem relax_isStrictLowerBarrier :
    IsStrictLowerBarrier relaxCoefficients (fun ψ => 1 / 4 - ψ ^ 2 / 8) (fun ψ => -(ψ / 4))
      (fun _ => -(1 / 4)) :=
  { deriv := fun ψ _ => by
      convert (((hasDerivAt_pow 2 ψ).div_const 8).const_sub (1 / 4)).hasDerivWithinAt using 1
      simp; ring
    deriv2 := fun ψ _ => by
      convert (((hasDerivAt_id' ψ).div_const 4).neg).hasDerivWithinAt using 1
    axis := fun _ => by norm_num
    strict := fun ψ _ => by
      simp only [relaxCoefficients, RadialCoefficients.semilinear_op]
      nlinarith [sq_nonneg ψ] }

/-- **Non-vacuity of the barrier theorem.** All hypotheses of `lt_of_isStrictLowerBarrier` hold
for the explicit decaying solution and the explicit barrier, so the temperature stays above
`1/4 − ψ²/8` on every horizon. -/
theorem relax_nonvacuous {τ : ℝ} (hτ : 0 ≤ τ) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ, 1 / 4 - ψ ^ 2 / 8 <
      (modeField 1 1 (-(1 + Real.pi ^ 2 / 4)) (Real.pi / 2)).T ψ t := by
  have := relaxMode_radialHeatTransport hτ
  refine lt_of_isStrictLowerBarrier (Tedge := fun _ => 1) relax_isStrictLowerBarrier
    (fun ψ hψ => ?_) (fun t _ => by norm_num)
  change 1 / 4 - ψ ^ 2 / 8 <
    1 + 1 * Real.exp (-(1 + Real.pi ^ 2 / 4) * 0) * Real.cos (Real.pi / 2 * ψ)
  have hc : 0 ≤ Real.cos (Real.pi / 2 * ψ) := Real.cos_nonneg_of_mem_Icc
    ⟨by nlinarith [Real.pi_pos, hψ.1], by nlinarith [Real.pi_pos, hψ.2]⟩
  simp only [mul_zero, Real.exp_zero, mul_one, one_mul]
  nlinarith [sq_nonneg ψ]

end PlasmaLean.Transport
