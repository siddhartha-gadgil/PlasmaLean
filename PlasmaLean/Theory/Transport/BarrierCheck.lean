/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Transport.Comparison
public import PlasmaLean.Certificates.PolyInterval

/-!
# Barrier comparison with a degenerate axis, and a rational piecewise barrier checker

## Why a degenerate-axis comparison theorem

In the normalized toroidal flux coordinate `ψ` the flux-surface-averaged diffusivity is
`D(ψ) = χ ⟨|∇ψ|²⟩`, and `⟨|∇ψ|²⟩ ∝ ψ` near the magnetic axis (for a cylinder `ψ = r²/a²`
gives `|∇ψ|² = 4ψ/a²` exactly). So `D(0) = 0`: the kernel floor `D ≥ Dmin > 0` of
`TransportLaws` never holds in this coordinate, and the axis Neumann condition `∂ψT(0,t) = 0`
of `ClassicalRadialSolution` is *not* the natural regularity condition either (a smooth
profile `T₀ − c r²` has `∂ψT(0) = −c a² ≠ 0`). At a degenerate axis no boundary condition is
needed at all (Fichera): if `D(0) = 0` and the drift coefficient `D'(0) ≥ 0`, the equation at
`ψ = 0` reduces to `∂ₜT = D'(0) ∂ψT + R`, whose characteristics `dψ/dt = −D'(0) ≤ 0` run
*toward* the axis: `ψ = 0` is an outflow boundary, so its values are determined from the
interior and no boundary condition may be prescribed there.

This module proves the comparison principle in exactly that setting:

* `DegenerateAxis c`: `D(0) = 0` and `D'(0) ≥ 0`.
* `AxisFreeSolution c Tedge τ u`: a classical solution as in `ClassicalRadialSolution`, but
  **without** the axis condition (`ClassicalRadialSolution.axisFree` shows that every kernel
  solution is one).
* `lt_of_residual_lt`: the first-touching argument for two regular fields `S`, `u` with
  `∂ₜS − N[S] < ∂ₜu − N[u]`, `S < u` initially and at the edge. Only `D ≥ 0` on `[0,1]` and
  `DegenerateAxis` are used; neither field needs an axis condition. The new ingredient is
  `op_le_op_of_touch_axis`: at a zero minimum of `u − S` at the axis, the one-sided slope of
  `u − S` is `≥ 0` and the drift `D'(0) ≥ 0` gives `N[S](0) ≤ N[u](0)`.
* Stationary barriers with a uniform margin and non-strict data, for lower and upper barriers
  (`le_of_lowerMargin_axisFree`, `le_of_upperMargin_axisFree`) and for all time
  (`*_forall_time`). The source `R` is only required to be continuous on
  `[0,1] × (lo, ∞)`, with the barrier above `lo` (e.g. `lo = 0` for sources involving `√T`
  and a reactivity defined only for `T > 0`).

## Rational piecewise barrier checker

`pieceCheck Q T κ bonus a ps` checks a list of pieces `(dᵢ, kᵢ)` covering `[a, d_last]`: on
the piece `[dᵢ₋₁, dᵢ]` the Horner lower bound of the Taylor-shifted polynomial `Q` is at least
`κ − bonus kᵢ`, and the profile polynomial `T` satisfies `T(dᵢ) ≥ kᵢ`. `pieceCheck_sound`:
if `T` is antitone, every real point `x` of the covered interval lies in a piece with
`T(x) ≥ kᵢ` and `Q(x) ≥ κ − bonus kᵢ`. In applications `Q` is an exact polynomial lower
bound for the transport operator *without* a temperature-dependent heating term, and
`bonus k` is a lower bound for that heating term valid whenever `T ≥ k` (for instance alpha
heating with a reactivity floor from Bosch–Hale windows).
-/

public section

noncomputable section

namespace PlasmaLean.Transport

open Set Filter Topology

/-! ### Degenerate axis -/

/-- **Degenerate (Fichera) axis condition**: the diffusivity vanishes at the axis and the
drift coefficient `D'(0)` there is nonnegative, so that no axis boundary condition is needed.
Holds for `D(ψ) = χ ⟨|∇ψ|²⟩` in the normalized toroidal flux coordinate. -/
structure DegenerateAxis (c : RadialCoefficients) : Prop where
  /-- `D(0) = 0`. -/
  D_zero : c.D 0 = 0
  /-- `D'(0) ≥ 0`. -/
  drift_nonneg : 0 ≤ c.dD 0

/-- A supplied classical solution of `∂ₜT = N[T]` on `[0,1] × [0,τ]` with edge Dirichlet data
and **no** axis condition (appropriate when the axis is degenerate). -/
structure AxisFreeSolution (c : RadialCoefficients) (Tedge : ℝ → ℝ) (τ : ℝ)
    (u : RadialField) : Prop where
  /-- The time horizon is nonnegative. -/
  tau_nonneg : 0 ≤ τ
  /-- Classical regularity on the closed rectangle. -/
  regular : u.Regular τ
  /-- The transport equation holds pointwise, including at the axis and the edge. -/
  pde : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ,
    u.Tt ψ t = c.op ψ (u.T ψ t) (u.Tψ ψ t) (u.Tψψ ψ t)
  /-- Edge Dirichlet condition. -/
  edge : ∀ t ∈ Icc 0 τ, u.T 1 t = Tedge t

/-- Every kernel classical solution is an axis-free solution (forget the axis condition). -/
theorem ClassicalRadialSolution.axisFree {c : RadialCoefficients} {Tedge : ℝ → ℝ} {τ : ℝ}
    {u : RadialField} (h : ClassicalRadialSolution c Tedge τ u) :
    AxisFreeSolution c Tedge τ u :=
  ⟨h.tau_nonneg, h.regular, h.pde, h.edge⟩

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

/-- **Touching at a degenerate axis.** If `u − S` has a zero minimum over `[0,1]` at `ψ = 0`,
then `N[S](0) ≤ N[u](0)`: the curvature term is switched off by `D(0) = 0`, and the drift
term has the right sign because the one-sided slope of `u − S` is `≥ 0`. -/
theorem op_le_op_of_touch_axis (c : RadialCoefficients) (hax : DegenerateAxis c)
    {uT sT : ℝ → ℝ} {uψ sψ uψψ sψψ : ℝ}
    (hu : HasDerivWithinAt uT uψ (Icc 0 1) 0) (hs : HasDerivWithinAt sT sψ (Icc 0 1) 0)
    (hmin : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ uT x - sT x) (hzero : uT 0 = sT 0) :
    c.op 0 (sT 0) sψ sψψ ≤ c.op 0 (uT 0) uψ uψψ := by
  have hslope : 0 ≤ uψ - sψ :=
    deriv_nonneg_of_leftEndMin (f := fun x => uT x - sT x) zero_lt_one (hu.sub hs)
      (fun x hx => by simp only [hzero, sub_self]; exact hmin x hx)
  unfold RadialCoefficients.op
  rw [hax.D_zero, hzero]
  simp only [zero_mul, zero_div, add_zero, zero_add]
  nlinarith [mul_nonneg hax.drift_nonneg hslope]

/-- **Touching at an interior point.** If `u − S` has a zero minimum over `[0,1]` at
`ψ₀ ∈ (0,1)` and `D(ψ₀) ≥ 0`, then `N[S](ψ₀) ≤ N[u](ψ₀)`. -/
theorem op_le_op_of_touch_interior (c : RadialCoefficients) {uT uψ uψψ sT sψ sψψ : ℝ → ℝ}
    {ψ₀ : ℝ} (h0 : 0 < ψ₀) (h1 : ψ₀ < 1) (hD : 0 ≤ c.D ψ₀)
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
  unfold RadialCoefficients.op
  rw [hzero, hs2]
  nlinarith [mul_le_mul_of_nonneg_left hcurv hD]

/-- **Comparison by residuals, degenerate axis** (first-touching-time argument). Let `S`, `u`
be regular fields on `[0,1] × [0,τ]` whose residuals satisfy `∂ₜS − N[S] < ∂ₜu − N[u]`
pointwise. If `S < u` initially and at the edge, then `S < u` on the whole rectangle. Only
`D ≥ 0` on `[0,1]` and `DegenerateAxis c` are used; no axis condition is imposed on either
field. (Lower barriers: `S` a strict subsolution, `u` a solution; upper barriers: `S` a
solution, `u` a strict supersolution.) -/
theorem lt_of_residual_lt {c : RadialCoefficients} {τ : ℝ} {u S : RadialField}
    (hD : ∀ ψ ∈ Icc (0 : ℝ) 1, 0 ≤ c.D ψ) (hax : DegenerateAxis c)
    (hu : u.Regular τ) (hS : S.Regular τ)
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
        (sψψ := fun x => S.Tψψ x ts) h hψs1 (hD ψs hψs) (hu.deriv_ψ ts hts)
        (hu.deriv_ψψ ts hts ψs hψs) (hS.deriv_ψ ts hts) (hS.deriv_ψψ ts hts ψs hψs) hmin hzero
    · subst h
      exact op_le_op_of_touch_axis c hax (hu.deriv_ψ ts hts 0 hψs) (hS.deriv_ψ ts hts 0 hψs)
        hmin hzero
  have hcross : S.Tt ψs ts < u.Tt ψs ts := by linarith [hres ψs hψs ts hts]
  have htd : u.Tt ψs ts - S.Tt ψs ts ≤ 0 :=
    deriv_nonpos_of_leftMin hts0 hts.2
      ((hu.deriv_t ψs hψs ts hts).sub (hS.deriv_t ψs hψs ts hts))
      (fun t ht => by
        change u.T ψs ts - S.T ψs ts ≤ u.T ψs t - S.T ψs t
        rw [hzero, sub_self]
        exact (sub_pos.2 (hgood t ⟨ht.1, ht.2.le.trans hts.2⟩ ht.2 ψs hψs)).le)
  linarith

/-! ### Stationary barriers with a margin -/

/-- Shared compactness step for the margin theorems: a regular profile `f` above `lo` on
`[0,1]`, and `R` continuous on `[0,1] × (lo,∞)`, give `δ₀ > 0` such that shifting the value
argument by any `|s| < δ₀` (staying in the band) changes `R(ψ, f ψ)` by less than `κ`. -/
theorem exists_shift_control {c : RadialCoefficients} {f f' f'' : ℝ → ℝ}
    (hf : ProfileRegular f f' f'') {lo : ℝ}
    (hRc : ContinuousOn (fun p : ℝ × ℝ => c.R p.1 p.2) (Icc 0 1 ×ˢ Ioi lo))
    (hlo : ∀ ψ ∈ Icc (0 : ℝ) 1, lo < f ψ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ δ₀ > 0, ∀ s : ℝ, |s| < δ₀ → ∀ ψ ∈ Icc (0 : ℝ) 1,
      |c.R ψ (f ψ + s) - c.R ψ (f ψ)| < κ := by
  obtain ⟨γ, hγ, hγle⟩ := exists_margin_of_continuousOn (g := fun x => f x - lo)
    (hf.continuousOn.sub continuousOn_const) (fun ψ hψ => sub_pos.2 (hlo ψ hψ))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  have hRuc : UniformContinuousOn (fun p : ℝ × ℝ => c.R p.1 p.2)
      (Icc (0 : ℝ) 1 ×ˢ Icc (lo + γ / 2) (M + 1)) :=
    (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
      (hRc.mono (prod_mono subset_rfl (fun x hx => by
        simp only [mem_Ioi]; linarith [hx.1])))
  rw [Metric.uniformContinuousOn_iff] at hRuc
  obtain ⟨δ0, hδ0, hδ⟩ := hRuc κ hκ
  refine ⟨min δ0 (min (γ / 2) 1), by positivity, fun s hs ψ hψ => ?_⟩
  have hs1 := lt_min_iff.1 hs
  have hs2 := lt_min_iff.1 hs1.2
  have habs := abs_lt.1 hs2.1
  have habs' := abs_lt.1 hs2.2
  have hfM := abs_le.1 (by simpa [Real.norm_eq_abs] using hM ψ hψ)
  have hfγ : γ ≤ f ψ - lo := hγle ψ hψ
  have hd := hδ (ψ, f ψ + s) ⟨hψ, by constructor <;> linarith⟩ (ψ, f ψ)
    ⟨hψ, by constructor <;> linarith⟩
    (by
      rw [Prod.dist_eq, dist_self, Real.dist_eq, show f ψ + s - f ψ = s by ring]
      rw [max_eq_right (abs_nonneg s)]; exact hs1.1)
  rwa [Real.dist_eq] at hd

/-- **Lower barrier with margin, degenerate axis.** Let `f` be a regular profile (no axis
condition needed) with `N[f] ≥ κ > 0` on `[0,1]`, `f > lo`, and `R` continuous on
`[0,1] × (lo, ∞)`. Then every axis-free classical solution with `f ≤ T(·,0)` and
`f(1) ≤ T_edge(t)` satisfies `f ≤ T` on `[0,1] × [0,τ]`. -/
theorem le_of_lowerMargin_axisFree {c : RadialCoefficients} {Tedge : ℝ → ℝ} {τ : ℝ}
    {u : RadialField} (hD : ∀ ψ ∈ Icc (0 : ℝ) 1, 0 ≤ c.D ψ) (hax : DegenerateAxis c)
    (hu : AxisFreeSolution c Tedge τ u) {f f' f'' : ℝ → ℝ} (hf : ProfileRegular f f' f'')
    {lo : ℝ} (hRc : ContinuousOn (fun p : ℝ × ℝ => c.R p.1 p.2) (Icc 0 1 ×ˢ Ioi lo))
    (hlo : ∀ ψ ∈ Icc (0 : ℝ) 1, lo < f ψ) {κ : ℝ} (hκ : 0 < κ)
    (hmargin : ∀ ψ ∈ Icc (0 : ℝ) 1, κ ≤ c.op ψ (f ψ) (f' ψ) (f'' ψ))
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, f ψ ≤ u.T ψ 0) (h1 : ∀ t ∈ Icc 0 τ, f 1 ≤ Tedge t) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ, f ψ ≤ u.T ψ t := by
  obtain ⟨δ₀, hδ₀, hctrl⟩ := exists_shift_control hf hRc hlo hκ
  have key : ∀ δ, 0 < δ → δ < δ₀ →
      ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ, f ψ - δ < u.T ψ t := by
    intro δ hδ hδlt
    have hreg : (RadialField.stationary (fun x => f x - δ) f' f'').Regular τ :=
      (ProfileRegular.stationary_regular
        ⟨fun ψ hψ => (hf.deriv ψ hψ).sub_const δ, hf.deriv2⟩ τ)
    refine lt_of_residual_lt (S := RadialField.stationary (fun x => f x - δ) f' f'') hD hax
      hu.regular hreg (fun ψ hψ t ht => ?_) (fun ψ hψ => by
        change f ψ - δ < u.T ψ 0; linarith [h0 ψ hψ])
      (fun t ht => by change f 1 - δ < u.T 1 t; rw [hu.edge t ht]; linarith [h1 t ht])
    have hc := abs_lt.1 (hctrl (-δ) (by rw [abs_neg, abs_of_pos hδ]; exact hδlt) ψ hψ)
    have h2 := c.op_sub_op ψ (f ψ + -δ) (f ψ) (f' ψ) (f'' ψ)
    have h3 := hmargin ψ hψ
    rw [hu.pde ψ hψ t ht]
    change 0 - c.op ψ (f ψ - δ) (f' ψ) (f'' ψ) < _
    rw [show f ψ - δ = f ψ + -δ by ring]
    linarith
  intro ψ hψ t ht
  refine le_of_forall_pos_lt_add (fun ε hε => ?_)
  have := key (min ε δ₀ / 2) (by positivity) (by linarith [min_le_right ε δ₀]) ψ hψ t ht
  linarith [min_le_left ε δ₀]

/-- **Upper barrier with margin, degenerate axis.** Let `g` be a regular profile with
`N[g] ≤ −κ < 0` on `[0,1]`, `g > lo`, and `R` continuous on `[0,1] × (lo, ∞)`. Then every
axis-free classical solution with `T(·,0) ≤ g` and `T_edge(t) ≤ g(1)` satisfies `T ≤ g` on
`[0,1] × [0,τ]`. -/
theorem le_of_upperMargin_axisFree {c : RadialCoefficients} {Tedge : ℝ → ℝ} {τ : ℝ}
    {u : RadialField} (hD : ∀ ψ ∈ Icc (0 : ℝ) 1, 0 ≤ c.D ψ) (hax : DegenerateAxis c)
    (hu : AxisFreeSolution c Tedge τ u) {g g' g'' : ℝ → ℝ} (hg : ProfileRegular g g' g'')
    {lo : ℝ} (hRc : ContinuousOn (fun p : ℝ × ℝ => c.R p.1 p.2) (Icc 0 1 ×ˢ Ioi lo))
    (hlo : ∀ ψ ∈ Icc (0 : ℝ) 1, lo < g ψ) {κ : ℝ} (hκ : 0 < κ)
    (hmargin : ∀ ψ ∈ Icc (0 : ℝ) 1, c.op ψ (g ψ) (g' ψ) (g'' ψ) ≤ -κ)
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, u.T ψ 0 ≤ g ψ) (h1 : ∀ t ∈ Icc 0 τ, Tedge t ≤ g 1) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ, u.T ψ t ≤ g ψ := by
  obtain ⟨δ₀, hδ₀, hctrl⟩ := exists_shift_control hg hRc hlo hκ
  have key : ∀ δ, 0 < δ → δ < δ₀ →
      ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc 0 τ, u.T ψ t < g ψ + δ := by
    intro δ hδ hδlt
    have hreg : (RadialField.stationary (fun x => g x + δ) g' g'').Regular τ :=
      (ProfileRegular.stationary_regular
        ⟨fun ψ hψ => (hg.deriv ψ hψ).add_const δ, hg.deriv2⟩ τ)
    refine lt_of_residual_lt (u := RadialField.stationary (fun x => g x + δ) g' g'') hD hax
      hreg hu.regular (fun ψ hψ t ht => ?_) (fun ψ hψ => by
        change u.T ψ 0 < g ψ + δ; linarith [h0 ψ hψ])
      (fun t ht => by change u.T 1 t < g 1 + δ; rw [hu.edge t ht]; linarith [h1 t ht])
    have hc := abs_lt.1 (hctrl δ (by rw [abs_of_pos hδ]; exact hδlt) ψ hψ)
    have h2 := c.op_sub_op ψ (g ψ + δ) (g ψ) (g' ψ) (g'' ψ)
    have h3 := hmargin ψ hψ
    rw [hu.pde ψ hψ t ht]
    change _ < 0 - c.op ψ (g ψ + δ) (g' ψ) (g'' ψ)
    linarith
  intro ψ hψ t ht
  refine le_of_forall_pos_lt_add (fun ε hε => ?_)
  have := key (min ε δ₀ / 2) (by positivity) (by linarith [min_le_right ε δ₀]) ψ hψ t ht
  linarith [min_le_left ε δ₀]

/-- **Lower barrier for all time, degenerate axis.** If the supplied field is an axis-free
classical solution on every horizon `[0,τ]`, the conclusion of `le_of_lowerMargin_axisFree`
holds for all `t ≥ 0`. -/
theorem le_of_lowerMargin_axisFree_forall_time {c : RadialCoefficients} {Tedge : ℝ → ℝ}
    {u : RadialField} (hD : ∀ ψ ∈ Icc (0 : ℝ) 1, 0 ≤ c.D ψ) (hax : DegenerateAxis c)
    (hu : ∀ τ, 0 ≤ τ → AxisFreeSolution c Tedge τ u) {f f' f'' : ℝ → ℝ}
    (hf : ProfileRegular f f' f'') {lo : ℝ}
    (hRc : ContinuousOn (fun p : ℝ × ℝ => c.R p.1 p.2) (Icc 0 1 ×ˢ Ioi lo))
    (hlo : ∀ ψ ∈ Icc (0 : ℝ) 1, lo < f ψ) {κ : ℝ} (hκ : 0 < κ)
    (hmargin : ∀ ψ ∈ Icc (0 : ℝ) 1, κ ≤ c.op ψ (f ψ) (f' ψ) (f'' ψ))
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, f ψ ≤ u.T ψ 0) (h1 : ∀ t, 0 ≤ t → f 1 ≤ Tedge t) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → f ψ ≤ u.T ψ t := fun ψ hψ t ht =>
  le_of_lowerMargin_axisFree hD hax (hu t ht) hf hRc hlo hκ hmargin h0
    (fun s hs => h1 s hs.1) ψ hψ t ⟨ht, le_rfl⟩

/-- **Upper barrier for all time, degenerate axis.** -/
theorem le_of_upperMargin_axisFree_forall_time {c : RadialCoefficients} {Tedge : ℝ → ℝ}
    {u : RadialField} (hD : ∀ ψ ∈ Icc (0 : ℝ) 1, 0 ≤ c.D ψ) (hax : DegenerateAxis c)
    (hu : ∀ τ, 0 ≤ τ → AxisFreeSolution c Tedge τ u) {g g' g'' : ℝ → ℝ}
    (hg : ProfileRegular g g' g'') {lo : ℝ}
    (hRc : ContinuousOn (fun p : ℝ × ℝ => c.R p.1 p.2) (Icc 0 1 ×ˢ Ioi lo))
    (hlo : ∀ ψ ∈ Icc (0 : ℝ) 1, lo < g ψ) {κ : ℝ} (hκ : 0 < κ)
    (hmargin : ∀ ψ ∈ Icc (0 : ℝ) 1, c.op ψ (g ψ) (g' ψ) (g'' ψ) ≤ -κ)
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, u.T ψ 0 ≤ g ψ) (h1 : ∀ t, 0 ≤ t → Tedge t ≤ g 1) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → u.T ψ t ≤ g ψ := fun ψ hψ t ht =>
  le_of_upperMargin_axisFree hD hax (hu t ht) hg hRc hlo hκ hmargin h0
    (fun s hs => h1 s hs.1) ψ hψ t ⟨ht, le_rfl⟩

/-- **Corner compatibility.** For an axis-free classical solution on `[0,τ]`, `τ > 0`, whose
edge data have derivative `e` at `t = 0` (within `[0,τ]`), the initial profile must satisfy
`N[T(·,0)](1) = e`: the edge condition and the equation must agree at the corner `(1,0)`. -/
theorem AxisFreeSolution.corner_compatibility {c : RadialCoefficients} {Tedge : ℝ → ℝ}
    {τ : ℝ} {u : RadialField} (hu : AxisFreeSolution c Tedge τ u) (hτ : 0 < τ) {e : ℝ}
    (he : HasDerivWithinAt Tedge e (Icc 0 τ) 0) :
    c.op 1 (u.T 1 0) (u.Tψ 1 0) (u.Tψψ 1 0) = e := by
  have h0 : (0 : ℝ) ∈ Icc 0 τ := ⟨le_rfl, hτ.le⟩
  have h1 := hu.regular.deriv_t 1 ⟨zero_le_one, le_rfl⟩ 0 h0
  have h2 : HasDerivWithinAt (fun s => u.T 1 s) e (Icc 0 τ) 0 :=
    he.congr (fun s hs => hu.edge s hs) (hu.edge 0 h0)
  rw [← hu.pde 1 ⟨zero_le_one, le_rfl⟩ 0 h0]
  exact (uniqueDiffOn_Icc hτ 0 h0).eq_deriv _ h1 h2

/-! ### The rational piecewise barrier checker -/

open PlasmaLean.Certificates

/-- Right end of a list of pieces `(dᵢ, kᵢ)` starting at `c`. -/
@[expose] def pieceEnd : ℚ → List (ℚ × ℚ) → ℚ
  | c, [] => c
  | _, (d, _) :: rest => pieceEnd d rest

/-- **Piecewise barrier checker.** Pieces `(dᵢ, kᵢ)` cover `[a, d_last]` consecutively. On
the piece `[c, d]` with label `k` it checks `c ≤ d`, the profile bound `k ≤ T(d)` (exact
rational evaluation) and the Horner lower bound `κ − bonus k ≤ lowerBound (d − c) (Q(c + ·))`.
-/
@[expose] def pieceCheck (Q T : List ℚ) (κ : ℚ) (bonus : ℚ → ℚ) : ℚ → List (ℚ × ℚ) → Bool
  | _, [] => true
  | c, (d, k) :: rest => decide (c ≤ d) && decide (k ≤ QPoly.evalQ T d) &&
      decide (κ - bonus k ≤ QPoly.lowerBound (d - c) (QPoly.shift c Q)) &&
      pieceCheck Q T κ bonus d rest

/-- An accepted list of pieces ends to the right of its start. -/
theorem le_pieceEnd {Q T : List ℚ} {κ : ℚ} {bonus : ℚ → ℚ} :
    ∀ (c : ℚ) (ps : List (ℚ × ℚ)), pieceCheck Q T κ bonus c ps = true → c ≤ pieceEnd c ps
  | c, [] => fun _ => le_rfl
  | c, (d, k) :: rest => fun h => by
    simp only [pieceCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1.trans (le_pieceEnd d rest h.2)

/-- **Soundness of the piecewise checker.** If the check passes and `T` is antitone on the
covered interval, every real `x ∈ [a, d_last]` lies in a piece with label `k` such that
`k ≤ T(x)` and `κ − bonus k ≤ Q(x)`. -/
theorem pieceCheck_sound {Q T : List ℚ} {κ : ℚ} {bonus : ℚ → ℚ} :
    ∀ (a : ℚ) (ps : List (ℚ × ℚ)), pieceCheck Q T κ bonus a ps = true → ps ≠ [] →
      AntitoneOn (QPoly.eval T) (Icc (a : ℝ) (pieceEnd a ps)) →
      ∀ x ∈ Icc (a : ℝ) (pieceEnd a ps), ∃ k : ℚ, (∃ d, (d, k) ∈ ps) ∧
        (k : ℝ) ≤ QPoly.eval T x ∧ ((κ - bonus k : ℚ) : ℝ) ≤ QPoly.eval Q x
  | _, [], _, hne, _ => absurd rfl hne
  | a, (d, k) :: rest, h, _, hT => by
    intro x hx
    simp only [pieceCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨had, hkd⟩, hlb⟩, hrest⟩ := h
    have hdend : (d : ℝ) ≤ pieceEnd d rest := by exact_mod_cast le_pieceEnd d rest hrest
    have hend : pieceEnd a ((d, k) :: rest) = pieceEnd d rest := rfl
    rw [hend] at hx hT
    rcases le_or_gt x d with hxd | hxd
    · refine ⟨k, ⟨d, List.mem_cons_self⟩, ?_, ?_⟩
      · have hTd : (k : ℝ) ≤ QPoly.eval T d := by
          rw [QPoly.eval_cast]; exact_mod_cast hkd
        exact hTd.trans (hT hx ⟨by exact_mod_cast had, hdend⟩ hxd)
      · have hb := QPoly.lowerBound_le (h := d - a) (QPoly.shift a Q) (t := x - a)
          (by linarith [hx.1]) (by push_cast; linarith)
        rw [QPoly.eval_shift, show ((a : ℚ) : ℝ) + (x - a) = x by ring] at hb
        exact (by exact_mod_cast hlb :
          ((κ - bonus k : ℚ) : ℝ) ≤ (QPoly.lowerBound (d - a) (QPoly.shift a Q) : ℝ)).trans hb
    · have hne' : rest ≠ [] := by
        rintro rfl
        simp only [pieceEnd] at hx
        linarith [hx.2]
      obtain ⟨k', ⟨d', hmem⟩, h1, h2⟩ := pieceCheck_sound d rest hrest hne'
        (hT.mono (Icc_subset_Icc (by exact_mod_cast had) le_rfl)) x ⟨hxd.le, hx.2⟩
      exact ⟨k', ⟨d', List.mem_cons_of_mem _ hmem⟩, h1, h2⟩

/-- Monotonicity certificate: if the checker certifies `−p' ≥ 0` on `[a,b]`, the polynomial
`p` is antitone on `[a,b]` (mean value theorem). Supplies the antitonicity hypothesis of
`pieceCheck_sound`. -/
theorem antitoneOn_eval_of_check {p : List ℚ} {a b : ℚ} {pts : List ℚ}
    (h : QPoly.checkOn (QPoly.scale (-1) (QPoly.deriv p)) 0 a b pts = true) :
    AntitoneOn (QPoly.eval p) (Icc (a : ℝ) b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) (QPoly.continuous_eval p).continuousOn
  · exact fun x _ => (QPoly.hasDerivAt_eval p x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(QPoly.hasDerivAt_eval p x).deriv]
    have := QPoly.checkOn_sound h x (interior_subset hx)
    simp only [QPoly.eval_scale, Rat.cast_zero, Rat.cast_neg, Rat.cast_one] at this
    linarith

/-! ### Sanity checks -/

/-- Sanity (degenerate case): with `D ≡ 0` and `D' ≡ 0` the degenerate-axis condition holds. -/
theorem degenerateAxis_of_zero (c : RadialCoefficients) (hD : ∀ ψ, c.D ψ = 0)
    (hdD : ∀ ψ, c.dD ψ = 0) : DegenerateAxis c :=
  ⟨hD 0, (hdD 0).symm.le⟩

/-- Sanity (accepted fixture): `Q = 1 − x` on `[0,1]` split at `1/2`, profile `T = 2 − x`,
labels `1`, bonus `0`, margin `0`. -/
theorem pieceCheck_accept :
    pieceCheck [1, -1] [2, -1] 0 (fun _ => 0) 0 [(1 / 2, 1), (1, 1)] = true := by
  decide +kernel

/-- Sanity (rejected fixture): `Q = 1 − 2x` is negative near `x = 1`, so margin `0` fails. -/
theorem pieceCheck_reject :
    pieceCheck [1, -2] [2, -1] 0 (fun _ => 0) 0 [(1 / 2, 1), (1, 1)] = false := by
  decide +kernel

/-- Sanity (the bonus is used): `Q = −1` with bonus `2` on label `1` passes margin `1`. -/
theorem pieceCheck_bonus :
    pieceCheck [-1] [2, -1] 1 (fun k => if k = 1 then 2 else 0) 0 [(1, 1)] = true := by
  decide +kernel

end PlasmaLean.Transport
