/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Transport.Comparison
public import PlasmaLean.Certificates.PolyInterval
public import PlasmaLean.Certificates.KernelFact
public import PlasmaLean.Certificates.BoolCert

/-!
# Barrier comparison with a degenerate axis, and a rational piecewise barrier checker

## Why a degenerate-axis comparison theorem

In the normalized toroidal flux coordinate `ψ` the flux-surface-averaged diffusivity is
`D(ψ) = χ ⟨|∇ψ|²⟩`, and `⟨|∇ψ|²⟩ ∝ ψ` near the magnetic axis (for a cylinder `ψ = r²/a²`
gives `|∇ψ|² = 4ψ/a²` exactly). So `D(0) = 0`, and the axis Neumann condition
`∂ψT(0,t) = 0` is *not* the natural regularity condition (a smooth profile `T₀ − c r²` has
`∂ψT(0) = −c a² ≠ 0`). (This module was written when the kernel still demanded
`D ≥ Dmin > 0` and the Neumann condition; since the kernel change of 2026-10-20 the kernel
has the `degenerate` axis kind, `DegenerateAxis` and `op_le_op_of_touch_axis` live in
`Comparison`, and `AxisFreeSolution.classical` identifies axis-free solutions with kernel
solutions for a degenerate axis. The axis-free statements below remain useful because they
take the coefficient hypotheses explicitly instead of through `TransportLaws`.)

At a degenerate axis no boundary condition is needed at all (Fichera): if `D(0) = 0` and the
drift coefficient `D'(0) ≥ 0`, the equation at `ψ = 0` reduces to `∂ₜT = D'(0) ∂ψT + R`,
whose characteristics `dψ/dt = −D'(0) ≤ 0` run *toward* the axis: `ψ = 0` is an outflow
boundary, so its values are determined from the interior and no boundary condition may be
prescribed there.

This module proves the comparison principle in exactly that setting:

* `DegenerateAxis c` (in `Comparison`): `D(0) = 0` and `D'(0) ≥ 0`.
* `AxisFreeSolution c Tedge τ u`: a classical solution as in `ClassicalRadialSolution`, but
  **without** the axis condition (`ClassicalRadialSolution.axisFree` shows that every kernel
  solution is one; `AxisFreeSolution.classical` gives the converse for a degenerate axis).
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

open PlasmaLean.Certificates.BoolCert

open Set Filter Topology

/-! ### Degenerate axis -/

/-- A supplied classical solution of `∂ₜT = N[T]` on `[0,1] × [0,τ]` with edge Dirichlet data
and **no** axis condition (appropriate when the axis is degenerate). Since the 2026-10-20
kernel change this largely duplicates `ClassicalRadialSolution` with `axis = .degenerate`
(`AxisFreeSolution.classical`, `ClassicalRadialSolution.axisFree`); it is kept for the
axis-free theorems that take coefficient hypotheses explicitly. New code should prefer the
kernel class. -/
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

/-- **Bridge to the kernel.** For a `degenerate` axis the kernel imposes no axis condition, so
axis-free solutions are exactly kernel classical solutions (converse of
`ClassicalRadialSolution.axisFree`). -/
theorem AxisFreeSolution.classical {c : RadialCoefficients} {Tedge : ℝ → ℝ} {τ : ℝ}
    {u : RadialField} (hk : c.axis = .degenerate) (h : AxisFreeSolution c Tedge τ u) :
    ClassicalRadialSolution c Tedge τ u where
  tau_nonneg := h.tau_nonneg
  regular := h.regular
  pde := h.pde
  axis := fun hr => absurd (hr.symm.trans hk) (by decide)
  edge := h.edge

/-- **Comparison by residuals, degenerate axis** (first-touching-time argument). Let `S`, `u`
be regular fields on `[0,1] × [0,τ]` whose residuals satisfy `∂ₜS − N[S] < ∂ₜu − N[u]`
pointwise. If `S < u` initially and at the edge, then `S < u` on the whole rectangle. Only
`D ≥ 0` on `[0,1]` and `DegenerateAxis c` are used; no axis condition is imposed on either
field. (Lower barriers: `S` a strict subsolution, `u` a solution; upper barriers: `S` a
solution, `u` a strict supersolution.) -/
theorem lt_of_residual_lt {c : RadialCoefficients} {τ : ℝ} {u S : RadialField}
    (hD : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ T : ℝ, 0 ≤ c.D ψ T) (hax : DegenerateAxis c)
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
        (sψψ := fun x => S.Tψψ x ts) h hψs1 (hD ψs hψs _) (hu.deriv_ψ ts hts)
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
argument by any `|s| < δ₀` changes `R(ψ, f ψ)` by less than `κ` (the case `U = (lo,∞)` of
`exists_shift_control_open`). -/
theorem exists_shift_control {c : RadialCoefficients} {f f' f'' : ℝ → ℝ}
    (hf : ProfileRegular f f' f'') {lo : ℝ}
    (hRc : ContinuousOn (fun p : ℝ × ℝ => c.R p.1 p.2) (Icc 0 1 ×ˢ Ioi lo))
    (hlo : ∀ ψ ∈ Icc (0 : ℝ) 1, lo < f ψ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ δ₀ > 0, ∀ s : ℝ, |s| < δ₀ → ∀ ψ ∈ Icc (0 : ℝ) 1,
      |c.R ψ (f ψ + s) - c.R ψ (f ψ)| < κ :=
  exists_shift_control_open hf isOpen_Ioi hRc hlo hκ

/-- **Lower barrier with margin, degenerate axis** (semilinear coefficients, `IsSemilinear`;
for quasilinear coefficients use `le_of_lowerMargin_shift`). Let `f` be a regular profile (no axis
condition needed) with `N[f] ≥ κ > 0` on `[0,1]`, `f > lo`, and `R` continuous on
`[0,1] × (lo, ∞)`. Then every axis-free classical solution with `f ≤ T(·,0)` and
`f(1) ≤ T_edge(t)` satisfies `f ≤ T` on `[0,1] × [0,τ]`. -/
theorem le_of_lowerMargin_axisFree {c : RadialCoefficients} {Tedge : ℝ → ℝ} {τ : ℝ}
    {u : RadialField} (hD : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ T : ℝ, 0 ≤ c.D ψ T) (hax : DegenerateAxis c)
    (hsl : c.IsSemilinear)
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
    have h2 := hsl.op_sub_op hψ (f ψ + -δ) (f ψ) (f' ψ) (f'' ψ)
    have h3 := hmargin ψ hψ
    rw [hu.pde ψ hψ t ht]
    change 0 - c.op ψ (f ψ - δ) (f' ψ) (f'' ψ) < _
    rw [show f ψ - δ = f ψ + -δ by ring]
    linarith
  intro ψ hψ t ht
  refine le_of_forall_pos_lt_add (fun ε hε => ?_)
  have := key (min ε δ₀ / 2) (by positivity) (by linarith [min_le_right ε δ₀]) ψ hψ t ht
  linarith [min_le_left ε δ₀]

/-- **Upper barrier with margin, degenerate axis** (semilinear coefficients, `IsSemilinear`;
for quasilinear coefficients use `le_of_upperMargin_shift`). Let `g` be a regular profile with
`N[g] ≤ −κ < 0` on `[0,1]`, `g > lo`, and `R` continuous on `[0,1] × (lo, ∞)`. Then every
axis-free classical solution with `T(·,0) ≤ g` and `T_edge(t) ≤ g(1)` satisfies `T ≤ g` on
`[0,1] × [0,τ]`. -/
theorem le_of_upperMargin_axisFree {c : RadialCoefficients} {Tedge : ℝ → ℝ} {τ : ℝ}
    {u : RadialField} (hD : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ T : ℝ, 0 ≤ c.D ψ T) (hax : DegenerateAxis c)
    (hsl : c.IsSemilinear)
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
    have h2 := hsl.op_sub_op hψ (g ψ + δ) (g ψ) (g' ψ) (g'' ψ)
    have h3 := hmargin ψ hψ
    rw [hu.pde ψ hψ t ht]
    change _ < 0 - c.op ψ (g ψ + δ) (g' ψ) (g'' ψ)
    linarith
  intro ψ hψ t ht
  refine le_of_forall_pos_lt_add (fun ε hε => ?_)
  have := key (min ε δ₀ / 2) (by positivity) (by linarith [min_le_right ε δ₀]) ψ hψ t ht
  linarith [min_le_left ε δ₀]

/-- **Lower barrier for all time, degenerate axis** (semilinear coefficients). If the
supplied field is an axis-free
classical solution on every horizon `[0,τ]`, the conclusion of `le_of_lowerMargin_axisFree`
holds for all `t ≥ 0`. -/
theorem le_of_lowerMargin_axisFree_forall_time {c : RadialCoefficients} {Tedge : ℝ → ℝ}
    {u : RadialField} (hD : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ T : ℝ, 0 ≤ c.D ψ T) (hax : DegenerateAxis c)
    (hsl : c.IsSemilinear) (hu : ∀ τ, 0 ≤ τ → AxisFreeSolution c Tedge τ u) {f f' f'' : ℝ → ℝ}
    (hf : ProfileRegular f f' f'') {lo : ℝ}
    (hRc : ContinuousOn (fun p : ℝ × ℝ => c.R p.1 p.2) (Icc 0 1 ×ˢ Ioi lo))
    (hlo : ∀ ψ ∈ Icc (0 : ℝ) 1, lo < f ψ) {κ : ℝ} (hκ : 0 < κ)
    (hmargin : ∀ ψ ∈ Icc (0 : ℝ) 1, κ ≤ c.op ψ (f ψ) (f' ψ) (f'' ψ))
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, f ψ ≤ u.T ψ 0) (h1 : ∀ t, 0 ≤ t → f 1 ≤ Tedge t) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → f ψ ≤ u.T ψ t := fun ψ hψ t ht =>
  le_of_lowerMargin_axisFree hD hax hsl (hu t ht) hf hRc hlo hκ hmargin h0
    (fun s hs => h1 s hs.1) ψ hψ t ⟨ht, le_rfl⟩

/-- **Upper barrier for all time, degenerate axis** (semilinear coefficients). -/
theorem le_of_upperMargin_axisFree_forall_time {c : RadialCoefficients} {Tedge : ℝ → ℝ}
    {u : RadialField} (hD : ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ T : ℝ, 0 ≤ c.D ψ T) (hax : DegenerateAxis c)
    (hsl : c.IsSemilinear) (hu : ∀ τ, 0 ≤ τ → AxisFreeSolution c Tedge τ u) {g g' g'' : ℝ → ℝ}
    (hg : ProfileRegular g g' g'') {lo : ℝ}
    (hRc : ContinuousOn (fun p : ℝ × ℝ => c.R p.1 p.2) (Icc 0 1 ×ˢ Ioi lo))
    (hlo : ∀ ψ ∈ Icc (0 : ℝ) 1, lo < g ψ) {κ : ℝ} (hκ : 0 < κ)
    (hmargin : ∀ ψ ∈ Icc (0 : ℝ) 1, c.op ψ (g ψ) (g' ψ) (g'' ψ) ≤ -κ)
    (h0 : ∀ ψ ∈ Icc (0 : ℝ) 1, u.T ψ 0 ≤ g ψ) (h1 : ∀ t, 0 ≤ t → Tedge t ≤ g 1) :
    ∀ ψ ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → u.T ψ t ≤ g ψ := fun ψ hψ t ht =>
  le_of_upperMargin_axisFree hD hax hsl (hu t ht) hg hRc hlo hκ hmargin h0
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

/-! ### Two-label piece checker (lower and upper barriers, level-transformed profiles) -/

/-- Right end of a list of two-label pieces `(dᵢ, kᵢ, Kᵢ)` starting at `c`. -/
@[expose] def pieceEnd2 : ℚ → List (ℚ × ℚ × ℚ) → ℚ
  | c, [] => c
  | _, (d, _, _) :: rest => pieceEnd2 d rest

/-- **Two-label piecewise checker.** Pieces `(dᵢ, kᵢ, Kᵢ)` cover `[a, d_last]` consecutively.
On the piece `[c, d]` it checks `c ≤ d`, the level bounds `lev k ≤ F(d)` and
`F(c) ≤ lev K` (exact rational evaluation), and the Horner bound
`κ − bonus k K ≤ lowerBound (d − c) (Q(c + ·))`. For an antitone `F` the labels bracket `F` on
the piece: `lev k ≤ F ≤ lev K`. Used with `F` the Kirchhoff transform of a barrier
(`lev = Φ`), so that `k ≤ T ≤ K` on the piece; the lower label feeds a reactivity floor, the
upper label a reactivity ceiling or a bremsstrahlung bound. -/
@[expose] def pieceCheck2 (Q F : List ℚ) (lev : ℚ → ℚ) (κ : ℚ) (bonus : ℚ → ℚ → ℚ) :
    ℚ → List (ℚ × ℚ × ℚ) → Bool
  | _, [] => true
  | c, (d, k, K) :: rest => decide (c ≤ d) && decide (lev k ≤ QPoly.evalQ F d) &&
      decide (QPoly.evalQ F c ≤ lev K) &&
      decide (κ - bonus k K ≤ QPoly.lowerBound (d - c) (QPoly.shift c Q)) &&
      pieceCheck2 Q F lev κ bonus d rest

/-- An accepted list of two-label pieces ends to the right of its start. -/
theorem le_pieceEnd2 {Q F : List ℚ} {lev : ℚ → ℚ} {κ : ℚ} {bonus : ℚ → ℚ → ℚ} :
    ∀ (c : ℚ) (ps : List (ℚ × ℚ × ℚ)), pieceCheck2 Q F lev κ bonus c ps = true →
      c ≤ pieceEnd2 c ps
  | c, [] => fun _ => le_rfl
  | c, (d, k, K) :: rest => fun h => by
    simp only [pieceCheck2, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1.1.trans (le_pieceEnd2 d rest h.2)

/-- **Soundness of the two-label checker.** If the check passes and `F` is antitone on the
covered interval, every real `x ∈ [a, d_last]` lies in a piece with labels `k`, `K` such that
`lev k ≤ F(x) ≤ lev K` and `κ − bonus k K ≤ Q(x)`. -/
theorem pieceCheck2_sound {Q F : List ℚ} {lev : ℚ → ℚ} {κ : ℚ} {bonus : ℚ → ℚ → ℚ} :
    ∀ (a : ℚ) (ps : List (ℚ × ℚ × ℚ)), pieceCheck2 Q F lev κ bonus a ps = true → ps ≠ [] →
      AntitoneOn (QPoly.eval F) (Icc (a : ℝ) (pieceEnd2 a ps)) →
      ∀ x ∈ Icc (a : ℝ) (pieceEnd2 a ps), ∃ k K : ℚ, (∃ d, (d, k, K) ∈ ps) ∧
        ((lev k : ℚ) : ℝ) ≤ QPoly.eval F x ∧ QPoly.eval F x ≤ ((lev K : ℚ) : ℝ) ∧
        ((κ - bonus k K : ℚ) : ℝ) ≤ QPoly.eval Q x
  | _, [], _, hne, _ => absurd rfl hne
  | a, (d, k, K) :: rest, h, _, hT => by
    intro x hx
    simp only [pieceCheck2, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨had, hkd⟩, hKc⟩, hlb⟩, hrest⟩ := h
    have hdend : (d : ℝ) ≤ pieceEnd2 d rest := by exact_mod_cast le_pieceEnd2 d rest hrest
    have hend : pieceEnd2 a ((d, k, K) :: rest) = pieceEnd2 d rest := rfl
    rw [hend] at hx hT
    rcases le_or_gt x d with hxd | hxd
    · refine ⟨k, K, ⟨d, List.mem_cons_self⟩, ?_, ?_, ?_⟩
      · have hTd : ((lev k : ℚ) : ℝ) ≤ QPoly.eval F d := by
          rw [QPoly.eval_cast]; exact_mod_cast hkd
        exact hTd.trans (hT hx ⟨by exact_mod_cast had, hdend⟩ hxd)
      · have hTc : QPoly.eval F a ≤ ((lev K : ℚ) : ℝ) := by
          rw [QPoly.eval_cast]; exact_mod_cast hKc
        exact (hT ⟨le_rfl, (by exact_mod_cast had : (a : ℝ) ≤ d).trans hdend⟩ hx hx.1).trans hTc
      · have hb := QPoly.lowerBound_le (h := d - a) (QPoly.shift a Q) (t := x - a)
          (by linarith [hx.1]) (by push_cast; linarith)
        rw [QPoly.eval_shift, show ((a : ℚ) : ℝ) + (x - a) = x by ring] at hb
        exact (by exact_mod_cast hlb :
          ((κ - bonus k K : ℚ) : ℝ) ≤ (QPoly.lowerBound (d - a) (QPoly.shift a Q) : ℝ)).trans hb
    · have hne' : rest ≠ [] := by
        rintro rfl
        simp only [pieceEnd2] at hx
        linarith [hx.2]
      obtain ⟨k', K', ⟨d', hmem⟩, h1, h2, h3⟩ := pieceCheck2_sound d rest hrest hne'
        (hT.mono (Icc_subset_Icc (by exact_mod_cast had) le_rfl)) x ⟨hxd.le, hx.2⟩
      exact ⟨k', K', ⟨d', List.mem_cons_of_mem _ hmem⟩, h1, h2, h3⟩

/-! ### Label-dependent piece checker -/

/-- **Label-dependent two-label checker.** As `pieceCheck2`, but the polynomial checked on a
piece may depend on its labels: on `[c, d]` with labels `(k, K)` it checks `c ≤ d`,
`lev k ≤ F(d)`, `F(c) ≤ lev K` and `κ ≤ lowerBound (d − c) ((Qf k K)(c + ·))`. Used when a
label-dependent source bound is multiplied by a non-constant profile (e.g. a density). -/
@[expose] def pieceCheckL (Qf : ℚ → ℚ → List ℚ) (F : List ℚ) (lev : ℚ → ℚ) (κ : ℚ) :
    ℚ → List (ℚ × ℚ × ℚ) → Bool
  | _, [] => true
  | c, (d, k, K) :: rest => decide (c ≤ d) && decide (lev k ≤ QPoly.evalQ F d) &&
      decide (QPoly.evalQ F c ≤ lev K) &&
      decide (κ ≤ QPoly.lowerBound (d - c) (QPoly.shift c (Qf k K))) &&
      pieceCheckL Qf F lev κ d rest

/-- An accepted list of label-dependent pieces ends to the right of its start. -/
theorem le_pieceEndL {Qf : ℚ → ℚ → List ℚ} {F : List ℚ} {lev : ℚ → ℚ} {κ : ℚ} :
    ∀ (c : ℚ) (ps : List (ℚ × ℚ × ℚ)), pieceCheckL Qf F lev κ c ps = true →
      c ≤ pieceEnd2 c ps
  | c, [] => fun _ => le_rfl
  | c, (d, k, K) :: rest => fun h => by
    simp only [pieceCheckL, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1.1.trans (le_pieceEndL d rest h.2)

/-- **Soundness of the label-dependent checker.** If the check passes and `F` is antitone on
the covered interval, every real `x ∈ [a, d_last]` lies in a piece with labels `k`, `K` such
that `lev k ≤ F(x) ≤ lev K` and `κ ≤ (Qf k K)(x)`. -/
theorem pieceCheckL_sound {Qf : ℚ → ℚ → List ℚ} {F : List ℚ} {lev : ℚ → ℚ} {κ : ℚ} :
    ∀ (a : ℚ) (ps : List (ℚ × ℚ × ℚ)), pieceCheckL Qf F lev κ a ps = true → ps ≠ [] →
      AntitoneOn (QPoly.eval F) (Icc (a : ℝ) (pieceEnd2 a ps)) →
      ∀ x ∈ Icc (a : ℝ) (pieceEnd2 a ps), ∃ k K : ℚ, (∃ d, (d, k, K) ∈ ps) ∧
        ((lev k : ℚ) : ℝ) ≤ QPoly.eval F x ∧ QPoly.eval F x ≤ ((lev K : ℚ) : ℝ) ∧
        ((κ : ℚ) : ℝ) ≤ QPoly.eval (Qf k K) x
  | _, [], _, hne, _ => absurd rfl hne
  | a, (d, k, K) :: rest, h, _, hT => by
    intro x hx
    simp only [pieceCheckL, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨had, hkd⟩, hKc⟩, hlb⟩, hrest⟩ := h
    have hdend : (d : ℝ) ≤ pieceEnd2 d rest := by exact_mod_cast le_pieceEndL d rest hrest
    have hend : pieceEnd2 a ((d, k, K) :: rest) = pieceEnd2 d rest := rfl
    rw [hend] at hx hT
    rcases le_or_gt x d with hxd | hxd
    · refine ⟨k, K, ⟨d, List.mem_cons_self⟩, ?_, ?_, ?_⟩
      · have hTd : ((lev k : ℚ) : ℝ) ≤ QPoly.eval F d := by
          rw [QPoly.eval_cast]; exact_mod_cast hkd
        exact hTd.trans (hT hx ⟨by exact_mod_cast had, hdend⟩ hxd)
      · have hTc : QPoly.eval F a ≤ ((lev K : ℚ) : ℝ) := by
          rw [QPoly.eval_cast]; exact_mod_cast hKc
        exact (hT ⟨le_rfl, (by exact_mod_cast had : (a : ℝ) ≤ d).trans hdend⟩ hx hx.1).trans hTc
      · have hb := QPoly.lowerBound_le (h := d - a) (QPoly.shift a (Qf k K)) (t := x - a)
          (by linarith [hx.1]) (by push_cast; linarith)
        rw [QPoly.eval_shift, show ((a : ℚ) : ℝ) + (x - a) = x by ring] at hb
        exact (by exact_mod_cast hlb :
          ((κ : ℚ) : ℝ) ≤ (QPoly.lowerBound (d - a) (QPoly.shift a (Qf k K)) : ℝ)).trans hb
    · have hne' : rest ≠ [] := by
        rintro rfl
        simp only [pieceEnd2] at hx
        linarith [hx.2]
      obtain ⟨k', K', ⟨d', hmem⟩, h1, h2, h3⟩ := pieceCheckL_sound d rest hrest hne'
        (hT.mono (Icc_subset_Icc (by exact_mod_cast had) le_rfl)) x ⟨hxd.le, hx.2⟩
      exact ⟨k', K', ⟨d', List.mem_cons_of_mem _ hmem⟩, h1, h2, h3⟩

/-! ### Sanity checks -/

/-- Sanity (degenerate case): with `D ≡ 0`, `∂ψD ≡ 0` and `∂TD ≡ 0` the degenerate-axis
condition holds. -/
theorem degenerateAxis_of_zero (c : RadialCoefficients) (hD : ∀ ψ T, c.D ψ T = 0)
    (hdD : ∀ ψ T, c.dD ψ T = 0) (hdDT : ∀ ψ T, c.dDT ψ T = 0) : DegenerateAxis c :=
  ⟨hD 0, fun T => (hdD 0 T).symm.le, hdDT 0⟩

/-- Sanity (accepted fixture): `Q = 1 − x` on `[0,1]` split at `1/2`, profile `T = 2 − x`,
labels `1`, bonus `0`, margin `0`. -/
theorem pieceCheck_accept :
    pieceCheck [1, -1] [2, -1] 0 (fun _ => 0) 0 [(1 / 2, 1), (1, 1)] = true := by
  bool_cert

/-- Sanity (rejected fixture): `Q = 1 − 2x` is negative near `x = 1`, so margin `0` fails. -/
theorem pieceCheck_reject :
    pieceCheck [1, -2] [2, -1] 0 (fun _ => 0) 0 [(1 / 2, 1), (1, 1)] = false := by
  bool_cert

/-- Sanity (the bonus is used): `Q = −1` with bonus `2` on label `1` passes margin `1`. -/
theorem pieceCheck_bonus :
    pieceCheck [-1] [2, -1] 1 (fun k => if k = 1 then 2 else 0) 0 [(1, 1)] = true := by
  bool_cert

/-- Sanity (two-label checker, accepted fixture): `F = 2 − x` lies in `[1, 2]` on `[0,1]`, the
labels `(1, 2)` bracket it, and `Q = 1 − x` with bonus `0` has margin `0`. -/
theorem pieceCheck2_accept :
    pieceCheck2 [1, -1] [2, -1] id 0 (fun _ _ => 0) 0 [(1 / 2, 1, 2), (1, 1, 2)] = true := by
  bool_cert

/-- Sanity (label-dependent checker, accepted fixture): `Q_k = k − x` with labels `k = 1`. -/
theorem pieceCheckL_accept :
    pieceCheckL (fun k _ => [k, -1]) [2, -1] id 0 0 [(1 / 2, 1, 2), (1, 1, 2)] = true := by
  bool_cert

/-- Sanity (label-dependent checker, rejected fixture): with `k = 1/2`, `Q_k = k − x` is
negative near `x = 1`. -/
theorem pieceCheckL_reject :
    pieceCheckL (fun k _ => [k, -1]) [2, -1] id 0 0 [(1 / 2, 1 / 2, 2), (1, 1 / 2, 2)] = false := by
  bool_cert

/-- Sanity (two-label checker, rejected fixture): the upper label `3/2` is below `F(0) = 2`. -/
theorem pieceCheck2_reject_label :
    pieceCheck2 [1, -1] [2, -1] id 0 (fun _ _ => 0) 0 [(1 / 2, 1, 3 / 2), (1, 1, 2)] = false := by
  bool_cert

end PlasmaLean.Transport
