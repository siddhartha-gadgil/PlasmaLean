/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevAlpha
public import PlasmaLean.Theory.Transport.FluxGeometry
public import PlasmaLean.Kernel.Fusion
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Ingredients of `solovev_one_plasma`: one Solov'ev plasma for the G1 and G2 chains

Plan: `notes/theory/transport-mhd-coupling.md`. This file proves the ingredients of the
combined "one plasma" theorem that do **not** depend on the quasilinear transport kernel (K2)
or on the two barrier certificates (those, and the final theorem, are in
`PlasmaLean.Design.SolovevBand`). Field: the reactor Solov'ev equilibrium of
`PlasmaLean.Design.SolovevAlpha` (`L = 10 m`, `A = 7/4 T`, `F = 50 T m`,
`p = p₀ (1 − ψ̃/ψ̃_e)`, `ψ̃_e = 625 m⁴`, `p₀ = 147/(256 μ₀) ≈ 457 kPa`).

## (a) Constant pressure offset (`offset_*`)

`ForceBalance` involves the pressure only through its gradient. For every constant `Δ`,
`p + Δ` has the same actual gradient as `p` (`offset_pressure_hasFDerivAt`,
`offset_pressure_gradient`, stated with Mathlib's `gradient`), so the kernel law
`ForceBalance B J ∇(p + Δ)` holds with the same `B` and the same Ampère current `J` at every
point off the axis (`offset_force_balance`), in particular at every point of the transport
domain `ψ̃ ≤ ψ̃_b` (`offset_force_balance_domain`), where also `p + Δ ≥ p₀/12 + Δ > 0`
(`offset_pressure_domain_lower`). The offset needs an (unmodelled) boundary sheet; the
exterior `ψ̃ > ψ̃_b` is not modelled.

## (b) Transport label and the alpha birth region (`label`, `birth_in_core`)

Transport edge `ψ̃_b = (11/12) ψ̃_e = 11·10⁴/192` (`psiB`), label `s = ψ̃/ψ̃_b` (`label`).
The birth region `ψ̃ ≤ ψ̃_e/4` of `reactor_alpha_confined` is exactly `s ≤ 3/11`
(`birth_in_core`, `birth_in_core_iff`), and the confinement shell of that theorem is exactly
`s ≤ 1` (`label_le_one_iff`). Corollary `alpha_stays_in_transport_domain`: every 3.5 MeV
alpha orbit born at `s ≤ 3/11` has `0 ≤ s ≤ 1` for all real times.

## (c) Solov'ev transport geometry (not in this file)

The flux-surface quantities of the label `s` are derived by hand in
`notes/theory/transport-mhd-coupling.md` §3.1 (`V'(s) ≈ 1599–1678 m³`, `g/s ∈ [0.4953,
0.5236]`, `h ∈ [0.4914, 0.5236]`, adaptive quadrature). **No series or enclosure is formalized
here.** The class `SolovevBand.IsSolovevGeometry` (in `PlasmaLean.Design.SolovevBand`) records
the flux-geometry laws together with widened enclosures `0.49 s ≤ g ≤ 0.525 s`,
`0.49 ≤ h ≤ 0.525` and continuity of `h` as **supplied** facts (coarea/divergence link and the
numerical enclosures), as `IsHelicalGeometry` does for the helical field.

## (d) Pressure comparison (`peqLabel`, `pressure_comparison`)

`reactorPressure_label`: exactly `p_eq = p₀ (1 − 11 s/12)` with `s = label x`
(`peqLabel μ₀ Δ s = Δ + p₀ (1 − 11 s/12)`). `pressure_comparison`: an upper barrier
`T ≤ T_sup` with `n c T_sup keV ≤ p_eq + Δ` on `[0,1]` bounds the plasma pressure by
`p_eq + Δ` for all `t ≥ 0`; `plasma_pressure_le_offset` is the same statement at points of
the transport domain in space.

## Assembly

`SolovevBand.solovev_one_plasma` (module `PlasmaLean.Design.SolovevBand`) combines
`offset_force_balance_domain` (`Δ = 40 kPa`), `alpha_stays_in_transport_domain`, the
quasilinear two-sided band `SolovevBand.solovev_band` (kernel change K2, density weighting
`FluxGeometry.weight_laws`, Kirchhoff-transform barriers) and `plasma_pressure_le_offset`
with the certificate `SolovevBand.tsup_pressure`. The certified parameter set differs from
the note's C2 set (driven, `≈ 120 MW` auxiliary heating, `Q ≈ 5.5`; see that module).

Scope: axisymmetric (tokamak-like) exact equilibrium, static fields; the layer
`ψ̃_b < ψ̃ < ψ̃_e` and the exterior are unmodelled; no MHD stability claim.
-/

open scoped RealInnerProductSpace

public section
noncomputable section
namespace PlasmaLean.Design.SolovevOnePlasma
open PlasmaLean.Fields PlasmaLean.Kinetic PlasmaLean.Design.Solovev
  PlasmaLean.Design.SolovevAlpha PlasmaLean.Fusion PlasmaLean.Transport WithLp Set

/-! ## (a) Constant pressure offset -/

/-- The reactor pressure with a constant offset `Δ` (a pressure pedestal at the boundary). -/
@[expose] def offsetPressure (μ₀ Δ : ℝ) (x : Space) : ℝ := reactorPressure μ₀ x + Δ

/-- Constant offsets preserve the actual pressure gradient. -/
theorem offset_pressure_hasFDerivAt (μ₀ Δ : ℝ) (x : Space) :
    HasFDerivAt (fun y => reactorPressure μ₀ y + Δ)
      (innerSL ℝ (pressureGrad μ₀ (7 / 4) 10 x)) x :=
  (reactor_pressure_hasFDerivAt μ₀ x).add_const Δ

/-- The (Mathlib) gradient of `p + Δ` is the explicit Solov'ev pressure gradient, for every
constant `Δ`. -/
theorem offset_pressure_gradient (μ₀ Δ : ℝ) (x : Space) :
    gradient (offsetPressure μ₀ Δ) x = pressureGrad μ₀ (7 / 4) 10 x := by
  refine HasGradientAt.gradient ?_
  rw [hasGradientAt_iff_hasFDerivAt]
  have e : InnerProductSpace.toDual ℝ Space (pressureGrad μ₀ (7 / 4) 10 x) =
      innerSL ℝ (pressureGrad μ₀ (7 / 4) 10 x) := by
    ext v; simp [InnerProductSpace.toDual_apply_apply]
  rw [e]
  exact offset_pressure_hasFDerivAt μ₀ Δ x

/-- Only `∇p` enters: the gradient of `p + Δ` does not depend on `Δ`. -/
theorem offset_pressure_gradient_indep (μ₀ Δ Δ' : ℝ) (x : Space) :
    gradient (offsetPressure μ₀ Δ) x = gradient (offsetPressure μ₀ Δ') x := by
  rw [offset_pressure_gradient, offset_pressure_gradient]

/-- **Offset equilibrium.** For every constant `Δ`, the reactor field `B` and its Ampère
current `J` satisfy the kernel law `ForceBalance B J ∇(p + Δ)` off the vertical axis. -/
theorem offset_force_balance {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (Δ : ℝ) {x : Space} (hx : R2 x ≠ 0) :
    ForceBalance (ofLp (reactorField x)) (ofLp (current μ₀ (7 / 4) 10 50 x))
      (ofLp (gradient (offsetPressure μ₀ Δ) x)) := by
  rw [offset_pressure_gradient]
  exact reactor_force_balance μ₀ hμ hx

/-! ## (b) Transport label -/

/-- Transport boundary flux `ψ̃_b = (11/12) ψ̃_e = 11·10⁴/192 m⁴` (the alpha-confinement
shell of `reactor_alpha_confined`). -/
@[expose] def psiB : ℝ := 11 * 10 ^ 4 / 192

/-- `ψ̃_b > 0`. -/
theorem psiB_pos : 0 < psiB := by norm_num [psiB]

/-- Transport label `s = ψ̃/ψ̃_b`. -/
@[expose] def label (x : Space) : ℝ := psiT 10 x / psiB

/-- `ψ̃ ≥ 0` everywhere. -/
theorem psiT_nonneg (x : Space) : 0 ≤ psiT 10 x := by
  unfold psiT R2; positivity

/-- `s ≥ 0`. -/
theorem label_nonneg (x : Space) : 0 ≤ label x :=
  div_nonneg (psiT_nonneg x) psiB_pos.le

/-- The transport domain `s ≤ 1` is exactly the confinement shell `ψ̃ ≤ ψ̃_b`. -/
theorem label_le_one_iff (x : Space) : label x ≤ 1 ↔ psiT 10 x ≤ psiB := by
  rw [label, div_le_one psiB_pos]

/-- The alpha birth region `ψ̃ ≤ ψ̃_e/4` is exactly `s ≤ 3/11`. -/
theorem birth_in_core_iff (x : Space) : label x ≤ 3 / 11 ↔ psiT 10 x ≤ 10 ^ 4 / 64 := by
  rw [label, div_le_iff₀ psiB_pos, psiB]; constructor <;> intro h <;> linarith

/-- **Alpha birth region inside the barrier core**: `ψ̃ ≤ ψ̃_e/4 ⇒ s ≤ 3/11 (< 3/10)`. -/
theorem birth_in_core {x : Space} (h : psiT 10 x ≤ 10 ^ 4 / 64) : label x ≤ 3 / 11 :=
  (birth_in_core_iff x).2 h

/-- Points of the transport domain are off the axis (`R² ≥ 50`). -/
theorem R2_ge_of_domain {x : Space} (hx : psiT 10 x ≤ psiB) : 50 ≤ R2 x := by
  have := (reactor_region_bounds x (by unfold psiB at hx; linarith)).1
  exact this

/-- **Offset equilibrium on the transport domain**: `ForceBalance B J ∇(p + Δ)` at every point
with `s ≤ 1`. -/
theorem offset_force_balance_domain {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (Δ : ℝ) {x : Space}
    (hx : label x ≤ 1) :
    ForceBalance (ofLp (reactorField x)) (ofLp (current μ₀ (7 / 4) 10 50 x))
      (ofLp (gradient (offsetPressure μ₀ Δ) x)) :=
  offset_force_balance hμ Δ
    (by have := R2_ge_of_domain ((label_le_one_iff x).1 hx); linarith)

/-- On the transport domain the offset pressure is at least `p₀/12 + Δ`. -/
theorem offset_pressure_domain_lower {μ₀ Δ : ℝ} (hμ : 0 < μ₀) {x : Space}
    (hx : label x ≤ 1) : 147 / (256 * μ₀) / 12 + Δ ≤ offsetPressure μ₀ Δ x := by
  have := (reactor_pressure_pos hμ ((label_le_one_iff x).1 hx)).1
  unfold offsetPressure; linarith

/-- **Alphas born in the hot core stay in the transport domain for all time.** Every 3.5 MeV
alpha orbit (hypotheses of `reactor_alpha_confined`) starting at `s ≤ 3/11` satisfies
`0 ≤ s ≤ 1` and `R² ≥ 50` for every real time. -/
theorem alpha_stays_in_transport_domain {m e : ℝ} (hm1 : 6.6446e-27 ≤ m)
    (hm2 : m ≤ 6.6448e-27) (he1 : 1.6021e-19 ≤ e) (he2 : e ≤ 1.6023e-19) {x v : ℝ → Space}
    (h : LorentzOrbit m (2 * e) (fun _ => 0) reactorField x v)
    (hK : m * ‖v 0‖ ^ 2 ≤ 2 * (3.5e6 * e)) (hs0 : label (x 0) ≤ 3 / 11) (t : ℝ) :
    label (x t) ∈ Icc (0 : ℝ) 1 ∧ 50 ≤ R2 (x t) := by
  have h0 := (birth_in_core_iff _).1 hs0
  obtain ⟨h1, h2⟩ := reactor_alpha_confined hm1 hm2 he1 he2 h hK (by linarith) t
  refine ⟨⟨label_nonneg _, (label_le_one_iff _).2 ?_⟩, h2⟩
  unfold psiB; linarith

/-- The same, with the birth region stated in flux: `ψ̃(x 0) ≤ ψ̃_e/4 ⇒ ∀ t, ψ̃(x t) ≤ ψ̃_b`. -/
theorem alpha_born_in_core {m e : ℝ} (hm1 : 6.6446e-27 ≤ m)
    (hm2 : m ≤ 6.6448e-27) (he1 : 1.6021e-19 ≤ e) (he2 : e ≤ 1.6023e-19) {x v : ℝ → Space}
    (h : LorentzOrbit m (2 * e) (fun _ => 0) reactorField x v)
    (hK : m * ‖v 0‖ ^ 2 ≤ 2 * (3.5e6 * e)) (hψ0 : psiT 10 (x 0) ≤ 10 ^ 4 / 64) (t : ℝ) :
    psiT 10 (x t) ≤ psiB :=
  (label_le_one_iff _).1
    (alpha_stays_in_transport_domain hm1 hm2 he1 he2 h hK (birth_in_core hψ0) t).1.2

/-- Sanity: the magnetic axis has label `0`. -/
theorem label_axis : label (toLp 2 ![10, 0, 0]) = 0 := by
  rw [label, reactor_axis_psi, zero_div]

/-- Sanity: the midplane points `R² = 50, 150` of the zero-pressure surface have label
`12/11 > 1`: the transport domain is strictly inside the plasma region. -/
theorem label_edge_points (r : ℝ) (hr : r ^ 2 = 50 ∨ r ^ 2 = 150) :
    label (toLp 2 ![r, 0, 0]) = 12 / 11 := by
  rw [label, reactor_edge_points r hr, psiB]; norm_num

/-! ## (d) Equilibrium pressure on labels and the pressure comparison -/

/-- Equilibrium pressure on labels with constant offset `Δ`:
`p_eq(s) + Δ = Δ + p₀ (1 − 11 s/12)`, `p₀ = 147/(256 μ₀)`. -/
@[expose] def peqLabel (μ₀ Δ s : ℝ) : ℝ := Δ + 147 / (256 * μ₀) * (1 - 11 / 12 * s)

/-- **Exact equilibrium pressure on labels**: `p(x) = p₀ (1 − 11 s/12)`, `s = label x`. -/
theorem reactorPressure_label {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (x : Space) :
    reactorPressure μ₀ x = peqLabel μ₀ 0 (label x) := by
  rw [reactorPressure_eq μ₀ hμ, peqLabel, label, psiB]
  ring

/-- The offset pressure on labels: `p(x) + Δ = peqLabel μ₀ Δ (label x)`. -/
theorem offsetPressure_label {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (Δ : ℝ) (x : Space) :
    offsetPressure μ₀ Δ x = peqLabel μ₀ Δ (label x) := by
  rw [offsetPressure, reactorPressure_label hμ, peqLabel, peqLabel]; ring

/-- Axis and edge values: `p_eq(0) + Δ = Δ + p₀`, `p_eq(1) + Δ = Δ + p₀/12`. -/
theorem peqLabel_axis_edge (μ₀ Δ : ℝ) :
    peqLabel μ₀ Δ 0 = Δ + 147 / (256 * μ₀) ∧ peqLabel μ₀ Δ 1 = Δ + 147 / (256 * μ₀) / 12 := by
  constructor <;> (unfold peqLabel; ring)

/-- With `μ₀ ∈ [1.2566e-6, 1.2567e-6]`, on `s ∈ [0,1]`:
`Δ + 456900 (1 − 11s/12) ≤ p_eq(s) + Δ ≤ Δ + 457000 (1 − 11s/12)` (Pa); at the edge
`p_eq(1) ≥ 38075 Pa`. -/
theorem peqLabel_bounds {μ₀ : ℝ} (h1 : 1.2566e-6 ≤ μ₀) (h2 : μ₀ ≤ 1.2567e-6) (Δ : ℝ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    Δ + 456900 * (1 - 11 / 12 * s) ≤ peqLabel μ₀ Δ s ∧
      peqLabel μ₀ Δ s ≤ Δ + 457000 * (1 - 11 / 12 * s) := by
  obtain ⟨p1, p2⟩ := reactor_axis_pressure μ₀ h1 h2
  have e : (3 * (7 / 4 : ℝ) ^ 2 / (16 * μ₀)) = 147 / (256 * μ₀) := by
    have : μ₀ ≠ 0 := by intro h; rw [h] at h1; norm_num at h1
    field_simp; norm_num
  rw [e] at p1 p2
  have hw : 0 ≤ 1 - 11 / 12 * s := by linarith [hs.2]
  unfold peqLabel
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right p1 hw, mul_le_mul_of_nonneg_right p2 hw]

/-- **Pressure comparison.** If `T(s,t) ≤ T_sup(s)` for all `t ≥ 0` and
`n(s) c T_sup(s) keV ≤ p_eq(s) + Δ` on `s ∈ [0,1]` (`n ≥ 0`, `c ≥ 0`), then the plasma
pressure `n c T keV` never exceeds `p_eq + Δ` on the transport domain. -/
theorem pressure_comparison {n Tsup peq : ℝ → ℝ} {T : ℝ → ℝ → ℝ} {c Δ : ℝ} (hc : 0 ≤ c)
    (hn : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ n s)
    (hT : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → T s t ≤ Tsup s)
    (hsup : ∀ s ∈ Icc (0 : ℝ) 1, n s * c * Tsup s * keV ≤ peq s + Δ) :
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → n s * c * T s t * keV ≤ peq s + Δ := by
  intro s hs t ht
  have hk : (0 : ℝ) ≤ keV := by norm_num [keV]
  have := mul_le_mul_of_nonneg_left (hT s hs t ht) (mul_nonneg (hn s hs) hc)
  have := mul_le_mul_of_nonneg_right this hk
  linarith [hsup s hs]

/-- **Plasma pressure below equilibrium pressure, in space.** With the hypotheses of
`pressure_comparison` for the reactor `p_eq + Δ = peqLabel μ₀ Δ`, at every point of the
transport domain and every `t ≥ 0`:
`n(s) c T(s,t) keV ≤ p(x) + Δ`, `s = label x`. -/
theorem plasma_pressure_le_offset {μ₀ Δ c : ℝ} (hμ : μ₀ ≠ 0) {n Tsup : ℝ → ℝ}
    {T : ℝ → ℝ → ℝ} (hc : 0 ≤ c) (hn : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ n s)
    (hT : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t, 0 ≤ t → T s t ≤ Tsup s)
    (hsup : ∀ s ∈ Icc (0 : ℝ) 1, n s * c * Tsup s * keV ≤ peqLabel μ₀ Δ s)
    {x : Space} (hx : label x ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    n (label x) * c * T (label x) t * keV ≤ reactorPressure μ₀ x + Δ := by
  have := pressure_comparison (peq := fun s => peqLabel μ₀ Δ s) (Δ := 0) hc hn hT
    (fun s hs => by simpa using hsup s hs) (label x) ⟨label_nonneg x, hx⟩ t ht
  rw [← offsetPressure, offsetPressure_label hμ]
  simpa using this

/-- Sanity (accepted fixture): a cold plasma `T ≡ 0 = T_sup` satisfies the hypotheses for
`Δ ≥ 0` at reactor `μ₀ > 0`, since `p_eq ≥ 0` on `[0,1]`. -/
theorem pressure_comparison_cold {μ₀ Δ : ℝ} (hμ : 0 < μ₀) (hΔ : 0 ≤ Δ) (n : ℝ → ℝ) :
    ∀ s ∈ Icc (0 : ℝ) 1, n s * (1 + 53 / 60) * 0 * keV ≤ peqLabel μ₀ Δ s := by
  intro s hs
  have : 0 ≤ 147 / (256 * μ₀) * (1 - 11 / 12 * s) :=
    mul_nonneg (by positivity) (by linarith [hs.2])
  unfold peqLabel; simp; linarith

/-- Rejected fixture: without truncation and without offset (transport edge on the
zero-pressure surface, label `12/11`, `Δ = 0`) the comparison hypothesis fails for a 1 keV edge
at the C2 edge density `2.5·10¹⁹ m⁻³`, because `p_eq = 0` there. -/
theorem edge_comparison_fails_untruncated (μ₀ : ℝ) :
    ¬ ((2.5e19 : ℝ) * (1 + 53 / 60) * 1 * keV ≤ peqLabel μ₀ 0 (12 / 11)) := by
  unfold peqLabel keV; norm_num

end PlasmaLean.Design.SolovevOnePlasma
