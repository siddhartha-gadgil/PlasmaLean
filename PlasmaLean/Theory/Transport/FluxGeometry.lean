/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Transport.Comparison
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Flux-surface geometry for radial transport, mean values, and coefficient enclosures

The kernel operator `N[T] = (1/V') ∂ψ (V' D ∂ψT) + R` needs `V'`, `V''`, `D`, `D'` as functions
of the flux label. For a non-symmetric equilibrium these are flux-surface averages that are
rarely available in closed form. This module isolates what the barrier theorems actually need.

## Flux geometry

`FluxGeometry` bundles `V'`, `V''`, `g = ⟨|∇ψ|²⟩`, `g'` and `h = ⟨Δψ⟩` (flux-surface
averages). Its laws (`FluxGeometry.Laws`) are `V' > 0`, the supplied derivatives, `g(0) = 0`
(the label vanishes on the axis, where `∇ψ = 0`), and the **Gauss identity**
`(V' g)' = V' h`: `V'⟨|∇ψ|²⟩ = ∮ |∇ψ| dS = ∫_{ψ' ≤ ψ} Δψ dV` by the divergence theorem, and
`d/dψ ∫_{ψ' ≤ ψ} f dV = V'⟨f⟩` by the coarea formula. (These two classical identities are the
reason the laws hold for a real equilibrium; they are recorded as laws, not proved.)

With a diffusivity profile `χ(ψ)` (derivative `χ'`) the transport coefficients are
`D = χ g`, `D' = χ' g + χ g'` (`FluxGeometry.coeffs`, with a `degenerate` axis), and the
operator becomes `N[T] = χ g T'' + (χ' g + χ h) T' + R` (`FluxGeometry.coeffs_op`).

## Enclosures from the Gauss identity

Pointwise bounds on `|∇ψ|²` over a flux surface give only crude bounds on its average (for an
elliptic surface `|∇ψ|²` varies by a factor ≈ 1.7). The Gauss identity does better: if
`H_lo ≤ h ≤ H_hi` and `|V''/V'| ≤ λ`, then
`H_lo ψ (1 − κψ) ≤ g(ψ) ≤ H_hi ψ (1 + κψ)` for `2κ ≥ λ(1+κ)` (`FluxGeometry.g_le`,
`FluxGeometry.le_g`), and `V'(0)(1 − μψ) ≤ V'(ψ) ≤ V'(0)(1 + μψ)` for `μ ≥ λ(1+μ)`
(`FluxGeometry.Vp_le`, `FluxGeometry.le_Vp`). These are proved by monotonicity.

## Mean values

`IsMeanValue g Σ m`: every pair of bounds for `g` on the set `Σ` also bounds `m`. Every average
of `g` against a probability measure carried by `Σ` is a mean value
(`isMeanValue_integral`), and so is every ratio `∫ f₂ dμ / ∫ f₁ dμ` with `f₁ > 0` on `Σ` with
respect to the pointwise ratio `f₂/f₁` (`isMeanValue_ratio_integral`). This is how
flux-surface averages are linked to pointwise bounds on flux surfaces.
-/

public section

noncomputable section

namespace PlasmaLean.Transport

open Set MeasureTheory

/-! ### Mean values -/

/-- `m` is a **mean value** of `g` over the set `Σ`: every pair of bounds for `g` on `Σ` also
bounds `m`. (For continuous `g` on a compact connected `Σ` this says `m ∈ g(Σ)`.) -/
def IsMeanValue {α : Type*} (g : α → ℝ) (S : Set α) (m : ℝ) : Prop :=
  ∀ lo hi : ℝ, (∀ x ∈ S, lo ≤ g x ∧ g x ≤ hi) → lo ≤ m ∧ m ≤ hi

/-- A value of `g` at a point of `Σ` is a mean value of `g` over `Σ`. -/
theorem IsMeanValue.of_mem {α : Type*} {g : α → ℝ} {S : Set α} {x : α} (hx : x ∈ S) :
    IsMeanValue g S (g x) := fun _ _ h => h x hx

/-- Sanity (degenerate case): over the empty set nothing is a mean value. -/
theorem not_isMeanValue_empty {α : Type*} (g : α → ℝ) (m : ℝ) : ¬ IsMeanValue g ∅ m := by
  intro h
  have := h (m + 1) m (fun x hx => absurd hx (notMem_empty x))
  linarith [this.1]

/-- Pointwise bounds on `Σ` bound every mean value. -/
theorem IsMeanValue.bounds {α : Type*} {g : α → ℝ} {S : Set α} {m lo hi : ℝ}
    (h : IsMeanValue g S m) (hb : ∀ x ∈ S, lo ≤ g x ∧ g x ≤ hi) : lo ≤ m ∧ m ≤ hi :=
  h lo hi hb

/-- **Averages are mean values.** For a probability measure `μ` carried by `Σ` (`μ Sᶜ = 0`)
and integrable `g`, the average `∫ g dμ` is a mean value of `g` over `Σ`. -/
theorem isMeanValue_integral {α : Type*} [MeasurableSpace α] {g : α → ℝ} {S : Set α}
    (μ : Measure α) [IsProbabilityMeasure μ] (hS : μ Sᶜ = 0) (hg : Integrable g μ) :
    IsMeanValue g S (∫ x, g x ∂μ) := by
  intro lo hi hb
  have hae : ∀ᵐ x ∂μ, x ∈ S := ae_iff.2 hS
  constructor
  · have := integral_mono_ae (integrable_const lo) hg
      (hae.mono fun x hx => (hb x hx).1)
    simpa using this
  · have := integral_mono_ae hg (integrable_const hi)
      (hae.mono fun x hx => (hb x hx).2)
    simpa using this

/-- **Ratios of averages are mean values of the pointwise ratio.** If `f₁ > 0` on `Σ`, `μ` is
carried by `Σ` and `∫ f₁ dμ > 0`, then `∫ f₂ dμ / ∫ f₁ dμ` is a mean value of `f₂ / f₁` over
`Σ` (it is the average of `f₂/f₁` for the weighted measure `f₁ dμ / ∫ f₁ dμ`). -/
theorem isMeanValue_ratio_integral {α : Type*} [MeasurableSpace α] {f₁ f₂ : α → ℝ}
    {S : Set α} (μ : Measure α) (hS : μ Sᶜ = 0) (h₁ : Integrable f₁ μ)
    (h₂ : Integrable f₂ μ) (hpos : ∀ x ∈ S, 0 < f₁ x) (hI : 0 < ∫ x, f₁ x ∂μ) :
    IsMeanValue (fun x => f₂ x / f₁ x) S ((∫ x, f₂ x ∂μ) / ∫ x, f₁ x ∂μ) := by
  intro lo hi hb
  have hae : ∀ᵐ x ∂μ, x ∈ S := ae_iff.2 hS
  have hlo : ∫ x, lo * f₁ x ∂μ ≤ ∫ x, f₂ x ∂μ :=
    integral_mono_ae (h₁.const_mul lo) h₂ (hae.mono fun x hx => by
      have := (hb x hx).1
      rwa [le_div_iff₀ (hpos x hx)] at this)
  have hhi : ∫ x, f₂ x ∂μ ≤ ∫ x, hi * f₁ x ∂μ :=
    integral_mono_ae h₂ (h₁.const_mul hi) (hae.mono fun x hx => by
      have := (hb x hx).2
      rwa [div_le_iff₀ (hpos x hx)] at this)
  rw [integral_const_mul] at hlo hhi
  exact ⟨by rw [le_div_iff₀ hI]; linarith, by rw [div_le_iff₀ hI]; linarith⟩

/-! ### A monotonicity tool -/

/-- If `F(0) ≥ 0` and `F' ≥ 0` on `(0,1)` (with one-sided derivatives on `[0,1]`), then
`F ≥ 0` on `[0,1]`. -/
theorem nonneg_of_deriv_nonneg_Icc {F F' : ℝ → ℝ}
    (hF : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt F (F' s) (Icc 0 1) s) (h0 : 0 ≤ F 0)
    (hF' : ∀ s ∈ Ioo (0 : ℝ) 1, 0 ≤ F' s) : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ F s := by
  have hmono : MonotoneOn F (Icc 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := F') (convex_Icc 0 1)
      (fun s hs => (hF s hs).continuousWithinAt) (fun s hs => ?_) (fun s hs => ?_)
    · rw [interior_Icc] at hs ⊢
      exact (hF s (Ioo_subset_Icc_self hs)).mono Ioo_subset_Icc_self
    · rw [interior_Icc] at hs; exact hF' s hs
  intro s hs
  exact h0.trans (hmono ⟨le_rfl, zero_le_one⟩ hs hs.1)

/-! ### Flux geometry -/

/-- Flux-surface geometry of a radial label `ψ ∈ [0,1]`: volume derivative `V'`, its derivative
`V''`, the average `g = ⟨|∇ψ|²⟩` with derivative `g'`, and the average `h = ⟨Δψ⟩`. -/
structure FluxGeometry where
  /-- Volume derivative `V'(ψ)`. -/
  Vp : ℝ → ℝ
  /-- Supplied derivative `V''(ψ)`. -/
  dVp : ℝ → ℝ
  /-- `g(ψ) = ⟨|∇ψ|²⟩`. -/
  g : ℝ → ℝ
  /-- Supplied derivative `g'(ψ)`. -/
  dg : ℝ → ℝ
  /-- `h(ψ) = ⟨Δψ⟩`. -/
  h : ℝ → ℝ

/-- Laws of a flux geometry on `[0,1]`: `V' > 0`, genuine derivatives, `g(0) = 0` (axis), and
the Gauss identity `(V' g)' = V' h` (divergence theorem plus coarea formula). -/
class FluxGeometry.Laws (G : FluxGeometry) : Prop where
  /-- `V' > 0`. -/
  Vp_pos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < G.Vp s
  /-- `dVp` is the derivative of `Vp`. -/
  Vp_deriv : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt G.Vp (G.dVp s) (Icc 0 1) s
  /-- `dg` is the derivative of `g`. -/
  g_deriv : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt G.g (G.dg s) (Icc 0 1) s
  /-- `⟨|∇ψ|²⟩ = 0` on the axis. -/
  g_zero : G.g 0 = 0
  /-- Gauss identity `(V' g)' = V' h`. -/
  gauss : ∀ s ∈ Icc (0 : ℝ) 1, G.dVp s * G.g s + G.Vp s * G.dg s = G.Vp s * G.h s

namespace FluxGeometry

variable (G : FluxGeometry)

/-- Transport coefficients from a flux geometry, a diffusivity profile `χ` with supplied
derivative `χ'`, a net source `R` posed on `Tdom`: `D = χ g`, `D' = χ' g + χ g'`, with a
`degenerate` axis (`D(0) = 0` since `g(0) = 0`). -/
@[expose] def coeffs (χ χ' : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (Tdom : Set ℝ) : RadialCoefficients :=
  ⟨G.Vp, G.dVp, fun s => χ s * G.g s, fun s => χ' s * G.g s + χ s * G.dg s, R, Tdom,
    .degenerate⟩

/-- **The operator in flux-geometry form**: `N[T] = χ g T'' + (χ' g + χ h) T' + R` on `[0,1]`
(the drift `D' + D V''/V'` equals `χ' g + χ h` by the Gauss identity). -/
theorem coeffs_op [hG : G.Laws] (χ χ' : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (Tdom : Set ℝ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (u uψ uψψ : ℝ) :
    (G.coeffs χ χ' R Tdom).op s u uψ uψψ =
      χ s * G.g s * uψψ + (χ' s * G.g s + χ s * G.h s) * uψ + R s u := by
  have hV := (hG.Vp_pos s hs).ne'
  have hg := hG.gauss s hs
  have : G.dg s + G.g s * G.dVp s / G.Vp s = G.h s := by
    field_simp; linarith
  simp only [RadialCoefficients.op, coeffs]
  rw [← this]; ring

/-- **The flux-geometry coefficients satisfy the kernel laws** (degenerate axis) when `χ ≥ 0`
and `g ≥ 0` on `[0,1]`, `χ'` is the derivative of `χ`, `Tdom` is open and `R` is continuous on
`[0,1] × Tdom`. -/
theorem coeffs_transportLaws [hG : G.Laws] {χ χ' : ℝ → ℝ} {R : ℝ → ℝ → ℝ} {Tdom : Set ℝ}
    (hχ : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ χ s)
    (hχ' : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt χ (χ' s) (Icc 0 1) s)
    (hg : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ G.g s) (hT : IsOpen Tdom)
    (hR : ContinuousOn (fun p : ℝ × ℝ => R p.1 p.2) (Icc 0 1 ×ˢ Tdom)) :
    TransportLaws (G.coeffs χ χ' R Tdom) where
  Vp_pos := hG.Vp_pos
  Vp_deriv := hG.Vp_deriv
  D_deriv := fun s hs => (hχ' s hs).mul (hG.g_deriv s hs)
  D_nonneg := fun s hs => mul_nonneg (hχ s hs) (hg s hs)
  D_axis := fun _ => by simp [coeffs, hG.g_zero]
  D_axis_regular := fun h => absurd h (by simp [coeffs])
  Tdom_open := hT
  R_cont := hR

/-- **Upper enclosure of `g = ⟨|∇ψ|²⟩` from the Gauss identity.** If `h ≤ H` on `[0,1]` and
`V''/V' ≥ −λ` on `(0,1)`, then `g(s) ≤ H s (1 + κ s)` whenever `λ (1 + κ) ≤ 2κ`. -/
theorem g_le [hG : G.Laws] {H lam κ : ℝ} (hH : 0 ≤ H) (hκ0 : 0 ≤ κ)
    (hκ : lam * (1 + κ) ≤ 2 * κ) (hh : ∀ s ∈ Icc (0 : ℝ) 1, G.h s ≤ H)
    (hV : ∀ s ∈ Ioo (0 : ℝ) 1, -lam * G.Vp s ≤ G.dVp s) :
    ∀ s ∈ Icc (0 : ℝ) 1, G.g s ≤ H * s * (1 + κ * s) := by
  have key := nonneg_of_deriv_nonneg_Icc
    (F := fun s => H * G.Vp s * (s * (1 + κ * s)) - G.Vp s * G.g s)
    (F' := fun s => H * (G.dVp s * (s * (1 + κ * s)) + G.Vp s * (1 + 2 * κ * s)) -
      (G.dVp s * G.g s + G.Vp s * G.dg s))
    (fun s hs => by
      have hp : HasDerivWithinAt (fun s : ℝ => s * (1 + κ * s)) (1 + 2 * κ * s) (Icc 0 1) s := by
        have := (hasDerivAt_id' s).mul ((hasDerivAt_id' s).const_mul κ |>.const_add 1)
        convert this.hasDerivWithinAt using 1
        ring
      have := (((hG.Vp_deriv s hs).const_mul H).mul hp).sub
        ((hG.Vp_deriv s hs).mul (hG.g_deriv s hs))
      convert this using 1
      ring)
    (by simp [hG.g_zero])
    (fun s hs => by
      have hs' := Ioo_subset_Icc_self hs
      rw [hG.gauss s hs']
      have hVp := hG.Vp_pos s hs'
      have h1 := hh s hs'
      have h2 := hV s hs
      have : G.Vp s * G.h s ≤ G.Vp s * H := mul_le_mul_of_nonneg_left h1 hVp.le
      have h3 : 0 ≤ H * G.Vp s * s * (2 * κ - lam * (1 + κ * s)) := by
        have : lam * (1 + κ * s) ≤ 2 * κ := by
          rcases le_total 0 lam with hl | hl
          · nlinarith [mul_le_mul_of_nonneg_left hs.2.le (mul_nonneg hl hκ0)]
          · nlinarith [mul_nonneg (neg_nonneg.2 hl) (mul_nonneg hκ0 hs.1.le)]
        have := hs.1.le
        positivity
      nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg hH (mul_nonneg hs.1.le
        (by nlinarith [hs.1] : (0 : ℝ) ≤ 1 + κ * s)))])
  intro s hs
  have hk := key s hs
  have hVp := hG.Vp_pos s hs
  have : G.Vp s * G.g s ≤ G.Vp s * (H * s * (1 + κ * s)) := by nlinarith
  exact le_of_mul_le_mul_left this hVp

/-- **Lower enclosure of `g = ⟨|∇ψ|²⟩` from the Gauss identity.** If `H ≤ h` on `[0,1]` and
`V''/V' ≤ λ` on `(0,1)`, then `H s (1 − κ s) ≤ g(s)` whenever `λ ≤ 2κ` and `κ ≤ 1`. -/
theorem le_g [hG : G.Laws] {H lam κ : ℝ} (hH : 0 ≤ H) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hκ : lam ≤ 2 * κ) (hh : ∀ s ∈ Icc (0 : ℝ) 1, H ≤ G.h s)
    (hV : ∀ s ∈ Ioo (0 : ℝ) 1, G.dVp s ≤ lam * G.Vp s) :
    ∀ s ∈ Icc (0 : ℝ) 1, H * s * (1 - κ * s) ≤ G.g s := by
  have key := nonneg_of_deriv_nonneg_Icc
    (F := fun s => G.Vp s * G.g s - H * G.Vp s * (s * (1 - κ * s)))
    (F' := fun s => (G.dVp s * G.g s + G.Vp s * G.dg s) -
      H * (G.dVp s * (s * (1 - κ * s)) + G.Vp s * (1 - 2 * κ * s)))
    (fun s hs => by
      have hp : HasDerivWithinAt (fun s : ℝ => s * (1 - κ * s)) (1 - 2 * κ * s) (Icc 0 1) s := by
        have := (hasDerivAt_id' s).mul ((hasDerivAt_id' s).const_mul κ |>.const_sub 1)
        convert this.hasDerivWithinAt using 1
        ring
      have := ((hG.Vp_deriv s hs).mul (hG.g_deriv s hs)).sub
        (((hG.Vp_deriv s hs).const_mul H).mul hp)
      convert this using 1
      ring)
    (by simp [hG.g_zero])
    (fun s hs => by
      have hs' := Ioo_subset_Icc_self hs
      rw [hG.gauss s hs']
      have hVp := hG.Vp_pos s hs'
      have h1 := hh s hs'
      have h2 := hV s hs
      have : G.Vp s * H ≤ G.Vp s * G.h s := mul_le_mul_of_nonneg_left h1 hVp.le
      have hsk : 0 ≤ 1 - κ * s := by
        nlinarith [mul_le_mul_of_nonneg_left hs.2.le hκ0]
      have h3 : 0 ≤ H * G.Vp s * s * (2 * κ - lam * (1 - κ * s)) := by
        have : lam * (1 - κ * s) ≤ 2 * κ := by
          rcases le_total 0 lam with hl | hl
          · nlinarith [mul_nonneg (mul_nonneg hl hκ0) hs.1.le]
          · nlinarith [mul_nonneg (neg_nonneg.2 hl) hsk]
        have := hs.1.le
        positivity
      nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg hH (mul_nonneg hs.1.le hsk))])
  intro s hs
  have hk := key s hs
  have hVp := hG.Vp_pos s hs
  have : G.Vp s * (H * s * (1 - κ * s)) ≤ G.Vp s * G.g s := by nlinarith
  exact le_of_mul_le_mul_left this hVp

/-- **Upper enclosure of `V'`.** If `V''/V' ≤ λ` on `(0,1)` and `λ (1 + μ) ≤ μ`, then
`V'(s) ≤ V'(0) (1 + μ s)` on `[0,1]`. -/
theorem Vp_le [hG : G.Laws] {lam μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : lam * (1 + μ) ≤ μ)
    (hV : ∀ s ∈ Ioo (0 : ℝ) 1, G.dVp s ≤ lam * G.Vp s) :
    ∀ s ∈ Icc (0 : ℝ) 1, G.Vp s ≤ G.Vp 0 * (1 + μ * s) := by
  have hpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < 1 + μ * s := fun s hs => by nlinarith [hs.1]
  have key := nonneg_of_deriv_nonneg_Icc
    (F := fun s => G.Vp 0 - G.Vp s / (1 + μ * s))
    (F' := fun s => -((G.dVp s * (1 + μ * s) - G.Vp s * μ) / (1 + μ * s) ^ 2))
    (fun s hs => by
      have hd : HasDerivWithinAt (fun s : ℝ => 1 + μ * s) μ (Icc 0 1) s := by
        simpa using ((hasDerivAt_id s).const_mul μ |>.const_add 1).hasDerivWithinAt
      exact ((hG.Vp_deriv s hs).div hd (hpos s hs).ne').const_sub _)
    (by simp)
    (fun s hs => by
      have hs' := Ioo_subset_Icc_self hs
      have hVp := hG.Vp_pos s hs'
      have h2 := hV s hs
      have hl : lam * (1 + μ * s) ≤ μ := by
        rcases le_total 0 lam with hl | hl
        · nlinarith [mul_le_mul_of_nonneg_left hs.2.le (mul_nonneg hl hμ0)]
        · nlinarith [mul_nonneg (neg_nonneg.2 hl) (hpos s hs').le]
      have : G.dVp s * (1 + μ * s) - G.Vp s * μ ≤ 0 := by
        nlinarith [mul_le_mul_of_nonneg_right h2 (hpos s hs').le]
      have := div_nonpos_of_nonpos_of_nonneg this (sq_nonneg (1 + μ * s))
      linarith)
  intro s hs
  have hk := key s hs
  have := hpos s hs
  rw [sub_nonneg, div_le_iff₀ this] at hk
  linarith

/-- **Lower enclosure of `V'`.** If `V''/V' ≥ −λ` on `(0,1)` and `λ (1 + μ) ≤ μ`, then
`V'(0) (1 − μ s) ≤ V'(s)` on `[0,1]`. -/
theorem le_Vp [hG : G.Laws] {lam μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : lam * (1 + μ) ≤ μ)
    (hV : ∀ s ∈ Ioo (0 : ℝ) 1, -lam * G.Vp s ≤ G.dVp s) :
    ∀ s ∈ Icc (0 : ℝ) 1, G.Vp 0 * (1 - μ * s) ≤ G.Vp s := by
  have hpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < 1 + μ * s := fun s hs => by nlinarith [hs.1]
  have key := nonneg_of_deriv_nonneg_Icc
    (F := fun s => G.Vp s * (1 + μ * s) - G.Vp 0)
    (F' := fun s => G.dVp s * (1 + μ * s) + G.Vp s * μ)
    (fun s hs => by
      have hd : HasDerivWithinAt (fun s : ℝ => 1 + μ * s) μ (Icc 0 1) s := by
        simpa using ((hasDerivAt_id s).const_mul μ |>.const_add 1).hasDerivWithinAt
      exact ((hG.Vp_deriv s hs).mul hd).sub_const _)
    (by simp)
    (fun s hs => by
      have hs' := Ioo_subset_Icc_self hs
      have hVp := hG.Vp_pos s hs'
      have h2 := hV s hs
      have hl : lam * (1 + μ * s) ≤ μ := by
        rcases le_total 0 lam with hl | hl
        · nlinarith [mul_le_mul_of_nonneg_left hs.2.le (mul_nonneg hl hμ0)]
        · nlinarith [mul_nonneg (neg_nonneg.2 hl) (hpos s hs').le]
      nlinarith [mul_le_mul_of_nonneg_right h2 (hpos s hs').le])
  intro s hs
  have hk := key s hs
  have hVp0 := hG.Vp_pos 0 ⟨le_rfl, zero_le_one⟩
  have hVp := hG.Vp_pos s hs
  nlinarith [mul_nonneg hVp0.le (sq_nonneg (μ * s)), hpos s hs]

end FluxGeometry

/-! ### Sanity checks -/

/-- Sanity (special case): the cylinder `ψ = r²/a²` with `V'` constant has `g = 4ψ/a²` and
`h = 4/a²`, which satisfy the Gauss identity; here with `a² = 4`, `V' = 1`. -/
@[expose] def cylGeometry : FluxGeometry := ⟨fun _ => 1, fun _ => 0, fun s => s, fun _ => 1,
  fun _ => 1⟩

/-- The cylinder geometry satisfies the flux-geometry laws. -/
instance : cylGeometry.Laws where
  Vp_pos := fun _ _ => one_pos
  Vp_deriv := fun _ _ => hasDerivWithinAt_const _ _ _
  g_deriv := fun s _ => (hasDerivAt_id s).hasDerivWithinAt
  g_zero := rfl
  gauss := fun _ _ => by simp [cylGeometry]

/-- Sanity: for the cylinder geometry (`λ = 0`, `h ≡ 1`) the enclosures are exact up to the
`κ` slack: `s (1 − κ s) ≤ g(s) = s ≤ s (1 + κ s)`. -/
theorem cylGeometry_enclosure {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    1 * s * (1 - 0 * s) ≤ cylGeometry.g s ∧ cylGeometry.g s ≤ 1 * s * (1 + 0 * s) :=
  ⟨cylGeometry.le_g (lam := 0) zero_le_one le_rfl zero_le_one (by norm_num) (fun _ _ => le_rfl)
      (fun _ _ => by simp [cylGeometry]) s hs,
    cylGeometry.g_le (lam := 0) zero_le_one le_rfl (by norm_num) (fun _ _ => le_rfl)
      (fun _ _ => by simp [cylGeometry]) s hs⟩

end PlasmaLean.Transport
