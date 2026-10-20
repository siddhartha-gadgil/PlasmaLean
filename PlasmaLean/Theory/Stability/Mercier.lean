/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Equilibrium.ScrewPinch

/-!
# The Mercier criterion in the cylindrical and large-aspect-ratio limits

The Mercier criterion (C. Mercier, Nucl. Fusion Suppl. 1962; J. M. Greene and
J. L. Johnson, Phys. Fluids 5, 510 (1962); general 3-D form in F. Bauer, O. Betancourt,
P. Garabedian, *Magnetohydrodynamic Equilibrium and Stability of Stellarators*, 1984) is
the necessary condition for stability of ideal-MHD interchange modes localized at a
rational surface. We use the Greene–Johnson index `D_I` with stability `D_I < 0`
(Mercier's own `D_M` and later `D_Merc` differ by sign and normalization; we do not
use them). Its general toroidal expression involves flux-surface averages of the
equilibrium; it is NOT formalized here. This module only records two limits that are
standard and can be tied to results already in the library.

**Cylindrical (screw-pinch) limit — Suydam.** In a straight periodic cylinder the
Mercier index reduces to

  `D_I = -1/4 - 2 μ₀ p' / (r Bz² (q'/q)²)`   (`mercierDI`),

and `mercier_iff_suydam` shows `D_I ≤ 0 ⟺ suydamQuantity ≥ 0` on every surface with
nonzero shear (`suydamQuantity_eq` is the exact identity
`suydamQuantity = -(r Bz² (q'/q)²/(2μ₀)) · D_I`). Thus the cylindrical Mercier
criterion is literally Suydam's criterion of
`PlasmaLean.Equilibrium.ScrewPinch`, and the localized Hardy-inequality results apply
(`localized_stable_of_mercier`). The value `-1/4` at zero pressure gradient
(`mercierDI_flat`) is the sharp Hardy constant of the Suydam module.

Caveat (Lean division): on a shearless surface `q' = 0` (or where `S = 0`) the formula
divides by zero and Lean returns `D_I = -1/4`, which would be spuriously "stable".
`MercierStableOn` therefore REQUIRES `S > 0` and nonzero shear on every surface
(`not_mercierStableOn_of_shearless`), and every pointwise link theorem assumes them; on
shearless surfaces use `suydam_fails_shearless`.

**Large-aspect-ratio circular tokamak (Shafranov–Yurchenko form).** To leading order in
the inverse aspect ratio the toroidal average curvature adds a factor `(1 - q²)` to the
pressure drive (V. D. Shafranov and E. I. Yurchenko, Sov. Phys. JETP 26, 682 (1968);
Freidberg, *Ideal MHD*, 2014, tokamak chapter):

  `r Bz² (q'/q)²/(8μ₀) + p' (1 - q²) ≥ 0`.

This is a SUPPLIED formula (a definition with sanity checks only, not derived here).
`mercierTokamakQ` takes `q` as a free function (the caller must supply the safety
factor of the same profiles); `mercierTokamak` builds `q` from `safetyFactor R₀ Bθ S`,
consistently with the shear `q'/q = shearRatio`.
Checks: it equals `suydamQuantity - q² p'` (`mercierTokamakQ_eq`); for `p' ≤ 0` Suydam
implies it (`mercierTokamakQ_of_suydam`), and `q ≥ 1` makes it hold with no shear at all
(`mercierTokamakQ_of_q_ge_one`, `mercierTokamak_of_safetyFactor_ge_one`;
favourable average curvature).

Scope: local interchange conditions only (necessary conditions); no global, ballooning,
free-boundary, resistive or kinetic statement, and no general 3-D `D_M`.
-/
public section

noncomputable section
namespace PlasmaLean.Stability.Mercier
open Set PlasmaLean.Stability PlasmaLean.Equilibrium.ScrewPinch

/-- Cylindrical Mercier index `D_I = -1/4 - 2 μ₀ p' / (r S (q'/q)²)`, `S = Bz²`. -/
@[expose] def mercierDI (μ₀ : ℝ) (p' Bθ S Bθ' S' : ℝ → ℝ) (r : ℝ) : ℝ :=
  -1 / 4 - 2 * μ₀ * p' r / (r * S r * shearRatio Bθ S Bθ' S' r ^ 2)

/-- Cylindrical Mercier stability on `(0, a]`: on every surface `S > 0`, the shear is
nonzero (so `D_I` is a genuine quotient) and `D_I ≤ 0`. -/
@[expose] def MercierStableOn (μ₀ a : ℝ) (p' Bθ S Bθ' S' : ℝ → ℝ) : Prop :=
  ∀ r ∈ Ioc 0 a, 0 < S r ∧ shearRatio Bθ S Bθ' S' r ≠ 0 ∧ mercierDI μ₀ p' Bθ S Bθ' S' r ≤ 0

/-- Exact identity: `suydamQuantity = -(r S (q'/q)²/(2μ₀)) · D_I` when the shear term is
nonzero. -/
theorem suydamQuantity_eq {μ₀ r : ℝ} {p' Bθ S Bθ' S' : ℝ → ℝ} (hμ : μ₀ ≠ 0)
    (hD : r * S r * shearRatio Bθ S Bθ' S' r ^ 2 ≠ 0) :
    suydamQuantity μ₀ p' Bθ S Bθ' S' r =
      -(r * S r * shearRatio Bθ S Bθ' S' r ^ 2 / (2 * μ₀)) * mercierDI μ₀ p' Bθ S Bθ' S' r := by
  have h3 := hD
  simp only [mul_ne_zero_iff, pow_ne_zero_iff two_ne_zero, ne_eq] at h3
  obtain ⟨⟨hr, hS⟩, hX⟩ := h3
  unfold suydamQuantity mercierDI
  field_simp
  ring

/-- **Cylindrical Mercier = Suydam.** On a surface with `r > 0`, `S > 0` and nonzero
shear, `D_I ≤ 0` iff Suydam's criterion holds there. -/
theorem mercier_iff_suydam {μ₀ r : ℝ} {p' Bθ S Bθ' S' : ℝ → ℝ} (hμ : 0 < μ₀) (hr : 0 < r)
    (hS : 0 < S r) (hsh : shearRatio Bθ S Bθ' S' r ≠ 0) :
    mercierDI μ₀ p' Bθ S Bθ' S' r ≤ 0 ↔ 0 ≤ suydamQuantity μ₀ p' Bθ S Bθ' S' r := by
  have hpos : 0 < r * S r * shearRatio Bθ S Bθ' S' r ^ 2 / (2 * μ₀) := by positivity
  rw [suydamQuantity_eq hμ.ne' (by positivity)]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- Strict version: `D_I < 0` iff Suydam holds strictly. -/
theorem mercier_lt_iff_suydam {μ₀ r : ℝ} {p' Bθ S Bθ' S' : ℝ → ℝ} (hμ : 0 < μ₀)
    (hr : 0 < r) (hS : 0 < S r) (hsh : shearRatio Bθ S Bθ' S' r ≠ 0) :
    mercierDI μ₀ p' Bθ S Bθ' S' r < 0 ↔ 0 < suydamQuantity μ₀ p' Bθ S Bθ' S' r := by
  have hpos : 0 < r * S r * shearRatio Bθ S Bθ' S' r ^ 2 / (2 * μ₀) := by positivity
  rw [suydamQuantity_eq hμ.ne' (by positivity)]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- Profile version: with nonzero shear on `(0, a]`, cylindrical Mercier stability is
`SuydamStableOn`. -/
theorem mercierStableOn_iff {μ₀ a : ℝ} {p' Bθ S Bθ' S' : ℝ → ℝ} (hμ : 0 < μ₀)
    (hS : ∀ r ∈ Ioc 0 a, 0 < S r) (hsh : ∀ r ∈ Ioc 0 a, shearRatio Bθ S Bθ' S' r ≠ 0) :
    MercierStableOn μ₀ a p' Bθ S Bθ' S' ↔ SuydamStableOn μ₀ a p' Bθ S Bθ' S' :=
  forall₂_congr fun r hr => by
    rw [← mercier_iff_suydam hμ hr.1 (hS r hr) (hsh r hr)]
    exact ⟨fun h => h.2.2, fun h => ⟨hS r hr, hsh r hr, h⟩⟩

/-- The guarded predicate implies Suydam with no extra hypotheses. -/
theorem MercierStableOn.suydam {μ₀ a : ℝ} {p' Bθ S Bθ' S' : ℝ → ℝ} (hμ : 0 < μ₀)
    (h : MercierStableOn μ₀ a p' Bθ S Bθ' S') : SuydamStableOn μ₀ a p' Bθ S Bθ' S' :=
  fun r hr => (mercier_iff_suydam hμ hr.1 (h r hr).1 (h r hr).2.1).mp (h r hr).2.2

/-- Sanity (no spurious stability): a shearless surface in `(0, a]` violates
`MercierStableOn`, even though Lean's `mercierDI` evaluates to `-1/4` there. -/
theorem not_mercierStableOn_of_shearless {μ₀ a r : ℝ} {p' Bθ S Bθ' S' : ℝ → ℝ}
    (hr : r ∈ Ioc 0 a) (hsh : shearRatio Bθ S Bθ' S' r = 0) :
    ¬ MercierStableOn μ₀ a p' Bθ S Bθ' S' := fun h => (h r hr).2.1 hsh

/-- Sanity: with no pressure gradient, `D_I = -1/4`, the sharp Hardy constant. -/
theorem mercierDI_flat {μ₀ r : ℝ} {p' Bθ S Bθ' S' : ℝ → ℝ} (hp : p' r = 0) :
    mercierDI μ₀ p' Bθ S Bθ' S' r = -1 / 4 := by
  simp [mercierDI, hp]

/-- Sanity: a pressure decreasing outward raises `D_I` above `-1/4` (destabilizing). -/
theorem mercierDI_gt_of_pressure_decreasing {μ₀ r : ℝ} {p' Bθ S Bθ' S' : ℝ → ℝ}
    (hμ : 0 < μ₀) (hr : 0 < r) (hS : 0 < S r) (hsh : shearRatio Bθ S Bθ' S' r ≠ 0)
    (hp : p' r < 0) : -1 / 4 < mercierDI μ₀ p' Bθ S Bθ' S' r := by
  unfold mercierDI
  have : 2 * μ₀ * p' r / (r * S r * shearRatio Bθ S Bθ' S' r ^ 2) < 0 :=
    div_neg_of_neg_of_pos (by nlinarith) (by positivity)
  linarith

/-- Link to the localized form: where `D_I ≤ 0` (nonzero shear), the model localized
interchange energy is nonnegative (`localized_stable`). -/
theorem localized_stable_of_mercier {μ₀ c r x₀ x₁ : ℝ} {p' Bθ S Bθ' S' ξ ξ' : ℝ → ℝ}
    (hμ : 0 < μ₀) (hc : 0 ≤ c) (hr : 0 < r) (hS : 0 < S r)
    (hsh : shearRatio Bθ S Bθ' S' r ≠ 0) (hM : mercierDI μ₀ p' Bθ S Bθ' S' r ≤ 0)
    (hle : x₀ ≤ x₁) (hξ : C1On ξ ξ' x₀ x₁) (h₀ : ξ x₀ = 0) (h₁ : ξ x₁ = 0) :
    0 ≤ suydamForm (localF μ₀ c Bθ S Bθ' S' r) (localG c p' r) x₀ x₁ ξ ξ' :=
  localized_stable hμ hc hr.le hS.le ((mercier_iff_suydam hμ hr hS hsh).mp hM) hle hξ h₀ h₁

/-- Link to the localized form, necessity: where `D_I > 0` (nonzero shear), arbitrarily
localized displacements with negative model energy exist (`localized_unstable`). -/
theorem localized_unstable_of_mercier {μ₀ c r ε : ℝ} {p' Bθ S Bθ' S' : ℝ → ℝ}
    (hμ : 0 < μ₀) (hc : 0 < c) (hr : 0 < r) (hS : 0 < S r)
    (hsh : shearRatio Bθ S Bθ' S' r ≠ 0) (hM : 0 < mercierDI μ₀ p' Bθ S Bθ' S' r)
    (hε : 0 < ε) :
    ∃ x₀ x₁ : ℝ, ∃ ξ ξ' : ℝ → ℝ, 0 < x₀ ∧ x₀ ≤ x₁ ∧ x₁ < ε ∧ C1On ξ ξ' x₀ x₁ ∧
      ξ x₀ = 0 ∧ ξ x₁ = 0 ∧
      suydamForm (localF μ₀ c Bθ S Bθ' S' r) (localG c p' r) x₀ x₁ ξ ξ' < 0 := by
  have : suydamQuantity μ₀ p' Bθ S Bθ' S' r < 0 := by
    by_contra h
    push Not at h
    exact absurd ((mercier_iff_suydam hμ hr hS hsh).mpr h) (not_le.mpr hM)
  exact localized_unstable hμ hc hr.le hS.le this hε

/-! ## Large-aspect-ratio tokamak form (supplied formula, sanity checks only) -/

/-- Shafranov–Yurchenko large-aspect-ratio Mercier quantity
`r S (q'/q)²/(8μ₀) + p' (1 - q²)` with `q` a free function. Consistency requirement
(not enforced): `q` must be the safety factor of the same profiles, as in
`mercierTokamak`. -/
@[expose] def mercierTokamakQ (μ₀ : ℝ) (q p' Bθ S Bθ' S' : ℝ → ℝ) (r : ℝ) : ℝ :=
  r * S r * shearRatio Bθ S Bθ' S' r ^ 2 / (8 * μ₀) + p' r * (1 - q r ^ 2)

/-- The large-aspect-ratio Mercier quantity with `q = safetyFactor R₀ Bθ S`
(`q = r Bz/(R₀ Bθ)`), consistent with `shearRatio = q'/q`. -/
@[expose] def mercierTokamak (μ₀ R₀ : ℝ) (p' Bθ S Bθ' S' : ℝ → ℝ) (r : ℝ) : ℝ :=
  mercierTokamakQ μ₀ (safetyFactor R₀ Bθ S) p' Bθ S Bθ' S' r

/-- The toroidal form is Suydam plus the average-curvature term `-q² p'`. -/
theorem mercierTokamakQ_eq (μ₀ : ℝ) (q p' Bθ S Bθ' S' : ℝ → ℝ) (r : ℝ) :
    mercierTokamakQ μ₀ q p' Bθ S Bθ' S' r =
      suydamQuantity μ₀ p' Bθ S Bθ' S' r - q r ^ 2 * p' r := by
  unfold mercierTokamakQ suydamQuantity; ring

/-- Sanity: with outward-decreasing pressure, Suydam implies the toroidal criterion
(toroidal average curvature is favourable at large aspect ratio). -/
theorem mercierTokamakQ_of_suydam {μ₀ r : ℝ} {q p' Bθ S Bθ' S' : ℝ → ℝ}
    (hs : 0 ≤ suydamQuantity μ₀ p' Bθ S Bθ' S' r) (hp : p' r ≤ 0) :
    0 ≤ mercierTokamakQ μ₀ q p' Bθ S Bθ' S' r := by
  rw [mercierTokamakQ_eq]
  nlinarith [sq_nonneg (q r)]

/-- Sanity: `q ≥ 1` with outward-decreasing pressure satisfies the toroidal criterion
without any shear. -/
theorem mercierTokamakQ_of_q_ge_one {μ₀ r : ℝ} {q p' Bθ S Bθ' S' : ℝ → ℝ} (hμ : 0 < μ₀)
    (hr : 0 ≤ r) (hS : 0 ≤ S r) (hq : 1 ≤ q r ^ 2) (hp : p' r ≤ 0) :
    0 ≤ mercierTokamakQ μ₀ q p' Bθ S Bθ' S' r := by
  unfold mercierTokamakQ
  have : 0 ≤ p' r * (1 - q r ^ 2) := mul_nonneg_of_nonpos_of_nonpos hp (by linarith)
  positivity

/-- Sanity: dropping the toroidal term (`q = 0` in the curvature factor) recovers the
Suydam quantity exactly. -/
theorem mercierTokamakQ_zero_q (μ₀ : ℝ) (p' Bθ S Bθ' S' : ℝ → ℝ) (r : ℝ) :
    mercierTokamakQ μ₀ (fun _ => 0) p' Bθ S Bθ' S' r =
      suydamQuantity μ₀ p' Bθ S Bθ' S' r := by
  simp [mercierTokamakQ_eq]

/-- Consistent version: `q ≥ 1` (from the actual safety factor) with outward-decreasing
pressure satisfies the large-aspect-ratio criterion. -/
theorem mercierTokamak_of_safetyFactor_ge_one {μ₀ R₀ r : ℝ} {p' Bθ S Bθ' S' : ℝ → ℝ}
    (hμ : 0 < μ₀) (hr : 0 ≤ r) (hS : 0 ≤ S r) (hq : 1 ≤ safetyFactor R₀ Bθ S r)
    (hp : p' r ≤ 0) : 0 ≤ mercierTokamak μ₀ R₀ p' Bθ S Bθ' S' r :=
  mercierTokamakQ_of_q_ge_one hμ hr hS (by nlinarith) hp

end PlasmaLean.Stability.Mercier
