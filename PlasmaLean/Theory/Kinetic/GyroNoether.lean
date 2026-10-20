/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.Noether
public import PlasmaLean.Theory.Kinetic.GuidingCentre

/-!
# Gyro-integrated Noether identity (Theorem B, M4/T8)

Source: `notes/theory/guiding-centre-averaging.md` §2.2 (Theorem B, proved informally and
sympy-checked there; this file is the formal version).

Model (as in `Noether.lean`): non-relativistic Newton–Lorentz orbits `x' = v`,
`m v' = q v × B(x)` in a static magnetic field, `E = 0`; orbits are supplied. `K` is a Killing
field (`IsKilling K DK`), `ψ` has gradient `G`, and the Noether momentum is
`p_K = m ⟪K(x), v⟫ + q ψ(x)` with `p_K' = q ⟪v, δ(x)⟫`, where

* `defectVec B G K = B × K + G` is the **symmetry defect vector**
  (`SymmetricFlux B G K ↔ δ ≡ 0`, see `symmetricFlux_iff_defectVec_eq_zero`);
* `gyroCorr B G K = B × δ/|B|²` is the gyro-correction `U`.

Results:

* `gyro_defect_identity`: the pointwise algebra
  `q ⟪v, δ⟫ = q ⟪v,B⟫⟪B,δ⟫/|B|² - m ⟪U, (q/m) v × B⟫` for `B ≠ 0`;
* `gyroNoether_hasDerivAt` (**Theorem B**): with `Q = p_K + m ⟪U(x), v⟫`,
  `Q' = q ⟪v,B⟫⟪B,δ⟫/|B|² + m ⟪DU(x) v, v⟫` exactly, wherever `B(x) ≠ 0`;
* `gyroNoether_band`: if on a region `S` the field is nonzero, `|⟪B,δ⟫| ≤ δ_∥ |B|`,
  `|U| ≤ u`, `‖DU‖ ≤ u₁`, and the orbit stays in `S` on `[0,t]`, then with `s = |v(0)|`
  `|q| |ψ(x t) - ψ(x 0)| ≤ |m| s (|K(x t)| + |K(x 0)|) + 2 |m| s u + (|q| s δ_∥ + |m| s² u₁) t`;
* `gyroNoether_trapped_until`: the resulting finite-time confinement in `{ψ ≤ c'}`;
* `norm_gyroCorr_le`: `|U| ≤ |δ|/|B|` (so `u = sup|δ|/B_min` is admissible).

Compared with `noether_approx_band` (secular rate `|q| s |δ|`) the perpendicular part of the
defect now enters only through `|m| s² ‖DU‖ ≈ |q| s |δ| ρ_L/L_δ`.

Sanity checks: exact symmetry (`δ ≡ 0`) gives `U ≡ 0`, `Q = p_K`, and the band reduces to
the bound of `noether_flux_band` (`gyroNoether_band_exact`); an exact field-line first integral
(`⟪B, ∇ψ⟫ = 0`) kills the parallel term (`inner_field_defectVec`,
`gyroNoether_band_firstIntegral`); in a uniform field with translation symmetry and a
quadratic `ψ` (linear defect) `Q' = -m ε v₀ v₁/B₀` explicitly (`uniform_linear_defect_deriv`),
whereas `p_K' = q ε x₁ v₁` grows with the position.

The note's statements are correct as written. Two harmless strengthenings: the derivative of
`U` and `B ≠ 0` are only required along the orbit (not on all of space, where `U` may fail to
be differentiable), and `m ≠ 0` is not needed for the derivative identity itself.
-/
public section
noncomputable section
namespace PlasmaLean.Kinetic
open PlasmaLean.Fields PlasmaLean.Kinetic.GuidingCentre WithLp
open scoped RealInnerProductSpace

/-- The symmetry defect vector `δ = B × K + G`; `SymmetricFlux B G K` iff `δ ≡ 0`. -/
@[expose] def defectVec (B G K : Space → Space) (y : Space) : Space :=
  cross (B y) (K y) + G y

/-- The gyro-correction `U = B × δ/|B|²`. -/
@[expose] def gyroCorr (B G K : Space → Space) (y : Space) : Space :=
  (‖B y‖ ^ 2)⁻¹ • cross (B y) (defectVec B G K y)

/-- The gyro-corrected Noether momentum `Q = p_K + m ⟪U(x), v⟫`. -/
@[expose] def gyroMomentum (m q : ℝ) (B G K : Space → Space) (ψ : Space → ℝ)
    (x v : ℝ → Space) (t : ℝ) : ℝ :=
  noetherMomentum m q K ψ x v t + m * ⟪gyroCorr B G K (x t), v t⟫

/-- Scalar triple product: `⟪k, v × b⟫ = ⟪v, b × k⟫`. -/
theorem inner_cross_cyclic (k v b : Space) : ⟪k, cross v b⟫ = ⟪v, cross b k⟫ := by
  simp [cross, cross_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_three]
  ring

/-- Binet–Cauchy: `⟪b × d, v × b⟫ = ⟪b, v⟫ ⟪d, b⟫ - |b|² ⟪d, v⟫`. -/
theorem inner_cross_binet (b d v : Space) :
    ⟪cross b d, cross v b⟫ = ⟪b, v⟫ * ⟪d, b⟫ - ‖b‖ ^ 2 * ⟪d, v⟫ := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [cross, cross_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_three]
  ring

/-- The Noether torque plus `ψ`-rate is the defect paired with the velocity:
`⟪K, v × B⟫ + ⟪G, v⟫ = ⟪v, δ⟫`. -/
theorem noether_rate_eq_defect (B G K : Space → Space) (y v : Space) :
    ⟪K y, cross v (B y)⟫ + ⟪G y, v⟫ = ⟪v, defectVec B G K y⟫ := by
  rw [defectVec, inner_add_right, inner_cross_cyclic, real_inner_comm (G y)]

/-- Key pairing: `⟪U, v × β⟫ = ⟪v,β⟫⟪β,δ⟫/|β|² - ⟪v, δ⟫` for `β ≠ 0`. -/
theorem inner_gyro_cross (β δ v : Space) (hβ : β ≠ 0) :
    ⟪(‖β‖ ^ 2)⁻¹ • cross β δ, cross v β⟫ = ⟪v, β⟫ * ⟪β, δ⟫ / ‖β‖ ^ 2 - ⟪v, δ⟫ := by
  have hn : ‖β‖ ^ 2 ≠ 0 := by positivity
  rw [inner_smul_left, inner_cross_binet, real_inner_comm β v, real_inner_comm δ β,
    real_inner_comm δ v]
  simp only [RCLike.conj_to_real]
  field_simp

/-- **Gyro-defect identity** (the sympy identity of the note): for `β ≠ 0`, `m ≠ 0`,
`q ⟪v, δ⟫ = q ⟪v,β⟫⟪β,δ⟫/|β|² - m ⟪β × δ/|β|², (q/m) v × β⟫`. -/
theorem gyro_defect_identity (m q : ℝ) (hm : m ≠ 0) (β δ v : Space) (hβ : β ≠ 0) :
    q * ⟪v, δ⟫ = q * (⟪v, β⟫ * ⟪β, δ⟫ / ‖β‖ ^ 2)
      - m * ⟪(‖β‖ ^ 2)⁻¹ • cross β δ, (q / m) • cross v β⟫ := by
  rw [inner_smul_right, inner_gyro_cross β δ v hβ]
  field_simp
  ring

/-- **Theorem B (gyro-integrated Noether identity).** Along a Newton–Lorentz orbit in a static
field (`E = 0`), wherever `B(x r) ≠ 0` and `U` has derivative `DU` at `x r`,
`d/dt [p_K + m ⟪U(x), v⟫] = q ⟪v,B⟫⟪B,δ⟫/|B|² + m ⟪DU(x) v, v⟫` exactly. -/
theorem gyroNoether_hasDerivAt {m q : ℝ} {B G K : Space → Space}
    {DK : Space → Space →L[ℝ] Space} {DU : Space → Space →L[ℝ] Space} {ψ : Space → ℝ}
    {x v : ℝ → Space} (h : LorentzOrbit m q (fun _ => 0) B x v) (hK : IsKilling K DK)
    (hψ : ∀ y, HasFDerivAt ψ (innerSL ℝ (G y)) y) {r : ℝ}
    (hU : HasFDerivAt (gyroCorr B G K) (DU (x r)) (x r)) (hB : B (x r) ≠ 0) :
    HasDerivAt (gyroMomentum m q B G K ψ x v)
      (q * (⟪v r, B (x r)⟫ * ⟪B (x r), defectVec B G K (x r)⟫ / ‖B (x r)‖ ^ 2)
        + m * ⟪DU (x r) (v r), v r⟫) r := by
  obtain ⟨a, ha, hlaw⟩ := h.newton r
  have hN := noetherMomentum_hasDerivAt h hK hψ r
  have hUx : HasDerivAt (fun s => gyroCorr B G K (x s)) (DU (x r) (v r)) r :=
    hU.comp_hasDerivAt r (h.position r)
  have hin := (hUx.inner ℝ ha).const_mul m
  have hsum := hN.add hin
  convert hsum using 1
  · funext s; rfl
  have hma : m * ⟪gyroCorr B G K (x r), a⟫ =
      q * ⟪gyroCorr B G K (x r), cross (v r) (B (x r))⟫ := by
    rw [← inner_smul_right, hlaw, zero_add, inner_smul_right]
  have hrate := noether_rate_eq_defect B G K (x r) (v r)
  have hkey : ⟪gyroCorr B G K (x r), cross (v r) (B (x r))⟫ =
      ⟪v r, B (x r)⟫ * ⟪B (x r), defectVec B G K (x r)⟫ / ‖B (x r)‖ ^ 2 -
        ⟪v r, defectVec B G K (x r)⟫ := inner_gyro_cross _ _ _ hB
  linear_combination -hma - q * hrate - q * hkey

/-- `|U| ≤ |δ|/|B|`. -/
theorem norm_gyroCorr_le (B G K : Space → Space) (y : Space) :
    ‖gyroCorr B G K y‖ ≤ ‖defectVec B G K y‖ / ‖B y‖ := by
  rcases eq_or_ne (B y) 0 with h0 | h0
  · simp [gyroCorr, h0]
  have hpos : 0 < ‖B y‖ := norm_pos_iff.mpr h0
  rw [gyroCorr, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc (‖B y‖ ^ 2)⁻¹ * ‖cross (B y) (defectVec B G K y)‖
      ≤ (‖B y‖ ^ 2)⁻¹ * (‖B y‖ * ‖defectVec B G K y‖) := by gcongr; exact norm_cross_le _ _
    _ = _ := by field_simp

/-- Bound on the forcing rate of `Q`:
`|q ⟪v,β⟫⟪β,δ⟫/|β|² + m ⟪L v, v⟫| ≤ |q| |v| δ_∥ + |m| |v|² u₁`
when `|⟪β,δ⟫| ≤ δ_∥ |β|` and `‖L‖ ≤ u₁`. -/
theorem gyro_rate_le {m q δpar u₁ : ℝ} {β δ v : Space} {L : Space →L[ℝ] Space}
    (hβ : β ≠ 0) (hpar : |⟪β, δ⟫| ≤ δpar * ‖β‖) (hL : ‖L‖ ≤ u₁) :
    |q * (⟪v, β⟫ * ⟪β, δ⟫ / ‖β‖ ^ 2) + m * ⟪L v, v⟫| ≤
      |q| * ‖v‖ * δpar + |m| * ‖v‖ ^ 2 * u₁ := by
  have hpos : 0 < ‖β‖ := norm_pos_iff.mpr hβ
  have h1 : |⟪v, β⟫ * ⟪β, δ⟫ / ‖β‖ ^ 2| ≤ ‖v‖ * δpar := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < ‖β‖ ^ 2), div_le_iff₀ (by positivity)]
    have hv := abs_real_inner_le_norm v β
    calc |⟪v, β⟫| * |⟪β, δ⟫| ≤ (‖v‖ * ‖β‖) * (δpar * ‖β‖) :=
          mul_le_mul hv hpar (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have h2 : |⟪L v, v⟫| ≤ ‖v‖ ^ 2 * u₁ := by
    calc |⟪L v, v⟫| ≤ ‖L v‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖L‖ * ‖v‖) * ‖v‖ := by gcongr; exact L.le_opNorm v
      _ ≤ (u₁ * ‖v‖) * ‖v‖ := by gcongr
      _ = _ := by ring
  calc _ ≤ |q * (⟪v, β⟫ * ⟪β, δ⟫ / ‖β‖ ^ 2)| + |m * ⟪L v, v⟫| := abs_add_le _ _
    _ = |q| * |⟪v, β⟫ * ⟪β, δ⟫ / ‖β‖ ^ 2| + |m| * |⟪L v, v⟫| := by rw [abs_mul, abs_mul]
    _ ≤ |q| * (‖v‖ * δpar) + |m| * (‖v‖ ^ 2 * u₁) := by gcongr
    _ = _ := by ring

/-- Momentum difference bound (local copy of the private lemma in `Noether.lean`). -/
private theorem pairing_diff_le {m : ℝ} (a b u w : Space) (hs : ‖u‖ = ‖w‖) :
    |m * (⟪a, w⟫ - ⟪b, u⟫)| ≤ |m| * ‖w‖ * (‖b‖ + ‖a‖) := by
  rw [abs_mul, mul_assoc]
  gcongr
  calc |⟪a, w⟫ - ⟪b, u⟫| ≤ |⟪a, w⟫| + |⟪b, u⟫| := abs_sub _ _
    _ ≤ ‖a‖ * ‖w‖ + ‖b‖ * ‖u‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ = ‖w‖ * (‖b‖ + ‖a‖) := by rw [hs]; ring

/-- **Gyro-Noether band.** On a region `S` where `B ≠ 0`, `U` has derivative `DU`,
`|⟪B,δ⟫| ≤ δ_∥ |B|`, `|U| ≤ u` and `‖DU‖ ≤ u₁`, if the orbit stays in `S` on `[0,t]` then,
with `s = |v(0)|`,
`|q| |ψ(x t) - ψ(x 0)| ≤ |m| s (|K(x t)| + |K(x 0)|) + 2 |m| s u + (|q| s δ_∥ + |m| s² u₁) t`. -/
theorem gyroNoether_band {m q : ℝ} (hm : m ≠ 0) {B G K : Space → Space}
    {DK : Space → Space →L[ℝ] Space} {DU : Space → Space →L[ℝ] Space} {ψ : Space → ℝ}
    {x v : ℝ → Space} (h : LorentzOrbit m q (fun _ => 0) B x v) (hK : IsKilling K DK)
    (hψ : ∀ y, HasFDerivAt ψ (innerSL ℝ (G y)) y) {S : Set Space} {δpar u u₁ : ℝ}
    (hB0 : ∀ y ∈ S, B y ≠ 0) (hDU : ∀ y ∈ S, HasFDerivAt (gyroCorr B G K) (DU y) y)
    (hpar : ∀ y ∈ S, |⟪B y, defectVec B G K y⟫| ≤ δpar * ‖B y‖)
    (hu : ∀ y ∈ S, ‖gyroCorr B G K y‖ ≤ u) (hu₁ : ∀ y ∈ S, ‖DU y‖ ≤ u₁)
    {t : ℝ} (ht : 0 ≤ t) (hin : ∀ s ∈ Set.Icc 0 t, x s ∈ S) :
    |q| * |ψ (x t) - ψ (x 0)| ≤
      |m| * ‖v 0‖ * (‖K (x t)‖ + ‖K (x 0)‖) + 2 * |m| * ‖v 0‖ * u +
        (|q| * ‖v 0‖ * δpar + |m| * ‖v 0‖ ^ 2 * u₁) * t := by
  have hdrift := invariant_drift (K := gyroMomentum m q B G K ψ x v)
    (fun s hs => gyroNoether_hasDerivAt h hK hψ (hDU _ (hin s hs)) (hB0 _ (hin s hs)))
    (fun s hs => by
      have := gyro_rate_le (m := m) (q := q) (v := v s) (hB0 _ (hin s hs))
        (hpar _ (hin s hs)) (hu₁ _ (hin s hs))
      rwa [speed_conserved hm h s 0] at this) ⟨ht, le_rfl⟩
  have hx0 := hin 0 ⟨le_rfl, ht⟩
  have hxt := hin t ⟨ht, le_rfl⟩
  have hspeed := speed_conserved hm h t 0
  have hKd := pairing_diff_le (m := m) (K (x 0)) (K (x t)) (v t) (v 0) hspeed
  have hUd := pairing_diff_le (m := m) (gyroCorr B G K (x 0)) (gyroCorr B G K (x t))
    (v t) (v 0) hspeed
  have hUd' : |m * (⟪gyroCorr B G K (x 0), v 0⟫ - ⟪gyroCorr B G K (x t), v t⟫)| ≤
      2 * |m| * ‖v 0‖ * u := by
    refine hUd.trans ?_
    have := add_le_add (hu _ hxt) (hu _ hx0)
    calc |m| * ‖v 0‖ * (‖gyroCorr B G K (x t)‖ + ‖gyroCorr B G K (x 0)‖)
        ≤ |m| * ‖v 0‖ * (u + u) := by gcongr
      _ = _ := by ring
  unfold gyroMomentum noetherMomentum at hdrift
  have e : q * (ψ (x t) - ψ (x 0)) =
      ((m * ⟪K (x t), v t⟫ + q * ψ (x t) + m * ⟪gyroCorr B G K (x t), v t⟫) -
        (m * ⟪K (x 0), v 0⟫ + q * ψ (x 0) + m * ⟪gyroCorr B G K (x 0), v 0⟫)) +
      m * (⟪K (x 0), v 0⟫ - ⟪K (x t), v t⟫) +
      m * (⟪gyroCorr B G K (x 0), v 0⟫ - ⟪gyroCorr B G K (x t), v t⟫) := by ring
  rw [← abs_mul, e]
  calc _ ≤ _ := abs_add_three _ _ _
    _ ≤ (|q| * ‖v 0‖ * δpar + |m| * ‖v 0‖ ^ 2 * u₁) * t +
        |m| * ‖v 0‖ * (‖K (x t)‖ + ‖K (x 0)‖) + 2 * |m| * ‖v 0‖ * u := by gcongr
    _ = _ := by ring

/-- **Finite-time confinement from the gyro-Noether band.** On `S = {ψ ≤ c}` assume the
hypotheses of `gyroNoether_band` and `‖K‖ ≤ κ`. If, with `s = |v(0)|`,
`|q| ψ(x 0) + |m| s (κ + |K(x 0)|) + 2 |m| s u + (|q| s δ_∥ + |m| s² u₁) T ≤ |q| c'` and
`c' < c`, then `ψ(x t) ≤ c'` for all `t ∈ [0,T]`. -/
theorem gyroNoether_trapped_until {m q : ℝ} (hm : m ≠ 0) (hq : q ≠ 0) {B G K : Space → Space}
    {DK : Space → Space →L[ℝ] Space} {DU : Space → Space →L[ℝ] Space} {ψ : Space → ℝ}
    {x v : ℝ → Space} (h : LorentzOrbit m q (fun _ => 0) B x v) (hK : IsKilling K DK)
    (hψ : ∀ y, HasFDerivAt ψ (innerSL ℝ (G y)) y) {c' c κ δpar u u₁ T : ℝ} (hcc : c' < c)
    (hκ : 0 ≤ κ) (hu0 : 0 ≤ u) (hδ : 0 ≤ δpar) (hu₁0 : 0 ≤ u₁) (hT : 0 ≤ T)
    (hB0 : ∀ y, ψ y ≤ c → B y ≠ 0)
    (hDU : ∀ y, ψ y ≤ c → HasFDerivAt (gyroCorr B G K) (DU y) y)
    (hpar : ∀ y, ψ y ≤ c → |⟪B y, defectVec B G K y⟫| ≤ δpar * ‖B y‖)
    (hu : ∀ y, ψ y ≤ c → ‖gyroCorr B G K y‖ ≤ u) (hu₁ : ∀ y, ψ y ≤ c → ‖DU y‖ ≤ u₁)
    (hreg : ∀ y, ψ y ≤ c → ‖K y‖ ≤ κ)
    (hgap : |q| * ψ (x 0) + |m| * ‖v 0‖ * (κ + ‖K (x 0)‖) + 2 * |m| * ‖v 0‖ * u +
      (|q| * ‖v 0‖ * δpar + |m| * ‖v 0‖ ^ 2 * u₁) * T ≤ |q| * c') :
    ∀ t ∈ Set.Icc 0 T, ψ (x t) ≤ c' := by
  have hqpos : 0 < |q| := abs_pos.mpr hq
  have hcont : Continuous fun s => ψ (x s) :=
    (continuous_iff_continuousAt.mpr fun y => (hψ y).continuousAt).comp
      h.continuous_position
  have hrate : 0 ≤ |q| * ‖v 0‖ * δpar + |m| * ‖v 0‖ ^ 2 * u₁ := by positivity
  refine trapped_until hcont hcc ?_ (fun t ht hhist => ?_)
  · have : 0 ≤ |m| * ‖v 0‖ * (κ + ‖K (x 0)‖) + 2 * |m| * ‖v 0‖ * u +
        (|q| * ‖v 0‖ * δpar + |m| * ‖v 0‖ ^ 2 * u₁) * T := by positivity
    have : |q| * ψ (x 0) ≤ |q| * c' := by linarith
    exact le_of_mul_le_mul_left this hqpos
  · have hb := gyroNoether_band (S := {y | ψ y ≤ c}) hm h hK hψ hB0 hDU hpar hu hu₁ ht.1
      (fun s hs => hhist s hs)
    have hn := hreg _ (hhist t ⟨ht.1, le_rfl⟩)
    have h1 : |q| * (ψ (x t) - ψ (x 0)) ≤ |q| * |ψ (x t) - ψ (x 0)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hqpos.le
    have h2 : |m| * ‖v 0‖ * (‖K (x t)‖ + ‖K (x 0)‖) ≤ |m| * ‖v 0‖ * (κ + ‖K (x 0)‖) := by
      gcongr
    have h3 : (|q| * ‖v 0‖ * δpar + |m| * ‖v 0‖ ^ 2 * u₁) * t ≤
        (|q| * ‖v 0‖ * δpar + |m| * ‖v 0‖ ^ 2 * u₁) * T :=
      mul_le_mul_of_nonneg_left ht.2 hrate
    have : |q| * ψ (x t) ≤ |q| * c' := by nlinarith
    exact le_of_mul_le_mul_left this hqpos

/-! ## Sanity checks -/

/-- Exact symmetry has zero defect vector. -/
theorem defectVec_eq_zero_of_symmetric {B G K : Space → Space} (hB : SymmetricFlux B G K)
    (y : Space) : defectVec B G K y = 0 := by
  have h := noether_rate_eq_defect B G K y (defectVec B G K y)
  rw [hB, neg_add_cancel, eq_comm, real_inner_self_eq_norm_sq] at h
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)

/-- `SymmetricFlux B G K` holds exactly when the defect vector vanishes identically. -/
theorem symmetricFlux_iff_defectVec_eq_zero (B G K : Space → Space) :
    SymmetricFlux B G K ↔ ∀ y, defectVec B G K y = 0 := by
  refine ⟨defectVec_eq_zero_of_symmetric, fun h y w => ?_⟩
  have := noether_rate_eq_defect B G K y w
  rw [h y, inner_zero_right] at this
  linarith

/-- Under exact symmetry the gyro-correction vanishes. -/
theorem gyroCorr_eq_zero_of_symmetric {B G K : Space → Space} (hB : SymmetricFlux B G K) :
    gyroCorr B G K = fun _ => 0 := by
  funext y
  simp [gyroCorr, defectVec_eq_zero_of_symmetric hB y, cross]

/-- Under exact symmetry the corrected momentum is the Noether momentum. -/
theorem gyroMomentum_eq_noether_of_symmetric {m q : ℝ} {B G K : Space → Space} {ψ : Space → ℝ}
    {x v : ℝ → Space} (hB : SymmetricFlux B G K) :
    gyroMomentum m q B G K ψ x v = noetherMomentum m q K ψ x v := by
  funext t
  simp [gyroMomentum, gyroCorr_eq_zero_of_symmetric hB]

/-- Sanity (exact symmetry): with `δ ≡ 0` (and `B` nonvanishing) the gyro-Noether band with
`δ_∥ = u = u₁ = 0` is exactly the bound of `noether_flux_band`, for every `t ≥ 0`. -/
theorem gyroNoether_band_exact {m q : ℝ} (hm : m ≠ 0) {B G K : Space → Space}
    {DK : Space → Space →L[ℝ] Space} {ψ : Space → ℝ} {x v : ℝ → Space}
    (h : LorentzOrbit m q (fun _ => 0) B x v) (hK : IsKilling K DK)
    (hψ : ∀ y, HasFDerivAt ψ (innerSL ℝ (G y)) y) (hB : SymmetricFlux B G K)
    (hB0 : ∀ y, B y ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    |q| * |ψ (x t) - ψ (x 0)| ≤ |m| * ‖v 0‖ * (‖K (x t)‖ + ‖K (x 0)‖) := by
  have hU := gyroCorr_eq_zero_of_symmetric hB
  have := gyroNoether_band (S := Set.univ) (DU := fun _ => 0) (δpar := 0) (u := 0) (u₁ := 0)
    hm h hK hψ (fun y _ => hB0 y) (fun y _ => by rw [hU]; exact hasFDerivAt_const 0 y)
    (fun y _ => by simp [defectVec_eq_zero_of_symmetric hB y])
    (fun y _ => by simp [hU]) (fun y _ => by simp) ht (fun _ _ => trivial)
  simpa using this

/-- The parallel defect only sees `∇ψ`: `⟪B, δ⟫ = ⟪B, G⟫`. -/
theorem inner_field_defectVec (B G K : Space → Space) (y : Space) :
    ⟪B y, defectVec B G K y⟫ = ⟪B y, G y⟫ := by
  rw [defectVec, inner_add_right, inner_cross_self, zero_add]

/-- Sanity (exact field-line first integral, approximate symmetry): if `⟪B, ∇ψ⟫ = 0` on `S`
then `δ_∥ = 0` and the secular rate is the pure finite-Larmor-radius term `|m| s² u₁`. -/
theorem gyroNoether_band_firstIntegral {m q : ℝ} (hm : m ≠ 0) {B G K : Space → Space}
    {DK : Space → Space →L[ℝ] Space} {DU : Space → Space →L[ℝ] Space} {ψ : Space → ℝ}
    {x v : ℝ → Space} (h : LorentzOrbit m q (fun _ => 0) B x v) (hK : IsKilling K DK)
    (hψ : ∀ y, HasFDerivAt ψ (innerSL ℝ (G y)) y) {S : Set Space} {u u₁ : ℝ}
    (hB0 : ∀ y ∈ S, B y ≠ 0) (hDU : ∀ y ∈ S, HasFDerivAt (gyroCorr B G K) (DU y) y)
    (hfi : ∀ y ∈ S, ⟪B y, G y⟫ = 0)
    (hu : ∀ y ∈ S, ‖gyroCorr B G K y‖ ≤ u) (hu₁ : ∀ y ∈ S, ‖DU y‖ ≤ u₁)
    {t : ℝ} (ht : 0 ≤ t) (hin : ∀ s ∈ Set.Icc 0 t, x s ∈ S) :
    |q| * |ψ (x t) - ψ (x 0)| ≤
      |m| * ‖v 0‖ * (‖K (x t)‖ + ‖K (x 0)‖) + 2 * |m| * ‖v 0‖ * u +
        |m| * ‖v 0‖ ^ 2 * u₁ * t := by
  have := gyroNoether_band (δpar := 0) hm h hK hψ hB0 hDU
    (fun y hy => by rw [inner_field_defectVec, hfi y hy]; simp) hu hu₁ ht hin
  simpa using this

/-! ### Uniform field, translation symmetry, linear defect -/

/-- Unit vector along the first axis (the translation Killing field of the example). -/
@[expose] def unitX : Space := toLp 2 ![1, 0, 0]

/-- Quadratic flux function `ψ = -B₀ y₁ + (ε/2) y₁²`: `ε = 0` is the exact invariant of the
translation `e₀` in the uniform field `B₀ e₂`. -/
@[expose] def quadFlux (B₀ ε : ℝ) (y : Space) : ℝ := -B₀ * y 1 + ε / 2 * y 1 ^ 2

/-- Gradient of `quadFlux`: `(0, -B₀ + ε y₁, 0)`. -/
@[expose] def quadFluxGrad (B₀ ε : ℝ) (y : Space) : Space := toLp 2 ![0, -B₀ + ε * y 1, 0]

/-- `quadFluxGrad` is the gradient of `quadFlux`. -/
theorem quadFlux_hasFDerivAt (B₀ ε : ℝ) (y : Space) :
    HasFDerivAt (quadFlux B₀ ε) (innerSL ℝ (quadFluxGrad B₀ ε y)) y := by
  have hp : HasFDerivAt (fun z : Space => z 1)
      (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ) y := by
    convert (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt using 1
    funext z; simp
  have := (hp.const_mul (-B₀)).add ((hp.pow 2).const_mul (ε / 2))
  convert this using 1
  · funext w; simp only [quadFlux, Pi.add_apply]
  ext w
  simp [quadFluxGrad, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  ring

/-- In the example the defect is `δ = (0, ε y₁, 0)` and the gyro-correction is the linear map
`U(y) = -(ε/B₀) y₁ e₀`. -/
theorem uniform_gyroCorr {B₀ ε : ℝ} (hB₀ : B₀ ≠ 0) :
    gyroCorr (uniformField B₀) (quadFluxGrad B₀ ε) (fun _ => unitX) =
      ⇑((-(ε / B₀)) • (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).smulRight unitX) := by
  have hn : ‖(toLp 2 ![0, 0, B₀] : Space)‖ ^ 2 = B₀ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_three]
  funext y
  ext i
  fin_cases i <;>
    simp [gyroCorr, defectVec, uniformField, quadFluxGrad, unitX, hn, cross, cross_apply]
  all_goals field_simp

/-- Sanity (uniform field, linear defect): for every orbit in `B₀ e₂` with the translation
`K = e₀` and `ψ = -B₀ y₁ + (ε/2) y₁²`, the corrected momentum has
`Q' = -m ε v₀ v₁/B₀`, of size `|m| s² |ε|/|B₀|` independent of position. -/
theorem uniform_linear_defect_deriv {m q B₀ ε : ℝ} (hB₀ : B₀ ≠ 0) {x v : ℝ → Space}
    (h : LorentzOrbit m q (fun _ => 0) (uniformField B₀) x v) (r : ℝ) :
    HasDerivAt (gyroMomentum m q (uniformField B₀) (quadFluxGrad B₀ ε) (fun _ => unitX)
      (quadFlux B₀ ε) x v) (-(m * ε * v r 0 * v r 1) / B₀) r := by
  set L := (-(ε / B₀)) • (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).smulRight unitX
  have hU : HasFDerivAt (gyroCorr (uniformField B₀) (quadFluxGrad B₀ ε) (fun _ => unitX))
      L (x r) := by rw [uniform_gyroCorr hB₀]; exact L.hasFDerivAt
  have hB : uniformField B₀ (x r) ≠ 0 := by
    intro h0
    have := congrArg (fun w : Space => w 2) h0
    exact hB₀ (by simpa [uniformField] using this)
  have hd := gyroNoether_hasDerivAt (DU := fun _ => L) h (translation_killing unitX)
    (quadFlux_hasFDerivAt B₀ ε) hU hB
  convert hd using 1
  rw [inner_field_defectVec]
  simp [L, uniformField, quadFluxGrad, unitX, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Fin.sum_univ_three]
  field_simp

/-- Contrast: in the same example the uncorrected Noether momentum has
`p_K' = q ε x₁ v₁`, a forcing proportional to the position (unbounded on unbounded regions). -/
theorem uniform_linear_defect_noether_deriv {m q B₀ ε : ℝ} {x v : ℝ → Space}
    (h : LorentzOrbit m q (fun _ => 0) (uniformField B₀) x v) (r : ℝ) :
    HasDerivAt (noetherMomentum m q (fun _ => unitX) (quadFlux B₀ ε) x v)
      (q * (ε * x r 1 * v r 1)) r := by
  have hd := noetherMomentum_hasDerivAt h (translation_killing unitX)
    (quadFlux_hasFDerivAt B₀ ε) r
  convert hd using 2
  simp [uniformField, quadFluxGrad, unitX, cross, cross_apply,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  ring

end PlasmaLean.Kinetic
