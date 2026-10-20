/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Stability.BallooningInfinite
public import PlasmaLean.Theory.Fields.Maxwell

/-!
# The ideal-ballooning reduction (supplied interface) and two-variable Riccati certificates

## The supplied reduction

For high toroidal mode number `n → ∞`, ideal-MHD perturbations of the eikonal form
`ξ = X exp(i n S)`, with `B · ∇S = 0`, reduce on each field line to a one-dimensional
Sturm–Liouville problem in the *covering space* (extended poloidal angle), Connor–Hastie–Taylor
(Phys. Rev. Lett. 40 (1978) 396) and, for general toroidal geometry, Dewar–Glasser
(Phys. Fluids 26 (1983) 3038). With a Clebsch representation `B = ∇ψ × ∇α` and the secular
eikonal gradient `k⊥ = ∇α`, the standard ballooning equation along a field line reads

  `B·∇(|∇α|²/B² B·∇X) + 2 μ₀ p'(ψ) (B × κ · ∇α)/B² X = 0`,

with energy `δW ∝ ∫ dl/B [ |k⊥|² |∂ₗ X|² − 2 μ₀ (b × k⊥ · ∇p)(b × k⊥ · κ) X²/B² ]`, where
`b = B/|B|` and `κ = b · ∇b` is the field-line curvature. If the field line is parametrized as
`t ↦ X(t)` with `X'(t) = λ(t) B(X(t))`, then `dl/B = ℓ dt` with `ℓ = |λ|`, and the energy is
`∫ (P X'² + Q X²) dt` with

  `P = |k|² / (ℓ |B|²)`  (`ballooningP`),
  `Q = −2 ℓ (B × k · μ₀∇p)(B × k · κ) / |B|⁴`  (`ballooningQ`).

`Q` is quadratic in `k`, so it is independent of orientation conventions, and only the part
of `κ` normal to `B` enters (`inner_cross_curvature`). For a field with derivative `DB`,
`fieldLineCurvature B (DB B)` is the exact curvature `b · ∇b`. `ballooningQ_clebsch` checks
that, for `B = ∇ψ × k` and `μ₀∇p = p' ∇ψ`, `Q = −2 ℓ p' (B × κ · k)/|B|²`, i.e. exactly the
drive of the Clebsch form above.

**SUPPLIED (not formalized):** that ideal ballooning stability of a flux surface is equivalent
to `LineData.Stable` (nonnegative energy for every compactly supported `X`) on every field
line of the surface and for every eikonal family (every `θ_k`). Here this reduction is an
interface, exactly like `NewcombReduction` and `MercierGeneral.mercierIndex`.

## Covering-space structure

The eikonal gradient on a flux surface has the secular form `k = k₀ − σ(t) k₁`, with `k₁`
along `∇ψ` and `σ(t)` growing linearly in `t` on average (local shear). Then
`P = p₀ + σ p₁ + σ² p₂` (`ballooningP_secular`) and, because `∇p ∥ ∇ψ`, `Q = q₀ + σ q₁`
(`ballooningQ_secular`): `P` grows like `θ²` and `Q` like `θ` times a periodic factor (the
geodesic curvature). The naive tail `P ~ s² θ², Q → const` of
`BallooningInfinite.tail_exponent_iff_suydam` is exactly the case `q₁ = 0`, constant `p₂`,
`σ = m t` (cylindrical/shearless-curvature model); see below.

## Two-variable Riccati certificates (uniform in `θ_k`)

`riccati2D_energy_nonneg`: let `P, Q : ℝ → ℝ → ℝ` be coefficients as functions of the line
parameter `t` and the secular variable `σ`, and `σ(t)` a curve with `σ' = d`. If a `C¹`
function `F(t, σ)` satisfies the transport–Riccati inequality

  `∂ₜF + d(t) ∂_σF + F²/P ≤ Q`   for ALL `(t, σ) ∈ ℝ²`,

then for EVERY shift `c` (every eikonal family `θ_k`) the line energy with coefficients
`P(t, σ(t) − c)`, `Q(t, σ(t) − c)` is nonnegative for all compactly supported `C¹` modes:
`φ(t) = F(t, σ(t) − c)` is a global Picone flux. One inequality on the `(t, σ)` plane thus
certifies all field lines/`θ_k` of a surface at once.

## Cross-check with Suydam/Mercier

For the cylindrical secular model `P = p₀ + p₂ σ²`, `Q = q₀`, `σ = m t`:
* `cylinder_energy_nonneg`: the certificate `F = α m p₂ σ` works iff `α(α+1) m² p₂ ≤ q₀`, the
  tail-exponent condition of `tail_exponent_iff_suydam` with `s² = m² p₂`;
* `cylinder_stable_of_suydam`: `m² p₂ + 4 q₀ ≥ 0` gives stability for every `θ_k`;
* `cylinder_unstable_of_suydam`: `m² p₂ + 4 q₀ < 0` gives a compactly supported mode of
  negative energy (`tail_unstable`).
So in this limit the ballooning certificate condition is exactly the Suydam criterion.

Sanity: `ballooningQ_no_pressure` (no pressure gradient, no drive),
`noPressure_energy_nonneg` (degenerate case: always stable), `cylinder_fixture_stable`
(accepted) and `cylinder_fixture_unstable` (rejected).
-/

public section
noncomputable section

namespace PlasmaLean.Stability.BallooningReduction

open Set PlasmaLean.Fields PlasmaLean.Stability PlasmaLean.Stability.BallooningInfinite
open scoped RealInnerProductSpace

/-! ## The supplied coefficient formulas -/

/-- Ballooning bending coefficient `P = |k|² / (ℓ |B|²)` (line element `dl/B = ℓ dt`,
eikonal gradient `k`, field `B`). -/
@[expose] def ballooningP (ℓ : ℝ) (B k : Space) : ℝ := ‖k‖ ^ 2 / (ℓ * ‖B‖ ^ 2)

/-- Ballooning drive `Q = −2 ℓ (B × k · μ₀∇p)(B × k · κ) / |B|⁴` (`gp = μ₀ ∇p`, `κ` the
field-line curvature). Negative `Q` is destabilizing. -/
@[expose] def ballooningQ (ℓ : ℝ) (B k gp κ : Space) : ℝ :=
  -(2 * ℓ * ⟪cross B k, gp⟫ * ⟪cross B k, κ⟫) / ‖B‖ ^ 4

/-- Field-line curvature `b · ∇b = (DB B − (b · DB B) b)/|B|²` from `DBB = (DB)(B)`, the
derivative of the field along itself. -/
@[expose] def fieldLineCurvature (B DBB : Space) : Space :=
  (‖B‖ ^ 2)⁻¹ • (DBB - (⟪B, DBB⟫ / ‖B‖ ^ 2) • B)

/-- `B × k` is orthogonal to `B`. -/
theorem inner_cross_self_left (B k : Space) : ⟪cross B k, B⟫ = 0 := by
  simp only [cross, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  simp [cross_apply]
  ring

/-- `B × k` is orthogonal to `k`. -/
theorem inner_cross_self_right (B k : Space) : ⟪cross B k, k⟫ = 0 := by
  simp only [cross, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  simp [cross_apply]
  ring

/-- Only the part of the curvature normal to `B` enters the drive:
`B × k · κ = B × k · DBB / |B|²`. -/
theorem inner_cross_curvature (B k DBB : Space) :
    ⟪cross B k, fieldLineCurvature B DBB⟫ = ⟪cross B k, DBB⟫ / ‖B‖ ^ 2 := by
  rw [fieldLineCurvature, inner_smul_right, inner_sub_right, inner_smul_right,
    inner_cross_self_left]
  ring

/-- Cross product is linear in the second slot (difference with a multiple). -/
theorem cross_sub_smul (B k₀ k₁ : Space) (σ : ℝ) :
    cross B (k₀ - σ • k₁) = cross B k₀ - σ • cross B k₁ := by
  apply space_ext <;> simp [cross, cross_apply] <;> ring

/-- **Secular structure of `P`.** For `k = k₀ − σ k₁`, `P = p₀ + σ p₁ + σ² p₂`. -/
theorem ballooningP_secular (ℓ σ : ℝ) (B k₀ k₁ : Space) :
    ballooningP ℓ B (k₀ - σ • k₁) =
      ‖k₀‖ ^ 2 / (ℓ * ‖B‖ ^ 2) + σ * (-(2 * ⟪k₀, k₁⟫) / (ℓ * ‖B‖ ^ 2)) +
        σ ^ 2 * (‖k₁‖ ^ 2 / (ℓ * ‖B‖ ^ 2)) := by
  unfold ballooningP
  rw [norm_sub_sq_real, norm_smul, inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- **Secular structure of `Q`.** If `μ₀∇p = μ k₁` (pressure gradient along the secular
direction `∇ψ`), then for `k = k₀ − σ k₁`, `Q = q₀ + σ q₁`. -/
theorem ballooningQ_secular (ℓ σ μ : ℝ) (B k₀ k₁ κ : Space) :
    ballooningQ ℓ B (k₀ - σ • k₁) (μ • k₁) κ =
      -(2 * ℓ * ⟪cross B k₀, μ • k₁⟫ * ⟪cross B k₀, κ⟫) / ‖B‖ ^ 4 +
        σ * (2 * ℓ * ⟪cross B k₀, μ • k₁⟫ * ⟪cross B k₁, κ⟫ / ‖B‖ ^ 4) := by
  unfold ballooningQ
  rw [cross_sub_smul, inner_sub_left, inner_sub_left, real_inner_smul_left,
    real_inner_smul_left, real_inner_smul_right (cross B k₁), inner_cross_self_right]
  ring

/-- **Cross-check with the Clebsch form of the ballooning equation.** If `B = ∇ψ × k`
(`k = ∇α`) and `μ₀∇p = p' ∇ψ`, then `Q = −2 ℓ p' (B × κ · k)/|B|²`, the drive of
`B·∇(|∇α|²/B² B·∇X) + 2 μ₀ p' (B × κ · ∇α)/B² X = 0`. -/
theorem ballooningQ_clebsch (ℓ p' : ℝ) (gψ k κ : Space) (hB : cross gψ k ≠ 0) :
    ballooningQ ℓ (cross gψ k) k (p' • gψ) κ =
      -(2 * ℓ * p' * ⟪cross (cross gψ k) κ, k⟫) / ‖cross gψ k‖ ^ 2 := by
  have h1 : ⟪cross (cross gψ k) k, p' • gψ⟫ = -(p' * ‖cross gψ k‖ ^ 2) := by
    rw [real_inner_smul_right, ← real_inner_self_eq_norm_sq]
    simp only [cross, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
    simp [cross_apply]
    ring
  have h2 : ⟪cross (cross gψ k) k, κ⟫ = -⟪cross (cross gψ k) κ, k⟫ := by
    simp only [cross, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
    simp [cross_apply]
    ring
  have hn : ‖cross gψ k‖ ≠ 0 := norm_ne_zero_iff.mpr hB
  unfold ballooningQ
  rw [h1, h2]
  field_simp

/-- Sanity: with no pressure gradient there is no drive. -/
theorem ballooningQ_no_pressure (ℓ : ℝ) (B k κ : Space) : ballooningQ ℓ B k 0 κ = 0 := by
  simp [ballooningQ]

/-! ## Field-line data -/

/-- Data of the supplied ballooning reduction along a parametrized field line `t ↦ X(t)`
(`X' = λ B`): line element `ℓ = |λ|`, field `B`, covering-space eikonal gradient `k`,
`gp = μ₀ ∇p` and curvature `κ`, all evaluated along the line. -/
structure LineData where
  /-- `dl/(|B| dt)`. -/
  ℓ : ℝ → ℝ
  /-- The field along the line. -/
  B : ℝ → Space
  /-- The eikonal gradient `k⊥ = ∇S` along the line (covering space). -/
  k : ℝ → Space
  /-- `μ₀ ∇p` along the line. -/
  gp : ℝ → Space
  /-- Field-line curvature along the line. -/
  κ : ℝ → Space
  ℓ_pos : ∀ t, 0 < ℓ t
  B_ne : ∀ t, B t ≠ 0
  k_ne : ∀ t, k t ≠ 0
  ℓ_cont : Continuous ℓ
  B_cont : Continuous B
  k_cont : Continuous k
  gp_cont : Continuous gp
  κ_cont : Continuous κ

namespace LineData
variable (D : LineData)

/-- The bending coefficient along the line. -/
@[expose] def P (t : ℝ) : ℝ := ballooningP (D.ℓ t) (D.B t) (D.k t)

/-- The drive along the line. -/
@[expose] def Q (t : ℝ) : ℝ := ballooningQ (D.ℓ t) (D.B t) (D.k t) (D.gp t) (D.κ t)

/-- The bending coefficient is positive. -/
theorem P_pos (t : ℝ) : 0 < D.P t := by
  unfold P ballooningP
  have := D.ℓ_pos t
  have hB : 0 < ‖D.B t‖ := norm_pos_iff.mpr (D.B_ne t)
  have hk : 0 < ‖D.k t‖ := norm_pos_iff.mpr (D.k_ne t)
  positivity

/-- Continuity of `P`. -/
theorem P_cont : Continuous D.P := by
  unfold P ballooningP
  have h1 := D.ℓ_cont; have h2 := D.B_cont; have h3 := D.k_cont
  refine Continuous.div (by fun_prop) (by fun_prop) fun t => ?_
  have := D.ℓ_pos t
  have hB : 0 < ‖D.B t‖ := norm_pos_iff.mpr (D.B_ne t)
  positivity

/-- Continuity of `Q`. -/
theorem Q_cont : Continuous D.Q := by
  unfold Q ballooningQ
  have h1 := D.ℓ_cont; have h2 := D.B_cont; have h3 := D.k_cont
  have h4 := D.gp_cont; have h5 := D.κ_cont
  have hc : Continuous fun t => cross (D.B t) (D.k t) :=
    continuous_cross.comp (h2.prodMk h3)
  refine Continuous.div (by fun_prop) (by fun_prop) fun t => ?_
  have hB : 0 < ‖D.B t‖ := norm_pos_iff.mpr (D.B_ne t)
  positivity

/-- The ballooning line operator (inertia `ℓ |k|²/|B|²`, unit density). -/
@[expose] def toLineOperator : LineOperator where
  P := D.P
  Q := D.Q
  W := fun t => D.ℓ t * ‖D.k t‖ ^ 2 / ‖D.B t‖ ^ 2
  P_pos := D.P_pos
  W_nonneg t := by have := D.ℓ_pos t; positivity
  P_cont := D.P_cont
  Q_cont := D.Q_cont
  W_cont := by
    have h1 := D.ℓ_cont; have h2 := D.B_cont; have h3 := D.k_cont
    refine Continuous.div (by fun_prop) (by fun_prop) fun t => ?_
    have hB : 0 < ‖D.B t‖ := norm_pos_iff.mpr (D.B_ne t)
    positivity

/-- **Ballooning stability of the line** (in the sense of the supplied reduction): every
compactly supported `C¹` mode has nonnegative energy `∫ (P X'² + Q X²)`. -/
@[expose] def Stable : Prop :=
  ∀ ξ ξ' : ℝ → ℝ, ∀ a b : ℝ, LineAdmissible ξ ξ' a b → 0 ≤ lineEnergy D.P D.Q ξ ξ'

end LineData

/-! ## Two-variable Riccati certificates -/

/-- **Two-variable Riccati certificate** for coefficients `P(t, σ)`, `Q(t, σ)` and secular
rate `d(t) = σ'(t)`: a `C¹` function `F(t, σ)` with partial derivatives `Ft`, `Fs` such that
`Ft + d Fs + F²/P ≤ Q` on the whole plane. -/
structure Riccati2D (P Q : ℝ → ℝ → ℝ) (d : ℝ → ℝ) where
  /-- The flux function on the `(t, σ)` plane. -/
  F : ℝ → ℝ → ℝ
  /-- Its `t`-derivative. -/
  Ft : ℝ → ℝ → ℝ
  /-- Its `σ`-derivative. -/
  Fs : ℝ → ℝ → ℝ
  hasFDeriv : ∀ t s, HasFDerivAt (fun p : ℝ × ℝ => F p.1 p.2)
    (Ft t s • ContinuousLinearMap.fst ℝ ℝ ℝ + Fs t s • ContinuousLinearMap.snd ℝ ℝ ℝ) (t, s)
  Ft_cont : Continuous fun p : ℝ × ℝ => Ft p.1 p.2
  Fs_cont : Continuous fun p : ℝ × ℝ => Fs p.1 p.2
  P_pos : ∀ t s, 0 < P t s
  ineq : ∀ t s, Ft t s + d t * Fs t s + F t s ^ 2 / P t s ≤ Q t s

/-- The flux of a two-variable certificate along the shifted curve `t ↦ (t, σ(t) − c)` has
derivative `Ft + d Fs`. -/
theorem Riccati2D.hasDerivAt_flux {P Q : ℝ → ℝ → ℝ} {d σ : ℝ → ℝ} (R : Riccati2D P Q d)
    (hσ : ∀ t, HasDerivAt σ (d t) t) (c t : ℝ) :
    HasDerivAt (fun t => R.F t (σ t - c))
      (R.Ft t (σ t - c) + d t * R.Fs t (σ t - c)) t := by
  have hpath : HasDerivAt (fun t => (t, σ t - c)) ((1 : ℝ), d t) t :=
    (hasDerivAt_id t).prodMk ((hσ t).sub_const c)
  have := (R.hasFDeriv t (σ t - c)).comp_hasDerivAt t hpath
  refine HasDerivAt.congr_deriv (f := fun t => R.F t (σ t - c)) this ?_
  simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
    Pi.smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

/-- **Two-variable certificate theorem (uniform in `θ_k`).** If `R` is a two-variable
Riccati certificate for `P, Q` with `σ' = d`, then for EVERY shift `c` and every compactly
supported `C¹` displacement, `∫ (P(t, σ(t) − c) ξ'² + Q(t, σ(t) − c) ξ²) ≥ 0`. -/
theorem riccati2D_energy_nonneg {P Q : ℝ → ℝ → ℝ} {d σ : ℝ → ℝ} (R : Riccati2D P Q d)
    (hPc : Continuous fun p : ℝ × ℝ => P p.1 p.2) (hQc : Continuous fun p : ℝ × ℝ => Q p.1 p.2)
    (hσ : ∀ t, HasDerivAt σ (d t) t) (hd : Continuous d) (c : ℝ) {ξ ξ' : ℝ → ℝ} {a b : ℝ}
    (h : LineAdmissible ξ ξ' a b) :
    0 ≤ lineEnergy (fun t => P t (σ t - c)) (fun t => Q t (σ t - c)) ξ ξ' := by
  have hσc : Continuous σ := continuous_iff_continuousAt.mpr fun t => (hσ t).continuousAt
  have hpath : Continuous fun t => (t, σ t - c) := continuous_id.prodMk (hσc.sub continuous_const)
  let op : LineOperator :=
    { P := fun t => P t (σ t - c)
      Q := fun t => Q t (σ t - c)
      W := fun _ => 0
      P_pos := fun t => R.P_pos t _
      W_nonneg := fun _ => le_rfl
      P_cont := hPc.comp hpath
      Q_cont := hQc.comp hpath
      W_cont := continuous_const }
  let D : PiconeData op.P (op.shifted 0) univ :=
    { φ := fun t => R.F t (σ t - c)
      h := fun t => R.Ft t (σ t - c) + d t * R.Fs t (σ t - c)
      deriv := fun t _ => R.hasDerivAt_flux hσ c t
      cont := ((R.Ft_cont.comp hpath).add (hd.mul (R.Fs_cont.comp hpath))).continuousOn
      gap := fun t _ => by
        have h1 := R.ineq t (σ t - c)
        have h2 : 0 ≤ R.F t (σ t - c) ^ 2 / P t (σ t - c) :=
          div_nonneg (sq_nonneg _) (R.P_pos _ _).le
        change R.Ft t (σ t - c) + d t * R.Fs t (σ t - c) ≤ Q t (σ t - c) - 0 * 0
        linarith
      disc := fun t _ => by
        have h1 := R.ineq t (σ t - c)
        have hP := R.P_pos t (σ t - c)
        change R.F t (σ t - c) ^ 2 ≤ P t (σ t - c) *
          (Q t (σ t - c) - 0 * 0 - (R.Ft t (σ t - c) + d t * R.Fs t (σ t - c)))
        have h3 : R.F t (σ t - c) ^ 2 / P t (σ t - c) ≤
            Q t (σ t - c) - (R.Ft t (σ t - c) + d t * R.Fs t (σ t - c)) := by linarith
        rw [div_le_iff₀ hP] at h3
        linarith }
  have hF := D.fluxBound h.le (subset_univ _) (fun x _ => (op.P_pos x).le)
    op.P_cont.continuousOn (op.shifted_cont 0).continuousOn
  have := op.lower_bound_of_fluxBound h hF
  simpa [op] using this

/-! ## Cross-check: the cylindrical secular model and the Suydam criterion -/

/-- The Riccati certificate `F = α m p₂ σ` for the cylindrical secular model
`P = p₀ + p₂ σ²`, `Q = q₀`, `σ' = m`, under the tail-exponent condition
`α (α + 1) m² p₂ ≤ q₀`. -/
@[expose] def cylinderCertificate {p₀ p₂ q₀ m α : ℝ} (hp₀ : 0 < p₀) (hp₂ : 0 < p₂)
    (hα : α * (α + 1) * (m ^ 2 * p₂) ≤ q₀) :
    Riccati2D (fun _ s => p₀ + p₂ * s ^ 2) (fun _ _ => q₀) (fun _ => m) where
  F := fun _ s => α * m * p₂ * s
  Ft := fun _ _ => 0
  Fs := fun _ _ => α * m * p₂
  hasFDeriv t s := by
    have := ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := (t, s))).const_mul (α * m * p₂)
    refine this.congr_fderiv ?_
    simp
  Ft_cont := continuous_const
  Fs_cont := continuous_const
  P_pos _ s := by positivity
  ineq t s := by
    have hP : 0 < p₀ + p₂ * s ^ 2 := by positivity
    have key : (α * m * p₂ * s) ^ 2 / (p₀ + p₂ * s ^ 2) ≤ α ^ 2 * (m ^ 2 * p₂) := by
      rw [div_le_iff₀ hP]
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg α) (sq_nonneg m)) (mul_nonneg hp₂.le hp₀.le)]
    nlinarith [key]

/-- **Cylinder, tail-exponent form.** For `P = p₀ + p₂ (m t − c)²`, `Q = q₀` and
`α (α + 1) m² p₂ ≤ q₀` (the condition of `tail_exponent_iff_suydam` with `s² = m² p₂`),
every compactly supported mode has nonnegative energy, for every shift `c`. -/
theorem cylinder_energy_nonneg {p₀ p₂ q₀ m α : ℝ} (hp₀ : 0 < p₀) (hp₂ : 0 < p₂)
    (hα : α * (α + 1) * (m ^ 2 * p₂) ≤ q₀) (c : ℝ) {ξ ξ' : ℝ → ℝ} {a b : ℝ}
    (h : LineAdmissible ξ ξ' a b) :
    0 ≤ lineEnergy (fun t => p₀ + p₂ * (m * t - c) ^ 2) (fun _ => q₀) ξ ξ' :=
  riccati2D_energy_nonneg (σ := fun t => m * t) (cylinderCertificate hp₀ hp₂ hα)
    (by fun_prop) continuous_const
    (fun t => by simpa using (hasDerivAt_id t).const_mul m) continuous_const c h

/-- **Cylinder, Suydam form (sufficiency).** If `m² p₂ + 4 q₀ ≥ 0` the cylindrical secular
model is ballooning stable for every `θ_k` (take `α = −1/2`). -/
theorem cylinder_stable_of_suydam {p₀ p₂ q₀ m : ℝ} (hp₀ : 0 < p₀) (hp₂ : 0 < p₂)
    (hS : 0 ≤ m ^ 2 * p₂ + 4 * q₀) (c : ℝ) {ξ ξ' : ℝ → ℝ} {a b : ℝ}
    (h : LineAdmissible ξ ξ' a b) :
    0 ≤ lineEnergy (fun t => p₀ + p₂ * (m * t - c) ^ 2) (fun _ => q₀) ξ ξ' :=
  cylinder_energy_nonneg (α := -1 / 2) hp₀ hp₂ (by nlinarith) c h

/-- The certificate condition of the cylinder is exactly the Suydam threshold: some `α`
works iff `m² p₂ + 4 q₀ ≥ 0` (`tail_exponent_iff_suydam` with `s = m √p₂`). -/
theorem cylinder_exponent_iff_suydam {p₂ q₀ m : ℝ} (hp₂ : 0 ≤ p₂) :
    (∃ α : ℝ, α * (α + 1) * (m ^ 2 * p₂) ≤ q₀) ↔ 0 ≤ m ^ 2 * p₂ + 4 * q₀ := by
  have e : m ^ 2 * p₂ = (m * Real.sqrt p₂) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hp₂]
  rw [e, tail_exponent_iff_suydam]

/-- **Cylinder, Suydam form (necessity).** If `m ≠ 0` and `m² p₂ + 4 q₀ < 0`, the line
`P = p₀ + p₂ (m t)²`, `Q = q₀` has a compactly supported `C¹` mode with negative energy
(`tail_unstable`). -/
theorem cylinder_unstable_of_suydam {p₀ p₂ q₀ m : ℝ} (hp₀ : 0 < p₀) (hp₂ : 0 < p₂)
    (hm : m ≠ 0) (hS : m ^ 2 * p₂ + 4 * q₀ < 0) :
    ∃ ξ ξ' : ℝ → ℝ, ∃ a b : ℝ, LineAdmissible ξ ξ' a b ∧
      lineEnergy (fun t => p₀ + p₂ * (m * t) ^ 2) (fun _ => q₀) ξ ξ' < 0 := by
  set δ := -(m ^ 2 * p₂ + 4 * q₀) / 8 with hδ
  have hδp : 0 < δ := by rw [hδ]; linarith
  have hm2 : 0 < m ^ 2 * p₂ := by positivity
  set Θ := max 1 (p₀ / δ) with hΘ
  have hΘ1 : 1 ≤ Θ := le_max_left _ _
  have hΘ2 : p₀ / δ ≤ Θ := le_max_right _ _
  obtain ⟨ξ, ξ', a, b, -, hA, hneg⟩ := tail_unstable (F := m ^ 2 * p₂ + δ) (G := q₀) (Θ := Θ)
    (P := fun t => p₀ + p₂ * (m * t) ^ 2) (Q := fun _ => q₀) (by fun_prop) continuous_const
    (by linarith) (by linarith) (by linarith)
    (fun x hx => by
      have hx1 : 1 ≤ x := hΘ1.trans hx
      have hx2 : p₀ ≤ δ * x := by
        have := (div_le_iff₀ hδp).mp (hΘ2.trans hx)
        linarith
      nlinarith)
    (fun _ _ => le_rfl)
  exact ⟨ξ, ξ', a, b, hA, hneg⟩

/-! ## Sanity checks -/

/-- Degenerate case: without drive (`Q = 0`) every line is stable (certificate `F = 0`). -/
theorem noPressure_energy_nonneg {P : ℝ → ℝ} (hP : ∀ t, 0 < P t) (hPc : Continuous P)
    {ξ ξ' : ℝ → ℝ} {a b : ℝ} (h : LineAdmissible ξ ξ' a b) :
    0 ≤ lineEnergy P (fun _ => 0) ξ ξ' := by
  have R : Riccati2D (fun t _ => P t) (fun _ _ => 0) (fun _ => 0) :=
    { F := fun _ _ => 0
      Ft := fun _ _ => 0
      Fs := fun _ _ => 0
      hasFDeriv := fun t s => by simpa using hasFDerivAt_const (0 : ℝ) (t, s)
      Ft_cont := continuous_const
      Fs_cont := continuous_const
      P_pos := fun t _ => hP t
      ineq := fun t s => by simp }
  simpa using riccati2D_energy_nonneg (σ := fun _ => 0) R (hPc.comp continuous_fst)
    continuous_const (fun t => hasDerivAt_const t 0) continuous_const 0 h

/-- Accepted fixture: `P = 1 + t²`, `Q = −1/5` (Suydam ratio `−1/5 ≥ −1/4`) is stable. -/
theorem cylinder_fixture_stable {ξ ξ' : ℝ → ℝ} {a b : ℝ} (h : LineAdmissible ξ ξ' a b) :
    0 ≤ lineEnergy (fun t => 1 + 1 * (1 * t - 0) ^ 2) (fun _ => -1 / 5) ξ ξ' :=
  cylinder_stable_of_suydam one_pos one_pos (by norm_num) 0 h

/-- Rejected fixture: `P = 1 + t²`, `Q = −1/2` (ratio `−1/2 < −1/4`) has a negative-energy
mode, so no certificate of any kind exists. -/
theorem cylinder_fixture_unstable :
    ∃ ξ ξ' : ℝ → ℝ, ∃ a b : ℝ, LineAdmissible ξ ξ' a b ∧
      lineEnergy (fun t => 1 + 1 * (1 * t) ^ 2) (fun _ => -1 / 2) ξ ξ' < 0 :=
  cylinder_unstable_of_suydam one_pos one_pos one_ne_zero (by norm_num)

end PlasmaLean.Stability.BallooningReduction
