/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.CanonicalMomentum

/-!
# A polynomial axisymmetric field with all-time full-orbit confinement

Synthetic, dimensionless example (lengths in units of the major radius, field in units of
a reference strength). With `R² = x₀² + x₁²` and `z = x₂`, the poloidal flux is
`ψ = R² z² / 2 + (R² - 1)² / 4`, and the field is
`B = (-x₀ z, -x₁ z, z² + R² - 1) + b (-x₁, x₀, 0)`,
i.e. `∇ψ × ∇φ` (with the `1/R²` cancelled by the chosen `ψ`) plus a toroidal part of
arbitrary strength `b`. Its sublevel set `{ψ ≤ 1/16}` is a solid torus-like region with
`1/2 ≤ R² ≤ 3/2`, avoiding the vertical axis.

`orbit_confined`: every full Newton–Lorentz orbit with normalized rigidity
`m ‖v‖ ≤ |q| / 64` that starts with `ψ ≤ 1/64` and `‖x‖ ≤ 4/3` satisfies `ψ ≤ 11/192`
and `R² ≥ 1/2` for ALL real times. The field is analytic, axisymmetric (tokamak-like),
not derived from coils, not shown to be an MHD equilibrium and not a stellarator. The orbit
is supplied; its existence is not proved here.
-/
public section
noncomputable section
namespace PlasmaLean.Design.PolyTokamak
open PlasmaLean.Fields PlasmaLean.Kinetic WithLp
open scoped RealInnerProductSpace

/-- Squared major radius. -/
@[expose] def R2 (x : Space) : ℝ := x 0 ^ 2 + x 1 ^ 2

/-- Poloidal flux function. -/
@[expose] def psi (x : Space) : ℝ := R2 x * x 2 ^ 2 / 2 + (R2 x - 1) ^ 2 / 4

/-- Explicit gradient of `psi`. -/
@[expose] def psiGrad (x : Space) : Space :=
  toLp 2 ![x 0 * (x 2 ^ 2 + R2 x - 1), x 1 * (x 2 ^ 2 + R2 x - 1), R2 x * x 2]

/-- The axisymmetric field with toroidal strength parameter `b`. -/
@[expose] def field (b : ℝ) (x : Space) : Space :=
  toLp 2 ![-(x 0 * x 2) - b * x 1, -(x 1 * x 2) + b * x 0, x 2 ^ 2 + R2 x - 1]

/-- The gradient formula, as an actual Fréchet derivative. -/
theorem psi_hasFDerivAt (x : Space) : HasFDerivAt psi (innerSL ℝ (psiGrad x)) x := by
  have h0 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).hasFDerivAt (x := x)
  have h1 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 1).hasFDerivAt (x := x)
  have h2 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 2).hasFDerivAt (x := x)
  have hR := (h0.pow 2).add (h1.pow 2)
  have h := ((hR.mul (h2.pow 2)).const_mul (1 / 2)).add
    (((hR.sub_const 1).pow 2).const_mul (1 / 4))
  convert h using 1
  · funext y; simp [psi, R2]; ring
  · ext v
    simp [psiGrad, R2, EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_three,
      dotProduct]
    ring

/-- The field has the axisymmetric flux structure with flux gradient `psiGrad`. -/
theorem field_axisymmetric (b : ℝ) : AxisymmetricFlux (field b) psiGrad := by
  unfold AxisymmetricFlux
  intro x v
  simp [angularZ, field, psiGrad, R2, cross, crossProduct,
    EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_three, dotProduct]
  ring

/-- Points with `ψ ≤ 1/16` lie at `1/2 ≤ R² ≤ 3/2` and `z² ≤ 1/4`. -/
theorem region_bounds (x : Space) (hx : psi x ≤ 1 / 16) :
    1 / 2 ≤ R2 x ∧ R2 x ≤ 3 / 2 ∧ x 2 ^ 2 ≤ 1 / 4 := by
  unfold psi at hx
  have hR : 0 ≤ R2 x := by unfold R2; positivity
  have hz := sq_nonneg (x 2)
  have hsq : (R2 x - 1) ^ 2 ≤ 1 / 4 := by nlinarith [mul_nonneg hR hz]
  have hlo : 1 / 2 ≤ R2 x := by nlinarith [sq_nonneg (R2 x - 1 + 1 / 2)]
  have hhi : R2 x ≤ 3 / 2 := by nlinarith [sq_nonneg (R2 x - 1 - 1 / 2)]
  refine ⟨hlo, hhi, ?_⟩
  nlinarith [sq_nonneg (R2 x - 1)]

/-- Points with `ψ ≤ 1/16` have norm at most `4/3`. -/
theorem region_norm (x : Space) (hx : psi x ≤ 1 / 16) : ‖x‖ ≤ 4 / 3 := by
  obtain ⟨-, hhi, hz⟩ := region_bounds x hx
  have hn := EuclideanSpace.norm_sq_eq x
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] at hn
  have : ‖x‖ ^ 2 ≤ (4 / 3) ^ 2 := by rw [hn]; unfold R2 at hhi; nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp this

/-- Sanity: the reference point `(1,0,0)` is on the magnetic axis `ψ = 0`. -/
theorem psi_axis : psi (toLp 2 ![1, 0, 0]) = 0 := by
  simp [psi, R2]

/-- Sanity: the vertical axis has `ψ = 1/4`, outside the confinement region. -/
theorem psi_vertical_axis (z : ℝ) : psi (toLp 2 ![0, 0, z]) = 1 / 4 := by
  simp [psi, R2]

/-- All-time full-orbit confinement in the polynomial axisymmetric field, for every
toroidal strength `b`, mass `m ≠ 0` and charge `q ≠ 0`. -/
theorem orbit_confined {b m q : ℝ} (hm : m ≠ 0) (hq : q ≠ 0) {x v : ℝ → Space}
    (h : LorentzOrbit m q (fun _ => 0) (field b) x v)
    (hrig : |m| * ‖v 0‖ ≤ |q| / 64) (hψ0 : psi (x 0) ≤ 1 / 64) (hx0 : ‖x 0‖ ≤ 4 / 3)
    (t : ℝ) : psi (x t) ≤ 11 / 192 ∧ 1 / 2 ≤ R2 (x t) ∧ ‖x t‖ ≤ 4 / 3 := by
  have hqpos : 0 < |q| := abs_pos.mpr hq
  have hk : |m| * ‖v 0‖ / |q| ≤ 1 / 64 := by
    rw [div_le_iff₀ hqpos]; linarith
  have hk0 : 0 ≤ |m| * ‖v 0‖ / |q| := by positivity
  have hgap : psi (x 0) + |m| * ‖v 0‖ / |q| * (4 / 3 + ‖x 0‖) ≤ 11 / 192 := by
    have : |m| * ‖v 0‖ / |q| * (4 / 3 + ‖x 0‖) ≤ 1 / 64 * (8 / 3) :=
      mul_le_mul hk (by linarith) (by positivity) (by norm_num)
    linarith
  have hp := orbit_trapped hm hq h psi_hasFDerivAt (field_axisymmetric b)
    (by norm_num : (11 / 192 : ℝ) < 1 / 16) (by norm_num) region_norm hgap t
  have hin : psi (x t) ≤ 1 / 16 := hp.trans (by norm_num)
  exact ⟨hp, (region_bounds _ hin).1, region_norm _ hin⟩

/-! ## Nonaxisymmetric ripple: finite-time confinement

Add the divergence-free, two-fold-periodic perturbation `ε (0, 0, x₀² - x₁²)`, which breaks
the rotational symmetry. Its symmetry defect on `{ψ ≤ 1/16}` is at most `2 |ε|`, so the
canonical-momentum argument gives confinement for times `T` with `2|ε| ‖v‖ T ≤ 1/384`. -/

/-- Rippled field: axisymmetric part plus a nonaxisymmetric vertical perturbation. -/
@[expose] def rippleField (b ε : ℝ) (x : Space) : Space :=
  field b x + toLp 2 ![0, 0, ε * (x 0 ^ 2 - x 1 ^ 2)]

/-- The ripple breaks axisymmetry: its vertical component changes sign under a quarter
turn `(x₀, x₁) ↦ (-x₁, x₀)` at `(1,0,0)` when `ε ≠ 0`. -/
theorem ripple_not_axisymmetric (b ε : ℝ) (hε : ε ≠ 0) :
    rippleField b ε (toLp 2 ![1, 0, 0]) 2 ≠ rippleField b ε (toLp 2 ![0, 1, 0]) 2 := by
  intro h
  have h' : ε = -ε := by
    simpa [rippleField, field, R2] using h
  exact hε (by linarith)

/-- Symmetry defect of the rippled field on the confinement region. -/
theorem ripple_defect (b ε : ℝ) :
    FluxDefectOn (rippleField b ε) psiGrad {y | psi y ≤ 1 / 16} (2 * |ε|) := by
  intro y hy w
  have hax := field_axisymmetric b y w
  have hR := (region_bounds y hy).2.1
  have hR0 : 0 ≤ R2 y := by unfold R2; positivity
  have e : angularZ y (cross w (rippleField b ε y)) + ⟪psiGrad y, w⟫ =
      -(ε * (y 0 ^ 2 - y 1 ^ 2) * (y 0 * w 0 + y 1 * w 1)) := by
    have : angularZ y (cross w (rippleField b ε y)) = angularZ y (cross w (field b y)) -
        ε * (y 0 ^ 2 - y 1 ^ 2) * (y 0 * w 0 + y 1 * w 1) := by
      simp [angularZ, rippleField, field, R2, cross, crossProduct]
      ring
    rw [this, hax]; ring
  rw [e, abs_neg]
  have hw := EuclideanSpace.norm_sq_eq w
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] at hw
  have hsq : (ε * (y 0 ^ 2 - y 1 ^ 2) * (y 0 * w 0 + y 1 * w 1)) ^ 2 ≤ (2 * |ε| * ‖w‖) ^ 2 := by
    have h1 : (y 0 ^ 2 - y 1 ^ 2) ^ 2 ≤ R2 y ^ 2 := by
      unfold R2; nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    have h2 : (y 0 * w 0 + y 1 * w 1) ^ 2 ≤ R2 y * ‖w‖ ^ 2 := by
      rw [hw]; unfold R2
      nlinarith [sq_nonneg (y 0 * w 1 - y 1 * w 0), sq_nonneg (y 0 * w 2),
        sq_nonneg (y 1 * w 2)]
    have h3 : R2 y ^ 2 * R2 y ≤ 4 := by nlinarith
    have hε2 : ε ^ 2 = |ε| ^ 2 := (sq_abs ε).symm
    calc (ε * (y 0 ^ 2 - y 1 ^ 2) * (y 0 * w 0 + y 1 * w 1)) ^ 2
        = ε ^ 2 * (y 0 ^ 2 - y 1 ^ 2) ^ 2 * (y 0 * w 0 + y 1 * w 1) ^ 2 := by ring
      _ ≤ ε ^ 2 * R2 y ^ 2 * (R2 y * ‖w‖ ^ 2) := by gcongr
      _ = ε ^ 2 * (R2 y ^ 2 * R2 y) * ‖w‖ ^ 2 := by ring
      _ ≤ ε ^ 2 * 4 * ‖w‖ ^ 2 := by gcongr
      _ = (2 * |ε| * ‖w‖) ^ 2 := by rw [hε2]; ring
  exact abs_le_of_sq_le_sq' hsq (by positivity) |> abs_le.mpr

/-- Finite-time full-orbit confinement in the rippled, nonaxisymmetric field: with
normalized rigidity at most `1/64`, initial `ψ ≤ 1/64` and `‖x 0‖ ≤ 4/3`, the orbit stays in
`{ψ ≤ 23/384}` (hence `R² ≥ 1/2`) for every `t ∈ [0,T]` provided `2|ε| ‖v 0‖ T ≤ 1/384`. -/
theorem ripple_orbit_confined {b ε m q T : ℝ} (hm : m ≠ 0) (hq : q ≠ 0) (hT : 0 ≤ T)
    {x v : ℝ → Space} (h : LorentzOrbit m q (fun _ => 0) (rippleField b ε) x v)
    (hrig : |m| * ‖v 0‖ ≤ |q| / 64) (hψ0 : psi (x 0) ≤ 1 / 64) (hx0 : ‖x 0‖ ≤ 4 / 3)
    (htime : 2 * |ε| * ‖v 0‖ * T ≤ 1 / 384) :
    ∀ t ∈ Set.Icc 0 T, psi (x t) ≤ 23 / 384 ∧ 1 / 2 ≤ R2 (x t) := by
  have hqpos : 0 < |q| := abs_pos.mpr hq
  have hk : |m| * ‖v 0‖ / |q| ≤ 1 / 64 := by
    rw [div_le_iff₀ hqpos]; linarith
  have hgap : psi (x 0) + |m| * ‖v 0‖ / |q| * (4 / 3 + ‖x 0‖) + 2 * |ε| * ‖v 0‖ * T ≤
      23 / 384 := by
    have : |m| * ‖v 0‖ / |q| * (4 / 3 + ‖x 0‖) ≤ 1 / 64 * (8 / 3) :=
      mul_le_mul hk (by linarith) (by positivity) (by norm_num)
    linarith
  intro t ht
  have hp := orbit_trapped_until hm hq h psi_hasFDerivAt
    (by norm_num : (23 / 384 : ℝ) < 1 / 16) (by norm_num) (by positivity) hT
    (ripple_defect b ε) region_norm hgap t ht
  exact ⟨hp, (region_bounds _ (hp.trans (by norm_num))).1⟩

/-- Sanity: with zero ripple the finite-time theorem holds for every horizon, consistent
with the all-time axisymmetric result. -/
theorem ripple_zero (b : ℝ) : rippleField b 0 = field b := by
  funext x
  simp [rippleField]

end PlasmaLean.Design.PolyTokamak
