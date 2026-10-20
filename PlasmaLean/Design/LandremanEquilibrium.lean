/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.ClebschDivergence
public import PlasmaLean.Kernel.Equilibrium
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Landreman's explicit non-axisymmetric toroidal MHS equilibria, family 1 (`ι = 2`)

Source: M. Landreman, *Analytic toroidal 3D MHD equilibria and steady Euler flows with
invariant surfaces*, arXiv:2609.26742 **v2** (28 Sep 2026), §2, equations (2.1)–(2.29).
Retrieved 20 Oct 2026. This is an **unrefereed preprint**. Every identity used here is
re-proved below from the stated formulas; nothing is taken on trust from the paper. The code
is independent of the Gómez-Serrano–Liehr–Taylor Lean library.

## The field (paper (2.1)–(2.4), with `μ₀ = 1` there)

For `a, b > 0` put `s = x²/a² + y²/b²`, `F = √(1 - (1-s)² - 4z²)` and
`B = ((2zx - (a/b) F y)/s, (2zy + (b/a) F x)/s, 1 - s)` on `𝒰 = {1 - (1-s)² - 4z² > 0}`.
The paper takes `a = √(1+ε)`, `b = √(1-ε)`, `0 < ε < 1` (`aE`, `bE`). Then
`Q = (x² + y² + 4z²)/2`, `H = Q + |B|²/2`, `ψ = (x² + y² + 4z² + |B|² - 2 + ε²)/4` and
`p = p_a - 2ψ`. Most identities hold for all `a, b ≠ 0` with `ε := (a² - b²)/2` (`epsAB`).

## Verified here (all on `𝒰`, with actual Fréchet derivatives)

* `field_divergence_free`: `∇ · B = 0` (Maxwell.lean operator `divergence`).
* `fieldDeriv_field`: `(B · ∇)B = -(x, y, 4z)` (paper (2.8)–(2.9)).
* `force_balance`: the kernel law `ForceBalance` (`J × B = ∇p`) with `J = (∇ × B)/μ₀` from the
  actual derivative and `p = (p_a - 2ψ)/μ₀` with its actual gradient (paper (2.5)).
* `field_tangent_psi`, `current_tangent_psi`, `psi_firstIntegral`: `B · ∇ψ = 0`, `J · ∇ψ = 0`.
* `uv_sq`, `psi_eq_uv`, `psi_nonneg`: field-line labels `u, v` with `u² + v² = (1 - rad)/4` and
  `ψ = (u + ε/2)² + v² ≥ 0` (paper (2.14)–(2.15)).
* `fieldLine_explicit`, `fieldLine_confined`, `fieldLine_closed`: every forward field line with
  `ψ ≤ δ < (1-|ε|)²/4` (paper (2.17)) stays in `𝒰` for all `t ≥ 0`, is the explicit harmonic
  oscillator with frequencies `1, 1, 2` (paper (2.10)), and closes: `γ(t + 2π) = γ(t)`.
* `axis_fieldLine`, `psi_axis`, `axis_nonplanar`: the magnetic axis (2.19)
  `(√(1-ε²) cos ζ, √(1-ε²) sin ζ, (ε/2) sin 2ζ)` is a field line with `ψ = 0`, and it is not
  contained in any plane for `ε ≠ 0`.
* `pressure_pos`, `pressure_boundary`, `pressure_axis`: with `p_a = 2δ`, `p > 0` inside `ψ < δ`,
  `p = 0` on `ψ = δ`, peak `2δ/μ₀` on the axis.
* Geometry: `toroidal_pos` (`x B_y - y B_x = abF > 0`, paper (2.22)), `U_off_axis`, `U_bounded`,
  `field_rotPi` (two field periods), `field_flipX` (stellarator symmetry),
  `field_not_axisymmetric` (not invariant under the quarter turn about `z` when `a² ≠ b²`),
  and the sanity check `field_axisymmetric_limit` (`ε = 0` is invariant).
* `force_balance_SI`, `realistic_instance`: the SI rescaling `B = B₀ B̂(x/L)`,
  `p = (B₀²/μ₀) p̂(x/L)` satisfies the kernel law. For `ε = 1/2`, `δ = 1/64`, `B₀ = 5 T` the axis
  field strength is in `[4.33, 5] T` and the local axis beta is in `[1/16, 1/12]`.

## Geometry and honesty

This configuration is genuinely **toroidal**, not a straight or periodic-cylinder model.
`𝒰` is a bounded region that avoids the `z`-axis, and the field circulates about that axis
(`toroidal_pos`). The paper states that the plasma `Ω_δ = {x ∈ 𝒰 : ψ ≤ δ}` is a solid torus
(via the coordinates (2.11)). That topology is **not** formalized here, and neither are the
covering claim of (2.11) or the volume integrals (2.20)–(2.29).

Idealization (family 1). The rotational transform is `ι ≡ 2`: every field line is closed and
there is no shear (non-generic). The configuration is a linear stretch (2.9) of an
axisymmetric Solov'ev field. It is not optimized and is not coil-derived. The closure
`γ(t + 2π) = γ(t)` is proved; the winding-number statement `ι = 2` (paper (2.23)–(2.25)) is
**not** formalized. No stability is claimed.

The sheared family 2 (paper §3) is not treated.
-/

open scoped RealInnerProductSpace

public section
noncomputable section
namespace PlasmaLean.Design.LandremanEquilibrium
open PlasmaLean.Fields WithLp

/-- Coordinate functional. -/
abbrev pr (i : Fin 3) : Space →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i

/-- `s = x²/a² + y²/b²`. -/
@[expose] def sF (a b : ℝ) (x : Space) : ℝ := x 0 ^ 2 / a ^ 2 + x 1 ^ 2 / b ^ 2

/-- The radicand `1 - (1 - s)² - 4 z²`. -/
@[expose] def rad (a b : ℝ) (x : Space) : ℝ := 1 - (1 - sF a b x) ^ 2 - 4 * x 2 ^ 2

/-- `F = √(1 - (1 - s)² - 4 z²)`. -/
@[expose] def Fr (a b : ℝ) (x : Space) : ℝ := √(rad a b x)

/-- Numerator of `B_x`. -/
@[expose] def N0 (a b : ℝ) (x : Space) : ℝ := 2 * x 2 * x 0 - a / b * Fr a b x * x 1

/-- Numerator of `B_y`. -/
@[expose] def N1 (a b : ℝ) (x : Space) : ℝ := 2 * x 2 * x 1 + b / a * Fr a b x * x 0

/-- The field. -/
@[expose] def field (a b : ℝ) (x : Space) : Space :=
  toLp 2 ![N0 a b x / sF a b x, N1 a b x / sF a b x, 1 - sF a b x]

/-- The region `𝒰`. -/
@[expose] def U (a b : ℝ) : Set Space := {x | 0 < rad a b x}

/-- On `𝒰`, `s > 0` (so the field is smooth there; paper below (2.2)). -/
theorem sF_pos {a b : ℝ} {x : Space} (hx : x ∈ U a b) : 0 < sF a b x := by
  have h : 0 < rad a b x := hx
  unfold rad at h
  nlinarith [sq_nonneg (x 2)]

/-! ## Derivatives -/

@[expose] def dsF (a b : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  (2 * x 0 / a ^ 2) • pr 0 + (2 * x 1 / b ^ 2) • pr 1

/-- Derivative of the radicand. -/
@[expose] def drad (a b : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  (2 * (1 - sF a b x)) • dsF a b x - (8 * x 2) • pr 2

/-- Derivative of `F = √rad` (valid where `rad > 0`). -/
@[expose] def dFr (a b : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  (1 / (2 * Fr a b x)) • drad a b x

/-- Derivative of the numerator `N₀`. -/
@[expose] def dN0 (a b : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  (2 * x 2) • pr 0 + (2 * x 0) • pr 2 - (a / b) • (Fr a b x • pr 1 + x 1 • dFr a b x)

/-- Derivative of the numerator `N₁`. -/
@[expose] def dN1 (a b : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  (2 * x 2) • pr 1 + (2 * x 1) • pr 2 + (b / a) • (Fr a b x • pr 0 + x 0 • dFr a b x)

/-- Derivative of a quotient `N / s`. -/
@[expose] def dQuot (a b : ℝ) (x : Space) (N : ℝ) (dN : Space →L[ℝ] ℝ) : Space →L[ℝ] ℝ :=
  (sF a b x)⁻¹ • dN - (N / sF a b x ^ 2) • dsF a b x

/-- The derivative operator of the field, assembled from its coordinates. -/
@[expose] def fieldDeriv (a b : ℝ) (x : Space) : Space →L[ℝ] Space :=
  (dQuot a b x (N0 a b x) (dN0 a b x)).smulRight (basis 0) +
  (dQuot a b x (N1 a b x) (dN1 a b x)).smulRight (basis 1) +
  (-dsF a b x).smulRight (basis 2)

/-- Transfer a derivative along a pointwise function identity and an operator identity. -/
theorem hfd {f g : Space → ℝ} {L L' : Space →L[ℝ] ℝ} {x : Space} (h : HasFDerivAt g L x)
    (hf : ∀ y, f y = g y) (hL : L = L') : HasFDerivAt f L' x := by
  rw [show f = g from funext hf, ← hL]; exact h

section Derivs
variable (a b : ℝ) (x : Space)

/-- Coordinate functions are differentiable. -/
theorem hasFDerivAt_pr (i : Fin 3) : HasFDerivAt (fun y : Space => y i) (pr i) x :=
  (pr i).hasFDerivAt

/-- Derivative of `s`. -/
theorem hasFDerivAt_sF : HasFDerivAt (sF a b) (dsF a b x) x := by
  have := (((hasFDerivAt_pr x 0).pow 2).mul_const (a ^ 2)⁻¹).add
    (((hasFDerivAt_pr x 1).pow 2).mul_const (b ^ 2)⁻¹)
  refine hfd this (fun y => by simp [sF, div_eq_mul_inv]) ?_
  ext v; simp [dsF]; ring

/-- Derivative of the radicand. -/
theorem hasFDerivAt_rad : HasFDerivAt (rad a b) (drad a b x) x := by
  have := ((((hasFDerivAt_sF a b x).const_sub 1).pow 2).const_sub 1).sub
    (((hasFDerivAt_pr x 2).pow 2).const_mul 4)
  refine hfd this (fun y => rfl) ?_
  ext v; simp [drad]; ring

/-- Derivative of `F` on `𝒰`. -/
theorem hasFDerivAt_Fr (hx : x ∈ U a b) : HasFDerivAt (Fr a b) (dFr a b x) x := by
  have := (hasFDerivAt_rad a b x).sqrt (ne_of_gt hx)
  exact hfd this (fun y => rfl) rfl

/-- Derivative of `N₀` on `𝒰`. -/
theorem hasFDerivAt_N0 (hx : x ∈ U a b) : HasFDerivAt (N0 a b) (dN0 a b x) x := by
  have := (((hasFDerivAt_pr x 2).const_mul 2).mul (hasFDerivAt_pr x 0)).sub
    (((hasFDerivAt_Fr a b x hx).const_mul (a / b)).mul (hasFDerivAt_pr x 1))
  refine hfd this (fun y => rfl) ?_
  ext v; simp [dN0]; ring

/-- Derivative of `N₁` on `𝒰`. -/
theorem hasFDerivAt_N1 (hx : x ∈ U a b) : HasFDerivAt (N1 a b) (dN1 a b x) x := by
  have := (((hasFDerivAt_pr x 2).const_mul 2).mul (hasFDerivAt_pr x 1)).add
    (((hasFDerivAt_Fr a b x hx).const_mul (b / a)).mul (hasFDerivAt_pr x 0))
  refine hfd this (fun y => rfl) ?_
  ext v; simp [dN1]; ring

/-- Derivative of `N / s` on `𝒰`. -/
theorem hasFDerivAt_quot (N : Space → ℝ) (dN : Space →L[ℝ] ℝ) (hx : x ∈ U a b)
    (h : HasFDerivAt N dN x) :
    HasFDerivAt (fun y => N y / sF a b y) (dQuot a b x (N x) dN) x := by
  have hs := (sF_pos hx).ne'
  have hi := (hasDerivAt_inv hs).hasFDerivAt.comp x (hasFDerivAt_sF a b x)
  have := h.mul hi
  refine hfd this (fun y => by simp [div_eq_mul_inv]) ?_
  ext v; simp [dQuot]; field_simp; ring

/-- The actual Fréchet derivative of the field at every point of `𝒰`. -/
theorem field_hasFDerivAt (hx : x ∈ U a b) :
    HasFDerivAt (field a b) (fieldDeriv a b x) x := by
  have hB := hasFDerivAt_of_coords (B := field a b)
    (L := ![dQuot a b x (N0 a b x) (dN0 a b x), dQuot a b x (N1 a b x) (dN1 a b x),
      -dsF a b x]) (x := x) (fun k => by
        fin_cases k
        · exact hasFDerivAt_quot a b x _ _ hx (hasFDerivAt_N0 a b x hx)
        · exact hasFDerivAt_quot a b x _ _ hx (hasFDerivAt_N1 a b x hx)
        · exact hfd ((hasFDerivAt_sF a b x).const_sub 1) (fun y => by simp [field]) rfl)
  refine hB.congr_fderiv ?_
  simp [fieldDeriv, Fin.sum_univ_three]

end Derivs

/-- Coordinates of the field derivative. -/
theorem fieldDeriv_apply (a b : ℝ) (x v : Space) :
    fieldDeriv a b x v 0 = dQuot a b x (N0 a b x) (dN0 a b x) v ∧
    fieldDeriv a b x v 1 = dQuot a b x (N1 a b x) (dN1 a b x) v ∧
    fieldDeriv a b x v 2 = -dsF a b x v := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [fieldDeriv, basis]

/-! ## Algebraic closing tactic

On `𝒰` the only non-polynomial quantity is `F = √rad`. After clearing denominators the
identities below are polynomial in `F`; `sq_elim F using h` rewrites `Fᵏ` (`k ≤ 8`) through
`F² = rad` and closes the remaining rational identity. -/

/-- Reduce powers of `F` through `h : F ^ 2 = R`, then clear denominators. -/
macro "sq_elim " F:term " using " h:term : tactic => `(tactic| (
  ring_nf
  simp only [show $F ^ 3 = $F * $F ^ 2 by ring, show $F ^ 4 = ($F ^ 2) ^ 2 by ring,
    show $F ^ 5 = $F * ($F ^ 2) ^ 2 by ring, show $F ^ 6 = ($F ^ 2) ^ 3 by ring,
    show $F ^ 7 = $F * ($F ^ 2) ^ 3 by ring, show $F ^ 8 = ($F ^ 2) ^ 4 by ring, $h:term]
  field_simp))

/-- `a² b² s = b² x² + a² y²`, kept as an atom while clearing denominators. -/
@[expose] def Sden (a b : ℝ) (x : Space) : ℝ := b ^ 2 * x 0 ^ 2 + a ^ 2 * x 1 ^ 2

/-- `sF` in cleared form. -/
theorem sF_eq {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (x : Space) :
    sF a b x = Sden a b x / (a ^ 2 * b ^ 2) := by
  unfold sF Sden; field_simp

/-- Clearing data at a point of `𝒰`: `S ≠ 0`, `F ≠ 0` and `F²` in cleared form. -/
theorem point_data {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) {x : Space} (hx : x ∈ U a b) :
    Sden a b x ≠ 0 ∧ Fr a b x ≠ 0 ∧
    Fr a b x ^ 2 = 1 - (1 - Sden a b x / (a ^ 2 * b ^ 2)) ^ 2 - 4 * x 2 ^ 2 := by
  have hs := (sF_pos hx).ne'
  refine ⟨?_, (Real.sqrt_pos.mpr hx).ne', ?_⟩
  · intro h; apply hs; rw [sF_eq ha hb, h]; simp
  · rw [Fr, Real.sq_sqrt hx.le, rad, sF_eq ha hb]

/-! ## `∇ · B = 0` and the transport identity `(B · ∇) B = -D x` -/

/-- `∇ · B = 0` on `𝒰` (paper, below (2.4), via the stretch (2.9)). -/
theorem field_divergence_free {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) {x : Space}
    (hx : x ∈ U a b) : divergence (fderiv ℝ (field a b) x) = 0 := by
  rw [(field_hasFDerivAt a b x hx).fderiv, divergence_apply]
  obtain ⟨e0, -, -⟩ := fieldDeriv_apply a b x (basis 0)
  obtain ⟨-, e1, -⟩ := fieldDeriv_apply a b x (basis 1)
  obtain ⟨-, -, e2⟩ := fieldDeriv_apply a b x (basis 2)
  rw [e0, e1, e2]
  obtain ⟨hS, hF, -⟩ := point_data ha hb hx
  simp [dQuot, dN0, dN1, dFr, drad, dsF, basis, N0, N1, sF_eq ha hb]
  field_simp
  unfold Sden
  ring

/-- The anisotropic position vector `D x = (x, y, 4z)`, `D = diag(1,1,4)` (paper (2.8)). -/
@[expose] def Dvec (x : Space) : Space := toLp 2 ![x 0, x 1, 4 * x 2]

/-- Transport identity `(B · ∇) B = -D x` on `𝒰` (paper (2.8)–(2.9): `B · ∇B = -∇Q`). -/
theorem fieldDeriv_field {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) {x : Space} (hx : x ∈ U a b) :
    fieldDeriv a b x (field a b x) = -Dvec x := by
  obtain ⟨e0, e1, e2⟩ := fieldDeriv_apply a b x (field a b x)
  obtain ⟨hS, hF, hF2⟩ := point_data ha hb hx
  apply space_ext
  · rw [e0]
    simp only [Fin.isValue, dQuot, sF_eq ha hb, inv_div, dN0, dFr, one_div, mul_inv_rev, drad,
        dsF, smul_add, N0, field, N1, sub_apply, smul_apply, add_apply, PiLp.proj_apply,
        Matrix.cons_val_zero, smul_eq_mul, Matrix.cons_val, Matrix.cons_val_one, Dvec,
        PiLp.neg_apply]
    generalize Fr a b x = F at *
    field_simp
    sq_elim F using hF2
    unfold Sden
    ring
  · rw [e1]
    simp only [Fin.isValue, dQuot, sF_eq ha hb, inv_div, dN1, dFr, one_div, mul_inv_rev, drad,
        dsF, smul_add, N1, field, N0, sub_apply, add_apply, smul_apply, PiLp.proj_apply,
        Matrix.cons_val_one, Matrix.cons_val_zero, smul_eq_mul, Matrix.cons_val, Dvec,
        PiLp.neg_apply]
    generalize Fr a b x = F at *
    field_simp
    sq_elim F using hF2
    unfold Sden
    ring
  · rw [e2]
    simp [dsF, N0, N1, field, Dvec, sF_eq ha hb]
    field_simp
    unfold Sden
    ring

/-- The transport identity for the actual Fréchet derivative. -/
theorem field_transport {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) {x : Space} (hx : x ∈ U a b) :
    fderiv ℝ (field a b) x (field a b x) = -Dvec x := by
  rw [(field_hasFDerivAt a b x hx).fderiv, fieldDeriv_field ha hb hx]


/-! ## Generic vector algebra: `(∇ × B) × B = (B · ∇)B - ∇|B|²/2` -/

/-- `Lᵀ B`, the vector with coordinates `⟪B, L eᵢ⟫` (equal to `∇|B|²/2` when `L = DB`). -/
@[expose] def adjApply (L : Space →L[ℝ] Space) (B : Space) : Space :=
  toLp 2 ![⟪B, L (basis 0)⟫, ⟪B, L (basis 1)⟫, ⟪B, L (basis 2)⟫]

/-- Expansion of a vector in the coordinate basis. -/
theorem eq_sum_basis (v : Space) : v = v 0 • basis 0 + v 1 • basis 1 + v 2 • basis 2 := by
  ext i; fin_cases i <;> simp [basis]

/-- Real inner product in coordinates. -/
theorem inner_coords (u v : Space) : ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]; ring

/-- `⟪B, L v⟫ = ⟪Lᵀ B, v⟫`. -/
theorem inner_apply_eq_adj (L : Space →L[ℝ] Space) (B v : Space) :
    ⟪B, L v⟫ = ⟪adjApply L B, v⟫ := by
  conv_lhs => rw [eq_sum_basis v]
  simp only [map_add, map_smul, inner_add_right, inner_smul_right]
  rw [inner_coords (adjApply L B) v]
  simp [adjApply]
  ring

/-- The vector identity `(curl L) × B = L B - Lᵀ B`, for every operator `L`. -/
theorem curl_cross_eq (L : Space →L[ℝ] Space) (B : Space) :
    cross (curl L) B = L B - adjApply L B := by
  obtain ⟨c0, c1, c2⟩ := curl_coords L
  have hLB : L B = B 0 • L (basis 0) + B 1 • L (basis 1) + B 2 • L (basis 2) := by
    conv_lhs => rw [eq_sum_basis B]
    simp only [map_add, map_smul]
  obtain ⟨x0, x1, x2⟩ := cross_coords (curl L) B
  apply space_ext
  · rw [x0, c1, c2, hLB]; simp [adjApply, inner_coords]; ring
  · rw [x1, c0, c2, hLB]; simp [adjApply, inner_coords]; ring
  · rw [x2, c0, c1, hLB]; simp [adjApply, inner_coords]; ring

/-! ## Bernoulli function, flux label and pressure -/

/-- Hydrodynamic pressure `Q = (x² + y² + 4z²)/2` (paper (2.3)). -/
@[expose] def Qf (x : Space) : ℝ := (x 0 ^ 2 + x 1 ^ 2 + 4 * x 2 ^ 2) / 2

/-- Bernoulli function `H = Q + |B|²/2` (paper (2.3)). -/
@[expose] def H (a b : ℝ) (x : Space) : ℝ := Qf x + ‖field a b x‖ ^ 2 / 2

/-- Its gradient `∇H = D x + (DB)ᵀ B`. -/
@[expose] def gradH (a b : ℝ) (x : Space) : Space :=
  Dvec x + adjApply (fieldDeriv a b x) (field a b x)

/-- The deformation parameter `ε = (a² - b²)/2` (`= ε` when `a = √(1+ε)`, `b = √(1-ε)`). -/
@[expose] def epsAB (a b : ℝ) : ℝ := (a ^ 2 - b ^ 2) / 2

/-- Flux label `ψ = (H - (a²+b²)/2 + ε²/2)/2`; with `a² + b² = 2` this is paper (2.4),
`ψ = (x² + y² + 4z² + |B|² - 2 + ε²)/4`. -/
@[expose] def psi (a b : ℝ) (x : Space) : ℝ :=
  (H a b x - (a ^ 2 + b ^ 2) / 2 + epsAB a b ^ 2 / 2) / 2

/-- `∇Q = D x`. -/
theorem Qf_hasFDerivAt (x : Space) : HasFDerivAt Qf (innerSL ℝ (Dvec x)) x := by
  have := ((((hasFDerivAt_pr x 0).pow 2).add ((hasFDerivAt_pr x 1).pow 2)).add
    (((hasFDerivAt_pr x 2).pow 2).const_mul 4)).mul_const (2 : ℝ)⁻¹
  refine hfd this (fun y => by simp [Qf]; ring) ?_
  ext v
  simp [Dvec, inner_coords]
  ring

/-- `H` has gradient `gradH` on `𝒰`. -/
theorem H_hasFDerivAt (a b : ℝ) {x : Space} (hx : x ∈ U a b) :
    HasFDerivAt (H a b) (innerSL ℝ (gradH a b x)) x := by
  have h := (Qf_hasFDerivAt x).add (((field_hasFDerivAt a b x hx).norm_sq).mul_const (2 : ℝ)⁻¹)
  refine hfd h (fun y => by simp [H]; ring) ?_
  ext v
  simp only [add_apply, innerSL_apply_apply, gradH, inner_add_left]
  simp [inner_apply_eq_adj]

/-- Gradient of `ψ`: `∇ψ = ∇H / 2`. -/
theorem psi_hasFDerivAt (a b : ℝ) {x : Space} (hx : x ∈ U a b) :
    HasFDerivAt (psi a b) (innerSL ℝ ((1 / 2 : ℝ) • gradH a b x)) x := by
  have h := (((H_hasFDerivAt a b hx).sub_const ((a ^ 2 + b ^ 2) / 2)).add_const
    (epsAB a b ^ 2 / 2)).mul_const (2 : ℝ)⁻¹
  refine hfd h (fun y => by simp [psi]; ring) ?_
  ext v
  simp

/-- Ampère current `J = (∇ × B)/μ₀` from the actual derivative. -/
@[expose] def current (μ₀ a b : ℝ) (x : Space) : Space :=
  μ₀⁻¹ • curl (fderiv ℝ (field a b) x)

/-- Pressure `p = (p_a - 2ψ)/μ₀` (paper (2.4), there with `μ₀ = 1`). -/
@[expose] def pressure (μ₀ pa a b : ℝ) (x : Space) : ℝ := (pa - 2 * psi a b x) / μ₀

/-- Pressure gradient `∇p = -∇H/μ₀`. -/
@[expose] def pressureGrad (μ₀ a b : ℝ) (x : Space) : Space := (-μ₀⁻¹) • gradH a b x

/-- The pressure gradient is the actual Fréchet derivative of the pressure on `𝒰`. -/
theorem pressure_hasFDerivAt (μ₀ pa a b : ℝ) {x : Space} (hx : x ∈ U a b) :
    HasFDerivAt (pressure μ₀ pa a b) (innerSL ℝ (pressureGrad μ₀ a b x)) x := by
  have h := (((psi_hasFDerivAt a b hx).const_mul 2).const_sub pa).mul_const μ₀⁻¹
  refine hfd h (fun y => by simp [pressure, div_eq_mul_inv]) ?_
  ext v
  simp [pressureGrad]

open Matrix in
/-- **Force balance** `J × B = ∇p` (the domain-kernel law) at every point of `𝒰`, with the
actual Ampère current and the actual pressure gradient (paper (2.5)). -/
theorem force_balance {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (μ₀ : ℝ) {x : Space}
    (hx : x ∈ U a b) :
    ForceBalance (ofLp (field a b x)) (ofLp (current μ₀ a b x)) (ofLp (pressureGrad μ₀ a b x)) := by
  refine ⟨?_⟩
  have e : ofLp (current μ₀ a b x) ⨯₃ ofLp (field a b x) =
      ofLp (cross (current μ₀ a b x) (field a b x)) := by simp [cross]
  have hc : current μ₀ a b x = μ₀⁻¹ • curl (fieldDeriv a b x) := by
    rw [current, (field_hasFDerivAt a b x hx).fderiv]
  rw [e, hc, ← crossBilinear_apply, map_smul, _root_.smul_apply,
    crossBilinear_apply, curl_cross_eq, fieldDeriv_field ha hb hx, pressureGrad, gradH]
  congr 1
  simp only [neg_smul, smul_add]
  module


open Matrix in
/-- Via the kernel: `B · ∇ψ = 0` on `𝒰` (`ψ` is a flux function). -/
theorem field_tangent_psi {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) {x : Space} (hx : x ∈ U a b) :
    ⟪field a b x, gradH a b x⟫ = 0 := by
  have := force_balance ha hb 1 hx
  have h := field_tangency (ofLp (field a b x)) (ofLp (current 1 a b x))
    (ofLp (pressureGrad 1 a b x))
  rw [inner_coords]
  simp [dotProduct, Fin.sum_univ_three, pressureGrad] at h
  linarith

open Matrix in
/-- Via the kernel: `J · ∇ψ = 0` on `𝒰` (the current lies on the flux surfaces). -/
theorem current_tangent_psi {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (μ₀ : ℝ) {x : Space}
    (hx : x ∈ U a b) : ⟪current μ₀ a b x, gradH a b x⟫ = 0 := by
  have := force_balance ha hb 1 hx
  have h := current_tangency (ofLp (field a b x)) (ofLp (current 1 a b x))
    (ofLp (pressureGrad 1 a b x))
  have hc : current μ₀ a b x = μ₀⁻¹ • current 1 a b x := by simp [current]
  rw [hc, inner_smul_left, inner_coords]
  simp only [dotProduct, pressureGrad, inv_one, neg_smul, one_smul, PiLp.neg_apply, mul_neg,
      Finset.sum_neg_distrib, Fin.sum_univ_three, Fin.isValue, neg_add_rev] at h
  simp only [conj_trivial]
  rw [show (current 1 a b x) 0 * (gradH a b x) 0 + (current 1 a b x) 1 * (gradH a b x) 1 +
    (current 1 a b x) 2 * (gradH a b x) 2 = 0 by linarith, mul_zero]


/-- `ψ` is an exact first integral of the field lines on `𝒰`. -/
theorem psi_firstIntegral {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    FirstIntegralOn (field a b) (psi a b) (U a b) := by
  intro x hx
  refine ⟨(psi_hasFDerivAt a b hx).differentiableAt, ?_⟩
  rw [(psi_hasFDerivAt a b hx).fderiv]
  simp [real_inner_comm, field_tangent_psi ha hb hx]

/-! ## Field-line labels `(u, v)` (paper (2.11)–(2.15)) -/

/-- Field-line label `u = (x²/a² + B_x²/a² - y²/b² - B_y²/b²)/4` (from paper (2.14)). -/
@[expose] def uF (a b : ℝ) (x : Space) : ℝ :=
  ((x 0 / a) ^ 2 + (field a b x 0 / a) ^ 2 - (x 1 / b) ^ 2 - (field a b x 1 / b) ^ 2) / 4

/-- Field-line label `v = (x y/(ab) + B_x B_y/(ab))/2`. -/
@[expose] def vF (a b : ℝ) (x : Space) : ℝ :=
  ((x 0 / a) * (x 1 / b) + (field a b x 0 / a) * (field a b x 1 / b)) / 2

/-- `u² + v² = q² = (1 - rad)/4 = z² + (1-s)²/4` on `𝒰` (paper, below (2.16)). -/
theorem uv_sq {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) {x : Space} (hx : x ∈ U a b) :
    uF a b x ^ 2 + vF a b x ^ 2 = (1 - rad a b x) / 4 := by
  obtain ⟨hS, hF, hF2⟩ := point_data ha hb hx
  simp only [uF, Fin.isValue, field, N0, sF_eq ha hb, N1, Matrix.cons_val_zero,
      Matrix.cons_val_one, vF, rad]
  generalize Fr a b x = F at *
  field_simp
  sq_elim F using hF2
  unfold Sden
  ring

/-- `ψ = (u + ε/2)² + v²` on `𝒰` (paper (2.15)). -/
theorem psi_eq_uv {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) {x : Space} (hx : x ∈ U a b) :
    psi a b x = (uF a b x + epsAB a b / 2) ^ 2 + vF a b x ^ 2 := by
  obtain ⟨hS, hF, hF2⟩ := point_data ha hb hx
  simp only [psi, H, Qf, Fin.isValue, field, N0, sF_eq ha hb, N1, EuclideanSpace.norm_sq_eq,
      Real.norm_eq_abs, sq_abs, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, epsAB, uF, vF]
  generalize Fr a b x = F at *
  field_simp
  sq_elim F using hF2
  unfold Sden
  ring

/-- `ψ ≥ 0` on `𝒰`, vanishing exactly on the magnetic axis `u = -ε/2, v = 0`. -/
theorem psi_nonneg {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) {x : Space} (hx : x ∈ U a b) :
    0 ≤ psi a b x := by
  rw [psi_eq_uv ha hb hx]; positivity


/-- Separating-shell bound: on `𝒰`, `ψ ≤ δ` forces `rad ≥ 1 - (|ε| + 2√δ)²`
(paper (2.17): `ψ`-circles of radius `√ψ` about `(-ε/2, 0)` inside the disc `q < 1/2`). -/
theorem rad_lower {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) {δ : ℝ} {x : Space} (hx : x ∈ U a b)
    (hψ : psi a b x ≤ δ) : 1 - (|epsAB a b| + 2 * √δ) ^ 2 ≤ rad a b x := by
  have h1 := uv_sq ha hb hx
  have h2 := psi_eq_uv ha hb hx
  set u := uF a b x
  set v := vF a b x
  set ε := epsAB a b
  set Q2 := (1 - rad a b x) / 4 with hQ2
  have hQ0 : 0 ≤ Q2 := by rw [← h1]; positivity
  set q := √Q2
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqq : q ^ 2 = Q2 := Real.sq_sqrt hQ0
  have hu : |u| ≤ q := Real.abs_le_sqrt (by nlinarith [sq_nonneg v])
  have hεu : -(|ε| * q) ≤ ε * u := by
    have := abs_mul ε u
    have := neg_abs_le (ε * u)
    have : |ε| * |u| ≤ |ε| * q := mul_le_mul_of_nonneg_left hu (abs_nonneg ε)
    linarith
  have hsq : (q - |ε| / 2) ^ 2 ≤ δ := by
    have : psi a b x = q ^ 2 + ε * u + ε ^ 2 / 4 := by rw [h2, hqq, ← h1]; ring
    nlinarith [sq_abs ε]
  have hle : q - |ε| / 2 ≤ √δ := by
    have := Real.abs_le_sqrt hsq
    exact (le_abs_self _).trans this
  have hq2 : q ^ 2 ≤ (|ε| / 2 + √δ) ^ 2 := by
    have : q ≤ |ε| / 2 + √δ := by linarith
    exact pow_le_pow_left₀ hq0 this 2
  rw [hqq, hQ2] at hq2
  nlinarith

/-- The shell radius is positive when `0 ≤ δ < (1 - |ε|)²/4` and `|ε| < 1` (paper (2.17)). -/
theorem shell_pos {ε δ : ℝ} (hε : |ε| < 1) (hδ : δ < (1 - |ε|) ^ 2 / 4) :
    0 < 1 - (|ε| + 2 * √δ) ^ 2 := by
  have hs : √δ < (1 - |ε|) / 2 := by
    rw [Real.sqrt_lt' (by linarith)]
    nlinarith
  have h0 := Real.sqrt_nonneg δ
  have h1 := abs_nonneg ε
  nlinarith

/-! ## Field lines are harmonic oscillators (paper (2.10)) -/

/-- Coordinates of a differentiable curve. -/
theorem coord_hasDerivAt {f : ℝ → Space} {f' : Space} {s : ℝ} (h : HasDerivAt f f' s)
    (k : Fin 3) : HasDerivAt (fun r => f r k) (f' k) s :=
  (pr k).hasFDerivAt.comp_hasDerivAt s h

/-- Along a field line inside `𝒰`, `d/dt B(γ) = -D γ`, i.e. `γ'' = -D γ` (paper (2.10)). -/
theorem fieldLine_accel {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) {γ : ℝ → Space} {s : ℝ}
    (hγ : HasDerivAt γ (field a b (γ s)) s) (hU : γ s ∈ U a b) :
    HasDerivAt (fun r => field a b (γ r)) (-Dvec (γ s)) s := by
  have := (field_hasFDerivAt a b (γ s) hU).comp_hasDerivAt s hγ
  rwa [fieldDeriv_field ha hb hU] at this

/-- Uniqueness for the harmonic oscillator `p' = q`, `q' = -ω² p` on `[0, T]`. -/
theorem osc_unique {p q : ℝ → ℝ} {ω T t : ℝ} (hω : ω ≠ 0)
    (hp : ∀ s ∈ Set.Icc 0 T, HasDerivAt p (q s) s)
    (hq : ∀ s ∈ Set.Icc 0 T, HasDerivAt q (-(ω ^ 2 * p s)) s) (ht : t ∈ Set.Icc 0 T) :
    p t = p 0 * Real.cos (ω * t) + q 0 / ω * Real.sin (ω * t) := by
  set c := p 0
  set d := q 0
  have hcos (s : ℝ) : HasDerivAt (fun s => Real.cos (ω * s)) (-Real.sin (ω * s) * ω) s := by
    have := ((hasDerivAt_id s).const_mul ω).cos
    simpa using this
  have hsin (s : ℝ) : HasDerivAt (fun s => Real.sin (ω * s)) (Real.cos (ω * s) * ω) s := by
    have := ((hasDerivAt_id s).const_mul ω).sin
    simpa using this
  let e : ℝ → ℝ := fun s => p s - c * Real.cos (ω * s) - d / ω * Real.sin (ω * s)
  let g : ℝ → ℝ := fun s => q s + c * ω * Real.sin (ω * s) - d * Real.cos (ω * s)
  have he (s : ℝ) (hs : s ∈ Set.Icc 0 T) : HasDerivAt e (g s) s := by
    have := ((hp s hs).sub ((hcos s).const_mul c)).sub ((hsin s).const_mul (d / ω))
    refine this.congr_deriv ?_
    simp only [g]; field_simp; ring
  have hg (s : ℝ) (hs : s ∈ Set.Icc 0 T) : HasDerivAt g (-(ω ^ 2 * e s)) s := by
    have := ((hq s hs).add ((hsin s).const_mul (c * ω))).sub ((hcos s).const_mul d)
    refine this.congr_deriv ?_
    simp only [e]; field_simp; ring
  have hK (s : ℝ) (hs : s ∈ Set.Icc 0 T) :
      HasDerivAt (fun s => ω ^ 2 * e s ^ 2 + g s ^ 2) 0 s := by
    have := (((he s hs).pow 2).const_mul (ω ^ 2)).add ((hg s hs).pow 2)
    refine this.congr_deriv ?_
    simp; ring
  have hc := Kinetic.exact_invariant (K' := fun _ => 0) hK (by simp) ht
  have e0 : e 0 = 0 := by simp [e, c]
  have g0 : g 0 = 0 := by simp [g, d]
  simp only [e0, g0] at hc
  have hω2 : 0 < ω ^ 2 := by positivity
  have het : e t = 0 := by
    have : ω ^ 2 * e t ^ 2 = 0 := by nlinarith [sq_nonneg (g t), sq_nonneg (e t)]
    have := (mul_eq_zero.mp this).resolve_left hω2.ne'
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  simp only [e] at het
  linarith

/-- The explicit oscillator solution with initial position `c` and velocity `d`:
frequencies `1, 1, 2` in `x, y, z` (paper (2.10)–(2.11)). -/
@[expose] def oscSol (c d : Space) (t : ℝ) : Space :=
  toLp 2 ![c 0 * Real.cos t + d 0 * Real.sin t, c 1 * Real.cos t + d 1 * Real.sin t,
    c 2 * Real.cos (2 * t) + d 2 / 2 * Real.sin (2 * t)]

/-- **Explicit field lines.** A field line that stays in `𝒰` on `[0, T]` is the explicit
oscillator solution determined by its initial point and the field there. -/
theorem fieldLine_explicit {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) {γ : ℝ → Space} {T : ℝ}
    (hγ : ∀ s ∈ Set.Icc 0 T, HasDerivAt γ (field a b (γ s)) s)
    (hU : ∀ s ∈ Set.Icc 0 T, γ s ∈ U a b) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    γ t = oscSol (γ 0) (field a b (γ 0)) t := by
  have hacc (s : ℝ) (hs : s ∈ Set.Icc 0 T) := fieldLine_accel ha hb (hγ s hs) (hU s hs)
  have h01 (k : Fin 3) (hk : k = 0 ∨ k = 1) :
      γ t k = γ 0 k * Real.cos t + field a b (γ 0) k * Real.sin t := by
    have := osc_unique (p := fun s => γ s k) (q := fun s => field a b (γ s) k) (ω := 1)
      one_ne_zero (fun s hs => coord_hasDerivAt (hγ s hs) k)
      (fun s hs => (coord_hasDerivAt (hacc s hs) k).congr_deriv (by
        rcases hk with rfl | rfl <;> simp [Dvec])) ht
    simpa using this
  have h2 : γ t 2 = γ 0 2 * Real.cos (2 * t) + field a b (γ 0) 2 / 2 * Real.sin (2 * t) :=
    osc_unique (p := fun s => γ s 2) (q := fun s => field a b (γ s) 2) (ω := 2)
      two_ne_zero (fun s hs => coord_hasDerivAt (hγ s hs) 2)
      (fun s hs => (coord_hasDerivAt (hacc s hs) 2).congr_deriv (by norm_num [Dvec])) ht
  apply space_ext
  · rw [h01 0 (Or.inl rfl)]; simp [oscSol]
  · rw [h01 1 (Or.inr rfl)]; simp [oscSol]
  · rw [h2]; simp [oscSol]

/-- The oscillator solutions are `2π`-periodic. -/
theorem oscSol_periodic (c d : Space) (t : ℝ) : oscSol c d (t + 2 * Real.pi) = oscSol c d t := by
  have h2 : 2 * (t + 2 * Real.pi) = 2 * t + 2 * Real.pi + 2 * Real.pi := by ring
  simp only [oscSol, Real.cos_add_two_pi, Real.sin_add_two_pi, h2]


/-! ## All-time confinement and closed field lines -/

/-- The radicand is continuous. -/
theorem continuous_rad (a b : ℝ) : Continuous (rad a b) := by
  unfold rad sF; fun_prop

/-- **Field-line confinement for all forward time.** Let `|ε| < 1`, `δ < (1-|ε|)²/4`
(paper (2.17)). A forward field line starting in `𝒰` with `ψ ≤ δ` stays in `𝒰`, keeps
its value of `ψ`, and stays at `rad ≥ 1 - (|ε| + 2√δ)² > 0`, for every `t ≥ 0`. -/
theorem fieldLine_confined {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hε : |epsAB a b| < 1)
    {δ : ℝ} (hδ : δ < (1 - |epsAB a b|) ^ 2 / 4) {γ : ℝ → Space}
    (hγ : IsForwardFieldLine (field a b) γ) (h0 : γ 0 ∈ U a b) (hψ0 : psi a b (γ 0) ≤ δ)
    {t : ℝ} (ht : 0 ≤ t) :
    γ t ∈ U a b ∧ psi a b (γ t) = psi a b (γ 0) ∧
      1 - (|epsAB a b| + 2 * √δ) ^ 2 ≤ rad a b (γ t) := by
  set r₁ := 1 - (|epsAB a b| + 2 * √δ) ^ 2 with hr₁def
  have hr₁ : 0 < r₁ := shell_pos hε hδ
  have hfi := psi_firstIntegral ha hb
  have hcont : ContinuousOn (fun s => rad a b (γ s)) (Set.Icc 0 t) := by
    refine (continuous_rad a b).comp_continuousOn ?_
    intro s hs
    exact (hγ s hs.1).continuousAt.continuousWithinAt
  -- conservation on any initial interval contained in `𝒰`
  have hcons (σ : ℝ) (hσ : σ ∈ Set.Icc 0 t) (hin : ∀ s ∈ Set.Icc 0 σ, γ s ∈ U a b) :
      psi a b (γ σ) = psi a b (γ 0) :=
    firstIntegral_conserved hfi (T := σ) (fun s hs => hγ s hs.1) hin ⟨hσ.1, le_rfl⟩
  have hstay : ∀ s ∈ Set.Icc 0 t, r₁ / 2 < rad a b (γ s) := by
    by_contra hneg
    push Not at hneg
    set B := Set.Icc 0 t ∩ (fun s => rad a b (γ s)) ⁻¹' Set.Iic (r₁ / 2) with hB
    have hBne : B.Nonempty := by
      obtain ⟨s, hs, hle⟩ := hneg
      exact ⟨s, hs, hle⟩
    have hBcl : IsClosed B := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hBbdd : BddBelow B := ⟨0, fun s hs => hs.1.1⟩
    set τ := sInf B
    have hτ : τ ∈ B := hBcl.csInf_mem hBne hBbdd
    have hbefore (s : ℝ) (hs0 : 0 ≤ s) (hsτ : s < τ) : r₁ / 2 < rad a b (γ s) := by
      by_contra hc
      push Not at hc
      have : s ∈ B := ⟨⟨hs0, by linarith [hτ.1.2]⟩, hc⟩
      exact absurd (csInf_le hBbdd this) (not_le.mpr hsτ)
    have hstart : r₁ ≤ rad a b (γ 0) := rad_lower ha hb h0 hψ0
    have hτt : τ ∈ Set.Icc 0 t := hτ.1
    have hcontτ : ContinuousOn (fun s => rad a b (γ s)) (Set.Icc 0 τ) :=
      hcont.mono (Set.Icc_subset_Icc le_rfl hτt.2)
    obtain ⟨σ, hσ, hσeq⟩ := intermediate_value_Icc' hτt.1 hcontτ
      (show 3 * r₁ / 4 ∈ Set.Icc (rad a b (γ τ)) (rad a b (γ 0)) by
        constructor
        · have : rad a b (γ τ) ≤ r₁ / 2 := hτ.2
          linarith
        · linarith)
    have hστ : σ < τ := by
      rcases lt_or_eq_of_le hσ.2 with h | h
      · exact h
      · exfalso
        have : rad a b (γ τ) ≤ r₁ / 2 := hτ.2
        rw [← h] at this
        simp only at hσeq
        linarith
    have hin : ∀ s ∈ Set.Icc 0 σ, γ s ∈ U a b := fun s hs => by
      change 0 < rad a b (γ s)
      have := hbefore s hs.1 (lt_of_le_of_lt hs.2 hστ)
      linarith
    have hσt : σ ∈ Set.Icc 0 t := ⟨hσ.1, by linarith [hτt.2]⟩
    have hψσ := hcons σ hσt hin
    have hlow := rad_lower ha hb (hin σ ⟨hσ.1, le_rfl⟩) (hψσ.le.trans hψ0)
    simp only at hσeq
    linarith
  have hin : ∀ s ∈ Set.Icc 0 t, γ s ∈ U a b := fun s hs => by
    change 0 < rad a b (γ s)
    linarith [hstay s hs]
  have hψt := hcons t ⟨ht, le_rfl⟩ hin
  exact ⟨hin t ⟨ht, le_rfl⟩, hψt, rad_lower ha hb (hin t ⟨ht, le_rfl⟩) (hψt.le.trans hψ0)⟩

/-- **Closed field lines.** Under the hypotheses of `fieldLine_confined`, every field line is
the explicit oscillator solution for all `t ≥ 0` and closes after parameter `2π`:
`γ (t + 2π) = γ t` (paper §2.2, §2.4: closed lines, consistent with `ι = 2`). -/
theorem fieldLine_closed {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hε : |epsAB a b| < 1)
    {δ : ℝ} (hδ : δ < (1 - |epsAB a b|) ^ 2 / 4) {γ : ℝ → Space}
    (hγ : IsForwardFieldLine (field a b) γ) (h0 : γ 0 ∈ U a b) (hψ0 : psi a b (γ 0) ≤ δ)
    {t : ℝ} (ht : 0 ≤ t) :
    γ t = oscSol (γ 0) (field a b (γ 0)) t ∧ γ (t + 2 * Real.pi) = γ t := by
  have hU (T : ℝ) : ∀ s ∈ Set.Icc 0 T, γ s ∈ U a b := fun s hs =>
    (fieldLine_confined ha hb hε hδ hγ h0 hψ0 hs.1).1
  have hd (T : ℝ) : ∀ s ∈ Set.Icc 0 T, HasDerivAt γ (field a b (γ s)) s := fun s hs => hγ s hs.1
  have e1 := fieldLine_explicit ha hb (hd t) (hU t) ⟨ht, le_rfl⟩
  have e2 := fieldLine_explicit ha hb (hd (t + 2 * Real.pi)) (hU _)
    ⟨by positivity, le_rfl⟩
  refine ⟨e1, ?_⟩
  rw [e2, e1, oscSol_periodic]


/-! ## Geometry: toroidal region, symmetries, non-axisymmetry -/

/-- `x B_y - y B_x = a b F` (paper (2.22): `B · ∇φ = abF/(x² + y²)`). -/
theorem toroidal_component {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) {x : Space}
    (hx : x ∈ U a b) : x 0 * field a b x 1 - x 1 * field a b x 0 = a * b * Fr a b x := by
  obtain ⟨hS, -, -⟩ := point_data ha hb hx
  simp [field, N0, N1, sF_eq ha hb]
  field_simp
  unfold Sden
  ring

/-- The toroidal field is positive on `𝒰` (for `a, b > 0`): every field line circulates
in the positive `φ` direction about the `z`-axis. -/
theorem toroidal_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : Space} (hx : x ∈ U a b) :
    0 < x 0 * field a b x 1 - x 1 * field a b x 0 := by
  rw [toroidal_component ha.ne' hb.ne' hx]
  have : 0 < Fr a b x := Real.sqrt_pos.mpr hx
  positivity

/-- `𝒰` avoids the symmetry axis `x = y = 0` (so it is a toroidal region about the `z`-axis). -/
theorem U_off_axis {a b : ℝ} {x : Space} (hx : x ∈ U a b) : x 0 ^ 2 + x 1 ^ 2 ≠ 0 := by
  intro h
  have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  have := sF_pos hx
  simp [sF, h0, h1] at this

/-- `𝒰` is bounded: `0 < s < 2` and `|z| < 1/2`. -/
theorem U_bounded {a b : ℝ} {x : Space} (hx : x ∈ U a b) :
    0 < sF a b x ∧ sF a b x < 2 ∧ 4 * x 2 ^ 2 < 1 := by
  have h : 0 < rad a b x := hx
  unfold rad at h
  refine ⟨sF_pos hx, ?_, ?_⟩ <;> nlinarith [sq_nonneg (x 2), sq_nonneg (1 - sF a b x)]

/-- Rotation by `π` about the `z`-axis. -/
@[expose] def rotPi (x : Space) : Space := toLp 2 ![-x 0, -x 1, x 2]

/-- Stellarator-symmetry involution: rotation by `π` about the `x`-axis. -/
@[expose] def flipX (x : Space) : Space := toLp 2 ![x 0, -x 1, -x 2]

/-- Rotation by `π/2` about the `z`-axis. -/
@[expose] def rotQ (x : Space) : Space := toLp 2 ![-x 1, x 0, x 2]

/-- Two field periods: `B(R_π x) = R_π B(x)` (paper §1). -/
theorem field_rotPi (a b : ℝ) (x : Space) : field a b (rotPi x) = rotPi (field a b x) := by
  have hs : sF a b (rotPi x) = sF a b x := by simp [sF, rotPi]
  have hF : Fr a b (rotPi x) = Fr a b x := by
    rw [Fr, Fr, rad, rad, hs]; simp [rotPi]
  simp only [field, N0, N1, hs, hF]
  apply space_ext <;> simp [rotPi] <;> ring

/-- Stellarator symmetry: `B(S x) = -S B(x)` for `S` the rotation by `π` about the `x`-axis
(paper §1). -/
theorem field_flipX (a b : ℝ) (x : Space) : field a b (flipX x) = -flipX (field a b x) := by
  have hs : sF a b (flipX x) = sF a b x := by simp [sF, flipX]
  have hF : Fr a b (flipX x) = Fr a b x := by
    rw [Fr, Fr, rad, rad, hs]; simp [flipX]
  simp only [field, N0, N1, hs, hF]
  apply space_ext <;> simp [flipX]
  all_goals ring

/-- The points used to exhibit non-axisymmetry lie in `𝒰`. -/
theorem quarter_points_mem {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : b ^ 2 < 2 * a ^ 2) :
    (toLp 2 ![b, 0, 0] : Space) ∈ U a b ∧ (toLp 2 ![0, b, 0] : Space) ∈ U a b := by
  constructor
  · change 0 < rad a b _
    simp only [rad, sF, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, add_zero, Matrix.cons_val,
        mul_zero, sub_zero, sub_pos, sq_lt_one_iff_abs_lt_one]
    have h1 : 0 < b ^ 2 / a ^ 2 := by positivity
    have h2 : b ^ 2 / a ^ 2 < 2 := by rw [div_lt_iff₀ (by positivity)]; linarith
    rw [abs_lt]; constructor <;> linarith
  · change 0 < rad a b _
    simp [rad, sF, hb]

/-- **Non-axisymmetry.** For `a² ≠ b²` the field is not invariant under the quarter turn
about the `z`-axis: `B_z` (which such a rotation preserves) differs at the points
`(b,0,0)` and `(0,b,0)` of `𝒰`. Hence the configuration is not axisymmetric. -/
theorem field_not_axisymmetric {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ^ 2 ≠ b ^ 2) :
    ¬ ∀ x ∈ U a b, field a b (rotQ x) = rotQ (field a b x) := by
  intro h
  by_cases hlt : b ^ 2 < 2 * a ^ 2
  · have hx := (quarter_points_mem ha hb hlt).1
    have := congrArg (fun v : Space => v 2) (h _ hx)
    simp [field, rotQ, sF, hb] at this
    apply hab
    field_simp at this
    linarith
  · have hlt' : a ^ 2 < 2 * b ^ 2 := by
      have : 0 < b ^ 2 := by positivity
      linarith
    have hx : (toLp 2 ![0, a, 0] : Space) ∈ U a b := by
      change 0 < rad a b _
      simp only [rad, sF, Fin.isValue, Matrix.cons_val_zero, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, zero_pow, zero_div, Matrix.cons_val_one, zero_add, Matrix.cons_val,
          mul_zero, sub_zero, sub_pos, sq_lt_one_iff_abs_lt_one]
      have h1 : 0 < a ^ 2 / b ^ 2 := by positivity
      have h2 : a ^ 2 / b ^ 2 < 2 := by rw [div_lt_iff₀ (by positivity)]; linarith
      rw [abs_lt]; constructor <;> linarith
    have := congrArg (fun v : Space => v 2) (h _ hx)
    simp [field, rotQ, sF, ha] at this
    apply hab
    field_simp at this
    linarith


/-! ## The paper's normalization `a = √(1+ε)`, `b = √(1-ε)` and the magnetic axis -/

/-- `a = √(1+ε)` (paper §2.1). -/
@[expose] def aE (ε : ℝ) : ℝ := √(1 + ε)

/-- `b = √(1-ε)` (paper §2.1). -/
@[expose] def bE (ε : ℝ) : ℝ := √(1 - ε)

section Normalized
variable {ε : ℝ}

/-- `a² = 1 + ε`. -/
theorem aE_sq (hε : |ε| < 1) : aE ε ^ 2 = 1 + ε := by
  rw [aE, Real.sq_sqrt]; linarith [neg_abs_le ε]

/-- `b² = 1 - ε`. -/
theorem bE_sq (hε : |ε| < 1) : bE ε ^ 2 = 1 - ε := by
  rw [bE, Real.sq_sqrt]; linarith [le_abs_self ε]

/-- `a > 0`. -/
theorem aE_pos (hε : |ε| < 1) : 0 < aE ε := Real.sqrt_pos.mpr (by linarith [neg_abs_le ε])

/-- `b > 0`. -/
theorem bE_pos (hε : |ε| < 1) : 0 < bE ε := Real.sqrt_pos.mpr (by linarith [le_abs_self ε])

/-- With the paper's normalization the deformation parameter is `ε`. -/
theorem epsAB_eq (hε : |ε| < 1) : epsAB (aE ε) (bE ε) = ε := by
  rw [epsAB, aE_sq hε, bE_sq hε]; ring

/-- `a b = √(1 - ε²)`, the major radius of the axis (paper (2.19)). -/
theorem aE_mul_bE (hε : |ε| < 1) : aE ε * bE ε = √(1 - ε ^ 2) := by
  rw [aE, bE, ← Real.sqrt_mul (by linarith [neg_abs_le ε])]; congr 1; ring

/-- The magnetic axis (paper (2.19)):
`γ(ζ) = (√(1-ε²) cos ζ, √(1-ε²) sin ζ, (ε/2) sin 2ζ)`, written with `√(1-ε²) = a b`. -/
@[expose] def axis (ε ζ : ℝ) : Space :=
  toLp 2 ![aE ε * bE ε * Real.cos ζ, aE ε * bE ε * Real.sin ζ, ε / 2 * Real.sin (2 * ζ)]

/-- Its tangent vector. -/
@[expose] def axisVel (ε ζ : ℝ) : Space :=
  toLp 2 ![-(aE ε * bE ε * Real.sin ζ), aE ε * bE ε * Real.cos ζ, ε * Real.cos (2 * ζ)]

/-- On the axis `s = 1 + ε - 2ε cos²ζ = 1 - ε cos 2ζ`. -/
theorem sF_axis (hε : |ε| < 1) (ζ : ℝ) :
    sF (aE ε) (bE ε) (axis ε ζ) = 1 + ε - 2 * ε * Real.cos ζ ^ 2 := by
  have ha := (aE_pos hε).ne'
  have hb := (bE_pos hε).ne'
  have hs : Real.sin ζ ^ 2 = 1 - Real.cos ζ ^ 2 := by rw [← Real.sin_sq_add_cos_sq ζ]; ring
  simp only [sF, axis, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (aE ε * bE ε * Real.cos ζ) ^ 2 / aE ε ^ 2 = bE ε ^ 2 * Real.cos ζ ^ 2 by
      field_simp,
    show (aE ε * bE ε * Real.sin ζ) ^ 2 / bE ε ^ 2 = aE ε ^ 2 * Real.sin ζ ^ 2 by
      field_simp, aE_sq hε, bE_sq hε, hs]
  ring

/-- On the axis the radicand is `a² b² = 1 - ε²`. -/
theorem rad_axis (hε : |ε| < 1) (ζ : ℝ) :
    rad (aE ε) (bE ε) (axis ε ζ) = (aE ε * bE ε) ^ 2 := by
  have hs : Real.sin ζ ^ 2 = 1 - Real.cos ζ ^ 2 := by rw [← Real.sin_sq_add_cos_sq ζ]; ring
  rw [rad, sF_axis hε, mul_pow, aE_sq hε, bE_sq hε]
  simp [axis, Real.sin_two_mul]
  linear_combination (-4 * ε ^ 2 * Real.cos ζ ^ 2) * hs

/-- The axis lies in `𝒰`. -/
theorem axis_mem (hε : |ε| < 1) (ζ : ℝ) : axis ε ζ ∈ U (aE ε) (bE ε) := by
  change 0 < rad _ _ _
  rw [rad_axis hε]
  have := aE_pos hε
  have := bE_pos hε
  positivity

/-- On the axis `F = a b = √(1 - ε²)`. -/
theorem Fr_axis (hε : |ε| < 1) (ζ : ℝ) : Fr (aE ε) (bE ε) (axis ε ζ) = aE ε * bE ε := by
  rw [Fr, rad_axis hε, Real.sqrt_sq (mul_pos (aE_pos hε) (bE_pos hε)).le]

/-- On the axis the field is the axis tangent. -/
theorem field_axis (hε : |ε| < 1) (ζ : ℝ) : field (aE ε) (bE ε) (axis ε ζ) = axisVel ε ζ := by
  have ha := (aE_pos hε).ne'
  have hb := (bE_pos hε).ne'
  have hS := sF_pos (axis_mem hε ζ)
  rw [sF_axis hε] at hS
  have hs : Real.sin ζ ^ 2 = 1 - Real.cos ζ ^ 2 := by rw [← Real.sin_sq_add_cos_sq ζ]; ring
  have hA := aE_sq hε
  have hB := bE_sq hε
  simp only [field, N0, N1, Fr_axis hε, sF_axis hε]
  apply space_ext
  · simp [axis, axisVel, Real.sin_two_mul]
    field_simp
    linear_combination (-Real.sin ζ) * hA
  · simp [axis, axisVel, Real.sin_two_mul]
    field_simp
    linear_combination (Real.cos ζ) * hB + (2 * ε * Real.cos ζ) * hs
  · simp [axis, axisVel, Real.cos_two_mul]
    ring

/-- Assemble the derivative of a curve from its coordinates. -/
theorem curve_hasDerivAt {f : ℝ → Space} {v : Space} {t : ℝ}
    (h : ∀ k, HasDerivAt (fun s => f s k) (v k) t) : HasDerivAt f v t := by
  have hf : f = fun s => ∑ k, f s k • basis k := by
    funext s; ext j; fin_cases j <;> simp [Fin.sum_univ_three, basis]
  have hv : v = ∑ k, v k • basis k := by
    ext j; fin_cases j <;> simp [Fin.sum_univ_three, basis]
  rw [hf, hv]
  exact HasDerivAt.fun_sum (fun k _ => (h k).smul_const (basis k))

/-- Derivative of the axis curve. -/
theorem axis_hasDerivAt (ζ : ℝ) : HasDerivAt (axis ε) (axisVel ε ζ) ζ := by
  apply curve_hasDerivAt
  intro k
  fin_cases k
  · simpa [axis, axisVel] using (Real.hasDerivAt_cos ζ).const_mul (aE ε * bE ε)
  · simpa [axis, axisVel] using (Real.hasDerivAt_sin ζ).const_mul (aE ε * bE ε)
  · have := (((hasDerivAt_id ζ).const_mul 2).sin).const_mul (ε / 2)
    refine (by simpa [axis] using this : HasDerivAt (fun s => axis ε s 2) _ ζ).congr_deriv ?_
    simp [axisVel]; ring

/-- **The magnetic axis is a field line**, for every parameter value (paper (2.19)). -/
theorem axis_fieldLine (hε : |ε| < 1) (ζ : ℝ) :
    HasDerivAt (axis ε) (field (aE ε) (bE ε) (axis ε ζ)) ζ := by
  rw [field_axis hε]; exact axis_hasDerivAt ζ

/-- The axis is a forward field line in the sense of `IsForwardFieldLine`. -/
theorem axis_isForwardFieldLine (hε : |ε| < 1) :
    IsForwardFieldLine (field (aE ε) (bE ε)) (axis ε) := fun ζ _ => axis_fieldLine hε ζ

/-- `ψ = 0` on the magnetic axis (paper, below (2.4) and (2.15)). -/
theorem psi_axis (hε : |ε| < 1) (ζ : ℝ) : psi (aE ε) (bE ε) (axis ε ζ) = 0 := by
  have hs : Real.sin ζ ^ 2 = 1 - Real.cos ζ ^ 2 := by rw [← Real.sin_sq_add_cos_sq ζ]; ring
  rw [psi, H, field_axis hε, epsAB_eq hε, aE_sq hε, bE_sq hε, Qf,
    EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_three, axis, axisVel, Real.sin_two_mul, Real.cos_two_mul, mul_pow,
    aE_sq hε, bE_sq hε]
  linear_combination (2 * ε ^ 2 * Real.cos ζ ^ 2 - ε ^ 2 + 1) * hs

/-- The axis closes after one period. -/
theorem axis_periodic (ζ : ℝ) : axis ε (ζ + 2 * Real.pi) = axis ε ζ := by
  have h2 : 2 * (ζ + 2 * Real.pi) = 2 * ζ + 2 * Real.pi + 2 * Real.pi := by ring
  simp only [axis, Real.cos_add_two_pi, Real.sin_add_two_pi, h2]

/-- **The axis is non-planar** for `ε ≠ 0` (paper, below (2.19)): no plane contains it. -/
theorem axis_nonplanar (hε : |ε| < 1) (h0 : ε ≠ 0) :
    ¬ ∃ n : Space, n ≠ 0 ∧ ∃ d : ℝ, ∀ ζ, ⟪n, axis ε ζ⟫ = d := by
  rintro ⟨n, hn, d, hd⟩
  have hab : aE ε * bE ε ≠ 0 := (mul_pos (aE_pos hε) (bE_pos hε)).ne'
  have e0 := hd 0
  have e1 := hd Real.pi
  have e2 := hd (Real.pi / 2)
  have e3 := hd (Real.pi / 4)
  simp only [inner_coords, axis] at e0 e1 e2 e3
  have h5 : 2 * (Real.pi / 2) = Real.pi := by ring
  simp only [Fin.isValue, Real.cos_zero, mul_one, Real.sin_zero, mul_zero, Matrix.cons_val_zero,
      Matrix.cons_val_one, add_zero, Matrix.cons_val, Real.cos_pi, mul_neg, Real.sin_pi,
      Real.sin_two_pi] at e0 e1
  simp only [Fin.isValue, Real.cos_pi_div_two, mul_zero, Real.sin_pi_div_two, mul_one, h5,
      Real.sin_pi, Matrix.cons_val_zero, Matrix.cons_val_one, zero_add, Matrix.cons_val,
      add_zero] at e2
  have h4 : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
  simp only [Fin.isValue, Real.cos_pi_div_four, Real.sin_pi_div_four, h4, Real.sin_pi_div_two,
      mul_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at e3
  have hn0 : n 0 = 0 := by
    have : n 0 * (aE ε * bE ε) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hab
  have hd0 : d = 0 := by rw [← e0, hn0]; ring
  have hn1 : n 1 = 0 := by
    have : n 1 * (aE ε * bE ε) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hab
  have hn2 : n 2 = 0 := by
    rw [hn0, hn1, hd0] at e3
    have : n 2 * (ε / 2) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right (by positivity)
  exact hn ((space_eq_zero_iff n).mpr ⟨hn0, hn1, hn2⟩)

end Normalized


/-! ## Pressure profile -/

/-- With `p_a = 2δ` (pressure vanishing on `ψ = δ`, paper (2.29)) the pressure is positive
strictly inside the surface `ψ = δ`. -/
theorem pressure_pos {μ₀ δ a b : ℝ} (hμ : 0 < μ₀) {x : Space} (hψ : psi a b x < δ) :
    0 < pressure μ₀ (2 * δ) a b x := by
  unfold pressure; apply div_pos _ hμ; linarith

/-- The pressure vanishes on the boundary surface `ψ = δ`. -/
theorem pressure_boundary {μ₀ δ a b : ℝ} {x : Space} (hψ : psi a b x = δ) :
    pressure μ₀ (2 * δ) a b x = 0 := by
  unfold pressure; rw [hψ]; ring

/-- On the magnetic axis the pressure takes its maximum value `2δ/μ₀`. -/
theorem pressure_axis {μ₀ δ ε : ℝ} (hε : |ε| < 1) (ζ : ℝ) :
    pressure μ₀ (2 * δ) (aE ε) (bE ε) (axis ε ζ) = 2 * δ / μ₀ := by
  unfold pressure; rw [psi_axis hε]; ring

/-- The pressure is at most its axis value on `𝒰` (`ψ ≥ 0`). -/
theorem pressure_le_axis {μ₀ δ a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hμ : 0 < μ₀) {x : Space}
    (hx : x ∈ U a b) : pressure μ₀ (2 * δ) a b x ≤ 2 * δ / μ₀ := by
  unfold pressure
  have := psi_nonneg ha hb hx
  gcongr
  linarith

/-! ## Sanity: the axisymmetric limit `ε = 0` -/

/-- For `a = b = 1` (`ε = 0`) the field is invariant under the quarter turn — consistent with
the axisymmetric Solov'ev limit (2.6); non-axisymmetry needs `ε ≠ 0`. -/
theorem field_axisymmetric_limit (x : Space) : field 1 1 (rotQ x) = rotQ (field 1 1 x) := by
  have hs : sF 1 1 (rotQ x) = sF 1 1 x := by simp [sF, rotQ]; ring
  have hF : Fr 1 1 (rotQ x) = Fr 1 1 x := by
    rw [Fr, Fr, rad, rad, hs]; simp [rotQ]
  simp only [field, N0, N1, hs, hF]
  apply space_ext <;> simp [rotQ]
  all_goals ring

/-- Sanity: in the paper's normalization `ε = 0` gives `a = b = 1`. -/
theorem aE_bE_zero : aE 0 = 1 ∧ bE 0 = 1 := by simp [aE, bE]

/-! ## SI scaling and a realistic instance -/

/-- SI field `B(x) = B₀ B̂(x / L)` (field scale `B₀` in tesla, length scale `L` in metres). -/
@[expose] def fieldSI (B₀ L a b : ℝ) (x : Space) : Space := B₀ • field a b (L⁻¹ • x)

/-- SI Ampère current `J = (∇ × B)/μ₀` from the actual derivative. -/
@[expose] def currentSI (μ₀ B₀ L a b : ℝ) (x : Space) : Space :=
  μ₀⁻¹ • curl (fderiv ℝ (fieldSI B₀ L a b) x)

/-- SI pressure `p(x) = (B₀²/μ₀) (p̂_a - 2ψ(x/L))`. -/
@[expose] def pressureSI (μ₀ B₀ L pa a b : ℝ) (x : Space) : ℝ :=
  B₀ ^ 2 / μ₀ * (pa - 2 * psi a b (L⁻¹ • x))

/-- SI pressure gradient `-(B₀²/(μ₀ L)) ∇̂H(x/L)`. -/
@[expose] def pressureGradSI (μ₀ B₀ L a b : ℝ) (x : Space) : Space :=
  (-(B₀ ^ 2 / μ₀ * L⁻¹)) • gradH a b (L⁻¹ • x)

/-- Actual derivative of the SI field (chain rule through `x ↦ x/L`). -/
theorem fieldSI_hasFDerivAt (B₀ L a b : ℝ) {x : Space} (hx : L⁻¹ • x ∈ U a b) :
    HasFDerivAt (fieldSI B₀ L a b) ((B₀ * L⁻¹) • fieldDeriv a b (L⁻¹ • x)) x := by
  have hlin : HasFDerivAt (fun y : Space => L⁻¹ • y) (L⁻¹ • ContinuousLinearMap.id ℝ Space) x :=
    (L⁻¹ • ContinuousLinearMap.id ℝ Space).hasFDerivAt
  have h := ((field_hasFDerivAt a b _ hx).comp x hlin).const_smul B₀
  refine h.congr_fderiv ?_
  ext v
  simp [smul_smul]

/-- The SI pressure gradient is the actual derivative of the SI pressure. -/
theorem pressureSI_hasFDerivAt (μ₀ B₀ L pa a b : ℝ) {x : Space} (hx : L⁻¹ • x ∈ U a b) :
    HasFDerivAt (pressureSI μ₀ B₀ L pa a b) (innerSL ℝ (pressureGradSI μ₀ B₀ L a b x)) x := by
  have hlin : HasFDerivAt (fun y : Space => L⁻¹ • y) (L⁻¹ • ContinuousLinearMap.id ℝ Space) x :=
    (L⁻¹ • ContinuousLinearMap.id ℝ Space).hasFDerivAt
  have h := ((((psi_hasFDerivAt a b hx).comp x hlin).const_mul 2).const_sub pa).const_mul
    (B₀ ^ 2 / μ₀)
  refine hfd h (fun y => rfl) ?_
  ext v
  simp [pressureGradSI]
  ring

open Matrix in
/-- **SI force balance** `J × B = ∇p` (domain-kernel law) for the scaled equilibrium, with the
actual Ampère current and actual pressure gradient, at every `x` with `x/L ∈ 𝒰`. -/
theorem force_balance_SI {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (μ₀ B₀ L : ℝ) {x : Space}
    (hx : L⁻¹ • x ∈ U a b) :
    ForceBalance (ofLp (fieldSI B₀ L a b x)) (ofLp (currentSI μ₀ B₀ L a b x))
      (ofLp (pressureGradSI μ₀ B₀ L a b x)) := by
  refine ⟨?_⟩
  have e : ofLp (currentSI μ₀ B₀ L a b x) ⨯₃ ofLp (fieldSI B₀ L a b x) =
      ofLp (cross (currentSI μ₀ B₀ L a b x) (fieldSI B₀ L a b x)) := by simp [cross]
  have hc : currentSI μ₀ B₀ L a b x =
      (μ₀⁻¹ * (B₀ * L⁻¹)) • curl (fieldDeriv a b (L⁻¹ • x)) := by
    rw [currentSI, (fieldSI_hasFDerivAt B₀ L a b hx).fderiv, curl, map_smul, ← curl, smul_smul]
  have hcr (k m : ℝ) (u w : Space) : cross (k • u) (m • w) = (k * m) • cross u w := by
    rw [← crossBilinear_apply, map_smul, map_smul, _root_.smul_apply, crossBilinear_apply,
      smul_smul, mul_comm]
  rw [e, hc, fieldSI, hcr, curl_cross_eq, fieldDeriv_field ha hb hx, pressureGradSI, gradH]
  congr 1
  rw [show (-(B₀ ^ 2 / μ₀ * L⁻¹)) = -(μ₀⁻¹ * (B₀ * L⁻¹) * B₀) by ring]
  module

/-- `|B̂|²` on the axis: `1 - ε² + ε² cos² 2ζ`. -/
theorem axis_field_normSq {ε : ℝ} (hε : |ε| < 1) (ζ : ℝ) :
    ‖field (aE ε) (bE ε) (axis ε ζ)‖ ^ 2 = 1 - ε ^ 2 + ε ^ 2 * Real.cos (2 * ζ) ^ 2 := by
  rw [field_axis hε, EuclideanSpace.norm_sq_eq]
  have hs := Real.sin_sq_add_cos_sq ζ
  simp [Fin.sum_univ_three, axisVel, mul_pow, aE_sq hε, bE_sq hε]
  linear_combination (1 - ε ^ 2) * hs

/-- **Realistic SI instance** (`ε = 1/2`, `δ = 1/64`, the first panel of the paper's
figure 1). With field scale `B₀ = 5 T`, any length scale `L > 0` and `p_a = 2δ`:
on the magnetic axis `x = L γ(ζ)` the field strength lies between `(5√3/2) T ≈ 4.33 T` and
`5 T` (`|B|² ∈ [75/4, 25]` T²) and the local beta `2μ₀p/|B|²` lies in `[1/16, 1/12]`
(6.25 %–8.33 %). The paper's volume-averaged value (2.29) is `β_V = 2/57 ≈ 3.5 %`
(not formalized here). Force balance holds by `force_balance_SI`. -/
theorem realistic_instance (μ₀ L : ℝ) (hμ : 0 < μ₀) (hL : 0 < L) (ζ : ℝ) :
    75 / 4 ≤ ‖fieldSI 5 L (aE (1 / 2)) (bE (1 / 2)) (L • axis (1 / 2) ζ)‖ ^ 2 ∧
    ‖fieldSI 5 L (aE (1 / 2)) (bE (1 / 2)) (L • axis (1 / 2) ζ)‖ ^ 2 ≤ 25 ∧
    1 / 16 ≤ 2 * μ₀ * pressureSI μ₀ 5 L (2 * (1 / 64)) (aE (1 / 2)) (bE (1 / 2))
        (L • axis (1 / 2) ζ) /
      ‖fieldSI 5 L (aE (1 / 2)) (bE (1 / 2)) (L • axis (1 / 2) ζ)‖ ^ 2 ∧
    2 * μ₀ * pressureSI μ₀ 5 L (2 * (1 / 64)) (aE (1 / 2)) (bE (1 / 2))
        (L • axis (1 / 2) ζ) /
      ‖fieldSI 5 L (aE (1 / 2)) (bE (1 / 2)) (L • axis (1 / 2) ζ)‖ ^ 2 ≤ 1 / 12 := by
  have hε : |(1 / 2 : ℝ)| < 1 := by norm_num [abs_of_pos]
  have hLx : L⁻¹ • (L • axis (1 / 2) ζ) = axis (1 / 2) ζ := by
    rw [smul_smul, inv_mul_cancel₀ hL.ne', one_smul]
  have hB : ‖fieldSI 5 L (aE (1 / 2)) (bE (1 / 2)) (L • axis (1 / 2) ζ)‖ ^ 2 =
      25 * (3 / 4 + Real.cos (2 * ζ) ^ 2 / 4) := by
    rw [fieldSI, hLx, norm_smul, mul_pow, axis_field_normSq hε]
    norm_num
    ring
  have hp : pressureSI μ₀ 5 L (2 * (1 / 64)) (aE (1 / 2)) (bE (1 / 2)) (L • axis (1 / 2) ζ) =
      25 / μ₀ * (1 / 32) := by
    rw [pressureSI, hLx, psi_axis hε]; norm_num
  have hc0 := sq_nonneg (Real.cos (2 * ζ))
  have hc1 : Real.cos (2 * ζ) ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one]; exact Real.abs_cos_le_one _
  rw [hB, hp]
  have hpos : 0 < 25 * (3 / 4 + Real.cos (2 * ζ) ^ 2 / 4) := by positivity
  refine ⟨by nlinarith, by nlinarith, ?_, ?_⟩
  · rw [le_div_iff₀ hpos]; field_simp; nlinarith
  · rw [div_le_iff₀ hpos]; field_simp; nlinarith


/-! ## Summary for the paper's family 1 -/

/-- **Landreman family 1** (arXiv:2609.26742 v2, §2; unrefereed preprint), for `0 < ε < 1`
and `δ < (1-ε)²/4`. With `a = √(1+ε)`, `b = √(1-ε)`:
1. `∇ · B = 0` and the kernel law `J × B = ∇p` (actual Ampère current, any `μ₀`) on `𝒰`;
2. `B · ∇ψ = 0` and `J · ∇ψ = 0` on `𝒰`;
3. the field is not axisymmetric;
4. the magnetic axis is a non-planar field line with `ψ = 0`;
5. every forward field line starting in `𝒰` with `ψ ≤ δ` stays in `𝒰`, keeps `ψ`, and closes
   after parameter `2π` (closed field lines, consistent with `ι = 2`). -/
theorem family1 {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hδ : δ < (1 - ε) ^ 2 / 4) :
    (∀ x ∈ U (aE ε) (bE ε), divergence (fderiv ℝ (field (aE ε) (bE ε)) x) = 0) ∧
    (∀ μ₀, ∀ x ∈ U (aE ε) (bE ε), ForceBalance (ofLp (field (aE ε) (bE ε) x))
      (ofLp (current μ₀ (aE ε) (bE ε) x)) (ofLp (pressureGrad μ₀ (aE ε) (bE ε) x))) ∧
    (∀ μ₀, ∀ x ∈ U (aE ε) (bE ε), ⟪field (aE ε) (bE ε) x, gradH (aE ε) (bE ε) x⟫ = 0 ∧
      ⟪current μ₀ (aE ε) (bE ε) x, gradH (aE ε) (bE ε) x⟫ = 0) ∧
    (¬ ∀ x ∈ U (aE ε) (bE ε), field (aE ε) (bE ε) (rotQ x) = rotQ (field (aE ε) (bE ε) x)) ∧
    (IsForwardFieldLine (field (aE ε) (bE ε)) (axis ε) ∧
      (∀ ζ, psi (aE ε) (bE ε) (axis ε ζ) = 0) ∧
      ¬ ∃ n : Space, n ≠ 0 ∧ ∃ d : ℝ, ∀ ζ, ⟪n, axis ε ζ⟫ = d) ∧
    (∀ γ : ℝ → Space, IsForwardFieldLine (field (aE ε) (bE ε)) γ → γ 0 ∈ U (aE ε) (bE ε) →
      psi (aE ε) (bE ε) (γ 0) ≤ δ → ∀ t, 0 ≤ t →
        γ t ∈ U (aE ε) (bE ε) ∧ psi (aE ε) (bE ε) (γ t) = psi (aE ε) (bE ε) (γ 0) ∧
        γ (t + 2 * Real.pi) = γ t) := by
  have hε : |ε| < 1 := by rw [abs_of_pos hε0]; exact hε1
  have ha := (aE_pos hε).ne'
  have hb := (bE_pos hε).ne'
  have hE : epsAB (aE ε) (bE ε) = ε := epsAB_eq hε
  have hεE : |epsAB (aE ε) (bE ε)| < 1 := by rwa [hE]
  have hδE : δ < (1 - |epsAB (aE ε) (bE ε)|) ^ 2 / 4 := by rwa [hE, abs_of_pos hε0]
  refine ⟨fun x hx => field_divergence_free ha hb hx, fun μ₀ x hx => force_balance ha hb μ₀ hx,
    fun μ₀ x hx => ⟨field_tangent_psi ha hb hx, current_tangent_psi ha hb μ₀ hx⟩, ?_,
    ⟨axis_isForwardFieldLine hε, psi_axis hε, axis_nonplanar hε hε0.ne'⟩, ?_⟩
  · refine field_not_axisymmetric ha hb ?_
    rw [aE_sq hε, bE_sq hε]; intro h; linarith
  · intro γ hγ h0 hψ t ht
    obtain ⟨h1, h2, -⟩ := fieldLine_confined ha hb hεE hδE hγ h0 hψ ht
    exact ⟨h1, h2, (fieldLine_closed ha hb hεE hδE hγ h0 hψ ht).2⟩

end PlasmaLean.Design.LandremanEquilibrium
