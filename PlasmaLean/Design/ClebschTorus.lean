/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FirstIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# A nonaxisymmetric analytic field with an all-time toroidal field-line barrier

Synthetic, dimensionless example (lengths in units of the major radius). Let

  ψ(x) = (x₀² + x₁² − 1)² + 4 (x₂ − x₀x₁/2)²,

a sheared torus function: its sublevel set {ψ ≤ 1/4} lies in the annular shell
1/2 ≤ x₀² + x₁² ≤ 3/2, |x₂| ≤ 5/8, avoids the vertical axis, and is NOT invariant under
rotation about that axis (`torusRegion_not_axisymmetric`). The field is

  B = B_T + (1/8) ∇ψ × ∇x₂,   B_T(x) = (−x₁, x₀, (x₀² − x₁²)/2),

where B_T is the shear-pushforward of a rigid toroidal rotation and the second term is a
Clebsch field. Both are tangent to the level sets of ψ, so every supplied forward field
line starting in {ψ ≤ 1/4} stays there, within distance 2 of the origin and away from
the axis, for all nonnegative parameter values (`fieldLine_stays_in_torus`). The field
does not vanish on the region and is itself nonaxisymmetric (`field_not_axisymmetric`).

Scope and limitations, recorded honestly:
* B is an analytic model field. It is NOT shown to be produced by any coil set, to be
  curl-free (it is not: B_T carries a uniform vertical curl), or to satisfy any MHD
  equilibrium law. By hand both terms are divergence-free; that is not formalized here.
* The barrier is an exact field-line statement only. Guiding-centre or full-orbit
  particle confinement, rotational transform, and stability are separate obligations.
* We do not prove that {ψ ≤ 1/4} is topologically a solid torus; only the containment
  bounds stated below are checked.
-/
public section
noncomputable section
namespace PlasmaLean.Design.ClebschTorus
open Fields WithLp

/-- The sheared torus function ψ. -/
@[expose] def psi (x : Space) : ℝ :=
  (x 0 ^ 2 + x 1 ^ 2 - 1) ^ 2 + 4 * (x 2 - x 0 * x 1 / 2) ^ 2

/-- The explicit gradient of ψ. -/
@[expose] def psiGrad (x : Space) : Space :=
  toLp 2 ![4 * x 0 * (x 0 ^ 2 + x 1 ^ 2 - 1) - 4 * x 1 * (x 2 - x 0 * x 1 / 2),
    4 * x 1 * (x 0 ^ 2 + x 1 ^ 2 - 1) - 4 * x 0 * (x 2 - x 0 * x 1 / 2),
    8 * (x 2 - x 0 * x 1 / 2)]

/-- The vertical coordinate, second Clebsch potential. -/
@[expose] def height (x : Space) : ℝ := x 2

/-- Shear pushforward of the rigid toroidal rotation; tangent to the level sets of ψ. -/
@[expose] def toroidalField (x : Space) : Space :=
  toLp 2 ![-x 1, x 0, (x 0 ^ 2 - x 1 ^ 2) / 2]

/-- The example field: toroidal part plus a small Clebsch field ∇ψ × ∇x₂. -/
@[expose] def field (x : Space) : Space :=
  toroidalField x + (1 / 8 : ℝ) • clebschField psi height x

/-- Rotation by a quarter turn about the vertical axis. -/
@[expose] def rot90 (x : Space) : Space := toLp 2 ![-x 1, x 0, x 2]

/-- Coordinate functions are continuous linear, with themselves as derivative. -/
theorem coord_hasFDerivAt (i : Fin 3) (x : Space) :
    HasFDerivAt (fun y : Space => y i) (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i) x :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt

/-- The gradient formula for ψ, proved as an actual Fréchet derivative. -/
theorem psi_hasGradientAt (x : Space) : HasGradientAt psi (psiGrad x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h0 := coord_hasFDerivAt 0 x
  have h1 := coord_hasFDerivAt 1 x
  have h2 := coord_hasFDerivAt 2 x
  have h := (((h0.pow 2).add (h1.pow 2)).sub_const 1).pow 2 |>.add
    (((h2.sub ((h0.mul h1).const_mul (1 / 2))).pow 2).const_mul 4)
  convert h using 1
  · funext y; simp only [psi, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]; ring
  · ext v
    simp [psiGrad, EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_three, dotProduct]
    ring

/-- The Mathlib gradient of ψ is the explicit formula. -/
theorem psi_gradient (x : Space) : gradient psi x = psiGrad x :=
  (psi_hasGradientAt x).gradient

/-- ψ is differentiable everywhere. -/
theorem psi_differentiable : Differentiable ℝ psi :=
  fun x => (psi_hasGradientAt x).differentiableAt

/-- The gradient of the height is the vertical unit vector. -/
theorem height_gradient (x : Space) : gradient height x = toLp 2 ![0, 0, 1] := by
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  have h : HasFDerivAt height (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 2) x :=
    coord_hasFDerivAt 2 x
  refine h.congr_fderiv ?_
  ext v
  simp [EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_three, dotProduct]

/-- Explicit components of the example field. -/
theorem field_apply (x : Space) :
    field x = toLp 2 ![-x 1 + (psiGrad x 1) / 8, x 0 - (psiGrad x 0) / 8,
      (x 0 ^ 2 - x 1 ^ 2) / 2] := by
  ext i
  fin_cases i <;>
    simp [field, toroidalField, clebschField, psi_gradient, height_gradient, cross,
      crossProduct, psiGrad] <;> ring

/-- B_T is tangent to the level sets of ψ. -/
theorem toroidal_firstIntegral : FirstIntegralOn toroidalField psi Set.univ := by
  intro x _
  refine ⟨psi_differentiable x, ?_⟩
  rw [(psi_hasGradientAt x).fderiv_apply]
  simp [psiGrad, toroidalField, EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_three,
    dotProduct]
  ring

/-- ψ is an exact global first integral of the example field. -/
theorem field_firstIntegral : FirstIntegralOn field psi Set.univ :=
  toroidal_firstIntegral.add
    ((clebsch_firstIntegral_left psi height _ (fun x _ => psi_differentiable x)).smul
      (fun _ => 1 / 8))

/-- The sublevel region {ψ ≤ 1/4} is an all-time forward field-line barrier. -/
theorem field_confined : FieldLineConfined field {x | psi x ≤ 1 / 4} :=
  sublevel_confined field_firstIntegral _

/-- Containment bounds for the region {ψ ≤ 1/4}: an annular shell avoiding the axis. -/
theorem torusRegion_bounds {x : Space} (hx : psi x ≤ 1 / 4) :
    1 / 2 ≤ x 0 ^ 2 + x 1 ^ 2 ∧ x 0 ^ 2 + x 1 ^ 2 ≤ 3 / 2 ∧ |x 2| ≤ 5 / 8 ∧
      |x 0 ^ 2 + x 1 ^ 2 - 1| ≤ 1 / 2 ∧ |x 2 - x 0 * x 1 / 2| ≤ 1 / 4 := by
  unfold psi at hx
  set s := x 0 ^ 2 + x 1 ^ 2 - 1
  set w := x 2 - x 0 * x 1 / 2
  have hs2 : s ^ 2 ≤ (1 / 2) ^ 2 := by nlinarith [sq_nonneg w]
  have hw2 : w ^ 2 ≤ (1 / 4) ^ 2 := by nlinarith [sq_nonneg s]
  have hs := abs_le_of_sq_le_sq' hs2 (by norm_num)
  have hw := abs_le_of_sq_le_sq' hw2 (by norm_num)
  have hsa : |s| ≤ 1 / 2 := abs_le.mpr hs
  have hwa : |w| ≤ 1 / 4 := abs_le.mpr hw
  have hm : |x 0 * x 1| ≤ 3 / 4 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1)]
  have hz : x 2 = w + x 0 * x 1 / 2 := by simp [w]
  refine ⟨by linarith [hs.1], by linarith [hs.2], ?_, hsa, hwa⟩
  rw [hz, abs_le]
  constructor <;> linarith [(abs_le.mp hm).1, (abs_le.mp hm).2, hw.1, hw.2]

/-- The barrier region lies in the closed ball of radius 2. -/
theorem torusRegion_subset_ball : {x | psi x ≤ 1 / 4} ⊆ Metric.closedBall 0 2 := by
  intro x hx
  obtain ⟨-, h2, hz, -, -⟩ := torusRegion_bounds hx
  have hz2 : x 2 ^ 2 ≤ (5 / 8) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hz 2
  rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  simp only [Real.norm_eq_abs, sq_abs, Fin.sum_univ_three]
  nlinarith

/-- The region is nonempty: the circle point (1,0,0) has ψ = 0. -/
theorem torusRegion_nonempty : psi (toLp 2 ![1, 0, 0]) ≤ 1 / 4 := by
  norm_num [psi]

/-- Elementary inequality behind nonvanishing of the field on the region. -/
theorem key_positive {r a m s w : ℝ} (hr : 1 / 2 ≤ r) (hm : |m| ≤ r / 2)
    (hs : |s| ≤ 1 / 2) (hw : |w| ≤ 1 / 4) : 0 < r + a ^ 2 / 4 - r * s / 2 + m * w := by
  have h1 : |r * s| ≤ r / 2 := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ r)]
    nlinarith [abs_nonneg s]
  have h2 : |m * w| ≤ r / 8 := by
    rw [abs_mul]
    nlinarith [abs_nonneg m, abs_nonneg w]
  nlinarith [neg_abs_le (r * s), le_abs_self (r * s), neg_abs_le (m * w), sq_nonneg a]

/-- On the barrier region, the field has positive projection on B_T, hence never
vanishes. -/
theorem field_inner_toroidal_pos {x : Space} (hx : psi x ≤ 1 / 4) :
    0 < inner ℝ (field x) (toroidalField x) := by
  obtain ⟨h1, -, -, hs, hw⟩ := torusRegion_bounds hx
  have hm : |x 0 * x 1| ≤ (x 0 ^ 2 + x 1 ^ 2) / 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1)]
  have hk := key_positive (a := x 0 ^ 2 - x 1 ^ 2) h1 hm hs hw
  rw [field_apply]
  simp [toroidalField, psiGrad, EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_three,
    dotProduct]
  nlinarith [hk]

/-- The field is nonvanishing on the barrier region. -/
theorem field_ne_zero {x : Space} (hx : psi x ≤ 1 / 4) : field x ≠ 0 := by
  intro h
  have := field_inner_toroidal_pos hx
  rw [h, inner_zero_left] at this
  exact lt_irrefl 0 this

/-- Main example theorem: every supplied forward field line starting in {ψ ≤ 1/4}
remains, for all nonnegative parameter values, in that region, inside the ball of
radius 2, and at cylindrical radius² at least 1/2 from the vertical axis. -/
theorem fieldLine_stays_in_torus {γ : ℝ → Space} (hγ : IsForwardFieldLine field γ)
    (h0 : psi (γ 0) ≤ 1 / 4) {t : ℝ} (ht : 0 ≤ t) :
    psi (γ t) ≤ 1 / 4 ∧ ‖γ t‖ ≤ 2 ∧ 1 / 2 ≤ γ t 0 ^ 2 + γ t 1 ^ 2 := by
  have hin : psi (γ t) ≤ 1 / 4 := field_confined γ hγ h0 t ht
  exact ⟨hin, fieldLine_bounded field_firstIntegral torusRegion_subset_ball hγ h0 ht,
    (torusRegion_bounds hin).1⟩

/-- The barrier region is not axisymmetric: a quarter turn maps one of its points
outside it. -/
theorem torusRegion_not_axisymmetric :
    psi (toLp 2 ![7 / 10, 7 / 10, 49 / 200]) ≤ 1 / 4 ∧
      1 / 4 < psi (rot90 (toLp 2 ![7 / 10, 7 / 10, 49 / 200])) := by
  constructor <;> norm_num [psi, rot90]

/-- The field is not equivariant under the quarter turn, so it is nonaxisymmetric. -/
theorem field_not_axisymmetric :
    field (rot90 (toLp 2 ![1, 0, 0])) ≠ rot90 (field (toLp 2 ![1, 0, 0])) := by
  intro h
  have h2 := congrArg (fun v : Space => v 2) h
  simp [field_apply, rot90, psiGrad] at h2
  norm_num at h2

end PlasmaLean.Design.ClebschTorus
