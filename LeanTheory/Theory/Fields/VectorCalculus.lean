/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Vector calculus on Euclidean three-space

General vector-calculus vocabulary shared by `Theory/Fields` and `Theory/KAM`:

* `Space = EuclideanSpace ℝ (Fin 3)`, the cross product `cross`, `norm_cross_le`,
  `continuous_cross`, `cross_coords`, `space_ext`;
* the coordinate basis `basis`, `divergence` and `curl` of a derivative operator
  `L = DB(x) : Space →L[ℝ] Space`, with coordinate formulas `divergence_apply`, `curl_coords`;
* the curl product rule `curl_fderiv_smul` (`∇ × (f b) = f ∇ × b + ∇f × b`) and
  `fderiv_apply_basis` (`Df(x) eᵢ = (∇f(x))ᵢ`);
* `IsForwardFieldLine B γ` (`γ' = B(γ)` for `t ≥ 0`) and `FirstIntegralOn`;
* complex three-vectors `CVec = Fin 3 → ℂ` with `ofRealV`, `reV`, `imV`, `norm_sq_space`.

Conventions: `(curl L)ₖ = (L e_{k+1})_{k+2} - (L e_{k+2})_{k+1}` (indices in `Fin 3`).

**Sanity.** `divergence_id` (the identity field has divergence 3), `curl_id` (a gradient field
has zero curl), `curl_fderiv_const_smul` and `curl_fderiv_smul_const` (degenerate product rules).
-/

open scoped RealInnerProductSpace
public section
noncomputable section
namespace LeanTheory.Fields
open Matrix WithLp

/-- Euclidean three-space. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The cross product, transported to Euclidean three-space. -/
@[expose] def cross (u v : Space) : Space := toLp 2 (ofLp u ⨯₃ ofLp v)

/-- Euclidean cross-product inequality, reusing Mathlib's angle identity. -/
theorem norm_cross_le (u v : Space) : ‖cross u v‖ ≤ ‖u‖ * ‖v‖ := by
  rw [cross, InnerProductGeometry.norm_ofLp_crossProduct]
  exact mul_le_of_le_one_right (by positivity) (Real.sin_le_one _)

/-- Continuity of the Euclidean cross product, proved from its coordinate formula. -/
theorem continuous_cross : Continuous (fun p : Space × Space => cross p.1 p.2) := by
  unfold cross
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> fun_prop


/-- Coordinate basis vector of physical space. -/
abbrev basis (i : Fin 3) : Space := EuclideanSpace.single i (1 : ℝ)

/-- Divergence as a continuous linear functional on spatial derivative operators. -/
@[expose] def divergenceCLM : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  ∑ i : Fin 3, (EuclideanSpace.proj i).comp (ContinuousLinearMap.apply ℝ Space (basis i))

/-- Divergence of a derivative operator: `∑ᵢ (L eᵢ)ᵢ`. -/
@[expose] def divergence (L : Space →L[ℝ] Space) : ℝ := divergenceCLM L

/-- Explicit coordinate formula for the divergence. -/
theorem divergence_apply (L : Space →L[ℝ] Space) :
    divergence L = L (basis 0) 0 + L (basis 1) 1 + L (basis 2) 2 := by
  simp [divergence, divergenceCLM, Fin.sum_univ_three]

/-- The `k`-th curl component as a continuous linear functional. -/
@[expose] def curlComponent (k : Fin 3) : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  (EuclideanSpace.proj (k + 2)).comp (ContinuousLinearMap.apply ℝ Space (basis (k + 1))) -
    (EuclideanSpace.proj (k + 1)).comp (ContinuousLinearMap.apply ℝ Space (basis (k + 2)))

/-- Curl as a continuous linear map on spatial derivative operators. -/
@[expose] def curlCLM : (Space →L[ℝ] Space) →L[ℝ] Space :=
  ∑ k : Fin 3, (curlComponent k).smulRight (basis k)

/-- Curl of a derivative operator. -/
@[expose] def curl (L : Space →L[ℝ] Space) : Space := curlCLM L

/-- The coordinates of the curl are the curl components. -/
theorem curl_apply (L : Space →L[ℝ] Space) (k : Fin 3) :
    curl L k = curlComponent k L := by
  fin_cases k <;>
    simp [curl, curlCLM, Fin.sum_univ_three]

/-- Explicit coordinate formula for the curl. -/
theorem curl_coords (L : Space →L[ℝ] Space) :
    curl L 0 = L (basis 1) 2 - L (basis 2) 1 ∧
    curl L 1 = L (basis 2) 0 - L (basis 0) 2 ∧
    curl L 2 = L (basis 0) 1 - L (basis 1) 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [curl_apply] <;> simp [curlComponent]

/-- A vector vanishes iff its three coordinates do. -/
theorem space_eq_zero_iff (v : Space) : v = 0 ↔ v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h0, h1, h2⟩
    ext i
    fin_cases i <;> simpa

/-- Extensionality for physical vectors through their three coordinates. -/
theorem space_ext {v w : Space} (h0 : v 0 = w 0) (h1 : v 1 = w 1) (h2 : v 2 = w 2) :
    v = w := by
  rw [← sub_eq_zero, space_eq_zero_iff]
  simp [h0, h1, h2]

/-- Coordinates of the Euclidean cross product. -/
theorem cross_coords (u v : Space) :
    cross u v 0 = u 1 * v 2 - u 2 * v 1 ∧
    cross u v 1 = u 2 * v 0 - u 0 * v 2 ∧
    cross u v 2 = u 0 * v 1 - u 1 * v 0 := by
  simp [cross, cross_apply]

/-! ### Sanity checks of the differential-operator conventions -/

/-- Sanity check: the identity operator (the field `B = x`) has divergence 3. -/
theorem divergence_id : divergence (ContinuousLinearMap.id ℝ Space) = 3 := by
  rw [divergence_apply]
  simp
  norm_num

/-- Sanity check: the identity operator (a gradient field) has zero curl. -/
theorem curl_id : curl (ContinuousLinearMap.id ℝ Space) = 0 := by
  obtain ⟨h0, h1, h2⟩ := curl_coords (ContinuousLinearMap.id ℝ Space)
  rw [space_eq_zero_iff]
  simp [h0, h1, h2]


/-- `curl` is additive. -/
theorem curl_add (L M : Space →L[ℝ] Space) : curl (L + M) = curl L + curl M := by
  simp [curl, map_add]

/-- `curl` is homogeneous. -/
theorem curl_smul (c : ℝ) (L : Space →L[ℝ] Space) : curl (c • L) = c • curl L := by
  simp [curl, map_smul]

/-- The derivative of a scalar field along a coordinate vector is the gradient coordinate. -/
theorem fderiv_apply_basis (f : Space → ℝ) (x : Space) (i : Fin 3) :
    fderiv ℝ f x (basis i) = gradient f x i := by
  rw [← inner_gradient_left, EuclideanSpace.inner_single_right]
  simp

/-- The curl of the rank-one operator `v ↦ (Df(x) v) w` is `∇f(x) × w`. -/
theorem curl_smulRight (f : Space → ℝ) (x : Space) (w : Space) :
    curl ((fderiv ℝ f x).smulRight w) = cross (gradient f x) w := by
  obtain ⟨h0, h1, h2⟩ := curl_coords ((fderiv ℝ f x).smulRight w)
  obtain ⟨c0, c1, c2⟩ := cross_coords (gradient f x) w
  simp only [ContinuousLinearMap.smulRight_apply, fderiv_apply_basis, PiLp.smul_apply,
    smul_eq_mul] at h0 h1 h2
  apply space_ext
  · rw [h0, c0]
  · rw [h1, c1]
  · rw [h2, c2]

/-- **Curl product rule**: `∇ × (f b) = f ∇ × b + ∇f × b` at a point where the scalar field `f` and
the vector field `b` are differentiable. -/
theorem curl_fderiv_smul {f : Space → ℝ} {b : Space → Space} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hb : DifferentiableAt ℝ b x) :
    curl (fderiv ℝ (fun y => f y • b y) x) =
      f x • curl (fderiv ℝ b x) + cross (gradient f x) (b x) := by
  have hd : HasFDerivAt (fun y => f y • b y)
      (f x • fderiv ℝ b x + (fderiv ℝ f x).smulRight (b x)) x :=
    hf.hasFDerivAt.smul hb.hasFDerivAt
  rw [hd.fderiv, curl_add, curl_smul, curl_smulRight]

/-- Sanity check: a constant factor commutes with the curl. -/
theorem curl_fderiv_const_smul (c : ℝ) {b : Space → Space} {x : Space}
    (hb : DifferentiableAt ℝ b x) :
    curl (fderiv ℝ (fun y => c • b y) x) = c • curl (fderiv ℝ b x) := by
  rw [curl_fderiv_smul (f := fun _ => c) (differentiableAt_const c) hb, gradient_fun_const]
  simp [cross]

/-- Sanity check: for a constant vector `w`, `∇ × (f w) = ∇f × w`. -/
theorem curl_fderiv_smul_const {f : Space → ℝ} (w : Space) {x : Space}
    (hf : DifferentiableAt ℝ f x) :
    curl (fderiv ℝ (fun y => f y • w) x) = cross (gradient f x) w := by
  rw [curl_fderiv_smul (b := fun _ => w) hf (differentiableAt_const w), fderiv_const_apply]
  simp [curl]


/-- ψ is an exact first integral of `B` on `U`: differentiable there with `B · ∇ψ = 0`. -/
@[expose] def FirstIntegralOn (B : Space → Space) (ψ : Space → ℝ) (U : Set Space) : Prop :=
  ∀ x ∈ U, DifferentiableAt ℝ ψ x ∧ fderiv ℝ ψ x (B x) = 0

/-- A classical forward field line of `B`: `γ' = B(γ)` at every nonnegative parameter. -/
@[expose] def IsForwardFieldLine (B : Space → Space) (γ : ℝ → Space) : Prop :=
  ∀ t, 0 ≤ t → HasDerivAt γ (B (γ t)) t

/-- Degenerate case: a constant function is a first integral of every field. -/
theorem firstIntegral_const (B : Space → Space) (k : ℝ) (U : Set Space) :
    FirstIntegralOn B (fun _ => k) U :=
  fun _ _ => ⟨differentiableAt_const k, by simp⟩

/-! ### Complex three-vectors -/

/-- Complex three-vectors (with the sup norm of `Fin 3 → ℂ`). -/
abbrev CVec : Type := Fin 3 → ℂ

/-- A real vector viewed as a complex vector. -/
@[expose] def ofRealV (x : Space) : CVec := fun i => ((x i : ℝ) : ℂ)

/-- The real part of a complex vector. -/
@[expose] def reV (y : CVec) : Space := WithLp.toLp 2 (fun i => (y i).re)

/-- The imaginary part of a complex vector. -/
@[expose] def imV (y : CVec) : Space := WithLp.toLp 2 (fun i => (y i).im)

/-- Coordinates of `reV`. -/
@[simp] theorem reV_apply (y : CVec) (i : Fin 3) : reV y i = (y i).re := rfl

/-- Coordinates of `imV`. -/
@[simp] theorem imV_apply (y : CVec) (i : Fin 3) : imV y i = (y i).im := rfl

/-- Coordinates of `ofRealV`. -/
@[simp] theorem ofRealV_apply (x : Space) (i : Fin 3) : ofRealV x i = ((x i : ℝ) : ℂ) := rfl

/-- The squared Euclidean norm of a vector of `Space` in coordinates. -/
theorem norm_sq_space (x : Space) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

/-- Sanity check: the real part of an embedded real vector is the vector itself. -/
theorem reV_ofRealV (x : Space) : reV (ofRealV x) = x := by
  ext i; simp

end LeanTheory.Fields
