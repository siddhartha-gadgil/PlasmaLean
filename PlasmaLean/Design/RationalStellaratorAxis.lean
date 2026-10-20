/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellarator
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Linear stability of the magnetic axis of the rational stellarator

`notes/theory/first-stellarator-rung.md` §1.3. Along the exact axis `R = 1, z = 0` of
`RationalStellarator.field ε`, parametrize field lines by the toroidal angle `φ`:
`dR/dφ = R B_R / B_φ`, `dz/dφ = R B_z / B_φ`. On the axis `B_R = B_z = 0` and
`R B_φ = 1` (`Bcomp_axis`), so the Jacobian of this system at the axis is the transverse
Jacobian `⟪e_a, DB(axis φ) e_b⟫`, `a, b ∈ {e_R(φ), e_z}` (`jacobianAtAxis`); this is proved
in `fieldLineSystem_hasFDerivAt` for the explicit system `fieldLineSystem`:

* `axis_jacobian`: `jacobianAtAxis ε φ = 2ε S(φ)`, `S(φ) = [[cos 2φ, sin 2φ], [sin 2φ, −cos 2φ]]`.

The variational equation `v' = 2ε S(φ) v` is solved explicitly in the frame rotating with
`φ`, where it has the constant matrix `M = [[2ε, 1], [−1, −2ε]]` with `M² = −κ² I`,
`κ = √(1 − 4ε²)`:

* `Φ_solves`: `Φ(φ) = Rot(φ) (cos κφ · I + (sin κφ / κ) M)` solves `Φ' = 2ε S(φ) Φ`,
  `Φ(0) = I` (entrywise derivatives), for `4ε² < 1`;
* `monodromy_trace`: `tr Φ(2π) = 2 cos 2πκ`;
* `axis_elliptic_of`: for `0 < 4ε² < 1` and `κ ≠ 1/2`, `|tr Φ(2π)| < 2` (elliptic);
* `axis_elliptic`: the case `ε = 1/4`, `κ = √3/2`, on-axis transform `ι₀ = 1 − √3/2`
  (`iota0_quarter`).

**Scope: this is LINEAR stability of the axis only** (the monodromy of the linearized
field-line flow has eigenvalues on the unit circle, away from `±1`). It does not prove
nonlinear (KAM) stability or confinement of any field line off the axis; nothing about
nested surfaces is claimed. The interpretation `ι₀ = 1 − κ` as the lab-frame rotation
number is recorded in the definition `iota0` and is not a separate theorem.
-/

open scoped RealInnerProductSpace

public section
noncomputable section
namespace PlasmaLean.Design.RationalStellarator
open PlasmaLean.Fields PlasmaLean.Vacuum WithLp Real Matrix

/-! ## The transverse Jacobian at the axis -/

/-- The cylindrical radial unit vector `e_R(φ) = (cos φ, sin φ, 0)` (equal to `axis φ`). -/
@[expose] def eR (φ : ℝ) : Space := toLp 2 ![cos φ, sin φ, 0]

/-- The vertical unit vector `e_z`. -/
@[expose] def eZ : Space := toLp 2 ![0, 0, 1]

/-- The transverse (poloidal-plane) Jacobian of the actual field at the axis point of
toroidal angle `φ`: entries `⟪e_a, DB(axis φ) e_b⟫` for `a, b ∈ (e_R, e_z)`. Because
`B_R = B_z = 0` and `R B_φ = 1` on the axis, this is the Jacobian at `(R, z) = (1, 0)` of the
`φ`-parametrized field-line system `(R B_R / B_φ, R B_z / B_φ)`. -/
@[expose] def jacobianAtAxis (ε φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![⟪eR φ, fderiv ℝ (field ε) (axis φ) (eR φ)⟫, ⟪eR φ, fderiv ℝ (field ε) (axis φ) eZ⟫;
     ⟪eZ, fderiv ℝ (field ε) (axis φ) (eR φ)⟫, ⟪eZ, fderiv ℝ (field ε) (axis φ) eZ⟫]

/-- The reflection matrix `S(φ)` (reflection through the line at angle `φ`). -/
@[expose] def S (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cos (2 * φ), sin (2 * φ); sin (2 * φ), -cos (2 * φ)]

/-- Action of the field derivative on a vector, via the Jacobian `JB`. -/
theorem fieldDeriv_apply' (ε : ℝ) (x v : Space) (i : Fin 3) :
    fieldDeriv ε x v i = JB ε x i 0 * v 0 + JB ε x i 1 * v 1 + JB ε x i 2 * v 2 := by
  rw [fieldDeriv, coords_apply, lin_apply]

/-- **The axis Jacobian**: the linearization of the field-line flow about the exact axis is
`v' = 2ε S(φ) v`. -/
theorem axis_jacobian (ε φ : ℝ) : jacobianAtAxis ε φ = (2 * ε) • S φ := by
  have hfd := (field_hasFDerivAt (axis φ) ε (axis_mem_domain φ)).fderiv
  have hcs : cos φ ^ 2 + sin φ ^ 2 = 1 := cos_sq_add_sin_sq φ
  have hr : r2 (axis φ) = 1 := by simp [r2, axis, hcs]
  have hw : winv (axis φ) = 1 := by simp [winv, hr]
  have hz : axis φ 2 = 0 := by simp [axis]
  have hA : Aq (axis φ) = 0 := by simp [Aq, hr, hz]
  have hB : Bq (axis φ) = 0 := by simp [Bq, hr, hz]
  have hY : Yp (axis φ) = 0 := by simp [Yp, hz]
  have hHn : Hnum (axis φ) = 0 := by simp [Hnum, hA, hB]
  have hH0 : H0 (axis φ) = 0 := by simp [H0, hr, hA, hB, hY]
  have hH1 : H1 (axis φ) = 0 := by simp [H1, hr, hA, hB, hY]
  have hH2 : H2 (axis φ) = 0 := by simp [H2, hz, hB]
  have h0 : axis φ 0 = cos φ := by simp [axis]
  have h1 : axis φ 1 = sin φ := by simp [axis]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [jacobianAtAxis, S, hfd, PiLp.inner_apply, Fin.sum_univ_three, fieldDeriv_apply',
      JB, JT, JG, wd, cv, cd, Hd, Hdd, H00, H01, H02, H11, H12, H22, hw, hHn, hH0, hH1, hH2,
      h0, h1, hz, eR, eZ, RCLike.inner_apply, conj_trivial, Fin.zero_eta, Fin.mk_one,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.smul_apply,
      Matrix.of_apply, smul_eq_mul, cos_two_mul, sin_two_mul]
  · linear_combination (15 * cos φ ^ 4 * ε / 2 + 3 * cos φ ^ 2 * ε / 2 - 15 * ε * sin φ ^ 4 / 2 -
      3 * ε * sin φ ^ 2 / 2 - 2 * ε) * hcs
  · linear_combination (-3 * cos φ ^ 3 * ε * sin φ - 3 * cos φ * ε * sin φ ^ 3 +
      9 * cos φ * ε * sin φ) * hcs
  · linear_combination (-3 * cos φ ^ 3 * ε * sin φ - 3 * cos φ * ε * sin φ ^ 3 +
      9 * cos φ * ε * sin φ) * hcs
  · linear_combination (2 * ε) * hcs

/-! ## The `φ`-parametrized field-line system and its Jacobian at the axis -/

/-- The toroidal unit vector `e_φ(φ) = (−sin φ, cos φ, 0)`. -/
@[expose] def eφ (φ : ℝ) : Space := toLp 2 ![-sin φ, cos φ, 0]

/-- The point with cylindrical coordinates `(R, φ, z) = (q 0, φ, q 1)` at fixed `φ`:
`R e_R(φ) + z e_z` (linear in `q = (R, z)`). -/
@[expose] def poloidalMap (φ : ℝ) : (Fin 2 → ℝ) →L[ℝ] Space :=
  (ContinuousLinearMap.proj 0).smulRight (eR φ) + (ContinuousLinearMap.proj 1).smulRight eZ

/-- The cylindrical component `⟪u, B⟫` of the field at the point `(R, z) = q` of the
poloidal half-plane at angle `φ` (`u = e_R, e_φ, e_z` gives `B_R, B_φ, B_z`). -/
@[expose] def Bcomp (ε φ : ℝ) (u : Space) (q : Fin 2 → ℝ) : ℝ :=
  ⟪u, field ε (poloidalMap φ q)⟫

/-- **The `φ`-parametrized field-line system** `dR/dφ = R B_R / B_φ`, `dz/dφ = R B_z / B_φ`
at fixed toroidal angle `φ`, as a map `(R, z) ↦ (dR/dφ, dz/dφ)`. -/
@[expose] def fieldLineSystem (ε φ : ℝ) (q : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![q 0 * Bcomp ε φ (eR φ) q * (Bcomp ε φ (eφ φ) q)⁻¹,
    q 0 * Bcomp ε φ eZ q * (Bcomp ε φ (eφ φ) q)⁻¹]

/-- The axis point `(R, z) = (1, 0)`. -/
@[expose] def axisRZ : Fin 2 → ℝ := ![1, 0]

theorem poloidalMap_axis (φ : ℝ) : poloidalMap φ axisRZ = axis φ := by
  ext k; fin_cases k <;> simp [poloidalMap, axisRZ, eR, eZ, axis]

/-- On the axis `B_R = 0`, `B_z = 0` and `R B_φ = 1`. -/
theorem Bcomp_axis (ε φ : ℝ) :
    Bcomp ε φ (eR φ) axisRZ = 0 ∧ Bcomp ε φ eZ axisRZ = 0 ∧ Bcomp ε φ (eφ φ) axisRZ = 1 := by
  simp only [Bcomp, poloidalMap_axis, field_axis]
  refine ⟨?_, ?_, ?_⟩
  · simp [eR, PiLp.inner_apply, Fin.sum_univ_three]; ring
  · simp [eZ, PiLp.inner_apply, Fin.sum_univ_three]
  · simp only [eφ, PiLp.inner_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      RCLike.inner_apply, conj_trivial]
    nlinarith [cos_sq_add_sin_sq φ]

/-- Derivative of a cylindrical field component at the axis point. -/
theorem Bcomp_hasFDerivAt (ε φ : ℝ) (u : Space) :
    HasFDerivAt (Bcomp ε φ u)
      ((innerSL ℝ u).comp ((fderiv ℝ (field ε) (axis φ)).comp (poloidalMap φ))) axisRZ := by
  have hB : HasFDerivAt (field ε) (fderiv ℝ (field ε) (axis φ)) (poloidalMap φ axisRZ) := by
    rw [poloidalMap_axis]
    exact (field_hasFDerivAt (axis φ) ε (axis_mem_domain φ)).differentiableAt.hasFDerivAt
  exact (innerSL ℝ u).hasFDerivAt.comp axisRZ (hB.comp axisRZ (poloidalMap φ).hasFDerivAt)

/-- **The Jacobian of the field-line system at the axis is `jacobianAtAxis`**: the actual
Fréchet derivative of `(R, z) ↦ (R B_R / B_φ, R B_z / B_φ)` at `(1, 0)` is the matrix
`⟪e_a, DB e_b⟫`; hence (`axis_jacobian`) it is `2ε S(φ)`. -/
theorem fieldLineSystem_hasFDerivAt (ε φ : ℝ) :
    HasFDerivAt (fieldLineSystem ε φ)
      (LinearMap.toContinuousLinearMap (Matrix.toLin' (jacobianAtAxis ε φ))) axisRZ := by
  obtain ⟨hR, hZ, hP⟩ := Bcomp_axis ε φ
  have hq : HasFDerivAt (fun q : Fin 2 → ℝ => q 0) (ContinuousLinearMap.proj 0) axisRZ :=
    hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 2 => ℝ) 0 axisRZ
  have hne : Bcomp ε φ (eφ φ) axisRZ ≠ 0 := by rw [hP]; norm_num
  have hinv := (hasDerivAt_inv hne).hasFDerivAt.comp axisRZ (Bcomp_hasFDerivAt ε φ (eφ φ))
  have h0 := (hq.mul (Bcomp_hasFDerivAt ε φ (eR φ))).mul hinv
  have h1 := (hq.mul (Bcomp_hasFDerivAt ε φ eZ)).mul hinv
  refine hasFDerivAt_pi'.mpr (fun i => ?_)
  have ha : axisRZ 0 = 1 := by simp [axisRZ]
  fin_cases i
  · refine h0.congr_fderiv ?_
    ext v
    simp [hR, hP, ha, jacobianAtAxis, dotProduct, Fin.sum_univ_two, poloidalMap]
    ring
  · refine h1.congr_fderiv ?_
    ext v
    simp [hZ, hP, ha, jacobianAtAxis, dotProduct, Fin.sum_univ_two, poloidalMap]
    ring

/-- The linearized field-line system at the axis is `v' = 2ε S(φ) v`, with the Jacobian
taken from the actual derivative of the `φ`-parametrized system. -/
theorem fieldLineSystem_jacobian (ε φ : ℝ) :
    HasFDerivAt (fieldLineSystem ε φ)
      (LinearMap.toContinuousLinearMap (Matrix.toLin' ((2 * ε) • S φ))) axisRZ := by
  rw [← axis_jacobian]
  exact fieldLineSystem_hasFDerivAt ε φ

/-! ## The variational equation and its monodromy -/

/-- `κ = √(1 − 4ε²)`: the rotation frequency in the frame co-rotating with `φ`. -/
@[expose] def κ (ε : ℝ) : ℝ := √(1 - 4 * ε ^ 2)

/-- The constant matrix of the variational equation in the co-rotating frame. -/
@[expose] def M (ε : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![2 * ε, 1; -1, -2 * ε]

/-- Rotation by angle `φ`. -/
@[expose] def rot (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![cos φ, -sin φ; sin φ, cos φ]

/-- `exp(φ M) = cos κφ · I + (sin κφ / κ) M`. -/
@[expose] def E (ε φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  cos (κ ε * φ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (sin (κ ε * φ) / κ ε) • M ε

/-- The fundamental matrix of `v' = 2ε S(φ) v`: `Φ(φ) = Rot(φ) exp(φ M)`. -/
@[expose] def Φ (ε φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := rot φ * E ε φ

/-- On-axis rotational transform `ι₀ = 1 − κ` (lab-frame rotation number of the linear
flow: the co-rotating frame turns once per transit, the linear flow `−κ` times). -/
@[expose] def iota0 (ε : ℝ) : ℝ := 1 - κ ε

/-- Entrywise derivative of a `2 × 2` matrix-valued function. -/
@[expose] def HasMatDeriv (A : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (A' : Matrix (Fin 2) (Fin 2) ℝ)
    (t : ℝ) : Prop :=
  ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t

/-- Product rule for entrywise matrix derivatives. -/
theorem HasMatDeriv.mul {A B : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {A' B' : Matrix (Fin 2) (Fin 2) ℝ}
    {t : ℝ} (hA : HasMatDeriv A A' t) (hB : HasMatDeriv B B' t) :
    HasMatDeriv (fun s => A s * B s) (A' * B t + A t * B') t := by
  intro i j
  have := ((hA i 0).mul (hB 0 j)).add ((hA i 1).mul (hB 1 j))
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply]
  convert this using 1
  ring

/-- `Rot' = J Rot` with `J` the rotation generator. -/
theorem hasMatDeriv_rot (t : ℝ) : HasMatDeriv rot (!![0, -1; 1, 0] * rot t) t := by
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [rot, Matrix.mul_apply, Fin.sum_univ_two] using hasDerivAt_cos t
  · simpa [rot, Matrix.mul_apply, Fin.sum_univ_two] using (hasDerivAt_sin t).fun_neg
  · simpa [rot, Matrix.mul_apply, Fin.sum_univ_two] using hasDerivAt_sin t
  · simpa [rot, Matrix.mul_apply, Fin.sum_univ_two] using hasDerivAt_cos t

/-- `M² = −κ² I`. -/
theorem M_sq (ε : ℝ) : M ε * M ε = (-(1 - 4 * ε ^ 2)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- `κ² = 1 − 4ε²` for `4ε² < 1`. -/
theorem κ_sq {ε : ℝ} (h : 4 * ε ^ 2 < 1) : κ ε ^ 2 = 1 - 4 * ε ^ 2 :=
  Real.sq_sqrt (by linarith)

/-- `κ > 0` for `4ε² < 1`. -/
theorem κ_pos {ε : ℝ} (h : 4 * ε ^ 2 < 1) : 0 < κ ε := Real.sqrt_pos.mpr (by linarith)

/-- `exp(φM)' = M exp(φM)`. -/
theorem hasMatDeriv_E {ε : ℝ} (h : 4 * ε ^ 2 < 1) (t : ℝ) :
    HasMatDeriv (E ε) (M ε * E ε t) t := by
  have hk := (κ_pos h).ne'
  have hk2 := κ_sq h
  have hc : HasDerivAt (fun s => cos (κ ε * s)) (-(κ ε * sin (κ ε * t))) t := by
    have := ((hasDerivAt_id t).const_mul (κ ε)).cos
    simpa [mul_comm] using this
  have hs : HasDerivAt (fun s => sin (κ ε * s) / κ ε) (cos (κ ε * t)) t := by
    have := (((hasDerivAt_id t).const_mul (κ ε)).sin).div_const (κ ε)
    simp only [id] at this
    convert this using 1
    field_simp
  have hM : M ε * E ε t = (-(κ ε * sin (κ ε * t))) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      cos (κ ε * t) • M ε := by
    rw [E, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, M_sq, ← hk2,
      smul_smul]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [M] <;> field_simp <;> ring
  rw [hM]
  intro i j
  have := (hc.mul_const ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j)).add (hs.mul_const (M ε i j))
  simp only [E, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  convert this using 1

-- The four entries of the matrix identity need different `linear_combination` coefficients;
-- a uniform `simp` followed by `first` is clearest.
set_option linter.flexible false in
/-- **The variational equation along the axis is solved by `Φ`**: entrywise
`Φ'(φ) = 2ε S(φ) Φ(φ)`, and `Φ(0) = I`. -/
theorem Φ_solves {ε : ℝ} (h : 4 * ε ^ 2 < 1) (φ : ℝ) :
    HasMatDeriv (Φ ε) ((2 * ε) • S φ * Φ ε φ) φ ∧ Φ ε 0 = 1 := by
  refine ⟨?_, ?_⟩
  · have hd := (hasMatDeriv_rot φ).mul (hasMatDeriv_E h φ)
    have key : !![(0 : ℝ), -1; 1, 0] * rot φ + rot φ * M ε = (2 * ε) • S φ * rot φ := by
      have hcs : cos φ ^ 2 + sin φ ^ 2 = 1 := cos_sq_add_sin_sq φ
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [rot, M, S, Matrix.mul_apply, Fin.sum_univ_two, cos_two_mul, sin_two_mul] <;>
        first
        | ring1
        | linear_combination (-4 * ε * cos φ) * hcs
        | linear_combination (4 * ε * cos φ) * hcs
    have e : !![(0 : ℝ), -1; 1, 0] * rot φ * E ε φ + rot φ * (M ε * E ε φ) =
        (2 * ε) • S φ * Φ ε φ := by
      rw [Φ, ← Matrix.mul_assoc (rot φ) (M ε), ← Matrix.add_mul, key, Matrix.mul_assoc]
    rw [← e]
    exact hd
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Φ, rot, E, M]

/-- `Rot(2π) = I`, so the monodromy is `exp(2π M)`. -/
theorem Φ_two_pi (ε : ℝ) : Φ ε (2 * π) = E ε (2 * π) := by
  have : rot (2 * π) = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [rot]
  rw [Φ, this, Matrix.one_mul]

/-- **Monodromy trace**: `tr Φ(2π) = 2 cos 2πκ`. -/
theorem monodromy_trace (ε : ℝ) : (Φ ε (2 * π)).trace = 2 * cos (2 * π * κ ε) := by
  rw [Φ_two_pi, Matrix.trace_fin_two]
  simp only [E, M, smul_of, smul_cons, smul_eq_mul, mul_one, smul_empty, mul_neg,
    Matrix.add_apply, Matrix.smul_apply, one_apply_eq, of_apply, cons_val', cons_val_zero,
    cons_val_fin_one, cons_val_one]
  rw [mul_comm (κ ε)]
  ring

/-- The monodromy is area preserving: `det Φ(2π) = 1` (for `4ε² < 1`). -/
theorem monodromy_det {ε : ℝ} (h : 4 * ε ^ 2 < 1) : (Φ ε (2 * π)).det = 1 := by
  have hk := (κ_pos h).ne'
  have hk2 := κ_sq h
  rw [Φ_two_pi, Matrix.det_fin_two]
  simp [E, M]
  field_simp
  linear_combination (-(sin (κ ε * 2 * π)) ^ 2) * hk2 +
    (κ ε) ^ 2 * cos_sq_add_sin_sq (κ ε * 2 * π)

/-- `0 < κ < 1` for `0 < 4ε² < 1`. -/
theorem κ_lt_one {ε : ℝ} (h0 : 0 < ε ^ 2) (h : 4 * ε ^ 2 < 1) : κ ε < 1 := by
  have := κ_sq h
  have := (κ_pos h).le
  nlinarith

/-- **The axis is elliptic** (linear stability only): for `0 < 4ε² < 1` with `κ ≠ 1/2`,
`|tr Φ(2π)| < 2`. Together with `det Φ(2π) = 1` the Floquet multipliers are a complex
conjugate pair on the unit circle, `e^{±2πiκ} ≠ ±1`. -/
theorem axis_elliptic_of {ε : ℝ} (h0 : 0 < ε ^ 2) (h : 4 * ε ^ 2 < 1) (hk : κ ε ≠ 1 / 2) :
    |(Φ ε (2 * π)).trace| < 2 := by
  rw [monodromy_trace, abs_mul, abs_two]
  suffices hc : |cos (2 * π * κ ε)| < 1 by linarith
  rcases (abs_cos_le_one (2 * π * κ ε)).lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  have hsin : sin (2 * π * κ ε) = 0 := by
    have h2 := sin_sq_add_cos_sq (2 * π * κ ε)
    have h3 : cos (2 * π * κ ε) ^ 2 = 1 := by rw [← sq_abs, heq, one_pow]
    nlinarith [sq_nonneg (sin (2 * π * κ ε))]
  obtain ⟨n, hn⟩ := sin_eq_zero_iff.mp hsin
  have hnk : (n : ℝ) = 2 * κ ε := by
    have := pi_pos
    field_simp at hn
    linarith
  have hpos : (0 : ℝ) < n := by rw [hnk]; linarith [κ_pos h]
  have hlt2 : (n : ℝ) < 2 := by rw [hnk]; linarith [κ_lt_one h0 h]
  have hn1 : n = 1 := by
    have a : 0 < n := by exact_mod_cast hpos
    have b : n < 2 := by exact_mod_cast hlt2
    omega
  apply hk
  rw [hn1] at hnk
  push_cast at hnk
  linarith

/-- For `ε = 1/4`: `κ = √3/2`. -/
theorem κ_quarter : κ (1 / 4) = √3 / 2 := by
  rw [κ, show (1 - 4 * (1 / 4 : ℝ) ^ 2) = 3 / 4 by norm_num,
    Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 3), show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

/-- For `ε = 1/4` the on-axis transform is the quadratic irrational `ι₀ = 1 − √3/2`. -/
theorem iota0_quarter : iota0 (1 / 4) = 1 - √3 / 2 := by rw [iota0, κ_quarter]

/-- **The magnetic axis of `field (1/4)` is linearly stable (elliptic)**:
`|tr Φ(2π)| = |2 cos(√3 π)| < 2`. Linear stability only; no nonlinear claim. -/
theorem axis_elliptic : |(Φ (1 / 4) (2 * π)).trace| < 2 := by
  refine axis_elliptic_of (by norm_num) (by norm_num) ?_
  rw [κ_quarter]
  intro h
  have h3 : √3 = 1 := by linarith
  have := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  rw [h3] at this
  norm_num at this

/-- Sanity (degenerate case `ε = 0`): the axis Jacobian vanishes, `κ = 1`, and the
monodromy is the identity (parabolic, `tr = 2`): no rotational transform without the
helical field. -/
theorem monodromy_trace_zero : (Φ 0 (2 * π)).trace = 2 := by
  rw [monodromy_trace]
  have : κ 0 = 1 := by simp [κ]
  rw [this, mul_one, cos_two_pi, mul_one]

end PlasmaLean.Design.RationalStellarator
