/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Kernel.Vacuum
public import PlasmaLean.Theory.Fields.ClebschDivergence
public import PlasmaLean.Theory.Fields.FirstIntegral
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# An exact rational vacuum stellarator field

The candidate field of `notes/theory/first-stellarator-rung.md` (§0, §1): in cylindrical
coordinates, with `R₀ = B₀ = 1`,
`B_ε = ∇φ + ε ∇h`, `h = f cos 2φ + g sin 2φ`, `f = ((R² − 1)² − 4z²)/(4R²)`,
`g = −z((R² − 1)(R² − 5) − 4z²)/(4R²)`. In Cartesian coordinates, with `r₂ = x² + y²`,
`h = H/4`, `H = Hnum / r₂²`,
`Hnum = ((r₂ − 1)² − 4z²)(x² − y²) − 2xyz((r₂ − 1)(r₂ − 5) − 4z²)`,
and `∇φ = (−y, x, 0)/r₂` (the field of a line current on the `z`-axis).

Lean model. Everything is an explicit rational function of the Cartesian coordinates on
`Space = EuclideanSpace ℝ (Fin 3)`; `winv = 1/r₂` (Lean's `r₂⁻¹`, so the formulas are
total, and meaningful on `domain = {r₂ > 0}`).
* `Hd i` are the partial derivatives of `Hnum` (verified with sympy, proved in Lean:
  `hasFDerivAt_Hnum`), `Hdd i j` its second partial derivatives (`hasFDerivAt_Hd`).
* `gradH = (G 0, G 1, G 2)` with `G i = Hd i / r₂² − 4 cᵢ Hnum / r₂³`, `c = (x, y, 0)`;
  `H_hasFDerivAt` proves `DH = ⟪gradH, ·⟫` on the domain.
* `field ε = toroidal + (ε/4) • gradH` is `∇φ + ε ∇h`.

Results.
* `field_hasFDerivAt`: the actual Fréchet derivative (explicit Jacobian `JB`).
* `field_vacuum`: `VacuumField domain (field ε)` (open, `C²`, `∇·B = 0`, `∇×B = 0`) for
  every `ε`. The divergence reduces to the polynomial identity
  `r₂ ΔHnum − 8(x ∂ₓHnum + y ∂_yHnum) + 16 Hnum = 0` (i.e. `ΔH = 0`), the curl to the
  symmetry of the Hessian.
* `axis_fieldLine`: the unit circle `t ↦ (cos t, sin t, 0)` is an exact field line for
  every `ε` (`∇H` vanishes on it and `∇φ` is its unit tangent).
* `field_rotPi` (two field periods: invariance under rotation by `π` about the `z`-axis),
  `field_stellSym` (stellarator symmetry `σ(x, y, z) = (y, x, −z)`, `B ∘ σ = −σ B`),
  `field_not_axisymmetric` (for `ε ≠ 0`).

Scope: a vacuum (β = 0) model field; no coil set reproduces it exactly (`ε ∇h` grows like
`R²` and must come from external windings). Field-line confinement is not proved here.
-/

open scoped RealInnerProductSpace

public section
noncomputable section
namespace PlasmaLean.Design.RationalStellarator
open PlasmaLean.Fields PlasmaLean.Vacuum WithLp

/-! ## The field -/

/-- Squared distance from the `z`-axis, `r₂ = x² + y²`. -/
@[expose] def r2 (y : Space) : ℝ := y 0 ^ 2 + y 1 ^ 2
/-- `1 / r₂` (Lean's total inverse). -/
@[expose] def winv (y : Space) : ℝ := (r2 y)⁻¹
/-- `(r₂ − 1)² − 4z²` (`= 4R² f`). -/
@[expose] def Aq (y : Space) : ℝ := (r2 y - 1) ^ 2 - 4 * y 2 ^ 2
/-- `(r₂ − 1)(r₂ − 5) − 4z²`. -/
@[expose] def Bq (y : Space) : ℝ := (r2 y - 1) * (r2 y - 5) - 4 * y 2 ^ 2
/-- `x² − y² = R² cos 2φ`. -/
@[expose] def Xd (y : Space) : ℝ := y 0 ^ 2 - y 1 ^ 2
/-- `2xyz = z R² sin 2φ`. -/
@[expose] def Yp (y : Space) : ℝ := 2 * y 0 * y 1 * y 2
/-- Numerator of the helical potential, a degree-6 polynomial. -/
@[expose] def Hnum (y : Space) : ℝ := Aq y * Xd y - Bq y * Yp y
/-- The helical potential `H = Hnum / r₂² = 4h`. -/
@[expose] def H (y : Space) : ℝ := Hnum y * winv y ^ 2

/-- `∂ₓ Hnum`. -/
@[expose] def H0 (y : Space) : ℝ :=
  4 * y 0 * (r2 y - 1) * Xd y + 2 * y 0 * Aq y - 4 * y 0 * (r2 y - 3) * Yp y -
    2 * y 1 * y 2 * Bq y
/-- `∂_y Hnum`. -/
@[expose] def H1 (y : Space) : ℝ :=
  4 * y 1 * (r2 y - 1) * Xd y - 2 * y 1 * Aq y - 4 * y 1 * (r2 y - 3) * Yp y -
    2 * y 0 * y 2 * Bq y
/-- `∂_z Hnum`. -/
@[expose] def H2 (y : Space) : ℝ := -8 * y 2 * Xd y + 8 * y 2 * Yp y - 2 * y 0 * y 1 * Bq y
/-- The gradient of `Hnum`, coordinate `i`. -/
@[expose] def Hd (i : Fin 3) (y : Space) : ℝ := ![H0 y, H1 y, H2 y] i

/-- `∂ₓ² Hnum`. -/
@[expose] def H00 (y : Space) : ℝ :=
  30*y 0^4 - 40*y 0^3*y 1*y 2 + 12*y 0^2*y 1^2 - 24*y 0^2 - 24*y 0*y 1^3*y 2 +
    72*y 0*y 1*y 2 - 2*y 1^4 - 8*y 2^2 + 2
/-- `∂ₓ∂_y Hnum`. -/
@[expose] def H01 (y : Space) : ℝ :=
  -10*y 0^4*y 2 + 8*y 0^3*y 1 - 36*y 0^2*y 1^2*y 2 + 36*y 0^2*y 2 - 8*y 0*y 1^3 -
    10*y 1^4*y 2 + 36*y 1^2*y 2 + 8*y 2^3 - 10*y 2
/-- `∂ₓ∂_z Hnum`. -/
@[expose] def H02 (y : Space) : ℝ :=
  -10*y 0^4*y 1 - 12*y 0^2*y 1^3 + 36*y 0^2*y 1 - 16*y 0*y 2 - 2*y 1^5 + 12*y 1^3 +
    24*y 1*y 2^2 - 10*y 1
/-- `∂_y² Hnum`. -/
@[expose] def H11 (y : Space) : ℝ :=
  2*y 0^4 - 24*y 0^3*y 1*y 2 - 12*y 0^2*y 1^2 - 40*y 0*y 1^3*y 2 + 72*y 0*y 1*y 2 -
    30*y 1^4 + 24*y 1^2 + 8*y 2^2 - 2
/-- `∂_y∂_z Hnum`. -/
@[expose] def H12 (y : Space) : ℝ :=
  -2*y 0^5 - 12*y 0^3*y 1^2 + 12*y 0^3 - 10*y 0*y 1^4 + 36*y 0*y 1^2 + 24*y 0*y 2^2 -
    10*y 0 + 16*y 1*y 2
/-- `∂_z² Hnum`. -/
@[expose] def H22 (y : Space) : ℝ := -8*y 0^2 + 48*y 0*y 1*y 2 + 8*y 1^2
/-- The Hessian of `Hnum` (symmetric by construction). -/
@[expose] def Hdd (i j : Fin 3) (y : Space) : ℝ :=
  ![![H00 y, H01 y, H02 y], ![H01 y, H11 y, H12 y], ![H02 y, H12 y, H22 y]] i j

/-- The cylindrical-radius vector `c = (x, y, 0)`. -/
@[expose] def cv (i : Fin 3) (y : Space) : ℝ := ![y 0, y 1, 0] i
/-- The constant Jacobian of `c`. -/
@[expose] def cd (i j : Fin 3) : ℝ := ![![1, 0, 0], ![0, 1, 0], ![0, 0, 0]] i j

/-- Coordinate `i` of `∇H`: `G i = Hd i / r₂² − 4 cᵢ Hnum / r₂³`. -/
@[expose] def G (i : Fin 3) (y : Space) : ℝ :=
  Hd i y * winv y ^ 2 - 4 * cv i y * Hnum y * winv y ^ 3

/-- The gradient `∇H` of the helical potential. -/
@[expose] def gradH (y : Space) : Space := toLp 2 ![G 0 y, G 1 y, G 2 y]

/-- The toroidal field `∇φ = (−y, x, 0)/r₂`. -/
@[expose] def toroidal (y : Space) : Space := toLp 2 ![-y 1 * winv y, y 0 * winv y, 0]

/-- **The rational stellarator field** `B_ε = ∇φ + ε ∇h = ∇φ + (ε/4) ∇H`. -/
@[expose] def field (ε : ℝ) (y : Space) : Space := toroidal y + (ε / 4) • gradH y

/-- The current-free region `{x² + y² > 0}` (all space minus the `z`-axis). -/
@[expose] def domain : Set Space := {y | 0 < r2 y}

/-- Coordinates of the field. -/
theorem field_apply (ε : ℝ) (y : Space) :
    field ε y 0 = -y 1 * winv y + ε / 4 * G 0 y ∧ field ε y 1 = y 0 * winv y + ε / 4 * G 1 y ∧
      field ε y 2 = ε / 4 * G 2 y := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [field, toroidal, gradH]

/-! ## Derivatives -/

/-- Coordinate functional. -/
abbrev pr (i : Fin 3) : Space →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i

/-- The linear functional with partial derivatives `(a, b, c)`. -/
@[expose] def lin (a b c : ℝ) : Space →L[ℝ] ℝ := a • pr 0 + b • pr 1 + c • pr 2

/-- Evaluation of `lin`. -/
theorem lin_apply (a b c : ℝ) (v : Space) : lin a b c v = a * v 0 + b * v 1 + c * v 2 := by
  simp [lin]

/-- Transfer a derivative along a pointwise identity, identifying the partials. -/
theorem hfd {f g : Space → ℝ} {L : Space →L[ℝ] ℝ} {a b c : ℝ} {x : Space}
    (h : HasFDerivAt g L x) (hf : ∀ y, f y = g y)
    (hL : ∀ v, L v = a * v 0 + b * v 1 + c * v 2) : HasFDerivAt f (lin a b c) x := by
  rw [show f = g from funext hf]
  refine h.congr_fderiv ?_
  ext v
  rw [hL, lin_apply]

/-- Partial derivatives of `1/r₂`. -/
@[expose] def wd (x : Space) (j : Fin 3) : ℝ := -2 * cv j x * winv x ^ 2

/-- Jacobian of the toroidal field. -/
@[expose] def JT (x : Space) (i j : Fin 3) : ℝ :=
  ![-(cd 1 j) * winv x - x 1 * wd x j, cd 0 j * winv x + x 0 * wd x j, 0] i

/-- Jacobian of `∇H`: the derivative of `G i` in direction `j`. -/
@[expose] def JG (x : Space) (i j : Fin 3) : ℝ :=
  Hdd i j x * winv x ^ 2 + Hd i x * (2 * winv x * wd x j) -
    4 * (cd i j * Hnum x * winv x ^ 3 +
      cv i x * (Hd j x * winv x ^ 3 + Hnum x * (3 * winv x ^ 2 * wd x j)))

/-- Jacobian of the field. -/
@[expose] def JB (ε : ℝ) (x : Space) (i j : Fin 3) : ℝ := JT x i j + ε / 4 * JG x i j

section Derivs
variable (x : Space)

/-- Coordinate functions are linear. -/
theorem hasFDerivAt_coord (i : Fin 3) : HasFDerivAt (fun y : Space => y i) (pr i) x :=
  (pr i).hasFDerivAt

/-- Derivative of `r₂`. -/
theorem hasFDerivAt_r2 : HasFDerivAt r2 (lin (2 * x 0) (2 * x 1) 0) x :=
  hfd (((hasFDerivAt_coord x 0).pow 2).add ((hasFDerivAt_coord x 1).pow 2))
    (fun y => rfl) (fun v => by simp)

/-- Derivative of `1/r₂` off the axis. -/
theorem hasFDerivAt_winv (hx : r2 x ≠ 0) :
    HasFDerivAt winv (lin (wd x 0) (wd x 1) (wd x 2)) x :=
  hfd ((hasDerivAt_inv hx).hasFDerivAt.comp x (hasFDerivAt_r2 x)) (fun y => rfl) (fun v => by
    simp [lin_apply, wd, cv, winv]; ring)

/-- Derivative of `c = (x, y, 0)`. -/
theorem hasFDerivAt_cv (i : Fin 3) :
    HasFDerivAt (cv i) (lin (cd i 0) (cd i 1) (cd i 2)) x := by
  fin_cases i
  · exact hfd (hasFDerivAt_coord x 0) (fun y => rfl) (fun v => by simp [cd])
  · exact hfd (hasFDerivAt_coord x 1) (fun y => rfl) (fun v => by simp [cd])
  · exact hfd (hasFDerivAt_const (0 : ℝ) x) (fun y => rfl) (fun v => by simp [cd])

/-- The gradient of `Hnum` is `(H0, H1, H2)` (sympy-checked, proved here). -/
theorem hasFDerivAt_Hnum : HasFDerivAt Hnum (lin (Hd 0 x) (Hd 1 x) (Hd 2 x)) x := by
  have c0 := hasFDerivAt_coord x 0
  have c1 := hasFDerivAt_coord x 1
  have c2 := hasFDerivAt_coord x 2
  have hr := hasFDerivAt_r2 x
  have := ((((hr.sub_const 1).pow 2).sub ((c2.pow 2).const_mul 4)).mul
    ((c0.pow 2).sub (c1.pow 2))).sub
    ((((hr.sub_const 1).mul (hr.sub_const 5)).sub ((c2.pow 2).const_mul 4)).mul
      (((c0.const_mul 2).mul c1).mul c2))
  refine hfd this (fun y => rfl) (fun v => ?_)
  simp [lin_apply, Hd, H0, H1, H2, Aq, Bq, Xd, Yp, r2]
  ring

/-- The Hessian of `Hnum` is `Hdd` (sympy-checked, proved here). -/
theorem hasFDerivAt_Hd (i : Fin 3) :
    HasFDerivAt (Hd i) (lin (Hdd i 0 x) (Hdd i 1 x) (Hdd i 2 x)) x := by
  have c0 := hasFDerivAt_coord x 0
  have c1 := hasFDerivAt_coord x 1
  have c2 := hasFDerivAt_coord x 2
  have hr := hasFDerivAt_r2 x
  have hA := ((hr.sub_const 1).pow 2).sub ((c2.pow 2).const_mul 4)
  have hB := ((hr.sub_const 1).mul (hr.sub_const 5)).sub ((c2.pow 2).const_mul 4)
  have hX := (c0.pow 2).sub (c1.pow 2)
  have hY := ((c0.const_mul 2).mul c1).mul c2
  fin_cases i
  · have := (((((c0.const_mul 4).mul (hr.sub_const 1)).mul hX).add ((c0.const_mul 2).mul hA)).sub
      (((c0.const_mul 4).mul (hr.sub_const 3)).mul hY)).sub (((c1.const_mul 2).mul c2).mul hB)
    refine hfd this (fun y => rfl) (fun v => ?_)
    simp [lin_apply, Hdd, H00, H01, H02, r2]
    ring
  · have := (((((c1.const_mul 4).mul (hr.sub_const 1)).mul hX).sub ((c1.const_mul 2).mul hA)).sub
      (((c1.const_mul 4).mul (hr.sub_const 3)).mul hY)).sub (((c0.const_mul 2).mul c2).mul hB)
    refine hfd this (fun y => rfl) (fun v => ?_)
    simp [lin_apply, Hdd, H01, H11, H12, r2]
    ring
  · have := (((c2.const_mul (-8)).mul hX).add ((c2.const_mul 8).mul hY)).sub
      (((c0.const_mul 2).mul c1).mul hB)
    refine hfd this (fun y => rfl) (fun v => ?_)
    simp [lin_apply, Hdd, H02, H12, H22, r2]
    ring

/-- Derivative of the coordinates of `∇H` off the axis. -/
theorem hasFDerivAt_G (hx : r2 x ≠ 0) (i : Fin 3) :
    HasFDerivAt (G i) (lin (JG x i 0) (JG x i 1) (JG x i 2)) x := by
  have hw := hasFDerivAt_winv x hx
  have := ((hasFDerivAt_Hd x i).mul (hw.pow 2)).sub
    ((((hasFDerivAt_cv x i).const_mul 4).mul (hasFDerivAt_Hnum x)).mul (hw.pow 3))
  refine hfd this (fun y => rfl) (fun v => ?_)
  simp [lin_apply, JG]
  ring

/-- The derivative of `H` is `⟪∇H, ·⟫` on the domain. -/
theorem H_hasFDerivAt (hx : x ∈ domain) : HasFDerivAt H (innerSL ℝ (gradH x)) x := by
  have hx' : r2 x ≠ 0 := ne_of_gt hx
  have hw := hasFDerivAt_winv x hx'
  have := (hasFDerivAt_Hnum x).mul (hw.pow 2)
  refine (hfd (a := G 0 x) (b := G 1 x) (c := G 2 x) this (fun y => rfl)
    (fun v => ?_)).congr_fderiv ?_
  · simp [lin_apply, G, wd, cv]
    ring
  · ext v
    simp [lin_apply, gradH, PiLp.inner_apply, Fin.sum_univ_three]
    ring

/-- Derivative of the coordinates of `∇φ` off the axis. -/
theorem hasFDerivAt_T (hx : r2 x ≠ 0) (i : Fin 3) :
    HasFDerivAt (fun y => toroidal y i) (lin (JT x i 0) (JT x i 1) (JT x i 2)) x := by
  have hw := hasFDerivAt_winv x hx
  fin_cases i
  · exact hfd ((hasFDerivAt_coord x 1).neg.mul hw) (fun y => by simp [toroidal])
      (fun v => by simp [lin_apply, JT, cd]; ring)
  · exact hfd ((hasFDerivAt_coord x 0).mul hw) (fun y => by simp [toroidal])
      (fun v => by simp [lin_apply, JT, cd]; ring)
  · exact hfd (hasFDerivAt_const (0 : ℝ) x) (fun y => by simp [toroidal])
      (fun v => by simp [JT])

/-- Derivative of the coordinates of the field off the axis. -/
theorem hasFDerivAt_fieldCoord (ε : ℝ) (hx : r2 x ≠ 0) (i : Fin 3) :
    HasFDerivAt (fun y => field ε y i) (lin (JB ε x i 0) (JB ε x i 1) (JB ε x i 2)) x := by
  have := (hasFDerivAt_T x hx i).add ((hasFDerivAt_G x hx i).const_mul (ε / 4))
  refine hfd this (fun y => ?_) (fun v => ?_)
  · fin_cases i <;> simp [field, gradH]
  · simp [lin_apply, JB]; ring

/-- The derivative operator of the field, assembled from the Jacobian `JB`. -/
@[expose] def fieldDeriv (ε : ℝ) (x : Space) : Space →L[ℝ] Space :=
  ∑ k, (lin (JB ε x k 0) (JB ε x k 1) (JB ε x k 2)).smulRight (basis k)

/-- **The actual Fréchet derivative of the field** at every point off the `z`-axis. -/
theorem field_hasFDerivAt (ε : ℝ) (hx : x ∈ domain) :
    HasFDerivAt (field ε) (fieldDeriv ε x) x :=
  hasFDerivAt_of_coords (fun k => hasFDerivAt_fieldCoord x ε (ne_of_gt hx) k)

/-- Entries of the derivative: `(DB eⱼ)ᵢ = JB i j`. -/
theorem fieldDeriv_entry (ε : ℝ) (i j : Fin 3) :
    fieldDeriv ε x (coordVec j) i = JB ε x i j := by
  rw [fieldDeriv, coords_apply, lin_apply]
  fin_cases j <;> simp

end Derivs

/-! ## Vacuum -/

/-- The divergence identity `∑ᵢ JB i i = 0` (uses `ΔH = 0`). -/
theorem JB_trace (ε : ℝ) {x : Space} (hx : r2 x ≠ 0) :
    JB ε x 0 0 + JB ε x 1 1 + JB ε x 2 2 = 0 := by
  have hw : winv x * (x 0 ^ 2 + x 1 ^ 2) = 1 := by
    rw [winv, ← r2]; exact inv_mul_cancel₀ hx
  linear_combination (norm := skip) (ε / 4) * (24 * Hnum x * winv x ^ 3 -
    winv x ^ 2 * (Hdd 0 0 x + Hdd 1 1 x + Hdd 2 2 x)) * hw
  simp only [JB, JT, JG, wd, cv, cd, Hd, Hdd, Hnum, H0, H1, H2, H00, H11, H22, Aq, Bq, Xd, Yp, r2,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-- The Jacobian is symmetric (curl free). -/
theorem JB_symm (ε : ℝ) {x : Space} (hx : r2 x ≠ 0) (i j : Fin 3) :
    JB ε x i j = JB ε x j i := by
  have hw : winv x * (x 0 ^ 2 + x 1 ^ 2) = 1 := by
    rw [winv, ← r2]; exact inv_mul_cancel₀ hx
  fin_cases i <;> fin_cases j <;>
    simp only [JB, JT, JG, wd, cv, cd, Hd, Hdd, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] <;>
    first
    | ring1
    | linear_combination (2 * winv x) * hw
    | linear_combination (-2 * winv x) * hw

/-- The domain is open. -/
theorem isOpen_domain : IsOpen domain :=
  isOpen_lt continuous_const (by unfold r2; fun_prop)

/-- `1/r₂` is smooth off the axis. -/
theorem contDiffAt_winv {x : Space} (hx : r2 x ≠ 0) : ContDiffAt ℝ 2 winv x := by
  have : ContDiff ℝ 2 r2 := by
    unfold r2
    have h0 : ContDiff ℝ 2 (fun y : Space => y 0) := (pr 0).contDiff
    have h1 : ContDiff ℝ 2 (fun y : Space => y 1) := (pr 1).contDiff
    fun_prop
  exact this.contDiffAt.inv hx

/-- The field is `C²` on the domain. -/
theorem field_contDiffOn (ε : ℝ) : ContDiffOn ℝ 2 (field ε) domain := by
  intro x hx
  have hx' : r2 x ≠ 0 := ne_of_gt hx
  refine ContDiffAt.contDiffWithinAt ?_
  have hw := contDiffAt_winv hx'
  have h0 : ContDiffAt ℝ 2 (fun y : Space => y 0) x := (pr 0).contDiff.contDiffAt
  have h1 : ContDiffAt ℝ 2 (fun y : Space => y 1) x := (pr 1).contDiff.contDiffAt
  have h2 : ContDiffAt ℝ 2 (fun y : Space => y 2) x := (pr 2).contDiff.contDiffAt
  have g0 : ContDiff ℝ 2 (fun y : Space => y 0) := (pr 0).contDiff
  have g1 : ContDiff ℝ 2 (fun y : Space => y 1) := (pr 1).contDiff
  have g2 : ContDiff ℝ 2 (fun y : Space => y 2) := (pr 2).contDiff
  have hHn : ContDiffAt ℝ 2 Hnum x := by
    unfold Hnum Aq Bq Xd Yp r2; fun_prop
  have hG : ∀ i, ContDiffAt ℝ 2 (G i) x := by
    intro i
    have hHd : ContDiffAt ℝ 2 (Hd i) x := by
      have k0 : ContDiff ℝ 2 H0 := by unfold H0 Aq Bq Xd Yp r2; fun_prop
      have k1 : ContDiff ℝ 2 H1 := by unfold H1 Aq Bq Xd Yp r2; fun_prop
      have k2 : ContDiff ℝ 2 H2 := by unfold H2 Bq Xd Yp r2; fun_prop
      fin_cases i
      exacts [k0.contDiffAt, k1.contDiffAt, k2.contDiffAt]
    have hcv : ContDiffAt ℝ 2 (cv i) x := by
      fin_cases i
      exacts [h0, h1, contDiffAt_const]
    unfold G; fun_prop
  refine (contDiffAt_piLp 2).mpr (fun i => ?_)
  fin_cases i
  · have e : (fun y => field ε y 0) = fun y => -y 1 * winv y + ε / 4 * G 0 y :=
      funext fun y => (field_apply ε y).1
    rw [show (⟨0, by norm_num⟩ : Fin 3) = 0 from rfl, e]
    have := hG 0
    fun_prop
  · have e : (fun y => field ε y 1) = fun y => y 0 * winv y + ε / 4 * G 1 y :=
      funext fun y => (field_apply ε y).2.1
    rw [show (⟨1, by norm_num⟩ : Fin 3) = 1 from rfl, e]
    have := hG 1
    fun_prop
  · have e : (fun y => field ε y 2) = fun y => ε / 4 * G 2 y :=
      funext fun y => (field_apply ε y).2.2
    rw [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, e]
    have := hG 2
    fun_prop

/-- **The rational stellarator field is an exact vacuum field** off the `z`-axis, for every
`ε`: open region, `C²`, `∇ · B = 0` and `∇ × B = 0`. -/
theorem field_vacuum (ε : ℝ) : VacuumField domain (field ε) := by
  refine ⟨isOpen_domain, field_contDiffOn ε, fun x hx => ?_, fun x hx => ?_⟩
  · rw [fieldDiv, (field_hasFDerivAt x ε hx).fderiv, divOp_apply, fieldDeriv_entry,
      fieldDeriv_entry, fieldDeriv_entry]
    exact JB_trace ε (ne_of_gt hx)
  · rw [fieldCurl, (field_hasFDerivAt x ε hx).fderiv, curlOp_eq_zero_iff]
    intro i j
    rw [fieldDeriv_entry, fieldDeriv_entry]
    exact JB_symm ε (ne_of_gt hx) i j

/-- Degenerate case `ε = 0`: the toroidal field `∇φ` alone is a vacuum field. -/
theorem toroidal_vacuum : VacuumField domain toroidal := by
  have h := field_vacuum 0
  have : field 0 = toroidal := by funext y; simp [field]
  rwa [this] at h

/-! ## The exact magnetic axis -/

/-- The unit circle in the plane `z = 0`, parametrized by the toroidal angle. -/
@[expose] def axis (t : ℝ) : Space := toLp 2 ![Real.cos t, Real.sin t, 0]

/-- On the axis the helical gradient vanishes and the field is the unit tangent. -/
theorem field_axis (ε t : ℝ) : field ε (axis t) = toLp 2 ![-Real.sin t, Real.cos t, 0] := by
  have hr : r2 (axis t) = 1 := by simp [r2, axis, Real.cos_sq_add_sin_sq]
  have hw : winv (axis t) = 1 := by simp [winv, hr]
  have hz : axis t 2 = 0 := by simp [axis]
  have hA : Aq (axis t) = 0 := by simp [Aq, hr, hz]
  have hB : Bq (axis t) = 0 := by simp [Bq, hr, hz]
  have hY : Yp (axis t) = 0 := by simp [Yp, hz]
  have hHn : Hnum (axis t) = 0 := by simp [Hnum, hA, hB]
  have hG : ∀ i, G i (axis t) = 0 := by
    intro i
    fin_cases i <;> simp [G, Hd, H0, H1, H2, hr, hz, hA, hB, hY, hHn]
  ext k
  fin_cases k <;> simp [field, toroidal, gradH, hG, hw] <;> simp [axis]

/-- **Exact magnetic axis**: the unit circle `t ↦ (cos t, sin t, 0)` is a field line of
`B_ε` for every `ε` (parameter = toroidal angle = arc length). -/
theorem axis_fieldLine (ε : ℝ) : IsForwardFieldLine (field ε) axis := by
  intro t _
  rw [field_axis]
  have hγ : axis = fun s => Real.cos s • basis 0 + Real.sin s • basis 1 := by
    funext s; ext k; fin_cases k <;> simp [axis, basis]
  rw [hγ]
  have := ((Real.hasDerivAt_cos t).smul_const (basis 0)).add
    ((Real.hasDerivAt_sin t).smul_const (basis 1))
  convert this using 1
  ext k; fin_cases k <;> simp [basis]

/-- The axis lies in the current-free domain. -/
theorem axis_mem_domain (t : ℝ) : axis t ∈ domain := by
  simp [domain, r2, axis, Real.cos_sq_add_sin_sq]

/-! ## Symmetries -/

/-- Rotation by `π` about the `z`-axis. -/
@[expose] def rotPi (y : Space) : Space := toLp 2 ![-y 0, -y 1, y 2]

/-- Stellarator symmetry: rotation by `π` about the line `x = y, z = 0`. -/
@[expose] def σ (y : Space) : Space := toLp 2 ![y 1, y 0, -y 2]

/-- Rotation by angle `α` about the `z`-axis. -/
@[expose] def rotZ (α : ℝ) (y : Space) : Space :=
  toLp 2 ![Real.cos α * y 0 - Real.sin α * y 1, Real.sin α * y 0 + Real.cos α * y 1, y 2]

/-- `r₂` is invariant under `Rot_π`. -/
theorem winv_rotPi (y : Space) : winv (rotPi y) = winv y := by
  simp [winv, r2, rotPi]

/-- `r₂` is invariant under `σ`. -/
theorem winv_σ (y : Space) : winv (σ y) = winv y := by
  simp [winv, r2, σ, add_comm]

/-- **Two field periods**: `B_ε ∘ Rot_π = Rot_π ∘ B_ε`. -/
theorem field_rotPi (ε : ℝ) (y : Space) : field ε (rotPi y) = rotPi (field ε y) := by
  ext k
  fin_cases k <;>
    simp [field, toroidal, gradH, G, Hd, cv, H0, H1, H2, Hnum, Aq, Bq, Xd, Yp, r2,
      winv_rotPi] <;> simp [rotPi] <;> ring

/-- Coordinates of `σ y`. -/
theorem σ_coords (y : Space) : σ y 0 = y 1 ∧ σ y 1 = y 0 ∧ σ y 2 = -y 2 := by
  simp [σ]

/-- `∇H ∘ σ = −σ ∇H` in coordinates (from `H ∘ σ = −H`). -/
theorem G_σ (y : Space) :
    G 0 (σ y) = -G 1 y ∧ G 1 (σ y) = -G 0 y ∧ G 2 (σ y) = G 2 y := by
  obtain ⟨s0, s1, s2⟩ := σ_coords y
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [G, Hd, cv, H0, H1, H2, Hnum, Aq, Bq, Xd, Yp, r2, winv_σ, s0, s1, s2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] <;> ring

/-- **Stellarator symmetry**: `B_ε ∘ σ = −σ ∘ B_ε`, `σ(x, y, z) = (y, x, −z)`
(`H ∘ σ = −H`, `φ ∘ σ = π/2 − φ`). -/
theorem field_stellSym (ε : ℝ) (y : Space) : field ε (σ y) = -σ (field ε y) := by
  obtain ⟨g0, g1, g2⟩ := G_σ y
  obtain ⟨f0, f1, f2⟩ := field_apply ε (σ y)
  obtain ⟨e0, e1, e2⟩ := field_apply ε y
  obtain ⟨s0, s1, s2⟩ := σ_coords y
  obtain ⟨t0, t1, t2⟩ := σ_coords (field ε y)
  ext k
  fin_cases k <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, PiLp.neg_apply, f0, f1,
      f2, g0, g1, g2, t0, t1, t2, e0, e1, e2, s0, s1, winv_σ] <;> ring

/-- **Not axisymmetric** for `ε ≠ 0`: some rotation about the `z`-axis does not commute
with `B_ε` (rotation by `π/2` at the point `(2, 0, 0)`). -/
theorem field_not_axisymmetric {ε : ℝ} (hε : ε ≠ 0) :
    ¬ ∀ α y, field ε (rotZ α y) = rotZ α (field ε y) := by
  intro h
  have h1 := congrArg (fun v : Space => v 1) (h (Real.pi / 2) (toLp 2 ![2, 0, 0]))
  simp [rotZ, field, toroidal, gradH, G, Hd, cv, H0, H1, H2, Hnum, Aq, Bq, Xd, Yp, winv,
    r2] at h1
  norm_num at h1
  apply hε
  linarith

end PlasmaLean.Design.RationalStellarator
