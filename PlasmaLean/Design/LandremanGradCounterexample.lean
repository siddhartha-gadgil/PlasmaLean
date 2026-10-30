/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanEquilibrium
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Landreman family 1 as a Grad counterexample (Q-17)

Research note: `notes/theory/grad-conjecture.md` (N-28). Source: M. Landreman, *Analytic
toroidal 3D MHD equilibria and steady Euler flows with invariant surfaces*, arXiv:2609.26742 v2
(unrefereed preprint), §2. The closed forms and the force balance are those compiled in
`Design/LandremanEquilibrium`; everything below is re-proved from them.

Grad's conjecture asks whether smooth toroidal magnetohydrostatic equilibria with nested flux
surfaces and non-constant pressure must have a continuous Euclidean symmetry. The main theorem
`family1_grad_counterexample` states, for `0 < ε < 1`, `0 < δ < (1-ε)²/4`, `μ₀ > 0` and the
plasma domain `Ω_δ = {x ∈ 𝒰 | ψ x ≤ δ}`:

1. `B`, `J = (∇ × B)/μ₀` and `p = (2δ - 2ψ)/μ₀` are `C^∞` on the open set `𝒰 ⊇ Ω_δ`
   (`contDiffOn_field`, `contDiffOn_current`, `contDiffOn_pressure`);
2. `∇ · B = 0` and `J × B = ∇p` with Mathlib's `gradient` of the explicit `p`;
3. nested toroidal flux surfaces: `ψ` is a first integral, `ψ ≥ 0`, the sublevel sets
   `{ψ ≤ c}` (`c ≤ δ`) are compact and increase with `c`, **each level set `{ψ = c}`,
   `0 < c ≤ δ`, is homeomorphic to `S¹ × S¹`** through the explicit map `torusMap`
   (`fluxSurface_homeo_torus`), and `{ψ = 0}` is homeomorphic to `S¹` and contains the
   magnetic axis (`axisSet_homeo_circle`);
4. `p` is not constant on `Ω_δ` (`2δ/μ₀` on the axis, `0` on the torus `ψ = δ`);
5. no continuous Euclidean symmetry: for every nonzero Killing field `K x = r × x + t`
   (rotations, translations, screw motions: axial and helical generators included) the Lie
   derivative `L_K B = (DB) K - r × B` is nonzero somewhere in `Ω_δ`
   (`killing_trivial_of_axis`: it already fails at one of the two axis points `ζ = 0, π/2`).

## The torus parametrization

In the stretched coordinates `X = x/a`, `Y = y/b` (`s = X² + Y²`, `w = (1-s)/2`,
`q² = w² + z² = (1 - rad)/4`) put `P = (2q² - w)/s`, `Q = zF/s`. Then
`(u + iv) s = (P + iQ)(X + iY)²` (`uF_eq`, `vF_eq`), `P² + Q² = q²` and `1 - 2P = rad/s`, where
`u, v` are Landreman's labels with `ψ = (u + ε/2)² + v²` (paper (2.15)). Conversely
(`surfPt`), `s = (1 - 4q²)/(1 - 2P)`, `x = a√s X`, `y = b√s Y`, `z = Q√(1-4q²)/(1 - 2P)`.
With `z₁, z₂ ∈ S¹` and `P + iQ = (-ε/2 + √c z₁) z̄₂²`, the point `torusMap a b c z₁ z₂` lies on
`ψ = c`; it is injective (`torusMap_inj`) and onto the level set (`torusMap_surj`), and a
continuous bijection from the compact `S¹ × S¹` to a Hausdorff space is a homeomorphism.
This formalizes the paper's claim (below (2.11)) that the surfaces are tori, which
`LandremanEquilibrium` had left open.

## Scope and what is not claimed

* The solid-torus topology of `Ω_δ` itself is not stated; what is proved is that `Ω_δ` is
  compact and is the union of the axis circle and the tori `{ψ = c}`, `0 < c ≤ δ`.
* Symmetry means invariance of `B` under the isometry flow of a Killing field, i.e.
  `L_K B = 0`; only continuous (one-parameter) symmetries are excluded. The family keeps its
  discrete symmetries: two field periods (`field_rotPi`) and stellarator symmetry
  (`field_flipX`). Plane-reflection symmetry is not addressed.
* `ι ≡ 2` (all field lines closed): the example is non-generic, as in the paper.
* Sanity contrast: at `ε = 0` (`a = b = 1`) the rotation generator `e_z × x` is a symmetry
  (`axisymmetric_limit_lie_zero`), so `ε ≠ 0` is necessary in item 5.
-/

open scoped RealInnerProductSpace ContDiff

public section
noncomputable section
namespace PlasmaLean.Design.LandremanGradCounterexample
open PlasmaLean.Fields WithLp LandremanEquilibrium

/-- `𝒰` is open. -/
theorem isOpen_U (a b : ℝ) : IsOpen (U a b) :=
  (continuous_rad a b).isOpen_preimage _ isOpen_Ioi

/-- `s` is smooth. -/
theorem contDiff_sF (a b : ℝ) : ContDiff ℝ ∞ (sF a b) := by
  unfold sF; fun_prop

/-- The radicand is smooth. -/
theorem contDiff_rad (a b : ℝ) : ContDiff ℝ ∞ (rad a b) := by
  unfold rad; have := contDiff_sF a b; fun_prop

/-- `F = √rad` is smooth on `𝒰`. -/
theorem contDiffOn_Fr (a b : ℝ) : ContDiffOn ℝ ∞ (Fr a b) (U a b) := fun _ hx =>
  ((contDiff_rad a b).contDiffAt.sqrt (ne_of_gt hx)).contDiffWithinAt

/-- The field is smooth on `𝒰`. -/
theorem contDiffOn_field (a b : ℝ) : ContDiffOn ℝ ∞ (field a b) (U a b) := by
  have hF := contDiffOn_Fr a b
  have hs := (contDiff_sF a b).contDiffOn (s := U a b)
  have hp (i : Fin 3) : ContDiffOn ℝ ∞ (fun x : Space => x i) (U a b) :=
    (pr i).contDiff.contDiffOn
  have hs0 : ∀ x ∈ U a b, sF a b x ≠ 0 := fun x hx => (sF_pos hx).ne'
  refine contDiffOn_piLp' 2 fun i => ?_
  fin_cases i
  · exact ((((hp 2).const_smul (2:ℝ)).mul (hp 0)).sub
      (((hF.const_smul (a / b))).mul (hp 1))).div hs hs0 |>.congr (fun x _ => by simp [field, N0])
  · exact ((((hp 2).const_smul (2:ℝ)).mul (hp 1)).add
      (((hF.const_smul (b / a))).mul (hp 0))).div hs hs0 |>.congr (fun x _ => by simp [field, N1])
  · exact ((contDiffOn_const (c := (1:ℝ))).sub hs).congr (fun x _ => by simp [field])

/-- The Ampère current `J = (∇ × B)/μ₀` (with the actual derivative) is smooth on `𝒰`. -/
theorem contDiffOn_current (μ₀ a b : ℝ) : ContDiffOn ℝ ∞ (current μ₀ a b) (U a b) := by
  have h := (contDiffOn_field a b).fderiv_of_isOpen (isOpen_U a b) (m := ∞) le_rfl
  exact ((curlCLM.contDiff.comp_contDiffOn h).const_smul μ₀⁻¹).congr
    (fun x _ => by simp [current, curl])

/-- The flux label `ψ` is smooth on `𝒰`. -/
theorem contDiffOn_psi (a b : ℝ) : ContDiffOn ℝ ∞ (psi a b) (U a b) := by
  have hQ : ContDiff ℝ ∞ Qf := by unfold Qf; fun_prop
  have hH : ContDiffOn ℝ ∞ (H a b) (U a b) :=
    (hQ.contDiffOn.add (((contDiffOn_field a b).norm_sq ℝ).div_const 2)).congr
      (fun x _ => by simp [H])
  exact (((hH.sub (contDiffOn_const (c := (a ^ 2 + b ^ 2) / 2))).add
      (contDiffOn_const (c := epsAB a b ^ 2 / 2))).div_const 2).congr
    (fun x _ => by simp [psi])

/-- The pressure `p = (p_a - 2ψ)/μ₀` is smooth on `𝒰`. -/
theorem contDiffOn_pressure (μ₀ pa a b : ℝ) : ContDiffOn ℝ ∞ (pressure μ₀ pa a b) (U a b) :=
  (((contDiffOn_const (c := pa)).sub ((contDiffOn_psi a b).const_smul (2:ℝ))).div_const μ₀).congr
    (fun x _ => by simp [pressure])

/-! ## Explicit torus parametrization of the flux surfaces -/

/-- Stretched coordinate `X = x/a`. -/
@[expose] def Xc (a : ℝ) (x : Space) : ℝ := x 0 / a

/-- Stretched coordinate `Y = y/b`. -/
@[expose] def Yc (b : ℝ) (x : Space) : ℝ := x 1 / b

/-- Surface label `P = (2q² - w)/s`, with `q² = (1 - rad)/4` and `w = (1 - s)/2`. -/
@[expose] def Pl (a b : ℝ) (x : Space) : ℝ :=
  (2 * ((1 - rad a b x) / 4) - (1 - sF a b x) / 2) / sF a b x

/-- Surface label `Q = z F/s`. -/
@[expose] def Ql (a b : ℝ) (x : Space) : ℝ := x 2 * Fr a b x / sF a b x

/-- `s = X² + Y²`. -/
theorem sF_eq_XY (a b : ℝ) (x : Space) : sF a b x = Xc a x ^ 2 + Yc b x ^ 2 := by
  simp [sF, Xc, Yc, div_pow]

/-- The field-line labels in terms of `(P, Q)`: `(u + i v) s = (P + i Q)(X + i Y)²`
(the real part). -/
theorem uF_eq {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) {x : Space} (hx : x ∈ U a b) :
    uF a b x * sF a b x =
      Pl a b x * (Xc a x ^ 2 - Yc b x ^ 2) - 2 * Ql a b x * Xc a x * Yc b x := by
  obtain ⟨hS, hF, hF2⟩ := point_data ha hb hx
  simp only [uF, Pl, Ql, Xc, Yc, rad, field, N0, N1, sF_eq ha hb, Fin.isValue,
    PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  generalize Fr a b x = F at *
  field_simp
  sq_elim F using hF2
  unfold Sden
  ring

/-- The imaginary part of `(u + i v) s = (P + i Q)(X + i Y)²`. -/
theorem vF_eq {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) {x : Space} (hx : x ∈ U a b) :
    vF a b x * sF a b x =
      2 * Pl a b x * Xc a x * Yc b x + Ql a b x * (Xc a x ^ 2 - Yc b x ^ 2) := by
  obtain ⟨hS, hF, hF2⟩ := point_data ha hb hx
  simp only [vF, Pl, Ql, Xc, Yc, rad, field, N0, N1, sF_eq ha hb, Fin.isValue,
    PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  generalize Fr a b x = F at *
  field_simp
  sq_elim F using hF2
  unfold Sden
  ring

/-- `P² + Q² = q² = (1 - rad)/4` on `𝒰`. -/
theorem PQ_sq {a b : ℝ} {x : Space} (hx : x ∈ U a b) :
    Pl a b x ^ 2 + Ql a b x ^ 2 = (1 - rad a b x) / 4 := by
  have hs := (sF_pos hx).ne'
  have hF2 : Fr a b x ^ 2 = rad a b x := Real.sq_sqrt hx.le
  simp only [Pl, Ql]
  field_simp
  rw [hF2]
  unfold rad
  ring

/-- `1 - 2P = rad/s` on `𝒰`. -/
theorem one_sub_two_Pl {a b : ℝ} {x : Space} (hx : x ∈ U a b) :
    1 - 2 * Pl a b x = rad a b x / sF a b x := by
  have hs := (sF_pos hx).ne'
  simp only [Pl]
  field_simp
  ring

/-- The point of `𝒰` with surface labels `(P, Q)` and stretched toroidal direction `(X, Y)`
(`X² + Y² = 1`): `s = (1 - 4q²)/(1 - 2P)`, `x = a √s X`, `y = b √s Y`,
`z = Q √(1 - 4q²)/(1 - 2P)`, where `q² = P² + Q²`. -/
@[expose] def surfPt (a b P Q X Y : ℝ) : Space :=
  toLp 2 ![a * √((1 - 4 * (P ^ 2 + Q ^ 2)) / (1 - 2 * P)) * X,
    b * √((1 - 4 * (P ^ 2 + Q ^ 2)) / (1 - 2 * P)) * Y,
    Q * √(1 - 4 * (P ^ 2 + Q ^ 2)) / (1 - 2 * P)]

section SurfPt
variable {a b P Q X Y : ℝ}

/-- `1 - 2P > 0` when `P² + Q² < 1/4`. -/
theorem one_sub_two_P_pos (hq : P ^ 2 + Q ^ 2 < 1 / 4) : 0 < 1 - 2 * P := by
  nlinarith [sq_nonneg Q, sq_nonneg (2 * P - 1)]

/-- `s = (1 - 4q²)/(1 - 2P)` at `surfPt`. -/
theorem sF_surfPt (ha : a ≠ 0) (hb : b ≠ 0) (hq : P ^ 2 + Q ^ 2 < 1 / 4)
    (hXY : X ^ 2 + Y ^ 2 = 1) :
    sF a b (surfPt a b P Q X Y) = (1 - 4 * (P ^ 2 + Q ^ 2)) / (1 - 2 * P) := by
  have hD := one_sub_two_P_pos hq
  have hD0 := hD.ne'
  have hS : 0 ≤ (1 - 4 * (P ^ 2 + Q ^ 2)) / (1 - 2 * P) := div_nonneg (by linarith) hD.le
  have hR := Real.sq_sqrt hS
  simp only [sF, surfPt, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [mul_pow, mul_pow, mul_pow, mul_pow, hR]
  generalize 1 - 2 * P = D at *
  field_simp
  linear_combination (1 - 4 * (P ^ 2 + Q ^ 2)) * hXY

/-- `rad = 1 - 4q²` at `surfPt`. -/
theorem rad_surfPt (ha : a ≠ 0) (hb : b ≠ 0) (hq : P ^ 2 + Q ^ 2 < 1 / 4)
    (hXY : X ^ 2 + Y ^ 2 = 1) :
    rad a b (surfPt a b P Q X Y) = 1 - 4 * (P ^ 2 + Q ^ 2) := by
  have hD := one_sub_two_P_pos hq
  have hD0 := hD.ne'
  have hT := Real.sq_sqrt (show 0 ≤ 1 - 4 * (P ^ 2 + Q ^ 2) by linarith)
  rw [rad, sF_surfPt ha hb hq hXY]
  simp only [surfPt, PiLp.toLp_apply, Matrix.cons_val]
  rw [div_pow, mul_pow, hT]
  generalize hDd : 1 - 2 * P = D at *
  field_simp
  have hP : P = (1 - D) / 2 := by linarith
  subst hP
  ring

/-- `surfPt` lies in `𝒰`. -/
theorem surfPt_mem (ha : a ≠ 0) (hb : b ≠ 0) (hq : P ^ 2 + Q ^ 2 < 1 / 4)
    (hXY : X ^ 2 + Y ^ 2 = 1) : surfPt a b P Q X Y ∈ U a b := by
  change 0 < rad a b _
  rw [rad_surfPt ha hb hq hXY]; linarith

/-- `F = √(1 - 4q²)` at `surfPt`. -/
theorem Fr_surfPt (ha : a ≠ 0) (hb : b ≠ 0) (hq : P ^ 2 + Q ^ 2 < 1 / 4)
    (hXY : X ^ 2 + Y ^ 2 = 1) :
    Fr a b (surfPt a b P Q X Y) = √(1 - 4 * (P ^ 2 + Q ^ 2)) := by
  rw [Fr, rad_surfPt ha hb hq hXY]

/-- The label `P` of `surfPt` is `P`. -/
theorem Pl_surfPt (ha : a ≠ 0) (hb : b ≠ 0) (hq : P ^ 2 + Q ^ 2 < 1 / 4)
    (hXY : X ^ 2 + Y ^ 2 = 1) : Pl a b (surfPt a b P Q X Y) = P := by
  have hD := one_sub_two_P_pos hq
  have hD0 := hD.ne'
  have hT : 0 < 1 - 4 * (P ^ 2 + Q ^ 2) := by linarith
  rw [Pl, rad_surfPt ha hb hq hXY, sF_surfPt ha hb hq hXY]
  generalize hDd : 1 - 2 * P = D at *
  field_simp
  have hP : P = (1 - D) / 2 := by linarith
  subst hP
  ring

/-- The label `Q` of `surfPt` is `Q`. -/
theorem Ql_surfPt (ha : a ≠ 0) (hb : b ≠ 0) (hq : P ^ 2 + Q ^ 2 < 1 / 4)
    (hXY : X ^ 2 + Y ^ 2 = 1) : Ql a b (surfPt a b P Q X Y) = Q := by
  have hD := one_sub_two_P_pos hq
  have hD0 := hD.ne'
  have hT : 0 < 1 - 4 * (P ^ 2 + Q ^ 2) := by linarith
  have hT2 := Real.sq_sqrt hT.le
  rw [Ql, Fr_surfPt ha hb hq hXY, sF_surfPt ha hb hq hXY]
  simp only [surfPt, PiLp.toLp_apply, Matrix.cons_val]
  generalize 1 - 2 * P = D at *
  field_simp
  rw [hT2]

/-- The stretched coordinates of `surfPt` are `√s (X, Y)`. -/
theorem XY_surfPt (ha : a ≠ 0) (hb : b ≠ 0) :
    Xc a (surfPt a b P Q X Y) = √((1 - 4 * (P ^ 2 + Q ^ 2)) / (1 - 2 * P)) * X ∧
    Yc b (surfPt a b P Q X Y) = √((1 - 4 * (P ^ 2 + Q ^ 2)) / (1 - 2 * P)) * Y := by
  constructor <;> simp [Xc, Yc, surfPt] <;> field_simp

/-- The flux label at `surfPt`:
`ψ = (P(X² - Y²) - 2QXY + ε/2)² + (2PXY + Q(X² - Y²))²`. -/
theorem psi_surfPt (ha : a ≠ 0) (hb : b ≠ 0) (hq : P ^ 2 + Q ^ 2 < 1 / 4)
    (hXY : X ^ 2 + Y ^ 2 = 1) :
    psi a b (surfPt a b P Q X Y) =
      (P * (X ^ 2 - Y ^ 2) - 2 * Q * X * Y + epsAB a b / 2) ^ 2 +
        (2 * P * X * Y + Q * (X ^ 2 - Y ^ 2)) ^ 2 := by
  have hm := surfPt_mem ha hb hq hXY
  have hs := sF_pos hm
  have hu := uF_eq ha hb hm
  have hv := vF_eq ha hb hm
  rw [sF_eq_XY, Pl_surfPt ha hb hq hXY, Ql_surfPt ha hb hq hXY] at hu hv
  obtain ⟨hX, hY⟩ := XY_surfPt (P := P) (Q := Q) (X := X) (Y := Y) ha hb
  rw [hX, hY] at hu hv
  set S := (1 - 4 * (P ^ 2 + Q ^ 2)) / (1 - 2 * P)
  have hS0 : 0 < S := div_pos (by linarith) (one_sub_two_P_pos hq)
  have hR := Real.sq_sqrt hS0.le
  have hsum : (√S * X) ^ 2 + (√S * Y) ^ 2 = S := by
    rw [mul_pow, mul_pow, hR]; linear_combination S * hXY
  rw [hsum] at hu hv
  have hu' : uF a b (surfPt a b P Q X Y) = P * (X ^ 2 - Y ^ 2) - 2 * Q * X * Y := by
    apply mul_right_cancel₀ hS0.ne'
    rw [hu]; linear_combination (P * (X ^ 2 - Y ^ 2) - 2 * Q * X * Y) * hR
  have hv' : vF a b (surfPt a b P Q X Y) = 2 * P * X * Y + Q * (X ^ 2 - Y ^ 2) := by
    apply mul_right_cancel₀ hS0.ne'
    rw [hv]; linear_combination (2 * P * X * Y + Q * (X ^ 2 - Y ^ 2)) * hR
  rw [psi_eq_uv ha hb hm, hu', hv']

end SurfPt

/-! ### The torus map `S¹ × S¹ → {ψ = c}` -/

/-- The complex surface label `ζ = (-ε/2 + √c z₁) z̄₂²`, with `ε = epsAB a b`. -/
@[expose] def zeta (a b c : ℝ) (z₁ z₂ : ℂ) : ℂ :=
  (-((epsAB a b / 2 : ℝ) : ℂ) + ((√c : ℝ) : ℂ) * z₁) * (starRingEnd ℂ z₂) ^ 2

/-- The explicit parametrization of the flux surface `ψ = c` by `(z₁, z₂) ∈ S¹ × S¹`:
`z₁ = e^{iθ}` is the poloidal angle about the magnetic axis in the `(u, v)` label plane and
`z₂ = e^{iφ}` the toroidal angle in the stretched coordinates `(x/a, y/b)`. -/
@[expose] def torusMap (a b c : ℝ) (z₁ z₂ : ℂ) : Space :=
  surfPt a b (zeta a b c z₁ z₂).re (zeta a b c z₁ z₂).im z₂.re z₂.im

/-- `|ζ| < 1/2` on `S¹ × S¹` under the shell condition `|ε|/2 + √c < 1/2`. -/
theorem zeta_sq_lt {a b c : ℝ} (hc : |epsAB a b| / 2 + √c < 1 / 2) {z₁ z₂ : ℂ}
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) :
    (zeta a b c z₁ z₂).re ^ 2 + (zeta a b c z₁ z₂).im ^ 2 < 1 / 4 := by
  have hn : ‖zeta a b c z₁ z₂‖ ≤ |epsAB a b| / 2 + √c := by
    rw [zeta, norm_mul, norm_pow, Complex.norm_conj, h₂, one_pow, mul_one]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_mul, h₁, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_div, abs_two, abs_of_nonneg (Real.sqrt_nonneg c)]
  have h0 : 0 ≤ ‖zeta a b c z₁ z₂‖ := norm_nonneg _
  have : ‖zeta a b c z₁ z₂‖ ^ 2 < 1 / 4 := by nlinarith
  have e := Complex.sq_norm (zeta a b c z₁ z₂)
  rw [Complex.normSq_apply] at e
  nlinarith

/-- `ζ z₂² = -ε/2 + √c z₁` for `|z₂| = 1`. -/
theorem zeta_mul_sq {a b c : ℝ} {z₁ z₂ : ℂ} (h₂ : ‖z₂‖ = 1) :
    zeta a b c z₁ z₂ * z₂ ^ 2 = -((epsAB a b / 2 : ℝ) : ℂ) + ((√c : ℝ) : ℂ) * z₁ := by
  have h : starRingEnd ℂ z₂ * z₂ = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h₂]; simp
  rw [zeta, mul_assoc, ← mul_pow, h, one_pow, mul_one]

section TorusMap
variable {a b c : ℝ}

/-- Real and imaginary parts of `ζ z₂²`. -/
theorem zeta_mul_sq_re_im (z₁ z₂ : ℂ) :
    (zeta a b c z₁ z₂ * z₂ ^ 2).re = (zeta a b c z₁ z₂).re * (z₂.re ^ 2 - z₂.im ^ 2) -
      2 * (zeta a b c z₁ z₂).im * z₂.re * z₂.im ∧
    (zeta a b c z₁ z₂ * z₂ ^ 2).im = 2 * (zeta a b c z₁ z₂).re * z₂.re * z₂.im +
      (zeta a b c z₁ z₂).im * (z₂.re ^ 2 - z₂.im ^ 2) := by
  constructor <;> simp [sq, Complex.mul_re, Complex.mul_im] <;> ring

/-- `z₂.re² + z₂.im² = 1` on the unit circle. -/
theorem re_sq_add_im_sq {z : ℂ} (h : ‖z‖ = 1) : z.re ^ 2 + z.im ^ 2 = 1 := by
  have e := Complex.sq_norm z
  rw [Complex.normSq_apply, h] at e
  nlinarith

/-- The torus map lands in `𝒰`. -/
theorem torusMap_mem (ha : a ≠ 0) (hb : b ≠ 0) (hc : |epsAB a b| / 2 + √c < 1 / 2)
    {z₁ z₂ : ℂ} (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) : torusMap a b c z₁ z₂ ∈ U a b :=
  surfPt_mem ha hb (zeta_sq_lt hc h₁ h₂) (re_sq_add_im_sq h₂)

/-- The torus map lands on the flux surface `ψ = c`. -/
theorem psi_torusMap (ha : a ≠ 0) (hb : b ≠ 0) (hc0 : 0 ≤ c)
    (hc : |epsAB a b| / 2 + √c < 1 / 2) {z₁ z₂ : ℂ} (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) :
    psi a b (torusMap a b c z₁ z₂) = c := by
  rw [torusMap, psi_surfPt ha hb (zeta_sq_lt hc h₁ h₂) (re_sq_add_im_sq h₂)]
  obtain ⟨er, ei⟩ := zeta_mul_sq_re_im (a := a) (b := b) (c := c) z₁ z₂
  rw [← er, ← ei, zeta_mul_sq h₂]
  have h1 := re_sq_add_im_sq h₁
  simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im, Complex.neg_im, neg_zero,
    Complex.mul_im, zero_add, add_zero]
  have hs := Real.sq_sqrt hc0
  linear_combination (√c) ^ 2 * h1 + hs

/-- The stretched toroidal direction `(x/a, y/b)/√s` of a point of `𝒰`, as a unit complex
number. -/
@[expose] def Z2 (a b : ℝ) (x : Space) : ℂ :=
  ⟨Xc a x / √(sF a b x), Yc b x / √(sF a b x)⟩

/-- The complex surface label `P + i Q` of a point. -/
@[expose] def Wl (a b : ℝ) (x : Space) : ℂ := ⟨Pl a b x, Ql a b x⟩

/-- `|Z2| = 1` on `𝒰`. -/
theorem norm_Z2 {x : Space} (hx : x ∈ U a b) : ‖Z2 a b x‖ = 1 := by
  have hs := sF_pos hx
  have hR := Real.sq_sqrt hs.le
  have hR0 := (Real.sqrt_pos.mpr hs).ne'
  have h2 : ‖Z2 a b x‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Z2]
    field_simp
    rw [hR, sF_eq_XY]
  nlinarith [norm_nonneg (Z2 a b x)]

/-- `(P + i Q) Z2² = u + i v` on `𝒰`: the label plane of paper (2.14)–(2.15). -/
theorem Wl_mul_Z2_sq (ha : a ≠ 0) (hb : b ≠ 0) {x : Space} (hx : x ∈ U a b) :
    Wl a b x * Z2 a b x ^ 2 = ⟨uF a b x, vF a b x⟩ := by
  have hs := sF_pos hx
  have hR := Real.sq_sqrt hs.le
  have hR0 := (Real.sqrt_pos.mpr hs).ne'
  have hu := uF_eq ha hb hx
  have hv := vF_eq ha hb hx
  apply Complex.ext
  · simp only [Wl, Z2, sq, Complex.mul_re, Complex.mul_im]
    field_simp
    rw [hR]
    linear_combination -hu
  · simp only [Wl, Z2, sq, Complex.mul_re, Complex.mul_im]
    field_simp
    rw [hR]
    linear_combination -hv

/-- `ψ = |(P + i Q) Z2² + ε/2|²` on `𝒰`. -/
theorem psi_eq_Wl (ha : a ≠ 0) (hb : b ≠ 0) {x : Space} (hx : x ∈ U a b) :
    psi a b x = ‖Wl a b x * Z2 a b x ^ 2 + ((epsAB a b / 2 : ℝ) : ℂ)‖ ^ 2 := by
  rw [Wl_mul_Z2_sq ha hb hx, Complex.sq_norm, Complex.normSq_apply, psi_eq_uv ha hb hx]
  simp [sq]

/-- **Reconstruction.** If `-ε/2 + √c z₁ = (P + i Q) Z2²` at `x ∈ 𝒰`, the torus map
returns `x`. -/
theorem torusMap_eq_of (ha : a ≠ 0) (hb : b ≠ 0) {x : Space} (hx : x ∈ U a b) {z₁ : ℂ}
    (h : -((epsAB a b / 2 : ℝ) : ℂ) + ((√c : ℝ) : ℂ) * z₁ = Wl a b x * Z2 a b x ^ 2) :
    torusMap a b c z₁ (Z2 a b x) = x := by
  have hn := norm_Z2 hx
  have hz : zeta a b c z₁ (Z2 a b x) = Wl a b x := by
    have hc : starRingEnd ℂ (Z2 a b x) * Z2 a b x = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
    rw [zeta, h, mul_assoc, ← mul_pow, mul_comm (Z2 a b x), hc]
    simp
  have hs := sF_pos hx
  have hR0 := Real.sqrt_pos.mpr hs
  have hr : 0 < rad a b x := hx
  have hF2 : Fr a b x ^ 2 = rad a b x := Real.sq_sqrt hr.le
  have h1 : 1 - 4 * (Pl a b x ^ 2 + Ql a b x ^ 2) = rad a b x := by rw [PQ_sq hx]; ring
  have h2 := one_sub_two_Pl hx
  have h3 : rad a b x / (rad a b x / sF a b x) = sF a b x := by field_simp
  rw [torusMap, hz]
  simp only [Wl, Z2, surfPt]
  rw [h1, h2, h3]
  apply space_ext
  · simp [Xc]; field_simp
  · simp [Yc]; field_simp
  · simp only [Matrix.cons_val, Ql, Fr]
    rw [← Fr]
    field_simp
    rw [hF2]

/-- The torus map's direction label is `z₂`. -/
theorem Z2_torusMap (ha : a ≠ 0) (hb : b ≠ 0) (hc : |epsAB a b| / 2 + √c < 1 / 2)
    {z₁ z₂ : ℂ} (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) : Z2 a b (torusMap a b c z₁ z₂) = z₂ := by
  have hq := zeta_sq_lt hc h₁ h₂
  have hXY := re_sq_add_im_sq h₂
  have hS := sF_surfPt ha hb hq hXY
  obtain ⟨hX, hY⟩ := XY_surfPt (P := (zeta a b c z₁ z₂).re) (Q := (zeta a b c z₁ z₂).im)
    (X := z₂.re) (Y := z₂.im) ha hb
  have hpos : 0 < √((1 - 4 * ((zeta a b c z₁ z₂).re ^ 2 + (zeta a b c z₁ z₂).im ^ 2)) /
      (1 - 2 * (zeta a b c z₁ z₂).re)) := by
    rw [← hS]; exact Real.sqrt_pos.mpr (sF_pos (surfPt_mem ha hb hq hXY))
  apply Complex.ext
  · simp only [Z2, torusMap, hX, hS]; exact mul_div_cancel_left₀ _ hpos.ne'
  · simp only [Z2, torusMap, hY, hS]; exact mul_div_cancel_left₀ _ hpos.ne'

/-- The torus map's surface label is `ζ`. -/
theorem Wl_torusMap (ha : a ≠ 0) (hb : b ≠ 0) (hc : |epsAB a b| / 2 + √c < 1 / 2)
    {z₁ z₂ : ℂ} (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) :
    Wl a b (torusMap a b c z₁ z₂) = zeta a b c z₁ z₂ := by
  have hq := zeta_sq_lt hc h₁ h₂
  have hXY := re_sq_add_im_sq h₂
  apply Complex.ext
  · exact Pl_surfPt ha hb hq hXY
  · exact Ql_surfPt ha hb hq hXY

/-- **Injectivity.** Equal images force equal toroidal angles `z₂` and equal `√c z₁`. -/
theorem torusMap_inj (ha : a ≠ 0) (hb : b ≠ 0) (hc : |epsAB a b| / 2 + √c < 1 / 2)
    {z₁ z₂ w₁ w₂ : ℂ} (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (k₁ : ‖w₁‖ = 1) (k₂ : ‖w₂‖ = 1)
    (h : torusMap a b c z₁ z₂ = torusMap a b c w₁ w₂) :
    z₂ = w₂ ∧ ((√c : ℝ) : ℂ) * z₁ = ((√c : ℝ) : ℂ) * w₁ := by
  have e2 : z₂ = w₂ := by
    rw [← Z2_torusMap ha hb hc h₁ h₂, h, Z2_torusMap ha hb hc k₁ k₂]
  have eW : zeta a b c z₁ z₂ = zeta a b c w₁ w₂ := by
    rw [← Wl_torusMap ha hb hc h₁ h₂, h, Wl_torusMap ha hb hc k₁ k₂]
  refine ⟨e2, ?_⟩
  have := congrArg (· * z₂ ^ 2) eW
  rw [zeta_mul_sq h₂, e2, zeta_mul_sq k₂] at this
  linear_combination this

/-- **Surjectivity onto the level set**, `c > 0`. -/
theorem torusMap_surj (ha : a ≠ 0) (hb : b ≠ 0) (hc0 : 0 < c) {x : Space} (hx : x ∈ U a b)
    (hψ : psi a b x = c) :
    ∃ z₁ : ℂ, ‖z₁‖ = 1 ∧ torusMap a b c z₁ (Z2 a b x) = x := by
  have hs := Real.sqrt_pos.mpr hc0
  have hn : ‖Wl a b x * Z2 a b x ^ 2 + ((epsAB a b / 2 : ℝ) : ℂ)‖ = √c := by
    rw [← hψ, psi_eq_Wl ha hb hx, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨(Wl a b x * Z2 a b x ^ 2 + ((epsAB a b / 2 : ℝ) : ℂ)) / ((√c : ℝ) : ℂ), ?_, ?_⟩
  · rw [norm_div, hn, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, div_self hs.ne']
  · apply torusMap_eq_of ha hb hx
    have : ((√c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    field_simp
    ring

/-- **Surjectivity onto the level set**, `c = 0` (the magnetic axis): any `z₁` works. -/
theorem torusMap_surj_zero (ha : a ≠ 0) (hb : b ≠ 0) {x : Space} (hx : x ∈ U a b)
    (hψ : psi a b x = 0) (z₁ : ℂ) : torusMap a b 0 z₁ (Z2 a b x) = x := by
  apply torusMap_eq_of ha hb hx
  have h0 : ‖Wl a b x * Z2 a b x ^ 2 + ((epsAB a b / 2 : ℝ) : ℂ)‖ = 0 := by
    have := psi_eq_Wl ha hb hx
    rw [hψ] at this
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this.symm
  rw [norm_eq_zero] at h0
  simp only [Real.sqrt_zero, Complex.ofReal_zero, zero_mul, add_zero]
  linear_combination -h0

/-- The shell condition from the paper's bound `c < (1 - |ε|)²/4` (paper (2.17)). -/
theorem shell_of_lt {ε c : ℝ} (hε : |ε| < 1) (hc : c < (1 - |ε|) ^ 2 / 4) :
    |ε| / 2 + √c < 1 / 2 := by
  have : √c < (1 - |ε|) / 2 := by
    rw [Real.sqrt_lt' (by linarith)]; nlinarith
  linarith

/-- The torus map is continuous on `S¹ × S¹`. -/
theorem continuous_torusMap (hc : |epsAB a b| / 2 + √c < 1 / 2) :
    Continuous fun p : Circle × Circle => torusMap a b c p.1 p.2 := by
  have hζ : Continuous fun p : Circle × Circle => zeta a b c p.1 p.2 := by
    unfold zeta; fun_prop
  have hP : Continuous fun p : Circle × Circle => (zeta a b c p.1 p.2).re :=
    Complex.continuous_re.comp hζ
  have hQ : Continuous fun p : Circle × Circle => (zeta a b c p.1 p.2).im :=
    Complex.continuous_im.comp hζ
  have hD : ∀ p : Circle × Circle, 1 - 2 * (zeta a b c p.1 p.2).re ≠ 0 := fun p =>
    (one_sub_two_P_pos (zeta_sq_lt hc (Circle.norm_coe p.1) (Circle.norm_coe p.2))).ne'
  have hT : Continuous fun p : Circle × Circle =>
      1 - 4 * ((zeta a b c p.1 p.2).re ^ 2 + (zeta a b c p.1 p.2).im ^ 2) := by fun_prop
  have hR : Continuous fun p : Circle × Circle =>
      √((1 - 4 * ((zeta a b c p.1 p.2).re ^ 2 + (zeta a b c p.1 p.2).im ^ 2)) /
        (1 - 2 * (zeta a b c p.1 p.2).re)) :=
    Real.continuous_sqrt.comp (hT.div (by fun_prop) hD)
  have h2 : Continuous fun p : Circle × Circle => ((p.2 : ℂ)) := by fun_prop
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  fin_cases i
  · exact (continuous_const.mul hR).mul (Complex.continuous_re.comp h2)
  · exact (continuous_const.mul hR).mul (Complex.continuous_im.comp h2)
  · exact (hQ.mul (Real.continuous_sqrt.comp hT)).div (by fun_prop) hD

end TorusMap

/-! ### Each flux surface is a torus; the degenerate surface is a circle -/

section Topology
variable {a b c : ℝ}

/-- **Each flux surface `ψ = c`, `0 < c`, `|ε|/2 + √c < 1/2`, is a 2-torus**: the explicit map
`torusMap` is a homeomorphism from `S¹ × S¹` onto the whole level set `{x ∈ 𝒰 | ψ x = c}`. -/
theorem fluxSurface_homeo_torus (ha : a ≠ 0) (hb : b ≠ 0) (hc0 : 0 < c)
    (hc : |epsAB a b| / 2 + √c < 1 / 2) :
    ∃ h : Circle × Circle ≃ₜ {x : Space // x ∈ U a b ∧ psi a b x = c},
      ∀ p, (h p : Space) = torusMap a b c p.1 p.2 := by
  let f : Circle × Circle → {x : Space // x ∈ U a b ∧ psi a b x = c} := fun p =>
    ⟨torusMap a b c p.1 p.2, torusMap_mem ha hb hc (Circle.norm_coe p.1) (Circle.norm_coe p.2),
      psi_torusMap ha hb hc0.le hc (Circle.norm_coe p.1) (Circle.norm_coe p.2)⟩
  have hf : Continuous f := (continuous_torusMap hc).subtype_mk _
  have hbij : Function.Bijective f := by
    constructor
    · intro p q hpq
      have h := congrArg Subtype.val hpq
      obtain ⟨e2, e1⟩ := torusMap_inj ha hb hc (Circle.norm_coe p.1) (Circle.norm_coe p.2)
        (Circle.norm_coe q.1) (Circle.norm_coe q.2) h
      have hs : ((√c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hc0).ne'
      exact Prod.ext (Circle.ext (mul_left_cancel₀ hs e1)) (Circle.ext e2)
    · rintro ⟨x, hx, hψ⟩
      obtain ⟨z₁, hz₁, he⟩ := torusMap_surj ha hb hc0 hx hψ
      refine ⟨(⟨z₁, mem_sphere_zero_iff_norm.2 hz₁⟩,
        ⟨Z2 a b x, mem_sphere_zero_iff_norm.2 (norm_Z2 hx)⟩), ?_⟩
      exact Subtype.ext he
  exact ⟨hf.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hbij), fun p => rfl⟩

/-- **The degenerate surface `ψ = 0` is a circle** (the magnetic axis): `z ↦ torusMap a b 0 1 z`
is a homeomorphism from `S¹` onto `{x ∈ 𝒰 | ψ x = 0}`. -/
theorem axisSet_homeo_circle (ha : a ≠ 0) (hb : b ≠ 0) (hε : |epsAB a b| < 1) :
    ∃ h : Circle ≃ₜ {x : Space // x ∈ U a b ∧ psi a b x = 0},
      ∀ z, (h z : Space) = torusMap a b 0 1 z := by
  have hc : |epsAB a b| / 2 + √0 < 1 / 2 := by rw [Real.sqrt_zero]; linarith
  have h1 : ‖(1 : ℂ)‖ = 1 := by simp
  let f : Circle → {x : Space // x ∈ U a b ∧ psi a b x = 0} := fun z =>
    ⟨torusMap a b 0 1 z, torusMap_mem ha hb hc h1 (Circle.norm_coe z),
      psi_torusMap ha hb le_rfl hc h1 (Circle.norm_coe z)⟩
  have hf : Continuous f := by
    have := (continuous_torusMap (a := a) (b := b) hc).comp
      (show Continuous fun z : Circle => ((1 : Circle), z) by fun_prop)
    exact this.subtype_mk _
  have hbij : Function.Bijective f := by
    constructor
    · intro p q hpq
      have h := congrArg Subtype.val hpq
      exact Circle.ext (torusMap_inj ha hb hc h1 (Circle.norm_coe p) h1 (Circle.norm_coe q) h).1
    · rintro ⟨x, hx, hψ⟩
      exact ⟨⟨Z2 a b x, mem_sphere_zero_iff_norm.2 (norm_Z2 hx)⟩,
        Subtype.ext (torusMap_surj_zero ha hb hx hψ 1)⟩
  exact ⟨hf.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hbij), fun z => rfl⟩

/-- `ψ` is continuous on `𝒰`. -/
theorem continuousOn_psi (a b : ℝ) : ContinuousOn (psi a b) (U a b) :=
  (contDiffOn_psi a b).continuousOn

/-- **Compact sublevel sets.** For `|ε| < 1` and `c < (1 - |ε|)²/4` the plasma region
`{x ∈ 𝒰 | ψ x ≤ c}` is compact. -/
theorem isCompact_sublevel (ha : a ≠ 0) (hb : b ≠ 0) (hε : |epsAB a b| < 1)
    (hc : c < (1 - |epsAB a b|) ^ 2 / 4) : IsCompact {x | x ∈ U a b ∧ psi a b x ≤ c} := by
  set r₁ := 1 - (|epsAB a b| + 2 * √c) ^ 2
  have hr₁ : 0 < r₁ := shell_pos hε hc
  have hset : {x | x ∈ U a b ∧ psi a b x ≤ c} = {x | r₁ ≤ rad a b x} ∩ psi a b ⁻¹' Set.Iic c := by
    ext x
    constructor
    · rintro ⟨hx, hψ⟩; exact ⟨rad_lower ha hb hx hψ, hψ⟩
    · rintro ⟨hx, hψ⟩
      exact ⟨show 0 < rad a b x by linarith [show r₁ ≤ rad a b x from hx], hψ⟩
  have hsub : {x | r₁ ≤ rad a b x} ⊆ U a b := fun x hx =>
    show 0 < rad a b x by linarith [show r₁ ≤ rad a b x from hx]
  have hcl : IsClosed ({x | r₁ ≤ rad a b x} ∩ psi a b ⁻¹' Set.Iic c) :=
    ((continuousOn_psi a b).mono hsub).preimage_isClosed_of_isClosed
      (isClosed_le continuous_const (continuous_rad a b)) isClosed_Iic
  rw [hset]
  refine Metric.isCompact_of_isClosed_isBounded hcl ?_
  rw [isBounded_iff_forall_norm_le]
  refine ⟨√(2 * a ^ 2 + 2 * b ^ 2 + 1), fun x hx => ?_⟩
  have hU : x ∈ U a b := hsub hx.1
  obtain ⟨hs0, hs2, hz⟩ := U_bounded hU
  have h0 : x 0 ^ 2 ≤ 2 * a ^ 2 := by
    have : x 0 ^ 2 / a ^ 2 < 2 := by
      unfold sF at hs2; nlinarith [div_nonneg (sq_nonneg (x 1)) (sq_nonneg b)]
    rw [div_lt_iff₀ (by positivity)] at this; linarith
  have h1 : x 1 ^ 2 ≤ 2 * b ^ 2 := by
    have : x 1 ^ 2 / b ^ 2 < 2 := by
      unfold sF at hs2; nlinarith [div_nonneg (sq_nonneg (x 0)) (sq_nonneg a)]
    rw [div_lt_iff₀ (by positivity)] at this; linarith
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  apply Real.sqrt_le_sqrt
  simp only [Real.norm_eq_abs, sq_abs]
  nlinarith

end Topology

/-! ## No continuous Euclidean symmetry -/

/-- The Killing field `K x = r × x + t` of `ℝ³` (rotation generator `r`, translation `t`). -/
@[expose] def killing (r t x : Space) : Space := cross r x + t

/-- `DK = r × ·`. -/
theorem killing_hasFDerivAt (r t x : Space) :
    HasFDerivAt (killing r t) (crossBilinear r) x := by
  have := ((crossBilinear r).hasFDerivAt (x := x)).add_const t
  exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by
    simp [killing, crossBilinear_apply])

/-- The Lie derivative `L_K B = [K, B] = (DB) K - (DK) B = (DB)(r × x + t) - r × B` of a vector
field `B` along the Killing field `K`. `B` is invariant under the isometry flow of `K` iff this
vanishes. -/
@[expose] def lieKilling (B : Space → Space) (r t x : Space) : Space :=
  fderiv ℝ B x (killing r t x) - cross r (B x)

section Symmetry
variable {ε : ℝ}

/-- The axis point at `ζ = 0`. -/
theorem axis_zero : axis ε 0 = toLp 2 ![aE ε * bE ε, 0, 0] := by
  apply space_ext <;> simp [axis]

/-- The axis point at `ζ = π/2`. -/
theorem axis_pi_div_two : axis ε (Real.pi / 2) = toLp 2 ![0, aE ε * bE ε, 0] := by
  apply space_ext <;> simp [axis, show 2 * (Real.pi / 2) = Real.pi by ring]

/-- Coordinates of a cross product, as rewrite rules. -/
theorem cross_apply_coords (u v : Space) :
    cross u v 0 = u 1 * v 2 - u 2 * v 1 ∧ cross u v 1 = u 2 * v 0 - u 0 * v 2 ∧
    cross u v 2 = u 0 * v 1 - u 1 * v 0 := cross_coords u v

/-- `L_K B = 0` at the axis point `ζ = 0`, `(ab, 0, 0)`, forces `r₀ = t₀ = 0` and one linear
relation between `r₁, r₂, t₁, t₂`. -/
theorem lie_axis_zero (hε : |ε| < 1) (r t : Space)
    (h : lieKilling (field (aE ε) (bE ε)) r t (axis ε 0) = 0) :
    r 0 = 0 ∧ t 0 = 0 ∧
      aE ε * (2 * bE ε * (-(aE ε * bE ε * r 1) + t 2) - aE ε * (aE ε * bE ε * r 2 + t 1)) =
        bE ε ^ 2 * (ε * r 1 - aE ε * bE ε * r 2) := by
  have hA := aE_sq hε
  have hB := bE_sq hε
  have ha := (aE_pos hε).ne'
  have hb := (bE_pos hε).ne'
  have hm := axis_mem hε 0
  have hF := Fr_axis hε 0
  have hs := sF_axis hε 0
  rw [axis_zero] at hm hF hs
  rw [show 1 + ε - 2 * ε * Real.cos 0 ^ 2 = bE ε ^ 2 by rw [hB]; simp; ring] at hs
  rw [lieKilling, axis_zero, (field_hasFDerivAt _ _ _ hm).fderiv, sub_eq_zero] at h
  obtain ⟨e0, e1, e2⟩ := fieldDeriv_apply (aE ε) (bE ε) (toLp 2 ![aE ε * bE ε, 0, 0])
    (killing r t (toLp 2 ![aE ε * bE ε, 0, 0]))
  have h0 := congrArg (· 0) h
  have h1 := congrArg (· 1) h
  have h2 := congrArg (· 2) h
  simp only at h0 h1 h2
  rw [e0] at h0
  rw [e1] at h1
  rw [e2] at h2
  have c0 := fun u v => (cross_apply_coords u v).1
  have c1 := fun u v => (cross_apply_coords u v).2.1
  have c2 := fun u v => (cross_apply_coords u v).2.2
  simp only [killing, dQuot, dN0, dN1, dFr, drad, dsF, N0, N1, hF, hs, field] at h0 h1 h2
  simp only [Fin.isValue, Matrix.cons_val, mul_zero, zero_smul, Matrix.cons_val_zero, zero_add,
    Matrix.cons_val_one, one_div, mul_inv_rev, zero_div, add_zero, sub_zero, zero_mul, sub_self,
    smul_apply, sub_apply, PiLp.proj_apply, PiLp.add_apply, c2, zero_sub, smul_eq_mul, c1,
    Nat.succ_eq_add_one, Nat.reduceAdd, c0, smul_add, add_apply] at h0 h1 h2
  have hpos : 0 < aE ε ^ 2 * (2 - bE ε ^ 2) := by rw [hA, hB]; nlinarith [abs_lt.mp hε]
  generalize aE ε = A at *
  generalize bE ε = B at *
  have hε' : ε = 1 - B ^ 2 := by linarith
  subst hε'
  field_simp at h0 h1 h2
  have hr0 : r 0 * (A ^ 2 * (2 - B ^ 2)) = 0 := by
    linear_combination 2 * h1 - B ^ 2 * h2 + 2 * t 0 * hA
  have hr0' : r 0 = 0 := (mul_eq_zero.mp hr0).resolve_right hpos.ne'
  refine ⟨hr0', ?_, by linear_combination h0⟩
  rw [hr0'] at h2
  linarith

/-- `L_K B = 0` at the axis point `ζ = π/2`, `(0, ab, 0)`, forces `r₁ = t₁ = 0` and one linear
relation between `r₀, r₂, t₀, t₂`. -/
theorem lie_axis_pi_div_two (hε : |ε| < 1) (r t : Space)
    (h : lieKilling (field (aE ε) (bE ε)) r t (axis ε (Real.pi / 2)) = 0) :
    r 1 = 0 ∧ t 1 = 0 ∧
      bE ε * (2 * aE ε * (aE ε * bE ε * r 0 + t 2) + bE ε * (-(aE ε * bE ε * r 2) + t 0)) =
        aE ε ^ 2 * (-(aE ε * bE ε * r 2) + ε * r 0) := by
  have hA := aE_sq hε
  have hB := bE_sq hε
  have ha := (aE_pos hε).ne'
  have hb := (bE_pos hε).ne'
  have hm := axis_mem hε (Real.pi / 2)
  have hF := Fr_axis hε (Real.pi / 2)
  have hs := sF_axis hε (Real.pi / 2)
  rw [axis_pi_div_two] at hm hF hs
  rw [show 1 + ε - 2 * ε * Real.cos (Real.pi / 2) ^ 2 = aE ε ^ 2 by rw [hA]; simp] at hs
  rw [lieKilling, axis_pi_div_two, (field_hasFDerivAt _ _ _ hm).fderiv, sub_eq_zero] at h
  obtain ⟨e0, e1, e2⟩ := fieldDeriv_apply (aE ε) (bE ε) (toLp 2 ![0, aE ε * bE ε, 0])
    (killing r t (toLp 2 ![0, aE ε * bE ε, 0]))
  have h0 := congrArg (· 0) h
  have h1 := congrArg (· 1) h
  have h2 := congrArg (· 2) h
  simp only at h0 h1 h2
  rw [e0] at h0
  rw [e1] at h1
  rw [e2] at h2
  have c0 := fun u v => (cross_apply_coords u v).1
  have c1 := fun u v => (cross_apply_coords u v).2.1
  have c2 := fun u v => (cross_apply_coords u v).2.2
  simp only [killing, dQuot, dN0, dN1, dFr, drad, dsF, N0, N1, hF, hs, field] at h0 h1 h2
  simp only [Fin.isValue, Matrix.cons_val, mul_zero, zero_smul, Matrix.cons_val_zero, add_zero,
    Matrix.cons_val_one, one_div, mul_inv_rev, zero_div, zero_add, sub_zero, smul_add, zero_sub,
    neg_add_rev, smul_neg, sub_apply, add_apply, neg_apply, smul_apply, PiLp.proj_apply,
    PiLp.add_apply, c1, sub_self, smul_eq_mul, Nat.succ_eq_add_one, Nat.reduceAdd, zero_mul, c0, c2,
    neg_inj] at h0 h1 h2
  have hpos : 0 < bE ε ^ 2 * (2 - aE ε ^ 2) := by rw [hA, hB]; nlinarith [abs_lt.mp hε]
  generalize aE ε = A at *
  generalize bE ε = B at *
  have hε' : ε = A ^ 2 - 1 := by linarith
  subst hε'
  field_simp at h0 h1 h2
  have hr1 : r 1 * (B ^ 2 * (2 - A ^ 2)) = 0 := by
    linear_combination -2 * h0 + A ^ 2 * h2 + 2 * t 1 * hB
  have hr1' : r 1 = 0 := (mul_eq_zero.mp hr1).resolve_right hpos.ne'
  refine ⟨hr1', ?_, by linear_combination h1⟩
  rw [hr1'] at h2
  linarith

/-- **No continuous Euclidean symmetry (pointwise form).** For `|ε| < 1`, `ε ≠ 0`, if the Lie
derivative of the field along the Killing field `K x = r × x + t` vanishes at the two axis
points `ζ = 0` and `ζ = π/2`, then `r = t = 0`. -/
theorem killing_trivial_of_axis (hε : |ε| < 1) (h0 : ε ≠ 0) (r t : Space)
    (hz : lieKilling (field (aE ε) (bE ε)) r t (axis ε 0) = 0)
    (hp : lieKilling (field (aE ε) (bE ε)) r t (axis ε (Real.pi / 2)) = 0) :
    r = 0 ∧ t = 0 := by
  obtain ⟨r0, t0, E0⟩ := lie_axis_zero hε r t hz
  obtain ⟨r1, t1, E1⟩ := lie_axis_pi_div_two hε r t hp
  have hA := aE_sq hε
  have hB := bE_sq hε
  have hab : aE ε * bE ε ≠ 0 := (mul_pos (aE_pos hε) (bE_pos hε)).ne'
  rw [r1, t1] at E0
  rw [r0, t0] at E1
  have k0 : aE ε * bE ε * (2 * t 2 - 2 * ε * r 2) = 0 := by
    linear_combination E0 + aE ε * bE ε * r 2 * hA - aE ε * bE ε * r 2 * hB
  have k1 : aE ε * bE ε * (2 * t 2 + 2 * ε * r 2) = 0 := by
    linear_combination E1 - aE ε * bE ε * r 2 * hA + aE ε * bE ε * r 2 * hB
  have k0' := (mul_eq_zero.mp k0).resolve_left hab
  have k1' := (mul_eq_zero.mp k1).resolve_left hab
  have hr2 : ε * r 2 = 0 := by linarith
  have r2 : r 2 = 0 := (mul_eq_zero.mp hr2).resolve_left h0
  have t2 : t 2 = 0 := by rw [r2] at k0'; linarith
  exact ⟨(space_eq_zero_iff r).mpr ⟨r0, r1, r2⟩, (space_eq_zero_iff t).mpr ⟨t0, t1, t2⟩⟩

end Symmetry

/-- The unit vector `e_z`. -/
@[expose] def ez : Space := toLp 2 ![0, 0, 1]

/-- **Sanity (contrast): the axisymmetric limit `ε = 0` (`a = b = 1`) has a continuous
symmetry.** The rotation generator `K = e_z × x` about the `z`-axis satisfies `L_K B = 0` at
every point of `𝒰`; so the hypothesis `ε ≠ 0` in `killing_trivial_of_axis` is needed. -/
theorem axisymmetric_limit_lie_zero {x : Space} (hx : x ∈ U 1 1) :
    lieKilling (field 1 1) ez 0 x = 0 := by
  have hs := (sF_pos hx).ne'
  have hF : Fr 1 1 x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  rw [lieKilling, (field_hasFDerivAt _ _ _ hx).fderiv, sub_eq_zero]
  obtain ⟨e0, e1, e2⟩ := fieldDeriv_apply 1 1 x (killing ez 0 x)
  have c0 := fun u v => (cross_apply_coords u v).1
  have c1 := fun u v => (cross_apply_coords u v).2.1
  have c2 := fun u v => (cross_apply_coords u v).2.2
  apply space_ext
  · rw [e0]
    simp only [killing, dQuot, dN0, dFr, drad, dsF, N0, N1, field]
    simp [c0, c1, c2, ez]
    field_simp
    ring
  · rw [e1]
    simp only [killing, dQuot, dN1, dFr, drad, dsF, N0, N1, field]
    simp [c0, c1, c2, ez]
    field_simp
    ring
  · rw [e2]
    simp [killing, dsF, c0, c1, c2, ez, field]
    ring

/-- `e_z ≠ 0`. -/
theorem ez_ne_zero : ez ≠ 0 := by
  intro h
  have := congrArg (· 2) h
  simp [ez] at this

/-! ## The Grad counterexample -/

/-- If `f` has Fréchet derivative `⟪v, ·⟫` at `x`, its Mathlib gradient there is `v` (the same
statement as `ForceBalanceGradient.gradient_eq_of_hasFDerivAt`, repeated here so that this
module does not import the heavy family-2 certificate chain behind that file). -/
theorem gradient_eq_of_hasFDerivAt' {f : Space → ℝ} {v x : Space}
    (h : HasFDerivAt f (innerSL ℝ v) x) : gradient f x = v := by
  refine HasGradientAt.gradient ?_
  rw [hasGradientAt_iff_hasFDerivAt]
  have e : InnerProductSpace.toDual ℝ Space v = innerSL ℝ v := by
    ext w; simp [InnerProductSpace.toDual_apply_apply]
  rw [e]
  exact h

/-- The plasma domain `Ω_δ = {x ∈ 𝒰 | ψ x ≤ δ}`. -/
@[expose] def plasma (a b δ : ℝ) : Set Space := {x | x ∈ U a b ∧ psi a b x ≤ δ}

/-- **Landreman family 1 is a smooth non-symmetric toroidal MHS equilibrium with nested flux
surfaces and non-constant pressure (a Grad counterexample).** For `0 < ε < 1`,
`0 < δ < (1 - ε)²/4`, `μ₀ > 0`, with `a = √(1+ε)`, `b = √(1-ε)`, pressure
`p = (2δ - 2ψ)/μ₀` and plasma domain `Ω_δ = {x ∈ 𝒰 | ψ x ≤ δ}`:

1. **Smoothness.** `𝒰 ⊇ Ω_δ` is open and the field `B`, the Ampère current `J = (∇ × B)/μ₀`
   and `p` are `C^∞` on `𝒰`.
2. **MHS equations.** On `𝒰`: `∇ · B = 0` and `J × B = ∇p` with `∇p` Mathlib's `gradient` of
   the explicit `p`.
3. **Nested toroidal flux surfaces.** `ψ` is a first integral (`B · ∇ψ = 0`) and `ψ ≥ 0` on
   `𝒰`; every sublevel set `{x ∈ 𝒰 | ψ x ≤ c}`, `c ≤ δ`, is compact and they increase with `c`
   (`Ω_δ` is the largest); for each `0 < c ≤ δ` the level set `{x ∈ 𝒰 | ψ x = c}` is
   homeomorphic to `S¹ × S¹` via the explicit map `torusMap`; the level set `ψ = 0` is
   homeomorphic to `S¹` and contains the magnetic axis.
4. **Non-constant pressure** on `Ω_δ`.
5. **No continuous Euclidean symmetry.** For every Killing field `K x = r × x + t` of `ℝ³` other
   than `0` (rotations, translations, and their combinations: axial and helical generators)
   there is a point of `Ω_δ` (on the magnetic axis) where `L_K B ≠ 0`. -/
theorem family1_grad_counterexample {ε δ μ₀ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ)
    (hδ : δ < (1 - ε) ^ 2 / 4) (hμ : 0 < μ₀) :
    -- 1. smoothness
    (IsOpen (U (aE ε) (bE ε)) ∧ plasma (aE ε) (bE ε) δ ⊆ U (aE ε) (bE ε) ∧
      ContDiffOn ℝ ∞ (field (aE ε) (bE ε)) (U (aE ε) (bE ε)) ∧
      ContDiffOn ℝ ∞ (current μ₀ (aE ε) (bE ε)) (U (aE ε) (bE ε)) ∧
      ContDiffOn ℝ ∞ (pressure μ₀ (2 * δ) (aE ε) (bE ε)) (U (aE ε) (bE ε))) ∧
    -- 2. `∇ · B = 0` and `J × B = ∇p`
    (∀ x ∈ U (aE ε) (bE ε), divergence (fderiv ℝ (field (aE ε) (bE ε)) x) = 0 ∧
      ForceBalance (ofLp (field (aE ε) (bE ε) x)) (ofLp (current μ₀ (aE ε) (bE ε) x))
        (ofLp (gradient (pressure μ₀ (2 * δ) (aE ε) (bE ε)) x))) ∧
    -- 3. nested toroidal flux surfaces
    (FirstIntegralOn (field (aE ε) (bE ε)) (psi (aE ε) (bE ε)) (U (aE ε) (bE ε)) ∧
      (∀ x ∈ U (aE ε) (bE ε), 0 ≤ psi (aE ε) (bE ε) x) ∧
      (∀ c c', c ≤ c' → c' ≤ δ → IsCompact (plasma (aE ε) (bE ε) c) ∧
        plasma (aE ε) (bE ε) c ⊆ plasma (aE ε) (bE ε) c') ∧
      (∀ c, 0 < c → c ≤ δ →
        ∃ h : Circle × Circle ≃ₜ {x : Space // x ∈ U (aE ε) (bE ε) ∧ psi (aE ε) (bE ε) x = c},
          ∀ p, (h p : Space) = torusMap (aE ε) (bE ε) c p.1 p.2) ∧
      (∃ h : Circle ≃ₜ {x : Space // x ∈ U (aE ε) (bE ε) ∧ psi (aE ε) (bE ε) x = 0},
          ∀ z, (h z : Space) = torusMap (aE ε) (bE ε) 0 1 z) ∧
      (∀ ζ, axis ε ζ ∈ plasma (aE ε) (bE ε) δ ∧ psi (aE ε) (bE ε) (axis ε ζ) = 0)) ∧
    -- 4. non-constant pressure
    (∃ x ∈ plasma (aE ε) (bE ε) δ, ∃ y ∈ plasma (aE ε) (bE ε) δ,
      pressure μ₀ (2 * δ) (aE ε) (bE ε) x ≠ pressure μ₀ (2 * δ) (aE ε) (bE ε) y) ∧
    -- 5. no continuous Euclidean symmetry
    (∀ r t : Space, (r ≠ 0 ∨ t ≠ 0) →
      ∃ x ∈ plasma (aE ε) (bE ε) δ, lieKilling (field (aE ε) (bE ε)) r t x ≠ 0) := by
  have hε : |ε| < 1 := by rw [abs_of_pos hε0]; exact hε1
  have ha := (aE_pos hε).ne'
  have hb := (bE_pos hε).ne'
  have hE : epsAB (aE ε) (bE ε) = ε := epsAB_eq hε
  have hεE : |epsAB (aE ε) (bE ε)| < 1 := by rwa [hE]
  have hcE (c : ℝ) (hc : c ≤ δ) : c < (1 - |epsAB (aE ε) (bE ε)|) ^ 2 / 4 := by
    rw [hE, abs_of_pos hε0]; linarith
  have haxis (ζ : ℝ) : axis ε ζ ∈ plasma (aE ε) (bE ε) δ ∧ psi (aE ε) (bE ε) (axis ε ζ) = 0 :=
    ⟨⟨axis_mem hε ζ, by rw [psi_axis hε]; exact hδ0.le⟩, psi_axis hε ζ⟩
  refine ⟨⟨isOpen_U _ _, fun x hx => hx.1, contDiffOn_field _ _, contDiffOn_current _ _ _,
    contDiffOn_pressure _ _ _ _⟩, fun x hx => ⟨field_divergence_free ha hb hx, ?_⟩,
    ⟨psi_firstIntegral ha hb, fun x hx => psi_nonneg ha hb hx, fun c c' hcc' hc' =>
      ⟨isCompact_sublevel ha hb hεE (hcE c (hcc'.trans hc')),
        fun x hx => ⟨hx.1, hx.2.trans hcc'⟩⟩,
      fun c hc0 hc => fluxSurface_homeo_torus ha hb hc0 (shell_of_lt hεE (hcE c hc)),
      axisSet_homeo_circle ha hb hεE, haxis⟩, ?_, ?_⟩
  · rw [gradient_eq_of_hasFDerivAt' (pressure_hasFDerivAt μ₀ (2 * δ) _ _ hx)]
    exact force_balance ha hb μ₀ hx
  · -- the axis (`p = 2δ/μ₀`) and a point of the boundary torus `ψ = δ` (`p = 0`)
    have hsh := shell_of_lt hεE (hcE δ le_rfl)
    have h1 : ‖(1 : ℂ)‖ = 1 := by simp
    refine ⟨axis ε 0, (haxis 0).1, torusMap (aE ε) (bE ε) δ 1 1,
      ⟨torusMap_mem ha hb hsh h1 h1, (psi_torusMap ha hb hδ0.le hsh h1 h1).le⟩, ?_⟩
    rw [pressure_axis hε, pressure_boundary (psi_torusMap ha hb hδ0.le hsh h1 h1)]
    positivity
  · intro r t hrt
    by_contra hall
    push Not at hall
    obtain ⟨hr, ht⟩ := killing_trivial_of_axis hε hε0.ne' r t (hall _ (haxis 0).1)
      (hall _ (haxis _).1)
    rcases hrt with h | h <;> contradiction

end PlasmaLean.Design.LandremanGradCounterexample
