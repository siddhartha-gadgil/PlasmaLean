/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamTorusA
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Toroidal coordinates about the exact axis and the rational stellarator field in them

Infrastructure for `Design/RationalStellaratorForever` (all-time confinement from an exact
invariant torus near torus A).

**Toroidal coordinates.** `torPt r α φ` is the point with cylindrical coordinates
`R = 1 + r cos α`, `z = r sin α`, toroidal angle `φ` (`cylPt`). For `0 < r < 1/2` the functions
`rt`, `θs`, `φs` of `Design/RationalStellarator` and `Theory/Fields/TorusTrapping` recover
`r`, `α`, `φ` (the angles modulo `2π`: `rt_torPt`, `θs_torPt`, `φs_torPt`), and every point of
the tube off the axis is of this form (`eq_torPt`).

**The field.** In cylindrical coordinates `B = B^R e_R + R B^φ e_φ + B^z e_z` with
`B^R = 2ε Ps / R³`, `B^z = ε Pz / R²`, `B^φ = D / R⁴` (`field_cylPt`; `Ps, Pz, D` the polynomials
of `Design/KamTorusA`). In toroidal coordinates `B = d/dt torPt (r + t v_r, α + t v_α, φ + t v_φ)`
with the explicit smooth components `v_r = cos α B^R + sin α B^z`,
`v_α = (cos α B^z − sin α B^R)/r`, `v_φ = B^φ` (`vRad`, `vPol`, `vTor`, `field_torPt`).

**The invariance defect in coordinates.** For a torus profile `ρ` and `G = rt − ρ(θs, φs)`,
`DG · B = v_r − Dρ(α, φ) · (v_α, v_φ)` at `torPt r α φ` (`fderiv_G_field_torPt`): the dependence on
`r` at fixed angles enters only through the smooth components `v`, which are Lipschitz in `r` on a
compact collar (`exists_lipschitz_W`).

**Angle lift.** `angF θ a b = θ + arctan (Im w / Re w)`, `w = (a + i b) e^{−iθ}`, is a smooth
polar angle of `(a, b)` where `Re w > 0` (`angF_polar`), with derivative
`(a b' − b a') / (a² + b²)` along any curve (`hasDerivAt_angF`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamTorusA

open Real Set Filter Topology PlasmaLean.Fields PlasmaLean.Design.RationalStellarator

/-! ## Points in cylindrical and toroidal coordinates -/

/-- The point with cylindrical coordinates `(R, φ, z)`. -/
def cylPt (R φ z : ℝ) : Space := WithLp.toLp 2 ![R * cos φ, R * sin φ, z]

/-- The point with toroidal coordinates `(r, α, φ)` about the axis `R = 1, z = 0`. -/
def torPt (r α φ : ℝ) : Space := cylPt (1 + r * cos α) φ (r * sin α)

/-- `r₂` of a cylindrical point. -/
theorem r2_cylPt (R φ z : ℝ) : r2 (cylPt R φ z) = R ^ 2 := by
  simp only [r2, cylPt]; simp; linear_combination R ^ 2 * cos_sq_add_sin_sq φ

/-- `Rc` of a cylindrical point with `R ≥ 0`. -/
theorem Rc_cylPt {R : ℝ} (hR : 0 ≤ R) (φ z : ℝ) : Rc (cylPt R φ z) = R := by
  rw [Rc, r2_cylPt, Real.sqrt_sq hR]

/-- The height of a cylindrical point. -/
theorem cylPt_two (R φ z : ℝ) : cylPt R φ z 2 = z := by simp [cylPt]

/-- `rt (torPt r α φ) = r` for `0 ≤ r ≤ 1`. -/
theorem rt_torPt {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (α φ : ℝ) : rt (torPt r α φ) = r := by
  have hR : 0 ≤ 1 + r * cos α := by nlinarith [neg_one_le_cos α]
  rw [torPt, rt, Rc_cylPt hR, cylPt_two]
  rw [show (1 + r * cos α - 1) ^ 2 + (r * sin α) ^ 2 = r ^ 2 by
    linear_combination r ^ 2 * cos_sq_add_sin_sq α]
  exact Real.sqrt_sq hr

/-- `arg (r e^{iα}) = α` modulo `2π` for `r > 0`. -/
theorem arg_polar {r : ℝ} (hr : 0 < r) (α : ℝ) :
    ∃ k : ℤ, Complex.arg (((r * cos α : ℝ) : ℂ) + ((r * sin α : ℝ) : ℂ) * Complex.I) =
      α + 2 * π * k := by
  have e : (((r * cos α : ℝ) : ℂ) + ((r * sin α : ℝ) : ℂ) * Complex.I) =
      (r : ℂ) * Complex.exp ((α : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]; push_cast; ring
  rw [e, Complex.arg_real_mul _ hr, Complex.arg_exp_mul_I, ← self_sub_toIocDiv_zsmul]
  refine ⟨-toIocDiv two_pi_pos (-π) α, ?_⟩
  rw [zsmul_eq_mul]; push_cast; ring

/-- `θs (torPt r α φ) = α` modulo `2π` for `0 < r ≤ 1`. -/
theorem θs_torPt {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (α φ : ℝ) :
    ∃ k : ℤ, θs (torPt r α φ) = α + 2 * π * k := by
  have hR : 0 ≤ 1 + r * cos α := by nlinarith [neg_one_le_cos α]
  rw [θs, wθ, torPt, Rc_cylPt hR, cylPt_two, add_sub_cancel_left]
  exact arg_polar hr α

/-- `φs (torPt r α φ) = φ` modulo `2π` for `0 ≤ r < 1`. -/
theorem φs_torPt {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (α φ : ℝ) :
    ∃ k : ℤ, φs (torPt r α φ) = φ + 2 * π * k := by
  have hR : 0 < 1 + r * cos α := by nlinarith [neg_one_le_cos α]
  have e0 : torPt r α φ 0 = (1 + r * cos α) * cos φ := by simp [torPt, cylPt]
  have e1 : torPt r α φ 1 = (1 + r * cos α) * sin φ := by simp [torPt, cylPt]
  rw [φs, wφ, e0, e1]
  exact arg_polar hR φ

/-- Every point of the tube off the axis is `torPt (rt y) (θs y) (φs y)`. -/
theorem eq_torPt {y : Space} (hy : rt y < 1 / 2) :
    y = torPt (rt y) (θs y) (φs y) := by
  have hr2 := r2_pos_of_rt_lt hy
  have hRc : Rc y = √(y 0 ^ 2 + y 1 ^ 2) := rfl
  have hθ1 := Complex.norm_mul_cos_arg (wθ y)
  have hθ2 := Complex.norm_mul_sin_arg (wθ y)
  have hφ1 := Complex.norm_mul_cos_arg (wφ y)
  have hφ2 := Complex.norm_mul_sin_arg (wφ y)
  have nθ : ‖wθ y‖ = rt y := by rw [wθ, Complex.norm_add_mul_I]; rfl
  have nφ : ‖wφ y‖ = Rc y := by rw [wφ, Complex.norm_add_mul_I]; rfl
  simp only [wθ, wφ, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im] at hθ1 hθ2 hφ1 hφ2
  rw [← wθ, nθ] at hθ1 hθ2
  rw [← wφ, nφ] at hφ1 hφ2
  simp only [mul_zero, sub_zero, mul_one, zero_add, add_zero] at hθ1 hθ2 hφ1 hφ2
  ext i
  fin_cases i
  · simp only [torPt, cylPt, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [← θs, ← φs] at *; linear_combination -hφ1 - cos (φs y) * hθ1
  · simp only [torPt, cylPt, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [← θs, ← φs] at *; linear_combination -hφ2 - sin (φs y) * hθ1
  · simp only [torPt, cylPt, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    rw [← θs] at *; linear_combination -hθ2

/-! ## The field in cylindrical and toroidal coordinates -/

/-- `B^R = ε ∂_R h = 2ε Ps / R³` (with `C = cos 2φ`, `S = sin 2φ`). -/
def cylBR (R z C S : ℝ) : ℝ := 2 * eps * Psfun R z C S / R ^ 3

/-- `B^z = ε ∂_z h = ε Pz / R²`. -/
def cylBZ (R z C S : ℝ) : ℝ := eps * Pzfun R z C S / R ^ 2

/-- `B^φ = (1 + ε ∂_φ h) / R² = D / R⁴`. -/
def cylBT (R z C S : ℝ) : ℝ := Dfun R z C S / R ^ 4

/-- **The rational stellarator field in cylindrical coordinates**:
`B = B^R e_R + R B^φ e_φ + B^z e_z`. -/
theorem field_cylPt {R : ℝ} (hR : 0 < R) (φ z : ℝ) :
    field (1 / 4) (cylPt R φ z) = WithLp.toLp 2
      ![cylBR R z (cos (2 * φ)) (sin (2 * φ)) * cos φ -
          R * cylBT R z (cos (2 * φ)) (sin (2 * φ)) * sin φ,
        cylBR R z (cos (2 * φ)) (sin (2 * φ)) * sin φ +
          R * cylBT R z (cos (2 * φ)) (sin (2 * φ)) * cos φ,
        cylBZ R z (cos (2 * φ)) (sin (2 * φ))] := by
  have hR0 : R ≠ 0 := hR.ne'
  have hcs := cos_sq_add_sin_sq φ
  have h0 : cylPt R φ z 0 = R * cos φ := by simp [cylPt]
  have h1 : cylPt R φ z 1 = R * sin φ := by simp [cylPt]
  have h2 : cylPt R φ z 2 = z := by simp [cylPt]
  have hr2 := r2_cylPt R φ z
  obtain ⟨f0, f1, f2⟩ := field_apply (1 / 4) (cylPt R φ z)
  rw [cos_two_mul, sin_two_mul]
  generalize cos φ = c at *
  generalize sin φ = s at *
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, f0]
    simp only [G, Hd, winv, hr2, cv, Hnum, Aq, Bq, Xd, Yp, H0, h0, h1, h2]
    simp only [Matrix.cons_val_zero, cylBR, cylBT, Psfun, Dfun, s2fs, s2gs,
      sfun, sgfun, eps]
    field_simp
    grind
  · simp only [Fin.mk_one, Fin.isValue, f1]
    simp only [G, Hd, winv, hr2, cv, Hnum, Aq, Bq, Xd, Yp, H1, h0, h1, h2]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, cylBR, cylBT, Psfun,
      Dfun, s2fs, s2gs, sfun, sgfun, eps]
    field_simp
    grind
  · simp only [Fin.reduceFinMk, Fin.isValue, f2]
    simp only [G, Hd, winv, hr2, cv, Hnum, Aq, Bq, Xd, Yp, H2, h0, h1, h2]
    simp only [Matrix.cons_val, cylBZ, Pzfun, sgz, eps]
    field_simp
    grind

/-- Radial component `v_r = cos α B^R + sin α B^z` of the field in toroidal coordinates
(arguments `c = cos α`, `s = sin α`, `C = cos 2φ`, `S = sin 2φ`). -/
def vRad (r c s C S : ℝ) : ℝ :=
  c * cylBR (1 + r * c) (r * s) C S + s * cylBZ (1 + r * c) (r * s) C S

/-- Poloidal component `v_α = (cos α B^z − sin α B^R) / r`. -/
def vPol (r c s C S : ℝ) : ℝ :=
  (c * cylBZ (1 + r * c) (r * s) C S - s * cylBR (1 + r * c) (r * s) C S) / r

/-- Toroidal component `v_φ = B^φ`. -/
def vTor (r c s C S : ℝ) : ℝ := cylBT (1 + r * c) (r * s) C S

/-- A curve in space is differentiable when its three coordinates are. -/
theorem hasDerivAt_toLp3 {f0 f1 f2 : ℝ → ℝ} {d0 d1 d2 t : ℝ} (h0 : HasDerivAt f0 d0 t)
    (h1 : HasDerivAt f1 d1 t) (h2 : HasDerivAt f2 d2 t) :
    HasDerivAt (fun s => (WithLp.toLp 2 ![f0 s, f1 s, f2 s] : Space))
      (WithLp.toLp 2 ![d0, d1, d2]) t := by
  have h := ((h0.smul_const (basis 0)).add (h1.smul_const (basis 1))).add
    (h2.smul_const (basis 2))
  convert h using 1
  · funext s; ext k; fin_cases k <;> simp [basis]
  · ext k; fin_cases k <;> simp [basis]

/-- Derivative of an affine function `t ↦ a + t b` at `0`. -/
theorem hasDerivAt_affine (a b : ℝ) : HasDerivAt (fun t : ℝ => a + t * b) b 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add a

/-- **The field in toroidal coordinates**: for `0 < r ≤ 1/2`, `B(torPt r α φ)` is the velocity of
`t ↦ torPt (r + t v_r) (α + t v_α) (φ + t v_φ)` at `t = 0`. -/
theorem field_torPt {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 2) (α φ : ℝ) :
    HasDerivAt (fun t => torPt (r + t * vRad r (cos α) (sin α) (cos (2 * φ)) (sin (2 * φ)))
        (α + t * vPol r (cos α) (sin α) (cos (2 * φ)) (sin (2 * φ)))
        (φ + t * vTor r (cos α) (sin α) (cos (2 * φ)) (sin (2 * φ))))
      (field (1 / 4) (torPt r α φ)) 0 := by
  have hR : 0 < 1 + r * cos α := by nlinarith [neg_one_le_cos α]
  set a := vRad r (cos α) (sin α) (cos (2 * φ)) (sin (2 * φ)) with ha
  set b := vPol r (cos α) (sin α) (cos (2 * φ)) (sin (2 * φ)) with hb
  set d := vTor r (cos α) (sin α) (cos (2 * φ)) (sin (2 * φ)) with hd
  have hra := hasDerivAt_affine r a
  have hαb := hasDerivAt_affine α b
  have hφd := hasDerivAt_affine φ d
  have hRt := (hra.mul hαb.cos).const_add 1
  have k0 := hRt.mul hφd.cos
  have k1 := hRt.mul hφd.sin
  have k2 := hra.mul hαb.sin
  have hγ := hasDerivAt_toLp3 k0 k1 k2
  simp only [zero_mul, add_zero] at hγ
  rw [torPt, field_cylPt hR]
  convert hγ using 1
  · rfl
  have hcs := cos_sq_add_sin_sq α
  have hr0 : r ≠ 0 := hr.ne'
  have hBR : a * cos α - r * sin α * b =
      cylBR (1 + r * cos α) (r * sin α) (cos (2 * φ)) (sin (2 * φ)) := by
    rw [ha, hb, vRad, vPol]
    generalize cylBR (1 + r * cos α) (r * sin α) (cos (2 * φ)) (sin (2 * φ)) = BR
    generalize cylBZ (1 + r * cos α) (r * sin α) (cos (2 * φ)) (sin (2 * φ)) = BZ
    field_simp
    linear_combination BR * hcs
  have hBZ : a * sin α + r * cos α * b =
      cylBZ (1 + r * cos α) (r * sin α) (cos (2 * φ)) (sin (2 * φ)) := by
    rw [ha, hb, vRad, vPol]
    generalize cylBR (1 + r * cos α) (r * sin α) (cos (2 * φ)) (sin (2 * φ)) = BR
    generalize cylBZ (1 + r * cos α) (r * sin α) (cos (2 * φ)) (sin (2 * φ)) = BZ
    field_simp
    linear_combination BZ * hcs
  ext k
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Pi.mul_apply,
      zero_mul, add_zero]
    rw [← hBR, hd, vTor]; ring
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_zero, Pi.mul_apply, zero_mul, add_zero]
    rw [← hBR, hd, vTor]; ring
  · simp only [Fin.reduceFinMk, Matrix.cons_val, Pi.mul_apply,
      zero_mul, add_zero]
    rw [← hBZ]; ring

/-! ## The invariance defect `DG · B` in toroidal coordinates -/

/-- **`DG · B` in toroidal coordinates.** For a torus profile `ρ`, `G = rt − ρ(θs, φs)` and
`0 < r < 1/2`: `DG · B = v_r − Dρ(α, φ) · (v_α, v_φ)` at `torPt r α φ`. -/
theorem fderiv_G_field_torPt {ρ : ℝ → ℝ → ℝ} (hρ : TorusProfile ρ) {r : ℝ} (hr : 0 < r)
    (hr1 : r < 1 / 2) (α φ : ℝ) :
    fderiv ℝ (fun x => rt x - ρ (θs x) (φs x)) (torPt r α φ) (field (1 / 4) (torPt r α φ)) =
      vRad r (cos α) (sin α) (cos (2 * φ)) (sin (2 * φ)) -
        fderiv ℝ (fun p : ℝ × ℝ => ρ p.1 p.2) (α, φ)
          (vPol r (cos α) (sin α) (cos (2 * φ)) (sin (2 * φ)),
            vTor r (cos α) (sin α) (cos (2 * φ)) (sin (2 * φ))) := by
  set a := vRad r (cos α) (sin α) (cos (2 * φ)) (sin (2 * φ))
  set b := vPol r (cos α) (sin α) (cos (2 * φ)) (sin (2 * φ))
  set d := vTor r (cos α) (sin α) (cos (2 * φ)) (sin (2 * φ))
  have hrt := rt_torPt hr.le (by linarith) α φ
  have hGd : DifferentiableAt ℝ (fun x => rt x - ρ (θs x) (φs x)) (torPt r α φ) :=
    TubeCoords.differentiableAt_G (c := tube) hρ
      ⟨show rt (torPt r α φ) < 1 / 2 by rw [hrt]; exact hr1,
        show 0 < rt (torPt r α φ) by rw [hrt]; exact hr⟩
  have hγ := field_torPt hr hr1.le α φ
  have h1 := hGd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by simp)
  have hcurve : HasDerivAt (fun t : ℝ => (α + t * b, φ + t * d)) (b, d) 0 :=
    (hasDerivAt_affine α b).prodMk (hasDerivAt_affine φ d)
  have h2 := (hasDerivAt_affine r a).sub
    ((hρ.differentiable (α, φ)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hcurve (by simp))
  refine h1.unique (h2.congr_of_eventuallyEq ?_)
  have hc : ContinuousAt (fun t : ℝ => r + t * a) 0 := (hasDerivAt_affine r a).continuousAt
  filter_upwards [hc.preimage_mem_nhds (Ioo_mem_nhds (a := 0) (b := 1 / 2)
    (by simpa using hr) (by simpa using hr1))] with t ht
  obtain ⟨ht0, ht1⟩ := ht
  simp only [Function.comp_apply]
  rw [rt_torPt ht0.le (by linarith)]
  obtain ⟨k, hk⟩ := θs_torPt ht0 (by linarith) (α + t * b) (φ + t * d)
  obtain ⟨m, hm⟩ := φs_torPt ht0.le (by linarith) (α + t * b) (φ + t * d)
  rw [hk, hm, hρ.shift]
  rfl

/-! ## Calculus lemmas -/

/-- Derivative of a `C¹` function of two variables along the line `(θ + t u, φ + t w)`, in terms
of its partial derivatives. -/
theorem hasDerivAt_line {f : ℝ → ℝ → ℝ} (hf : Differentiable ℝ (fun p : ℝ × ℝ => f p.1 p.2))
    (θ φ u w : ℝ) :
    HasDerivAt (fun t => f (θ + t * u) (φ + t * w))
      (u * deriv (fun θ' => f θ' φ) θ + w * deriv (fun φ' => f θ φ') φ) 0 := by
  set D := fderiv ℝ (fun p : ℝ × ℝ => f p.1 p.2) (θ, φ)
  have hD : HasFDerivAt (fun p : ℝ × ℝ => f p.1 p.2) D (θ, φ) := (hf _).hasFDerivAt
  have h1 : HasDerivAt (fun θ' => f θ' φ) (D (1, 0)) θ :=
    hD.comp_hasDerivAt_of_eq θ (HasDerivAt.prodMk (hasDerivAt_id θ) (hasDerivAt_const θ φ)) rfl
  have h2 : HasDerivAt (fun φ' => f θ φ') (D (0, 1)) φ :=
    hD.comp_hasDerivAt_of_eq φ (HasDerivAt.prodMk (hasDerivAt_const φ θ) (hasDerivAt_id φ)) rfl
  have h3 := hD.comp_hasDerivAt_of_eq (0 : ℝ)
    ((hasDerivAt_affine θ u).prodMk (hasDerivAt_affine φ w)) (by simp)
  rw [h1.deriv, h2.deriv]
  convert h3 using 1
  · rfl
  rw [show ((u, w) : ℝ × ℝ) = u • ((1 : ℝ), (0 : ℝ)) + w • ((0 : ℝ), (1 : ℝ)) by simp,
    map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- A continuous function on `ℝ²`, `2π`-periodic in both variables, is bounded. -/
theorem exists_bound_of_periodic {E : Type*} [NormedAddCommGroup E] {f : ℝ × ℝ → E}
    (hf : Continuous f) (h1 : ∀ a b, f (a + 2 * π, b) = f (a, b))
    (h2 : ∀ a b, f (a, b + 2 * π) = f (a, b)) : ∃ C, ∀ p, ‖f p‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc 0 (2 * π) ×ˢ Icc 0 (2 * π)) hf.continuousOn
  refine ⟨C, fun ⟨a, b⟩ => ?_⟩
  obtain ⟨a', ha', e1⟩ := Function.Periodic.exists_mem_Ico₀ (f := fun a => f (a, b))
    (fun a => h1 a b) two_pi_pos a
  obtain ⟨b', hb', e2⟩ := Function.Periodic.exists_mem_Ico₀ (f := fun b => f (a', b))
    (fun b => h2 a' b) two_pi_pos b
  rw [e1, e2]
  exact hC _ ⟨Ico_subset_Icc_self ha', Ico_subset_Icc_self hb'⟩

/-! ## A smooth polar angle -/

/-- The polar angle `θ + arctan (Im w / Re w)` of `(a, b)`, `w = (a + i b) e^{−iθ}`, a smooth lift
where `Re w = a cos θ + b sin θ > 0`. -/
def angF (θ a b : ℝ) : ℝ := θ + arctan ((b * cos θ - a * sin θ) / (a * cos θ + b * sin θ))

/-- Sanity check: on the ray of direction `θ` the polar angle `angF θ` is `θ` itself. -/
theorem angF_ray (θ r : ℝ) : angF θ (r * cos θ) (r * sin θ) = θ := by
  rw [angF, show r * sin θ * cos θ - r * cos θ * sin θ = 0 by ring, zero_div, arctan_zero,
    add_zero]

/-- `angF θ a b - θ ∈ (−π/2, π/2)`. -/
theorem angF_sub_mem (θ a b : ℝ) : |angF θ a b - θ| < π / 2 := by
  rw [angF, add_sub_cancel_left, abs_lt]
  exact ⟨neg_pi_div_two_lt_arctan _, arctan_lt_pi_div_two _⟩

/-- **`angF` is a polar angle** of `(a, b)` when `a cos θ + b sin θ > 0`. -/
theorem angF_polar {θ a b : ℝ} (h : 0 < a * cos θ + b * sin θ) :
    a = √(a ^ 2 + b ^ 2) * cos (angF θ a b) ∧ b = √(a ^ 2 + b ^ 2) * sin (angF θ a b) := by
  set X := a * cos θ + b * sin θ with hX
  set Y := b * cos θ - a * sin θ with hY
  have hcs := cos_sq_add_sin_sq θ
  have hXY : X ^ 2 + Y ^ 2 = a ^ 2 + b ^ 2 := by
    rw [hX, hY]; linear_combination (a ^ 2 + b ^ 2) * hcs
  have hpos : 0 < a ^ 2 + b ^ 2 := by rw [← hXY]; positivity
  set S := √(a ^ 2 + b ^ 2) with hS
  have hSpos : 0 < S := Real.sqrt_pos.mpr hpos
  have hS2 : S ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt hpos.le
  have hsq : √(1 + (Y / X) ^ 2) = S / X := by
    rw [show 1 + (Y / X) ^ 2 = (S / X) ^ 2 by field_simp; rw [hS2, ← hXY]]
    exact Real.sqrt_sq (by positivity)
  have hc : cos (arctan (Y / X)) = X / S := by
    rw [cos_arctan, hsq]; field_simp
  have hs : sin (arctan (Y / X)) = Y / S := by
    rw [sin_arctan, hsq]; field_simp
  rw [angF, cos_add, sin_add, hc, hs]
  constructor
  · field_simp; rw [hX, hY]; linear_combination (-a) * hcs
  · field_simp; rw [hX, hY]; linear_combination (-b) * hcs

/-- **Derivative of the polar angle** along a curve: `(a b' − b a') / (a² + b²)`. -/
theorem hasDerivAt_angF {θf af bf : ℝ → ℝ} {θ' a' b' t : ℝ} (hθ : HasDerivAt θf θ' t)
    (ha : HasDerivAt af a' t) (hb : HasDerivAt bf b' t)
    (h : 0 < af t * cos (θf t) + bf t * sin (θf t)) :
    HasDerivAt (fun t => angF (θf t) (af t) (bf t))
      ((af t * b' - bf t * a') / (af t ^ 2 + bf t ^ 2)) t := by
  have hX := (ha.mul hθ.cos).add (hb.mul hθ.sin)
  have hY := (hb.mul hθ.cos).sub (ha.mul hθ.sin)
  have hq := (hY.div hX h.ne').arctan
  have hall := hθ.add hq
  convert hall using 1
  · rfl
  simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.div_apply]
  set c := cos (θf t)
  set s := sin (θf t)
  set a := af t
  set b := bf t
  have hcs : c ^ 2 + s ^ 2 = 1 := cos_sq_add_sin_sq _
  have hXY : (a * c + b * s) ^ 2 + (b * c - a * s) ^ 2 = a ^ 2 + b ^ 2 := by
    linear_combination (a ^ 2 + b ^ 2) * hcs
  have hpos : 0 < a ^ 2 + b ^ 2 := by rw [← hXY]; positivity
  have hX0 : a * c + b * s ≠ 0 := h.ne'
  have h1 : 1 + ((b * c - a * s) / (a * c + b * s)) ^ 2 ≠ 0 := by positivity
  field_simp
  grind

/-! ## Lipschitz bound of the defect in the radial variable -/

/-- The defect `v_r − p_α v_α − p_φ v_φ` as a function of
`(r, cos α, sin α, cos 2φ, sin 2φ, p_α, p_φ)`. -/
def Wfun (q : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) : ℝ :=
  vRad q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 -
    q.2.2.2.2.2.1 * vPol q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 -
    q.2.2.2.2.2.2 * vTor q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1

/-- The compact convex parameter box `r ∈ [1/20, 1/4]`, trigonometric values in `[−1, 1]`,
`|p_α|, |p_φ| ≤ C`. -/
def Wbox (C : ℝ) : Set (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) :=
  Icc (1 / 20) (1 / 4) ×ˢ Icc (-1) 1 ×ˢ Icc (-1) 1 ×ˢ Icc (-1) 1 ×ˢ Icc (-1) 1 ×ˢ
    Icc (-C) C ×ˢ Icc (-C) C

/-- `Wfun` is `C¹` on the box. -/
theorem contDiffOn_Wfun (C : ℝ) : ContDiffOn ℝ 1 Wfun (Wbox C) := by
  intro q hq
  obtain ⟨⟨hr0, hr1⟩, ⟨hc0, hc1⟩, -⟩ := hq
  have hR : 1 + q.1 * q.2.1 ≠ 0 := by nlinarith
  have hr : q.1 ≠ 0 := by linarith
  have hR2 : (1 + q.1 * q.2.1) ^ 2 ≠ 0 := pow_ne_zero _ hR
  have hR3 : (1 + q.1 * q.2.1) ^ 3 ≠ 0 := pow_ne_zero _ hR
  have hR4 : (1 + q.1 * q.2.1) ^ 4 ≠ 0 := pow_ne_zero _ hR
  refine ContDiffAt.contDiffWithinAt ?_
  unfold Wfun vRad vPol vTor cylBR cylBZ cylBT Psfun Pzfun Dfun s2fs s2gs sgz sfun sgfun
  fun_prop (disch := assumption)

/-- **Uniform Lipschitz bound in `r`** of the defect function on the box. -/
theorem exists_lipschitz_W (C : ℝ) : ∃ L : NNReal, ∀ q q' : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ,
    q ∈ Wbox C → q' ∈ Wbox C → q.2 = q'.2 → |Wfun q - Wfun q'| ≤ L * |q.1 - q'.1| := by
  have hconv : Convex ℝ (Wbox C) := by
    unfold Wbox
    exact (convex_Icc _ _).prod ((convex_Icc _ _).prod ((convex_Icc _ _).prod
      ((convex_Icc _ _).prod ((convex_Icc _ _).prod ((convex_Icc _ _).prod (convex_Icc _ _))))))
  have hcpt : IsCompact (Wbox C) := by
    unfold Wbox
    exact isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)))))
  obtain ⟨L, hL⟩ := (contDiffOn_Wfun C).exists_lipschitzOnWith one_ne_zero hconv hcpt
  refine ⟨L, fun q q' hq hq' h2 => ?_⟩
  have h := hL.dist_le_mul q hq q' hq'
  rw [Real.dist_eq, Prod.dist_eq, h2, dist_self, Real.dist_eq,
    max_eq_left (abs_nonneg _)] at h
  exact h

end PlasmaLean.Design.KamTorusA
