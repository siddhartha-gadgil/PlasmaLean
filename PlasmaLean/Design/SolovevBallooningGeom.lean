/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevBallooningChart
public import PlasmaLean.Theory.Stability.BallooningReduction
public import PlasmaLean.Design.SolovevMercierCertified

/-!
# Ballooning certificate: the field-line geometry of the reactor Solov'ev surfaces

For the reactor Solov'ev equilibrium of `SolovevAlpha` (`A = 7/4 T`, `L = 10 m`, `F = 50 T m`,
`ψ̃ = R²z²/2 + (R² − L²)²/4`) and EVERY surface `ψ̃ = s²`, `0 < s ≤ 25`, this module computes
the ballooning line data along the exact field line `SolovevMercier.lineS` from the actual
equilibrium (as in the earlier integer-`s` version, now with `s` real):

* `reactorLine`: line element `ℓ = |λ|` (`lnEll_eq_abs_lam`), the actual field (`B_line`), the
  actual `μ₀∇p` (`lnGp_eq_pressure`), the actual curvature from the field derivative
  (`DBB_line`), and the covering-space eikonal gradient `k = k₀ − (σ(t) − c) ∇√ψ̃`
  (`lnB_inner_lnEik`, `meridian_dual`, `hasDerivAt_phiS`, `lnD_eq_mixed`);
* `P_geom`, `Q_geom`: `P = p₀ + σ p₁ + σ² p₂`, `Q = q₀ + σ q₁` with the "physical" trees
  `pp0, …, pq1` (variables `(cos t, sin t, R, √2, 1/R, 1/|B|², s, 1/s)`);
* `Bk0gp_eq` (`B × k₀ · μ₀∇p = 3c|B|²`) and `B2_deriv_eq` (the secular drive is an exact
  derivative), giving `hasDerivAt_a` (`a' = q₁`).
-/

public section
noncomputable section

namespace PlasmaLean.Design.SolovevBallooning

open Real Set PlasmaLean.Fields PlasmaLean.Certificates.ValidatedQuadrature
open PlasmaLean.Stability.BallooningInfinite PlasmaLean.Stability.BallooningReduction
open PlasmaLean.Design.Solovev PlasmaLean.Design.SolovevMercier PlasmaLean.Design.SolovevAlpha
open scoped RealInnerProductSpace
open Tm

/-! ## Cylindrical vectors -/

/-- The vector with cylindrical components `(a, b, c)` (radial, toroidal, vertical) at
toroidal angle `φ`. -/
@[expose] def cyl (φ a b c : ℝ) : Space :=
  WithLp.toLp 2 ![a * Real.cos φ - b * Real.sin φ, a * Real.sin φ + b * Real.cos φ, c]

/-- Inner product in cylindrical components. -/
theorem inner_cyl (φ a b c a' b' c' : ℝ) :
    ⟪cyl φ a b c, cyl φ a' b' c'⟫ = a * a' + b * b' + c * c' := by
  simp only [cyl, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  simp
  linear_combination (a * a' + b * b') * Real.sin_sq_add_cos_sq φ

/-- Squared norm in cylindrical components. -/
theorem norm_sq_cyl (φ a b c : ℝ) : ‖cyl φ a b c‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_cyl]; ring

/-- Cross product in cylindrical components (right-handed frame `e_R, e_φ, e_z`). -/
theorem cross_cyl (φ a b c a' b' c' : ℝ) :
    cross (cyl φ a b c) (cyl φ a' b' c') =
      cyl φ (b * c' - c * b') (c * a' - a * c') (a * b' - b * a') := by
  apply space_ext <;> simp [cross, cross_apply, cyl]
  · ring
  · ring
  · linear_combination (a * b' - b * a') * Real.sin_sq_add_cos_sq φ

/-- Difference of cylindrical vectors. -/
theorem cyl_sub (φ a b c a' b' c' : ℝ) :
    cyl φ a b c - cyl φ a' b' c' = cyl φ (a - a') (b - b') (c - c') := by
  apply space_ext <;> simp [cyl] <;> ring

/-- Scalar multiple of a cylindrical vector. -/
theorem smul_cyl (φ k a b c : ℝ) : k • cyl φ a b c = cyl φ (k * a) (k * b) (k * c) := by
  apply space_ext <;> simp [cyl] <;> ring

/-- A cylindrical vector with nonzero toroidal component is nonzero. -/
theorem cyl_ne_zero {φ a b c : ℝ} (hb : b ≠ 0) : cyl φ a b c ≠ 0 := by
  intro h
  have := congrArg (fun v => ‖v‖ ^ 2) h
  simp only [norm_sq_cyl, norm_zero] at this
  have : 0 < b ^ 2 := by positivity
  nlinarith [sq_nonneg a, sq_nonneg c]

/-- Continuity of a cylindrical vector field along continuous components. -/
theorem continuous_cyl {φ a b c : ℝ → ℝ} (hφ : Continuous φ) (ha : Continuous a)
    (hb : Continuous b) (hc : Continuous c) : Continuous fun t => cyl (φ t) (a t) (b t) (c t) := by
  unfold cyl
  apply (PiLp.continuous_toLp 2 _).comp
  refine continuous_pi fun i => ?_
  fin_cases i <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;> fun_prop

/-! ## Physical trees along the line

Variables: `0 x = cos t`, `1 y = sin t`, `2 R`, `3 r = √2`, `4 1/R`, `5 1/|B|²`, `6 s`,
`7 1/s`. All trees use the reactor constants `A = 7/4`, `L = 10`, `F = 50`
(`c = A/L² = 7/400`). -/

/-- `1/s`. -/ @[expose] def tIs : Tm := v 7

/-- Height `z = √2 s x / R`. -/
@[expose] def pz : Tm := mul (mul tr tS) (mul tX tiR)
/-- `W = z² + R² − L²`. -/
@[expose] def pW : Tm := add (add (sq pz) (sq tR)) (c (-100) 1)
/-- Radial field `B_R = −c R z`. -/
@[expose] def pBR : Tm := neg (mul (c 7 400) (mul tR pz))
/-- Toroidal field `B_φ = F/R`. -/
@[expose] def pBP : Tm := mul (c 50 1) tiR
/-- Vertical field `B_z = c W`. -/
@[expose] def pBZ : Tm := mul (c 7 400) pW
/-- `(∇√ψ̃)_R = R W/(2s)`. -/
@[expose] def pgsR : Tm := mul (mul (c 1 2) tIs) (mul tR pW)
/-- `(∇√ψ̃)_z = R² z/(2s)`. -/
@[expose] def pgsZ : Tm := mul (mul (c 1 2) tIs) (mul (sq tR) pz)
/-- `(∇t)_R = x (L² + s y)/(s R)`. -/
@[expose] def pgtR : Tm := mul tIs (mul (mul tX (add (c 100 1) (mul tS tY))) tiR)
/-- `(∇t)_z = −R y/(√2 s)`. -/
@[expose] def pgtZ : Tm := neg (mul (mul (c 1 2) tIs) (mul (mul tR tY) tr))
/-- `∂ₜΦ = −rate/R³`. -/
@[expose] def pPhit : Tm := neg (mul trate (mul tiR (sq tiR)))
/-- `k₀ = ∇φ − ∂ₜΦ ∇t`, radial. -/
@[expose] def pkR : Tm := neg (mul pPhit pgtR)
/-- `k₀`, toroidal (`1/R`). -/
@[expose] def pkP : Tm := tiR
/-- `k₀`, vertical. -/
@[expose] def pkZ : Tm := neg (mul pPhit pgtZ)
/-- `μ₀ ∂_R p = −3 c² R W`. -/
@[expose] def pgpR : Tm := mul (c (-147) 160000) (mul tR pW)
/-- `μ₀ ∂_z p = −3 c² R² z`. -/
@[expose] def pgpZ : Tm := mul (c (-147) 160000) (mul (sq tR) pz)
/-- `(DB · B)_R = c² R z² − F²/R³ − c² R W`. -/
@[expose] def pGR : Tm :=
  Tm.sub (Tm.sub (mul (c 49 160000) (mul tR (sq pz))) (mul (c 2500 1) (mul tiR (sq tiR))))
    (mul (c 49 160000) (mul tR pW))
/-- `(DB · B)_z = 2 c² z (W − R²)`. -/
@[expose] def pGZ : Tm := mul (c 49 80000) (mul pz (Tm.sub pW (sq tR)))
/-- `|B|²`. -/
@[expose] def pB2 : Tm := add (add (sq pBR) (sq pBP)) (sq pBZ)
/-- `p₀ = |k₀|²/(ℓ|B|²)`. -/
@[expose] def pp0 : Tm := mul (add (add (sq pkR) (sq pkP)) (sq pkZ)) tden
/-- `p₁ = −2 k₀·∇√ψ̃/(ℓ|B|²)`. -/
@[expose] def pp1 : Tm := mul (mul (c (-2) 1) (add (mul pkR pgsR) (mul pkZ pgsZ))) tden
/-- `p₂ = |∇√ψ̃|²/(ℓ|B|²)`. -/
@[expose] def pp2 : Tm := mul (add (sq pgsR) (sq pgsZ)) tden
/-- `(B × b)·g` for `b = (bR, bP, bZ)` and a meridional `g = (gR, 0, gZ)`. -/
@[expose] def pcross (bR bP bZ gR gZ : Tm) : Tm :=
  add (mul (Tm.sub (mul pBP bZ) (mul pBZ bP)) gR) (mul (Tm.sub (mul pBR bP) (mul pBP bR)) gZ)
/-- `B × k₀ · μ₀∇p`. -/
@[expose] def pBk0gp : Tm := pcross pkR pkP pkZ pgpR pgpZ
/-- `B × k₀ · (DB B)`. -/
@[expose] def pBk0G : Tm := pcross pkR pkP pkZ pGR pGZ
/-- `B × ∇√ψ̃ · (DB B)`. -/
@[expose] def pBgsG : Tm := pcross pgsR (c 0 1) pgsZ pGR pGZ
/-- `q₀ = −2ℓ (B×k₀·μ₀∇p)(B×k₀·DB B)/|B|⁶`. -/
@[expose] def pq0 : Tm := neg (mul (mul (mul (c 2 1) tell) (mul pBk0gp pBk0G)) (mul tiB (sq tiB)))
/-- `q₁ = 2ℓ (B×k₀·μ₀∇p)(B×∇√ψ̃·DB B)/|B|⁶`. -/
@[expose] def pq1 : Tm := mul (mul (mul (c 2 1) tell) (mul pBk0gp pBgsG)) (mul tiB (sq tiB))
/-- Secular rate `d = ∂ₛ∂ₜΦ = 3 rate y/R⁵`. -/
@[expose] def pd : Tm := mul (mul (mul (c 3 1) trate) tY) (mul tiR (sq (sq tiR)))

/-- Value assignment along the line (`s`, `1/s` in the slots `6`, `7`). -/
@[expose] def envP (s x y R r iR iB : ℝ) : ℕ → ℝ := envR x y R r iR iB s s⁻¹ 0

/-- Derivative assignment (the constant slots `6, 7, 8` have derivative `0`). -/
@[expose] def envD (x y R r iR iB : ℝ) : ℕ → ℝ := envR x y R r iR iB 0 0 0

/-- The variables along the line with the `1/|B|²` slot set to `0`. -/
@[expose] def envL0 (s t : ℝ) : ℕ → ℝ :=
  envP s (Real.cos t) (Real.sin t) (RS 10 s t) √2 (RS 10 s t)⁻¹ 0

/-- `|B|²` along the line (the tree `pB2` does not use the slot `5`). -/
@[expose] def B2v (s t : ℝ) : ℝ := pB2.eval (envL0 s t)

/-- **The variables along the field line** on the surface `ψ̃ = s²`:
`(cos t, sin t, R(t), √2, 1/R(t), 1/|B|², s, 1/s)`. -/
@[expose] def envL (s t : ℝ) : ℕ → ℝ :=
  envP s (Real.cos t) (Real.sin t) (RS 10 s t) √2 (RS 10 s t)⁻¹ (B2v s t)⁻¹

/-- `R > 0` on the reactor surfaces `0 < s ≤ 25`. -/
theorem RS_pos_r {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (t : ℝ) : 0 < RS 10 s t :=
  RS_pos hs0.le (by norm_num; linarith) t

/-! ## The field-line geometry of the reactor surface `ψ̃ = s²` -/


/-- `R² = x₀² + x₁²` along the field line. -/
theorem R2_line (s : ℝ) (t : ℝ) : R2 (lineS (7 / 4) 10 50 s t) = RS 10 s t ^ 2 := by
  simp only [R2, lineS, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination RS 10 s t ^ 2 * Real.sin_sq_add_cos_sq (phiS (7 / 4) 10 50 s t)

/-- **The actual field along the line** in cylindrical components:
`B = (−c R z, F/R, c W)` at toroidal angle `φ(t)`. -/
theorem B_line {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (t : ℝ) :
    reactorField (lineS (7 / 4) 10 50 s t) = cyl (phiS (7 / 4) 10 50 s t)
      (pBR.eval (envL s t)) (pBP.eval (envL s t)) (pBZ.eval (envL s t)) := by
  have hR := RS_pos_r hs0 hs t
  have h2 := R2_line s t
  apply space_ext
  · simp only [reactorField, field, poloidal, phiGrad, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, h2]
    simp [lineS, cyl, Tm.eval, envL, envP, envR, pBR, pBP, pz, tX, tR, tr, tiR, tS, zS]
    field_simp
    ring
  · simp only [reactorField, field, poloidal, phiGrad, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, h2]
    simp [lineS, cyl, Tm.eval, envL, envP, envR, pBR, pBP, pz, tX, tR, tr, tiR, tS, zS]
    field_simp
    ring
  · simp only [reactorField, field, poloidal, phiGrad, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, h2]
    simp [lineS, cyl, Tm.eval, envL, envP, envR, pBZ, pW, pz, tX, tR, tr, tiR, tS, zS]
    ring

/-- Coordinates of the field derivative applied to a vector. -/
theorem fieldDeriv_coord (A L F : ℝ) (x w : Space) (j : Fin 3) :
    fieldDeriv A L F x w j =
      jac A L F x j 0 * w 0 + jac A L F x j 1 * w 1 + jac A L F x j 2 * w 2 := by
  rw [fieldDeriv, PlasmaLean.Fields.coords_apply]
  simp [row, Fin.sum_univ_three]

/-- **The derivative of the actual field along itself**, `(DB) B`, along the line:
`(c² R z² − F²/R³ − c² R W, 0, 2 c² z (W − R²))`. -/
theorem DBB_line {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (t : ℝ) :
    fieldDeriv (7 / 4) 10 50 (lineS (7 / 4) 10 50 s t) (reactorField (lineS (7 / 4) 10 50 s t)) =
      cyl (phiS (7 / 4) 10 50 s t) (pGR.eval (envL s t)) 0 (pGZ.eval (envL s t)) := by
  have hR := RS_pos_r hs0 hs t
  have h2 := R2_line s t
  have hc := Real.sin_sq_add_cos_sq (phiS (7 / 4) 10 50 s t)
  rw [B_line hs0 hs t]
  apply space_ext
  · rw [fieldDeriv_coord]
    simp only [jac, h2]
    simp [lineS, cyl, Tm.eval, envL, envP, envR, pBR, pBP, pBZ, pW, pGR, pz, tX, tR, tr, tiR, tS,
      zS,
      Tm.sub]
    field_simp
    linear_combination (-((√2 * s * Real.cos t * RS 10 (s) t * 22400000000) *
      Real.sin (phiS (7 / 4) 10 50 (s) t) +
      (64000000000000:ℝ) * Real.cos (phiS (7 / 4) 10 50 (s) t))) * hc
  · rw [fieldDeriv_coord]
    simp only [jac, h2]
    simp [lineS, cyl, Tm.eval, envL, envP, envR, pBR, pBP, pBZ, pW, pGR, pz, tX, tR, tr, tiR, tS,
      zS,
      Tm.sub]
    field_simp
    linear_combination ((√2 * s * Real.cos t * RS 10 (s) t * 22400000000) *
      Real.cos (phiS (7 / 4) 10 50 (s) t) -
      (64000000000000:ℝ) * Real.sin (phiS (7 / 4) 10 50 (s) t)) * hc
  · rw [fieldDeriv_coord]
    simp only [jac, h2]
    simp [lineS, cyl, Tm.eval, envL, envP, envR, pBR, pBP, pBZ, pW, pGZ, pz, tX, tR, tr, tiR, tS,
      zS,
      Tm.sub]
    field_simp
    linear_combination (-(RS 10 (s) t ^ 4 * √2 * s * Real.cos t * 7840000)) * hc

/-- The actual gradient of `ψ̃` along the line is `2s ∇√ψ̃` with
`∇√ψ̃ = (R W/(2s), 0, R² z/(2s))`. -/
theorem psiTGrad_line {s : ℝ} (hs0 : 0 < s) (t : ℝ) :
    psiTGrad 10 (lineS (7 / 4) 10 50 s t) = (2 * s) •
      cyl (phiS (7 / 4) 10 50 s t) (pgsR.eval (envL s t)) 0 (pgsZ.eval (envL s t)) := by
  have h2 := R2_line s t
  have hs : s ≠ 0 := hs0.ne'
  rw [smul_cyl]
  apply space_ext
  · simp only [psiTGrad, h2]
    simp [lineS, cyl, Tm.eval, envL, envP, envR, pgsR, pW, pz, tX, tR, tr, tiR, tS, tIs, zS]
    field_simp
    ring
  · simp only [psiTGrad, h2]
    simp [lineS, cyl, Tm.eval, envL, envP, envR, pgsR, pW, pz, tX, tR, tr, tiR, tS, tIs, zS]
    field_simp
    ring
  · simp only [psiTGrad, h2]
    simp [lineS, cyl, Tm.eval, envL, envP, envR, pgsZ, pz, tX, tR, tr, tiR, tS, tIs, zS]
    field_simp

/-- The actual `∇φ` along the line is `(0, 1/R, 0)`. -/
theorem phiGrad_line {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (t : ℝ) :
    phiGrad (lineS (7 / 4) 10 50 s t) = cyl (phiS (7 / 4) 10 50 s t) 0 (pkP.eval (envL s t)) 0 := by
  have hR := RS_pos_r hs0 hs t
  have h2 := R2_line s t
  apply space_ext
  · simp only [phiGrad, PiLp.smul_apply, smul_eq_mul, h2]
    simp [lineS, cyl, Tm.eval, envL, envP, envR, pkP, tiR]
    field_simp
  · simp only [phiGrad, PiLp.smul_apply, smul_eq_mul, h2]
    simp [lineS, cyl, Tm.eval, envL, envP, envR, pkP, tiR]
    field_simp
  · simp [phiGrad, cyl]

/-! ## Two exact identities (geodesic-curvature structure) -/

/-- `B × k₀ · μ₀∇p = 3 c |B|²`, `c = 7/400` (for any point of the surface relations
`x² + y² = 1`, `R² = L² + 2 s y`, `r² = 2`). -/
theorem Bk0gp_eq (s : ℝ) {x y R r : ℝ} (iB : ℝ) (hx : x ^ 2 + y ^ 2 = 1)
    (hR : R ^ 2 = 100 + 2 * s * y) (hr : r ^ 2 = 2) (hRne : R ≠ 0) (hs : (s : ℝ) ≠ 0) :
    pBk0gp.eval (envP s x y R r R⁻¹ iB) =
      3 * (7 / 400) * pB2.eval (envP s x y R r R⁻¹ iB) := by
  simp [Tm.eval, envP, envR, pBk0gp, pcross, pB2, pBR, pBP, pBZ, pkR, pkP, pkZ, pgpR, pgpZ, pPhit,
    trate, pgtR, pgtZ, pz, pW, tX, tY, tR, tr, tiR, tS, tIs, Tm.sub]
  field_simp
  linear_combination (4704000000000000*r^4*s^2*y + 9408000000000000*r^2*s^2*y
    + 940800000000000000*r^2*s) * hx + (4704000000000000*R^2*r^2*y
    + 9408000000000000*r^2*s*y^2 - 18816000000000000*s) * hR
    + (-4704000000000000*r^2*s^2*y^3 + 4704000000000000*r^2*s^2*y
    + 18816000000000000*s^2*y + 940800000000000000*s) * hr

/-- `(75/s) ∂ₜ|B|² = 6 c ℓ (B × ∇√ψ̃ · DB B)`: the secular drive is an exact `t`-derivative. -/
theorem B2_deriv_eq (s : ℝ) {x y R r : ℝ} (iB diB : ℝ) (hx : x ^ 2 + y ^ 2 = 1)
    (hR : R ^ 2 = 100 + 2 * s * y) (hr : r ^ 2 = 2) (hRne : R ≠ 0) (hs : (s : ℝ) ≠ 0) :
    75 / s * pB2.deriv (envP s x y R r R⁻¹ iB)
        (envD (-y) x (s * x * R⁻¹) 0 (-(s * x * R⁻¹) * R⁻¹ * R⁻¹) diB) =
      6 * (7 / 400) * tell.eval (envP s x y R r R⁻¹ iB) * pBgsG.eval (envP s x y R r R⁻¹ iB) := by
  simp [Tm.eval, Tm.deriv, envP, envD, envR, pBgsG, pcross, pB2, pBR, pBP, pBZ, pgsR, pgsZ, pGR,
    pGZ, tell, pz, pW, tX, tR, tr, tiR, tS, tIs, Tm.sub]
  field_simp
  linear_combination (188160000000000*R^4*r^4*s^2*x - 376320000000000*R^2*r^4*s^3*x*y
    - 37632000000000000*R^2*r^4*s^2*x + 37632000000000000*R^2*r^2*s^2*x
    + 188160000000000*r^6*s^4*x^3 - 188160000000000*r^6*s^4*x*y^2
    + 188160000000000*r^6*s^4*x - 376320000000000*r^4*s^4*x^3
    + 376320000000000*r^4*s^4*x*y^2 - 376320000000000*r^4*s^4*x) * hx
    + (94080000000000*R^6*r^2*x + 376320000000000*R^6*x - 376320000000000*R^4*r^2*s*x*y
    - 18816000000000000*R^4*r^2*x + 752640000000000*R^4*s*x*y
    - 188160000000000*R^2*r^4*s^2*x*y^2 + 188160000000000*R^2*r^4*s^2*x
    - 752640000000000*R^2*r^2*s^2*x*y^2 - 37632000000000000*R^2*r^2*s*x*y
    + 1505280000000000*R^2*s^2*x*y^2 + 75264000000000000*R^2*s*x*y
    + 18816000000000000*r^4*s^2*x*y^2 - 18816000000000000*r^4*s^2*x
    - 1505280000000000*r^2*s^3*x*y^3 - 188160000000000000*r^2*s^2*x*y^2
    + 37632000000000000*r^2*s^2*x - 3763200000000000000*r^2*s*x*y
    + 768000000000000000000*r^2*x + 3010560000000000*s^3*x*y^3
    + 301056000000000000*s^2*x*y^2 + 7526400000000000000*s*x*y
    - 1536000000000000000000*x) * hR + (188160000000000*r^4*s^4*x*y^4
    - 376320000000000*r^4*s^4*x*y^2 + 188160000000000*r^4*s^4*x
    + 37632000000000000*r^2*s^3*x*y^3 - 37632000000000000*r^2*s^3*x*y
    + 1881600000000000000*r^2*s^2*x*y^2 - 1881600000000000000*r^2*s^2*x
    - 3010560000000000*s^4*x*y^4 - 451584000000000000*s^3*x*y^3
    - 22579200000000000000*s^2*x*y^2 + 1159680000000000000000*s*x*y
    + 76800000000000000000000*x) * hr

/-! ## Derivatives and continuity of the variables along the line -/

/-- `t`-derivatives of the first five variables (slot `5` set to `0`). -/
@[expose] def denv0 (s : ℝ) (t : ℝ) : ℕ → ℝ :=
  envD (-Real.sin t) (Real.cos t) (s * Real.cos t * (RS 10 s t)⁻¹) 0
    (-(s * Real.cos t * (RS 10 s t)⁻¹) * (RS 10 s t)⁻¹ * (RS 10 s t)⁻¹) 0

/-- `t`-derivatives of all six variables along the line. -/
@[expose] def denv (s : ℝ) (t : ℝ) : ℕ → ℝ :=
  envD (-Real.sin t) (Real.cos t) (s * Real.cos t * (RS 10 s t)⁻¹) 0
    (-(s * Real.cos t * (RS 10 s t)⁻¹) * (RS 10 s t)⁻¹ * (RS 10 s t)⁻¹)
    (-(pB2.deriv (envL0 s t) (denv0 s t) * ((B2v s t)⁻¹) ^ 2))

/-- `R(t)` is differentiable with `R' = s cos t / R`. -/
theorem hasDerivAt_RS_nat {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (t : ℝ) :
    HasDerivAt (RS 10 s) (s * Real.cos t * (RS 10 s t)⁻¹) t := by
  have h := PlasmaLean.Design.SolovevMercierCertified.hasDerivAt_RS_t (s := s)
    (by exact_mod_cast hs0) (by exact_mod_cast hs) t
  simpa [div_eq_mul_inv] using h

/-- Derivatives of the first five variables. -/
theorem hasDerivAt_env0 {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (t : ℝ) (i : ℕ) :
    HasDerivAt (fun t => envL0 s t i) (denv0 s t i) t := by
  have hR := RS_pos_r hs0 hs t
  have hd := hasDerivAt_RS_nat hs0 hs t
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i
  · simpa [envL0, denv0, envP, envD, envR] using Real.hasDerivAt_cos t
  · simpa [envL0, denv0, envP, envD, envR] using Real.hasDerivAt_sin t
  · simpa [envL0, denv0, envP, envD, envR] using hd
  · simpa [envL0, denv0, envP, envD, envR] using hasDerivAt_const t (√2)
  · have := hd.inv hR.ne'
    simp only [envL0, denv0, envP, envD, envR]
    convert this using 1
    field_simp
  · simpa [envL0, denv0, envP, envD, envR] using hasDerivAt_const t (0 : ℝ)
  · simpa [envL0, denv0, envP, envD, envR] using hasDerivAt_const t s
  · simpa [envL0, denv0, envP, envD, envR] using hasDerivAt_const t s⁻¹
  · simpa [envL0, denv0, envP, envD, envR] using hasDerivAt_const t (0 : ℝ)
  · simpa [envL0, denv0, envP, envD, envR] using hasDerivAt_const t (0 : ℝ)

/-- `|B|² = B_R² + B_φ² + B_z²` along the line. -/
theorem B2v_eq (s : ℝ) (t : ℝ) : B2v s t = pBR.eval (envL s t) ^ 2 +
    pBP.eval (envL s t) ^ 2 + pBZ.eval (envL s t) ^ 2 := by
  simp [B2v, Tm.eval, pB2, pBR, pBP, pBZ, pW, pz, tX, tR, tr, tiR, tS, envL, envL0, envP, envR]

/-- `|B|² > 0` along the line (the toroidal field never vanishes). -/
theorem B2v_pos {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (t : ℝ) : 0 < B2v s t := by
  have hR := RS_pos_r hs0 hs t
  rw [B2v_eq]
  have : 0 < pBP.eval (envL s t) := by
    simp only [Tm.eval, pBP, tiR, envL, envP, envR]; push_cast; positivity
  positivity

/-- `pB2` does not see the slot `5`: its value along the line is `B2v`. -/
theorem tB2_env (s : ℝ) (t : ℝ) : pB2.eval (envL s t) = B2v s t := by
  simp [B2v, Tm.eval, pB2, pBR, pBP, pBZ, pW, pz, tX, tR, tr, tiR, tS, envL, envL0, envP, envR]

/-- `|B|²` is differentiable along the line. -/
theorem hasDerivAt_B2v {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (t : ℝ) :
    HasDerivAt (B2v s) (pB2.deriv (envL0 s t) (denv0 s t)) t :=
  pB2.hasDerivAt (ρ := envL0 s) (ρ' := denv0 s) (hasDerivAt_env0 hs0 hs t)

/-- **Derivatives of all six variables along the line.** -/
theorem hasDerivAt_env {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (t : ℝ) (i : ℕ) :
    HasDerivAt (fun t => envL s t i) (denv s t i) t := by
  rcases i with _ | _ | _ | _ | _ | _ | i
  · simpa [envL, denv, envL0, denv0, envP, envD, envR] using hasDerivAt_env0 hs0 hs t 0
  · simpa [envL, denv, envL0, denv0, envP, envD, envR] using hasDerivAt_env0 hs0 hs t 1
  · simpa [envL, denv, envL0, denv0, envP, envD, envR] using hasDerivAt_env0 hs0 hs t 2
  · simpa [envL, denv, envL0, denv0, envP, envD, envR] using hasDerivAt_env0 hs0 hs t 3
  · simpa [envL, denv, envL0, denv0, envP, envD, envR] using hasDerivAt_env0 hs0 hs t 4
  · have h := (hasDerivAt_B2v hs0 hs t).inv (B2v_pos hs0 hs t).ne'
    simp only [envL, denv, envP, envD, envR]
    convert h using 1
    field_simp
  · have h := hasDerivAt_env0 hs0 hs t (i + 6)
    have e1 : (fun t => envL s t (i + 6)) = fun t => envL0 s t (i + 6) := by
      funext t; rcases i with _ | _ | _ | i <;> simp [envL, envL0, envP, envR]
    have e2 : denv s t (i + 6) = denv0 s t (i + 6) := by
      rcases i with _ | _ | _ | i <;> simp [denv, denv0, envD, envR]
    rw [e1, e2]; exact h

/-- Continuity of the variables along the line. -/
theorem continuous_env {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (i : ℕ) :
    Continuous fun t => envL s t i :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_env hs0 hs t i).continuousAt

/-- Continuity of any tree along the line. -/
theorem continuous_tree {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (e : Tm) :
    Continuous fun t => e.eval (envL s t) :=
  e.continuous_eval (continuous_env hs0 hs)

/-- Differentiability of any tree along the line. -/
theorem hasDerivAt_tree {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (e : Tm) (t : ℝ) :
    HasDerivAt (fun t => e.eval (envL s t)) (e.deriv (envL s t) (denv s t)) t :=
  e.hasDerivAt (hasDerivAt_env hs0 hs t)

/-- The toroidal angle of the line is continuous. -/
theorem continuous_phiS {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) :
    Continuous (phiS (7 / 4) 10 50 s) := by
  have hc := continuous_invCube (L := 10) (s := s) hs0.le (by norm_num; linarith)
  unfold phiS
  refine continuous_iff_continuousAt.mpr fun t => ?_
  exact ((hc.integral_hasStrictDerivAt 0 t).hasDerivAt.const_mul _).neg.continuousAt

/-! ## The secular drive is an exact derivative: `a' = q₁` -/

/-- The coefficient `a = a₀ − (75/s)/|B|²` of the secular part of the flux function (`a₀` a
tree in `√2, s, 1/s` only, i.e. constant along the line). -/
@[expose] def pa (a0 : Tm) : Tm := Tm.sub a0 (mul (mul (c 75 1) tIs) tiB)

/-- A tree that only uses the variables with vanishing derivative has derivative `0`. -/
theorem deriv_eq_zero_of_usesOnly {P : ℕ → Prop} (e : Tm) (he : e.UsesOnly P) {ρ ρ' : ℕ → ℝ}
    (h : ∀ i, P i → ρ' i = 0) : e.deriv ρ ρ' = 0 := by
  induction e with
  | c p q => rfl
  | v i => exact h i he
  | add a b iha ihb => simp only [Tm.deriv, iha he.1, ihb he.2, add_zero]
  | mul a b iha ihb => simp only [Tm.deriv, iha he.1, ihb he.2, zero_mul, mul_zero, add_zero]
  | neg a iha => simp only [Tm.deriv, iha he, neg_zero]
  | sq a iha => simp only [Tm.deriv, iha he, mul_zero]

/-- Surface relations along the line: `cos² + sin² = 1`, `R² = L² + 2 s sin t`, `√2² = 2`. -/
theorem line_relations {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (t : ℝ) :
    Real.cos t ^ 2 + Real.sin t ^ 2 = 1 ∧ RS 10 s t ^ 2 = 100 + 2 * s * Real.sin t ∧
      √2 ^ 2 = 2 ∧ RS 10 s t ≠ 0 := by
  refine ⟨by linarith [Real.sin_sq_add_cos_sq t], ?_, Real.sq_sqrt (by norm_num),
    (RS_pos_r hs0 hs t).ne'⟩
  rw [RS_sq hs0.le (by norm_num; linarith)]
  simp [uS]; norm_num

/-- **`a' = q₁` along the line.** The `t`-derivative of `a = a₀ − (75/s)/|B|²` is exactly the
coefficient `q₁` of the secular (geodesic-curvature) part of the ballooning drive. This is
what makes the two-variable certificate possible (the `σ³` terms cancel identically). -/
theorem hasDerivAt_a (a0 : Tm) (ha0 : a0.UsesOnly fun i => i = 3 ∨ 6 ≤ i) {s : ℝ}
    (hs0 : 0 < s) (hs : s ≤ 25) (t : ℝ) :
    HasDerivAt (fun t => (pa a0).eval (envL s t)) (pq1.eval (envL s t)) t := by
  have h := hasDerivAt_tree hs0 hs (pa a0) t
  refine h.congr_deriv ?_
  obtain ⟨hx, hR, hr, hRne⟩ := line_relations hs0 hs t
  have hsne : s ≠ 0 := hs0.ne'
  have hB := (B2v_pos hs0 hs t).ne'
  have hI1 := Bk0gp_eq s ((B2v s t)⁻¹) hx hR hr hRne hsne
  have hI2 := B2_deriv_eq s 0 0 hx hR hr hRne hsne
  have e1 : pB2.eval (envP s (Real.cos t) (Real.sin t) (RS 10 s t) √2 (RS 10 s t)⁻¹
      (B2v s t)⁻¹) = B2v s t := tB2_env s t
  have e2 : pB2.deriv (envP s (Real.cos t) (Real.sin t) (RS 10 s t) √2 (RS 10 s t)⁻¹ 0)
      (envD (-Real.sin t) (Real.cos t) (s * Real.cos t * (RS 10 s t)⁻¹) 0
        (-(s * Real.cos t * (RS 10 s t)⁻¹) * (RS 10 s t)⁻¹ * (RS 10 s t)⁻¹) 0) =
      pB2.deriv (envL0 s t) (denv0 s t) := rfl
  have e3 : tell.eval (envP s (Real.cos t) (Real.sin t) (RS 10 s t) √2 (RS 10 s t)⁻¹ 0) =
      tell.eval (envL s t) := by simp [Tm.eval, tell, tr, tiR, envL, envP, envR]
  have e4 : pBgsG.eval (envP s (Real.cos t) (Real.sin t) (RS 10 s t) √2 (RS 10 s t)⁻¹ 0) =
      pBgsG.eval (envL s t) := by
    simp [Tm.eval, pBgsG, pcross, pBR, pBP, pBZ, pgsR, pgsZ, pGR, pGZ, pz, pW, tX, tR, tr,
      tiR, tS, tIs, envL, envP, envR]
  rw [e1] at hI1
  rw [e2, e3, e4] at hI2
  have hq : pq1.eval (envL s t) = 2 * tell.eval (envL s t) * (pBk0gp.eval (envL s t) *
      pBgsG.eval (envL s t)) * ((B2v s t)⁻¹ * ((B2v s t)⁻¹ * (B2v s t)⁻¹)) := by
    simp only [Tm.eval, pq1, tiB, envL, envP, envR]; ring
  have h0 : a0.deriv (envL s t) (denv s t) = 0 := by
    apply deriv_eq_zero_of_usesOnly a0 ha0
    intro i hi
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp_all [denv, envD, envR]
  have hd : (pa a0).deriv (envL s t) (denv s t) =
      75 / s * pB2.deriv (envL0 s t) (denv0 s t) * ((B2v s t)⁻¹) ^ 2 := by
    simp only [pa, Tm.sub, Tm.deriv, h0, tIs, tiB, Tm.eval]
    simp [denv, envP, envD, envR, envL]
    field_simp
  have hk : pBk0gp.eval (envL s t) = 3 * (7 / 400) * B2v s t := hI1
  rw [hq, hd, hk, hI2]
  field_simp
  ring

/-! ## The ballooning line data of the reactor surfaces -/

section line
variable (s : ℝ)

/-- The secular rate `d(t) = ∂ₛ∂ₜΦ = 3 rate sin t / R⁵` along the line. -/
@[expose] def lnD (t : ℝ) : ℝ := pd.eval (envL s t)

/-- The secular coefficient `σ(t) = ∫_{π/2}^t d`, i.e. `∂ₛΦ(s, t)` up to a constant. -/
@[expose] def lnSig (t : ℝ) : ℝ := ∫ τ in (π / 2)..t, lnD s τ

/-- `∇√ψ̃` along the line (the secular direction `k₁`). -/
@[expose] def lnGs (t : ℝ) : Space :=
  cyl (phiS (7 / 4) 10 50 s t) (pgsR.eval (envL s t)) 0 (pgsZ.eval (envL s t))

/-- `∇t` along the line (gradient of the poloidal coordinate). -/
@[expose] def lnGt (t : ℝ) : Space :=
  cyl (phiS (7 / 4) 10 50 s t) (pgtR.eval (envL s t)) 0 (pgtZ.eval (envL s t))

/-- The periodic part `k₀ = ∇φ − ∂ₜΦ ∇t` of the eikonal gradient. -/
@[expose] def lnK0 (t : ℝ) : Space :=
  cyl (phiS (7 / 4) 10 50 s t) (pkR.eval (envL s t)) (pkP.eval (envL s t))
    (pkZ.eval (envL s t))

/-- The covering-space eikonal gradient of the ballooning family with shift `c`:
`k = ∇(φ − Φ(s, t)) = k₀ − (σ(t) − c) ∇√ψ̃`. -/
@[expose] def lnEik (c t : ℝ) : Space := lnK0 s t - (lnSig s t - c) • lnGs s t

/-- The line element `ℓ = |λ|`, `dl/|B| = ℓ dt`. -/
@[expose] def lnEll (t : ℝ) : ℝ := tell.eval (envL s t)

/-- `μ₀ ∇p` along the line (actual Solov'ev pressure). -/
@[expose] def lnGp (t : ℝ) : Space :=
  (-(3 * ((7 / 4 : ℝ) / 10 ^ 2) ^ 2)) • psiTGrad 10 (lineS (7 / 4) 10 50 s t)

/-- The actual field along the line. -/
@[expose] def lnB (t : ℝ) : Space := reactorField (lineS (7 / 4) 10 50 s t)

/-- The actual field-line curvature `b · ∇b`, from the actual field derivative. -/
@[expose] def lnKappa (t : ℝ) : Space :=
  fieldLineCurvature (lnB s t) (fieldDeriv (7 / 4) 10 50 (lineS (7 / 4) 10 50 s t) (lnB s t))

end line

/-- `σ' = d`. -/
theorem hasDerivAt_lnSig {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (t : ℝ) :
    HasDerivAt (lnSig s) (lnD s t) t :=
  ((continuous_tree hs0 hs pd).integral_hasStrictDerivAt (π / 2) t).hasDerivAt

/-- `μ₀ ∇p` is the actual pressure gradient (times `μ₀`) of the reactor pressure. -/
theorem lnGp_eq_pressure (s : ℝ) {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (t : ℝ) :
    lnGp s t = μ₀ • pressureGrad μ₀ (7 / 4) 10 (lineS (7 / 4) 10 50 s t) := by
  rw [lnGp, pressureGrad, smul_smul]
  congr 1
  field_simp

/-- `ℓ = |λ|` for the reparametrization `X' = λ B` of `lineS_fieldLine`. -/
theorem lnEll_eq_abs_lam {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (t : ℝ) :
    lnEll s t = |lamS (7 / 4) 10 s t| := by
  have hR := RS_pos_r hs0 hs t
  have h2 : (0:ℝ) < √2 := by positivity
  rw [lamS, abs_neg, abs_of_pos (by positivity)]
  simp [lnEll, Tm.eval, tell, tr, tiR, envL, envP, envR]
  field_simp
  rw [Real.sq_sqrt (by norm_num)]
  ring

/-- `μ₀∇p = μ ∇√ψ̃` with `μ = −6 c² s`. -/
theorem lnGp_eq {s : ℝ} (hs0 : 0 < s) (t : ℝ) :
    lnGp s t = (-(3 * ((7 / 4 : ℝ) / 10 ^ 2) ^ 2) * (2 * s)) • lnGs s t := by
  rw [lnGp, psiTGrad_line hs0, smul_smul, lnGs]

/-- The eikonal gradient in cylindrical components. -/
theorem lnEik_eq (s : ℝ) (c t : ℝ) : lnEik s c t = cyl (phiS (7 / 4) 10 50 s t)
    (pkR.eval (envL s t) - (lnSig s t - c) * pgsR.eval (envL s t)) (pkP.eval (envL s t))
    (pkZ.eval (envL s t) - (lnSig s t - c) * pgsZ.eval (envL s t)) := by
  rw [lnEik, lnK0, lnGs, smul_cyl, cyl_sub]
  ring_nf

/-! ## Identification of the ballooning coefficients -/

/-- The bending coefficient as a polynomial in the secular variable:
`P(t, σ) = p₀ + σ p₁ + σ² p₂`. -/
@[expose] def Pc (s : ℝ) (t σ : ℝ) : ℝ :=
  pp0.eval (envL s t) + σ * pp1.eval (envL s t) + σ ^ 2 * pp2.eval (envL s t)

/-- The drive as an affine function of the secular variable: `Q(t, σ) = q₀ + σ q₁`. -/
@[expose] def Qc (s : ℝ) (t σ : ℝ) : ℝ := pq0.eval (envL s t) + σ * pq1.eval (envL s t)

/-- `|B|² = B2v` along the line. -/
theorem norm_sq_lnB {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (t : ℝ) : ‖lnB s t‖ ^ 2 = B2v s t := by
  rw [lnB, B_line hs0 hs, norm_sq_cyl, B2v_eq]

/-- `1/(ℓ |B|²)` equals the tree `tden`. -/
theorem tden_eq {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (t : ℝ) :
    tden.eval (envL s t) = (lnEll s t * B2v s t)⁻¹ := by
  have hR := RS_pos_r hs0 hs t
  have hB := B2v_pos hs0 hs t
  have hr : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2 : (0:ℝ) < √2 := by positivity
  simp only [tden, lnEll, Tm.eval, tell, tr, tR, tiR, tiB, envL, envP, envR]
  field_simp
  rw [hr]
  ring

/-- **Bending coefficient along the line**: for every secular value `σ`,
`ballooningP ℓ B (k₀ − σ ∇√ψ̃) = P(t, σ)`. -/
theorem P_geom {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (t σ : ℝ) :
    ballooningP (lnEll s t) (lnB s t) (lnK0 s t - σ • lnGs s t) = Pc s t σ := by
  rw [ballooningP_secular, norm_sq_lnB hs0 hs, lnK0, lnGs, inner_cyl, norm_sq_cyl, norm_sq_cyl]
  have hd := tden_eq hs0 hs t
  simp only [Pc, pp0, pp1, pp2, Tm.eval, hd]
  ring

/-- **Drive along the line**: for every secular value `σ`,
`ballooningQ ℓ B (k₀ − σ ∇√ψ̃) (μ₀∇p) κ = Q(t, σ)`, with the actual curvature. -/
theorem Q_geom {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (t σ : ℝ) :
    ballooningQ (lnEll s t) (lnB s t) (lnK0 s t - σ • lnGs s t) (lnGp s t) (lnKappa s t) =
      Qc s t σ := by
  have hB := B2v_pos hs0 hs t
  have hsne : s ≠ 0 := hs0.ne'
  rw [lnGp_eq hs0, ballooningQ_secular, lnKappa, inner_cross_curvature, inner_cross_curvature,
    show ‖lnB s t‖ ^ 4 = (‖lnB s t‖ ^ 2) ^ 2 by ring, norm_sq_lnB hs0 hs]
  simp only [lnB]
  rw [DBB_line hs0 hs, B_line hs0 hs, lnK0, lnGs, smul_cyl, cross_cyl, cross_cyl, inner_cyl,
    inner_cyl, inner_cyl]
  have gR : pgpR.eval (envL s t) =
      -(3 * ((7 / 4 : ℝ) / 10 ^ 2) ^ 2) * (2 * s) * pgsR.eval (envL s t) := by
    simp only [pgpR, pgsR, Tm.eval, tIs, envL, envP, envR]; push_cast; field_simp; ring
  have gZ : pgpZ.eval (envL s t) =
      -(3 * ((7 / 4 : ℝ) / 10 ^ 2) ^ 2) * (2 * s) * pgsZ.eval (envL s t) := by
    simp only [pgpZ, pgsZ, Tm.eval, tIs, envL, envP, envR]; push_cast; field_simp; ring
  have hiB : tiB.eval (envL s t) = (B2v s t)⁻¹ := by simp [Tm.eval, tiB, envL, envP, envR]
  simp only [Qc, pq0, pq1, pBk0gp, pBk0G, pBgsG, pcross, Tm.sub, Tm.eval, gR, gZ, hiB,
    lnEll]
  push_cast
  field_simp
  ring

/-- **The eikonal is a field-line label gradient: `B · k = 0`** along the line, for every
shift `c` (`∂ₜΦ ∇t·B` cancels `∇φ·B`, and `∇√ψ̃ · B = 0`). -/
theorem lnB_inner_lnEik {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (c t : ℝ) :
    ⟪lnB s t, lnEik s c t⟫ = 0 := by
  obtain ⟨hx, hR, hr, hRne⟩ := line_relations hs0 hs t
  have hsne : s ≠ 0 := hs0.ne'
  rw [lnB, B_line hs0 hs, lnEik_eq, inner_cyl]
  simp only [pBR, pBP, pBZ, pkR, pkP, pkZ, pgsR, pgsZ, pPhit, trate, pgtR, pgtZ, pW, pz,
    tX, tY, tR, tr, tiR, tS, tIs, Tm.eval, envL, envP, envR]
  push_cast
  field_simp
  linear_combination (-10000*√2^4*(s : ℝ)^2*Real.sin t - 20000*√2^2*(s : ℝ)^2*Real.sin t -
      2000000*√2^2*(s : ℝ)) * hx
    + (-10000*RS 10 (s : ℝ) t^2*√2^2*Real.sin t -
      20000*√2^2*(s : ℝ)*Real.sin t^2 + 40000*(s : ℝ)) * hR
    + (10000*√2^2*(s : ℝ)^2*Real.sin t^3 -
      10000*√2^2*(s : ℝ)^2*Real.sin t - 40000*(s : ℝ)^2*Real.sin t - 2000000*(s : ℝ)) * hr

/-- `∇√ψ̃` along the line is continuous. -/
theorem continuous_lnGs {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) : Continuous (lnGs s) :=
  continuous_cyl (continuous_phiS hs0 hs) (continuous_tree hs0 hs _) continuous_const
    (continuous_tree hs0 hs _)

/-- The actual field along the line is continuous. -/
theorem continuous_lnB {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) : Continuous (lnB s) := by
  have : lnB s = fun t => cyl (phiS (7 / 4) 10 50 s t) (pBR.eval (envL s t))
      (pBP.eval (envL s t)) (pBZ.eval (envL s t)) := funext fun t => B_line hs0 hs t
  rw [this]
  exact continuous_cyl (continuous_phiS hs0 hs) (continuous_tree hs0 hs _)
    (continuous_tree hs0 hs _) (continuous_tree hs0 hs _)

/-- The field derivative along the line is continuous. -/
theorem continuous_lnDBB {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) :
    Continuous fun t => fieldDeriv (7 / 4) 10 50 (lineS (7 / 4) 10 50 s t) (lnB s t) := by
  have : (fun t => fieldDeriv (7 / 4) 10 50 (lineS (7 / 4) 10 50 s t) (lnB s t)) =
      fun t => cyl (phiS (7 / 4) 10 50 s t) (pGR.eval (envL s t)) 0
        (pGZ.eval (envL s t)) := funext fun t => DBB_line hs0 hs t
  rw [this]
  exact continuous_cyl (continuous_phiS hs0 hs) (continuous_tree hs0 hs _) continuous_const
    (continuous_tree hs0 hs _)

/-- The field never vanishes along the line. -/
theorem lnB_ne {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (t : ℝ) : lnB s t ≠ 0 := by
  rw [lnB, B_line hs0 hs]
  apply cyl_ne_zero
  have hR := RS_pos_r hs0 hs t
  simp only [Tm.eval, pBP, tiR, envL, envP, envR]
  exact mul_ne_zero (by norm_num) (inv_ne_zero hR.ne')

/-- **The ballooning line data of the reactor surface `ψ̃ = s²`** (`1 ≤ s ≤ 25`) for the
eikonal family with shift `c` (`θ_k`): the exact field line `lineS`, the actual field,
pressure gradient and curvature, and the covering-space eikonal gradient
`k = ∇(φ − Φ(s, t)) = k₀ − (σ(t) − c) ∇√ψ̃`. -/
@[expose] def reactorLine {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (c : ℝ) : LineData where
  ℓ := lnEll s
  B := lnB s
  k := lnEik s c
  gp := lnGp s
  κ := lnKappa s
  ℓ_pos t := by
    have hR := RS_pos_r hs0 hs t
    simp only [lnEll, Tm.eval, tell, tr, tiR, envL, envP, envR]
    push_cast
    positivity
  B_ne t := lnB_ne hs0 hs t
  k_ne t := by
    rw [lnEik_eq]
    apply cyl_ne_zero
    have hR := RS_pos_r hs0 hs t
    simp only [Tm.eval, pkP, tiR, envL, envP, envR]
    exact inv_ne_zero hR.ne'
  ℓ_cont := continuous_tree hs0 hs tell
  B_cont := continuous_lnB hs0 hs
  k_cont := by
    have hσ : Continuous (lnSig s) := continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_lnSig hs0 hs t).continuousAt
    have : lnEik s c = fun t => lnK0 s t - (lnSig s t - c) • lnGs s t := rfl
    rw [this]
    refine Continuous.sub ?_ ((hσ.sub continuous_const).smul (continuous_lnGs hs0 hs))
    exact continuous_cyl (continuous_phiS hs0 hs) (continuous_tree hs0 hs _)
      (continuous_tree hs0 hs _) (continuous_tree hs0 hs _)
  gp_cont := by
    have : lnGp s = fun t => (-(3 * ((7 / 4 : ℝ) / 10 ^ 2) ^ 2) * (2 * s)) • lnGs s t :=
      funext fun t => lnGp_eq hs0 t
    rw [this]
    exact (continuous_lnGs hs0 hs).const_smul (-(3 * ((7 / 4 : ℝ) / 10 ^ 2) ^ 2) * (2 * s))
  κ_cont := by
    have hB := continuous_lnB hs0 hs
    have hD := continuous_lnDBB hs0 hs
    have hn : ∀ t, ‖lnB s t‖ ^ 2 ≠ 0 := fun t => by
      have := norm_pos_iff.mpr (lnB_ne hs0 hs t); positivity
    have h1 : Continuous fun t => (⟪lnB s t, fieldDeriv (7 / 4) 10 50 (lineS (7 / 4) 10 50 s t)
        (lnB s t)⟫ / ‖lnB s t‖ ^ 2 : ℝ) :=
      Continuous.div (continuous_inner.comp (hB.prodMk hD)) (hB.norm.pow 2) hn
    have h0 : Continuous fun t => ((‖lnB s t‖ ^ 2)⁻¹ : ℝ) := (hB.norm.pow 2).inv₀ hn
    unfold lnKappa fieldLineCurvature
    exact h0.smul (hD.sub (h1.smul hB))

/-- The bending coefficient of the reactor line is `P(t, σ(t) − c)`. -/
theorem reactorLine_P {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (c t : ℝ) :
    (reactorLine hs0 hs c).P t = Pc s t (lnSig s t - c) := by
  simp only [LineData.P, reactorLine, lnEik]
  exact P_geom hs0 hs t _

/-- The drive of the reactor line is `Q(t, σ(t) − c)`. -/
theorem reactorLine_Q {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (c t : ℝ) :
    (reactorLine hs0 hs c).Q t = Qc s t (lnSig s t - c) := by
  simp only [LineData.Q, reactorLine, lnEik]
  exact Q_geom hs0 hs t _


/-! ## The eikonal is the covering-space gradient of the field-line label -/

/-- **`∇√ψ̃` and `∇t` are the dual basis of the meridian coordinates `(s, t) ↦ (R, z)`**:
with the actual partial derivatives `∂ₛR, ∂ₜR, ∂ₛz, ∂ₜz` of `jacobian_eq`
(`SolovevMercierCertified`), `∇√ψ̃ · ∂ₛX = 1`, `∇√ψ̃ · ∂ₜX = 0`, `∇t · ∂ₛX = 0`, `∇t · ∂ₜX = 1`.
By the chain rule these are the gradients of the coordinate functions `√ψ̃` and `t`, so
`lnEik = ∇(φ − Φ(√ψ̃, t)) + c ∇√ψ̃` with `∂ₜΦ = −rate/R³` (`hasDerivAt_phiS`) and
`∂ₛ∂ₜΦ = σ'` (`lnD_eq_mixed`). -/
theorem meridian_dual {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (t : ℝ) :
    pgsR.eval (envL s t) * (Real.sin t / RS 10 s t) + pgsZ.eval (envL s t) *
        ((√2 * Real.cos t * RS 10 s t - √2 * s * Real.cos t * (Real.sin t / RS 10 s t)) /
          RS 10 s t ^ 2) = 1 ∧
    pgsR.eval (envL s t) * (s * Real.cos t / RS 10 s t) + pgsZ.eval (envL s t) *
        ((√2 * s * -Real.sin t * RS 10 s t - √2 * s * Real.cos t * (s * Real.cos t / RS 10 s t)) /
          RS 10 s t ^ 2) = 0 ∧
    pgtR.eval (envL s t) * (Real.sin t / RS 10 s t) + pgtZ.eval (envL s t) *
        ((√2 * Real.cos t * RS 10 s t - √2 * s * Real.cos t * (Real.sin t / RS 10 s t)) /
          RS 10 s t ^ 2) = 0 ∧
    pgtR.eval (envL s t) * (s * Real.cos t / RS 10 s t) + pgtZ.eval (envL s t) *
        ((√2 * s * -Real.sin t * RS 10 s t - √2 * s * Real.cos t * (s * Real.cos t / RS 10 s t)) /
          RS 10 s t ^ 2) = 1 := by
  obtain ⟨hx, hR, hr, hRne⟩ := line_relations hs0 hs t
  have hsne : s ≠ 0 := hs0.ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [pgsR, pgsZ, pW, pz, tX, tR, tr, tiR, tS, tIs, Tm.eval, envL, envP, envR]
    push_cast
    field_simp
    linear_combination (RS 10 s t^2*√2^2*s) * hx + (RS 10 s t^2*Real.sin t
      - √2^2*s*Real.sin t^2 + √2^2*s + 2*s*Real.sin t^2 - 2*s) * hR
      + (-2*s^2*Real.sin t^3 + 2*s^2*Real.sin t - 100*s*Real.sin t^2 + 100*s) * hr
  · simp only [pgsR, pgsZ, pW, pz, tX, tR, tr, tiR, tS, tIs, Tm.eval, envL, envP, envR]
    push_cast
    field_simp
    linear_combination (RS 10 s t^2*Real.cos t - √2^2*s*Real.cos t*Real.sin t
      + 2*s*Real.cos t*Real.sin t) * hR + (-2*s^2*Real.cos t*Real.sin t^2
      - 100*s*Real.cos t*Real.sin t) * hr
  · simp only [pgtR, pgtZ, tX, tY, tR, tr, tiR, tS, tIs, Tm.eval, envL, envP, envR]
    push_cast
    field_simp
    linear_combination (-√2^2*Real.cos t*Real.sin t) * hR + (-s*Real.cos t*Real.sin t^2
      - 100*Real.cos t*Real.sin t) * hr
  · simp only [pgtR, pgtZ, tX, tY, tR, tr, tiR, tS, tIs, Tm.eval, envL, envP, envR]
    push_cast
    field_simp
    linear_combination (√2^2*s*Real.sin t + 2*s*Real.sin t + 200) * hx
      + (√2^2*Real.sin t^2 - 2) * hR + (s*Real.sin t^3 + s*Real.sin t
      + 100*Real.sin t^2) * hr

/-- The winding rate: `F L²/(√2 A) = 10000 √2/7`. -/
theorem rateS_eq : rateS (7 / 4) 10 50 = 10000 * √2 / 7 := by
  have h2 : (0:ℝ) < √2 := by positivity
  have hr : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold rateS
  field_simp
  rw [hr]
  norm_num

/-- `∂ₜΦ = −rate/R³` along the line (the toroidal winding of the exact field line). -/
theorem hasDerivAt_phiS {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (t : ℝ) :
    HasDerivAt (phiS (7 / 4) 10 50 s) (pPhit.eval (envL s t)) t := by
  have hc := continuous_invCube (L := 10) (s := s) hs0.le (by norm_num; linarith)
  have h := ((hc.integral_hasStrictDerivAt 0 t).hasDerivAt.const_mul (rateS (7 / 4) 10 50)).neg
  unfold phiS
  refine h.congr_deriv ?_
  rw [rateS_eq]
  simp only [pPhit, trate, tr, tiR, Tm.eval, envL, envP, envR]
  push_cast
  ring

/-- `k₀ = ∇φ − ∂ₜΦ ∇t` with the actual `∇φ` and `∂ₜΦ`. -/
theorem lnK0_eq {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (t : ℝ) :
    lnK0 s t = phiGrad (lineS (7 / 4) 10 50 s t) - pPhit.eval (envL s t) • lnGt s t := by
  rw [phiGrad_line hs0 hs, lnGt, smul_cyl, cyl_sub, lnK0]
  simp only [pkR, pkZ, Tm.eval]
  ring_nf

/-- **`σ' = ∂ₛ∂ₜΦ`**: the secular rate is the derivative in the surface label of the winding
rate `∂ₜΦ = −rate R⁻³` (so `σ(t) = ∂ₛΦ(s, t) + const` by Fubini/FTC, standard). -/
theorem lnD_eq_mixed {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (t : ℝ) :
    HasDerivAt (fun σ : ℝ => -(rateS (7 / 4) 10 50 * (RS 10 σ t ^ 3)⁻¹)) (lnD s t) s := by
  have hsI : s ∈ Ioo (-45 : ℝ) 45 := ⟨by linarith, by linarith⟩
  have h := ((PlasmaLean.Design.SolovevMercierCertified.hasDerivAt_invRS3 hsI t).const_mul
    (rateS (7 / 4) 10 50)).neg
  refine h.congr_deriv ?_
  have hR := RS_pos_r hs0 hs t
  rw [rateS_eq]
  simp only [lnD, pd, trate, tY, tr, tiR, Tm.eval, envL, envP, envR]
  push_cast
  field_simp


end PlasmaLean.Design.SolovevBallooning
