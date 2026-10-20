/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanEquilibrium
public import PlasmaLean.Theory.Stability.MercierShearless
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Local (Mercier) stability verdict for Landreman's explicit 3-D equilibria

Sources: M. Landreman, *Analytic toroidal 3D MHD equilibria and steady Euler flows with
invariant surfaces*, arXiv:2609.26742 **v2** (28 Sep 2026; LaTeX source retrieved 21 Oct 2026),
§2 (family 1, `ι ≡ 2`) and §3 (family 2, sheared). **The paper does not discuss stability**:
its source contains no mention of magnetic well, Mercier, interchange or ballooning; the
word "Mercier" appears only as a citation for near-axis expansions, and the conclusions list
other extensions (other periods, irrational constant `ι`, non-stellarator-symmetric, vacuum,
quasisymmetric). Stability criterion: the general Mercier index of
`PlasmaLean.Stability.MercierGeneral` (Landreman–Jorge 2020, eq. (3.1)) — a **SUPPLIED
formula**, whose derivation from `δW` is not formalized; `D_Merc > 0` is a necessary local
(interchange) condition only.

## Family 1 (`ι ≡ 2`, zero shear): Mercier UNSTABLE on every flux surface (proved)

* Field-line coordinates (paper (2.12)–(2.16)), verified here: `emb_mem_U`, `field_emb`
  (`B(r) = ∂_ζ r`), `psi_emb` (`ψ = (u + ε/2)² + v²`), `gradH_emb_ne_zero` (`∇ψ ≠ 0` off the
  axis), and the **constant Jacobian** `emb_jacobian` (`det ∂(x,y,z)/∂(u,v,ζ) = -ab`, with the
  partial derivatives proved to be the actual derivatives). Hence `V = 2π²abψ` and
  `Φ = πabψ` are both linear in `ψ` (paper (2.20)–(2.21); the change-of-variables/covering
  step is not formalized), so `V'' = 0` in the toroidal-flux label: **neither well nor hill**.
  Every field line closes (`fieldLine_closed`) with `ι ≡ 2`, so `ι' = 0`.
* With `ι' = 0` and `V'' = 0` the Mercier index reduces to
  `(∫B·Ξ w)² - ∫|Ξ|² w ∫B² w`, which is `< 0` by strict Cauchy–Schwarz because force balance
  makes `Ξ = μ₀J - I'B` nowhere parallel to `B` (`MercierShearless`). Result:
  `family1_mercier_unstable` — for EVERY surface `0 < ψ₀`, `|ε|/2 + √ψ₀ < 1/2`, every sampling
  measure, every positive weight, every `I'`, `s_G`, `s_ψ`, `p'`: `D_Merc < 0`. So the honest
  statement is stronger than "marginal": the supplied criterion is strictly violated.
  The hill+weak-shear lemma `mercierIndex_neg_of_hill` is what is used (hill term `= 0`).
* Caveat: for exactly shearless, closed-line surfaces Mercier's asymptotics degenerate; the
  natural closed-line interchange criterion involves `U = ∮ dl/|B|`, and
  `closedLine_specificVolume` proves `U = 2π` on every field line, so `U' = 0`: that criterion
  is marginal at this order. The library's cylindrical `MercierStableOn` rejects shearless
  surfaces by definition; the general `mercierIndex` used here has no such guard.

## Family 2 (`ε = 1/4`, `S = 4`, `λ = 15`): Mercier UNSTABLE (numerical, hill-driven)

* Numerics (`scripts/landreman_mercier_oracle.py`, untrusted; a 2-D and a 1-D route agree to
  `10⁻⁴` or better): `D_Merc < 0` on `k = 0.05, 0.1, 0.3, 0.5, 0.7, 0.9` for both `s_G = ±1`,
  e.g. `k = 1/20`: `ι' ≈ 825`, `s_ψμ₀p'V'' ≈ -75173` (a strong magnetic HILL),
  `∫|Ξ|²w ≈ 6775`, `∫B·Ξ w ≈ -6319`, `∫B²w ≈ 7.59·10⁶`, `D_Merc ≈ -1.0·10⁷`.
* Mechanism (exact reduction, derived by hand, checked numerically, not formalized):
  `V'(ψ_t) = 2π E(k) ι(ψ_t)` with `E = 4K(k)`, so positive shear forces a hill
  (`hill_of_shear`); near the axis `∫B²w ~ 1/k²` and the hill term dominates every other term.
* Lean: `mercierIndex_neg_of_hill_dominates` (general algebraic criterion) and
  `family2_mercier_unstable_of_enclosures` (`k = 1/20`), whose numerical hypotheses need only
  factor-`2.5` accuracy. **Not certified**: no validated quadrature was carried out for
  family 2 (the inputs `ι'`, `V''`, `I'` are `ψ`-derivatives of flux/volume/current integrals
  whose identification with coordinate integrals needs unformalized change of variables and
  Stokes; `∫B·Ξ w` involves a `5·10⁻⁵` cancellation between `∫J·B w` and `I'∫B²w`).
* The verdict depends on parameters: for `λ = 50` the outer surface `k = 9/10` has
  `D_Merc > 0` (strong shear wins), `family2_lam50_outer_stable`; near the axis it is negative
  for all `λ` tested (2, 5, 15, 50).
-/

open scoped RealInnerProductSpace

public section
noncomputable section
namespace PlasmaLean.Design.LandremanMercier
open PlasmaLean.Fields WithLp PlasmaLean.Design.LandremanEquilibrium Real

/-! ## Field-line coordinates (paper (2.12)–(2.16)) -/

/-- `L(q²) = √((1 + √(1 - 4q²))/2)` (paper (2.13)); `L² + q²/L² = 1`. -/
@[expose] def Lq (q2 : ℝ) : ℝ := √((1 + √(1 - 4 * q2)) / 2)

/-- The field-line coordinate map `(u, v, ζ) ↦ x` (paper (2.12)), with `cos 2ζ`, `sin 2ζ`
written as `c² - s²`, `2sc`. -/
@[expose] def emb (a b u v ζ : ℝ) : Space :=
  toLp 2 ![a * (Lq (u ^ 2 + v ^ 2) * cos ζ + (u * cos ζ + v * sin ζ) / Lq (u ^ 2 + v ^ 2)),
    b * (Lq (u ^ 2 + v ^ 2) * sin ζ + (v * cos ζ - u * sin ζ) / Lq (u ^ 2 + v ^ 2)),
    v * (cos ζ ^ 2 - sin ζ ^ 2) - 2 * u * sin ζ * cos ζ]

/-- `∂_ζ` of the coordinate map (which equals the field there, `field_emb`). -/
@[expose] def embVel (a b u v ζ : ℝ) : Space :=
  toLp 2 ![a * (-(Lq (u ^ 2 + v ^ 2) * sin ζ) + (v * cos ζ - u * sin ζ) / Lq (u ^ 2 + v ^ 2)),
    b * (Lq (u ^ 2 + v ^ 2) * cos ζ - (u * cos ζ + v * sin ζ) / Lq (u ^ 2 + v ^ 2)),
    -(4 * v * sin ζ * cos ζ) - 2 * u * (cos ζ ^ 2 - sin ζ ^ 2)]

section Lq
variable {q2 : ℝ}

/-- `L > 0`. -/
theorem Lq_pos : 0 < Lq q2 := Real.sqrt_pos.mpr (by positivity)

/-- `L² = (1 + √(1 - 4q²))/2`. -/
theorem Lq_sq : Lq q2 ^ 2 = (1 + √(1 - 4 * q2)) / 2 := Real.sq_sqrt (by positivity)

/-- `2L² - 1 = √(1 - 4q²)`. -/
theorem two_Lq_sq_sub_one : 2 * Lq q2 ^ 2 - 1 = √(1 - 4 * q2) := by rw [Lq_sq]; ring

/-- `L⁴ - L² + q² = 0` (paper (2.13)), for `4q² ≤ 1`. -/
theorem Lq_rel (h : 4 * q2 ≤ 1) : Lq q2 ^ 4 - Lq q2 ^ 2 + q2 = 0 := by
  have hr := Real.sq_sqrt (show 0 ≤ 1 - 4 * q2 by linarith)
  have : Lq q2 ^ 4 = (Lq q2 ^ 2) ^ 2 := by ring
  rw [this, Lq_sq]
  nlinarith [hr]

/-- `2L² - 1 > 0` for `4q² < 1`. -/
theorem two_Lq_sq_sub_one_pos (h : 4 * q2 < 1) : 0 < 2 * Lq q2 ^ 2 - 1 := by
  rw [two_Lq_sq_sub_one]; exact Real.sqrt_pos.mpr (by linarith)

end Lq

section Emb
variable {a b u v ζ : ℝ}

/-- `s = x²/a² + y²/b² = 1 + 2(u cos 2ζ + v sin 2ζ)` on the coordinate image. -/
theorem sF_emb (ha : a ≠ 0) (hb : b ≠ 0) (hq : 4 * (u ^ 2 + v ^ 2) ≤ 1) :
    sF a b (emb a b u v ζ) = 1 + 2 * (u * (cos ζ ^ 2 - sin ζ ^ 2) + 2 * v * sin ζ * cos ζ) := by
  have hL := Lq_rel hq
  have hL0 := (Lq_pos (q2 := u ^ 2 + v ^ 2)).ne'
  have hcs := sin_sq_add_cos_sq ζ
  simp only [sF, emb]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  generalize Lq (u ^ 2 + v ^ 2) = L at *
  generalize cos ζ = c at *
  generalize sin ζ = s at *
  field_simp
  grind

/-- The radicand on the coordinate image: `1 - (1-s)² - 4z² = (2L² - 1)²`. -/
theorem rad_emb (ha : a ≠ 0) (hb : b ≠ 0) (hq : 4 * (u ^ 2 + v ^ 2) ≤ 1) :
    rad a b (emb a b u v ζ) = (2 * Lq (u ^ 2 + v ^ 2) ^ 2 - 1) ^ 2 := by
  have hL := Lq_rel hq
  have hcs := sin_sq_add_cos_sq ζ
  rw [rad, sF_emb ha hb hq]
  simp only [emb]
  simp only [sub_add_cancel_left, even_two, Even.neg_pow, Fin.isValue, Matrix.cons_val]
  generalize Lq (u ^ 2 + v ^ 2) = L at *
  generalize cos ζ = c at *
  generalize sin ζ = s at *
  grind

/-- The coordinate image of the disc `4(u² + v²) < 1` lies in `𝒰`. -/
theorem emb_mem_U (ha : a ≠ 0) (hb : b ≠ 0) (hq : 4 * (u ^ 2 + v ^ 2) < 1) :
    emb a b u v ζ ∈ U a b := by
  change 0 < rad a b _
  rw [rad_emb ha hb hq.le]
  exact pow_pos (two_Lq_sq_sub_one_pos hq) 2

/-- `F = 2L² - 1` on the coordinate image. -/
theorem Fr_emb (ha : a ≠ 0) (hb : b ≠ 0) (hq : 4 * (u ^ 2 + v ^ 2) < 1) :
    Fr a b (emb a b u v ζ) = 2 * Lq (u ^ 2 + v ^ 2) ^ 2 - 1 := by
  rw [Fr, rad_emb ha hb hq.le, Real.sqrt_sq (two_Lq_sq_sub_one_pos hq).le]

/-- **The field on the coordinate image is `∂_ζ` of the coordinate map** (paper, below
(2.13): "direct substitution confirms `B(r) = ∂_ζ r`"). -/
theorem field_emb (ha : a ≠ 0) (hb : b ≠ 0) (hq : 4 * (u ^ 2 + v ^ 2) < 1) :
    field a b (emb a b u v ζ) = embVel a b u v ζ := by
  have hL := Lq_rel hq.le
  have hL0 := (Lq_pos (q2 := u ^ 2 + v ^ 2)).ne'
  have hcs := sin_sq_add_cos_sq ζ
  have hs := sF_emb (ζ := ζ) ha hb hq.le
  have hs0 : sF a b (emb a b u v ζ) ≠ 0 := (sF_pos (emb_mem_U ha hb hq)).ne'
  have hF := Fr_emb (ζ := ζ) ha hb hq
  ext i
  fin_cases i
  · simp only [field, N0, hF, Fin.zero_eta, Fin.isValue]
    rw [hs] at hs0 ⊢
    simp only [emb, Fin.isValue, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      sub_add_cancel_left, embVel]
    generalize Lq (u ^ 2 + v ^ 2) = L at *
    generalize cos ζ = c at *
    generalize sin ζ = s at *
    field_simp
    grind
  · simp only [field, N1, hF, Fin.mk_one, Fin.isValue]
    rw [hs] at hs0 ⊢
    simp only [emb, Fin.isValue, Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero,
      sub_add_cancel_left, embVel]
    generalize Lq (u ^ 2 + v ^ 2) = L at *
    generalize cos ζ = c at *
    generalize sin ζ = s at *
    field_simp
    grind
  · simp only [field, Fin.reduceFinMk, Fin.isValue]
    rw [hs]
    simp [embVel]
    ring

/-- **The flux label on the coordinate image** (paper (2.15)):
`ψ(r(u, v, ζ)) = (u + ε/2)² + v²`, `ε = (a² - b²)/2`. -/
theorem psi_emb (ha : a ≠ 0) (hb : b ≠ 0) (hq : 4 * (u ^ 2 + v ^ 2) < 1) :
    psi a b (emb a b u v ζ) = (u + epsAB a b / 2) ^ 2 + v ^ 2 := by
  have hL := Lq_rel hq.le
  have hL0 := (Lq_pos (q2 := u ^ 2 + v ^ 2)).ne'
  have hcs := sin_sq_add_cos_sq ζ
  simp only [psi, H, field_emb ha hb hq, Qf, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs,
    Fin.sum_univ_three, epsAB]
  simp only [emb, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, embVel]
  generalize Lq (u ^ 2 + v ^ 2) = L at *
  generalize cos ζ = c at *
  generalize sin ζ = s at *
  field_simp
  grind

/-- Differentiability of a curve from that of its coordinates. -/
theorem curve_differentiableAt {f : ℝ → Space} {t : ℝ}
    (h : ∀ k, DifferentiableAt ℝ (fun s => f s k) t) : DifferentiableAt ℝ f t :=
  (curve_hasDerivAt (v := toLp 2 fun k => deriv (fun s => f s k) t)
    (fun k => by simpa using (h k).hasDerivAt)).differentiableAt

/-- Along a straight line `t ↦ (u + t p, v + t r)` in the label plane (inside the disc), the
coordinate map is differentiable. -/
theorem emb_line_differentiableAt (p r : ℝ) (hq : 4 * (u ^ 2 + v ^ 2) < 1) :
    DifferentiableAt ℝ (fun t => emb a b (u + t * p) (v + t * r) ζ) 0 := by
  have hQ : DifferentiableAt ℝ (fun t : ℝ => (u + t * p) ^ 2 + (v + t * r) ^ 2) 0 := by fun_prop
  have hR : DifferentiableAt ℝ (fun t : ℝ => √(1 - 4 * ((u + t * p) ^ 2 + (v + t * r) ^ 2))) 0 :=
    (hQ.const_mul 4).const_sub 1 |>.sqrt (by simp; linarith)
  have hL : DifferentiableAt ℝ (fun t : ℝ => Lq ((u + t * p) ^ 2 + (v + t * r) ^ 2)) 0 := by
    unfold Lq
    exact ((hR.const_add 1).div_const 2).sqrt (by
      simp only [zero_mul, add_zero, ne_eq, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false]
      positivity)
  have hL0 : Lq ((u + 0 * p) ^ 2 + (v + 0 * r) ^ 2) ≠ 0 := Lq_pos.ne'
  have hu : DifferentiableAt ℝ (fun t : ℝ => u + t * p) 0 := by fun_prop
  have hv : DifferentiableAt ℝ (fun t : ℝ => v + t * r) 0 := by fun_prop
  apply curve_differentiableAt
  intro k
  fin_cases k
  · simp only [emb, Fin.zero_eta, Fin.isValue, PiLp.toLp_apply, Matrix.cons_val_zero]
    exact ((hL.mul_const _).add (((hu.mul_const _).add (hv.mul_const _)).div hL hL0)).const_mul a
  · simp only [emb, Fin.mk_one, Fin.isValue, PiLp.toLp_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    exact ((hL.mul_const _).add (((hv.mul_const _).sub (hu.mul_const _)).div hL hL0)).const_mul b
  · simp only [emb, Fin.reduceFinMk, Fin.isValue, PiLp.toLp_apply, Matrix.cons_val]
    fun_prop

/-- **`∇ψ ≠ 0` off the magnetic axis** on the coordinate image: if `4(u² + v²) < 1` and
`ψ = (u + ε/2)² + v² > 0` then `∇H = 2∇ψ ≠ 0` at `r(u, v, ζ)`. Proof: along the radial
label line `t ↦ (u + t(u + ε/2), (1 + t) v)` the flux label is `(1 + t)² ψ`, whose derivative
`2ψ` at `t = 0` equals `⟪∇ψ, γ'(0)⟫`. -/
theorem gradH_emb_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) (hq : 4 * (u ^ 2 + v ^ 2) < 1)
    (hψ : 0 < (u + epsAB a b / 2) ^ 2 + v ^ 2) : gradH a b (emb a b u v ζ) ≠ 0 := by
  set e := epsAB a b / 2
  set P := (u + e) ^ 2 + v ^ 2
  set γ : ℝ → Space := fun t => emb a b (u + t * (u + e)) (v + t * v) ζ
  have hγ := (emb_line_differentiableAt (a := a) (b := b) (ζ := ζ) (u + e) v hq).hasDerivAt
  have hγ0 : γ 0 = emb a b u v ζ := by simp [γ]
  have hmem : γ 0 ∈ U a b := by rw [hγ0]; exact emb_mem_U ha hb hq
  have hcomp := (psi_hasFDerivAt a b hmem).comp_hasDerivAt (0 : ℝ) hγ
  -- eventually the line stays in the disc, where `ψ = (1+t)² P`
  have hcont : Continuous fun t : ℝ => 4 * ((u + t * (u + e)) ^ 2 + (v + t * v) ^ 2) := by
    fun_prop
  have hev : ∀ᶠ t in nhds (0 : ℝ), 4 * ((u + t * (u + e)) ^ 2 + (v + t * v) ^ 2) < 1 :=
    hcont.continuousAt.eventually_lt continuousAt_const (by simpa using hq)
  have heq : (fun t => (1 + t) ^ 2 * P) =ᶠ[nhds (0 : ℝ)] (psi a b ∘ γ) := by
    filter_upwards [hev] with t ht
    simp only [Function.comp, γ]
    rw [psi_emb ha hb ht]
    simp only [P, e]
    ring
  have hpoly : HasDerivAt (fun t : ℝ => (1 + t) ^ 2 * P) (2 * P) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).const_add 1).pow 2).mul_const P
    simpa using this
  have huniq := hpoly.unique (hcomp.congr_of_eventuallyEq heq)
  intro h0
  rw [hγ0, h0] at huniq
  simp at huniq
  linarith

/-! ### The Jacobian of the field-line coordinates is constant (paper (2.12)) -/

/-- `dL/d(q²) = -1/(2L(2L² - 1))`. -/
theorem hasDerivAt_Lq {q2 : ℝ} (h : 4 * q2 < 1) :
    HasDerivAt Lq (-1 / (2 * Lq q2 * (2 * Lq q2 ^ 2 - 1))) q2 := by
  have hr : 0 < 1 - 4 * q2 := by linarith
  have h1 := (((hasDerivAt_id q2).const_mul 4).const_sub 1).sqrt hr.ne'
  have h2 := ((h1.const_add 1).div_const 2).sqrt
    (show (1 + √(1 - 4 * id q2)) / 2 ≠ 0 by
      simp only [id_eq, ne_eq, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false]; positivity)
  refine h2.congr_deriv ?_
  have e1 : √(1 - 4 * id q2) = 2 * Lq q2 ^ 2 - 1 := by simp [two_Lq_sq_sub_one]
  have e2 : √((1 + √(1 - 4 * id q2)) / 2) = Lq q2 := by simp [Lq]
  rw [e2, e1]
  have := two_Lq_sq_sub_one_pos h
  have := (Lq_pos (q2 := q2)).ne'
  field_simp
  ring

/-- `∂L/∂u = -u/(L(2L² - 1))` (write `Lu`; similarly `∂L/∂v = -v/(L(2L² - 1))`). -/
@[expose] def Lder (u v w : ℝ) : ℝ :=
  -w / (Lq (u ^ 2 + v ^ 2) * (2 * Lq (u ^ 2 + v ^ 2) ^ 2 - 1))

/-- `∂_u` of the coordinate map. -/
@[expose] def embDu (a b u v ζ : ℝ) : Space :=
  toLp 2 ![a * (Lder u v u * cos ζ + cos ζ / Lq (u ^ 2 + v ^ 2) -
      (u * cos ζ + v * sin ζ) * Lder u v u / Lq (u ^ 2 + v ^ 2) ^ 2),
    b * (Lder u v u * sin ζ - sin ζ / Lq (u ^ 2 + v ^ 2) -
      (v * cos ζ - u * sin ζ) * Lder u v u / Lq (u ^ 2 + v ^ 2) ^ 2),
    -(2 * sin ζ * cos ζ)]

/-- `∂_v` of the coordinate map. -/
@[expose] def embDv (a b u v ζ : ℝ) : Space :=
  toLp 2 ![a * (Lder u v v * cos ζ + sin ζ / Lq (u ^ 2 + v ^ 2) -
      (u * cos ζ + v * sin ζ) * Lder u v v / Lq (u ^ 2 + v ^ 2) ^ 2),
    b * (Lder u v v * sin ζ + cos ζ / Lq (u ^ 2 + v ^ 2) -
      (v * cos ζ - u * sin ζ) * Lder u v v / Lq (u ^ 2 + v ^ 2) ^ 2),
    cos ζ ^ 2 - sin ζ ^ 2]

/-- `∂_u r = embDu` (actual derivative). -/
theorem hasDerivAt_emb_u (hq : 4 * (u ^ 2 + v ^ 2) < 1) :
    HasDerivAt (fun w => emb a b w v ζ) (embDu a b u v ζ) u := by
  have hLd : HasDerivAt (fun w => Lq (w ^ 2 + v ^ 2)) (Lder u v u) u := by
    have := (hasDerivAt_Lq hq).comp u (((hasDerivAt_id u).pow 2).add_const (v ^ 2))
    refine this.congr_deriv ?_
    have := two_Lq_sq_sub_one_pos hq
    have := (Lq_pos (q2 := u ^ 2 + v ^ 2)).ne'
    simp [Lder]
    field_simp
  have hL0 : Lq (u ^ 2 + v ^ 2) ≠ 0 := Lq_pos.ne'
  apply curve_hasDerivAt
  intro k
  fin_cases k
  · have := (((hLd.mul_const (cos ζ)).add ((((hasDerivAt_id u).mul_const (cos ζ)).add_const
      (v * sin ζ)).div hLd hL0)).const_mul a)
    convert this using 1
    · funext w; simp [emb]
    · simp [embDu, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      field_simp
      ring
  · have := (((hLd.mul_const (sin ζ)).add (((((hasDerivAt_id u).mul_const (sin ζ)).const_sub
      (v * cos ζ))).div hLd hL0)).const_mul b)
    convert this using 1
    · funext w; simp [emb]
    · simp [embDu, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      field_simp
      ring
  · have := ((hasDerivAt_id u).mul_const (2 * sin ζ * cos ζ)).const_sub
      (v * (cos ζ ^ 2 - sin ζ ^ 2))
    convert this using 1
    · funext w; simp [emb]; ring
    · simp [embDu, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]

/-- `∂_v r = embDv` (actual derivative). -/
theorem hasDerivAt_emb_v (hq : 4 * (u ^ 2 + v ^ 2) < 1) :
    HasDerivAt (fun w => emb a b u w ζ) (embDv a b u v ζ) v := by
  have hLd : HasDerivAt (fun w => Lq (u ^ 2 + w ^ 2)) (Lder u v v) v := by
    have := (hasDerivAt_Lq hq).comp v (((hasDerivAt_id v).pow 2).const_add (u ^ 2))
    refine this.congr_deriv ?_
    have := two_Lq_sq_sub_one_pos hq
    have := (Lq_pos (q2 := u ^ 2 + v ^ 2)).ne'
    simp [Lder]
    field_simp
  have hL0 : Lq (u ^ 2 + v ^ 2) ≠ 0 := Lq_pos.ne'
  apply curve_hasDerivAt
  intro k
  fin_cases k
  · have := (((hLd.mul_const (cos ζ)).add ((((hasDerivAt_id v).mul_const (sin ζ)).const_add
      (u * cos ζ)).div hLd hL0)).const_mul a)
    convert this using 1
    · funext w; simp [emb]
    · simp [embDv, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      field_simp
      ring
  · have := (((hLd.mul_const (sin ζ)).add (((((hasDerivAt_id v).mul_const (cos ζ)).sub_const
      (u * sin ζ))).div hLd hL0)).const_mul b)
    convert this using 1
    · funext w; simp [emb]
    · simp [embDv, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      field_simp
      ring
  · have := ((hasDerivAt_id v).mul_const (cos ζ ^ 2 - sin ζ ^ 2)).sub_const
      (2 * u * sin ζ * cos ζ)
    convert this using 1
    · funext w; simp [emb]
    · simp [embDv, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]

/-- `∂_ζ r = embVel` (actual derivative). -/
theorem hasDerivAt_emb_zeta : HasDerivAt (fun w => emb a b u v w) (embVel a b u v ζ) ζ := by
  set L := Lq (u ^ 2 + v ^ 2)
  apply curve_hasDerivAt
  intro k
  fin_cases k
  · have := ((((hasDerivAt_cos ζ).const_mul L).add ((((hasDerivAt_cos ζ).const_mul u).add
      ((hasDerivAt_sin ζ).const_mul v)).div_const L)).const_mul a)
    convert this using 1
    · funext w; simp [emb, L, mul_comm]
    · simp [embVel, L, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      ring
  · have := ((((hasDerivAt_sin ζ).const_mul L).add ((((hasDerivAt_cos ζ).const_mul v).sub
      ((hasDerivAt_sin ζ).const_mul u)).div_const L)).const_mul b)
    convert this using 1
    · funext w; simp [emb, L, mul_comm]
    · simp [embVel, L, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      ring
  · have := ((((hasDerivAt_cos ζ).pow 2).sub ((hasDerivAt_sin ζ).pow 2)).const_mul v).sub
      ((((hasDerivAt_sin ζ).mul (hasDerivAt_cos ζ))).const_mul (2 * u))
    convert this using 1
    · funext w; simp [emb]; ring
    · simp [embVel, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      ring

/-- **Constant Jacobian** (paper (2.12)): `det ∂(x, y, z)/∂(u, v, ζ) = r_u · (r_v × r_ζ) = -ab`
at every point of the disc `4(u² + v²) < 1`. Consequently the volume element is
`ab du dv dζ`; with `(u, v) = (-ε/2 + √ψ cos α, √ψ sin α)` (`du dv = dψ dα/2`) this gives
`dV/dψ = 2π² ab` and toroidal flux `Φ = π ab ψ` (paper (2.20)–(2.21)), both linear in `ψ`, so
`V''(ψ_t) = 0` in the toroidal-flux label (the change-of-variables/covering step itself is
not formalized). -/
theorem emb_jacobian (hq : 4 * (u ^ 2 + v ^ 2) < 1) :
    ⟪embDu a b u v ζ, cross (embDv a b u v ζ) (embVel a b u v ζ)⟫ = -(a * b) := by
  have hL := Lq_rel hq.le
  have hL0 := (Lq_pos (q2 := u ^ 2 + v ^ 2)).ne'
  have hD := (two_Lq_sq_sub_one_pos hq).ne'
  have hcs := sin_sq_add_cos_sq ζ
  rw [inner_coords]
  simp only [Fin.isValue, embDu, Lder, Matrix.cons_val_zero, cross, embDv, embVel, cross_apply,
    Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val_one, Matrix.cons_val, neg_mul]
  generalize Lq (u ^ 2 + v ^ 2) = L at *
  generalize cos ζ = c at *
  generalize sin ζ = s at *
  field_simp
  grind

end Emb

/-! ## Family 1 is Mercier unstable on every flux surface -/

/-- The point of the flux surface `ψ = ψ₀` with surface angles `(α, ζ)` (paper (2.16)):
`r(-ε/2 + √ψ₀ cos α, √ψ₀ sin α, ζ)`. -/
@[expose] def surfPt (a b ψ₀ α ζ : ℝ) : Space :=
  emb a b (-(epsAB a b / 2) + √ψ₀ * cos α) (√ψ₀ * sin α) ζ

/-- Surfaces with `|ε|/2 + √ψ₀ < 1/2` (i.e. `ψ₀ < (1-|ε|)²/4`, paper (2.17)) stay inside the
label disc `4(u² + v²) < 1`. -/
theorem surf_in_disc {ε ψ₀ α : ℝ} (hin : |ε| / 2 + √ψ₀ < 1 / 2) :
    4 * ((-(ε / 2) + √ψ₀ * cos α) ^ 2 + (√ψ₀ * sin α) ^ 2) < 1 := by
  have hρ := Real.sqrt_nonneg ψ₀
  have hc := sin_sq_add_cos_sq α
  have hc1 := neg_one_le_cos α
  have hc2 := cos_le_one α
  have he := abs_nonneg ε
  have hle : (-(ε / 2) + √ψ₀ * cos α) ^ 2 + (√ψ₀ * sin α) ^ 2 ≤ (|ε| / 2 + √ψ₀) ^ 2 := by
    have : -(ε * cos α) ≤ |ε| := by
      have := abs_mul ε (cos α)
      have : |ε * cos α| ≤ |ε| := by
        rw [abs_mul]; exact mul_le_of_le_one_right he (abs_cos_le_one α)
      linarith [neg_abs_le (ε * cos α)]
    have e1 : (-(ε / 2) + √ψ₀ * cos α) ^ 2 + (√ψ₀ * sin α) ^ 2 =
        ε ^ 2 / 4 + √ψ₀ * (-(ε * cos α)) + √ψ₀ ^ 2 * (sin α ^ 2 + cos α ^ 2) := by ring
    rw [e1, hc, add_sq, div_pow, sq_abs]
    nlinarith [mul_le_mul_of_nonneg_left this hρ]
  have h0 : 0 ≤ |ε| / 2 + √ψ₀ := by positivity
  nlinarith

/-- Sanity: `surfPt` lies on the flux surface `ψ = ψ₀`, inside `𝒰`. -/
theorem surfPt_on_surface {a b ψ₀ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hψ₀ : 0 ≤ ψ₀)
    (hin : |epsAB a b| / 2 + √ψ₀ < 1 / 2) (α ζ : ℝ) :
    surfPt a b ψ₀ α ζ ∈ U a b ∧ psi a b (surfPt a b ψ₀ α ζ) = ψ₀ := by
  have hd := surf_in_disc (α := α) hin
  refine ⟨emb_mem_U ha hb hd, ?_⟩
  rw [surfPt, psi_emb ha hb hd]
  have := Real.sq_sqrt hψ₀
  have := sin_sq_add_cos_sq α
  nlinarith

/-- Off the axis the pressure gradient does not vanish on the surface. -/
theorem pressureGrad_surfPt_ne_zero {a b ψ₀ μ₀ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hμ : μ₀ ≠ 0)
    (hψ₀ : 0 < ψ₀) (hin : |epsAB a b| / 2 + √ψ₀ < 1 / 2) (α ζ : ℝ) :
    pressureGrad μ₀ a b (surfPt a b ψ₀ α ζ) ≠ 0 := by
  have hd := surf_in_disc (α := α) hin
  have hP : 0 < (-(epsAB a b / 2) + √ψ₀ * cos α + epsAB a b / 2) ^ 2 + (√ψ₀ * sin α) ^ 2 := by
    have := Real.sq_sqrt hψ₀.le
    have := sin_sq_add_cos_sq α
    nlinarith
  have hg := gradH_emb_ne_zero (ζ := ζ) ha hb hd hP
  rw [pressureGrad, surfPt]
  exact smul_ne_zero (by simpa using hμ) hg

/-- Force balance at the surface points, in `cross` form: `J × B = ∇p`. -/
theorem cross_surfPt {a b ψ₀ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (μ₀ : ℝ) (hψ₀ : 0 ≤ ψ₀)
    (hin : |epsAB a b| / 2 + √ψ₀ < 1 / 2) (α ζ : ℝ) :
    cross (current μ₀ a b (surfPt a b ψ₀ α ζ)) (field a b (surfPt a b ψ₀ α ζ)) =
      pressureGrad μ₀ a b (surfPt a b ψ₀ α ζ) := by
  have hfb := (force_balance ha hb μ₀ (surfPt_on_surface ha hb hψ₀ hin α ζ).1).balance
  unfold cross
  rw [hfb]

open MeasureTheory PlasmaLean.Stability.MercierGeneral PlasmaLean.Stability.MercierShearless in
/-- **Family 1 is Mercier unstable on every flux surface.** Let `0 < ψ₀` with
`|ε|/2 + √ψ₀ < 1/2` (any surface of the plasma `Ω_δ`, paper (2.17)), and let the surface be
sampled by surface angles `α, ζ : P → ℝ` on a nonzero measure space `P` (e.g. Lebesgue
measure on `[0, 2π]²`). Take the ACTUAL field `B = field a b` and Ampère current
`J = current μ₀ a b` at the surface points, `Ξ = μ₀ J - I' B` for an ARBITRARY value `I'`, and
an ARBITRARY positive weight `w` (in the source `w = 1/|∇ψ|³` times the area element). With
`ι' = 0` (every field line closes, `ι ≡ 2`) and `V'' = 0` (`emb_jacobian`: `V` and the
toroidal flux are both linear in `ψ`), the general Mercier index is negative:
the Mercier criterion is violated, for every choice of the signs `s_G, s_ψ` and of `p'`. -/
theorem family1_mercier_unstable {a b ψ₀ μ₀ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hμ : μ₀ ≠ 0)
    (hψ₀ : 0 < ψ₀) (hin : |epsAB a b| / 2 + √ψ₀ < 1 / 2)
    {P : Type*} [MeasurableSpace P] {μ : Measure P} [NeZero μ] (α ζ : P → ℝ)
    (I' sG sψ muP : ℝ) (w : P → ℝ) (hw : ∀ x, 0 < w x)
    (iB : Integrable (fun x => ‖field a b (surfPt a b ψ₀ (α x) (ζ x))‖ ^ 2 * w x) μ)
    (iX : Integrable (fun x => ‖μ₀ • current μ₀ a b (surfPt a b ψ₀ (α x) (ζ x)) -
      I' • field a b (surfPt a b ψ₀ (α x) (ζ x))‖ ^ 2 * w x) μ)
    (iBX : Integrable (fun x => ⟪field a b (surfPt a b ψ₀ (α x) (ζ x)),
      μ₀ • current μ₀ a b (surfPt a b ψ₀ (α x) (ζ x)) -
        I' • field a b (surfPt a b ψ₀ (α x) (ζ x))⟫ * w x) μ) :
    mercierIndex ⟨sG, sψ, 0, muP, 0,
      ∫ x, ⟪field a b (surfPt a b ψ₀ (α x) (ζ x)),
        μ₀ • current μ₀ a b (surfPt a b ψ₀ (α x) (ζ x)) -
          I' • field a b (surfPt a b ψ₀ (α x) (ζ x))⟫ * w x ∂μ,
      ∫ x, ‖μ₀ • current μ₀ a b (surfPt a b ψ₀ (α x) (ζ x)) -
          I' • field a b (surfPt a b ψ₀ (α x) (ζ x))‖ ^ 2 * w x ∂μ,
      ∫ x, ‖field a b (surfPt a b ψ₀ (α x) (ζ x))‖ ^ 2 * w x ∂μ⟩ < 0 :=
  mercierIndex_neg_of_forceBalance_Vpp_zero hμ I' sG sψ muP
    (fun x => field a b (surfPt a b ψ₀ (α x) (ζ x)))
    (fun x => current μ₀ a b (surfPt a b ψ₀ (α x) (ζ x)))
    (fun x => pressureGrad μ₀ a b (surfPt a b ψ₀ (α x) (ζ x))) w
    (fun x => cross_surfPt ha hb μ₀ hψ₀.le hin (α x) (ζ x))
    (fun x => pressureGrad_surfPt_ne_zero ha hb hμ hψ₀ hin (α x) (ζ x)) hw iB iX iBX

/-- The field does not vanish on `𝒰` (for `a, b > 0`), by `toroidal_pos`. -/
theorem field_ne_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : Space} (hx : x ∈ U a b) :
    field a b x ≠ 0 := by
  intro h
  have := toroidal_pos ha hb hx
  rw [h] at this
  simp at this

/-- **Closed-line specific volume** `U = ∮ dl/|B|`: along every field line of the plasma
(`ψ ≤ δ`), over one closure period, `∫₀^{2π} |γ'|/|B(γ)| dt = 2π`. So `U` is the same on all
field lines and all surfaces, `dU/dψ = 0`: the closed-line (Kadomtsev-type) interchange
criterion, which is the natural one for `ι ≡ 2`, has no destabilising or stabilising
`U'` term either (it is marginal at this order). The Mercier index is negative for the
different reason that `Ξ` is not parallel to `B` (`family1_mercier_unstable`). -/
theorem closedLine_specificVolume {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hε : |epsAB a b| < 1) {δ : ℝ} (hδ : δ < (1 - |epsAB a b|) ^ 2 / 4) {γ : ℝ → Space}
    (hγ : IsForwardFieldLine (field a b) γ) (h0 : γ 0 ∈ U a b) (hψ0 : psi a b (γ 0) ≤ δ) :
    ∫ t in (0 : ℝ)..(2 * π), ‖deriv γ t‖ / ‖field a b (γ t)‖ = 2 * π := by
  have hπ : (0 : ℝ) ≤ 2 * π := by positivity
  rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) ?_]
  · simp
  intro t ht
  rw [Set.uIcc_of_le hπ] at ht
  have hU := (fieldLine_confined ha.ne' hb.ne' hε hδ hγ h0 hψ0 ht.1).1
  simp only; rw [(hγ t ht.1).deriv]
  exact div_self (norm_ne_zero_iff.mpr (field_ne_zero ha hb hU))

/-- The surface point `α = ζ = 0` of the surface `ψ = 1/64` for the paper's example
`ε = 1/2` (`a = √(3/2)`, `b = √(1/2)`). -/
@[expose] def examplePt : Space := surfPt (aE (1 / 2)) (bE (1 / 2)) (1 / 64) 0 0

open MeasureTheory PlasmaLean.Stability.MercierGeneral in
/-- Sanity (the hypotheses of `family1_mercier_unstable` are satisfiable): for the paper's
example `ε = 1/2` (`a = √(3/2)`, `b = √(1/2)`), the surface `ψ₀ = 1/64` and a one-point
sample (Dirac measure, unit weight) the index is negative for every `I'`, `s_G`, `s_ψ`,
`p'`. -/
theorem family1_mercier_unstable_example (I' sG sψ muP : ℝ) :
    mercierIndex ⟨sG, sψ, 0, muP, 0,
      ⟪field (aE (1 / 2)) (bE (1 / 2)) examplePt,
        (1 : ℝ) • current 1 (aE (1 / 2)) (bE (1 / 2)) examplePt -
          I' • field (aE (1 / 2)) (bE (1 / 2)) examplePt⟫ * 1,
      ‖(1 : ℝ) • current 1 (aE (1 / 2)) (bE (1 / 2)) examplePt -
          I' • field (aE (1 / 2)) (bE (1 / 2)) examplePt‖ ^ 2 * 1,
      ‖field (aE (1 / 2)) (bE (1 / 2)) examplePt‖ ^ 2 * 1⟩ < 0 := by
  have hε : |(1 / 2 : ℝ)| < 1 := by norm_num [abs_of_pos]
  have ha := (aE_pos hε).ne'
  have hb := (bE_pos hε).ne'
  have he : epsAB (aE (1 / 2)) (bE (1 / 2)) = 1 / 2 := epsAB_eq hε
  have hs : √(1 / 64 : ℝ) = 1 / 8 := by
    rw [show (1 / 64 : ℝ) = (1 / 8) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hin : |epsAB (aE (1 / 2)) (bE (1 / 2))| / 2 + √(1 / 64 : ℝ) < 1 / 2 := by
    rw [he, hs]; norm_num [abs_of_pos]
  have := family1_mercier_unstable (μ := Measure.dirac ()) ha hb one_ne_zero
    (by norm_num : (0 : ℝ) < 1 / 64) hin (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) I' sG sψ muP
    (fun _ => 1) (fun _ => one_pos) (Integrable.of_finite) (Integrable.of_finite)
    (Integrable.of_finite)
  simpa [examplePt] using this

/-! ## Family 2 (sheared): hill-dominated Mercier instability -/

section Family2
open PlasmaLean.Stability.MercierGeneral

/-- **Hill-dominated Mercier instability** (general algebraic criterion). If `s_G² = 1`,
Cauchy–Schwarz `(∫B·Ξ w)² ≤ ∫|Ξ|²w ∫B²w` holds (automatic for genuine integrals
with a common nonnegative weight), and the magnetic-hill term dominates,
`(2π²ι')² + 2·2π²|ι'|·|∫B·Ξ w| < -(s_ψ μ₀ p' V'') ∫B²w`, then `D_Merc < 0`. (No upper bound
on `∫|Ξ|²w` is needed: that term only destabilises further.) -/
theorem mercierIndex_neg_of_hill_dominates {d : MercierSurfaceData} (hs : d.sG ^ 2 = 1)
    (hCS : d.intBXi ^ 2 ≤ d.intXi2 * d.intB2)
    (hdom : (2 * π ^ 2 * d.iotaPrime) ^ 2 + 2 * (2 * π ^ 2 * |d.iotaPrime|) * |d.intBXi| <
      -(d.sψ * d.muPprime * d.Vpp) * d.intB2) : mercierIndex d < 0 := by
  unfold mercierIndex MercierSurfaceData.shearBracket MercierSurfaceData.wellBracket
  apply div_neg_of_neg_of_pos _ (by positivity)
  have habs : |d.sG| = 1 := by
    have := sq_abs d.sG
    nlinarith [abs_nonneg d.sG, sq_nonneg (|d.sG| - 1), sq_nonneg (|d.sG| + 1)]
  have hcross : -(2 * (d.sG * (2 * π ^ 2) * d.iotaPrime * d.intBXi)) ≤
      2 * (2 * π ^ 2 * |d.iotaPrime|) * |d.intBXi| := by
    have h1 := neg_abs_le (d.sG * (2 * π ^ 2) * d.iotaPrime * d.intBXi)
    have h2 : |d.sG * (2 * π ^ 2) * d.iotaPrime * d.intBXi| =
        2 * π ^ 2 * |d.iotaPrime| * |d.intBXi| := by
      rw [abs_mul, abs_mul, abs_mul, habs, abs_of_pos (by positivity : (0 : ℝ) < 2 * π ^ 2)]
      ring
    linarith
  have hsq : (d.sG * (2 * π ^ 2) * d.iotaPrime - d.intBXi) ^ 2 =
      (2 * π ^ 2 * d.iotaPrime) ^ 2 - 2 * (d.sG * (2 * π ^ 2) * d.iotaPrime * d.intBXi) +
        d.intBXi ^ 2 := by
    have : (d.sG * (2 * π ^ 2) * d.iotaPrime) ^ 2 = (2 * π ^ 2 * d.iotaPrime) ^ 2 := by
      rw [mul_pow, mul_pow, hs]; ring
    rw [sub_sq, this]; ring
  rw [hsq]
  nlinarith

/-- **Positive shear forces a magnetic hill in family 2.** For family 2 the specific volume
in the toroidal-flux label is `V'(ψ_t) = 2π E(k) ι(ψ_t)` with `E(k) = ∫₀^{2π} dχ/√(1 - k² sin² χ)`
(`= 4K(k)`, increasing in `k`), `ψ = k²/2` (derived from the Jacobian (3.18) and the
`ζ ↦ π/2 - ζ` symmetry of the paper; NOT formalized here, but checked numerically (to `10⁻⁶`) by
`scripts/landreman_mercier_oracle.py`). Whatever the functions, if `E, ι > 0`, `E' > 0` and
`ι' ≥ 0`, then `(2π E ι)' > 0`: a magnetic hill `V'' > 0`. -/
theorem hill_of_shear {E ι : ℝ → ℝ} {E' ι' t : ℝ} (hE : HasDerivAt E E' t)
    (hι : HasDerivAt ι ι' t) (hE0 : 0 < E t) (hE' : 0 < E') (hι0 : 0 < ι t) (hι' : 0 ≤ ι') :
    0 < deriv (fun s => 2 * π * E s * ι s) t := by
  have h : HasDerivAt (fun s => 2 * π * E s * ι s) (2 * π * E' * ι t + 2 * π * E t * ι') t := by
    have := (hE.const_mul (2 * π)).mul hι
    convert this using 1
  rw [h.deriv]
  have := pi_pos
  have : 0 ≤ 2 * π * E t * ι' := by positivity
  have : 0 < 2 * π * E' * ι t := by positivity
  linarith

/-- **Family 2 (`ε = 1/4`, `S = 4`, `λ = 15`, `μ₀ = 1`), surface `k = 1/20` (`ψ = 1/800`):
Mercier unstable, given order-of-magnitude enclosures of the inputs.** The untrusted oracle
`scripts/landreman_mercier_oracle.py` gives (toroidal-flux label, `s_ψ = 1`):
`ι' ≈ 825.3`, `μ₀ p' ≈ -1.0664`, `V'' ≈ 70490` (a hill), so `s_ψ μ₀ p' V'' ≈ -75173`;
`∫B·Ξ w ≈ -6319`, `∫|Ξ|² w ≈ 6775`, `∫B² w ≈ 7.593·10⁶`; `D_Merc ≈ -1.01·10⁷` for both
`s_G = ±1`. This theorem only needs each input to be within a factor `≈ 2.5` of these values:
`∫B²w ≥ 3·10⁶`, `|∫B·Ξ w| ≤ 2·10⁴`, `|ι'| ≤ 2000`, `s_ψ μ₀ p' V'' ≤ -3·10⁴`, plus
Cauchy–Schwarz. These enclosures are NOT certified (no validated quadrature): they are the
explicit numerical hypotheses of the verdict. -/
theorem family2_mercier_unstable_of_enclosures {d : MercierSurfaceData} (hs : d.sG ^ 2 = 1)
    (hc : 3000000 ≤ d.intB2) (hb : |d.intBXi| ≤ 20000) (hi : |d.iotaPrime| ≤ 2000)
    (hW : d.sψ * d.muPprime * d.Vpp ≤ -30000) (hCS : d.intBXi ^ 2 ≤ d.intXi2 * d.intB2) :
    mercierIndex d < 0 := by
  have hπ2 : π ^ 2 < 10 := by nlinarith [pi_lt_d2, pi_pos]
  have hA : 2 * π ^ 2 * |d.iotaPrime| ≤ 40000 := by
    have := abs_nonneg d.iotaPrime
    nlinarith [pi_pos]
  refine mercierIndex_neg_of_hill_dominates hs hCS ?_
  have hA0 : 0 ≤ 2 * π ^ 2 * |d.iotaPrime| := by positivity
  have e : (2 * π ^ 2 * d.iotaPrime) ^ 2 = (2 * π ^ 2 * |d.iotaPrime|) ^ 2 := by
    rw [mul_pow, mul_pow (2 * π ^ 2) |d.iotaPrime|, sq_abs]
  rw [e]
  have h1 : (2 * π ^ 2 * |d.iotaPrime|) ^ 2 ≤ 40000 ^ 2 := pow_le_pow_left₀ hA0 hA 2
  have h2 : 2 * (2 * π ^ 2 * |d.iotaPrime|) * |d.intBXi| ≤ 2 * 40000 * 20000 :=
    by nlinarith [abs_nonneg d.intBXi]
  have h3 : 30000 * 3000000 ≤ -(d.sψ * d.muPprime * d.Vpp) * d.intB2 := by nlinarith
  nlinarith

/-- The oracle values for family 2 (`ε = 1/4`, `S = 4`, `λ = 15`, `k = 1/20`), rounded,
with either sign `s_G`. -/
@[expose] def family2OracleData (sG : ℝ) : MercierSurfaceData :=
  ⟨sG, 1, 825.28, -1.06644, 70490.2, -6318.58, 6774.69, 7593280⟩

/-- Accepted fixture: the oracle values satisfy the enclosures, so `D_Merc < 0` for
`s_G = ±1`. -/
theorem family2OracleData_unstable (sG : ℝ) (hs : sG ^ 2 = 1) :
    mercierIndex (family2OracleData sG) < 0 :=
  family2_mercier_unstable_of_enclosures hs (by norm_num [family2OracleData])
    (by norm_num [family2OracleData, abs_of_neg]) (by norm_num [family2OracleData, abs_of_pos])
    (by norm_num [family2OracleData]) (by norm_num [family2OracleData])

/-- Rejected fixture (the verdict depends on the parameters): the oracle values for `λ = 50`
on the outer surface `k = 9/10` (`ι' ≈ 17080`, strong shear) give `D_Merc > 0`, i.e. there the
shear term wins and the surface is Mercier STABLE. -/
theorem family2_lam50_outer_stable :
    0 < mercierIndex ⟨1, 1, 17079.55, -0.21107, 1733992.2, -10436.16, 3214.46, 152788⟩ := by
  unfold mercierIndex MercierSurfaceData.shearBracket MercierSurfaceData.wellBracket
  apply div_pos _ (by positivity)
  have h1 : 3.14 < π := pi_gt_d2
  have hX : 347000 ≤ 1 * (2 * π ^ 2) * 17079.55 - -10436.16 := by nlinarith
  nlinarith

end Family2

end PlasmaLean.Design.LandremanMercier
