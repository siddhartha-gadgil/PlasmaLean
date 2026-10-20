/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanEquilibrium
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.Real.Pi.Bounds
public import PlasmaLean.Certificates.PolyInterval

/-!
# Landreman's explicit toroidal MHS equilibria, family 2 (sheared rotational transform)

Source: M. Landreman, *Analytic toroidal 3D MHD equilibria and steady Euler flows with
invariant surfaces*, arXiv:2609.26742 **v2** (28 Sep 2026), §3 "Solutions with magnetic shear",
equations (3.1)–(3.27). Retrieved 21 Oct 2026 (arXiv LaTeX source). This is an **unrefereed
preprint**. Every identity used here is re-proved below from the stated formulas; nothing is
taken on trust from the paper. The code is independent of the Gómez-Serrano–Liehr–Taylor Lean
library and does not adapt any of its code. Family 1 (`ι = 2`) is
`PlasmaLean.Design.LandremanEquilibrium`.

## The field (paper (3.1)–(3.3), with `μ₀ = 1` there)

With `ω = x + iy`, `K = ω̄ √(1 + ε/ω̄²)` (principal root) and `Ξ = ωK + π/2 - S`:
`B_x + i B_y = i e^{-iλz} sin Ξ/(2K)`, `B_z = Re(e^{-iλz} cos Ξ)/λ`,
`ψ = (sin² λz + (Re(e^{-iλz} cos Ξ))²)/2`, `p = p_a - ψ/λ²`. Here it is written in real
variables: `P = ωK = σ + iν = √Z` with `Z = ω²(ω̄² + ε)`, `σ = √((|Z| + Re Z)/2)`, `ν = εxy/σ`
(`sg`, `nu`), `u = e^{-iλz} cos(P - S)`, `v = e^{-iλz} sin(P - S)` and `w = ω/P`:
`B_x + iB_y = (i/2) u w`, `B_z = -Re v/λ` (`field`). `field_eq_paper` proves that this is
exactly the paper's complex formula (`fieldPaper`) on the smooth region `𝒰` (`U`: `(x, y)` off
the segment `x = 0`, `|y| ≤ √ε`), and `psi_eq_paper` does the same for `ψ`.

## Verified here (actual Fréchet derivatives throughout)

* `field_divergence_free`: `∇ · B = 0` on `𝒰`.
* `force_balance`: the kernel law `ForceBalance` (`J × B = ∇p`) with `J = (∇ × B)/μ₀` from the
  actual derivative and `p = (p_a - ψ/λ²)/μ₀` with its actual gradient (paper (3.7)); the key
  step is `transport_key`, `(B·∇)B - (DB)ᵀB = -∇ψ/λ²`.
* `field_tangent_psi`, `current_tangent_psi`, `psi_firstIntegral`: `B · ∇ψ = J · ∇ψ = 0`.
* `pressure_pos`, `pressure_boundary`, `pressure_le_axis`: with `p_a = δ/λ²`, `p > 0` inside
  `ψ < δ`, `p = 0` on `ψ = δ`, maximal on the axis.
* `field_axis`, `axis_tangent`, `psi_axis`, `axis_planar`, `axis_ellipse`, `axis_not_circle`:
  the magnetic axis (3.20) `(a_c(S) cos ζ, b_c(S) sin ζ, 0)` is a planar, non-circular ellipse
  (`b_c² - a_c² = ε`) on which `ψ = 0`; there `B = (cosh ν/(2G)) γ'` with `G > 0`, so the axis is
  an integral curve of `B` up to a positive time change.
* `field_not_axisymmetric` (for `ε > 0`, `ε(S + ε) ≤ 3S`), `field_rotPi` (two field periods),
  sanity `field_axisymmetric_limit` (`ε = 0` is axisymmetric).
* `fieldLine_confined`: for `ε = 1/4`, `S = 4`, every forward field line starting in the region
  `R` (`|σ - S| < π/2`, `|λz| < π/2`) with `ψ ≤ 81/200` stays in `R` on its flux surface for all
  time; `surface_nonempty`: every surface `ψ = k²/2`, `k < 1`, meets `R`.
* **Shear** (`shear`, `rotTransform_sheared`, `family2_shear`), for `ε = 1/4`, `S = 4` and every
  `λ ≠ 0`. Along a field line on `ψ = k²/2` the point `(X, Y) = (λB_z, -sin λz)` turns on its
  circle with angular velocity `θ' = cos λz` (paper (3.21); `LiftedLine.pol_rate`), and the polar
  angle has `φ' = (σ Re u + ν Im u)/(2|P|²)` (`torRate_eq`). On the inner surface
  `ψ = 1/800` (`k = 1/20`) `φ' ≥ (3/25) θ'` (`surface_k1`, `inner_winding`). On the outer
  surface `ψ = 81/200` (`k = 9/10`) `φ' ≤ c_X X/cos λz + cos λz · p(Y²)` (`surface_k2`), where
  `X/cos λz = -(artanh Y)'` and `cos λz (p(Y²) - ⟨p⟩)` is the derivative of a polynomial in
  `X, Y`; so `φ(t) - φ(0) ≤ ⟨p⟩ (θ(t) - θ(0)) + D` with `1/⟨p⟩ ≈ 8.94` (`outer_winding`). The
  polynomial inequality behind `surface_k2` is a kernel-checked `QPoly.checkOn` certificate
  (`Pcoeffs_check`). Hence the winding ratios satisfy `≤ 25/3` (inner, all `t > 0`) and
  `≥ 17/2` (outer, all large `t`), and any rotational transforms satisfy
  `ι(1/800) ≤ 25/3 < 17/2 ≤ ι(81/200)`. (Numerical integration gives `ι ≈ 7.98` and
  `ι ≈ 11.86`.)
* `force_balance_SI`, `realistic_instance`: the SI rescaling `B = B₀ B̂(x/L)`,
  `p = (B₀²/μ₀) p̂(x/L)` satisfies the kernel law; for `ε = 1/4`, `S = 4`, `λ = 15`,
  `δ = 81/200`, `B₀ = 20 T` the axis field is `|B| ≈ 4.9–5.2 T` and the local axis beta is in
  `[1/20, 1/16]`.

## Scope and honesty

* The shear theorem is for the family member `ε = 1/4`, `S = 4` (any `λ`), not for the paper's
  example (3.27) (`ε = 2`, `S = 1`), whose transform varies only by `≈ 10⁻³`
  (`2.28690 → 2.2878`), beyond the reach of the pointwise bounds used here. The rotational
  transform (3.24) is formalized as the limit of winding ratios of continuous angle lifts
  (`HasRotTransform`); the paper's ODE (3.24) and on-axis formula (3.25)–(3.26) are not used.
* Existence of field lines (ODE solutions) and of differentiable angle lifts is assumed in
  `LiftedLine`, not proved; `surface_nonempty` shows the positional hypotheses are satisfiable.
* Not formalized: the claim that `Ω_δ` is a solid torus covered once by the coordinates
  (3.12)–(3.18), stellarator symmetry, and the volume-averaged beta (3.28)–(3.34).
* No stability is claimed. The equilibrium is exact and smooth on `𝒰` but idealized
  (not optimized, not coil-derived); the paper's own example has very weak shear.
* The coefficient identities `sg_coeff0`–`nu_coeff1`, the polynomial `pP` and the grid
  `Pgrid` were found by untrusted scripts (sympy, a linear program); Lean checks them.
-/

open scoped RealInnerProductSpace

public section
noncomputable section
namespace PlasmaLean.Design.LandremanFamily2
open PlasmaLean.Fields WithLp
open PlasmaLean.Design.LandremanEquilibrium (pr hfd hasFDerivAt_pr adjApply curl_cross_eq
  inner_coords inner_apply_eq_adj coord_hasDerivAt rotQ rotPi curve_hasDerivAt)

/-! ## Definitions -/

/-- `r² = x² + y²`. -/
@[expose] def r2 (x : Space) : ℝ := x 0 ^ 2 + x 1 ^ 2

/-- `Re Z`, where `Z = ω² (ω̄² + ε) = |ω|⁴ + ε ω²` and `ω = x + i y`. -/
@[expose] def Zr (ε : ℝ) (x : Space) : ℝ := r2 x ^ 2 + ε * (x 0 ^ 2 - x 1 ^ 2)

/-- `Im Z = 2 ε x y`. -/
@[expose] def Zi (ε : ℝ) (x : Space) : ℝ := 2 * ε * x 0 * x 1

/-- `|Z|`. -/
@[expose] def Mo (ε : ℝ) (x : Space) : ℝ := √(Zr ε x ^ 2 + Zi ε x ^ 2)

/-- `σ = Re √Z` (principal branch), so that `σ + iν = ωK` in the paper's notation. -/
@[expose] def sg (ε : ℝ) (x : Space) : ℝ := √((Mo ε x + Zr ε x) / 2)

/-- `ν = Im √Z = ε x y / σ`. -/
@[expose] def nu (ε : ℝ) (x : Space) : ℝ := ε * x 0 * x 1 / sg ε x

/-- `|P|² = σ² + ν²` where `P = σ + iν` (equal to `|Z|` on the region, `Mq_eq_Mo`). -/
@[expose] def Mq (ε : ℝ) (x : Space) : ℝ := sg ε x ^ 2 + nu ε x ^ 2

/-- The smooth region `𝒰`: `Z` avoids the closed negative real axis, i.e. `(x, y)` avoids the
segment `x = 0`, `|y| ≤ √ε` (paper, below (3.7)). -/
@[expose] def U (ε : ℝ) : Set Space := {x | 0 < Mo ε x + Zr ε x}

/-- `cos λz`. -/
@[expose] def cz (lam : ℝ) (x : Space) : ℝ := Real.cos (lam * x 2)

/-- `sin λz`. -/
@[expose] def sz (lam : ℝ) (x : Space) : ℝ := Real.sin (lam * x 2)

/-- `Re u`, `u = e^{-iλz} cos(P - S)`. -/
@[expose] def uR (ε S lam : ℝ) (x : Space) : ℝ :=
  cz lam x * Real.cos (sg ε x - S) * Real.cosh (nu ε x) -
    sz lam x * Real.sin (sg ε x - S) * Real.sinh (nu ε x)

/-- `Im u`. -/
@[expose] def uI (ε S lam : ℝ) (x : Space) : ℝ :=
  -(sz lam x * Real.cos (sg ε x - S) * Real.cosh (nu ε x) +
    cz lam x * Real.sin (sg ε x - S) * Real.sinh (nu ε x))

/-- `Re v`, `v = e^{-iλz} sin(P - S)`. -/
@[expose] def vR (ε S lam : ℝ) (x : Space) : ℝ :=
  cz lam x * Real.sin (sg ε x - S) * Real.cosh (nu ε x) +
    sz lam x * Real.cos (sg ε x - S) * Real.sinh (nu ε x)

/-- `Im v`. -/
@[expose] def vI (ε S lam : ℝ) (x : Space) : ℝ :=
  cz lam x * Real.cos (sg ε x - S) * Real.sinh (nu ε x) -
    sz lam x * Real.sin (sg ε x - S) * Real.cosh (nu ε x)

/-- `α = Re(ω P̄) = σ x + ν y`. -/
@[expose] def al (ε : ℝ) (x : Space) : ℝ := sg ε x * x 0 + nu ε x * x 1

/-- `β = Im(ω P̄) = σ y - ν x`. -/
@[expose] def be (ε : ℝ) (x : Space) : ℝ := sg ε x * x 1 - nu ε x * x 0

/-- The family-2 field in real form. With `w = ω/P = 1/K = (α + iβ)/|P|²`,
`B_x + i B_y = (i/2) u w` and `B_z = -Re v / λ` (paper (3.2)). -/
@[expose] def field (ε S lam : ℝ) (x : Space) : Space :=
  toLp 2 ![-(uR ε S lam x * be ε x + uI ε S lam x * al ε x) / (2 * Mq ε x),
    (uR ε S lam x * al ε x - uI ε S lam x * be ε x) / (2 * Mq ε x),
    -vR ε S lam x / lam]

/-! ## Algebraic relations on `𝒰` -/

section Relations
variable {ε : ℝ} {x : Space}

/-- `|Z|² = (Re Z)² + (Im Z)²`. -/
theorem Mo_sq (ε : ℝ) (x : Space) : Mo ε x ^ 2 = Zr ε x ^ 2 + Zi ε x ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- `|Re Z| ≤ |Z|`. -/
theorem abs_Zr_le (ε : ℝ) (x : Space) : |Zr ε x| ≤ Mo ε x :=
  Real.abs_le_sqrt (by nlinarith [sq_nonneg (Zi ε x)])

/-- On `𝒰`, `σ > 0`. -/
theorem sg_pos (hx : x ∈ U ε) : 0 < sg ε x :=
  Real.sqrt_pos.mpr (by have : 0 < Mo ε x + Zr ε x := hx; linarith)

/-- `σ² = (|Z| + Re Z)/2` on `𝒰`. -/
theorem sg_sq (hx : x ∈ U ε) : sg ε x ^ 2 = (Mo ε x + Zr ε x) / 2 :=
  Real.sq_sqrt (by have : 0 < Mo ε x + Zr ε x := hx; linarith)

/-- `σ ν = ε x y` on `𝒰`. -/
theorem sg_mul_nu (hx : x ∈ U ε) : sg ε x * nu ε x = ε * x 0 * x 1 := by
  have := (sg_pos hx).ne'
  unfold nu; field_simp

/-- `σ² - ν² = Re Z` on `𝒰`. -/
theorem sg_sq_sub_nu_sq (hx : x ∈ U ε) : sg ε x ^ 2 - nu ε x ^ 2 = Zr ε x := by
  have hs : sg ε x ^ 2 ≠ 0 := pow_ne_zero 2 (sg_pos hx).ne'
  have h2 := sg_sq hx
  have hm := Mo_sq ε x
  have hn : nu ε x ^ 2 * sg ε x ^ 2 = Zi ε x ^ 2 / 4 := by
    rw [← mul_pow, mul_comm, sg_mul_nu hx, Zi]; ring
  refine mul_right_cancel₀ hs ?_
  linear_combination (sg ε x ^ 2 + (Mo ε x - Zr ε x) / 2) * h2 - hn + (1 / 4 : ℝ) * hm

/-- `|P|² = |Z|` on `𝒰`. -/
theorem Mq_eq_Mo (hx : x ∈ U ε) : Mq ε x = Mo ε x := by
  have h1 := sg_sq_sub_nu_sq hx
  have h2 := sg_sq hx
  unfold Mq; linarith

/-- On `𝒰`, `x² + y² > 0` (the region avoids the `z`-axis). -/
theorem r2_pos (hx : x ∈ U ε) : 0 < r2 x := by
  have h : 0 < Mo ε x + Zr ε x := hx
  by_contra hc
  have h0 : x 0 = 0 := by unfold r2 at hc; nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  have h1 : x 1 = 0 := by unfold r2 at hc; nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  simp [Mo, Zr, Zi, r2, h0, h1] at h

/-- On `𝒰`, `|P|² > 0`. -/
theorem Mq_pos (hx : x ∈ U ε) : 0 < Mq ε x := by
  have := sg_pos hx; unfold Mq; positivity

end Relations

/-! ### Coefficient identities (polynomial certificates generated by an untrusted sympy
script; each is checked here by `linear_combination` and `field_simp; ring`) -/

/-- Coefficient identity for `dσ` (first component). -/
theorem sg_coeff0 {p q s n ε : ℝ} (hs : s ≠ 0) (hm : n ^ 2 + s ^ 2 ≠ 0)
    (hr : p ^ 2 + q ^ 2 ≠ 0)
    (h1 : s ^ 2 - n ^ 2 = (p ^ 2 + q ^ 2) ^ 2 + ε * (p ^ 2 - q ^ 2))
    (h2 : s * n = ε * p * q) :
    (1/2 : ℝ)*(1/(s))*(2*p*ε ^ 2*q ^ 2*(1/(n ^ 2 + s ^ 2)) + ε*p + (1/2 : ℝ)*p*(4*p ^ 2 +
      4*q ^ 2) + (1/2 : ℝ)*(1/(n ^ 2 + s ^ 2))*(ε*(p ^ 2 - q ^ 2) + (p ^ 2 +
      q ^ 2) ^ 2)*(2*ε*p + p*(4*p ^ 2 + 4*q ^ 2))) =
      ((1/(p ^ 2 + q ^ 2)) + (1/(n ^ 2 + s ^ 2))*(p ^ 2 + q ^ 2))*(n*q + p*s) := by
  rw [← sub_eq_zero]
  have hN : ε ^ 2*p ^ 5 + 2*ε ^ 2*p ^ 3*q ^ 2 + p*ε ^ 2*q ^ 4 + ε*n ^ 2*p ^ 3 +
      ε*p*n ^ 2*q ^ 2 + 3*ε*p ^ 7 + 5*ε*p ^ 5*q ^ 2 + ε*p ^ 3*q ^ 4 + ε*p ^ 3*s ^ 2 -
      ε*p*q ^ 6 + ε*p*q ^ 2*s ^ 2 - 2*q*s*n ^ 3 + 2*n ^ 2*p ^ 5 + 4*n ^ 2*p ^ 3*q ^ 2 +
      2*p*n ^ 2*q ^ 4 - 2*p*n ^ 2*s ^ 2 - 2*n*q*s*p ^ 4 - 4*n*s*p ^ 2*q ^ 3 - 2*n*s*q ^ 5 -
      2*n*q*s ^ 3 + 2*p ^ 9 + 8*p ^ 7*q ^ 2 + 12*p ^ 5*q ^ 4 + 8*p ^ 3*q ^ 6 + 2*p*q ^ 8 -
      2*p*s ^ 4 = 0 := by
    linear_combination (-ε*p ^ 3 - 3*ε*p*q ^ 2 + 4*n*q*s - 2*p ^ 5 - 4*p ^ 3*q ^ 2 -
      2*p*q ^ 4 - 2*p*s ^ 2) * h1 + (2*(-2*ε*q ^ 3 + q*n ^ 2 - 2*n*p*s + q*p ^ 4 +
      2*p ^ 2*q ^ 3 + q ^ 5 - 3*q*s ^ 2)) * h2
  rw [show (1/2 : ℝ)*(1/(s))*(2*p*ε ^ 2*q ^ 2*(1/(n ^ 2 + s ^ 2)) + ε*p +
      (1/2 : ℝ)*p*(4*p ^ 2 + 4*q ^ 2) + (1/2 : ℝ)*(1/(n ^ 2 + s ^ 2))*(ε*(p ^ 2 - q ^ 2) +
      (p ^ 2 + q ^ 2) ^ 2)*(2*ε*p + p*(4*p ^ 2 + 4*q ^ 2))) - (((1/(p ^ 2 + q ^ 2)) +
      (1/(n ^ 2 + s ^ 2))*(p ^ 2 + q ^ 2))*(n*q + p*s)) =
      (ε ^ 2*p ^ 5 + 2*ε ^ 2*p ^ 3*q ^ 2 + p*ε ^ 2*q ^ 4 + ε*n ^ 2*p ^ 3 + ε*p*n ^ 2*q ^ 2
      + 3*ε*p ^ 7 + 5*ε*p ^ 5*q ^ 2 + ε*p ^ 3*q ^ 4 + ε*p ^ 3*s ^ 2 - ε*p*q ^ 6 +
      ε*p*q ^ 2*s ^ 2 - 2*q*s*n ^ 3 + 2*n ^ 2*p ^ 5 + 4*n ^ 2*p ^ 3*q ^ 2 + 2*p*n ^ 2*q ^ 4
      - 2*p*n ^ 2*s ^ 2 - 2*n*q*s*p ^ 4 - 4*n*s*p ^ 2*q ^ 3 - 2*n*s*q ^ 5 - 2*n*q*s ^ 3 +
      2*p ^ 9 + 8*p ^ 7*q ^ 2 + 12*p ^ 5*q ^ 4 + 8*p ^ 3*q ^ 6 + 2*p*q ^ 8 -
      2*p*s ^ 4) / (2*s*(n ^ 2 + s ^ 2)*(p ^ 2 + q ^ 2)) by field_simp; ring, hN, zero_div]

/-- Coefficient identity for `dσ` (second component). -/
theorem sg_coeff1 {p q s n ε : ℝ} (hs : s ≠ 0) (hm : n ^ 2 + s ^ 2 ≠ 0)
    (hr : p ^ 2 + q ^ 2 ≠ 0)
    (h1 : s ^ 2 - n ^ 2 = (p ^ 2 + q ^ 2) ^ 2 + ε * (p ^ 2 - q ^ 2))
    (h2 : s * n = ε * p * q) :
    (1/2 : ℝ)*(1/(s))*(2*q*ε ^ 2*p ^ 2*(1/(n ^ 2 + s ^ 2)) - ε*q + (1/2 : ℝ)*q*(4*p ^ 2 +
      4*q ^ 2) + (1/2 : ℝ)*(1/(n ^ 2 + s ^ 2))*(ε*(p ^ 2 - q ^ 2) + (p ^ 2 +
      q ^ 2) ^ 2)*(-2*ε*q + q*(4*p ^ 2 + 4*q ^ 2))) =
      ((1/(p ^ 2 + q ^ 2)) + (1/(n ^ 2 + s ^ 2))*(p ^ 2 + q ^ 2))*(-n*p + q*s) := by
  rw [← sub_eq_zero]
  have hN : q*ε ^ 2*p ^ 4 + 2*ε ^ 2*p ^ 2*q ^ 3 + ε ^ 2*q ^ 5 - ε*q*n ^ 2*p ^ 2 -
      ε*n ^ 2*q ^ 3 + ε*q*p ^ 6 - ε*p ^ 4*q ^ 3 - 5*ε*p ^ 2*q ^ 5 - ε*q*p ^ 2*s ^ 2 -
      3*ε*q ^ 7 - ε*q ^ 3*s ^ 2 + 2*p*s*n ^ 3 + 2*q*n ^ 2*p ^ 4 + 4*n ^ 2*p ^ 2*q ^ 3 +
      2*n ^ 2*q ^ 5 - 2*q*n ^ 2*s ^ 2 + 2*n*s*p ^ 5 + 4*n*s*p ^ 3*q ^ 2 + 2*n*p*s*q ^ 4 +
      2*n*p*s ^ 3 + 2*q*p ^ 8 + 8*p ^ 6*q ^ 3 + 12*p ^ 4*q ^ 5 + 8*p ^ 2*q ^ 7 + 2*q ^ 9 -
      2*q*s ^ 4 = 0 := by
    linear_combination (-q*(ε*p ^ 2 - ε*q ^ 2 + 2*p ^ 4 + 4*p ^ 2*q ^ 2 + 2*q ^ 4 +
      2*s ^ 2)) * h1 + (2*(-2*ε*p*q ^ 2 + p*n ^ 2 - 2*n*q*s + p ^ 5 + 2*p ^ 3*q ^ 2 +
      p*q ^ 4 + p*s ^ 2)) * h2
  rw [show (1/2 : ℝ)*(1/(s))*(2*q*ε ^ 2*p ^ 2*(1/(n ^ 2 + s ^ 2)) - ε*q +
      (1/2 : ℝ)*q*(4*p ^ 2 + 4*q ^ 2) + (1/2 : ℝ)*(1/(n ^ 2 + s ^ 2))*(ε*(p ^ 2 - q ^ 2) +
      (p ^ 2 + q ^ 2) ^ 2)*(-2*ε*q + q*(4*p ^ 2 + 4*q ^ 2))) - (((1/(p ^ 2 + q ^ 2)) +
      (1/(n ^ 2 + s ^ 2))*(p ^ 2 + q ^ 2))*(-n*p + q*s)) =
      (q*ε ^ 2*p ^ 4 + 2*ε ^ 2*p ^ 2*q ^ 3 + ε ^ 2*q ^ 5 - ε*q*n ^ 2*p ^ 2 - ε*n ^ 2*q ^ 3
      + ε*q*p ^ 6 - ε*p ^ 4*q ^ 3 - 5*ε*p ^ 2*q ^ 5 - ε*q*p ^ 2*s ^ 2 - 3*ε*q ^ 7 -
      ε*q ^ 3*s ^ 2 + 2*p*s*n ^ 3 + 2*q*n ^ 2*p ^ 4 + 4*n ^ 2*p ^ 2*q ^ 3 + 2*n ^ 2*q ^ 5 -
      2*q*n ^ 2*s ^ 2 + 2*n*s*p ^ 5 + 4*n*s*p ^ 3*q ^ 2 + 2*n*p*s*q ^ 4 + 2*n*p*s ^ 3 +
      2*q*p ^ 8 + 8*p ^ 6*q ^ 3 + 12*p ^ 4*q ^ 5 + 8*p ^ 2*q ^ 7 + 2*q ^ 9 -
      2*q*s ^ 4) / (2*s*(n ^ 2 + s ^ 2)*(p ^ 2 + q ^ 2)) by field_simp; ring, hN, zero_div]

/-- Coefficient identity for `dν` (first component). -/
theorem nu_coeff0 {p q s n ε : ℝ} (hs : s ≠ 0) (hm : n ^ 2 + s ^ 2 ≠ 0)
    (hr : p ^ 2 + q ^ 2 ≠ 0)
    (h1 : s ^ 2 - n ^ 2 = (p ^ 2 + q ^ 2) ^ 2 + ε * (p ^ 2 - q ^ 2))
    (h2 : s * n = ε * p * q) :
    -ε*p*q*(1/(s ^ 2))*((1/(p ^ 2 + q ^ 2)) + (1/(n ^ 2 + s ^ 2))*(p ^ 2 + q ^ 2))*(n*q +
      p*s) + ε*q*(1/(s)) =
      (-(1/(p ^ 2 + q ^ 2)) + (1/(n ^ 2 + s ^ 2))*(p ^ 2 + q ^ 2))*(-n*p + q*s) := by
  rw [← sub_eq_zero]
  have hN : -ε*p*n ^ 3*q ^ 2 + ε*s*n ^ 2*q ^ 3 - ε*n*p ^ 5*q ^ 2 - 2*ε*n*p ^ 3*q ^ 4 -
      ε*n*p*q ^ 6 - ε*n*p*q ^ 2*s ^ 2 - ε*q*s*p ^ 6 - 2*ε*s*p ^ 4*q ^ 3 - ε*s*p ^ 2*q ^ 5 +
      ε*q ^ 3*s ^ 3 - p*n ^ 3*s ^ 2 + q*n ^ 2*s ^ 3 + n*p ^ 5*s ^ 2 + 2*n*p ^ 3*q ^ 2*s ^ 2
      + n*p*q ^ 4*s ^ 2 - n*p*s ^ 4 - q*p ^ 4*s ^ 3 - 2*p ^ 2*q ^ 3*s ^ 3 - q ^ 5*s ^ 3 +
      q*s ^ 5 = 0 := by
    linear_combination (ε*n*p*q ^ 2 + ε*q*s*p ^ 2 - n*p*s ^ 2 + q*s ^ 3) * h1 +
      (-ε*n*q*p ^ 2 + ε*n*q ^ 3 - ε*s*p ^ 3 + ε*p*s*q ^ 2 - 2*p*s*n ^ 2 + 2*n*q*s ^ 2) * h2
  rw [show -ε*p*q*(1/(s ^ 2))*((1/(p ^ 2 + q ^ 2)) + (1/(n ^ 2 + s ^ 2))*(p ^ 2 +
      q ^ 2))*(n*q + p*s) + ε*q*(1/(s)) - ((-(1/(p ^ 2 + q ^ 2)) + (1/(n ^ 2 +
      s ^ 2))*(p ^ 2 + q ^ 2))*(-n*p + q*s)) =
      (-ε*p*n ^ 3*q ^ 2 + ε*s*n ^ 2*q ^ 3 - ε*n*p ^ 5*q ^ 2 - 2*ε*n*p ^ 3*q ^ 4 -
      ε*n*p*q ^ 6 - ε*n*p*q ^ 2*s ^ 2 - ε*q*s*p ^ 6 - 2*ε*s*p ^ 4*q ^ 3 - ε*s*p ^ 2*q ^ 5 +
      ε*q ^ 3*s ^ 3 - p*n ^ 3*s ^ 2 + q*n ^ 2*s ^ 3 + n*p ^ 5*s ^ 2 + 2*n*p ^ 3*q ^ 2*s ^ 2
      + n*p*q ^ 4*s ^ 2 - n*p*s ^ 4 - q*p ^ 4*s ^ 3 - 2*p ^ 2*q ^ 3*s ^ 3 - q ^ 5*s ^ 3 +
      q*s ^ 5) / (s ^ 2*(n ^ 2 + s ^ 2)*(p ^ 2 + q ^ 2)) by field_simp; ring, hN, zero_div]

/-- Coefficient identity for `dν` (second component). -/
theorem nu_coeff1 {p q s n ε : ℝ} (hs : s ≠ 0) (hm : n ^ 2 + s ^ 2 ≠ 0)
    (hr : p ^ 2 + q ^ 2 ≠ 0)
    (h1 : s ^ 2 - n ^ 2 = (p ^ 2 + q ^ 2) ^ 2 + ε * (p ^ 2 - q ^ 2))
    (h2 : s * n = ε * p * q) :
    -ε*p*q*(1/(s ^ 2))*((1/(p ^ 2 + q ^ 2)) + (1/(n ^ 2 + s ^ 2))*(p ^ 2 + q ^ 2))*(-n*p +
      q*s) + ε*p*(1/(s)) =
      ((1/(p ^ 2 + q ^ 2)) - (1/(n ^ 2 + s ^ 2))*(p ^ 2 + q ^ 2))*(n*q + p*s) := by
  rw [← sub_eq_zero]
  have hN : ε*q*n ^ 3*p ^ 2 + ε*s*n ^ 2*p ^ 3 + ε*n*q*p ^ 6 + 2*ε*n*p ^ 4*q ^ 3 +
      ε*n*p ^ 2*q ^ 5 + ε*n*q*p ^ 2*s ^ 2 - ε*s*p ^ 5*q ^ 2 - 2*ε*s*p ^ 3*q ^ 4 +
      ε*p ^ 3*s ^ 3 - ε*p*s*q ^ 6 - q*n ^ 3*s ^ 2 - p*n ^ 2*s ^ 3 + n*q*p ^ 4*s ^ 2 +
      2*n*p ^ 2*q ^ 3*s ^ 2 + n*q ^ 5*s ^ 2 - n*q*s ^ 4 + p ^ 5*s ^ 3 + 2*p ^ 3*q ^ 2*s ^ 3
      + p*q ^ 4*s ^ 3 - p*s ^ 5 = 0 := by
    linear_combination (-ε*n*q*p ^ 2 + ε*p*s*q ^ 2 - n*q*s ^ 2 - p*s ^ 3) * h1 + (ε*n*p ^ 3
      - ε*n*p*q ^ 2 - ε*q*s*p ^ 2 + ε*s*q ^ 3 - 2*q*s*n ^ 2 - 2*n*p*s ^ 2) * h2
  rw [show -ε*p*q*(1/(s ^ 2))*((1/(p ^ 2 + q ^ 2)) + (1/(n ^ 2 + s ^ 2))*(p ^ 2 +
      q ^ 2))*(-n*p + q*s) + ε*p*(1/(s)) - (((1/(p ^ 2 + q ^ 2)) - (1/(n ^ 2 +
      s ^ 2))*(p ^ 2 + q ^ 2))*(n*q + p*s)) =
      (ε*q*n ^ 3*p ^ 2 + ε*s*n ^ 2*p ^ 3 + ε*n*q*p ^ 6 + 2*ε*n*p ^ 4*q ^ 3 + ε*n*p ^ 2*q ^ 5
      + ε*n*q*p ^ 2*s ^ 2 - ε*s*p ^ 5*q ^ 2 - 2*ε*s*p ^ 3*q ^ 4 + ε*p ^ 3*s ^ 3 -
      ε*p*s*q ^ 6 - q*n ^ 3*s ^ 2 - p*n ^ 2*s ^ 3 + n*q*p ^ 4*s ^ 2 + 2*n*p ^ 2*q ^ 3*s ^ 2
      + n*q ^ 5*s ^ 2 - n*q*s ^ 4 + p ^ 5*s ^ 3 + 2*p ^ 3*q ^ 2*s ^ 3 + p*q ^ 4*s ^ 3 -
      p*s ^ 5) / (s ^ 2*(n ^ 2 + s ^ 2)*(p ^ 2 + q ^ 2)) by field_simp; ring, hN, zero_div]


/-! ## Derivatives

All derivatives below are actual Fréchet derivatives on `𝒰`. The derivative of `σ` is first
obtained from the two square roots and then rewritten, using the relations above, in the compact
form `dσ = c₊ (α dx + β dy)`, `dν = c₋ (-β dx + α dy)` with `c± = 1/r² ± r²/|P|²`
(equivalently `dP = K dω + (r²/K) dω̄` with `K = P/ω`; cf. paper (3.4)–(3.5):
`∂_ω K = 0`, `∂_ω̄ K = ω̄/K`). -/

/-- Derivative of `Re Z`. -/
@[expose] def dZr (ε : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  (4 * r2 x * x 0 + 2 * ε * x 0) • pr 0 + (4 * r2 x * x 1 - 2 * ε * x 1) • pr 1

/-- Derivative of `Im Z`. -/
@[expose] def dZi (ε : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  (2 * ε * x 1) • pr 0 + (2 * ε * x 0) • pr 1

/-- `c₊ = 1/r² + r²/|P|²`. -/
@[expose] def cp (ε : ℝ) (x : Space) : ℝ := 1 / r2 x + r2 x / Mq ε x

/-- `c₋ = 1/r² - r²/|P|²`. -/
@[expose] def cm (ε : ℝ) (x : Space) : ℝ := 1 / r2 x - r2 x / Mq ε x

/-- Compact derivative of `σ`. -/
@[expose] def dsg (ε : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  cp ε x • (al ε x • pr 0 + be ε x • pr 1)

/-- Compact derivative of `ν`. -/
@[expose] def dnu (ε : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  cm ε x • ((-be ε x) • pr 0 + al ε x • pr 1)

/-- Derivative of `Re u`: `du = -iλ u dz - v dP`. -/
@[expose] def duR (ε S lam : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  (lam * uI ε S lam x) • pr 2 - vR ε S lam x • dsg ε x + vI ε S lam x • dnu ε x

/-- Derivative of `Im u`. -/
@[expose] def duI (ε S lam : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  (-(lam * uR ε S lam x)) • pr 2 - vR ε S lam x • dnu ε x - vI ε S lam x • dsg ε x

/-- Derivative of `Re v`: `dv = -iλ v dz + u dP`. -/
@[expose] def dvR (ε S lam : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  (lam * vI ε S lam x) • pr 2 + uR ε S lam x • dsg ε x - uI ε S lam x • dnu ε x

/-- Derivative of `Im v`. -/
@[expose] def dvI (ε S lam : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  (-(lam * vR ε S lam x)) • pr 2 + uR ε S lam x • dnu ε x + uI ε S lam x • dsg ε x

/-- Derivative of `α`. -/
@[expose] def dal (ε : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  x 0 • dsg ε x + sg ε x • pr 0 + x 1 • dnu ε x + nu ε x • pr 1

/-- Derivative of `β`. -/
@[expose] def dbe (ε : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  x 1 • dsg ε x + sg ε x • pr 1 - x 0 • dnu ε x - nu ε x • pr 0

/-- Derivative of `|P|²`. -/
@[expose] def dMq (ε : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  (2 * sg ε x) • dsg ε x + (2 * nu ε x) • dnu ε x

/-- Derivative of a quotient `N / D` (with `D = 2|P|²`). -/
@[expose] def dQuot (N D : ℝ) (dN dD : Space →L[ℝ] ℝ) : Space →L[ℝ] ℝ :=
  D⁻¹ • dN - (N / D ^ 2) • dD

/-- Numerator of `B_x` (times `2|P|²`). -/
@[expose] def N0 (ε S lam : ℝ) (x : Space) : ℝ := -(uR ε S lam x * be ε x + uI ε S lam x * al ε x)

/-- Numerator of `B_y` (times `2|P|²`). -/
@[expose] def N1 (ε S lam : ℝ) (x : Space) : ℝ := uR ε S lam x * al ε x - uI ε S lam x * be ε x

/-- Derivative of `N0`. -/
@[expose] def dN0 (ε S lam : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  -(be ε x • duR ε S lam x + uR ε S lam x • dbe ε x + al ε x • duI ε S lam x +
    uI ε S lam x • dal ε x)

/-- Derivative of `N1`. -/
@[expose] def dN1 (ε S lam : ℝ) (x : Space) : Space →L[ℝ] ℝ :=
  al ε x • duR ε S lam x + uR ε S lam x • dal ε x - be ε x • duI ε S lam x -
    uI ε S lam x • dbe ε x

/-- The derivative operator of the field, assembled from its coordinates. -/
@[expose] def fieldDeriv (ε S lam : ℝ) (x : Space) : Space →L[ℝ] Space :=
  (dQuot (N0 ε S lam x) (2 * Mq ε x) (dN0 ε S lam x) (2 • dMq ε x)).smulRight (basis 0) +
  (dQuot (N1 ε S lam x) (2 * Mq ε x) (dN1 ε S lam x) (2 • dMq ε x)).smulRight (basis 1) +
  (-(lam⁻¹ • dvR ε S lam x)).smulRight (basis 2)

section Derivs
variable (ε S lam : ℝ) (x : Space)

/-- Derivative of `Re Z`. -/
theorem hasFDerivAt_Zr : HasFDerivAt (Zr ε) (dZr ε x) x := by
  have := ((((hasFDerivAt_pr x 0).pow 2).add ((hasFDerivAt_pr x 1).pow 2)).pow 2).add
    ((((hasFDerivAt_pr x 0).pow 2).sub ((hasFDerivAt_pr x 1).pow 2)).const_mul ε)
  refine hfd this (fun y => rfl) ?_
  ext v
  simp only [Fin.isValue, Pi.add_apply, Nat.add_one_sub_one, pow_one, smul_add, nsmul_eq_mul,
    Nat.cast_ofNat, add_apply, smul_apply, PiLp.proj_apply, smul_eq_mul, sub_apply, dZr, r2]
  ring

/-- Derivative of `Im Z`. -/
theorem hasFDerivAt_Zi : HasFDerivAt (Zi ε) (dZi ε x) x := by
  have := (((hasFDerivAt_pr x 0).const_mul (2 * ε)).mul (hasFDerivAt_pr x 1))
  refine hfd this (fun y => rfl) ?_
  ext v
  simp only [Fin.isValue, add_apply, smul_apply, PiLp.proj_apply, smul_eq_mul, dZi]
  ring

/-- On `𝒰`, `|Z| > 0`. -/
theorem Mo_pos {ε : ℝ} {x : Space} (hx : x ∈ U ε) : 0 < Mo ε x := by
  have h1 := abs_Zr_le ε x
  have h2 : 0 < Mo ε x + Zr ε x := hx
  linarith [le_abs_self (Zr ε x)]

/-- Derivative of `|Z|` on `𝒰`. -/
theorem hasFDerivAt_Mo {x : Space} (hx : x ∈ U ε) :
    HasFDerivAt (Mo ε) ((Zr ε x / Mo ε x) • dZr ε x + (Zi ε x / Mo ε x) • dZi ε x) x := by
  have hne : Zr ε x ^ 2 + Zi ε x ^ 2 ≠ 0 := by
    rw [← Mo_sq]; exact pow_ne_zero 2 (Mo_pos hx).ne'
  have := (((hasFDerivAt_Zr ε x).pow 2).add ((hasFDerivAt_Zi ε x).pow 2)).sqrt hne
  refine hfd this (fun y => rfl) ?_
  have hm : √(Zr ε x ^ 2 + Zi ε x ^ 2) = Mo ε x := rfl
  have hM := (Mo_pos hx).ne'
  ext v
  simp only [Pi.add_apply, hm, one_div, mul_inv_rev, Nat.add_one_sub_one, pow_one, nsmul_eq_mul,
    Nat.cast_ofNat, smul_add, add_apply, smul_apply, smul_eq_mul]
  field_simp

/-- Derivative of `σ` on `𝒰`, in compact form. -/
theorem hasFDerivAt_sg {x : Space} (hx : x ∈ U ε) : HasFDerivAt (sg ε) (dsg ε x) x := by
  have hne : (Mo ε x + Zr ε x) * 2⁻¹ ≠ 0 := by
    have : 0 < Mo ε x + Zr ε x := hx
    positivity
  have := (((hasFDerivAt_Mo ε hx).fun_add (hasFDerivAt_Zr ε x)).mul_const (2 : ℝ)⁻¹).sqrt hne
  refine hfd this (fun y => by rw [sg, div_eq_mul_inv]) ?_
  have hs : √((Mo ε x + Zr ε x) * 2⁻¹) = sg ε x := by rw [sg, div_eq_mul_inv]
  have hMo : Mo ε x = sg ε x ^ 2 + nu ε x ^ 2 := (Mq_eq_Mo hx).symm
  have h1 := sg_sq_sub_nu_sq hx
  have h2 := sg_mul_nu hx
  have hs0 := (sg_pos hx).ne'
  have hr0 := (r2_pos hx).ne'
  have hm0 := (Mq_pos hx).ne'
  ext v
  simp only [hs, one_div, mul_inv_rev, dZr, Fin.isValue, smul_add, dZi, add_apply, smul_apply,
      PiLp.proj_apply, smul_eq_mul, dsg, cp, al, be]
  rw [hMo]
  unfold Mq at hm0 ⊢
  unfold Zr Zi r2 at *
  generalize sg ε x = s at *
  generalize nu ε x = n at *
  generalize x 0 = p at *
  generalize x 1 = q at *
  have hm : n ^ 2 + s ^ 2 ≠ 0 := by rwa [add_comm]
  linear_combination (v 0) * sg_coeff0 hs0 hm hr0 h1 h2 + (v 1) * sg_coeff1 hs0 hm hr0 h1 h2

/-- Derivative of `ν` on `𝒰`, in compact form. -/
theorem hasFDerivAt_nu {x : Space} (hx : x ∈ U ε) : HasFDerivAt (nu ε) (dnu ε x) x := by
  have hs0 := (sg_pos hx).ne'
  have hi := (hasDerivAt_inv hs0).hasFDerivAt.comp x (hasFDerivAt_sg ε hx)
  have := (((hasFDerivAt_pr x 0).const_mul ε).mul (hasFDerivAt_pr x 1)).mul hi
  refine hfd this (fun y => by simp only [nu, div_eq_mul_inv]; rfl) ?_
  have h1 := sg_sq_sub_nu_sq hx
  have h2 := sg_mul_nu hx
  have hr0 := (r2_pos hx).ne'
  have hm0 := (Mq_pos hx).ne'
  have hn : nu ε x = ε * x 0 * x 1 / sg ε x := rfl
  ext v
  simp only [Fin.isValue, Pi.mul_apply, dsg, cp, one_div, al, be, smul_add,
      ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smulₛₗ, RingHom.id_apply,
      Function.comp_apply, add_apply, smul_apply, ContinuousLinearMap.comp_apply, PiLp.proj_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_neg, dnu, cm, neg_sub]
  unfold Mq at hm0 ⊢
  unfold Zr r2 at *
  generalize sg ε x = s at *
  generalize nu ε x = n at *
  generalize x 0 = p at *
  generalize x 1 = q at *
  have hm : n ^ 2 + s ^ 2 ≠ 0 := by rwa [add_comm]
  linear_combination (v 0) * nu_coeff0 hs0 hm hr0 h1 h2 + (v 1) * nu_coeff1 hs0 hm hr0 h1 h2

/-- Derivative of `cos λz`. -/
theorem hasFDerivAt_cz : HasFDerivAt (cz lam) ((-(lam * sz lam x)) • pr 2) x := by
  have := ((hasFDerivAt_pr x 2).const_mul lam).cos
  refine hfd this (fun y => rfl) ?_
  ext v
  simp only [Fin.isValue, smul_apply, PiLp.proj_apply, smul_eq_mul, neg_mul, sz, neg_inj]
  ring

/-- Derivative of `sin λz`. -/
theorem hasFDerivAt_sz : HasFDerivAt (sz lam) ((lam * cz lam x) • pr 2) x := by
  have := ((hasFDerivAt_pr x 2).const_mul lam).sin
  refine hfd this (fun y => rfl) ?_
  ext v
  simp only [Fin.isValue, smul_apply, PiLp.proj_apply, smul_eq_mul, cz]
  ring

/-- Derivative of `Re u` on `𝒰`. -/
theorem hasFDerivAt_uR {x : Space} (hx : x ∈ U ε) :
    HasFDerivAt (uR ε S lam) (duR ε S lam x) x := by
  have hX := (hasFDerivAt_sg ε hx).sub_const S
  have := (((hasFDerivAt_cz lam x).mul hX.cos).mul (hasFDerivAt_nu ε hx).cosh).sub
    (((hasFDerivAt_sz lam x).mul hX.sin).mul (hasFDerivAt_nu ε hx).sinh)
  refine hfd this (fun y => rfl) ?_
  ext v
  simp only [Pi.mul_apply, Fin.isValue, smul_add, sub_apply, add_apply, smul_apply, smul_eq_mul,
      neg_mul, mul_neg, PiLp.proj_apply, duR, uI, neg_add_rev, vR, vI]
  ring

/-- Derivative of `Im u` on `𝒰`. -/
theorem hasFDerivAt_uI {x : Space} (hx : x ∈ U ε) :
    HasFDerivAt (uI ε S lam) (duI ε S lam x) x := by
  have hX := (hasFDerivAt_sg ε hx).sub_const S
  have := ((((hasFDerivAt_sz lam x).mul hX.cos).mul (hasFDerivAt_nu ε hx).cosh).add
    (((hasFDerivAt_cz lam x).mul hX.sin).mul (hasFDerivAt_nu ε hx).sinh)).neg
  refine hfd this (fun y => rfl) ?_
  ext v
  simp only [Pi.mul_apply, Fin.isValue, smul_add, neg_add_rev, add_apply, neg_apply, smul_apply,
      PiLp.proj_apply, smul_eq_mul, neg_mul, mul_neg, neg_neg, duI, uR, vR, vI, sub_apply]
  ring

/-- Derivative of `Re v` on `𝒰`. -/
theorem hasFDerivAt_vR {x : Space} (hx : x ∈ U ε) :
    HasFDerivAt (vR ε S lam) (dvR ε S lam x) x := by
  have hX := (hasFDerivAt_sg ε hx).sub_const S
  have := (((hasFDerivAt_cz lam x).mul hX.sin).mul (hasFDerivAt_nu ε hx).cosh).add
    (((hasFDerivAt_sz lam x).mul hX.cos).mul (hasFDerivAt_nu ε hx).sinh)
  refine hfd this (fun y => rfl) ?_
  ext v
  simp only [Pi.mul_apply, Fin.isValue, smul_add, add_apply, smul_apply, smul_eq_mul,
      PiLp.proj_apply, neg_mul, mul_neg, dvR, vI, uR, uI, neg_add_rev, sub_apply]
  ring

/-- Derivative of `Im v` on `𝒰`. -/
theorem hasFDerivAt_vI {x : Space} (hx : x ∈ U ε) :
    HasFDerivAt (vI ε S lam) (dvI ε S lam x) x := by
  have hX := (hasFDerivAt_sg ε hx).sub_const S
  have := (((hasFDerivAt_cz lam x).mul hX.cos).mul (hasFDerivAt_nu ε hx).sinh).sub
    (((hasFDerivAt_sz lam x).mul hX.sin).mul (hasFDerivAt_nu ε hx).cosh)
  refine hfd this (fun y => rfl) ?_
  ext v
  simp only [Pi.mul_apply, Fin.isValue, smul_add, sub_apply, add_apply, smul_apply, smul_eq_mul,
      neg_mul, mul_neg, PiLp.proj_apply, dvI, vR, uR, uI, neg_add_rev]
  ring

/-- Derivative of `α` on `𝒰`. -/
theorem hasFDerivAt_al {x : Space} (hx : x ∈ U ε) : HasFDerivAt (al ε) (dal ε x) x := by
  have := ((hasFDerivAt_sg ε hx).mul (hasFDerivAt_pr x 0)).add
    ((hasFDerivAt_nu ε hx).mul (hasFDerivAt_pr x 1))
  refine hfd this (fun y => rfl) ?_
  ext v
  simp only [Fin.isValue, add_apply, smul_apply, PiLp.proj_apply, smul_eq_mul, dal]
  ring

/-- Derivative of `β` on `𝒰`. -/
theorem hasFDerivAt_be {x : Space} (hx : x ∈ U ε) : HasFDerivAt (be ε) (dbe ε x) x := by
  have := ((hasFDerivAt_sg ε hx).mul (hasFDerivAt_pr x 1)).sub
    ((hasFDerivAt_nu ε hx).mul (hasFDerivAt_pr x 0))
  refine hfd this (fun y => rfl) ?_
  ext v
  simp only [Fin.isValue, sub_apply, add_apply, smul_apply, PiLp.proj_apply, smul_eq_mul, dbe]
  ring

/-- Derivative of `|P|²` on `𝒰`. -/
theorem hasFDerivAt_Mq {x : Space} (hx : x ∈ U ε) : HasFDerivAt (Mq ε) (dMq ε x) x := by
  have := ((hasFDerivAt_sg ε hx).pow 2).add ((hasFDerivAt_nu ε hx).pow 2)
  refine hfd this (fun y => rfl) ?_
  ext v
  simp only [Nat.add_one_sub_one, pow_one, nsmul_eq_mul, Nat.cast_ofNat, add_apply, smul_apply,
      smul_eq_mul, dMq]

/-- Derivative of `N / (2|P|²)` on `𝒰`. -/
theorem hasFDerivAt_quot {N : Space → ℝ} {dN : Space →L[ℝ] ℝ} {x : Space} (hx : x ∈ U ε)
    (h : HasFDerivAt N dN x) :
    HasFDerivAt (fun y => N y / (2 * Mq ε y)) (dQuot (N x) (2 * Mq ε x) dN (2 • dMq ε x)) x := by
  have hs : 2 * Mq ε x ≠ 0 := by have := Mq_pos hx; positivity
  have hD : HasFDerivAt (fun y => 2 * Mq ε y) (2 • dMq ε x) x := by
    have := (hasFDerivAt_Mq ε hx).const_mul 2
    refine this.congr_fderiv ?_
    ext v; simp only [smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  have hi := (hasDerivAt_inv hs).hasFDerivAt.comp x hD
  have := h.mul hi
  refine hfd this (fun y => by simp only [div_eq_mul_inv]; rfl) ?_
  ext v
  simp only [ContinuousLinearMap.comp_smul, Function.comp_apply, mul_inv_rev, add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
      mul_neg, smul_neg, nsmul_eq_mul, Nat.cast_ofNat, dQuot, sub_apply]
  field_simp
  ring

/-- Derivative of `N0` on `𝒰`. -/
theorem hasFDerivAt_N0 {x : Space} (hx : x ∈ U ε) :
    HasFDerivAt (N0 ε S lam) (dN0 ε S lam x) x := by
  have := (((hasFDerivAt_uR ε S lam hx).mul (hasFDerivAt_be ε hx)).add
    ((hasFDerivAt_uI ε S lam hx).mul (hasFDerivAt_al ε hx))).neg
  refine hfd this (fun y => rfl) ?_
  ext v
  simp only [neg_add_rev, add_apply, neg_apply, smul_apply, smul_eq_mul, dN0]
  ring

/-- Derivative of `N1` on `𝒰`. -/
theorem hasFDerivAt_N1 {x : Space} (hx : x ∈ U ε) :
    HasFDerivAt (N1 ε S lam) (dN1 ε S lam x) x := by
  have := ((hasFDerivAt_uR ε S lam hx).mul (hasFDerivAt_al ε hx)).sub
    ((hasFDerivAt_uI ε S lam hx).mul (hasFDerivAt_be ε hx))
  refine hfd this (fun y => rfl) ?_
  ext v
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, dN1]
  ring

/-- **The actual Fréchet derivative of the field** at every point of `𝒰`. -/
theorem field_hasFDerivAt {x : Space} (hx : x ∈ U ε) :
    HasFDerivAt (field ε S lam) (fieldDeriv ε S lam x) x := by
  have hB := hasFDerivAt_of_coords (B := field ε S lam)
    (L := ![dQuot (N0 ε S lam x) (2 * Mq ε x) (dN0 ε S lam x) (2 • dMq ε x),
      dQuot (N1 ε S lam x) (2 * Mq ε x) (dN1 ε S lam x) (2 • dMq ε x),
      -(lam⁻¹ • dvR ε S lam x)]) (x := x) (fun k => by
        fin_cases k
        · exact hasFDerivAt_quot ε hx (hasFDerivAt_N0 ε S lam hx)
        · exact hasFDerivAt_quot ε hx (hasFDerivAt_N1 ε S lam hx)
        · have := ((hasFDerivAt_vR ε S lam hx).const_mul lam⁻¹).neg
          refine hfd this (fun y => ?_) ?_
          · simp only [field, neg_add_rev, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val,
              Pi.neg_apply]
            ring
          · ext v; simp only [neg_apply, smul_apply, smul_eq_mul, Fin.reduceFinMk,
              Matrix.cons_val])
  refine hB.congr_fderiv ?_
  simp only [Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, fieldDeriv]

end Derivs

/-! ## `∇ · B = 0` -/

/-- **`∇ · B = 0` on `𝒰`** (paper, below (3.4): `2∂_ω W = i cos Ξ`, so `∂_z B_z` cancels the
horizontal divergence). -/
theorem field_divergence_free {ε S lam : ℝ} (hl : lam ≠ 0) {x : Space} (hx : x ∈ U ε) :
    divergence (fderiv ℝ (field ε S lam) x) = 0 := by
  rw [(field_hasFDerivAt ε S lam hx).fderiv, divergence_apply]
  have hr := (r2_pos hx).ne'
  have hm := (Mq_pos hx).ne'
  simp only [Fin.isValue, fieldDeriv, dQuot, mul_inv_rev, dN0, duR, dsg, cp, one_div, smul_add, dnu,
      cm, dbe, duI, dal, neg_add_rev, smul_neg, N0, dMq, basis, dN1, N1, dvR, add_apply,
      ContinuousLinearMap.smulRight_apply, sub_apply, neg_apply, smul_apply, PiLp.proj_apply, ne_eq,
      one_ne_zero, not_false_eq_true, PiLp.single_eq_of_ne, smul_eq_mul, mul_zero, neg_zero,
      PiLp.single_eq_same, mul_one, mul_neg, neg_neg, zero_add, Fin.reduceEq, add_zero,
      sub_neg_eq_add, zero_sub, nsmul_eq_mul, Nat.cast_ofNat, neg_smul, PiLp.add_apply,
      PiLp.smul_apply, zero_ne_one, PiLp.neg_apply, sub_zero, sub_self]
  unfold Mq r2 al be at *
  generalize uR ε S lam x = a at *
  generalize uI ε S lam x = b at *
  generalize vR ε S lam x = c at *
  generalize vI ε S lam x = d at *
  generalize sg ε x = s at *
  generalize nu ε x = n at *
  generalize x 0 = p at *
  generalize x 1 = q at *
  field_simp
  ring

/-! ## Trigonometric identities for `u`, `v` -/

/-- `Re u Im u + Re v Im v = -sin λz cos λz`, i.e. `Im(u² + v²)/2 = Im(e^{-2iλz})/2`
(from `cos² + sin² = 1` for the complex argument `P - S`). -/
theorem uv_cross (ε S lam : ℝ) (x : Space) :
    uI ε S lam x * uR ε S lam x + vI ε S lam x * vR ε S lam x = -(sz lam x * cz lam x) := by
  have h1 := Real.cos_sq_add_sin_sq (sg ε x - S)
  have h2 := Real.cosh_sq_sub_sinh_sq (nu ε x)
  unfold uR uI vR vI
  linear_combination (-(cz lam x * sz lam x) * (Real.cosh (nu ε x) ^ 2 - Real.sinh (nu ε x) ^ 2)) *
    h1 + (-(cz lam x * sz lam x)) * h2

/-! ## Flux label, pressure and force balance -/

/-- The flux label (paper (3.3)): `ψ = (sin² λz + (Re(e^{-iλz} cos Ξ))²)/2`; here
`Re(e^{-iλz} cos Ξ) = -Re v = λ B_z`. -/
@[expose] def psi (ε S lam : ℝ) (x : Space) : ℝ := (sz lam x ^ 2 + vR ε S lam x ^ 2) / 2

/-- The gradient of `ψ`. -/
@[expose] def gradPsi (ε S lam : ℝ) (x : Space) : Space :=
  toLp 2 ![vR ε S lam x * dvR ε S lam x (basis 0), vR ε S lam x * dvR ε S lam x (basis 1),
    lam * (sz lam x * cz lam x) + vR ε S lam x * dvR ε S lam x (basis 2)]

/-- A linear functional in coordinates. -/
theorem clm_coords (f : Space →L[ℝ] ℝ) (v : Space) :
    f v = v 0 * f (basis 0) + v 1 * f (basis 1) + v 2 * f (basis 2) := by
  conv_lhs => rw [LandremanEquilibrium.eq_sum_basis v]
  simp only [map_add, map_smul, smul_eq_mul]

/-- `ψ` has gradient `gradPsi` on `𝒰`. -/
theorem psi_hasFDerivAt (ε S lam : ℝ) {x : Space} (hx : x ∈ U ε) :
    HasFDerivAt (psi ε S lam) (innerSL ℝ (gradPsi ε S lam x)) x := by
  have := (((hasFDerivAt_sz lam x).pow 2).add ((hasFDerivAt_vR ε S lam hx).pow 2)).mul_const
    (2 : ℝ)⁻¹
  refine hfd this (fun y => by simp only [psi, div_eq_mul_inv]; rfl) ?_
  ext v
  rw [innerSL_apply_apply, inner_coords]
  simp only [Nat.add_one_sub_one, pow_one, nsmul_eq_mul, Nat.cast_ofNat, Fin.isValue, smul_add,
      add_apply, smul_apply, PiLp.proj_apply, smul_eq_mul, gradPsi, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
  rw [clm_coords (dvR ε S lam x) v]
  simp only [Fin.isValue, basis]
  ring

/-- Ampère current `J = (∇ × B)/μ₀` from the actual derivative. -/
@[expose] def current (μ₀ ε S lam : ℝ) (x : Space) : Space :=
  μ₀⁻¹ • curl (fderiv ℝ (field ε S lam) x)

/-- Pressure `p = (p_a - ψ/λ²)/μ₀` (paper (3.3), there with `μ₀ = 1`). -/
@[expose] def pressure (μ₀ pa ε S lam : ℝ) (x : Space) : ℝ := (pa - psi ε S lam x / lam ^ 2) / μ₀

/-- Pressure gradient `∇p = -∇ψ/(μ₀ λ²)`. -/
@[expose] def pressureGrad (μ₀ ε S lam : ℝ) (x : Space) : Space :=
  (-(μ₀ * lam ^ 2)⁻¹) • gradPsi ε S lam x

/-- The pressure gradient is the actual Fréchet derivative of the pressure on `𝒰`. -/
theorem pressure_hasFDerivAt (μ₀ pa ε S lam : ℝ) {x : Space} (hx : x ∈ U ε) :
    HasFDerivAt (pressure μ₀ pa ε S lam) (innerSL ℝ (pressureGrad μ₀ ε S lam x)) x := by
  have h := (((psi_hasFDerivAt ε S lam hx).mul_const (lam ^ 2)⁻¹).const_sub pa).mul_const μ₀⁻¹
  refine hfd h (fun y => by simp only [pressure, div_eq_mul_inv]) ?_
  ext v
  simp only [smul_neg, neg_apply, smul_apply, coe_innerSL_apply, smul_eq_mul, pressureGrad,
      mul_inv_rev, neg_smul, map_neg, map_smul, neg_inj]
  ring

/-- Coordinates of the field derivative. -/
theorem fieldDeriv_apply (ε S lam : ℝ) (x v : Space) :
    fieldDeriv ε S lam x v 0 = dQuot (N0 ε S lam x) (2 * Mq ε x) (dN0 ε S lam x) (2 • dMq ε x) v ∧
    fieldDeriv ε S lam x v 1 = dQuot (N1 ε S lam x) (2 * Mq ε x) (dN1 ε S lam x) (2 • dMq ε x) v ∧
    fieldDeriv ε S lam x v 2 = -(lam⁻¹ * dvR ε S lam x v) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [fieldDeriv, basis]

/-- The key identity `(B·∇)B - (DB)ᵀB = -∇ψ/λ²` on `𝒰`, equivalently the transport identity
`(B·∇)B = -∇Q` with `Q = -|B_⊥|²/2 + sin²(λz)/(2λ²)` (paper (3.5)–(3.7)). -/
theorem transport_key {ε S lam : ℝ} (hl : lam ≠ 0) {x : Space} (hx : x ∈ U ε) :
    fieldDeriv ε S lam x (field ε S lam x) - adjApply (fieldDeriv ε S lam x) (field ε S lam x) =
      (-(lam ^ 2)⁻¹) • gradPsi ε S lam x := by
  have hr := (r2_pos hx).ne'
  have hm := (Mq_pos hx).ne'
  have hT := uv_cross ε S lam x
  have hT' : sz lam x * cz lam x = -(uI ε S lam x * uR ε S lam x
      + vI ε S lam x * vR ε S lam x) := by
    linarith
  apply space_ext
  · simp only [Fin.isValue, fieldDeriv, dQuot, mul_inv_rev, dN0, duR, dsg, cp, one_div, smul_add,
      dnu, cm, dbe, duI, dal, neg_add_rev, smul_neg, N0, dMq, basis, dN1, N1, dvR, field, add_apply,
      ContinuousLinearMap.smulRight_apply, sub_apply, neg_apply, smul_apply, PiLp.proj_apply,
      Matrix.cons_val_one, Matrix.cons_val_zero, smul_eq_mul, mul_neg, neg_neg,
      Matrix.cons_val, nsmul_eq_mul, Nat.cast_ofNat, neg_smul, adjApply, ne_eq, one_ne_zero,
      not_false_eq_true, PiLp.single_eq_of_ne, mul_zero, neg_zero, PiLp.single_eq_same, mul_one,
      zero_add, Fin.reduceEq, add_zero, sub_neg_eq_add, zero_sub, inner_coords,
      PiLp.add_apply, PiLp.smul_apply, zero_ne_one, PiLp.neg_apply, sub_zero, sub_self,
      PiLp.sub_apply, gradPsi]
    unfold Mq r2 al be at *
    generalize uR ε S lam x = a at *
    generalize uI ε S lam x = b at *
    generalize vR ε S lam x = c at *
    generalize vI ε S lam x = d at *
    generalize sg ε x = s at *
    generalize nu ε x = n at *
    generalize x 0 = p at *
    generalize x 1 = q at *
    field_simp
    ring
  · simp only [Fin.isValue, fieldDeriv, dQuot, mul_inv_rev, dN0, duR, dsg, cp, one_div, smul_add,
      dnu, cm, dbe, duI, dal, neg_add_rev, smul_neg, N0, dMq, basis, dN1, N1, dvR, field, add_apply,
      ContinuousLinearMap.smulRight_apply, sub_apply, neg_apply, smul_apply, PiLp.proj_apply,
      Matrix.cons_val_one, Matrix.cons_val_zero, smul_eq_mul, mul_neg, neg_neg,
      Matrix.cons_val, nsmul_eq_mul, Nat.cast_ofNat, neg_smul, adjApply, ne_eq, one_ne_zero,
      not_false_eq_true, PiLp.single_eq_of_ne, mul_zero, neg_zero, PiLp.single_eq_same, mul_one,
      zero_add, Fin.reduceEq, add_zero, sub_neg_eq_add, zero_sub, inner_coords,
      PiLp.add_apply, PiLp.smul_apply, zero_ne_one, PiLp.neg_apply, sub_zero, sub_self,
      PiLp.sub_apply, gradPsi]
    unfold Mq r2 al be at *
    generalize uR ε S lam x = a at *
    generalize uI ε S lam x = b at *
    generalize vR ε S lam x = c at *
    generalize vI ε S lam x = d at *
    generalize sg ε x = s at *
    generalize nu ε x = n at *
    generalize x 0 = p at *
    generalize x 1 = q at *
    field_simp
    ring
  · simp only [Fin.isValue, fieldDeriv, dQuot, mul_inv_rev, dN0, duR, dsg, cp, one_div, smul_add,
      dnu, cm, dbe, duI, dal, neg_add_rev, smul_neg, N0, dMq, basis, dN1, N1, dvR, field, add_apply,
      ContinuousLinearMap.smulRight_apply, sub_apply, neg_apply, smul_apply, PiLp.proj_apply,
      Matrix.cons_val_one, Matrix.cons_val_zero, smul_eq_mul, mul_neg, neg_neg,
      Matrix.cons_val, nsmul_eq_mul, Nat.cast_ofNat, neg_smul, adjApply, ne_eq, one_ne_zero,
      not_false_eq_true, PiLp.single_eq_of_ne, mul_zero, neg_zero, PiLp.single_eq_same, mul_one,
      zero_add, Fin.reduceEq, add_zero, sub_neg_eq_add, zero_sub, inner_coords,
      PiLp.add_apply, PiLp.smul_apply, zero_ne_one, PiLp.neg_apply, sub_zero, sub_self,
      PiLp.sub_apply, gradPsi]
    rw [hT']
    unfold Mq r2 al be at *
    generalize uR ε S lam x = a at *
    generalize uI ε S lam x = b at *
    generalize vR ε S lam x = c at *
    generalize vI ε S lam x = d at *
    generalize sg ε x = s at *
    generalize nu ε x = n at *
    generalize x 0 = p at *
    generalize x 1 = q at *
    field_simp
    ring

open Matrix in
/-- **Force balance** `J × B = ∇p` (the domain-kernel law) at every point of `𝒰`, with the
actual Ampère current `J = (∇ × B)/μ₀` and the actual pressure gradient (paper (3.7) and below:
`(∇ × B) × B = -∇H = ∇p`, `H = ψ/λ²`). -/
theorem force_balance {ε S lam : ℝ} (hl : lam ≠ 0) (μ₀ : ℝ) {x : Space} (hx : x ∈ U ε) :
    ForceBalance (ofLp (field ε S lam x)) (ofLp (current μ₀ ε S lam x))
      (ofLp (pressureGrad μ₀ ε S lam x)) := by
  refine ⟨?_⟩
  have e : ofLp (current μ₀ ε S lam x) ⨯₃ ofLp (field ε S lam x) =
      ofLp (cross (current μ₀ ε S lam x) (field ε S lam x)) := by simp [cross]
  have hc : current μ₀ ε S lam x = μ₀⁻¹ • curl (fieldDeriv ε S lam x) := by
    rw [current, (field_hasFDerivAt ε S lam hx).fderiv]
  rw [e, hc, ← crossBilinear_apply, map_smul, _root_.smul_apply, crossBilinear_apply,
    curl_cross_eq, transport_key hl hx, pressureGrad, smul_smul]
  congr 2
  field_simp

open Matrix in
/-- Via the kernel: `B · ∇ψ = 0` on `𝒰` (`ψ` is a flux function; paper, below (3.7)). -/
theorem field_tangent_psi {ε S lam : ℝ} (hl : lam ≠ 0) {x : Space} (hx : x ∈ U ε) :
    ⟪field ε S lam x, gradPsi ε S lam x⟫ = 0 := by
  have := force_balance (S := S) hl 1 hx
  have h := field_tangency (ofLp (field ε S lam x)) (ofLp (current 1 ε S lam x))
    (ofLp (pressureGrad 1 ε S lam x))
  have hl2 : (lam ^ 2)⁻¹ ≠ 0 := by positivity
  rw [inner_coords]
  simp only [dotProduct, pressureGrad, one_mul, neg_smul, PiLp.neg_apply, PiLp.smul_apply,
      smul_eq_mul, mul_neg, Finset.sum_neg_distrib, Fin.sum_univ_three, Fin.isValue,
      neg_add_rev] at h
  have h' : (lam ^ 2)⁻¹ * (field ε S lam x 0 * gradPsi ε S lam x 0 +
      field ε S lam x 1 * gradPsi ε S lam x 1 + field ε S lam x 2 * gradPsi ε S lam x 2) = 0 := by
    linarith
  exact (mul_eq_zero.mp h').resolve_left hl2

open Matrix in
/-- Via the kernel: `J · ∇ψ = 0` on `𝒰` (the current lies on the flux surfaces). -/
theorem current_tangent_psi {ε S lam : ℝ} (hl : lam ≠ 0) (μ₀ : ℝ) {x : Space} (hx : x ∈ U ε) :
    ⟪current μ₀ ε S lam x, gradPsi ε S lam x⟫ = 0 := by
  have := force_balance (S := S) hl 1 hx
  have h := current_tangency (ofLp (field ε S lam x)) (ofLp (current 1 ε S lam x))
    (ofLp (pressureGrad 1 ε S lam x))
  have hl2 : (lam ^ 2)⁻¹ ≠ 0 := by positivity
  have hJ : current μ₀ ε S lam x = μ₀⁻¹ • current 1 ε S lam x := by
    simp only [current, inv_one, one_smul]
  rw [hJ, real_inner_smul_left, inner_coords]
  simp only [dotProduct, pressureGrad, one_mul, neg_smul, PiLp.neg_apply, PiLp.smul_apply,
      smul_eq_mul, mul_neg, Finset.sum_neg_distrib, Fin.sum_univ_three, Fin.isValue,
      neg_add_rev] at h
  have h' : (lam ^ 2)⁻¹ * (current 1 ε S lam x 0 * gradPsi ε S lam x 0 +
      current 1 ε S lam x 1 * gradPsi ε S lam x 1 +
      current 1 ε S lam x 2 * gradPsi ε S lam x 2) = 0 := by
    linarith
  rw [(mul_eq_zero.mp h').resolve_left hl2, mul_zero]

/-- `ψ` is an exact first integral of the field on `𝒰`. -/
theorem psi_firstIntegral {ε S lam : ℝ} (hl : lam ≠ 0) :
    FirstIntegralOn (field ε S lam) (psi ε S lam) (U ε) := by
  intro x hx
  refine ⟨(psi_hasFDerivAt ε S lam hx).differentiableAt, ?_⟩
  rw [(psi_hasFDerivAt ε S lam hx).fderiv, innerSL_apply_apply, real_inner_comm,
    field_tangent_psi hl hx]

/-! ## Field-line kinematics on the flux surfaces (paper §3.3)

With `X = λ B_z` and `Y = -sin λz` (paper (3.8)), `ψ = (X² + Y²)/2`, and along every field
line `X' = Y cos λz`, `Y' = -X cos λz`: the point `(X, Y)` turns on its circle with angular
velocity `cos λz` (paper (3.21): `B · ∇χ = √(1 - k² sin² χ)`). -/

/-- `X = λ B_z = Re(e^{-iλz} cos Ξ)` (paper (3.8)). -/
@[expose] def Xf (ε S lam : ℝ) (x : Space) : ℝ := -vR ε S lam x

/-- `Y = -sin λz` (paper (3.8)). -/
@[expose] def Yf (lam : ℝ) (x : Space) : ℝ := -sz lam x

/-- `ψ = (X² + Y²)/2` (paper (3.8)). -/
theorem psi_eq_XY (ε S lam : ℝ) (x : Space) :
    psi ε S lam x = (Xf ε S lam x ^ 2 + Yf lam x ^ 2) / 2 := by
  unfold psi Xf Yf; ring

/-- `B · ∇(Re v) = sin λz cos λz`, i.e. `B · ∇X = Y cos λz`. -/
theorem dvR_field {ε S lam : ℝ} (hl : lam ≠ 0) {x : Space} (hx : x ∈ U ε) :
    dvR ε S lam x (field ε S lam x) = sz lam x * cz lam x := by
  have hr := (r2_pos hx).ne'
  have hm := (Mq_pos hx).ne'
  have key : dvR ε S lam x (field ε S lam x) =
      -(uI ε S lam x * uR ε S lam x + vI ε S lam x * vR ε S lam x) := by
    simp only [dvR, Fin.isValue, dsg, cp, one_div, smul_add, dnu, cm, field, neg_add_rev, sub_apply,
        add_apply, smul_apply, PiLp.proj_apply, Matrix.cons_val, smul_eq_mul, Matrix.cons_val_zero,
        Matrix.cons_val_one, neg_mul, mul_neg]
    unfold Mq r2 al be at *
    generalize uR ε S lam x = a at *
    generalize uI ε S lam x = b at *
    generalize vR ε S lam x = c at *
    generalize vI ε S lam x = d at *
    generalize sg ε x = s at *
    generalize nu ε x = n at *
    generalize x 0 = p at *
    generalize x 1 = q at *
    field_simp
    ring
  rw [key, uv_cross]
  ring

/-- Along a field line, `d/dt X(γ) = Y(γ) cos λz`. -/
theorem X_along {ε S lam : ℝ} (hl : lam ≠ 0) {γ : ℝ → Space} {t : ℝ}
    (hγ : HasDerivAt γ (field ε S lam (γ t)) t) (hU : γ t ∈ U ε) :
    HasDerivAt (fun s => Xf ε S lam (γ s)) (Yf lam (γ t) * cz lam (γ t)) t := by
  have := ((hasFDerivAt_vR ε S lam hU).comp_hasDerivAt t hγ).neg
  rw [dvR_field hl hU] at this
  refine this.congr_deriv ?_
  unfold Yf; ring

/-- Along a field line, `d/dt Y(γ) = -X(γ) cos λz`. -/
theorem Y_along {ε S lam : ℝ} (hl : lam ≠ 0) {γ : ℝ → Space} {t : ℝ}
    (hγ : HasDerivAt γ (field ε S lam (γ t)) t) :
    HasDerivAt (fun s => Yf lam (γ s)) (-(Xf ε S lam (γ t)) * cz lam (γ t)) t := by
  have := ((hasFDerivAt_sz lam (γ t)).comp_hasDerivAt t hγ).neg
  refine this.congr_deriv ?_
  simp only [Fin.isValue, field, neg_add_rev, smul_apply, PiLp.proj_apply, Matrix.cons_val,
      smul_eq_mul, Xf, neg_neg]
  field_simp

/-- The toroidal angular velocity `B · ∇φ = (x B_y - y B_x)/(x² + y²)` (polar angle `φ`). -/
@[expose] def torRate (ε S lam : ℝ) (x : Space) : ℝ :=
  (x 0 * field ε S lam x 1 - x 1 * field ε S lam x 0) / r2 x

/-- `B · ∇φ = Re(u/P)/2 = (σ Re u + ν Im u)/(2|P|²)`. -/
theorem torRate_eq {ε S lam : ℝ} {x : Space} (hx : x ∈ U ε) :
    torRate ε S lam x =
      (sg ε x * uR ε S lam x + nu ε x * uI ε S lam x) / (2 * Mq ε x) := by
  have hr := (r2_pos hx).ne'
  have hm := (Mq_pos hx).ne'
  simp only [torRate, Fin.isValue, field, neg_add_rev, Matrix.cons_val_one, Matrix.cons_val_zero]
  unfold Mq r2 al be at *
  field_simp
  ring

/-! ### Angle lifts -/

/-- **Poloidal angle rate.** If `X = -k cos θ` and `Y = k sin θ` near `t` (with `k ≠ 0`),
`X' = Y c`, `Y' = -X c`, and `θ` is differentiable at `t`, then `θ'(t) = c`. -/
theorem poloidal_lift_deriv {X Y θ : ℝ → ℝ} {k c t : ℝ} (hk : k ≠ 0)
    (hX : HasDerivAt X (Y t * c) t) (hY : HasDerivAt Y (-(X t) * c) t)
    (hθ : DifferentiableAt ℝ θ t)
    (hXθ : ∀ᶠ s in nhds t, X s = -k * Real.cos (θ s))
    (hYθ : ∀ᶠ s in nhds t, Y s = k * Real.sin (θ s)) :
    HasDerivAt θ c t := by
  have hθ' := hθ.hasDerivAt
  have h1 : HasDerivAt X (-k * (-Real.sin (θ t) * deriv θ t)) t :=
    (hθ'.cos.const_mul (-k)).congr_of_eventuallyEq hXθ
  have h2 : HasDerivAt Y (k * (Real.cos (θ t) * deriv θ t)) t :=
    (hθ'.sin.const_mul k).congr_of_eventuallyEq hYθ
  have e1 := hX.unique h1
  have e2 := hY.unique h2
  have hXt : X t = -k * Real.cos (θ t) := hXθ.self_of_nhds
  have hYt : Y t = k * Real.sin (θ t) := hYθ.self_of_nhds
  rw [hYt] at e1
  rw [hXt] at e2
  have hsc := Real.sin_sq_add_cos_sq (θ t)
  have : k * (deriv θ t - c) = 0 := by
    linear_combination (-Real.sin (θ t)) * e1 + (-Real.cos (θ t)) * e2 +
      (-(k * (deriv θ t - c))) * hsc
  have hd : deriv θ t = c := by
    have := (mul_eq_zero.mp this).resolve_left hk
    linarith
  rw [← hd]; exact hθ'

/-- **Toroidal angle rate.** If `x = R cos φ`, `y = R sin φ` near `t` with
`R = √(x² + y²) > 0`, `x' = bx`, `y' = by`, and `φ` is differentiable at `t`, then
`φ'(t) = (x by - y bx)/(x² + y²)`. -/
theorem toroidal_lift_deriv {x y φ : ℝ → ℝ} {bx by' t : ℝ} (hr : 0 < x t ^ 2 + y t ^ 2)
    (hx : HasDerivAt x bx t) (hy : HasDerivAt y by' t) (hφ : DifferentiableAt ℝ φ t)
    (hxφ : ∀ᶠ s in nhds t, x s = √(x s ^ 2 + y s ^ 2) * Real.cos (φ s))
    (hyφ : ∀ᶠ s in nhds t, y s = √(x s ^ 2 + y s ^ 2) * Real.sin (φ s)) :
    HasDerivAt φ ((x t * by' - y t * bx) / (x t ^ 2 + y t ^ 2)) t := by
  have hφ' := hφ.hasDerivAt
  set R' := (2 * x t * bx + 2 * y t * by') / (2 * √(x t ^ 2 + y t ^ 2))
  have hR : HasDerivAt (fun s => √(x s ^ 2 + y s ^ 2)) R' t := by
    have := ((hx.pow 2).add (hy.pow 2)).sqrt hr.ne'
    refine this.congr_deriv ?_
    simp only [R', Nat.cast_ofNat, Pi.add_apply, Pi.pow_apply]
    ring
  have h1 : HasDerivAt x (R' * Real.cos (φ t) +
      √(x t ^ 2 + y t ^ 2) * (-Real.sin (φ t) * deriv φ t)) t :=
    (hR.mul hφ'.cos).congr_of_eventuallyEq hxφ
  have h2 : HasDerivAt y (R' * Real.sin (φ t) +
      √(x t ^ 2 + y t ^ 2) * (Real.cos (φ t) * deriv φ t)) t :=
    (hR.mul hφ'.sin).congr_of_eventuallyEq hyφ
  have e1 := hx.unique h1
  have e2 := hy.unique h2
  have hxt : x t = √(x t ^ 2 + y t ^ 2) * Real.cos (φ t) := hxφ.self_of_nhds
  have hyt : y t = √(x t ^ 2 + y t ^ 2) * Real.sin (φ t) := hyφ.self_of_nhds
  have hsq : √(x t ^ 2 + y t ^ 2) ^ 2 = x t ^ 2 + y t ^ 2 := Real.sq_sqrt hr.le
  have hsc := Real.sin_sq_add_cos_sq (φ t)
  set Rv := √(x t ^ 2 + y t ^ 2) with hRv
  have key : x t * by' - y t * bx = Rv ^ 2 * deriv φ t := by
    rw [e1, e2]
    linear_combination (R' * Real.sin (φ t) + Rv * Real.cos (φ t) * deriv φ t) * hxt +
      (-(R' * Real.cos (φ t)) + Rv * Real.sin (φ t) * deriv φ t) * hyt + (Rv ^ 2 * deriv φ t) * hsc
  have hd : deriv φ t = (x t * by' - y t * bx) / (x t ^ 2 + y t ^ 2) := by
    rw [key, hsq]; field_simp
  rw [← hd]; exact hφ'

/-! ## Shear: numerical constants -/

/-- `cosh(1/8) ≤ 1 + 1/127`. -/
theorem cosh_eighth_le : Real.cosh (1 / 8) ≤ 1 + 1 / 127 := by
  have h1 := Real.cosh_le_exp_half_sq (1 / 8)
  have h := Real.exp_bound (x := (1 / 8) ^ 2 / 2) (by norm_num [abs_of_pos]) (n := 2) (by norm_num)
  simp only [one_div, inv_pow, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
      pow_zero, Nat.factorial, Nat.cast_one, ne_eq, one_ne_zero, not_false_eq_true, div_self,
      pow_one, Nat.succ_eq_add_one, zero_add, mul_one, div_one, sq_abs, Nat.reduceAdd,
      Nat.cast_ofNat] at h
  have := (abs_le.mp h).2
  norm_num at this h1 ⊢
  linarith

/-- `sinh(1/8) ≤ 251/2000`. -/
theorem sinh_eighth_le : Real.sinh (1 / 8) ≤ 251 / 2000 := by
  rw [Real.sinh_eq]
  have h1 := Real.exp_bound (x := 1 / 8) (by norm_num [abs_of_pos]) (n := 3) (by norm_num)
  have h2 := Real.exp_bound (x := -(1 / 8)) (by norm_num [abs_of_pos]) (n := 3) (by norm_num)
  simp only [one_div, inv_pow, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
      pow_zero, inv_one, Nat.factorial, Nat.cast_one, ne_eq, one_ne_zero, not_false_eq_true,
      div_self, pow_one, Nat.succ_eq_add_one, zero_add, mul_one, div_one, Nat.reduceAdd,
      Nat.cast_ofNat, abs_inv, Nat.abs_ofNat, Nat.reduceMul, even_two, Even.neg_pow,
      abs_neg] at h1 h2
  have a1 := (abs_le.mp h1).2
  have a2 := (abs_le.mp h2).1
  norm_num at a1 a2 ⊢
  linarith

/-- `sin(113/100) ≥ 9/10`. -/
theorem sin_113_ge : 9 / 10 ≤ Real.sin (113 / 100) := by
  rw [← Real.cos_pi_div_two_sub]
  have h1 := Real.one_sub_sq_div_two_le_cos (x := Real.pi / 2 - 113 / 100)
  have hp1 := Real.pi_lt_d4
  have hp2 := Real.pi_gt_d4
  nlinarith

/-- `sin(1/19) ≥ 1/20`. -/
theorem sin_19_ge : 1 / 20 ≤ Real.sin (1 / 19) := by
  have := Real.sin_ge_sub_cube (x := 1 / 19) (by norm_num)
  norm_num at this ⊢
  linarith

/-- If `|ξ| < π/2`, `0 ≤ ξm ≤ π/2` and `sin² ξ ≤ sin² ξm`, then `|ξ| ≤ ξm`. -/
theorem abs_le_of_sin_sq_le {ξ ξm : ℝ} (hξ : |ξ| < Real.pi / 2) (h0 : 0 ≤ ξm)
    (h : Real.sin ξ ^ 2 ≤ Real.sin ξm ^ 2) : |ξ| ≤ ξm := by
  by_contra hc
  push Not at hc
  have hlt := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) hξ.le hc
  have hsm : 0 ≤ Real.sin ξm :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  have habs : |Real.sin ξ| = Real.sin |ξ| :=
    Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith [Real.pi_pos])
  have : Real.sin ξm ^ 2 < Real.sin ξ ^ 2 := by
    rw [← sq_abs (Real.sin ξ), habs]
    exact pow_lt_pow_left₀ hlt hsm (by norm_num)
  linarith

/-- For `|ξ| ≤ ξm`, `|ξ| (1 - ξm²/6) ≤ |sin ξ|`. -/
theorem abs_mul_le_abs_sin {ξ ξm : ℝ} (h : |ξ| ≤ ξm) (hm : ξm ≤ 3) :
    |ξ| * (1 - ξm ^ 2 / 6) ≤ |Real.sin ξ| := by
  have h3 := Real.sin_ge_sub_cube (abs_nonneg ξ)
  have hpi : |ξ| ≤ Real.pi := by linarith [Real.pi_gt_three]
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hpi]
  have : |ξ| ^ 2 ≤ ξm ^ 2 := pow_le_pow_left₀ (abs_nonneg ξ) h 2
  nlinarith [abs_nonneg ξ]

/-! ## Shear: pointwise inequalities in the atoms -/

/-- First step: `(σ a + ν b)/(2(σ² + ν²)) ≤ R/(2σ) + 9/(160σ²)` when `|a| ≤ R`, `|ν| ≤ 1/8`,
`|b| ≤ 9/10`. -/
theorem tor_le_inv {s a n b R : ℝ} (hs : 0 < s) (hR : 0 ≤ R) (ha : a ^ 2 ≤ R ^ 2)
    (hn : n ^ 2 ≤ 1 / 64) (hb : b ^ 2 ≤ 81 / 100) :
    (s * a + n * b) / (2 * (s ^ 2 + n ^ 2)) ≤ R / (2 * s) + 9 / (160 * s ^ 2) := by
  have ha' := (abs_le_of_sq_le_sq' ha hR).2
  have hnb : n * b ≤ 9 / 80 :=
    (abs_le_of_sq_le_sq' (show (n * b) ^ 2 ≤ (9 / 80) ^ 2 by
      rw [mul_pow]; nlinarith [sq_nonneg n, sq_nonneg b]) (by norm_num)).2
  have hD : 0 < 2 * (s ^ 2 + n ^ 2) := by positivity
  have hpos : 0 ≤ R / (2 * s) + 9 / (160 * s ^ 2) := by positivity
  have h2 : (R / (2 * s) + 9 / (160 * s ^ 2)) * (2 * s ^ 2) = R * s + 9 / 80 := by
    field_simp; ring
  rw [div_le_iff₀ hD]
  calc s * a + n * b ≤ R * s + 9 / 80 := by nlinarith
    _ = (R / (2 * s) + 9 / (160 * s ^ 2)) * (2 * s ^ 2) := h2.symm
    _ ≤ (R / (2 * s) + 9 / (160 * s ^ 2)) * (2 * (s ^ 2 + n ^ 2)) :=
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg n]) hpos

/-- The constant `c₂ = γ² (ξₘ/6 + 1/σ_min)/S²` with `γ = 1.271`, `ξₘ = 1.13`, `σ_min = 2.87`,
`S = 4`. -/
@[expose] def c2 : ℝ := (1271 / 1000) ^ 2 * (113 / 600 + 100 / 287) / 16

/-- Second step: for `|ξ| ≤ 1.13`, `1/(4 + ξ) ≤ 1/4 - sin ξ/16 + c₂ sin² ξ`. -/
theorem inv_s_le {ξ : ℝ} (hξ : |ξ| ≤ 113 / 100) :
    1 / (4 + ξ) ≤ 1 / 4 - Real.sin ξ / 16 + c2 * Real.sin ξ ^ 2 := by
  have hA := abs_mul_le_abs_sin hξ (by norm_num)
  have hγ : |ξ| ≤ 1271 / 1000 * |Real.sin ξ| := by nlinarith [abs_nonneg ξ]
  have hξ2 : ξ ^ 2 ≤ (1271 / 1000) ^ 2 * Real.sin ξ ^ 2 := by
    rw [← sq_abs ξ, ← sq_abs (Real.sin ξ), ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg ξ) hγ 2
  have hc := Real.abs_sub_sin_le ξ
  have hcube : -ξ ≤ -Real.sin ξ + |ξ| ^ 3 / 6 := by linarith [neg_abs_le (ξ - Real.sin ξ)]
  have h3 : |ξ| ^ 3 ≤ 113 / 100 * ξ ^ 2 := by
    rw [← sq_abs ξ, pow_succ, mul_comm]
    exact mul_le_mul_of_nonneg_right hξ (sq_nonneg _)
  have hs : 287 / 100 ≤ 4 + ξ := by linarith [neg_abs_le ξ]
  have hid : 1 / (4 + ξ) = 1 / 4 - ξ / 16 + ξ ^ 2 / (16 * (4 + ξ)) := by
    field_simp; ring
  have hq : ξ ^ 2 / (16 * (4 + ξ)) ≤ ξ ^ 2 * (100 / (16 * 287)) := by
    rw [div_le_iff₀ (by positivity)]
    have : 0 ≤ ξ ^ 2 := sq_nonneg ξ
    nlinarith
  rw [hid]
  unfold c2
  nlinarith [sq_nonneg (Real.sin ξ)]

/-- Third step: from `sin ξ cosh ν cos λz = -X + Y cos ξ sinh ν`, bounds on `-sin ξ` and
`sin² ξ` in terms of `X`, `Y`, `cos λz`. -/
theorem sx_bounds {sx ch c X Y cx sh : ℝ} (h : sx * ch * c = -X + Y * cx * sh) (hc : 0 < c)
    (hch1 : 1 ≤ ch) (hch2 : ch ≤ 1 + 1 / 127) (hsh : |sh| ≤ 251 / 2000) (hcx : |cx| ≤ 1)
    (hX : X ^ 2 ≤ 81 / 100) (hY : Y ^ 2 ≤ 81 / 100) :
    -sx ≤ (X + 9 / 10 * (1 / 127 + 251 / 2000)) / c ∧
      sx ^ 2 ≤ ((1 + 251 / 2000) * X ^ 2 + 1413 / 10000 * Y ^ 2) / c ^ 2 := by
  have hXa : |X| ≤ 9 / 10 := abs_le_of_sq_le_sq (by norm_num; linarith) (by norm_num)
  have hYa : |Y| ≤ 9 / 10 := abs_le_of_sq_le_sq (by norm_num; linarith) (by norm_num)
  have hYcs : |Y * cx * sh| ≤ 9 / 10 * (251 / 2000) := by
    rw [abs_mul, abs_mul]
    have := mul_le_mul hYa hcx (abs_nonneg _) (by norm_num)
    have := mul_le_mul this hsh (abs_nonneg _) (by norm_num)
    linarith
  have hch0 : 0 < ch := by linarith
  constructor
  · rw [le_div_iff₀ hc]
    have hm : -sx * c * ch = X - Y * cx * sh := by linarith
    have hX1 : X * (1 - ch) ≤ 9 / 10 * (1 / 127) := by
      have : |X * (1 - ch)| ≤ 9 / 10 * (1 / 127) := by
        rw [abs_mul, abs_of_nonpos (by linarith : 1 - ch ≤ 0)]
        exact mul_le_mul hXa (by linarith) (by linarith) (by norm_num)
      linarith [le_abs_self (X * (1 - ch))]
    have hY1 := neg_abs_le (Y * cx * sh)
    have key : -sx * c * ch ≤ (X + 9 / 10 * (1 / 127 + 251 / 2000)) * ch := by
      rw [hm]; nlinarith
    exact le_of_mul_le_mul_right key hch0
  · rw [le_div_iff₀ (by positivity)]
    have hsq : (sx * c) ^ 2 * ch ^ 2 = (X - Y * cx * sh) ^ 2 := by
      rw [← mul_pow, show sx * c * ch = -(X - Y * cx * sh) by linarith [h], neg_sq]
    have h1 : (sx * c) ^ 2 ≤ (X - Y * cx * sh) ^ 2 := by
      rw [← hsq]
      have : 1 ≤ ch ^ 2 := by nlinarith
      nlinarith [sq_nonneg (sx * c)]
    have hY2 : |Y * cx * sh| ≤ 251 / 2000 * |Y| := by
      rw [abs_mul, abs_mul]
      have := mul_le_mul_of_nonneg_left hcx (abs_nonneg Y)
      have := mul_le_mul this hsh (abs_nonneg _) (by positivity)
      linarith
    have h2 : (X - Y * cx * sh) ^ 2 ≤ (|X| + 251 / 2000 * |Y|) ^ 2 := by
      rw [← sq_abs (X - Y * cx * sh)]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (by linarith)) 2
    have h3 : (|X| + 251 / 2000 * |Y|) ^ 2 ≤
        (1 + 251 / 2000) * X ^ 2 + 1413 / 10000 * Y ^ 2 := by
      nlinarith [sq_nonneg (|X| - |Y|), sq_abs X, sq_abs Y, sq_nonneg Y]
    nlinarith

/-- The polynomial `p(u)` whose average over a poloidal turn bounds `1/ι` on the outer surface
(found by an untrusted linear program; verified below). -/
@[expose] def pP (u : ℝ) : ℝ :=
  767 / 10000 + 643 / 10000 * u - 1081 / 10000 * u ^ 2 + 2153 / 10000 * u ^ 3

/-- The weight `Q(u) = (1 + η)(k² - u) + 0.1413 u` (`0.1413 ≥ η + η²`), `η = 0.1255`,
`k² = 0.81`. -/
@[expose] def Qw (u : ℝ) : ℝ :=
  (1 + 251 / 2000) * (81 / 100 - u) + 1413 / 10000 * u

/-- Coefficients (in `c = cos λz`, constant first) of
`c³ p(1 - c²) - A₀ c² - A₁ Q(1 - c²) - A₂ c` with `A₀ = 0.06355`, `A₁ = 0.0123`, `A₂ = 0.00171`. -/
@[expose] def Pcoeffs : List ℚ :=
  [1784607 / 2000000000, -171 / 100000, -3782783 / 50000000, 1241 / 5000, 0, -247 / 500, 0,
    2689 / 5000, 0, -2153 / 10000]

/-- Sixteen pieces of `[0.4358, 1]` (untrusted search). -/
@[expose] def Pgrid : List ℚ :=
  [7537 / 16000, 20253 / 40000, 43327 / 80000, 11537 / 20000, 48969 / 80000, 5179 / 8000,
    54611 / 80000, 7179 / 10000, 60253 / 80000, 31537 / 40000, 13179 / 16000, 17179 / 20000,
    71537 / 80000, 37179 / 40000, 77179 / 80000, 1]

/-- Kernel-checked certificate: the polynomial is nonnegative on `[0.4358, 1]`. -/
theorem Pcoeffs_check :
    Certificates.QPoly.checkOn Pcoeffs 0 (2179 / 5000) 1 Pgrid = true := by
  decide +kernel

/-- Fourth step (the polynomial inequality): for `c = cos λz > 0` with `c² = 1 - u`,
`0 ≤ u ≤ 0.81`: `A₀ + A₁ Q(u)/c² + A₂/c ≤ c p(u)`. -/
theorem poly_k2 {c u : ℝ} (hc : 0 < c) (hcu : c ^ 2 = 1 - u) (hu0 : 0 ≤ u)
    (hu : u ≤ 81 / 100) :
    6355 / 100000 + 123 / 10000 * Qw u / c ^ 2 + 171 / 100000 / c ≤ c * pP u := by
  have hc1 : c ≤ 1 := by nlinarith
  have hclo : 2179 / 5000 ≤ c := by nlinarith
  have hP := Certificates.QPoly.checkOn_sound Pcoeffs_check c
    ⟨by push_cast; linarith, by push_cast; linarith⟩
  have hev : Certificates.QPoly.eval Pcoeffs c = c ^ 3 * pP (1 - c ^ 2) -
      6355 / 100000 * c ^ 2 - 123 / 10000 * Qw (1 - c ^ 2) - 171 / 100000 * c := by
    simp only [Pcoeffs, Certificates.QPoly.eval_cons, Rat.cast_div, Rat.cast_ofNat,
        Certificates.QPoly.eval, Rat.cast_neg, Rat.cast_zero, mul_zero, add_zero, zero_add, pP, Qw]
    ring
  rw [hev] at hP
  have hu' : u = 1 - c ^ 2 := by linarith
  subst hu'
  have key : c ^ 2 * (c * pP (1 - c ^ 2) - (6355 / 100000 + 123 / 10000 * Qw (1 - c ^ 2) / c ^ 2 +
      171 / 100000 / c)) = c ^ 3 * pP (1 - c ^ 2) - 6355 / 100000 * c ^ 2 -
      123 / 10000 * Qw (1 - c ^ 2) - 171 / 100000 * c := by
    field_simp; ring
  have : 0 ≤ c ^ 2 * (c * pP (1 - c ^ 2) - (6355 / 100000 + 123 / 10000 * Qw (1 - c ^ 2) / c ^ 2 +
      171 / 100000 / c)) := by
    rw [key]; push_cast at hP; linarith
  have h2 : 0 < c ^ 2 := by positivity
  have := (mul_nonneg_iff_of_pos_left h2).mp this
  linarith

/-- **Pointwise bound on the outer surface** (in the atoms): combining the four steps,
`(σ a + ν b)/(2(σ² + ν²)) ≤ c_X X/c + c p(Y²)` with `c_X = 0.4537/32`. -/
theorem k2_pure {s a n b X Y c cx sx ch sh ξ : ℝ} (hs : s = 4 + ξ) (hξ : |ξ| ≤ 113 / 100)
    (hsx : sx = Real.sin ξ) (ha : a ^ 2 ≤ (4537 / 10000) ^ 2) (hn : n ^ 2 ≤ 1 / 64)
    (hb : b ^ 2 ≤ 81 / 100) (hrel : sx * ch * c = -X + Y * cx * sh) (hc : 0 < c)
    (hcY : c ^ 2 = 1 - Y ^ 2) (hch1 : 1 ≤ ch) (hch2 : ch ≤ 1 + 1 / 127)
    (hsh : |sh| ≤ 251 / 2000) (hcx : |cx| ≤ 1) (hXY : X ^ 2 + Y ^ 2 = 81 / 100) :
    (s * a + n * b) / (2 * (s ^ 2 + n ^ 2)) ≤ 4537 / 320000 * X / c + c * pP (Y ^ 2) := by
  have hs0 : 287 / 100 ≤ s := by rw [hs]; linarith [neg_abs_le ξ]
  have hspos : 0 < s := by linarith
  have T1 := tor_le_inv hspos (by norm_num) ha hn hb
  have T2 := inv_s_le hξ
  rw [← hs, ← hsx] at T2
  have hX2 : X ^ 2 ≤ 81 / 100 := by nlinarith [sq_nonneg Y]
  have hY2 : Y ^ 2 ≤ 81 / 100 := by nlinarith [sq_nonneg X]
  obtain ⟨T3a, T3b⟩ := sx_bounds hrel hc hch1 hch2 hsh hcx hX2 hY2
  have hQ : (1 + 251 / 2000) * X ^ 2 + 1413 / 10000 * Y ^ 2 = Qw (Y ^ 2) := by
    unfold Qw; rw [show X ^ 2 = 81 / 100 - Y ^ 2 by linarith]
  rw [hQ] at T3b
  have T4 := poly_k2 hc hcY (sq_nonneg Y) hY2
  have hss : 9 / (160 * s ^ 2) ≤ 9 / (160 * (287 / 100) ^ 2) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  have hc2 : c2 * (4537 / 10000) / 2 ≤ 123 / 10000 := by unfold c2; norm_num
  have hc2pos : 0 ≤ c2 := by unfold c2; positivity
  have hQpos : 0 ≤ Qw (Y ^ 2) := by unfold Qw; nlinarith
  have hR : 4537 / 10000 / (2 * s) = 4537 / 20000 * (1 / s) := by field_simp; norm_num
  have e1 : 4537 / 320000 * ((X + 9 / 10 * (1 / 127 + 251 / 2000)) / c) ≤
      4537 / 320000 * X / c + 171 / 100000 / c := by
    have : 4537 / 320000 * ((X + 9 / 10 * (1 / 127 + 251 / 2000)) / c) =
        4537 / 320000 * X / c + 4537 / 320000 * (9 / 10 * (1 / 127 + 251 / 2000)) / c := by
      ring
    rw [this]
    have h3 : 4537 / 320000 * (9 / 10 * (1 / 127 + 251 / 2000)) / c ≤ 171 / 100000 / c :=
      div_le_div_of_nonneg_right (by norm_num) hc.le
    linarith
  have e2 : c2 * (4537 / 20000) * (Qw (Y ^ 2) / c ^ 2) ≤ 123 / 10000 * Qw (Y ^ 2) / c ^ 2 := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  calc (s * a + n * b) / (2 * (s ^ 2 + n ^ 2))
      ≤ 4537 / 20000 * (1 / s) + 9 / (160 * s ^ 2) := by rw [← hR]; exact T1
    _ ≤ 4537 / 20000 * (1 / 4 - sx / 16 + c2 * sx ^ 2) + 9 / (160 * (287 / 100) ^ 2) := by
        gcongr
    _ = 4537 / 80000 + 4537 / 320000 * (-sx) + c2 * (4537 / 20000) * sx ^ 2 +
        9 / (160 * (287 / 100) ^ 2) := by ring
    _ ≤ 4537 / 80000 + 4537 / 320000 * ((X + 9 / 10 * (1 / 127 + 251 / 2000)) / c) +
        c2 * (4537 / 20000) * (Qw (Y ^ 2) / c ^ 2) + 9 / (160 * (287 / 100) ^ 2) := by
        gcongr
    _ ≤ 4537 / 320000 * X / c + (6355 / 100000 + 123 / 10000 * Qw (Y ^ 2) / c ^ 2 +
        171 / 100000 / c) := by
        linarith [e1, e2]
    _ ≤ 4537 / 320000 * X / c + c * pP (Y ^ 2) := by linarith

/-- **Pointwise bound on the inner surface** (in the atoms): for `σ ∈ [4 - 1/19, 4 + 1/19]`,
`a ≥ 199/200`, `|ν| ≤ 1/8`, `|b| ≤ 1/20`: `(σ a + ν b)/(2(σ² + ν²)) ≥ 3/25`. -/
theorem k1_pure {s a n b : ℝ} (hs1 : 4 - 1 / 19 ≤ s) (hs2 : s ≤ 4 + 1 / 19) (ha : 199 / 200 ≤ a)
    (hn : n ^ 2 ≤ 1 / 64) (hb : b ^ 2 ≤ 1 / 400) :
    3 / 25 ≤ (s * a + n * b) / (2 * (s ^ 2 + n ^ 2)) := by
  have hnb : -(1 / 160) ≤ n * b :=
    (abs_le_of_sq_le_sq' (show (n * b) ^ 2 ≤ (1 / 160) ^ 2 by
      rw [mul_pow]; nlinarith [sq_nonneg n, sq_nonneg b]) (by norm_num)).1
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ s - (4 - 1 / 19)) (by linarith : (0 : ℝ) ≤ 4
      + 1 / 19 - s)]

/-- Positivity of the toroidal rate on the outer surface (in the atoms). -/
theorem k2_pos_pure {s a n b : ℝ} (hs : 287 / 100 ≤ s) (ha : 88 / 1000 ≤ a)
    (hn : n ^ 2 ≤ 1 / 64) (hb : b ^ 2 ≤ 81 / 100) : 0 < (s * a + n * b) / (2 * (s ^ 2
        + n ^ 2)) := by
  have hnb : -(9 / 80) ≤ n * b :=
    (abs_le_of_sq_le_sq' (show (n * b) ^ 2 ≤ (9 / 80) ^ 2 by
      rw [mul_pow]; nlinarith [sq_nonneg n, sq_nonneg b]) (by norm_num)).1
  apply div_pos _ (by positivity)
  nlinarith

/-! ## Shear: the atoms on a flux surface -/

/-- `(Re u)² + X² + Y² = cosh² ν` (paper (3.17): `(∂X/∂σ)² = T² = cosh² ν - X² - Y²`). -/
theorem uR_sq_add (ε S lam : ℝ) (x : Space) :
    uR ε S lam x ^ 2 + Xf ε S lam x ^ 2 + Yf lam x ^ 2 = Real.cosh (nu ε x) ^ 2 := by
  have h1 := Real.cos_sq_add_sin_sq (sg ε x - S)
  have h2 := Real.cosh_sq_sub_sinh_sq (nu ε x)
  have h3 := Real.cos_sq_add_sin_sq (lam * x 2)
  unfold uR Xf Yf vR cz sz
  linear_combination (Real.cosh (nu ε x) ^ 2 * Real.cos (lam * x 2) ^ 2 +
    Real.sinh (nu ε x) ^ 2 * Real.sin (lam * x 2) ^ 2) * h1 +
    (Real.cos (lam * x 2) ^ 2 - 1) * h2 + (Real.sinh (nu ε x) ^ 2 + 1) * h3

/-- `(Im u)² + sin²(σ - S) = X² + Y²` (paper (3.14): `2ψ = sin² ξ + (…)²`). -/
theorem uI_sq_add (ε S lam : ℝ) (x : Space) :
    uI ε S lam x ^ 2 + Real.sin (sg ε x - S) ^ 2 = Xf ε S lam x ^ 2 + Yf lam x ^ 2 := by
  have h1 := Real.cos_sq_add_sin_sq (sg ε x - S)
  have h2 := Real.cosh_sq_sub_sinh_sq (nu ε x)
  have h3 := Real.cos_sq_add_sin_sq (lam * x 2)
  unfold uI Xf Yf vR cz sz
  linear_combination (Real.sin (lam * x 2) ^ 2 * (Real.cosh (nu ε x) ^ 2 -
    Real.sinh (nu ε x) ^ 2)) * h1 + (-(Real.cos (lam * x 2) ^ 2 * Real.sin (sg ε x - S) ^ 2) -
    Real.sin (sg ε x - S) ^ 2 * Real.sin (lam * x 2) ^ 2 + Real.sin (lam * x 2) ^ 2) * h2 +
    (-(Real.sin (sg ε x - S) ^ 2)) * h3

/-- `sin(σ - S) cosh ν cos λz = -X + Y cos(σ - S) sinh ν`. -/
theorem sx_rel (ε S lam : ℝ) (x : Space) :
    Real.sin (sg ε x - S) * Real.cosh (nu ε x) * cz lam x =
      -Xf ε S lam x + Yf lam x * Real.cos (sg ε x - S) * Real.sinh (nu ε x) := by
  unfold Xf Yf vR; ring

/-- `cos² λz = 1 - Y²`. -/
theorem cz_sq (lam : ℝ) (x : Space) : cz lam x ^ 2 = 1 - Yf lam x ^ 2 := by
  have := Real.cos_sq_add_sin_sq (lam * x 2)
  unfold cz Yf sz; linarith

/-- `ν² ≤ ε²/4` on `𝒰` for `ε ≥ 0` (paper (3.10): `ν = (ε/2) sin 2ζ`). -/
theorem nu_sq_le {ε : ℝ} {x : Space} (hx : x ∈ U ε) : nu ε x ^ 2 ≤ ε ^ 2 / 4 := by
  have hs := sg_pos hx
  have h2 := sg_sq hx
  have hm := Mo_sq ε x
  have hZ := abs_Zr_le ε x
  have hM0 : 0 ≤ Mo ε x := Real.sqrt_nonneg _
  -- `8 x² y² ≤ |Z| + Re Z`
  have key : 8 * (x 0 * x 1) ^ 2 ≤ Mo ε x + Zr ε x := by
    have hid : (Mo ε x + Zr ε x - 8 * (x 0 * x 1) ^ 2) * (Mo ε x - Zr ε x + 8 * (x 0 * x 1) ^ 2) =
        4 * (x 0 * x 1) ^ 2 * (ε + 2 * (x 0 ^ 2 - x 1 ^ 2)) ^ 2 := by
      rw [show (Mo ε x + Zr ε x - 8 * (x 0 * x 1) ^ 2) * (Mo ε x - Zr ε x + 8 * (x 0 * x 1) ^ 2) =
        Mo ε x ^ 2 - (Zr ε x - 8 * (x 0 * x 1) ^ 2) ^ 2 by ring, hm]
      unfold Zr Zi r2; ring
    have hpos : 0 ≤ Mo ε x - Zr ε x + 8 * (x 0 * x 1) ^ 2 := by
      linarith [le_abs_self (Zr ε x), sq_nonneg (x 0 * x 1)]
    rcases hpos.lt_or_eq with hlt | heq
    · have : 0 ≤ (Mo ε x + Zr ε x - 8 * (x 0 * x 1) ^ 2) *
          (Mo ε x - Zr ε x + 8 * (x 0 * x 1) ^ 2) := by rw [hid]; positivity
      have := (mul_nonneg_iff_of_pos_right hlt).mp this
      linarith
    · have hxy : (x 0 * x 1) ^ 2 = 0 := by
        have : Mo ε x = Zr ε x - 8 * (x 0 * x 1) ^ 2 := by linarith
        nlinarith [le_abs_self (Zr ε x), neg_abs_le (Zr ε x), sq_nonneg (x 0 * x 1)]
      rw [hxy]; nlinarith
  have hn : nu ε x ^ 2 * sg ε x ^ 2 = ε ^ 2 * (x 0 * x 1) ^ 2 := by
    rw [← mul_pow, mul_comm, sg_mul_nu hx]; ring
  have : nu ε x ^ 2 * sg ε x ^ 2 ≤ ε ^ 2 / 4 * sg ε x ^ 2 := by
    rw [hn, h2]; nlinarith [sq_nonneg ε]
  exact le_of_mul_le_mul_right this (by positivity)

/-- Lower bound for `Re u = cos λz cos ξ cosh ν - sin λz sin ξ sinh ν` (in the atoms). -/
theorem uR_lower {cz cx ch sz sx sh m t : ℝ} (hcz : 0 < cz) (hcx : 0 < cx) (hm : 0 ≤ m)
    (hcz2 : m ^ 2 ≤ cz ^ 2) (hcx2 : m ^ 2 ≤ cx ^ 2) (hch : 1 ≤ ch) (hszx : sz ^ 2 * sx ^ 2 ≤ t ^ 2)
    (ht : 0 ≤ t) (hsh : |sh| ≤ 251 / 2000) :
    m ^ 2 - t * (251 / 2000) ≤ cz * cx * ch - sz * sx * sh := by
  have h1 : m ≤ cz := by nlinarith
  have h2 : m ≤ cx := by nlinarith
  have h3 : m ^ 2 ≤ cz * cx := by nlinarith [mul_le_mul h1 h2 hm hcz.le]
  have h4 : cz * cx ≤ cz * cx * ch := by nlinarith [mul_pos hcz hcx]
  have h5 : |sz * sx| ≤ t := abs_le_of_sq_le_sq (by rw [mul_pow]; exact hszx) ht
  have h6 : |sz * sx * sh| ≤ t * (251 / 2000) := by
    rw [abs_mul]; exact mul_le_mul h5 hsh (abs_nonneg _) ht
  linarith [le_abs_self (sz * sx * sh)]

/-- The good region `R`: smooth (`𝒰`), with `|σ - S| < π/2` and `|λz| < π/2` (the branch of the
paper's coordinates (3.9)–(3.15) containing the magnetic axis). -/
@[expose] def R (ε S lam : ℝ) : Set Space :=
  {x | x ∈ U ε ∧ |sg ε x - S| < Real.pi / 2 ∧ |lam * x 2| < Real.pi / 2}

/-- Common facts at a point of `R` for `ε = 1/4`, `S = 4`. -/
theorem R_facts {lam : ℝ} {x : Space} (hx : x ∈ R (1 / 4) 4 lam) :
    0 < cz lam x ∧ 0 < Real.cos (sg (1 / 4) x - 4) ∧ nu (1 / 4) x ^ 2 ≤ 1 / 64 ∧
      1 ≤ Real.cosh (nu (1 / 4) x) ∧ Real.cosh (nu (1 / 4) x) ≤ 1 + 1 / 127 ∧
      |Real.sinh (nu (1 / 4) x)| ≤ 251 / 2000 := by
  obtain ⟨hU, hξ, hz⟩ := hx
  have hn : nu (1 / 4) x ^ 2 ≤ 1 / 64 := by have := nu_sq_le hU; norm_num at this ⊢; linarith
  have hna : |nu (1 / 4) x| ≤ 1 / 8 := abs_le_of_sq_le_sq (by norm_num; linarith) (by norm_num)
  refine ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le (lam * x 2)],
      by linarith [le_abs_self (lam * x 2)]⟩,
    Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le (sg (1 / 4) x - 4)],
      by linarith [le_abs_self (sg (1 / 4) x - 4)]⟩, hn, Real.one_le_cosh _, ?_, ?_⟩
  · refine (Real.cosh_le_cosh.mpr ?_).trans cosh_eighth_le
    rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)]
  · rw [Real.abs_sinh]
    exact (Real.sinh_le_sinh.mpr hna).trans sinh_eighth_le

/-- **The outer surface `ψ = 81/200` (`k = 9/10`)**, for `ε = 1/4`, `S = 4`, any `λ ≠ 0`:
`B · ∇φ ≤ c_X X / cos λz + cos λz · p(Y²)` and `B · ∇φ > 0`. -/
theorem surface_k2 {lam : ℝ} {x : Space} (hx : x ∈ R (1 / 4) 4 lam)
    (hψ : psi (1 / 4) 4 lam x = 81 / 200) :
    torRate (1 / 4) 4 lam x ≤
      4537 / 320000 * Xf (1 / 4) 4 lam x / cz lam x + cz lam x * pP (Yf lam x ^ 2) ∧
    0 < torRate (1 / 4) 4 lam x := by
  obtain ⟨hc, hcx, hn, hch1, hch2, hsh⟩ := R_facts hx
  obtain ⟨hU, hξ0, -⟩ := hx
  have hXY : Xf (1 / 4) 4 lam x ^ 2 + Yf lam x ^ 2 = 81 / 100 := by
    have := psi_eq_XY (1 / 4) 4 lam x; linarith
  have huI := uI_sq_add (1 / 4) 4 lam x
  have huR := uR_sq_add (1 / 4) 4 lam x
  have hsx2 : Real.sin (sg (1 / 4) x
      - 4) ^ 2 ≤ 81 / 100 := by nlinarith [sq_nonneg (uI (1 / 4) 4 lam x)]
  have h113 := sin_113_ge
  have hξ : |sg (1 / 4) x - 4| ≤ 113 / 100 :=
    abs_le_of_sin_sq_le hξ0 (by norm_num) (by nlinarith)
  have ha : uR (1 / 4) 4 lam x ^ 2 ≤ (4537 / 10000) ^ 2 := by nlinarith
  have hb : uI (1 / 4) 4 lam x ^ 2 ≤ 81 / 100
      := by nlinarith [sq_nonneg (Real.sin (sg (1 / 4) x - 4))]
  have hcY := cz_sq lam x
  rw [torRate_eq hU]
  unfold Mq
  refine ⟨k2_pure (ξ := sg (1 / 4) x - 4) (by ring) hξ rfl ha hn hb (sx_rel (1 / 4) 4 lam x) hc hcY
    hch1 hch2 hsh (Real.abs_cos_le_one _) hXY, ?_⟩
  have hs0 : 287 / 100 ≤ sg (1 / 4) x := by linarith [neg_abs_le (sg (1 / 4) x - 4)]
  have hY2 : Yf lam x ^ 2 ≤ 81 / 100 := by nlinarith [sq_nonneg (Xf (1 / 4) 4 lam x)]
  have hlow := uR_lower (m := √(19 / 100)) (t := 81 / 100) (sz := sz lam x)
    (sx := Real.sin (sg (1 / 4) x - 4)) hc hcx (Real.sqrt_nonneg _)
    (by rw [Real.sq_sqrt (by norm_num)]; linarith) (by
      rw [Real.sq_sqrt (by norm_num)]; nlinarith [Real.cos_sq_add_sin_sq (sg (1 / 4) x - 4)])
    hch1 (by
      have h1 : sz lam x ^ 2 ≤ 81 / 100 := by unfold Yf at hY2; nlinarith
      have := mul_le_mul h1 hsx2 (sq_nonneg _) (by norm_num)
      linarith)
    (by norm_num) hsh
  rw [Real.sq_sqrt (by norm_num)] at hlow
  exact k2_pos_pure hs0 (by unfold uR; linarith) hn hb

/-- **The inner surface `ψ = 1/800` (`k = 1/20`)**, for `ε = 1/4`, `S = 4`, any `λ`:
`B · ∇φ ≥ 3/25`. -/
theorem surface_k1 {lam : ℝ} {x : Space} (hx : x ∈ R (1 / 4) 4 lam)
    (hψ : psi (1 / 4) 4 lam x = 1 / 800) : 3 / 25 ≤ torRate (1 / 4) 4 lam x := by
  obtain ⟨hc, hcx, hn, hch1, -, hsh⟩ := R_facts hx
  obtain ⟨hU, hξ0, -⟩ := hx
  have hXY : Xf (1 / 4) 4 lam x ^ 2 + Yf lam x ^ 2 = 1 / 400 := by
    have := psi_eq_XY (1 / 4) 4 lam x; linarith
  have huI := uI_sq_add (1 / 4) 4 lam x
  have hsx2 : Real.sin (sg (1 / 4) x - 4) ^ 2 ≤ 1 / 400 := by
    nlinarith [sq_nonneg (uI (1 / 4) 4 lam x)]
  have h19 := sin_19_ge
  have hξ : |sg (1 / 4) x - 4| ≤ 1 / 19 :=
    abs_le_of_sin_sq_le hξ0 (by norm_num) (by nlinarith)
  have hb : uI (1 / 4) 4 lam x ^ 2 ≤ 1 / 400 := by
    nlinarith [sq_nonneg (Real.sin (sg (1 / 4) x - 4))]
  have hcY := cz_sq lam x
  have hY2 : Yf lam x ^ 2 ≤ 1 / 400 := by nlinarith [sq_nonneg (Xf (1 / 4) 4 lam x)]
  have hlow := uR_lower (m := √(399 / 400)) (t := 1 / 400) (sz := sz lam x)
    (sx := Real.sin (sg (1 / 4) x - 4)) hc hcx (Real.sqrt_nonneg _)
    (by rw [Real.sq_sqrt (by norm_num)]; linarith) (by
      rw [Real.sq_sqrt (by norm_num)]; nlinarith [Real.cos_sq_add_sin_sq (sg (1 / 4) x - 4)])
    hch1 (by
      have h1 : sz lam x ^ 2 ≤ 1 / 400 := by unfold Yf at hY2; nlinarith
      have := mul_le_mul h1 hsx2 (sq_nonneg _) (by norm_num)
      linarith)
    (by norm_num) hsh
  rw [Real.sq_sqrt (by norm_num)] at hlow
  rw [torRate_eq hU]
  unfold Mq
  exact k1_pure (by linarith [neg_abs_le (sg (1 / 4) x - 4)])
    (by linarith [le_abs_self (sg (1 / 4) x - 4)]) (by unfold uR; linarith) hn hb

/-! ## Shear: angle rates along field lines -/

/-- A field line on a flux surface, with continuous angle lifts. `θ` is the poloidal angle of
the paper's (3.19) (`X = -k cos θ`, `Y = k sin θ`) and `φ` is the geometric (polar) toroidal
angle (`x = r cos φ`, `y = r sin φ`). -/
structure LiftedLine (ε S lam k : ℝ) (γ : ℝ → Space) (θ φ : ℝ → ℝ) : Prop where
  line : IsForwardFieldLine (field ε S lam) γ
  inR : ∀ t, 0 ≤ t → γ t ∈ R ε S lam
  surface : psi ε S lam (γ 0) = k ^ 2 / 2
  pol : ∀ t, 0 ≤ t → Xf ε S lam (γ t) = -k * Real.cos (θ t) ∧ Yf lam (γ t) = k * Real.sin (θ t)
  tor : ∀ t, 0 ≤ t → γ t 0 = √(r2 (γ t)) * Real.cos (φ t) ∧
    γ t 1 = √(r2 (γ t)) * Real.sin (φ t)
  pol_diff : ∀ t, 0 ≤ t → DifferentiableAt ℝ θ t
  tor_diff : ∀ t, 0 ≤ t → DifferentiableAt ℝ φ t

namespace LiftedLine
variable {ε S lam k : ℝ} {γ : ℝ → Space} {θ φ : ℝ → ℝ}

/-- `ψ` is constant along the line. -/
theorem psi_const (L : LiftedLine ε S lam k γ θ φ) (hl : lam ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    psi ε S lam (γ t) = k ^ 2 / 2 := by
  rw [← L.surface]
  exact firstIntegral_conserved (psi_firstIntegral hl) (T := t) (fun s hs => L.line s hs.1)
    (fun s hs => (L.inR s hs.1).1) ⟨ht, le_rfl⟩

/-- `X² + Y² = k²` along the line. -/
theorem XY_sq (L : LiftedLine ε S lam k γ θ φ) (hl : lam ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    Xf ε S lam (γ t) ^ 2 + Yf lam (γ t) ^ 2 = k ^ 2 := by
  have := L.psi_const hl ht
  rw [psi_eq_XY] at this
  linarith

/-- Poloidal rate: `θ' = cos λz` (paper (3.21)). -/
theorem pol_rate (L : LiftedLine ε S lam k γ θ φ) (hl : lam ≠ 0) (hk : k ≠ 0) {t : ℝ}
    (ht : 0 < t) : HasDerivAt θ (cz lam (γ t)) t := by
  have hev : ∀ᶠ s in nhds t, 0 ≤ s :=
    Filter.mem_of_superset (Ioi_mem_nhds ht) (fun s hs => le_of_lt hs)
  exact poloidal_lift_deriv hk (X_along hl (L.line t ht.le) (L.inR t ht.le).1)
    (Y_along hl (L.line t ht.le)) (L.pol_diff t ht.le)
    (hev.mono fun s hs => (L.pol s hs).1) (hev.mono fun s hs => (L.pol s hs).2)

/-- Toroidal rate: `φ' = B · ∇φ`. -/
theorem tor_rate (L : LiftedLine ε S lam k γ θ φ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt φ (torRate ε S lam (γ t)) t := by
  have hev : ∀ᶠ s in nhds t, 0 ≤ s :=
    Filter.mem_of_superset (Ioi_mem_nhds ht) (fun s hs => le_of_lt hs)
  have hr := r2_pos (L.inR t ht.le).1
  have h := toroidal_lift_deriv (x := fun s => γ s 0) (y := fun s => γ s 1) hr
    (coord_hasDerivAt (L.line t ht.le) 0) (coord_hasDerivAt (L.line t ht.le) 1)
    (L.tor_diff t ht.le) (hev.mono fun s hs => (L.tor s hs).1)
    (hev.mono fun s hs => (L.tor s hs).2)
  exact h

end LiftedLine

/-! ## Shear: winding inequalities -/

/-- A function with nonnegative derivative on `(0, ∞)`, continuous on `[0, ∞)`, is
nondecreasing there. -/
theorem le_of_deriv_nonneg {f : ℝ → ℝ} (hc : ∀ t, 0 ≤ t → ContinuousAt f t)
    (hd : ∀ t, 0 < t → ∃ f', HasDerivAt f f' t ∧ 0 ≤ f') {t : ℝ} (ht : 0 ≤ t) :
    f 0 ≤ f t := by
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun x hx => (hc x hx).continuousWithinAt
    · rw [interior_Ici]
      intro x hx
      obtain ⟨f', h, -⟩ := hd x hx
      exact h.differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro x hx
      obtain ⟨f', h, h0⟩ := hd x hx
      rw [h.deriv]; exact h0
  exact hmono Set.self_mem_Ici ht ht

/-- Strict version: positive derivative on `(0, ∞)`. -/
theorem lt_of_deriv_pos {f : ℝ → ℝ} (hc : ∀ t, 0 ≤ t → ContinuousAt f t)
    (hd : ∀ t, 0 < t → ∃ f', HasDerivAt f f' t ∧ 0 < f') {t : ℝ} (ht : 0 < t) :
    f 0 < f t := by
  have hmono : StrictMonoOn f (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact fun x hx => (hc x hx).continuousWithinAt
    · rw [interior_Ici]
      intro x hx
      obtain ⟨f', h, h0⟩ := hd x hx
      rw [h.deriv]; exact h0
  exact hmono Set.self_mem_Ici ht.le ht

/-- **Inner surface `k = 1/20`.** Along every lifted field line on `ψ = 1/800`:
`φ(t) - φ(0) ≥ (3/25)(θ(t) - θ(0))` and `θ(t) - θ(0) ≥ 0.99 t`. -/
theorem inner_winding {lam : ℝ} (hl : lam ≠ 0) {γ : ℝ → Space} {θ φ : ℝ → ℝ}
    (L : LiftedLine (1 / 4) 4 lam (1 / 20) γ θ φ) {t : ℝ} (ht : 0 ≤ t) :
    3 / 25 * (θ t - θ 0) ≤ φ t - φ 0 ∧ 99 / 100 * t ≤ θ t - θ 0 := by
  have hk : (1 / 20 : ℝ) ≠ 0 := by norm_num
  have hψ (s : ℝ) (hs : 0 ≤ s) : psi (1 / 4) 4 lam (γ s) = 1 / 800 := by
    rw [L.psi_const hl hs]; norm_num
  constructor
  · have := le_of_deriv_nonneg (f := fun s => φ s - 3 / 25 * θ s)
      (fun s hs => ((L.tor_diff s hs).continuousAt).sub
        (((L.pol_diff s hs).continuousAt).const_mul _))
      (fun s hs => ⟨_, (L.tor_rate hs).sub ((L.pol_rate hl hk hs).const_mul (3 / 25)), by
        have h1 := surface_k1 (L.inR s hs.le) (hψ s hs.le)
        have h2 := Real.cos_le_one (lam * γ s 2)
        unfold cz
        nlinarith⟩) ht
    linarith
  · have := le_of_deriv_nonneg (f := fun s => θ s - 99 / 100 * s)
      (fun s hs => ((L.pol_diff s hs).continuousAt).sub (continuousAt_id.const_mul _))
      (fun s hs => ⟨_, (L.pol_rate hl hk hs).sub ((hasDerivAt_id s).const_mul (99 / 100)), by
        have hc := (R_facts (L.inR s hs.le)).1
        have hXY := L.XY_sq hl hs.le
        have hcY := cz_sq lam (γ s)
        have : (99 / 100 : ℝ) ≤ cz lam (γ s) := by nlinarith [sq_nonneg (Xf (1 / 4) 4 lam (γ s))]
        simp only [mul_one]
        linarith⟩) ht
    simp only [mul_zero, sub_zero] at this
    linarith

/-- Coefficients of the Lyapunov polynomial (`B · ∇ Pl = cos λz (p(Y²) - ⟨p⟩)` on `X² + Y² = k²`).
-/
@[expose] def q1c : ℝ := 13906513 / 320000000

/-- Coefficient of `X Y³`. -/
@[expose] def q3c : ℝ := 14891 / 1600000

/-- Coefficient of `X Y⁵`. -/
@[expose] def q5c : ℝ := 2153 / 60000

/-- The average `⟨p⟩ = p₀ + q₁ k²` of `p(k² sin² θ)` over a poloidal turn (`≈ 0.11190`). -/
@[expose] def pAvg : ℝ := 3580827553 / 32000000000

/-- The Lyapunov polynomial `Pl(X, Y) = X (q₁ Y + q₃ Y³ + q₅ Y⁵)`. -/
@[expose] def Pl (X Y : ℝ) : ℝ := X * (q1c * Y + q3c * Y ^ 3 + q5c * Y ^ 5)

/-- `artanh Y = (log(1 + Y) - log(1 - Y))/2`. -/
@[expose] def Ath (Y : ℝ) : ℝ := (Real.log (1 + Y) - Real.log (1 - Y)) / 2

/-- The derivative identity for `Pl` on the circle `X² + Y² = 81/100`. -/
theorem Pl_identity {X Y c : ℝ} (h : X ^ 2 + Y ^ 2 = 81 / 100) :
    Y * c * (q1c * Y + q3c * Y ^ 3 + q5c * Y ^ 5) +
      X * (q1c + q3c * (3 * Y ^ 2) + q5c * (5 * Y ^ 4)) * (-X * c) = c * (pP (Y ^ 2) - pAvg) := by
  unfold q1c q3c q5c pP pAvg
  linear_combination (-c * (13906513 / 320000000 + 14891 / 1600000 * (3 * Y ^ 2) +
    2153 / 60000 * (5 * Y ^ 4))) * h

/-- **Outer surface `k = 9/10`.** Along every lifted field line on `ψ = 81/200`:
`φ(t) - φ(0) ≤ ⟨p⟩ (θ(t) - θ(0)) + D` for a constant `D`, `φ(t) > φ(0)` for `t > 0`, and
`θ(t) - θ(0) ≥ 0.43 t`. -/
theorem outer_winding {lam : ℝ} (hl : lam ≠ 0) {γ : ℝ → Space} {θ φ : ℝ → ℝ}
    (L : LiftedLine (1 / 4) 4 lam (9 / 10) γ θ φ) :
    ∃ D : ℝ, ∀ t, 0 ≤ t → φ t - φ 0 ≤ pAvg * (θ t - θ 0) + D ∧
      43 / 100 * t ≤ θ t - θ 0 ∧ (0 < t → 0 < φ t - φ 0) := by
  have hk : (9 / 10 : ℝ) ≠ 0 := by norm_num
  set X : ℝ → ℝ := fun s => Xf (1 / 4) 4 lam (γ s) with hXdef
  set Y : ℝ → ℝ := fun s => Yf lam (γ s) with hYdef
  have hXY (s : ℝ) (hs : 0 ≤ s) : X s ^ 2 + Y s ^ 2 = 81 / 100 := by
    have := L.XY_sq hl hs; norm_num at this ⊢; exact this
  have hYb (s : ℝ) (hs : 0 ≤ s) : |Y s| ≤ 9 / 10 :=
    abs_le_of_sq_le_sq (by nlinarith [hXY s hs, sq_nonneg (X s)]) (by norm_num)
  have hXb (s : ℝ) (hs : 0 ≤ s) : |X s| ≤ 9 / 10 :=
    abs_le_of_sq_le_sq (by nlinarith [hXY s hs, sq_nonneg (Y s)]) (by norm_num)
  have hdX (s : ℝ) (hs : 0 ≤ s) : HasDerivAt X (Y s * cz lam (γ s)) s :=
    X_along hl (L.line s hs) (L.inR s hs).1
  have hdY (s : ℝ) (hs : 0 ≤ s) : HasDerivAt Y (-(X s) * cz lam (γ s)) s :=
    Y_along hl (L.line s hs)
  have hψ (s : ℝ) (hs : 0 ≤ s) : psi (1 / 4) 4 lam (γ s) = 81 / 200 := by
    rw [L.psi_const hl hs]; norm_num
  -- the Lyapunov function
  set F : ℝ → ℝ := fun s => pAvg * θ s + Pl (X s) (Y s) - 4537 / 320000 * Ath (Y s) - φ s
    with hFdef
  have hY1 (s : ℝ) (hs : 0 ≤ s) : 0 < 1 + Y s := by linarith [neg_abs_le (Y s), hYb s hs]
  have hY2 (s : ℝ) (hs : 0 ≤ s) : 0 < 1 - Y s := by linarith [le_abs_self (Y s), hYb s hs]
  have hdA (s : ℝ) (hs : 0 ≤ s) : HasDerivAt (fun s => Ath (Y s))
      ((-(X s) * cz lam (γ s) / (1 + Y s) - (-(-(X s) * cz lam (γ s))) / (1 - Y s)) / 2) s := by
    have := ((((hdY s hs).const_add 1).log (hY1 s hs).ne').sub
      (((hdY s hs).const_sub 1).log (hY2 s hs).ne')).div_const 2
    exact this
  have hdPl (s : ℝ) (hs : 0 ≤ s) : HasDerivAt (fun s => Pl (X s) (Y s))
      (cz lam (γ s) * (pP (Y s ^ 2) - pAvg)) s := by
    have h := (hdX s hs).mul ((((hdY s hs).const_mul q1c).add (((hdY s hs).pow 3).const_mul
        q3c)).add
      (((hdY s hs).pow 5).const_mul q5c))
    refine h.congr_deriv ?_
    rw [← Pl_identity (c := cz lam (γ s)) (hXY s hs)]
    simp only [Nat.cast_ofNat, Pi.add_apply, Pi.pow_apply]
    ring
  have hcz (s : ℝ) (hs : 0 ≤ s) : 0 < cz lam (γ s) := (R_facts (L.inR s hs)).1
  have hcY (s : ℝ) : cz lam (γ s) ^ 2 = 1 - Y s ^ 2 := cz_sq lam (γ s)
  have hFmono : ∀ t, 0 ≤ t → F 0 ≤ F t := fun t ht => le_of_deriv_nonneg (f := F)
    (fun s hs => (((((L.pol_diff s hs).continuousAt).const_mul pAvg).add
      (hdPl s hs).continuousAt).sub ((hdA s hs).continuousAt.const_mul _)).sub
      (L.tor_diff s hs).continuousAt)
    (fun s hs => ⟨_, ((((L.pol_rate hl hk hs).const_mul pAvg).add (hdPl s hs.le)).sub
      ((hdA s hs.le).const_mul (4537 / 320000))).sub (L.tor_rate hs), by
        have hb := (surface_k2 (L.inR s hs.le) (hψ s hs.le)).1
        have hc := hcz s hs.le
        have e : (-(X s) * cz lam (γ s) / (1 + Y s) - -(-(X s) * cz lam (γ s)) / (1 - Y s)) / 2 =
            -(X s) * cz lam (γ s) / ((1 + Y s) * (1 - Y s)) := by
          have := (hY1 s hs.le).ne'
          have := (hY2 s hs.le).ne'
          field_simp
          ring
        have e2 : (1 + Y s) * (1 - Y s) = cz lam (γ s) ^ 2 := by rw [hcY]; ring
        rw [e, e2]
        have e3 : -(X s) * cz lam (γ s) / cz lam (γ s) ^ 2 = -(X s) / cz lam (γ s) := by
          field_simp
        rw [e3]
        have e4 : 4537 / 320000 * Xf (1 / 4) 4 lam (γ s) / cz lam (γ s) =
            4537 / 320000 * (X s / cz lam (γ s)) := by simp only [hXdef]; ring
        rw [e4] at hb
        have e5 : 4537 / 320000 * (-(X s) / cz lam (γ s)) = -(4537 / 320000
            * (X s / cz lam (γ s))) := by
          ring
        rw [e5]
        nlinarith⟩) ht
  -- bounds on the bounded part
  have hPl (s : ℝ) (hs : 0 ≤ s) : Pl (X s) (Y s) ≤
      9 / 10 * (q1c * (9 / 10) + q3c * (9 / 10) ^ 3 + q5c * (9 / 10) ^ 5) := by
    have hq1 : 0 ≤ q1c := by unfold q1c; norm_num
    have hq3 : 0 ≤ q3c := by unfold q3c; norm_num
    have hq5 : 0 ≤ q5c := by unfold q5c; norm_num
    have hY := hYb s hs
    have hinner : |q1c * Y s + q3c * Y s ^ 3 + q5c * Y s ^ 5| ≤
        q1c * (9 / 10) + q3c * (9 / 10) ^ 3 + q5c * (9 / 10) ^ 5 := by
      refine (abs_add_le _ _).trans ?_
      refine add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_
      · rw [abs_mul, abs_of_nonneg hq1]; exact mul_le_mul_of_nonneg_left hY hq1
      · rw [abs_mul, abs_of_nonneg hq3, abs_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hY 3) hq3
      · rw [abs_mul, abs_of_nonneg hq5, abs_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hY 5) hq5
    have : |Pl (X s) (Y s)| ≤ 9 / 10 * (q1c * (9 / 10) + q3c * (9 / 10) ^ 3
        + q5c * (9 / 10) ^ 5) := by
      unfold Pl
      rw [abs_mul]
      exact mul_le_mul (hXb s hs) hinner (abs_nonneg _) (by norm_num)
    exact (le_abs_self _).trans this
  have hA (s : ℝ) (hs : 0 ≤ s) :
      (Real.log (1 / 10) - Real.log (19 / 10)) / 2 ≤ Ath (Y s) := by
    unfold Ath
    have h1 : Real.log (1 / 10) ≤ Real.log (1 + Y s) :=
      Real.log_le_log (by norm_num) (by linarith [neg_abs_le (Y s), hYb s hs])
    have h2 : Real.log (1 - Y s) ≤ Real.log (19 / 10) :=
      Real.log_le_log (hY2 s hs) (by linarith [neg_abs_le (Y s), hYb s hs])
    linarith
  refine ⟨9 / 10 * (q1c * (9 / 10) + q3c * (9 / 10) ^ 3 + q5c * (9 / 10) ^ 5) -
    4537 / 320000 * ((Real.log (1 / 10) - Real.log (19 / 10)) / 2) -
    (Pl (X 0) (Y 0) - 4537 / 320000 * Ath (Y 0)), fun t ht => ⟨?_, ?_, ?_⟩⟩
  · have h1 := hFmono t ht
    have h2 := hPl t ht
    have h3 := hA t ht
    simp only [hFdef] at h1
    nlinarith
  · have := le_of_deriv_nonneg (f := fun s => θ s - 43 / 100 * s)
      (fun s hs => ((L.pol_diff s hs).continuousAt).sub (continuousAt_id.const_mul _))
      (fun s hs => ⟨_, (L.pol_rate hl hk hs).sub ((hasDerivAt_id s).const_mul (43 / 100)), by
        have hc := hcz s hs.le
        have := hcY s
        have : (43 / 100 : ℝ) ≤ cz lam (γ s) := by nlinarith [hXY s hs.le, sq_nonneg (X s)]
        simp only [mul_one]
        linarith⟩) ht
    simp only [mul_zero, sub_zero] at this
    linarith
  · intro htp
    have := lt_of_deriv_pos (f := φ) (fun s hs => (L.tor_diff s hs).continuousAt)
      (fun s hs => ⟨_, L.tor_rate hs, (surface_k2 (L.inR s hs.le) (hψ s hs.le)).2⟩) htp
    linarith

/-- The rotational transform of a lifted field line: the limit of poloidal over toroidal winding,
`ι = lim (θ(t) - θ(0))/(φ(t) - φ(0))` as the field-line parameter `t → ∞` (paper (3.24), which
uses the toroidal angle `ζ` of (3.9); `ζ - φ` stays bounded, so the two limits agree). -/
@[expose] def HasRotTransform (θ φ : ℝ → ℝ) (ι : ℝ) : Prop :=
  Filter.Tendsto (fun t => (θ t - θ 0) / (φ t - φ 0)) Filter.atTop (nhds ι)

/-- **Magnetic shear in Landreman's family 2** (`ε = 1/4`, `S = 4`, any `λ ≠ 0`).
Let `γ₁` be a field line on the flux surface `ψ = 1/800` (`k = 1/20`, close to the magnetic
axis) and `γ₂` one on `ψ = 81/200` (`k = 9/10`), both staying in the region `R`, with
continuous angle lifts. Then
1. on the inner surface the winding ratio `(θ₁(t) - θ₁(0))/(φ₁(t) - φ₁(0))` is at most `25/3`
   for every `t > 0`;
2. on the outer surface the winding ratio is at least `17/2` for all large `t`.
So the field lines on the two surfaces wind at different rates. (Numerically, `ι ≈ 7.98` and
`ι ≈ 11.86`; the proved bounds are `ι₁ ≤ 8.34 < 8.5 ≤ ι₂`, cf. `rotTransform_sheared`.) -/
theorem shear {lam : ℝ} (hl : lam ≠ 0) {γ₁ γ₂ : ℝ → Space} {θ₁ φ₁ θ₂ φ₂ : ℝ → ℝ}
    (L₁ : LiftedLine (1 / 4) 4 lam (1 / 20) γ₁ θ₁ φ₁)
    (L₂ : LiftedLine (1 / 4) 4 lam (9 / 10) γ₂ θ₂ φ₂) :
    (∀ t, 0 < t → (θ₁ t - θ₁ 0) / (φ₁ t - φ₁ 0) ≤ 25 / 3) ∧
    (∃ T, ∀ t, T ≤ t → 17 / 2 ≤ (θ₂ t - θ₂ 0) / (φ₂ t - φ₂ 0)) := by
  constructor
  · intro t ht
    obtain ⟨h1, h2⟩ := inner_winding hl L₁ ht.le
    have hpos : 0 < φ₁ t - φ₁ 0 := by nlinarith
    rw [div_le_iff₀ hpos]
    linarith
  · obtain ⟨D, hD⟩ := outer_winding hl L₂
    refine ⟨412 * |D| + 1, fun t ht => ?_⟩
    have ht0 : 0 < t := by linarith [abs_nonneg D]
    obtain ⟨h1, h2, h3⟩ := hD t ht0.le
    have hpos := h3 ht0
    rw [le_div_iff₀ hpos]
    have hA : pAvg = 3580827553 / 32000000000 := rfl
    have hDa := le_abs_self D
    nlinarith

/-- **Corollary: the rotational transform is sheared.** If the lines of `shear` have
rotational transforms `ι₁` and `ι₂`, then `ι₁ ≤ 25/3 < 17/2 ≤ ι₂`; in particular `ι₁ ≠ ι₂`. -/
theorem rotTransform_sheared {lam : ℝ} (hl : lam ≠ 0) {γ₁ γ₂ : ℝ → Space}
    {θ₁ φ₁ θ₂ φ₂ : ℝ → ℝ} (L₁ : LiftedLine (1 / 4) 4 lam (1 / 20) γ₁ θ₁ φ₁)
    (L₂ : LiftedLine (1 / 4) 4 lam (9 / 10) γ₂ θ₂ φ₂) {ι₁ ι₂ : ℝ}
    (h₁ : HasRotTransform θ₁ φ₁ ι₁) (h₂ : HasRotTransform θ₂ φ₂ ι₂) :
    ι₁ ≤ 25 / 3 ∧ 17 / 2 ≤ ι₂ ∧ ι₁ < ι₂ := by
  obtain ⟨hin, T, hout⟩ := shear hl L₁ L₂
  have a : ι₁ ≤ 25 / 3 := le_of_tendsto h₁ (Filter.eventually_atTop.mpr ⟨1, fun t ht =>
    hin t (by linarith)⟩)
  have b : 17 / 2 ≤ ι₂ := ge_of_tendsto h₂ (Filter.eventually_atTop.mpr ⟨T, hout⟩)
  exact ⟨a, b, by linarith⟩

/-! ## Pressure profile -/

/-- `ψ ≥ 0` everywhere (paper (3.8): `ψ = (X² + Y²)/2`). -/
theorem psi_nonneg (ε S lam : ℝ) (x : Space) : 0 ≤ psi ε S lam x := by
  unfold psi; positivity

/-- With `p_a = δ/λ²` the pressure is positive inside the surface `ψ = δ`. -/
theorem pressure_pos {μ₀ δ ε S lam : ℝ} (hμ : 0 < μ₀) (hl : lam ≠ 0) {x : Space}
    (hψ : psi ε S lam x < δ) : 0 < pressure μ₀ (δ / lam ^ 2) ε S lam x := by
  unfold pressure
  have : 0 < lam ^ 2 := by positivity
  apply div_pos _ hμ
  rw [← sub_div]
  exact div_pos (by linarith) this

/-- With `p_a = δ/λ²` the pressure vanishes on the boundary surface `ψ = δ`. -/
theorem pressure_boundary {μ₀ δ ε S lam : ℝ} {x : Space} (hψ : psi ε S lam x = δ) :
    pressure μ₀ (δ / lam ^ 2) ε S lam x = 0 := by
  unfold pressure; rw [hψ]; ring

/-- The pressure never exceeds its value `δ/(λ² μ₀)` on the magnetic axis (`ψ = 0`). -/
theorem pressure_le_axis {μ₀ δ ε S lam : ℝ} (hμ : 0 < μ₀) (x : Space) :
    pressure μ₀ (δ / lam ^ 2) ε S lam x ≤ δ / lam ^ 2 / μ₀ := by
  unfold pressure
  apply div_le_div_of_nonneg_right _ hμ.le
  have := psi_nonneg ε S lam x
  have : 0 ≤ psi ε S lam x / lam ^ 2 := by positivity
  linarith

/-! ## The planar elliptic magnetic axis (paper (3.9), (3.20)) -/

/-- `h(S) = √(4S² + ε²)` (paper (3.9)). -/
@[expose] def hC (ε S : ℝ) : ℝ := √(4 * S ^ 2 + ε ^ 2)

/-- Semi-axis `a_c(S) = √((h - ε)/2)` (paper (3.9)). -/
@[expose] def aC (ε S : ℝ) : ℝ := √((hC ε S - ε) / 2)

/-- Semi-axis `b_c(S) = √((h + ε)/2)` (paper (3.9)). -/
@[expose] def bC (ε S : ℝ) : ℝ := √((hC ε S + ε) / 2)

section Axis
variable {ε S : ℝ}

/-- `h > |ε|` for `S ≠ 0`. -/
theorem hC_gt (hS : 0 < S) : |ε| < hC ε S := by
  unfold hC
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)

/-- `a_c² = (h - ε)/2`. -/
theorem aC_sq (hS : 0 < S) : aC ε S ^ 2 = (hC ε S - ε) / 2 :=
  Real.sq_sqrt (by linarith [hC_gt (ε := ε) hS, le_abs_self ε])

/-- `b_c² = (h + ε)/2`. -/
theorem bC_sq (hS : 0 < S) : bC ε S ^ 2 = (hC ε S + ε) / 2 :=
  Real.sq_sqrt (by linarith [hC_gt (ε := ε) hS, neg_abs_le ε])

/-- `a_c > 0`. -/
theorem aC_pos (hS : 0 < S) : 0 < aC ε S :=
  Real.sqrt_pos.mpr (by linarith [hC_gt (ε := ε) hS, le_abs_self ε])

/-- `b_c > 0`. -/
theorem bC_pos (hS : 0 < S) : 0 < bC ε S :=
  Real.sqrt_pos.mpr (by linarith [hC_gt (ε := ε) hS, neg_abs_le ε])

/-- `b_c² - a_c² = ε` (confocal ellipses, foci `(0, ±√ε)`). -/
theorem bC_sq_sub (hS : 0 < S) : bC ε S ^ 2 - aC ε S ^ 2 = ε := by
  rw [aC_sq hS, bC_sq hS]; ring

/-- `a_c b_c = S`. -/
theorem aC_mul_bC (hS : 0 < S) : aC ε S * bC ε S = S := by
  have h2 : (aC ε S * bC ε S) ^ 2 = S ^ 2 := by
    rw [mul_pow, aC_sq hS, bC_sq hS]
    have : hC ε S ^ 2 = 4 * S ^ 2 + ε ^ 2 := Real.sq_sqrt (by positivity)
    nlinarith
  have := mul_pos (aC_pos (ε := ε) hS) (bC_pos (ε := ε) hS)
  nlinarith [sq_nonneg (aC ε S * bC ε S - S), sq_nonneg (aC ε S * bC ε S + S)]

end Axis

/-- The magnetic axis (paper (3.20)): the planar ellipse
`γ(ζ) = (a_c(S) cos ζ, b_c(S) sin ζ, 0)`. -/
@[expose] def axis (ε S ζ : ℝ) : Space :=
  toLp 2 ![aC ε S * Real.cos ζ, bC ε S * Real.sin ζ, 0]

/-- Its tangent vector. -/
@[expose] def axisVel (ε S ζ : ℝ) : Space :=
  toLp 2 ![-(aC ε S * Real.sin ζ), bC ε S * Real.cos ζ, 0]

/-- `G = |K|² = b_c² cos² ζ + a_c² sin² ζ` on the axis (paper (3.16)). -/
@[expose] def Gax (ε S ζ : ℝ) : ℝ := bC ε S ^ 2 * Real.cos ζ ^ 2 + aC ε S ^ 2 * Real.sin ζ ^ 2

section AxisField
variable {ε S : ℝ}

/-- `Re Z = S² - ε² cos² ζ sin² ζ` on the axis. -/
theorem Zr_axis (hS : 0 < S) (ζ : ℝ) :
    Zr ε (axis ε S ζ) = S ^ 2 - ε ^ 2 * Real.cos ζ ^ 2 * Real.sin ζ ^ 2 := by
  have h1 := bC_sq_sub (ε := ε) hS
  have h2 := aC_mul_bC (ε := ε) hS
  have h3 := Real.cos_sq_add_sin_sq ζ
  simp only [Zr, r2, axis, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  set a := aC ε S
  set b := bC ε S
  set c := Real.cos ζ
  set s := Real.sin ζ
  linear_combination (-(a ^ 2 * c ^ 4) + b ^ 2 * s ^ 4 + ε * c ^ 4 - ε * c ^ 2) * h1 +
    ((c ^ 2 + s ^ 2) ^ 2 * (S + a * b)) * h2 +
    (S ^ 2 * c ^ 2 + S ^ 2 * s ^ 2 + S ^ 2 - ε * b ^ 2 * c ^ 2 + ε * b ^ 2 * s ^ 2
        + c ^ 2 * ε ^ 2) * h3

/-- `Im Z = 2 ε S cos ζ sin ζ` on the axis. -/
theorem Zi_axis (hS : 0 < S) (ζ : ℝ) :
    Zi ε (axis ε S ζ) = 2 * ε * S * Real.cos ζ * Real.sin ζ := by
  have h2 := aC_mul_bC (ε := ε) hS
  simp only [Zi, axis, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (2 * ε * Real.cos ζ * Real.sin ζ) * h2

/-- `|Z| = S² + ε² cos² ζ sin² ζ` on the axis. -/
theorem Mo_axis (hS : 0 < S) (ζ : ℝ) :
    Mo ε (axis ε S ζ) = S ^ 2 + ε ^ 2 * Real.cos ζ ^ 2 * Real.sin ζ ^ 2 := by
  rw [Mo, Zr_axis hS, Zi_axis hS]
  rw [show (S ^ 2 - ε ^ 2 * Real.cos ζ ^ 2 * Real.sin ζ ^ 2) ^ 2 +
      (2 * ε * S * Real.cos ζ * Real.sin ζ) ^ 2 =
      (S ^ 2 + ε ^ 2 * Real.cos ζ ^ 2 * Real.sin ζ ^ 2) ^ 2 by ring]
  exact Real.sqrt_sq (by positivity)

/-- `σ = S` on the axis (paper, above (3.20): `X = Y = 0` gives `σ = S`, `z = 0`). -/
theorem sg_axis (hS : 0 < S) (ζ : ℝ) : sg ε (axis ε S ζ) = S := by
  rw [sg, Mo_axis hS, Zr_axis hS]
  rw [show (S ^ 2 + ε ^ 2 * Real.cos ζ ^ 2 * Real.sin ζ ^ 2 +
      (S ^ 2 - ε ^ 2 * Real.cos ζ ^ 2 * Real.sin ζ ^ 2)) / 2 = S ^ 2 by ring]
  exact Real.sqrt_sq hS.le

/-- The axis lies in `𝒰`. -/
theorem axis_mem (hS : 0 < S) (ζ : ℝ) : axis ε S ζ ∈ U ε := by
  change 0 < Mo ε _ + Zr ε _
  rw [Mo_axis hS, Zr_axis hS]
  nlinarith

/-- `ν = ε cos ζ sin ζ = (ε/2) sin 2ζ` on the axis (paper (3.10)). -/
theorem nu_axis (hS : 0 < S) (ζ : ℝ) :
    nu ε (axis ε S ζ) = ε * Real.cos ζ * Real.sin ζ := by
  have h2 := aC_mul_bC (ε := ε) hS
  rw [nu, sg_axis hS]
  simp only [axis, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  linear_combination (ε * Real.cos ζ * Real.sin ζ) * h2

/-- `ψ = 0` on the axis: the axis is the degenerate flux surface (paper (3.20)). -/
theorem psi_axis (hS : 0 < S) (lam ζ : ℝ) : psi ε S lam (axis ε S ζ) = 0 := by
  rw [psi, vR, sg_axis hS, sub_self]
  simp only [sz, cz, axis, PiLp.toLp_apply, Matrix.cons_val, mul_zero, Real.sin_zero,
    Real.cos_zero]
  ring

/-- `G > 0`. -/
theorem Gax_pos (hS : 0 < S) (ζ : ℝ) : 0 < Gax ε S ζ := by
  have ha := aC_pos (ε := ε) hS
  have hb := bC_pos (ε := ε) hS
  have h3 := Real.cos_sq_add_sin_sq ζ
  unfold Gax
  have hm := lt_min (pow_pos ha 2) (pow_pos hb 2)
  nlinarith [min_le_left (aC ε S ^ 2) (bC ε S ^ 2), min_le_right (aC ε S ^ 2) (bC ε S ^ 2),
    sq_nonneg (Real.cos ζ), sq_nonneg (Real.sin ζ)]

end AxisField

section AxisField2
variable {ε S : ℝ}

/-- Polynomial identities behind the field on the axis. -/
theorem axis_identities (hS : 0 < S) (ζ : ℝ) :
    (S * (bC ε S * Real.sin ζ) - ε * Real.cos ζ * Real.sin ζ * (aC ε S * Real.cos ζ)) * Gax ε S ζ =
      aC ε S * Real.sin ζ * (S ^ 2 + (ε * Real.cos ζ * Real.sin ζ) ^ 2) ∧
    (S * (aC ε S * Real.cos ζ) + ε * Real.cos ζ * Real.sin ζ * (bC ε S * Real.sin ζ)) * Gax ε S ζ =
      bC ε S * Real.cos ζ * (S ^ 2 + (ε * Real.cos ζ * Real.sin ζ) ^ 2) := by
  have h1 := bC_sq_sub (ε := ε) hS
  have h2 := aC_mul_bC (ε := ε) hS
  have h3 := Real.cos_sq_add_sin_sq ζ
  unfold Gax
  set a := aC ε S
  set b := bC ε S
  set c := Real.cos ζ
  set s := Real.sin ζ
  rw [← h2]
  constructor
  · linear_combination (-(a * s * (b ^ 2 * s ^ 2 - b ^ 2 - ε * c ^ 2 * s ^ 2))) * h1 +
      (a * s * b ^ 2 * (b ^ 2 - ε * c ^ 2 - ε)) * h3
  · linear_combination (-(b * c * (a ^ 2 * s ^ 2 + b ^ 2 * c ^ 2 + b ^ 2 * s ^ 2 - b ^ 2 +
      ε * s ^ 4 - ε * s ^ 2))) * h1 + (b * c * (b ^ 2 - ε) * (b ^ 2 + ε * s ^ 2)) * h3

/-- **The field on the axis is tangent to it**: `B(γ(ζ)) = (cosh ν / (2G)) γ'(ζ)` with
`ν = ε cos ζ sin ζ`, a positive multiple of the tangent (paper (3.20), (3.23): on the axis
`B · ∇ζ = cosh ν / (2G) > 0`). -/
theorem field_axis (hS : 0 < S) (lam ζ : ℝ) :
    field ε S lam (axis ε S ζ) =
      (Real.cosh (ε * Real.cos ζ * Real.sin ζ) / (2 * Gax ε S ζ)) • axisVel ε S ζ := by
  have hG := Gax_pos (ε := ε) hS ζ
  obtain ⟨k0, k1⟩ := axis_identities (ε := ε) hS ζ
  have hz : (axis ε S ζ) 2 = 0 := rfl
  have huR : uR ε S lam (axis ε S ζ) = Real.cosh (ε * Real.cos ζ * Real.sin ζ) := by
    simp only [uR, cz, sz, hz, sg_axis hS, nu_axis hS, mul_zero, Real.cos_zero, Real.sin_zero,
      sub_self, one_mul, zero_mul, sub_zero]
  have huI : uI ε S lam (axis ε S ζ) = 0 := by
    simp only [uI, cz, sz, hz, sg_axis hS, mul_zero, Real.cos_zero, Real.sin_zero, sub_self,
      zero_mul, mul_zero, add_zero, neg_zero]
  have hvR : vR ε S lam (axis ε S ζ) = 0 := by
    simp only [vR, cz, sz, hz, sg_axis hS, mul_zero, Real.sin_zero, sub_self, zero_mul, add_zero]
  have hMq : Mq ε (axis ε S ζ) = S ^ 2 + (ε * Real.cos ζ * Real.sin ζ) ^ 2 := by
    rw [Mq, sg_axis hS, nu_axis hS]
  have hMp : 0 < S ^ 2 + (ε * Real.cos ζ * Real.sin ζ) ^ 2 := by positivity
  apply space_ext
  · simp only [field, huR, huI, hMq, al, be, sg_axis hS, nu_axis hS]
    simp only [axis, axisVel, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      PiLp.smul_apply, smul_eq_mul, zero_mul, add_zero]
    field_simp
    linear_combination (-1 : ℝ) * k0
  · simp only [field, huR, huI, hMq, al, be, sg_axis hS, nu_axis hS]
    simp only [axis, axisVel, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      PiLp.smul_apply, smul_eq_mul, zero_mul, sub_zero]
    field_simp
    linear_combination k1
  · simp only [field, hvR, axisVel, PiLp.toLp_apply, Matrix.cons_val, PiLp.smul_apply,
      smul_eq_mul, neg_zero, zero_div, mul_zero]

end AxisField2

section AxisCurve
variable {ε S : ℝ}

/-- Derivative of the axis curve. -/
theorem axis_hasDerivAt (ζ : ℝ) : HasDerivAt (axis ε S) (axisVel ε S ζ) ζ := by
  apply curve_hasDerivAt
  intro k
  fin_cases k
  · simpa [axis, axisVel] using (Real.hasDerivAt_cos ζ).const_mul (aC ε S)
  · simpa [axis, axisVel] using (Real.hasDerivAt_sin ζ).const_mul (bC ε S)
  · simpa [axis, axisVel] using hasDerivAt_const ζ (0 : ℝ)

/-- **The axis is an integral curve of the field** up to the positive time change
`dt = (2G/cosh ν) dζ`: `γ'(ζ) = (2G/cosh ν) B(γ(ζ))`. -/
theorem axis_tangent (hS : 0 < S) (lam ζ : ℝ) :
    HasDerivAt (axis ε S)
      ((2 * Gax ε S ζ / Real.cosh (ε * Real.cos ζ * Real.sin ζ)) •
        field ε S lam (axis ε S ζ)) ζ := by
  rw [field_axis hS, smul_smul]
  have hG := Gax_pos (ε := ε) hS ζ
  have hc := Real.cosh_pos (ε * Real.cos ζ * Real.sin ζ)
  rw [show 2 * Gax ε S ζ / Real.cosh (ε * Real.cos ζ * Real.sin ζ) *
      (Real.cosh (ε * Real.cos ζ * Real.sin ζ) / (2 * Gax ε S ζ)) = 1 by field_simp, one_smul]
  exact axis_hasDerivAt ζ

/-- The field does not vanish on the axis. -/
theorem field_axis_ne_zero (hS : 0 < S) (lam ζ : ℝ) : field ε S lam (axis ε S ζ) ≠ 0 := by
  rw [field_axis hS]
  have hG := Gax_pos (ε := ε) hS ζ
  have hc := Real.cosh_pos (ε * Real.cos ζ * Real.sin ζ)
  refine smul_ne_zero (by positivity) ?_
  intro h
  have h0 := congrArg (fun v : Space => v 0) h
  have h1 := congrArg (fun v : Space => v 1) h
  simp only [axisVel, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    PiLp.zero_apply, neg_eq_zero, mul_eq_zero] at h0 h1
  have ha := (aC_pos (ε := ε) hS).ne'
  have hb := (bC_pos (ε := ε) hS).ne'
  have := Real.sin_sq_add_cos_sq ζ
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  all_goals first | exact ha h0 | exact hb h1 | (rw [h0, h1] at this; norm_num at this)

/-- **The axis is planar** (it lies in `z = 0`). -/
theorem axis_planar (ζ : ℝ) : axis ε S ζ 2 = 0 := rfl

/-- **The axis is an ellipse** with semi-axes `a_c(S)`, `b_c(S)`. -/
theorem axis_ellipse (hS : 0 < S) (ζ : ℝ) :
    (axis ε S ζ 0 / aC ε S) ^ 2 + (axis ε S ζ 1 / bC ε S) ^ 2 = 1 := by
  have ha := (aC_pos (ε := ε) hS).ne'
  have hb := (bC_pos (ε := ε) hS).ne'
  simp only [axis, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  linear_combination Real.cos_sq_add_sin_sq ζ

/-- For `ε ≠ 0` the axis is not a circle: its semi-axes differ (`b_c² - a_c² = ε`). -/
theorem axis_not_circle (hS : 0 < S) (hε : ε ≠ 0) : aC ε S ≠ bC ε S := by
  intro h
  have := bC_sq_sub (ε := ε) hS
  rw [h, sub_self] at this
  exact hε this.symm

end AxisCurve

/-! ## Symmetry and non-axisymmetry -/

/-- **Two field periods**: `B(R_π x) = R_π B(x)` for the rotation by `π` about the `z`-axis. -/
theorem field_rotPi (ε S lam : ℝ) (x : Space) : field ε S lam (rotPi x) = rotPi (field ε S lam x)
    := by
  have h0 : rotPi x 0 = -x 0 := rfl
  have h1 : rotPi x 1 = -x 1 := rfl
  have h2 : rotPi x 2 = x 2 := rfl
  have hr : r2 (rotPi x) = r2 x := by unfold r2; rw [h0, h1]; ring
  have hZr : Zr ε (rotPi x) = Zr ε x := by unfold Zr; rw [hr, h0, h1]; ring
  have hZi : Zi ε (rotPi x) = Zi ε x := by unfold Zi; rw [h0, h1]; ring
  have hs : sg ε (rotPi x) = sg ε x := by unfold sg Mo; rw [hZr, hZi]
  have hn : nu ε (rotPi x) = nu ε x := by unfold nu; rw [hs, h0, h1]; ring
  have hcz : cz lam (rotPi x) = cz lam x := by unfold cz; rw [h2]
  have hsz : sz lam (rotPi x) = sz lam x := by unfold sz; rw [h2]
  have huR : uR ε S lam (rotPi x) = uR ε S lam x := by unfold uR; rw [hcz, hsz, hs, hn]
  have huI : uI ε S lam (rotPi x) = uI ε S lam x := by unfold uI; rw [hcz, hsz, hs, hn]
  have hvR : vR ε S lam (rotPi x) = vR ε S lam x := by unfold vR; rw [hcz, hsz, hs, hn]
  have hal : al ε (rotPi x) = -al ε x := by unfold al; rw [hs, hn, h0, h1]; ring
  have hbe : be ε (rotPi x) = -be ε x := by unfold be; rw [hs, hn, h0, h1]; ring
  have hM : Mq ε (rotPi x) = Mq ε x := by unfold Mq; rw [hs, hn]
  apply space_ext
  · rw [show rotPi (field ε S lam x) 0 = -(field ε S lam x 0) from rfl]
    simp only [field, PiLp.toLp_apply, Matrix.cons_val_zero]
    rw [huR, huI, hal, hbe, hM]; ring
  · rw [show rotPi (field ε S lam x) 1 = -(field ε S lam x 1) from rfl]
    simp only [field, PiLp.toLp_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [huR, huI, hal, hbe, hM]; ring
  · rw [show rotPi (field ε S lam x) 2 = field ε S lam x 2 from rfl]
    simp only [field, PiLp.toLp_apply, Matrix.cons_val]
    rw [hvR]

/-- **Non-axisymmetry** (for `0 < ε`, with the mild size condition `ε(S + ε) ≤ 3S`, which holds
e.g. for `ε ≤ 1 ≤ S`): the field is not invariant under the quarter turn about the `z`-axis.
At `x = (b_c, 0, 0)` the vertical field `B_z = -sin(σ - S)/λ` is nonzero, while at the rotated
point `(0, b_c, 0)`, which lies on the magnetic axis, `B_z = 0`. -/
theorem field_not_axisymmetric {ε S lam : ℝ} (hε : 0 < ε) (hS : 0 < S)
    (hεS : ε * (S + ε) ≤ 3 * S) (hl : lam ≠ 0) :
    ¬ ∀ x ∈ U ε, field ε S lam (rotQ x) = rotQ (field ε S lam x) := by
  intro h
  set b := bC ε S with hbdef
  set x1 : Space := toLp 2 ![b, 0, 0] with hx1
  have hb := bC_pos (ε := ε) hS
  have hb2 := bC_sq (ε := ε) hS
  have hab := aC_mul_bC (ε := ε) hS
  have hba := bC_sq_sub (ε := ε) hS
  have e0 : x1 0 = b := rfl
  have e1 : x1 1 = 0 := rfl
  have e2 : x1 2 = 0 := rfl
  have hZr : Zr ε x1 = b ^ 4 + ε * b ^ 2 := by unfold Zr r2; rw [e0, e1]; ring
  have hZi : Zi ε x1 = 0 := by unfold Zi; rw [e1]; ring
  have hZpos : 0 < Zr ε x1 := by rw [hZr]; positivity
  have hMo : Mo ε x1 = Zr ε x1 := by
    rw [Mo, hZi]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
    exact Real.sqrt_sq hZpos.le
  have hmem : x1 ∈ U ε := by change 0 < Mo ε x1 + Zr ε x1; rw [hMo]; linarith
  have hsg : sg ε x1 = √(Zr ε x1) := by rw [sg, hMo]; ring_nf
  have hnu : nu ε x1 = 0 := by unfold nu; rw [e1]; ring
  have hsg2 : sg ε x1 ^ 2 = b ^ 4 + ε * b ^ 2 := by rw [hsg, Real.sq_sqrt hZpos.le, hZr]
  have hS2 : S ^ 2 = b ^ 4 - ε * b ^ 2 := by
    rw [← hab, mul_pow, show aC ε S ^ 2 = b ^ 2 - ε by linarith]; ring
  have hsgpos : 0 < sg ε x1 := sg_pos hmem
  have hgt : S < sg ε x1 := by nlinarith
  -- `b² ≤ S + ε`
  have hh : hC ε S ≤ 2 * S + ε := by
    unfold hC
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hb2le : b ^ 2 ≤ S + ε := by rw [hb2]; linarith
  have hlt : sg ε x1 - S < Real.pi := by
    have h1 : (sg ε x1 - S) * (sg ε x1 + S) = 2 * ε * b ^ 2 := by nlinarith
    have h2 : (sg ε x1 - S) * (2 * S) ≤ 2 * ε * b ^ 2 := by nlinarith
    have h3 : (sg ε x1 - S) * S ≤ 3 * S := by nlinarith
    have : sg ε x1 - S ≤ 3 := le_of_mul_le_mul_right (by linarith) hS
    linarith [Real.pi_gt_three]
  have hsin : 0 < Real.sin (sg ε x1 - S) := Real.sin_pos_of_pos_of_lt_pi (by linarith) hlt
  have hB1 : field ε S lam x1 2 = -Real.sin (sg ε x1 - S) / lam := by
    simp only [field, vR, cz, sz, e2, hnu, PiLp.toLp_apply, Matrix.cons_val, mul_zero,
      Real.cos_zero, Real.sin_zero, Real.cosh_zero, Real.sinh_zero, one_mul, mul_one, zero_mul,
      add_zero]
  have hrot : rotQ x1 = axis ε S (Real.pi / 2) := by
    apply space_ext <;> simp [rotQ, axis, x1, hbdef]
  have hB2 : field ε S lam (rotQ x1) 2 = 0 := by
    rw [hrot, field_axis hS]
    simp only [axisVel, PiLp.smul_apply, Matrix.cons_val, smul_eq_mul, mul_zero]
  have := congrArg (fun v : Space => v 2) (h x1 hmem)
  simp only at this
  rw [hB2, show rotQ (field ε S lam x1) 2 = field ε S lam x1 2 from rfl, hB1] at this
  have : Real.sin (sg ε x1 - S) = 0 := by
    field_simp at this; linarith
  linarith

/-- Sanity: in the limit `ε = 0` the field is axisymmetric (invariant under the quarter turn;
paper, below (3.7): "`ε → 0` corresponds to axisymmetry"). -/
theorem field_axisymmetric_limit (S lam : ℝ) (x : Space) :
    field 0 S lam (rotQ x) = rotQ (field 0 S lam x) := by
  have h0 : rotQ x 0 = -x 1 := rfl
  have h1 : rotQ x 1 = x 0 := rfl
  have h2 : rotQ x 2 = x 2 := rfl
  have hr : r2 (rotQ x) = r2 x := by unfold r2; rw [h0, h1]; ring
  have hZr : Zr 0 (rotQ x) = Zr 0 x := by unfold Zr; rw [hr]; ring
  have hZi : Zi 0 (rotQ x) = Zi 0 x := by unfold Zi; ring
  have hs : sg 0 (rotQ x) = sg 0 x := by unfold sg Mo; rw [hZr, hZi]
  have hn : nu 0 (rotQ x) = 0 := by unfold nu; ring
  have hn' : nu 0 x = 0 := by unfold nu; ring
  have hcz : cz lam (rotQ x) = cz lam x := by unfold cz; rw [h2]
  have hsz : sz lam (rotQ x) = sz lam x := by unfold sz; rw [h2]
  have huR : uR 0 S lam (rotQ x) = uR 0 S lam x := by unfold uR; rw [hcz, hsz, hs, hn, hn']
  have huI : uI 0 S lam (rotQ x) = uI 0 S lam x := by unfold uI; rw [hcz, hsz, hs, hn, hn']
  have hvR : vR 0 S lam (rotQ x) = vR 0 S lam x := by unfold vR; rw [hcz, hsz, hs, hn, hn']
  have hal : al 0 (rotQ x) = -be 0 x := by unfold al be; rw [hs, hn, hn', h0, h1]; ring
  have hbe : be 0 (rotQ x) = al 0 x := by unfold al be; rw [hs, hn, hn', h0, h1]; ring
  have hM : Mq 0 (rotQ x) = Mq 0 x := by unfold Mq; rw [hs, hn, hn']
  apply space_ext
  · rw [show rotQ (field 0 S lam x) 0 = -(field 0 S lam x 1) from rfl]
    simp only [field, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [huR, huI, hal, hbe, hM]; ring
  · rw [show rotQ (field 0 S lam x) 1 = field 0 S lam x 0 from rfl]
    simp only [field, PiLp.toLp_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [huR, huI, hal, hbe, hM]; ring
  · rw [show rotQ (field 0 S lam x) 2 = field 0 S lam x 2 from rfl]
    simp only [field, PiLp.toLp_apply, Matrix.cons_val]
    rw [hvR]

/-! ## All-time confinement in the plasma region -/

/-- On `R` (for `ε = 1/4`, `S = 4`), `ψ ≤ 81/200` forces `|σ - 4| ≤ 1.13` and `|λz| ≤ 1.13`. -/
theorem R_bound {lam : ℝ} {x : Space} (hx : x ∈ R (1 / 4) 4 lam)
    (hψ : psi (1 / 4) 4 lam x ≤ 81 / 200) :
    |sg (1 / 4) x - 4| ≤ 113 / 100 ∧ |lam * x 2| ≤ 113 / 100 := by
  obtain ⟨-, hξ0, hz0⟩ := hx
  have hXY : Xf (1 / 4) 4 lam x ^ 2 + Yf lam x ^ 2 ≤ 81 / 100 := by
    have := psi_eq_XY (1 / 4) 4 lam x; linarith
  have huI := uI_sq_add (1 / 4) 4 lam x
  have h113 := sin_113_ge
  constructor
  · exact abs_le_of_sin_sq_le hξ0 (by norm_num)
      (by nlinarith [sq_nonneg (uI (1 / 4) 4 lam x)])
  · refine abs_le_of_sin_sq_le hz0 (by norm_num) ?_
    have : Real.sin (lam * x 2) ^ 2 = Yf lam x ^ 2 := by unfold Yf sz; ring
    nlinarith [sq_nonneg (Xf (1 / 4) 4 lam x)]

/-- A point with `|σ - 4| < π/2` and `|λz| < π/2` lies in `R` (`σ > 0` gives `x ∈ 𝒰`). -/
theorem mem_R_of {lam : ℝ} {x : Space} (h1 : |sg (1 / 4) x - 4| < Real.pi / 2)
    (h2 : |lam * x 2| < Real.pi / 2) : x ∈ R (1 / 4) 4 lam := by
  refine ⟨?_, h1, h2⟩
  have hs : 0 < sg (1 / 4) x := by
    linarith [neg_abs_le (sg (1 / 4) x - 4), Real.pi_lt_d2]
  have := Real.sqrt_pos.mp hs
  change 0 < Mo (1 / 4) x + Zr (1 / 4) x
  linarith

/-- `σ` is continuous. -/
theorem continuous_sg (ε : ℝ) : Continuous (sg ε) := by
  unfold sg Mo Zr Zi r2
  fun_prop

/-- **All-time confinement** (for `ε = 1/4`, `S = 4`, any `λ ≠ 0`): a forward field line that
starts in `R` with `ψ ≤ 81/200` stays in `R` and keeps its value of `ψ` for all `t ≥ 0`. -/
theorem fieldLine_confined {lam : ℝ} (hl : lam ≠ 0) {γ : ℝ → Space}
    (hγ : IsForwardFieldLine (field (1 / 4) 4 lam) γ) (h0 : γ 0 ∈ R (1 / 4) 4 lam)
    (hψ0 : psi (1 / 4) 4 lam (γ 0) ≤ 81 / 200) {t : ℝ} (ht : 0 ≤ t) :
    γ t ∈ R (1 / 4) 4 lam ∧ psi (1 / 4) 4 lam (γ t) = psi (1 / 4) 4 lam (γ 0) := by
  set m : ℝ → ℝ := fun s => max |sg (1 / 4) (γ s) - 4| |lam * γ s 2| with hmdef
  have hpi := Real.pi_gt_d4
  have hcont : ContinuousOn m (Set.Icc 0 t) := by
    have hγc : ContinuousOn γ (Set.Icc 0 t) := fun s hs =>
      (hγ s hs.1).continuousAt.continuousWithinAt
    have h2 : ContinuousOn (fun s => γ s 2) (Set.Icc 0 t) :=
      ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 2).continuous).comp_continuousOn hγc
    exact ContinuousOn.sup (((continuous_sg _).comp_continuousOn hγc).sub
      continuousOn_const).abs (ContinuousOn.abs (continuousOn_const.mul h2))
  have hfi := psi_firstIntegral (ε := 1 / 4) (S := 4) hl
  have hcons (σ : ℝ) (hσ : σ ∈ Set.Icc 0 t) (hin : ∀ s ∈ Set.Icc 0 σ, γ s ∈ R (1 / 4) 4 lam) :
      psi (1 / 4) 4 lam (γ σ) = psi (1 / 4) 4 lam (γ 0) :=
    firstIntegral_conserved hfi (T := σ) (fun s hs => hγ s hs.1) (fun s hs => (hin s hs).1)
      ⟨hσ.1, le_rfl⟩
  have hmR (s : ℝ) (hs : m s < 3 / 2) : γ s ∈ R (1 / 4) 4 lam :=
    mem_R_of (by linarith [le_max_left |sg (1 / 4) (γ s) - 4| |lam * γ s 2|])
      (by linarith [le_max_right |sg (1 / 4) (γ s) - 4| |lam * γ s 2|])
  have hmb (s : ℝ) (hR : γ s ∈ R (1 / 4) 4 lam) (hψ : psi (1 / 4) 4 lam (γ s) ≤ 81 / 200) :
      m s ≤ 113 / 100 := by
    obtain ⟨a, b⟩ := R_bound hR hψ
    exact max_le a b
  have hstay : ∀ s ∈ Set.Icc 0 t, m s < 3 / 2 := by
    by_contra hneg
    push Not at hneg
    set B := Set.Icc 0 t ∩ m ⁻¹' Set.Ici (3 / 2) with hB
    have hBne : B.Nonempty := by
      obtain ⟨s, hs, hle⟩ := hneg
      exact ⟨s, hs, hle⟩
    have hBcl : IsClosed B := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hBbdd : BddBelow B := ⟨0, fun s hs => hs.1.1⟩
    set τ := sInf B
    have hτ : τ ∈ B := hBcl.csInf_mem hBne hBbdd
    have hbefore (s : ℝ) (hs0 : 0 ≤ s) (hsτ : s < τ) : m s < 3 / 2 := by
      by_contra hc
      push Not at hc
      have : s ∈ B := ⟨⟨hs0, by linarith [hτ.1.2]⟩, hc⟩
      exact absurd (csInf_le hBbdd this) (not_le.mpr hsτ)
    have hstart : m 0 ≤ 113 / 100 := hmb 0 h0 hψ0
    have hτt : τ ∈ Set.Icc 0 t := hτ.1
    have hcontτ : ContinuousOn m (Set.Icc 0 τ) := hcont.mono (Set.Icc_subset_Icc le_rfl hτt.2)
    obtain ⟨σ, hσ, hσeq⟩ := intermediate_value_Icc hτt.1 hcontτ
      (show (13 / 10 : ℝ) ∈ Set.Icc (m 0) (m τ) by
        constructor
        · linarith
        · have : 3 / 2 ≤ m τ := hτ.2
          linarith)
    have hστ : σ < τ := by
      rcases lt_or_eq_of_le hσ.2 with h | h
      · exact h
      · exfalso
        have : 3 / 2 ≤ m τ := hτ.2
        rw [← h] at this
        linarith
    have hin : ∀ s ∈ Set.Icc 0 σ, γ s ∈ R (1 / 4) 4 lam := fun s hs =>
      hmR s (hbefore s hs.1 (lt_of_le_of_lt hs.2 hστ))
    have hσt : σ ∈ Set.Icc 0 t := ⟨hσ.1, by linarith [hτt.2]⟩
    have hψσ := hcons σ hσt hin
    have := hmb σ (hin σ ⟨hσ.1, le_rfl⟩) (hψσ.le.trans hψ0)
    linarith
  have hin : ∀ s ∈ Set.Icc 0 t, γ s ∈ R (1 / 4) 4 lam := fun s hs => hmR s (hstay s hs)
  exact ⟨hin t ⟨ht, le_rfl⟩, hcons t ⟨ht, le_rfl⟩ hin⟩

/-! ## Agreement with the paper's complex formulas (3.1)–(3.2) -/

section Paper
open Complex ComplexConjugate

/-- `ω = x + i y`. -/
@[expose] def omega (x : Space) : ℂ := ⟨x 0, x 1⟩

/-- The paper's `K = ω̄ √(1 + ε/ω̄²)` (principal square root, positive real part; (3.1)). -/
@[expose] def Kp (ε : ℝ) (x : Space) : ℂ :=
  conj (omega x) * (1 + (ε : ℂ) / conj (omega x) ^ 2) ^ (2⁻¹ : ℂ)

/-- The paper's `Ξ = ω K + π/2 - S` ((3.1)). -/
@[expose] def Xip (ε S : ℝ) (x : Space) : ℂ := omega x * Kp ε x + (Real.pi / 2 : ℝ) - (S : ℂ)

/-- The paper's field (3.2), verbatim:
`B_x + i B_y = i e^{-iλz} sin Ξ / (2K)`, `B_z = Re(e^{-iλz} cos Ξ)/λ`. -/
@[expose] def fieldPaper (ε S lam : ℝ) (x : Space) : Space :=
  toLp 2 ![(I * exp (-I * (lam * x 2 : ℝ)) / (2 * Kp ε x) * sin (Xip ε S x)).re,
    (I * exp (-I * (lam * x 2 : ℝ)) / (2 * Kp ε x) * sin (Xip ε S x)).im,
    (exp (-I * (lam * x 2 : ℝ)) * cos (Xip ε S x)).re / lam]

/-- The square-root factor: `√(1 + ε/ω̄²) = (σ + iν)/r²` on `𝒰`. -/
theorem sqrt_factor {ε : ℝ} {x : Space} (hx : x ∈ U ε) :
    (1 + (ε : ℂ) / conj (omega x) ^ 2) ^ (2⁻¹ : ℂ) =
      ⟨sg ε x / r2 x, nu ε x / r2 x⟩ := by
  have hr := r2_pos hx
  have hu : (1 + (ε : ℂ) / conj (omega x) ^ 2) = ⟨Zr ε x / r2 x ^ 2, Zi ε x / r2 x ^ 2⟩ := by
    have hne : conj (omega x) ^ 2 ≠ 0 := by
      apply pow_ne_zero
      intro h
      have h0 := congrArg Complex.re h
      have h1 := congrArg Complex.im h
      simp only [omega, conj_re, conj_im, zero_re, zero_im, neg_eq_zero] at h0 h1
      unfold r2 at hr
      rw [h0, h1] at hr
      norm_num at hr
    rw [one_add_div hne, div_eq_iff hne]
    have hr' : r2 x ≠ 0 := hr.ne'
    apply Complex.ext
    · simp only [omega, Fin.isValue, pow_two, add_re, mul_re, conj_re, conj_im, mul_neg, neg_mul,
        neg_neg, ofReal_re, Zr, Zi, mul_im]
      unfold r2 at hr'
      field_simp
      unfold r2
      ring
    · simp only [omega, Fin.isValue, pow_two, add_im, mul_im, conj_re, conj_im, mul_neg, neg_mul,
        ofReal_im, add_zero, Zr, Zi, mul_re, neg_neg]
      unfold r2 at hr'
      field_simp
      unfold r2
      ring
  have hr2 : r2 x ^ 2 ≠ 0 := by positivity
  set u : ℂ := ⟨Zr ε x / r2 x ^ 2, Zi ε x / r2 x ^ 2⟩ with hudef
  have hnorm : ‖u‖ = Mo ε x / r2 x ^ 2 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, Mo]
    simp only [u]
    rw [div_pow, div_pow, ← add_div, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq (by positivity)]
  have hMo : Mo ε x = sg ε x ^ 2 + nu ε x ^ 2 := (Mq_eq_Mo hx).symm
  have h2 := sg_sq hx
  have hnu2 : (Mo ε x - Zr ε x) / 2 = nu ε x ^ 2 := by linarith
  have hsg2 : (Mo ε x + Zr ε x) / 2 = sg ε x ^ 2 := by linarith
  have hs := sg_pos hx
  rw [hu]
  apply Complex.ext
  · rw [Complex.cpow_inv_two_re, hnorm]
    simp only [u]
    rw [← add_div, div_div, show r2 x ^ 2 * 2 = 2 * r2 x ^ 2 by ring, ← div_div, hsg2,
      Real.sqrt_div' _ (by positivity), Real.sqrt_sq hs.le, Real.sqrt_sq hr.le]
  · have hnu : nu ε x = Zi ε x / (2 * sg ε x) := by
      unfold nu Zi; field_simp
    rcases le_or_gt 0 (Zi ε x) with hZ | hZ
    · have hZ' : 0 ≤ u.im := by simp only [u]; positivity
      rw [Complex.cpow_inv_two_im_eq_sqrt hZ', hnorm]
      simp only [u]
      have hn0 : 0 ≤ nu ε x := by rw [hnu]; positivity
      rw [← sub_div, div_div, show r2 x ^ 2 * 2 = 2 * r2 x ^ 2 by ring, ← div_div, hnu2,
        Real.sqrt_div' _ (by positivity), Real.sqrt_sq hn0, Real.sqrt_sq hr.le]
    · have hZ' : u.im < 0 := by
        simp only [u]; exact div_neg_of_neg_of_pos hZ (by positivity)
      rw [Complex.cpow_inv_two_im_eq_neg_sqrt hZ', hnorm]
      simp only [u]
      have hn0 : nu ε x < 0 := by rw [hnu]; exact div_neg_of_neg_of_pos hZ (by positivity)
      rw [← sub_div, div_div, show r2 x ^ 2 * 2 = 2 * r2 x ^ 2 by ring, ← div_div, hnu2,
        Real.sqrt_div' _ (by positivity), Real.sqrt_sq_eq_abs, abs_of_neg hn0,
        Real.sqrt_sq hr.le]
      ring

/-- `ω K = P = σ + iν`. -/
theorem omega_mul_Kp {ε : ℝ} {x : Space} (hx : x ∈ U ε) :
    omega x * Kp ε x = ⟨sg ε x, nu ε x⟩ := by
  have hr := (r2_pos hx).ne'
  rw [Kp, sqrt_factor hx]
  apply Complex.ext
  · simp only [omega, mul_re, conj_re, conj_im, mul_im]
    unfold r2 at hr ⊢
    field_simp
    ring
  · simp only [omega, mul_im, conj_re, conj_im, mul_re]
    unfold r2 at hr ⊢
    field_simp
    ring

/-- `Ξ = (σ - S + π/2) + iν`. -/
theorem Xip_eq {ε S : ℝ} {x : Space} (hx : x ∈ U ε) :
    Xip ε S x = ((sg ε x - S : ℝ) : ℂ) + (nu ε x : ℂ) * I + ((Real.pi / 2 : ℝ) : ℂ) := by
  rw [Xip, omega_mul_Kp hx]
  apply Complex.ext
  · simp only [add_re, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero]
    ring
  · simp only [add_im, sub_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, mul_zero, mul_one,
      zero_add, sub_zero, add_zero]

/-- `sin Ξ = cos(σ - S) cosh ν - i sin(σ - S) sinh ν`. -/
theorem sin_Xip {ε S : ℝ} {x : Space} (hx : x ∈ U ε) :
    sin (Xip ε S x) = ((Real.cos (sg ε x - S) * Real.cosh (nu ε x) : ℝ) : ℂ) -
      ((Real.sin (sg ε x - S) * Real.sinh (nu ε x) : ℝ) : ℂ) * I := by
  rw [Xip_eq hx, Complex.ofReal_div, Complex.ofReal_ofNat, sin_add_pi_div_two, cos_add_mul_I]
  push_cast
  ring

/-- `cos Ξ = -(sin(σ - S) cosh ν + i cos(σ - S) sinh ν)`. -/
theorem cos_Xip {ε S : ℝ} {x : Space} (hx : x ∈ U ε) :
    cos (Xip ε S x) = -(((Real.sin (sg ε x - S) * Real.cosh (nu ε x) : ℝ) : ℂ) +
      ((Real.cos (sg ε x - S) * Real.sinh (nu ε x) : ℝ) : ℂ) * I) := by
  rw [Xip_eq hx, Complex.ofReal_div, Complex.ofReal_ofNat, cos_add_pi_div_two, sin_add_mul_I]
  push_cast
  ring

/-- `e^{-iλz} = cos λz - i sin λz`. -/
theorem exp_neg_I (t : ℝ) :
    exp (-I * (t : ℂ)) = ((Real.cos t : ℝ) : ℂ) - ((Real.sin t : ℝ) : ℂ) * I := by
  rw [show -I * (t : ℂ) = ((-t : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

/-- **Source fidelity**: the real-variable field `field` is exactly the paper's complex formula
(3.1)–(3.2) (with the principal square root, `Re √· > 0`), at every point of `𝒰`. -/
theorem field_eq_paper (ε S lam : ℝ) {x : Space} (hx : x ∈ U ε) :
    field ε S lam x = fieldPaper ε S lam x := by
  have hr := r2_pos hx
  have hm := Mq_pos hx
  have hK : Kp ε x = conj (omega x) * ⟨sg ε x / r2 x, nu ε x / r2 x⟩ := by
    rw [Kp, sqrt_factor hx]
  have hK0 : 2 * Kp ε x ≠ 0 := by
    intro h
    have h1 := congrArg (fun z => omega x * z) h
    simp only [mul_zero] at h1
    rw [show omega x * (2 * Kp ε x) = 2 * (omega x * Kp ε x) by ring, omega_mul_Kp hx] at h1
    have := congrArg Complex.re h1
    simp at this
    linarith [sg_pos hx]
  have hB : I * exp (-I * (lam * x 2 : ℝ)) / (2 * Kp ε x) * sin (Xip ε S x) =
      ⟨field ε S lam x 0, field ε S lam x 1⟩ := by
    rw [div_mul_eq_mul_div, div_eq_iff hK0, exp_neg_I, sin_Xip hx, hK]
    simp only [field, uR, uI, al, be, cz, sz, omega, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    unfold Mq r2 at *
    generalize Real.cos (lam * x 2) = c1 at *
    generalize Real.sin (lam * x 2) = s1 at *
    generalize Real.cos (sg ε x - S) = c2 at *
    generalize Real.sin (sg ε x - S) = s2 at *
    generalize Real.cosh (nu ε x) = c3 at *
    generalize Real.sinh (nu ε x) = s3 at *
    generalize sg ε x = σ at *
    generalize nu ε x = n at *
    generalize x 0 = p at *
    generalize x 1 = q at *
    apply Complex.ext
    · simp only [mul_re, mul_im, sub_re, sub_im, ofReal_re, ofReal_im, I_re, I_im, conj_re,
        conj_im, re_ofNat, im_ofNat]
      field_simp
      ring
    · simp only [mul_re, mul_im, sub_re, sub_im, ofReal_re, ofReal_im, I_re, I_im, conj_re,
        conj_im, re_ofNat, im_ofNat]
      field_simp
      ring
  apply space_ext
  · simp only [fieldPaper, PiLp.toLp_apply, Matrix.cons_val_zero]
    rw [hB]
  · simp only [fieldPaper, PiLp.toLp_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [hB]
  · simp only [fieldPaper, PiLp.toLp_apply, Matrix.cons_val]
    rw [exp_neg_I, cos_Xip hx]
    simp only [field, vR, cz, sz, PiLp.toLp_apply, Matrix.cons_val]
    generalize Real.cos (lam * x 2) = c1
    generalize Real.sin (lam * x 2) = s1
    generalize Real.cos (sg ε x - S) = c2
    generalize Real.sin (sg ε x - S) = s2
    generalize Real.cosh (nu ε x) = c3
    generalize Real.sinh (nu ε x) = s3
    simp only [mul_re, neg_re, add_re, sub_re, ofReal_re, ofReal_im, mul_im, I_re, I_im, sub_im,
      add_im, neg_im]
    ring

/-- The paper's flux label (3.3): `ψ = (sin² λz + (Re(e^{-iλz} cos Ξ))²)/2`. -/
theorem psi_eq_paper (ε S lam : ℝ) {x : Space} (hx : x ∈ U ε) :
    psi ε S lam x = (Real.sin (lam * x 2) ^ 2 +
      ((exp (-I * (lam * x 2 : ℝ)) * cos (Xip ε S x)).re) ^ 2) / 2 := by
  have h : (exp (-I * (lam * x 2 : ℝ)) * cos (Xip ε S x)).re = -vR ε S lam x := by
    rw [exp_neg_I, cos_Xip hx]
    simp only [vR, cz, sz]
    generalize Real.cos (lam * x 2) = c1
    generalize Real.sin (lam * x 2) = s1
    generalize Real.cos (sg ε x - S) = c2
    generalize Real.sin (sg ε x - S) = s2
    generalize Real.cosh (nu ε x) = c3
    generalize Real.sinh (nu ε x) = s3
    simp only [mul_re, neg_re, add_re, sub_re, ofReal_re, ofReal_im, mul_im, I_re, I_im, sub_im,
      add_im, neg_im]
    ring
  rw [h, psi, sz]
  ring

end Paper

/-! ## The flux surfaces in `R` are nonempty -/

/-- Every surface `ψ = k²/2`, `0 ≤ k < 1`, meets `R` (for `S > 0`, `λ ≠ 0`): the point
`(a_c(S), 0, arcsin(k)/λ)` lies on it. Hence the hypotheses on positions in `LiftedLine` are
satisfiable. -/
theorem surface_nonempty {ε S lam k : ℝ} (hS : 0 < S) (hl : lam ≠ 0) (hk0 : 0 ≤ k)
    (hk1 : k < 1) : ∃ x ∈ R ε S lam, psi ε S lam x = k ^ 2 / 2 := by
  set x : Space := toLp 2 ![aC ε S, 0, Real.arcsin k / lam] with hxdef
  have hxy : (x 0, x 1) = ((axis ε S 0) 0, (axis ε S 0) 1) := by simp [hxdef, axis]
  have hZr : Zr ε x = Zr ε (axis ε S 0) := by
    unfold Zr r2
    simp only [Prod.mk.injEq] at hxy
    rw [hxy.1, hxy.2]
  have hZi : Zi ε x = Zi ε (axis ε S 0) := by
    unfold Zi
    simp only [Prod.mk.injEq] at hxy
    rw [hxy.1, hxy.2]
  have hsg : sg ε x = S := by
    rw [← sg_axis (ε := ε) hS 0]; unfold sg Mo; rw [hZr, hZi]
  have hU : x ∈ U ε := by
    have := axis_mem (ε := ε) hS 0
    change 0 < Mo ε x + Zr ε x
    unfold Mo; rw [hZr, hZi]; exact this
  have hnu : nu ε x = 0 := by
    unfold nu; simp [hxdef]
  have hz : lam * x 2 = Real.arcsin k := by simp [hxdef]; field_simp
  have harc1 : Real.arcsin k < Real.pi / 2 := Real.arcsin_lt_pi_div_two.mpr hk1
  have harc2 : -(Real.pi / 2) < Real.arcsin k := Real.neg_pi_div_two_lt_arcsin.mpr (by linarith)
  refine ⟨x, ⟨hU, by rw [hsg, sub_self, abs_zero]; positivity, ?_⟩, ?_⟩
  · rw [hz, abs_lt]; exact ⟨harc2, harc1⟩
  · simp only [psi, sz, vR, cz, hz, hsg, hnu, sub_self, Real.sin_zero, Real.sinh_zero, mul_zero,
      zero_mul, add_zero, Real.sin_arcsin (by linarith) hk1.le]
    ring

/-- Constructing a `LiftedLine` from initial data (for `ε = 1/4`, `S = 4`): by
`fieldLine_confined`, a field line starting in `R` on a surface `ψ = k²/2 ≤ 81/200` stays in
`R`. -/
theorem LiftedLine.of_start {lam k : ℝ} (hl : lam ≠ 0) (hk : k ^ 2 ≤ 81 / 100)
    {γ : ℝ → Space} {θ φ : ℝ → ℝ} (hγ : IsForwardFieldLine (field (1 / 4) 4 lam) γ)
    (h0 : γ 0 ∈ R (1 / 4) 4 lam) (hψ : psi (1 / 4) 4 lam (γ 0) = k ^ 2 / 2)
    (pol : ∀ t, 0 ≤ t → Xf (1 / 4) 4 lam (γ t) = -k * Real.cos (θ t) ∧
      Yf lam (γ t) = k * Real.sin (θ t))
    (tor : ∀ t, 0 ≤ t → γ t 0 = √(r2 (γ t)) * Real.cos (φ t) ∧
      γ t 1 = √(r2 (γ t)) * Real.sin (φ t))
    (pol_diff : ∀ t, 0 ≤ t → DifferentiableAt ℝ θ t)
    (tor_diff : ∀ t, 0 ≤ t → DifferentiableAt ℝ φ t) :
    LiftedLine (1 / 4) 4 lam k γ θ φ :=
  ⟨hγ, fun t ht => (fieldLine_confined hl hγ h0 (by rw [hψ]; linarith) ht).1, hψ, pol, tor,
    pol_diff, tor_diff⟩

/-! ## SI scaling and a realistic instance -/

/-- SI field `B(x) = B₀ B̂(x/L)` (field scale `B₀` in tesla, length scale `L` in metres). -/
@[expose] def fieldSI (B₀ L ε S lam : ℝ) (x : Space) : Space := B₀ • field ε S lam (L⁻¹ • x)

/-- SI Ampère current `J = (∇ × B)/μ₀` from the actual derivative. -/
@[expose] def currentSI (μ₀ B₀ L ε S lam : ℝ) (x : Space) : Space :=
  μ₀⁻¹ • curl (fderiv ℝ (fieldSI B₀ L ε S lam) x)

/-- SI pressure `p(x) = (B₀²/μ₀)(p̂_a - ψ(x/L)/λ²)`. -/
@[expose] def pressureSI (μ₀ B₀ L pa ε S lam : ℝ) (x : Space) : ℝ :=
  B₀ ^ 2 / μ₀ * (pa - psi ε S lam (L⁻¹ • x) / lam ^ 2)

/-- SI pressure gradient `-(B₀²/(μ₀ L λ²)) ∇̂ψ(x/L)`. -/
@[expose] def pressureGradSI (μ₀ B₀ L ε S lam : ℝ) (x : Space) : Space :=
  (-(B₀ ^ 2 / μ₀ * L⁻¹ / lam ^ 2)) • gradPsi ε S lam (L⁻¹ • x)

/-- Actual derivative of the SI field (chain rule through `x ↦ x/L`). -/
theorem fieldSI_hasFDerivAt (B₀ L ε S lam : ℝ) {x : Space} (hx : L⁻¹ • x ∈ U ε) :
    HasFDerivAt (fieldSI B₀ L ε S lam) ((B₀ * L⁻¹) • fieldDeriv ε S lam (L⁻¹ • x)) x := by
  have hlin : HasFDerivAt (fun y : Space => L⁻¹ • y) (L⁻¹ • ContinuousLinearMap.id ℝ Space) x :=
    (L⁻¹ • ContinuousLinearMap.id ℝ Space).hasFDerivAt
  have h := ((field_hasFDerivAt ε S lam hx).comp x hlin).const_smul B₀
  refine h.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.comp_smulₛₗ, map_inv₀, RingHom.id_apply,
      ContinuousLinearMap.comp_id, smul_smul, smul_apply, PiLp.smul_apply, smul_eq_mul]

/-- The SI pressure gradient is the actual derivative of the SI pressure. -/
theorem pressureSI_hasFDerivAt (μ₀ B₀ L pa ε S lam : ℝ) {x : Space} (hx : L⁻¹ • x ∈ U ε) :
    HasFDerivAt (pressureSI μ₀ B₀ L pa ε S lam)
      (innerSL ℝ (pressureGradSI μ₀ B₀ L ε S lam x)) x := by
  have hlin : HasFDerivAt (fun y : Space => L⁻¹ • y) (L⁻¹ • ContinuousLinearMap.id ℝ Space) x :=
    (L⁻¹ • ContinuousLinearMap.id ℝ Space).hasFDerivAt
  have h := ((((psi_hasFDerivAt ε S lam hx).comp x hlin).mul_const (lam ^ 2)⁻¹).const_sub
    pa).const_mul (B₀ ^ 2 / μ₀)
  refine hfd h (fun y => by simp only [pressureSI, div_eq_mul_inv]; rfl) ?_
  ext v
  simp only [ContinuousLinearMap.comp_smulₛₗ, map_inv₀, RingHom.id_apply,
      ContinuousLinearMap.comp_id, smul_neg, neg_apply, smul_apply, coe_innerSL_apply, smul_eq_mul,
      pressureGradSI, neg_smul, map_neg, map_smul, neg_inj]
  ring

open Matrix in
/-- **SI force balance** `J × B = ∇p` (domain-kernel law) for the scaled equilibrium, with the
actual Ampère current and actual pressure gradient, at every `x` with `x/L ∈ 𝒰`. -/
theorem force_balance_SI {ε S lam : ℝ} (hl : lam ≠ 0) (μ₀ B₀ L : ℝ) {x : Space}
    (hx : L⁻¹ • x ∈ U ε) :
    ForceBalance (ofLp (fieldSI B₀ L ε S lam x)) (ofLp (currentSI μ₀ B₀ L ε S lam x))
      (ofLp (pressureGradSI μ₀ B₀ L ε S lam x)) := by
  refine ⟨?_⟩
  have e : ofLp (currentSI μ₀ B₀ L ε S lam x) ⨯₃ ofLp (fieldSI B₀ L ε S lam x) =
      ofLp (cross (currentSI μ₀ B₀ L ε S lam x) (fieldSI B₀ L ε S lam x)) := by simp [cross]
  have hc : currentSI μ₀ B₀ L ε S lam x =
      (μ₀⁻¹ * (B₀ * L⁻¹)) • curl (fieldDeriv ε S lam (L⁻¹ • x)) := by
    rw [currentSI, (fieldSI_hasFDerivAt B₀ L ε S lam hx).fderiv, curl, map_smul, ← curl,
      smul_smul]
  have hcr (k m : ℝ) (u w : Space) : cross (k • u) (m • w) = (k * m) • cross u w := by
    rw [← crossBilinear_apply, map_smul, map_smul, _root_.smul_apply, crossBilinear_apply,
      smul_smul, mul_comm]
  rw [e, hc, fieldSI, hcr, curl_cross_eq, transport_key hl hx, pressureGradSI, smul_smul]
  congr 2
  field_simp

/-- `|B|² = cosh² ν/(4G)` on the magnetic axis. -/
theorem axis_field_normSq {ε S : ℝ} (hS : 0 < S) (lam ζ : ℝ) :
    ‖field ε S lam (axis ε S ζ)‖ ^ 2 =
      Real.cosh (ε * Real.cos ζ * Real.sin ζ) ^ 2 / (4 * Gax ε S ζ) := by
  have hG := Gax_pos (ε := ε) hS ζ
  rw [field_axis hS, norm_smul, mul_pow, EuclideanSpace.norm_sq_eq]
  have hv : ∑ i, ‖axisVel ε S ζ i‖ ^ 2 = Gax ε S ζ := by
    simp only [Fin.sum_univ_three, axisVel, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, Real.norm_eq_abs, sq_abs, Gax]
    ring
  rw [hv, Real.norm_eq_abs, abs_of_pos (by positivity)]
  field_simp
  ring

/-- Bounds on `G` for `ε = 1/4`, `S = 4`: `3.875 ≤ G ≤ 4.13`. -/
theorem Gax_bounds (ζ : ℝ) : 3875 / 1000 ≤ Gax (1 / 4) 4 ζ ∧ Gax (1 / 4) 4 ζ ≤ 413 / 100 := by
  have ha := aC_sq (ε := 1 / 4) (S := 4) (by norm_num)
  have hb := bC_sq (ε := 1 / 4) (S := 4) (by norm_num)
  have hh : hC (1 / 4) 4 ^ 2 = 4 * 4 ^ 2 + (1 / 4) ^ 2 := Real.sq_sqrt (by positivity)
  have hh0 : 0 ≤ hC (1 / 4) 4 := Real.sqrt_nonneg _
  have h1 : 8 ≤ hC (1 / 4) 4 := by nlinarith
  have h2 : hC (1 / 4) 4 ≤ 801 / 100 := by nlinarith
  have hcs := Real.cos_sq_add_sin_sq ζ
  unfold Gax
  constructor <;> nlinarith [sq_nonneg (Real.cos ζ), sq_nonneg (Real.sin ζ)]

/-- **Realistic SI instance** (`ε = 1/4`, `S = 4`, `λ = 15`, boundary surface `δ = 81/200`, the
outer surface of the shear theorem). With field scale `B₀ = 20 T`, any length scale `L > 0`
and `p_a = δ/λ²` (pressure vanishing on `ψ = δ`): on the magnetic axis `x = L γ(ζ)` the field
strength satisfies `24 ≤ |B|² ≤ 27` T² (`|B| ≈ 4.9–5.2 T`) and the local beta
`2μ₀p/|B|²` lies in `[1/20, 1/16]` (5 %–6.25 %). Force balance holds by `force_balance_SI`
and the shear theorem `shear` holds for every `λ ≠ 0`. -/
theorem realistic_instance (μ₀ L : ℝ) (hμ : 0 < μ₀) (hL : 0 < L) (ζ : ℝ) :
    24 ≤ ‖fieldSI 20 L (1 / 4) 4 15 (L • axis (1 / 4) 4 ζ)‖ ^ 2 ∧
    ‖fieldSI 20 L (1 / 4) 4 15 (L • axis (1 / 4) 4 ζ)‖ ^ 2 ≤ 27 ∧
    1 / 20 ≤ 2 * μ₀ * pressureSI μ₀ 20 L (81 / 200 / 15 ^ 2) (1 / 4) 4 15 (L • axis (1 / 4) 4 ζ) /
      ‖fieldSI 20 L (1 / 4) 4 15 (L • axis (1 / 4) 4 ζ)‖ ^ 2 ∧
    2 * μ₀ * pressureSI μ₀ 20 L (81 / 200 / 15 ^ 2) (1 / 4) 4 15 (L • axis (1 / 4) 4 ζ) /
      ‖fieldSI 20 L (1 / 4) 4 15 (L • axis (1 / 4) 4 ζ)‖ ^ 2 ≤ 1 / 16 := by
  have hLx : L⁻¹ • (L • axis (1 / 4) 4 ζ) = axis (1 / 4) 4 ζ := by
    rw [smul_smul, inv_mul_cancel₀ hL.ne', one_smul]
  obtain ⟨hG1, hG2⟩ := Gax_bounds ζ
  set c := Real.cosh (1 / 4 * Real.cos ζ * Real.sin ζ) with hc
  have hc1 : 1 ≤ c := Real.one_le_cosh _
  have hc2 : c ≤ 1 + 1 / 127 := by
    refine (Real.cosh_le_cosh.mpr ?_).trans cosh_eighth_le
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)]
    have h1 := Real.abs_cos_le_one ζ
    have h2 := Real.abs_sin_le_one ζ
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    have : |Real.cos ζ| * |Real.sin ζ| ≤ 1 / 2 := by
      have := Real.cos_sq_add_sin_sq ζ
      nlinarith [sq_abs (Real.cos ζ), sq_abs (Real.sin ζ),
        sq_nonneg (|Real.cos ζ| - |Real.sin ζ|)]
    nlinarith [abs_nonneg (Real.cos ζ), abs_nonneg (Real.sin ζ)]
  have hB : ‖fieldSI 20 L (1 / 4) 4 15 (L • axis (1 / 4) 4 ζ)‖ ^ 2 =
      400 * (c ^ 2 / (4 * Gax (1 / 4) 4 ζ)) := by
    rw [fieldSI, hLx, norm_smul, mul_pow, axis_field_normSq (by norm_num), ← hc]
    norm_num
  have hp : pressureSI μ₀ 20 L (81 / 200 / 15 ^ 2) (1 / 4) 4 15 (L • axis (1 / 4) 4 ζ) =
      400 / μ₀ * (81 / 200 / 225) := by
    rw [pressureSI, hLx, psi_axis (by norm_num)]; norm_num
  have hGpos : 0 < Gax (1 / 4) 4 ζ := by linarith
  rw [hB, hp]
  have hBpos : 0 < 400 * (c ^ 2 / (4 * Gax (1 / 4) 4 ζ)) := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show 400 * (c ^ 2 / (4 * Gax (1 / 4) 4 ζ)) = 100 * c ^ 2 / Gax (1 / 4) 4 ζ by ring,
      le_div_iff₀ hGpos]
    nlinarith
  · rw [show 400 * (c ^ 2 / (4 * Gax (1 / 4) 4 ζ)) = 100 * c ^ 2 / Gax (1 / 4) 4 ζ by ring,
      div_le_iff₀ hGpos]
    nlinarith
  · rw [le_div_iff₀ hBpos]
    field_simp
    nlinarith
  · rw [div_le_iff₀ hBpos]
    field_simp
    nlinarith

/-! ## Summary -/

/-- **Landreman family 2** (arXiv:2609.26742 v2, §3; unrefereed preprint), for `ε > 0`, `S > 0`,
`λ ≠ 0`:
1. the real-variable field is the paper's complex formula (3.2) on `𝒰`;
2. `∇ · B = 0` and the kernel law `J × B = ∇p` (actual Ampère current, any `μ₀`) on `𝒰`;
3. `B · ∇ψ = 0` and `J · ∇ψ = 0` on `𝒰`, with `ψ` the paper's (3.3);
4. the magnetic axis (3.20) is a planar, non-circular ellipse with `ψ = 0`, and it is an
   integral curve of `B` up to a positive time change;
5. for `ε(S + ε) ≤ 3S` the field is not axisymmetric. -/
theorem family2 {ε S lam : ℝ} (hε : 0 < ε) (hS : 0 < S) (hl : lam ≠ 0) :
    (∀ x ∈ U ε, field ε S lam x = fieldPaper ε S lam x) ∧
    (∀ x ∈ U ε, divergence (fderiv ℝ (field ε S lam) x) = 0) ∧
    (∀ μ₀, ∀ x ∈ U ε, ForceBalance (ofLp (field ε S lam x)) (ofLp (current μ₀ ε S lam x))
      (ofLp (pressureGrad μ₀ ε S lam x))) ∧
    (∀ μ₀, ∀ x ∈ U ε, ⟪field ε S lam x, gradPsi ε S lam x⟫ = 0 ∧
      ⟪current μ₀ ε S lam x, gradPsi ε S lam x⟫ = 0) ∧
    (∀ ζ, psi ε S lam (axis ε S ζ) = 0 ∧ axis ε S ζ 2 = 0 ∧
      HasDerivAt (axis ε S) ((2 * Gax ε S ζ / Real.cosh (ε * Real.cos ζ * Real.sin ζ)) •
        field ε S lam (axis ε S ζ)) ζ) ∧ aC ε S ≠ bC ε S ∧
    (ε * (S + ε) ≤ 3 * S → ¬ ∀ x ∈ U ε, field ε S lam (rotQ x) = rotQ (field ε S lam x)) :=
  ⟨fun _ hx => field_eq_paper ε S lam hx, fun _ hx => field_divergence_free hl hx,
    fun μ₀ _ hx => force_balance hl μ₀ hx,
    fun μ₀ _ hx => ⟨field_tangent_psi hl hx, current_tangent_psi hl μ₀ hx⟩,
    fun ζ => ⟨psi_axis hS lam ζ, axis_planar ζ, axis_tangent hS lam ζ⟩, axis_not_circle hS hε.ne',
    fun h => field_not_axisymmetric hε hS h hl⟩

/-- **Confinement and shear for `ε = 1/4`, `S = 4`** (any `λ ≠ 0`): field lines starting in
`R` with `ψ ≤ 81/200` stay in `R` for all time on their flux surface; and the rotational
transform is sheared between the surfaces `ψ = 1/800` and `ψ = 81/200`:
`ι(1/800) ≤ 25/3 < 17/2 ≤ ι(81/200)` (`rotTransform_sheared`, `shear`). -/
theorem family2_shear {lam : ℝ} (hl : lam ≠ 0) :
    (∀ γ : ℝ → Space, IsForwardFieldLine (field (1 / 4) 4 lam) γ → γ 0 ∈ R (1 / 4) 4 lam →
      psi (1 / 4) 4 lam (γ 0) ≤ 81 / 200 → ∀ t, 0 ≤ t →
        γ t ∈ R (1 / 4) 4 lam ∧ psi (1 / 4) 4 lam (γ t) = psi (1 / 4) 4 lam (γ 0)) ∧
    (∀ (γ₁ γ₂ : ℝ → Space) (θ₁ φ₁ θ₂ φ₂ : ℝ → ℝ) (ι₁ ι₂ : ℝ),
      LiftedLine (1 / 4) 4 lam (1 / 20) γ₁ θ₁ φ₁ → LiftedLine (1 / 4) 4 lam (9 / 10) γ₂ θ₂ φ₂ →
      HasRotTransform θ₁ φ₁ ι₁ → HasRotTransform θ₂ φ₂ ι₂ → ι₁ < ι₂) :=
  ⟨fun _ hγ h0 hψ _ ht => fieldLine_confined hl hγ h0 hψ ht,
    fun _ _ _ _ _ _ _ _ L₁ L₂ h₁ h₂ => (rotTransform_sheared hl L₁ L₂ h₁ h₂).2.2⟩

end PlasmaLean.Design.LandremanFamily2
