/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2

/-!
# Landreman family 2: closed forms of `B`, `∇ψ` and `J` on each flux surface

Source: M. Landreman, *Analytic toroidal 3D MHD equilibria and steady Euler flows with
invariant surfaces*, arXiv:2609.26742 **v2**, §3 (an unrefereed preprint; every identity below
is re-proved from the definitions in `PlasmaLean.Design.LandremanFamily2`). These closed forms
are the inputs of a validated-quadrature Mercier certificate.

## Parametrization of the surface `ψ = k²/2`

With `s1, c1 = sin χ, cos χ` and `s2, c2 = sin 2ζ, cos 2ζ`: `Y = k s1`, `X = k c1`,
`cc = √(1 - Y²)`, `ν = (ε/2) s2`, `T = √(cosh² ν - k²)`, `T₀ = cosh² ν - Y²`,
`sA = (cc cosh ν X + Y sinh ν T)/T₀`, `cA = (cc cosh ν T - Y sinh ν X)/T₀`,
`uIc = (Y cc T - cosh ν sinh ν X)/T₀`, `σ = S + arcsin sA`, `h = √(4σ² + ε²)`,
`m = (h - ε c2)/2`, `q = σ² + ν²`, `r = m²/q`, and
`Bsq = (T² + uIc²)(m/q)/4 + X²/λ²`, `gX2 = (q/m)(T²(1+r)² + uIc²(1-r)²)`,
`gp2 = X² gX2 + λ² T² uIc²`, `BD = (T²(1+r) - uIc²(1-r))/(2λ)`.
The point `surfPt ε S λ k χ ζ = (a_c(σ) cos ζ, b_c(σ) sin ζ, -arcsin(k sin χ)/λ)` has the
horizontal position of the axis ellipse (paper (3.20)) of parameter `σ` (paper (3.9)–(3.15)).

## Proved

* `curl_fieldDeriv`: on `𝒰`, `∇ × B = λ B + Δ` with `Δ = λ⁻¹(-∂_y Re v, ∂ₓ Re v, 0)`
  (`∂_z(B_x + iB_y) = -iλ(B_x + iB_y)` and `∂ₓB_y - ∂_yB_x = λB_z`), for the actual Fréchet
  derivative; hence `μ₀ J - I' B = (λ - I') B + Δ` (`Xi_eq`).
* For `ε = 1/4`, `S = 4`, every `λ ≠ 0`, `0 < k ≤ 19/20` and all angles `χ, ζ`:
  `surfPt_mem_U`, `psi_surfPt` (`ψ = k²/2`), `normSq_field_surfPt` (`|B|² = Bsq`),
  `normSq_gradPsi_surfPt` (`|∇ψ|² = gp2`), and for every `μ₀ ≠ 0`, `I'`,
  `inner_field_Xi_surfPt` (`⟪B, Ξ⟫ = (λ - I') Bsq + BD`) and `normSq_Xi_surfPt`
  (`|Ξ|² = (λ - I')² Bsq + 2(λ - I') BD + gX2/λ²`). The `_of` versions hold for every `ε`,
  every `S ≥ 2`, `k² < 1`, under the hypothesis `cA > 0`.
* Positivity and identities of the closed forms for arbitrary `(s1, c1)` on the unit circle:
  `T0_pos`, `cc_pos`, `T_pos`, `sA_sq_add_cA_sq`, `sA_sq_add_uIc_sq`, `abs_sA_le`,
  `cA_pos` (`ε = 1/4`, `|s2| ≤ 1`, `0 < k ≤ 19/20`), `sigma_pos` (`S ≥ 2`), `m_pos`, `G_pos`
  (`|c2| ≤ 1`), `q_pos`, `gX2_pos`, `gp2_pos`, `Bsq_pos`.

## Scope

Pointwise identities only: no claim that `surfPt` covers the surface exactly once, and no
quadrature or Mercier verdict is made here.
-/

open scoped RealInnerProductSpace

public section
noncomputable section
namespace PlasmaLean.Design.LandremanFamily2Surface
open PlasmaLean.Fields WithLp
open PlasmaLean.Design.LandremanFamily2
open PlasmaLean.Design.LandremanEquilibrium (inner_coords)

/-! ## Closed-form building blocks

Throughout, `s1, c1` stand for `sin χ, cos χ` and `s2, c2` for `sin 2ζ, cos 2ζ`. -/

/-- `Y = k sin χ` (paper (3.13): `Y = -sin λz = k sin χ` on the surface `ψ = k²/2`). -/
@[expose] def Yc (k s1 : ℝ) : ℝ := k * s1

/-- `X = k cos χ` (paper (3.13): `X = λ B_z`). -/
@[expose] def Xc (k c1 : ℝ) : ℝ := k * c1

/-- `cos λz = √(1 - Y²)`. -/
@[expose] def cc (k s1 : ℝ) : ℝ := √(1 - Yc k s1 ^ 2)

/-- `ν = (ε/2) sin 2ζ` (paper (3.10)). -/
@[expose] def nuc (ε s2 : ℝ) : ℝ := ε / 2 * s2

/-- `cosh ν`. -/
@[expose] def chc (ε s2 : ℝ) : ℝ := Real.cosh (nuc ε s2)

/-- `sinh ν`. -/
@[expose] def shc (ε s2 : ℝ) : ℝ := Real.sinh (nuc ε s2)

/-- `T = √(cosh² ν - k²)` (paper (3.17)). -/
@[expose] def Tc (ε k s2 : ℝ) : ℝ := √(chc ε s2 ^ 2 - k ^ 2)

/-- `T₀ = cosh² ν - Y²`. -/
@[expose] def T0c (ε k s1 s2 : ℝ) : ℝ := chc ε s2 ^ 2 - Yc k s1 ^ 2

/-- `sin(σ - S)` on the surface. -/
@[expose] def sA (ε k s1 c1 s2 : ℝ) : ℝ :=
  (cc k s1 * chc ε s2 * Xc k c1 + Yc k s1 * shc ε s2 * Tc ε k s2) / T0c ε k s1 s2

/-- `cos(σ - S)` on the surface. -/
@[expose] def cA (ε k s1 c1 s2 : ℝ) : ℝ :=
  (cc k s1 * chc ε s2 * Tc ε k s2 - Yc k s1 * shc ε s2 * Xc k c1) / T0c ε k s1 s2

/-- `Im u` on the surface. -/
@[expose] def uIc (ε k s1 c1 s2 : ℝ) : ℝ :=
  (Yc k s1 * cc k s1 * Tc ε k s2 - chc ε s2 * shc ε s2 * Xc k c1) / T0c ε k s1 s2

/-- `Im v` on the surface. -/
@[expose] def vIc (ε k s1 c1 s2 : ℝ) : ℝ :=
  (shc ε s2 * chc ε s2 * Tc ε k s2 + cc k s1 * Yc k s1 * Xc k c1) / T0c ε k s1 s2

/-- `σ = S + arcsin(sin(σ - S))` on the surface. -/
@[expose] def sigc (ε S k s1 c1 s2 : ℝ) : ℝ := S + Real.arcsin (sA ε k s1 c1 s2)

/-- `h = √(4σ² + ε²)` (paper (3.9) with `S` replaced by `σ`). -/
@[expose] def hc (ε S k s1 c1 s2 : ℝ) : ℝ := √(4 * sigc ε S k s1 c1 s2 ^ 2 + ε ^ 2)

/-- `m = (h - ε cos 2ζ)/2`, equal to `r² = x² + y²` on the surface. -/
@[expose] def mc (ε S k s1 c1 s2 c2 : ℝ) : ℝ := (hc ε S k s1 c1 s2 - ε * c2) / 2

/-- `G = (h + ε cos 2ζ)/2` (paper (3.16)). -/
@[expose] def Gc (ε S k s1 c1 s2 c2 : ℝ) : ℝ := (hc ε S k s1 c1 s2 + ε * c2) / 2

/-- `q = σ² + ν² = |P|²`. -/
@[expose] def qc (ε S k s1 c1 s2 : ℝ) : ℝ := sigc ε S k s1 c1 s2 ^ 2 + nuc ε s2 ^ 2

/-- `r = m²/q`. -/
@[expose] def rc (ε S k s1 c1 s2 c2 : ℝ) : ℝ := mc ε S k s1 c1 s2 c2 ^ 2 / qc ε S k s1 c1 s2

/-- Closed form of `|B|²` on the surface. -/
@[expose] def Bsq (ε S lam k s1 c1 s2 c2 : ℝ) : ℝ :=
  (Tc ε k s2 ^ 2 + uIc ε k s1 c1 s2 ^ 2) * (mc ε S k s1 c1 s2 c2 / qc ε S k s1 c1 s2) / 4 +
    Xc k c1 ^ 2 / lam ^ 2

/-- Closed form of `(∂ₓ Re v)² + (∂_y Re v)²` on the surface. -/
@[expose] def gX2 (ε S k s1 c1 s2 c2 : ℝ) : ℝ :=
  (qc ε S k s1 c1 s2 / mc ε S k s1 c1 s2 c2) *
    (Tc ε k s2 ^ 2 * (1 + rc ε S k s1 c1 s2 c2) ^ 2 +
      uIc ε k s1 c1 s2 ^ 2 * (1 - rc ε S k s1 c1 s2 c2) ^ 2)

/-- Closed form of `|∇ψ|²` on the surface. -/
@[expose] def gp2 (ε S lam k s1 c1 s2 c2 : ℝ) : ℝ :=
  Xc k c1 ^ 2 * gX2 ε S k s1 c1 s2 c2 + lam ^ 2 * Tc ε k s2 ^ 2 * uIc ε k s1 c1 s2 ^ 2

/-- Closed form of `⟪B, Δ⟫` on the surface. -/
@[expose] def BD (ε S lam k s1 c1 s2 c2 : ℝ) : ℝ :=
  (Tc ε k s2 ^ 2 * (1 + rc ε S k s1 c1 s2 c2) -
    uIc ε k s1 c1 s2 ^ 2 * (1 - rc ε S k s1 c1 s2 c2)) / (2 * lam)

/-- The point of the flux surface `ψ = k²/2` with angles `(χ, ζ)`: its first two coordinates
are those of the magnetic axis `axis ε σ ζ` of the parameter `σ`, and `λz = -arcsin(k sin χ)`. -/
@[expose] def surfPt (ε S lam k χ ζ : ℝ) : Space :=
  toLp 2 ![aC ε (sigc ε S k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ))) * Real.cos ζ,
    bC ε (sigc ε S k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ))) * Real.sin ζ,
    -Real.arcsin (k * Real.sin χ) / lam]

/-! ## Identities and bounds for the closed forms -/

section ClosedForm
variable {ε S lam k s1 c1 s2 c2 : ℝ}

/-- `X² + Y² = k²` on the circle `s1² + c1² = 1`. -/
theorem Xc_sq_add_Yc_sq (h1 : s1 ^ 2 + c1 ^ 2 = 1) : Xc k c1 ^ 2 + Yc k s1 ^ 2 = k ^ 2 := by
  unfold Xc Yc; linear_combination k ^ 2 * h1

/-- `Y² ≤ k²`. -/
theorem Yc_sq_le (h1 : s1 ^ 2 + c1 ^ 2 = 1) : Yc k s1 ^ 2 ≤ k ^ 2 := by
  have := Xc_sq_add_Yc_sq (k := k) h1; nlinarith [sq_nonneg (Xc k c1)]

/-- `cosh ν ≥ 1`. -/
theorem one_le_chc : 1 ≤ chc ε s2 := Real.one_le_cosh _

/-- `cosh² ν - sinh² ν = 1`. -/
theorem chc_sq_sub_shc_sq : chc ε s2 ^ 2 - shc ε s2 ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq _

/-- `cos² λz = 1 - Y²`. -/
theorem cc_sq (h1 : s1 ^ 2 + c1 ^ 2 = 1) (hk : k ^ 2 < 1) : cc k s1 ^ 2 = 1 - Yc k s1 ^ 2 :=
  Real.sq_sqrt (by linarith [Yc_sq_le (k := k) h1])

/-- `cos λz > 0`. -/
theorem cc_pos (h1 : s1 ^ 2 + c1 ^ 2 = 1) (hk : k ^ 2 < 1) : 0 < cc k s1 :=
  Real.sqrt_pos.mpr (by linarith [Yc_sq_le (k := k) h1])

/-- `T² = cosh² ν - k²`. -/
theorem Tc_sq (hk : k ^ 2 < 1) : Tc ε k s2 ^ 2 = chc ε s2 ^ 2 - k ^ 2 :=
  Real.sq_sqrt (by nlinarith [one_le_chc (ε := ε) (s2 := s2)])

/-- `T > 0`. -/
theorem T_pos (hk : k ^ 2 < 1) : 0 < Tc ε k s2 :=
  Real.sqrt_pos.mpr (by nlinarith [one_le_chc (ε := ε) (s2 := s2)])

/-- `T₀ > 0`. -/
theorem T0_pos (h1 : s1 ^ 2 + c1 ^ 2 = 1) (hk : k ^ 2 < 1) : 0 < T0c ε k s1 s2 := by
  unfold T0c; nlinarith [one_le_chc (ε := ε) (s2 := s2), Yc_sq_le (k := k) h1]

/-- `sin²(σ - S) + cos²(σ - S) = 1` for the closed forms. -/
theorem sA_sq_add_cA_sq (h1 : s1 ^ 2 + c1 ^ 2 = 1) (hk : k ^ 2 < 1) :
    sA ε k s1 c1 s2 ^ 2 + cA ε k s1 c1 s2 ^ 2 = 1 := by
  have hT0 := (T0_pos (ε := ε) (s2 := s2) h1 hk).ne'
  have hcc := cc_sq h1 hk
  have hch := chc_sq_sub_shc_sq (ε := ε) (s2 := s2)
  have hT := Tc_sq (ε := ε) (s2 := s2) hk
  have hXY := Xc_sq_add_Yc_sq (k := k) h1
  unfold sA cA
  unfold T0c at hT0 ⊢
  generalize cc k s1 = a at *
  generalize chc ε s2 = ch at *
  generalize shc ε s2 = sh at *
  generalize Tc ε k s2 = T at *
  generalize Xc k c1 = X at *
  generalize Yc k s1 = Y at *
  field_simp
  linear_combination (ch ^ 2 - Y ^ 2 + (X ^ 2 + T ^ 2 - (ch ^ 2 - Y ^ 2))) *
    (ch ^ 2 * hcc - Y ^ 2 * hch) + (ch ^ 2 - Y ^ 2) * (hXY + hT)

/-- `sin²(σ - S) + (Im u)² = k²` for the closed forms. -/
theorem sA_sq_add_uIc_sq (h1 : s1 ^ 2 + c1 ^ 2 = 1) (hk : k ^ 2 < 1) :
    sA ε k s1 c1 s2 ^ 2 + uIc ε k s1 c1 s2 ^ 2 = k ^ 2 := by
  have hT0 := (T0_pos (ε := ε) (s2 := s2) h1 hk).ne'
  have hcc := cc_sq h1 hk
  have hch := chc_sq_sub_shc_sq (ε := ε) (s2 := s2)
  have hT := Tc_sq (ε := ε) (s2 := s2) hk
  have hXY := Xc_sq_add_Yc_sq (k := k) h1
  unfold sA uIc
  unfold T0c at hT0 ⊢
  generalize cc k s1 = a at *
  generalize chc ε s2 = ch at *
  generalize shc ε s2 = sh at *
  generalize Tc ε k s2 = T at *
  generalize Xc k c1 = X at *
  generalize Yc k s1 = Y at *
  field_simp
  linear_combination (ch ^ 2 - Y ^ 2) * (ch ^ 2 * hXY + Y ^ 2 * hT) +
    (X ^ 2 * ch ^ 2 + Y ^ 2 * T ^ 2) * (hcc - hch)

/-- `|sin(σ - S)| ≤ k`. -/
theorem abs_sA_le (h1 : s1 ^ 2 + c1 ^ 2 = 1) (hk0 : 0 ≤ k) (hk : k ^ 2 < 1) :
    |sA ε k s1 c1 s2| ≤ k := by
  have := sA_sq_add_uIc_sq (ε := ε) (s2 := s2) h1 hk
  exact abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (uIc ε k s1 c1 s2)]) hk0

/-- `|sinh ν| ≤ 251/2000` for `ε = 1/4`, `|sin 2ζ| ≤ 1`. -/
theorem abs_shc_le (hs2 : |s2| ≤ 1) : |shc (1 / 4) s2| ≤ 251 / 2000 := by
  unfold shc nuc
  rw [Real.abs_sinh]
  refine (Real.sinh_le_sinh.mpr ?_).trans sinh_eighth_le
  rw [abs_mul]; norm_num; linarith

/-- `cos(σ - S) > 0` for `ε = 1/4`, `0 < k ≤ 19/20`. -/
theorem cA_pos (h1 : s1 ^ 2 + c1 ^ 2 = 1) (hs2 : |s2| ≤ 1) (hk0 : 0 < k) (hk1 : k ≤ 19 / 20) :
    0 < cA (1 / 4) k s1 c1 s2 := by
  have hk : k ^ 2 < 1 := by nlinarith
  have hT0 := T0_pos (ε := 1 / 4) (s2 := s2) h1 hk
  have hcc := cc_sq h1 hk
  have hcc0 := (cc_pos h1 hk).le
  have hT := Tc_sq (ε := 1 / 4) (s2 := s2) hk
  have hT00 := (T_pos (ε := 1 / 4) (s2 := s2) hk).le
  have hXY := Xc_sq_add_Yc_sq (k := k) h1
  have hch := one_le_chc (ε := 1 / 4) (s2 := s2)
  have hsh := abs_shc_le hs2
  unfold cA
  apply div_pos _ hT0
  generalize cc k s1 = a at *
  generalize chc (1 / 4) s2 = ch at *
  generalize shc (1 / 4) s2 = sh at *
  generalize Tc (1 / 4) k s2 = T at *
  generalize Xc k c1 = X at *
  generalize Yc k s1 = Y at *
  have haT : 1 - k ^ 2 ≤ a * T := by
    have hsq : (1 - k ^ 2) ^ 2 ≤ (a * T) ^ 2 := by
      have e1 : 1 - k ^ 2 ≤ 1 - Y ^ 2 := by nlinarith [sq_nonneg X]
      have e2 : 1 - k ^ 2 ≤ ch ^ 2 - k ^ 2 := by nlinarith
      rw [mul_pow, hcc, hT, sq]
      exact mul_le_mul e1 e2 (by linarith) (by linarith)
    exact (pow_le_pow_iff_left₀ (by linarith) (by positivity) two_ne_zero).mp hsq
  have h2 : a * T ≤ a * ch * T := by nlinarith [mul_nonneg hcc0 hT00]
  have hYX : |Y * X| ≤ k ^ 2 / 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (Y + X), sq_nonneg (Y - X)]
  have h3 : |Y * sh * X| ≤ 251 / 2000 * (k ^ 2 / 2) := by
    rw [show Y * sh * X = sh * (Y * X) by ring, abs_mul]
    exact mul_le_mul hsh hYX (abs_nonneg _) (by norm_num)
  have h4 := le_abs_self (Y * sh * X)
  nlinarith

/-- `σ > 0` as soon as `S ≥ 2` (since `arcsin ≥ -π/2`). -/
theorem sigma_pos (hS : 2 ≤ S) : 0 < sigc ε S k s1 c1 s2 := by
  unfold sigc
  linarith [Real.neg_pi_div_two_le_arcsin (sA ε k s1 c1 s2), Real.pi_lt_four]

/-- `h > |ε|` (for `σ > 0`). -/
theorem abs_lt_hc (hS : 2 ≤ S) : |ε| < hc ε S k s1 c1 s2 :=
  hC_gt (sigma_pos hS)

/-- `h > 0`. -/
theorem hc_pos (hS : 2 ≤ S) : 0 < hc ε S k s1 c1 s2 :=
  lt_of_le_of_lt (abs_nonneg ε) (abs_lt_hc hS)

/-- `m > 0` (for `|cos 2ζ| ≤ 1`). -/
theorem m_pos (hS : 2 ≤ S) (hc2 : |c2| ≤ 1) : 0 < mc ε S k s1 c1 s2 c2 := by
  have h := abs_lt_hc (ε := ε) (k := k) (s1 := s1) (c1 := c1) (s2 := s2) hS
  have : ε * c2 ≤ |ε| := by
    calc ε * c2 ≤ |ε * c2| := le_abs_self _
      _ = |ε| * |c2| := abs_mul _ _
      _ ≤ |ε| := mul_le_of_le_one_right (abs_nonneg _) hc2
  unfold mc; linarith

/-- `G > 0` (for `|cos 2ζ| ≤ 1`). -/
theorem G_pos (hS : 2 ≤ S) (hc2 : |c2| ≤ 1) : 0 < Gc ε S k s1 c1 s2 c2 := by
  have h := abs_lt_hc (ε := ε) (k := k) (s1 := s1) (c1 := c1) (s2 := s2) hS
  have : -|ε| ≤ ε * c2 := by
    have : |ε * c2| ≤ |ε| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hc2
    linarith [neg_abs_le (ε * c2)]
  unfold Gc; linarith

/-- `q > 0`. -/
theorem q_pos (hS : 2 ≤ S) : 0 < qc ε S k s1 c1 s2 := by
  have := sigma_pos (ε := ε) (k := k) (s1 := s1) (c1 := c1) (s2 := s2) hS
  unfold qc; positivity

/-- `r ≥ 0`. -/
theorem r_nonneg (hS : 2 ≤ S) : 0 ≤ rc ε S k s1 c1 s2 c2 := by
  have := q_pos (ε := ε) (k := k) (s1 := s1) (c1 := c1) (s2 := s2) hS
  unfold rc; positivity

/-- `(∂ₓ Re v)² + (∂_y Re v)² > 0` in closed form. -/
theorem gX2_pos (hS : 2 ≤ S) (hc2 : |c2| ≤ 1) (hk : k ^ 2 < 1) :
    0 < gX2 ε S k s1 c1 s2 c2 := by
  have hq := q_pos (ε := ε) (k := k) (s1 := s1) (c1 := c1) (s2 := s2) hS
  have hm := m_pos (ε := ε) (k := k) (s1 := s1) (c1 := c1) (s2 := s2) hS hc2
  have hr := r_nonneg (ε := ε) (k := k) (s1 := s1) (c1 := c1) (s2 := s2) (c2 := c2) hS
  have hT := T_pos (ε := ε) (s2 := s2) hk
  unfold gX2
  have : 0 < Tc ε k s2 ^ 2 * (1 + rc ε S k s1 c1 s2 c2) ^ 2 := by positivity
  have : 0 < qc ε S k s1 c1 s2 / mc ε S k s1 c1 s2 c2 := by positivity
  positivity

/-- `|∇ψ|² > 0` in closed form (for `λ ≠ 0`, `0 < k`). -/
theorem gp2_pos (h1 : s1 ^ 2 + c1 ^ 2 = 1) (hS : 2 ≤ S) (hc2 : |c2| ≤ 1) (hk0 : 0 < k)
    (hk : k ^ 2 < 1) (hl : lam ≠ 0) : 0 < gp2 ε S lam k s1 c1 s2 c2 := by
  have hg := gX2_pos (ε := ε) (k := k) (s1 := s1) (c1 := c1) (s2 := s2) (c2 := c2) hS hc2 hk
  unfold gp2
  by_cases hX : Xc k c1 = 0
  · have hY : Yc k s1 ^ 2 = k ^ 2 := by
      have := Xc_sq_add_Yc_sq (k := k) h1; rw [hX] at this; linarith
    have hY0 : Yc k s1 ≠ 0 := by
      intro h; rw [h] at hY; nlinarith
    have hu : uIc ε k s1 c1 s2 ≠ 0 := by
      unfold uIc
      rw [hX, mul_zero, sub_zero]
      exact div_ne_zero (mul_ne_zero (mul_ne_zero hY0 (cc_pos h1 hk).ne') (T_pos hk).ne')
        (T0_pos h1 hk).ne'
    have := T_pos (ε := ε) (s2 := s2) hk
    rw [hX]; positivity
  · have : 0 < Xc k c1 ^ 2 * gX2 ε S k s1 c1 s2 c2 := by positivity
    positivity

/-- `|B|² > 0` in closed form (for `λ ≠ 0`). -/
theorem Bsq_pos (hS : 2 ≤ S) (hc2 : |c2| ≤ 1) (hk : k ^ 2 < 1) :
    0 < Bsq ε S lam k s1 c1 s2 c2 := by
  have hq := q_pos (ε := ε) (k := k) (s1 := s1) (c1 := c1) (s2 := s2) hS
  have hm := m_pos (ε := ε) (k := k) (s1 := s1) (c1 := c1) (s2 := s2) hS hc2
  have hT := T_pos (ε := ε) (s2 := s2) hk
  unfold Bsq
  have : 0 < (Tc ε k s2 ^ 2 + uIc ε k s1 c1 s2 ^ 2) * (mc ε S k s1 c1 s2 c2 /
    qc ε S k s1 c1 s2) / 4 := by positivity
  positivity

/-- The coefficient identity `(T² c₊² + U² c₋²) q m = gX2` with `c± = 1/m ± m/q`. -/
theorem gX2_eq (hS : 2 ≤ S) (hc2 : |c2| ≤ 1) (T U : ℝ) :
    (T ^ 2 * (1 / mc ε S k s1 c1 s2 c2 + mc ε S k s1 c1 s2 c2 / qc ε S k s1 c1 s2) ^ 2 +
      U ^ 2 * (1 / mc ε S k s1 c1 s2 c2 - mc ε S k s1 c1 s2 c2 / qc ε S k s1 c1 s2) ^ 2) *
        qc ε S k s1 c1 s2 * mc ε S k s1 c1 s2 c2 =
      (qc ε S k s1 c1 s2 / mc ε S k s1 c1 s2 c2) *
        (T ^ 2 * (1 + rc ε S k s1 c1 s2 c2) ^ 2 + U ^ 2 * (1 - rc ε S k s1 c1 s2 c2) ^ 2) := by
  have hq := (q_pos (ε := ε) (k := k) (s1 := s1) (c1 := c1) (s2 := s2) hS).ne'
  have hm := (m_pos (ε := ε) (k := k) (s1 := s1) (c1 := c1) (s2 := s2) hS hc2).ne'
  unfold rc
  field_simp

end ClosedForm

/-! ## The curl of the field: `μ₀ J = λ B + Δ` -/

/-- The correction `Δ = λ⁻¹ (-∂_y Re v, ∂ₓ Re v, 0) = ∇B_z × ẑ` (since `B_z = -Re v/λ`). -/
@[expose] def Delta (ε S lam : ℝ) (x : Space) : Space :=
  lam⁻¹ • toLp 2 ![-(dvR ε S lam x (basis 1)), dvR ε S lam x (basis 0), 0]

/-- **Key identity** on `𝒰`: `∇ × B = λ B + Δ` for the actual derivative `fieldDeriv` (from
`∂_z(B_x + iB_y) = -iλ(B_x + iB_y)` and `∂ₓ B_y - ∂_y B_x = -Re v = λ B_z`). -/
theorem curl_fieldDeriv {ε S lam : ℝ} (hl : lam ≠ 0) {x : Space} (hx : x ∈ U ε) :
    curl (fieldDeriv ε S lam x) = lam • field ε S lam x + Delta ε S lam x := by
  have hr := (r2_pos hx).ne'
  have hm := (Mq_pos hx).ne'
  obtain ⟨c0, c1, c2⟩ := curl_coords (fieldDeriv ε S lam x)
  apply space_ext
  · rw [c0]
    simp only [Fin.isValue, fieldDeriv, dQuot, mul_inv_rev, dN0, duR, dsg, cp, one_div, smul_add,
      dnu, cm, dbe, duI, dal, neg_add_rev, smul_neg, N0, dMq, basis, dN1, N1, dvR, add_apply,
      ContinuousLinearMap.smulRight_apply, sub_apply, neg_apply, smul_apply, PiLp.proj_apply,
      ne_eq, one_ne_zero, not_false_eq_true, PiLp.single_eq_of_ne, smul_eq_mul, mul_zero,
      neg_zero, PiLp.single_eq_same, mul_one, mul_neg, neg_neg, zero_add, Fin.reduceEq, add_zero,
      sub_neg_eq_add, zero_sub, nsmul_eq_mul, Nat.cast_ofNat, neg_smul, PiLp.add_apply,
      PiLp.smul_apply, zero_ne_one, PiLp.neg_apply, sub_zero, sub_self, field, Delta,
      Matrix.cons_val_zero]
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
  · rw [c1]
    simp only [Fin.isValue, fieldDeriv, dQuot, mul_inv_rev, dN0, duR, dsg, cp, one_div, smul_add,
      dnu, cm, dbe, duI, dal, neg_add_rev, smul_neg, N0, dMq, basis, dN1, N1, dvR, add_apply,
      ContinuousLinearMap.smulRight_apply, sub_apply, neg_apply, smul_apply, PiLp.proj_apply,
      ne_eq, one_ne_zero, not_false_eq_true, PiLp.single_eq_of_ne, smul_eq_mul, mul_zero,
      neg_zero, PiLp.single_eq_same, mul_one, mul_neg, neg_neg, zero_add, Fin.reduceEq, add_zero,
      sub_neg_eq_add, zero_sub, nsmul_eq_mul, Nat.cast_ofNat, neg_smul, PiLp.add_apply,
      PiLp.smul_apply, zero_ne_one, PiLp.neg_apply, sub_zero, sub_self, field, Delta,
      Matrix.cons_val_zero, Matrix.cons_val_one]
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
  · rw [c2]
    simp only [Fin.isValue, fieldDeriv, dQuot, mul_inv_rev, dN0, duR, dsg, cp, one_div, smul_add,
      dnu, cm, dbe, duI, dal, neg_add_rev, smul_neg, N0, dMq, basis, dN1, N1, dvR, add_apply,
      ContinuousLinearMap.smulRight_apply, sub_apply, neg_apply, smul_apply, PiLp.proj_apply,
      ne_eq, one_ne_zero, not_false_eq_true, PiLp.single_eq_of_ne, smul_eq_mul, mul_zero,
      neg_zero, PiLp.single_eq_same, mul_one, mul_neg, neg_neg, zero_add, Fin.reduceEq, add_zero,
      sub_neg_eq_add, zero_sub, nsmul_eq_mul, Nat.cast_ofNat, neg_smul, PiLp.add_apply,
      PiLp.smul_apply, zero_ne_one, PiLp.neg_apply, sub_zero, field, Delta,
      Matrix.cons_val]
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

/-! ## General pointwise formulas on `𝒰` -/

section General
variable {ε S lam : ℝ} {x : Space}

/-- `∂ₓ Re v = Re u c₊ α + Im u c₋ β`. -/
theorem dvR_basis0 (ε S lam : ℝ) (x : Space) :
    dvR ε S lam x (basis 0) =
      uR ε S lam x * cp ε x * al ε x + uI ε S lam x * cm ε x * be ε x := by
  simp [dvR, dsg, dnu, basis]; ring

/-- `∂_y Re v = Re u c₊ β - Im u c₋ α`. -/
theorem dvR_basis1 (ε S lam : ℝ) (x : Space) :
    dvR ε S lam x (basis 1) =
      uR ε S lam x * cp ε x * be ε x - uI ε S lam x * cm ε x * al ε x := by
  simp [dvR, dsg, dnu, basis]; ring

/-- `∂_z Re v = λ Im v`. -/
theorem dvR_basis2 (ε S lam : ℝ) (x : Space) :
    dvR ε S lam x (basis 2) = lam * vI ε S lam x := by
  simp [dvR, dsg, dnu, basis]

/-- `(∂ₓ Re v)² + (∂_y Re v)² = ((Re u)² c₊² + (Im u)² c₋²) |P|² r²`. -/
theorem dvR_sq_add (ε S lam : ℝ) (x : Space) :
    dvR ε S lam x (basis 0) ^ 2 + dvR ε S lam x (basis 1) ^ 2 =
      (uR ε S lam x ^ 2 * cp ε x ^ 2 + uI ε S lam x ^ 2 * cm ε x ^ 2) * Mq ε x * r2 x := by
  rw [dvR_basis0, dvR_basis1]
  unfold al be Mq r2
  ring

/-- `|B|² = ((Re u)² + (Im u)²) (r²/|P|²)/4 + (Re v)²/λ²` on `𝒰`. -/
theorem normSq_field (hx : x ∈ U ε) :
    ‖field ε S lam x‖ ^ 2 =
      (uR ε S lam x ^ 2 + uI ε S lam x ^ 2) * (r2 x / Mq ε x) / 4 + vR ε S lam x ^ 2 / lam ^ 2 := by
  have hm := (Mq_pos hx).ne'
  rw [← real_inner_self_eq_norm_sq, inner_coords]
  simp only [field, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  unfold Mq r2 al be at *
  field_simp
  ring

/-- `|∇ψ|² = (Re v)² ((∂ₓ Re v)² + (∂_y Re v)²) + λ² (sin λz cos λz + Re v Im v)²`. -/
theorem normSq_gradPsi (ε S lam : ℝ) (x : Space) :
    ‖gradPsi ε S lam x‖ ^ 2 =
      vR ε S lam x ^ 2 * (dvR ε S lam x (basis 0) ^ 2 + dvR ε S lam x (basis 1) ^ 2) +
        lam ^ 2 * (sz lam x * cz lam x + vR ε S lam x * vI ε S lam x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_coords]
  simp only [gradPsi, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, dvR_basis2]
  ring

/-- `⟪B, Δ⟫ = r² ((Re u)² c₊ - (Im u)² c₋)/(2λ)` on `𝒰`. -/
theorem inner_field_Delta (hl : lam ≠ 0) (hx : x ∈ U ε) :
    ⟪field ε S lam x, Delta ε S lam x⟫ =
      r2 x * (uR ε S lam x ^ 2 * cp ε x - uI ε S lam x ^ 2 * cm ε x) / (2 * lam) := by
  have hm := (Mq_pos hx).ne'
  rw [inner_coords]
  simp only [field, Delta, PiLp.smul_apply, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, dvR_basis0, dvR_basis1, smul_eq_mul]
  unfold Mq r2 al be at *
  field_simp
  ring

/-- `|Δ|² = ((∂ₓ Re v)² + (∂_y Re v)²)/λ²`. -/
theorem normSq_Delta (ε S lam : ℝ) (x : Space) :
    ‖Delta ε S lam x‖ ^ 2 =
      (dvR ε S lam x (basis 0) ^ 2 + dvR ε S lam x (basis 1) ^ 2) / lam ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_coords]
  simp only [Delta, PiLp.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, smul_eq_mul]
  ring

/-- `μ₀ J = ∇ × B = λ B + Δ` on `𝒰` (for `μ₀ ≠ 0`, `λ ≠ 0`). -/
theorem smul_current (hl : lam ≠ 0) {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (hx : x ∈ U ε) :
    μ₀ • current μ₀ ε S lam x = lam • field ε S lam x + Delta ε S lam x := by
  rw [current, (field_hasFDerivAt ε S lam hx).fderiv, smul_smul, mul_inv_cancel₀ hμ, one_smul,
    curl_fieldDeriv hl hx]

/-- `Ξ = μ₀ J - I' B = (λ - I') B + Δ` on `𝒰`. -/
theorem Xi_eq (hl : lam ≠ 0) {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (I' : ℝ) (hx : x ∈ U ε) :
    μ₀ • current μ₀ ε S lam x - I' • field ε S lam x =
      (lam - I') • field ε S lam x + Delta ε S lam x := by
  rw [smul_current hl hμ hx, sub_smul]; abel

/-- `⟪B, Ξ⟫ = (λ - I') |B|² + ⟪B, Δ⟫` on `𝒰`. -/
theorem inner_field_Xi (hl : lam ≠ 0) {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (I' : ℝ) (hx : x ∈ U ε) :
    ⟪field ε S lam x, μ₀ • current μ₀ ε S lam x - I' • field ε S lam x⟫ =
      (lam - I') * ‖field ε S lam x‖ ^ 2 + ⟪field ε S lam x, Delta ε S lam x⟫ := by
  rw [Xi_eq hl hμ I' hx, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]

/-- `|Ξ|² = (λ - I')² |B|² + 2 (λ - I') ⟪B, Δ⟫ + |Δ|²` on `𝒰`. -/
theorem normSq_Xi (hl : lam ≠ 0) {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (I' : ℝ) (hx : x ∈ U ε) :
    ‖μ₀ • current μ₀ ε S lam x - I' • field ε S lam x‖ ^ 2 =
      (lam - I') ^ 2 * ‖field ε S lam x‖ ^ 2 + 2 * (lam - I') * ⟪field ε S lam x, Delta ε S lam x⟫ +
        ‖Delta ε S lam x‖ ^ 2 := by
  rw [Xi_eq hl hμ I' hx, norm_add_sq_real, norm_smul, real_inner_smul_left, mul_pow,
    Real.norm_eq_abs, sq_abs]
  ring

end General


/-! ## Algebra of the atoms on the surface -/

section AtomAlgebra
variable {ε lam k s1 c1 s2 : ℝ}

/-- `Re u = cos λz cos(σ-S) cosh ν - sin λz sin(σ-S) sinh ν = T` on the surface. -/
theorem uR_alg (h1 : s1 ^ 2 + c1 ^ 2 = 1) (hk : k ^ 2 < 1) :
    cc k s1 * cA ε k s1 c1 s2 * chc ε s2 - -Yc k s1 * sA ε k s1 c1 s2 * shc ε s2 =
      Tc ε k s2 := by
  have hT0 := (T0_pos (ε := ε) (s2 := s2) h1 hk).ne'
  have hcc := cc_sq h1 hk
  have hch := chc_sq_sub_shc_sq (ε := ε) (s2 := s2)
  unfold sA cA
  unfold T0c at hT0 ⊢
  generalize cc k s1 = a at *
  generalize chc ε s2 = ch at *
  generalize shc ε s2 = sh at *
  generalize Tc ε k s2 = T at *
  generalize Xc k c1 = X at *
  generalize Yc k s1 = Y at *
  field_simp
  linear_combination T * ch ^ 2 * hcc - T * Y ^ 2 * hch

/-- `Im u = uIc` on the surface. -/
theorem uI_alg (h1 : s1 ^ 2 + c1 ^ 2 = 1) (hk : k ^ 2 < 1) :
    -(-Yc k s1 * cA ε k s1 c1 s2 * chc ε s2 + cc k s1 * sA ε k s1 c1 s2 * shc ε s2) =
      uIc ε k s1 c1 s2 := by
  have hT0 := (T0_pos (ε := ε) (s2 := s2) h1 hk).ne'
  have hcc := cc_sq h1 hk
  have hch := chc_sq_sub_shc_sq (ε := ε) (s2 := s2)
  unfold sA cA uIc
  unfold T0c at hT0 ⊢
  generalize cc k s1 = a at *
  generalize chc ε s2 = ch at *
  generalize shc ε s2 = sh at *
  generalize Tc ε k s2 = T at *
  generalize Xc k c1 = X at *
  generalize Yc k s1 = Y at *
  field_simp
  linear_combination Y * a * T * hch - ch * sh * X * hcc

/-- `Re v = X` on the surface. -/
theorem vR_alg (h1 : s1 ^ 2 + c1 ^ 2 = 1) (hk : k ^ 2 < 1) :
    cc k s1 * sA ε k s1 c1 s2 * chc ε s2 + -Yc k s1 * cA ε k s1 c1 s2 * shc ε s2 = Xc k c1 := by
  have hT0 := (T0_pos (ε := ε) (s2 := s2) h1 hk).ne'
  have hcc := cc_sq h1 hk
  have hch := chc_sq_sub_shc_sq (ε := ε) (s2 := s2)
  unfold sA cA
  unfold T0c at hT0 ⊢
  generalize cc k s1 = a at *
  generalize chc ε s2 = ch at *
  generalize shc ε s2 = sh at *
  generalize Tc ε k s2 = T at *
  generalize Xc k c1 = X at *
  generalize Yc k s1 = Y at *
  field_simp
  linear_combination X * ch ^ 2 * hcc - X * Y ^ 2 * hch

/-- `Im v = vIc` on the surface. -/
theorem vI_alg (h1 : s1 ^ 2 + c1 ^ 2 = 1) (hk : k ^ 2 < 1) :
    cc k s1 * cA ε k s1 c1 s2 * shc ε s2 - -Yc k s1 * sA ε k s1 c1 s2 * chc ε s2 =
      vIc ε k s1 c1 s2 := by
  have hT0 := (T0_pos (ε := ε) (s2 := s2) h1 hk).ne'
  have hcc := cc_sq h1 hk
  have hch := chc_sq_sub_shc_sq (ε := ε) (s2 := s2)
  unfold sA cA vIc
  unfold T0c at hT0 ⊢
  generalize cc k s1 = a at *
  generalize chc ε s2 = ch at *
  generalize shc ε s2 = sh at *
  generalize Tc ε k s2 = T at *
  generalize Xc k c1 = X at *
  generalize Yc k s1 = Y at *
  field_simp
  linear_combination sh * ch * T * hcc + a * Y * X * hch

/-- `sin λz cos λz + Re v Im v = -T Im u` on the surface. -/
theorem gz_alg (h1 : s1 ^ 2 + c1 ^ 2 = 1) (hk : k ^ 2 < 1) :
    -Yc k s1 * cc k s1 + Xc k c1 * vIc ε k s1 c1 s2 = -(Tc ε k s2 * uIc ε k s1 c1 s2) := by
  have hT0 := (T0_pos (ε := ε) (s2 := s2) h1 hk).ne'
  have hT := Tc_sq (ε := ε) (s2 := s2) hk
  have hXY := Xc_sq_add_Yc_sq (k := k) h1
  unfold vIc uIc
  unfold T0c at hT0 ⊢
  generalize cc k s1 = a at *
  generalize chc ε s2 = ch at *
  generalize shc ε s2 = sh at *
  generalize Tc ε k s2 = T at *
  generalize Xc k c1 = X at *
  generalize Yc k s1 = Y at *
  field_simp
  linear_combination Y * a * (hXY + hT)

end AtomAlgebra

/-! ## The atoms at the surface point -/

section Surface
variable {ε S lam k χ ζ : ℝ}

/-- `σ` at the surface point. -/
theorem sg_surfPt (hS : 2 ≤ S) :
    sg ε (surfPt ε S lam k χ ζ) = sigc ε S k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) := by
  have h : sg ε (surfPt ε S lam k χ ζ) =
      sg ε (axis ε (sigc ε S k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ))) ζ) := rfl
  rw [h, sg_axis (sigma_pos hS)]

/-- `ν = (ε/2) sin 2ζ` at the surface point. -/
theorem nu_surfPt (hS : 2 ≤ S) :
    nu ε (surfPt ε S lam k χ ζ) = nuc ε (Real.sin (2 * ζ)) := by
  have h : nu ε (surfPt ε S lam k χ ζ) =
      nu ε (axis ε (sigc ε S k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ))) ζ) := rfl
  rw [h, nu_axis (sigma_pos hS), nuc, Real.sin_two_mul]
  ring

/-- `|P|² = q` at the surface point. -/
theorem Mq_surfPt (hS : 2 ≤ S) :
    Mq ε (surfPt ε S lam k χ ζ) = qc ε S k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) := by
  rw [Mq, sg_surfPt hS, nu_surfPt hS, qc]

/-- `r² = m` at the surface point. -/
theorem r2_surfPt (hS : 2 ≤ S) :
    r2 (surfPt ε S lam k χ ζ) =
      mc ε S k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ)) := by
  have hσ := sigma_pos (ε := ε) (k := k) (s1 := Real.sin χ) (c1 := Real.cos χ)
    (s2 := Real.sin (2 * ζ)) hS
  have h : r2 (surfPt ε S lam k χ ζ) =
      (aC ε (sigc ε S k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ))) * Real.cos ζ) ^ 2 +
      (bC ε (sigc ε S k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ))) * Real.sin ζ) ^ 2 := rfl
  have hh : hC ε (sigc ε S k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ))) =
      hc ε S k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) := rfl
  rw [h, mul_pow, mul_pow, aC_sq hσ, bC_sq hσ, hh, mc, Real.cos_two_mul]
  have := Real.cos_sq_add_sin_sq ζ
  linear_combination ((hc ε S k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) + ε) / 2) * this

/-- The surface point lies in the smooth region `𝒰`. -/
theorem surfPt_mem_U_of (hS : 2 ≤ S) : surfPt ε S lam k χ ζ ∈ U ε :=
  axis_mem (ε := ε) (sigma_pos hS) ζ

/-- `cos λz = √(1 - Y²)` at the surface point. -/
theorem cz_surfPt (hl : lam ≠ 0) :
    cz lam (surfPt ε S lam k χ ζ) = cc k (Real.sin χ) := by
  have h : cz lam (surfPt ε S lam k χ ζ) =
      Real.cos (lam * (-Real.arcsin (k * Real.sin χ) / lam)) := rfl
  rw [h, show lam * (-Real.arcsin (k * Real.sin χ) / lam) = -Real.arcsin (k * Real.sin χ) by
    field_simp, Real.cos_neg, Real.cos_arcsin]
  rfl

/-- `sin λz = -Y` at the surface point. -/
theorem sz_surfPt (hl : lam ≠ 0) (hk : k ^ 2 < 1) :
    sz lam (surfPt ε S lam k χ ζ) = -Yc k (Real.sin χ) := by
  have hY := Yc_sq_le (k := k) (Real.sin_sq_add_cos_sq χ)
  have h : sz lam (surfPt ε S lam k χ ζ) =
      Real.sin (lam * (-Real.arcsin (k * Real.sin χ) / lam)) := rfl
  rw [h, show lam * (-Real.arcsin (k * Real.sin χ) / lam) = -Real.arcsin (k * Real.sin χ) by
    field_simp, Real.sin_neg, Real.sin_arcsin]
  · rfl
  · unfold Yc at hY; nlinarith
  · unfold Yc at hY; nlinarith

/-- `sin(σ - S) = sA` at the surface point. -/
theorem sin_surfPt (hS : 2 ≤ S) (hk : k ^ 2 < 1) :
    Real.sin (sg ε (surfPt ε S lam k χ ζ) - S) =
      sA ε k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) := by
  have h := sA_sq_add_cA_sq (ε := ε) (s2 := Real.sin (2 * ζ)) (Real.sin_sq_add_cos_sq χ) hk
  rw [sg_surfPt hS, sigc, add_sub_cancel_left, Real.sin_arcsin]
  · nlinarith [sq_nonneg (cA ε k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)))]
  · nlinarith [sq_nonneg (cA ε k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)))]

/-- `cos(σ - S) = cA` at the surface point (using `cA > 0`). -/
theorem cos_surfPt (hS : 2 ≤ S) (hk : k ^ 2 < 1)
    (hcA : 0 < cA ε k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ))) :
    Real.cos (sg ε (surfPt ε S lam k χ ζ) - S) =
      cA ε k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) := by
  have h := sA_sq_add_cA_sq (ε := ε) (s2 := Real.sin (2 * ζ)) (Real.sin_sq_add_cos_sq χ) hk
  rw [sg_surfPt hS, sigc, add_sub_cancel_left, Real.cos_arcsin,
    show 1 - sA ε k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) ^ 2 =
      cA ε k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) ^ 2 by linarith,
    Real.sqrt_sq hcA.le]

/-- `cosh ν` at the surface point. -/
theorem cosh_surfPt (hS : 2 ≤ S) :
    Real.cosh (nu ε (surfPt ε S lam k χ ζ)) = chc ε (Real.sin (2 * ζ)) := by
  rw [nu_surfPt hS, chc]

/-- `sinh ν` at the surface point. -/
theorem sinh_surfPt (hS : 2 ≤ S) :
    Real.sinh (nu ε (surfPt ε S lam k χ ζ)) = shc ε (Real.sin (2 * ζ)) := by
  rw [nu_surfPt hS, shc]

/-- The four atoms `Re u, Im u, Re v, Im v` at the surface point. -/
theorem atoms_surfPt (hl : lam ≠ 0) (hS : 2 ≤ S) (hk : k ^ 2 < 1)
    (hcA : 0 < cA ε k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ))) :
    uR ε S lam (surfPt ε S lam k χ ζ) = Tc ε k (Real.sin (2 * ζ)) ∧
    uI ε S lam (surfPt ε S lam k χ ζ) = uIc ε k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) ∧
    vR ε S lam (surfPt ε S lam k χ ζ) = Xc k (Real.cos χ) ∧
    vI ε S lam (surfPt ε S lam k χ ζ) = vIc ε k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) := by
  have h1 := Real.sin_sq_add_cos_sq χ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [uR, cz_surfPt hl, sz_surfPt hl hk, sin_surfPt hS hk, cos_surfPt hS hk hcA,
      cosh_surfPt hS, sinh_surfPt hS, uR_alg h1 hk]
  · rw [uI, cz_surfPt hl, sz_surfPt hl hk, sin_surfPt hS hk, cos_surfPt hS hk hcA,
      cosh_surfPt hS, sinh_surfPt hS, uI_alg h1 hk]
  · rw [vR, cz_surfPt hl, sz_surfPt hl hk, sin_surfPt hS hk, cos_surfPt hS hk hcA,
      cosh_surfPt hS, sinh_surfPt hS, vR_alg h1 hk]
  · rw [vI, cz_surfPt hl, sz_surfPt hl hk, sin_surfPt hS hk, cos_surfPt hS hk hcA,
      cosh_surfPt hS, sinh_surfPt hS, vI_alg h1 hk]

/-- `ψ = k²/2` at the surface point (general admissible parameters). -/
theorem psi_surfPt_of (hl : lam ≠ 0) (hS : 2 ≤ S) (hk : k ^ 2 < 1)
    (hcA : 0 < cA ε k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ))) :
    psi ε S lam (surfPt ε S lam k χ ζ) = k ^ 2 / 2 := by
  rw [psi, sz_surfPt hl hk, (atoms_surfPt hl hS hk hcA).2.2.1]
  have := Xc_sq_add_Yc_sq (k := k) (Real.sin_sq_add_cos_sq χ)
  linear_combination this / 2

/-- `|B|² = Bsq` at the surface point (general admissible parameters). -/
theorem normSq_field_surfPt_of (hl : lam ≠ 0) (hS : 2 ≤ S) (hk : k ^ 2 < 1)
    (hcA : 0 < cA ε k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ))) :
    ‖field ε S lam (surfPt ε S lam k χ ζ)‖ ^ 2 =
      Bsq ε S lam k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ)) := by
  obtain ⟨a1, a2, a3, -⟩ := atoms_surfPt hl hS hk hcA
  rw [normSq_field (surfPt_mem_U_of hS), a1, a2, a3, r2_surfPt hS, Mq_surfPt hS, Bsq]

/-- `|∇ψ|² = gp2` at the surface point (general admissible parameters). -/
theorem normSq_gradPsi_surfPt_of (hl : lam ≠ 0) (hS : 2 ≤ S) (hk : k ^ 2 < 1)
    (hcA : 0 < cA ε k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ))) :
    ‖gradPsi ε S lam (surfPt ε S lam k χ ζ)‖ ^ 2 =
      gp2 ε S lam k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ)) := by
  obtain ⟨a1, a2, a3, a4⟩ := atoms_surfPt hl hS hk hcA
  rw [normSq_gradPsi, dvR_sq_add, cp, cm, a1, a2, a3, a4, r2_surfPt hS, Mq_surfPt hS,
    sz_surfPt hl hk, cz_surfPt hl, gz_alg (Real.sin_sq_add_cos_sq χ) hk,
    gX2_eq hS (Real.abs_cos_le_one _), gp2, gX2]
  ring

/-- `(∂ₓ Re v)² + (∂_y Re v)² = gX2` at the surface point. -/
theorem dvR_sq_add_surfPt (hl : lam ≠ 0) (hS : 2 ≤ S) (hk : k ^ 2 < 1)
    (hcA : 0 < cA ε k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ))) :
    dvR ε S lam (surfPt ε S lam k χ ζ) (basis 0) ^ 2 +
        dvR ε S lam (surfPt ε S lam k χ ζ) (basis 1) ^ 2 =
      gX2 ε S k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ)) := by
  obtain ⟨a1, a2, -, -⟩ := atoms_surfPt hl hS hk hcA
  rw [dvR_sq_add, cp, cm, a1, a2, r2_surfPt hS, Mq_surfPt hS,
    gX2_eq hS (Real.abs_cos_le_one _), gX2]

/-- `⟪B, Δ⟫ = BD` at the surface point. -/
theorem inner_field_Delta_surfPt (hl : lam ≠ 0) (hS : 2 ≤ S) (hk : k ^ 2 < 1)
    (hcA : 0 < cA ε k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ))) :
    ⟪field ε S lam (surfPt ε S lam k χ ζ), Delta ε S lam (surfPt ε S lam k χ ζ)⟫ =
      BD ε S lam k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ)) := by
  obtain ⟨a1, a2, -, -⟩ := atoms_surfPt hl hS hk hcA
  have hq := (q_pos (ε := ε) (k := k) (s1 := Real.sin χ) (c1 := Real.cos χ)
    (s2 := Real.sin (2 * ζ)) hS).ne'
  have hm := (m_pos (ε := ε) (k := k) (s1 := Real.sin χ) (c1 := Real.cos χ)
    (s2 := Real.sin (2 * ζ)) hS (Real.abs_cos_le_one (2 * ζ))).ne'
  rw [inner_field_Delta hl (surfPt_mem_U_of hS), cp, cm, a1, a2, r2_surfPt hS, Mq_surfPt hS,
    BD, rc]
  field_simp

/-- `⟪B, Ξ⟫ = (λ - I') Bsq + BD` at the surface point (general admissible parameters). -/
theorem inner_field_Xi_surfPt_of (hl : lam ≠ 0) (hS : 2 ≤ S) (hk : k ^ 2 < 1)
    (hcA : 0 < cA ε k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ))) {μ₀ : ℝ} (hμ : μ₀ ≠ 0)
    (I' : ℝ) :
    ⟪field ε S lam (surfPt ε S lam k χ ζ),
        μ₀ • current μ₀ ε S lam (surfPt ε S lam k χ ζ) -
          I' • field ε S lam (surfPt ε S lam k χ ζ)⟫ =
      (lam - I') * Bsq ε S lam k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ)) +
        BD ε S lam k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ)) := by
  rw [inner_field_Xi hl hμ I' (surfPt_mem_U_of hS), normSq_field_surfPt_of hl hS hk hcA,
    inner_field_Delta_surfPt hl hS hk hcA]

/-- `|Ξ|² = (λ - I')² Bsq + 2 (λ - I') BD + gX2/λ²` at the surface point (general admissible
parameters). -/
theorem normSq_Xi_surfPt_of (hl : lam ≠ 0) (hS : 2 ≤ S) (hk : k ^ 2 < 1)
    (hcA : 0 < cA ε k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ))) {μ₀ : ℝ} (hμ : μ₀ ≠ 0)
    (I' : ℝ) :
    ‖μ₀ • current μ₀ ε S lam (surfPt ε S lam k χ ζ) -
        I' • field ε S lam (surfPt ε S lam k χ ζ)‖ ^ 2 =
      (lam - I') ^ 2 *
          Bsq ε S lam k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ)) +
        2 * (lam - I') *
          BD ε S lam k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ)) +
        gX2 ε S k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ)) / lam ^ 2 := by
  rw [normSq_Xi hl hμ I' (surfPt_mem_U_of hS), normSq_field_surfPt_of hl hS hk hcA,
    inner_field_Delta_surfPt hl hS hk hcA, normSq_Delta, dvR_sq_add_surfPt hl hS hk hcA]

end Surface


/-! ## The admissible family member `ε = 1/4`, `S = 4` -/

section Admissible
variable {lam k χ ζ : ℝ}

/-- `cos(σ - S) > 0` at the angles `(χ, ζ)` for `ε = 1/4`, `0 < k ≤ 19/20`. -/
theorem cA_pos_angles (hk0 : 0 < k) (hk1 : k ≤ 19 / 20) :
    0 < cA (1 / 4) k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) :=
  cA_pos (Real.sin_sq_add_cos_sq χ) (Real.abs_sin_le_one _) hk0 hk1

/-- `k² < 1` for `0 < k ≤ 19/20`. -/
theorem k_sq_lt_one (hk0 : 0 < k) (hk1 : k ≤ 19 / 20) : k ^ 2 < 1 := by nlinarith

/-- **(a)** The surface point lies in the smooth region `𝒰`. -/
theorem surfPt_mem_U : surfPt (1 / 4) 4 lam k χ ζ ∈ U (1 / 4) :=
  surfPt_mem_U_of (by norm_num)

/-- **(a)** The surface point lies on the flux surface `ψ = k²/2`. -/
theorem psi_surfPt (hl : lam ≠ 0) (hk0 : 0 < k) (hk1 : k ≤ 19 / 20) :
    psi (1 / 4) 4 lam (surfPt (1 / 4) 4 lam k χ ζ) = k ^ 2 / 2 :=
  psi_surfPt_of hl (by norm_num) (k_sq_lt_one hk0 hk1) (cA_pos_angles hk0 hk1)

/-- **(b)** `|B|² = Bsq` at the surface point. -/
theorem normSq_field_surfPt (hl : lam ≠ 0) (hk0 : 0 < k) (hk1 : k ≤ 19 / 20) :
    ‖field (1 / 4) 4 lam (surfPt (1 / 4) 4 lam k χ ζ)‖ ^ 2 =
      Bsq (1 / 4) 4 lam k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ)) :=
  normSq_field_surfPt_of hl (by norm_num) (k_sq_lt_one hk0 hk1) (cA_pos_angles hk0 hk1)

/-- **(b)** `|∇ψ|² = gp2` at the surface point. -/
theorem normSq_gradPsi_surfPt (hl : lam ≠ 0) (hk0 : 0 < k) (hk1 : k ≤ 19 / 20) :
    ‖gradPsi (1 / 4) 4 lam (surfPt (1 / 4) 4 lam k χ ζ)‖ ^ 2 =
      gp2 (1 / 4) 4 lam k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ)) :=
  normSq_gradPsi_surfPt_of hl (by norm_num) (k_sq_lt_one hk0 hk1) (cA_pos_angles hk0 hk1)

/-- **(c)** With `Ξ = μ₀ J - I' B`: `⟪B, Ξ⟫ = (λ - I') Bsq + BD` at the surface point. -/
theorem inner_field_Xi_surfPt (hl : lam ≠ 0) (hk0 : 0 < k) (hk1 : k ≤ 19 / 20) {μ₀ : ℝ}
    (hμ : μ₀ ≠ 0) (I' : ℝ) :
    ⟪field (1 / 4) 4 lam (surfPt (1 / 4) 4 lam k χ ζ),
        μ₀ • current μ₀ (1 / 4) 4 lam (surfPt (1 / 4) 4 lam k χ ζ) -
          I' • field (1 / 4) 4 lam (surfPt (1 / 4) 4 lam k χ ζ)⟫ =
      (lam - I') *
          Bsq (1 / 4) 4 lam k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ)) +
        BD (1 / 4) 4 lam k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ)) :=
  inner_field_Xi_surfPt_of hl (by norm_num) (k_sq_lt_one hk0 hk1) (cA_pos_angles hk0 hk1) hμ I'

/-- **(c)** With `Ξ = μ₀ J - I' B`: `|Ξ|² = (λ - I')² Bsq + 2 (λ - I') BD + gX2/λ²` at the
surface point. -/
theorem normSq_Xi_surfPt (hl : lam ≠ 0) (hk0 : 0 < k) (hk1 : k ≤ 19 / 20) {μ₀ : ℝ}
    (hμ : μ₀ ≠ 0) (I' : ℝ) :
    ‖μ₀ • current μ₀ (1 / 4) 4 lam (surfPt (1 / 4) 4 lam k χ ζ) -
        I' • field (1 / 4) 4 lam (surfPt (1 / 4) 4 lam k χ ζ)‖ ^ 2 =
      (lam - I') ^ 2 *
          Bsq (1 / 4) 4 lam k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ)) +
        2 * (lam - I') *
          BD (1 / 4) 4 lam k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ)) +
        gX2 (1 / 4) 4 k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ)) /
          lam ^ 2 :=
  normSq_Xi_surfPt_of hl (by norm_num) (k_sq_lt_one hk0 hk1) (cA_pos_angles hk0 hk1) hμ I'

end Admissible

/-! ## Sanity checks -/

/-- Sanity check: for `k = 0` the closed form gives `sin(σ - S) = 0`. -/
theorem sA_k_zero (ε s1 c1 s2 : ℝ) : sA ε 0 s1 c1 s2 = 0 := by
  simp [sA, Xc, Yc]

/-- Sanity check: the degenerate surface `k = 0` is the magnetic axis. -/
theorem surfPt_k_zero (ε S lam χ ζ : ℝ) : surfPt ε S lam 0 χ ζ = axis ε S ζ := by
  have hσ : sigc ε S 0 (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) = S := by
    simp [sigc, sA_k_zero]
  apply space_ext
  · simp [surfPt, axis, hσ]
  · simp [surfPt, axis, hσ]
  · simp [surfPt, axis]

/-- Sanity check: at `χ = 0`, `ζ = 0` the surface point of `ε = 1/4`, `S = 4` has
`|∇ψ|² = λ² T² (Im u)² + k² gX2 > 0` (the closed form is nondegenerate). -/
theorem gp2_pos_example :
    0 < gp2 (1 / 4) 4 15 (1 / 20) (Real.sin 0) (Real.cos 0) (Real.sin (2 * 0))
      (Real.cos (2 * 0)) :=
  gp2_pos (Real.sin_sq_add_cos_sq 0) (by norm_num) (Real.abs_cos_le_one _) (by norm_num)
    (by norm_num) (by norm_num)

end PlasmaLean.Design.LandremanFamily2Surface
