/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamTorusACheck
public import PlasmaLean.Theory.Fields.TorusTrapping
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A certified approximate invariant torus of the rational stellarator (KAM route, stage K2)

Stage K2 of `notes/theory/kam-route.md` (§5): a **validated approximate invariant torus** of the
rational stellarator field `field (1/4)` (`Design/RationalStellarator`), with an explicit, tiny,
rigorous bound on its invariance error.

**The torus.** Torus A (rotational transform `ι = [0;7,3,1,1,…] = (75 + √5)/562 ≈ 0.137431`) is
the explicit trigonometric polynomial map `(θ, φ) ↦ (R, z)` in cylindrical coordinates,
`R(θ, φ) = ∑ a_{km} cos(kθ + mψ)`, `z(θ, φ) = ∑ b_{km} sin(kθ + mψ)`, `ψ = 2φ − π/2`,
`|k| ≤ 32`, `|m| ≤ 22`, with exact dyadic coefficients (`torusR`, `torusZ`; data in
`Design/KamTorusAData`, 2 × 1463 coefficients over `2^90`; stellarator symmetric about `φ = π/4`).
The angle `θ ∈ ℝ/2πℤ` is the poloidal angle of the linear flow, `φ` the toroidal angle; the torus
is `π`-periodic in `φ` (two field periods).

**The invariance equation (flow form).** With the helical potential `h = f cos 2φ + g sin 2φ`
(`hpot`; `hpot_eq_H`: `h = H/4` for the `H` of `Design/RationalStellarator`), `B = ∇φ + ε∇h`,
`ε = 1/4`, has `B^R = ε ∂_R h`, `B^z = ε ∂_z h`, `B^φ = (1 + ε ∂_φ h)/R²`, so field lines
parametrized by `φ` satisfy `dR/dφ = R² ε ∂_R h / (1 + ε ∂_φ h)`,
`dz/dφ = R² ε ∂_z h / (1 + ε ∂_φ h)`.
An invariant torus with frequency `ι` is a map `K = (R, z)` with
`∂_φ K + ι ∂_θ K = X(K, φ)`. Multiplied by the polynomial `D = R² (1 + ε ∂_φ h)` (`Dfun`,
`Dfun_eq`), the residuals
`resR = D (∂_φ R + ι ∂_θ R) − 2εR Ps`, `resZ = D (∂_φ z + ι ∂_θ z) − εR² Pz`
(`Ps = R³ ∂_R h / 2`, `Pz = R² ∂_z h`; `hasDerivAt_hpot_R`, `hasDerivAt_hpot_z`) are polynomials in
`R, z, cos 2φ, sin 2φ`, hence trigonometric polynomials in `(θ, φ)`. Their derivatives are the
actual partial derivatives of the torus (`hasDerivAt_torusR_θ`, …).

**Main results.**
* `torusA_error_le`: `|resR θ φ| ≤ 1.23 × 10⁻²³` and `|resZ θ φ| ≤ 6.94 × 10⁻²⁴` for **all real**
  `θ, φ` (sup norm; the bound is the `ℓ¹` norm of the exact Fourier coefficients of the residual,
  i.e. the weighted `ℓ¹_ν` norm with `ν = 1`).
* `torusA_D_bounds`: `0.59 ≤ D ≤ 1.42`, hence (`torusA_flow_error`) the unnormalized flow-form
  error `|∂_φ K + ι ∂_θ K − X(K, φ)|` is at most `2.1 × 10⁻²³` (`R`) and `1.18 × 10⁻²³` (`z`).
* `torusA_graph`: the torus is a radial graph about the exact magnetic axis: the poloidal winding
  rate `(R − 1) ∂_θ z − z ∂_θ R ≥ 0.015 > 0` (the polar angle about the axis is strictly increasing
  in `θ`), and `0.078 ≤ rt ≤ 0.1893 < 1/2` for the distance `rt` from the axis of
  `Theory/Fields/TorusTrapping`, evaluated at the torus points `torusPoint θ φ`.

**Method.** The residual, multiplied by `2^{Q+4} σ⁶ e^{iκ}` (`σ = 2^91`, `ι` replaced by the
dyadic `ι_q = Iq/2^96`, `|ι − ι_q| ≤ 10⁻²⁹`), is the value on the unit torus `u = e^{iθ}`,
`v = e^{iψ}` of an integer polynomial `R̂_R ∈ ℤ[u][v]` (`evalC_RR`), so
`|resR| ≤ ‖R̂_R‖₁ / (2^{Q+4}σ⁶)`.
`‖R̂_R‖₁` is computed exactly by Kronecker substitution and a digit sum in the kernel
(`Certificates/Kronecker2D`, `Design/KamTorusACheck`): no truncation, no rounding, no tail.

**Remaining for K3** (not attempted here; constants from the note, §2.2 and §4). An a posteriori KAM
theorem in the FHL/ELP-S form needs, on a complex strip of width `ρ` (in turns),
`C₁ ‖E‖_ρ / (γ⁴ ρ^{4τ}) < 1` with `τ = 1`, `γ ≈ 0.069` (period map; `γ ≈ 0.27` for `k ≥ 2` with the
low divisors treated exactly), the ELP-S twist `𝒯 ≈ 9.7 × 10⁻⁴ ≠ 0`, and an explicit `C₁`. The
bound here is for `ρ = 0`; the oracle (`scripts/kam_oracle/`) reports the strip norms
(dominated by the Fourier truncation tail), which K3 must certify by the same method with weighted
digit sums.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamTorusA

open Finset PlasmaLean.Certificates.Kron2

/-! ## The torus and its derivatives -/

/-- The shifted toroidal angle `ψ = 2φ − π/2` (stellarator symmetry plane `φ = π/4`). -/
def psi (φ : ℝ) : ℝ := 2 * φ - Real.pi / 2

/-- The phase `(i − N) θ + (j − M) ψ` of grid mode `(i, j)`. -/
def ang (i j : ℕ) (θ φ : ℝ) : ℝ := ((i : ℝ) - N) * θ + ((j : ℝ) - M) * psi φ

/-- `R(θ, φ)`: distance from the `z`-axis of the torus point (a cosine series). -/
def torusR (θ φ : ℝ) : ℝ :=
  ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1), (cA i j : ℝ) / 2 ^ P * Real.cos (ang i j θ φ)

/-- `z(θ, φ)`: height of the torus point (a sine series). -/
def torusZ (θ φ : ℝ) : ℝ :=
  ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1), (cB i j : ℝ) / 2 ^ P * Real.sin (ang i j θ φ)

/-- `∂_θ R`. -/
def torusRθ (θ φ : ℝ) : ℝ :=
  ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1),
    (cA i j : ℝ) / 2 ^ P * (-Real.sin (ang i j θ φ) * ((i : ℝ) - N))

/-- `∂_φ R`. -/
def torusRφ (θ φ : ℝ) : ℝ :=
  ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1),
    (cA i j : ℝ) / 2 ^ P * (-Real.sin (ang i j θ φ) * (((j : ℝ) - M) * 2))

/-- `∂_θ z`. -/
def torusZθ (θ φ : ℝ) : ℝ :=
  ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1),
    (cB i j : ℝ) / 2 ^ P * (Real.cos (ang i j θ φ) * ((i : ℝ) - N))

/-- `∂_φ z`. -/
def torusZφ (θ φ : ℝ) : ℝ :=
  ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1),
    (cB i j : ℝ) / 2 ^ P * (Real.cos (ang i j θ φ) * (((j : ℝ) - M) * 2))

theorem hasDerivAt_ang_θ (i j : ℕ) (θ φ : ℝ) :
    HasDerivAt (fun θ => ang i j θ φ) ((i : ℝ) - N) θ := by
  have := ((hasDerivAt_id θ).const_mul ((i : ℝ) - N)).add_const (((j : ℝ) - M) * psi φ)
  simpa [ang] using this

theorem hasDerivAt_ang_φ (i j : ℕ) (θ φ : ℝ) :
    HasDerivAt (fun φ => ang i j θ φ) (((j : ℝ) - M) * 2) φ := by
  have h := (((hasDerivAt_id φ).const_mul 2).sub_const (Real.pi / 2)).const_mul ((j : ℝ) - M)
  have := h.const_add (((i : ℝ) - N) * θ)
  simpa [ang, psi] using this

/-- `torusRθ` is the `θ`-derivative of `torusR`. -/
theorem hasDerivAt_torusR_θ (θ φ : ℝ) :
    HasDerivAt (fun θ => torusR θ φ) (torusRθ θ φ) θ :=
  HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ =>
    ((hasDerivAt_ang_θ i j θ φ).cos).const_mul _

/-- `torusRφ` is the `φ`-derivative of `torusR`. -/
theorem hasDerivAt_torusR_φ (θ φ : ℝ) :
    HasDerivAt (fun φ => torusR θ φ) (torusRφ θ φ) φ :=
  HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ =>
    ((hasDerivAt_ang_φ i j θ φ).cos).const_mul _

/-- `torusZθ` is the `θ`-derivative of `torusZ`. -/
theorem hasDerivAt_torusZ_θ (θ φ : ℝ) :
    HasDerivAt (fun θ => torusZ θ φ) (torusZθ θ φ) θ :=
  HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ =>
    ((hasDerivAt_ang_θ i j θ φ).sin).const_mul _

/-- `torusZφ` is the `φ`-derivative of `torusZ`. -/
theorem hasDerivAt_torusZ_φ (θ φ : ℝ) :
    HasDerivAt (fun φ => torusZ θ φ) (torusZφ θ φ) φ :=
  HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ =>
    ((hasDerivAt_ang_φ i j θ φ).sin).const_mul _

/-! ## The field in cylindrical coordinates -/

/-- `ε = 1/4`. -/
def eps : ℝ := 1 / 4

/-- `R² f = ((R² − 1)² − 4z²)/4`. -/
def sfun (R z : ℝ) : ℝ := ((R ^ 2 - 1) ^ 2 - 4 * z ^ 2) / 4
/-- `R² g = −z((R² − 1)(R² − 5) − 4z²)/4`. -/
def sgfun (R z : ℝ) : ℝ := -z * ((R ^ 2 - 1) * (R ^ 2 - 5) - 4 * z ^ 2) / 4
/-- `R³ ∂_R f / 2 = (R⁴ − 1 + 4z²)/4`. -/
def s2fs (R z : ℝ) : ℝ := (R ^ 4 - 1 + 4 * z ^ 2) / 4
/-- `R³ ∂_R g / 2 = −z(R⁴ − 5 + 4z²)/4`. -/
def s2gs (R z : ℝ) : ℝ := -z * (R ^ 4 - 5 + 4 * z ^ 2) / 4
/-- `R² ∂_z g = −((R² − 1)(R² − 5) − 12z²)/4`. -/
def sgz (R z : ℝ) : ℝ := -((R ^ 2 - 1) * (R ^ 2 - 5) - 12 * z ^ 2) / 4

/-- The helical potential `h = f cos 2φ + g sin 2φ` in cylindrical coordinates. -/
def hpot (R z φ : ℝ) : ℝ := (sfun R z * Real.cos (2 * φ) + sgfun R z * Real.sin (2 * φ)) / R ^ 2

/-- `D = R² (1 + ε ∂_φ h)` as a polynomial in `R, z, c₂ = cos 2φ, s₂ = sin 2φ`. -/
def Dfun (R z c2 s2 : ℝ) : ℝ := R ^ 2 + eps * (-2 * sfun R z * s2 + 2 * sgfun R z * c2)
/-- `Ps = R³ ∂_R h / 2`. -/
def Psfun (R z c2 s2 : ℝ) : ℝ := s2fs R z * c2 + s2gs R z * s2
/-- `Pz = R² ∂_z h`. -/
def Pzfun (R z c2 s2 : ℝ) : ℝ := -2 * z * c2 + sgz R z * s2

/-- **`h = H/4`**: `hpot` is the helical potential of `Design/RationalStellarator` in cylindrical
coordinates. -/
theorem hpot_eq_H {R : ℝ} (hR : R ≠ 0) (z φ : ℝ) :
    hpot R z φ =
      RationalStellarator.H (WithLp.toLp 2 ![R * Real.cos φ, R * Real.sin φ, z]) / 4 := by
  have hcs := Real.cos_sq_add_sin_sq φ
  set y : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![R * Real.cos φ, R * Real.sin φ, z]
  have h0 : y 0 = R * Real.cos φ := by simp [y]
  have h1 : y 1 = R * Real.sin φ := by simp [y]
  have h2 : y 2 = z := by simp [y]
  have hr2 : RationalStellarator.r2 y = R ^ 2 := by
    rw [RationalStellarator.r2, h0, h1]; linear_combination R ^ 2 * hcs
  have hX : RationalStellarator.Xd y = R ^ 2 * Real.cos (2 * φ) := by
    rw [RationalStellarator.Xd, h0, h1, Real.cos_two_mul]; linear_combination (-R ^ 2) * hcs
  have hY : RationalStellarator.Yp y = R ^ 2 * z * Real.sin (2 * φ) := by
    rw [RationalStellarator.Yp, h0, h1, h2, Real.sin_two_mul]; ring
  have hA : RationalStellarator.Aq y = (R ^ 2 - 1) ^ 2 - 4 * z ^ 2 := by
    rw [RationalStellarator.Aq, hr2, h2]
  have hB : RationalStellarator.Bq y = (R ^ 2 - 1) * (R ^ 2 - 5) - 4 * z ^ 2 := by
    rw [RationalStellarator.Bq, hr2, h2]
  rw [RationalStellarator.H, RationalStellarator.winv, RationalStellarator.Hnum, hr2, hX, hY, hA,
    hB,
    hpot, sfun, sgfun]
  field_simp
  ring

/-- `∂_φ h`. -/
theorem hasDerivAt_hpot_φ (R z φ : ℝ) :
    HasDerivAt (fun φ => hpot R z φ)
      ((-2 * sfun R z * Real.sin (2 * φ) + 2 * sgfun R z * Real.cos (2 * φ)) / R ^ 2) φ := by
  have h1 := ((hasDerivAt_id φ).const_mul 2).cos
  have h2 := ((hasDerivAt_id φ).const_mul 2).sin
  have := ((h1.const_mul (sfun R z)).add (h2.const_mul (sgfun R z))).div_const (R ^ 2)
  convert this using 1
  · simp [hpot]
  · simp; ring

/-- `D = R² (1 + ε ∂_φ h)`. -/
theorem Dfun_eq {R : ℝ} (hR : R ≠ 0) (z φ : ℝ) :
    Dfun R z (Real.cos (2 * φ)) (Real.sin (2 * φ)) =
      R ^ 2 * (1 + eps * ((-2 * sfun R z * Real.sin (2 * φ) + 2 * sgfun R z * Real.cos (2 * φ)) /
        R ^ 2)) := by
  simp only [Dfun]; field_simp

/-- `∂_R h = 2 Ps / R³`, i.e. `2εR Ps = εR⁴ ∂_R h`. -/
theorem hasDerivAt_hpot_R {R : ℝ} (hR : R ≠ 0) (z φ : ℝ) :
    HasDerivAt (fun R => hpot R z φ)
      (2 * Psfun R z (Real.cos (2 * φ)) (Real.sin (2 * φ)) / R ^ 3) R := by
  have hf : HasDerivAt (fun R => sfun R z) (R * (R ^ 2 - 1)) R := by
    have := ((((hasDerivAt_id R).pow 2).sub_const 1).pow 2).sub_const (4 * z ^ 2)
    convert this.div_const 4 using 1
    · funext x; simp [sfun]
    · simp; ring
  have hg : HasDerivAt (fun R => sgfun R z) (-z * R * (R ^ 2 - 3)) R := by
    have := (((((hasDerivAt_id R).pow 2).sub_const 1).mul
      (((hasDerivAt_id R).pow 2).sub_const 5)).sub_const (4 * z ^ 2)).const_mul (-z)
    convert this.div_const 4 using 1
    · funext x; simp [sgfun]
    · simp; ring
  have hq := ((hf.mul_const (Real.cos (2 * φ))).add (hg.mul_const (Real.sin (2 * φ)))).div
    ((hasDerivAt_id R).pow 2) (pow_ne_zero 2 hR)
  convert hq using 1
  · funext x; simp [hpot]
  · simp only [Pi.add_apply, Pi.pow_apply, id, Psfun, s2fs, s2gs, sfun, sgfun]
    field_simp
    ring

/-- `∂_z h = Pz / R²`. -/
theorem hasDerivAt_hpot_z (R z φ : ℝ) :
    HasDerivAt (fun z => hpot R z φ)
      (Pzfun R z (Real.cos (2 * φ)) (Real.sin (2 * φ)) / R ^ 2) z := by
  have hf : HasDerivAt (fun z => sfun R z) (-2 * z) z := by
    have := ((hasDerivAt_id z).pow 2).const_mul 4
    convert (this.const_sub ((R ^ 2 - 1) ^ 2)).div_const 4 using 1
    · funext x; simp [sfun]
    · simp; ring
  have hg : HasDerivAt (fun z => sgfun R z) (sgz R z) z := by
    have := (hasDerivAt_id z).neg.mul
      ((((hasDerivAt_id z).pow 2).const_mul 4).const_sub ((R ^ 2 - 1) * (R ^ 2 - 5)))
    convert this.div_const 4 using 1
    · funext x; simp [sgfun]
    · simp [sgz]; ring
  have := ((hf.mul_const (Real.cos (2 * φ))).add
    (hg.mul_const (Real.sin (2 * φ)))).div_const (R ^ 2)
  convert this using 1
  · funext x; simp [hpot]
  · simp [Pzfun]

/-! ## The residuals -/

/-- The rotational transform of torus A, `ι = [0;7,3,1,1,1,…] = (75 + √5)/562`. -/
def iota : ℝ := (75 + Real.sqrt 5) / 562

/-- Its dyadic approximation `ι_q = Iq / 2^Q`. -/
def iotaQ : ℝ := (Iq : ℝ) / 2 ^ Q

/-- The `R`-residual `D (∂_φ R + ι ∂_θ R) − 2εR Ps` for transform `ι`. -/
def resRw (ι θ φ : ℝ) : ℝ :=
  Dfun (torusR θ φ) (torusZ θ φ) (Real.cos (2 * φ)) (Real.sin (2 * φ)) *
      (torusRφ θ φ + ι * torusRθ θ φ) -
    2 * eps * torusR θ φ * Psfun (torusR θ φ) (torusZ θ φ) (Real.cos (2 * φ)) (Real.sin (2 * φ))

/-- The `z`-residual `D (∂_φ z + ι ∂_θ z) − εR² Pz` for transform `ι`. -/
def resZw (ι θ φ : ℝ) : ℝ :=
  Dfun (torusR θ φ) (torusZ θ φ) (Real.cos (2 * φ)) (Real.sin (2 * φ)) *
      (torusZφ θ φ + ι * torusZθ θ φ) -
    eps * torusR θ φ ^ 2 * Pzfun (torusR θ φ) (torusZ θ φ) (Real.cos (2 * φ)) (Real.sin (2 * φ))

/-- The `R`-residual of torus A. -/
def resR (θ φ : ℝ) : ℝ := resRw iota θ φ
/-- The `z`-residual of torus A. -/
def resZ (θ φ : ℝ) : ℝ := resZw iota θ φ

/-! ## The residual as the value of an integer polynomial on the unit torus -/

/-- `u = e^{iθ}`. -/
def uu (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)
/-- `v = e^{iψ}`. -/
def vv (φ : ℝ) : ℂ := Complex.exp (psi φ * Complex.I)
/-- `w = uᴺ vᴹ`. -/
def ww (θ φ : ℝ) : ℂ := uu θ ^ N * vv φ ^ M

theorem norm_uu (θ : ℝ) : ‖uu θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
theorem norm_vv (φ : ℝ) : ‖vv φ‖ = 1 := Complex.norm_exp_ofReal_mul_I _
theorem norm_ww (θ φ : ℝ) : ‖ww θ φ‖ = 1 := by simp [ww, norm_uu, norm_vv]

theorem uv_pow (i j : ℕ) (θ φ : ℝ) :
    uu θ ^ i * vv φ ^ j = ww θ φ * Complex.exp (ang i j θ φ * Complex.I) := by
  simp only [uu, vv, ww, ← Complex.exp_nat_mul, ← Complex.exp_add, ang]
  congr 1; push_cast; ring

theorem evalC_gridPoly (g : ℕ → ℕ → ℤ) (θ φ : ℝ) :
    evalC (uu θ) (vv φ) (gridPoly g) = ww θ φ * ∑ i ∈ range (2 * N + 1),
      ∑ j ∈ range (2 * M + 1), (g i j : ℂ) * Complex.exp (ang i j θ φ * Complex.I) := by
  rw [gridPoly, map_sum, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [map_sum, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [evalC_monomial, mul_assoc, uv_pow]; ring

theorem ang_refl {i j : ℕ} (hi : i ≤ 2 * N) (hj : j ≤ 2 * M) (θ φ : ℝ) :
    ang (2 * N - i) (2 * M - j) θ φ = -ang i j θ φ := by
  simp only [ang, Nat.cast_sub hi, Nat.cast_sub hj]; push_cast; ring

theorem sum_reflect1 (n : ℕ) (G : ℕ → ℂ) :
    ∑ i ∈ range (n + 1), G (n - i) = ∑ i ∈ range (n + 1), G i := by
  rw [← sum_range_reflect G (n + 1)]
  exact sum_congr rfl fun i _ => by congr 1

theorem sum_refl (F : ℕ → ℕ → ℂ) :
    ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1), F (2 * N - i) (2 * M - j) =
      ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1), F i j := by
  rw [sum_reflect1 (2 * N) (fun i => ∑ j ∈ range (2 * M + 1), F i (2 * M - j))]
  exact sum_congr rfl fun i _ => sum_reflect1 (2 * M) (F i)

/-- Symmetrization: a grid `g = wt (c + s c ∘ refl)` with `wt ∘ refl = p wt` (`p² = 1`). -/
theorem sum_sym (g c wt : ℕ → ℕ → ℤ) (s p : ℤ) (hp : p * p = 1)
    (hg : ∀ i j, g i j = wt i j * (c i j + s * c (2 * N - i) (2 * M - j)))
    (hwt : ∀ i j, i ≤ 2 * N → j ≤ 2 * M → wt (2 * N - i) (2 * M - j) = p * wt i j) (θ φ : ℝ) :
    ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1),
        (g i j : ℂ) * Complex.exp (ang i j θ φ * Complex.I) =
      ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1), ((wt i j * c i j : ℤ) : ℂ) *
        (Complex.exp (ang i j θ φ * Complex.I) +
          ((s * p : ℤ) : ℂ) * Complex.exp (-(ang i j θ φ : ℂ) * Complex.I)) := by
  have hp' : (p : ℂ) * p = 1 := by exact_mod_cast hp
  have key : ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1),
      ((wt i j * (s * c (2 * N - i) (2 * M - j)) : ℤ) : ℂ) * Complex.exp (ang i j θ φ * Complex.I) =
      ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1), ((wt i j * c i j : ℤ) : ℂ) *
        (((s * p : ℤ) : ℂ) * Complex.exp (-(ang i j θ φ : ℂ) * Complex.I)) := by
    rw [← sum_refl (fun i j => ((wt i j * c i j : ℤ) : ℂ) *
      (((s * p : ℤ) : ℂ) * Complex.exp (-(ang i j θ φ : ℂ) * Complex.I)))]
    refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
    have hi' : i ≤ 2 * N := by simp at hi; omega
    have hj' : j ≤ 2 * M := by simp at hj; omega
    rw [ang_refl hi' hj', hwt i j hi' hj']
    push_cast
    simp only [neg_neg]
    linear_combination (-(wt i j : ℂ) * s * c (2 * N - i) (2 * M - j) *
      Complex.exp (ang i j θ φ * Complex.I)) * hp'
  have expand : ∀ i j, (g i j : ℂ) * Complex.exp (ang i j θ φ * Complex.I) =
      ((wt i j * c i j : ℤ) : ℂ) * Complex.exp (ang i j θ φ * Complex.I) +
        ((wt i j * (s * c (2 * N - i) (2 * M - j)) : ℤ) : ℂ) *
          Complex.exp (ang i j θ φ * Complex.I) := by
    intro i j; rw [hg]; push_cast; ring
  have expand2 : ∀ i j, ((wt i j * c i j : ℤ) : ℂ) * (Complex.exp (ang i j θ φ * Complex.I) +
      ((s * p : ℤ) : ℂ) * Complex.exp (-(ang i j θ φ : ℂ) * Complex.I)) =
      ((wt i j * c i j : ℤ) : ℂ) * Complex.exp (ang i j θ φ * Complex.I) +
        ((wt i j * c i j : ℤ) : ℂ) *
          (((s * p : ℤ) : ℂ) * Complex.exp (-(ang i j θ φ : ℂ) * Complex.I)) := by
    intro i j; ring
  simp_rw [expand, expand2, sum_add_distrib]
  rw [key]

/-- `e^{ix} + e^{−ix} = 2 cos x`. -/
theorem exp_add_exp (x : ℂ) :
    Complex.exp (x * Complex.I) + Complex.exp (-x * Complex.I) = 2 * Complex.cos x :=
  (Complex.two_cos x).symm

/-- `e^{ix} − e^{−ix} = 2i sin x`. -/
theorem exp_sub_exp (x : ℂ) :
    Complex.exp (x * Complex.I) - Complex.exp (-x * Complex.I) = 2 * Complex.I * Complex.sin x := by
  linear_combination (-Complex.I) * Complex.two_sin x +
    (Complex.exp (x * Complex.I) - Complex.exp (-x * Complex.I)) * Complex.I_sq

/-- Normalize `a + (±1) b` and close a per-mode identity. -/
macro "mode_close" : tactic =>
  `(tactic| (push_cast; simp only [one_mul, neg_one_mul, neg_neg, ← sub_eq_add_neg, exp_add_exp,
    exp_sub_exp]; (try field_simp); (try ring_nf); (try simp only [Complex.I_sq]); (try ring_nf)))

/-- The common scale `t = σ w`. -/
def tt (θ φ : ℝ) : ℂ := (sig : ℂ) * ww θ φ

theorem sig_eq : (sig : ℂ) = 2 * 2 ^ P := by simp [sig, pow_succ]; ring

/-- The weight `i − N` is odd under reflection. -/
theorem wtθ_refl {i : ℕ} (hi : i ≤ 2 * N) : ((2 * N - i : ℕ) : ℤ) - N = -1 * ((i : ℤ) - N) := by
  rw [Nat.cast_sub hi]; push_cast; ring

/-- The weight `j − M` is odd under reflection. -/
theorem wtψ_refl {j : ℕ} (hj : j ≤ 2 * M) : ((2 * M - j : ℕ) : ℤ) - M = -1 * ((j : ℤ) - M) := by
  rw [Nat.cast_sub hj]; push_cast; ring

theorem evalC_Rh (θ φ : ℝ) : evalC (uu θ) (vv φ) (gridPoly gR) = tt θ φ * torusR θ φ := by
  rw [evalC_gridPoly, sum_sym gR cA (fun _ _ => 1) 1 1 (by norm_num)
    (fun i j => by simp only [gR]; ring)
    (fun _ _ _ _ => by simp)]
  simp only [torusR, tt, sig_eq, Complex.ofReal_sum, mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  mode_close

theorem evalC_Zh (θ φ : ℝ) :
    evalC (uu θ) (vv φ) (gridPoly gZ) = Complex.I * tt θ φ * torusZ θ φ := by
  rw [evalC_gridPoly, sum_sym gZ cB (fun _ _ => 1) (-1) 1 (by norm_num)
    (fun i j => by simp only [gZ]; ring) (fun _ _ _ _ => by simp)]
  simp only [torusZ, tt, sig_eq, Complex.ofReal_sum, mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  mode_close

theorem evalC_Rth (θ φ : ℝ) :
    evalC (uu θ) (vv φ) (gridPoly gRth) = -Complex.I * tt θ φ * torusRθ θ φ := by
  rw [evalC_gridPoly, sum_sym gRth cA (fun i _ => (i : ℤ) - N) 1 (-1) (by norm_num)
    (fun i j => by simp only [gRth, gR]; ring) 
    (fun i j hi _ => wtθ_refl hi)]
  simp only [torusRθ, tt, sig_eq, Complex.ofReal_sum, mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  mode_close

theorem evalC_Rps (θ φ : ℝ) :
    evalC (uu θ) (vv φ) (gridPoly gRps) = -Complex.I * tt θ φ * torusRφ θ φ / 2 := by
  rw [evalC_gridPoly, sum_sym gRps cA (fun _ j => (j : ℤ) - M) 1 (-1) (by norm_num)
    (fun i j => by simp only [gRps, gR]; ring) 
    (fun i j _ hj => wtψ_refl hj)]
  simp only [torusRφ, tt, sig_eq, Complex.ofReal_sum, mul_sum, sum_div]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  mode_close

theorem evalC_Zth (θ φ : ℝ) : evalC (uu θ) (vv φ) (gridPoly gZth) = tt θ φ * torusZθ θ φ := by
  rw [evalC_gridPoly, sum_sym gZth cB (fun i _ => (i : ℤ) - N) (-1) (-1) (by norm_num)
    (fun i j => by simp only [gZth, gZ]; ring) 
    (fun i j hi _ => wtθ_refl hi)]
  simp only [torusZθ, tt, sig_eq, Complex.ofReal_sum, mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  mode_close

theorem evalC_Zps (θ φ : ℝ) : evalC (uu θ) (vv φ) (gridPoly gZps) = tt θ φ * torusZφ θ φ / 2 := by
  rw [evalC_gridPoly, sum_sym gZps cB (fun _ j => (j : ℤ) - M) (-1) (-1) (by norm_num)
    (fun i j => by simp only [gZps, gZ]; ring) 
    (fun i j _ hj => wtψ_refl hj)]
  simp only [torusZφ, tt, sig_eq, Complex.ofReal_sum, mul_sum, sum_div]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  mode_close

theorem evalC_tP (θ φ : ℝ) : evalC (uu θ) (vv φ) tP = tt θ φ := by
  rw [tP, evalC_monomial, tt, ww]; push_cast; ring

theorem evalC_vP (θ φ : ℝ) : evalC (uu θ) (vv φ) vP = vv φ := by
  rw [vP, evalC_monomial]; simp

theorem vv_mul_exp_neg (φ : ℝ) :
    vv φ * Complex.exp (-(psi φ : ℂ) * Complex.I) = 1 := by
  rw [vv, ← Complex.exp_add]; ring_nf; exact Complex.exp_zero

theorem evalC_ChP (θ φ : ℝ) :
    evalC (uu θ) (vv φ) ChP = 2 * vv φ * (Real.cos (psi φ) : ℂ) := by
  rw [ChP, map_add, evalC_monomial, evalC_monomial, Complex.ofReal_cos,
    show 2 * vv φ * Complex.cos (psi φ : ℂ) = vv φ * (2 * Complex.cos (psi φ : ℂ)) by ring,
    ← exp_add_exp]
  have h := vv_mul_exp_neg φ
  simp only [Int.cast_one, one_mul, pow_zero, mul_one]
  rw [show Complex.exp (↑(psi φ) * Complex.I) = vv φ from rfl]
  linear_combination (-1 : ℂ) * h

theorem evalC_SvP (θ φ : ℝ) :
    evalC (uu θ) (vv φ) SvP = 2 * Complex.I * vv φ * (Real.sin (psi φ) : ℂ) := by
  rw [SvP, map_sub, evalC_monomial, evalC_monomial, Complex.ofReal_sin,
    show 2 * Complex.I * vv φ * Complex.sin (psi φ : ℂ) =
      vv φ * (2 * Complex.I * Complex.sin (psi φ : ℂ)) by ring, ← exp_sub_exp]
  have h := vv_mul_exp_neg φ
  simp only [Int.cast_one, one_mul, pow_zero, mul_one]
  rw [show Complex.exp (↑(psi φ) * Complex.I) = vv φ from rfl]
  linear_combination h

theorem cos_two_mul_eq (φ : ℝ) : Real.cos (2 * φ) = -Real.sin (psi φ) := by
  rw [psi, Real.sin_sub_pi_div_two]; ring
theorem sin_two_mul_eq (φ : ℝ) : Real.sin (2 * φ) = Real.cos (psi φ) := by
  rw [psi, Real.cos_sub_pi_div_two]

/-! ## Algebraic identities (the `i`-bookkeeping) -/

theorem I_pow3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
theorem I_pow4 : Complex.I ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num
theorem I_pow5 : Complex.I ^ 5 = Complex.I := by rw [pow_succ, I_pow4, one_mul]
theorem I_pow6 : Complex.I ^ 6 = -1 := by rw [pow_succ, I_pow5, Complex.I_mul_I]
theorem I_pow7 : Complex.I ^ 7 = -Complex.I := by rw [pow_succ, I_pow6]; ring

/-- Normalize a polynomial identity in `ℂ` modulo `i² = −1`. -/
macro "ring_I" : tactic =>
  `(tactic| (
    ring_nf
    try simp only [Complex.I_sq, I_pow3, I_pow4, I_pow5, I_pow6, I_pow7]
    try ring_nf))

theorem Dform_alg (t v : ℂ) (R z c sn : ℝ) :
    Dform (t * R) (Complex.I * t * z) t v (2 * v * c) (2 * Complex.I * v * sn) =
      16 * t ^ 5 * v * (Dfun R z (-sn) c : ℂ) := by
  simp only [Dform, Dfun, sfun, sgfun, eps, nsmul_eq_mul]; push_cast; ring_I

theorem PRform_alg (t v : ℂ) (R z c sn : ℝ) :
    PRform (t * R) (Complex.I * t * z) t (2 * v * c) (2 * Complex.I * v * sn) =
      -8 * Complex.I * t ^ 5 * v * (Psfun R z (-sn) c : ℂ) := by
  simp only [PRform, Psfun, s2fs, s2gs, nsmul_eq_mul]; push_cast; ring_I

theorem PZform_alg (t v : ℂ) (R z c sn : ℝ) :
    PZform (t * R) (Complex.I * t * z) t (2 * v * c) (2 * Complex.I * v * sn) =
      -8 * t ^ 4 * v * (Pzfun R z (-sn) c : ℂ) := by
  simp only [PZform, Pzfun, sgz, nsmul_eq_mul]; push_cast; ring_I

theorem Iq_eq : (Iq : ℂ) = 2 ^ Q * (iotaQ : ℂ) := by
  simp only [iotaQ]; push_cast; field_simp

theorem RRform_alg (t v : ℂ) (R z Rθ Rφ c sn : ℝ) :
    RRform (t * R) (Complex.I * t * z) (-Complex.I * t * Rθ) (-Complex.I * t * Rφ / 2) t v
        (2 * v * c) (2 * Complex.I * v * sn) =
      -Complex.I * 2 ^ (Q + 4) * t ^ 6 * v *
        ((Dfun R z (-sn) c * (Rφ + iotaQ * Rθ) - 2 * eps * R * Psfun R z (-sn) c : ℝ) : ℂ) := by
  rw [RRform, Dform_alg, PRform_alg, Lform, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul, Iq_eq]
  simp only [eps]
  push_cast
  ring_I

theorem RZform_alg (t v : ℂ) (R z Zθ Zφ c sn : ℝ) :
    RZform (t * R) (Complex.I * t * z) (t * Zθ) (t * Zφ / 2) t v
        (2 * v * c) (2 * Complex.I * v * sn) =
      2 ^ (Q + 5) * t ^ 6 * v *
        ((Dfun R z (-sn) c * (Zφ + iotaQ * Zθ) - eps * R ^ 2 * Pzfun R z (-sn) c : ℝ) : ℂ) := by
  rw [RZform, Dform_alg, PZform_alg, Lform, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul,
    nsmul_eq_mul, Iq_eq]
  simp only [eps]
  push_cast
  ring_I

theorem Nform_alg (t : ℂ) (R z Rθ Zθ : ℝ) :
    Nform (t * R) (Complex.I * t * z) (-Complex.I * t * Rθ) (t * Zθ) t =
      t ^ 2 * (((R - 1) * Zθ - z * Rθ : ℝ) : ℂ) := by
  simp only [Nform]; push_cast; ring_I

theorem rt2form_alg (t : ℂ) (R z : ℝ) :
    rt2form (t * R) (Complex.I * t * z) t = t ^ 2 * (((R - 1) ^ 2 + z ^ 2 : ℝ) : ℂ) := by
  simp only [rt2form]; push_cast; ring_I

theorem dK2form_alg (t : ℂ) (Rθ Zθ : ℝ) :
    dK2form (-Complex.I * t * Rθ) (t * Zθ) = t ^ 2 * ((Rθ ^ 2 + Zθ ^ 2 : ℝ) : ℂ) := by
  simp only [dK2form]; push_cast; ring_I

/-! ## Evaluation of the cleared residuals on the torus -/

/-- The cleared `R`-residual as a formal polynomial. -/
noncomputable def RRpoly : P2 :=
  RRform (gridPoly gR) (gridPoly gZ) (gridPoly gRth) (gridPoly gRps) tP vP ChP SvP
/-- The cleared `z`-residual as a formal polynomial. -/
noncomputable def RZpoly : P2 :=
  RZform (gridPoly gR) (gridPoly gZ) (gridPoly gZth) (gridPoly gZps) tP vP ChP SvP
/-- `D̂` as a formal polynomial. -/
noncomputable def Dpoly : P2 := Dform (gridPoly gR) (gridPoly gZ) tP vP ChP SvP
/-- `N̂` as a formal polynomial. -/
noncomputable def Npoly : P2 := Nform (gridPoly gR) (gridPoly gZ) (gridPoly gRth) (gridPoly gZth) tP
/-- `(R̂ − t)² − Ẑ²` as a formal polynomial. -/
noncomputable def rt2poly : P2 := rt2form (gridPoly gR) (gridPoly gZ) tP
/-- `Ẑ_θ² − R̂_θ²` as a formal polynomial. -/
noncomputable def dK2poly : P2 := dK2form (gridPoly gRth) (gridPoly gZth)

theorem cosψ_sinψ (φ : ℝ) :
    Real.cos (2 * φ) = -Real.sin (psi φ) ∧ Real.sin (2 * φ) = Real.cos (psi φ) :=
  ⟨cos_two_mul_eq φ, sin_two_mul_eq φ⟩

theorem evalC_RR (θ φ : ℝ) : evalC (uu θ) (vv φ) RRpoly =
    (((2 ^ (Q + 4) * (sig : ℝ) ^ 6) * resRw iotaQ θ φ : ℝ) : ℂ) *
      (-Complex.I * ww θ φ ^ 6 * vv φ) := by
  rw [RRpoly, RRform_map, evalC_Rh, evalC_Zh, evalC_Rth, evalC_Rps, evalC_tP, evalC_vP, evalC_ChP,
    evalC_SvP, RRform_alg, resRw, cos_two_mul_eq, sin_two_mul_eq, tt]
  push_cast; ring

theorem evalC_RZ (θ φ : ℝ) : evalC (uu θ) (vv φ) RZpoly =
    (((2 ^ (Q + 5) * (sig : ℝ) ^ 6) * resZw iotaQ θ φ : ℝ) : ℂ) * (ww θ φ ^ 6 * vv φ) := by
  rw [RZpoly, RZform_map, evalC_Rh, evalC_Zh, evalC_Zth, evalC_Zps, evalC_tP, evalC_vP, evalC_ChP,
    evalC_SvP, RZform_alg, resZw, cos_two_mul_eq, sin_two_mul_eq, tt]
  push_cast; ring

/-- The `D`-value at the torus point. -/
def Dval (θ φ : ℝ) : ℝ :=
  Dfun (torusR θ φ) (torusZ θ φ) (Real.cos (2 * φ)) (Real.sin (2 * φ))

theorem evalC_D (θ φ : ℝ) : evalC (uu θ) (vv φ) Dpoly =
    (((16 * (sig : ℝ) ^ 5) * Dval θ φ : ℝ) : ℂ) * (uu θ ^ (5 * N) * vv φ ^ (5 * M + 1)) := by
  rw [Dpoly, Dform_map, evalC_Rh, evalC_Zh, evalC_tP, evalC_vP, evalC_ChP, evalC_SvP, Dform_alg,
    Dval, cos_two_mul_eq, sin_two_mul_eq, tt, ww]
  push_cast; ring

theorem evalC_N (θ φ : ℝ) : evalC (uu θ) (vv φ) Npoly =
    (((sig : ℝ) ^ 2 * ((torusR θ φ - 1) * torusZθ θ φ - torusZ θ φ * torusRθ θ φ) : ℝ) : ℂ) *
      (uu θ ^ (2 * N) * vv φ ^ (2 * M)) := by
  rw [Npoly, Nform_map, evalC_Rh, evalC_Zh, evalC_Rth, evalC_Zth, evalC_tP, Nform_alg, tt, ww]
  push_cast; ring

theorem evalC_rt2 (θ φ : ℝ) : evalC (uu θ) (vv φ) rt2poly =
    (((sig : ℝ) ^ 2 * ((torusR θ φ - 1) ^ 2 + torusZ θ φ ^ 2) : ℝ) : ℂ) * (ww θ φ ^ 2) := by
  rw [rt2poly, rt2form_map, evalC_Rh, evalC_Zh, evalC_tP, rt2form_alg, tt]
  push_cast; ring

theorem evalC_dK2 (θ φ : ℝ) : evalC (uu θ) (vv φ) dK2poly =
    (((sig : ℝ) ^ 2 * (torusRθ θ φ ^ 2 + torusZθ θ φ ^ 2) : ℝ) : ℂ) * (ww θ φ ^ 2) := by
  rw [dK2poly, dK2form_map, evalC_Rth, evalC_Zth, dK2form_alg, tt]
  push_cast; ring

/-! ## Exact `ℓ¹` norms from the kernel computations -/

theorem kron_RRpoly : kron 656 385 RRpoly = RRint 656 385 := by
  rw [RRpoly, RRform_map, kron_gridPoly, kron_gridPoly, kron_gridPoly, kron_gridPoly, kron_tP,
    kron_vP, kron_ChP, kron_SvP]; rfl

theorem kron_RZpoly : kron 656 385 RZpoly = RZint 656 385 := by
  rw [RZpoly, RZform_map, kron_gridPoly, kron_gridPoly, kron_gridPoly, kron_gridPoly, kron_tP,
    kron_vP, kron_ChP, kron_SvP]; rfl

theorem kron_Dpoly : kron 656 385 Dpoly = Dint 656 385 := by
  rw [Dpoly, Dform_map, kron_gridPoly, kron_gridPoly, kron_tP, kron_vP, kron_ChP, kron_SvP]; rfl

theorem kron_Npoly : kron 192 129 Npoly = Nint 192 129 := by
  rw [Npoly, Nform_map, kron_gridPoly, kron_gridPoly, kron_gridPoly, kron_gridPoly, kron_tP]; rfl

theorem kron_rt2poly : kron 192 129 rt2poly = rt2int 192 129 := by
  rw [rt2poly, rt2form_map, kron_gridPoly, kron_gridPoly, kron_tP]; rfl

theorem kron_dK2poly : kron 192 129 dK2poly = dK2int 192 129 := by
  rw [dK2poly, dK2form_map, kron_gridPoly, kron_gridPoly]; rfl

theorem l1_RRpoly : l1 RRpoly = l1Kron 656 17 (RRint 656 385) := by
  rw [← kron_RRpoly]
  refine l1_eq_l1Kron (a := 12 * N) (J := 12 * M + 2) (by norm_num) ?_ (by norm_num [N])
    (by norm_num [M]) ?_
  · exact box_RRform (box_gridPoly _) (box_gridPoly _) (box_gridPoly _) (box_gridPoly _) box_tP
      box_vP box_ChP box_SvP
  · exact (l1_RRform (l1_gridPoly_le _) (l1_gridPoly_le _) (l1_gridPoly_le _) (l1_gridPoly_le _)
      l1_tP l1_vP l1_ChP l1_SvP).trans_lt apriori_RR

theorem l1_RZpoly : l1 RZpoly = l1Kron 656 17 (RZint 656 385) := by
  rw [← kron_RZpoly]
  refine l1_eq_l1Kron (a := 12 * N) (J := 12 * M + 2) (by norm_num) ?_ (by norm_num [N])
    (by norm_num [M]) ?_
  · exact box_RZform (box_gridPoly _) (box_gridPoly _) (box_gridPoly _) (box_gridPoly _) box_tP
      box_vP box_ChP box_SvP
  · exact (l1_RZform (l1_gridPoly_le _) (l1_gridPoly_le _) (l1_gridPoly_le _) (l1_gridPoly_le _)
      l1_tP l1_vP l1_ChP l1_SvP).trans_lt apriori_RZ

/-- The centre monomial `c0D u^{5N} v^{5M+1}` of `D̂`. -/
noncomputable def Dmono : P2 :=
  Polynomial.monomial (5 * M + 1) (Polynomial.monomial (5 * N) (c0D : ℤ))

theorem l1_Dsub : l1 (Dpoly - Dmono) =
    l1Kron 656 17
      (Dint 656 385 - (c0D : ℤ) * ((pow2 (656 * (5 * N + 385 * (5 * M + 1))) : ℕ) : ℤ)) := by
  have hk : kron 656 385 (Dpoly - Dmono) =
      Dint 656 385 - (c0D : ℤ) * ((pow2 (656 * (5 * N + 385 * (5 * M + 1))) : ℕ) : ℤ) := by
    rw [map_sub, kron_Dpoly, Dmono, kron_monomial, pow2_eq]; push_cast; rfl
  rw [← hk]
  refine l1_eq_l1Kron (a := 10 * N) (J := 10 * M + 2) (by norm_num) ?_ (by norm_num [N])
    (by norm_num [M]) ?_
  · exact InBox.sub (box_Dform (box_gridPoly _) (box_gridPoly _) box_tP box_vP box_ChP box_SvP)
      (InBox.mono (InBox.monomial _ _ _) (by omega) (by omega))
  · refine (l1_sub' (l1_Dform (l1_gridPoly_le _) (l1_gridPoly_le _) l1_tP l1_vP l1_ChP l1_SvP)
      (le_of_eq (by rw [Dmono, l1_monomial]; rfl))).trans_lt apriori_D

/-- The centre monomial `c0N u^{2N} v^{2M}` of `N̂`. -/
noncomputable def Nmono : P2 := Polynomial.monomial (2 * M) (Polynomial.monomial (2 * N) (c0N : ℤ))

theorem l1_Nsub : l1 (Npoly - Nmono) =
    l1Kron 192 14
      (Nint 192 129 - (c0N : ℤ) * ((pow2 (192 * (2 * N + 129 * (2 * M))) : ℕ) : ℤ)) := by
  have hk : kron 192 129 (Npoly - Nmono) =
      Nint 192 129 - (c0N : ℤ) * ((pow2 (192 * (2 * N + 129 * (2 * M))) : ℕ) : ℤ) := by
    rw [map_sub, kron_Npoly, Nmono, kron_monomial, pow2_eq]; push_cast; rfl
  rw [← hk]
  refine l1_eq_l1Kron (a := 4 * N) (J := 4 * M) (by norm_num) ?_ (by norm_num [N])
    (by norm_num [M]) ?_
  · exact InBox.sub (box_Nform (box_gridPoly _) (box_gridPoly _) (box_gridPoly _) (box_gridPoly _)
      box_tP) (InBox.mono (InBox.monomial _ _ _) (by omega) (by omega))
  · refine (l1_sub' (l1_Nform (l1_gridPoly_le _) (l1_gridPoly_le _) (l1_gridPoly_le _)
      (l1_gridPoly_le _) l1_tP) (le_of_eq (by rw [Nmono, l1_monomial]; rfl))).trans_lt apriori_N

theorem l1_rt2poly : l1 rt2poly = l1Kron 192 14 (rt2int 192 129) := by
  rw [← kron_rt2poly]
  refine l1_eq_l1Kron (a := 4 * N) (J := 4 * M) (by norm_num) ?_ (by norm_num [N])
    (by norm_num [M]) ?_
  · exact box_rt2form (box_gridPoly _) (box_gridPoly _) box_tP
  · exact (l1_rt2form (l1_gridPoly_le _) (l1_gridPoly_le _) l1_tP).trans_lt apriori_rt2

theorem l1_dK2poly : l1 dK2poly = l1Kron 192 14 (dK2int 192 129) := by
  rw [← kron_dK2poly]
  refine l1_eq_l1Kron (a := 4 * N) (J := 4 * M) (by norm_num) ?_ (by norm_num [N])
    (by norm_num [M]) ?_
  · exact box_dK2form (box_gridPoly _) (box_gridPoly _)
  · exact (l1_dK2form (l1_gridPoly_le _) (l1_gridPoly_le _)).trans_lt apriori_dK2

/-! ## The certified bounds -/

theorem sig_pos : (0 : ℝ) < sig := by unfold sig; positivity

theorem norm_mono (θ φ : ℝ) (a b : ℕ) : ‖uu θ ^ a * vv φ ^ b‖ = 1 := by
  simp [norm_uu, norm_vv]

/-- Residual with the dyadic `ι_q`: `|R-residual| ≤ 1.22 × 10⁻²³`. -/
theorem resRq_le (θ φ : ℝ) : |resRw iotaQ θ φ| ≤ 122 / 10 ^ 25 := by
  have hκ : (0 : ℝ) < 2 ^ (Q + 4) * (sig : ℝ) ^ 6 := by have := sig_pos; positivity
  have hm : ‖-Complex.I * ww θ φ ^ 6 * vv φ‖ = 1 := by simp [norm_ww, norm_vv]
  have h1 := abs_le_of_evalC (norm_uu θ) (norm_vv φ) hκ hm (evalC_RR θ φ)
  rw [l1_RRpoly] at h1
  have h2 : (l1Kron 656 17 (RRint 656 385) : ℝ) * 10 ^ 25 ≤
      122 * (2 ^ (Q + 4) * (sig : ℝ) ^ 6) := by
    exact_mod_cast check_RR
  refine h1.trans ?_
  rw [div_le_div_iff₀ hκ (by positivity)]
  linarith

/-- Residual with the dyadic `ι_q`: `|z-residual| ≤ 6.93 × 10⁻²⁴`. -/
theorem resZq_le (θ φ : ℝ) : |resZw iotaQ θ φ| ≤ 693 / 10 ^ 26 := by
  have hκ : (0 : ℝ) < 2 ^ (Q + 5) * (sig : ℝ) ^ 6 := by have := sig_pos; positivity
  have hm : ‖ww θ φ ^ 6 * vv φ‖ = 1 := by simp [norm_ww, norm_vv]
  have h1 := abs_le_of_evalC (norm_uu θ) (norm_vv φ) hκ hm (evalC_RZ θ φ)
  rw [l1_RZpoly] at h1
  have h2 : (l1Kron 656 17 (RZint 656 385) : ℝ) * 10 ^ 26 ≤
      693 * (2 ^ (Q + 5) * (sig : ℝ) ^ 6) := by
    exact_mod_cast check_RZ
  refine h1.trans ?_
  rw [div_le_div_iff₀ hκ (by positivity)]
  linarith

/-- **`0.59 ≤ D ≤ 1.42`** on the whole torus: the flow-form normalization is harmless. -/
theorem torusA_D_bounds (θ φ : ℝ) : 59 / 100 ≤ Dval θ φ ∧ |Dval θ φ| ≤ 142 / 100 := by
  have hκ : (0 : ℝ) < 16 * (sig : ℝ) ^ 5 := by have := sig_pos; positivity
  obtain ⟨c1, c2⟩ := check_D
  rw [← l1_Dsub] at c1 c2
  have c1' : 100 * (l1 (Dpoly - Dmono) : ℝ) + 59 * (16 * (sig : ℝ) ^ 5) ≤ 100 * (c0D : ℝ) := by
    exact_mod_cast c1
  have c2' : 100 * (c0D : ℝ) + 100 * (l1 (Dpoly - Dmono) : ℝ) ≤ 142 * (16 * (sig : ℝ) ^ 5) := by
    exact_mod_cast c2
  have hlow := le_of_evalC (norm_uu θ) (norm_vv φ) hκ (c0D : ℤ) (evalC_D θ φ)
  rw [show (Polynomial.monomial (5 * M + 1) (Polynomial.monomial (5 * N) ((c0D : ℕ) : ℤ)) : P2) =
    Dmono from rfl] at hlow
  push_cast at hlow
  -- upper bound: `|κ D| ≤ ‖evalC (Dpoly − Dmono)‖ + c0D`
  have hup : |16 * (sig : ℝ) ^ 5 * Dval θ φ| ≤ (l1 (Dpoly - Dmono) : ℝ) + (c0D : ℝ) := by
    have hb := norm_evalC_le (norm_uu θ).le (norm_vv φ).le (Dpoly - Dmono)
    rw [map_sub, evalC_D, Dmono, evalC_monomial] at hb
    have hm := norm_mono θ φ (5 * N) (5 * M + 1)
    have e : evalC (uu θ) (vv φ) Dpoly = evalC (uu θ) (vv φ) (Dpoly - Dmono) +
        (c0D : ℂ) * (uu θ ^ (5 * N) * vv φ ^ (5 * M + 1)) := by
      rw [map_sub, Dmono, evalC_monomial]; push_cast; ring
    have hn := norm_add_le (evalC (uu θ) (vv φ) (Dpoly - Dmono))
      ((c0D : ℂ) * (uu θ ^ (5 * N) * vv φ ^ (5 * M + 1)))
    rw [← e, evalC_D, norm_mul, hm, mul_one, Complex.norm_real, Real.norm_eq_abs, norm_mul, hm,
      mul_one, Complex.norm_natCast] at hn
    exact hn.trans (by linarith [norm_evalC_le (norm_uu θ).le (norm_vv φ).le (Dpoly - Dmono)])
  refine ⟨?_, ?_⟩
  · refine le_trans ?_ hlow
    rw [le_div_iff₀ hκ]; linarith
  · rw [abs_mul, abs_of_pos hκ] at hup
    rw [← mul_le_mul_iff_of_pos_left hκ]
    linarith

/-- `|∂_θ R| ≤ 1/5`. -/
theorem torusRθ_le (θ φ : ℝ) : |torusRθ θ φ| ≤ 1 / 5 := by
  have hm : ‖-Complex.I * ww θ φ‖ = 1 := by simp [norm_ww]
  have h := abs_le_of_evalC (norm_uu θ) (norm_vv φ) sig_pos hm
    (show evalC (uu θ) (vv φ) (gridPoly gRth) = (((sig : ℝ) * torusRθ θ φ : ℝ) : ℂ) *
      (-Complex.I * ww θ φ) by rw [evalC_Rth, tt]; push_cast; ring)
  have h1 : (l1 (gridPoly gRth) : ℝ) ≤ gridL1 gRth := by exact_mod_cast l1_gridPoly_le _
  have h2 : 5 * (gridL1 gRth : ℝ) ≤ sig := by exact_mod_cast gridL1_gRth_le
  refine h.trans ?_
  rw [div_le_iff₀ sig_pos]; linarith

/-- `|∂_θ z| ≤ 1/5`. -/
theorem torusZθ_le (θ φ : ℝ) : |torusZθ θ φ| ≤ 1 / 5 := by
  have hm : ‖ww θ φ‖ = 1 := norm_ww θ φ
  have h := abs_le_of_evalC (norm_uu θ) (norm_vv φ) sig_pos hm
    (show evalC (uu θ) (vv φ) (gridPoly gZth) = (((sig : ℝ) * torusZθ θ φ : ℝ) : ℂ) * ww θ φ by
      rw [evalC_Zth, tt]; push_cast; ring)
  have h1 : (l1 (gridPoly gZth) : ℝ) ≤ gridL1 gZth := by exact_mod_cast l1_gridPoly_le _
  have h2 : 5 * (gridL1 gZth : ℝ) ≤ sig := by exact_mod_cast gridL1_gZth_le
  refine h.trans ?_
  rw [div_le_iff₀ sig_pos]; linarith

/-- `|ι − ι_q| ≤ 10⁻²⁹`. -/
theorem iota_sub_iotaQ : |iota - iotaQ| ≤ 1 / 10 ^ 29 := by
  have hlo : (562 * ((Iq : ℝ) / 2 ^ Q) - 75) - 562 / 10 ^ 29 ≤ Real.sqrt 5 := by
    rw [Real.le_sqrt (by norm_num [Iq, Q]) (by norm_num)]; norm_num [Iq, Q]
  have hhi : Real.sqrt 5 ≤ (562 * ((Iq : ℝ) / 2 ^ Q) - 75) + 562 / 10 ^ 29 := by
    rw [Real.sqrt_le_left (by norm_num [Iq, Q])]; norm_num [Iq, Q]
  rw [abs_le, iota, iotaQ]
  constructor <;> linarith

/-- `resR` differs from its dyadic version by `D (ι − ι_q) ∂_θ R`. -/
theorem resR_sub (θ φ : ℝ) :
    resR θ φ - resRw iotaQ θ φ = Dval θ φ * (iota - iotaQ) * torusRθ θ φ := by
  simp only [resR, resRw, Dval]; ring

theorem resZ_sub (θ φ : ℝ) :
    resZ θ φ - resZw iotaQ θ φ = Dval θ φ * (iota - iotaQ) * torusZθ θ φ := by
  simp only [resZ, resZw, Dval]; ring

/-- **K2 main theorem: the invariance error of torus A.** For all real `θ, φ`,
`|D (∂_φ R + ι ∂_θ R) − 2εR Ps| ≤ 1.23 × 10⁻²³` and `|D (∂_φ z + ι ∂_θ z) − εR² Pz| ≤ 6.94 × 10⁻²⁴`,
with the exact `ι = (75 + √5)/562`. -/
theorem torusA_error_le (θ φ : ℝ) : |resR θ φ| ≤ 123 / 10 ^ 25 ∧ |resZ θ φ| ≤ 694 / 10 ^ 26 := by
  have hD := (torusA_D_bounds θ φ).2
  have hi := iota_sub_iotaQ
  have hcorr : ∀ x : ℝ, |x| ≤ 1 / 5 →
      |Dval θ φ * (iota - iotaQ) * x| ≤ 142 / 100 * (1 / 10 ^ 29) * (1 / 5) := by
    intro x hx
    rw [abs_mul, abs_mul]
    gcongr
  constructor
  · have h1 := resRq_le θ φ
    have h2 := hcorr _ (torusRθ_le θ φ)
    rw [← resR_sub] at h2
    have := abs_sub_abs_le_abs_sub (resR θ φ) (resRw iotaQ θ φ)
    norm_num at h1 h2 ⊢; linarith
  · have h1 := resZq_le θ φ
    have h2 := hcorr _ (torusZθ_le θ φ)
    rw [← resZ_sub] at h2
    have := abs_sub_abs_le_abs_sub (resZ θ φ) (resZw iotaQ θ φ)
    norm_num at h1 h2 ⊢; linarith

/-- The field-line vector field `dR/dφ = 2εR Ps / D` at the torus point. -/
def XRval (θ φ : ℝ) : ℝ :=
  2 * eps * torusR θ φ * Psfun (torusR θ φ) (torusZ θ φ) (Real.cos (2 * φ)) (Real.sin (2 * φ)) /
    Dval θ φ

/-- The field-line vector field `dz/dφ = εR² Pz / D` at the torus point. -/
def XZval (θ φ : ℝ) : ℝ :=
  eps * torusR θ φ ^ 2 * Pzfun (torusR θ φ) (torusZ θ φ) (Real.cos (2 * φ)) (Real.sin (2 * φ)) /
    Dval θ φ

/-- **Unnormalized flow-form invariance error**:
`|∂_φ R + ι ∂_θ R − X_R(K, φ)| ≤ 2.1 × 10⁻²³`, `|∂_φ z + ι ∂_θ z − X_z(K, φ)| ≤ 1.18 × 10⁻²³`. -/
theorem torusA_flow_error (θ φ : ℝ) :
    |torusRφ θ φ + iota * torusRθ θ φ - XRval θ φ| ≤ 21 / 10 ^ 24 ∧
      |torusZφ θ φ + iota * torusZθ θ φ - XZval θ φ| ≤ 118 / 10 ^ 25 := by
  obtain ⟨hD, -⟩ := torusA_D_bounds θ φ
  obtain ⟨hR, hZ⟩ := torusA_error_le θ φ
  have hDpos : 0 < Dval θ φ := by linarith
  have eR : torusRφ θ φ + iota * torusRθ θ φ - XRval θ φ = resR θ φ / Dval θ φ := by
    simp only [resR, resRw, XRval, Dval] at *; field_simp
  have eZ : torusZφ θ φ + iota * torusZθ θ φ - XZval θ φ = resZ θ φ / Dval θ φ := by
    simp only [resZ, resZw, XZval, Dval] at *; field_simp
  rw [eR, eZ, abs_div, abs_div, abs_of_pos hDpos]
  constructor
  · rw [div_le_iff₀ hDpos]; nlinarith [abs_nonneg (resR θ φ)]
  · rw [div_le_iff₀ hDpos]; nlinarith [abs_nonneg (resZ θ φ)]

/-! ## The torus is a radial graph about the magnetic axis -/

/-- **Poloidal winding rate**: `(R − 1) ∂_θ z − z ∂_θ R ≥ 0.015`; the polar angle of
`(R − 1, z)` about the axis is strictly increasing in `θ` (its derivative is this rate over
`(R − 1)² + z²`). -/
theorem torusA_winding (θ φ : ℝ) :
    15 / 1000 ≤ (torusR θ φ - 1) * torusZθ θ φ - torusZ θ φ * torusRθ θ φ := by
  have hκ : (0 : ℝ) < (sig : ℝ) ^ 2 := by have := sig_pos; positivity
  have hlow := le_of_evalC (norm_uu θ) (norm_vv φ) hκ (c0N : ℤ) (evalC_N θ φ)
  rw [show (Polynomial.monomial (2 * M) (Polynomial.monomial (2 * N) ((c0N : ℕ) : ℤ)) : P2) =
    Nmono from rfl, l1_Nsub] at hlow
  have c1 : 1000 * (l1Kron 192 14 (Nint 192 129 - (c0N : ℤ) *
      ((pow2 (192 * (2 * N + 129 * (2 * M))) : ℕ) : ℤ)) : ℝ) + 15 * (sig : ℝ) ^ 2 ≤
        1000 * (c0N : ℝ) := by exact_mod_cast check_N
  push_cast at hlow
  refine le_trans ?_ hlow
  rw [le_div_iff₀ hκ]; linarith

/-- `(R − 1)² + z² ≤ 0.0358`. -/
theorem torusA_rt2_le (θ φ : ℝ) : (torusR θ φ - 1) ^ 2 + torusZ θ φ ^ 2 ≤ 358 / 10000 := by
  have hκ : (0 : ℝ) < (sig : ℝ) ^ 2 := by have := sig_pos; positivity
  have hm : ‖ww θ φ ^ 2‖ = 1 := by simp [norm_ww]
  have h := abs_le_of_evalC (norm_uu θ) (norm_vv φ) hκ hm (evalC_rt2 θ φ)
  rw [l1_rt2poly] at h
  have c : 10000 * (l1Kron 192 14 (rt2int 192 129) : ℝ) ≤ 358 * (sig : ℝ) ^ 2 := by
    exact_mod_cast check_rt2
  refine (le_abs_self _).trans (h.trans ?_)
  rw [div_le_iff₀ hκ]; linarith

/-- `(∂_θ R)² + (∂_θ z)² ≤ 0.0367`. -/
theorem torusA_dK2_le (θ φ : ℝ) : torusRθ θ φ ^ 2 + torusZθ θ φ ^ 2 ≤ 367 / 10000 := by
  have hκ : (0 : ℝ) < (sig : ℝ) ^ 2 := by have := sig_pos; positivity
  have hm : ‖ww θ φ ^ 2‖ = 1 := by simp [norm_ww]
  have h := abs_le_of_evalC (norm_uu θ) (norm_vv φ) hκ hm (evalC_dK2 θ φ)
  rw [l1_dK2poly] at h
  have c : 10000 * (l1Kron 192 14 (dK2int 192 129) : ℝ) ≤ 367 * (sig : ℝ) ^ 2 := by
    exact_mod_cast check_dK2
  refine (le_abs_self _).trans (h.trans ?_)
  rw [div_le_iff₀ hκ]; linarith

/-- `(R − 1)² + z² ≥ 0.006` (Cauchy–Schwarz: winding rate² ≤ rt² |∂_θ K|²). -/
theorem torusA_rt2_ge (θ φ : ℝ) : 6 / 1000 ≤ (torusR θ φ - 1) ^ 2 + torusZ θ φ ^ 2 := by
  have hw := torusA_winding θ φ
  have hd := torusA_dK2_le θ φ
  set a := torusR θ φ - 1; set z := torusZ θ φ
  set p := torusRθ θ φ; set q := torusZθ θ φ
  have hcs : (a * q - z * p) ^ 2 ≤ (a ^ 2 + z ^ 2) * (p ^ 2 + q ^ 2) := by
    nlinarith [sq_nonneg (a * p + z * q)]
  have h1 : (15 / 1000 : ℝ) ^ 2 ≤ (a * q - z * p) ^ 2 := by
    exact pow_le_pow_left₀ (by norm_num) hw 2
  by_contra hcon
  push Not at hcon
  have h0 : 0 ≤ a ^ 2 + z ^ 2 := by positivity
  have : (a ^ 2 + z ^ 2) * (p ^ 2 + q ^ 2) ≤ 6 / 1000 * (367 / 10000) := by
    apply mul_le_mul hcon.le hd (by positivity) (by norm_num)
  nlinarith

/-- The point of torus A at angles `(θ, φ)`, in Cartesian coordinates. -/
def torusPoint (θ φ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![torusR θ φ * Real.cos φ, torusR θ φ * Real.sin φ, torusZ θ φ]

/-- `rt` of a torus point: `√((R − 1)² + z²)` (with `R > 0`). -/
theorem rt_torusPoint (θ φ : ℝ) :
    RationalStellarator.rt (torusPoint θ φ) =
      Real.sqrt ((torusR θ φ - 1) ^ 2 + torusZ θ φ ^ 2) := by
  have hR : 0 ≤ torusR θ φ := by nlinarith [torusA_rt2_le θ φ, sq_nonneg (torusZ θ φ)]
  have hcs := Real.cos_sq_add_sin_sq φ
  have hr2 : RationalStellarator.r2 (torusPoint θ φ) = torusR θ φ ^ 2 := by
    simp only [RationalStellarator.r2, torusPoint]; simp; linear_combination torusR θ φ ^ 2 * hcs
  simp only [RationalStellarator.rt, RationalStellarator.Rc, hr2, Real.sqrt_sq hR]
  simp [torusPoint]

/-- **The graph property (K2)**: torus A lies in the annulus `0.077 ≤ rt ≤ 0.19` about the exact
magnetic axis (inside the tube `rt < 1/2` of `Theory/Fields/TorusTrapping`), and its poloidal
angle about the axis is strictly increasing in `θ` at every `φ` (winding rate `≥ 0.015`). These
are the hypotheses `0 < ρ_min ≤ ρ ≤ R₁ < 1/2` of
`RationalStellarator.rationalStellarator_confined_forever_of_torus` for the profile of the exact
KAM torus near torus A, once K3 provides it and the inversion `θ ↦ polar angle` is carried out. -/
theorem torusA_graph (θ φ : ℝ) :
    77 / 1000 ≤ RationalStellarator.rt (torusPoint θ φ) ∧
      RationalStellarator.rt (torusPoint θ φ) ≤ 19 / 100 ∧
      15 / 1000 ≤ (torusR θ φ - 1) * torusZθ θ φ - torusZ θ φ * torusRθ θ φ := by
  rw [rt_torusPoint]
  refine ⟨?_, ?_, torusA_winding θ φ⟩
  · rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith [torusA_rt2_ge θ φ]
  · rw [Real.sqrt_le_left (by norm_num)]
    linarith [torusA_rt2_le θ φ]

end PlasmaLean.Design.KamTorusA
