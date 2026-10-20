/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorForeverCert
public import PlasmaLean.Design.RationalStellaratorForeverCoords
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# An exact invariant torus near torus A traps the field lines forever (KAM route, K3 geometry)

The **geometric half** of all-time field-line confinement for the rational stellarator
`field (1/4)`: an *exactly* invariant torus that is `C¹`-close (within `10⁻⁶`) to the certified
approximate torus A of `Design/KamTorusA` traps every field line starting inside it, for all
time (`rationalStellarator_confined_forever_of_exact`). The existence of such a torus is the
analytic half (KAM, stage K3); here it is the hypothesis `ExactTorus Rk zk`: a `C²` map
`(θ, φ) ↦ (R, z) = (Rk θ φ, zk θ φ)`, `2π`-periodic in `θ`, `π`-periodic in `φ`, satisfying the flow
form `D (∂_φ K + ι ∂_θ K) = (2εR Ps, εR² Pz)` of the field-line equations exactly and
`|K − K_A|, |∂_θ K − ∂_θ K_A| ≤ 10⁻⁶` pointwise.

**Construction of the profile.**
1. *Bounds* (`ExactTorus.rt2_bounds`, `ExactTorus.radial_pos`, `ExactTorus.wind_pos`): from the
   certified facts on torus A (`torusA_rt2_le/ge`, `torusA_winding`, and the new
   `torusA_radial_ge`: `(R − 1) cos θ + z sin θ ≥ 1/20`) and the closeness, the exact torus has
   `0.077 ≤ rt ≤ 0.19`, `(R − 1) cos θ + z sin θ > 0` and winding rate
   `(R − 1) ∂_θ z − z ∂_θ R > 0.0149`.
2. *Poloidal angle* `Θ(θ, φ) = angF θ (R − 1) z` (`Θf`), a `C¹` polar angle of `(R − 1, z)` with
   `Θ(θ + 2π, φ) = Θ + 2π`, `Θ(θ, φ + π) = Θ`, `|Θ − θ| < π/2` and `∂_θ Θ = wind / rt² > 0`.
3. `Φ(θ, φ) = (Θ(θ, φ), φ)` is a `C¹` bijection of `ℝ²` with invertible derivative, hence a
   homeomorphism with `C¹` inverse (`ExactTorus.homeo`, `Homeomorph.contDiff_symm`); the profile
   is `ρ(α, φ) = rt(K(Φ⁻¹(α, φ)))` (`ExactTorus.profile`), a torus profile with
   `0.077 ≤ ρ ≤ 0.19`, `ρ(Θ(θ, φ), φ) = rt(K(θ, φ))` (`ExactTorus.profile_Θf`).
4. *Tangency* (`ExactTorus.tangent`): differentiating `ρ(Θ, φ) = rt(K)` along the invariant
   lines `t ↦ (θ + ι t, φ + t)` and using the invariance equations gives
   `v_r = Dρ · (v_α, v_φ)` on the torus, i.e. `DG · B = 0` there (`fderiv_G_field_torPt`).
5. *Collar bound*: at fixed angles `DG · B` depends on `rt` only through the smooth toroidal
   components `v` of the field, which are uniformly Lipschitz on a compact box
   (`exists_lipschitz_W`); together with a bound on `Dρ` (periodicity and compactness) this gives
   `|DG · B| ≤ L |G|` on the collar `|G| < 1/100`. `RationalStellarator.
   rationalStellarator_confined_forever_of_torus` then concludes.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamTorusA

open Real Set Filter Topology PlasmaLean.Fields PlasmaLean.Design.RationalStellarator

open Real in
/-- An exactly invariant torus `(θ, φ) ↦ (R, z)` of the flow form of the field-line equations of
`field (1/4)`, `C²`, `2π`-periodic in `θ`, `π`-periodic in `φ`, and `C¹`-close (within `10⁻⁶`)
to torus A. -/
structure ExactTorus (Rk zk : ℝ → ℝ → ℝ) : Prop where
  /-- `R` is `C²` in both angles. -/
  smooth_R : ContDiff ℝ 2 (fun p : ℝ × ℝ => Rk p.1 p.2)
  /-- `z` is `C²` in both angles. -/
  smooth_z : ContDiff ℝ 2 (fun p : ℝ × ℝ => zk p.1 p.2)
  /-- `R` is `2π`-periodic in `θ`. -/
  per_θ_R : ∀ θ φ, Rk (θ + 2 * π) φ = Rk θ φ
  /-- `z` is `2π`-periodic in `θ`. -/
  per_θ_z : ∀ θ φ, zk (θ + 2 * π) φ = zk θ φ
  /-- `R` is `π`-periodic in `φ`. -/
  per_φ_R : ∀ θ φ, Rk θ (φ + π) = Rk θ φ
  /-- `z` is `π`-periodic in `φ`. -/
  per_φ_z : ∀ θ φ, zk θ (φ + π) = zk θ φ
  /-- Exact invariance, `R`-component: `D (∂_φ R + ι ∂_θ R) = 2εR Ps`. -/
  inv_R : ∀ θ φ, Dfun (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) *
      (deriv (fun φ' => Rk θ φ') φ + iota * deriv (fun θ' => Rk θ' φ) θ) =
    2 * eps * Rk θ φ * Psfun (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ))
  /-- Exact invariance, `z`-component: `D (∂_φ z + ι ∂_θ z) = εR² Pz`. -/
  inv_z : ∀ θ φ, Dfun (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) *
      (deriv (fun φ' => zk θ φ') φ + iota * deriv (fun θ' => zk θ' φ) θ) =
    eps * Rk θ φ ^ 2 * Pzfun (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ))
  /-- `C⁰`-closeness of `R` to torus A. -/
  close_R : ∀ θ φ, |Rk θ φ - torusR θ φ| ≤ 1 / 10 ^ 6
  /-- `C⁰`-closeness of `z` to torus A. -/
  close_z : ∀ θ φ, |zk θ φ - torusZ θ φ| ≤ 1 / 10 ^ 6
  /-- Closeness of `∂_θ R` to that of torus A. -/
  close_Rθ : ∀ θ φ, |deriv (fun θ' => Rk θ' φ) θ - torusRθ θ φ| ≤ 1 / 10 ^ 6
  /-- Closeness of `∂_θ z` to that of torus A. -/
  close_zθ : ∀ θ φ, |deriv (fun θ' => zk θ' φ) θ - torusZθ θ φ| ≤ 1 / 10 ^ 6

/-! ## Elementary estimates -/

/-- `|R − 1| ≤ 0.19` on torus A. -/
theorem torusA_abs_R_sub_one (θ φ : ℝ) : |torusR θ φ - 1| ≤ 19 / 100 := by
  have h := torusA_rt2_le θ φ
  have hz := sq_nonneg (torusZ θ φ)
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (torusR θ φ - 1 - 19 / 100),
    sq_nonneg (torusR θ φ - 1 + 19 / 100)]

/-- `|z| ≤ 0.19` on torus A. -/
theorem torusA_abs_Z (θ φ : ℝ) : |torusZ θ φ| ≤ 19 / 100 := by
  have h := torusA_rt2_le θ φ
  have h1 := sq_nonneg (torusR θ φ - 1)
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (torusZ θ φ - 19 / 100),
    sq_nonneg (torusZ θ φ + 19 / 100)]

/-- Perturbation of a product: `|x y − x' y'| ≤ δ (B + δ) + A δ`. -/
theorem abs_mul_sub_mul_le {x y x' y' δ A B : ℝ} (hx : |x - x'| ≤ δ) (hy : |y - y'| ≤ δ)
    (hx' : |x'| ≤ A) (hy' : |y'| ≤ B) : |x * y - x' * y'| ≤ δ * (B + δ) + A * δ := by
  have hy2 : |y| ≤ B + δ := by have := abs_sub_abs_le_abs_sub y y'; linarith
  calc |x * y - x' * y'| = |(x - x') * y + x' * (y - y')| := by ring_nf
    _ ≤ |x - x'| * |y| + |x'| * |y - y'| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ δ * (B + δ) + A * δ := by
        have h0 : 0 ≤ δ := (abs_nonneg _).trans hx
        gcongr
        exact (abs_nonneg _).trans hx'

/-- `D > 0` on the box `0.8 ≤ R ≤ 1.2`, `|z| ≤ 0.2`. -/
theorem Dfun_pos {R z C S : ℝ} (hR0 : 8 / 10 ≤ R) (hR1 : R ≤ 12 / 10) (hz : |z| ≤ 2 / 10)
    (hC : |C| ≤ 1) (hS : |S| ≤ 1) : 0 < Dfun R z C S := by
  have hz2 : z ^ 2 ≤ 4 / 100 := by
    have := sq_abs z; nlinarith [abs_nonneg z]
  have hR2 : |R ^ 2 - 1| ≤ 44 / 100 := by rw [abs_le]; constructor <;> nlinarith
  have hf : |sfun R z| ≤ 1 / 10 := by
    have h1 : (R ^ 2 - 1) ^ 2 ≤ (44 / 100) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hR2 2
    rw [sfun, abs_le]; constructor <;> nlinarith [sq_nonneg (R ^ 2 - 1), sq_nonneg z]
  have hg : |sgfun R z| ≤ 1 / 8 := by
    have h5 : |R ^ 2 - 5| ≤ 437 / 100 := by rw [abs_le]; constructor <;> nlinarith
    have hq : |(R ^ 2 - 1) * (R ^ 2 - 5) - 4 * z ^ 2| ≤ 44 / 100 * (437 / 100) + 16 / 100 := by
      calc |(R ^ 2 - 1) * (R ^ 2 - 5) - 4 * z ^ 2|
          ≤ |(R ^ 2 - 1) * (R ^ 2 - 5)| + |4 * z ^ 2| := abs_sub _ _
        _ ≤ 44 / 100 * (437 / 100) + 16 / 100 := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * z ^ 2)]
          gcongr
          linarith
    rw [sgfun, abs_div, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    calc |z| * |(R ^ 2 - 1) * (R ^ 2 - 5) - 4 * z ^ 2| / 4
        ≤ 2 / 10 * (44 / 100 * (437 / 100) + 16 / 100) / 4 := by gcongr
      _ ≤ 1 / 8 := by norm_num
  have hprod1 : |sfun R z * S| ≤ 1 / 10 := by
    rw [abs_mul]; calc |sfun R z| * |S| ≤ 1 / 10 * 1 := by gcongr
      _ = 1 / 10 := by ring
  have hprod2 : |sgfun R z * C| ≤ 1 / 8 := by
    rw [abs_mul]; calc |sgfun R z| * |C| ≤ 1 / 8 * 1 := by gcongr
      _ = 1 / 8 := by ring
  rw [Dfun, eps]
  have := (abs_le.mp hprod1).1
  have := (abs_le.mp hprod2).1
  nlinarith [(abs_le.mp hprod1).2, (abs_le.mp hprod2).2]

/-! ## The poloidal angle and the radius of a torus -/

/-- The poloidal angle about the axis of the point `(Rk θ φ, zk θ φ)` (a smooth lift). -/
def Θf (Rk zk : ℝ → ℝ → ℝ) (θ φ : ℝ) : ℝ := angF θ (Rk θ φ - 1) (zk θ φ)

/-- The distance `√((R − 1)² + z²)` from the axis of the point `(Rk θ φ, zk θ φ)`. -/
def rtK (Rk zk : ℝ → ℝ → ℝ) (θ φ : ℝ) : ℝ := √((Rk θ φ - 1) ^ 2 + zk θ φ ^ 2)

/-- The winding rate `(R − 1) ∂_θ z − z ∂_θ R`. -/
def windK (Rk zk : ℝ → ℝ → ℝ) (θ φ : ℝ) : ℝ :=
  (Rk θ φ - 1) * deriv (fun θ' => zk θ' φ) θ - zk θ φ * deriv (fun θ' => Rk θ' φ) θ

/-- The map `Φ(θ, φ) = (Θ(θ, φ), φ)`. -/
def Φmap (Rk zk : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (Θf Rk zk p.1 p.2, p.2)

namespace ExactTorus

variable {Rk zk : ℝ → ℝ → ℝ} (hK : ExactTorus Rk zk)
include hK

/-- `|R − 1| ≤ 0.19 + 10⁻⁶`. -/
theorem abs_R_sub_one (θ φ : ℝ) : |Rk θ φ - 1| ≤ 19 / 100 + 1 / 10 ^ 6 := by
  have h1 := hK.close_R θ φ
  have h2 := torusA_abs_R_sub_one θ φ
  have := abs_sub_abs_le_abs_sub (Rk θ φ - 1) (torusR θ φ - 1)
  rw [show Rk θ φ - 1 - (torusR θ φ - 1) = Rk θ φ - torusR θ φ by ring] at this
  linarith

/-- `|z| ≤ 0.19 + 10⁻⁶`. -/
theorem abs_Z (θ φ : ℝ) : |zk θ φ| ≤ 19 / 100 + 1 / 10 ^ 6 := by
  have h1 := hK.close_z θ φ
  have h2 := torusA_abs_Z θ φ
  have := abs_sub_abs_le_abs_sub (zk θ φ) (torusZ θ φ)
  linarith

/-- `0.006 − 10⁻⁶ ≤ (R − 1)² + z² ≤ 0.0358 + 10⁻⁶`. -/
theorem rt2_bounds (θ φ : ℝ) :
    6 / 1000 - 1 / 10 ^ 6 ≤ (Rk θ φ - 1) ^ 2 + zk θ φ ^ 2 ∧
      (Rk θ φ - 1) ^ 2 + zk θ φ ^ 2 ≤ 358 / 10000 + 1 / 10 ^ 6 := by
  have hR : |(Rk θ φ - 1) - (torusR θ φ - 1)| ≤ 1 / 10 ^ 6 := by
    rw [show Rk θ φ - 1 - (torusR θ φ - 1) = Rk θ φ - torusR θ φ by ring]; exact hK.close_R θ φ
  have h1 := abs_mul_sub_mul_le hR hR (torusA_abs_R_sub_one θ φ) (torusA_abs_R_sub_one θ φ)
  have h2 := abs_mul_sub_mul_le (hK.close_z θ φ) (hK.close_z θ φ) (torusA_abs_Z θ φ)
    (torusA_abs_Z θ φ)
  have a1 := abs_le.mp h1
  have a2 := abs_le.mp h2
  have l := torusA_rt2_ge θ φ
  have u := torusA_rt2_le θ φ
  constructor <;> nlinarith

/-- `0.8 ≤ R ≤ 1.2` on the exact torus. -/
theorem R_bounds (θ φ : ℝ) : 8 / 10 ≤ Rk θ φ ∧ Rk θ φ ≤ 12 / 10 := by
  have := abs_le.mp (hK.abs_R_sub_one θ φ)
  constructor <;> linarith [this.1, this.2]

/-- `D > 0` on the exact torus. -/
theorem D_pos (θ φ : ℝ) :
    0 < Dfun (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) :=
  Dfun_pos (hK.R_bounds θ φ).1 (hK.R_bounds θ φ).2 ((hK.abs_Z θ φ).trans (by norm_num))
    (abs_cos_le_one _) (abs_sin_le_one _)

/-- `(R − 1) cos θ + z sin θ > 0` on the exact torus. -/
theorem radial_pos (θ φ : ℝ) : 0 < (Rk θ φ - 1) * cos θ + zk θ φ * sin θ := by
  have hA := torusA_radial_ge θ φ
  have h1 : |(Rk θ φ - torusR θ φ) * cos θ| ≤ 1 / 10 ^ 6 := by
    rw [abs_mul]
    calc |Rk θ φ - torusR θ φ| * |cos θ| ≤ 1 / 10 ^ 6 * 1 := by
          gcongr
          · exact hK.close_R θ φ
          · exact abs_cos_le_one θ
      _ = 1 / 10 ^ 6 := by ring
  have h2 : |(zk θ φ - torusZ θ φ) * sin θ| ≤ 1 / 10 ^ 6 := by
    rw [abs_mul]
    calc |zk θ φ - torusZ θ φ| * |sin θ| ≤ 1 / 10 ^ 6 * 1 := by
          gcongr
          · exact hK.close_z θ φ
          · exact abs_sin_le_one θ
      _ = 1 / 10 ^ 6 := by ring
  have e : (Rk θ φ - 1) * cos θ + zk θ φ * sin θ =
      ((torusR θ φ - 1) * cos θ + torusZ θ φ * sin θ) +
        (Rk θ φ - torusR θ φ) * cos θ + (zk θ φ - torusZ θ φ) * sin θ := by ring
  rw [e]
  linarith [(abs_le.mp h1).1, (abs_le.mp h2).1]

/-- The winding rate of the exact torus is `> 0.0149`. -/
theorem wind_pos (θ φ : ℝ) : 149 / 10000 < windK Rk zk θ φ := by
  have hA := torusA_winding θ φ
  have hR : |(Rk θ φ - 1) - (torusR θ φ - 1)| ≤ 1 / 10 ^ 6 := by
    rw [show Rk θ φ - 1 - (torusR θ φ - 1) = Rk θ φ - torusR θ φ by ring]; exact hK.close_R θ φ
  have h1 := abs_mul_sub_mul_le hR (hK.close_zθ θ φ) (torusA_abs_R_sub_one θ φ)
    (torusZθ_le θ φ)
  have h2 := abs_mul_sub_mul_le (hK.close_z θ φ) (hK.close_Rθ θ φ) (torusA_abs_Z θ φ)
    (torusRθ_le θ φ)
  rw [windK]
  have a1 := (abs_le.mp h1).1
  have a2 := (abs_le.mp h2).2
  nlinarith

/-- The radius of the exact torus is positive. -/
theorem rtK_pos (θ φ : ℝ) : 0 < rtK Rk zk θ φ :=
  Real.sqrt_pos.mpr (by linarith [(hK.rt2_bounds θ φ).1])

/-- `0.077 ≤ rt ≤ 0.19` on the exact torus. -/
theorem rtK_bounds (θ φ : ℝ) : 77 / 1000 ≤ rtK Rk zk θ φ ∧ rtK Rk zk θ φ ≤ 19 / 100 := by
  obtain ⟨l, u⟩ := hK.rt2_bounds θ φ
  constructor
  · rw [rtK, Real.le_sqrt (by norm_num) (by positivity)]; linarith
  · rw [rtK, Real.sqrt_le_left (by norm_num)]; linarith

/-- The exact torus in polar form about the axis: `R − 1 = rt cos Θ`, `z = rt sin Θ`. -/
theorem polar (θ φ : ℝ) :
    Rk θ φ - 1 = rtK Rk zk θ φ * cos (Θf Rk zk θ φ) ∧
      zk θ φ = rtK Rk zk θ φ * sin (Θf Rk zk θ φ) :=
  angF_polar (hK.radial_pos θ φ)

/-- `R` is `C¹`. -/
theorem contDiff_R : ContDiff ℝ 1 (fun p : ℝ × ℝ => Rk p.1 p.2) := hK.smooth_R.of_le (by norm_num)

/-- `z` is `C¹`. -/
theorem contDiff_Z : ContDiff ℝ 1 (fun p : ℝ × ℝ => zk p.1 p.2) := hK.smooth_z.of_le (by norm_num)

/-- `R` is differentiable. -/
theorem differentiable_R : Differentiable ℝ (fun p : ℝ × ℝ => Rk p.1 p.2) :=
  hK.contDiff_R.differentiable (by norm_num)

/-- `z` is differentiable. -/
theorem differentiable_Z : Differentiable ℝ (fun p : ℝ × ℝ => zk p.1 p.2) :=
  hK.contDiff_Z.differentiable (by norm_num)

/-- The `θ`-partial derivative of `R`. -/
theorem hasDerivAt_R_θ (θ φ : ℝ) :
    HasDerivAt (fun θ' => Rk θ' φ) (deriv (fun θ' => Rk θ' φ) θ) θ := by
  have hd : DifferentiableAt ℝ ((fun p : ℝ × ℝ => Rk p.1 p.2) ∘ fun θ' => (θ', φ)) θ :=
    (hK.differentiable_R _).comp θ (by fun_prop)
  exact hd.hasDerivAt

/-- The `θ`-partial derivative of `z`. -/
theorem hasDerivAt_Z_θ (θ φ : ℝ) :
    HasDerivAt (fun θ' => zk θ' φ) (deriv (fun θ' => zk θ' φ) θ) θ := by
  have hd : DifferentiableAt ℝ ((fun p : ℝ × ℝ => zk p.1 p.2) ∘ fun θ' => (θ', φ)) θ :=
    (hK.differentiable_Z _).comp θ (by fun_prop)
  exact hd.hasDerivAt

/-- `∂_θ Θ = wind / rt²`. -/
theorem hasDerivAt_Θf_θ (θ φ : ℝ) :
    HasDerivAt (fun θ' => Θf Rk zk θ' φ) (windK Rk zk θ φ / rtK Rk zk θ φ ^ 2) θ := by
  have h := hasDerivAt_angF (θf := id) (af := fun θ' => Rk θ' φ - 1) (bf := fun θ' => zk θ' φ)
    (hasDerivAt_id θ) ((hK.hasDerivAt_R_θ θ φ).sub_const 1) (hK.hasDerivAt_Z_θ θ φ)
    (hK.radial_pos θ φ)
  rw [rtK, Real.sq_sqrt (by positivity), windK]
  exact h

/-- `∂_θ Θ > 0`. -/
theorem deriv_Θf_pos (θ φ : ℝ) : 0 < deriv (fun θ' => Θf Rk zk θ' φ) θ := by
  rw [(hK.hasDerivAt_Θf_θ θ φ).deriv]
  have := hK.wind_pos θ φ
  have := hK.rtK_pos θ φ
  positivity

/-- `Θ(θ + 2π, φ) = Θ(θ, φ) + 2π`. -/
theorem Θf_add_two_pi (θ φ : ℝ) : Θf Rk zk (θ + 2 * π) φ = Θf Rk zk θ φ + 2 * π := by
  simp only [Θf, angF, hK.per_θ_R, hK.per_θ_z, cos_add_two_pi, sin_add_two_pi]
  ring

/-- `Θ(θ, φ + π) = Θ(θ, φ)`. -/
theorem Θf_add_pi (θ φ : ℝ) : Θf Rk zk θ (φ + π) = Θf Rk zk θ φ := by
  simp only [Θf, hK.per_φ_R, hK.per_φ_z]

/-- `rt` of the exact torus is `2π`-periodic in `θ`. -/
theorem rtK_add_two_pi (θ φ : ℝ) : rtK Rk zk (θ + 2 * π) φ = rtK Rk zk θ φ := by
  simp only [rtK, hK.per_θ_R, hK.per_θ_z]

/-- `rt` of the exact torus is `π`-periodic in `φ`. -/
theorem rtK_add_pi (θ φ : ℝ) : rtK Rk zk θ (φ + π) = rtK Rk zk θ φ := by
  simp only [rtK, hK.per_φ_R, hK.per_φ_z]

end ExactTorus

/-! ## The map `Φ(θ, φ) = (Θ(θ, φ), φ)` and its inverse -/

/-- The candidate derivative of `Φ` at `p`. -/
def dΦ (Rk zk : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (fderiv ℝ (fun p : ℝ × ℝ => Θf Rk zk p.1 p.2) p).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)

namespace ExactTorus

variable {Rk zk : ℝ → ℝ → ℝ} (hK : ExactTorus Rk zk)
include hK

/-- `Θ` is `C¹` on `ℝ²`. -/
theorem contDiff_Θf : ContDiff ℝ 1 (fun p : ℝ × ℝ => Θf Rk zk p.1 p.2) := by
  have hR := hK.contDiff_R
  have hZ := hK.contDiff_Z
  have hnum : ContDiff ℝ 1
      (fun p : ℝ × ℝ => zk p.1 p.2 * cos p.1 - (Rk p.1 p.2 - 1) * sin p.1) := by fun_prop
  have hden : ContDiff ℝ 1
      (fun p : ℝ × ℝ => (Rk p.1 p.2 - 1) * cos p.1 + zk p.1 p.2 * sin p.1) := by fun_prop
  exact contDiff_fst.add (Real.contDiff_arctan.comp
    (hnum.div hden fun p => (hK.radial_pos p.1 p.2).ne'))

/-- `Φ` is `C¹`. -/
theorem contDiff_Φmap : ContDiff ℝ 1 (Φmap Rk zk) := hK.contDiff_Θf.prodMk contDiff_snd

/-- `dΦ` is the derivative of `Φ`. -/
theorem hasFDerivAt_Φmap (p : ℝ × ℝ) : HasFDerivAt (Φmap Rk zk) (dΦ Rk zk p) p :=
  ((hK.contDiff_Θf.differentiable (by norm_num) p).hasFDerivAt).prodMk (hasFDerivAt_snd)

/-- `DΘ · (1, 0) = ∂_θ Θ = wind / rt²`. -/
theorem fderiv_Θf_one_zero (p : ℝ × ℝ) :
    fderiv ℝ (fun p : ℝ × ℝ => Θf Rk zk p.1 p.2) p (1, 0) =
      windK Rk zk p.1 p.2 / rtK Rk zk p.1 p.2 ^ 2 := by
  have hD := (hK.contDiff_Θf.differentiable (by norm_num) p).hasFDerivAt
  have h := hD.comp_hasDerivAt_of_eq p.1
    (HasDerivAt.prodMk (hasDerivAt_id p.1) (hasDerivAt_const p.1 p.2)) rfl
  exact h.unique (hK.hasDerivAt_Θf_θ p.1 p.2)

/-- `dΦ` is injective. -/
theorem dΦ_injective (p : ℝ × ℝ) : Function.Injective (dΦ Rk zk p) := by
  refine (injective_iff_map_eq_zero _).mpr fun v hv => ?_
  have h2 : v.2 = 0 := by simpa [dΦ] using congrArg Prod.snd hv
  have h1 : fderiv ℝ (fun p : ℝ × ℝ => Θf Rk zk p.1 p.2) p v = 0 := by
    simpa [dΦ] using congrArg Prod.fst hv
  have hv' : v = v.1 • ((1 : ℝ), (0 : ℝ)) := by ext <;> simp [h2]
  rw [hv', map_smul, fderiv_Θf_one_zero hK, smul_eq_mul] at h1
  have hpos : 0 < windK Rk zk p.1 p.2 / rtK Rk zk p.1 p.2 ^ 2 := by
    have := hK.wind_pos p.1 p.2
    have := hK.rtK_pos p.1 p.2
    positivity
  have hv1 : v.1 = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h hpos.ne'
  exact Prod.ext hv1 h2

/-- The derivative of `Φ` as a continuous linear equivalence. -/
def dΦequiv (p : ℝ × ℝ) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  (LinearEquiv.ofInjectiveEndo (dΦ Rk zk p).toLinearMap (hK.dΦ_injective p)).toContinuousLinearEquiv

/-- `Φ` has the invertible strict derivative `dΦequiv` everywhere. -/
theorem hasStrictFDerivAt_Φmap (p : ℝ × ℝ) :
    HasStrictFDerivAt (Φmap Rk zk) (hK.dΦequiv p : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p := by
  have h := (hK.contDiff_Φmap.contDiffAt (x := p)).hasStrictFDerivAt (by norm_num)
  rw [(hK.hasFDerivAt_Φmap p).fderiv] at h
  have e : (hK.dΦequiv p : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = dΦ Rk zk p :=
    ContinuousLinearMap.ext fun v => rfl
  rw [e]; exact h

/-- `Φ` is a bijection of `ℝ²`: `θ ↦ Θ(θ, φ)` is strictly increasing and onto. -/
theorem Φmap_bijective : Function.Bijective (Φmap Rk zk) := by
  constructor
  · intro p q hpq
    simp only [Φmap, Prod.mk.injEq] at hpq
    obtain ⟨h1, h2⟩ := hpq
    have hmono : StrictMono (fun θ => Θf Rk zk θ p.2) :=
      strictMono_of_deriv_pos (fun θ => hK.deriv_Θf_pos θ p.2)
    rw [← h2] at h1
    exact Prod.ext (hmono.injective h1) h2
  · intro q
    have hcont : Continuous (fun θ => Θf Rk zk θ q.2) :=
      continuous_iff_continuousAt.2 fun θ => (hK.hasDerivAt_Θf_θ θ q.2).continuousAt
    have hb : ∀ θ, |Θf Rk zk θ q.2 - θ| < π / 2 := fun θ => angF_sub_mem _ _ _
    have htop : Tendsto (fun θ => Θf Rk zk θ q.2) atTop atTop :=
      tendsto_atTop_mono (fun θ => by simp only [id]; linarith [(abs_lt.mp (hb θ)).1])
        (tendsto_atTop_add_const_right _ (-(π / 2)) tendsto_id)
    have hbot : Tendsto (fun θ => Θf Rk zk θ q.2) atBot atBot :=
      tendsto_atBot_mono (fun θ => by simp only [id]; linarith [(abs_lt.mp (hb θ)).2])
        (tendsto_atBot_add_const_right _ (π / 2) tendsto_id)
    obtain ⟨θ, hθ⟩ := hcont.surjective htop hbot q.1
    exact ⟨(θ, q.2), by simp [Φmap, hθ]⟩

/-- `Φ` as a homeomorphism of `ℝ²` (continuous, bijective, open by the inverse function
theorem). -/
def homeo : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  (Equiv.ofBijective (Φmap Rk zk) hK.Φmap_bijective).toHomeomorphOfContinuousOpen
    hK.contDiff_Φmap.continuous
    (isOpenMap_of_hasStrictFDerivAt_equiv (f' := hK.dΦequiv) hK.hasStrictFDerivAt_Φmap)

/-- The homeomorphism is `Φ`. -/
theorem coe_homeo : ⇑hK.homeo = Φmap Rk zk := rfl

/-- `Φ ∘ Φ⁻¹ = id`. -/
theorem Φmap_symm (q : ℝ × ℝ) : Φmap Rk zk (hK.homeo.symm q) = q := by
  rw [← hK.coe_homeo]; exact hK.homeo.apply_symm_apply q

/-- `Φ⁻¹ ∘ Φ = id`. -/
theorem symm_Φmap (p : ℝ × ℝ) : hK.homeo.symm (Φmap Rk zk p) = p := by
  rw [← hK.coe_homeo]; exact hK.homeo.symm_apply_apply p

/-- `Φ⁻¹` preserves the toroidal angle. -/
theorem symm_snd (α φ : ℝ) : (hK.homeo.symm (α, φ)).2 = φ := by
  have := congrArg Prod.snd (hK.Φmap_symm (α, φ)); exact this

/-- `Θ(Φ⁻¹(α, φ)) = α`. -/
theorem Θf_symm (α φ : ℝ) : Θf Rk zk (hK.homeo.symm (α, φ)).1 φ = α := by
  have h1 := congrArg Prod.fst (hK.Φmap_symm (α, φ))
  simp only [Φmap] at h1
  rw [hK.symm_snd α φ] at h1
  exact h1

/-- **`Φ⁻¹` is `C¹`** (inverse function theorem). -/
theorem contDiff_symm : ContDiff ℝ 1 hK.homeo.symm :=
  hK.homeo.contDiff_symm (f₀' := hK.dΦequiv) (fun a => (hK.hasStrictFDerivAt_Φmap a).hasFDerivAt)
    hK.contDiff_Φmap

/-! ## The profile -/

/-- **The profile of the exact torus**: `ρ(α, φ) = rt(K(Φ⁻¹(α, φ)))`, the distance from the axis
of the torus point with poloidal angle `α` about the axis and toroidal angle `φ`. -/
def profile (α φ : ℝ) : ℝ := rtK Rk zk (hK.homeo.symm (α, φ)).1 (hK.homeo.symm (α, φ)).2

/-- `ρ(Θ(θ, φ), φ) = rt(K(θ, φ))`. -/
theorem profile_Θf (θ φ : ℝ) : hK.profile (Θf Rk zk θ φ) φ = rtK Rk zk θ φ := by
  rw [profile, show ((Θf Rk zk θ φ, φ) : ℝ × ℝ) = Φmap Rk zk (θ, φ) from rfl, symm_Φmap]

/-- `rt` of the exact torus is `C¹`. -/
theorem contDiff_rtK : ContDiff ℝ 1 (fun p : ℝ × ℝ => rtK Rk zk p.1 p.2) := by
  have hR := hK.contDiff_R
  have hZ := hK.contDiff_Z
  have h : ContDiff ℝ 1 (fun p : ℝ × ℝ => (Rk p.1 p.2 - 1) ^ 2 + zk p.1 p.2 ^ 2) := by fun_prop
  exact h.sqrt fun p => by linarith [(hK.rt2_bounds p.1 p.2).1]

/-- The profile is `C¹`. -/
theorem contDiff_profile : ContDiff ℝ 1 (fun p : ℝ × ℝ => hK.profile p.1 p.2) :=
  hK.contDiff_rtK.comp hK.contDiff_symm

/-- `ρ` is `2π`-periodic in the poloidal angle. -/
theorem profile_add_two_pi (α φ : ℝ) : hK.profile (α + 2 * π) φ = hK.profile α φ := by
  have h : Φmap Rk zk ((hK.homeo.symm (α, φ)).1 + 2 * π, (hK.homeo.symm (α, φ)).2) =
      (α + 2 * π, φ) := by
    simp only [Φmap, hK.Θf_add_two_pi, hK.symm_snd, hK.Θf_symm]
  rw [profile, ← h, symm_Φmap, hK.rtK_add_two_pi]
  rfl

/-- `ρ` is `π`-periodic in the toroidal angle. -/
theorem profile_add_pi (α φ : ℝ) : hK.profile α (φ + π) = hK.profile α φ := by
  have h : Φmap Rk zk ((hK.homeo.symm (α, φ)).1, (hK.homeo.symm (α, φ)).2 + π) =
      (α, φ + π) := by
    simp only [Φmap, hK.Θf_add_pi, hK.symm_snd, hK.Θf_symm]
  rw [profile, ← h, symm_Φmap, hK.rtK_add_pi]
  rfl

/-- **The profile is a torus profile.** -/
theorem torusProfile : TorusProfile hK.profile where
  differentiable := hK.contDiff_profile.differentiable (by norm_num)
  periodic_left := hK.profile_add_two_pi
  periodic_right := fun α φ => by
    rw [show φ + 2 * π = (φ + π) + π by ring, hK.profile_add_pi, hK.profile_add_pi]

/-- `0.077 ≤ ρ ≤ 0.19`. -/
theorem profile_bounds (α φ : ℝ) : 77 / 1000 ≤ hK.profile α φ ∧ hK.profile α φ ≤ 19 / 100 :=
  hK.rtK_bounds _ _

end ExactTorus

/-! ## Tangency of the field to the torus -/

namespace ExactTorus

variable {Rk zk : ℝ → ℝ → ℝ} (hK : ExactTorus Rk zk)
include hK

/-- **Tangency.** On the torus `r = ρ(α, φ)` the toroidal components of the field satisfy
`v_r = Dρ(α, φ) · (v_α, v_φ)`: differentiate `ρ(Θ, φ) = rt(K)` along the invariant line
`t ↦ (θ + ι t, φ + t)` and use the invariance equations. -/
theorem tangent (α φ : ℝ) :
    vRad (hK.profile α φ) (cos α) (sin α) (cos (2 * φ)) (sin (2 * φ)) =
      fderiv ℝ (fun p : ℝ × ℝ => hK.profile p.1 p.2) (α, φ)
        (vPol (hK.profile α φ) (cos α) (sin α) (cos (2 * φ)) (sin (2 * φ)),
          vTor (hK.profile α φ) (cos α) (sin α) (cos (2 * φ)) (sin (2 * φ))) := by
  set θ := (hK.homeo.symm (α, φ)).1
  have hΘ : Θf Rk zk θ φ = α := hK.Θf_symm α φ
  have hr0 : hK.profile α φ = rtK Rk zk θ φ := by rw [← hK.profile_Θf θ φ, hΘ]
  obtain ⟨hpa, hpb⟩ := hK.polar θ φ
  rw [hΘ] at hpa hpb
  have hrpos := hK.rtK_pos θ φ
  have hr2 : rtK Rk zk θ φ ^ 2 = (Rk θ φ - 1) ^ 2 + zk θ φ ^ 2 :=
    Real.sq_sqrt (by positivity)
  -- derivatives along the invariant line `t ↦ (θ + ι t, φ + t)`
  have hLR := hasDerivAt_line hK.differentiable_R θ φ iota 1
  have hLZ := hasDerivAt_line hK.differentiable_Z θ φ iota 1
  set La := iota * deriv (fun θ' => Rk θ' φ) θ + 1 * deriv (fun φ' => Rk θ φ') φ with hLa
  set Lb := iota * deriv (fun θ' => zk θ' φ) θ + 1 * deriv (fun φ' => zk θ φ') φ with hLb
  have hpos0 : 0 < (Rk (θ + 0 * iota) (φ + 0 * 1) - 1) * cos (θ + 0 * iota) +
      zk (θ + 0 * iota) (φ + 0 * 1) * sin (θ + 0 * iota) := by
    simpa using hK.radial_pos θ φ
  have hΘl := hasDerivAt_angF (hasDerivAt_affine θ iota) (hLR.sub_const 1) hLZ hpos0
  simp only [zero_mul, add_zero] at hΘl
  set LΘ := ((Rk θ φ - 1) * Lb - zk θ φ * La) / ((Rk θ φ - 1) ^ 2 + zk θ φ ^ 2) with hLΘ
  -- the identity `ρ(Θ, φ) = rt(K)` along the line
  set D := fderiv ℝ (fun p : ℝ × ℝ => hK.profile p.1 p.2) (α, φ)
  have hD : HasFDerivAt (fun p : ℝ × ℝ => hK.profile p.1 p.2) D (α, φ) :=
    (hK.contDiff_profile.differentiable (by norm_num) _).hasFDerivAt
  have hc : HasDerivAt (fun t : ℝ => (Θf Rk zk (θ + t * iota) (φ + t * 1), φ + t * 1))
      (LΘ, 1) 0 := HasDerivAt.prodMk hΘl (hasDerivAt_affine φ 1)
  have h1 := hD.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp [hΘ])
  have hfun : ((fun p : ℝ × ℝ => hK.profile p.1 p.2) ∘
      fun t : ℝ => (Θf Rk zk (θ + t * iota) (φ + t * 1), φ + t * 1)) =
      fun t => rtK Rk zk (θ + t * iota) (φ + t * 1) :=
    funext fun t => hK.profile_Θf _ _
  rw [hfun] at h1
  have hf := ((hLR.sub_const 1).pow 2).add (hLZ.pow 2)
  have hs := hf.sqrt (ne_of_gt (by
    simp only [Pi.add_apply, Pi.pow_apply, zero_mul, add_zero]
    linarith [(hK.rt2_bounds θ φ).1]))
  have hkey := h1.unique hs
  simp only [Pi.add_apply, Pi.pow_apply, zero_mul, add_zero, Nat.cast_ofNat] at hkey
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, pow_one] at hkey
  -- the invariance equations
  have hDpos := hK.D_pos θ φ
  have hIR : Dfun (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) * La =
      2 * eps * Rk θ φ * Psfun (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) := by
    rw [hLa, ← hK.inv_R θ φ]; ring
  have hIZ : Dfun (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) * Lb =
      eps * Rk θ φ ^ 2 * Pzfun (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) := by
    rw [hLb, ← hK.inv_z θ φ]; ring
  -- algebra
  have hR1 : 1 + rtK Rk zk θ φ * cos α = Rk θ φ := by linarith
  have hZ1 : rtK Rk zk θ φ * sin α = zk θ φ := by linarith
  have hRpos : 0 < Rk θ φ := by linarith [(hK.R_bounds θ φ).1]
  have hvec : ((vPol (rtK Rk zk θ φ) (cos α) (sin α) (cos (2 * φ)) (sin (2 * φ)),
      vTor (rtK Rk zk θ φ) (cos α) (sin α) (cos (2 * φ)) (sin (2 * φ))) : ℝ × ℝ) =
      vTor (rtK Rk zk θ φ) (cos α) (sin α) (cos (2 * φ)) (sin (2 * φ)) • (LΘ, (1 : ℝ)) := by
    ext
    · simp only [Prod.smul_mk, smul_eq_mul, vPol, vTor, hR1, hZ1, cylBR, cylBZ, cylBT, hLΘ]
      rw [show cos α = (Rk θ φ - 1) / rtK Rk zk θ φ by field_simp; linarith,
        show sin α = zk θ φ / rtK Rk zk θ φ by field_simp; linarith, ← hr2]
      have hLa' : La = 2 * eps * Rk θ φ *
          Psfun (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) /
            Dfun (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) := by
        field_simp; linarith
      have hLb' : Lb = eps * Rk θ φ ^ 2 *
          Pzfun (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) /
            Dfun (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) := by
        field_simp; linarith
      rw [hLa', hLb']
      field_simp
    · simp
  rw [hr0, hvec, map_smul, smul_eq_mul, hkey]
  simp only [vRad, vTor, hR1, hZ1, cylBR, cylBZ, cylBT]
  rw [show cos α = (Rk θ φ - 1) / rtK Rk zk θ φ by field_simp; linarith,
    show sin α = zk θ φ / rtK Rk zk θ φ by field_simp; linarith]
  have hLa' : La = 2 * eps * Rk θ φ *
      Psfun (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) /
        Dfun (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) := by
    field_simp; linarith
  have hLb' : Lb = eps * Rk θ φ ^ 2 *
      Pzfun (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) /
        Dfun (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) := by
    field_simp; linarith
  rw [hLa', hLb', show √((Rk θ φ - 1) ^ 2 + zk θ φ ^ 2) = rtK Rk zk θ φ from rfl]
  field_simp

end ExactTorus

/-! ## All-time confinement -/

namespace ExactTorus

variable {Rk zk : ℝ → ℝ → ℝ} (hK : ExactTorus Rk zk)
include hK

/-- The derivative of the profile is bounded (it is continuous and doubly periodic). -/
theorem exists_bound_fderiv_profile :
    ∃ C, ∀ p, ‖fderiv ℝ (fun p : ℝ × ℝ => hK.profile p.1 p.2) p‖ ≤ C := by
  set F := fun p : ℝ × ℝ => hK.profile p.1 p.2
  have hcont : Continuous (fderiv ℝ F) := hK.contDiff_profile.continuous_fderiv (by norm_num)
  have hper : ∀ v : ℝ × ℝ, (fun x => F (x + v)) = F → ∀ x, fderiv ℝ F (x + v) = fderiv ℝ F x :=
    fun v hv x => by rw [← fderiv_comp_add_right (𝕜 := ℝ) (f := F) (x := x) v, hv]
  refine exists_bound_of_periodic hcont (fun a b => ?_) (fun a b => ?_)
  · have h := hper ((2 * π, 0) : ℝ × ℝ) (funext fun x => by
      simp only [F, Prod.fst_add, Prod.snd_add, add_zero, hK.profile_add_two_pi]) (a, b)
    simpa using h
  · have h := hper ((0, 2 * π) : ℝ × ℝ) (funext fun x => by
      simp only [F, Prod.fst_add, Prod.snd_add, add_zero, hK.torusProfile.periodic_right]) (a, b)
    simpa using h

end ExactTorus

/-- **All-time confinement from an exact invariant torus near torus A** (the geometric half of
the KAM route). If `(Rk, zk)` is an exactly invariant torus of `field (1/4)`, `C²`, with the
periodicities of torus A and `C¹`-close to it within `10⁻⁶` (`ExactTorus`), then there is a torus
profile `ρ` with `0.077 ≤ ρ ≤ 0.19` such that every two-sided field line of `field (1/4)` starting
on the exact magnetic axis or inside the torus `rt < ρ(θs, φs)` stays inside it, in particular
within distance `0.19` of the axis, **for all time**. -/
theorem rationalStellarator_confined_forever_of_exact {Rk zk : ℝ → ℝ → ℝ}
    (hK : ExactTorus Rk zk) :
    ∃ ρ : ℝ → ℝ → ℝ, Fields.TorusProfile ρ ∧ (∀ a b, 77 / 1000 ≤ ρ a b) ∧
      (∀ a b, ρ a b ≤ 19 / 100) ∧
      ∀ {γ : ℝ → Space}, IsFieldLine (field (1 / 4)) γ →
        (rt (γ 0) = 0 ∨ rt (γ 0) < ρ (θs (γ 0)) (φs (γ 0))) →
        ∀ t, rt (γ t) ≤ 19 / 100 ∧ (rt (γ t) = 0 ∨ rt (γ t) < ρ (θs (γ t)) (φs (γ t))) := by
  obtain ⟨Cρ, hCρ⟩ := hK.exists_bound_fderiv_profile
  obtain ⟨L, hL⟩ := exists_lipschitz_W Cρ
  have hρ := hK.torusProfile
  refine ⟨hK.profile, hρ, fun a b => (hK.profile_bounds a b).1,
    fun a b => (hK.profile_bounds a b).2, ?_⟩
  intro γ hγ h0
  refine rationalStellarator_confined_forever_of_torus (1 / 4) hρ (ρmin := 77 / 1000)
    (R₁ := 19 / 100) (g₀ := 1 / 100) (L := L) (by norm_num)
    (fun a b => (hK.profile_bounds a b).1) (fun a b => (hK.profile_bounds a b).2) (by norm_num)
    (by norm_num) ?_ hγ h0
  intro y hy hpos hG
  have hyeq : y = torPt (rt y) (θs y) (φs y) := eq_torPt hy
  obtain ⟨hr0l, hr0u⟩ := hK.profile_bounds (θs y) (φs y)
  have hrr := abs_lt.mp hG
  -- `DG · B` at `y` and on the torus, in toroidal coordinates
  have hF := fderiv_G_field_torPt hρ hpos hy (θs y) (φs y)
  rw [← hyeq] at hF
  rw [hF]
  have htan := hK.tangent (θs y) (φs y)
  set D := fderiv ℝ (fun p : ℝ × ℝ => hK.profile p.1 p.2) (θs y, φs y) with hDdef
  have hlin : ∀ x x' : ℝ, D (x, x') = x * D (1, 0) + x' * D (0, 1) := fun x x' => by
    rw [show ((x, x') : ℝ × ℝ) = x • ((1 : ℝ), (0 : ℝ)) + x' • ((0 : ℝ), (1 : ℝ)) by simp,
      map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hb1 : |D (1, 0)| ≤ Cρ := by
    have := D.le_opNorm (1, 0)
    rw [Real.norm_eq_abs] at this
    simpa using this.trans (by simpa using hCρ (θs y, φs y))
  have hb2 : |D (0, 1)| ≤ Cρ := by
    have := D.le_opNorm (0, 1)
    rw [Real.norm_eq_abs] at this
    simpa using this.trans (by simpa using hCρ (θs y, φs y))
  set r₀ := hK.profile (θs y) (φs y)
  set q : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ := (rt y, cos (θs y), sin (θs y), cos (2 * φs y),
    sin (2 * φs y), D (1, 0), D (0, 1))
  set q₀ : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ := (r₀, cos (θs y), sin (θs y), cos (2 * φs y),
    sin (2 * φs y), D (1, 0), D (0, 1))
  have hWq : vRad (rt y) (cos (θs y)) (sin (θs y)) (cos (2 * φs y)) (sin (2 * φs y)) -
      D (vPol (rt y) (cos (θs y)) (sin (θs y)) (cos (2 * φs y)) (sin (2 * φs y)),
        vTor (rt y) (cos (θs y)) (sin (θs y)) (cos (2 * φs y)) (sin (2 * φs y))) = Wfun q := by
    rw [hlin]; simp only [Wfun, q]; ring
  have hWq₀ : Wfun q₀ = 0 := by
    simp only [Wfun, q₀]; rw [htan, hlin]; ring
  have hmem : ∀ x : ℝ, 1 / 20 ≤ x → x ≤ 1 / 4 → (x, cos (θs y), sin (θs y), cos (2 * φs y),
      sin (2 * φs y), D (1, 0), D (0, 1)) ∈ Wbox Cρ := fun x h1 h2 =>
    ⟨⟨h1, h2⟩, ⟨neg_one_le_cos _, cos_le_one _⟩, ⟨neg_one_le_sin _, sin_le_one _⟩,
      ⟨neg_one_le_cos _, cos_le_one _⟩, ⟨neg_one_le_sin _, sin_le_one _⟩, abs_le.mp hb1,
      abs_le.mp hb2⟩
  have hq : q ∈ Wbox Cρ := hmem _ (by linarith) (by linarith)
  have hq₀ : q₀ ∈ Wbox Cρ := hmem _ (by linarith) (by linarith)
  rw [hWq, ← sub_zero (Wfun q), ← hWq₀]
  exact hL q q₀ hq hq₀ rfl

end PlasmaLean.Design.KamTorusA
