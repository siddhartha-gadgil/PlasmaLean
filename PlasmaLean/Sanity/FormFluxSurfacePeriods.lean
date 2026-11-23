/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormFluxSurfacePeriods
public import PlasmaLean.Design.RationalStellaratorContract

/-!
# Sanity checks for the periods of a flux surface (`Theory/Fields/FormFluxSurfacePeriods`)

The surface is the circular torus `R = 1 + a cos θ`, `z = a sin θ` (`circR`, `circZ`).

1. **Accepted: the wire field.** For `toroidal = ∇φ = e_φ/R` (`0 < a < 1`) the poloidal period
   is `0` at every `φ` and the toroidal period is `2π` at every `θ`
   (`toroidal_poloidalPeriod`, `toroidal_toroidalPeriod`). So the class of `B♭` on the surface
   is `[dφ]`: `toroidal_class` exhibits the periodic function, and `toroidal_class_unique`
   shows that the coefficients `(0, 1)` are forced.
2. **Accepted: a uniform field** (in particular `e_z`) has both periods `0` on every doubly
   periodic `C²` torus: it is a gradient (`uniform_periods`, `ez_periods`).
3. **Rejected: the hypothesis `curl B = 0` is needed.** For the shear field `B = x₀ e_z` the
   poloidal circulation at the toroidal angle `φ₀` is `π a² cos φ₀`
   (`shear_poloidalCirculation`): it depends on `φ₀` (`shear_poloidalCirculation_ne`,
   `shear_poloidalPeriod_ne`). Hence the pulled-back form has no potential on the plane
   (`shear_no_potential`) and the field is not curl-free everywhere (`shear_not_curl_free`).
-/

public section
noncomputable section

namespace PlasmaLean.Sanity.FormFluxSurfacePeriods

open Real WithLp PlasmaLean.Vacuum PlasmaLean.Fields PlasmaLean.Contract PlasmaLean.Forms
open PlasmaLean.Design.RationalStellarator PlasmaLean.Design.RationalStellaratorContract
open scoped RealInnerProductSpace

/-! ## The circular torus -/

/-- The circular torus is a doubly periodic `C²` torus, for every `a`. -/
theorem circ_periodicC2Torus (a : ℝ) : PeriodicC2Torus (circR a) (circZ a) :=
  ⟨by unfold circR; fun_prop, by unfold circZ; fun_prop, fun θ φ => by simp [circR],
    fun θ φ => by simp [circZ], fun _ _ => rfl, fun _ _ => rfl⟩

/-- The major radius of the circular torus is positive for `0 < a < 1`. -/
theorem circR_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (θ : ℝ) : 0 < 1 + a * cos θ := by
  nlinarith [neg_one_le_cos θ, cos_le_one θ]

/-- The circular torus (`0 < a < 1`) lies in the region off the axis. -/
theorem circ_mem_domain {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (p : ℝ × ℝ) :
    torusMap (circR a) (circZ a) p ∈ PlasmaLean.Design.RationalStellarator.domain :=
  cylPoint_mem_domain (circR_pos ha ha1 p.1) _ _

/-! ## Accepted: the wire field `∇φ` -/

/-- **The poloidal period of `∇φ` on the circular torus is `0`**, at every toroidal parameter.
The value at `φ = 0` is the fixture `toroidal_circ_circulation_zero`; the other values follow
from the independence theorem. -/
theorem toroidal_poloidalPeriod {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (φ : ℝ) :
    poloidalPeriod toroidal (circR a) (circZ a) φ = 0 := by
  have h := circ_periodicC2Torus a
  rw [h.poloidalPeriod_eq_of_curl_eq_zero toroidal_vacuum.isOpen
    (toroidal_vacuum.contDiffOn.of_le (by norm_num)) toroidal_vacuum.curl_eq_zero
    (circ_mem_domain ha ha1) φ 0, h.poloidalPeriod_eq_poloidalCirculation]
  exact toroidal_circ_circulation_zero ha ha1

/-- The pulled-back form of `∇φ` on the circular torus takes the value `1` on `∂_φ`. -/
theorem toroidal_torusForm_φ {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (θ φ : ℝ) :
    torusForm toroidal (circR a) (circZ a) (θ, φ) (0, 1) = 1 := by
  have hpos := circR_pos ha ha1 θ
  rw [(circ_periodicC2Torus a).torusForm_apply_φ]
  have hd0 : HasDerivAt
      (fun t => (toLp 2 ![(1 + a * cos θ) * cos t, (1 + a * cos θ) * sin t, a * sin θ] : Space))
      (toLp 2 ![(1 + a * cos θ) * (-sin φ), (1 + a * cos θ) * cos φ, 0]) φ :=
    hasDerivAt_space3 ((hasDerivAt_cos φ).const_mul _) ((hasDerivAt_sin φ).const_mul _)
      (hasDerivAt_const φ (a * sin θ))
  have hd : HasDerivAt (fun t => torusMap (circR a) (circZ a) (θ, t))
      (toLp 2 ![(1 + a * cos θ) * (-sin φ), (1 + a * cos θ) * cos φ, 0]) φ := hd0
  rw [hd.deriv]
  change ⟪toroidal (cylPoint (1 + a * cos θ) φ (a * sin θ)), _⟫ = 1
  rw [toroidal_cylPoint hpos]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_three, dotProduct]
  simp
  field_simp
  nlinarith [sin_sq_add_cos_sq φ]

/-- **The toroidal period of `∇φ` on the circular torus is `2π`**, at every poloidal
parameter: the circulation around the wire. -/
theorem toroidal_toroidalPeriod {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (θ : ℝ) :
    toroidalPeriod toroidal (circR a) (circZ a) θ = 2 * π := by
  simp [toroidalPeriod, toroidal_torusForm_φ ha ha1]

/-- **The class of `∇φ` on the circular torus is `[dφ]`**: `β̃ - dφ` is the differential of a
doubly periodic function on the plane. -/
theorem toroidal_class {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∃ g : ℝ × ℝ → ℝ, (∀ p, g (p + (2 * π, 0)) = g p) ∧ (∀ p, g (p + (0, 2 * π)) = g p) ∧
      ∀ p, HasFDerivAt g (torusForm toroidal (circR a) (circZ a) p
        - (0 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ
        - (1 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  have hπ : (2 * π) ≠ 0 := by positivity
  have h := (circ_periodicC2Torus a).exists_periodic_potential_of_curl_eq_zero
    toroidal_vacuum.isOpen (toroidal_vacuum.contDiffOn.of_le (by norm_num))
    toroidal_vacuum.curl_eq_zero (circ_mem_domain ha ha1) 0 0
  rw [toroidal_poloidalPeriod ha ha1, toroidal_toroidalPeriod ha ha1, zero_div,
    div_self hπ] at h
  exact h

/-- **The coefficients of the class are forced**: if `β̃ = a' dθ + b' dφ + dg` for `∇φ` on the
circular torus with `g` doubly periodic, then `a' = 0` and `b' = 1`. -/
theorem toroidal_class_unique {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {a' b' : ℝ} {g : ℝ × ℝ → ℝ}
    (hgθ : ∀ p, g (p + (2 * π, 0)) = g p) (hgφ : ∀ p, g (p + (0, 2 * π)) = g p)
    (hg : ∀ p, HasFDerivAt g (torusForm toroidal (circR a) (circZ a) p
      - a' • ContinuousLinearMap.fst ℝ ℝ ℝ - b' • ContinuousLinearMap.snd ℝ ℝ ℝ) p) :
    a' = 0 ∧ b' = 1 := by
  have hπ : (0 : ℝ) < 2 * π := by positivity
  obtain ⟨h1, h2⟩ := (circ_periodicC2Torus a).periods_eq_of_periodic_potential
    (continuousAt_of_contDiffOn_torus toroidal_vacuum.isOpen
      (toroidal_vacuum.contDiffOn.of_le (by norm_num)) (circ_mem_domain ha ha1)) hgθ hgφ hg 0 0
  rw [toroidal_poloidalPeriod ha ha1] at h1
  rw [toroidal_toroidalPeriod ha ha1] at h2
  constructor
  · nlinarith
  · nlinarith

/-! ## Accepted: uniform fields -/

/-- **A uniform field has both periods `0`** on every doubly periodic `C²` torus: it is the
gradient of `x ↦ ⟪c, x⟫`. -/
theorem uniform_periods {R z : ℝ → ℝ → ℝ} (h : PeriodicC2Torus R z) (c : Space) (θ φ : ℝ) :
    poloidalPeriod (fun _ => c) R z φ = 0 ∧ toroidalPeriod (fun _ => c) R z θ = 0 :=
  h.periods_eq_zero_of_gradient (fun _ => continuousAt_const)
    (Φ := fun x => innerSL ℝ c x) (fun _ => (innerSL ℝ c).hasFDerivAt) θ φ

/-- The uniform vertical field `e_z` has both periods `0` on the circular torus. -/
theorem ez_periods (a θ φ : ℝ) :
    poloidalPeriod (fun _ => (EuclideanSpace.single 2 1 : Space)) (circR a) (circZ a) φ = 0 ∧
      toroidalPeriod (fun _ => (EuclideanSpace.single 2 1 : Space)) (circR a) (circZ a) θ = 0 :=
  uniform_periods (circ_periodicC2Torus a) _ θ φ

/-! ## Rejected: a field with current through the surface -/

/-- The **shear field** `B = x₀ e_z`, with `curl B = -e_y ≠ 0`. -/
def shear (x : Space) : Space := toLp 2 ![0, 0, x 0]

/-- **The poloidal circulation of the shear field on the circular torus is `π a² cos φ₀`.** -/
theorem shear_poloidalCirculation (a φ₀ : ℝ) :
    poloidalCirculation shear (circR a) (circZ a) φ₀ = π * a ^ 2 * cos φ₀ := by
  have hint : ∀ θ, ⟪shear (poloidalLoop (circR a) (circZ a) φ₀ θ),
      deriv (poloidalLoop (circR a) (circZ a) φ₀) θ⟫
        = a * cos φ₀ * cos θ + a ^ 2 * cos φ₀ * cos θ ^ 2 := fun θ => by
    have hR : HasDerivAt (fun t => circR a t φ₀) (a * -sin θ) θ :=
      ((hasDerivAt_cos θ).const_mul a).const_add 1
    have hz : HasDerivAt (fun t => circZ a t φ₀) (a * cos θ) θ :=
      (hasDerivAt_sin θ).const_mul a
    rw [(hasDerivAt_poloidalLoop hR hz).deriv]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_three, dotProduct]
    simp [shear, poloidalLoop, cylPoint, circR, circZ]
    ring
  rw [poloidalCirculation, lineIntegral]
  simp only [hint]
  rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_cos,
    integral_cos_sq]
  simp
  ring

/-- **The poloidal circulation of the shear field depends on the toroidal angle**: its values
at `φ₀ = 0` and `φ₀ = π` differ (for `a ≠ 0`). -/
theorem shear_poloidalCirculation_ne {a : ℝ} (ha : a ≠ 0) :
    poloidalCirculation shear (circR a) (circZ a) 0 ≠
      poloidalCirculation shear (circR a) (circZ a) π := by
  rw [shear_poloidalCirculation, shear_poloidalCirculation, cos_zero, cos_pi]
  intro h
  have h2 : π * a ^ 2 = 0 := by linarith
  exact (mul_ne_zero pi_ne_zero (pow_ne_zero 2 ha)) h2

/-- **The poloidal period of the shear field depends on the toroidal parameter.** -/
theorem shear_poloidalPeriod_ne {a : ℝ} (ha : a ≠ 0) :
    poloidalPeriod shear (circR a) (circZ a) 0 ≠ poloidalPeriod shear (circR a) (circZ a) π := by
  rw [(circ_periodicC2Torus a).poloidalPeriod_eq_poloidalCirculation,
    (circ_periodicC2Torus a).poloidalPeriod_eq_poloidalCirculation]
  exact shear_poloidalCirculation_ne ha

/-- The shear field is smooth. -/
theorem contDiff_shear : ContDiff ℝ 1 shear := by
  refine (contDiff_piLp 2).2 fun i => ?_
  fin_cases i
  · simpa [shear] using (contDiff_const : ContDiff ℝ 1 fun _ : Space => (0 : ℝ))
  · simpa [shear] using (contDiff_const : ContDiff ℝ 1 fun _ : Space => (0 : ℝ))
  · simpa [shear] using (contDiff_piLp_apply (p := 2) (i := (0 : Fin 3)) :
      ContDiff ℝ 1 fun x : Space => x 0)

/-- **The pulled-back form of the shear field is not exact on the plane**: it has no
potential (for `a ≠ 0`), so it is not closed. -/
theorem shear_no_potential {a : ℝ} (ha : a ≠ 0) :
    ¬ ∃ χ : ℝ × ℝ → ℝ, ∀ p, HasFDerivAt χ (torusForm shear (circR a) (circZ a) p) p := by
  rintro ⟨χ, hχ⟩
  exact shear_poloidalPeriod_ne ha ((circ_periodicC2Torus a).poloidalPeriod_eq_of_potential
    (fun _ => contDiff_shear.continuous.continuousAt) hχ 0 π)

/-- **The shear field is not curl-free**: otherwise its poloidal circulation on the circular
torus would not depend on the toroidal angle. -/
theorem shear_not_curl_free : ¬ ∀ x, fieldCurl shear x = 0 := fun hc =>
  shear_poloidalCirculation_ne one_ne_zero
    ((circ_periodicC2Torus 1).poloidalCirculation_eq_of_curl_eq_zero isOpen_univ
      contDiff_shear.contDiffOn (fun x _ => hc x) (fun _ => Set.mem_univ _) 0 π)

end PlasmaLean.Sanity.FormFluxSurfacePeriods
