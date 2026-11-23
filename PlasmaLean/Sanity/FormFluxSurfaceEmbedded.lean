/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormFluxSurfaceEmbedded
public import PlasmaLean.Sanity.FormFluxSurfacePeriods

/-!
# Sanity checks for embedded flux surfaces (`Theory/Fields/FormFluxSurfaceEmbedded`)

1. **Accepted: the circular torus** `R = 1 + a cos θ`, `z = a sin θ` with `0 < a < 1` is an
   `EmbeddedTorus` (`circ_embeddedTorus`), by the section criterion; so its descended map is a
   `C²` embedding of the 2-torus (`circ_isSmoothEmbedding`). On it the class of the wire field
   `∇φ` is `[dφ]`, as a statement on the torus (`toroidal_class_on_torus`), and the coefficients
   are forced (`toroidal_class_on_torus_unique`).
2. **Rejected: a doubly covered torus** `R = 1 + a cos 2θ`, `z = a sin 2θ`. It is a
   `PeriodicC2Torus` (`dbl_periodicC2Torus`) and for `0 < a < 1` it is even a `FieldTorus` of
   `∇φ` (`dbl_fieldTorus`) and an immersion (`dbl_immersion`), but it is not injective modulo
   the periods (`dbl_not_injectiveModPeriods`): `θ = 0` and `θ = π` give the same point. So
   it is not an `EmbeddedTorus` and its descended map is not injective. Hence neither
   `PeriodicC2Torus` nor `FieldTorus` implies embeddedness, and the injectivity clause is
   not implied by the immersion clause.
3. **Rejected: a degenerate torus** `a = 0` (the circle `R = 1`, `z = 0`): it is a
   `PeriodicC2Torus` with `R > 0`, but its differential is nowhere injective
   (`circle_not_immersion`), so it is not an `EmbeddedTorus` (`circle_not_embeddedTorus`).
-/

public section
noncomputable section

namespace PlasmaLean.Sanity.FormFluxSurfaceEmbedded

open Real WithLp PlasmaLean.Vacuum PlasmaLean.Fields PlasmaLean.Contract PlasmaLean.Forms
open PlasmaLean.Design.RationalStellarator PlasmaLean.Design.RationalStellaratorContract
open PlasmaLean.Sanity.FormFluxSurfacePeriods
open scoped RealInnerProductSpace Manifold

/-- The period `2π` is positive (needed for the circle `AddCircle (2 * π)`). -/
local instance factTwoPiPos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-! ## Accepted: the circular torus -/

/-- The `θ`-derivative of the major radius of the circular torus. -/
theorem deriv_circR (a θ φ : ℝ) : deriv (fun t => circR a t φ) θ = a * -sin θ :=
  (((hasDerivAt_cos θ).const_mul a).const_add 1).deriv

/-- The `θ`-derivative of the height of the circular torus. -/
theorem deriv_circZ (a θ φ : ℝ) : deriv (fun t => circZ a t φ) θ = a * cos θ :=
  ((hasDerivAt_sin θ).const_mul a).deriv

/-- **The circular torus with `0 < a < 1` is an embedded torus.** -/
theorem circ_embeddedTorus {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    EmbeddedTorus (circR a) (circZ a) := by
  refine EmbeddedTorus.of_sections (circ_periodicC2Torus a) (fun θ _ => circR_pos ha ha1 θ)
    (fun θ θ' φ h1 h2 => ?_) (fun θ φ h => ?_)
  · have hc : cos θ = cos θ' := by
      simp only [circR] at h1
      exact mul_left_cancel₀ ha.ne' (by linarith)
    have hs : sin θ = sin θ' := mul_left_cancel₀ ha.ne' h2
    exact exists_int_of_cos_sin_eq hc hs
  · rw [deriv_circR, deriv_circZ] at h
    have hs : sin θ = 0 := by
      have := (mul_eq_zero.1 h.1).resolve_left ha.ne'
      linarith
    have hc : cos θ = 0 := (mul_eq_zero.1 h.2).resolve_left ha.ne'
    have := sin_sq_add_cos_sq θ
    rw [hs, hc] at this
    norm_num at this

/-- **The circular torus is the image of a `C²` embedding of the 2-torus.** -/
theorem circ_isSmoothEmbedding {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Manifold.IsSmoothEmbedding (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, Space) 2
      (torusEmb (circR a) (circZ a)) :=
  (circ_embeddedTorus ha ha1).isSmoothEmbedding_torusEmb

/-- **The class of `∇φ` on the circular torus is `[dφ]`, on the torus**: `β - dφ` is the
differential of a `C¹` function on `AngleTorus`. -/
theorem toroidal_class_on_torus {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∃ g : AngleTorus → ℝ, ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ) 1 g ∧
      ∀ x, HasMFDerivAt (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ) g x (torusFormT toroidal (circR a) (circZ a) x
        - (0 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ
        - (1 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) := by
  have hπ : (2 * π) ≠ 0 := by positivity
  have h := (circ_periodicC2Torus a).exists_potential_on_torus
    toroidal_vacuum.isOpen (toroidal_vacuum.contDiffOn.of_le (by norm_num))
    toroidal_vacuum.curl_eq_zero (circ_mem_domain ha ha1) 0 0
  rw [toroidal_poloidalPeriod ha ha1, toroidal_toroidalPeriod ha ha1, zero_div,
    div_self hπ] at h
  exact h

/-- **The coefficients of the class on the torus are forced**: if `β = a' dθ + b' dφ + dg` on
the torus for `∇φ` on the circular torus, then `a' = 0` and `b' = 1`. -/
theorem toroidal_class_on_torus_unique {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {a' b' : ℝ}
    {g : AngleTorus → ℝ}
    (hg : ∀ x, HasMFDerivAt (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ) g x
      (torusFormT toroidal (circR a) (circZ a) x
        - a' • ContinuousLinearMap.fst ℝ ℝ ℝ - b' • ContinuousLinearMap.snd ℝ ℝ ℝ)) :
    a' = 0 ∧ b' = 1 := by
  have hπ : (0 : ℝ) < 2 * π := by positivity
  obtain ⟨h1, h2⟩ := (circ_periodicC2Torus a).periods_eq_of_potential_on_torus
    (continuousAt_of_contDiffOn_torus toroidal_vacuum.isOpen
      (toroidal_vacuum.contDiffOn.of_le (by norm_num)) (circ_mem_domain ha ha1)) hg 0 0
  rw [toroidal_poloidalPeriod ha ha1] at h1
  rw [toroidal_toroidalPeriod ha ha1] at h2
  constructor
  · nlinarith
  · nlinarith

/-! ## Rejected: a doubly covered torus -/

/-- The doubly covered circular torus: `R = 1 + a cos 2θ`. -/
def dblR (a : ℝ) (θ _φ : ℝ) : ℝ := 1 + a * cos (2 * θ)

/-- The doubly covered circular torus: `z = a sin 2θ`. -/
def dblZ (a : ℝ) (θ _φ : ℝ) : ℝ := a * sin (2 * θ)

/-- The doubly covered torus is a doubly periodic `C²` torus, for every `a`. -/
theorem dbl_periodicC2Torus (a : ℝ) : PeriodicC2Torus (dblR a) (dblZ a) :=
  ⟨by unfold dblR; fun_prop, by unfold dblZ; fun_prop,
    fun θ φ => by
      simp only [dblR]
      rw [show 2 * (θ + 2 * π) = 2 * θ + 2 * π + 2 * π by ring, cos_add_two_pi,
        cos_add_two_pi],
    fun θ φ => by
      simp only [dblZ]
      rw [show 2 * (θ + 2 * π) = 2 * θ + 2 * π + 2 * π by ring, sin_add_two_pi,
        sin_add_two_pi],
    fun _ _ => rfl, fun _ _ => rfl⟩

/-- **The doubly covered torus (`0 < a < 1`) is a `FieldTorus` of `∇φ`** with rotation number
`0`: the contract's torus predicate does not exclude it. -/
theorem dbl_fieldTorus {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    FieldTorus toroidal (dblR a) (dblZ a) 0 := by
  have hRpos : ∀ θ, 0 < 1 + a * cos (2 * θ) := fun θ => by
    nlinarith [neg_one_le_cos (2 * θ), cos_le_one (2 * θ)]
  have h := dbl_periodicC2Torus a
  refine ⟨h.contDiff_R.continuous, h.contDiff_z.continuous, fun θ _ => hRpos θ, h.per_θ_R,
    h.per_θ_z, h.per_φ_R, h.per_φ_z, fun θ φ => ?_⟩
  refine ⟨(1 + a * cos (2 * θ)) ^ 2, ?_⟩
  have hφ : HasDerivAt (fun t : ℝ => φ + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add φ
  have h0 := (hφ.cos).const_mul (1 + a * cos (2 * θ))
  have h1 := (hφ.sin).const_mul (1 + a * cos (2 * θ))
  have h3 := hasDerivAt_space3 h0 h1 (hasDerivAt_const (0 : ℝ) (a * sin (2 * θ)))
  simp only [dblR, dblZ, mul_zero, add_zero]
  refine h3.congr_deriv ?_
  rw [toroidal_cylPoint (hRpos θ)]
  have hR0 := (hRpos θ).ne'
  ext i
  fin_cases i <;> simp <;> field_simp

/-- **The doubly covered torus is not injective modulo the periods**: the parameters
`(0, 0)` and `(π, 0)` have the same image, and `π` is not an integer multiple of `2π`. -/
theorem dbl_not_injectiveModPeriods (a : ℝ) : ¬ InjectiveModPeriods (dblR a) (dblZ a) := by
  intro hinj
  obtain ⟨m, n, hmn⟩ := hinj (0, 0) (π, 0) (by simp [torusMap, dblR, dblZ])
  have h1 : π = 2 * π * m := by simpa using congrArg Prod.fst hmn
  have h2 : (1 : ℝ) = 2 * m := by
    have hπ := pi_pos
    have : π * 1 = π * (2 * m) := by linarith
    exact mul_left_cancel₀ hπ.ne' this
  have h3 : (1 : ℤ) = 2 * m := by exact_mod_cast h2
  omega

/-- The doubly covered torus is not an embedded torus. -/
theorem dbl_not_embeddedTorus (a : ℝ) : ¬ EmbeddedTorus (dblR a) (dblZ a) := fun h =>
  dbl_not_injectiveModPeriods a h.injective

/-- The descended map of the doubly covered torus is not injective on the 2-torus. -/
theorem dbl_torusEmb_not_injective (a : ℝ) :
    ¬ Function.Injective (torusEmb (dblR a) (dblZ a)) := fun h =>
  dbl_not_injectiveModPeriods a
    ((dbl_periodicC2Torus a).periodicTorus.injective_torusEmb_iff.1 h)

/-- **The doubly covered torus is an immersion** for `0 < a < 1`: the injectivity clause of
`EmbeddedTorus` is not implied by the immersion clause. -/
theorem dbl_immersion {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (p : ℝ × ℝ) :
    Function.Injective (fderiv ℝ (torusMap (dblR a) (dblZ a)) p) := by
  have hRpos : 0 < dblR a p.1 p.2 := by
    simp only [dblR]
    nlinarith [neg_one_le_cos (2 * p.1), cos_le_one (2 * p.1)]
  refine ((dbl_periodicC2Torus a).injective_fderiv_torusMap_iff hRpos).2 fun h => ?_
  have hd : HasDerivAt (fun t : ℝ => 2 * t) 2 p.1 := by
    simpa using (hasDerivAt_id p.1).const_mul (2 : ℝ)
  have hR : deriv (fun t => dblR a t p.2) p.1 = a * (-sin (2 * p.1) * 2) :=
    ((hd.cos.const_mul a).const_add 1).deriv
  have hz : deriv (fun t => dblZ a t p.2) p.1 = a * (cos (2 * p.1) * 2) :=
    (hd.sin.const_mul a).deriv
  rw [hR, hz] at h
  have hs : sin (2 * p.1) = 0 := by
    have := (mul_eq_zero.1 h.1).resolve_left ha.ne'
    linarith
  have hc : cos (2 * p.1) = 0 := by
    have := (mul_eq_zero.1 h.2).resolve_left ha.ne'
    linarith
  have := sin_sq_add_cos_sq (2 * p.1)
  rw [hs, hc] at this
  norm_num at this

/-! ## Rejected: a degenerate torus -/

/-- **The degenerate torus `a = 0` (a circle) is nowhere an immersion**: the differential of
its torus map kills `∂_θ`. -/
theorem circle_not_immersion (p : ℝ × ℝ) :
    ¬ Function.Injective (fderiv ℝ (torusMap (circR 0) (circZ 0)) p) := by
  have hR : 0 < circR 0 p.1 p.2 := by simp [circR]
  rw [(circ_periodicC2Torus 0).injective_fderiv_torusMap_iff hR, not_not, deriv_circR,
    deriv_circZ]
  simp

/-- The degenerate torus `a = 0` is not an embedded torus, although it is a doubly periodic
`C²` torus with `R > 0`. -/
theorem circle_not_embeddedTorus : ¬ EmbeddedTorus (circR 0) (circZ 0) := fun h =>
  circle_not_immersion (0, 0) (h.immersion (0, 0))

end PlasmaLean.Sanity.FormFluxSurfaceEmbedded
