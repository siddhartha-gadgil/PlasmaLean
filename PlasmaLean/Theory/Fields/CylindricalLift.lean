/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Contract.StellaratorContract
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Lifted cylindrical coordinates along a path that avoids the axis

A differentiable path `X` in three-space that stays off the `z`-axis has a lifted toroidal angle
`θ(τ)` on the universal cover (no branch cut), and its cylindrical coordinates `(θ, R, z)` are
differentiable with the expected velocity.

* `cylVelocity θ R u`: the velocity of `(θ, (R, z))` for the Cartesian velocity `u`; it is linear
  in `u` (`cylVelocity_add`, `cylVelocity_smul`) and bounded by `max 1 R⁻¹ * ‖u‖`
  (`norm_cylVelocity_le`).
* `exists_lift`: the lift exists on `[0, T]`, with two-sided derivatives at every point of
  `[0, T]`.

The angle is built by integration, `θ(τ) = θ₀ + ∫₀^τ (X₀ v₁ − X₁ v₀)/(X₀² + X₁²)` (the integrand
is frozen outside `[0, T]`), and `R = √(X₀² + X₁²)`. With `u = X₀ cos θ + X₁ sin θ` and
`w = −X₀ sin θ + X₁ cos θ`, the quotients `u/R` and `w/R` have zero derivative, hence keep their
initial values `1` and `0`; this gives `X = cylPoint R θ z`.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Fields.CylindricalLift
open Set Filter Topology Real WithLp PlasmaLean.Fields PlasmaLean.Contract

/-- The plane of the coordinates `(R, z)`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Velocity of the lifted cylindrical coordinates `(θ, (R, z))` for Cartesian velocity `u`. -/
def cylVelocity (θ R : ℝ) (u : Space) : ℝ × Plane :=
  ((-Real.sin θ * u 0 + Real.cos θ * u 1) / R,
    WithLp.toLp 2 ![Real.cos θ * u 0 + Real.sin θ * u 1, u 2])

/-- `cylVelocity` is additive in the Cartesian velocity. -/
theorem cylVelocity_add (θ R : ℝ) (u u' : Space) :
    cylVelocity θ R (u + u') = cylVelocity θ R u + cylVelocity θ R u' := by
  refine Prod.ext ?_ ?_
  · simp only [cylVelocity, PiLp.add_apply, Prod.fst_add]; ring
  · ext i; fin_cases i <;> simp [cylVelocity]; ring

/-- `cylVelocity` is homogeneous in the Cartesian velocity. -/
theorem cylVelocity_smul (θ R c : ℝ) (u : Space) :
    cylVelocity θ R (c • u) = c • cylVelocity θ R u := by
  refine Prod.ext ?_ ?_
  · simp only [cylVelocity, PiLp.smul_apply, smul_eq_mul, Prod.smul_fst]; ring
  · ext i; fin_cases i <;> simp [cylVelocity]; ring

/-- The cylindrical velocity is bounded by `max 1 R⁻¹` times the Cartesian speed. -/
theorem norm_cylVelocity_le {R : ℝ} (hR : 0 < R) (θ : ℝ) (u : Space) :
    ‖cylVelocity θ R u‖ ≤ max 1 R⁻¹ * ‖u‖ := by
  have hu : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  have hcs := Real.cos_sq_add_sin_sq θ
  have h1 : ‖(cylVelocity θ R u).1‖ ≤ R⁻¹ * ‖u‖ := by
    have habs : |-Real.sin θ * u 0 + Real.cos θ * u 1| ≤ ‖u‖ := by
      refine abs_le_of_sq_le_sq ?_ (norm_nonneg _)
      rw [hu]
      nlinarith [sq_nonneg (Real.cos θ * u 0 + Real.sin θ * u 1), sq_nonneg (u 2),
        sq_nonneg (u 0), sq_nonneg (u 1)]
    rw [cylVelocity, Real.norm_eq_abs, abs_div, abs_of_pos hR, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left habs (inv_nonneg.2 hR.le)
  have h2 : ‖(cylVelocity θ R u).2‖ ≤ ‖u‖ := by
    have := abs_le_of_sq_le_sq (a := ‖(cylVelocity θ R u).2‖) (b := ‖u‖) ?_ (norm_nonneg _)
    · rwa [abs_of_nonneg (norm_nonneg _)] at this
    · rw [hu, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      simp only [cylVelocity, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
      nlinarith [sq_nonneg (-Real.sin θ * u 0 + Real.cos θ * u 1), sq_nonneg (u 0),
        sq_nonneg (u 1)]
  rw [Prod.norm_def]
  refine max_le (h1.trans ?_) (h2.trans ?_)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  · exact le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _)

/-- A quotient `f / √s` has zero derivative when `f' s = f s' / 2`. -/
theorem hasDerivAt_div_sqrt_zero {f s : ℝ → ℝ} {f' s' x : ℝ} (hf : HasDerivAt f f' x)
    (hs : HasDerivAt s s' x) (hpos : 0 < s x) (h : f' * s x = f x * (s' / 2)) :
    HasDerivAt (fun y => f y / √(s y)) 0 x := by
  have hq : 0 < √(s x) := Real.sqrt_pos.2 hpos
  have hd := hf.div (hs.sqrt hpos.ne') hq.ne'
  convert hd using 1
  have hsq : √(s x) * √(s x) = s x := Real.mul_self_sqrt hpos.le
  have hnum : f' * √(s x) - f x * (s' / (2 * √(s x))) = 0 := by
    have : (f' * √(s x) - f x * (s' / (2 * √(s x)))) * √(s x) = 0 := by
      have h2 : √(s x) ^ 2 = s x := Real.sq_sqrt hpos.le
      field_simp
      linear_combination 2 * f' * h2 + 2 * h
    exact (mul_eq_zero.1 this).resolve_right hq.ne'
  rw [hnum, zero_div]

/-- A curve in the plane is differentiable when its two coordinates are. -/
theorem hasDerivAt_plane {f0 f1 : ℝ → ℝ} {d0 d1 t : ℝ} (h0 : HasDerivAt f0 d0 t)
    (h1 : HasDerivAt f1 d1 t) :
    HasDerivAt (fun s => (WithLp.toLp 2 ![f0 s, f1 s] : Plane)) (WithLp.toLp 2 ![d0, d1]) t := by
  have h := (h0.smul_const (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))).add
    (h1.smul_const (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))
  convert h using 1
  · funext s; ext k; fin_cases k <;> simp
  · ext k; fin_cases k <;> simp

/-- **Lifted cylindrical coordinates.** A differentiable path on `[0, T]` that avoids the
`z`-axis and starts at `cylPoint R₀ θ₀ z₀` has a lifted angle `θ` and a radius `R > 0` with
`X = cylPoint R θ z`, and `(θ, (R, z))` has the velocity `cylVelocity θ R v` at every point of
`[0, T]` (two-sided, also at the end points). -/
theorem exists_lift {X v : ℝ → Space} {T θ₀ R₀ z₀ : ℝ} (hT : 0 ≤ T)
    (hd : ∀ τ ∈ Icc 0 T, HasDerivAt X (v τ) τ) (hv : ContinuousOn v (Icc 0 T))
    (axis : ∀ τ ∈ Icc 0 T, 0 < X τ 0 ^ 2 + X τ 1 ^ 2)
    (start : X 0 = cylPoint R₀ θ₀ z₀) (hR₀ : 0 < R₀) :
    ∃ θ R : ℝ → ℝ, θ 0 = θ₀ ∧ R 0 = R₀ ∧ ∀ τ ∈ Icc 0 T,
      0 < R τ ∧ X τ = cylPoint (R τ) (θ τ) (X τ 2) ∧
      HasDerivAt (fun σ => (θ σ, (WithLp.toLp 2 ![R σ, X σ 2] : Plane)))
        (cylVelocity (θ τ) (R τ) (v τ)) τ := by
  -- coordinates of the path
  have hXi : ∀ (i : Fin 3), ∀ τ ∈ Icc 0 T, HasDerivAt (fun σ => X σ i) (v τ i) τ := by
    intro i τ hτ
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt τ (hd τ hτ)
  have hXc : ContinuousOn X (Icc 0 T) := fun τ hτ => (hd τ hτ).continuousAt.continuousWithinAt
  have hXic : ∀ i : Fin 3, ContinuousOn (fun σ => X σ i) (Icc 0 T) := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp_continuousOn hXc
  have hvic : ∀ i : Fin 3, ContinuousOn (fun σ => v σ i) (Icc 0 T) := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp_continuousOn hv
  -- the squared radius and the angular rate
  set s : ℝ → ℝ := fun σ => X σ 0 ^ 2 + X σ 1 ^ 2 with hs
  set G : ℝ → ℝ := fun σ => (X σ 0 * v σ 1 - X σ 1 * v σ 0) / s σ with hG
  have hsd : ∀ τ ∈ Icc 0 T, HasDerivAt s (2 * X τ 0 * v τ 0 + 2 * X τ 1 * v τ 1) τ := by
    intro τ hτ
    have h := ((hXi 0 τ hτ).pow 2).add ((hXi 1 τ hτ).pow 2)
    convert h using 1
    simp
  have hGc : ContinuousOn G (Icc 0 T) :=
    (((hXic 0).mul (hvic 1)).sub ((hXic 1).mul (hvic 0))).div
      (((hXic 0).pow 2).add ((hXic 1).pow 2)) (fun τ hτ => (axis τ hτ).ne')
  set g : ℝ → ℝ := fun x => G (max 0 (min T x)) with hg
  have hgc : Continuous g :=
    hGc.comp_continuous (by fun_prop) (fun x => ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩)
  have hgG : ∀ τ ∈ Icc 0 T, g τ = G τ := by
    intro τ hτ
    simp [hg, min_eq_right hτ.2, max_eq_right hτ.1]
  set θ : ℝ → ℝ := fun σ => θ₀ + ∫ x in (0 : ℝ)..σ, g x with hθ
  have hθd : ∀ τ ∈ Icc 0 T, HasDerivAt θ (G τ) τ := by
    intro τ hτ
    rw [← hgG τ hτ]
    exact (intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable _ _)
      (hgc.stronglyMeasurableAtFilter _ _) hgc.continuousAt).const_add θ₀
  have hθ0 : θ 0 = θ₀ := by simp [hθ]
  have hcs := Real.cos_sq_add_sin_sq θ₀
  have hX0 := (cylPoint_coords R₀ θ₀ z₀).1
  have hX1 := (cylPoint_coords R₀ θ₀ z₀).2.1
  rw [← start] at hX0 hX1
  have hs0 : s 0 = R₀ ^ 2 := by
    simp only [hs, hX0, hX1]
    linear_combination R₀ ^ 2 * hcs
  have hR0 : √(s 0) = R₀ := by rw [hs0, Real.sqrt_sq hR₀.le]
  -- the rotated coordinates
  set u : ℝ → ℝ := fun σ => X σ 0 * Real.cos (θ σ) + X σ 1 * Real.sin (θ σ) with hu
  set w : ℝ → ℝ := fun σ => -(X σ 0) * Real.sin (θ σ) + X σ 1 * Real.cos (θ σ) with hw
  have hud : ∀ τ ∈ Icc 0 T, HasDerivAt (fun σ => u σ / √(s σ)) 0 τ := by
    intro τ hτ
    have h := ((hXi 0 τ hτ).mul (hθd τ hτ).cos).add ((hXi 1 τ hτ).mul (hθd τ hτ).sin)
    refine hasDerivAt_div_sqrt_zero h (hsd τ hτ) (axis τ hτ) ?_
    have hpos : s τ ≠ 0 := (axis τ hτ).ne'
    simp only [hG, hu]
    field_simp
    simp only [hs]
    ring
  have hwd : ∀ τ ∈ Icc 0 T, HasDerivAt (fun σ => w σ / √(s σ)) 0 τ := by
    intro τ hτ
    have h := ((hXi 0 τ hτ).neg.mul (hθd τ hτ).sin).add ((hXi 1 τ hτ).mul (hθd τ hτ).cos)
    refine hasDerivAt_div_sqrt_zero h (hsd τ hτ) (axis τ hτ) ?_
    have hpos : s τ ≠ 0 := (axis τ hτ).ne'
    simp only [hG, hw, Pi.neg_apply]
    field_simp
    simp only [hs]
    ring
  have hconst : ∀ {f : ℝ → ℝ}, (∀ τ ∈ Icc 0 T, HasDerivAt f 0 τ) → ∀ τ ∈ Icc 0 T, f τ = f 0 :=
    fun {f} hf => constant_of_has_deriv_right_zero
      (fun τ hτ => (hf τ hτ).continuousAt.continuousWithinAt)
      (fun τ hτ => (hf τ (Ico_subset_Icc_self hτ)).hasDerivWithinAt)
  have hu0 : u 0 = R₀ := by
    simp only [hu, hθ0, hX0, hX1]
    linear_combination R₀ * hcs
  have hw0 : w 0 = 0 := by
    simp only [hw, hθ0, hX0, hX1]
    ring
  refine ⟨θ, fun σ => √(s σ), hθ0, hR0, fun τ hτ => ?_⟩
  have hpos : 0 < s τ := axis τ hτ
  have hRpos : 0 < √(s τ) := Real.sqrt_pos.2 hpos
  have hsq : √(s τ) * √(s τ) = s τ := Real.mul_self_sqrt hpos.le
  have huR : u τ = √(s τ) := by
    have h := hconst hud τ hτ
    simp only [hu0, hR0, div_self hR₀.ne'] at h
    exact (div_eq_one_iff_eq hRpos.ne').1 h
  have hw0' : w τ = 0 := by
    have h := hconst hwd τ hτ
    simp only [hw0, zero_div] at h
    exact (div_eq_zero_iff.1 h).resolve_right hRpos.ne'
  have hcsτ := Real.cos_sq_add_sin_sq (θ τ)
  have hx0 : X τ 0 = √(s τ) * Real.cos (θ τ) := by
    rw [← huR]
    linear_combination (-(X τ 0)) * hcsτ - Real.sin (θ τ) * hw0'
  have hx1 : X τ 1 = √(s τ) * Real.sin (θ τ) := by
    rw [← huR]
    linear_combination (-(X τ 1)) * hcsτ + Real.cos (θ τ) * hw0'
  refine ⟨hRpos, ?_, ?_⟩
  · ext i
    fin_cases i
    · simpa [cylPoint] using hx0
    · simpa [cylPoint] using hx1
    · simp [cylPoint]
  · have h := (hθd τ hτ).prodMk
      (hasDerivAt_plane ((hsd τ hτ).sqrt hpos.ne') (hXi 2 τ hτ))
    convert h using 1
    refine Prod.ext ?_ ?_
    · simp only [cylVelocity, hG]
      rw [hx0, hx1]
      set ρ : ℝ := √(s τ) with hρ
      have hsρ : s τ = ρ ^ 2 := by rw [sq, hsq]
      rw [hsρ]
      field_simp
      ring
    · simp only [cylVelocity]
      congr 2
      rw [hx0, hx1]
      field_simp

/-- Sanity check: on the unit circle `τ ↦ cylPoint 1 τ 0` the lift is `θ = id`, `R = 1`, and
the angle unwinds at unit rate. -/
theorem cylVelocity_circle (τ : ℝ) :
    cylVelocity τ 1 (WithLp.toLp 2 ![-Real.sin τ, Real.cos τ, 0]) =
      (1, WithLp.toLp 2 ![0, 0]) := by
  have h := Real.cos_sq_add_sin_sq τ
  refine Prod.ext ?_ ?_
  · simp only [cylVelocity, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, div_one]
    linear_combination h
  · ext i; fin_cases i <;> simp [cylVelocity]; ring

end PlasmaLean.Fields.CylindricalLift
