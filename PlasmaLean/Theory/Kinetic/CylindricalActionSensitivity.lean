/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorActionDensity
public import PlasmaLean.Theory.Contract.StellaratorContract

/-! # Geometric arclength sensitivity on a common angular window

The norm of the cylindrical tangent is the Euclidean norm of its azimuthal,
radial and vertical components. The pointwise and integrated estimates also
allow two independently oriented angular clocks.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Kinetic.CylindricalActionSensitivity
open Contract Fields Real Set MeasureTheory MirrorSublevelAction MirrorActionDensity

/-- The azimuthal component is R times angular speed. With angle as parameter
the three arguments are radius, radial derivative and vertical derivative. -/
def components (angular radial vertical : ℝ) : Space :=
  WithLp.toLp 2 ![angular, radial, vertical]

def speed (angular radial vertical : ℝ) : ℝ := ‖components angular radial vertical‖

theorem speed_sq (r u v : ℝ) : speed r u v ^ 2 = r ^ 2 + u ^ 2 + v ^ 2 := by
  simp [speed, components, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

theorem speed_formula (r u v : ℝ) : speed r u v = √(r ^ 2 + u ^ 2 + v ^ 2) := by
  rw [← speed_sq, Real.sqrt_sq (show 0 ≤ speed r u v from norm_nonneg _)]

/-- Actual Cartesian arclength density of any differentiable cylindrical curve,
including an arbitrary signed angular clock. No division by field strength occurs. -/
theorem cartesian_speed {R φ Z : ℝ → ℝ} {t u ω v : ℝ}
    (hr : HasDerivAt R u t) (hp : HasDerivAt φ ω t) (hz : HasDerivAt Z v t) :
    ‖deriv (fun s => cylPoint (R s) (φ s) (Z s)) t‖ = speed (R t * ω) u v := by
  have d := hasDerivAt_space3 (hr.mul hp.cos) (hr.mul hp.sin) hz
  simp only [Pi.mul_apply] at d
  change ‖deriv (fun s => WithLp.toLp 2 ![R s * cos (φ s), R s * sin (φ s), Z s]) t‖ = _
  rw [d.deriv]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change speed (u * cos (φ t) + R t * (-sin (φ t) * ω))
      (u * sin (φ t) + R t * (cos (φ t) * ω)) v ^ 2 = speed (R t * ω) u v ^ 2
  simp only [speed_sq]
  linear_combination (u ^ 2 + (R t * ω) ^ 2) * sin_sq_add_cos_sq (φ t)

/-- The reverse triangle inequality retains the combined Euclidean coordinate
error, including at zero velocity and at a turning point of any component. -/
theorem speed_difference (r u v s p q : ℝ) :
    |speed r u v - speed s p q| ≤ √((r - s) ^ 2 + (u - p) ^ 2 + (v - q) ^ 2) := by
  have diff : components r u v - components s p q = components (r-s) (u-p) (v-q) := by
    ext i
    fin_cases i <;> simp [components]
  calc
    _ ≤ ‖components r u v - components s p q‖ := abs_norm_sub_norm_le ..
    _ = _ := by rw [diff]; exact speed_formula ..

/-- The bound applies to the true Cartesian tangent norms per radian of geometric angle. -/
theorem same_angle {R S Z W : ℝ → ℝ} {t u p v q : ℝ}
    (hr : HasDerivAt R u t) (hs : HasDerivAt S p t) (hz : HasDerivAt Z v t)
    (hw : HasDerivAt W q t) :
    |‖deriv (fun x => cylPoint (R x) x (Z x)) t‖ -
        ‖deriv (fun x => cylPoint (S x) x (W x)) t‖| ≤
      √((R t - S t) ^ 2 + (u - p) ^ 2 + (v - q) ^ 2) := by
  have one : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
  rw [cartesian_speed hr one hz, cartesian_speed hs one hw, mul_one, mul_one]
  exact speed_difference ..

/-- Concentric circles give equality in the sensitivity estimate; vertical
translations of either circle leave its angular arclength density unchanged. -/
theorem circles_attain {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (z w t : ℝ) :
    |‖deriv (fun x => cylPoint r x z) t‖ - ‖deriv (fun x => cylPoint s x w) t‖| = |r-s| := by
  have circle (x y : ℝ) (hx : 0 ≤ x) : ‖deriv (fun τ => cylPoint x τ y) t‖ = x := by
    simpa [speed_formula, Real.sqrt_sq hx] using
      cartesian_speed (hasDerivAt_const t x) (hasDerivAt_id t) (hasDerivAt_const t y)
  rw [circle _ _ hr, circle _ _ hs]

/-- A unit circle and a helix coincide at angle zero while their true
arclength densities differ by one there. Position agreement leaves the
vertical-velocity contribution unconstrained. -/
theorem same_point_different_tangents :
    cylPoint 1 0 (√3 * 0) = cylPoint 1 0 0 ∧
      ‖deriv (fun t => cylPoint 1 t (√3 * t)) 0‖ - ‖deriv (fun t => cylPoint 1 t 0) 0‖ = 1 := by
  constructor
  · simp
  · have one : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id _
    have rise : HasDerivAt (fun t : ℝ => √3 * t) (√3) 0 := by simpa using one.const_mul (√3)
    rw [cartesian_speed (hasDerivAt_const 0 1) one rise,
      cartesian_speed (hasDerivAt_const 0 1) one (hasDerivAt_const 0 0)]
    have root : √(4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num [speed_formula, Real.sq_sqrt, root]

/-- At a fixed positive radius, departures from purely azimuthal motion cost at
most a quadratic amount in the radial and vertical velocities. -/
theorem transverse_quadratic {r : ℝ} (hr : 0 < r) (u v : ℝ) :
    0 ≤ speed r u v - r ∧ speed r u v - r ≤ (u ^ 2 + v ^ 2) / (2 * r) := by
  have sq := speed_sq r u v
  have nonneg : 0 ≤ speed r u v := norm_nonneg _
  have lower : r ≤ speed r u v := by nlinarith only [sq, sq_nonneg u, sq_nonneg v, hr, nonneg]
  refine ⟨sub_nonneg.mpr lower, (le_div_iff₀ (by linarith)).mpr ?_⟩
  nlinarith only [sq, sq_nonneg (speed r u v - r)]

/-- A spatial velocity Lipschitz bound L gives √(1+L²) for angular
arclength density in the physical radius-height plane. -/
theorem density_of_velocity_lipschitz {V : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (x y : EuclideanSpace ℝ (Fin 2)) {L : ℝ} (hL : 0 ≤ L)
    (vel : ‖V x - V y‖ ≤ L * ‖x - y‖) :
    |speed (x 0) (V x 0) (V x 1) - speed (y 0) (V y 0) (V y 1)| ≤ √(1 + L ^ 2) * ‖x - y‖ := by
  apply (speed_difference ..).trans
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  have dx : |x 0 - y 0| ≤ ‖x - y‖ := PiLp.norm_apply_le (x - y) 0
  have p : ‖V x - V y‖ ^ 2 = (V x 0 - V y 0) ^ 2 + (V x 1 - V y 1) ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have radial := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr dx
  have motion := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mpr vel
  rw [p] at motion
  rw [sq_abs] at radial
  rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
  nlinarith only [radial, motion]

variable {X : Type*} [MeasurableSpace X]

/-- A fixed-density field-profile estimate combines with L¹ control on cylindrical
tangent components to bound the action variation with physical arclength weights. -/
theorem action_components (μ : Measure X) {j k : X → Space} {B C : X → ℝ} {base h E : ℝ}
    (mj : Measurable j) (mk : Measurable k) (ij : Integrable j μ) (ik : Integrable k μ)
    (mc : AEMeasurable C μ) (floorC : ∀ᵐ x ∂μ, base ≤ C x)
    (profile : |action (arcMeasure μ (fun x => ‖j x‖)) B h -
      action (arcMeasure μ (fun x => ‖j x‖)) C h| ≤ E) :
    |action (arcMeasure μ (fun x => ‖j x‖)) B h -
      action (arcMeasure μ (fun x => ‖k x‖)) C h| ≤ E + √(2 * (h-base)) * ∫ x, ‖j x - k x‖ ∂μ := by
  apply (profile_and_density μ mj.norm mk.norm (.of_forall fun _ => norm_nonneg _)
    (.of_forall fun _ => norm_nonneg _) ij.norm ik.norm mc floorC profile).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  exact integral_mono ((ij.norm.sub ik.norm).abs) (ij.sub ik).norm
    (fun x => abs_norm_sub_norm_le (j x) (k x))

/-- On a finite geometric-angle interval a uniform three-component discrepancy
costs its width times the discrepancy times the maximum parallel speed. -/
theorem action_window {a b base h E η : ℝ} (hab : a ≤ b) {j k : ℝ → Space} {B C : ℝ → ℝ}
    (mj : Measurable j) (mk : Measurable k)
    (ij : Integrable j (volume.restrict (Ioc a b))) (ik : Integrable k (volume.restrict (Ioc a b)))
    (mc : AEMeasurable C (volume.restrict (Ioc a b)))
    (floorC : ∀ᵐ x ∂volume.restrict (Ioc a b), base ≤ C x)
    (close : ∀ x ∈ Ioo a b, ‖j x - k x‖ ≤ η)
    (profile : |action (arcMeasure (volume.restrict (Ioc a b)) (fun x => ‖j x‖)) B h -
      action (arcMeasure (volume.restrict (Ioc a b)) (fun x => ‖j x‖)) C h| ≤ E) :
    |action (arcMeasure (volume.restrict (Ioc a b)) (fun x => ‖j x‖)) B h -
      action (arcMeasure (volume.restrict (Ioc a b)) (fun x => ‖k x‖)) C h| ≤
      E + √(2 * (h - base)) * ((b - a) * η) := by
  let μ := volume.restrict (Ioc a b)
  have bound : (∫ x, ‖j x - k x‖ ∂μ) ≤ ∫ _, η ∂μ :=
    integral_mono_ae (ij.sub ik).norm (integrable_const _)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae (volume.ae_ne b)]
          with x hx apart
        exact close x ⟨hx.1, lt_of_le_of_ne hx.2 apart⟩)
  simp only [μ, integral_const, smul_eq_mul, measureReal_restrict_apply_univ,
    Real.volume_real_Ioc_of_le hab] at bound
  exact (action_components μ mj mk ij ik mc floorC profile).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left bound (Real.sqrt_nonneg _)))

/-- Action with the arclength density defined directly by differentiating the
physical Cartesian curve at the geometric toroidal angle. -/
def physicalAction (R Z B : ℝ → ℝ) (a b h : ℝ) : ℝ :=
  MirrorHeightAction.action B (fun x => ‖deriv (fun t => cylPoint (R t) t (Z t)) x‖) a b h

/-- A measured vector of radius, radial derivative and vertical derivative
represents the physical arclength density throughout the interior of a window.
No endpoint derivatives are needed. -/
theorem physicalAction_eq {a b h : ℝ} (hab : a ≤ b) {R Z : ℝ → ℝ} (B : ℝ → ℝ)
    {j : ℝ → Space} (mj : Measurable j)
    (jet : ∀ t ∈ Ioo a b, j t 0 = R t ∧ HasDerivAt R (j t 1) t ∧ HasDerivAt Z (j t 2) t) :
    physicalAction R Z B a b h =
      action (arcMeasure (volume.restrict (Ioc a b)) (fun t => ‖j t‖)) B h := by
  rw [arcMeasure, action_trace hab B _ h mj.norm (fun t _ => norm_nonneg (j t))]
  apply intervalIntegral.integral_congr_Ioo_of_le hab
  intro t ht
  obtain ⟨rad, dr, dz⟩ := jet t ht
  have one : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
  have vector : components (j t 0) (j t 1) (j t 2) = j t := by
    ext i
    fin_cases i <;> simp [components]
  dsimp only
  rw [cartesian_speed dr one dz, mul_one, ← rad, speed, vector]

/-- Full physical interval result. A common fixed-curve field-profile error E
and a uniform cylindrical tangent mismatch η give an explicit action budget
for any two physical curves over the same finite angular window. -/
theorem physical_action_window {a b base h E η : ℝ} (hab : a ≤ b)
    {R Z S W B C : ℝ → ℝ} {j k : ℝ → Space} (mj : Measurable j) (mk : Measurable k)
    (ij : Integrable j (volume.restrict (Ioc a b))) (ik : Integrable k (volume.restrict (Ioc a b)))
    (lhs : ∀ t ∈ Ioo a b, j t 0 = R t ∧ HasDerivAt R (j t 1) t ∧ HasDerivAt Z (j t 2) t)
    (rhs : ∀ t ∈ Ioo a b, k t 0 = S t ∧ HasDerivAt S (k t 1) t ∧ HasDerivAt W (k t 2) t)
    (mc : AEMeasurable C (volume.restrict (Ioc a b)))
    (floorC : ∀ᵐ x ∂volume.restrict (Ioc a b), base ≤ C x)
    (close : ∀ x ∈ Ioo a b, ‖j x - k x‖ ≤ η)
    (profile : |physicalAction R Z B a b h - physicalAction R Z C a b h| ≤ E) :
    |physicalAction R Z B a b h - physicalAction S W C a b h| ≤
      E + √(2 * (h - base)) * ((b - a) * η) := by
  rw [physicalAction_eq hab B mj lhs, physicalAction_eq hab C mj lhs] at profile
  rw [physicalAction_eq hab B mj lhs, physicalAction_eq hab C mk rhs]
  exact action_window hab mj mk ij ik mc floorC close profile

/-- In a constant-strength field, two concentric circles attain the full
finite-window error coefficient for the physical arclength term. -/
theorem circle_action_attains {a b r s : ℝ} (hab : a ≤ b) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (z w base h : ℝ) :
    |physicalAction (fun _ => r) (fun _ => z) (fun _ => base) a b h -
      physicalAction (fun _ => s) (fun _ => w) (fun _ => base) a b h| =
      √(2 * (h - base)) * ((b - a) * |r - s|) := by
  have circle (R H : ℝ) (pos : 0 ≤ R) :
      physicalAction (fun _ => R) (fun _ => H) (fun _ => base) a b h =
        (b-a) * (R * √(2 * (h - base))) := by
    have tangent (t : ℝ) : ‖deriv (fun x => cylPoint R x H) t‖ = R := by
      simpa [speed_formula, Real.sqrt_sq pos] using
        cartesian_speed (hasDerivAt_const t R) (hasDerivAt_id t) (hasDerivAt_const t H)
    simp only [physicalAction, MirrorHeightAction.action, tangent, intervalIntegral.integral_const,
      smul_eq_mul]
  rw [circle _ _ hr, circle _ _ hs, ← mul_sub, ← sub_mul, abs_mul, abs_mul,
    abs_of_nonneg (sub_nonneg.mpr hab), abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

end PlasmaLean.Kinetic.CylindricalActionSensitivity
