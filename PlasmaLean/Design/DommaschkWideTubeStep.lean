/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkWideTubeHessian
public import PlasmaLean.Design.DommaschkWideTraceFields

/-!
# A wide-tube slab certificate for the QA2R field line flow

One slab of a wide-tube trace is certified by two families of real inequalities:
the trace and disk bounds of the frame-reduced Jacobian on the reference line
(`CentralBounds`), and the bounds of `DommaschkWideTubeHessian.TubeBounds` for its
derivative in the two frame directions on a coordinate rectangle that contains the
moving trial ball. With the closed rational side conditions of `Numbers.Valid` they
give a two-sided bound for the frame-reduced Jacobian on the whole trial ball, by the
mean value bridge of `DommaschkJacobianSecond`, and the field hypotheses of the
position-frame step.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkWideTubeStep

open Certificates PositionFrameSlabs TrajectoryTaylorModel QPoly DommaschkBounceTaylor Set
open DommaschkPhysicalTraceStep DommaschkKam DommaschkKam.DkPoly DommaschkJacobian
open DommaschkWideTubeHessian
open DommaschkBounceField (atPoint)
open scoped RealInnerProductSpace
open Fields.LogNormTrajectory (MovingFrame.jacobian)

/-- The certificate inequalities on the reference line: a lower bound for the common
denominator `det M · D²` and two-sided bounds for the trace, the diagonal difference
and the off-diagonal sum of the numerator of `M⁻¹(J M - M')`. -/
def CentralBounds (l r : Frame) (τ u z c s dl tr di off : ℝ) : Prop :=
  let m := frameEntries l r τ
  let denSq := evR u z c s dD * evR u z c s dD
  let A := transformedNumerator (spatialNumerator u z c s) m (velocityEntries l r) denSq
  dl ≤ m.det * denSq ∧ |A.a + A.d| ≤ tr ∧ |A.a - A.d| ≤ di ∧ |A.b + A.c| ≤ off

/-- The rational numbers of one wide-tube slab certificate. -/
structure Numbers where
  /-- Lower bound for `det M · D²` on the reference line. -/
  dl : ℚ
  /-- Bound for the central trace numerator. -/
  tr : ℚ
  /-- Bound for the central diagonal difference. -/
  di : ℚ
  /-- Bound for the central off-diagonal sum. -/
  off : ℚ
  /-- Radius of a disk containing the central traceless part. -/
  disk : ℚ
  /-- Two-sided bound for the reduced Jacobian on the reference line. -/
  mu₀ : ℚ
  /-- Lower bound for `det M · D³` on the tube. -/
  dlT : ℚ
  /-- Trace bound, first frame direction. -/
  tr₀ : ℚ
  /-- Diagonal difference bound, first frame direction. -/
  di₀ : ℚ
  /-- Off-diagonal sum bound, first frame direction. -/
  off₀ : ℚ
  /-- Disk radius, first frame direction. -/
  disk₀ : ℚ
  /-- Bound for the derivative of the reduced Jacobian in the first frame direction. -/
  g₀ : ℚ
  /-- Trace bound, second frame direction. -/
  tr₁ : ℚ
  /-- Diagonal difference bound, second frame direction. -/
  di₁ : ℚ
  /-- Off-diagonal sum bound, second frame direction. -/
  off₁ : ℚ
  /-- Disk radius, second frame direction. -/
  disk₁ : ℚ
  /-- Bound for the derivative of the reduced Jacobian in the second frame direction. -/
  g₁ : ℚ
  /-- Bound for the Euclidean combination of `g₀` and `g₁`. -/
  lip : ℚ
  /-- The certified two-sided bound on the trial ball. -/
  mu : ℚ

/-- The closed rational side conditions of a slab certificate with frame radius `ρ`. -/
structure Numbers.Valid (n : Numbers) (ρ : ℚ) : Prop where
  dl : 0 < n.dl
  mu₀ : 0 ≤ n.mu₀
  disk : 0 ≤ n.disk
  small : n.di ^ 2 + n.off ^ 2 ≤ n.disk ^ 2
  budget : n.tr + n.disk ≤ 2 * n.dl * n.mu₀
  dlT : 0 < n.dlT
  g₀ : 0 ≤ n.g₀
  disk₀ : 0 ≤ n.disk₀
  small₀ : n.di₀ ^ 2 + n.off₀ ^ 2 ≤ n.disk₀ ^ 2
  budget₀ : n.tr₀ + n.disk₀ ≤ 2 * n.dlT * n.g₀
  g₁ : 0 ≤ n.g₁
  disk₁ : 0 ≤ n.disk₁
  small₁ : n.di₁ ^ 2 + n.off₁ ^ 2 ≤ n.disk₁ ^ 2
  budget₁ : n.tr₁ + n.disk₁ ≤ 2 * n.dlT * n.g₁
  lip : 0 ≤ n.lip
  combine : n.g₀ ^ 2 + n.g₁ ^ 2 ≤ n.lip ^ 2
  total : n.mu₀ + n.lip * ρ ≤ n.mu

/-- Accepted fixture: with unit denominators and all other numbers zero the side
conditions hold for every radius. -/
theorem Numbers.valid_zero (ρ : ℚ) :
    Numbers.Valid ⟨1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ ρ := by
  constructor <;> norm_num

/-- Degenerate case: with radius zero the certified bound may equal the central one. -/
theorem Numbers.valid_radius_zero :
    Numbers.Valid ⟨1, 1, 0, 0, 0, 1 / 2, 1, 3, 0, 0, 0, 3 / 2, 4, 0, 0, 0, 2, 5 / 2, 1 / 2⟩ 0 := by
  constructor <;> norm_num

/-- Rejected fixture: the certified bound cannot be smaller than the central bound plus
the mean value term. -/
theorem Numbers.not_valid_small :
    ¬ Numbers.Valid
      ⟨1, 1, 0, 0, 0, 1 / 2, 1, 3, 0, 0, 0, 3 / 2, 4, 0, 0, 0, 2, 5 / 2, 1 / 2⟩ 1 := by
  intro h
  have h1 := h.total
  norm_num at h1

/-- The coordinate rectangle of a tube model at one normalized time. -/
def rectangle (tube : Inputs) (τ : ℝ) : Set Plane :=
  {ζ | tube.u.Mem τ (ζ 0 - dkR0) ∧ tube.z.Mem τ (ζ 1)}

/-- The rectangle is convex, as the mean value bridge requires. -/
theorem convex_rectangle (tube : Inputs) (τ : ℝ) : Convex ℝ (rectangle tube τ) := by
  have key (c ρ x y p q : ℝ) (hx : |x - c| ≤ ρ) (hy : |y - c| ≤ ρ) (hp : 0 ≤ p) (hq : 0 ≤ q)
      (hpq : p + q = 1) : |p * x + q * y - c| ≤ ρ := by
    have e : p * x + q * y - c = p * (x - c) + q * (y - c) := by
      linear_combination c * hpq
    have one : p * ρ + q * ρ = ρ := by rw [← add_mul, hpq, one_mul]
    rw [e]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hq]
    linarith only [mul_le_mul_of_nonneg_left hx hp, mul_le_mul_of_nonneg_left hy hq, one]
  intro x hx y hy p q hp hq hpq
  constructor
  · have h := key (dkR0 + eval tube.u.poly τ) tube.u.radius (x 0) (y 0) p q
      (by simpa only [Model.Mem, sub_sub] using hx.1)
      (by simpa only [Model.Mem, sub_sub] using hy.1) hp hq hpq
    simpa only [Model.Mem, sub_sub, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using h
  · have h := key (eval tube.z.poly τ) tube.z.radius (x 1) (y 1) p q hx.2 hy.2 hp hq hpq
    simpa only [Model.Mem, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using h

/-- The reference point belongs to a model of the reference line with zero radius. -/
theorem central_membership {r : Step} {m : Inputs} (hm : CenterMatches r m)
    (cu : m.u.radius = 0) (cz : m.z.radius = 0) (a t : ℝ) :
    m.u.Mem (coord a t) (reference a r t 0 - dkR0) ∧ m.z.Mem (coord a t) (reference a r t 1) := by
  have x := congrFun (hm.position a t) 0
  have z := congrFun (hm.position a t) 1
  change reference a r t 0 = dkR0 + eval m.u.poly (coord a t) at x
  change reference a r t 1 = eval m.z.poly (coord a t) at z
  constructor
  · rw [Model.Mem, x, cu]
    simp
  · rw [Model.Mem, z, cz]
    simp

variable {lim : Limits} {s : State} {r : Step} {a phase : ℝ} {central tube : Inputs}
  {radial vertical : ℕ} {n : Numbers}

/-- **Two-sided bound on the trial ball.** The central bounds on the reference line and
the directional bounds on the tube rectangle bound the frame-reduced Jacobian of the
forward field line flow on the whole trial ball, at every time of the slab. -/
theorem abs_quadratic (ok : geometry lim s r = true)
    (hc : CenterMatches r central) (cu : central.u.radius = 0) (cz : central.z.radius = 0)
    (ht : CenterMatches r tube)
    (box : PositionFrameProjection.Rectangle s.frame r.frame r.trial radial vertical)
    (hu : (tube.u.radius : ℝ) = (radial : ℝ) / 2 ^ 80)
    (hz : (tube.z.radius : ℝ) = (vertical : ℝ) / 2 ^ 80)
    (valid : n.Valid (r.trial / 2 ^ 80))
    (hcentral : ∀ t ∈ Icc a (a + 1 / 64), ∀ u z,
      central.u.Mem (coord a t) u → central.z.Mem (coord a t) z →
      CentralBounds s.frame r.frame (coord a t) u z (Real.cos (2 * (phase + 1 * t)))
        (Real.sin (2 * (phase + 1 * t))) n.dl n.tr n.di n.off)
    (htube : ∀ t ∈ Icc a (a + 1 / 64), ∀ u z,
      tube.u.Mem (coord a t) u → tube.z.Mem (coord a t) z →
      let c := Real.cos (2 * (phase + 1 * t))
      let s' := Real.sin (2 * (phase + 1 * t))
      TubeBounds (frameEntries s.frame r.frame (coord a t)) (jet dnR u z c s')
        (jet dnZ u z c s') (jet dD u z c s') n.dlT n.tr₀ n.di₀ n.off₀ n.tr₁ n.di₁ n.off₁) :
    ∀ t ∈ Icc a (a + 1 / 64), ∀ v ∈ Metric.closedBall (0 : Plane) (r.trial / (2 : ℝ) ^ 80),
      ∀ w : Plane, |⟪w, MovingFrame.jacobian
        (velocityJacobian phase 1 t (reference a r t + moving s r a t v)) (moving s r a t)
        (frameVelocity s.frame r.frame) w⟫| ≤ n.mu * ‖w‖ ^ 2 := by
  intro t ht' v hv w
  have hs := abs_coord_le ht'
  have hdet : affineDet s.frame r.frame (coord a t) ≠ 0 := det_ne_zero ok hs
  have dpos : 0 < affineDet s.frame r.frame (coord a t) := by
    obtain ⟨_, _, _, h₁, h₂, _⟩ := geometry_sound ok
    linarith [h₂ (coord a t) hs]
  have cast {x y : ℚ} (h : x ≤ y) : (x : ℝ) ≤ (y : ℝ) := Rat.cast_le.mpr h
  have dlT : (0 : ℝ) < n.dlT := by exact_mod_cast valid.dlT
  have inside (ζ : Plane) (hζ : ζ ∈ rectangle tube (coord a t)) :=
    htube t ht' (ζ 0 - dkR0) (ζ 1) hζ.1 hζ.2
  have mem (v' : Plane) (hv' : v' ∈ Metric.closedBall (0 : Plane) (r.trial / (2 : ℝ) ^ 80)) :
      reference a r t + moving s r a t v' ∈ rectangle tube (coord a t) :=
    DommaschkWideTraceFields.forward_membership ok ht box hu hz ht' hv'
  have hzero : reference a r t ∈ rectangle tube (coord a t) := by
    have h := mem 0 (Metric.mem_closedBall_self (by positivity))
    simpa only [map_zero, add_zero] using h
  have both (ζ : Plane) (hζ : ζ ∈ rectangle tube (coord a t)) :=
    directional_bounds phase t s.frame r.frame (coord a t) ζ w hdet dlT
      (g₀ := n.g₀) (g₁ := n.g₁) (disk₀ := n.disk₀) (disk₁ := n.disk₁)
      (by exact_mod_cast valid.g₀) (by exact_mod_cast valid.disk₀)
      (by exact_mod_cast cast valid.small₀) (by exact_mod_cast cast valid.budget₀)
      (by exact_mod_cast valid.g₁) (by exact_mod_cast valid.disk₁)
      (by exact_mod_cast cast valid.small₁) (by exact_mod_cast cast valid.budget₁)
      (inside ζ hζ)
  obtain ⟨cmu, cmz⟩ := central_membership hc cu cz a t
  have key := DommaschkJacobianSecond.abs_quad_le_of_central_bounds phase t s.frame r.frame
    (coord a t) (T := rectangle tube (coord a t)) (ref := reference a r t) (v := v) (w := w)
    (g₀ := n.g₀) (g₁ := n.g₁) (ρ := r.trial / (2 : ℝ) ^ 80) (disk := n.disk) (mu := n.mu₀)
    (convex_rectangle tube (coord a t))
    (fun ζ hζ => by
      obtain ⟨hd, _⟩ := inside ζ hζ
      have hp := dlT.trans_le hd
      intro h0
      change (jet dD (ζ 0 - dkR0) (ζ 1) (Real.cos (2 * (phase + 1 * t)))
        (Real.sin (2 * (phase + 1 * t)))).v = 0 at h0
      rw [h0] at hp
      simp at hp)
    (fun ζ hζ => (both ζ hζ).1) (fun ζ hζ => (both ζ hζ).2) hzero (mem v hv)
    (by simpa using hv) (by exact_mod_cast valid.dl) (by exact_mod_cast valid.mu₀)
    (by exact_mod_cast valid.disk) (by exact_mod_cast cast valid.small)
    (by exact_mod_cast cast valid.budget) (hcentral t ht' _ _ cmu cmz)
  refine key.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
  have hsqrt : Real.sqrt ((n.g₀ : ℝ) ^ 2 + (n.g₁ : ℝ) ^ 2) ≤ n.lip := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by exact_mod_cast valid.lip, by exact_mod_cast cast valid.combine⟩
  have total : (n.mu₀ : ℝ) + n.lip * (r.trial / (2 : ℝ) ^ 80) ≤ n.mu := by
    have h := cast valid.total
    push_cast at h
    exact h
  have ρ0 : (0 : ℝ) ≤ r.trial / (2 : ℝ) ^ 80 := by positivity
  nlinarith only [mul_le_mul_of_nonneg_right hsqrt ρ0, total]

/-- The lower half of `abs_quadratic`, in the form used by the backward distance
estimate. -/
theorem neg_le_quadratic
    (h : ∀ t ∈ Icc a (a + 1 / 64), ∀ v ∈ Metric.closedBall (0 : Plane) (r.trial / (2 : ℝ) ^ 80),
      ∀ w : Plane, |⟪w, MovingFrame.jacobian
        (velocityJacobian phase 1 t (reference a r t + moving s r a t v)) (moving s r a t)
        (frameVelocity s.frame r.frame) w⟫| ≤ n.mu * ‖w‖ ^ 2)
    {t : ℝ} (ht : t ∈ Icc a (a + 1 / 64)) {v : Plane}
    (hv : v ∈ Metric.closedBall (0 : Plane) (r.trial / (2 : ℝ) ^ 80)) (w : Plane) :
    -(n.mu * ‖w‖ ^ 2) ≤ ⟪w, MovingFrame.jacobian
      (velocityJacobian phase 1 t (reference a r t + moving s r a t v)) (moving s r a t)
      (frameVelocity s.frame r.frame) w⟫ :=
  (abs_le.mp (h t ht v hv w)).1

/-- **Field hypotheses of a wide step.** The same certificate, a residual bound on the
reference line and a margin keeping the rectangle away from the axis give all the field
inputs of `PositionFrameWide.physical_step_on` on the trial ball. -/
theorem field_bounds (ok : geometry lim s r = true)
    (hc : CenterMatches r central) (cu : central.u.radius = 0) (cz : central.z.radius = 0)
    (ht : CenterMatches r tube)
    (box : PositionFrameProjection.Rectangle s.frame r.frame r.trial radial vertical)
    (hu : (tube.u.radius : ℝ) = (radial : ℝ) / 2 ^ 80)
    (hz : (tube.z.radius : ℝ) = (vertical : ℝ) / 2 ^ 80)
    (safe : tube.u.radius + magnitude (difference tube.u.poly [0]) ≤ 1 / 2)
    (valid : n.Valid (r.trial / 2 ^ 80)) (hmu : n.mu ≤ r.mu)
    (hcentral : ∀ t ∈ Icc a (a + 1 / 64), ∀ u z,
      central.u.Mem (coord a t) u → central.z.Mem (coord a t) z →
      CentralBounds s.frame r.frame (coord a t) u z (Real.cos (2 * (phase + 1 * t)))
        (Real.sin (2 * (phase + 1 * t))) n.dl n.tr n.di n.off)
    (htube : ∀ t ∈ Icc a (a + 1 / 64), ∀ u z,
      tube.u.Mem (coord a t) u → tube.z.Mem (coord a t) z →
      let c := Real.cos (2 * (phase + 1 * t))
      let s' := Real.sin (2 * (phase + 1 * t))
      TubeBounds (frameEntries s.frame r.frame (coord a t)) (jet dnR u z c s')
        (jet dnZ u z c s') (jet dD u z c s') n.dlT n.tr₀ n.di₀ n.off₀ n.tr₁ n.di₁ n.off₁)
    (res : ∀ t ∈ Ico a (a + 1 / 64), ‖(moving s r a t).symm
      (euclideanFlow phase 1 t (reference a r t) - referenceVelocity a r t)‖ ≤ r.defect) :
    FieldBounds s r a (euclideanFlow phase 1) (velocityJacobian phase 1) ballDomain := by
  have quad := abs_quadratic (phase := phase) ok hc cu cz ht box hu hz valid hcentral htube
  apply DommaschkWideTraceFields.field_bounds_of_geometry ok _ _ res
  · intro t ht' v hv
    let x := reference a r t + moving s r a t v
    have hs := abs_coord_le ht'
    obtain ⟨mu', mz'⟩ := DommaschkWideTraceFields.forward_membership ok ht box hu hz ht' hv
    have hr := enclose (c := ⟨[0], 1 / 2⟩) hs mu' safe
    change (⟨[0], 1 / 2⟩ : Model).Mem (coord a t) (x 0 - dkR0) at hr
    norm_num [Model.Mem, dkR0, abs_le] at hr
    have pos : 0 < x 0 := by linarith
    refine ⟨pos, ?_⟩
    obtain ⟨hd, _⟩ := htube t ht' (x 0 - dkR0) (x 1) mu' mz'
    have dlT : (0 : ℝ) < n.dlT := by exact_mod_cast valid.dlT
    have hp := dlT.trans_le hd
    intro h0
    change (jet dD (x 0 - dkR0) (x 1) (Real.cos (2 * (phase + 1 * t)))
      (Real.sin (2 * (phase + 1 * t)))).v = 0 at h0
    rw [h0] at hp
    simp at hp
  · intro t ht' v hv w
    have h := quad t (Ico_subset_Icc_self ht') v hv w
    have hm : (n.mu : ℝ) ≤ (r.mu : ℝ) := Rat.cast_le.mpr hmu
    exact (le_abs_self _).trans (h.trans (mul_le_mul_of_nonneg_right hm (sq_nonneg _)))

end PlasmaLean.Design.DommaschkWideTubeStep
