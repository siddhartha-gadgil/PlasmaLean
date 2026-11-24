/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import PlasmaLean.Certificates.PositionFrameSlabs
public import PlasmaLean.Certificates.DyadicTaylorModel
public import PlasmaLean.Theory.Fields.MovingFrameSlabs

/-!
# Realizing a checked position frame on the Euclidean plane

The four stored affine entries act on the two physical coordinates. The
adjugate divided by the certified determinant gives the inverse needed by the
moving-frame ODE. Time increases by 1 / 64 on each outward slab.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Certificates.PositionFrameSlabs

open Set
open scoped RealInnerProductSpace

/-- Euclidean position coordinates carrying the norm used by the certificate. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A real two-by-two matrix acting on Euclidean position vectors. -/
def matrix (a b c d : ℝ) : Plane →L[ℝ] Plane :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin !![a,b;c,d])

@[simp] theorem matrix_zero (a b c d : ℝ) (v : Plane) :
    matrix a b c d v 0 = a*v 0 + b*v 1 := by
  change (Matrix.mulVec !![a,b;c,d] (WithLp.ofLp v)) 0 = _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[simp] theorem matrix_one (a b c d : ℝ) (v : Plane) :
    matrix a b c d v 1 = c*v 0 + d*v 1 := by
  change (Matrix.mulVec !![a,b;c,d] (WithLp.ofLp v)) 1 = _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Decompose the matrix into the four constant Cartesian basis operators. -/
theorem matrix_basis (a b c d : ℝ) :
    matrix a b c d = a • matrix 1 0 0 0 + b • matrix 0 1 0 0 +
      c • matrix 0 0 1 0 + d • matrix 0 0 0 1 := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  fin_cases i <;> simp

private theorem continuous_matrix {a b c d : ℝ → ℝ}
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (hd : Continuous d) :
    Continuous (fun t => matrix (a t) (b t) (c t) (d t)) := by
  simp_rw [matrix_basis (a _) (b _) (c _) (d _)]
  fun_prop

/-- The affine coordinate takes values −1 and 1 at the physical slab endpoints. -/
def coord (a t : ℝ) : ℝ := 128 * (t-a) - 1

theorem abs_coord_le {a t : ℝ} (ht : t ∈ Icc a (a + 1 / 64)) : |coord a t| ≤ 1 := by
  rcases ht with ⟨h₀,h₁⟩
  rw [abs_le]
  unfold coord
  constructor <;> linarith

/-- Forward matrix at the normalized time in the archived reference. -/
def forward (l r : Frame) (u : ℝ) : Plane →L[ℝ] Plane :=
  matrix (entry l.a r.a u) (entry l.b r.b u) (entry l.c r.c u) (entry l.d r.d u)

/-- The adjugate divided by the normalized determinant. -/
def backward (l r : Frame) (u : ℝ) : Plane →L[ℝ] Plane :=
  (affineDet l r u)⁻¹ • matrix (entry l.d r.d u) (-entry l.b r.b u)
    (-entry l.c r.c u) (entry l.a r.a u)

theorem mutual_inverse (l r : Frame) (u : ℝ) (h : affineDet l r u ≠ 0) :
    Function.LeftInverse (backward l r u) (forward l r u) ∧
    Function.RightInverse (backward l r u) (forward l r u) := by
  unfold affineDet at h
  constructor <;> intro v <;> ext i <;> fin_cases i <;>
    simp [backward, forward, affineDet] <;> field_simp [h] <;> ring

/-- The affine frame as a continuous linear equivalence at every certified time.
At a singular time outside the checked cell we use the identity. -/
def frameEquiv (l r : Frame) (u : ℝ) : Plane ≃L[ℝ] Plane :=
  if h : affineDet l r u ≠ 0 then
    ContinuousLinearEquiv.equivOfInverse (forward l r u) (backward l r u)
      (mutual_inverse l r u h).1 (mutual_inverse l r u h).2
  else ContinuousLinearEquiv.refl ℝ Plane

theorem frameEquiv_forward {l r : Frame} {u : ℝ} (h : affineDet l r u ≠ 0) :
    (frameEquiv l r u).toContinuousLinearMap = forward l r u := by simp [frameEquiv,h]

theorem frameEquiv_backward {l r : Frame} {u : ℝ} (h : affineDet l r u ≠ 0) :
    (frameEquiv l r u).symm.toContinuousLinearMap = backward l r u := by
  simp only [frameEquiv, dite_eq_left h]; rfl

theorem det_ne_zero {lim : Limits} {s : State} {r : Step} (h : geometry lim s r = true)
    {u : ℝ} (hu : |u| ≤ 1) : affineDet s.frame r.frame u ≠ 0 := by
  obtain ⟨_,_,_,h₁,h₂,_⟩ := geometry_sound h
  linarith [h₂ u hu]

/-- The squared-coordinate check bounds the operator norm on the Euclidean plane. -/
theorem frame_op_norm {lim : Limits} {s : State} {r : Step} (h : geometry lim s r = true)
    {u : ℝ} (hu : |u| ≤ 1) : ‖(frameEquiv s.frame r.frame u).toContinuousLinearMap‖ ≤ r.op := by
  rw [frameEquiv_forward (det_ne_zero h hu)]
  obtain ⟨_,_,_,_,_,ho,_⟩ := geometry_sound h
  apply ContinuousLinearMap.opNorm_le_bound _ ho
  intro v
  have sq : ‖forward s.frame r.frame u v‖^2 ≤ ((r.op : ℝ) * ‖v‖)^2 := by
    simpa only [forward, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, matrix_zero,
      matrix_one, mul_pow] using (frame_norm_sq h hu (v 0) (v 1))
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ho (norm_nonneg _))).mp sq

/-- Constant derivative of the frame with respect to elapsed physical angle. -/
def frameVelocity (l r : Frame) : Plane →L[ℝ] Plane :=
  (64 : ℝ) • (forward l r 1 - forward l r (-1))

private theorem forward_affine (l r : Frame) (a t : ℝ) :
    forward l r (coord a t) = forward l r (-1) +
      ((t-a)/(a + 1 / 64-a)) • (forward l r 1 - forward l r (-1)) := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  fin_cases i <;> simp [forward, entry, coord] <;> ring

theorem hasDerivWithinAt_frame {lim : Limits} {s : State} {r : Step} (h : geometry lim s r = true)
    (a : ℝ) {t : ℝ} (ht : t ∈ Icc a (a + 1 / 64)) :
    HasDerivWithinAt (fun t => (frameEquiv s.frame r.frame (coord a t)).toContinuousLinearMap)
      (frameVelocity s.frame r.frame) (Icc a (a + 1 / 64)) t := by
  have der := (Fields.LogNormTrajectory.MovingFrame.hasDerivAt_affine_frame
    (forward s.frame r.frame (-1)) (forward s.frame r.frame 1) a (a + 1 / 64) t).hasDerivWithinAt
      (s := Icc a (a + 1 / 64))
  have con (x : ℝ) (hx : x ∈ Icc a (a + 1 / 64)) :=
    (frameEquiv_forward (det_ne_zero h (abs_coord_le hx))).trans (forward_affine _ _ a x)
  have len : (a + 1 / 64-a)⁻¹ = (64:ℝ) := by ring_nf
  rw [len] at der
  exact der.congr con (con t ht)

theorem continuousOn_frame_inverse {lim : Limits} {s : State} {r : Step}
    (h : geometry lim s r = true) (a : ℝ) :
    ContinuousOn (fun t => (frameEquiv s.frame r.frame (coord a t)).symm.toContinuousLinearMap)
      (Icc a (a + 1 / 64)) := by
  have nz : ∀ t ∈ Icc a (a + 1 / 64), affineDet s.frame r.frame (coord a t) ≠ 0 :=
    fun _ ht => det_ne_zero h (abs_coord_le ht)
  apply ContinuousOn.congr _ (fun t ht => frameEquiv_backward (nz t ht))
  unfold backward
  apply ContinuousOn.fun_smul
  · apply ContinuousOn.inv₀ _ nz
    unfold affineDet entry coord
    fun_prop
  · apply Continuous.continuousOn
    apply continuous_matrix <;> unfold entry coord <;> fun_prop

/-- The dyadic polynomial selected by one physical coordinate. -/
def polynomial (r : Step) (i : Fin 2) : List ℚ :=
  (TrajectoryTaylorModel.ofDyadic 80 (![r.px,r.py] i) 0).poly

/-- The saved nominal position at elapsed physical time. -/
def reference (a : ℝ) (r : Step) (t : ℝ) : Plane :=
  WithLp.toLp 2 (fun i => QPoly.eval (polynomial r i) (coord a t))

/-- Differentiate the actual saved polynomial and rescale its normalized time. -/
def referenceVelocity (a : ℝ) (r : Step) (t : ℝ) : Plane :=
  WithLp.toLp 2 (fun i => QPoly.eval (QPoly.deriv (polynomial r i)) (coord a t) * 128)

theorem hasDerivAt_reference (a : ℝ) (r : Step) (t : ℝ) :
    HasDerivAt (reference a r) (referenceVelocity a r t) t := by
  let toPlane := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap
  apply toPlane.hasFDerivAt.comp_hasDerivAt
  apply hasDerivAt_pi.mpr
  intro i
  have hz : HasDerivAt (coord a) 128 t := by
    unfold coord
    simpa only [id_eq, mul_one] using ((((hasDerivAt_id t).sub_const a).const_mul 128).sub_const 1)
  exact (QPoly.hasDerivAt_eval _ _).comp t hz

theorem continuous_referenceVelocity (a : ℝ) (r : Step) : Continuous (referenceVelocity a r) := by
  let toPlane := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap
  apply toPlane.continuous.comp
  apply continuous_pi
  intro i
  exact ((QPoly.continuous_eval _).comp (by unfold coord; fun_prop)).mul continuous_const

private theorem eval_atSign (p : List ℤ) (z : ℤ) :
    QPoly.eval (p.map (fun c : ℤ => (c : ℚ))) (z : ℝ) = (atSign p z : ℝ) := by
  induction p with
  | nil => simp [atSign]
  | cons c cs ih =>
    change (c : ℚ) + (z : ℝ) * QPoly.eval _ _ = ((c + z * atSign cs z : ℤ) : ℝ)
    push_cast
    rw [ih]

/-- Convert a packed pair into physical Cartesian coordinates. -/
def point (p : Point) : Plane := WithLp.toLp 2 ![p.x / (2 : ℝ)^80, p.y / (2 : ℝ)^80]

/-- The incoming endpoint of the saved reference in integer units. -/
def firstPoint (r : Step) : Point := ⟨atSign r.px (-1), atSign r.py (-1)⟩

private theorem reference_at_integer (a t : ℝ) (r : Step) (z : ℤ) (h : coord a t = (z : ℝ)) :
    reference a r t = point ⟨atSign r.px z, atSign r.py z⟩ := by
  ext i
  fin_cases i <;>
    simp [reference, point, polynomial, TrajectoryTaylorModel.ofDyadic, h, eval_atSign,
      div_eq_inv_mul]

theorem reference_start (a : ℝ) (r : Step) : reference a r a = point (firstPoint r) := by
  exact reference_at_integer a a r (-1) (by simp [coord])

theorem reference_end (a : ℝ) (r : Step) : reference a r (a + 1 / 64) = point (next r).point := by
  exact reference_at_integer a _ r 1 (by simp [coord]; ring)

private theorem entry_start (m n : ℤ) : entry m n (-1) = m / (2 : ℝ)^40 := by
  simp [entry]; ring

private theorem entry_end (m n : ℤ) : entry m n 1 = n / (2 : ℝ)^40 := by
  simp [entry]; ring

private theorem entry_fixed (m : ℤ) : entry m m 0 = m / (2 : ℝ)^40 := by
  simp [entry]; ring

private theorem same_equiv {l r l' r' : Frame} {u v : ℝ} (d : affineDet l r u ≠ 0)
    (e : affineDet l' r' v ≠ 0) (m : forward l r u = forward l' r' v) :
    frameEquiv l r u = frameEquiv l' r' v := by
  apply ContinuousLinearEquiv.ext
  funext x
  exact DFunLike.congr_fun ((frameEquiv_forward d).trans (m.trans (frameEquiv_forward e).symm)) x

theorem frame_start {lim : Limits} {s : State} {r : Step} (h : geometry lim s r = true) :
    frameEquiv s.frame r.frame (-1) = frameEquiv s.frame s.frame 0 := by
  have nz := det_ne_zero h (by norm_num : |(-1 : ℝ)| ≤ 1)
  apply same_equiv nz
  · simpa only [affineDet, entry_start, entry_fixed] using nz
  · simp only [forward, entry_start, entry_fixed]

theorem frame_end {lim : Limits} {s : State} {r : Step} (h : geometry lim s r = true) :
    frameEquiv s.frame r.frame 1 = frameEquiv r.frame r.frame 0 := by
  have nz := det_ne_zero h (by norm_num : |(1 : ℝ)| ≤ 1)
  apply same_equiv nz
  · simpa only [affineDet, entry_end, entry_fixed] using nz
  · simp only [forward, entry_end, entry_fixed]

/-- In physical units, the inverse frame sends the mismatch of the two adjacent
references into the certified Euclidean jump ball. -/
theorem norm_reference_jump {lim : Limits} {s : State} {r : Step} (h : geometry lim s r = true) :
    ‖(frameEquiv s.frame r.frame (-1)).symm (point s.point - point (firstPoint r))‖ ≤
      r.jumpBound / (2 : ℝ)^80 := by
  let m := s.frame
  let p := displacement s r
  let X : ℝ := 2^40*(m.d*p.x-m.b*p.y : ℤ) / (det m : ℝ)
  let Y : ℝ := 2^40*(m.a*p.y-m.c*p.x : ℤ) / (det m : ℝ)
  have nz := det_ne_zero h (by norm_num : |(-1 : ℝ)| ≤ 1)
  have de : affineDet s.frame r.frame (-1) = (det s.frame : ℝ)/2^80 := by
    simp only [affineDet,entry_start,det]; push_cast; ring
  have hn : (det m : ℝ) ≠ 0 := by
    exact_mod_cast (geometry_sound h).2.1.ne'
  let v := point s.point - point (firstPoint r)
  have coords : (backward s.frame r.frame (-1) v) 0 = -X/2^80 ∧
      (backward s.frame r.frame (-1) v) 1 = -Y/2^80 := by
    constructor <;> simp [backward, de, entry_start,v,point,firstPoint,X,Y,p,m,displacement] <;>
      field_simp [hn] <;> ring
  change ‖(frameEquiv s.frame r.frame (-1)).symm.toContinuousLinearMap v‖ ≤ _
  rw [frameEquiv_backward nz, EuclideanSpace.norm_eq, Fin.sum_univ_two, coords.1, coords.2]
  have bound : Real.sqrt (X^2+Y^2) ≤ r.jumpBound := inverse_jump h
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  have rearr : (-X/2^80)^2 + (-Y/2^80)^2 = (X^2+Y^2) / (2^80)^2 := by ring
  rw [rearr, Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity)]
  exact div_le_div_of_nonneg_right bound (by positivity)

/-- Physical entry or exit set encoded by one inherited reference state. -/
def stateSet (s : State) : Set Plane :=
  Fields.TrajectorySlabs.MovingFrame.ellipsoid (frameEquiv s.frame s.frame 0)
    (point s.point) (s.radius/(2 : ℝ)^80)

/-- Under the initial identity frame, the physical entry test is exactly the
sum-of-two-squares inequality used by the launch estimates. -/
theorem mem_stateSet_identity {s : State} (hs : s.frame = ⟨2 ^ 40, 0, 0, 2 ^ 40⟩) (v : Plane) :
    v ∈ stateSet s ↔
    (v 0 - s.point.x/(2 : ℝ)^80)^2 + (v 1 - s.point.y/(2 : ℝ)^80)^2 ≤
      (s.radius/(2 : ℝ)^80)^2 := by
  change ‖(frameEquiv s.frame s.frame 0).symm.toContinuousLinearMap (v-point s.point)‖ ≤ _ ↔ _
  rw [hs, frameEquiv_backward (by norm_num [affineDet,entry])]
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  norm_num [backward, affineDet, entry, point]

/-- Checked normalized square for ordinary derivative and continuity bounds. -/
def trialSquare (r : ℝ) : Set Plane :=
  {v | ∀ i, v i ∈ Icc (-r) r}

private theorem square_facts {T : ℝ} (hT : 0 ≤ T) :
    IsCompact (trialSquare T) ∧ Convex ℝ (trialSquare T) ∧
    Metric.closedBall (0 : Plane) T ⊆ trialSquare T ∧
    ∃ P : Plane → Plane, LipschitzWith 1 P ∧ (∀ v, P v ∈ trialSquare T) ∧
      ∀ v ∈ trialSquare T, P v = v := by
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)
  have eq : trialSquare T = L ⁻¹' Icc (fun _ => -T) (fun _ => T) := by
    ext v
    exact ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩, fun h i => ⟨h.1 i,h.2 i⟩⟩
  constructor
  · rw [eq]
    exact L.toHomeomorph.isCompact_preimage.mpr isCompact_Icc
  constructor
  · rw [eq]
    exact (convex_Icc _ _).linear_preimage L.toLinearMap
  constructor
  · intro v hv i
    have bound : ‖v‖ ≤ T := by simpa using hv
    exact abs_le.mp ((show |v i| ≤ ‖v‖ from PiLp.norm_apply_le v i).trans bound)
  · exact Fields.LogNormTrajectory.euclideanBox_retraction (lo := fun _ => -T)
      (hi := fun _ => T) (fun _ => neg_le_self hT)

/-- Affine frame used by the physical-time ODE step. -/
def moving (s : State) (r : Step) (a t : ℝ) : Plane ≃L[ℝ] Plane :=
  frameEquiv s.frame r.frame (coord a t)

/-- True position enclosure represented by a recorded slab. -/
def physicalSlab (s : State) (r : Step) (a : ℝ) : Fields.TrajectorySlabs.Slab Plane :=
  ⟨a,a + 1 / 64,fun t => Fields.TrajectorySlabs.MovingFrame.ellipsoid
    (moving s r a t) (reference a r t) (r.outgoing/(2 : ℝ)^80) ∩
    {x | dist x (reference a r t) ≤ r.physicalOut/(2 : ℝ)^80}⟩

/-- The outstanding analytic field inputs for one slab. Only continuity and
differentiability require the larger square. The quantitative spatial test
uses the Euclidean trial ball and the defect uses the central reference. -/
structure FieldBounds (s : State) (r : Step) (a : ℝ) (F : ℝ → Plane → Plane)
    (J : ℝ → Plane → Plane →L[ℝ] Plane) : Prop where
  field : ContinuousOn (fun q : ℝ × Plane => F q.1 (reference a r q.1 + moving s r a q.1 q.2))
    (Icc a (a + 1 / 64) ×ˢ trialSquare (r.trial/(2 : ℝ)^80))
  jac : ContinuousOn (fun q : ℝ × Plane => J q.1 (reference a r q.1 + moving s r a q.1 q.2))
    (Icc a (a + 1 / 64) ×ˢ trialSquare (r.trial/(2 : ℝ)^80))
  derivative : ∀ t ∈ Icc a (a + 1 / 64), ∀ v ∈ trialSquare (r.trial/(2 : ℝ)^80),
    HasFDerivAt (F t) (J t (reference a r t + moving s r a t v))
      (reference a r t + moving s r a t v)
  quadratic : ∀ t ∈ Ico a (a + 1 / 64), ∀ v ∈ Metric.closedBall (0 : Plane) (r.trial/(2 : ℝ)^80),
    ∀ w : Plane, ⟪w, Fields.LogNormTrajectory.MovingFrame.jacobian
      (J t (reference a r t + moving s r a t v)) (moving s r a t)
      (frameVelocity s.frame r.frame) w⟫ ≤ r.mu * ‖w‖^2
  residual : ∀ t ∈ Ico a (a + 1 / 64), ‖(moving s r a t).symm
    (F t (reference a r t) - referenceVelocity a r t)‖ ≤ r.defect

/-- Realize a checked datum as a physical ODE step, including the reference
jump, the shared endpoint states, and the rounded physical position error. -/
theorem physical_step {lim : Limits} {s : State} {r : Step} {a : ℝ} {F : ℝ → Plane → Plane}
    {J : ℝ → Plane → Plane →L[ℝ] Plane} (ok : test lim s r = true)
    (bounds : FieldBounds s r a F J) :
    Fields.TrajectorySlabs.Step F (physicalSlab s r a) (stateSet s) (stateSet (next r)) := by
  obtain ⟨hg,hr⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨inc,hε,hlen,hprop,htrial,_,hop,_,_,_⟩ := growth_sound hr
  have ab : a ≤ a + 1 / 64 := by linarith
  have len : a + 1 / 64-a = (1 / 64 : ℝ) := by ring
  have tight : Fields.TrajectorySlabs.MovingFrame.propagated a (a + 1 / 64)
      (r.incoming/(2:ℝ)^80) r.mu r.defect ≤ r.outgoing/(2:ℝ)^80 := by
    simpa only [Fields.TrajectorySlabs.MovingFrame.propagated, len, mul_one_div, one_div_mul_eq_div]
      using hprop
  obtain ⟨compact,conv,tube,retract⟩ := square_facts (T := r.trial/(2:ℝ)^80) (by positivity)
  have step := Fields.TrajectorySlabs.MovingFrame.step_of_defect
    (a := a) (b := a + 1 / 64) (r := r.incoming/(2:ℝ)^80) (L := (r.mu : ℝ))
    (ε := (r.defect : ℝ)) (T := r.trial/(2:ℝ)^80) ab (by positivity) hε
    (by simpa only [len, mul_one_div] using hlen) (tight.trans_lt htrial)
    compact conv tube retract (fun t _ => (hasDerivAt_reference a r t).hasDerivWithinAt)
    (fun _ ht => hasDerivWithinAt_frame hg a ht) (continuousOn_frame_inverse hg a)
    (continuous_referenceVelocity a r).continuousOn continuousOn_const
    bounds.field bounds.jac bounds.derivative bounds.quadratic bounds.residual
  have rounded := Fields.TrajectorySlabs.MovingFrame.round_outward step tight
  have start : moving s r a a = frameEquiv s.frame s.frame 0 := by
    simpa [moving,coord] using frame_start hg
  have stop : moving s r a (a + 1 / 64) = frameEquiv r.frame r.frame 0 := by
    have z : coord a (a + 1 / 64) = 1 := by unfold coord; ring
    simpa only [moving,z] using frame_end hg
  have shift : stateSet s ⊆ Fields.TrajectorySlabs.MovingFrame.ellipsoid
        (moving s r a a) (reference a r a) (r.incoming/(2:ℝ)^80) := by
    rw [reference_start,start]
    apply Fields.TrajectorySlabs.MovingFrame.ellipsoid_shift
    have hj := norm_reference_jump hg
    rw [frame_start hg] at hj
    rw [inc,Nat.cast_add,add_div]
    exact add_le_add le_rfl hj
  refine ⟨ab,fun x hx => ?_⟩
  obtain ⟨v,x₀,final,within⟩ := rounded.solve x (shift hx)
  refine ⟨v,x₀,?_,fun t ht => ?_⟩
  · change v (a + 1 / 64) ∈ Fields.TrajectorySlabs.MovingFrame.ellipsoid
      (moving s r a (a + 1 / 64)) (reference a r (a + 1 / 64)) (r.outgoing/(2:ℝ)^80) at final
    simpa only [stop,reference_end,stateSet,next,physicalSlab] using final
  · obtain ⟨deriv,ellipsoid,physical⟩ := within t ht
    refine ⟨deriv,ellipsoid,?_⟩
    change dist (v t) (reference a r t) ≤ r.physicalOut/(2:ℝ)^80
    change dist (v t) (reference a r t) ≤ ‖(moving s r a t).toContinuousLinearMap‖ * _ at physical
    apply physical.trans
    apply (mul_le_mul_of_nonneg_right (frame_op_norm hg (abs_coord_le ht)) (by positivity)).trans
    simpa only [← mul_div_assoc] using div_le_div_of_nonneg_right hop (by positivity : (0:ℝ) ≤ 2^80)

private theorem stationaryVelocity (a t : ℝ) : referenceVelocity a stationary t = 0 := by
  ext i
  fin_cases i <;> norm_num [referenceVelocity, polynomial, stationary,
    TrajectoryTaylorModel.ofDyadic,
    QPoly.scale, QPoly.deriv, QPoly.add, QPoly.eval, List.replicate_succ]

/-- With a constant identity frame and zero field, the exactly checked
stationary data supply a complete physical step, including their field bounds. -/
theorem stationary_step (a : ℝ) : Fields.TrajectorySlabs.Step (fun _ _ => 0)
    (physicalSlab (next stationary) stationary a) (stateSet (next stationary))
    (stateSet (next stationary)) := by
  apply physical_step (J := fun _ _ => 0) stationary_checked
  refine ⟨continuousOn_const, continuousOn_const, fun _ _ _ _ => ?_, ?_, ?_⟩
  · exact hasFDerivAt_const _ _
  · intro t _ v _ w
    have frame : frameVelocity (next stationary).frame stationary.frame = 0 := by
      simp [frameVelocity,next,forward,entry]
    rw [frame]
    simp [Fields.LogNormTrajectory.MovingFrame.jacobian, stationary]
  · intro t ht
    rw [stationaryVelocity]
    simp [stationary]

end PlasmaLean.Certificates.PositionFrameSlabs
