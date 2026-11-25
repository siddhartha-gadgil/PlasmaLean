/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkSectorActionBand
public import PlasmaLean.Theory.Geometry.ActionFaceBarrier

/-! # First radial exits tested against the two measured birth-centered actions -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkPhysicalActionExit
open Set Theory.KAM Certificates.PositionFrameSlabs
open DommaschkRadialFamilyContinuity DommaschkRadialActionAlternative DommaschkNativeWellAction
open DommaschkMirrorLaunch DommaschkSectorActionBand Kinetic.MirrorActionEnvelope
open Kinetic.MirrorHeightAction

abbrev reach : ℝ := 327 / 64

/-- A measured value belongs to the first well around the actual birth on an ordinary
physical field line through that birth. Only the common endpoint ODE window is required. -/
def Observation (uC zC uA zA : FA) (r φ j : ℝ) : Prop :=
  ∃ (y : ℝ → Plane) (a b : ℝ), y φ = coordinates.symm (birth uC zC uA zA r φ) ∧
    Enclosed y (-reach) reach ∧ LaunchWell (field y) φ level a b ∧
    action (field y) (density y) a b level = j

/-- Both face values occur on genuine physical trajectories. Their comparisons also hold
for every independent measurement through the same birth. -/
structure BoundaryValues (uC zC uA zA : FA) (φ : ℝ) : Prop where
  inner_exists : ∃ j, Observation uC zC uA zA (47 / 100) φ j
  outer_exists : ∃ j, Observation uC zC uA zA (239 / 500) φ j
  inner_lt : ∀ j, Observation uC zC uA zA (47 / 100) φ j → j < lowAction
  lt_outer : ∀ j, Observation uC zC uA zA (239 / 500) φ j → highAction < j

private theorem identify {uC zC uA zA : FA} {r φ j l b : ℝ} {y : ℝ → Plane}
    (time : φ ∈ Icc (-reach) reach) (path : Enclosed y (-reach) reach)
    (born : y φ = coordinates.symm (birth uC zC uA zA r φ))
    (w : LaunchWell (field y) 0 level l b) (cover : Icc l b ⊆ Icc (-reach) reach)
    (inside : φ ∈ Ioo l b) (obs : Observation uC zC uA zA r φ j) :
    j = action (field y) (density y) l b level := by
  obtain ⟨z, L, R, birthZ, pathZ, wellZ, value⟩ := obs
  obtain ⟨same, mass⟩ := transfer_well path pathZ time (born.trans birthZ.symm) w cover
  have first : LaunchWell (field z) φ level l b :=
    ⟨inside.1, inside.2, same.left_hit, same.right_hit, same.accessible⟩
  obtain ⟨left, right⟩ := wellZ.unique first
  rw [← value, left, right, mass]

theorem of_endpoint_witnesses {uC zC uA zA : FA} {φ l r L R : ℝ} {y z : ℝ → Plane}
    (time : φ ∈ Icc (-(327 / 64)) (327 / 64))
    (py : Enclosed y (-(327 / 64)) (327 / 64))
    (pz : Enclosed z (-(327 / 64)) (327 / 64))
    (yb : y φ = coordinates.symm (birth uC zC uA zA (47 / 100) φ))
    (zb : z φ = coordinates.symm (birth uC zC uA zA (239 / 500) φ))
    (wy : LaunchWell (field y) 0 level l r) (wz : LaunchWell (field z) 0 level L R)
    (cy : Icc l r ⊆ Icc (-(327 / 64)) (327 / 64))
    (cz : Icc L R ⊆ Icc (-(327 / 64)) (327 / 64))
    (lo : action (field y) (density y) l r level ≤ 1146552112157123 / 844424930131968)
    (hi : 790254733800996141875465767 / 580284393415022003858964480 ≤
      action (field z) (density z) L R level)
    (iy : φ ∈ Ioo l r) (iz : φ ∈ Ioo L R) : BoundaryValues uC zC uA zA φ := by
  constructor
  · exact ⟨_, y, l, r, yb, py, ⟨iy.1, iy.2, wy.left_hit, wy.right_hit, wy.accessible⟩, rfl⟩
  · exact ⟨_, z, L, R, zb, pz, ⟨iz.1, iz.2, wz.left_hit, wz.right_hit, wz.accessible⟩, rfl⟩
  · intro j obs
    rw [identify time py yb wy cy iy obs]
    exact lo.trans_lt (by norm_num [lowAction, target])
  · intro j obs
    rw [identify time pz zb wz cz iz obs]
    exact lt_of_lt_of_le (by norm_num [highAction, target]) hi

/-- Evaluate the action at a potential first radial exit. Before such an exit the
trajectory only has to identify its height, phase and field-line action at the face. -/
def ObservesFaces (uC zC uA zA : FA) (r φ J : ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ t ∈ Icc 0 T, (∀ s ∈ Icc 0 t, r s ∈ Icc (47 / 100) (239 / 500)) →
    (r t = 47 / 100 ∨ r t = 239 / 500) →
      |φ t| ≤ 1 / 2 ^ 19 ∧ Observation uC zC uA zA (r t) (φ t) (J t)

/-- The two certified strict boundary signs allow a closed action-drift budget.
The estimate is only required until a potential first exit. -/
theorem stays_inside {uC zC uA zA : FA} {r φ J : ℝ → ℝ} {T d : ℝ}
    (faces : ∀ θ, |θ| ≤ 1 / 2 ^ 19 → BoundaryValues uC zC uA zA θ)
    (observe : ObservesFaces uC zC uA zA r φ J T) (cr : ContinuousOn r (Icc 0 T))
    (birth : r 0 ∈ Ioo (47 / 100) (239 / 500))
    (budget : |J 0 - target| + d ≤ 19 / 10000)
    (drift : ∀ t ∈ Icc 0 T, (∀ s ∈ Icc 0 t, r s ∈ Icc (47 / 100) (239 / 500)) →
      |J t - J 0| ≤ d) : ∀ t ∈ Icc 0 T, r t ∈ Ioo (47 / 100) (239 / 500) := by
  intro t ht
  by_contra outside
  obtain ⟨s, hs, hit, prior⟩ := ActionFaceBarrier.first_hit_of_departure cr birth ht outside
  obtain ⟨phase, physical⟩ := observe s hs prior hit
  have signs := faces _ phase
  have close : |J s - target| ≤ 19 / 10000 := calc
    _ ≤ |J s - J 0| + |J 0 - target| := abs_sub_le _ _ _
    _ ≤ d + |J 0 - target| := add_le_add_left (drift s hs prior) _
    _ ≤ _ := (add_comm d _).le.trans budget
  have range := abs_le.mp close
  rcases hit with left | right
  · rw [left] at physical
    have low := signs.inner_lt _ physical
    unfold lowAction at low
    exact (not_lt_of_ge (by linarith only [range.1] : target - 21 / 10000 ≤ J s)) low
  · rw [right] at physical
    have high := signs.lt_outer _ physical
    unfold highAction at high
    exact (not_lt_of_ge (by linarith only [range.2] : J s ≤ target + 19 / 10000)) high

/-- A bounded first-order correction and a bounded second-order remainder provide the
action-drift hypothesis. Their verification on a particle path is an independent input. -/
theorem stays_inside_of_correction {uC zC uA zA : FA} {r φ J g k : ℝ → ℝ} {T ε G K : ℝ}
    (faces : ∀ θ, |θ| ≤ 1 / 2 ^ 19 → BoundaryValues uC zC uA zA θ)
    (observe : ObservesFaces uC zC uA zA r φ J T) (cr : ContinuousOn r (Icc 0 T))
    (birth : r 0 ∈ Ioo (47 / 100) (239 / 500)) (hK : 0 ≤ K)
    (budget : |J 0 - target| + (2 * |ε| * G + T * ε ^ 2 * K) ≤ 19 / 10000)
    (correction : ∀ t ∈ Icc 0 T, r t ∈ Icc (47 / 100) (239 / 500) → |g t| ≤ G)
    (residual : ∀ t ∈ Icc 0 T, r t ∈ Icc (47 / 100) (239 / 500) → |k t| ≤ K)
    (derivative : ∀ t ∈ Icc 0 T, r t ∈ Icc (47 / 100) (239 / 500) →
      HasDerivAt (fun v => J v + ε * g v) (ε ^ 2 * k t) t) :
    ∀ t ∈ Icc 0 T, r t ∈ Ioo (47 / 100) (239 / 500) := by
  apply stays_inside faces observe cr birth budget
  intro t ht prior
  have sub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have bound := AveragedConfinement.displacement_le ht.1
    (fun s hs => (derivative s (sub hs) (prior s hs)).hasDerivWithinAt)
    (fun s hs => residual s (sub hs) (prior s hs))
    (correction 0 ⟨le_rfl, ht.1.trans ht.2⟩ (Ioo_subset_Icc_self birth))
    (correction t ht (prior t (right_mem_Icc.mpr ht.1)))
  exact bound.trans (by gcongr; exact ht.2)

end PlasmaLean.Design.DommaschkPhysicalActionExit
