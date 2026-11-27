/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FlowLabelStay
public import PlasmaLean.Certificates.PositionFrameCore
public import PlasmaLean.Design.DommaschkTubeCheck
public import PlasmaLean.Design.DommaschkTubeSymmetry
public import PlasmaLean.Design.DommaschkCylindricalDrift

/-!
# A QA2R guiding centre born in a certified tube stays in it

The composition of the ingredients of note N-216, generic over the chain of position-frame
slabs. A Littlejohn guiding-centre orbit (a supplied model) in the QA2R vacuum field, born over
the two-sided tube of a chain with its field-line label near the initial point of the chain,
stays over the tube for an explicit time, and its label moves by at most `κ t`.

* `Chain`: the checked data of a chain starting at angle `0` with the identity frame.
* `halfTube`, `tube`, `isOpen_region`: the two-sided tube of the chain around angle `0`, with
  the speed bound `9/25` of the envelope (`DommaschkRegionFieldBounds.planar_speed_le`).
* `sectionCheck`, `section_of_check`, `section_of_flip`: the reflected core at angle `0` lies in
  the inner tube when the outgoing radius of the first record with twice the height of its
  reference point is below the backward radius of the first slab. The initial point need not
  lie on the midplane.
* `mem_coreD_of_label`: a point of the tube whose label and reflected label lie in the entry
  set of the chain lies in the doubled core; `closedBall_subset_entry` gives both from a ball
  around the initial point.
* `window`, `isCompact_window`, `window_subset`: the doubled core over a closed window of
  angles is a compact subset of the region of the tube.
* `mem_closed_of_bootstrap`: a continuation lemma for a path, an open set and a closed subset.
* `exists_lift_full`: the lifted path of an orbit, differentiable at every time.
* `lift_stays`: the conclusion on an interval on which the orbit is known to stay off the axis
  with nonvanishing field.
* `stays_in_tube`: the assembled theorem, without that a-priori hypothesis.

The bounds `g` for `‖∇|B|‖` and `bT` for `|B|` on the outer tube are hypotheses.

**Sanity.** `sectionCheck_stationary`, `sectionCheck_reject` are fixtures of the check, and
`side_conditions_zero` shows that the numerical side conditions of `stays_in_tube` on `κ`,
`vpar` and `b'` can be met together for `T = 0`. This is only a consistency check of the
hypotheses: no concrete instance of `Chain` with an orbit is constructed here.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkTubeDrift

open Certificates PositionFrameSlabs PositionFrameTube DommaschkJacobian DommaschkTubeCheck
open DommaschkTubeSymmetry DommaschkSignedTraceDomain DommaschkJacobianReflection Fields Set
open Contract Kinetic Kinetic.GCLittlejohn
open Fields.CylindricalLift (cylVelocity)
open DommaschkCartesianAngleFlow DommaschkCylindricalDrift

/-! ### The data of a chain and its abbreviations -/

/-- Backward radius number `k`, from the list in units of 2⁻⁸⁰. -/
abbrev radius (bs : List ℕ) (k : ℕ) : ℝ := (bs.getD k 0 : ℝ) / 2 ^ 80

/-- The outer tube of the chain, doubled by the phase-zero reflection. -/
abbrev outerD (s₀ : State) (rows : List Step) : ℝ → Set Plane :=
  FlowLabel.doubleW flipIso 0 (outer s₀ 0 rows)

/-- The inner tube of the chain, doubled by the phase-zero reflection. -/
abbrev innerD (s₀ : State) (rows : List Step) (bs : List ℕ) : ℝ → Set Plane :=
  FlowLabel.doubleV flipIso 0 (inner s₀ 0 rows (radius bs))

/-- The angle at which the chain ends. -/
abbrev stop (rows : List Step) : ℝ := time 0 rows.length

/-- Lipschitz constant of the section label in the plane. -/
abbrev labelConstant (E Bq : ℚ) : ℝ := 1 * Real.exp E * Bq

/-- The field-line label at angle `0`. -/
abbrev Lab (s₀ : State) (rows : List Step) : ℝ × Plane → Plane :=
  FlowLabel.label (euclideanFlow 0 1) (outerD s₀ rows) 0

/-- The checked data of a chain of wide position-frame slabs for the planar field-line
equation of QA2R, starting at angle `0` with the identity frame. -/
structure Chain (s₀ e : State) (rows : List Step) (bs : List ℕ) (E Bq : ℚ) : Prop where
  /-- the records are valid wide steps -/
  steps : PositionFrameWideChain.Steps s₀ rows e
  /-- field bounds on every slab -/
  bounds : FieldBoundsOn (euclideanFlow 0 1) (velocityJacobian 0 1) s₀ 0 rows ballDomain
  /-- lower bounds for the frame Jacobian on every slab -/
  lower : LowerOn (velocityJacobian 0 1) s₀ 0 rows
  /-- the backward radii pass their check -/
  radii : radiiCheck rows bs = true
  /-- the outgoing radii are below the backward radii -/
  margin : marginCheck rows bs = true
  /-- the trial tube lies in the cylindrical envelope -/
  packed : rows.all trialPacked = true
  /-- the constants of the label pass their check -/
  const : constCheck rows E Bq = true
  /-- the initial frame is the identity -/
  frame : s₀.frame = ⟨2 ^ 40, 0, 0, 2 ^ 40⟩
  /-- the chain is nonempty -/
  pos : 0 < rows.length

section ChainFacts

variable {s₀ e : State} {rows : List Step} {bs : List ℕ} {E Bq : ℚ}

/-- The geometric checks of the chain. -/
theorem Chain.geo (ch : Chain s₀ e rows bs E Bq) : Geo s₀ rows := Geo.of_steps ch.steps

/-- The inverse of the frame of the first slab at angle `0` is the identity. -/
theorem frameAt_symm_start (ch : Chain s₀ e rows bs E Bq) (a : ℝ) (w : Plane) :
    (frameAt s₀ a rows 0 a).symm w = w := by
  have start := frameAt_start (a := a) ch.geo ch.pos
  rw [time_zero] at start
  rw [start]
  exact frameEquiv_symm_identity ch.frame w

/-- The label constant is at least one. -/
theorem one_le_labelConstant (ch : Chain s₀ e rows bs E Bq) : 1 ≤ labelConstant E Bq := by
  obtain ⟨hE, hB⟩ := const_of_check ch.const
  have E0 : (0 : ℝ) ≤ E :=
    (Finset.sum_nonneg fun j _ => div_nonneg (le_max_left _ _) (by norm_num)).trans hE
  have hexp : (1 : ℝ) ≤ Real.exp E := Real.one_le_exp E0
  have hBq : (1 : ℝ) ≤ Bq := by
    have mem : (0 : ℝ) ∈ Icc (time 0 0) (time 0 (0 + 1)) := by
      rw [time_succ, time_zero]
      exact ⟨le_rfl, by norm_num⟩
    have inv := (frameAt_inv_op_norm (a := 0) ch.geo ch.pos mem).trans (hB 0 ch.pos)
    have le := (frameAt s₀ 0 rows 0 0).symm.toContinuousLinearMap.le_opNorm
      (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
    have id : (frameAt s₀ 0 rows 0 0).symm.toContinuousLinearMap
        (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) = EuclideanSpace.single (0 : Fin 2) (1 : ℝ) :=
      frameAt_symm_start ch 0 _
    rw [id, PiLp.norm_single, norm_one, mul_one] at le
    exact le.trans inv
  unfold labelConstant
  nlinarith

/-- Every point of the trial tube lies in the cylindrical envelope. -/
theorem region_of_outer (ch : Chain s₀ e rows bs E Bq) {t : ℝ} {x : Plane}
    (hx : x ∈ outer s₀ 0 rows t) : Region x :=
  DommaschkTubeCheck.region_of_outer ch.geo ch.packed hx

/-- Every point of the doubled trial tube lies in the cylindrical envelope. -/
theorem region_of_outerD (ch : Chain s₀ e rows bs E Bq) {t : ℝ} {x : Plane}
    (hx : x ∈ outerD s₀ rows t) : Region x := by
  rcases lt_trichotomy 0 t with h | h | h
  · rw [outerD, FlowLabel.doubleW_of_lt h] at hx
    exact region_of_outer ch hx
  · rw [outerD, ← h, FlowLabel.doubleW_self] at hx
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact region_of_outer ch hx
    · exact region_flip (region_of_outer ch hy)
  · rw [outerD, FlowLabel.doubleW_of_gt h] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact region_flip (region_of_outer ch hy)

/-! ### The tube -/

/-- **One-sided tube.** For toroidal angles in `[0, stop rows)`: from the inner tube field lines
run back to angle `0` inside the trial tube, where they are unique, at most `labelConstant`
times further apart at angle `0`, and have speed at most `9/25`. -/
theorem halfTube (ch : Chain s₀ e rows bs E Bq) :
    FlowLabel.HalfTube (euclideanFlow 0 1) flipIso 0 (stop rows) (outer s₀ 0 rows)
      (inner s₀ 0 rows (radius bs)) (labelConstant E Bq) (9 / 25) := by
  obtain ⟨hE, hB⟩ := const_of_check ch.const
  exact PositionFrameTube.halfTube ch.geo ch.bounds ch.lower (radii_of_check ch.radii) ch.pos hE
    (frameAt_start_identity ch.geo ch.pos ch.frame) hB (one_le_labelConstant ch) (by norm_num)
    flipIso flipIso_involutive
    (fun t x hx => DommaschkRegionFieldBounds.planar_speed_le (region_of_outer ch hx) t)
    (fun t x hx => flow_symm t x (lt_of_lt_of_le (by norm_num) (region_of_outer ch hx).1.1))

/-- **Two-sided tube** around toroidal angle `0`, by the phase-zero reflection. -/
theorem tube (ch : Chain s₀ e rows bs E Bq) :
    FlowLabel.Tube (euclideanFlow 0 1) 0 (2 * 0 - stop rows) (stop rows) (outerD s₀ rows)
      (innerD s₀ rows bs) (labelConstant E Bq) (9 / 25) :=
  (halfTube ch).double

/-- The space-time region over the two-sided inner tube is open. -/
theorem isOpen_region (ch : Chain s₀ e rows bs E Bq) :
    IsOpen (FlowLabel.region (2 * 0 - stop rows) (stop rows) (innerD s₀ rows bs)) :=
  PositionFrameTube.isOpen_region ch.geo (radii_of_check ch.radii) flipIso flipIso_involutive
    ch.pos

/-! ### The section hypothesis off the midplane -/

/-- The reflection moves a point by twice its height. -/
theorem norm_flip_sub (q : Plane) : ‖flipIso q - q‖ = 2 * |q 1| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp only [PiLp.sub_apply, flipIso_apply, flip_zero, flip_one, sub_self, Real.norm_eq_abs,
    sq_abs]
  rw [show (0 : ℝ) ^ 2 + (-q 1 - q 1) ^ 2 = (2 * |q 1|) ^ 2 by rw [mul_pow, sq_abs]; ring]
  exact Real.sqrt_sq (by positivity)

/-- The distance of a reflected point from a centre is at most the distance of the point, plus
twice the height of the centre. -/
theorem norm_flip_sub_le (y q : Plane) : ‖flipIso y - q‖ ≤ ‖y - q‖ + 2 * |q 1| := by
  have split : flipIso y - q = flipIso (y - q) + (flipIso q - q) := by
    rw [map_sub]
    abel
  rw [split, ← norm_flip_sub q, ← flipIso.norm_map (y - q)]
  exact norm_add_le _ _

/-- **The section hypothesis for the identity initial frame.** If the outgoing radius of the
first record, with twice the height of its reference point at the initial time, is below the
backward radius of the first slab, the reflected core at the initial time lies in the inner
tube. -/
theorem section_of_flip (ch : Chain s₀ e rows bs E Bq) {a : ℝ} {β : ℕ → ℝ}
    (hβ : ((rowAt rows 0).outgoing : ℝ) / 2 ^ 80 + 2 * |reference a (rowAt rows 0) a 1| < β 1) :
    flipIso '' core s₀ a rows a ⊆ inner s₀ a rows β a := by
  have g0 : ∀ y : Plane, gauge s₀ a rows 0 (a, y) = ‖y - reference a (rowAt rows 0) a‖ := by
    intro y
    change ‖(frameAt s₀ a rows 0 a).symm (y - reference (time a 0) (rowAt rows 0) a)‖ = _
    rw [frameAt_symm_start ch, time_zero]
  rintro _ ⟨y, ⟨k, hk, hmem, hg⟩, rfl⟩
  obtain rfl : k = 0 := by
    have h' : time a k ≤ time a 0 := by
      rw [time_zero]
      exact hmem.1
    exact Nat.le_zero.mp (time_le_iff.mp h')
  rw [g0] at hg
  refine ⟨0, ch.pos, ?_, ?_⟩
  · rw [time_succ, time_zero]
    exact ⟨le_rfl, by linarith⟩
  · rw [g0]
    exact lt_of_le_of_lt ((norm_flip_sub_le _ _).trans (by linarith)) hβ

/-- Executable form of the hypothesis of `section_of_flip`, in units of 2⁻⁸⁰: the outgoing
radius of the first record with twice the height of its first reference point is below the
second backward radius. -/
def sectionCheck (rows : List Step) (bs : List ℕ) : Bool :=
  Nat.blt ((rowAt rows 0).outgoing + 2 * (firstPoint (rowAt rows 0)).y.natAbs) (bs.getD 1 0)

/-- **Soundness of the section check.** -/
theorem section_of_check (ch : Chain s₀ e rows bs E Bq) (h : sectionCheck rows bs = true) :
    flipIso '' core s₀ 0 rows 0 ⊆ inner s₀ 0 rows (radius bs) 0 := by
  refine section_of_flip ch ?_
  rw [sectionCheck, Nat.blt_eq] at h
  have h' : (((rowAt rows 0).outgoing + 2 * (firstPoint (rowAt rows 0)).y.natAbs : ℕ) : ℝ) <
      (bs.getD 1 0 : ℝ) := by exact_mod_cast h
  have height : |reference 0 (rowAt rows 0) 0 1| =
      ((firstPoint (rowAt rows 0)).y.natAbs : ℝ) / 2 ^ 80 := by
    rw [reference_start, Nat.cast_natAbs, Int.cast_abs]
    simp [point, abs_div]
  rw [height, radius]
  push_cast at h'
  rw [← mul_div_assoc, ← add_div]
  exact div_lt_div_of_pos_right h' (by positivity)

/-! ### Labels in the entry set and the doubled core -/

/-- With the identity frame, the entry set is the closed ball around the initial point. -/
theorem mem_stateSet_iff (ch : Chain s₀ e rows bs E Bq) (v : Plane) :
    v ∈ stateSet s₀ ↔ ‖v - point s₀.point‖ ≤ s₀.radius / 2 ^ 80 := by
  change ‖(frameEquiv s₀.frame s₀.frame 0).symm (v - point s₀.point)‖ ≤ _ ↔ _
  rw [frameEquiv_symm_identity ch.frame]

/-- A closed ball around the initial point, of radius smaller than the radius of the entry set
by twice the height of the initial point, lies in the entry set together with its mirror
image. -/
theorem closedBall_subset_entry (ch : Chain s₀ e rows bs E Bq) {ρ : ℝ}
    (hρ : ρ + 2 * |(s₀.point.y : ℝ)| / 2 ^ 80 ≤ s₀.radius / 2 ^ 80) :
    Metric.closedBall (point s₀.point) ρ ⊆
      {ℓ | ℓ ∈ stateSet s₀ ∧ flipIso ℓ ∈ stateSet s₀} := by
  intro ℓ hℓ
  rw [Metric.mem_closedBall, dist_eq_norm] at hℓ
  have height : 2 * |point s₀.point 1| = 2 * |(s₀.point.y : ℝ)| / 2 ^ 80 := by
    simp [point, abs_div, mul_div_assoc]
  have nonneg : 0 ≤ 2 * |(s₀.point.y : ℝ)| / (2 : ℝ) ^ 80 := by positivity
  refine ⟨(mem_stateSet_iff ch ℓ).mpr (by linarith), (mem_stateSet_iff ch _).mpr ?_⟩
  have := norm_flip_sub_le ℓ (point s₀.point)
  rw [height] at this
  linarith

/-- **Points with label in the entry set lie in the doubled core.** A point of the region of the
two-sided tube whose label lies in the entry set of the chain, together with the mirror image
of the label, lies in the doubled core. -/
theorem mem_coreD_of_label (ch : Chain s₀ e rows bs E Bq) {p : ℝ × Plane}
    (hp : p ∈ FlowLabel.region (2 * 0 - stop rows) (stop rows) (innerD s₀ rows bs))
    (h1 : Lab s₀ rows p ∈ stateSet s₀) (h2 : flipIso (Lab s₀ rows p) ∈ stateSet s₀) :
    p.2 ∈ coreD flipIso s₀ 0 rows p.1 := by
  obtain ⟨t, x⟩ := p
  obtain ⟨ht, hx⟩ := hp
  change t ∈ Ioo (2 * 0 - stop rows) (stop rows) at ht
  change x ∈ innerD s₀ rows bs t at hx
  change x ∈ coreD flipIso s₀ 0 rows t
  have half := halfTube ch
  have tb := tube ch
  have forward : ∀ {t : ℝ} {x : Plane}, t ∈ Ico 0 (stop rows) →
      t ∈ Ioo (2 * 0 - stop rows) (stop rows) →
      x ∈ inner s₀ 0 rows (radius bs) t → Lab s₀ rows (t, x) ∈ stateSet s₀ →
      x ∈ core s₀ 0 rows t := by
    intro t x ht ht' hx hl
    obtain ⟨v, hv, sol⟩ := half.reach t ht x hx
    have sol' : FlowLabel.SolOn (euclideanFlow 0 1) (outerD s₀ rows) 0 t v := by
      intro τ hτ
      refine ⟨(sol τ hτ).1, FlowLabel.subset_doubleW ?_ (sol τ hτ).2⟩
      rw [uIcc_of_le ht.1] at hτ
      exact hτ.1
    have lab : Lab s₀ rows (t, x) = v 0 := FlowLabel.label_eq tb (p := (t, x)) ht' hv sol'
    rw [lab] at hl
    exact mem_core_of_label ch.steps ch.bounds ch.lower ch.pos ⟨ht.1, ht.2.le⟩ hv sol hl
  rcases lt_trichotomy 0 t with h | h | h
  · rw [show coreD flipIso s₀ 0 rows t = core s₀ 0 rows t from FlowLabel.doubleW_of_lt h]
    rw [innerD, FlowLabel.doubleV_of_lt h] at hx
    exact forward ⟨h.le, ht.2⟩ ht hx h1
  · subst h
    rw [show coreD flipIso s₀ 0 rows 0 = _ from FlowLabel.doubleW_self]
    rw [innerD, FlowLabel.doubleV_self] at hx
    exact Or.inl (forward ⟨le_rfl, ht.2⟩ ht hx.1 h1)
  · rw [show coreD flipIso s₀ 0 rows t = _ from FlowLabel.doubleW_of_gt h]
    rw [innerD, FlowLabel.doubleV_of_gt h] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hb : 2 * 0 - t < stop rows := by linarith [ht.1]
    have ht0 : (0 : ℝ) ≤ 2 * 0 - t := by linarith
    obtain ⟨w, hw, sol⟩ := half.reach (2 * 0 - t) ⟨ht0, hb⟩ y hy
    have sol' := half.solOn_reflect h hb sol
    have lab : Lab s₀ rows (t, flipIso y) = flipIso (w (2 * 0 - 0)) :=
      FlowLabel.label_eq tb (p := (t, flipIso y)) ht (congrArg flipIso hw) sol'
    rw [lab, flipIso_involutive, show (2 * 0 - 0 : ℝ) = 0 by ring] at h2
    exact mem_image_of_mem flipIso
      (mem_core_of_label ch.steps ch.bounds ch.lower ch.pos ⟨ht0, hb.le⟩ hw sol h2)

/-! ### The compact core window -/

/-- The doubled core over the closed window of angles `[-b', b']`. -/
def window (s₀ : State) (rows : List Step) (b' : ℝ) : Set (ℝ × Plane) :=
  {p | p.1 ∈ Icc (-b') b' ∧ p.2 ∈ coreD flipIso s₀ 0 rows p.1}

/-- The core window is closed. -/
theorem isClosed_window (ch : Chain s₀ e rows bs E Bq) (b' : ℝ) :
    IsClosed (window s₀ rows b') :=
  isClosed_coreD_window ch.geo flipIso flipIso_involutive (-b') b'

/-- A core window ending before the end of the chain lies in the region of the tube. -/
theorem window_subset (ch : Chain s₀ e rows bs E Bq) (hsec : sectionCheck rows bs = true)
    {b' : ℝ} (hb' : b' < stop rows) :
    window s₀ rows b' ⊆ FlowLabel.region (2 * 0 - stop rows) (stop rows) (innerD s₀ rows bs) := by
  rintro p ⟨ht, hx⟩
  have ht' : p.1 ∈ Ioo (2 * 0 - stop rows) (stop rows) :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact ⟨ht', coreD_subset ch.steps (margin_of_check ch.margin) flipIso flipIso_involutive
    (section_of_check ch hsec) ht' hx⟩

/-- The points of a core window lie over the cylindrical envelope. -/
theorem region_of_window (ch : Chain s₀ e rows bs E Bq) (hsec : sectionCheck rows bs = true)
    {b' : ℝ} (hb' : b' < stop rows) {p : ℝ × Plane} (hp : p ∈ window s₀ rows b') :
    Region p.2 :=
  have h := window_subset ch hsec hb' hp
  region_of_outerD ch ((tube ch).subset h.1 h.2)

/-- The cylindrical envelope is bounded. -/
theorem norm_le_of_region {x : Plane} (h : Region x) : ‖x‖ ≤ 2 := by
  obtain ⟨⟨lo, hi⟩, hz⟩ := h
  obtain ⟨z1, z2⟩ := abs_le.mp hz
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  nlinarith

/-- **The core window is compact.** -/
theorem isCompact_window (ch : Chain s₀ e rows bs E Bq) (hsec : sectionCheck rows bs = true)
    {b' : ℝ} (hb' : b' < stop rows) : IsCompact (window s₀ rows b') := by
  refine IsCompact.of_isClosed_subset
    ((isCompact_Icc (a := -b') (b := b')).prod (isCompact_closedBall (0 : Plane) 2))
    (isClosed_window ch b') fun p hp => ⟨hp.1, ?_⟩
  rw [mem_closedBall_zero_iff]
  exact norm_le_of_region (region_of_window ch hsec hb' hp)

end ChainFacts

/-! ### Continuation and the lifted path -/

/-- The point of space with lifted cylindrical coordinates `(θ, (R, z))` depends continuously
on them. -/
theorem continuous_cylPoint :
    Continuous fun p : ℝ × Plane => cylPoint (p.2 0) p.1 (p.2 1) := by
  unfold cylPoint
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  fin_cases i <;>
    simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;>
    fun_prop

/-- **Continuation.** Let `γ` be continuous at the times of `[0, T]`, `Ω` open and `K ⊆ Ω`
closed, with `γ 0 ∈ Ω`. If staying in `Ω` up to a time implies staying in `K` up to that time,
then `γ` stays in `K` on `[0, T]`. -/
theorem mem_closed_of_bootstrap {Y : Type*} [TopologicalSpace Y] {γ : ℝ → Y} {T : ℝ}
    {Ω K : Set Y} (hT : 0 ≤ T) (cont : ∀ t ∈ Icc 0 T, ContinuousAt γ t) (hΩ : IsOpen Ω)
    (hK : IsClosed K) (sub : K ⊆ Ω) (h0 : γ 0 ∈ Ω)
    (step : ∀ t ∈ Icc 0 T, (∀ s ∈ Icc 0 t, γ s ∈ Ω) → ∀ s ∈ Icc 0 t, γ s ∈ K) :
    ∀ t ∈ Icc 0 T, γ t ∈ K := by
  have zero : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT
  have only0 : ∀ s ∈ Icc (0 : ℝ) 0, γ s ∈ Ω := by
    intro s hs
    rw [Icc_self, mem_singleton_iff] at hs
    rwa [hs]
  let A : Set ℝ := {t | ∀ s ∈ Icc 0 t, γ s ∈ K}
  have all : Icc 0 T ⊆ A := by
    refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin ?_ ?_ ?_
    · refine isClosed_of_closure_subset fun t ht => ?_
      have htI : t ∈ Icc 0 T := by
        have := closure_mono (inter_subset_right (s := A) (t := Icc 0 T)) ht
        rwa [isClosed_Icc.closure_eq] at this
      refine ⟨fun s hs => ?_, htI⟩
      rcases hs.2.lt_or_eq with hlt | heq
      · obtain ⟨t', ht', ht'A⟩ := mem_closure_iff.mp ht (Ioi s) isOpen_Ioi hlt
        exact ht'A.1 s ⟨hs.1, (mem_Ioi.mp ht').le⟩
      · rw [heq]
        have c := (cont t htI).continuousWithinAt (s := A ∩ Icc 0 T)
        have := c.mem_closure ht (t := K) fun t' ht' => ht'.1 t' ⟨ht'.2.1, le_rfl⟩
        rwa [hK.closure_eq] at this
    · exact step 0 zero only0
    · rintro t ⟨htA, ht⟩
      have htI : t ∈ Icc 0 T := ⟨ht.1, ht.2.le⟩
      have near : ∀ᶠ t' in nhds t, γ t' ∈ Ω :=
        (cont t htI).eventually (hΩ.mem_nhds (sub (htA t ⟨ht.1, le_rfl⟩)))
      obtain ⟨l, u, hlu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp near
      have lt : t < min u T := lt_min hlu.2 ht.2
      refine Filter.mem_of_superset (Ioo_mem_nhdsGT lt) fun t' ht' => ?_
      have ht'I : t' ∈ Icc 0 T := ⟨ht.1.trans ht'.1.le, ht'.2.le.trans (min_le_right _ _)⟩
      refine step t' ht'I fun s hs => ?_
      rcases le_or_gt s t with h | h
      · exact sub (htA s ⟨hs.1, h⟩)
      · exact hsub ⟨hlu.1.trans h, hs.2.trans_lt (ht'.2.trans_le (min_le_left _ _))⟩
  exact fun t ht => all ht t (right_mem_Icc.mpr ht.1)

/-- **Lifted QA2R guiding-centre orbit, differentiable at every time.** A Littlejohn orbit in
the QA2R field on `[0, T]` that stays off the axis and where the field does not vanish has a
lifted path `X = (θ, (R, z))` with velocity `λ (1, euclideanFlow 0 1 θ (R, z)) + w` at every time
of `[0, T]`, where `λ = (v_∥/|B|) B_φ/R`. The energy keeps its value at birth, and at the times
at which the lifted point is over the envelope, `w` is the lifted drift, bounded in terms of
the energy at birth. -/
theorem exists_lift_full {m q : ℝ} {bth : GCBirth} {z : ℝ → Space × ℝ} {T θ₀ R₀ z₀ : ℝ}
    (hT : 0 ≤ T) (hm : 0 < m) (hq : q ≠ 0) (hμ : 0 ≤ bth.2.2)
    (orbit : GCBirthOrbitOn B m q bth z T)
    (reg : ∀ τ ∈ Icc 0 T, (z τ).1 ∈ CylAlgebra.domain ∧ B (z τ).1 ≠ 0)
    (start : bth.1 = cylPoint R₀ θ₀ z₀) (hR₀ : 0 < R₀) :
    ∃ (X : ℝ → ℝ × Plane) (w : ℝ → ℝ × Plane), X 0 = (θ₀, WithLp.toLp 2 ![R₀, z₀]) ∧
      ∀ τ ∈ Icc 0 T,
        (z τ).1 = cylPoint ((X τ).2 0) (X τ).1 ((X τ).2 1) ∧
        HasDerivAt X (CylindricalDrift.rate B omega (z τ) (X τ) •
          FlowLabel.field (euclideanFlow 0 1) (X τ) + w τ) τ ∧
        hamiltonian m bth.2.2 B (z τ).1 (z τ).2 = hamiltonian m bth.2.2 B bth.1 bth.2.1 ∧
        (Region (X τ).2 → ‖w τ‖ ≤ max 1 ((X τ).2 0)⁻¹ *
          (2 * hamiltonian m bth.2.2 B bth.1 bth.2.1 / (|q| * ‖B (z τ).1‖ ^ 2) *
            ‖gradAbsB B (z τ).1‖)) := by
  have hv := CylindricalDrift.continuousOn_velocity orbit (fun τ hτ =>
    continuousAt_velocity (reg τ hτ).1 (reg τ hτ).2 m q bth.2.2 (z τ).2)
  have diff : ∀ τ ∈ Icc 0 T, DifferentiableAt ℝ B (z τ).1 := fun τ hτ =>
    (DommaschkRegionRegularity.contDiffAt_domain (reg τ hτ).1).differentiableAt (by norm_num)
  have energy := CylindricalDrift.hamiltonian_eq_birth hm.ne' orbit
    (fun τ hτ => (diff τ hτ).norm ℝ (reg τ hτ).2)
  obtain ⟨X, hX0, h⟩ :=
    CylindricalDrift.exists_lift hT orbit hv (fun τ hτ => (reg τ hτ).1) start hR₀
  refine ⟨X, fun τ => cylVelocity (X τ).1 ((X τ).2 0) (littlejohnVelocity B m q bth.2.2 (z τ)).1 -
    CylindricalDrift.rate B omega (z τ) (X τ) • FlowLabel.field (euclideanFlow 0 1) (X τ),
    hX0, fun τ hτ => ?_⟩
  obtain ⟨hpt, hpos, hd⟩ := h τ hτ
  refine ⟨hpt, by rwa [add_sub_cancel], energy τ hτ, fun hG => ?_⟩
  have nz : B (z τ).1 ≠ 0 := (reg τ hτ).2
  have nc : curl (fderiv ℝ B (z τ).1) = 0 := by
    rw [hpt]
    exact DommaschkRegionRegularity.field_curl hG _
  have rl : cylVelocity (X τ).1 ((X τ).2 0) (B (z τ).1) =
      omega (X τ) • FlowLabel.field (euclideanFlow 0 1) (X τ) := by
    rw [hpt]
    exact cylVelocity_field hG
  beta_reduce
  rw [CylindricalDrift.cylVelocity_littlejohn nz (diff τ hτ) nc hq rl, add_sub_cancel_left,
    ← energy τ hτ]
  exact CylindricalDrift.norm_perturbation_le hpos nz hm.le hμ

/-! ### The assembled theorem -/

section Orbit

variable {s₀ e : State} {rows : List Step} {bs : List ℕ} {E Bq : ℚ}
  {m q g bT κ r vpar b' T θ₀ R₀ z₀ : ℝ} {bth : GCBirth} {z : ℝ → Space × ℝ}
  (ch : Chain s₀ e rows bs E Bq) (hsec : sectionCheck rows bs = true) (hbT : 0 < bT)
  (hfield : ∀ t ∈ Ioo (-stop rows) (stop rows), ∀ x ∈ outerD s₀ rows t,
    ‖gradAbsB B (cylPoint (x 0) t (x 1))‖ ≤ g ∧ bT ≤ ‖B (cylPoint (x 0) t (x 1))‖)
  (hm : 0 < m) (hq : q ≠ 0) (hμ : 0 ≤ bth.2.2) (start : bth.1 = cylPoint R₀ θ₀ z₀)
  (hp₀ : ((θ₀, WithLp.toLp 2 ![R₀, z₀]) : ℝ × Plane) ∈
    FlowLabel.region (2 * 0 - stop rows) (stop rows) (innerD s₀ rows bs))
  (orbit : GCBirthOrbitOn B m q bth z T) (hT : 0 ≤ T)
  (hκ : labelConstant E Bq * (1 + 9 / 25) *
    (8 / 7 * (2 * hamiltonian m bth.2.2 B bth.1 bth.2.1 / (|q| * bT ^ 2) * g)) ≤ κ)
  (hstart : ‖Lab s₀ rows (θ₀, WithLp.toLp 2 ![R₀, z₀]) - point s₀.point‖ ≤ r)
  (hball : r + κ * T + 2 * |(s₀.point.y : ℝ)| / 2 ^ 80 ≤ s₀.radius / 2 ^ 80)
  (hvpar : 2 * (hamiltonian m bth.2.2 B bth.1 bth.2.1 - bth.2.2 * bT) ≤ m * vpar ^ 2)
  (hvpar0 : 0 ≤ vpar)
  (hwin : |θ₀| + (vpar / bT * ((13 / 10) / (7 / 8)) +
    8 / 7 * (2 * hamiltonian m bth.2.2 B bth.1 bth.2.1 / (|q| * bT ^ 2) * g)) * T ≤ b')
  (hb' : b' < stop rows)

include ch hsec hbT hfield hm hq hμ start hp₀ orbit hκ hstart hball hvpar hvpar0 hwin hb'

/-- **No exit, given regularity.** On an interval `[0, T']`, `T' ≤ T`, on which the orbit stays
off the axis and the field does not vanish at its points, the lifted path stays in the core
window and its label moves by at most `κ t`. The hypotheses are those of `stays_in_tube`. -/
theorem lift_stays {T' : ℝ} (hT' : T' ∈ Icc 0 T)
    (reg : ∀ τ ∈ Icc 0 T', (z τ).1 ∈ CylAlgebra.domain ∧ B (z τ).1 ≠ 0) :
    ∃ X : ℝ → ℝ × Plane, X 0 = (θ₀, WithLp.toLp 2 ![R₀, z₀]) ∧ ∀ t ∈ Icc 0 T',
      (z t).1 = cylPoint ((X t).2 0) (X t).1 ((X t).2 1) ∧ X t ∈ window s₀ rows b' ∧
      ‖Lab s₀ rows (X t) - Lab s₀ rows (θ₀, WithLp.toLp 2 ![R₀, z₀])‖ ≤ κ * t := by
  have tb := tube ch
  have hC : 0 ≤ labelConstant E Bq := le_trans zero_le_one tb.one_le
  have reg₀ : Region (WithLp.toLp 2 ![R₀, z₀] : Plane) :=
    region_of_outerD ch (tb.subset hp₀.1 hp₀.2)
  have hR₀ : 0 < R₀ := lt_of_lt_of_le (by norm_num) (show (7 / 8 : ℝ) ≤ R₀ from reg₀.1.1)
  have e0 : (2 : ℝ) * 0 - stop rows = -stop rows := by ring
  have hfield' : ∀ p ∈ FlowLabel.region (2 * 0 - stop rows) (stop rows) (innerD s₀ rows bs),
      ‖gradAbsB B (cylPoint (p.2 0) p.1 (p.2 1))‖ ≤ g ∧
        bT ≤ ‖B (cylPoint (p.2 0) p.1 (p.2 1))‖ :=
    fun p hp => hfield p.1 (e0 ▸ hp.1) p.2 (tb.subset hp.1 hp.2)
  have hg : 0 ≤ g := (norm_nonneg _).trans (hfield' _ hp₀).1
  have hH : 0 ≤ 2 * hamiltonian m bth.2.2 B bth.1 bth.2.1 := by
    have h1 := mul_nonneg hμ (norm_nonneg (B bth.1))
    have h2 := mul_nonneg hm.le (sq_nonneg bth.2.1)
    rw [hamiltonian]
    linarith
  have hqa : 0 < |q| := abs_pos.mpr hq
  set H := hamiltonian m bth.2.2 B bth.1 bth.2.1 with hHdef
  set D := 8 / 7 * (2 * H / (|q| * bT ^ 2) * g) with hD
  have hD0 : 0 ≤ D := by positivity
  have hκ0 : 0 ≤ κ := le_trans (by positivity) hκ
  have hL0 : 0 ≤ vpar / bT * ((13 / 10) / (7 / 8)) + D := by positivity
  obtain ⟨X, w, hX0, h⟩ := exists_lift_full hT'.1 hm hq hμ
    ⟨orbit.1, fun s hs => orbit.2 s ⟨hs.1, hs.2.trans hT'.2⟩⟩ reg start hR₀
  -- bounds at the times at which the lifted point is in the region of the tube
  have inreg : ∀ t ∈ Icc 0 T',
      X t ∈ FlowLabel.region (2 * 0 - stop rows) (stop rows) (innerD s₀ rows bs) →
      ‖w t‖ ≤ D ∧ |CylindricalDrift.rate B omega (z t) (X t)| ≤
        vpar / bT * ((13 / 10) / (7 / 8)) := by
    intro t ht hreg
    obtain ⟨hpt, -, energy, hw⟩ := h t ht
    have hG : Region (X t).2 := region_of_outerD ch (tb.subset hreg.1 hreg.2)
    obtain ⟨hgrad, hstr⟩ := hfield' _ hreg
    rw [← hpt] at hgrad hstr
    have hBpos : 0 < ‖B (z t).1‖ := hbT.trans_le hstr
    constructor
    · refine (hw hG).trans ?_
      have hmax := max_inv_le hG
      rw [hD]
      gcongr
    · obtain ⟨lo, hi⟩ := omega_bounds hG
      rw [CylindricalDrift.abs_rate_eq, abs_of_nonneg (by linarith : (0 : ℝ) ≤ omega (X t))]
      have hv : |(z t).2| ≤ vpar := by
        refine abs_le_of_sq_le_sq ?_ hvpar0
        have hE : m * (z t).2 ^ 2 / 2 + bth.2.2 * ‖B (z t).1‖ = H := energy
        have := mul_le_mul_of_nonneg_left hstr hμ
        have : m * (z t).2 ^ 2 ≤ m * vpar ^ 2 := by linarith
        exact le_of_mul_le_mul_left this hm
      gcongr
  have ball : Metric.closedBall (point s₀.point) (r + κ * T') ⊆
      {ℓ | ℓ ∈ stateSet s₀ ∧ flipIso ℓ ∈ stateSet s₀} :=
    closedBall_subset_entry ch (by nlinarith [mul_le_mul_of_nonneg_left hT'.2 hκ0])
  have small : ∀ t ∈ Icc 0 T',
      (∀ s ∈ Icc 0 t, X s ∈ FlowLabel.region (2 * 0 - stop rows) (stop rows)
        (innerD s₀ rows bs)) → labelConstant E Bq * (1 + 9 / 25) * ‖w t‖ ≤ κ := by
    intro t ht inU
    have hw := (inreg t ht (inU t (right_mem_Icc.mpr ht.1))).1
    exact (mul_le_mul_of_nonneg_left hw (by positivity)).trans hκ
  have window : ∀ t ∈ Icc 0 T',
      (∀ s ∈ Icc 0 t, X s ∈ FlowLabel.region (2 * 0 - stop rows) (stop rows)
        (innerD s₀ rows bs)) → (X t).1 ∈ Icc (-b') b' := by
    intro t ht inU
    have sub : Icc 0 t ⊆ Icc 0 T' := Icc_subset_Icc_right ht.2
    have der : ∀ s ∈ Icc 0 t, HasDerivWithinAt (fun s => (X s).1)
        ((CylindricalDrift.rate B omega (z s) (X s) •
          FlowLabel.field (euclideanFlow 0 1) (X s) + w s).1) (Icc 0 t) s := by
      intro s hs
      have d := (ContinuousLinearMap.fst ℝ ℝ Plane).hasFDerivAt.comp_hasDerivAt s
        (h s (sub hs)).2.1
      exact d.hasDerivWithinAt
    have bound : ∀ s ∈ Icc 0 t, ‖(CylindricalDrift.rate B omega (z s) (X s) •
        FlowLabel.field (euclideanFlow 0 1) (X s) + w s).1‖ ≤
        vpar / bT * ((13 / 10) / (7 / 8)) + D := by
      intro s hs
      obtain ⟨hw, hr⟩ := inreg s (sub hs) (inU s hs)
      rw [Real.norm_eq_abs]
      exact (CylindricalDrift.abs_angle_rate_le _ _ _ _).trans (add_le_add hr hw)
    have mv := (convex_Icc 0 t).norm_image_sub_le_of_norm_hasDerivWithin_le der bound
      (left_mem_Icc.mpr ht.1) (right_mem_Icc.mpr ht.1)
    have mv' : |(X t).1 - θ₀| ≤ (vpar / bT * ((13 / 10) / (7 / 8)) + D) * t := by
      simpa [hX0, abs_of_nonneg ht.1] using mv
    have hLt := mul_le_mul_of_nonneg_left (ht.2.trans hT'.2) hL0
    have tri := abs_sub_abs_le_abs_sub (X t).1 θ₀
    exact abs_le.mp (by linarith)
  have main := FlowLabel.stays_core tb (isOpen_region ch)
    (fun p hp => DommaschkRegionRegularity.contDiffAt_spaceTime_region
      (region_of_outerD ch (tb.subset hp.1 hp.2)) p.1)
    (isClosed_window ch b') (window_subset ch hsec hb')
    (S := {ℓ | ℓ ∈ stateSet s₀ ∧ flipIso ℓ ∈ stateSet s₀}) (a' := -b') (b' := b')
    (fun p hp hw hS => ⟨hw, mem_coreD_of_label ch hp hS.1 hS.2⟩)
    (lam := fun t => CylindricalDrift.rate B omega (z t) (X t)) (r := r)
    (ℓ₀ := point s₀.point) hT'.1 (by rw [hX0]; exact hp₀) (fun t ht => (h t ht).2.1) small
    window (by rw [hX0]; exact hstart) ball
  refine ⟨X, hX0, fun t ht => ⟨(h t ht).1, (main t ht).1, ?_⟩⟩
  have := (main t ht).2
  rwa [hX0] at this

include hT

/-- **A QA2R guiding centre born in the tube stays in it.** A Littlejohn guiding-centre orbit
on `[0, T]` in the QA2R field, born at a point of the region of the two-sided tube of the chain
whose label is within `r` of the initial point of the chain, has a lifted path that stays in
the region of the tube, in the doubled core and in the window of angles `[-b', b']`, and its
label moves by at most `κ t`. Here `g` and `bT` bound `‖∇|B|‖` and `|B|` on the outer tube,
`κ` dominates the label constant times the drift bound, the closed ball of radius `r + κ T`
around the initial point lies in the entry set of the chain together with its mirror image,
`vpar` bounds the parallel speed by the energy, and the angle does not leave `[-b', b']`. -/
theorem stays_in_tube :
    ∃ X : ℝ → ℝ × Plane, X 0 = (θ₀, WithLp.toLp 2 ![R₀, z₀]) ∧ ∀ t ∈ Icc 0 T,
      (z t).1 = cylPoint ((X t).2 0) (X t).1 ((X t).2 1) ∧
      X t ∈ FlowLabel.region (2 * 0 - stop rows) (stop rows) (innerD s₀ rows bs) ∧
      (X t).2 ∈ coreD flipIso s₀ 0 rows (X t).1 ∧ |(X t).1| ≤ b' ∧
      ‖Lab s₀ rows (X t) - Lab s₀ rows (θ₀, WithLp.toLp 2 ![R₀, z₀])‖ ≤ κ * t := by
  have closed : IsClosed ((fun p : ℝ × Plane => cylPoint (p.2 0) p.1 (p.2 1)) ''
      window s₀ rows b') :=
    ((isCompact_window ch hsec hb').image continuous_cylPoint).isClosed
  have sub : (fun p : ℝ × Plane => cylPoint (p.2 0) p.1 (p.2 1)) '' window s₀ rows b' ⊆
      regular := by
    rintro _ ⟨p, hp, rfl⟩
    exact in_regular (region_of_window ch hsec hb' hp) p.1
  have reg₀ : Region (WithLp.toLp 2 ![R₀, z₀] : Plane) :=
    region_of_outerD ch ((tube ch).subset hp₀.1 hp₀.2)
  have h0 : (z 0).1 ∈ regular := by
    rw [orbit.1, start]
    exact in_regular reg₀ θ₀
  have all := mem_closed_of_bootstrap (γ := fun t => (z t).1) hT
    (fun t ht => continuous_fst.continuousAt.comp (orbit.2 t ht).continuousAt) isOpen_regular
    closed sub h0 (fun t ht hΩ s hs => by
      obtain ⟨X, -, h⟩ := lift_stays ch hsec hbT hfield hm hq hμ start hp₀ orbit hκ hstart hball
        hvpar hvpar0 hwin hb' ht (fun τ hτ => ⟨(hΩ τ hτ).1, field_ne_zero (hΩ τ hτ)⟩)
      exact ⟨X s, (h s hs).2.1, (h s hs).1.symm⟩)
  obtain ⟨X, hX0, h⟩ := lift_stays ch hsec hbT hfield hm hq hμ start hp₀ orbit hκ hstart hball
    hvpar hvpar0 hwin hb' ⟨hT, le_rfl⟩
    (fun τ hτ => ⟨(sub (all τ hτ)).1, field_ne_zero (sub (all τ hτ))⟩)
  refine ⟨X, hX0, fun t ht => ?_⟩
  obtain ⟨hpt, hw, hlab⟩ := h t ht
  exact ⟨hpt, window_subset ch hsec hb' hw, hw.2, abs_le.mpr hw.1, hlab⟩

end Orbit

/-! ### Sanity -/

/-- The section check accepts the stationary record, whose reference lies on the midplane,
with a positive backward radius. -/
theorem sectionCheck_stationary : sectionCheck [stationary] [0, 1] = true := by
  with_unfolding_all rfl

/-- A backward radius equal to the outgoing radius is rejected. -/
theorem sectionCheck_reject : sectionCheck [stationary] [0, 0] = false := by
  with_unfolding_all rfl

/-- A list of radii without a second entry is rejected. -/
theorem sectionCheck_short : sectionCheck [stationary] [0] = false := by
  with_unfolding_all rfl

/-- **Consistency of the numerical side conditions for `T = 0`.** For an angle of birth inside
the window of the chain, the hypotheses of `stays_in_tube` on `κ`, `vpar` and `b'` can be met
together for `T = 0`; the hypothesis on the label then reads
`r + 2 |y₀| / 2⁸⁰ ≤ radius / 2⁸⁰`. This is a consistency check of the side conditions only: no
chain and no orbit is constructed. -/
theorem side_conditions_zero {C H m μ q g bT θ₀ b : ℝ} (hm : 0 < m) (hθ : |θ₀| < b) :
    ∃ κ vpar b' : ℝ, C * (1 + 9 / 25) * (8 / 7 * (2 * H / (|q| * bT ^ 2) * g)) ≤ κ ∧
      2 * (H - μ * bT) ≤ m * vpar ^ 2 ∧ 0 ≤ vpar ∧
      |θ₀| + (vpar / bT * ((13 / 10) / (7 / 8)) +
        8 / 7 * (2 * H / (|q| * bT ^ 2) * g)) * 0 ≤ b' ∧ b' < b ∧
      ∀ r : ℝ, r + κ * 0 = r := by
  refine ⟨_, Real.sqrt (|2 * (H - μ * bT)| / m), |θ₀|, le_rfl, ?_, Real.sqrt_nonneg _, by simp,
    hθ, fun r => by simp⟩
  rw [Real.sq_sqrt (by positivity), mul_div_cancel₀ _ hm.ne']
  exact le_abs_self _

end PlasmaLean.Design.DommaschkTubeDrift
