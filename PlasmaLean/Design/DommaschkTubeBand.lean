/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkTubeOrbit
public import PlasmaLean.Theory.Contract.BandSpec
public import PlasmaLean.Theory.Contract.TrappedBirthCoordinates

/-!
# The band form of clause C2 from the orbit theorem of a certified tube

Generic over the chain of position-frame slabs, with the field bounds on the outer tube as a
hypothesis, exactly as in `DommaschkTubeDrift.stays_in_tube` (gradient `g`, strength `bT`,
toroidal component `cφ`, speed `M`), and over the pitch floor `p₀`. The field is the QA2R vacuum
field `DommaschkCartesianAngleFlow.B`.

* `circle`: the circle of radius `15/16` in the midplane, as a closed curve of period one;
  `infDist_le`, `excursion_le`: every point over the cylindrical envelope `Region` is within
  `1/8` of it, so the distance to it changes by at most `1/8` between two such points.
* `chart`: the cylindrical chart `x ↦ (θ, (R, z))` on the half space `x₀ > 0`.
* `good`: the births over the inner tube of the chain with angle below `a`, label within `ρ`
  of the initial point of the chain, positive moment, energy in `(0, e₂)` and `μ/E > p₀`, for
  a pitch floor `p₀` with `p₀ · bT ≤ 1`; `isOpen_good`: this set is open.
* `conditions`: a good birth satisfies the side conditions of the orbit theorem, when three
  inequalities between the constants hold. With the pitch floor the energy factor of the drift
  is `2H - μ bT ≤ (2 - p₀ bT) e₂` and the parallel speed satisfies
  `m v_∥² ≤ 2 e₂ (1 - p₀ bT)`.
* `bandContract`: `Contract.BandContract` for any open set `W` of trapped reference births
  that are good, as support, and any birth law that is absolutely continuous with finite
  positive mass on `W`. Coverage fraction one holds because the support itself is contained in
  the reference population. The excursion `1/8` is the size of the cross-section of the
  envelope.
* `support`: the interior of the reference population of good births, a canonical choice of
  `W`; `bandContract_support`, `bandContract_restrict`.
* `mem_region_zero`, `lab_zero`, `lift_mem_good`: a birth at angle `0` near the initial point
  of the chain is good.
* `norm_le_abs_add_abs`, `toLp_coords`: two elementary facts about the plane used by the
  instances.

**Sanity.** `circle_zero` evaluates the axis, `chart_cylPoint` and `cylPoint_chart` show that
the chart inverts `cylPoint`, and `good_subset_pos` records that a good birth has positive
moment. No concrete chain is constructed here.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkTubeBand

open Certificates PositionFrameSlabs PositionFrameTube DommaschkJacobian DommaschkTubeCheck
open DommaschkTubeSymmetry DommaschkSignedTraceDomain DommaschkJacobianReflection Fields Set
open Contract Kinetic Kinetic.GCLittlejohn MeasureTheory
open DommaschkCartesianAngleFlow DommaschkCylindricalDrift DommaschkTubeDrift
open DommaschkKam (cylBphi)

/-! ### The reference circle and the excursion -/

/-- The circle of radius `15/16` in the midplane, with period one. -/
def circle (s : ℝ) : Space := cylPoint (15 / 16) (2 * Real.pi * s) 0

/-- Sanity: the circle starts on the positive first axis. -/
theorem circle_zero : circle 0 = WithLp.toLp 2 ![15 / 16, 0, 0] := by
  simp [circle, cylPoint]

/-- The circle is a smooth curve. -/
theorem contDiff_circle : ContDiff ℝ 1 circle := by
  refine contDiff_euclidean.mpr fun i => ?_
  fin_cases i
  · change ContDiff ℝ 1 fun s : ℝ => 15 / 16 * Real.cos (2 * Real.pi * s)
    fun_prop
  · change ContDiff ℝ 1 fun s : ℝ => 15 / 16 * Real.sin (2 * Real.pi * s)
    fun_prop
  · change ContDiff ℝ 1 fun _ : ℝ => (0 : ℝ)
    fun_prop

/-- The circle has period one. -/
theorem periodic_circle : Function.Periodic circle 1 := by
  intro s
  simp only [circle, cylPoint, mul_add, mul_one, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- Every point of the circle of radius `15/16` in the midplane is a value of `circle`. -/
theorem mem_range_circle (θ : ℝ) : cylPoint (15 / 16) θ 0 ∈ range circle :=
  ⟨θ / (2 * Real.pi), by
    rw [circle, mul_div_cancel₀ _ (by positivity)]⟩

/-- A point over the cylindrical envelope is within `1/8` of the point of the circle at the
same angle. -/
theorem dist_circle_le {p : Plane} (reg : Region p) (θ : ℝ) :
    dist (cylPoint (p 0) θ (p 1)) (cylPoint (15 / 16) θ 0) ≤ 1 / 8 := by
  obtain ⟨⟨lo, hi⟩, hz⟩ := reg
  obtain ⟨z1, z2⟩ := abs_le.mp hz
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_three, Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  simp only [cylPoint, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Real.dist_eq, sq_abs]
  have cs := Real.cos_sq_add_sin_sq θ
  have e : (p 0 * Real.cos θ - 15 / 16 * Real.cos θ) ^ 2 +
      (p 0 * Real.sin θ - 15 / 16 * Real.sin θ) ^ 2 + (p 1 - 0) ^ 2 =
      (p 0 - 15 / 16) ^ 2 + p 1 ^ 2 := by
    linear_combination (p 0 - 15 / 16) ^ 2 * cs
  rw [e]
  nlinarith

/-- The distance from a point over the cylindrical envelope to the circle is at most `1/8`. -/
theorem infDist_le {p : Plane} (reg : Region p) (θ : ℝ) :
    Metric.infDist (cylPoint (p 0) θ (p 1)) (range circle) ≤ 1 / 8 :=
  (Metric.infDist_le_dist_of_mem (mem_range_circle θ)).trans (dist_circle_le reg θ)

/-- **Excursion.** Between two points over the cylindrical envelope the distance to the circle
changes by at most `1/8`, the size of the cross-section of the envelope. -/
theorem excursion_le {p p' : Plane} (reg : Region p) (reg' : Region p') (θ θ' : ℝ) :
    |Metric.infDist (cylPoint (p 0) θ (p 1)) (range circle) -
      Metric.infDist (cylPoint (p' 0) θ' (p' 1)) (range circle)| ≤ 1 / 8 := by
  have h1 := infDist_le reg θ
  have h2 := infDist_le reg' θ'
  have n1 := Metric.infDist_nonneg (x := cylPoint (p 0) θ (p 1)) (s := range circle)
  have n2 := Metric.infDist_nonneg (x := cylPoint (p' 0) θ' (p' 1)) (s := range circle)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The Euclidean norm in the plane is at most the sum of the absolute values of the
coordinates. -/
theorem norm_le_abs_add_abs (v : Plane) : ‖v‖ ≤ |v 0| + |v 1| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  simp only [Real.norm_eq_abs, sq_abs]
  nlinarith [abs_nonneg (v 0), abs_nonneg (v 1), sq_abs (v 0), sq_abs (v 1)]

/-- A point of the plane is determined by its two coordinates. -/
theorem toLp_coords (v : Plane) : (WithLp.toLp 2 ![v 0, v 1] : Plane) = v := by
  ext i
  fin_cases i <;> rfl

/-! ### The cylindrical chart -/

/-- Cylindrical coordinates `(θ, (R, z))` of a point with positive first coordinate, with
`θ ∈ (-π/2, π/2)`. -/
def chart (x : Space) : ℝ × Plane :=
  (Real.arctan (x 1 / x 0), WithLp.toLp 2 ![Real.sqrt (x 0 ^ 2 + x 1 ^ 2), x 2])

/-- The chart inverts `cylPoint` on the half space of positive first coordinate. -/
theorem cylPoint_chart {x : Space} (hx : 0 < x 0) :
    cylPoint (Real.sqrt (x 0 ^ 2 + x 1 ^ 2)) (Real.arctan (x 1 / x 0)) (x 2) = x := by
  have hs : Real.sqrt (x 0 ^ 2 + x 1 ^ 2) = x 0 * Real.sqrt (1 + (x 1 / x 0) ^ 2) := by
    have e : x 0 ^ 2 + x 1 ^ 2 = x 0 ^ 2 * (1 + (x 1 / x 0) ^ 2) := by
      field_simp
    rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hx.le]
  have hpos : 0 < Real.sqrt (1 + (x 1 / x 0) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  ext i
  fin_cases i
  · simp only [cylPoint, Fin.zero_eta, PiLp.toLp_apply, Matrix.cons_val_zero]
    rw [hs, Real.cos_arctan]
    field_simp
  · simp only [cylPoint, Fin.mk_one, PiLp.toLp_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [hs, Real.sin_arctan]
    field_simp
  · simp [cylPoint]

/-- The chart of a point given in cylindrical coordinates at angle `0`. -/
theorem chart_cylPoint {R : ℝ} (hR : 0 < R) (z : ℝ) :
    chart (cylPoint R 0 z) = (0, WithLp.toLp 2 ![R, z]) := by
  simp [chart, cylPoint, Real.sqrt_sq hR.le]

/-- The chart is continuous on the half space of positive first coordinate. -/
theorem continuousAt_chart {x : Space} (hx : 0 < x 0) : ContinuousAt chart x := by
  have c0 : Continuous fun y : Space => y 0 := by fun_prop
  have c1 : Continuous fun y : Space => y 1 := by fun_prop
  have c2 : Continuous fun y : Space => y 2 := by fun_prop
  refine ContinuousAt.prodMk ?_ ?_
  · exact Real.continuous_arctan.continuousAt.comp (c1.continuousAt.div c0.continuousAt hx.ne')
  · refine (PiLp.continuous_toLp 2 _).continuousAt.comp (continuousAt_pi.mpr fun i => ?_)
    fin_cases i
    · exact (Real.continuous_sqrt.comp ((c0.pow 2).add (c1.pow 2))).continuousAt
    · exact c2.continuousAt

/-! ### Good births -/

/-- **Good births** for a chain: births with positive first coordinate whose cylindrical
coordinates lie over the two-sided inner tube of the chain at an angle of absolute value below
`a`, whose field-line label is within `ρ` of the initial point of the chain, with positive
magnetic moment, energy `E` in `(0, e₂)` and `p₀ · E < μ` (that is, pitch `μ/E > p₀`). -/
def good (s₀ : State) (rows : List Step) (bs : List ℕ) (m ρ a e₂ p₀ : ℝ) : Set GCBirth :=
  {b | 0 < b.1 0 ∧ |(chart b.1).1| < a ∧
    chart b.1 ∈ FlowLabel.region (2 * 0 - stop rows) (stop rows) (innerD s₀ rows bs) ∧
    ‖Lab s₀ rows (chart b.1) - point s₀.point‖ < ρ ∧ 0 < b.2.2 ∧
    0 < hamiltonian m b.2.2 B b.1 b.2.1 ∧ hamiltonian m b.2.2 B b.1 b.2.1 < e₂ ∧
    p₀ * hamiltonian m b.2.2 B b.1 b.2.1 < b.2.2}

/-- Sanity: a good birth has positive magnetic moment. -/
theorem good_subset_pos {s₀ : State} {rows : List Step} {bs : List ℕ} {m ρ a e₂ p₀ : ℝ} :
    good s₀ rows bs m ρ a e₂ p₀ ⊆ {b | 0 < b.2.2} := fun _ hb => hb.2.2.2.2.1

section ChainFacts

variable {s₀ e : State} {rows : List Step} {bs : List ℕ} {E Bq : ℚ}

/-- The label is Lipschitz on the region over the inner tube. -/
theorem lipschitzOnWith_lab (ch : Chain s₀ e rows bs E Bq) :
    LipschitzOnWith (Real.toNNReal (labelConstant E Bq * (1 + 9 / 25))) (Lab s₀ rows)
      (FlowLabel.region (2 * 0 - stop rows) (stop rows) (innerD s₀ rows bs)) := by
  have tb := tube ch
  have hC : 0 ≤ labelConstant E Bq := le_trans zero_le_one tb.one_le
  refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm]
  refine (FlowLabel.norm_label_sub_le tb hp hq).trans ?_
  have h2 : ‖p.2 - q.2‖ ≤ dist p q := by
    rw [← dist_eq_norm, Prod.dist_eq]
    exact le_max_right _ _
  have h1 : |p.1 - q.1| ≤ dist p q := by
    rw [← Real.dist_eq, Prod.dist_eq]
    exact le_max_left _ _
  have : ‖p.2 - q.2‖ + 9 / 25 * |p.1 - q.1| ≤ (1 + 9 / 25) * dist p q := by linarith
  calc labelConstant E Bq * (‖p.2 - q.2‖ + 9 / 25 * |p.1 - q.1|)
      ≤ labelConstant E Bq * ((1 + 9 / 25) * dist p q) := mul_le_mul_of_nonneg_left this hC
    _ = labelConstant E Bq * (1 + 9 / 25) * dist p q := by ring

/-- The position of a birth whose chart lies over the inner tube, in cylindrical coordinates
over the envelope. -/
theorem region_of_chart (ch : Chain s₀ e rows bs E Bq) {x : Space}
    (hp : chart x ∈ FlowLabel.region (2 * 0 - stop rows) (stop rows) (innerD s₀ rows bs)) :
    Region (chart x).2 :=
  region_of_outerD ch ((tube ch).subset hp.1 hp.2)

/-- **The good births form an open set.** -/
theorem isOpen_good (ch : Chain s₀ e rows bs E Bq) (m ρ a e₂ p₀ : ℝ) :
    IsOpen (good s₀ rows bs m ρ a e₂ p₀) := by
  refine isOpen_iff_mem_nhds.mpr fun b hb => ?_
  obtain ⟨hx, hθ, hp, hl, hμ, hE0, hE, hpitch⟩ := hb
  have cx : ContinuousAt (fun q : GCBirth => q.1) b := continuous_fst.continuousAt
  have cv : ContinuousAt (fun q : GCBirth => q.2.1) b :=
    (continuous_fst.comp continuous_snd).continuousAt
  have cm : ContinuousAt (fun q : GCBirth => q.2.2) b :=
    (continuous_snd.comp continuous_snd).continuousAt
  have c0 : ContinuousAt (fun q : GCBirth => q.1 0) b := by fun_prop
  have cc : ContinuousAt (fun q : GCBirth => chart q.1) b :=
    ContinuousAt.comp (f := fun q : GCBirth => q.1) (continuousAt_chart hx) cx
  have cθ : ContinuousAt (fun q : GCBirth => |(chart q.1).1|) b :=
    (continuous_abs.comp continuous_fst).continuousAt.comp cc
  have op := isOpen_region ch
  have cl : ContinuousAt (fun q : GCBirth => ‖Lab s₀ rows (chart q.1) - point s₀.point‖) b := by
    have cL : ContinuousAt (Lab s₀ rows) (chart b.1) :=
      (lipschitzOnWith_lab ch).continuousOn.continuousAt (op.mem_nhds hp)
    exact (ContinuousAt.comp (f := fun q : GCBirth => chart q.1) cL cc).sub
      continuousAt_const |>.norm
  have field : ContinuousAt (fun x : Space => ‖B x‖) b.1 := by
    have reg := in_regular (region_of_chart ch hp) (chart b.1).1
    have eq : cylPoint ((chart b.1).2 0) (chart b.1).1 ((chart b.1).2 1) = b.1 :=
      cylPoint_chart hx
    rw [eq] at reg
    exact (strength_smooth reg).continuousAt
  have ce : ContinuousAt (fun q : GCBirth => hamiltonian m q.2.2 B q.1 q.2.1) b := by
    change ContinuousAt (fun q : GCBirth => m * q.2.1 ^ 2 / 2 + q.2.2 * ‖B q.1‖) b
    exact ((continuousAt_const.mul (cv.pow 2)).div_const 2).add (cm.mul (field.comp cx))
  filter_upwards [c0.eventually_const_lt hx, cθ.eventually_lt_const hθ,
    cc (op.mem_nhds hp), cl.eventually_lt_const hl, cm.eventually_const_lt hμ,
    ce.eventually_const_lt hE0, ce.eventually_lt_const hE,
    ((continuousAt_const.mul ce).eventually_lt cm hpitch)] with q h1 h2 h3 h4 h5 h6 h7 h8
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-! ### Births at the section -/

/-- A point of the section close to the first reference point of the chain lies in the region
over the two-sided inner tube: its distance from the reference point, with twice the height of
the reference point, is below the backward radius of the first slab. -/
theorem mem_region_zero (ch : Chain s₀ e rows bs E Bq) {x : Plane}
    (near : ‖x - reference 0 (rowAt rows 0) 0‖ + 2 * |reference 0 (rowAt rows 0) 0 1| <
      radius bs 1) :
    ((0 : ℝ), x) ∈ FlowLabel.region (2 * 0 - stop rows) (stop rows) (innerD s₀ rows bs) := by
  have g0 : ∀ y : Plane, gauge s₀ 0 rows 0 (0, y) = ‖y - reference 0 (rowAt rows 0) 0‖ := by
    intro y
    change ‖(frameAt s₀ 0 rows 0 0).symm (y - reference (time 0 0) (rowAt rows 0) 0)‖ = _
    rw [frameAt_symm_start ch, time_zero]
  have nn : 0 ≤ 2 * |reference 0 (rowAt rows 0) 0 1| := by positivity
  have mem : ∀ y : Plane, ‖y - reference 0 (rowAt rows 0) 0‖ < radius bs 1 →
      y ∈ inner s₀ 0 rows (radius bs) 0 := by
    intro y hy
    refine ⟨0, ch.pos, ?_, ?_⟩
    · rw [time_succ, time_zero]
      exact ⟨le_rfl, by norm_num⟩
    · rw [g0]
      exact hy
  refine ⟨(tube ch).section_mem, ?_⟩
  change x ∈ innerD s₀ rows bs 0
  rw [innerD, FlowLabel.doubleV_self]
  refine ⟨mem x (by linarith), flipIso x, mem _ ?_, flipIso_involutive x⟩
  exact lt_of_le_of_lt (norm_flip_sub_le _ _) near

/-- **The label at the section.** A point of the region at angle `0` is its own label. -/
theorem lab_zero (ch : Chain s₀ e rows bs E Bq) {x : Plane}
    (hx : ((0 : ℝ), x) ∈ FlowLabel.region (2 * 0 - stop rows) (stop rows) (innerD s₀ rows bs)) :
    Lab s₀ rows (0, x) = x := by
  have tb := tube ch
  have h := FlowLabel.label_eq tb (p := ((0 : ℝ), x)) hx.1
    (v := fun s : ℝ => x + s • euclideanFlow 0 1 0 x) (by simp) (fun τ hτ => by
      rw [uIcc_self, mem_singleton_iff] at hτ
      subst hτ
      refine ⟨?_, ?_⟩
      · have d := ((hasDerivAt_id (0 : ℝ)).smul_const (euclideanFlow 0 1 0 x)).const_add x
        simpa using d.hasDerivWithinAt
      · simpa using tb.subset hx.1 hx.2)
  simpa using h

end ChainFacts

/-- **A birth at the section is good.** The lift of energy `e` and mirror height `h` at the
point with cylindrical coordinates `(R, 0, z)` is a good birth when `(R, z)` is close to the
first reference point of the chain and within `ρ` of its initial point, `e < e₂`, and the
field strength at the point is below `h` with `p₀ · h < 1`. -/
theorem lift_mem_good {s₀ e' : State} {rows : List Step} {bs : List ℕ} {E Bq : ℚ}
    (ch : Chain s₀ e' rows bs E Bq) {m ρ a e₂ p₀ R z e h : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hR : 0 < R) (he : 0 < e) (he₂ : e < e₂) (hh : p₀ * h < 1)
    (strict : ‖B (cylPoint R 0 z)‖ < h)
    (near : ‖(WithLp.toLp 2 ![R, z] : Plane) - reference 0 (rowAt rows 0) 0‖ +
      2 * |reference 0 (rowAt rows 0) 0 1| < radius bs 1)
    (lab : ‖(WithLp.toLp 2 ![R, z] : Plane) - point s₀.point‖ < ρ) (neg : Bool) :
    TrappedBirthCoordinates.lift B m (cylPoint R 0 z) e h neg ∈
      good s₀ rows bs m ρ a e₂ p₀ := by
  obtain ⟨atx, μpos, -, eq, -, -⟩ :=
    TrappedBirthCoordinates.lift_values (B := B) (x := cylPoint R 0 z) neg hm he strict
  have hreg := mem_region_zero ch near
  have hh0 : 0 < h := (norm_nonneg _).trans_lt strict
  have moment : (TrappedBirthCoordinates.lift B m (cylPoint R 0 z) e h neg).2.2 = e / h := rfl
  rw [TrappedBirthCoordinates.energy] at eq
  refine ⟨?_, ?_, ?_, ?_, μpos, ?_, ?_, ?_⟩
  · rw [atx]
    simpa [cylPoint] using hR
  · rw [atx, chart_cylPoint hR]
    simpa using ha
  · rw [atx, chart_cylPoint hR]
    exact hreg
  · rw [atx, chart_cylPoint hR, lab_zero ch hreg]
    exact lab
  · rw [eq]
    exact he
  · rw [eq]
    exact he₂
  · rw [eq, moment, lt_div_iff₀ hh0]
    nlinarith [mul_lt_mul_of_pos_left hh he]

/-! ### The orbit theorem for good births -/

section Band

variable {s₀ e : State} {rows : List Step} {bs : List ℕ} {E Bq : ℚ}
  {m q g bT cφ M p₀ κ ρ a e₂ vp b' T : ℝ}
  (ch : Chain s₀ e rows bs E Bq) (hsec : sectionCheck rows bs = true) (hbT : 0 < bT)
  (hbT' : p₀ * bT ≤ 1)
  (hfield : ∀ t ∈ Ioo (-stop rows) (stop rows), ∀ x ∈ outerD s₀ rows t,
    ‖gradAbsB B (cylPoint (x 0) t (x 1))‖ ≤ g ∧ bT ≤ ‖B (cylPoint (x 0) t (x 1))‖ ∧
      cylBphi (x 0) t (x 1) ≤ cφ ∧ ‖euclideanFlow 0 1 t x‖ ≤ M)
  (hm : 0 < m) (hq : q ≠ 0)
  (hκ : labelConstant E Bq * (1 + M) *
    (8 / 7 * ((2 - p₀ * bT) * e₂ / (|q| * bT ^ 2) * g)) ≤ κ)
  (hball : ρ + κ * T + 2 * |(s₀.point.y : ℝ)| / 2 ^ 80 ≤ s₀.radius / 2 ^ 80)
  (hvp : 2 * e₂ * (1 - p₀ * bT) ≤ m * vp ^ 2) (hvp0 : 0 ≤ vp)
  (hwin : a + (vp / bT * (cφ / (7 / 8)) +
    8 / 7 * ((2 - p₀ * bT) * e₂ / (|q| * bT ^ 2) * g)) * T ≤ b')
  (hb' : b' < stop rows)

include ch hbT hbT' hfield hm hq hκ hvp hwin in
/-- **A good birth satisfies the side conditions of the orbit theorem**, with the constants
`κ`, `ρ`, `vp`, `b'` fixed by the three inequalities `hκ`, `hvp`, `hwin` in terms of the upper
energy `e₂` and the pitch floor `p₀`. -/
theorem conditions (hT : 0 ≤ T) {b : GCBirth} (hb : b ∈ good s₀ rows bs m ρ a e₂ p₀) :
    0 ≤ b.2.2 ∧
    b.1 = cylPoint (Real.sqrt (b.1 0 ^ 2 + b.1 1 ^ 2)) (Real.arctan (b.1 1 / b.1 0)) (b.1 2) ∧
    ((Real.arctan (b.1 1 / b.1 0),
        WithLp.toLp 2 ![Real.sqrt (b.1 0 ^ 2 + b.1 1 ^ 2), b.1 2]) : ℝ × Plane) ∈
      FlowLabel.region (2 * 0 - stop rows) (stop rows) (innerD s₀ rows bs) ∧
    labelConstant E Bq * (1 + M) * (8 / 7 *
      ((2 * hamiltonian m b.2.2 B b.1 b.2.1 - b.2.2 * bT) / (|q| * bT ^ 2) * g)) ≤ κ ∧
    ‖Lab s₀ rows (Real.arctan (b.1 1 / b.1 0),
        WithLp.toLp 2 ![Real.sqrt (b.1 0 ^ 2 + b.1 1 ^ 2), b.1 2]) - point s₀.point‖ ≤ ρ ∧
    2 * (hamiltonian m b.2.2 B b.1 b.2.1 - b.2.2 * bT) ≤ m * vp ^ 2 ∧
    |Real.arctan (b.1 1 / b.1 0)| + (vp / bT * (cφ / (7 / 8)) + 8 / 7 *
      ((2 * hamiltonian m b.2.2 B b.1 b.2.1 - b.2.2 * bT) / (|q| * bT ^ 2) * g)) * T ≤ b' := by
  obtain ⟨hx, hθ, hp, hl, hμ, hE0, hE, hpitch⟩ := hb
  have tb := tube ch
  have hC : 0 ≤ labelConstant E Bq := le_trans zero_le_one tb.one_le
  obtain ⟨hg, -, hM, -⟩ :=
    constants_nonneg ch hbT hfield hm hq hμ.le (cylPoint_chart hx).symm hp
  have hqa : 0 < |q| := abs_pos.mpr hq
  set H := hamiltonian m b.2.2 B b.1 b.2.1 with hH
  have h1 : p₀ * H * bT ≤ b.2.2 * bT := mul_le_mul_of_nonneg_right hpitch.le hbT.le
  have num : 2 * H - b.2.2 * bT ≤ (2 - p₀ * bT) * e₂ := by
    have h2 : H * (2 - p₀ * bT) ≤ e₂ * (2 - p₀ * bT) :=
      mul_le_mul_of_nonneg_right hE.le (by linarith)
    nlinarith
  have drift : 8 / 7 * ((2 * H - b.2.2 * bT) / (|q| * bT ^ 2) * g) ≤
      8 / 7 * ((2 - p₀ * bT) * e₂ / (|q| * bT ^ 2) * g) := by
    gcongr
  refine ⟨hμ.le, (cylPoint_chart hx).symm, hp, ?_, hl.le, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left drift (mul_nonneg hC (by linarith))).trans hκ
  · have h2 : H * (1 - p₀ * bT) ≤ e₂ * (1 - p₀ * bT) :=
      mul_le_mul_of_nonneg_right hE.le (by linarith)
    nlinarith
  · have hθ' : |Real.arctan (b.1 1 / b.1 0)| ≤ a := hθ.le
    have := mul_le_mul_of_nonneg_right drift hT
    nlinarith

include ch hsec hbT hbT' hfield hm hq hκ hball hvp hvp0 hwin hb'

/-- **The band form of C2 on an open set of good trapped births.** Let `W` be an open set of
births of the trapped reference population (for the energy and pitch windows given) that are
good births of the chain, and `ν` a birth law that is absolutely continuous with finite
positive mass on `W`. Then the QA2R field meets the band contract with support `W`, the circle
of radius `15/16` as axis, horizon `T`, excursion `1/8` and fraction one.

Fraction one holds by construction, since the support `W` lies in the reference population.
The excursion `1/8` is the size of the cross-section of the cylindrical envelope, not of the
tube. The horizon is limited by `hball`. -/
theorem bandContract (hT : 0 < T) {W : Set GCBirth} {energies pitches : Set ℝ}
    (hW : IsOpen W)
    (sub : W ⊆ trappedReference B m (good s₀ rows bs m ρ a e₂ p₀) energies pitches)
    {ν : Measure GCBirth} (ac : ν ≪ volume) (fin : ν W ≠ ⊤) (pos : ν W ≠ 0) :
    BandContract
      { m := m, q := q, ν := ν, support := W, energy := energies, pitch := pitches,
        axis := circle, horizon := T, excursion := 1 / 8, minFraction := 1 } B := by
  have vac := DommaschkQA2R.field_vacuum DommaschkQA2R.candidate
  have ne : W.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    simp [hne] at pos
  have ref : trappedReference B m W energies pitches = W :=
    Subset.antisymm (fun _ hb => hb.1) (fun _ hb => ⟨hb, (sub hb).2⟩)
  have compact : IsCompact (range circle) :=
    periodic_circle.compact_of_continuous one_ne_zero contDiff_circle.continuous
  -- the conclusions of the orbit theorem for a birth of `W`
  have key : ∀ b ∈ W, (∃ z, GCBirthOrbitOn B m q b z T) ∧ (∃ p : Plane, ∃ θ : ℝ,
      Region p ∧ b.1 = cylPoint (p 0) θ (p 1)) ∧
      ∀ t ∈ Icc 0 T, ∀ z, GCBirthOrbitOn B m q b z t → ∃ p : Plane, ∃ θ : ℝ,
        Region p ∧ (z t).1 = cylPoint (p 0) θ (p 1) := by
    intro b hb
    have hgood := (sub hb).1
    obtain ⟨hμ, start, hp₀, hκ', hstart, hvpar, hwin'⟩ :=
      conditions ch hbT hbT' hfield hm hq hκ hvp hwin hT.le hgood
    refine ⟨DommaschkTubeOrbit.exists_orbit ch hsec hbT hfield hm hq hμ start hp₀ hT.le hκ'
      hstart hball hvpar hvp0 hwin' hb', ⟨_, _, region_of_chart ch hgood.2.2.1, start⟩, ?_⟩
    intro t ht z orbit
    obtain ⟨⟨p, hp, hpt⟩, -⟩ := DommaschkTubeOrbit.state_mem ch hsec hbT hfield hm hq hμ start
      hp₀ hκ' hstart hball hvpar hvp0 hwin' hb' ht orbit t (right_mem_Icc.mpr ht.1)
    exact ⟨p.2, p.1, region_of_window ch hsec hb' hp, hpt.symm⟩
  refine ⟨⟨hm, hq, hT, by norm_num, one_pos, le_rfl, ac, ?_, contDiff_circle,
    periodic_circle⟩, ?_⟩
  · exact ⟨_, by rw [hW.interior_eq]; exact ne.some_mem⟩
  refine ⟨CylAlgebra.domain, W, 1, vac.isOpen, vac.contDiffOn, vac.div_eq_zero, le_rfl, ?_, ?_⟩
  · refine ⟨hm, hq, range_nonempty _, compact, hT, by norm_num, ?_, fun b hb => (key b hb).1,
      ?_⟩
    · change BirthCoverage ν (trappedReference B m W energies pitches) W 1
      rw [ref]
      exact BirthCoverage.full hW.measurableSet fin (ENNReal.toReal_pos pos fin)
    · intro b hb t ht z orbit
      obtain ⟨-, ⟨p₀, θ₀, reg₀, start⟩, h⟩ := key b hb
      obtain ⟨p, θ, reg, hpt⟩ := h t ht z orbit
      have hreg := in_regular reg θ
      rw [← hpt] at hreg
      have nz := field_ne_zero hreg
      refine ⟨nz, ?_, ?_⟩
      · rw [VacuumLittlejohnLocal.vacuum_parallel vac ⟨hreg.1, nz⟩]
        exact norm_ne_zero_iff.mpr nz
      · change |Metric.infDist (z t).1 (range circle) - Metric.infDist b.1 (range circle)| ≤ _
        rw [hpt, start]
        exact excursion_le reg reg₀ θ θ₀
  · intro b hb t ht z orbit
    obtain ⟨p, θ, reg, hpt⟩ := (key b hb).2.2 t ht z orbit
    rw [hpt]
    exact (in_regular reg θ).1

/-- The interior of the trapped reference population of good births of a chain: the canonical
open support for `bandContract`. -/
def support (s₀ : State) (rows : List Step) (bs : List ℕ) (m ρ a e₂ p₀ : ℝ)
    (energies pitches : Set ℝ) : Set GCBirth :=
  interior (trappedReference B m (good s₀ rows bs m ρ a e₂ p₀) energies pitches)

omit ch hsec hbT hbT' hfield hm hq hκ hball hvp hvp0 hwin hb' in
/-- The support is open. -/
theorem isOpen_support (energies pitches : Set ℝ) :
    IsOpen (support s₀ rows bs m ρ a e₂ p₀ energies pitches) := isOpen_interior

/-- **The band form of C2 with the canonical support**: `bandContract` for the interior of the
reference population of good births. -/
theorem bandContract_support (hT : 0 < T) {energies pitches : Set ℝ} {ν : Measure GCBirth}
    (ac : ν ≪ volume) (fin : ν (support s₀ rows bs m ρ a e₂ p₀ energies pitches) ≠ ⊤)
    (pos : ν (support s₀ rows bs m ρ a e₂ p₀ energies pitches) ≠ 0) :
    BandContract
      { m := m, q := q, ν := ν, support := support s₀ rows bs m ρ a e₂ p₀ energies pitches,
        energy := energies, pitch := pitches, axis := circle, horizon := T, excursion := 1 / 8,
        minFraction := 1 } B :=
  bandContract ch hsec hbT hbT' hfield hm hq hκ hball hvp hvp0 hwin hb' hT isOpen_interior
    interior_subset ac fin pos

/-- **A concrete admissible birth law.** With the volume of the unit ball around a point of the
canonical support as birth law, the band contract holds without hypotheses on the law. -/
theorem bandContract_restrict (hT : 0 < T) {energies pitches : Set ℝ} {p : GCBirth}
    (hp : p ∈ support s₀ rows bs m ρ a e₂ p₀ energies pitches) :
    BandContract
      { m := m, q := q, ν := volume.restrict (Metric.ball p 1),
        support := support s₀ rows bs m ρ a e₂ p₀ energies pitches, energy := energies,
        pitch := pitches, axis := circle, horizon := T, excursion := 1 / 8,
        minFraction := 1 } B := by
  refine bandContract_support ch hsec hbT hbT' hfield hm hq hκ hball hvp hvp0 hwin hb' hT
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self) ?_ ?_
  · refine ((measure_mono (subset_univ _)).trans_lt ?_).ne
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  · rw [Measure.restrict_apply (isOpen_support energies pitches).measurableSet]
    exact (((isOpen_support energies pitches).inter Metric.isOpen_ball).measure_pos volume
      ⟨p, hp, Metric.mem_ball_self one_pos⟩).ne'

end Band

end PlasmaLean.Design.DommaschkTubeBand
