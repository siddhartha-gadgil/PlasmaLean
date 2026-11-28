"""Write the band-form (C2) instance module of the wide-tube library (N-216 stage 5).

    python3 scripts/qa2r_wide/assemble_band.py

The module needs both generated libraries: `QA2RWide` (tube, field bounds, orbit theorem) and
`QA2RGenerated` (`CommonLittlejohnCache`, regular mirror births at the original launch point).
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TEXT = r'''/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import WideTube.DommaschkWideTubeRows000Orbit
public import CommonLittlejohnCache.DommaschkCommonLittlejohn325
public import PlasmaLean.Design.DommaschkTubeBand

/-! # The band form of clause C2 for the QA2R vacuum field near the label-0.474 line

Hand-written. An instance of `Contract.BandContract` for the QA2R vacuum field, from the orbit
theorem of the two-sided tube around forward slabs 0–223 (`DommaschkWideTubeRows000Orbit`) and
the regular mirror births at the original launch point (`DommaschkRegularMirrorHeightBand325`,
`DommaschkCommonLittlejohnTime.from_path`).

* `kappa`, `Inputs`: the drift constant and the numerical conditions on the inputs of the
  specification (species, upper energy, horizon, a bound for the parallel speed).
* `goodBirths`, `support`, `spec`: the good births of the tube, the support (the interior of
  the trapped reference population of good births) and the specification.
* `band_contract`: the contract for every birth law that is absolutely continuous with finite
  positive mass on the support.
* `launch_near`, `seed_through_birth`, `exists_seed`: the original launch point at angle `0`
  is within `1/20000` of the initial point of the tube, and its lifts of every energy of the
  window, every height of the top mirror band and both signs lie in the support.
* `band_contract_restrict`: the contract for the volume of a unit ball as birth law.
* `inputs_example`, `band_contract_example`: the conditions hold for explicit numbers.

**What is and is not proved.** The support is an open set defined from the reference
population, so the covered fraction one holds by construction: every trapped reference birth
of the support is covered because the support consists of such births. The excursion `1/8` is
the size of the cross-section of the cylindrical envelope `Region` around the circle of radius
`15/16`, not a bound on the scale of the tube. The horizon is limited by `kappa q e₂ * T ≤
1/10000`. Lengths, field strength, mass, charge, energy and time are in the units of the model
field; no physical device is modelled. -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkWideTubeRows000Band

open Certificates PositionFrameSlabs PositionFrameTube Fields Set Contract MeasureTheory
open Contract.TrappedBirthCoordinates Kinetic.GCLittlejohn
open DommaschkTubeBand DommaschkWideTubeRows000Tube
open DommaschkSignedObservable DommaschkSignedBirthApproach
open DommaschkCommonLittlejohnTime DommaschkFirstMirrorLaunchSign
open DommaschkCartesianAngleFlow (B)

set_option linter.style.longLine false
set_option maxRecDepth 16384

/-- The drift constant of the label for upper energy `e₂` and charge `q`: the label constant
of the tube times `1 + 9/25` times the bound for the drift speed. -/
def kappa (q e₂ : ℝ) : ℝ :=
  DommaschkTubeDrift.labelConstant exponent inverseBound * (1 + 9 / 25) *
    (8 / 7 * (2 * e₂ / (|q| * (1039 / 1000) ^ 2) * (11 / 8)))

/-- **Conditions on the inputs of the specification**: mass `m`, charge `q`, upper energy
`e₂`, horizon `T` and a bound `vp` for the parallel speed. They are explicit inequalities
between the inputs, fixed before any proof. -/
structure Inputs (m q e₂ T vp : ℝ) : Prop where
  /-- positive mass -/
  mass_pos : 0 < m
  /-- nonzero charge -/
  charge_ne : q ≠ 0
  /-- positive horizon -/
  horizon_pos : 0 < T
  /-- the label drifts by at most `1/10000` up to the horizon -/
  drift : kappa q e₂ * T ≤ 1 / 10000
  /-- the bound for the parallel speed is nonnegative -/
  speed_nonneg : 0 ≤ vp
  /-- the bound dominates the parallel speed allowed by energy `e₂` and pitch above `9/10` -/
  speed : 2 * e₂ * (1 - 9 / 10 * (1039 / 1000)) ≤ m * vp ^ 2
  /-- the toroidal angle changes by at most `3` up to the horizon -/
  angle : (vp / (1039 / 1000) * ((13 / 10) / (7 / 8)) +
    8 / 7 * (2 * e₂ / (|q| * (1039 / 1000) ^ 2) * (11 / 8))) * T ≤ 3

/-- The good births of the tube: angle below `1/4`, label within `1/10000` of the initial point
of the tube, positive moment, energy in `(0, e₂)` and pitch above `9/10`. -/
def goodBirths (m e₂ : ℝ) : Set GCBirth :=
  good DommaschkWideTubeRows000.start rows beta m (1 / 10000) (1 / 4) e₂

/-- The support: the interior of the trapped reference population of good births with energy
in `(e₁, e₂)` and pitch above `9/10`. -/
def support (m e₁ e₂ : ℝ) : Set GCBirth :=
  DommaschkTubeBand.support DommaschkWideTubeRows000.start rows beta m (1 / 10000) (1 / 4) e₂
    (Ioo e₁ e₂) (Ioi (9 / 10))

/-- The support is the interior of the reference population of good births. -/
theorem support_eq (m e₁ e₂ : ℝ) : support m e₁ e₂ =
    interior (trappedReference B m (goodBirths m e₂) (Ioo e₁ e₂) (Ioi (9 / 10))) := rfl

/-- The support is open. -/
theorem isOpen_support (m e₁ e₂ : ℝ) : IsOpen (support m e₁ e₂) := isOpen_interior

/-- Every birth of the support is a trapped reference birth and a good birth. -/
theorem support_subset (m e₁ e₂ : ℝ) :
    support m e₁ e₂ ⊆ trappedReference B m (goodBirths m e₂) (Ioo e₁ e₂) (Ioi (9 / 10)) :=
  interior_subset

/-- **The specification.** Species `(m, q)`, birth law `ν`, the support above, energy window
`(e₁, e₂)`, pitch window `(9/10, ∞)`, the circle of radius `15/16` in the midplane as axis,
horizon `T`, excursion `1/8` and required fraction one. -/
def spec (m q : ℝ) (ν : Measure GCBirth) (e₁ e₂ T : ℝ) : BandSpec :=
  { m := m, q := q, ν := ν, support := support m e₁ e₂, energy := Ioo e₁ e₂,
    pitch := Ioi (9 / 10), axis := circle, horizon := T, excursion := 1 / 8, minFraction := 1 }

/-- **The band form of C2 for the QA2R vacuum field.** Under the conditions `Inputs` on the
species, the upper energy and the horizon, and for every birth law `ν` that is absolutely
continuous with finite positive mass on the support, the QA2R field meets the band contract
for the specification `spec`.

Caveats. The support is an open set defined from the trapped reference population, so the
covered fraction one holds by construction. The excursion `1/8` is the size of the
cross-section of the cylindrical envelope, not a bound on the scale of the tube. The horizon
is limited by `kappa q e₂ * T ≤ 1/10000`. Lengths and field are in the units of the model. -/
theorem band_contract {m q e₁ e₂ T vp : ℝ} (h : Inputs m q e₂ T vp) {ν : Measure GCBirth}
    (ac : ν ≪ volume) (fin : ν (support m e₁ e₂) ≠ ⊤) (pos : ν (support m e₁ e₂) ≠ 0) :
    BandContract (spec m q ν e₁ e₂ T) B := by
  have stop : (13 / 4 : ℝ) < DommaschkTubeDrift.stop rows := by
    rw [show DommaschkTubeDrift.stop rows = 224 / 64 from DommaschkWideTubeRows000Tube.stop]
    norm_num
  have hball : (1 / 10000 : ℝ) + kappa q e₂ * T +
      2 * |(DommaschkWideTubeRows000.start.point.y : ℝ)| / 2 ^ 80 ≤
      DommaschkWideTubeRows000.start.radius / 2 ^ 80 := by
    have y : (DommaschkWideTubeRows000.start.point.y : ℝ) = 5079 := by
      norm_num [DommaschkWideTubeRows000.start]
    have r : (DommaschkWideTubeRows000.start.radius : ℝ) = 278052938511364710182 := by
      norm_num [DommaschkWideTubeRows000.start]
    rw [y, r]
    have := h.drift
    norm_num
    linarith
  exact bandContract_support chain section_checked (by norm_num) (by norm_num)
    DommaschkWideTubeRows000Orbit.field_bounds h.mass_pos h.charge_ne (le_refl (kappa q e₂))
    hball h.speed h.speed_nonneg (b' := 13 / 4) (by linarith [h.angle]) stop h.horizon_pos
    ac fin pos

/-! ### The original launch point -/

/-- **The original launch point is close to the initial point of the tube.** The point at
angle `0` of a field line in the certified slabs of the original trace is within `1/20000` of
the initial point of the wide tube. -/
theorem launch_near {x : Plane} {y : ℝ → Plane}
    (path : Path 325 DommaschkPhysicalPrefix325.exitState DommaschkBackwardPrefix325.exitState
      DommaschkPhysicalPrefix325.rows DommaschkBackwardPrefix325.rows x y) :
    ‖y 0 - point DommaschkWideTubeRows000.start.point‖ < 1 / 20000 := by
  have cons : DommaschkPhysicalPrefix325.rows =
      DommaschkPhysicalFirstStep.row :: DommaschkPhysicalPrefix325.rows.tail := rfl
  have mem := path.forward
    (physicalSlab (DommaschkMirrorLaunch.MirrorEndpoint.start .q0r470)
      DommaschkPhysicalFirstStep.row 0)
    (by rw [cons, physicalSlabs]; exact List.mem_cons_self) 0
    (show (0 : ℝ) ∈ Icc 0 (0 + 1 / 64) from ⟨le_rfl, by norm_num⟩)
  have d : dist (y 0) (reference 0 DommaschkPhysicalFirstStep.row 0) ≤
      DommaschkPhysicalFirstStep.row.physicalOut / (2 : ℝ) ^ 80 := mem.2
  have fp : firstPoint DommaschkPhysicalFirstStep.row =
      ⟨1203469614412824074129409, 223481⟩ := by with_unfolding_all rfl
  have po : DommaschkPhysicalFirstStep.row.physicalOut = 1481700234749866732 := by
    with_unfolding_all rfl
  rw [reference_start, dist_eq_norm, fp, po] at d
  have diff : ‖point ⟨1203469614412824074129409, 223481⟩ -
      point DommaschkWideTubeRows000.start.point‖ ≤
      (50580606556345530534 + 218402) / (2 : ℝ) ^ 80 := by
    refine (norm_le_abs_add_abs _).trans (le_of_eq ?_)
    simp only [point, DommaschkWideTubeRows000.start, PiLp.sub_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    norm_num [abs_of_nonneg, abs_of_nonpos]
  have tri := norm_sub_le_norm_sub_add_norm_sub (y 0)
    (point ⟨1203469614412824074129409, 223481⟩) (point DommaschkWideTubeRows000.start.point)
  have num : ((1481700234749866732 : ℕ) : ℝ) / 2 ^ 80 +
      (50580606556345530534 + 218402) / (2 : ℝ) ^ 80 < 1 / 20000 := by norm_num
  linarith

/-- **The seeds lie in the support.** On the field line through the torus-interpolated birth
of the original construction, at angle `0`: the launch point is within `1/20000` of the initial
point of the tube, and its lifts of every energy `e ∈ (e₁, e₂)`, every mirror height of the top
band and both signs of the parallel velocity lie in the support. -/
theorem seed_through_birth : ThroughBirth (fun φ y => φ = 0 →
    ‖y 0 - point DommaschkWideTubeRows000.start.point‖ < 1 / 20000 ∧
    ∀ (m e₁ e₂ e h : ℝ) (neg : Bool), 0 < m → 0 < e₁ → e ∈ Ioo e₁ e₂ →
      h ∈ Icc (height false : ℝ) (height true) →
      lift B m (DommaschkFirstMirrorWell.point y 0) e h neg ∈ support m e₁ e₂) := by
  obtain ⟨uC, zC, uA, zA, r, z, tc, ta, ic, ia, nested, every⟩ :=
    DommaschkRegularMirrorHeightBand325.from_birth
  refine ⟨uC, zC, uA, zA, r, z, tc, ta, ic, ia, nested, fun φ small => ?_⟩
  obtain ⟨y, start, x, path, band⟩ := every φ small
  refine ⟨y, start, ?_⟩
  rintro rfl
  have region := DommaschkSignedTraceDomain.on_path path (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl
  have u : UniformAt (DommaschkFirstMirrorWell.point y 0) :=
    from_path path (by norm_num) region band.1 (by norm_num)
  have near := launch_near path
  refine ⟨near, ?_⟩
  intro m e₁ e₂ e h neg hm he₁ he hh
  have e0 : 0 < e := he₁.trans he.1
  have strict : ‖B (cylPoint (y 0 0) 0 (y 0 1))‖ < h :=
    DommaschkTrappedBirthCoordinates.strict_at_birth (φ := 0) band.1 (by norm_num) hh
  have h0 : 0 < h := (norm_nonneg _).trans_lt strict
  have top : h < 10 / 9 := by
    have : ((height true : ℚ) : ℝ) < 10 / 9 := by norm_num [height]
    linarith [hh.2]
  have zero : (0 : ℝ) ∈ Icc (-((325 : ℕ) : ℝ) / 64) ((325 : ℕ) / 64) := by
    constructor <;> norm_num
  have hR : 0 < y 0 0 := by linarith [(region 0 zero).1.1]
  have first : firstPoint (rowAt rows 0) = DommaschkWideTubeRows000.start.point := by
    with_unfolding_all rfl
  have seed : ∀ neg' : Bool,
      lift B m (cylPoint (y 0 0) 0 (y 0 1)) e h neg' ∈ goodBirths m e₂ := by
    intro neg'
    refine lift_mem_good chain hm (by norm_num) hR e0 he.2 top strict ?_ ?_ neg'
    · rw [toLp_coords, reference_start, first]
      have y1 : point DommaschkWideTubeRows000.start.point 1 = 5079 / (2 : ℝ) ^ 80 := by
        simp [point, DommaschkWideTubeRows000.start]
      have b1 : DommaschkTubeDrift.radius beta 1 = 362536891244355314226 / (2 : ℝ) ^ 80 := by
        simp [DommaschkTubeDrift.radius, beta]
      rw [y1, b1, abs_of_nonneg (by positivity)]
      have num : (1 / 20000 : ℝ) + 2 * (5079 / (2 : ℝ) ^ 80) <
          362536891244355314226 / (2 : ℝ) ^ 80 := by norm_num
      linarith
    · rw [toLp_coords]
      linarith
  obtain ⟨_, _, both⟩ := u m 1 e h 1 hm one_ne_zero e0 hh one_pos (fun _ => goodBirths m e₂)
    (Ioo e₁ e₂) (Ioi (9 / 10))
    (fun neg' => by
      have op : IsOpen (goodBirths m e₂) := isOpen_good chain m (1 / 10000) (1 / 4) e₂
      rw [op.interior_eq]
      exact seed neg')
    (by rw [isOpen_Ioo.interior_eq]; exact he)
    (by
      rw [isOpen_Ioi.interior_eq, mem_Ioi, lt_div_iff₀ h0]
      linarith)
  obtain ⟨W, op, mem, inside, -⟩ := both neg
  rw [support_eq]
  exact interior_maximal (fun b hb => (inside hb).1) op mem

/-- **A seed in cylindrical coordinates.** There is a point at angle `0`, within `1/20000` of
the initial point of the tube, whose lifts of every energy of the window, every mirror height
of the top band and both signs lie in the support. -/
theorem exists_seed : ∃ R z : ℝ,
    ‖(WithLp.toLp 2 ![R, z] : Plane) - point DommaschkWideTubeRows000.start.point‖ < 1 / 20000 ∧
    ∀ (m e₁ e₂ e h : ℝ) (neg : Bool), 0 < m → 0 < e₁ → e ∈ Ioo e₁ e₂ →
      h ∈ Icc (height false : ℝ) (height true) →
      lift B m (cylPoint R 0 z) e h neg ∈ support m e₁ e₂ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, every⟩ := seed_through_birth
  obtain ⟨y, -, h⟩ := every 0 (by norm_num)
  obtain ⟨near, seeds⟩ := h rfl
  exact ⟨y 0 0, y 0 1, by rw [toLp_coords]; exact near, seeds⟩

/-- The top mirror band is nonempty. -/
theorem height_mem : ((height true : ℚ) : ℝ) ∈ Icc (height false : ℝ) (height true) :=
  ⟨by norm_num [height], le_rfl⟩

/-- **The support is nonempty** when the energy window is. -/
theorem support_nonempty {m e₁ e₂ : ℝ} (hm : 0 < m) (he₁ : 0 < e₁) (he : e₁ < e₂) :
    (support m e₁ e₂).Nonempty := by
  obtain ⟨R, z, -, seeds⟩ := exists_seed
  exact ⟨_, seeds m e₁ e₂ ((e₁ + e₂) / 2) (height true) false hm he₁
    ⟨by linarith, by linarith⟩ height_mem⟩

/-- **The contract with a concrete birth law.** Under the conditions `Inputs` and for a
nonempty energy window `0 < e₁ < e₂`, there is a birth `p` of the support such that the QA2R
field meets the band contract with the volume of the unit ball around `p` as birth law. No
hypothesis on the birth law remains. The caveats of `band_contract` apply. -/
theorem band_contract_restrict {m q e₁ e₂ T vp : ℝ} (h : Inputs m q e₂ T vp) (he₁ : 0 < e₁)
    (he : e₁ < e₂) : ∃ p ∈ support m e₁ e₂,
      BandContract (spec m q (volume.restrict (Metric.ball p 1)) e₁ e₂ T) B := by
  obtain ⟨p, hp⟩ := support_nonempty h.mass_pos he₁ he
  refine ⟨p, hp, band_contract h
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self) ?_ ?_⟩
  · refine ((measure_mono (subset_univ _)).trans_lt ?_).ne
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  · rw [Measure.restrict_apply (isOpen_support m e₁ e₂).measurableSet]
    exact (((isOpen_support m e₁ e₂).inter Metric.isOpen_ball).measure_pos volume
      ⟨p, hp, Metric.mem_ball_self one_pos⟩).ne'

/-! ### The conditions are satisfiable -/

/-- **The conditions on the inputs hold for explicit numbers**: mass `1`, charge `1`, upper
energy `10⁻⁶`, horizon `10` and parallel speed bound `10⁻³`, in the units of the model. -/
theorem inputs_example : Inputs 1 1 (1 / 1000000) 10 (1 / 1000) := by
  have hexp : Real.exp (223 / 2000) ≤ 113 / 100 := by
    have h1 := Real.one_sub_le_exp_neg (223 / 2000)
    rw [Real.exp_neg] at h1
    have pos := Real.exp_pos (223 / 2000)
    have : Real.exp (223 / 2000) * (1 - 223 / 2000) ≤ 1 := by
      calc Real.exp (223 / 2000) * (1 - 223 / 2000)
          ≤ Real.exp (223 / 2000) * (Real.exp (223 / 2000))⁻¹ :=
            mul_le_mul_of_nonneg_left h1 pos.le
        _ = 1 := mul_inv_cancel₀ pos.ne'
    linarith
  refine ⟨one_pos, one_ne_zero, by norm_num, ?_, by norm_num, by norm_num, by norm_num⟩
  have cast : ((exponent : ℚ) : ℝ) = 223 / 2000 := by norm_num [exponent]
  have cast' : ((inverseBound : ℚ) : ℝ) = 1741 / 1000 := by norm_num [inverseBound]
  rw [kappa, DommaschkTubeDrift.labelConstant, cast, cast']
  norm_num
  linarith

/-- **The instance is not vacuous**: for mass `1`, charge `1`, energy window
`(5·10⁻⁷, 10⁻⁶)` and horizon `10` (units of the model), there is a birth `p` of the support
such that the QA2R field meets the band contract with the volume of the unit ball around `p`
as birth law. The caveats of `band_contract` apply. -/
theorem band_contract_example : ∃ p ∈ support 1 (1 / 2000000) (1 / 1000000),
    BandContract (spec 1 1 (volume.restrict (Metric.ball p 1)) (1 / 2000000) (1 / 1000000) 10)
      B :=
  band_contract_restrict inputs_example (by norm_num) (by norm_num)

end PlasmaLean.Design.DommaschkWideTubeRows000Band
'''

if __name__ == "__main__":
    path = ROOT / "generated/qa2r_wide/WideTube/DommaschkWideTubeRows000Band.lean"
    path.write_text(TEXT)
    print(path)
