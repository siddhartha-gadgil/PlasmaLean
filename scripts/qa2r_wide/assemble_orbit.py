"""Write the orbit theorem module of the wide-tube library (N-216 stage 4).

    python3 scripts/qa2r_wide/assemble_orbit.py

The module instantiates `DommaschkTubeDrift.stays_in_tube` with the chain of
`DommaschkWideTubeRows000Tube` and the field bounds of `DommaschkWideTubeRows000Field`:
gradient of the field strength, field strength from below, toroidal component from above and
planar speed, all on the two-sided trial tube.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TEXT = r'''/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import WideTube.DommaschkWideTubeRows000Tube
public import WideTube.DommaschkWideTubeRows000Field
public import PlasmaLean.Design.DommaschkTubeOrbit

/-! # A QA2R guiding centre born in the tube around the label-0.474 line stays in it

Written by `scripts/qa2r_wide/assemble_orbit.py`. `DommaschkTubeDrift.stays_in_tube` for the
first 224 forward slabs and their mirror images, with the certified field bounds on the tube:
gradient of the field strength at most 11/8, field strength at least 1039/1000, toroidal
component at most 21/20 and speed of the planar field-line equation at most 7/50. The drift
constant is `labelConstant · (1 + 7/50) · (8/7) · (2H - μ · 1039/1000)/(|q| (1039/1000)²) · 11/8`
with `H` the energy at birth and `μ` the magnetic moment, and the angular rate is at most
`vpar/(1039/1000) · (21/20)/(7/8)` plus the drift. -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkWideTubeRows000Orbit

open Certificates PositionFrameSlabs PositionFrameTube DommaschkJacobian Fields Set Contract
open DommaschkTubeDrift DommaschkWideTubeRows000Tube Kinetic.GCLittlejohn
open DommaschkCartesianAngleFlow (B)

set_option linter.style.longLine false

/-- Certified field bounds on the two-sided trial tube. -/
theorem field_bounds : ∀ t ∈ Ioo (-stop rows) (stop rows),
    ∀ x ∈ outerD DommaschkWideTubeRows000.start rows t,
      ‖gradAbsB B (cylPoint (x 0) t (x 1))‖ ≤ (11 / 8 : ℝ) ∧
        (1039 / 1000 : ℝ) ≤ ‖B (cylPoint (x 0) t (x 1))‖ ∧
        DommaschkKam.cylBphi (x 0) t (x 1) ≤ (21 / 20 : ℝ) ∧
        ‖euclideanFlow 0 1 t x‖ ≤ (7 / 50 : ℝ) :=
  fun _ _ _ hx => ⟨DommaschkWideTubeRows000Field.gradAbsB_le hx,
    DommaschkWideTubeRows000Field.strength_ge hx,
    (DommaschkWideTubeRows000Field.toroidal_bounds hx).2,
    DommaschkWideTubeRows000Field.speed_le hx⟩

/-- **Orbit theorem.** A Littlejohn orbit of the QA2R field born at `cylPoint R₀ θ₀ z₀` over the
inner tube, whose field-line label is within `r` of the reference point, stays over the tube up
to time `T` and its label moves at most `κ t`, under the explicit side conditions on `κ`, `r`,
the parallel speed bound `vpar` and the angle window `b' < 224/64`. The constants are those of
the tube: speed bound `7/50`, toroidal component at most `21/20`, and the drift bound with the
energy factor `2H - μ · 1039/1000` (`H` the energy at birth, `μ` the magnetic moment). -/
theorem stays_in_tube {m q κ r vpar b' T θ₀ R₀ z₀ : ℝ} {bth : GCBirth} {z : ℝ → Space × ℝ}
    (hm : 0 < m) (hq : q ≠ 0) (hμ : 0 ≤ bth.2.2) (start : bth.1 = cylPoint R₀ θ₀ z₀)
    (hp₀ : ((θ₀, WithLp.toLp 2 ![R₀, z₀]) : ℝ × Plane) ∈
      FlowLabel.region (2 * 0 - stop rows) (stop rows)
        (innerD DommaschkWideTubeRows000.start rows beta))
    (orbit : GCBirthOrbitOn B m q bth z T) (hT : 0 ≤ T)
    (hκ : labelConstant exponent inverseBound * (1 + 7 / 50) *
      (8 / 7 * ((2 * hamiltonian m bth.2.2 B bth.1 bth.2.1 - bth.2.2 * (1039 / 1000)) /
        (|q| * (1039 / 1000) ^ 2) * (11 / 8))) ≤ κ)
    (hstart : ‖Lab DommaschkWideTubeRows000.start rows (θ₀, WithLp.toLp 2 ![R₀, z₀]) -
      point DommaschkWideTubeRows000.start.point‖ ≤ r)
    (hball : r + κ * T + 2 * |(DommaschkWideTubeRows000.start.point.y : ℝ)| / 2 ^ 80 ≤
      DommaschkWideTubeRows000.start.radius / 2 ^ 80)
    (hvpar : 2 * (hamiltonian m bth.2.2 B bth.1 bth.2.1 - bth.2.2 * (1039 / 1000)) ≤
      m * vpar ^ 2)
    (hvpar0 : 0 ≤ vpar)
    (hwin : |θ₀| + (vpar / (1039 / 1000) * ((21 / 20) / (7 / 8)) +
      8 / 7 * ((2 * hamiltonian m bth.2.2 B bth.1 bth.2.1 - bth.2.2 * (1039 / 1000)) /
        (|q| * (1039 / 1000) ^ 2) * (11 / 8))) * T ≤ b')
    (hb' : b' < stop rows) :
    ∃ X : ℝ → ℝ × Plane, X 0 = (θ₀, WithLp.toLp 2 ![R₀, z₀]) ∧ ∀ t ∈ Icc 0 T,
      (z t).1 = cylPoint ((X t).2 0) (X t).1 ((X t).2 1) ∧
      X t ∈ FlowLabel.region (2 * 0 - stop rows) (stop rows)
        (innerD DommaschkWideTubeRows000.start rows beta) ∧
      (X t).2 ∈ coreD DommaschkTubeSymmetry.flipIso DommaschkWideTubeRows000.start 0 rows (X t).1 ∧
      |(X t).1| ≤ b' ∧
      ‖Lab DommaschkWideTubeRows000.start rows (X t) -
        Lab DommaschkWideTubeRows000.start rows (θ₀, WithLp.toLp 2 ![R₀, z₀])‖ ≤ κ * t :=
  DommaschkTubeDrift.stays_in_tube chain section_checked (by norm_num) field_bounds hm hq hμ
    start hp₀ orbit hT hκ hstart hball hvpar hvpar0 hwin hb'

/-- **Existence.** Under the same side conditions the orbit exists on `[0, T]`, so the
statement is unconditional: the guiding centre born there has a Littlejohn orbit up to time
`T`, it stays over the tube, and its label moves at most `κ t`. -/
theorem exists_orbit_stays_in_tube {m q κ r vpar b' T θ₀ R₀ z₀ : ℝ} {bth : GCBirth}
    (hm : 0 < m) (hq : q ≠ 0) (hμ : 0 ≤ bth.2.2) (start : bth.1 = cylPoint R₀ θ₀ z₀)
    (hp₀ : ((θ₀, WithLp.toLp 2 ![R₀, z₀]) : ℝ × Plane) ∈
      FlowLabel.region (2 * 0 - stop rows) (stop rows)
        (innerD DommaschkWideTubeRows000.start rows beta))
    (hT : 0 ≤ T)
    (hκ : labelConstant exponent inverseBound * (1 + 7 / 50) *
      (8 / 7 * ((2 * hamiltonian m bth.2.2 B bth.1 bth.2.1 - bth.2.2 * (1039 / 1000)) /
        (|q| * (1039 / 1000) ^ 2) * (11 / 8))) ≤ κ)
    (hstart : ‖Lab DommaschkWideTubeRows000.start rows (θ₀, WithLp.toLp 2 ![R₀, z₀]) -
      point DommaschkWideTubeRows000.start.point‖ ≤ r)
    (hball : r + κ * T + 2 * |(DommaschkWideTubeRows000.start.point.y : ℝ)| / 2 ^ 80 ≤
      DommaschkWideTubeRows000.start.radius / 2 ^ 80)
    (hvpar : 2 * (hamiltonian m bth.2.2 B bth.1 bth.2.1 - bth.2.2 * (1039 / 1000)) ≤
      m * vpar ^ 2)
    (hvpar0 : 0 ≤ vpar)
    (hwin : |θ₀| + (vpar / (1039 / 1000) * ((21 / 20) / (7 / 8)) +
      8 / 7 * ((2 * hamiltonian m bth.2.2 B bth.1 bth.2.1 - bth.2.2 * (1039 / 1000)) /
        (|q| * (1039 / 1000) ^ 2) * (11 / 8))) * T ≤ b')
    (hb' : b' < stop rows) :
    ∃ (z : ℝ → Space × ℝ) (X : ℝ → ℝ × Plane), GCBirthOrbitOn B m q bth z T ∧
      X 0 = (θ₀, WithLp.toLp 2 ![R₀, z₀]) ∧ ∀ t ∈ Icc 0 T,
      (z t).1 = cylPoint ((X t).2 0) (X t).1 ((X t).2 1) ∧
      X t ∈ FlowLabel.region (2 * 0 - stop rows) (stop rows)
        (innerD DommaschkWideTubeRows000.start rows beta) ∧
      (X t).2 ∈ coreD DommaschkTubeSymmetry.flipIso DommaschkWideTubeRows000.start 0 rows (X t).1 ∧
      |(X t).1| ≤ b' ∧
      ‖Lab DommaschkWideTubeRows000.start rows (X t) -
        Lab DommaschkWideTubeRows000.start rows (θ₀, WithLp.toLp 2 ![R₀, z₀])‖ ≤ κ * t :=
  DommaschkTubeOrbit.exists_orbit_stays_in_tube chain section_checked (by norm_num) field_bounds
    hm hq hμ start hp₀ hT hκ hstart hball hvpar hvpar0 hwin hb'

end PlasmaLean.Design.DommaschkWideTubeRows000Orbit
'''

if __name__ == "__main__":
    path = ROOT / "generated/qa2r_wide/WideTube/DommaschkWideTubeRows000Orbit.lean"
    path.write_text(TEXT)
    print(path)
