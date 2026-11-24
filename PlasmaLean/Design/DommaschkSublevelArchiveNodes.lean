/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.MirrorSublevelQuadrature
public import PlasmaLean.Design.DommaschkActionQ0R470
public import PlasmaLean.Design.DommaschkActionQ0R478
public import PlasmaLean.Design.DommaschkSublevelActionGrids

/-! # Closed-threshold arclengths from two complete Dommaschk archives

The upper node samples the left endpoint of adaptive cell 71. The lower
node samples the right endpoint of cell 63. Each cutoff equals the speed
witness of some original time panels, so strict and weak selection differ.
-/

@[expose] public section
namespace PlasmaLean.Design.DommaschkSublevelArchiveNodes
open MeasureTheory Set Certificates.MirrorActionQuadrature Certificates.MirrorSublevelQuadrature
open Kinetic.MirrorSublevelAction

set_option maxRecDepth 16384

namespace Upper
open DommaschkSublevelActionGrids.Q0R470

/-- Density of every archived time cell reaching the upper node threshold. -/
theorem tail_at_node : packetTail 78848 DommaschkActionQ0R470.slabs = 28064234084 := by rfl

/-- The tie at the node contributes 1,865,338 density ticks. -/
theorem tail_above_node : packetTail 78849 DommaschkActionQ0R470.slabs = 28062368746 := by rfl

/-- This particular upper node hypothesis follows from the original physical packet cover. -/
theorem node {f w : ℝ → ℝ} (c : Covers true w f mirrorHeight (-(325 : ℝ) / 64)
      DommaschkActionQ0R470.slabs) (hf : Measurable f) (hw : Measurable w)
    (hn : ∀ t ∈ Icc (-(325 : ℝ) / 64) (325 / 64), 0 ≤ w t)
    (hi : IntegrableOn w (Ioc (-(325 : ℝ) / 64) (325 / 64))) :
    sublevelLength ((volume.restrict (Ioc (-(325 : ℝ) / 64) (325 / 64))).withDensity
      (fun t => ENNReal.ofReal (w t))) f
      (mirrorHeight - (Certificates.SublevelActionGrid.speed table 1048576 71)^2 / 2) ≤
      Certificates.SublevelActionGrid.height table 3221225472 71 := by
  have endpt : -(325 : ℝ) / 64 + DommaschkActionQ0R470.slabs.length / 64 = 325 / 64 := by
    rw [DommaschkActionQ0R470.checked.len]
    norm_num
  have h := covers_sublevel (v := 78848) (Or.inl rfl) endpt c hf hw hn hi
  rw [tail_at_node] at h
  rw [Certificates.SublevelActionGrid.speed, Certificates.SublevelActionGrid.height,
    show Certificates.SublevelActionGrid.tick table 71 = 78848 by rfl,
    show (Certificates.SublevelActionGrid.cell table 71).height = 28064234084 by rfl]
  norm_num [Certificates.MirrorActionQuadrature.Directed] at h ⊢
  exact h

end Upper

namespace Lower
open DommaschkSublevelActionGrids.Q0R478

/-- Density of every archived time cell reaching the lower node threshold. -/
theorem tail_at_node : packetTail 63488 DommaschkActionQ0R478.slabs = 29173279094 := by rfl

/-- The tie at the node contributes 1,863,002 density ticks. -/
theorem tail_above_node : packetTail 63489 DommaschkActionQ0R478.slabs = 29171416092 := by rfl

/-- This particular lower node hypothesis follows from the original physical packet cover. -/
theorem node {f w : ℝ → ℝ} (c : Covers false w f mirrorHeight (-(327 : ℝ) / 64)
      DommaschkActionQ0R478.slabs) (hf : Measurable f) (hw : Measurable w)
    (hn : ∀ t ∈ Icc (-(327 : ℝ) / 64) (327 / 64), 0 ≤ w t)
    (hi : IntegrableOn w (Ioc (-(327 : ℝ) / 64) (327 / 64))) :
    Certificates.SublevelActionGrid.height table 3221225472 63 ≤
    sublevelLength ((volume.restrict (Ioc (-(327 : ℝ) / 64) (327 / 64))).withDensity
      (fun t => ENNReal.ofReal (w t))) f
      (mirrorHeight - (Certificates.SublevelActionGrid.speed table 1048576 (63 + 1))^2 / 2) := by
  have endpt : -(327 : ℝ) / 64 + DommaschkActionQ0R478.slabs.length / 64 = 327 / 64 := by
    rw [DommaschkActionQ0R478.checked.len]
    norm_num
  have h := covers_sublevel (v := 63488) (Or.inr (by norm_num)) endpt c hf hw hn hi
  rw [tail_at_node] at h
  rw [Certificates.SublevelActionGrid.speed, Certificates.SublevelActionGrid.height,
    show Certificates.SublevelActionGrid.tick table (63 + 1) = 63488 by rfl,
    show (Certificates.SublevelActionGrid.cell table 63).height = 29173279094 by rfl]
  norm_num [Certificates.MirrorActionQuadrature.Directed] at h ⊢
  exact h

end Lower
end PlasmaLean.Design.DommaschkSublevelArchiveNodes
