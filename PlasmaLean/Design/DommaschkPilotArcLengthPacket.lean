/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkPilotArcLength

/-! # Exact integrated radial floor on the first 316 paired pilot slabs -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkPilotArcLength
open Certificates.PositionFrameSlabs

set_option maxRecDepth 65536 in
theorem exact_sum :
    arcFloor DommaschkPositionFramesFwd.blocks.flatten
      DommaschkPositionFramesBack.blocks.flatten 316 =
      180067881457796589806937503 / 19342813113834066795298816 := by
  with_unfolding_all rfl

theorem packet :
    (9309 / 1000 : ℝ) ≤
      (arcFloor DommaschkPositionFramesFwd.blocks.flatten
        DommaschkPositionFramesBack.blocks.flatten 316 : ℝ) := by
  rw [exact_sum]
  norm_num

end PlasmaLean.Design.DommaschkPilotArcLength
