/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilData

/-!
# Polygonal-coil frontier certificate, part 0

Kernel evaluations (`decide +kernel`) of the checker `checkChunk` of
`Design/PolygonCoilCheck` on chunks of 4 consecutive line pairs of the face grids of
`Design/PolygonCoilData` (chunk `i` of face `f` is `(gridF.drop (4 * i)).take 5`).
Each theorem certifies, through `Design/PolygonCoilSoundA`-`D`, the frontier error bound on the
corresponding cells. (Modules are chained pairwise only to bound the number of concurrent
kernel processes during a build.)
-/

@[expose] public section

namespace PlasmaLean.Design.PolygonCoil

/-- Certificate chunk 0 of face 0. -/
theorem cert_0_0 : checkChunk offs filsD face0 ((grid0.drop (4 * 0)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 6 of face 0. -/
theorem cert_0_6 : checkChunk offs filsD face0 ((grid0.drop (4 * 6)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 12 of face 0. -/
theorem cert_0_12 : checkChunk offs filsD face0 ((grid0.drop (4 * 12)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 18 of face 0. -/
theorem cert_0_18 : checkChunk offs filsD face0 ((grid0.drop (4 * 18)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 24 of face 0. -/
theorem cert_0_24 : checkChunk offs filsD face0 ((grid0.drop (4 * 24)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 30 of face 0. -/
theorem cert_0_30 : checkChunk offs filsD face0 ((grid0.drop (4 * 30)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 36 of face 0. -/
theorem cert_0_36 : checkChunk offs filsD face0 ((grid0.drop (4 * 36)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 1 of face 1. -/
theorem cert_1_1 : checkChunk offs filsD face1 ((grid1.drop (4 * 1)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 7 of face 1. -/
theorem cert_1_7 : checkChunk offs filsD face1 ((grid1.drop (4 * 7)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 13 of face 1. -/
theorem cert_1_13 : checkChunk offs filsD face1 ((grid1.drop (4 * 13)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 19 of face 1. -/
theorem cert_1_19 : checkChunk offs filsD face1 ((grid1.drop (4 * 19)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 25 of face 1. -/
theorem cert_1_25 : checkChunk offs filsD face1 ((grid1.drop (4 * 25)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 31 of face 1. -/
theorem cert_1_31 : checkChunk offs filsD face1 ((grid1.drop (4 * 31)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 37 of face 1. -/
theorem cert_1_37 : checkChunk offs filsD face1 ((grid1.drop (4 * 37)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 43 of face 1. -/
theorem cert_1_43 : checkChunk offs filsD face1 ((grid1.drop (4 * 43)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 49 of face 1. -/
theorem cert_1_49 : checkChunk offs filsD face1 ((grid1.drop (4 * 49)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 55 of face 1. -/
theorem cert_1_55 : checkChunk offs filsD face1 ((grid1.drop (4 * 55)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 5 of face 2. -/
theorem cert_2_5 : checkChunk offs filsD face2 ((grid2.drop (4 * 5)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 11 of face 2. -/
theorem cert_2_11 : checkChunk offs filsD face2 ((grid2.drop (4 * 11)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 17 of face 2. -/
theorem cert_2_17 : checkChunk offs filsD face2 ((grid2.drop (4 * 17)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 23 of face 2. -/
theorem cert_2_23 : checkChunk offs filsD face2 ((grid2.drop (4 * 23)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 29 of face 2. -/
theorem cert_2_29 : checkChunk offs filsD face2 ((grid2.drop (4 * 29)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 35 of face 2. -/
theorem cert_2_35 : checkChunk offs filsD face2 ((grid2.drop (4 * 35)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 41 of face 2. -/
theorem cert_2_41 : checkChunk offs filsD face2 ((grid2.drop (4 * 41)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 47 of face 2. -/
theorem cert_2_47 : checkChunk offs filsD face2 ((grid2.drop (4 * 47)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 0 of face 3. -/
theorem cert_3_0 : checkChunk offs filsD face3 ((grid3.drop (4 * 0)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 6 of face 3. -/
theorem cert_3_6 : checkChunk offs filsD face3 ((grid3.drop (4 * 6)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 12 of face 3. -/
theorem cert_3_12 : checkChunk offs filsD face3 ((grid3.drop (4 * 12)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 18 of face 3. -/
theorem cert_3_18 : checkChunk offs filsD face3 ((grid3.drop (4 * 18)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 24 of face 3. -/
theorem cert_3_24 : checkChunk offs filsD face3 ((grid3.drop (4 * 24)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 30 of face 3. -/
theorem cert_3_30 : checkChunk offs filsD face3 ((grid3.drop (4 * 30)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 36 of face 3. -/
theorem cert_3_36 : checkChunk offs filsD face3 ((grid3.drop (4 * 36)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 42 of face 3. -/
theorem cert_3_42 : checkChunk offs filsD face3 ((grid3.drop (4 * 42)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 48 of face 3. -/
theorem cert_3_48 : checkChunk offs filsD face3 ((grid3.drop (4 * 48)).take 5) = true := by
  decide +kernel

end PlasmaLean.Design.PolygonCoil
