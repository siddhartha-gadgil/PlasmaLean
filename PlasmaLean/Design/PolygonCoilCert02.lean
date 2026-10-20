/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilData

/-!
# Polygonal-coil frontier certificate, part 2

Kernel evaluations (`decide +kernel`) of the checker `checkChunk` of
`Design/PolygonCoilCheck` on chunks of 4 consecutive line pairs of the face grids of
`Design/PolygonCoilData` (chunk `i` of face `f` is `(gridF.drop (4 * i)).take 5`).
Each theorem certifies, through `Design/PolygonCoilSoundA`-`D`, the frontier error bound on the
corresponding cells. (Modules are chained pairwise only to bound the number of concurrent
kernel processes during a build.)
-/

@[expose] public section

namespace PlasmaLean.Design.PolygonCoil

/-- Certificate chunk 2 of face 0. -/
theorem cert_0_2 : checkChunk offs filsD face0 ((grid0.drop (4 * 2)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 8 of face 0. -/
theorem cert_0_8 : checkChunk offs filsD face0 ((grid0.drop (4 * 8)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 14 of face 0. -/
theorem cert_0_14 : checkChunk offs filsD face0 ((grid0.drop (4 * 14)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 20 of face 0. -/
theorem cert_0_20 : checkChunk offs filsD face0 ((grid0.drop (4 * 20)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 26 of face 0. -/
theorem cert_0_26 : checkChunk offs filsD face0 ((grid0.drop (4 * 26)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 32 of face 0. -/
theorem cert_0_32 : checkChunk offs filsD face0 ((grid0.drop (4 * 32)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 38 of face 0. -/
theorem cert_0_38 : checkChunk offs filsD face0 ((grid0.drop (4 * 38)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 3 of face 1. -/
theorem cert_1_3 : checkChunk offs filsD face1 ((grid1.drop (4 * 3)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 9 of face 1. -/
theorem cert_1_9 : checkChunk offs filsD face1 ((grid1.drop (4 * 9)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 15 of face 1. -/
theorem cert_1_15 : checkChunk offs filsD face1 ((grid1.drop (4 * 15)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 21 of face 1. -/
theorem cert_1_21 : checkChunk offs filsD face1 ((grid1.drop (4 * 21)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 27 of face 1. -/
theorem cert_1_27 : checkChunk offs filsD face1 ((grid1.drop (4 * 27)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 33 of face 1. -/
theorem cert_1_33 : checkChunk offs filsD face1 ((grid1.drop (4 * 33)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 39 of face 1. -/
theorem cert_1_39 : checkChunk offs filsD face1 ((grid1.drop (4 * 39)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 45 of face 1. -/
theorem cert_1_45 : checkChunk offs filsD face1 ((grid1.drop (4 * 45)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 51 of face 1. -/
theorem cert_1_51 : checkChunk offs filsD face1 ((grid1.drop (4 * 51)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 0 of face 2. -/
theorem cert_2_0 : checkChunk offs filsD face2 ((grid2.drop (4 * 0)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 6 of face 2. -/
theorem cert_2_6 : checkChunk offs filsD face2 ((grid2.drop (4 * 6)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 12 of face 2. -/
theorem cert_2_12 : checkChunk offs filsD face2 ((grid2.drop (4 * 12)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 18 of face 2. -/
theorem cert_2_18 : checkChunk offs filsD face2 ((grid2.drop (4 * 18)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 24 of face 2. -/
theorem cert_2_24 : checkChunk offs filsD face2 ((grid2.drop (4 * 24)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 30 of face 2. -/
theorem cert_2_30 : checkChunk offs filsD face2 ((grid2.drop (4 * 30)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 36 of face 2. -/
theorem cert_2_36 : checkChunk offs filsD face2 ((grid2.drop (4 * 36)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 42 of face 2. -/
theorem cert_2_42 : checkChunk offs filsD face2 ((grid2.drop (4 * 42)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 48 of face 2. -/
theorem cert_2_48 : checkChunk offs filsD face2 ((grid2.drop (4 * 48)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 1 of face 3. -/
theorem cert_3_1 : checkChunk offs filsD face3 ((grid3.drop (4 * 1)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 7 of face 3. -/
theorem cert_3_7 : checkChunk offs filsD face3 ((grid3.drop (4 * 7)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 13 of face 3. -/
theorem cert_3_13 : checkChunk offs filsD face3 ((grid3.drop (4 * 13)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 19 of face 3. -/
theorem cert_3_19 : checkChunk offs filsD face3 ((grid3.drop (4 * 19)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 25 of face 3. -/
theorem cert_3_25 : checkChunk offs filsD face3 ((grid3.drop (4 * 25)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 31 of face 3. -/
theorem cert_3_31 : checkChunk offs filsD face3 ((grid3.drop (4 * 31)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 37 of face 3. -/
theorem cert_3_37 : checkChunk offs filsD face3 ((grid3.drop (4 * 37)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 43 of face 3. -/
theorem cert_3_43 : checkChunk offs filsD face3 ((grid3.drop (4 * 43)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 49 of face 3. -/
theorem cert_3_49 : checkChunk offs filsD face3 ((grid3.drop (4 * 49)).take 5) = true := by
  decide +kernel

end PlasmaLean.Design.PolygonCoil
