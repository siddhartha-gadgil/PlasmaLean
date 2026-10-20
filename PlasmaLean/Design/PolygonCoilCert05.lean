/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCert02

/-!
# Polygonal-coil frontier certificate, part 5

Kernel evaluations (`decide +kernel`) of the checker `checkChunk` of
`Design/PolygonCoilCheck` on chunks of 4 consecutive line pairs of the face grids of
`Design/PolygonCoilData` (chunk `i` of face `f` is `(gridF.drop (4 * i)).take 5`).
Each theorem certifies, through `Design/PolygonCoilSoundA`-`D`, the frontier error bound on the
corresponding cells. (Modules are chained pairwise only to bound the number of concurrent
kernel processes during a build.)
-/

@[expose] public section

namespace PlasmaLean.Design.PolygonCoil

/-- Certificate chunk 5 of face 0. -/
theorem cert_0_5 : checkChunk offs filsD face0 ((grid0.drop (4 * 5)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 11 of face 0. -/
theorem cert_0_11 : checkChunk offs filsD face0 ((grid0.drop (4 * 11)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 17 of face 0. -/
theorem cert_0_17 : checkChunk offs filsD face0 ((grid0.drop (4 * 17)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 23 of face 0. -/
theorem cert_0_23 : checkChunk offs filsD face0 ((grid0.drop (4 * 23)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 29 of face 0. -/
theorem cert_0_29 : checkChunk offs filsD face0 ((grid0.drop (4 * 29)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 35 of face 0. -/
theorem cert_0_35 : checkChunk offs filsD face0 ((grid0.drop (4 * 35)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 41 of face 0. -/
theorem cert_0_41 : checkChunk offs filsD face0 ((grid0.drop (4 * 41)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 0 of face 1. -/
theorem cert_1_0 : checkChunk offs filsD face1 ((grid1.drop (4 * 0)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 6 of face 1. -/
theorem cert_1_6 : checkChunk offs filsD face1 ((grid1.drop (4 * 6)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 12 of face 1. -/
theorem cert_1_12 : checkChunk offs filsD face1 ((grid1.drop (4 * 12)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 18 of face 1. -/
theorem cert_1_18 : checkChunk offs filsD face1 ((grid1.drop (4 * 18)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 24 of face 1. -/
theorem cert_1_24 : checkChunk offs filsD face1 ((grid1.drop (4 * 24)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 30 of face 1. -/
theorem cert_1_30 : checkChunk offs filsD face1 ((grid1.drop (4 * 30)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 36 of face 1. -/
theorem cert_1_36 : checkChunk offs filsD face1 ((grid1.drop (4 * 36)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 42 of face 1. -/
theorem cert_1_42 : checkChunk offs filsD face1 ((grid1.drop (4 * 42)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 48 of face 1. -/
theorem cert_1_48 : checkChunk offs filsD face1 ((grid1.drop (4 * 48)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 54 of face 1. -/
theorem cert_1_54 : checkChunk offs filsD face1 ((grid1.drop (4 * 54)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 3 of face 2. -/
theorem cert_2_3 : checkChunk offs filsD face2 ((grid2.drop (4 * 3)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 9 of face 2. -/
theorem cert_2_9 : checkChunk offs filsD face2 ((grid2.drop (4 * 9)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 15 of face 2. -/
theorem cert_2_15 : checkChunk offs filsD face2 ((grid2.drop (4 * 15)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 21 of face 2. -/
theorem cert_2_21 : checkChunk offs filsD face2 ((grid2.drop (4 * 21)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 27 of face 2. -/
theorem cert_2_27 : checkChunk offs filsD face2 ((grid2.drop (4 * 27)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 33 of face 2. -/
theorem cert_2_33 : checkChunk offs filsD face2 ((grid2.drop (4 * 33)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 39 of face 2. -/
theorem cert_2_39 : checkChunk offs filsD face2 ((grid2.drop (4 * 39)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 45 of face 2. -/
theorem cert_2_45 : checkChunk offs filsD face2 ((grid2.drop (4 * 45)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 51 of face 2. -/
theorem cert_2_51 : checkChunk offs filsD face2 ((grid2.drop (4 * 51)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 5 of face 3. -/
theorem cert_3_5 : checkChunk offs filsD face3 ((grid3.drop (4 * 5)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 11 of face 3. -/
theorem cert_3_11 : checkChunk offs filsD face3 ((grid3.drop (4 * 11)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 17 of face 3. -/
theorem cert_3_17 : checkChunk offs filsD face3 ((grid3.drop (4 * 17)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 23 of face 3. -/
theorem cert_3_23 : checkChunk offs filsD face3 ((grid3.drop (4 * 23)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 29 of face 3. -/
theorem cert_3_29 : checkChunk offs filsD face3 ((grid3.drop (4 * 29)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 35 of face 3. -/
theorem cert_3_35 : checkChunk offs filsD face3 ((grid3.drop (4 * 35)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 41 of face 3. -/
theorem cert_3_41 : checkChunk offs filsD face3 ((grid3.drop (4 * 41)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 47 of face 3. -/
theorem cert_3_47 : checkChunk offs filsD face3 ((grid3.drop (4 * 47)).take 5) = true := by
  decide +kernel

end PlasmaLean.Design.PolygonCoil
