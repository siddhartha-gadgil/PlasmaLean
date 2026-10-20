/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCert01

/-!
# Polygonal-coil frontier certificate, part 4

Kernel evaluations (`decide +kernel`) of the checker `checkChunk` of
`Design/PolygonCoilCheck` on chunks of 4 consecutive line pairs of the face grids of
`Design/PolygonCoilData` (chunk `i` of face `f` is `(gridF.drop (4 * i)).take 5`).
Each theorem certifies, through `Design/PolygonCoilSoundA`-`D`, the frontier error bound on the
corresponding cells. (Modules are chained pairwise only to bound the number of concurrent
kernel processes during a build.)
-/

@[expose] public section

namespace PlasmaLean.Design.PolygonCoil

/-- Certificate chunk 4 of face 0. -/
theorem cert_0_4 : checkChunk offs filsD face0 ((grid0.drop (4 * 4)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 10 of face 0. -/
theorem cert_0_10 : checkChunk offs filsD face0 ((grid0.drop (4 * 10)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 16 of face 0. -/
theorem cert_0_16 : checkChunk offs filsD face0 ((grid0.drop (4 * 16)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 22 of face 0. -/
theorem cert_0_22 : checkChunk offs filsD face0 ((grid0.drop (4 * 22)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 28 of face 0. -/
theorem cert_0_28 : checkChunk offs filsD face0 ((grid0.drop (4 * 28)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 34 of face 0. -/
theorem cert_0_34 : checkChunk offs filsD face0 ((grid0.drop (4 * 34)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 40 of face 0. -/
theorem cert_0_40 : checkChunk offs filsD face0 ((grid0.drop (4 * 40)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 5 of face 1. -/
theorem cert_1_5 : checkChunk offs filsD face1 ((grid1.drop (4 * 5)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 11 of face 1. -/
theorem cert_1_11 : checkChunk offs filsD face1 ((grid1.drop (4 * 11)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 17 of face 1. -/
theorem cert_1_17 : checkChunk offs filsD face1 ((grid1.drop (4 * 17)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 23 of face 1. -/
theorem cert_1_23 : checkChunk offs filsD face1 ((grid1.drop (4 * 23)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 29 of face 1. -/
theorem cert_1_29 : checkChunk offs filsD face1 ((grid1.drop (4 * 29)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 35 of face 1. -/
theorem cert_1_35 : checkChunk offs filsD face1 ((grid1.drop (4 * 35)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 41 of face 1. -/
theorem cert_1_41 : checkChunk offs filsD face1 ((grid1.drop (4 * 41)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 47 of face 1. -/
theorem cert_1_47 : checkChunk offs filsD face1 ((grid1.drop (4 * 47)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 53 of face 1. -/
theorem cert_1_53 : checkChunk offs filsD face1 ((grid1.drop (4 * 53)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 2 of face 2. -/
theorem cert_2_2 : checkChunk offs filsD face2 ((grid2.drop (4 * 2)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 8 of face 2. -/
theorem cert_2_8 : checkChunk offs filsD face2 ((grid2.drop (4 * 8)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 14 of face 2. -/
theorem cert_2_14 : checkChunk offs filsD face2 ((grid2.drop (4 * 14)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 20 of face 2. -/
theorem cert_2_20 : checkChunk offs filsD face2 ((grid2.drop (4 * 20)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 26 of face 2. -/
theorem cert_2_26 : checkChunk offs filsD face2 ((grid2.drop (4 * 26)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 32 of face 2. -/
theorem cert_2_32 : checkChunk offs filsD face2 ((grid2.drop (4 * 32)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 38 of face 2. -/
theorem cert_2_38 : checkChunk offs filsD face2 ((grid2.drop (4 * 38)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 44 of face 2. -/
theorem cert_2_44 : checkChunk offs filsD face2 ((grid2.drop (4 * 44)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 50 of face 2. -/
theorem cert_2_50 : checkChunk offs filsD face2 ((grid2.drop (4 * 50)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 3 of face 3. -/
theorem cert_3_3 : checkChunk offs filsD face3 ((grid3.drop (4 * 3)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 9 of face 3. -/
theorem cert_3_9 : checkChunk offs filsD face3 ((grid3.drop (4 * 9)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 15 of face 3. -/
theorem cert_3_15 : checkChunk offs filsD face3 ((grid3.drop (4 * 15)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 21 of face 3. -/
theorem cert_3_21 : checkChunk offs filsD face3 ((grid3.drop (4 * 21)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 27 of face 3. -/
theorem cert_3_27 : checkChunk offs filsD face3 ((grid3.drop (4 * 27)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 33 of face 3. -/
theorem cert_3_33 : checkChunk offs filsD face3 ((grid3.drop (4 * 33)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 39 of face 3. -/
theorem cert_3_39 : checkChunk offs filsD face3 ((grid3.drop (4 * 39)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 45 of face 3. -/
theorem cert_3_45 : checkChunk offs filsD face3 ((grid3.drop (4 * 45)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 51 of face 3. -/
theorem cert_3_51 : checkChunk offs filsD face3 ((grid3.drop (4 * 51)).take 5) = true := by
  decide +kernel

end PlasmaLean.Design.PolygonCoil
