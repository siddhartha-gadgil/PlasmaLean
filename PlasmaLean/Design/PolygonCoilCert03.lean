/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCert00

/-!
# Polygonal-coil frontier certificate, part 3

Kernel evaluations (`decide +kernel`) of the checker `checkChunk` of
`Design/PolygonCoilCheck` on chunks of 4 consecutive line pairs of the face grids of
`Design/PolygonCoilData` (chunk `i` of face `f` is `(gridF.drop (4 * i)).take 5`).
Each theorem certifies, through `Design/PolygonCoilSoundA`-`D`, the frontier error bound on the
corresponding cells. (Modules are chained pairwise only to bound the number of concurrent
kernel processes during a build.)
-/

@[expose] public section

namespace PlasmaLean.Design.PolygonCoil

/-- Certificate chunk 3 of face 0. -/
theorem cert_0_3 : checkChunk offs filsD face0 ((grid0.drop (4 * 3)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 9 of face 0. -/
theorem cert_0_9 : checkChunk offs filsD face0 ((grid0.drop (4 * 9)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 15 of face 0. -/
theorem cert_0_15 : checkChunk offs filsD face0 ((grid0.drop (4 * 15)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 21 of face 0. -/
theorem cert_0_21 : checkChunk offs filsD face0 ((grid0.drop (4 * 21)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 27 of face 0. -/
theorem cert_0_27 : checkChunk offs filsD face0 ((grid0.drop (4 * 27)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 33 of face 0. -/
theorem cert_0_33 : checkChunk offs filsD face0 ((grid0.drop (4 * 33)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 39 of face 0. -/
theorem cert_0_39 : checkChunk offs filsD face0 ((grid0.drop (4 * 39)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 4 of face 1. -/
theorem cert_1_4 : checkChunk offs filsD face1 ((grid1.drop (4 * 4)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 10 of face 1. -/
theorem cert_1_10 : checkChunk offs filsD face1 ((grid1.drop (4 * 10)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 16 of face 1. -/
theorem cert_1_16 : checkChunk offs filsD face1 ((grid1.drop (4 * 16)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 22 of face 1. -/
theorem cert_1_22 : checkChunk offs filsD face1 ((grid1.drop (4 * 22)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 28 of face 1. -/
theorem cert_1_28 : checkChunk offs filsD face1 ((grid1.drop (4 * 28)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 34 of face 1. -/
theorem cert_1_34 : checkChunk offs filsD face1 ((grid1.drop (4 * 34)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 40 of face 1. -/
theorem cert_1_40 : checkChunk offs filsD face1 ((grid1.drop (4 * 40)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 46 of face 1. -/
theorem cert_1_46 : checkChunk offs filsD face1 ((grid1.drop (4 * 46)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 52 of face 1. -/
theorem cert_1_52 : checkChunk offs filsD face1 ((grid1.drop (4 * 52)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 1 of face 2. -/
theorem cert_2_1 : checkChunk offs filsD face2 ((grid2.drop (4 * 1)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 7 of face 2. -/
theorem cert_2_7 : checkChunk offs filsD face2 ((grid2.drop (4 * 7)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 13 of face 2. -/
theorem cert_2_13 : checkChunk offs filsD face2 ((grid2.drop (4 * 13)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 19 of face 2. -/
theorem cert_2_19 : checkChunk offs filsD face2 ((grid2.drop (4 * 19)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 25 of face 2. -/
theorem cert_2_25 : checkChunk offs filsD face2 ((grid2.drop (4 * 25)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 31 of face 2. -/
theorem cert_2_31 : checkChunk offs filsD face2 ((grid2.drop (4 * 31)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 37 of face 2. -/
theorem cert_2_37 : checkChunk offs filsD face2 ((grid2.drop (4 * 37)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 43 of face 2. -/
theorem cert_2_43 : checkChunk offs filsD face2 ((grid2.drop (4 * 43)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 49 of face 2. -/
theorem cert_2_49 : checkChunk offs filsD face2 ((grid2.drop (4 * 49)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 2 of face 3. -/
theorem cert_3_2 : checkChunk offs filsD face3 ((grid3.drop (4 * 2)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 8 of face 3. -/
theorem cert_3_8 : checkChunk offs filsD face3 ((grid3.drop (4 * 8)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 14 of face 3. -/
theorem cert_3_14 : checkChunk offs filsD face3 ((grid3.drop (4 * 14)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 20 of face 3. -/
theorem cert_3_20 : checkChunk offs filsD face3 ((grid3.drop (4 * 20)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 26 of face 3. -/
theorem cert_3_26 : checkChunk offs filsD face3 ((grid3.drop (4 * 26)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 32 of face 3. -/
theorem cert_3_32 : checkChunk offs filsD face3 ((grid3.drop (4 * 32)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 38 of face 3. -/
theorem cert_3_38 : checkChunk offs filsD face3 ((grid3.drop (4 * 38)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 44 of face 3. -/
theorem cert_3_44 : checkChunk offs filsD face3 ((grid3.drop (4 * 44)).take 5) = true := by
  decide +kernel

/-- Certificate chunk 50 of face 3. -/
theorem cert_3_50 : checkChunk offs filsD face3 ((grid3.drop (4 * 50)).take 5) = true := by
  decide +kernel

end PlasmaLean.Design.PolygonCoil
