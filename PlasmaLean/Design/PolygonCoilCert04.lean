/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCert01

/-!
# Polygonal-coil frontier certificate, part 4

Explicit certificates (`chunk_cert`, `Design/PolygonCoilChunkCert`: one leaf per vertex step,
per block of three segment steps, per corner assembly and per cell) of the checker `checkChunk`
of `Design/PolygonCoilCheck` on chunks of 4 consecutive line pairs of the face grids of
`Design/PolygonCoilData` (chunk `i` of face `f` is `(gridF.drop (4 * i)).take 5`), with the
filament data read from the literal `filsDLB` (`filsDLB_eq`) and the face checks `faceChkF`.
Each theorem certifies, through `Design/PolygonCoilSoundA`-`D`, the frontier error bound on the
corresponding cells. (Modules are chained pairwise only to bound the number of concurrent
build processes.)
-/

@[expose] public section

namespace PlasmaLean.Design.PolygonCoil

/-- Certificate chunk 4 of face 0. -/
theorem cert_0_4 : checkChunk offs filsD face0 ((grid0.drop (4 * 4)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 10 of face 0. -/
theorem cert_0_10 : checkChunk offs filsD face0 ((grid0.drop (4 * 10)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 16 of face 0. -/
theorem cert_0_16 : checkChunk offs filsD face0 ((grid0.drop (4 * 16)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 22 of face 0. -/
theorem cert_0_22 : checkChunk offs filsD face0 ((grid0.drop (4 * 22)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 28 of face 0. -/
theorem cert_0_28 : checkChunk offs filsD face0 ((grid0.drop (4 * 28)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 34 of face 0. -/
theorem cert_0_34 : checkChunk offs filsD face0 ((grid0.drop (4 * 34)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 40 of face 0. -/
theorem cert_0_40 : checkChunk offs filsD face0 ((grid0.drop (4 * 40)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 5 of face 1. -/
theorem cert_1_5 : checkChunk offs filsD face1 ((grid1.drop (4 * 5)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 11 of face 1. -/
theorem cert_1_11 : checkChunk offs filsD face1 ((grid1.drop (4 * 11)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 17 of face 1. -/
theorem cert_1_17 : checkChunk offs filsD face1 ((grid1.drop (4 * 17)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 23 of face 1. -/
theorem cert_1_23 : checkChunk offs filsD face1 ((grid1.drop (4 * 23)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 29 of face 1. -/
theorem cert_1_29 : checkChunk offs filsD face1 ((grid1.drop (4 * 29)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 35 of face 1. -/
theorem cert_1_35 : checkChunk offs filsD face1 ((grid1.drop (4 * 35)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 41 of face 1. -/
theorem cert_1_41 : checkChunk offs filsD face1 ((grid1.drop (4 * 41)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 47 of face 1. -/
theorem cert_1_47 : checkChunk offs filsD face1 ((grid1.drop (4 * 47)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 53 of face 1. -/
theorem cert_1_53 : checkChunk offs filsD face1 ((grid1.drop (4 * 53)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 2 of face 2. -/
theorem cert_2_2 : checkChunk offs filsD face2 ((grid2.drop (4 * 2)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

end PlasmaLean.Design.PolygonCoil
