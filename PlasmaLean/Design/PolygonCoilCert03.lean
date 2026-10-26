/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCert00

/-!
# Polygonal-coil frontier certificate, part 3

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

/-- Certificate chunk 3 of face 0. -/
theorem cert_0_3 : checkChunk offs filsD face0 ((grid0.drop (4 * 3)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 9 of face 0. -/
theorem cert_0_9 : checkChunk offs filsD face0 ((grid0.drop (4 * 9)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 15 of face 0. -/
theorem cert_0_15 : checkChunk offs filsD face0 ((grid0.drop (4 * 15)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 21 of face 0. -/
theorem cert_0_21 : checkChunk offs filsD face0 ((grid0.drop (4 * 21)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 27 of face 0. -/
theorem cert_0_27 : checkChunk offs filsD face0 ((grid0.drop (4 * 27)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 33 of face 0. -/
theorem cert_0_33 : checkChunk offs filsD face0 ((grid0.drop (4 * 33)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 39 of face 0. -/
theorem cert_0_39 : checkChunk offs filsD face0 ((grid0.drop (4 * 39)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 4 of face 1. -/
theorem cert_1_4 : checkChunk offs filsD face1 ((grid1.drop (4 * 4)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 10 of face 1. -/
theorem cert_1_10 : checkChunk offs filsD face1 ((grid1.drop (4 * 10)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 16 of face 1. -/
theorem cert_1_16 : checkChunk offs filsD face1 ((grid1.drop (4 * 16)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 22 of face 1. -/
theorem cert_1_22 : checkChunk offs filsD face1 ((grid1.drop (4 * 22)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 28 of face 1. -/
theorem cert_1_28 : checkChunk offs filsD face1 ((grid1.drop (4 * 28)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 34 of face 1. -/
theorem cert_1_34 : checkChunk offs filsD face1 ((grid1.drop (4 * 34)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 40 of face 1. -/
theorem cert_1_40 : checkChunk offs filsD face1 ((grid1.drop (4 * 40)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 46 of face 1. -/
theorem cert_1_46 : checkChunk offs filsD face1 ((grid1.drop (4 * 46)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 52 of face 1. -/
theorem cert_1_52 : checkChunk offs filsD face1 ((grid1.drop (4 * 52)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 1 of face 2. -/
theorem cert_2_1 : checkChunk offs filsD face2 ((grid2.drop (4 * 1)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

end PlasmaLean.Design.PolygonCoil
