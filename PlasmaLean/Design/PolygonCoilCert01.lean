/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilDataL

/-!
# Polygonal-coil frontier certificate, part 1

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

/-- Certificate chunk 1 of face 0. -/
theorem cert_0_1 : checkChunk offs filsD face0 ((grid0.drop (4 * 1)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 7 of face 0. -/
theorem cert_0_7 : checkChunk offs filsD face0 ((grid0.drop (4 * 7)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 13 of face 0. -/
theorem cert_0_13 : checkChunk offs filsD face0 ((grid0.drop (4 * 13)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 19 of face 0. -/
theorem cert_0_19 : checkChunk offs filsD face0 ((grid0.drop (4 * 19)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 25 of face 0. -/
theorem cert_0_25 : checkChunk offs filsD face0 ((grid0.drop (4 * 25)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 31 of face 0. -/
theorem cert_0_31 : checkChunk offs filsD face0 ((grid0.drop (4 * 31)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 37 of face 0. -/
theorem cert_0_37 : checkChunk offs filsD face0 ((grid0.drop (4 * 37)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 2 of face 1. -/
theorem cert_1_2 : checkChunk offs filsD face1 ((grid1.drop (4 * 2)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 8 of face 1. -/
theorem cert_1_8 : checkChunk offs filsD face1 ((grid1.drop (4 * 8)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 14 of face 1. -/
theorem cert_1_14 : checkChunk offs filsD face1 ((grid1.drop (4 * 14)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 20 of face 1. -/
theorem cert_1_20 : checkChunk offs filsD face1 ((grid1.drop (4 * 20)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 26 of face 1. -/
theorem cert_1_26 : checkChunk offs filsD face1 ((grid1.drop (4 * 26)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 32 of face 1. -/
theorem cert_1_32 : checkChunk offs filsD face1 ((grid1.drop (4 * 32)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 38 of face 1. -/
theorem cert_1_38 : checkChunk offs filsD face1 ((grid1.drop (4 * 38)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 44 of face 1. -/
theorem cert_1_44 : checkChunk offs filsD face1 ((grid1.drop (4 * 44)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 50 of face 1. -/
theorem cert_1_50 : checkChunk offs filsD face1 ((grid1.drop (4 * 50)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 56 of face 1. -/
theorem cert_1_56 : checkChunk offs filsD face1 ((grid1.drop (4 * 56)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

end PlasmaLean.Design.PolygonCoil
