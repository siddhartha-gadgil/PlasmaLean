/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilDataL

/-!
# Polygonal-coil frontier certificate, part 0

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

/-- Certificate chunk 0 of face 0. -/
theorem cert_0_0 : checkChunk offs filsD face0 ((grid0.drop (4 * 0)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 6 of face 0. -/
theorem cert_0_6 : checkChunk offs filsD face0 ((grid0.drop (4 * 6)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 12 of face 0. -/
theorem cert_0_12 : checkChunk offs filsD face0 ((grid0.drop (4 * 12)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 18 of face 0. -/
theorem cert_0_18 : checkChunk offs filsD face0 ((grid0.drop (4 * 18)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 24 of face 0. -/
theorem cert_0_24 : checkChunk offs filsD face0 ((grid0.drop (4 * 24)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 30 of face 0. -/
theorem cert_0_30 : checkChunk offs filsD face0 ((grid0.drop (4 * 30)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 36 of face 0. -/
theorem cert_0_36 : checkChunk offs filsD face0 ((grid0.drop (4 * 36)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk0

/-- Certificate chunk 1 of face 1. -/
theorem cert_1_1 : checkChunk offs filsD face1 ((grid1.drop (4 * 1)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 7 of face 1. -/
theorem cert_1_7 : checkChunk offs filsD face1 ((grid1.drop (4 * 7)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 13 of face 1. -/
theorem cert_1_13 : checkChunk offs filsD face1 ((grid1.drop (4 * 13)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 19 of face 1. -/
theorem cert_1_19 : checkChunk offs filsD face1 ((grid1.drop (4 * 19)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 25 of face 1. -/
theorem cert_1_25 : checkChunk offs filsD face1 ((grid1.drop (4 * 25)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 31 of face 1. -/
theorem cert_1_31 : checkChunk offs filsD face1 ((grid1.drop (4 * 31)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 37 of face 1. -/
theorem cert_1_37 : checkChunk offs filsD face1 ((grid1.drop (4 * 37)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 43 of face 1. -/
theorem cert_1_43 : checkChunk offs filsD face1 ((grid1.drop (4 * 43)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 49 of face 1. -/
theorem cert_1_49 : checkChunk offs filsD face1 ((grid1.drop (4 * 49)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

/-- Certificate chunk 55 of face 1. -/
theorem cert_1_55 : checkChunk offs filsD face1 ((grid1.drop (4 * 55)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk1

end PlasmaLean.Design.PolygonCoil
