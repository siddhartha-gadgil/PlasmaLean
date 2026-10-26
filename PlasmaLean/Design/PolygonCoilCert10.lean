/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCert04

/-!
# Polygonal-coil frontier certificate, part 10

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

/-- Certificate chunk 8 of face 2. -/
theorem cert_2_8 : checkChunk offs filsD face2 ((grid2.drop (4 * 8)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 14 of face 2. -/
theorem cert_2_14 : checkChunk offs filsD face2 ((grid2.drop (4 * 14)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 20 of face 2. -/
theorem cert_2_20 : checkChunk offs filsD face2 ((grid2.drop (4 * 20)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 26 of face 2. -/
theorem cert_2_26 : checkChunk offs filsD face2 ((grid2.drop (4 * 26)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 32 of face 2. -/
theorem cert_2_32 : checkChunk offs filsD face2 ((grid2.drop (4 * 32)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 38 of face 2. -/
theorem cert_2_38 : checkChunk offs filsD face2 ((grid2.drop (4 * 38)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 44 of face 2. -/
theorem cert_2_44 : checkChunk offs filsD face2 ((grid2.drop (4 * 44)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 50 of face 2. -/
theorem cert_2_50 : checkChunk offs filsD face2 ((grid2.drop (4 * 50)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 3 of face 3. -/
theorem cert_3_3 : checkChunk offs filsD face3 ((grid3.drop (4 * 3)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 9 of face 3. -/
theorem cert_3_9 : checkChunk offs filsD face3 ((grid3.drop (4 * 9)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 15 of face 3. -/
theorem cert_3_15 : checkChunk offs filsD face3 ((grid3.drop (4 * 15)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 21 of face 3. -/
theorem cert_3_21 : checkChunk offs filsD face3 ((grid3.drop (4 * 21)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 27 of face 3. -/
theorem cert_3_27 : checkChunk offs filsD face3 ((grid3.drop (4 * 27)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 33 of face 3. -/
theorem cert_3_33 : checkChunk offs filsD face3 ((grid3.drop (4 * 33)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 39 of face 3. -/
theorem cert_3_39 : checkChunk offs filsD face3 ((grid3.drop (4 * 39)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 45 of face 3. -/
theorem cert_3_45 : checkChunk offs filsD face3 ((grid3.drop (4 * 45)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 51 of face 3. -/
theorem cert_3_51 : checkChunk offs filsD face3 ((grid3.drop (4 * 51)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

end PlasmaLean.Design.PolygonCoil
