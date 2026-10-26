/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCert00

/-!
# Polygonal-coil frontier certificate, part 6

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

/-- Certificate chunk 5 of face 2. -/
theorem cert_2_5 : checkChunk offs filsD face2 ((grid2.drop (4 * 5)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 11 of face 2. -/
theorem cert_2_11 : checkChunk offs filsD face2 ((grid2.drop (4 * 11)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 17 of face 2. -/
theorem cert_2_17 : checkChunk offs filsD face2 ((grid2.drop (4 * 17)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 23 of face 2. -/
theorem cert_2_23 : checkChunk offs filsD face2 ((grid2.drop (4 * 23)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 29 of face 2. -/
theorem cert_2_29 : checkChunk offs filsD face2 ((grid2.drop (4 * 29)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 35 of face 2. -/
theorem cert_2_35 : checkChunk offs filsD face2 ((grid2.drop (4 * 35)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 41 of face 2. -/
theorem cert_2_41 : checkChunk offs filsD face2 ((grid2.drop (4 * 41)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 47 of face 2. -/
theorem cert_2_47 : checkChunk offs filsD face2 ((grid2.drop (4 * 47)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 0 of face 3. -/
theorem cert_3_0 : checkChunk offs filsD face3 ((grid3.drop (4 * 0)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 6 of face 3. -/
theorem cert_3_6 : checkChunk offs filsD face3 ((grid3.drop (4 * 6)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 12 of face 3. -/
theorem cert_3_12 : checkChunk offs filsD face3 ((grid3.drop (4 * 12)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 18 of face 3. -/
theorem cert_3_18 : checkChunk offs filsD face3 ((grid3.drop (4 * 18)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 24 of face 3. -/
theorem cert_3_24 : checkChunk offs filsD face3 ((grid3.drop (4 * 24)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 30 of face 3. -/
theorem cert_3_30 : checkChunk offs filsD face3 ((grid3.drop (4 * 30)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 36 of face 3. -/
theorem cert_3_36 : checkChunk offs filsD face3 ((grid3.drop (4 * 36)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 42 of face 3. -/
theorem cert_3_42 : checkChunk offs filsD face3 ((grid3.drop (4 * 42)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 48 of face 3. -/
theorem cert_3_48 : checkChunk offs filsD face3 ((grid3.drop (4 * 48)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

end PlasmaLean.Design.PolygonCoil
