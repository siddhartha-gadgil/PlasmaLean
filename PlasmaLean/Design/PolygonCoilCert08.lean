/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCert02

/-!
# Polygonal-coil frontier certificate, part 8

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

/-- Certificate chunk 6 of face 2. -/
theorem cert_2_6 : checkChunk offs filsD face2 ((grid2.drop (4 * 6)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 12 of face 2. -/
theorem cert_2_12 : checkChunk offs filsD face2 ((grid2.drop (4 * 12)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 18 of face 2. -/
theorem cert_2_18 : checkChunk offs filsD face2 ((grid2.drop (4 * 18)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 24 of face 2. -/
theorem cert_2_24 : checkChunk offs filsD face2 ((grid2.drop (4 * 24)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 30 of face 2. -/
theorem cert_2_30 : checkChunk offs filsD face2 ((grid2.drop (4 * 30)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 36 of face 2. -/
theorem cert_2_36 : checkChunk offs filsD face2 ((grid2.drop (4 * 36)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 42 of face 2. -/
theorem cert_2_42 : checkChunk offs filsD face2 ((grid2.drop (4 * 42)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 48 of face 2. -/
theorem cert_2_48 : checkChunk offs filsD face2 ((grid2.drop (4 * 48)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 1 of face 3. -/
theorem cert_3_1 : checkChunk offs filsD face3 ((grid3.drop (4 * 1)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 7 of face 3. -/
theorem cert_3_7 : checkChunk offs filsD face3 ((grid3.drop (4 * 7)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 13 of face 3. -/
theorem cert_3_13 : checkChunk offs filsD face3 ((grid3.drop (4 * 13)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 19 of face 3. -/
theorem cert_3_19 : checkChunk offs filsD face3 ((grid3.drop (4 * 19)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 25 of face 3. -/
theorem cert_3_25 : checkChunk offs filsD face3 ((grid3.drop (4 * 25)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 31 of face 3. -/
theorem cert_3_31 : checkChunk offs filsD face3 ((grid3.drop (4 * 31)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 37 of face 3. -/
theorem cert_3_37 : checkChunk offs filsD face3 ((grid3.drop (4 * 37)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 43 of face 3. -/
theorem cert_3_43 : checkChunk offs filsD face3 ((grid3.drop (4 * 43)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 49 of face 3. -/
theorem cert_3_49 : checkChunk offs filsD face3 ((grid3.drop (4 * 49)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

end PlasmaLean.Design.PolygonCoil
