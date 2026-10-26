/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCert03

/-!
# Polygonal-coil frontier certificate, part 9

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

/-- Certificate chunk 7 of face 2. -/
theorem cert_2_7 : checkChunk offs filsD face2 ((grid2.drop (4 * 7)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 13 of face 2. -/
theorem cert_2_13 : checkChunk offs filsD face2 ((grid2.drop (4 * 13)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 19 of face 2. -/
theorem cert_2_19 : checkChunk offs filsD face2 ((grid2.drop (4 * 19)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 25 of face 2. -/
theorem cert_2_25 : checkChunk offs filsD face2 ((grid2.drop (4 * 25)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 31 of face 2. -/
theorem cert_2_31 : checkChunk offs filsD face2 ((grid2.drop (4 * 31)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 37 of face 2. -/
theorem cert_2_37 : checkChunk offs filsD face2 ((grid2.drop (4 * 37)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 43 of face 2. -/
theorem cert_2_43 : checkChunk offs filsD face2 ((grid2.drop (4 * 43)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 49 of face 2. -/
theorem cert_2_49 : checkChunk offs filsD face2 ((grid2.drop (4 * 49)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 2 of face 3. -/
theorem cert_3_2 : checkChunk offs filsD face3 ((grid3.drop (4 * 2)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 8 of face 3. -/
theorem cert_3_8 : checkChunk offs filsD face3 ((grid3.drop (4 * 8)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 14 of face 3. -/
theorem cert_3_14 : checkChunk offs filsD face3 ((grid3.drop (4 * 14)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 20 of face 3. -/
theorem cert_3_20 : checkChunk offs filsD face3 ((grid3.drop (4 * 20)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 26 of face 3. -/
theorem cert_3_26 : checkChunk offs filsD face3 ((grid3.drop (4 * 26)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 32 of face 3. -/
theorem cert_3_32 : checkChunk offs filsD face3 ((grid3.drop (4 * 32)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 38 of face 3. -/
theorem cert_3_38 : checkChunk offs filsD face3 ((grid3.drop (4 * 38)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 44 of face 3. -/
theorem cert_3_44 : checkChunk offs filsD face3 ((grid3.drop (4 * 44)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 50 of face 3. -/
theorem cert_3_50 : checkChunk offs filsD face3 ((grid3.drop (4 * 50)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

end PlasmaLean.Design.PolygonCoil
