/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCert05

/-!
# Polygonal-coil frontier certificate, part 11

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

/-- Certificate chunk 3 of face 2. -/
theorem cert_2_3 : checkChunk offs filsD face2 ((grid2.drop (4 * 3)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 9 of face 2. -/
theorem cert_2_9 : checkChunk offs filsD face2 ((grid2.drop (4 * 9)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 15 of face 2. -/
theorem cert_2_15 : checkChunk offs filsD face2 ((grid2.drop (4 * 15)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 21 of face 2. -/
theorem cert_2_21 : checkChunk offs filsD face2 ((grid2.drop (4 * 21)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 27 of face 2. -/
theorem cert_2_27 : checkChunk offs filsD face2 ((grid2.drop (4 * 27)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 33 of face 2. -/
theorem cert_2_33 : checkChunk offs filsD face2 ((grid2.drop (4 * 33)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 39 of face 2. -/
theorem cert_2_39 : checkChunk offs filsD face2 ((grid2.drop (4 * 39)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 45 of face 2. -/
theorem cert_2_45 : checkChunk offs filsD face2 ((grid2.drop (4 * 45)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 51 of face 2. -/
theorem cert_2_51 : checkChunk offs filsD face2 ((grid2.drop (4 * 51)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 5 of face 3. -/
theorem cert_3_5 : checkChunk offs filsD face3 ((grid3.drop (4 * 5)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 11 of face 3. -/
theorem cert_3_11 : checkChunk offs filsD face3 ((grid3.drop (4 * 11)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 17 of face 3. -/
theorem cert_3_17 : checkChunk offs filsD face3 ((grid3.drop (4 * 17)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 23 of face 3. -/
theorem cert_3_23 : checkChunk offs filsD face3 ((grid3.drop (4 * 23)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 29 of face 3. -/
theorem cert_3_29 : checkChunk offs filsD face3 ((grid3.drop (4 * 29)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 35 of face 3. -/
theorem cert_3_35 : checkChunk offs filsD face3 ((grid3.drop (4 * 35)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 41 of face 3. -/
theorem cert_3_41 : checkChunk offs filsD face3 ((grid3.drop (4 * 41)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 47 of face 3. -/
theorem cert_3_47 : checkChunk offs filsD face3 ((grid3.drop (4 * 47)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

end PlasmaLean.Design.PolygonCoil
