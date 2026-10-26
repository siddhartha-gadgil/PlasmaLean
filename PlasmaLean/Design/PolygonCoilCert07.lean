/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCert01

/-!
# Polygonal-coil frontier certificate, part 7

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

/-- Certificate chunk 4 of face 2. -/
theorem cert_2_4 : checkChunk offs filsD face2 ((grid2.drop (4 * 4)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 10 of face 2. -/
theorem cert_2_10 : checkChunk offs filsD face2 ((grid2.drop (4 * 10)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 16 of face 2. -/
theorem cert_2_16 : checkChunk offs filsD face2 ((grid2.drop (4 * 16)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 22 of face 2. -/
theorem cert_2_22 : checkChunk offs filsD face2 ((grid2.drop (4 * 22)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 28 of face 2. -/
theorem cert_2_28 : checkChunk offs filsD face2 ((grid2.drop (4 * 28)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 34 of face 2. -/
theorem cert_2_34 : checkChunk offs filsD face2 ((grid2.drop (4 * 34)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 40 of face 2. -/
theorem cert_2_40 : checkChunk offs filsD face2 ((grid2.drop (4 * 40)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 46 of face 2. -/
theorem cert_2_46 : checkChunk offs filsD face2 ((grid2.drop (4 * 46)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 52 of face 2. -/
theorem cert_2_52 : checkChunk offs filsD face2 ((grid2.drop (4 * 52)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk2

/-- Certificate chunk 4 of face 3. -/
theorem cert_3_4 : checkChunk offs filsD face3 ((grid3.drop (4 * 4)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 10 of face 3. -/
theorem cert_3_10 : checkChunk offs filsD face3 ((grid3.drop (4 * 10)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 16 of face 3. -/
theorem cert_3_16 : checkChunk offs filsD face3 ((grid3.drop (4 * 16)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 22 of face 3. -/
theorem cert_3_22 : checkChunk offs filsD face3 ((grid3.drop (4 * 22)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 28 of face 3. -/
theorem cert_3_28 : checkChunk offs filsD face3 ((grid3.drop (4 * 28)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 34 of face 3. -/
theorem cert_3_34 : checkChunk offs filsD face3 ((grid3.drop (4 * 34)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 40 of face 3. -/
theorem cert_3_40 : checkChunk offs filsD face3 ((grid3.drop (4 * 40)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 46 of face 3. -/
theorem cert_3_46 : checkChunk offs filsD face3 ((grid3.drop (4 * 46)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

/-- Certificate chunk 52 of face 3. -/
theorem cert_3_52 : checkChunk offs filsD face3 ((grid3.drop (4 * 52)).take 5) = true := by
  chunk_cert filsDLB_eq faceChk3

end PlasmaLean.Design.PolygonCoil
