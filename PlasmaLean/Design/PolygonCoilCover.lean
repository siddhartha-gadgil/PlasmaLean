/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCert06
public import PlasmaLean.Design.PolygonCoilCert07
public import PlasmaLean.Design.PolygonCoilCert08
public import PlasmaLean.Design.PolygonCoilCert09
public import PlasmaLean.Design.PolygonCoilCert10
public import PlasmaLean.Design.PolygonCoilCert11
public import PlasmaLean.Design.PolygonCoilSoundD
public import PlasmaLean.Certificates.KernelFact
public import PlasmaLean.Certificates.BoolCert

/-!
# The certified frontier bound on the four faces of the fundamental frontier piece

Assembles the kernel certificates `cert_F_i` (`Design/PolygonCoilCert00`–`11`) through the
soundness theorem `grid_cover` (`Design/PolygonCoilSoundD`):

* `filsValid`: the integer coil data passes `filOK` (checked once by `kernel_fact`);
* `faceOK0`–`faceOK3`: the face data carries the proved `hel` constants;
* `cover0`–`cover3`: on each face `F`, for `φ ∈ [φ_1696, φ_9889] ⊇ [π/4, 3π/4]` and every `w` in
  the face range, `‖Bseg fils - hel‖ ≤ etaFp·2⁻⁴⁰` and the distance to every coil segment is
  `≥ 1/5` (`FaceGood`).
-/

public section
noncomputable section

namespace PlasmaLean.Design.PolygonCoil

open PlasmaLean.Certificates.BoolCert
open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator
    PlasmaLean.Design.RationalStellarator.Coils
  Set Real

/-- The integer coil data is valid (one kernel evaluation). -/
theorem dataOK_eq : dataOK = true := by bool_cert

/-- Every filament is nonempty and there are at most `nSeg` segments. -/
theorem fils_shape : (fils.all fun f => !f.2.isEmpty) = true ∧ (allSegs fils).length ≤ nSeg := by
  constructor
  · kernel_fact
  · kernel_fact

/-- **Validity of the coil data.** -/
theorem filsValid : FilsValid offs fils := by
  refine ⟨fun f hf => ?_, fun f hf => ?_, fils_shape.2⟩
  · have := List.all_eq_true.mp fils_shape.1 f hf
    simpa using this
  · exact List.all_eq_true.mp dataOK_eq f hf

/-- Face 0 carries the proved `hel` constants. -/
theorem faceOK0 : FaceOK face0 := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> simp only [face0, helPhiC, helWC] <;> norm_num

/-- Face 1 carries the proved `hel` constants. -/
theorem faceOK1 : FaceOK face1 := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> simp only [face1, helPhiC, helWC] <;> norm_num

/-- Face 2 carries the proved `hel` constants. -/
theorem faceOK2 : FaceOK face2 := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> simp only [face2, helPhiC, helWC] <;> norm_num

/-- Face 3 carries the proved `hel` constants. -/
theorem faceOK3 : FaceOK face3 := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> simp only [face3, helPhiC, helWC] <;> norm_num

/-- **The certified bound on face 0.** -/
theorem cover0 : FaceGood fils face0 (phiM 1696) (phiM 9889) := by
  have h := grid_cover offs fils filsValid face0 faceOK0 42 grid0
    (by rw [show grid0.length = 166 from rfl]; norm_num)
    (by rw [show grid0.length = 166 from rfl]; norm_num)
    (fun i hi => by
      interval_cases i
      exacts [cert_0_0, cert_0_1, cert_0_2, cert_0_3, cert_0_4, cert_0_5, cert_0_6, cert_0_7,
          cert_0_8, cert_0_9, cert_0_10, cert_0_11, cert_0_12, cert_0_13, cert_0_14, cert_0_15,
          cert_0_16, cert_0_17, cert_0_18, cert_0_19, cert_0_20, cert_0_21, cert_0_22, cert_0_23,
          cert_0_24, cert_0_25, cert_0_26, cert_0_27, cert_0_28, cert_0_29, cert_0_30, cert_0_31,
          cert_0_32, cert_0_33, cert_0_34, cert_0_35, cert_0_36, cert_0_37, cert_0_38, cert_0_39,
          cert_0_40, cert_0_41])
  rwa [show grid0.headD 0 = 1696 from rfl, show grid0.getLastD 0 = 9889 from rfl] at h

/-- **The certified bound on face 1.** -/
theorem cover1 : FaceGood fils face1 (phiM 1696) (phiM 9889) := by
  have h := grid_cover offs fils filsValid face1 faceOK1 57 grid1
    (by rw [show grid1.length = 227 from rfl]; norm_num)
    (by rw [show grid1.length = 227 from rfl]; norm_num)
    (fun i hi => by
      interval_cases i
      exacts [cert_1_0, cert_1_1, cert_1_2, cert_1_3, cert_1_4, cert_1_5, cert_1_6, cert_1_7,
          cert_1_8, cert_1_9, cert_1_10, cert_1_11, cert_1_12, cert_1_13, cert_1_14, cert_1_15,
          cert_1_16, cert_1_17, cert_1_18, cert_1_19, cert_1_20, cert_1_21, cert_1_22, cert_1_23,
          cert_1_24, cert_1_25, cert_1_26, cert_1_27, cert_1_28, cert_1_29, cert_1_30, cert_1_31,
          cert_1_32, cert_1_33, cert_1_34, cert_1_35, cert_1_36, cert_1_37, cert_1_38, cert_1_39,
          cert_1_40, cert_1_41, cert_1_42, cert_1_43, cert_1_44, cert_1_45, cert_1_46, cert_1_47,
          cert_1_48, cert_1_49, cert_1_50, cert_1_51, cert_1_52, cert_1_53, cert_1_54, cert_1_55,
          cert_1_56])
  rwa [show grid1.headD 0 = 1696 from rfl, show grid1.getLastD 0 = 9889 from rfl] at h

/-- **The certified bound on face 2.** -/
theorem cover2 : FaceGood fils face2 (phiM 1696) (phiM 9889) := by
  have h := grid_cover offs fils filsValid face2 faceOK2 53 grid2
    (by rw [show grid2.length = 211 from rfl]; norm_num)
    (by rw [show grid2.length = 211 from rfl]; norm_num)
    (fun i hi => by
      interval_cases i
      exacts [cert_2_0, cert_2_1, cert_2_2, cert_2_3, cert_2_4, cert_2_5, cert_2_6, cert_2_7,
          cert_2_8, cert_2_9, cert_2_10, cert_2_11, cert_2_12, cert_2_13, cert_2_14, cert_2_15,
          cert_2_16, cert_2_17, cert_2_18, cert_2_19, cert_2_20, cert_2_21, cert_2_22, cert_2_23,
          cert_2_24, cert_2_25, cert_2_26, cert_2_27, cert_2_28, cert_2_29, cert_2_30, cert_2_31,
          cert_2_32, cert_2_33, cert_2_34, cert_2_35, cert_2_36, cert_2_37, cert_2_38, cert_2_39,
          cert_2_40, cert_2_41, cert_2_42, cert_2_43, cert_2_44, cert_2_45, cert_2_46, cert_2_47,
          cert_2_48, cert_2_49, cert_2_50, cert_2_51, cert_2_52])
  rwa [show grid2.headD 0 = 1696 from rfl, show grid2.getLastD 0 = 9889 from rfl] at h

/-- **The certified bound on face 3.** -/
theorem cover3 : FaceGood fils face3 (phiM 1696) (phiM 9889) := by
  have h := grid_cover offs fils filsValid face3 faceOK3 53 grid3
    (by rw [show grid3.length = 210 from rfl]; norm_num)
    (by rw [show grid3.length = 210 from rfl]; norm_num)
    (fun i hi => by
      interval_cases i
      exacts [cert_3_0, cert_3_1, cert_3_2, cert_3_3, cert_3_4, cert_3_5, cert_3_6, cert_3_7,
          cert_3_8, cert_3_9, cert_3_10, cert_3_11, cert_3_12, cert_3_13, cert_3_14, cert_3_15,
          cert_3_16, cert_3_17, cert_3_18, cert_3_19, cert_3_20, cert_3_21, cert_3_22, cert_3_23,
          cert_3_24, cert_3_25, cert_3_26, cert_3_27, cert_3_28, cert_3_29, cert_3_30, cert_3_31,
          cert_3_32, cert_3_33, cert_3_34, cert_3_35, cert_3_36, cert_3_37, cert_3_38, cert_3_39,
          cert_3_40, cert_3_41, cert_3_42, cert_3_43, cert_3_44, cert_3_45, cert_3_46, cert_3_47,
          cert_3_48, cert_3_49, cert_3_50, cert_3_51, cert_3_52])
  rwa [show grid3.headD 0 = 1696 from rfl, show grid3.getLastD 0 = 9889 from rfl] at h

end PlasmaLean.Design.PolygonCoil
