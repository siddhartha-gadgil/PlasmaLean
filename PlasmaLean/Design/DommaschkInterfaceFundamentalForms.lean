/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkInterfaceArcBounds
public import PlasmaLean.Theory.Fields.WeakQuasisymmetry

/-!
# Fundamental forms in the physical cylindrical frame

At a geometrical toroidal angle φ the oriented moving frame is (e_R,e_φ,e_z).
The tangent vectors use the geometric parametrization. The curvature convention of
N-44 is II(v,w) = v·∇_w n, so its coefficients with normal N are -N·X_ij.
Here N = X_φ × X_θ, the orientation of a meridian with positive poloidal winding.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkInterfaceFundamentalForms

open PlasmaLean.Fields PlasmaLean.Contract PlasmaLean.Stability.InterfacePrincipalDirection
open PlasmaLean.Design.DommaschkInterfaceArcGeometry PlasmaLean.Design.DommaschkInterfaceArcProfiles
open PlasmaLean.Design.DommaschkInterfaceArcBounds
open WithLp Real Matrix
open scoped RealInnerProductSpace

/-- Convert orthonormal cylindrical vector components to physical Cartesian space. -/
def frame (φ r s z : ℝ) : Space :=
  toLp 2 ![r * cos φ - s * sin φ, r * sin φ + s * cos φ, z]

private theorem frame_inner (φ r s z u v w : ℝ) :
    ⟪frame φ r s z, frame φ u v w⟫ = r*u + s*v + z*w := by
  simp [frame, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  linear_combination (r*u+s*v) * Real.sin_sq_add_cos_sq φ

private theorem frame_cross (φ r s z u v w : ℝ) :
    cross (frame φ r s z) (frame φ u v w) =
    frame φ (s*w-z*v) (z*u-r*w) (r*v-s*u) := by
  ext i
  fin_cases i <;> simp [frame, cross, cross_apply]
  · ring
  · ring
  · linear_combination (r*v-s*u) * Real.sin_sq_add_cos_sq φ

/-- The two first derivatives in the angular coordinates. -/
def Xθ (φ : ℝ) (j : Jet → ℝ) : Space := frame φ (j .rθ) 0 (j .zθ)
def Xφ (φ : ℝ) (j : Jet → ℝ) : Space := frame φ (j .rφ) (j .radius) (j .zφ)

/-- Second derivatives include the rotation of the cylindrical frame with toroidal angle. -/
def Xθθ (φ : ℝ) (j : Jet → ℝ) : Space := frame φ (j .rθθ) 0 (j .zθθ)
def Xθφ (φ : ℝ) (j : Jet → ℝ) : Space := frame φ (j .rθφ) (j .rθ) (j .zθφ)
def Xφφ (φ : ℝ) (j : Jet → ℝ) : Space := frame φ (j .rφφ - j .radius) (2*j .rφ) (j .zφφ)

/-- Embedded tangent vector with the supplied angular components. -/
def tangent (φ : ℝ) (j : Jet → ℝ) (v : ℝ × ℝ) : Space :=
  v.1 • Xθ φ j + v.2 • Xφ φ j

/-- Bilinear second derivative of the parametrization, with the mixed partial in both slots. -/
def second (φ : ℝ) (j : Jet → ℝ) (v w : ℝ × ℝ) : Space :=
  (v.1*w.1) • Xθθ φ j + (v.1*w.2 + v.2*w.1) • Xθφ φ j + (v.2*w.2) • Xφφ φ j

/-- The normal selected by the ordered tangent vectors. -/
def normal (φ : ℝ) (j : Jet → ℝ) : Space := cross (Xφ φ j) (Xθ φ j)

/-- The polynomial metric row is exactly the Euclidean tangent pairing. -/
theorem metric_pair (φ ι : ℝ) (j : Jet → ℝ) (w : ℝ × ℝ) :
    pair (metricRow ι j) w = ⟪tangent φ j (ι,1), tangent φ j w⟫ := by
  simp only [pair, metricRow, one_smul, tangent, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, Xθ, Xφ, frame_inner]
  ring

/-- The polynomial curvature row is the negative Euclidean normal pairing with the Hessian. -/
theorem curvature_pair (φ ι : ℝ) (j : Jet → ℝ) (w : ℝ × ℝ) :
    pair (curvatureRow ι j) w = -⟪normal φ j, second φ j (ι,1) w⟫ := by
  simp [pair, curvatureRow, normal, second, inner_add_right, real_inner_smul_right,
    Xθ, Xφ, Xθθ, Xθφ, Xφφ, frame_cross, frame_inner]
  ring

open PlasmaLean.Theory.KAM KamNewton KamNewton.ProfileAngle DommaschkKamC DommaschkKamA

/-- Differentiating vector components in the rotating frame adds angular-velocity terms. -/
theorem hasDerivAt_frame {r s z f : ℝ → ℝ} {t dr ds dz df : ℝ}
    (hr : HasDerivAt r dr t) (hs : HasDerivAt s ds t) (hz : HasDerivAt z dz t)
    (hf : HasDerivAt f df t) :
    HasDerivAt (fun x => frame (f x) (r x) (s x) (z x))
      (frame (f t) (dr - s t * df) (ds + r t * df) dz) t := by
  unfold frame
  apply hasDerivAt_space3
  · convert (hr.mul hf.cos).sub (hs.mul hf.sin) using 1
    ring
  · convert (hr.mul hf.sin).add (hs.mul hf.cos) using 1
    ring
  · exact hz

/-- The Cartesian parametrization of the Dommaschk profiles. -/
def surface (u z : FA) (θ φ : ℝ) : Space := cylPoint (RofC u θ φ) φ (Zof z θ φ)

private theorem surface_eq (u z : FA) (θ φ : ℝ) :
    surface u z θ φ = frame φ (RofC u θ φ) 0 (Zof z θ φ) := by
  simp [surface, frame, cylPoint]

/-- Poloidal tangent at arbitrary angular coordinates. -/
def polVec (u z : FA) (θ φ : ℝ) : Space :=
  frame φ (Zof (dTh u) θ φ) 0 (Zof (dTh z) θ φ)

/-- Toroidal tangent at arbitrary angular coordinates. -/
def torVec (u z : FA) (θ φ : ℝ) : Space :=
  frame φ (Zof (dPh u) θ φ) (RofC u θ φ) (Zof (dPh z) θ φ)

private theorem dirθ {u z : FA} (hu : Ana u) (hz : Ana z) (θ φ : ℝ) :
    deriv (fun t => surface u z t φ) θ = polVec u z θ φ := by
  simp only [surface_eq, polVec]
  have h := hasDerivAt_frame (hasDerivAt_RofC_θ hu θ φ) (hasDerivAt_const θ (0 : ℝ))
    (hasDerivAt_Zof_θ hz θ φ) (hasDerivAt_const θ φ)
  simpa [Zof] using h.deriv

private theorem dirφ {u z : FA} (hu : Ana u) (hz : Ana z) (θ φ : ℝ) :
    deriv (surface u z θ) φ = torVec u z θ φ := by
  change deriv (fun t => surface u z θ t) φ = _
  simp only [surface_eq, torVec]
  have h := hasDerivAt_frame (hasDerivAt_RofC_φ hu θ φ) (hasDerivAt_const φ (0 : ℝ))
    (hasDerivAt_Zof_φ hz θ φ) (hasDerivAt_id φ)
  simpa [Zof] using h.deriv

private theorem dzR (p : ProfileAngle) (u : FA) :
    p.partialD (RofC u) = p.partialD (Zof u) := by
  funext θ φ
  cases p <;> exact deriv_const_add _

/-- Physical angular first and second derivatives of the exact parametrization are
the five cylindrical vectors used by the metric and curvature rows. -/
theorem surface_derivatives {u z : FA} (hu : Ana u) (hz : Ana z) (φ : ℝ) :
    let j := cylindricalJet u z φ
    deriv (fun t => surface u z t φ) 0 = Xθ φ j ∧
    deriv (surface u z 0) φ = Xφ φ j ∧
    deriv (fun q => deriv (fun t => surface u z t φ) q) 0 = Xθθ φ j ∧
    deriv (fun p => deriv (fun t => surface u z t p) 0) φ = Xθφ φ j ∧
    deriv (fun p => deriv (surface u z 0) p) φ = Xφφ φ j := by
  have hut := hu.d 1 0
  have hup := hu.d 0 2
  have hzt := hz.d 1 0
  have hzp := hz.d 0 2
  have hθθ := hasDerivAt_frame (hasDerivAt_Zof_θ hut 0 φ) (hasDerivAt_const 0 (0 : ℝ))
    (hasDerivAt_Zof_θ hzt 0 φ) (hasDerivAt_const 0 φ)
  have hθφ := hasDerivAt_frame (hasDerivAt_Zof_φ hut 0 φ) (hasDerivAt_const φ (0 : ℝ))
    (hasDerivAt_Zof_φ hzt 0 φ) (hasDerivAt_id φ)
  have hφφ := hasDerivAt_frame (hasDerivAt_Zof_φ hup 0 φ) (hasDerivAt_RofC_φ hu 0 φ)
    (hasDerivAt_Zof_φ hzp 0 φ) (hasDerivAt_id φ)
  dsimp only
  simp only [dirθ hu hz, dirφ hu hz, Xθ, Xφ, Xθθ, Xθφ, Xφφ, cylindricalJet,
    dzR, partial_Zof _ hu, partial_Zof _ hz, partial_Zof _ (analytic _ hu),
    partial_Zof _ (analytic _ hz)]
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · simpa [polVec, symbol, dTh, Zof] using hθθ.deriv
  · simpa [polVec, symbol, dTh, dPh, Zof] using hθφ.deriv
  · simpa [torVec, symbol, dPh, Zof, two_mul] using hφφ.deriv

/-- On a positive circular meridian at its outer equator, the chosen cross product
points radially outward. -/
theorem circular_meridian_outer_normal (φ R a : ℝ) :
    cross (frame φ 0 R 0) (frame φ 0 0 a) = frame φ (R * a) 0 0 := by
  simp [frame_cross]

/-- The cross product is nonzero on the entire certified arc. -/
theorem normal_ne_zero {u z : FA} (h : ExactTorusA u z) {φ : ℝ} (hφ : φ ∈ Set.Icc 0 (1 / 5)) :
    normal φ (cylindricalJet u z φ) ≠ 0 := by
  have hp := (direction_positive (inBox_of_seedMargin h (seedMargins.2.2 φ hφ))).2
  rw [curvature_pair (φ := φ)] at hp
  intro hn
  simp [hn] at hp

/-- The chosen normal has strictly positive radial component throughout the exact arc. -/
theorem normal_radial_pos {u z : FA} (h : ExactTorusA u z) {φ : ℝ} (hφ : φ ∈ Set.Icc 0 (1 / 5)) :
    0 < ⟪normal φ (cylindricalJet u z φ), frame φ 1 0 0⟫ := by
  have hb := inBox_of_seedMargin h (seedMargins.2.2 φ hφ) Jet.zθ
  have hb' := (mem_gridBox_iff.mp hb).1
  have hr : 0 < cylindricalJet u z φ .radius := h.R_pos 0 φ
  have hz : 0 < cylindricalJet u z φ .zθ :=
    (show (0 : ℝ) < (1427 : ℤ) / 65536 by norm_num).trans_le hb'
  simpa [normal, Xφ, Xθ, frame_cross, frame_inner] using mul_pos hr hz

/-- The half-plane obstruction permits any nonzero physical field speed, of either
sign, and any positive rescaling of the ordered normal. -/
theorem exactTorusA_scaled_obstruction {u z : FA} (h : ExactTorusA u z) :
    ∃ φ ∈ Set.Icc 0 (1 / 5), ∀ (q l : ℝ) (w : ℝ × ℝ), 0 < l →
      let j := cylindricalJet u z φ
      let v := (DommaschkKamDio.dkIotaA, (1 : ℝ))
      0 < ⟪q • tangent φ j v, tangent φ j w⟫ →
      0 < -⟪l • normal φ j, q • second φ j v w⟫ := by
  obtain ⟨φ, hφ, hr⟩ := exactTorusA_obstruction h
  refine ⟨φ, hφ, ?_⟩
  intro q l w hl
  dsimp only
  rw [real_inner_smul_left, ← metric_pair]
  intro hw
  have hs (a : ℝ × ℝ) : pair a (q * w.1, q * w.2) = q * pair a w := by unfold pair; ring
  have hp := hr (q * w.1, q * w.2) ((hs _).symm ▸ hw)
  rw [hs, curvature_pair (φ := φ)] at hp
  rw [real_inner_smul_left, real_inner_smul_right]
  linarith only [mul_pos hl hp]

/-- The angular speed converting the straight field direction to the candidate field. -/
def fieldSpeed (u z : FA) (φ : ℝ) : ℝ :=
  DommaschkKam.cylBphi (RofC u 0 φ) φ (Zof z 0 φ) / RofC u 0 φ

/-- Nonvanishing physical speed on the exact torus. -/
theorem fieldSpeed_ne_zero {u z : FA} (h : ExactTorusA u z) (φ : ℝ) : fieldSpeed u z φ ≠ 0 :=
  div_ne_zero (h.Bphi_ne 0 φ) (h.R_pos 0 φ).ne'

private theorem field_frame (R φ z : ℝ) :
    DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint R φ z) =
      frame φ (DommaschkKam.cylBR R φ z) (DommaschkKam.cylBphi R φ z)
        (DommaschkKam.cylBz R φ z) := by
  set F := DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint R φ z)
  ext i
  fin_cases i <;> simp [frame, DommaschkKam.cylBR, DommaschkKam.cylBphi, DommaschkKam.cylBz, ← show
    DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint R φ z) = F from rfl]
  · linear_combination (-(F 0)) * Real.sin_sq_add_cos_sq φ
  · linear_combination (-(F 1)) * Real.sin_sq_add_cos_sq φ

private theorem speed_tangent (φ ι q : ℝ) (j : Jet → ℝ) :
    q • tangent φ j (ι, 1) =
      frame φ (q * (j .rφ + ι * j .rθ)) (q * j .radius) (q * (j .zφ + ι * j .zθ)) := by
  ext i
  fin_cases i <;> simp [tangent, Xθ, Xφ, frame] <;> ring

/-- In physical Cartesian coordinates this multiple of the angular tangent is the
actual candidate magnetic field at the certified interface. -/
theorem field_eq_speed_tangent {u z : FA} (h : ExactTorusA u z) (φ : ℝ) :
    DommaschkQA2R.field DommaschkQA2R.candidate (surface u z 0 φ) =
      fieldSpeed u z φ • tangent φ (cylindricalJet u z φ) (DommaschkKamDio.dkIotaA, 1) := by
  set R := RofC u 0 φ
  set Z := Zof z 0 φ
  set Bp := DommaschkKam.cylBphi R φ Z
  have hR : R ≠ 0 := (h.R_pos 0 φ).ne'
  have hR7 : R ^ 7 ≠ 0 := pow_ne_zero _ hR
  rw [surface, field_frame, speed_tangent]
  congr 1
  · change DommaschkKam.cylBR R φ Z = Bp / R * _
    rw [div_mul_eq_mul_div, eq_div_iff hR]
    apply mul_left_cancel₀ hR7
    change _ = R ^ 7 * (Bp * (deriv (fun t => RofC u 0 t) φ +
      DommaschkKamDio.dkIotaA * deriv (fun t => RofC u t φ) 0))
    linear_combination -(h.inv_R 0 φ)
  · exact (div_mul_cancel₀ Bp hR).symm
  · change DommaschkKam.cylBz R φ Z = Bp / R * _
    rw [div_mul_eq_mul_div, eq_div_iff hR]
    apply mul_left_cancel₀ hR7
    change _ = R ^ 7 * (Bp * (deriv (fun t => Zof z 0 t) φ +
      DommaschkKamDio.dkIotaA * deriv (fun t => Zof z t φ) 0))
    linear_combination -(h.inv_Z 0 φ)

/-- On every exact torus A there is a point on the arc where every tangent
variation with positive pairing against the actual magnetic field has positive
mixed second fundamental form for the unit normal selected by Xφ × Xθ. -/
theorem exactTorusA_unitNormal_field_obstruction {u z : FA} (h : ExactTorusA u z) :
    ∃ φ ∈ Set.Icc 0 (1 / 5), ∀ w : ℝ × ℝ,
      let j := cylindricalJet u z φ
      let n := ‖normal φ j‖⁻¹ • normal φ j
      0 < ⟪DommaschkQA2R.field DommaschkQA2R.candidate (surface u z 0 φ), tangent φ j w⟫ →
      0 < -⟪n, fieldSpeed u z φ • second φ j (DommaschkKamDio.dkIotaA, 1) w⟫ := by
  obtain ⟨φ, hφ, hs⟩ := exactTorusA_scaled_obstruction h
  refine ⟨φ, hφ, ?_⟩
  intro w
  dsimp only
  rw [field_eq_speed_tangent h]
  exact hs _ _ w (inv_pos.mpr (norm_pos_iff.mpr (normal_ne_zero h hφ)))

/-- Unit normal at arbitrary angular coordinates in the chosen orientation. -/
def unitNormal (u z : FA) (θ φ : ℝ) : Space :=
  let N := cross (torVec u z θ φ) (polVec u z θ φ)
  ‖N‖⁻¹ • N

private theorem polVec_jet {u z : FA} (hu : Ana u) (hz : Ana z) (φ : ℝ) :
    polVec u z 0 φ = Xθ φ (cylindricalJet u z φ) := by
  rw [← dirθ hu hz]
  exact (surface_derivatives hu hz φ).1

private theorem torVec_jet {u z : FA} (hu : Ana u) (hz : Ana z) (φ : ℝ) :
    torVec u z 0 φ = Xφ φ (cylindricalJet u z φ) := by
  rw [← dirφ hu hz]
  exact (surface_derivatives hu hz φ).2.1

private theorem z_line {y : FA} (hy : Ana y) (φ : ℝ) (w : ℝ × ℝ) :
    HasDerivAt (fun t => Zof y (t*w.1) (φ+t*w.2))
      (w.1 * Zof (dTh y) 0 φ + w.2 * Zof (dPh y) 0 φ) 0 := by
  have h := KamTorusA.hasDerivAt_line ((contDiff_Zof hy).differentiable (by norm_num)) 0 φ w.1 w.2
  change HasDerivAt (fun t => Zof y (0+t*w.1) (φ+t*w.2)) (w.1 * deriv (fun t => Zof y t φ) 0 +
    w.2 * deriv (Zof y 0) φ) 0 at h
  rw [(hasDerivAt_Zof_θ hy 0 φ).deriv, (hasDerivAt_Zof_φ hy 0 φ).deriv] at h
  simpa only [zero_add, Zof] using h

private theorem tangent_line_derivatives {u z : FA} (hu : Ana u) (hz : Ana z) (φ : ℝ)
    (w : ℝ × ℝ) :
    HasDerivAt (fun t => polVec u z (t*w.1) (φ+t*w.2))
      (second φ (cylindricalJet u z φ) (1,0) w) 0 ∧
    HasDerivAt (fun t => torVec u z (t*w.1) (φ+t*w.2))
      (second φ (cylindricalJet u z φ) (0,1) w) 0 := by
  have hp := hasDerivAt_frame (z_line (hu.d 1 0) φ w) (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    (z_line (hz.d 1 0) φ w) (KamTorusA.hasDerivAt_affine φ w.2)
  have ht := hasDerivAt_frame (z_line (hu.d 0 2) φ w) ((z_line hu φ w).const_add DommaschkKam.dkR0)
    (z_line (hz.d 0 2) φ w) (KamTorusA.hasDerivAt_affine φ w.2)
  have hcu : dS 1 0 (dS 0 2 u) = dS 0 2 (dS 1 0 u) := dS_dS_comm 1 0 0 2 hu
  have hcz : dS 1 0 (dS 0 2 z) = dS 0 2 (dS 1 0 z) := dS_dS_comm 1 0 0 2 hz
  constructor
  · apply hp.congr_deriv
    ext i
    fin_cases i <;> simp [second, Xθθ, Xθφ, Xφφ, frame, cylindricalJet, dzR, partial_Zof _ hu,
      partial_Zof _ hz, symbol,
      dTh, dPh, partial_Zof _ (hu.d 1 0), partial_Zof _ (hz.d 1 0)] <;> ring
  · apply ht.congr_deriv
    ext i
    fin_cases i <;> simp [second, Xθθ, Xθφ, Xφφ, frame, cylindricalJet, dzR, partial_Zof _ hu,
      partial_Zof _ hz, symbol,
      dTh, dPh, partial_Zof _ (hu.d 1 0), partial_Zof _ (hz.d 1 0),
      partial_Zof _ (hu.d 0 2), partial_Zof _ (hz.d 0 2), hcu, hcz, RofC] <;> ring

/-- Differentiating normal–tangent orthogonality along an angular line identifies the
normal derivative pairing with the negative unit-normal pairing against the Hessian. -/
theorem normal_derivative_pair {u z : FA} (h : ExactTorusA u z) {φ : ℝ}
    (hφ : φ ∈ Set.Icc 0 (1 / 5)) (v w : ℝ × ℝ) :
    let j := cylindricalJet u z φ
    ⟪tangent φ j v, deriv (fun t => unitNormal u z (t*w.1) (φ+t*w.2)) 0⟫ =
      -⟪‖normal φ j‖⁻¹ • normal φ j, second φ j v w⟫ := by
  let p := fun t : ℝ => polVec u z (t*w.1) (φ+t*w.2)
  let s := fun t : ℝ => torVec u z (t*w.1) (φ+t*w.2)
  let N := fun t : ℝ => cross (s t) (p t)
  let n := fun t : ℝ => ‖N t‖⁻¹ • N t
  obtain ⟨hp, hs⟩ := tangent_line_derivatives h.ana_u h.ana_z φ w
  have hdN : DifferentiableAt ℝ N 0 :=
    (crossBilinear.differentiableAt.comp 0 hs.differentiableAt).clm_apply hp.differentiableAt
  have ep : p 0 = Xθ φ (cylindricalJet u z φ) := by simpa [p] using polVec_jet h.ana_u h.ana_z φ
  have es : s 0 = Xφ φ (cylindricalJet u z φ) := by simpa [s] using torVec_jet h.ana_u h.ana_z φ
  have eN : N 0 = normal φ (cylindricalJet u z φ) := by
    change cross (s 0) (p 0) = _
    rw [es, ep]
    rfl
  have hN : N 0 ≠ 0 := eN ▸ normal_ne_zero h hφ
  have hdn : DifferentiableAt ℝ n 0 := ((hdN.norm ℝ hN).inv (norm_ne_zero_iff.mpr hN)).smul hdN
  have hh := ((hp.const_smul v.1).add (hs.const_smul v.2)).inner ℝ hdn.hasDerivAt
  have orth (t : ℝ) : ⟪v.1 • p t + v.2 • s t, n t⟫ = 0 := by
    simp [n, N, real_inner_smul_right, inner_add_left, real_inner_smul_left,
      inner_cross_right_self, inner_cross_left_self]
  have he := hh.deriv
  change deriv (fun t => ⟪v.1 • p t + v.2 • s t, n t⟫) 0 = _ at he
  simp only [orth, deriv_const] at he
  change 0 = ⟪v.1 • p 0 + v.2 • s 0, deriv n 0⟫ +
      ⟪_, n 0⟫ at he
  have hv : v.1 • second φ (cylindricalJet u z φ) (1,0) w +
      v.2 • second φ (cylindricalJet u z φ) (0,1) w = second φ (cylindricalJet u z φ) v w := by
    simp [second, smul_add, smul_smul, add_smul]
    abel
  rw [hv, real_inner_comm (n 0) _, ep, es] at he
  change _ = _ at he
  have en : n 0 = ‖normal φ (cylindricalJet u z φ)‖⁻¹ • normal φ (cylindricalJet u z φ) := by
    simp only [n, eN]
  rw [en] at he
  exact eq_neg_of_add_eq_zero_left he.symm

/-- With the source's sign convention, the actual magnetic field has strictly
positive pairing with the derivative of the oriented unit normal along every
tangent variation with positive field pairing at one point of the exact torus. -/
theorem exactTorusA_field_normalDerivative_obstruction {u z : FA} (h : ExactTorusA u z) :
    ∃ φ ∈ Set.Icc 0 (1 / 5), ∀ w : ℝ × ℝ,
      let B := DommaschkQA2R.field DommaschkQA2R.candidate (surface u z 0 φ)
      0 < ⟪B, tangent φ (cylindricalJet u z φ) w⟫ →
      0 < ⟪B, deriv (fun t => unitNormal u z (t*w.1) (φ+t*w.2)) 0⟫ := by
  obtain ⟨φ, hφ, hp⟩ := exactTorusA_unitNormal_field_obstruction h
  refine ⟨φ, hφ, ?_⟩
  intro w
  dsimp only
  intro hw
  have he := hp w hw
  rw [field_eq_speed_tangent h, real_inner_smul_left, normal_derivative_pair h hφ]
  rw [real_inner_smul_right] at he
  simpa only [mul_neg, neg_mul] using he

end PlasmaLean.Design.DommaschkInterfaceFundamentalForms
