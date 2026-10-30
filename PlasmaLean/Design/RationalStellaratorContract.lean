/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Contract.StellaratorContract
public import PlasmaLean.Design.RationalStellaratorConfinedForever

/-!
# Clause C1 for the rational stellarator vacuum field, and the tokamak exclusion for `∇φ`

Instances of the C1 definitions of `Theory/Contract/StellaratorContract`.

**Witness (C1 holds).** `rationalStellarator_currentFreeTransform`: the exact rational
stellarator field `field (1/4)` (a vacuum field, `field_vacuum`) satisfies clause C1 with
`I_max = 0` and `ι_min = ι_A = (75 + √5)/562 ≈ 0.1374` on the one-surface family consisting of the
exact KAM torus near torus A (`torusA_exact`, `exactTorus`):
* `ExactTorus.fieldTorus`: an `ExactTorus` (the flow form `D (∂_φ K + ι ∂_θ K) = (2εR Ps, εR² Pz)`
  of the field-line equations) is a `FieldTorus` with rotation number `ι_A` (velocity
  `(R⁴/D) • B`, `field_cylPt`);
* `ExactTorus.poloidalAngle`: its polar angle `Θf` about the circle `R = 1, z = 0` is a
  poloidal-angle convention (`polar`, `Θf_add_two_pi`, `Θf_add_pi`);
* `ExactTorus.surface`: the section is the radial filling `k ↦ 1 + k (K(χ, 0) − (1, 0))`,
  `0 ≤ k ≤ 1`, of the poloidal loop at `φ = 0`, which lies in the vacuum region (`R ≥ 0.8`).
So C1 holds on one certified torus. Not yet: a nested family of certified tori with
`ι ≥ ι_min` on each (only one exact torus is certified).

**Tokamak exclusion (C1 fails although `I = 0`).** The purely toroidal vacuum field
`toroidal = ∇φ = e_φ/R` (`toroidal_vacuum`): `toroidal_purelyToroidal`; the circular tori
`circTorus a` (`0 < a < 1`) are invariant with transform `0` (`circTorus_iotaOnTorus`; the
definition is not vacuous for this field); their sections carry zero current
(`toroidal_circ_current_zero`); and `toroidal_not_currentFreeTransform`: `∇φ` fails C1 for every
`I_max`, `ι_min` and every family of surfaces.
-/

public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorContract

open Real Set PlasmaLean.Fields PlasmaLean.Contract PlasmaLean.Design.RationalStellarator
open PlasmaLean.Design.KamTorusA

/-- The contract's cylindrical point is the cylindrical point of `KamTorusA`. -/
theorem cylPoint_eq_cylPt (R φ z : ℝ) : cylPoint R φ z = cylPt R φ z := rfl

/-! ## The tokamak exclusion for `∇φ` -/

/-- The vacuum field `∇φ = e_φ/R` is purely toroidal. -/
theorem toroidal_purelyToroidal : PurelyToroidal toroidal := fun x => by
  simp only [toroidal]
  refine ⟨by simp, ?_⟩
  simp
  ring

/-- **`∇φ` fails C1** for every `I_max`, every `ι_min` and every family of surfaces (although it
is a vacuum field): its invariant tori have `ι = 0`. -/
theorem toroidal_not_currentFreeTransform {μ₀ Imax ιmin : ℝ} {S : Set SurfaceData} :
    ¬ CurrentFreeTransform μ₀ toroidal S Imax ιmin :=
  not_currentFreeTransform_of_purelyToroidal toroidal_purelyToroidal

/-- The circular torus of minor radius `a` about the circle `R = 1, z = 0`: `R = 1 + a cos θ`. -/
@[expose] def circR (a : ℝ) (θ _φ : ℝ) : ℝ := 1 + a * cos θ

/-- The circular torus: `z = a sin θ`. -/
@[expose] def circZ (a : ℝ) (θ _φ : ℝ) : ℝ := a * sin θ

/-- `toroidal` at a cylindrical point: `(−sin φ, cos φ, 0)/R`. -/
theorem toroidal_cylPoint {R : ℝ} (hR : 0 < R) (φ z : ℝ) :
    toroidal (cylPoint R φ z) = WithLp.toLp 2 ![-(sin φ / R), cos φ / R, 0] := by
  rw [toroidal, winv, cylPoint_eq_cylPt, r2_cylPt]
  have hR0 := hR.ne'
  ext i
  fin_cases i <;> simp [cylPt] <;> field_simp

/-- **Instance**: the circular tori (`0 < a < 1`) are invariant tori of `∇φ` with rotational
transform `0`, with the poloidal angle `θ` about the circle `R = 1, z = 0`. -/
theorem circTorus_iotaOnTorus {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    IotaOnTorus toroidal (circR a) (circZ a) 0 := by
  have hRpos : ∀ θ, 0 < 1 + a * cos θ := fun θ => by
    nlinarith [neg_one_le_cos θ, cos_le_one θ]
  refine ⟨⟨by unfold circR; fun_prop, by unfold circZ; fun_prop, fun θ _ => hRpos θ,
    fun θ φ => by simp [circR], fun θ φ => by simp [circZ], fun _ _ => rfl, fun _ _ => rfl,
    fun θ φ => ?_⟩, 1, 0, fun θ _ => θ, ⟨continuous_fst, fun θ φ => ⟨a, ha, ?_, ?_⟩,
    fun _ _ => rfl, fun _ _ => rfl⟩⟩
  · refine ⟨(1 + a * cos θ) ^ 2, ?_⟩
    have hφ : HasDerivAt (fun t : ℝ => φ + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add φ
    have h0 := (hφ.cos).const_mul (1 + a * cos θ)
    have h1 := (hφ.sin).const_mul (1 + a * cos θ)
    have h := hasDerivAt_toLp3 h0 h1 (hasDerivAt_const (0 : ℝ) (a * sin θ))
    simp only [circR, circZ, mul_zero, add_zero]
    refine h.congr_deriv ?_
    rw [toroidal_cylPoint (hRpos θ)]
    have hR0 := (hRpos θ).ne'
    ext i
    fin_cases i <;> simp <;> field_simp
  · simp [circR]
  · simp [circZ]

/-- The radial filling of the poloidal loop of the circular torus at `φ = 0`. -/
@[expose] def circSection (a : ℝ) (p : Space) : Space :=
  cylPoint (1 + p 0 * (a * cos (p 1))) 0 (p 0 * (a * sin (p 1)))

/-- The C1 surface data of the circular torus of `∇φ`. -/
@[expose] def circSurface (a : ℝ) : SurfaceData where
  R := circR a
  z := circZ a
  iota := 0
  X := circSection a
  ζ₀ := 0
  k₀ := 1
  φ₀ := 0

/-- The section spans the poloidal loop. -/
theorem circSurface_spans (a : ℝ) : (circSurface a).Spans := by
  refine ⟨zero_le_one, fun χ => ?_, fun χ χ' => ?_⟩ <;>
    simp [circSurface, circSection, circR, circZ, coordPt]

/-- **`∇φ` carries no current through the sections of the circular tori** (`toroidal_vacuum`):
it passes the current clause of C1 and fails only the transform clause. -/
theorem toroidal_circ_current_zero {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (μ₀ : ℝ) :
    netToroidalCurrent μ₀ toroidal (circSection a) 0 1 = 0 := by
  refine netToroidalCurrent_eq_zero_of_vacuum toroidal_vacuum zero_le_one fun k hk χ _ => ?_
  change 0 < r2 (cylPt _ _ _)
  rw [r2_cylPt]
  simp only [coordPt, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have := neg_one_le_cos χ
  have e1 : 0 ≤ k * (a * cos χ + a) := mul_nonneg hk.1 (by nlinarith)
  have e2 : k * a ≤ a := by nlinarith [hk.2]
  have : 0 < 1 + k * (a * cos χ) := by nlinarith
  positivity

/-! ## The witness: the exact KAM torus of the rational stellarator -/

namespace ExactTorus

variable {Rk zk : ℝ → ℝ → ℝ} (hK : ExactTorus Rk zk)
include hK

/-- **An `ExactTorus` is a `FieldTorus` of `field (1/4)` with rotation number `ι_A`**: the image
of each line `t ↦ (θ + ι_A t, φ + t)` has velocity `(R⁴/D) • B`. -/
theorem fieldTorus : FieldTorus (field (1 / 4)) Rk zk iota where
  continuous_R := hK.contDiff_R.continuous
  continuous_z := hK.contDiff_Z.continuous
  R_pos θ φ := by linarith [(hK.R_bounds θ φ).1]
  per_θ_R := hK.per_θ_R
  per_θ_z := hK.per_θ_z
  per_φ_R θ φ := by rw [show φ + 2 * π = φ + π + π by ring, hK.per_φ_R, hK.per_φ_R]
  per_φ_z θ φ := by rw [show φ + 2 * π = φ + π + π by ring, hK.per_φ_z, hK.per_φ_z]
  flow θ φ := by
    have hLR := hasDerivAt_line hK.differentiable_R θ φ iota 1
    have hLZ := hasDerivAt_line hK.differentiable_Z θ φ iota 1
    simp only [mul_one, one_mul] at hLR hLZ
    set La := iota * deriv (fun θ' => Rk θ' φ) θ + deriv (fun φ' => Rk θ φ') φ with hLa
    set Lb := iota * deriv (fun θ' => zk θ' φ) θ + deriv (fun φ' => zk θ φ') φ with hLb
    have hφ : HasDerivAt (fun t : ℝ => φ + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add φ
    have h0 := hLR.mul hφ.cos
    have h1 := hLR.mul hφ.sin
    have h := hasDerivAt_toLp3 h0 h1 hLZ
    have hRpos : 0 < Rk θ φ := by linarith [(hK.R_bounds θ φ).1]
    have hD := hK.D_pos θ φ
    set D := Dfun (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) with hDdef
    have hIR : D * La = 2 * eps * Rk θ φ *
        Psfun (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) := by
      rw [hLa, ← hK.inv_R θ φ]; ring
    have hIZ : D * Lb = eps * Rk θ φ ^ 2 *
        Pzfun (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) := by
      rw [hLb, ← hK.inv_z θ φ]; ring
    refine ⟨Rk θ φ ^ 4 / D, h.congr_deriv ?_⟩
    rw [cylPoint_eq_cylPt, field_cylPt hRpos]
    simp only [zero_mul, add_zero, mul_one]
    have hD0 := hD.ne'
    have hR0 := hRpos.ne'
    ext i
    fin_cases i
    · simp only [cylBR, cylBT, Fin.zero_eta, Fin.isValue, PiLp.smul_apply,
        Matrix.cons_val_zero, smul_eq_mul]
      rw [show La = 2 * eps * Rk θ φ * Psfun (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) / D by
        field_simp; linarith]
      field_simp
      ring
    · simp only [cylBR, cylBT, Fin.mk_one, Fin.isValue, PiLp.smul_apply,
        Matrix.cons_val_one, Matrix.cons_val_zero, smul_eq_mul]
      rw [show La = 2 * eps * Rk θ φ * Psfun (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) / D by
        field_simp; linarith]
      field_simp
      ring
    · simp only [cylBZ, Fin.reduceFinMk, Fin.isValue, PiLp.smul_apply,
        Matrix.cons_val, smul_eq_mul]
      rw [show Lb = eps * Rk θ φ ^ 2 * Pzfun (Rk θ φ) (zk θ φ) (cos (2 * φ)) (sin (2 * φ)) / D by
        field_simp; linarith]
      field_simp

/-- The polar angle `Θf` about the circle `R = 1, z = 0` is a poloidal-angle convention for an
`ExactTorus`. -/
theorem poloidalAngle : PoloidalAngle Rk zk 1 0 (Θf Rk zk) where
  continuous := hK.contDiff_Θf.continuous
  polar θ φ := ⟨rtK Rk zk θ φ, hK.rtK_pos θ φ, (hK.polar θ φ).1, by simpa using (hK.polar θ φ).2⟩
  wind_θ := hK.Θf_add_two_pi
  wind_φ θ φ := by rw [show φ + 2 * π = φ + π + π by ring, hK.Θf_add_pi, hK.Θf_add_pi]

/-- An `ExactTorus` has rotational transform `ι_A` in the sense of the contract. -/
theorem iotaOnTorus : IotaOnTorus (field (1 / 4)) Rk zk iota :=
  ⟨ExactTorus.fieldTorus hK, 1, 0, Θf Rk zk, ExactTorus.poloidalAngle hK⟩

end ExactTorus

/-- The radial filling `k ↦ (1, 0) + k ((R, z)(χ, 0) − (1, 0))` of the poloidal loop at `φ = 0`
of a torus `(R, z)`. -/
@[expose] def fillSection (Rk zk : ℝ → ℝ → ℝ) (p : Space) : Space :=
  cylPoint (1 + p 0 * (Rk (p 1) 0 - 1)) 0 (p 0 * zk (p 1) 0)

/-- The C1 surface data of a torus `(R, z)` with transform `ι_A` and its radial filling. -/
@[expose] def exactSurface (Rk zk : ℝ → ℝ → ℝ) : SurfaceData where
  R := Rk
  z := zk
  iota := iota
  X := fillSection Rk zk
  ζ₀ := 0
  k₀ := 1
  φ₀ := 0

/-- The radial filling spans the poloidal loop. -/
theorem exactSurface_spans (Rk zk : ℝ → ℝ → ℝ) : (exactSurface Rk zk).Spans := by
  refine ⟨zero_le_one, fun χ => ?_, fun χ χ' => ?_⟩ <;>
    simp [exactSurface, fillSection, coordPt]

/-- The radial filling of an `ExactTorus` lies in the vacuum region `R > 0`. -/
theorem fillSection_mem {Rk zk : ℝ → ℝ → ℝ} (hK : ExactTorus Rk zk) {k χ : ℝ}
    (hk : k ∈ Icc (0 : ℝ) 1) : fillSection Rk zk (coordPt k χ 0) ∈ domain := by
  change 0 < r2 (cylPt _ _ _)
  rw [r2_cylPt]
  simp only [coordPt, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have := (hK.R_bounds χ 0).1
  have e1 : 0 ≤ k * (Rk χ 0 - 1 + 1 / 5) := mul_nonneg hk.1 (by linarith)
  have e2 : k ≤ 1 := hk.2
  have : 0 < 1 + k * (Rk χ 0 - 1) := by nlinarith
  positivity

/-- `ι_A > 0`. -/
theorem iota_pos : 0 < iota := by unfold iota; positivity

/-- **C1 witness**: the rational stellarator vacuum field satisfies clause C1 with `I_max = 0` and
`ι_min = ι_A = (75 + √5)/562` on the exact KAM torus near torus A. -/
theorem rationalStellarator_currentFreeTransform (μ₀ : ℝ) :
    ∃ S : Set SurfaceData, CurrentFreeTransform μ₀ (field (1 / 4)) S 0 iota := by
  obtain ⟨u, z, hu, hz, hur, hzr, hR, hZ, hC⟩ := PlasmaLean.Design.KamNewton.torusA_exact
  have hK := PlasmaLean.Design.KamNewton.exactTorus hu hz hur hzr hR hZ hC
  refine ⟨{exactSurface (KamNewton.Rof u) (KamNewton.Zof z)},
    currentFreeTransform_of_vacuum (field_vacuum (1 / 4)) (singleton_nonempty _) iota_pos
      ?_ ?_ ?_ ?_⟩
  · rintro s rfl; exact ExactTorus.iotaOnTorus hK
  · rintro s rfl; exact exactSurface_spans _ _
  · rintro s rfl k hk χ _; exact fillSection_mem hK hk
  · rintro s rfl; exact le_rfl

end PlasmaLean.Design.RationalStellaratorContract
