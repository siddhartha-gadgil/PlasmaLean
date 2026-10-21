/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCSmooth
public import PlasmaLean.Design.RationalStellaratorGCCyl
public import PlasmaLean.Theory.Kinetic.GuidingCentrePassing
public import PlasmaLean.Theory.Kinetic.GuidingCentre

/-!
# The `μ > 0` passing guiding-centre field of the rational stellarator (`gcFieldMu`)

Passing guiding centres with magnetic moment `μ` and energy `E` move along the field lines of
`B̃ = B + ∇×(ρ_{E,μ} b)` (`Theory/Kinetic/GuidingCentrePassing`, `modFieldFn`, `rhoE`). For the
rational stellarator `B = field (1/4)` (curl free) both parts of the correction are parallel to
`B × ∇|B|²`:

* `curlb_eq_cross`: `∇×b = ½ |B|⁻³ B × ∇|B|²`;
* `gradAbsB_eq`: `∇|B| = ∇|B|² / (2|B|)`, so `∇ρ × b ∥ B × ∇|B|²`.

**Main identity** (`modFieldFn_rhoE_eq`): where `B ≠ 0` and `μ|B| < E`,

`B̃_{E,μ} = gcField (ρ₀ F) = gcFieldMu ρ₀ λ`,  `ρ₀ = (m/q)√(2E/m)`, `λ = μ/E`,
`F = (1 − λ|B|/2)/√(1 − λ|B|)`,

i.e. the `μ > 0` passing field is the `μ = 0` guiding-centre field `gcField` with the
position-dependent gyro-length `ρ₀ F(x)`. `gcFieldMu ρ₀ λ` is `C¹` on the open region
`muRegion λ = {r₂ > 0, B ≠ 0, λ|B| < 1}` (`gcFieldMu_contDiffOn`).

**Sanity.** `Fmu_zero`: `F = 1` for `λ = 0`, so `gcFieldMu ρ₀ 0 = gcField ρ₀`
(`gcFieldMu_zero`).
-/

open scoped RealInnerProductSpace

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator PlasmaLean.Kinetic.GCLittlejohn
  PlasmaLean.Design.KamTorusA
  PlasmaLean.Kinetic.GCPassing PlasmaLean.Kinetic.GuidingCentre WithLp

/-! ## The two parts of the correction -/

/-- **`∇×b = ½ |B|⁻³ B × ∇|B|²`** on `gcRegion`. -/
theorem curlb_eq_cross {x : Space} (hx : x ∈ gcRegion) :
    curlb (field (1 / 4)) x =
      (1 / 2 * Qf x ^ (-(3 : ℝ) / 2)) • cross (field (1 / 4) x) (gradient Qf x) := by
  have h := gcField_eq 1 hx.1 hx.2
  rw [gcField, modField, one_smul, add_right_inj] at h
  exact h

/-- `|B|` is differentiable on `gcRegion`. -/
theorem differentiableAt_normB {x : Space} (hx : x ∈ gcRegion) :
    DifferentiableAt ℝ (fun y => ‖field (1 / 4) y‖) x :=
  ((field_hasFDerivAt x (1 / 4) hx.1).differentiableAt).norm ℝ hx.2

/-- `b` is differentiable on `gcRegion`. -/
theorem differentiableAt_bhat {x : Space} (hx : x ∈ gcRegion) :
    DifferentiableAt ℝ (bhat (field (1 / 4))) x :=
  ((differentiableAt_normB hx).inv (norm_ne_zero_iff.2 hx.2)).smul
    (field_hasFDerivAt x (1 / 4) hx.1).differentiableAt

/-- **`∇|B| = ∇|B|² / (2|B|)`** on `gcRegion`. -/
theorem gradAbsB_eq {x : Space} (hx : x ∈ gcRegion) :
    gradAbsB (field (1 / 4)) x = (2 * ‖field (1 / 4) x‖)⁻¹ • gradient Qf x := by
  have hn := (differentiableAt_normB hx).hasGradientAt
  have hn0 : ‖field (1 / 4) x‖ ≠ 0 := norm_ne_zero_iff.2 hx.2
  have hQ : HasGradientAt Qf ((2 * ‖field (1 / 4) x‖) • gradAbsB (field (1 / 4)) x) x := by
    rw [hasGradientAt_iff_hasFDerivAt] at hn ⊢
    have h2 := hn.pow 2
    refine (h2.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    · ext v
      simp [gradAbsB, map_smul]
    · simp [Qf]
  rw [hQ.gradient, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

/-! ## The passing field is a guiding-centre field with variable gyro-length -/

/-- The scalar `F = (1 − λ|B|/2)/√(1 − λ|B|)`. -/
def Fmu (lm : ℝ) (x : Space) : ℝ :=
  (1 - lm * ‖field (1 / 4) x‖ / 2) / √(1 - lm * ‖field (1 / 4) x‖)

/-- **Sanity**: `F = 1` for `λ = 0`. -/
theorem Fmu_zero (x : Space) : Fmu 0 x = 1 := by simp [Fmu]

/-- **The `μ > 0` passing guiding-centre field** `gcField (ρ₀ F(x))` of the rational stellarator. -/
def gcFieldMu (ρ₀ lm : ℝ) (x : Space) : Space := gcField (ρ₀ * Fmu lm x) x

/-- **Sanity**: for `λ = 0` it is the `μ = 0` guiding-centre field. -/
theorem gcFieldMu_zero (ρ₀ : ℝ) : gcFieldMu ρ₀ 0 = gcField ρ₀ := by
  funext x; simp [gcFieldMu, Fmu_zero]

/-- The gyro-length identity: `(m/q) w + μ|B|/(q w) = ρ₀ F` with `w = √(2(E − μ|B|)/m)`. -/
theorem rho_eff_eq {m q μ E nB : ℝ} (hm : 0 < m) (hq : q ≠ 0) (hE : 0 < E) (hw : μ * nB < E) :
    m / q * √(2 * (E - μ * nB) / m) + μ * nB / (q * √(2 * (E - μ * nB) / m)) =
      m / q * √(2 * E / m) * ((1 - μ / E * nB / 2) / √(1 - μ / E * nB)) := by
  have h1 : 0 < 1 - μ / E * nB := by
    rw [sub_pos, div_mul_eq_mul_div, div_lt_one hE]; exact hw
  have h2 : 0 < 2 * E / m := by positivity
  set s := √(2 * E / m) with hs
  set t := √(1 - μ / E * nB) with ht
  have hs0 : 0 < s := Real.sqrt_pos.2 h2
  have ht0 : 0 < t := Real.sqrt_pos.2 h1
  have hs2 : s ^ 2 = 2 * E / m := Real.sq_sqrt h2.le
  have ht2 : t ^ 2 = 1 - μ / E * nB := Real.sq_sqrt h1.le
  have hwst : √(2 * (E - μ * nB) / m) = s * t := by
    rw [hs, ht, ← Real.sqrt_mul h2.le]
    congr 1
    field_simp
  have hE0 : E ≠ 0 := hE.ne'
  have hm0 : m ≠ 0 := hm.ne'
  rw [hwst]
  calc m / q * (s * t) + μ * nB / (q * (s * t)) = (m * s ^ 2 * t ^ 2 + μ * nB) / (q * s * t) := by
        field_simp
    _ = (m * s ^ 2 * (1 - μ / E * nB / 2)) / (q * s * t) := by
        rw [ht2]; congr 1; rw [hs2]; field_simp; ring
    _ = m / q * s * ((1 - μ / E * nB / 2) / t) := by
        field_simp

/-- **The passing field is a guiding-centre field with variable gyro-length**: where `B ≠ 0` and
`μ|B| < E`, `B + ∇×(ρ_{E,μ} b) = gcField (ρ₀ F)` with `ρ₀ = (m/q)√(2E/m)`, `λ = μ/E`. -/
theorem modFieldFn_rhoE_eq {m q μ E : ℝ} (hm : 0 < m) (hq : q ≠ 0) (hE : 0 < E) {x : Space}
    (hx : x ∈ gcRegion) (hw : μ * ‖field (1 / 4) x‖ < E) :
    modFieldFn (rhoE m q μ E 1 (field (1 / 4))) (field (1 / 4)) x =
      gcFieldMu (m / q * √(2 * E / m)) (μ / E) x := by
  have hn0 : 0 < ‖field (1 / 4) x‖ := norm_pos_iff.2 hx.2
  have hu : 0 < 2 * (E - μ * ‖field (1 / 4) x‖) / m := by
    have : 0 < E - μ * ‖field (1 / 4) x‖ := by linarith
    positivity
  have hgr := hasGradientAt_rhoE (q := q) (σ := 1) hm.ne' (differentiableAt_normB hx) hu
  rw [modFieldFn_eq hgr.differentiableAt (differentiableAt_bhat hx), hgr.gradient,
    curlb_eq_cross hx, gradAbsB_eq hx, gcFieldMu, gcField_eq _ hx.1 hx.2]
  have hQr : Qf x ^ (-(3 : ℝ) / 2) = (‖field (1 / 4) x‖ ^ 3)⁻¹ := by
    rw [show Qf x = ‖field (1 / 4) x‖ ^ 2 from rfl, show -(3 : ℝ) / 2 = -(3 / 2) by ring,
      Real.rpow_neg (by positivity), show ‖field (1 / 4) x‖ ^ 2 = ‖field (1 / 4) x‖ ^ (2 : ℝ) by
        norm_cast, ← Real.rpow_mul hn0.le]
    norm_num
  have hcr : cross (gradient Qf x) (field (1 / 4) x) =
      -cross (field (1 / 4) x) (gradient Qf x) := by
    simp only [cross]
    rw [← WithLp.toLp_neg, ← cross_anticomm]
  simp only [bhat, cross_smul_left', cross_smul_right', smul_smul, hcr, smul_neg, hQr]
  rw [add_assoc, ← sub_eq_add_neg, ← sub_smul]
  congr 2
  have hw' := rho_eff_eq hm hq hE (show μ * ‖field (1 / 4) x‖ < E from hw)
  rw [Fmu, ← mul_assoc, ← hw', rhoE]
  set w := √(2 * (E - μ * ‖field (1 / 4) x‖) / m)
  have hw0 : 0 < w := Real.sqrt_pos.2 hu
  field_simp
  ring

/-! ## Regularity -/

/-- The region `{r₂ > 0, B ≠ 0, λ|B| < 1}`. -/
def muRegion (lm : ℝ) : Set Space := {x | x ∈ gcRegion ∧ lm * ‖field (1 / 4) x‖ < 1}

/-- `muRegion λ` is open. -/
theorem isOpen_muRegion (lm : ℝ) : IsOpen (muRegion lm) := by
  have hc : ContinuousOn (fun x => lm * ‖field (1 / 4) x‖) gcRegion :=
    continuousOn_const.mul ((field_contDiffOn_n (1 / 4) 0).continuousOn.mono
      (fun x hx => hx.1)).norm
  exact hc.isOpen_inter_preimage isOpen_gcRegion isOpen_Iio

/-- `|B|` is smooth on `gcRegion`. -/
theorem normB_contDiffOn (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (fun x => ‖field (1 / 4) x‖) gcRegion :=
  ((field_contDiffOn_n (1 / 4) n).mono fun _ hx => hx.1).norm ℝ fun _ hx => hx.2

/-- `F` is smooth on `muRegion λ`. -/
theorem Fmu_contDiffOn (lm : ℝ) (n : WithTop ℕ∞) : ContDiffOn ℝ n (Fmu lm) (muRegion lm) := by
  have hN := (normB_contDiffOn n).mono (fun x (hx : x ∈ muRegion lm) => hx.1)
  have h1 : ContDiffOn ℝ n (fun x => 1 - lm * ‖field (1 / 4) x‖) (muRegion lm) :=
    contDiffOn_const.sub (contDiffOn_const.mul hN)
  have hs : ContDiffOn ℝ n (fun x => √(1 - lm * ‖field (1 / 4) x‖)) (muRegion lm) :=
    h1.sqrt fun x hx => by have := hx.2; linarith
  exact ((contDiffOn_const.sub ((contDiffOn_const.mul hN).div_const 2)).div hs fun x hx => by
    have := hx.2; exact (Real.sqrt_pos.2 (by linarith)).ne')

/-- The explicit form of `gcFieldMu` on `gcRegion`. -/
theorem gcFieldMu_eq (ρ₀ lm : ℝ) {x : Space} (hx : x ∈ gcRegion) :
    gcFieldMu ρ₀ lm x = field (1 / 4) x +
      (ρ₀ * Fmu lm x / 2 * Qf x ^ (-(3 : ℝ) / 2)) • cross (field (1 / 4) x) (gradient Qf x) :=
  gcField_eq _ hx.1 hx.2

/-- **`gcFieldMu ρ₀ λ` is `C¹`** on the open region `muRegion λ`. -/
theorem gcFieldMu_contDiffOn (ρ₀ lm : ℝ) : ContDiffOn ℝ 1 (gcFieldMu ρ₀ lm) (muRegion lm) := by
  have hsub : muRegion lm ⊆ domain := fun x hx => hx.1.1
  have hB := (field_contDiffOn_n (1 / 4) 1).mono hsub
  have hQ := (Qf_contDiffOn 1).mono hsub
  have hg := (gradient_Qf_contDiffOn 1).mono hsub
  have hQr : ContDiffOn ℝ 1 (fun x => Qf x ^ (-(3 : ℝ) / 2)) (muRegion lm) := fun x hx =>
    ((hQ x hx).contDiffAt ((isOpen_muRegion lm).mem_nhds hx)).rpow_const_of_ne
      (Qf_pos hx.1).ne' |>.contDiffWithinAt
  have hc : ContDiffOn ℝ 1 (fun x => cross (field (1 / 4) x) (gradient Qf x)) (muRegion lm) :=
    (contDiff_cross 1).comp_contDiffOn (hB.prodMk hg)
  have hF : ContDiffOn ℝ 1 (fun x => field (1 / 4) x +
      (ρ₀ * Fmu lm x / 2 * Qf x ^ (-(3 : ℝ) / 2)) • cross (field (1 / 4) x) (gradient Qf x))
      (muRegion lm) :=
    hB.add ((((contDiffOn_const.mul (Fmu_contDiffOn lm 1)).div_const 2).mul hQr).smul hc)
  exact hF.congr fun x hx => gcFieldMu_eq ρ₀ lm hx.1

/-! ## An upper bound for `|B|` near the magnetic axis -/

/-- The polynomial bound used by `qr_le`. -/
theorem qr_poly_bound {x : ℝ} (hx : 49 / 100 ≤ x) :
    (456 / 1000) ^ 2 * x + x * (x + 195 / 1000) ^ 2 + (412 / 1000) ^ 2 * x ^ 2 ≤ 9 * x ^ 4 := by
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, 0 ≤ t ∧ 49 / 100 + t = x := ⟨x - 49 / 100, by linarith, by ring⟩
  nlinarith [pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4]

/-- **`|B|² ≤ 9` on the box** `0.7 ≤ R ≤ 1.3`, `|z| ≤ 0.3` (in the variables of the flow form). -/
theorem qr_le {R z C S : ℝ} (hR0 : 7 / 10 ≤ R) (hR1 : R ≤ 13 / 10) (hz : |z| ≤ 3 / 10)
    (hC : |C| ≤ 1) (hS : |S| ≤ 1) : qr R z C S ≤ 9 * R ^ 8 := by
  obtain ⟨hz1, hz2⟩ := abs_le.mp hz
  obtain ⟨hC1, hC2⟩ := abs_le.mp hC
  obtain ⟨hS1, hS2⟩ := abs_le.mp hS
  have hz2' : z ^ 2 ≤ 9 / 100 := by nlinarith
  have hRp : 0 < R := by linarith
  have hR4a : (7 / 10 : ℝ) ^ 4 ≤ R ^ 4 := pow_le_pow_left₀ (by norm_num) hR0 4
  have hR4b : R ^ 4 ≤ (13 / 10 : ℝ) ^ 4 := pow_le_pow_left₀ hRp.le hR1 4
  -- the three components
  have hsf : |sfun R z| ≤ 12 / 100 := by
    have h1 : (R ^ 2 - 1) ^ 2 ≤ (69 / 100) ^ 2 := by
      have : |R ^ 2 - 1| ≤ 69 / 100 := by rw [abs_le]; constructor <;> nlinarith
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
    rw [sfun, abs_le]; constructor <;> nlinarith [sq_nonneg (R ^ 2 - 1), sq_nonneg z]
  have hsg : |sgfun R z| ≤ 27 / 100 := by
    have h5 : |(R ^ 2 - 1) * (R ^ 2 - 5) - 4 * z ^ 2| ≤ 69 / 100 * (451 / 100) + 36 / 100 := by
      have a1 : |R ^ 2 - 1| ≤ 69 / 100 := by rw [abs_le]; constructor <;> nlinarith
      have a2 : |R ^ 2 - 5| ≤ 451 / 100 := by rw [abs_le]; constructor <;> nlinarith
      calc |(R ^ 2 - 1) * (R ^ 2 - 5) - 4 * z ^ 2|
          ≤ |(R ^ 2 - 1) * (R ^ 2 - 5)| + |4 * z ^ 2| := abs_sub _ _
        _ ≤ 69 / 100 * (451 / 100) + 36 / 100 := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * z ^ 2)]
          gcongr; linarith
    rw [sgfun, abs_div, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    calc |z| * |(R ^ 2 - 1) * (R ^ 2 - 5) - 4 * z ^ 2| / 4
        ≤ 3 / 10 * (69 / 100 * (451 / 100) + 36 / 100) / 4 := by gcongr
      _ ≤ 27 / 100 := by norm_num
  have hD : |Dfun R z C S - R ^ 2| ≤ 195 / 1000 := by
    have e : Dfun R z C S - R ^ 2 = eps * (-2 * sfun R z * S + 2 * sgfun R z * C) := by
      rw [Dfun]; ring
    rw [e, eps, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    have h1 : |-2 * sfun R z * S + 2 * sgfun R z * C| ≤ 2 * (12 / 100) + 2 * (27 / 100) := by
      calc |-2 * sfun R z * S + 2 * sgfun R z * C|
          ≤ |-2 * sfun R z * S| + |2 * sgfun R z * C| := abs_add_le _ _
        _ = 2 * (|sfun R z| * |S|) + 2 * (|sgfun R z| * |C|) := by
          simp only [abs_mul, abs_neg, abs_two]; ring
        _ ≤ 2 * (12 / 100 * 1) + 2 * (27 / 100 * 1) := by gcongr
        _ = 2 * (12 / 100) + 2 * (27 / 100) := by ring
    linarith
  have hPs : |Psfun R z C S| ≤ 912 / 1000 := by
    have a1 : |s2fs R z| ≤ 555 / 1000 := by
      rw [s2fs, abs_le]; constructor <;> nlinarith
    have a2 : |s2gs R z| ≤ 357 / 1000 := by
      have : |R ^ 4 - 5 + 4 * z ^ 2| ≤ 476 / 100 := by rw [abs_le]; constructor <;> nlinarith
      rw [s2gs, abs_div, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      calc |z| * |R ^ 4 - 5 + 4 * z ^ 2| / 4 ≤ 3 / 10 * (476 / 100) / 4 := by gcongr
        _ ≤ 357 / 1000 := by norm_num
    calc |Psfun R z C S| ≤ |s2fs R z * C| + |s2gs R z * S| := abs_add_le _ _
      _ = |s2fs R z| * |C| + |s2gs R z| * |S| := by rw [abs_mul, abs_mul]
      _ ≤ 555 / 1000 * 1 + 357 / 1000 * 1 := by gcongr
      _ = 912 / 1000 := by norm_num
  have hPz : |Pzfun R z C S| ≤ 1648 / 1000 := by
    have a1 : |sgz R z| ≤ 1048 / 1000 := by
      have b1 : |R ^ 2 - 1| ≤ 69 / 100 := by rw [abs_le]; constructor <;> nlinarith
      have b2 : |R ^ 2 - 5| ≤ 451 / 100 := by rw [abs_le]; constructor <;> nlinarith
      have : |(R ^ 2 - 1) * (R ^ 2 - 5) - 12 * z ^ 2| ≤ 69 / 100 * (451 / 100) + 108 / 100 := by
        calc |(R ^ 2 - 1) * (R ^ 2 - 5) - 12 * z ^ 2|
            ≤ |(R ^ 2 - 1) * (R ^ 2 - 5)| + |12 * z ^ 2| := abs_sub _ _
          _ ≤ 69 / 100 * (451 / 100) + 108 / 100 := by
            rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 12 * z ^ 2)]
            gcongr; linarith
      rw [sgz, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      calc |(R ^ 2 - 1) * (R ^ 2 - 5) - 12 * z ^ 2| / 4 ≤
          (69 / 100 * (451 / 100) + 108 / 100) / 4 := by gcongr
        _ ≤ 1048 / 1000 := by norm_num
    calc |Pzfun R z C S| ≤ |-2 * z * C| + |sgz R z * S| := abs_add_le _ _
      _ = 2 * (|z| * |C|) + |sgz R z| * |S| := by simp only [abs_mul, abs_neg, abs_two]; ring
      _ ≤ 2 * (3 / 10 * 1) + 1048 / 1000 * 1 := by gcongr
      _ = 1648 / 1000 := by norm_num
  have hnR : nRr R z C S ^ 2 ≤ (456 / 1000) ^ 2 * R ^ 2 := by
    have : |nRr R z C S| ≤ 456 / 1000 * R := by
      rw [nRr, eps, abs_mul, abs_mul, abs_mul, abs_of_pos hRp]
      calc |2| * |1 / 4| * R * |Psfun R z C S| ≤ 2 * (1 / 4) * R * (912 / 1000) := by
            rw [abs_two, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]; gcongr
        _ ≤ 456 / 1000 * R := by nlinarith
    rw [show (456 / 1000) ^ 2 * R ^ 2 = (456 / 1000 * R) ^ 2 by ring, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hnZ : nZr R z C S ^ 2 ≤ (412 / 1000) ^ 2 * R ^ 4 := by
    have : |nZr R z C S| ≤ 412 / 1000 * R ^ 2 := by
      rw [nZr, eps, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < R ^ 2)]
      calc |1 / 4| * R ^ 2 * |Pzfun R z C S| ≤ 1 / 4 * R ^ 2 * (1648 / 1000) := by
            rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]; gcongr
        _ = 412 / 1000 * R ^ 2 := by ring
    rw [show (412 / 1000) ^ 2 * R ^ 4 = (412 / 1000 * R ^ 2) ^ 2 by ring, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hD2 : Dfun R z C S ^ 2 ≤ (R ^ 2 + 195 / 1000) ^ 2 := by
    have h := abs_le.mp hD
    have h0 : 0 ≤ Dfun R z C S := by nlinarith
    exact pow_le_pow_left₀ h0 (by linarith) 2
  have hx : 49 / 100 ≤ R ^ 2 := by nlinarith
  have hR2 : R ^ 2 * Dfun R z C S ^ 2 ≤ R ^ 2 * (R ^ 2 + 195 / 1000) ^ 2 :=
    mul_le_mul_of_nonneg_left hD2 (by positivity)
  have hsum : qr R z C S ≤ (456 / 1000) ^ 2 * R ^ 2 + R ^ 2 * (R ^ 2 + 195 / 1000) ^ 2 +
      (412 / 1000) ^ 2 * R ^ 4 := by
    unfold qr; linarith
  have hpoly := qr_poly_bound hx
  rw [show R ^ 8 = (R ^ 2) ^ 4 by ring, show R ^ 4 = (R ^ 2) ^ 2 by ring] at *
  linarith

/-- **`|B| ≤ 3` in the closed tube `rt ≤ 3/10`** about the magnetic axis. -/
theorem norm_field_le {y : Space} (hy : rt y ≤ 3 / 10) : ‖field (1 / 4) y‖ ≤ 3 := by
  have hy' : rt y < 1 / 2 := by linarith
  have hyeq := eq_torPt hy'
  set r := rt y
  set α := θs y
  have hr0 : 0 ≤ r := rt_nonneg y
  have hc := abs_le.mp (Real.abs_cos_le_one α)
  have hs := abs_le.mp (Real.abs_sin_le_one α)
  have hR0 : 7 / 10 ≤ 1 + r * Real.cos α := by nlinarith
  have hR1 : 1 + r * Real.cos α ≤ 13 / 10 := by nlinarith
  have hz : |r * Real.sin α| ≤ 3 / 10 := by
    rw [abs_mul, abs_of_nonneg hr0]
    calc r * |Real.sin α| ≤ 3 / 10 * 1 := by gcongr; exact Real.abs_sin_le_one α
      _ = 3 / 10 := by ring
  set R := 1 + r * Real.cos α
  have hRpos : 0 < R := by linarith
  have hQ : Qf y = qr R (r * Real.sin α) (Real.cos (2 * φs y)) (Real.sin (2 * φs y)) / R ^ 8 := by
    conv_lhs => rw [hyeq, torPt]
    exact Qf_cylPt hRpos _ _
  have hq := qr_le hR0 hR1 hz (Real.abs_cos_le_one (2 * φs y)) (Real.abs_sin_le_one (2 * φs y))
  have hQle : Qf y ≤ 3 ^ 2 := by
    rw [hQ, div_le_iff₀ (by positivity)]; linarith
  rw [Qf] at hQle
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp hQle

/-- The closed tube `rt ≤ 3/10` lies in `muRegion λ` for `0 ≤ λ ≤ 1/4`. -/
theorem tube_subset_muRegion {lm : ℝ} (h0 : 0 ≤ lm) (h1 : lm ≤ 1 / 4) {y : Space}
    (hy : rt y ≤ 3 / 10) : y ∈ muRegion lm := by
  refine ⟨tube_subset_gcRegion hy, ?_⟩
  have := norm_field_le hy
  nlinarith [norm_nonneg (field (1 / 4) y)]

end PlasmaLean.Design.RationalStellaratorGC
