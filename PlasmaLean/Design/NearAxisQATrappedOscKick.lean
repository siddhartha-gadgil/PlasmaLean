/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedOscLegs

/-!
# The oscillatory kick of an exact-QA reference bounce: assembled enclosure

Companion to `notes/theory/trapped-alpha-status.md` §6. Model only: `exactQA`, vacuum Boozer
guiding-centre equations, orbits of `NearAxisQATrappedResonance.Setup` (start window
`ψ₀ ∈ [4.75, 5.79] T m²`, tip field `B_t = E/μ ∈ [5.4, 5.5] T`).

**Leaves and covers** (defined in `Design/NearAxisQATrappedOscCells`): `OscLeaf … a b c d` says
that there are oracle enclosures for which the leg checks `legAOk`, `legBOk` and the final check
`finalOk` pass on the index box `PBI a b × TBI c d`; `OscCover` is a binary subdivision of an index
box into leaves, and `OscCover.sound` gives the leaf data at every point of the box.
`finalOk_sound` turns the final check into real inequalities.

**Main results (conditional on a cover).**

* `exactQA_kick_osc_of_cover`: for every `Setup` orbit (`T ≥ 1.6 ms`) the bounce closes at a time
  `P ∈ [Pmin, Pmax] μs`, `ρ(P) = 0`, `(ψ, θ)(P) = (ψ, θ)(0)`, `sin Δ > 0` and
  `ι₀ Δ ∈ [DlS, DhS] · 2⁻³²` (`Δ = φ(P) − φ(0)`), and the normalised oscillatory kick integrals
  `Ĉ = ∫₀ᴾ A w cos 2(φ − φ₀)`, `Ŝ = ∫₀ᴾ A w sin 2(φ − φ₀)` satisfy `√(Ĉ² + Ŝ²) ≤ Kn sin Δ`;
* `reference_kick_osc_of_cover`: the same for the reference kick integrals
  `C = ∫₀ᴾ g cos 2(φ − φ₀)`, `S = ∫₀ᴾ g sin 2(φ − φ₀)` with `g = refAmp b₁`:
  `√(C² + S²) ≤ 2|b₁| q Kn |sin Δ|`, i.e. in flux units `√(C² + S²)/(q ι₀ |sin Δ|) ≤ 2|b₁| Kn/ι₀`.

The cover itself (the kernel checks) is in `Design/NearAxisQATrappedOscCover`.
-/
public section
noncomputable section

namespace PlasmaLean.Design.NearAxisQATrappedOsc
open PlasmaLean.Certificates.ValidatedQuadrature PlasmaLean.Design.NearAxisQATrappedCells
  PlasmaLean.Kinetic.Boozer PlasmaLean.Design.NearAxisQA PlasmaLean.Design.NearAxisQATrappedBounce
  PlasmaLean.Design.NearAxisQATrappedResonance PlasmaLean.Design.NearAxisQATrappedPeriodic
  FIvX Real Set

/-! ## The final check in real form -/

/-- The scaled magnitude bound `max(−lo, hi)` bounds `|x|` for `x` in a valid enclosure. -/
theorem abs_le_mag {I : FIv} {x : ℝ} (h : I.Mem x) (hok : I.ok = true) :
    |x| ≤ fxVal (max (-I.lo) I.hi) := by
  obtain ⟨h1, h2⟩ := h hok
  have hm1 : fxVal (-I.lo) ≤ fxVal (max (-I.lo) I.hi) := fxVal_le_of_le (le_max_left _ _)
  have hm2 : fxVal I.hi ≤ fxVal (max (-I.lo) I.hi) := fxVal_le_of_le (le_max_right _ _)
  have : fxVal (-I.lo) = -fxVal I.lo := by unfold fxVal; push_cast; ring
  rw [abs_le]; constructor <;> linarith

/-- **Real form of `finalOk`.** If `Ĉ ∈ Cin + Cout`, `Ŝ ∈ Sin + Sout`, `ι₀ Δ ∈ J2`,
`10⁶ P ∈ Tin + Tout` and `finalOk … Kn 1 Pmin Pmax DlS DhS` holds, then `sin Δ > 0`,
`√(Ĉ² + Ŝ²) ≤ Kn sin Δ`, `Pmin · 10⁻⁶ ≤ P ≤ Pmax · 10⁻⁶` and `fxVal DlS ≤ ι₀ Δ ≤ fxVal DhS`. -/
theorem finalOk_sound {Cin Sin Cout Sout J2 Tin Tout : FIv} {Kn Pmin Pmax DlS DhS : ℤ}
    (h : finalOk Cin Sin Cout Sout J2 Tin Tout Kn 1 Pmin Pmax DlS DhS = true) {Ch Sh Δ P : ℝ}
    (hC : (Cin.add Cout).Mem Ch) (hS : (Sin.add Sout).Mem Sh) (hΔ : J2.Mem (211 / 500 * Δ))
    (hP : (Tin.add Tout).Mem (10 ^ 6 * P)) :
    0 < sin Δ ∧ √(Ch ^ 2 + Sh ^ 2) ≤ Kn * sin Δ ∧ (Pmin : ℝ) / 10 ^ 6 ≤ P ∧
      P ≤ (Pmax : ℝ) / 10 ^ 6 ∧ fxVal DlS ≤ 211 / 500 * Δ ∧ 211 / 500 * Δ ≤ fxVal DhS := by
  simp only [finalOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hci, hsi⟩, hco⟩, hso⟩, hti⟩, hto⟩, hJok⟩, hKn⟩, hsok⟩, hs0⟩, hK⟩, hT⟩,
    hTx⟩, hDl⟩, hDh⟩ := h
  have hsin := (mem_cosSinC (z := Δ) (Φ := J2.mul (C 500 211)) (by
    have := FIv.mem_mul hΔ (mem_C (p := 500) (q := 211) (r := 500 / 211) (by norm_num))
    rwa [show 211 / 500 * Δ * (500 / 211) = Δ by ring] at this)).2
  obtain ⟨hs1, -⟩ := hsin hsok
  have hslo : 0 < fxVal (sinDI J2).lo := by rw [← fxVal_zero]; exact fxVal_lt_of_lt hs0
  have hsinpos : 0 < sin Δ := lt_of_lt_of_le hslo hs1
  obtain ⟨hP1, hP2⟩ := hP (by simp [FIv.add, hti, hto])
  obtain ⟨hΔ1, hΔ2⟩ := hΔ hJok
  have hsc : ∀ n : ℤ, fxVal (n * fxScale) = n := fun n => by
    unfold fxVal; push_cast; rw [mul_div_assoc, div_self fxScale_pos.ne', mul_one]
  refine ⟨hsinpos, ?_, ?_, ?_, (fxVal_le_of_le hDl).trans hΔ1, hΔ2.trans (fxVal_le_of_le hDh)⟩
  · -- the amplitude inequality
    have hCa := abs_le_mag hC (by simp [FIv.add, hci, hco])
    have hSa := abs_le_mag hS (by simp [FIv.add, hsi, hso])
    set cm := max (-(Cin.add Cout).lo) (Cin.add Cout).hi
    set sm := max (-(Sin.add Sout).lo) (Sin.add Sout).hi
    set sl := (sinDI J2).lo
    have hK' : ((cm * cm + sm * sm : ℤ) : ℝ) ≤ ((Kn * Kn * (sl * sl) : ℤ) : ℝ) := by
      exact_mod_cast (by linarith [hK] : cm * cm + sm * sm ≤ Kn * Kn * (sl * sl))
    have hS2 : (0 : ℝ) < (fxScale : ℝ) ^ 2 := pow_pos fxScale_pos 2
    have hreal : fxVal cm ^ 2 + fxVal sm ^ 2 ≤ ((Kn : ℝ) * fxVal sl) ^ 2 := by
      unfold fxVal
      rw [div_pow, div_pow, mul_div_assoc', div_pow, ← add_div, div_le_div_iff_of_pos_right hS2]
      push_cast at hK'
      nlinarith [hK']
    have h1 : Ch ^ 2 + Sh ^ 2 ≤ fxVal cm ^ 2 + fxVal sm ^ 2 := by
      have a := sq_le_sq' (abs_le.mp hCa).1 (abs_le.mp hCa).2
      have b := sq_le_sq' (abs_le.mp hSa).1 (abs_le.mp hSa).2
      linarith
    have hKn' : (0 : ℝ) ≤ Kn := by exact_mod_cast hKn
    have h2 : ((Kn : ℝ) * fxVal sl) ^ 2 ≤ ((Kn : ℝ) * sin Δ) ^ 2 := by
      apply pow_le_pow_left₀ (mul_nonneg hKn' hslo.le)
      exact mul_le_mul_of_nonneg_left hs1 hKn'
    calc √(Ch ^ 2 + Sh ^ 2) ≤ √(((Kn : ℝ) * sin Δ) ^ 2) :=
          Real.sqrt_le_sqrt (h1.trans (hreal.trans h2))
      _ = Kn * sin Δ := Real.sqrt_sq (mul_nonneg hKn' hsinpos.le)
  · have : (Pmin : ℝ) ≤ fxVal (Tin.add Tout).lo := by rw [← hsc]; exact fxVal_le_of_le hT
    rw [div_le_iff₀ (by norm_num)]
    linarith
  · have : fxVal (Tin.add Tout).hi ≤ (Pmax : ℝ) := by rw [← hsc]; exact fxVal_le_of_le hTx
    rw [le_div_iff₀ (by norm_num)]
    linarith

/-! ## The enclosure along a bounce -/

/-- **Oscillatory kick integrals of an exact-QA bounce, given a cover of the window.** For every
orbit of the setting `Setup` (start window, pitch window) on `[0, T]` with `T ≥ 1.6 ms`, the
bounce closes at a time `P` with `Pmin μs ≤ P ≤ 1.6 ms`, `ρ(P) = 0`, `ψ(P) = ψ(0)`,
`θ(P) = θ(0)`, `sin Δ > 0` for `Δ = φ(P) − φ(0)`, and the normalised kick integrals satisfy
`√(Ĉ² + Ŝ²) ≤ Kn sin Δ`, `Ĉ = ∫₀ᴾ A w cos 2(φ − φ₀)`, `Ŝ = ∫₀ᴾ A w sin 2(φ − φ₀)`. -/
theorem exactQA_kick_osc_of_cover {Kn Pmin Pmax DlS DhS : ℤ}
    (hcov : OscCover Kn Pmin Pmax DlS DhS 0 120 0 128)
    {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ} (S : Setup μ T ψ θ φ ρ) (hT : 2 * Lhalf ≤ T) :
    ∃ P : ℝ, 0 < P ∧ (Pmin : ℝ) / 10 ^ 6 ≤ P ∧ P ≤ (Pmax : ℝ) / 10 ^ 6 ∧ P ≤ 2 * Lhalf ∧
      ρ P = 0 ∧ ψ P = ψ 0 ∧ θ P = θ 0 ∧ 0 < sin (φ P - φ 0) ∧
      fxVal DlS ≤ 211 / 500 * (φ P - φ 0) ∧ 211 / 500 * (φ P - φ 0) ≤ fxVal DhS ∧
      √((∫ t in (0 : ℝ)..P, Setup.Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
          (20 / 57 * ψ t) * cos (2 * (φ t - φ 0))) ^ 2 +
        (∫ t in (0 : ℝ)..P, Setup.Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
          (20 / 57 * ψ t) * sin (2 * (φ t - φ 0))) ^ 2) ≤ Kn * sin (φ P - φ 0) := by
  have hψ0 : ψ 0 ∈ Icc (19 / 4 : ℝ) (47 / 8) := ⟨by linarith [S.psi0.1], by linarith [S.psi0.2]⟩
  obtain ⟨Mfi, Mfo, Mbi, mbi, Mbo, mbo, ci, co, -, -⟩ := precession_cert hψ0 S.Bt_mem
  obtain ⟨z₁, z₂, hz₁, hz₁₂, hz₂, hρz₁, hρz₂, hneg, hpos, hθ0, hθz₁, hθz₂, hψz₂, hθz₂'⟩ :=
    S.bounce_closes ci hT
  have hz₂T : z₂ ≤ T := hz₂.trans hT
  have hwin : OscAt Kn Pmin Pmax DlS DhS (ψ 0) (Eα / μ) := hcov.sound
    (by have := S.psi0; constructor <;> push_cast <;> linarith [this.1, this.2])
    (by have := S.Bt_mem; constructor <;> push_cast <;> linarith [this.1, this.2])
  obtain ⟨P, Tb, Θ0, Cin, Sin, J1, Tin, Cout, Sout, J2, Tout, hP, hTb, hA, hB, hF⟩ := hwin
  obtain ⟨hΘ, hθz₁eq, hC1, hS1, hJ1, hT1⟩ := S.inner_leg_osc hP hTb hA ci hz₁
    (hz₁₂.le.trans hz₂T) hρz₁ hneg hθ0 hθz₁
  obtain ⟨hC2, hS2, hJ2, hT2⟩ := S.outer_leg_osc hP hTb hB co hz₁ hz₁₂ hz₂T hρz₁ hρz₂ hpos
    hθz₁ hθz₂ hθz₂' hΘ hθz₁eq hJ1
  -- glue the two legs
  have hΦc : ContinuousOn (fun t => 2 * (φ t - φ 0)) (Icc 0 T) :=
    continuousOn_const.mul (S.cont_phi.sub continuousOn_const)
  have hGi : ∀ f : ℝ → ℝ, Continuous f → ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ T →
      IntervalIntegrable (fun t => Setup.Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
        (20 / 57 * ψ t) * f (2 * (φ t - φ 0))) MeasureTheory.volume u v := by
    intro f hf u v hu huv hv
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le huv]
    exact ((S.cont_Aw.mul (hf.comp_continuousOn hΦc))).mono (Icc_subset_Icc hu hv)
  have hsplit : ∀ f : ℝ → ℝ, Continuous f →
      (∫ t in (0 : ℝ)..z₂, Setup.Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
        (20 / 57 * ψ t) * f (2 * (φ t - φ 0))) =
      (∫ t in (0 : ℝ)..z₁, Setup.Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
        (20 / 57 * ψ t) * f (2 * (φ t - φ 0))) +
      ∫ t in z₁..z₂, Setup.Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
        (20 / 57 * ψ t) * f (2 * (φ t - φ 0)) := fun f hf =>
    (intervalIntegral.integral_add_adjacent_intervals
      (hGi f hf 0 z₁ le_rfl hz₁.le (hz₁₂.le.trans hz₂T))
      (hGi f hf z₁ z₂ hz₁.le hz₁₂.le hz₂T)).symm
  have hCt := FIv.mem_add hC1 hC2
  have hSt := FIv.mem_add hS1 hS2
  rw [← hsplit cos continuous_cos] at hCt
  rw [← hsplit sin continuous_sin] at hSt
  have hΔ : J2.Mem (211 / 500 * (φ z₂ - φ 0)) := by
    have hp := S.prec_eq le_rfl (hz₁.le.trans hz₁₂.le) hz₂T
    rw [hθz₂', sub_self, zero_add] at hp
    rw [hp]; exact hJ2
  have hTt : (Tin.add Tout).Mem (10 ^ 6 * z₂) := by
    have := FIv.mem_add hT1 hT2
    convert this using 1; ring
  obtain ⟨hs, hK, hPmin, hPmax, hD1, hD2⟩ := finalOk_sound hF hCt hSt hΔ hTt
  exact ⟨z₂, hz₁.trans hz₁₂, hPmin, hPmax, hz₂, hρz₂, hψz₂, hθz₂', hs, hD1, hD2, hK⟩

/-- Along an orbit of the start window the reference amplitude is `g = −2 b₁ q · A w`. -/
theorem refAmp_eq (b₁ μ : ℝ) (ψ θ φ ρ : ℝ → ℝ) (t : ℝ) :
    refAmp b₁ μ ψ θ ρ t = -(2 * b₁) * qα *
      (Setup.Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * (20 / 57 * ψ t)) := by
  have eB : along exactQA.B ψ θ φ t = Bf (ψ t) (θ t) := by
    simp only [along]; rw [exactQA_B_eq]; rfl
  have hq : (qα : ℝ) ≠ 0 := by norm_num [qα]
  have hm : (mα : ℝ) ≠ 0 := by norm_num [mα]
  unfold refAmp Setup.Afac; rw [eB]; field_simp; ring

/-- **Reference kick data with the oscillatory bound, given a cover.** For every exact-QA
reference orbit of the start window (`Setup`, `T ≥ 1.6 ms`) and every `b₁`, the bounce closes at
`P ∈ [Pmin μs, 1.6 ms]` with `sin Δ > 0` (`Δ = φ(P) − φ(0)`), the reference kick is
`C sin 2φ(0) + S cos 2φ(0)` with `C = ∫₀ᴾ g cos 2(φ − φ₀)`, `S = ∫₀ᴾ g sin 2(φ − φ₀)`,
`g = refAmp b₁`, and `√(C² + S²) ≤ 2 |b₁| q Kn sin Δ`. -/
theorem reference_kick_osc_of_cover {Kn Pmin Pmax DlS DhS : ℤ}
    (hcov : OscCover Kn Pmin Pmax DlS DhS 0 120 0 128)
    (b₁ : ℝ) {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ} (S : Setup μ T ψ θ φ ρ) (hT : 2 * Lhalf ≤ T) :
    ∃ P : ℝ, 0 < P ∧ (Pmin : ℝ) / 10 ^ 6 ≤ P ∧ P ≤ (Pmax : ℝ) / 10 ^ 6 ∧ P ≤ 2 * Lhalf ∧
      ρ P = 0 ∧ ψ P = ψ 0 ∧ θ P = θ 0 ∧ 0 < sin (φ P - φ 0) ∧
      fxVal DlS ≤ 211 / 500 * (φ P - φ 0) ∧ 211 / 500 * (φ P - φ 0) ≤ fxVal DhS ∧
      (∫ t in (0 : ℝ)..P, refAmp b₁ μ ψ θ ρ t * sin (2 * φ t)) =
        (∫ t in (0 : ℝ)..P, refAmp b₁ μ ψ θ ρ t * cos (2 * (φ t - φ 0))) * sin (2 * φ 0) +
          (∫ t in (0 : ℝ)..P, refAmp b₁ μ ψ θ ρ t * sin (2 * (φ t - φ 0))) * cos (2 * φ 0) ∧
      √((∫ t in (0 : ℝ)..P, refAmp b₁ μ ψ θ ρ t * cos (2 * (φ t - φ 0))) ^ 2 +
        (∫ t in (0 : ℝ)..P, refAmp b₁ μ ψ θ ρ t * sin (2 * (φ t - φ 0))) ^ 2) ≤
        2 * |b₁| * qα * Kn * sin (φ P - φ 0) := by
  obtain ⟨P, hP0, hPmin, hPmax, hPL, hρP, hψP, hθP, hs, hD1, hD2, hK⟩ :=
    exactQA_kick_osc_of_cover hcov S hT
  have hPT : P ≤ T := hPL.trans hT
  have hsub : Icc 0 P ⊆ Icc 0 T := Icc_subset_Icc le_rfl hPT
  have hu : uIcc 0 P = Icc 0 P := uIcc_of_le hP0.le
  have hΦc : ContinuousOn (fun t => 2 * (φ t - φ 0)) (Icc 0 T) :=
    continuousOn_const.mul (S.cont_phi.sub continuousOn_const)
  have hGi : ∀ f : ℝ → ℝ, Continuous f →
      IntervalIntegrable (fun t => Setup.Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
        (20 / 57 * ψ t) * f (2 * (φ t - φ 0))) MeasureTheory.volume 0 P := by
    intro f hf
    apply ContinuousOn.intervalIntegrable; rw [hu]
    exact ((S.cont_Aw.mul (hf.comp_continuousOn hΦc))).mono hsub
  have hconv : ∀ f : ℝ → ℝ,
      (∫ t in (0 : ℝ)..P, refAmp b₁ μ ψ θ ρ t * f (2 * (φ t - φ 0))) =
        -(2 * b₁) * qα * ∫ t in (0 : ℝ)..P,
          Setup.Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * (20 / 57 * ψ t) *
            f (2 * (φ t - φ 0)) := by
    intro f
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; rw [refAmp_eq b₁ μ ψ θ φ ρ t]; ring
  refine ⟨P, hP0, hPmin, hPmax, hPL, hρP, hψP, hθP, hs, hD1, hD2, ?_, ?_⟩
  · have e : ∀ t, refAmp b₁ μ ψ θ ρ t * sin (2 * φ t) =
        refAmp b₁ μ ψ θ ρ t * cos (2 * (φ t - φ 0)) * sin (2 * φ 0) +
          refAmp b₁ μ ψ θ ρ t * sin (2 * (φ t - φ 0)) * cos (2 * φ 0) := by
      intro t
      have : 2 * φ t = 2 * φ 0 + 2 * (φ t - φ 0) := by ring
      rw [this, sin_add]; ring
    have hI1 := (hGi cos continuous_cos).const_mul (-(2 * b₁) * qα)
    have hI2 := (hGi sin continuous_sin).const_mul (-(2 * b₁) * qα)
    have h1 : IntervalIntegrable (fun t => refAmp b₁ μ ψ θ ρ t * cos (2 * (φ t - φ 0)))
        MeasureTheory.volume 0 P := by
      refine hI1.congr ?_
      intro t _; simp only; rw [refAmp_eq b₁ μ ψ θ φ ρ t]; ring
    have h2 : IntervalIntegrable (fun t => refAmp b₁ μ ψ θ ρ t * sin (2 * (φ t - φ 0)))
        MeasureTheory.volume 0 P := by
      refine hI2.congr ?_
      intro t _; simp only; rw [refAmp_eq b₁ μ ψ θ φ ρ t]; ring
    simp_rw [e]
    rw [intervalIntegral.integral_add (h1.mul_const _) (h2.mul_const _),
      intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
  · rw [hconv cos, hconv sin]
    set X := ∫ t in (0 : ℝ)..P, Setup.Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
      (20 / 57 * ψ t) * cos (2 * (φ t - φ 0))
    set Y := ∫ t in (0 : ℝ)..P, Setup.Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
      (20 / 57 * ψ t) * sin (2 * (φ t - φ 0))
    have e : (-(2 * b₁) * qα * X) ^ 2 + (-(2 * b₁) * qα * Y) ^ 2 =
        (-(2 * b₁) * qα) ^ 2 * (X ^ 2 + Y ^ 2) := by ring
    rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
    have hq : (0 : ℝ) < qα := by norm_num [qα]
    rw [abs_mul, abs_neg, abs_mul, abs_of_pos hq, abs_two]
    have := mul_le_mul_of_nonneg_left hK (show (0 : ℝ) ≤ 2 * |b₁| * qα by positivity)
    linarith

end PlasmaLean.Design.NearAxisQATrappedOsc
