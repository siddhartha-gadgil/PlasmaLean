/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Contract.IrrationalTorus
public import PlasmaLean.Design.DommaschkKamLoopCurrent
public import PlasmaLean.Design.DommaschkKamQ16

/-!
# Embedded Dommaschk tori C and A

The exact rotation numbers are irrational. The smooth Dommaschk field off the axis,
the winding of each section, and the regularity of the exact profiles therefore imply
embeddedness. The results below retain the current and transform allowances on each
singleton and the nested pair. The Q-16 statement uses the same witnesses for
embeddedness, physical invariance, nesting, chart regularity and both defect bounds.

This is an on-demand module.
-/

@[expose] public section

noncomputable section

namespace PlasmaLean.Design.DommaschkKamEmbedded

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Contract WEll1Z2
open PlasmaLean.Forms PlasmaLean.Fields.VacuumBoozer
open DommaschkKamNested (NestedTori)
open DommaschkKamC (RofC ExactTorusC surfaceC)
open DommaschkKamA (ExactTorusA surfaceA)

local notation "Bdk" => DommaschkQA2R.field DommaschkQA2R.candidate
local notation "Vdk" => DommaschkQA2R.potential DommaschkQA2R.candidate

/-- Irrationality of the exact rotation number on torus C. -/
theorem irrational_iotaC : Irrational DommaschkKamDio.dkIotaC :=
  ((irrational_sqrt_five.natCast_add 85).div_natCast (m := 361) (by norm_num)).neg

/-- Irrationality of the exact rotation number on torus A. -/
theorem irrational_iotaA : Irrational DommaschkKamDio.dkIotaA :=
  ((irrational_sqrt_five.natCast_add 19).div_natCast (m := 89) (by norm_num)).neg

/-- Analytic Dommaschk profiles realizing an irrational poloidal transform give an embedded
torus. The regularity of the physical vector field follows from its vacuum law off the axis. -/
private theorem embedded_of_analytic {u z : FA} {ι : ℝ}
    (hi : IotaOnTorus Bdk (RofC u) (Zof z) ι) (hι : Irrational ι) (hu : Ana u) (hz : Ana z) :
    EmbeddedTorus (RofC u) (Zof z) := by
  obtain ⟨hT, _, _, _, hP⟩ := hi
  apply hT.embeddedTorus_of_irrational hP hι (DommaschkKamC.contDiff_RofC hu) (contDiff_Zof hz)
  intro θ φ
  have hx := DommaschkQA2R.poloidalLoop_mem_domain (z := Zof z) (hT.R_pos θ φ)
  exact (DommaschkQA2R.candidate_vacuum.contDiffOn.contDiffAt
    (DommaschkQA2R.candidate_vacuum.isOpen.mem_nhds hx)).of_le (by norm_num)

/-- The KAM surface C is embedded for every exact witness in its certificate. -/
theorem torusC_embedded {u z : FA} (h : ExactTorusC u z) : EmbeddedTorus (RofC u) (Zof z) :=
  embedded_of_analytic h.iotaOnTorus irrational_iotaC h.ana_u h.ana_z

/-- The KAM surface A is embedded for every exact witness in its certificate. -/
theorem torusA_embedded {u z : FA} (h : ExactTorusA u z) : EmbeddedTorus (RofC u) (Zof z) :=
  embedded_of_analytic h.iotaOnTorus irrational_iotaA h.ana_u h.ana_z

/-- The exact inner torus satisfies embedded C1 with its original singleton transform bound. -/
theorem dommaschkC_embedded_C1 {μ₀ : ℝ} (hμ : 0 < μ₀) :
    ∃ u z : FA, ExactTorusC u z ∧
      EmbeddedCurrentFreeTransform μ₀ Bdk {surfaceC u z} 0 (6 / 25) := by
  obtain ⟨u, z, h⟩ := DommaschkKamLoopCurrent.exists_exactTorusC
  refine ⟨u, z, h, DommaschkKamC.dommaschk_C1_of_exact h hμ, ?_⟩
  rintro s rfl
  exact torusC_embedded h

/-- The exact outer torus satisfies embedded C1 with its original singleton transform bound. -/
theorem dommaschkA_embedded_C1 {μ₀ : ℝ} (hμ : 0 < μ₀) :
    ∃ u z : FA, ExactTorusA u z ∧
      EmbeddedCurrentFreeTransform μ₀ Bdk {surfaceA u z} 0 (1193 / 5000) := by
  obtain ⟨u, z, h⟩ := DommaschkKamA.exists_exactTorusA
  refine ⟨u, z, h, DommaschkKamA.dommaschkA_C1_of_exact h hμ, ?_⟩
  rintro s rfl
  exact torusA_embedded h

private theorem ana_of_close {u u₀ : FA} {ρ μ : ℝ} (hρ : 0 < ρ) (hd : Bd ρ (u - u₀) μ)
    (h₀ : Ana u₀) : Ana u := by
  have hu : Ana (u - u₀) := ⟨ρ, μ, hρ, hd⟩
  simpa using hu.add h₀

/-- Embedded C1 on the very surfaces of the Q-16 certificate, retaining the sharp defect
constants, both Boozer hypotheses and both certified strip distances. -/
theorem dommaschk_Q16_embedded :
    ∃ (sC sA : SurfaceData) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      sC.iota = DommaschkKamDio.dkIotaC ∧ sA.iota = DommaschkKamDio.dkIotaA ∧
      IotaOnTorus Bdk sC.R sC.z sC.iota ∧ IotaOnTorus Bdk sA.R sA.z sA.iota ∧
      NestedTori sC.R sC.z sA.R sA.z R₀ z₀ ΘC ΘA ∧
      (1193 / 5000 : ℝ) ≤ |sC.iota| ∧ (1193 / 5000 : ℝ) ≤ |sA.iota| ∧
      (∀ μ₀ : ℝ, 0 < μ₀ → EmbeddedCurrentFreeTransform μ₀ Bdk {sC, sA} 0 (1193 / 5000)) ∧
      TorusQADefectLe Bdk sC.iota (cylTorus sC.R sC.z) (21 / 1000) ∧
      TorusQADefectLe Bdk sA.iota (cylTorus sA.R sA.z) (32 / 1000) ∧
      (∀ θ φ, (104259 / 100000 : ℝ) ≤ ‖Bdk (cylTorus sC.R sC.z θ φ)‖) ∧
      (∀ θ φ, (102656 / 100000 : ℝ) ≤ ‖Bdk (cylTorus sA.R sA.z θ φ)‖) ∧
      (∀ S : Finset (ℤ × ℤ), (∀ q ∈ S, OracleOffQA q) →
        oracleDefect 2 sC.iota (torusPot Vdk (cylTorus sC.R sC.z))
          (torusModB Bdk (cylTorus sC.R sC.z)) S ≤ (63 / 10000 : ℝ) * |sC.iota|) ∧
      (∀ S : Finset (ℤ × ℤ), (∀ q ∈ S, OracleOffQA q) →
        oracleDefect 2 sA.iota (torusPot Vdk (cylTorus sA.R sA.z))
          (torusModB Bdk (cylTorus sA.R sA.z)) S ≤ (90 / 10000 : ℝ) * |sA.iota|) ∧
      BoozerChartHyp 2 sC.iota (torusPot Vdk (cylTorus sC.R sC.z))
        (torusModB Bdk (cylTorus sC.R sC.z)) ∧
      BoozerChartHyp 2 sA.iota (torusPot Vdk (cylTorus sA.R sA.z))
        (torusModB Bdk (cylTorus sA.R sA.z)) ∧
      ∃ uC zC uA zA : FA, sC = surfaceC uC zC ∧ sA = surfaceA uA zA ∧
        Close (9 / 1400) DommaschkKamDio.dkIotaC uC zC DommaschkKamC.u₀C DommaschkKamC.z₀C
          ((1 / 10 ^ 12 : ℚ) : ℝ) ∧
        Close (9 / 1400) DommaschkKamDio.dkIotaA uA zA DommaschkKamA.u₀A DommaschkKamA.z₀A
          ((1 / 10 ^ 12 : ℚ) : ℝ) := by
  obtain ⟨sC, sA, R₀, z₀, ΘC, ΘA, eC, eA, iC, iA, hn, gC, gA, h1, tC, tA, bC, bA,
    dC, dA, chartC, chartA, uC, zC, uA, zA, esC, esA, closeC, closeA⟩ :=
    DommaschkKamQ16.dommaschk_Q16_chart
  subst sC
  subst sA
  have hr : (0 : ℝ) < 9 / 1400 := by norm_num
  have embC := embedded_of_analytic iC irrational_iotaC
    (ana_of_close hr closeC.du DommaschkKamC.ana_u₀C)
    (ana_of_close hr closeC.dz DommaschkKamC.ana_z₀C)
  have embA := embedded_of_analytic iA irrational_iotaA
    (ana_of_close hr closeA.du DommaschkKamA.ana_u₀A)
    (ana_of_close hr closeA.dz DommaschkKamA.ana_z₀A)
  refine ⟨_, _, R₀, z₀, ΘC, ΘA, eC, eA, iC, iA, hn, gC, gA, ?_, tC, tA, bC, bA,
    dC, dA, chartC, chartA, uC, zC, uA, zA, rfl, rfl, closeC, closeA⟩
  intro μ₀ hμ
  refine ⟨h1 μ₀ hμ, ?_⟩
  rintro s (rfl | rfl)
  · exact embC
  · exact embA

/-- The exact Dommaschk field has an embedded pair satisfying the established ray order,
zero current and the common transform bound. -/
theorem dommaschk_nested_embedded_C1 {μ₀ : ℝ} (hμ : 0 < μ₀) :
    ∃ (sC sA : SurfaceData) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      sC.iota = DommaschkKamDio.dkIotaC ∧ sA.iota = DommaschkKamDio.dkIotaA ∧
      EmbeddedCurrentFreeTransform μ₀ Bdk {sC, sA} 0 (1193 / 5000) ∧
      NestedTori sC.R sC.z sA.R sA.z R₀ z₀ ΘC ΘA := by
  obtain ⟨sC, sA, R₀, z₀, ΘC, ΘA, eC, eA, _, _, hn, _, _, h1, _⟩ := dommaschk_Q16_embedded
  exact ⟨sC, sA, R₀, z₀, ΘC, ΘA, eC, eA, h1 μ₀ hμ, hn⟩

/-- The nested embedded pair realizes the loop-current fixture. Starting with allowance one,
Stokes on the meridian half-space recovers zero current on each of the same two surfaces. -/
theorem dommaschk_nested_embedded_current_eq_zero {μ₀ : ℝ} (hμ : 0 < μ₀) :
    ∃ (sC sA : SurfaceData) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      sC.iota = DommaschkKamDio.dkIotaC ∧ sA.iota = DommaschkKamDio.dkIotaA ∧
      NestedTori sC.R sC.z sA.R sA.z R₀ z₀ ΘC ΘA ∧
      EmbeddedCurrentFreeTransform μ₀ Bdk {sC, sA} 1 (1193 / 5000) ∧
      EmbeddedCurrentFreeTransform μ₀ Bdk {sC, sA} 0 (1193 / 5000) ∧
      ∀ s ∈ ({sC, sA} : Set SurfaceData), s.current μ₀ Bdk = 0 := by
  obtain ⟨sC, sA, R₀, z₀, ΘC, ΘA, eC, eA, h0, hn⟩ := dommaschk_nested_embedded_C1 hμ
  have h1 := h0.mono zero_le_one le_rfl (by norm_num)
  exact ⟨sC, sA, R₀, z₀, ΘC, ΘA, eC, eA, hn, h1,
    ⟨DommaschkKamLoopCurrent.candidate_imax_zero h1.toCurrentFreeTransform, h1.embedded⟩,
    fun _ hs => DommaschkKamLoopCurrent.candidate_current_eq_zero h1.toCurrentFreeTransform hs⟩

/-- The uniform one-percent Q-16 tier holds on an embedded pair with the same witnesses
for current, transform, and ray ordering. -/
theorem dommaschk_Q16_strong_embedded :
    ∃ (sC sA : SurfaceData) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      sC.iota = DommaschkKamDio.dkIotaC ∧ sA.iota = DommaschkKamDio.dkIotaA ∧
      NestedTori sC.R sC.z sA.R sA.z R₀ z₀ ΘC ΘA ∧
      (∀ μ₀ : ℝ, 0 < μ₀ → EmbeddedCurrentFreeTransform μ₀ Bdk {sC, sA} 0 (1193 / 5000)) ∧
      ∀ s ∈ ({sC, sA} : Set SurfaceData), ∀ S : Finset (ℤ × ℤ), (∀ q ∈ S, OracleOffQA q) →
        oracleDefect 2 s.iota (torusPot Vdk (cylTorus s.R s.z))
          (torusModB Bdk (cylTorus s.R s.z)) S ≤ (1 / 100 : ℝ) * |s.iota| := by
  obtain ⟨sC, sA, R₀, z₀, ΘC, ΘA, eC, eA, _, _, hn, _, _, h1, _, _, _, _, dC, dA, _⟩ :=
    dommaschk_Q16_embedded
  refine ⟨sC, sA, R₀, z₀, ΘC, ΘA, eC, eA, hn, h1, ?_⟩
  rintro s (rfl | rfl) S hS
  · exact (dC S hS).trans (mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _))
  · exact (dA S hS).trans (mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _))

end PlasmaLean.Design.DommaschkKamEmbedded
