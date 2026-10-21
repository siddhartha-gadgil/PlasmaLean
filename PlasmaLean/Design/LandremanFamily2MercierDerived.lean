/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2MercierStable
public import PlasmaLean.Design.LandremanFamily2FluxLabels
public import PlasmaLean.Design.LandremanFamily2SignCert
public import PlasmaLean.Design.LandremanFamily2Coarea

/-!
# The Mercier-stable band of family 2 with all labels derived from the field

`LandremanFamily2MercierStable.family2_mercier_stable` certifies `D_Merc > 0` for the surface
data `family2Data`, whose flux labels `ψ_t, ψ_p`, volume `V` and current `I` were *defined* as
primitives of hand-derived one-dimensional integrals, and whose area element `JacR` was taken
from paper (3.18). This module removes that gap.

`family2DataPhys` builds the eight Mercier numbers from **physical** objects only:

* `ψ_t = Φ_t/2π`, `Φ_t` the flux of the actual field through the toroidal cross-section
  `ζ = 0` (`LandremanFamily2FluxLabels.torFlux`);
* `ψ_p = Φ_p/2π`, `Φ_p` the flux through the ribbon `χ = 0` from the magnetic axis
  (`polFlux`); `ι = dψ_p/dψ_t`;
* `V` = the Lebesgue volume of the plasma `{x ∈ R | ψ(x) ≤ k²/2}` (`plasma`);
* `I = μ₀ I_tor/2π`, `I_tor` the flux of the actual current `J = (∇ × B)/μ₀` through the
  cross-section `ζ = 0` (`torCurrent`);
* the area element `|det Dx|/k`, the actual Jacobian determinant (`fderiv`) of the coordinate
  map `(ψ, χ, ζ) ↦ x` (`dψ = k dk`), which is injective on the box and covers the plasma up to
  the null magnetic axis (`LandremanFamily2Coords`); by the coarea formula
  (`LandremanFamily2Coarea`) `JacR dχ dζ` is the surface measure `dS/|∇ψ|`;
* `μ₀ p'`, `B`, `J`, `∇ψ` as before (actual pressure, field, current, gradient).

`family2DataPhys_eq` proves `family2DataPhys = family2Data` on every surface `0 < k < 19/20`
(the labels agree on a neighbourhood, so all derivatives agree), and
**`family2_mercier_stable_derived`** restates the certified band `k ∈ [7/10, 9/10]`
(`λ = 200`, both signs `s_G`, every `μ₀ > 0`, `p_a`) for the physical data, together with the
identifications and the certified signs `ι' > 0` (shear) and `V'' > 0` (magnetic hill)
(`LandremanFamily2SignCert`).

What remains supplied: the general Mercier formula (Landreman–Jorge 2020, eq. (3.1)) itself,
and the choice of the cross-sections (`ζ = 0`, `χ = 0`) on which the fluxes are evaluated (by
`∇·B = 0` any other choice gives the same values, but that independence is not formalized).
-/

open scoped RealInnerProductSpace

public section
noncomputable section

namespace PlasmaLean.Design.LandremanFamily2MercierDerived

open Real Set MeasureTheory Filter Topology
open PlasmaLean.Fields PlasmaLean.Design.LandremanFamily2
open PlasmaLean.Design.LandremanFamily2Surface PlasmaLean.Design.LandremanFamily2Rotated
open PlasmaLean.Design.LandremanFamily2Coords PlasmaLean.Design.LandremanFamily2Labels
open PlasmaLean.Design.LandremanFamily2FluxLabels PlasmaLean.Design.LandremanFamily2MercierData
open PlasmaLean.Design.LandremanFamily2Quad PlasmaLean.Stability.MercierGeneral

/-! ## The physical labels -/

/-- Toroidal-flux label `ψ_t(k) = Φ_t(k)/2π` (flux through the cross-section `ζ = 0`). -/
@[expose] def torN (lam k : ℝ) : ℝ := torFlux lam k / (2 * π)

/-- Poloidal-flux label `ψ_p(k) = Φ_p(k)/2π` (flux through the ribbon `χ = 0`). -/
@[expose] def polN (lam k : ℝ) : ℝ := polFlux lam k / (2 * π)

/-- Lebesgue volume of the plasma `{x ∈ R | ψ(x) ≤ k²/2}`. -/
@[expose] def volN (lam k : ℝ) : ℝ := (volume (plasma lam k)).toReal

/-- Boozer current `I(k) = μ₀ I_tor(k)/2π` (current through the cross-section `ζ = 0`). -/
@[expose] def curN (μ₀ lam k : ℝ) : ℝ := μ₀ * torCurrent μ₀ lam k / (2 * π)

/-- Rotational transform `ι = dψ_p/dψ_t`. -/
@[expose] def iotaN (lam k : ℝ) : ℝ := deriv (polN lam) k / deriv (torN lam) k

/-- The area element: the actual Jacobian determinant of `(ψ, χ, ζ) ↦ x`, `|det Dx|/k`. -/
@[expose] def areaN (lam k χ ζ : ℝ) : ℝ := |(fderiv ℝ (coordMap lam) (pt k χ ζ)).det| / k

/-- `dψ_t/dψ`. -/
@[expose] def tpN (lam k : ℝ) : ℝ := deriv (torN lam) k / k

/-- The surface weight `|det Dx|/(k ψ_t'³ |∇ψ|²)`. -/
@[expose] def wSurfN (lam k χ ζ : ℝ) : ℝ :=
  areaN lam k χ ζ / (tpN lam k ^ 3 * ‖gradPsi (1 / 4) 4 lam (surfPt (1 / 4) 4 lam k χ ζ)‖ ^ 2)

/-- `I' = dI/dψ_t`. -/
@[expose] def IprimeN (μ₀ lam k : ℝ) : ℝ := deriv (curN μ₀ lam) k / deriv (torN lam) k

/-- `Ξ = μ₀ J - I' B`. -/
@[expose] def XiN (μ₀ lam k χ ζ : ℝ) : Space :=
  μ₀ • current μ₀ (1 / 4) 4 lam (surfPt (1 / 4) 4 lam k χ ζ) -
    IprimeN μ₀ lam k • field (1 / 4) 4 lam (surfPt (1 / 4) 4 lam k χ ζ)

/-- `∫ B² dS/|∇ψ_t|³` with the physical area element. -/
@[expose] def intB2N (lam k : ℝ) : ℝ :=
  ∫ ζ in (-π)..π, ∫ χ in (-π)..π,
    ‖field (1 / 4) 4 lam (surfPt (1 / 4) 4 lam k χ ζ)‖ ^ 2 * wSurfN lam k χ ζ

/-- `∫ B·Ξ dS/|∇ψ_t|³` with the physical area element. -/
@[expose] def intBXiN (μ₀ lam k : ℝ) : ℝ :=
  ∫ ζ in (-π)..π, ∫ χ in (-π)..π,
    ⟪field (1 / 4) 4 lam (surfPt (1 / 4) 4 lam k χ ζ), XiN μ₀ lam k χ ζ⟫ * wSurfN lam k χ ζ

/-- `∫ |Ξ|² dS/|∇ψ_t|³` with the physical area element. -/
@[expose] def intXi2N (μ₀ lam k : ℝ) : ℝ :=
  ∫ ζ in (-π)..π, ∫ χ in (-π)..π, ‖XiN μ₀ lam k χ ζ‖ ^ 2 * wSurfN lam k χ ζ

/-- `ι' = dι/dψ_t`. -/
@[expose] def iotaPrimeN (lam k : ℝ) : ℝ := deriv (iotaN lam) k / deriv (torN lam) k

/-- `μ₀ p' = μ₀ dp/dψ_t` (actual pressure). -/
@[expose] def muPprimeN (μ₀ pa lam k : ℝ) : ℝ :=
  deriv (fun κ => μ₀ * pressure μ₀ pa (1 / 4) 4 lam (surfPt (1 / 4) 4 lam κ 0 0)) k /
    deriv (torN lam) k

/-- `V'' = d²V/dψ_t²` of the Lebesgue volume. -/
@[expose] def VppN (lam k : ℝ) : ℝ :=
  deriv (fun κ => deriv (volN lam) κ / deriv (torN lam) κ) k / deriv (torN lam) k

/-- **The Mercier surface data of family 2 from physical quantities only.** -/
@[expose] def family2DataPhys (μ₀ pa lam sG k : ℝ) : MercierSurfaceData where
  sG := sG
  sψ := 1
  iotaPrime := iotaPrimeN lam k
  muPprime := muPprimeN μ₀ pa lam k
  Vpp := VppN lam k
  intBXi := intBXiN μ₀ lam k
  intXi2 := intXi2N μ₀ lam k
  intB2 := intB2N lam k

/-! ## Identification with `family2Data` -/

section Ident
variable {lam k : ℝ}

/-- The open range of surfaces. -/
theorem Ioo_nhds (hk0 : 0 < k) (hk1 : k < 19 / 20) : Ioo (0 : ℝ) (19 / 20) ∈ 𝓝 k :=
  Ioo_mem_nhds hk0 hk1

/-- `ψ_t = psiT` on `(0, 19/20)`. -/
theorem torN_eq (hl : 0 < lam) {κ : ℝ} (hκ : κ ∈ Ioo (0 : ℝ) (19 / 20)) :
    torN lam κ = psiT lam (1 / 4) 4 κ := by
  rw [torN, torFlux_eq hl hκ.1.le hκ.2]; field_simp

/-- `ψ_p = psiP` on `(0, 19/20)`. -/
theorem polN_eq (hl : 0 < lam) {κ : ℝ} (hκ : κ ∈ Ioo (0 : ℝ) (19 / 20)) :
    polN lam κ = psiP lam (1 / 4) κ := by
  rw [polN, polFlux_eq hl hκ.1.le hκ.2]; field_simp

/-- `V = volK` on `(0, 19/20)`. -/
theorem volN_eq (hl : 0 < lam) {κ : ℝ} (hκ : κ ∈ Ioo (0 : ℝ) (19 / 20)) :
    volN lam κ = volK lam (1 / 4) κ := volumeReal_plasma hl hκ.1.le hκ.2

/-- `I = curK` on `(0, 19/20)`. -/
theorem curN_eq (hl : 0 < lam) {μ₀ : ℝ} (hμ : μ₀ ≠ 0) {κ : ℝ} (hκ : κ ∈ Ioo (0 : ℝ) (19 / 20)) :
    curN μ₀ lam κ = curK lam (1 / 4) 4 κ := torCurrent_eq hl hμ hκ.1.le hκ.2

/-- Derivatives of the toroidal-flux label agree on `(0, 19/20)`. -/
theorem deriv_torN (hl : 0 < lam) {κ : ℝ} (hκ : κ ∈ Ioo (0 : ℝ) (19 / 20)) :
    deriv (torN lam) κ = deriv (psiT lam (1 / 4) 4) κ :=
  Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (Ioo_nhds hκ.1 hκ.2)
    fun _ h => torN_eq hl h)

/-- Derivatives of the poloidal-flux label agree on `(0, 19/20)`. -/
theorem deriv_polN (hl : 0 < lam) {κ : ℝ} (hκ : κ ∈ Ioo (0 : ℝ) (19 / 20)) :
    deriv (polN lam) κ = deriv (psiP lam (1 / 4)) κ :=
  Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (Ioo_nhds hκ.1 hκ.2)
    fun _ h => polN_eq hl h)

/-- Derivatives of the volume agree on `(0, 19/20)`. -/
theorem deriv_volN (hl : 0 < lam) {κ : ℝ} (hκ : κ ∈ Ioo (0 : ℝ) (19 / 20)) :
    deriv (volN lam) κ = deriv (volK lam (1 / 4)) κ :=
  Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (Ioo_nhds hκ.1 hκ.2)
    fun _ h => volN_eq hl h)

/-- Derivatives of the current agree on `(0, 19/20)`. -/
theorem deriv_curN (hl : 0 < lam) {μ₀ : ℝ} (hμ : μ₀ ≠ 0) {κ : ℝ}
    (hκ : κ ∈ Ioo (0 : ℝ) (19 / 20)) :
    deriv (curN μ₀ lam) κ = deriv (curK lam (1 / 4) 4) κ :=
  Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (Ioo_nhds hκ.1 hκ.2)
    fun _ h => curN_eq hl hμ h)

/-- **The area element is the Jacobian `JacR`** (paper (3.18) derived): `|det Dx|/k = JacR`. -/
theorem areaN_eq (hl : 0 < lam) (hk0 : 0 < k) (hk1 : k < 19 / 20) (χ ζ : ℝ) :
    areaN lam k χ ζ = JacR lam k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ))
      (Real.cos (2 * ζ)) := by
  have hg : Good (pt k χ ζ) := ⟨by simpa using hk0, by simpa using hk1.le⟩
  rw [areaN, (hasFDerivAt_coordMap (lam := lam) hg).fderiv,
    coordDeriv_det hl hg (by simpa using hk1),
    abs_of_pos (mul_pos hg.1 (JacP_pos hl hg))]
  simp only [pt_0]
  rw [mul_div_cancel_left₀ _ hk0.ne']
  simp [JacP]

/-- The rotational transform agrees on `(0, 19/20)`. -/
theorem iotaN_eq (hl : 0 < lam) {κ : ℝ} (hκ : κ ∈ Ioo (0 : ℝ) (19 / 20)) :
    iotaN lam κ = iotaK lam (1 / 4) 4 κ := by
  rw [iotaN, iotaK, deriv_polN hl hκ, deriv_torN hl hκ]

/-- **`family2DataPhys = family2Data`** on every surface `0 < k < 19/20` (`λ > 0`, `μ₀ ≠ 0`). -/
theorem family2DataPhys_eq (hl : 0 < lam) {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (pa sG : ℝ) (hk0 : 0 < k)
    (hk1 : k < 19 / 20) : family2DataPhys μ₀ pa lam sG k = family2Data μ₀ pa lam sG k := by
  have hk : k ∈ Ioo (0 : ℝ) (19 / 20) := ⟨hk0, hk1⟩
  have hnb := Ioo_nhds hk0 hk1
  have htp : tpN lam k = tpK lam k := by rw [tpN, tpK, deriv_torN hl hk]
  have hw : ∀ χ ζ, wSurfN lam k χ ζ = wSurf lam k χ ζ := fun χ ζ => by
    rw [wSurfN, wSurf, htp, areaN_eq hl hk0 hk1]
  have hI : IprimeN μ₀ lam k = IprimeK lam k := by
    rw [IprimeN, IprimeK, deriv_curN hl hμ hk, deriv_torN hl hk]
  have hXi : ∀ χ ζ, XiN μ₀ lam k χ ζ = XiS μ₀ lam k χ ζ := fun χ ζ => by
    rw [XiN, XiS, hI]
  have hio : iotaPrimeN lam k = iotaPrimeK lam k := by
    rw [iotaPrimeN, iotaPrimeK, deriv_torN hl hk]
    congr 1
    exact Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem hnb fun _ h => iotaN_eq hl h)
  have hmu : muPprimeN μ₀ pa lam k = muPprimeK μ₀ pa lam k := by
    rw [muPprimeN, muPprimeK, deriv_torN hl hk]
  have hV : VppN lam k = VppK lam k := by
    rw [VppN, VppK, deriv_torN hl hk]
    congr 1
    refine Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem hnb fun κ h => ?_)
    simp only [deriv_volN hl h, deriv_torN hl h]
  have hB2 : intB2N lam k = intB2K lam k := by
    simp only [intB2N, intB2K, hw]
  have hBX : intBXiN μ₀ lam k = intBXiK μ₀ lam k := by
    simp only [intBXiN, intBXiK, hw, hXi]
  have hX2 : intXi2N μ₀ lam k = intXi2K μ₀ lam k := by
    simp only [intXi2N, intXi2K, hw, hXi]
  simp only [family2DataPhys, family2Data, hio, hmu, hV, hB2, hBX, hX2]

end Ident

/-! ## The derived stable band -/

/-- **Family 2 (`ε = 1/4`, `S = 4`, `λ = 200`) is Mercier stable on every flux surface
`ψ = k²/2`, `k ∈ [7/10, 9/10]`, with every label derived from the field.** For every `μ₀ > 0`,
`p_a`, `s_G = ±1`:

1. the labels of `family2Data` are the physical ones: `psiT = Φ_t/2π` (toroidal flux through
   `ζ = 0`), `psiP = Φ_p/2π` (poloidal flux through the ribbon `χ = 0`), `volK` = Lebesgue
   volume of the plasma `{x ∈ R | ψ ≤ k²/2}`, `curK = μ₀ I_tor/2π` (current through `ζ = 0`);
2. the area element `JacR` is the actual Jacobian `|det Dx|/k` of `(ψ, χ, ζ) ↦ x`, and
   `JacR dχ dζ` is the coarea measure `dS/|∇ψ|`: `d/dψ ∫_{ψ' ≤ ψ} f dx = ∫∫ f JacR dζ dχ` for
   every continuous `f`;
3. the physical Mercier data equal `family2Data`, and are Mercier stable (`D_Merc > 0`);
4. certified signs: `ι' > 0` (shear) and `V'' > 0` (magnetic hill), for the physical labels.

The Mercier formula itself (Landreman–Jorge 2020, eq. (3.1)) remains supplied. -/
theorem family2_mercier_stable_derived {μ₀ : ℝ} (hμ : 0 < μ₀) (pa : ℝ) {sG : ℝ}
    (hsG : sG = 1 ∨ sG = -1) {k : ℝ} (hk : k ∈ Icc (7 / 10 : ℝ) (9 / 10)) :
    psiT 200 (1 / 4) 4 k = torFlux 200 k / (2 * π) ∧
    psiP 200 (1 / 4) k = polFlux 200 k / (2 * π) ∧
    volK 200 (1 / 4) k = (volume (plasma 200 k)).toReal ∧
    curK 200 (1 / 4) 4 k = μ₀ * torCurrent μ₀ 200 k / (2 * π) ∧
    (∀ χ ζ, JacR 200 k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ)) =
      |(fderiv ℝ (coordMap 200) (pt k χ ζ)).det| / k) ∧
    (∀ f : Space → ℝ, Continuous f →
      HasDerivAt (fun ψ => ∫ x in LandremanFamily2Coarea.plasmaPsi 200 ψ, f x)
        (∫ χ in (-π)..π, ∫ ζ in (-π)..π, f (surfPt (1 / 4) 4 200 k χ ζ) *
          JacR 200 k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ))) (k ^ 2 / 2)) ∧
    family2DataPhys μ₀ pa 200 sG k = family2Data μ₀ pa 200 sG k ∧
    MercierStable (family2DataPhys μ₀ pa 200 sG k) ∧
    0 < iotaPrimeN 200 k ∧ 0 < VppN 200 k := by
  have hl : (0 : ℝ) < 200 := by norm_num
  have hk0 : 0 < k := by linarith [hk.1]
  have hk1 : k < 19 / 20 := by linarith [hk.2]
  have hkI : k ∈ Ioo (0 : ℝ) (19 / 20) := ⟨hk0, hk1⟩
  have hD := family2DataPhys_eq hl hμ.ne' pa sG hk0 hk1
  have hsh := LandremanFamily2SignCert.family2_shear_hill hk
  have hio : iotaPrimeN 200 k = iotaPrimeK 200 k := by
    have := congrArg MercierSurfaceData.iotaPrime hD
    simpa [family2DataPhys, family2Data] using this
  have hV : VppN 200 k = VppK 200 k := by
    have := congrArg MercierSurfaceData.Vpp hD
    simpa [family2DataPhys, family2Data] using this
  have hco : ∀ f : Space → ℝ, Continuous f →
      HasDerivAt (fun ψ => ∫ x in LandremanFamily2Coarea.plasmaPsi 200 ψ, f x)
        (∫ χ in (-π)..π, ∫ ζ in (-π)..π, f (surfPt (1 / 4) 4 200 k χ ζ) *
          JacR 200 k (Real.sin χ) (Real.cos χ) (Real.sin (2 * ζ)) (Real.cos (2 * ζ)))
        (k ^ 2 / 2) := fun f hf => by
    have h := LandremanFamily2Coarea.hasDerivAt_integral_plasmaPsi hl hf (ψ := k ^ 2 / 2)
      ⟨by positivity, by nlinarith [hk.2]⟩
    rwa [show √(2 * (k ^ 2 / 2)) = k by
      rw [show 2 * (k ^ 2 / 2) = k ^ 2 by ring, Real.sqrt_sq hk0.le]] at h
  refine ⟨(torN_eq hl hkI).symm, (polN_eq hl hkI).symm, (volN_eq hl hkI).symm,
    (curN_eq hl hμ.ne' hkI).symm, fun χ ζ => (areaN_eq hl hk0 hk1 χ ζ).symm, hco, hD, ?_, ?_, ?_⟩
  · rw [hD]; exact LandremanFamily2Cert.family2_mercier_stable hμ pa hsG hk
  · rw [hio]; exact hsh.1
  · rw [hV]; exact hsh.2

/-! ## Sanity checks -/

/-- Degenerate case: the plasma `ψ ≤ 0` (the magnetic axis) has volume zero. -/
theorem volume_plasma_zero {lam : ℝ} (hl : 0 < lam) : volume (plasma lam 0) = 0 := by
  rw [volume_plasma hl le_rfl (by norm_num), volK, intervalIntegral.integral_same,
    ENNReal.ofReal_zero]

/-- At `k = 0` the coordinate point is the magnetic axis (paper (3.20)). -/
theorem coordMap_k_zero (lam χ ζ : ℝ) : coordMap lam (pt 0 χ ζ) = axis (1 / 4) 4 ζ := by
  have h : coordMap lam (pt 0 χ ζ) = surfPt (1 / 4) 4 lam 0 χ ζ := by
    simp only [coordMap, pt_0, pt_1, pt_2]
  rw [h, surfPt_k_zero]

/-- Non-degeneracy: the toroidal flux through every surface `0 < k₀ < 19/20` is positive. -/
theorem torFlux_pos {lam k₀ : ℝ} (hl : 0 < lam) (hk0 : 0 < k₀) (hk₀ : k₀ < 19 / 20) :
    0 < torFlux lam k₀ := by
  rw [torFlux_eq hl hk0.le hk₀, psiT]
  have : 0 < ∫ κ in (0 : ℝ)..k₀, κ * F1 (1 / 4) 4 κ / (4 * π * lam) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun x hx => ?_) hk0
    · refine ContinuousOn.intervalIntegrable ?_
      refine ((continuousOn_id.mul (continuousOn_F1 (by norm_num))).div_const _).mono ?_
      intro x hx
      rw [uIcc_of_le hk0.le] at hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · have := F1_pos (S := 4) (by norm_num : (1 / 4 : ℝ) ≠ 0)
        (⟨by linarith [hx.1], by linarith [hx.2]⟩ : x ∈ Ioo (-1 : ℝ) 1)
      have := hx.1
      positivity
  positivity

end PlasmaLean.Design.LandremanFamily2MercierDerived
