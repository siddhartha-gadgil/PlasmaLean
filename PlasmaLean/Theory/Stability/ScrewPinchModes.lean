/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Stability.Newcomb
public import PlasmaLean.Theory.Equilibrium.ScrewPinch

/-!
# Newcomb's mode-by-mode ideal-MHD energy for the screw pinch

For a periodic screw pinch (length `2πR₀`, wavenumber `k = n/R₀`, poloidal number `m`),
Newcomb (1960) minimized the ideal-MHD energy `δW` over the two tangential displacement
components for a fixed radial displacement `ξ(r)` of the mode `exp i(mθ + kz)`. The
result is the one-dimensional form `∫₀ᵃ (f ξ'² + g ξ²) dr` (up to a positive factor and a
fixed-boundary surface term which vanishes for a conducting wall at the plasma edge).

**Source-extracted coefficients (supplied, not derived here).** We use the form printed as
Eq. (2) of A. S. Glasser, A. H. Glasser, R. Conlin, E. Kolemen, *An ideal MHD δW stability
analysis that bypasses the Newcomb equation*, Phys. Plasmas 27, 022114 (2020), after
Newcomb, Ann. Phys. 10, 232 (1960), and Freidberg, *Ideal MHD* (2014), screw-pinch
chapter. With `μ² = m² + k² r²`, `b = Bθ/r` and the field-line bending factor
`F = k Bz + m b = k·B`, in SI units (`μ₀ p'` in T²/m):

* `f = r³ F² / μ²`,
* `g = 2 k² r² μ₀ p' / μ² + (μ² - 1) r F² / μ² + 2 k² r³ (k² Bz² - m² b²) / μ⁴`.

`coefF_textbook`, `coefG_textbook` show these agree, for `r ≠ 0`, with Freidberg's
`f = r F²/k₀²`, `g = 2k²μ₀p'/k₀² + ((k₀²r² - 1)/(k₀²r²)) r F² + 2k²(k²Bz² - m²Bθ²/r²)/(r k₀⁴)`,
`k₀² = k² + m²/r²`. Writing the profiles through `b = Bθ/r` makes the coefficients
continuous up to the magnetic axis. The 3-D reduction itself is the hypothesis interface
`NewcombReduction`; no axiom is introduced.

**Checks of the extraction.**

* Suydam limit (`suydam_limit_G`, `suydam_limit_shear`, `suydam_limit_weight`): at a
  resonant surface `F = 0` the coefficient `g` equals ScrewPinch.lean's `localG c p'` and
  `r³ F'² / μ²` equals `localF μ₀ c …` with `c = μ₀ k² r²/μ²`, and this weight is
  `μ₀ Bθ²/(Bθ² + Bz²)`: exactly the documented Suydam weight `Bθ²/B²` (μ₀ normalization).
* Uniform vacuum field (`uniform_vacuum_stable`): `Bθ = 0`, `p' = 0` gives `g ≥ 0`, so
  every mode with `m² ≥ 1` is stable.
* `k = 0` (`zero_k_stable`) and the `(m, k) ↦ (-m, -k)` symmetry (`modeStable_neg`).

**Stability notion.** `ModeStable μ₀ a m k p' Bz b`: the reduced energy is nonnegative for
every C¹ radial displacement on `[0, a]` with `ξ(a) = 0` (conducting wall at the plasma
edge, fixed boundary). No condition at the axis is imposed, which is a larger class than
Newcomb's admissible one (`ξ(0) = 0` for `|m| ≥ 2`), so the statement is stronger. The
`m = 0` (sausage) mode is excluded throughout (`m² ≥ 1`): its reduction involves plasma
compressibility and is not covered by this formula.

**Certificates.** `picone_lower` is the Picone argument with lower-bound coefficients
`fL ≤ f`, `gL ≤ g` and a free axis value (`φ(x₀) = 0` replaces `ξ(x₀) = 0`), the form used
with exact polynomial checks in `PlasmaLean.Design.ScrewPinchModes`.

Scope: fixed-boundary ideal MHD for one cylindrical mode at a time; no free-boundary,
resistive, kinetic or toroidal effects, and the full-spectrum statement needs every
`(m, n)` (see the design file for what is covered).
-/
public section

noncomputable section
namespace PlasmaLean.Stability.ScrewPinchModes
open Set intervalIntegral PlasmaLean.Equilibrium.ScrewPinch

/-- `μ² = m² + k² r²`. -/
@[expose] def muSq (m k r : ℝ) : ℝ := m ^ 2 + k ^ 2 * r ^ 2

/-- Field-line bending factor `F = k Bz + m b` with `b = Bθ / r`. -/
@[expose] def kpar (m k : ℝ) (Bz b : ℝ → ℝ) (r : ℝ) : ℝ := k * Bz r + m * b r

/-- Newcomb's coefficient `f = r³ F² / μ²`. -/
@[expose] def coefF (m k : ℝ) (Bz b : ℝ → ℝ) (r : ℝ) : ℝ :=
  r ^ 3 * kpar m k Bz b r ^ 2 / muSq m k r

/-- Newcomb's coefficient `g` (see the module documentation). -/
@[expose] def coefG (μ₀ m k : ℝ) (p' Bz b : ℝ → ℝ) (r : ℝ) : ℝ :=
  2 * k ^ 2 * r ^ 2 * (μ₀ * p' r) / muSq m k r +
    (muSq m k r - 1) * r * kpar m k Bz b r ^ 2 / muSq m k r +
    2 * k ^ 2 * r ^ 3 * (k ^ 2 * Bz r ^ 2 - m ^ 2 * b r ^ 2) / muSq m k r ^ 2

/-- Fixed-boundary stability of the `(m, k)` mode in Newcomb's reduced form. -/
@[expose] def ModeStable (μ₀ a m k : ℝ) (p' Bz b : ℝ → ℝ) : Prop :=
  ∀ ξ ξ' : ℝ → ℝ, C1On ξ ξ' 0 a → ξ a = 0 →
    0 ≤ newcombForm (coefF m k Bz b) (coefG μ₀ m k p' Bz b) 0 a ξ ξ'

/-- `μ² > 0` for a nonzero poloidal number. -/
theorem muSq_pos {m : ℝ} (hm : m ≠ 0) (k r : ℝ) : 0 < muSq m k r := by
  unfold muSq; positivity

/-- `μ² ≥ 1` when `m² ≥ 1`. -/
theorem one_le_muSq {m : ℝ} (hm : 1 ≤ m ^ 2) (k r : ℝ) : 1 ≤ muSq m k r := by
  unfold muSq; nlinarith [sq_nonneg (k * r)]

/-- `f ≥ 0` on `r ≥ 0`. -/
theorem coefF_nonneg {m k r : ℝ} (hm : m ≠ 0) (Bz b : ℝ → ℝ) (hr : 0 ≤ r) :
    0 ≤ coefF m k Bz b r := by
  have := muSq_pos hm k r
  unfold coefF; positivity

/-- Agreement with Freidberg's form of `f` away from the axis. -/
theorem coefF_textbook {m k r : ℝ} (hm : m ≠ 0) (hr : r ≠ 0) (Bz Bθ : ℝ → ℝ) :
    coefF m k Bz (fun s => Bθ s / s) r =
      r * (k * Bz r + m * Bθ r / r) ^ 2 / (k ^ 2 + m ^ 2 / r ^ 2) := by
  have hK : k ^ 2 * r ^ 2 + m ^ 2 ≠ 0 := by positivity
  unfold coefF kpar muSq
  field_simp
  ring

/-- Agreement with Freidberg's form of `g` away from the axis. -/
theorem coefG_textbook {μ₀ m k r : ℝ} (hm : m ≠ 0) (hr : r ≠ 0) (p' Bz Bθ : ℝ → ℝ) :
    coefG μ₀ m k p' Bz (fun s => Bθ s / s) r =
      2 * k ^ 2 * (μ₀ * p' r) / (k ^ 2 + m ^ 2 / r ^ 2) +
      ((k ^ 2 + m ^ 2 / r ^ 2) * r ^ 2 - 1) / ((k ^ 2 + m ^ 2 / r ^ 2) * r ^ 2) *
        r * (k * Bz r + m * Bθ r / r) ^ 2 +
      2 * k ^ 2 / (r * (k ^ 2 + m ^ 2 / r ^ 2) ^ 2) *
        (k ^ 2 * Bz r ^ 2 - m ^ 2 * Bθ r ^ 2 / r ^ 2) := by
  have hK : k ^ 2 * r ^ 2 + m ^ 2 ≠ 0 := by positivity
  unfold coefG kpar muSq
  field_simp
  ring

/-- Continuity of `f` from continuity of the profiles. -/
theorem coefF_continuousOn {m k : ℝ} (hm : m ≠ 0) {Bz b : ℝ → ℝ} {s : Set ℝ}
    (hBz : ContinuousOn Bz s) (hb : ContinuousOn b s) : ContinuousOn (coefF m k Bz b) s := by
  unfold coefF kpar muSq
  refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun r _ => (muSq_pos hm k r).ne')

/-- Continuity of `g` from continuity of the profiles. -/
theorem coefG_continuousOn {μ₀ m k : ℝ} (hm : m ≠ 0) {p' Bz b : ℝ → ℝ} {s : Set ℝ}
    (hp : ContinuousOn p' s) (hBz : ContinuousOn Bz s) (hb : ContinuousOn b s) :
    ContinuousOn (coefG μ₀ m k p' Bz b) s := by
  have hK := fun r => (muSq_pos hm k r).ne'
  unfold coefG kpar
  refine ((ContinuousOn.div (by fun_prop) (by unfold muSq; fun_prop) fun r _ => hK r).add
    (ContinuousOn.div (by unfold muSq; fun_prop) (by unfold muSq; fun_prop)
      fun r _ => hK r)).add
    (ContinuousOn.div (by fun_prop) (by unfold muSq; fun_prop)
      fun r _ => pow_ne_zero _ (hK r))

/-! ## Generic stability criteria -/

/-- A nonnegative potential coefficient gives stability (no certificate needed). -/
theorem modeStable_of_g_nonneg {μ₀ a m k : ℝ} {p' Bz b : ℝ → ℝ} (hm : m ≠ 0) (ha : 0 ≤ a)
    (hg : ∀ r ∈ Icc 0 a, 0 ≤ coefG μ₀ m k p' Bz b r) : ModeStable μ₀ a m k p' Bz b := by
  intro ξ ξ' _ _
  apply integral_nonneg ha
  intro r hr
  have := coefF_nonneg (k := k) hm Bz b hr.1
  have := hg r hr
  positivity

/-- **Picone with lower-bound coefficients and a free axis value.** If `fL ≤ f`,
`gL ≤ g`, `fL ≥ 0`, and a C¹ function `φ` with derivative `h` satisfies `φ(x₀) = 0`,
`h ≤ gL` and `φ² ≤ fL (gL - h)`, then `Q(ξ) ≥ 0` for every C¹ `ξ` with `ξ(x₁) = 0`;
no condition on `ξ(x₀)` is needed. -/
theorem picone_lower {f g fL gL φ h ξ ξ' : ℝ → ℝ} {x₀ x₁ : ℝ} (hle : x₀ ≤ x₁)
    (hξ : C1On ξ ξ' x₀ x₁) (hφ₀ : φ x₀ = 0) (h₁ : ξ x₁ = 0)
    (hf : ContinuousOn f (uIcc x₀ x₁)) (hg : ContinuousOn g (uIcc x₀ x₁))
    (hφ : ∀ x ∈ uIcc x₀ x₁, HasDerivAt φ (h x) x) (hh : ContinuousOn h (uIcc x₀ x₁))
    (hfL : ∀ x ∈ uIcc x₀ x₁, 0 ≤ fL x) (hff : ∀ x ∈ uIcc x₀ x₁, fL x ≤ f x)
    (hgg : ∀ x ∈ uIcc x₀ x₁, gL x ≤ g x) (hgap : ∀ x ∈ uIcc x₀ x₁, h x ≤ gL x)
    (hdisc : ∀ x ∈ uIcc x₀ x₁, φ x ^ 2 ≤ fL x * (gL x - h x)) :
    0 ≤ newcombForm f g x₀ x₁ ξ ξ' := by
  have hφc : ContinuousOn φ (uIcc x₀ x₁) :=
    fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  have hP : ∀ x ∈ uIcc x₀ x₁, HasDerivAt (fun y => φ y * ξ y ^ 2)
      (h x * ξ x ^ 2 + φ x * (2 * ξ x * ξ' x)) x := by
    intro x hx
    have := (hφ x hx).mul ((hξ.deriv x hx).pow 2)
    convert this using 1
    simp only [Pi.pow_apply, Nat.cast_ofNat]; ring
  have hPi : IntervalIntegrable (fun x => h x * ξ x ^ 2 + φ x * (2 * ξ x * ξ' x))
      MeasureTheory.volume x₀ x₁ :=
    ((hh.mul (hξ.continuousOn.pow 2)).add
      (hφc.mul ((continuousOn_const.mul hξ.continuousOn).mul hξ.cont))).intervalIntegrable
  have hftc : ∫ x in x₀..x₁, (h x * ξ x ^ 2 + φ x * (2 * ξ x * ξ' x)) = 0 := by
    rw [integral_eq_sub_of_hasDerivAt hP hPi, h₁, hφ₀]; ring
  have hmono : ∫ x in x₀..x₁, (h x * ξ x ^ 2 + φ x * (2 * ξ x * ξ' x)) ≤
      newcombForm f g x₀ x₁ ξ ξ' := by
    apply integral_mono_on hle hPi (newcomb_integrable hξ hf hg)
    intro x hx
    have hx' : x ∈ uIcc x₀ x₁ := Icc_subset_uIcc hx
    have q := quadratic_nonneg (p := ξ' x) (q := ξ x) (hfL x hx')
      (by linarith [hgap x hx']) (hdisc x hx')
    have h1 : fL x * ξ' x ^ 2 ≤ f x * ξ' x ^ 2 :=
      mul_le_mul_of_nonneg_right (hff x hx') (sq_nonneg _)
    have h2 : gL x * ξ x ^ 2 ≤ g x * ξ x ^ 2 :=
      mul_le_mul_of_nonneg_right (hgg x hx') (sq_nonneg _)
    nlinarith [q]
  rw [hftc] at hmono
  exact hmono

/-! ## Sanity checks of the extracted coefficients -/

/-- Symmetry: `(m, k)` and `(-m, -k)` describe the same mode. -/
theorem coefF_neg (m k : ℝ) (Bz b : ℝ → ℝ) : coefF (-m) (-k) Bz b = coefF m k Bz b := by
  funext r; unfold coefF kpar muSq; ring

/-- Symmetry of `g`. -/
theorem coefG_neg (μ₀ m k : ℝ) (p' Bz b : ℝ → ℝ) :
    coefG μ₀ (-m) (-k) p' Bz b = coefG μ₀ m k p' Bz b := by
  funext r; unfold coefG kpar muSq; ring

/-- Stability is invariant under `(m, k) ↦ (-m, -k)`. -/
theorem modeStable_neg {μ₀ a m k : ℝ} {p' Bz b : ℝ → ℝ} :
    ModeStable μ₀ a (-m) (-k) p' Bz b ↔ ModeStable μ₀ a m k p' Bz b := by
  unfold ModeStable; rw [coefF_neg, coefG_neg]

/-- Uniform vacuum field `Bz = B₀`, `Bθ = 0`, `p' = 0`: every mode with `m² ≥ 1` is
stable, for every wavenumber. -/
theorem uniform_vacuum_stable {μ₀ a m k B₀ : ℝ} (hm : 1 ≤ m ^ 2) (ha : 0 ≤ a) :
    ModeStable μ₀ a m k (fun _ => 0) (fun _ => B₀) (fun _ => 0) := by
  have hm0 : m ≠ 0 := by rintro rfl; norm_num at hm
  refine modeStable_of_g_nonneg hm0 ha fun r hr => ?_
  have hK := one_le_muSq hm k r
  have hK0 : 0 < muSq m k r := by linarith
  unfold coefG kpar
  have : 0 ≤ (muSq m k r - 1) * r * (k * B₀ + m * 0) ^ 2 / muSq m k r := by
    have := hr.1; have : 0 ≤ muSq m k r - 1 := by linarith
    positivity
  have : 0 ≤ 2 * k ^ 2 * r ^ 3 * (k ^ 2 * B₀ ^ 2 - m ^ 2 * 0 ^ 2) / muSq m k r ^ 2 := by
    have := hr.1; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, sub_zero]
    positivity
  simp only [mul_zero, zero_div, zero_add] at *
  linarith

/-- Modes with `k = 0` and `m² ≥ 1` are stable for every profile. -/
theorem zero_k_stable {μ₀ a m : ℝ} {p' Bz b : ℝ → ℝ} (hm : 1 ≤ m ^ 2) (ha : 0 ≤ a) :
    ModeStable μ₀ a m 0 p' Bz b := by
  have hm0 : m ≠ 0 := by rintro rfl; norm_num at hm
  refine modeStable_of_g_nonneg hm0 ha fun r hr => ?_
  have hK := one_le_muSq hm 0 r
  unfold coefG
  have : 0 ≤ (muSq m 0 r - 1) * r * kpar m 0 Bz b r ^ 2 / muSq m 0 r := by
    have := hr.1; have : 0 ≤ muSq m 0 r - 1 := by linarith
    have : 0 < muSq m 0 r := by linarith
    positivity
  simpa using this

/-! ## Suydam limit at a resonant surface -/

/-- At a resonant surface (`F = 0`), `g` reduces to the Suydam drive `localG c p'` with
weight `c = μ₀ k² r²/μ²`. -/
theorem suydam_limit_G {μ₀ m k r : ℝ} {p' Bz b : ℝ → ℝ} (hm : m ≠ 0)
    (hres : kpar m k Bz b r = 0) :
    coefG μ₀ m k p' Bz b r = localG (μ₀ * k ^ 2 * r ^ 2 / muSq m k r) p' r := by
  have hK := (muSq_pos hm k r).ne'
  have hb : m * b r = -(k * Bz r) := by unfold kpar at hres; linarith
  have hD : k ^ 2 * Bz r ^ 2 - m ^ 2 * b r ^ 2 = 0 := by
    have : m ^ 2 * b r ^ 2 = (m * b r) ^ 2 := by ring
    rw [this, hb]; ring
  unfold coefG localG
  rw [hres, hD]
  field_simp
  ring

/-- At a resonant surface the bending factor has derivative `k Bz (q'/q)`: with
`Bz = √S` and `b = Bθ/r`, `F' = k √S · shearRatio`. -/
theorem suydam_limit_shear {m k r : ℝ} {Bθ S Bθ' S' : ℝ → ℝ} (hr : r ≠ 0) (hS : 0 < S r)
    (hB : Bθ r ≠ 0) (dS : HasDerivAt S (S' r) r) (dB : HasDerivAt Bθ (Bθ' r) r)
    (hres : kpar m k (fun s => Real.sqrt (S s)) (fun s => Bθ s / s) r = 0) :
    HasDerivAt (kpar m k (fun s => Real.sqrt (S s)) (fun s => Bθ s / s))
      (k * Real.sqrt (S r) * shearRatio Bθ S Bθ' S' r) r := by
  have hsq := Real.sqrt_pos.mpr hS
  have e : Real.sqrt (S r) ^ 2 = S r := Real.sq_sqrt hS.le
  have hd := ((dS.sqrt hS.ne').const_mul k).add ((dB.div (hasDerivAt_id' r) hr).const_mul m)
  unfold kpar
  convert hd using 1
  unfold kpar at hres
  have hm : m = -(k * Real.sqrt (S r)) * r / Bθ r := by
    field_simp; field_simp at hres; linarith
  unfold shearRatio
  rw [hm]
  field_simp
  linear_combination (k * r * S' r * Bθ r) * e

/-- At a resonant surface the leading shear coefficient `r³ F'²/μ²` is ScrewPinch.lean's
`localF μ₀ c` with the same weight `c = μ₀ k² r²/μ²`. -/
theorem suydam_limit_F {μ₀ m k r : ℝ} {Bθ S Bθ' S' : ℝ → ℝ} (hμ : μ₀ ≠ 0) (hm : m ≠ 0)
    (hS : 0 ≤ S r) :
    r ^ 3 * (k * Real.sqrt (S r) * shearRatio Bθ S Bθ' S' r) ^ 2 / muSq m k r =
      localF μ₀ (μ₀ * k ^ 2 * r ^ 2 / muSq m k r) Bθ S Bθ' S' r := by
  have hK := (muSq_pos hm k r).ne'
  have e : Real.sqrt (S r) ^ 2 = S r := Real.sq_sqrt hS
  unfold localF
  field_simp
  rw [e]
  ring

/-- The Suydam weight at a resonant surface is `μ₀ Bθ²/(Bθ² + Bz²)`, i.e. the documented
`Bθ²/B²` of ScrewPinch.lean in the `μ₀` normalization. -/
theorem suydam_limit_weight {μ₀ m k r : ℝ} {Bθ S : ℝ → ℝ} (hm : m ≠ 0) (hr : r ≠ 0)
    (hS : 0 < S r) (hB : Bθ r ≠ 0)
    (hres : kpar m k (fun s => Real.sqrt (S s)) (fun s => Bθ s / s) r = 0) :
    μ₀ * k ^ 2 * r ^ 2 / muSq m k r = μ₀ * Bθ r ^ 2 / (Bθ r ^ 2 + S r) := by
  have e : Real.sqrt (S r) ^ 2 = S r := Real.sq_sqrt hS.le
  unfold kpar at hres
  have hmb : m * Bθ r = -(k * Real.sqrt (S r) * r) := by
    field_simp at hres; linarith
  have hK := (muSq_pos hm k r).ne'
  have hden : Bθ r ^ 2 + S r ≠ 0 := by positivity
  rw [div_eq_div_iff hK hden]
  unfold muSq
  have : m ^ 2 * Bθ r ^ 2 = k ^ 2 * S r * r ^ 2 := by
    have : m ^ 2 * Bθ r ^ 2 = (m * Bθ r) ^ 2 := by ring
    rw [this, hmb]
    linear_combination (k ^ 2 * r ^ 2) * e
  linear_combination (-μ₀) * this

/-! ## The 3-D reduction as a hypothesis interface -/

/-- Supplied Newcomb reduction for one mode: the full ideal-MHD energy `W` of an
admissible displacement `d` is bounded below by a positive multiple of the reduced form of
its radial component. -/
structure NewcombReduction {Disp : Type*} (W : Disp → ℝ) (admissible : Disp → Prop)
    (radial : Disp → (ℝ → ℝ) × (ℝ → ℝ)) (μ₀ a m k : ℝ) (p' Bz b : ℝ → ℝ) : Prop where
  scale_pos : ∃ C : ℝ, 0 < C ∧ ∀ d, admissible d →
    C * newcombForm (coefF m k Bz b) (coefG μ₀ m k p' Bz b) 0 a (radial d).1 (radial d).2 ≤
      W d
  regular : ∀ d, admissible d → C1On (radial d).1 (radial d).2 0 a
  wall : ∀ d, admissible d → (radial d).1 a = 0

/-- Under the supplied reduction, reduced-form stability gives `W ≥ 0` for every
admissible displacement of the mode. -/
theorem NewcombReduction.energy_nonneg {Disp : Type*} {W : Disp → ℝ}
    {admissible : Disp → Prop} {radial : Disp → (ℝ → ℝ) × (ℝ → ℝ)} {μ₀ a m k : ℝ}
    {p' Bz b : ℝ → ℝ} (hR : NewcombReduction W admissible radial μ₀ a m k p' Bz b)
    (hs : ModeStable μ₀ a m k p' Bz b) (d : Disp) (hd : admissible d) : 0 ≤ W d := by
  obtain ⟨C, hC, hW⟩ := hR.scale_pos
  exact le_trans (mul_nonneg hC.le (hs _ _ (hR.regular d hd) (hR.wall d hd))) (hW d hd)

/-- Non-vacuity: the reduced form itself, on C¹ radial displacements with the wall
condition, satisfies the interface. -/
theorem newcombReduction_self (μ₀ a m k : ℝ) (p' Bz b : ℝ → ℝ) :
    NewcombReduction (fun d : (ℝ → ℝ) × (ℝ → ℝ) =>
        newcombForm (coefF m k Bz b) (coefG μ₀ m k p' Bz b) 0 a d.1 d.2)
      (fun d => C1On d.1 d.2 0 a ∧ d.1 a = 0) id μ₀ a m k p' Bz b where
  scale_pos := ⟨1, one_pos, fun d _ => by simp⟩
  regular _ hd := hd.1
  wall _ hd := hd.2

end PlasmaLean.Stability.ScrewPinchModes
