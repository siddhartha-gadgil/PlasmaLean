/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCFamForever

/-!
# Robust all-time confinement of passing alpha guiding centres (an interval of `B₀R₀`)

**Model assumption.** Guiding centres move according to the Littlejohn guiding-centre equations
(`Theory/Kinetic/GuidingCentreLittlejohn`, `LittlejohnOrbit`): a supplied model, not derived here
from the Newton–Lorentz equations. Only passing particles with magnetic moment `μ = 0` and
`v∥ > 0` are treated. This is a single pitch angle, a measure-zero set in velocity space; the
"robust" (positive-measure) range is in `B₀R₀` only.

**Main results.**

* `rationalStellarator_gc_confined_forever_cell` (model units `R₀ = B₀ = 1`): for every
  `ρ_s = m v_∥/q ∈ [63/16384, 65/16384]` there is a torus profile `P` (`0.03 ≤ P ≤ 0.255`, the
  exact KAM torus of `gcField ρ_s`) trapping every `μ = 0` Littlejohn orbit in `field (1/4)` with
  that `ρ_s` that starts on the axis or inside the torus, with `B*_∥ = |B| ≥ 1/10` along it; such
  orbits exist from every starting point inside.
* **`alpha_gc_confined_forever_robust`** (SI): for 3.5 MeV alpha particles (mass
  `m ∈ [6.6446, 6.6447] × 10⁻²⁷ kg`, charge `q = 2e`, `e ∈ [1.6021, 1.6022] × 10⁻¹⁹ C`, all kinetic
  energy parallel, `v_∥ = √(2K/m) > 0`) in the field `fieldSI B₀ R₀ x = B₀ · field (1/4) (x/R₀)`
  with **any** `B₀ R₀ ∈ [67.95, 69.99] T·m` (a −1.5%/+1.4% tolerance on `B₀` around the design value
  `≈ 69 T·m` of `alpha_gc_confined_forever`), there is a torus profile `P` (depending on `B₀R₀`
  through `ρ_s = m v_∥/(q B₀R₀) ∈ [63/16384, 65/16384]`) such that passing (`μ = 0`) guiding centres
  starting inside the scaled torus stay inside it for all time, within `0.255 R₀` of the magnetic
  axis, and such orbits exist from every starting point inside.

**Proof.** `ρ_s` lies in the cell (`alpha_ρs_mem`), so the exact torus of `gcField ρ_s`
(`gc_family_torus`, one KAM certificate for the whole cell) traps the field lines of the time
change `(v/|B|) gcField ρ_s` (`gc_family_master`); a `μ = 0` orbit is such a field line
(`littlejohnSI_isFieldLineF`), as for `ρ_s = 1/256` (`Design/RationalStellaratorGCConfined`).

**Sanity.** `alpha_ρs_mem`: the alpha parameter `ρ_s` lies in the certified cell.
-/

open scoped RealInnerProductSpace

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open Real Set PlasmaLean.Fields PlasmaLean.Design.RationalStellarator PlasmaLean.Design.KamTorusA
  PlasmaLean.Kinetic.GCLittlejohn WithLp

/-! ## Model units -/

/-- A `μ = 0` Littlejohn orbit in `field (1/4)` with `m v_∥/q = ρ` is a field line of
`VgcF ρ v_∥(0)`. -/
theorem littlejohn_isFieldLine_VgcF {m q ρ : ℝ} {X : ℝ → Space} {v : ℝ → ℝ}
    (h : LittlejohnOrbit m q 0 (field (1 / 4)) X v) (hρ : m * v 0 / q = ρ) :
    IsFieldLine (VgcF ρ (v 0)) X := fun t => by
  have := velocity_eq_modField h t
  rw [BstarPar_field, hρ] at this
  exact this

/-- **All-time confinement of passing guiding centres for every `ρ_s` of the cell** (Littlejohn
model, `μ = 0`, model units `R₀ = B₀ = 1`). For every `ρ_s ∈ [63/16384, 65/16384]` there is a torus
profile `P` with `0.03 ≤ P ≤ 0.255` such that every `μ = 0` Littlejohn orbit `(X, v_∥)` in
`B = field (1/4)` with `m v_∥/q = ρ_s` starting on the axis or inside the torus stays inside it
for all time, with `B*_∥ = |B| ≥ 1/10` along the orbit; from every point on the axis or inside the
torus and every `v₀` with `m v₀/q = ρ_s` there is such an orbit (with `v_∥ ≡ v₀`). -/
theorem rationalStellarator_gc_confined_forever_cell {ρs : ℝ}
    (hρ : ρs ∈ Set.Icc (63 / 16384 : ℝ) (65 / 16384)) :
    ∃ P : ℝ → ℝ → ℝ, TorusProfile P ∧ (∀ a b, 3 / 100 ≤ P a b) ∧ (∀ a b, P a b ≤ 255 / 1000) ∧
      (∀ (m q : ℝ) (X : ℝ → Space) (v : ℝ → ℝ), LittlejohnOrbit m q 0 (field (1 / 4)) X v →
        m * v 0 / q = ρs → (rt (X 0) = 0 ∨ rt (X 0) < P (θs (X 0)) (φs (X 0))) →
        ∀ t, rt (X t) ≤ 255 / 1000 ∧ (rt (X t) = 0 ∨ rt (X t) < P (θs (X t)) (φs (X t))) ∧
          1 / 10 ≤ BstarPar m q (field (1 / 4)) (v t) (X t)) ∧
      ∀ (m q v₀ : ℝ) (x₀ : Space), m * v₀ / q = ρs →
        (rt x₀ = 0 ∨ rt x₀ < P (θs x₀) (φs x₀)) →
        ∃ X : ℝ → Space, LittlejohnOrbit m q 0 (field (1 / 4)) X (fun _ => v₀) ∧ X 0 = x₀ := by
  obtain ⟨P, hP, hlo, hhi, -, -, hE, hV⟩ := gc_family_master hρ
  have hρ0 : ρs ≠ 0 := by have := hρ.1; intro h; rw [h] at this; norm_num at this
  refine ⟨P, hP, hlo, hhi, fun m q X v h hs h0 t => ?_, fun m q v₀ x₀ hs h0 => ?_⟩
  · have hv0 : v 0 ≠ 0 := by
      intro hz; rw [hz, mul_zero, zero_div] at hs; exact hρ0 hs.symm
    obtain ⟨hr, hin⟩ := hV (v 0) hv0 X (littlejohn_isFieldLine_VgcF h hs) h0 t
    exact ⟨hr, hin, by rw [BstarPar_field]; exact norm_field_ge (by linarith)⟩
  · have hv0 : v₀ ≠ 0 := by
      intro hz; rw [hz, mul_zero, zero_div] at hs; exact hρ0 hs.symm
    obtain ⟨Y, ⟨hY, hY0⟩, -⟩ := hE v₀ hv0 x₀ h0
    refine ⟨Y, ⟨fun t => ?_, fun t => ?_⟩, hY0⟩
    · have := hY t
      rw [BstarPar_field, Bstar_eq_modField, hs, zero_div, zero_smul, add_zero, smul_smul,
        ← div_eq_inv_mul]
      exact this
    · simpa using hasDerivAt_const t v₀

/-! ## SI units -/

/-- In SI units, a `μ = 0` Littlejohn orbit with `m v_∥/(q B₀ R₀) = ρ` is, after rescaling
`Y = X/R₀`, a field line of `VgcF ρ (v_∥/R₀)`. -/
theorem littlejohnSI_isFieldLineF {m q B₀ R₀ ρ : ℝ} (hB₀ : 0 < B₀) (hR₀ : 0 < R₀)
    {X : ℝ → Space} {v : ℝ → ℝ} (h : LittlejohnOrbit m q 0 (fieldSI B₀ R₀) X v)
    (hρ : m * v 0 / q / (B₀ * R₀) = ρ) :
    IsFieldLine (VgcF ρ (v 0 / R₀)) (fun t => R₀⁻¹ • X t) := fun t => by
  have h1 := (velocity_eq_modField h t).const_smul R₀⁻¹
  rw [BstarPar_fieldSI hB₀ hR₀, fieldSI_modField hB₀ hR₀, hρ, smul_smul, smul_smul] at h1
  convert h1 using 1
  simp only [VgcF, gcField]
  congr 1
  have hn : ‖field (1 / 4) (R₀⁻¹ • X t)‖ ≠ 0 ∨ ‖field (1 / 4) (R₀⁻¹ • X t)‖ = 0 := by tauto
  rcases hn with hn | hn
  · field_simp
  · rw [hn]; simp

/-- **The alpha parameter lies in the certified cell**: for `B₀R₀ ∈ [67.95, 69.99] T·m`,
`ρ_s = m v_∥/(q B₀ R₀) ∈ [63/16384, 65/16384]` (with `v_∥ = √(2K/m)`, `K = 3.5 MeV`, `q = 2e`). -/
theorem alpha_ρs_mem {m e B₀ R₀ : ℝ} (hm1 : 6.6446e-27 ≤ m) (hm2 : m ≤ 6.6447e-27)
    (he1 : 1.6021e-19 ≤ e) (he2 : e ≤ 1.6022e-19) (hB₀ : 0 < B₀) (hR₀ : 0 < R₀)
    (hBR1 : 67.95 ≤ B₀ * R₀) (hBR2 : B₀ * R₀ ≤ 69.99) :
    m * √(2 * (3.5e6 * e) / m) / (2 * e) / (B₀ * R₀) ∈ Set.Icc (63 / 16384 : ℝ) (65 / 16384) := by
  obtain ⟨h1, h2⟩ := alpha_B0R0_bounds hm1 hm2 he1 he2
  have he : 0 < e := by linarith
  have hBR : 0 < B₀ * R₀ := by positivity
  set K := m * √(2 * (3.5e6 * e) / m) / (2 * e) with hK
  have e1 : 256 * m * √(2 * (3.5e6 * e) / m) / (2 * e) = 256 * K := by rw [hK]; ring
  rw [e1] at h1 h2
  constructor
  · rw [le_div_iff₀ hBR]; nlinarith
  · rw [div_le_iff₀ hBR]; nlinarith

/-- **Robust all-time confinement of passing 3.5 MeV alpha guiding centres in SI units**
(Littlejohn guiding-centre model — a supplied model, not derived from the Lorentz force — with
magnetic moment `μ = 0`). Let `m ∈ [6.6446, 6.6447] × 10⁻²⁷ kg` (alpha mass),
`e ∈ [1.6021, 1.6022] × 10⁻¹⁹ C`, `q = 2e`, kinetic energy `K = 3.5 MeV = 3.5 × 10⁶ e` J, all of it
parallel: `v_∥ = √(2K/m) > 0`. Consider the rational stellarator field in SI units
`fieldSI B₀ R₀ x = B₀ · field (1/4) (x/R₀)` with **any** `B₀ R₀ ∈ [67.95, 69.99] T·m`.

Then there is a torus profile `P` (`0.03 ≤ P ≤ 0.255`, in units of `R₀`; the exact KAM torus of
the guiding-centre field `gcField ρ_s`, `ρ_s = m v_∥/(q B₀ R₀)`, so `P` depends on `B₀ R₀`) such
that

* (non-vacuity) from every point `x₀` with `x₀/R₀` on the axis or inside the torus there is such a
  guiding-centre orbit `(X, v_∥ ≡ √(2K/m))` with `X 0 = x₀`; and
* every such guiding-centre orbit `(X, v_∥)` starting on the magnetic axis or inside the torus (in
  the scaled coordinates `X/R₀`) stays inside it, in particular within distance `0.255 R₀` of the
  magnetic axis, for all time. -/
theorem alpha_gc_confined_forever_robust (m e B₀ R₀ : ℝ) (hm1 : 6.6446e-27 ≤ m)
    (hm2 : m ≤ 6.6447e-27) (he1 : 1.6021e-19 ≤ e) (he2 : e ≤ 1.6022e-19) (hB₀ : 0 < B₀)
    (hR₀ : 0 < R₀) (hBR1 : 67.95 ≤ B₀ * R₀) (hBR2 : B₀ * R₀ ≤ 69.99) :
    ∃ P : ℝ → ℝ → ℝ, TorusProfile P ∧ (∀ a b, 3 / 100 ≤ P a b) ∧ (∀ a b, P a b ≤ 255 / 1000) ∧
      (∀ x₀ : Space,
        (rt (R₀⁻¹ • x₀) = 0 ∨ rt (R₀⁻¹ • x₀) < P (θs (R₀⁻¹ • x₀)) (φs (R₀⁻¹ • x₀))) →
        ∃ X : ℝ → Space, LittlejohnOrbit m (2 * e) 0 (fieldSI B₀ R₀) X
          (fun _ => √(2 * (3.5e6 * e) / m)) ∧ X 0 = x₀) ∧
      ∀ (X : ℝ → Space) (v : ℝ → ℝ), LittlejohnOrbit m (2 * e) 0 (fieldSI B₀ R₀) X v →
        v 0 = √(2 * (3.5e6 * e) / m) →
        (rt (R₀⁻¹ • X 0) = 0 ∨ rt (R₀⁻¹ • X 0) < P (θs (R₀⁻¹ • X 0)) (φs (R₀⁻¹ • X 0))) →
        ∀ t, rt (R₀⁻¹ • X t) ≤ 255 / 1000 ∧
          (rt (R₀⁻¹ • X t) = 0 ∨ rt (R₀⁻¹ • X t) < P (θs (R₀⁻¹ • X t)) (φs (R₀⁻¹ • X t))) := by
  set v₀ := √(2 * (3.5e6 * e) / m) with hv₀
  set ρs := m * v₀ / (2 * e) / (B₀ * R₀) with hρs
  have hmem : ρs ∈ Set.Icc (63 / 16384 : ℝ) (65 / 16384) :=
    alpha_ρs_mem hm1 hm2 he1 he2 hB₀ hR₀ hBR1 hBR2
  obtain ⟨P, hP, hlo, hhi, -, -, hE, hV⟩ := gc_family_master hmem
  have hm : 0 < m := by linarith
  have he : 0 < e := by linarith
  have hvpos : 0 < v₀ := Real.sqrt_pos.2 (by positivity)
  refine ⟨P, hP, hlo, hhi, fun x₀ h0 => ?_, fun X v h hv0 h0 t => ?_⟩
  · obtain ⟨Y, ⟨hY, hY0⟩, -⟩ := hE (v₀ / R₀) (div_ne_zero hvpos.ne' hR₀.ne') _ h0
    have hXY : ∀ t, R₀⁻¹ • (R₀ • Y t) = Y t := fun t => by
      rw [smul_smul, inv_mul_cancel₀ hR₀.ne', one_smul]
    refine ⟨fun t => R₀ • Y t, ⟨fun t => ?_, fun t => ?_⟩, ?_⟩
    · have h1 := (hY t).const_smul R₀
      rw [BstarPar_fieldSI hB₀ hR₀, hXY, Bstar_eq_modField, fieldSI_modField hB₀ hR₀, hXY,
        ← hρs, zero_div, zero_smul, add_zero]
      convert h1 using 1
      simp only [VgcF, gcField, smul_smul]
      congr 1
      rcases eq_or_ne ‖field (1 / 4) (Y t)‖ 0 with hn | hn
      · rw [hn]; simp
      · field_simp
    · simpa using hasDerivAt_const t v₀
    · change R₀ • Y 0 = x₀
      rw [hY0, smul_smul, mul_inv_cancel₀ hR₀.ne', one_smul]
  · have hv0' : 0 < v 0 := by rw [hv0]; exact hvpos
    have hs : m * v 0 / (2 * e) / (B₀ * R₀) = ρs := by rw [hv0]
    exact hV (v 0 / R₀) (div_ne_zero hv0'.ne' hR₀.ne') _
      (littlejohnSI_isFieldLineF hB₀ hR₀ h hs) h0 t

end PlasmaLean.Design.RationalStellaratorGC
