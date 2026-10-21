/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCMuForever
public import PlasmaLean.Design.RationalStellaratorGCMuSI

/-!
# All-time confinement of passing guiding centres with `μ > 0` (a pitch-angle cell)

**Model assumption.** Guiding centres move according to the Littlejohn guiding-centre equations
(`Theory/Kinetic/GuidingCentreLittlejohn`, `LittlejohnOrbit`), a supplied model. Here the magnetic
moment `μ` is **positive** (or zero): passing particles with `v_∥(0) > 0` and
`λ = μ/E ∈ [0, 1/16]` (model units `R₀ = B₀ = 1`; `sin²χ = λ|B| ≤ |B|/16` for the pitch angle
`χ` at the start), with `ρ₀ = (m/q)√(2E/m) = 1/256`. This is a positive-measure set of
pitch angles at the single energy `E` and the single `B₀R₀` fixed by `ρ₀ = 1/256`; it is still
measure zero in 3-D velocity space. Also: non-relativistic, collisionless (no slowing-down, so `E`
is fixed), static vacuum model field `field (1/4)`, not coil-produced.

**Main results.** `rationalStellarator_gc_mu_confined_forever` (model units): for every
`λ ∈ [0, 1/16]` there is a torus profile `P` (`0.03 ≤ P ≤ 0.255`, the exact KAM torus of the
`μ > 0` passing field `gcFieldMu (1/256) λ`) such that every Littlejohn orbit with energy `E`,
`μ = λE`, `ρ₀ = 1/256` and `v_∥(0) > 0` starting on the axis or inside the torus stays inside it
for all time and stays passing (`v_∥(t) = √(2(E − μ|B|)/m) > 0`); such orbits exist from every
point inside.
In SI units (`gc_mu_passing_confined_forever_SI`, `fieldSI B₀ R₀`): for `m√(2E/m)/(qB₀R₀) = 1/256`
and every `μ ∈ [0, E/(16B₀)]`; for 3.5 MeV alphas with `B₀R₀ = 256 m v/(2e) ≈ 69 T·m`
(`alpha_gc_passing_confined_forever`).

**Proof.** The field line `Y` of `VmuF` from `X 0` is trapped in the closed tube `rt ≤ 0.255`
(`mu_family_master`), a compact subset of `muRegion λ` (where `λ|B| < 1`); by the bootstrap
`littlejohn_mu_eq_fieldLine` (continuity + Grönwall uniqueness) the orbit is `Y`. No a priori
assumption that the orbit stays passing is needed. Existence: field lines of `VmuF` are Littlejohn
orbits (`littlejohn_of_fieldLine`).

**Sanity.** `rho0_param_alpha`: the normalisation `ρ₀ = 1/256` is attained (`m = q = 1`,
`E = 1/131072`).
-/

open scoped RealInnerProductSpace

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open Real Set PlasmaLean.Fields PlasmaLean.Design.RationalStellarator PlasmaLean.Design.KamTorusA
  PlasmaLean.Kinetic.GCLittlejohn WithLp

/-- **All-time confinement of passing guiding centres with `μ > 0`** (Littlejohn model, model units
`R₀ = B₀ = 1`, `B = field (1/4)`). For every `λ ∈ [0, 1/16]` there is a torus profile `P` with
`0.03 ≤ P ≤ 0.255` such that for all `m > 0`, `q ≠ 0`, `E > 0`, `μ = λE` with
`(m/q)√(2E/m) = 1/256`:

* every Littlejohn orbit `(X, v_∥)` with energy `H(X 0, v_∥ 0) = E` and `v_∥(0) > 0` starting on
  the axis or inside the torus stays inside it for all time (within `0.255` of the axis), and stays
  passing: `v_∥(t) = √(2(E − μ|B(X t)|)/m) > 0`;
* from every point `x₀` on the axis or inside the torus there is such an orbit with `X 0 = x₀`. -/
theorem rationalStellarator_gc_mu_confined_forever {lm : ℝ}
    (hlm : lm ∈ Set.Icc (0 : ℝ) (1 / 16)) :
    ∃ P : ℝ → ℝ → ℝ, TorusProfile P ∧ (∀ a b, 3 / 100 ≤ P a b) ∧ (∀ a b, P a b ≤ 255 / 1000) ∧
      (∀ (m q μ E : ℝ) (X : ℝ → Space) (v : ℝ → ℝ), 0 < m → q ≠ 0 → 0 < E →
        m / q * √(2 * E / m) = 1 / 256 → μ = lm * E →
        LittlejohnOrbit m q μ (field (1 / 4)) X v →
        hamiltonian m μ (field (1 / 4)) (X 0) (v 0) = E → 0 < v 0 →
        (rt (X 0) = 0 ∨ rt (X 0) < P (θs (X 0)) (φs (X 0))) →
        ∀ t, rt (X t) ≤ 255 / 1000 ∧ (rt (X t) = 0 ∨ rt (X t) < P (θs (X t)) (φs (X t))) ∧
          v t = √(2 * (E - μ * ‖field (1 / 4) (X t)‖) / m) ∧ 0 < v t) ∧
      ∀ (m q μ E : ℝ) (x₀ : Space), 0 < m → q ≠ 0 → 0 < E →
        m / q * √(2 * E / m) = 1 / 256 → μ = lm * E →
        (rt x₀ = 0 ∨ rt x₀ < P (θs x₀) (φs x₀)) →
        ∃ X : ℝ → Space, LittlejohnOrbit m q μ (field (1 / 4)) X
          (fun t => √(2 * (E - μ * ‖field (1 / 4) (X t)‖) / m)) ∧ X 0 = x₀ ∧
          ∀ t, 0 < √(2 * (E - μ * ‖field (1 / 4) (X t)‖) / m) := by
  obtain ⟨P, hP, hlo, hhi, -, -, hE, hV⟩ := mu_family_master hlm
  have hKU := tube27_subset_muRegion hlm
  have hK : IsCompact {y : Space | rt y ≤ 255 / 1000} := isCompact_rtLe' (by norm_num)
  have hKU' : {y : Space | rt y ≤ 255 / 1000} ⊆ muRegion lm := fun y hy =>
    hKU y (le_trans (show rt y ≤ 255 / 1000 from hy) (by norm_num))
  have hlE : ∀ {μ E : ℝ}, 0 < E → μ = lm * E → μ / E = lm := fun hE h => by
    rw [h]; field_simp
  refine ⟨P, hP, hlo, hhi, fun m q μ E X v hm hq hE0 hρ hμ h hH hv0 h0 => ?_,
    fun m q μ E x₀ hm hq hE0 hρ hμ h0 => ?_⟩
  · have hc : √(2 * E / m) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
    obtain ⟨Y, ⟨hY, hY0⟩, -⟩ := hE _ hc (X 0) h0
    have htrap := hV _ hc Y hY (by rw [hY0]; exact h0)
    rw [← hρ, ← hlE hE0 hμ] at hY
    have hKU2 : {y : Space | rt y ≤ 255 / 1000} ⊆ muRegion (μ / E) := by
      rw [hlE hE0 hμ]; exact hKU'
    obtain ⟨hXY, hvv⟩ := littlejohn_mu_eq_fieldLine hm hq hE0 h hH hv0 hK hKU2 hY
      (fun t => (htrap t).1) hY0.symm
    intro t
    obtain ⟨h1, h2⟩ := htrap t
    rw [← hXY] at h1 h2
    exact ⟨h1, h2, hvv t⟩
  · have hc : √(2 * E / m) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
    obtain ⟨Y, ⟨hY, hY0⟩, -⟩ := hE _ hc x₀ h0
    have htrap := hV _ hc Y hY (by rw [hY0]; exact h0)
    have hYU : ∀ t, Y t ∈ muRegion (μ / E) := fun t => by
      rw [hlE hE0 hμ]; exact hKU' (htrap t).1
    rw [← hρ, ← hlE hE0 hμ] at hY
    refine ⟨Y, littlejohn_of_fieldLine hm hq hE0 hY hYU, hY0, fun t => ?_⟩
    have h2 := (hYU t).2
    rw [div_mul_eq_mul_div, div_lt_one hE0] at h2
    have : 0 < E - μ * ‖field (1 / 4) (Y t)‖ := by linarith
    exact Real.sqrt_pos.2 (by positivity)

/-- **Sanity**: the normalisation `ρ₀ = (m/q)√(2E/m) = 1/256` is attained (`m = q = 1`,
`E = 1/131072`). -/
theorem rho0_param_alpha : (1 : ℝ) / 1 * √(2 * (1 / 131072) / 1) = 1 / 256 := by
  rw [show (2 : ℝ) * (1 / 131072) / 1 = (1 / 256) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  norm_num

/-! ## SI units -/

/-- `√(2E₁/m₁) = √(2E/m)/R₀` for the model parameters `E₁ = E/(B₀R₀²)`, `m₁ = m/B₀`. -/
theorem sqrt_model_param {m E B₀ R₀ : ℝ} (hm : 0 < m) (hB₀ : 0 < B₀) (hR₀ : 0 < R₀) :
    √(2 * (E / (B₀ * R₀ ^ 2)) / (m / B₀)) = √(2 * E / m) / R₀ := by
  rw [show 2 * (E / (B₀ * R₀ ^ 2)) / (m / B₀) = (2 * E / m) / R₀ ^ 2 by field_simp,
    Real.sqrt_div' _ (by positivity), Real.sqrt_sq hR₀.le]

/-- **All-time confinement of `μ > 0` passing guiding centres in SI units** (Littlejohn model).
Let `m > 0`, `q ≠ 0`, `E > 0`, `B₀, R₀ > 0` with `m √(2E/m)/(q B₀ R₀) = 1/256`, and
`μ ∈ [0, E/(16B₀)]` (pitch angles with `sin²χ = μ|B|/E ≤ |B|/(16B₀)`). In the field
`fieldSI B₀ R₀` there is a torus profile `P` (`0.03 ≤ P ≤ 0.255` in units of `R₀`) such that every
Littlejohn orbit with energy `E`, magnetic moment `μ` and `v_∥(0) > 0` starting (in the scaled
coordinates `X/R₀`) on the axis or inside the torus stays inside it for all time and stays passing
(`v_∥ > 0`); from every such starting point there is such an orbit. -/
theorem gc_mu_passing_confined_forever_SI {m q E B₀ R₀ μ : ℝ} (hm : 0 < m) (hq : q ≠ 0)
    (hE : 0 < E) (hB₀ : 0 < B₀) (hR₀ : 0 < R₀) (hρ : m * √(2 * E / m) / (q * B₀ * R₀) = 1 / 256)
    (hμ : μ ∈ Set.Icc (0 : ℝ) (E / (16 * B₀))) :
    ∃ P : ℝ → ℝ → ℝ, TorusProfile P ∧ (∀ a b, 3 / 100 ≤ P a b) ∧ (∀ a b, P a b ≤ 255 / 1000) ∧
      (∀ (X : ℝ → Space) (v : ℝ → ℝ), LittlejohnOrbit m q μ (fieldSI B₀ R₀) X v →
        hamiltonian m μ (fieldSI B₀ R₀) (X 0) (v 0) = E → 0 < v 0 →
        (rt (R₀⁻¹ • X 0) = 0 ∨ rt (R₀⁻¹ • X 0) < P (θs (R₀⁻¹ • X 0)) (φs (R₀⁻¹ • X 0))) →
        ∀ t, rt (R₀⁻¹ • X t) ≤ 255 / 1000 ∧
          (rt (R₀⁻¹ • X t) = 0 ∨ rt (R₀⁻¹ • X t) < P (θs (R₀⁻¹ • X t)) (φs (R₀⁻¹ • X t))) ∧
          0 < v t) ∧
      ∀ x₀ : Space,
        (rt (R₀⁻¹ • x₀) = 0 ∨ rt (R₀⁻¹ • x₀) < P (θs (R₀⁻¹ • x₀)) (φs (R₀⁻¹ • x₀))) →
        ∃ (X : ℝ → Space) (v : ℝ → ℝ), LittlejohnOrbit m q μ (fieldSI B₀ R₀) X v ∧ X 0 = x₀ ∧
          hamiltonian m μ (fieldSI B₀ R₀) (X 0) (v 0) = E ∧ ∀ t, 0 < v t := by
  set lm := μ * B₀ / E with hlmdef
  have hlm : lm ∈ Set.Icc (0 : ℝ) (1 / 16) := by
    refine ⟨by have := hμ.1; positivity, ?_⟩
    have h2 := hμ.2
    rw [le_div_iff₀ (by positivity)] at h2
    rw [hlmdef, div_le_iff₀ hE]; linarith
  obtain ⟨P, hP, hlo, hhi, hconf, hex⟩ := rationalStellarator_gc_mu_confined_forever hlm
  have hB : B₀ ≠ 0 := hB₀.ne'
  have hR : R₀ ≠ 0 := hR₀.ne'
  set E₁ := E / (B₀ * R₀ ^ 2) with hE₁
  have hE1 : 0 < E₁ := by positivity
  have hρ₁ : m / B₀ / q * √(2 * E₁ / (m / B₀)) = 1 / 256 := by
    rw [hE₁, sqrt_model_param hm hB₀ hR₀, ← hρ]; field_simp
  have hμ₁ : μ / R₀ ^ 2 = lm * E₁ := by rw [hlmdef, hE₁]; field_simp
  refine ⟨P, hP, hlo, hhi, fun X v h hH hv0 h0 t => ?_, fun x₀ h0 => ?_⟩
  · have h1 := (littlejohnSI_iff hB₀ hR₀).1 h
    have hH1 : hamiltonian (m / B₀) (μ / R₀ ^ 2) (field (1 / 4)) (R₀⁻¹ • X 0) (v 0 / R₀) = E₁ := by
      rw [hamiltonian_fieldSI hB₀ hR₀] at hH
      rw [hE₁, ← hH]; field_simp
    obtain ⟨r1, r2, -, r4⟩ := hconf (m / B₀) q (μ / R₀ ^ 2) E₁ _ _ (by positivity) hq hE1 hρ₁ hμ₁
      h1 hH1 (by positivity) h0 t
    exact ⟨r1, r2, by
      have : 0 < v t / R₀ := r4
      exact (div_pos_iff_of_pos_right hR₀).1 this⟩
  · obtain ⟨Y, hY, hY0, hpos⟩ := hex (m / B₀) q (μ / R₀ ^ 2) E₁ (R₀⁻¹ • x₀) (by positivity) hq hE1
      hρ₁ hμ₁ h0
    set w := fun t => √(2 * (E₁ - μ / R₀ ^ 2 * ‖field (1 / 4) (Y t)‖) / (m / B₀)) with hw
    refine ⟨fun t => R₀ • Y t, fun t => R₀ * w t, ?_, ?_, ?_, fun t => ?_⟩
    · rw [littlejohnSI_iff hB₀ hR₀]
      have e1 : (fun t => R₀⁻¹ • R₀ • Y t) = Y := by
        funext t; rw [smul_smul, inv_mul_cancel₀ hR, one_smul]
      have e2 : (fun t => R₀ * w t / R₀) = w := by funext t; field_simp
      rw [e1, e2]; exact hY
    · change R₀ • Y 0 = x₀
      rw [hY0, smul_smul, mul_inv_cancel₀ hR, one_smul]
    · rw [hamiltonian_fieldSI hB₀ hR₀]
      have e1 : R₀⁻¹ • R₀ • Y 0 = Y 0 := by rw [smul_smul, inv_mul_cancel₀ hR, one_smul]
      have e2 : R₀ * w 0 / R₀ = w 0 := by field_simp
      rw [e1, e2, hamiltonian]
      have hp := hpos 0
      have hs : w 0 ^ 2 = 2 * (E₁ - μ / R₀ ^ 2 * ‖field (1 / 4) (Y 0)‖) / (m / B₀) :=
        Real.sq_sqrt (Real.sqrt_pos.1 hp).le
      rw [hs, hE₁]
      field_simp
      ring
    · exact mul_pos hR₀ (hpos t)

/-- **All-time confinement of passing 3.5 MeV alpha guiding centres with `μ > 0`** (Littlejohn
model; a positive-measure set of pitch angles). Let `m ∈ [6.6446, 6.6447] × 10⁻²⁷ kg`,
`e ∈ [1.6021, 1.6022] × 10⁻¹⁹ C`, `q = 2e`, energy `K = 3.5 MeV = 3.5 × 10⁶ e` J, and
`B₀R₀ = 256 m √(2K/m)/(2e)`. Then `B₀R₀ ∈ [68.9, 69] T·m` (`alpha_B0R0_bounds`), and for
**every** magnetic moment `μ ∈ [0, K/(16B₀)]` (initial pitch angles with `sin²χ ≤ |B|/(16B₀)`, up
to `≈ 14.5°` near the axis — informal: `arcsin(1/4)`, position dependent) there is a torus
profile `P` (`0.03 ≤ P ≤ 0.255` in units of `R₀`)
such that every passing (`v_∥(0) > 0`) guiding-centre orbit with energy `K` and moment `μ`
starting on the axis or inside the scaled torus stays inside it, within `0.255 R₀` of the magnetic
axis, and passing, for all time; such orbits exist from every starting point inside. -/
theorem alpha_gc_passing_confined_forever {m e B₀ R₀ μ : ℝ} (hm1 : 6.6446e-27 ≤ m)
    (hm2 : m ≤ 6.6447e-27) (he1 : 1.6021e-19 ≤ e) (he2 : e ≤ 1.6022e-19) (hB₀ : 0 < B₀)
    (hR₀ : 0 < R₀) (hBR : B₀ * R₀ = 256 * m * √(2 * (3.5e6 * e) / m) / (2 * e))
    (hμ : μ ∈ Set.Icc (0 : ℝ) (3.5e6 * e / (16 * B₀))) :
    68.9 ≤ B₀ * R₀ ∧ B₀ * R₀ ≤ 69 ∧
    ∃ P : ℝ → ℝ → ℝ, TorusProfile P ∧ (∀ a b, 3 / 100 ≤ P a b) ∧ (∀ a b, P a b ≤ 255 / 1000) ∧
      (∀ (X : ℝ → Space) (v : ℝ → ℝ), LittlejohnOrbit m (2 * e) μ (fieldSI B₀ R₀) X v →
        hamiltonian m μ (fieldSI B₀ R₀) (X 0) (v 0) = 3.5e6 * e → 0 < v 0 →
        (rt (R₀⁻¹ • X 0) = 0 ∨ rt (R₀⁻¹ • X 0) < P (θs (R₀⁻¹ • X 0)) (φs (R₀⁻¹ • X 0))) →
        ∀ t, rt (R₀⁻¹ • X t) ≤ 255 / 1000 ∧
          (rt (R₀⁻¹ • X t) = 0 ∨ rt (R₀⁻¹ • X t) < P (θs (R₀⁻¹ • X t)) (φs (R₀⁻¹ • X t))) ∧
          0 < v t) ∧
      ∀ x₀ : Space,
        (rt (R₀⁻¹ • x₀) = 0 ∨ rt (R₀⁻¹ • x₀) < P (θs (R₀⁻¹ • x₀)) (φs (R₀⁻¹ • x₀))) →
        ∃ (X : ℝ → Space) (v : ℝ → ℝ), LittlejohnOrbit m (2 * e) μ (fieldSI B₀ R₀) X v ∧
          X 0 = x₀ ∧ hamiltonian m μ (fieldSI B₀ R₀) (X 0) (v 0) = 3.5e6 * e ∧ ∀ t, 0 < v t := by
  have hm : 0 < m := by linarith
  have he : 0 < e := by linarith
  obtain ⟨b1, b2⟩ := alpha_B0R0_bounds hm1 hm2 he1 he2
  refine ⟨by rw [hBR]; exact b1, by rw [hBR]; exact b2, ?_⟩
  refine gc_mu_passing_confined_forever_SI hm (by positivity) (by positivity) hB₀ hR₀ ?_ hμ
  rw [show 2 * e * B₀ * R₀ = 2 * e * (B₀ * R₀) by ring, hBR]
  have : 0 < √(2 * (3.5e6 * e) / m) := Real.sqrt_pos.2 (by positivity)
  field_simp

end PlasmaLean.Design.RationalStellaratorGC
