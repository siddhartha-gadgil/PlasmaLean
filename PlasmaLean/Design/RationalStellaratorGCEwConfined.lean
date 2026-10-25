/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCEwForever
public import PlasmaLean.Design.RationalStellaratorGCBoxConfined

/-!
# All-time confinement of alpha guiding centres over an energy window of ±0.4 eV

**Model assumption.** Guiding centres move according to the Littlejohn guiding-centre equations
(`Theory/Kinetic/GuidingCentreLittlejohn`, `LittlejohnOrbit`), a supplied model, not derived from
the Lorentz force. Non-relativistic, collisionless (no slowing-down or pitch-angle scattering, so
`E` and `μ` are constants of the motion), static vacuum model field `field (1/4)` (the rational
stellarator, not coil-produced), scaled to `fieldSI B₀ R₀`.

**Main results.**

* `rationalStellarator_gc_ew_confined_forever` (model units): for every gyro-length
  `ρ ∈ rhoEw = [1/256 − 2⁻³², 1/256 + 2⁻³²]` and every `λ = μ/E ∈ [0, 1/16]` there is a torus
  profile `P` (`0.03 ≤ P ≤ 0.255`) trapping every passing (`v_∥(0) > 0`) Littlejohn orbit that
  starts on the axis or inside it, for all time; it stays passing; such orbits exist.
* `gc_ew_passing_confined_forever_SI`: the same in SI units.
* `alpha_gc_ew_confined_forever` and **`alpha_gc_confined_forever_energy_window`**: 3.5 MeV-design
  alphas at the **fixed** `B₀R₀ = 256 m √(2K/m)/(2e) ∈ [68.9, 69] T·m`: every energy
  `E ∈ [(1 − 2⁻²⁴)² K, (1 + 2⁻²⁴)² K] ⊇ [K − 0.4 eV, K + 0.4 eV]` and every `μ ∈ [0, E/(16B₀)]`.
* `alpha_gc_ew_confined_forever_velocity_set` and **`alphaEwVel_volume_pos`**: at every starting
  point within `0.03 R₀` of the axis, the set of initial velocities with kinetic energy in
  `[(1 − 2⁻²⁴)² K, (1 + 2⁻²⁴)² K]`, `⟨w, b⟩ > 0` and `sin²χ ≤ |B(x₀)|/(16 B₀)` has positive
  Lebesgue measure in `ℝ³`, and all its guiding-centre orbits stay confined and passing.

**Size.** Relative energy width `≈ 2.4 × 10⁻⁷` (`±0.417 eV` at 3.5 MeV) times the full pitch-angle
cell; about `3 × 10¹⁶` times the frozen-torus box of `Design/RationalStellaratorGCBoxConfined`.
The width is set by the admissibility balls (radius `1.18 × 10⁻⁸`) of the certified low-resolution
chain: the family torus moves by `≈ 30 · 2⁻³²` in `u`.

**Proof.** `ew_family_master` (`Design/RationalStellaratorGCEwForever`) and the bootstrap
`littlejohn_mu_eq_fieldLine`, exactly as in `Design/RationalStellaratorGCBoxConfined`.

**Sanity.** `alpha_rho_mem_ew`: the design energy `K` itself lies in the window.
-/

open scoped RealInnerProductSpace

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open Real Set PlasmaLean.Fields PlasmaLean.Design.RationalStellarator PlasmaLean.Design.KamTorusA
  PlasmaLean.Kinetic.GCLittlejohn WithLp MeasureTheory

/-- **All-time confinement of passing guiding centres over the energy window** (Littlejohn model,
model
units `R₀ = B₀ = 1`, `B = field (1/4)`). For every gyro-length `ρ ∈ rhoEw` and every
`λ ∈ [0, 1/16]` there is a torus profile `P` with `0.03 ≤ P ≤ 0.255` such that for all `m > 0`,
`q ≠ 0`, `E > 0` with `(m/q)√(2E/m) = ρ` and `μ = λE`:

* every Littlejohn orbit `(X, v_∥)` with energy `E` and `v_∥(0) > 0` starting on the axis or inside
  the torus stays inside it for all time and stays passing, `v_∥(t) = √(2(E − μ|B(X t)|)/m) > 0`;
* from every point `x₀` on the axis or inside the torus there is such an orbit with `X 0 = x₀`. -/
theorem rationalStellarator_gc_ew_confined_forever {ρ lm : ℝ} (hρ : ρ ∈ rhoEw)
    (hlm : lm ∈ Set.Icc (0 : ℝ) (1 / 16)) :
    ∃ P : ℝ → ℝ → ℝ, TorusProfile P ∧ (∀ a b, 3 / 100 ≤ P a b) ∧ (∀ a b, P a b ≤ 255 / 1000) ∧
      (∀ (m q μ E : ℝ) (X : ℝ → Space) (v : ℝ → ℝ), 0 < m → q ≠ 0 → 0 < E →
        m / q * √(2 * E / m) = ρ → μ = lm * E →
        LittlejohnOrbit m q μ (field (1 / 4)) X v →
        hamiltonian m μ (field (1 / 4)) (X 0) (v 0) = E → 0 < v 0 →
        (rt (X 0) = 0 ∨ rt (X 0) < P (θs (X 0)) (φs (X 0))) →
        ∀ t, rt (X t) ≤ 255 / 1000 ∧ (rt (X t) = 0 ∨ rt (X t) < P (θs (X t)) (φs (X t))) ∧
          v t = √(2 * (E - μ * ‖field (1 / 4) (X t)‖) / m) ∧ 0 < v t) ∧
      ∀ (m q μ E : ℝ) (x₀ : Space), 0 < m → q ≠ 0 → 0 < E →
        m / q * √(2 * E / m) = ρ → μ = lm * E →
        (rt x₀ = 0 ∨ rt x₀ < P (θs x₀) (φs x₀)) →
        ∃ X : ℝ → Space, LittlejohnOrbit m q μ (field (1 / 4)) X
          (fun t => √(2 * (E - μ * ‖field (1 / 4) (X t)‖) / m)) ∧ X 0 = x₀ ∧
          ∀ t, 0 < √(2 * (E - μ * ‖field (1 / 4) (X t)‖) / m) := by
  obtain ⟨P, hP, hlo, hhi, -, -, hE, hV⟩ := ew_family_master hρ hlm
  have hKU := tube27_subset_muRegion hlm
  have hK : IsCompact {y : Space | rt y ≤ 255 / 1000} := isCompact_rtLe' (by norm_num)
  have hKU' : {y : Space | rt y ≤ 255 / 1000} ⊆ muRegion lm := fun y hy =>
    hKU y (le_trans (show rt y ≤ 255 / 1000 from hy) (by norm_num))
  have hlE : ∀ {μ E : ℝ}, 0 < E → μ = lm * E → μ / E = lm := fun hE h => by
    rw [h]; field_simp
  refine ⟨P, hP, hlo, hhi, fun m q μ E X v hm hq hE0 hρE hμ h hH hv0 h0 => ?_,
    fun m q μ E x₀ hm hq hE0 hρE hμ h0 => ?_⟩
  · have hc : √(2 * E / m) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
    obtain ⟨Y, ⟨hY, hY0⟩, -⟩ := hE _ hc (X 0) h0
    have htrap := hV _ hc Y hY (by rw [hY0]; exact h0)
    rw [← hρE, ← hlE hE0 hμ] at hY
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
    rw [← hρE, ← hlE hE0 hμ] at hY
    refine ⟨Y, littlejohn_of_fieldLine hm hq hE0 hY hYU, hY0, fun t => ?_⟩
    have h2 := (hYU t).2
    rw [div_mul_eq_mul_div, div_lt_one hE0] at h2
    have : 0 < E - μ * ‖field (1 / 4) (Y t)‖ := by linarith
    exact Real.sqrt_pos.2 (by positivity)


/-! ## SI units -/

/-- **All-time confinement of `μ > 0` passing guiding centres over the energy window, in SI units**
(Littlejohn model). Let `m > 0`, `q ≠ 0`, `E > 0`, `B₀, R₀ > 0` with
`m √(2E/m)/(q B₀ R₀) ∈ rhoEw` and `μ ∈ [0, E/(16B₀)]`. In the field `fieldSI B₀ R₀` there is a
torus profile `P` (`0.03 ≤ P ≤ 0.255` in units of `R₀`) such that every Littlejohn orbit with
energy `E`, magnetic moment `μ` and `v_∥(0) > 0` starting (in the scaled coordinates `X/R₀`) on
the axis or inside the torus stays inside it for all time and stays passing; from every such
starting point there is such an orbit. -/
theorem gc_ew_passing_confined_forever_SI {m q E B₀ R₀ μ : ℝ} (hm : 0 < m) (hq : q ≠ 0)
    (hE : 0 < E) (hB₀ : 0 < B₀) (hR₀ : 0 < R₀) (hρ : m * √(2 * E / m) / (q * B₀ * R₀) ∈ rhoEw)
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
  obtain ⟨P, hP, hlo, hhi, hconf, hex⟩ := rationalStellarator_gc_ew_confined_forever hρ hlm
  have hB : B₀ ≠ 0 := hB₀.ne'
  have hR : R₀ ≠ 0 := hR₀.ne'
  set E₁ := E / (B₀ * R₀ ^ 2) with hE₁
  have hE1 : 0 < E₁ := by positivity
  have hρ₁ : m / B₀ / q * √(2 * E₁ / (m / B₀)) = m * √(2 * E / m) / (q * B₀ * R₀) := by
    rw [hE₁, sqrt_model_param hm hB₀ hR₀]; field_simp
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


/-- **The gyro-length of an alpha of energy `E ∈ [(1 − 2⁻²⁴)² K, (1 + 2⁻²⁴)² K]` at the design
`B₀R₀` lies in the energy window** `|ρ − 1/256| ≤ 2⁻³²`. -/
theorem alpha_rho_mem_ew {m e E : ℝ} (hm : 0 < m) (he : 0 < e)
    (hE1 : (1 - 1 / 2 ^ 24) ^ 2 * alphaK e ≤ E) (hE2 : E ≤ (1 + 1 / 2 ^ 24) ^ 2 * alphaK e) :
    m * √(2 * E / m) / (2 * e * alphaBR m e) ∈ rhoEw := by
  have hK : 0 < alphaK e := by rw [alphaK]; positivity
  set s := √(2 * E / m) with hs
  set s₀ := √(2 * alphaK e / m) with hs₀
  have hs₀p : 0 < s₀ := Real.sqrt_pos.2 (by positivity)
  have key : m * s / (2 * e * alphaBR m e) = s / (256 * s₀) := by
    rw [alphaBR, ← hs₀]; field_simp
  have hε : (0 : ℝ) ≤ 1 - 1 / 2 ^ 24 := by norm_num
  have hε' : (0 : ℝ) ≤ 1 + 1 / 2 ^ 24 := by norm_num
  have h1 : s ≤ (1 + 1 / 2 ^ 24) * s₀ := by
    have e1 : (1 + 1 / 2 ^ 24) * s₀ = √((1 + 1 / 2 ^ 24) ^ 2 * (2 * alphaK e / m)) := by
      rw [Real.sqrt_mul' _ (by positivity), Real.sqrt_sq hε']
    rw [e1]
    refine Real.sqrt_le_sqrt ?_
    rw [show (1 + 1 / 2 ^ 24 : ℝ) ^ 2 * (2 * alphaK e / m) =
      2 * ((1 + 1 / 2 ^ 24) ^ 2 * alphaK e) / m by ring]
    gcongr
  have h2 : (1 - 1 / 2 ^ 24) * s₀ ≤ s := by
    have e1 : (1 - 1 / 2 ^ 24) * s₀ = √((1 - 1 / 2 ^ 24) ^ 2 * (2 * alphaK e / m)) := by
      rw [Real.sqrt_mul' _ (by positivity), Real.sqrt_sq hε]
    rw [e1]
    refine Real.sqrt_le_sqrt ?_
    rw [show (1 - 1 / 2 ^ 24 : ℝ) ^ 2 * (2 * alphaK e / m) =
      2 * ((1 - 1 / 2 ^ 24) ^ 2 * alphaK e) / m by ring]
    gcongr
  rw [key, rhoEw, hEw]
  constructor
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_le_iff₀ (by positivity)]; nlinarith

/-- **All-time confinement of passing alpha guiding centres over the energy window and the
pitch-angle cell** (Littlejohn model). Let `m ∈ [6.6446, 6.6447] × 10⁻²⁷ kg`,
`e ∈ [1.6021, 1.6022] ×
10⁻¹⁹ C`, `q = 2e`, `K = 3.5 MeV`, and fix `B₀R₀ = 256 m √(2K/m)/(2e)` (`∈ [68.9, 69] T·m`). For
**every** energy `E ∈ [(1 − 2⁻²⁴)² K, (1 + 2⁻²⁴)² K]` and **every** magnetic moment
`μ ∈ [0, E/(16B₀)]` there
is a torus profile `P` (`0.03 ≤ P ≤ 0.255` in units of `R₀`) such that every passing guiding-centre
orbit with energy `E` and moment `μ` starting on the axis or inside the scaled torus stays inside
it and passing for all time; such orbits exist from every starting point inside. -/
theorem alpha_gc_ew_confined_forever {m e B₀ R₀ E μ : ℝ} (hm1 : 6.6446e-27 ≤ m)
    (hm2 : m ≤ 6.6447e-27) (he1 : 1.6021e-19 ≤ e) (he2 : e ≤ 1.6022e-19) (hB₀ : 0 < B₀)
    (hR₀ : 0 < R₀) (hBR : B₀ * R₀ = alphaBR m e)
    (hE1 : (1 - 1 / 2 ^ 24) ^ 2 * alphaK e ≤ E) (hE2 : E ≤ (1 + 1 / 2 ^ 24) ^ 2 * alphaK e)
    (hμ : μ ∈ Set.Icc (0 : ℝ) (E / (16 * B₀))) :
    68.9 ≤ B₀ * R₀ ∧ B₀ * R₀ ≤ 69 ∧
    ∃ P : ℝ → ℝ → ℝ, TorusProfile P ∧ (∀ a b, 3 / 100 ≤ P a b) ∧ (∀ a b, P a b ≤ 255 / 1000) ∧
      (∀ (X : ℝ → Space) (v : ℝ → ℝ), LittlejohnOrbit m (2 * e) μ (fieldSI B₀ R₀) X v →
        hamiltonian m μ (fieldSI B₀ R₀) (X 0) (v 0) = E → 0 < v 0 →
        (rt (R₀⁻¹ • X 0) = 0 ∨ rt (R₀⁻¹ • X 0) < P (θs (R₀⁻¹ • X 0)) (φs (R₀⁻¹ • X 0))) →
        ∀ t, rt (R₀⁻¹ • X t) ≤ 255 / 1000 ∧
          (rt (R₀⁻¹ • X t) = 0 ∨ rt (R₀⁻¹ • X t) < P (θs (R₀⁻¹ • X t)) (φs (R₀⁻¹ • X t))) ∧
          0 < v t) ∧
      ∀ x₀ : Space,
        (rt (R₀⁻¹ • x₀) = 0 ∨ rt (R₀⁻¹ • x₀) < P (θs (R₀⁻¹ • x₀)) (φs (R₀⁻¹ • x₀))) →
        ∃ (X : ℝ → Space) (v : ℝ → ℝ), LittlejohnOrbit m (2 * e) μ (fieldSI B₀ R₀) X v ∧
          X 0 = x₀ ∧ hamiltonian m μ (fieldSI B₀ R₀) (X 0) (v 0) = E ∧ ∀ t, 0 < v t := by
  have hm : 0 < m := by linarith
  have he : 0 < e := by linarith
  obtain ⟨b1, b2⟩ := alpha_B0R0_bounds hm1 hm2 he1 he2
  have hK : 0 < alphaK e := by rw [alphaK]; positivity
  have hE : 0 < E := lt_of_lt_of_le (by positivity) hE1
  refine ⟨by rw [hBR, alphaBR, alphaK]; exact b1, by rw [hBR, alphaBR, alphaK]; exact b2, ?_⟩
  refine gc_ew_passing_confined_forever_SI hm (by positivity) hE hB₀ hR₀ ?_ hμ
  rw [show 2 * e * B₀ * R₀ = 2 * e * (B₀ * R₀) by ring, hBR]
  exact alpha_rho_mem_ew hm he hE1 hE2

/-- **All-time confinement of passing alpha guiding centres over the energy window
`E ∈ [3.5 MeV − 0.4 eV, 3.5 MeV + 0.4 eV]`** (Littlejohn model; non-relativistic, collisionless,
static vacuum model field). Alpha mass and charge as in `alpha_gc_ew_confined_forever`, the fixed
design `B₀R₀ = 256 m √(2K/m)/(2e)`: for every energy `E` with `|E − K| ≤ 0.4 eV` (`eV = e` joules)
and every magnetic moment `μ ∈ [0, E/(16B₀)]` (`λ ∈ [0, 1/16]`) there is a torus profile `P`
(`0.03 ≤ P ≤ 0.255`) such that every passing guiding-centre orbit (`v_∥ > 0`) with energy `E` and
moment `μ` starting on the axis or inside the scaled torus stays inside it, within `0.255 R₀` of the
axis, and passing, for all time; such orbits exist from every starting point inside. -/
theorem alpha_gc_confined_forever_energy_window {m e B₀ R₀ E μ : ℝ} (hm1 : 6.6446e-27 ≤ m)
    (hm2 : m ≤ 6.6447e-27) (he1 : 1.6021e-19 ≤ e) (he2 : e ≤ 1.6022e-19) (hB₀ : 0 < B₀)
    (hR₀ : 0 < R₀) (hBR : B₀ * R₀ = alphaBR m e) (hE : |E - alphaK e| ≤ 0.4 * e)
    (hμ : μ ∈ Set.Icc (0 : ℝ) (E / (16 * B₀))) :
    68.9 ≤ B₀ * R₀ ∧ B₀ * R₀ ≤ 69 ∧
    ∃ P : ℝ → ℝ → ℝ, TorusProfile P ∧ (∀ a b, 3 / 100 ≤ P a b) ∧ (∀ a b, P a b ≤ 255 / 1000) ∧
      (∀ (X : ℝ → Space) (v : ℝ → ℝ), LittlejohnOrbit m (2 * e) μ (fieldSI B₀ R₀) X v →
        hamiltonian m μ (fieldSI B₀ R₀) (X 0) (v 0) = E → 0 < v 0 →
        (rt (R₀⁻¹ • X 0) = 0 ∨ rt (R₀⁻¹ • X 0) < P (θs (R₀⁻¹ • X 0)) (φs (R₀⁻¹ • X 0))) →
        ∀ t, rt (R₀⁻¹ • X t) ≤ 255 / 1000 ∧
          (rt (R₀⁻¹ • X t) = 0 ∨ rt (R₀⁻¹ • X t) < P (θs (R₀⁻¹ • X t)) (φs (R₀⁻¹ • X t))) ∧
          0 < v t) ∧
      ∀ x₀ : Space,
        (rt (R₀⁻¹ • x₀) = 0 ∨ rt (R₀⁻¹ • x₀) < P (θs (R₀⁻¹ • x₀)) (φs (R₀⁻¹ • x₀))) →
        ∃ (X : ℝ → Space) (v : ℝ → ℝ), LittlejohnOrbit m (2 * e) μ (fieldSI B₀ R₀) X v ∧
          X 0 = x₀ ∧ hamiltonian m μ (fieldSI B₀ R₀) (X 0) (v 0) = E ∧ ∀ t, 0 < v t := by
  have he : 0 < e := by linarith
  have h := abs_le.mp hE
  refine alpha_gc_ew_confined_forever hm1 hm2 he1 he2 hB₀ hR₀ hBR ?_ ?_ hμ
  · rw [alphaK] at h ⊢; nlinarith
  · rw [alphaK] at h ⊢; nlinarith

/-- **The velocity set** at `x₀`: initial velocity vectors `w ∈ ℝ³` with kinetic energy in
`[(1 − 2⁻²⁴)² K, (1 + 2⁻²⁴)² K]`, `v_∥ = ⟨w, b(x₀)⟩ > 0` and `μ(w) B₀ ≤ E/16` (pitch angles with
`sin²χ ≤ |B(x₀)|/(16 B₀)`). -/
def alphaEwVel (m K B₀ : ℝ) (B : Space → Space) (x₀ : Space) : Set Space :=
  {w | (1 - 1 / 2 ^ 24) ^ 2 * K ≤ kinE m w ∧ kinE m w ≤ (1 + 1 / 2 ^ 24) ^ 2 * K ∧
    0 < vParOf B x₀ w ∧
    muOf m B x₀ w ≤ kinE m w / (16 * B₀)}

/-- **All-time confinement of alpha guiding centres for a positive-measure set of initial
velocities** (Littlejohn model; non-relativistic, collisionless, static vacuum model field).
Alpha mass and charge as in `alpha_gc_ew_confined_forever`, `K = 3.5 MeV`, and the fixed
`B₀R₀ = 256 m √(2K/m)/(2e)`. Let `x₀` be a starting point within `0.03 R₀` of the magnetic axis
(`rt(x₀/R₀) < 0.03`) and `w ∈ alphaEwVel` an initial velocity vector (energy in
`[(1 − 2⁻²⁴)² K, (1 + 2⁻²⁴)² K]`, `⟨w, b⟩ > 0`, `sin²χ ≤ |B(x₀)|/(16B₀)`). Then there is a torus
profile `P`
(`0.03 ≤ P ≤ 0.255`) such that every Littlejohn orbit with magnetic moment `μ(w)`, `X(0) = x₀` and
`v_∥(0) = ⟨w, b(x₀)⟩` stays inside the torus, within `0.255 R₀` of the axis, and passing, for all
time; and such an orbit exists. -/
theorem alpha_gc_ew_confined_forever_velocity_set {m e B₀ R₀ : ℝ} (hm1 : 6.6446e-27 ≤ m)
    (hm2 : m ≤ 6.6447e-27) (he1 : 1.6021e-19 ≤ e) (he2 : e ≤ 1.6022e-19) (hB₀ : 0 < B₀)
    (hR₀ : 0 < R₀) (hBR : B₀ * R₀ = alphaBR m e) {x₀ : Space} (hx₀ : rt (R₀⁻¹ • x₀) < 3 / 100)
    {w : Space} (hw : w ∈ alphaEwVel m (alphaK e) B₀ (fieldSI B₀ R₀) x₀) :
    ∃ P : ℝ → ℝ → ℝ, TorusProfile P ∧ (∀ a b, 3 / 100 ≤ P a b) ∧ (∀ a b, P a b ≤ 255 / 1000) ∧
      (∀ (X : ℝ → Space) (v : ℝ → ℝ),
        LittlejohnOrbit m (2 * e) (muOf m (fieldSI B₀ R₀) x₀ w) (fieldSI B₀ R₀) X v →
        X 0 = x₀ → v 0 = vParOf (fieldSI B₀ R₀) x₀ w →
        ∀ t, rt (R₀⁻¹ • X t) ≤ 255 / 1000 ∧
          (rt (R₀⁻¹ • X t) = 0 ∨ rt (R₀⁻¹ • X t) < P (θs (R₀⁻¹ • X t)) (φs (R₀⁻¹ • X t))) ∧
          0 < v t) ∧
      ∃ (X : ℝ → Space) (v : ℝ → ℝ),
        LittlejohnOrbit m (2 * e) (muOf m (fieldSI B₀ R₀) x₀ w) (fieldSI B₀ R₀) X v ∧
        X 0 = x₀ ∧ v 0 = vParOf (fieldSI B₀ R₀) x₀ w ∧ ∀ t, 0 < v t := by
  obtain ⟨hE1, hE2, hv, hμ2⟩ := hw
  have hm : 0 < m := by linarith
  have he : 0 < e := by linarith
  have hBx : fieldSI B₀ R₀ x₀ ≠ 0 := fieldSI_ne_zero hB₀ (by linarith)
  have hμ0 : 0 ≤ muOf m (fieldSI B₀ R₀) x₀ w := by rw [muOf]; positivity
  obtain ⟨-, -, P, hP, hlo, hhi, hconf, hex⟩ := alpha_gc_ew_confined_forever hm1 hm2 he1 he2
    hB₀ hR₀ hBR hE1 hE2 ⟨hμ0, hμ2⟩
  have hstart : ∀ y : Space, rt (R₀⁻¹ • y) < 3 / 100 →
      (rt (R₀⁻¹ • y) = 0 ∨ rt (R₀⁻¹ • y) < P (θs (R₀⁻¹ • y)) (φs (R₀⁻¹ • y))) :=
    fun y hy => Or.inr (lt_of_lt_of_le hy (hlo _ _))
  have hH := hamiltonian_vParOf (m := m) hBx w
  refine ⟨P, hP, hlo, hhi, fun X v h hX0 hv0 t => ?_, ?_⟩
  · have hH' : hamiltonian m (muOf m (fieldSI B₀ R₀) x₀ w) (fieldSI B₀ R₀) (X 0) (v 0) =
        kinE m w := by rw [hX0, hv0]; exact hH
    exact hconf X v h hH' (by rw [hv0]; exact hv) (by rw [hX0]; exact hstart x₀ hx₀) t
  · obtain ⟨X, v, h, hX0, hH', hpos⟩ := hex x₀ (hstart x₀ hx₀)
    refine ⟨X, v, h, hX0, ?_, hpos⟩
    rw [hX0, ← hH] at hH'
    simp only [hamiltonian] at hH'
    have hsq : v 0 ^ 2 = vParOf (fieldSI B₀ R₀) x₀ w ^ 2 := by
      have := mul_left_cancel₀ hm.ne' (show m * (v 0 ^ 2) = m * (vParOf (fieldSI B₀ R₀) x₀ w ^ 2)
        by linarith)
      exact this
    exact (pow_left_inj₀ (hpos 0).le hv.le (by norm_num)).1 hsq

/-- **The velocity set has positive Lebesgue measure in `ℝ³`** (at every starting point within
`0.03 R₀` of the magnetic axis, for `m, K, B₀ > 0`): it contains a nonempty open set. -/
theorem alphaEwVel_volume_pos {m K B₀ R₀ : ℝ} (hm : 0 < m) (hK : 0 < K) (hB₀ : 0 < B₀)
    {x₀ : Space} (hx₀ : rt (R₀⁻¹ • x₀) < 3 / 100) :
    0 < volume (alphaEwVel m K B₀ (fieldSI B₀ R₀) x₀) := by
  set B := fieldSI B₀ R₀ with hBdef
  have hBx : B x₀ ≠ 0 := fieldSI_ne_zero hB₀ (by linarith)
  have hb := norm_bhat_eq_one hBx
  set ε : ℝ := 1 / 2 ^ 24 with hε
  set U : Set Space := {w | (1 - ε) ^ 2 * K < kinE m w ∧ kinE m w < (1 + ε) ^ 2 * K ∧
    0 < vParOf B x₀ w ∧
    muOf m B x₀ w < kinE m w / (16 * B₀)} with hU
  have hcE : Continuous (kinE m) := by unfold kinE; fun_prop
  have hcV : Continuous (vParOf B x₀) := by unfold vParOf; fun_prop
  have hcM : Continuous (muOf m B x₀) := by unfold muOf; fun_prop
  have hUo : IsOpen U :=
    ((isOpen_lt continuous_const hcE).inter (isOpen_lt hcE continuous_const)).inter
      ((isOpen_lt continuous_const hcV).inter (isOpen_lt hcM (hcE.div_const _))) |>.preimage
        continuous_id |> fun h => by
          simpa [hU, Set.ofPred_and, Set.inter_assoc] using h
  set s : ℝ := √(2 * K / m) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = 2 * K / m := Real.sq_sqrt (by positivity)
  have hk : kinE m (s • bhat B x₀) = K := by
    rw [kinE, norm_smul, Real.norm_eq_abs, abs_of_pos hs0, hb, mul_one, hs2]; field_simp
  have hvp : vParOf B x₀ (s • bhat B x₀) = s := by
    rw [vParOf, inner_smul_left, real_inner_self_eq_norm_sq, hb]; simp
  have hmu : muOf m B x₀ (s • bhat B x₀) = 0 := by
    rw [muOf, hvp, sub_self, norm_zero]; ring
  have hmem : s • bhat B x₀ ∈ U := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hk, hε]; nlinarith
    · rw [hk, hε]; nlinarith
    · rw [hvp]; exact hs0
    · rw [hmu, hk]; positivity
  have hsub : U ⊆ alphaEwVel m K B₀ B x₀ := fun w hw =>
    ⟨hw.1.le, hw.2.1.le, hw.2.2.1, hw.2.2.2.le⟩
  exact lt_of_lt_of_le (hUo.measure_pos volume ⟨_, hmem⟩) (measure_mono hsub)

end PlasmaLean.Design.RationalStellaratorGC
