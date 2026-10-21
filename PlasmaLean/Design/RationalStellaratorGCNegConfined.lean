/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCConfined
public import PlasmaLean.Design.RationalStellaratorGCNegForever

/-!
# All-time confinement of passing guiding centres with `v∥ < 0`, and both signs of `v∥`

**Model assumption.** As in `Design/RationalStellaratorGCConfined`: guiding centres move according
to the Littlejohn guiding-centre equations (`Theory/Kinetic/GuidingCentreLittlejohn`,
`LittlejohnOrbit`), a supplied model, not derived here from the Newton–Lorentz equations. Only
passing particles with magnetic moment `μ = 0` are treated.

**Main results.**

* `rationalStellarator_gc_confined_forever_neg` (model units `R₀ = B₀ = 1`): there is a torus
  profile `ρ` (`0.025 ≤ ρ ≤ 0.282`, the exact KAM torus of rotational transform
  `ι_B = (161 − √5)/1178` of the guiding-centre field `gcField (−1/256)`) such that every `μ = 0`
  Littlejohn orbit in `B = field (1/4)` with `ρ_s = m v_∥/q = −1/256` (for `m, q > 0`: `v_∥ < 0`)
  whose guiding centre starts on the magnetic axis or inside the torus stays inside the torus for
  all time, with `B*_∥ = |B| ≥ 1/10` along it; such orbits exist from every starting point inside.
* `alpha_gc_confined_forever_neg` (SI): the same for 3.5 MeV alphas moving **against** the field,
  `v_∥ = −√(2K/m)`, in `fieldSI B₀ R₀` with the same relation `B₀R₀ = 256 m √(2K/m)/q`.
* **`alpha_gc_confined_forever_pm`**: both signs at once. There are **two** torus profiles: `ρ₊`
  (`0.03 ≤ ρ₊ ≤ 0.253`, the `ι = (75 + √5)/562` torus of `gcField (1/256)`, from
  `alpha_gc_confined_forever`) for `v_∥ = +√(2K/m)` and `ρ₋` (`0.025 ≤ ρ₋ ≤ 0.282`, the `ι_B` torus
  of `gcField (−1/256)`) for `v_∥ = −√(2K/m)`. A guiding centre of either sign starting inside the
  torus of **its own sign** (in the scaled coordinates `X/R₀`) stays inside that torus forever (and
  such orbits exist). The two tori are different surfaces; a guiding centre with `v_∥ > 0` starting
  inside `ρ₋` but outside `ρ₊` is not covered.

**Proof.** As for `v_∥ > 0`: `B*_∥ = |B|` exactly, so a `μ = 0` orbit with `m v_∥/q = −1/256` is a
field line of the `C¹` field `(v_∥/|B|) · gcField (−1/256)` (`Vgc`); rescaling by the nonvanishing
factor keeps the exact flow torus (`FlowTorus.smul`), which traps the field lines
(`FlowTorus.confined_existsUnique`). The negative factor `v_∥/|B| < 0` only reverses time.
-/

open scoped RealInnerProductSpace

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGCNeg

open PlasmaLean.Design.RationalStellaratorGC

open Real Set PlasmaLean.Fields PlasmaLean.Design.RationalStellarator PlasmaLean.Design.KamTorusA
  PlasmaLean.Kinetic.GCLittlejohn PlasmaLean.Theory.KAM WithLp

/-! ## The time-changed guiding-centre field (`ρ_s = −1/256`) -/

/-- The guiding-centre velocity field `(c/|B|) · gcField (−1/256)` (`c = v_∥` in model units). -/
def Vgc (c : ℝ) (x : Space) : Space := (c / ‖field (1 / 4) x‖) • gcField (-1 / 256) x

/-- `Vgc c` is `C¹` on the region `{r₂ > 0, B ≠ 0}`. -/
theorem Vgc_contDiffOn (c : ℝ) : ContDiffOn ℝ 1 (Vgc c) gcRegion := by
  have hB : ContDiffOn ℝ 1 (field (1 / 4)) gcRegion :=
    (field_contDiffOn_n (1 / 4) 1).mono fun x hx => hx.1
  have hn : ContDiffOn ℝ 1 (fun x => ‖field (1 / 4) x‖) gcRegion :=
    hB.norm ℝ fun x hx => hx.2
  have hl : ContDiffOn ℝ 1 (fun x => c / ‖field (1 / 4) x‖) gcRegion :=
    contDiffOn_const.div hn fun x hx => norm_ne_zero_iff.2 hx.2
  exact hl.smul (gcField_contDiffOn_one (-1 / 256))

/-- **The master confinement theorem for `ρ_s = −1/256`**: one torus profile `ρ` (the exact
`ι_B` guiding-centre torus) traps the field lines of `gcField (−1/256)` and of every time change
`(c/|B|) gcField (−1/256)`, `c ≠ 0`. -/
theorem gc_master :
    ∃ ρ : ℝ → ℝ → ℝ, TorusProfile ρ ∧ (∀ a b, 1 / 40 ≤ ρ a b) ∧ (∀ a b, ρ a b ≤ 141 / 500) ∧
      (∀ x₀ : Space, (rt x₀ = 0 ∨ rt x₀ < ρ (θs x₀) (φs x₀)) →
        ∃! γ : ℝ → Space, IsFieldLine (gcField (-1 / 256)) γ ∧ γ 0 = x₀) ∧
      (∀ γ : ℝ → Space, IsFieldLine (gcField (-1 / 256)) γ →
        (rt (γ 0) = 0 ∨ rt (γ 0) < ρ (θs (γ 0)) (φs (γ 0))) →
        ∀ t, rt (γ t) ≤ 141 / 500 ∧ (rt (γ t) = 0 ∨ rt (γ t) < ρ (θs (γ t)) (φs (γ t)))) ∧
      (∀ c : ℝ, c ≠ 0 → ∀ x₀ : Space, (rt x₀ = 0 ∨ rt x₀ < ρ (θs x₀) (φs x₀)) →
        ∃! Y : ℝ → Space, IsFieldLine (Vgc c) Y ∧ Y 0 = x₀) ∧
      ∀ c : ℝ, c ≠ 0 → ∀ Y : ℝ → Space, IsFieldLine (Vgc c) Y →
        (rt (Y 0) = 0 ∨ rt (Y 0) < ρ (θs (Y 0)) (φs (Y 0))) →
        ∀ t, rt (Y t) ≤ 141 / 500 ∧ (rt (Y t) = 0 ∨ rt (Y t) < ρ (θs (Y t)) (φs (Y t))) := by
  obtain ⟨Rk, zk, hK⟩ := gc_flowTorus
  have hKU : ∀ y : Space, rt y ≤ 73 / 250 → y ∈ gcRegion :=
    fun y hy => tube_subset_gcRegion (by linarith)
  obtain ⟨h1, h2⟩ := hK.confined_existsUnique isOpen_gcRegion (gcField_contDiffOn_one (-1 / 256))
    (R₁ := 73 / 250) (g₀ := 1 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hKU
  have hK' : ∀ c : ℝ, c ≠ 0 → FlowTorus (Vgc c) iotaB (1 / 40) (141 / 500) Rk zk := by
    intro c hc
    refine hK.smul (fun x => c / ‖field (1 / 4) x‖) ?_
    intro θ φ
    have hRp : 0 < Rk θ φ := by linarith [hK.R_gt θ φ]
    have hrt : rt (cylPt (Rk θ φ) φ (zk θ φ)) = rtK Rk zk θ φ := by
      rw [rt, Rc_cylPt hRp.le, cylPt_two]; rfl
    have hB := norm_field_ge (y := cylPt (Rk θ φ) φ (zk θ φ))
      (by rw [hrt]; linarith [hK.rt_le θ φ])
    exact div_ne_zero hc (by linarith)
  exact ⟨hK.profile, hK.torusProfile, fun a b => (hK.profile_bounds a b).1,
    fun a b => (hK.profile_bounds a b).2, h1, h2,
    fun c hc => ((hK' c hc).confined_existsUnique isOpen_gcRegion (Vgc_contDiffOn c)
      (R₁ := 73 / 250) (g₀ := 1 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hKU).1,
    fun c hc => ((hK' c hc).confined_existsUnique isOpen_gcRegion (Vgc_contDiffOn c)
      (R₁ := 73 / 250) (g₀ := 1 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hKU).2⟩

/-! ## Passing guiding centres with `v∥ < 0` in model units -/

/-- A `μ = 0` Littlejohn orbit in `field (1/4)` with `m v_∥/q = −1/256` is a field line of
`Vgc v_∥(0)`. -/
theorem littlejohn_isFieldLine_Vgc {m q : ℝ} {X : ℝ → Space} {v : ℝ → ℝ}
    (h : LittlejohnOrbit m q 0 (field (1 / 4)) X v) (hρ : m * v 0 / q = -1 / 256) :
    IsFieldLine (Vgc (v 0)) X := fun t => by
  have := velocity_eq_modField h t
  rw [BstarPar_field, hρ] at this
  exact this

/-- **All-time confinement of passing guiding centres with `v∥ < 0`** (Littlejohn model, `μ = 0`,
model units `R₀ = B₀ = 1`). There is a torus profile `ρ` with `0.025 ≤ ρ ≤ 0.282` (the exact KAM
torus of rotational transform `ι_B = (161 − √5)/1178` of the guiding-centre field
`gcField (−1/256)` about the magnetic axis of `field (1/4)`) such that every `μ = 0` Littlejohn
guiding-centre orbit `(X, v_∥)` in `B = field (1/4)` with `ρ_s = m v_∥/q = −1/256` (for `m, q > 0`
this means `v_∥ < 0`) whose guiding centre starts on the axis or inside the torus stays inside the
torus — within distance `0.282` of the axis — for all time, forward and backward, with
`B*_∥ = |B| ≥ 1/10` along the orbit. Non-vacuity: from every point on the axis or inside the torus
and every `v₀` with `m v₀/q = −1/256` there is such an orbit (with `v_∥ ≡ v₀`). -/
theorem rationalStellarator_gc_confined_forever_neg :
    ∃ ρ : ℝ → ℝ → ℝ, TorusProfile ρ ∧ (∀ a b, 1 / 40 ≤ ρ a b) ∧ (∀ a b, ρ a b ≤ 141 / 500) ∧
      (∀ (m q : ℝ) (X : ℝ → Space) (v : ℝ → ℝ), LittlejohnOrbit m q 0 (field (1 / 4)) X v →
        m * v 0 / q = -1 / 256 → (rt (X 0) = 0 ∨ rt (X 0) < ρ (θs (X 0)) (φs (X 0))) →
        ∀ t, rt (X t) ≤ 141 / 500 ∧ (rt (X t) = 0 ∨ rt (X t) < ρ (θs (X t)) (φs (X t))) ∧
          1 / 10 ≤ BstarPar m q (field (1 / 4)) (v t) (X t)) ∧
      ∀ (m q v₀ : ℝ) (x₀ : Space), m * v₀ / q = -1 / 256 →
        (rt x₀ = 0 ∨ rt x₀ < ρ (θs x₀) (φs x₀)) →
        ∃ X : ℝ → Space, LittlejohnOrbit m q 0 (field (1 / 4)) X (fun _ => v₀) ∧ X 0 = x₀ := by
  obtain ⟨ρ, hρ, hlo, hhi, -, -, hE, hV⟩ := gc_master
  refine ⟨ρ, hρ, hlo, hhi, fun m q X v h hs h0 t => ?_, fun m q v₀ x₀ hs h0 => ?_⟩
  · have hv0 : v 0 ≠ 0 := by
      intro hz; rw [hz, mul_zero, zero_div] at hs; norm_num at hs
    obtain ⟨hr, hin⟩ := hV (v 0) hv0 X (littlejohn_isFieldLine_Vgc h hs) h0 t
    exact ⟨hr, hin, by rw [BstarPar_field]; exact norm_field_ge (by linarith)⟩
  · have hv0 : v₀ ≠ 0 := by
      intro hz; rw [hz, mul_zero, zero_div] at hs; norm_num at hs
    obtain ⟨Y, ⟨hY, hY0⟩, -⟩ := hE v₀ hv0 x₀ h0
    refine ⟨Y, ⟨fun t => ?_, fun t => ?_⟩, hY0⟩
    · have := hY t
      rw [BstarPar_field, Bstar_eq_modField, hs, zero_div, zero_smul, add_zero, smul_smul,
        ← div_eq_inv_mul]
      exact this
    · simpa using hasDerivAt_const t v₀

/-! ## SI units -/

/-- In SI units, a `μ = 0` Littlejohn orbit with `m v_∥/(q B₀ R₀) = −1/256` is, after rescaling
`Y = X/R₀`, a field line of `Vgc (v_∥/R₀)`. -/
theorem littlejohnSI_isFieldLine {m q B₀ R₀ : ℝ} (hB₀ : 0 < B₀) (hR₀ : 0 < R₀) {X : ℝ → Space}
    {v : ℝ → ℝ} (h : LittlejohnOrbit m q 0 (fieldSI B₀ R₀) X v)
    (hρ : m * v 0 / q / (B₀ * R₀) = -1 / 256) :
    IsFieldLine (Vgc (v 0 / R₀)) (fun t => R₀⁻¹ • X t) := fun t => by
  have h1 := (velocity_eq_modField h t).const_smul R₀⁻¹
  rw [BstarPar_fieldSI hB₀ hR₀, fieldSI_modField hB₀ hR₀, hρ, smul_smul, smul_smul] at h1
  convert h1 using 1
  simp only [Vgc, gcField]
  congr 1
  have hn : ‖field (1 / 4) (R₀⁻¹ • X t)‖ ≠ 0 ∨ ‖field (1 / 4) (R₀⁻¹ • X t)‖ = 0 := by tauto
  rcases hn with hn | hn
  · field_simp
  · rw [hn]; simp

/-- **All-time confinement of passing 3.5 MeV alpha guiding centres moving against the field**
(SI units; Littlejohn guiding-centre model — a supplied model — with magnetic moment `μ = 0`).
Let `m ∈ [6.6446, 6.6447] × 10⁻²⁷ kg`, `e ∈ [1.6021, 1.6022] × 10⁻¹⁹ C`, `q = 2e`,
`K = 3.5 MeV = 3.5 × 10⁶ e` J, all of it parallel with **negative** sign:
`v_∥ = −√(2K/m) < 0`. In `fieldSI B₀ R₀` with `B₀ R₀ = 256 m √(2K/m)/q ∈ [68.9, 69.0] T·m` (the
same relation as for `v_∥ > 0`, `alpha_B0R0_bounds`), so that `ρ_s = m v_∥/(q B₀ R₀) = −1/256`,
there is a torus profile `ρ` (`0.025 ≤ ρ ≤ 0.282`, in units of `R₀`; the exact `ι_B` KAM torus of
`gcField (−1/256)`) such that such orbits exist from every point `x₀` with `x₀/R₀` on the axis or
inside the torus, and every such orbit starting there stays inside the torus (within `0.282 R₀` of
the magnetic axis) for all time. -/
theorem alpha_gc_confined_forever_neg :
    ∃ ρ : ℝ → ℝ → ℝ, TorusProfile ρ ∧ (∀ a b, 1 / 40 ≤ ρ a b) ∧ (∀ a b, ρ a b ≤ 141 / 500) ∧
      (∀ (m e B₀ R₀ : ℝ), 6.6446e-27 ≤ m → m ≤ 6.6447e-27 → 1.6021e-19 ≤ e → e ≤ 1.6022e-19 →
        0 < B₀ → 0 < R₀ → B₀ * R₀ = 256 * m * √(2 * (3.5e6 * e) / m) / (2 * e) →
        ∀ x₀ : Space,
          (rt (R₀⁻¹ • x₀) = 0 ∨ rt (R₀⁻¹ • x₀) < ρ (θs (R₀⁻¹ • x₀)) (φs (R₀⁻¹ • x₀))) →
          ∃ X : ℝ → Space, LittlejohnOrbit m (2 * e) 0 (fieldSI B₀ R₀) X
            (fun _ => -√(2 * (3.5e6 * e) / m)) ∧ X 0 = x₀) ∧
      ∀ (m e B₀ R₀ : ℝ), 6.6446e-27 ≤ m → m ≤ 6.6447e-27 → 1.6021e-19 ≤ e → e ≤ 1.6022e-19 →
        0 < B₀ → 0 < R₀ → B₀ * R₀ = 256 * m * √(2 * (3.5e6 * e) / m) / (2 * e) →
        ∀ (X : ℝ → Space) (v : ℝ → ℝ), LittlejohnOrbit m (2 * e) 0 (fieldSI B₀ R₀) X v →
          v 0 = -√(2 * (3.5e6 * e) / m) →
          (rt (R₀⁻¹ • X 0) = 0 ∨ rt (R₀⁻¹ • X 0) < ρ (θs (R₀⁻¹ • X 0)) (φs (R₀⁻¹ • X 0))) →
          ∀ t, rt (R₀⁻¹ • X t) ≤ 141 / 500 ∧
            (rt (R₀⁻¹ • X t) = 0 ∨ rt (R₀⁻¹ • X t) < ρ (θs (R₀⁻¹ • X t)) (φs (R₀⁻¹ • X t))) := by
  obtain ⟨ρ, hρ, hlo, hhi, -, -, hE, hV⟩ := gc_master
  refine ⟨ρ, hρ, hlo, hhi, fun m e B₀ R₀ hm1 hm2 he1 he2 hB₀ hR₀ hBR x₀ h0 => ?_,
    fun m e B₀ R₀ hm1 hm2 he1 he2 hB₀ hR₀ hBR X v h hv0 h0 t => ?_⟩
  · -- existence of the orbits (non-vacuity)
    have hm : 0 < m := by linarith
    have he : 0 < e := by linarith
    set s := √(2 * (3.5e6 * e) / m) with hs_def
    have hspos : 0 < s := Real.sqrt_pos.2 (by positivity)
    have hs : m * -s / (2 * e) / (B₀ * R₀) = -1 / 256 := by
      rw [hBR]
      have : 0 < m * s := by positivity
      field_simp
    obtain ⟨Y, ⟨hY, hY0⟩, -⟩ := hE (-s / R₀) (div_ne_zero (neg_ne_zero.2 hspos.ne') hR₀.ne') _ h0
    have hXY : ∀ t, R₀⁻¹ • (R₀ • Y t) = Y t := fun t => by
      rw [smul_smul, inv_mul_cancel₀ hR₀.ne', one_smul]
    refine ⟨fun t => R₀ • Y t, ⟨fun t => ?_, fun t => ?_⟩, ?_⟩
    · have h1 := (hY t).const_smul R₀
      rw [BstarPar_fieldSI hB₀ hR₀, hXY, Bstar_eq_modField, fieldSI_modField hB₀ hR₀, hXY, hs,
        zero_div, zero_smul, add_zero]
      convert h1 using 1
      simp only [Vgc, gcField, smul_smul]
      congr 1
      rcases eq_or_ne ‖field (1 / 4) (Y t)‖ 0 with hn | hn
      · rw [hn]; simp
      · field_simp
    · simpa using hasDerivAt_const t (-s)
    · change R₀ • Y 0 = x₀
      rw [hY0, smul_smul, mul_inv_cancel₀ hR₀.ne', one_smul]
  · have hm : 0 < m := by linarith
    have he : 0 < e := by linarith
    have hvneg : v 0 < 0 := by
      rw [hv0]; exact neg_neg_of_pos (Real.sqrt_pos.2 (by positivity))
    have hs : m * v 0 / (2 * e) / (B₀ * R₀) = -1 / 256 := by
      rw [hBR, hv0]
      have : 0 < m * √(2 * (3.5e6 * e) / m) := mul_pos hm (Real.sqrt_pos.2 (by positivity))
      field_simp
    exact hV (v 0 / R₀) (div_ne_zero hvneg.ne hR₀.ne') _
      (littlejohnSI_isFieldLine hB₀ hR₀ h hs) h0 t

/-! ## Both signs of the parallel velocity -/

/-- **All-time confinement of passing 3.5 MeV alpha guiding centres of both signs of `v_∥`**
(SI units; Littlejohn guiding-centre model — a supplied model, not derived from the Lorentz force —
with magnetic moment `μ = 0`). Let `m ∈ [6.6446, 6.6447] × 10⁻²⁷ kg`,
`e ∈ [1.6021, 1.6022] × 10⁻¹⁹ C`, `q = 2e`, `K = 3.5 MeV = 3.5 × 10⁶ e` J all parallel, so
`v_∥ = ±√(2K/m)`, and `fieldSI B₀ R₀ x = B₀ · field (1/4) (x/R₀)` with
`B₀ R₀ = 256 m √(2K/m)/q ∈ [68.9, 69.0] T·m`, i.e. `ρ_s = m v_∥/(q B₀ R₀) = ±1/256`.

There are **two** torus profiles (radial graphs about the magnetic axis, in units of `R₀`):
`ρ₊` with `0.03 ≤ ρ₊ ≤ 0.253` (the exact KAM torus of rotational transform `(75 + √5)/562` of
`gcField (1/256)`) and `ρ₋` with `0.025 ≤ ρ₋ ≤ 0.282` (the exact KAM torus of rotational transform
`(161 − √5)/1178` of `gcField (−1/256)`), such that for each sign `σ = ±`:

* (non-vacuity) from every `x₀` with `x₀/R₀` on the axis or inside the torus `ρ_σ` there is such a
  guiding-centre orbit with `v_∥ ≡ σ√(2K/m)` and `X 0 = x₀`; and
* every such guiding-centre orbit with `v_∥(0) = σ√(2K/m)` starting on the axis or inside the
  torus `ρ_σ` (in the scaled coordinates `X/R₀`) stays inside `ρ_σ` for all time — within
  `0.253 R₀` (`σ = +`), resp. `0.282 R₀` (`σ = −`), of the magnetic axis.

Each sign uses its own torus; the statement says nothing about an orbit of one sign starting
inside the other sign's torus only. -/
theorem alpha_gc_confined_forever_pm :
    ∃ ρp ρn : ℝ → ℝ → ℝ, TorusProfile ρp ∧ TorusProfile ρn ∧
      (∀ a b, 3 / 100 ≤ ρp a b ∧ ρp a b ≤ 253 / 1000) ∧
      (∀ a b, 1 / 40 ≤ ρn a b ∧ ρn a b ≤ 141 / 500) ∧
      ∀ (m e B₀ R₀ : ℝ), 6.6446e-27 ≤ m → m ≤ 6.6447e-27 → 1.6021e-19 ≤ e → e ≤ 1.6022e-19 →
        0 < B₀ → 0 < R₀ → B₀ * R₀ = 256 * m * √(2 * (3.5e6 * e) / m) / (2 * e) →
        -- `v_∥ > 0`: the torus `ρp`
        (∀ x₀ : Space,
          (rt (R₀⁻¹ • x₀) = 0 ∨ rt (R₀⁻¹ • x₀) < ρp (θs (R₀⁻¹ • x₀)) (φs (R₀⁻¹ • x₀))) →
          ∃ X : ℝ → Space, LittlejohnOrbit m (2 * e) 0 (fieldSI B₀ R₀) X
            (fun _ => √(2 * (3.5e6 * e) / m)) ∧ X 0 = x₀) ∧
        (∀ (X : ℝ → Space) (v : ℝ → ℝ), LittlejohnOrbit m (2 * e) 0 (fieldSI B₀ R₀) X v →
          v 0 = √(2 * (3.5e6 * e) / m) →
          (rt (R₀⁻¹ • X 0) = 0 ∨ rt (R₀⁻¹ • X 0) < ρp (θs (R₀⁻¹ • X 0)) (φs (R₀⁻¹ • X 0))) →
          ∀ t, rt (R₀⁻¹ • X t) ≤ 253 / 1000 ∧
            (rt (R₀⁻¹ • X t) = 0 ∨ rt (R₀⁻¹ • X t) < ρp (θs (R₀⁻¹ • X t)) (φs (R₀⁻¹ • X t)))) ∧
        -- `v_∥ < 0`: the torus `ρn`
        (∀ x₀ : Space,
          (rt (R₀⁻¹ • x₀) = 0 ∨ rt (R₀⁻¹ • x₀) < ρn (θs (R₀⁻¹ • x₀)) (φs (R₀⁻¹ • x₀))) →
          ∃ X : ℝ → Space, LittlejohnOrbit m (2 * e) 0 (fieldSI B₀ R₀) X
            (fun _ => -√(2 * (3.5e6 * e) / m)) ∧ X 0 = x₀) ∧
        ∀ (X : ℝ → Space) (v : ℝ → ℝ), LittlejohnOrbit m (2 * e) 0 (fieldSI B₀ R₀) X v →
          v 0 = -√(2 * (3.5e6 * e) / m) →
          (rt (R₀⁻¹ • X 0) = 0 ∨ rt (R₀⁻¹ • X 0) < ρn (θs (R₀⁻¹ • X 0)) (φs (R₀⁻¹ • X 0))) →
          ∀ t, rt (R₀⁻¹ • X t) ≤ 141 / 500 ∧
            (rt (R₀⁻¹ • X t) = 0 ∨ rt (R₀⁻¹ • X t) < ρn (θs (R₀⁻¹ • X t)) (φs (R₀⁻¹ • X t))) := by
  obtain ⟨ρp, hρp, hlop, hhip, hEp, hVp⟩ := RationalStellaratorGC.alpha_gc_confined_forever
  obtain ⟨ρn, hρn, hlon, hhin, hEn, hVn⟩ := alpha_gc_confined_forever_neg
  exact ⟨ρp, ρn, hρp, hρn, fun a b => ⟨hlop a b, hhip a b⟩, fun a b => ⟨hlon a b, hhin a b⟩,
    fun m e B₀ R₀ hm1 hm2 he1 he2 hB₀ hR₀ hBR =>
      ⟨hEp m e B₀ R₀ hm1 hm2 he1 he2 hB₀ hR₀ hBR, hVp m e B₀ R₀ hm1 hm2 he1 he2 hB₀ hR₀ hBR,
        hEn m e B₀ R₀ hm1 hm2 he1 he2 hB₀ hR₀ hBR, hVn m e B₀ R₀ hm1 hm2 he1 he2 hB₀ hR₀ hBR⟩⟩

/-- **Sanity**: the two signs really are different guiding-centre fields: for a given orbit at
most one of the two hypotheses `v_∥(0) = ±√(2K/m)` holds (`K > 0`). -/
theorem alpha_sign_exclusive {m e : ℝ} (hm : 0 < m) (he : 0 < e) (v : ℝ) :
    ¬ (v = √(2 * (3.5e6 * e) / m) ∧ v = -√(2 * (3.5e6 * e) / m)) := by
  rintro ⟨h1, h2⟩
  have hs : 0 < √(2 * (3.5e6 * e) / m) := Real.sqrt_pos.2 (by positivity)
  linarith

end PlasmaLean.Design.RationalStellaratorGCNeg
