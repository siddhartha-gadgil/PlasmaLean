/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCForever

/-!
# All-time confinement of passing guiding centres in the rational stellarator

**Model assumption.** Guiding centres move according to the Littlejohn guiding-centre equations
(`Theory/Kinetic/GuidingCentreLittlejohn`, `LittlejohnOrbit`): a supplied model, not derived here
from the Newton–Lorentz equations. Only passing particles with magnetic moment `μ = 0` are treated.

**Main results.**

* `rationalStellarator_gc_confined_forever` (model units `R₀ = B₀ = 1`): there is a torus profile
  `ρ` (`0.03 ≤ ρ ≤ 0.253`, the exact KAM torus of the guiding-centre field) such that every `μ = 0`
  Littlejohn orbit in `B = field (1/4)` with `ρ_s = m v_∥/q = 1/256` (for `m, q > 0`: `v_∥ > 0`)
  whose guiding centre starts on the magnetic axis or inside the torus stays inside the torus for
  all time, and `B*_∥ = |B| ≥ 1/10` along it; such orbits exist from every starting point inside.
* `alpha_gc_confined_forever` (SI): for 3.5 MeV alpha particles (mass
  `m ∈ [6.6446, 6.6447] × 10⁻²⁷ kg`, charge `q = 2e`, `e ∈ [1.6021, 1.6022] × 10⁻¹⁹ C`, all kinetic
  energy parallel: `v_∥ = √(2K/m)`), in the field `fieldSI B₀ R₀ x = B₀ · field (1/4) (x/R₀)`
  scaled with `B₀R₀ = 256 m v_∥/q ∈ [68.9, 69.0] T·m` (so that `ρ_s = m v_∥/(q B₀ R₀) = 1/256`),
  passing (`μ = 0`, `v_∥ > 0`) guiding centres starting inside the scaled torus stay inside it for
  all time (and such orbits exist from every starting point inside).

**Proof.** For the curl-free field, `B*_∥ = |B|` exactly (`BstarPar_field`), so a `μ = 0` orbit
solves `Ẋ = (v_∥/|B|) gcField ρ_s (X)` *globally* (`velocity_eq_modField`): it is a field line of
the `C¹` field `(c/|B|) · gcField (1/256)` (`Vgc`). Rescaling a field by a nonvanishing function
keeps flow tori (`FlowTorus.smul`), so the exact guiding-centre torus traps these field lines
(`FlowTorus.confined_existsUnique`, `gc_master`). This a-priori route avoids the circularity in
applying `littlejohn_mu0_confined` (whose hypotheses `v₀/B*_∥(X t) ≥ c > 0` would need the
confinement first); afterwards `B*_∥ = |B| ≥ 1/10` holds along the orbit (`BstarPar_ge`). The SI
version reduces to model units by `fieldSI_modField`: `B̃_SI(x) = B₀ · gcField ρ_s (x/R₀)`.

**Scope.** Only `ρ_s = +1/256` (one value of `B₀R₀` per particle energy): every other `B₀R₀` needs
its own KAM certificate; `v_∥ < 0` needs the `ρ_s = −1/256` torus (not certified, see
`notes/theory/gc-kam-status.md`).
-/

open scoped RealInnerProductSpace

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open Real Set PlasmaLean.Fields PlasmaLean.Design.RationalStellarator PlasmaLean.Design.KamTorusA
  PlasmaLean.Kinetic.GCLittlejohn WithLp

/-! ## Rescaled fields keep flow tori -/

namespace FlowTorus

variable {V : Space → Space} {ι ρmin ρmax : ℝ} {Rk zk : ℝ → ℝ → ℝ}

/-- **Rescaling by a nonvanishing function keeps flow tori**: `λ V` has the same invariant tori. -/
theorem smul (hK : FlowTorus V ι ρmin ρmax Rk zk) (lam : Space → ℝ)
    (hlam : ∀ θ φ, lam (cylPt (Rk θ φ) φ (zk θ φ)) ≠ 0) :
    FlowTorus (fun x => lam x • V x) ι ρmin ρmax Rk zk := by
  have eR : ∀ R φ z, cR (fun x => lam x • V x) R φ z = lam (cylPt R φ z) * cR V R φ z :=
    fun R φ z => real_inner_smul_left _ _ _
  have eT : ∀ R φ z, cT (fun x => lam x • V x) R φ z = lam (cylPt R φ z) * cT V R φ z :=
    fun R φ z => by simp only [cT, real_inner_smul_left, mul_div_assoc]
  have eZ : ∀ R φ z, cZ (fun x => lam x • V x) R φ z = lam (cylPt R φ z) * cZ V R φ z :=
    fun R φ z => real_inner_smul_left _ _ _
  refine ⟨hK.smooth_R, hK.smooth_z, hK.per_θ_R, hK.per_θ_z, hK.per_φ_R, hK.per_φ_z,
    fun θ φ => ?_, fun θ φ => ?_, fun θ φ => ?_, hK.radial_pos, hK.wind_pos, hK.rt_ge, hK.rt_le,
    hK.ρmin_pos, hK.ρmax_lt⟩
  · rw [eT, eR, ← hK.inv_R θ φ]; ring
  · rw [eT, eZ, ← hK.inv_z θ φ]; ring
  · rw [eT]; exact mul_ne_zero (hlam θ φ) (hK.cT_ne θ φ)

end FlowTorus

/-! ## The time-changed guiding-centre field -/

/-- The guiding-centre velocity field `(c/|B|) · gcField (1/256)` (`c = v_∥` in model units). -/
def Vgc (c : ℝ) (x : Space) : Space := (c / ‖field (1 / 4) x‖) • gcField (1 / 256) x

/-- `Vgc c` is `C¹` on the region `{r₂ > 0, B ≠ 0}`. -/
theorem Vgc_contDiffOn (c : ℝ) : ContDiffOn ℝ 1 (Vgc c) gcRegion := by
  have hB : ContDiffOn ℝ 1 (field (1 / 4)) gcRegion :=
    (field_contDiffOn_n (1 / 4) 1).mono fun x hx => hx.1
  have hn : ContDiffOn ℝ 1 (fun x => ‖field (1 / 4) x‖) gcRegion :=
    hB.norm ℝ fun x hx => hx.2
  have hl : ContDiffOn ℝ 1 (fun x => c / ‖field (1 / 4) x‖) gcRegion :=
    contDiffOn_const.div hn fun x hx => norm_ne_zero_iff.2 hx.2
  exact hl.smul (gcField_contDiffOn_one (1 / 256))

/-- **The master confinement theorem**: one torus profile `ρ` (the exact guiding-centre torus)
traps the field lines of `gcField (1/256)` and of every time change `(c/|B|) gcField (1/256)`,
`c ≠ 0`. -/
theorem gc_master :
    ∃ ρ : ℝ → ℝ → ℝ, TorusProfile ρ ∧ (∀ a b, 3 / 100 ≤ ρ a b) ∧ (∀ a b, ρ a b ≤ 253 / 1000) ∧
      (∀ x₀ : Space, (rt x₀ = 0 ∨ rt x₀ < ρ (θs x₀) (φs x₀)) →
        ∃! γ : ℝ → Space, IsFieldLine (gcField (1 / 256)) γ ∧ γ 0 = x₀) ∧
      (∀ γ : ℝ → Space, IsFieldLine (gcField (1 / 256)) γ →
        (rt (γ 0) = 0 ∨ rt (γ 0) < ρ (θs (γ 0)) (φs (γ 0))) →
        ∀ t, rt (γ t) ≤ 253 / 1000 ∧ (rt (γ t) = 0 ∨ rt (γ t) < ρ (θs (γ t)) (φs (γ t)))) ∧
      (∀ c : ℝ, c ≠ 0 → ∀ x₀ : Space, (rt x₀ = 0 ∨ rt x₀ < ρ (θs x₀) (φs x₀)) →
        ∃! Y : ℝ → Space, IsFieldLine (Vgc c) Y ∧ Y 0 = x₀) ∧
      ∀ c : ℝ, c ≠ 0 → ∀ Y : ℝ → Space, IsFieldLine (Vgc c) Y →
        (rt (Y 0) = 0 ∨ rt (Y 0) < ρ (θs (Y 0)) (φs (Y 0))) →
        ∀ t, rt (Y t) ≤ 253 / 1000 ∧ (rt (Y t) = 0 ∨ rt (Y t) < ρ (θs (Y t)) (φs (Y t))) := by
  obtain ⟨Rk, zk, hK⟩ := gc_flowTorus
  have hKU : ∀ y : Space, rt y ≤ 263 / 1000 → y ∈ gcRegion :=
    fun y hy => tube_subset_gcRegion (by linarith)
  obtain ⟨h1, h2⟩ := hK.confined_existsUnique isOpen_gcRegion (gcField_contDiffOn_one (1 / 256))
    (R₁ := 263 / 1000) (g₀ := 1 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hKU
  have hK' : ∀ c : ℝ, c ≠ 0 → FlowTorus (Vgc c) iota (3 / 100) (253 / 1000) Rk zk := by
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
      (R₁ := 263 / 1000) (g₀ := 1 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hKU).1,
    fun c hc => ((hK' c hc).confined_existsUnique isOpen_gcRegion (Vgc_contDiffOn c)
      (R₁ := 263 / 1000) (g₀ := 1 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hKU).2⟩

/-! ## Passing guiding centres in model units -/

/-- A `μ = 0` Littlejohn orbit in `field (1/4)` with `m v_∥/q = 1/256` is a field line of
`Vgc v_∥(0)`. -/
theorem littlejohn_isFieldLine_Vgc {m q : ℝ} {X : ℝ → Space} {v : ℝ → ℝ}
    (h : LittlejohnOrbit m q 0 (field (1 / 4)) X v) (hρ : m * v 0 / q = 1 / 256) :
    IsFieldLine (Vgc (v 0)) X := fun t => by
  have := velocity_eq_modField h t
  rw [BstarPar_field, hρ] at this
  exact this

/-- **All-time confinement of passing guiding centres** (Littlejohn model, `μ = 0`, model units
`R₀ = B₀ = 1`). There is a torus profile `ρ` with `0.03 ≤ ρ ≤ 0.253` (the exact KAM torus of the
guiding-centre field `gcField (1/256)` about the magnetic axis of `field (1/4)`) such that every
`μ = 0` Littlejohn guiding-centre orbit `(X, v_∥)` in `B = field (1/4)` with
`ρ_s = m v_∥/q = 1/256` (for `m, q > 0` this means `v_∥ > 0`) whose guiding centre starts on the
axis or inside the torus stays inside the torus — within distance `0.253` of the axis — for all
time, forward and backward, with `B*_∥ = |B| ≥ 1/10` along the orbit. Non-vacuity: from every
point on the axis or inside the torus and every `v₀` with `m v₀/q = 1/256` there is such an orbit
(with `v_∥ ≡ v₀`). -/
theorem rationalStellarator_gc_confined_forever :
    ∃ ρ : ℝ → ℝ → ℝ, TorusProfile ρ ∧ (∀ a b, 3 / 100 ≤ ρ a b) ∧ (∀ a b, ρ a b ≤ 253 / 1000) ∧
      (∀ (m q : ℝ) (X : ℝ → Space) (v : ℝ → ℝ), LittlejohnOrbit m q 0 (field (1 / 4)) X v →
        m * v 0 / q = 1 / 256 → (rt (X 0) = 0 ∨ rt (X 0) < ρ (θs (X 0)) (φs (X 0))) →
        ∀ t, rt (X t) ≤ 253 / 1000 ∧ (rt (X t) = 0 ∨ rt (X t) < ρ (θs (X t)) (φs (X t))) ∧
          1 / 10 ≤ BstarPar m q (field (1 / 4)) (v t) (X t)) ∧
      ∀ (m q v₀ : ℝ) (x₀ : Space), m * v₀ / q = 1 / 256 →
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

/-- **Sanity / the `B*_∥` lower bound**: in the tube `rt ≤ 0.3` (which contains the torus of
`rationalStellarator_gc_confined_forever`), `B*_∥ ≥ 1/10` for every `m, q, v_∥`. -/
theorem BstarPar_ge {y : Space} (hy : rt y ≤ 3 / 10) (m q v : ℝ) :
    1 / 10 ≤ BstarPar m q (field (1 / 4)) v y := by
  rw [BstarPar_field]; exact norm_field_ge hy

/-! ## SI units -/

/-- The rational stellarator field in SI units: `B_SI(x) = B₀ · field (1/4) (x/R₀)` (field
strength `B₀` on the magnetic axis, major radius `R₀`). -/
def fieldSI (B₀ R₀ : ℝ) (x : Space) : Space := B₀ • field (1 / 4) (R₀⁻¹ • x)

/-- `b_SI(x) = b(x/R₀)` for `B₀ > 0`. -/
theorem bhat_fieldSI {B₀ : ℝ} (hB₀ : 0 < B₀) (R₀ : ℝ) :
    bhat (fieldSI B₀ R₀) = fun x => bhat (field (1 / 4)) (R₀⁻¹ • x) := by
  funext x
  simp only [bhat, fieldSI, norm_smul, Real.norm_eq_abs, abs_of_pos hB₀, smul_smul]
  by_cases h : field (1 / 4) (R₀⁻¹ • x) = 0
  · rw [h]; simp
  · congr 1
    have := norm_ne_zero_iff.2 h
    field_simp

/-- `∇×b_SI(x) = R₀⁻¹ (∇×b)(x/R₀)`. -/
theorem curlb_fieldSI {B₀ : ℝ} (hB₀ : 0 < B₀) (R₀ : ℝ) (x : Space) :
    curlb (fieldSI B₀ R₀) x = R₀⁻¹ • curlb (field (1 / 4)) (R₀⁻¹ • x) := by
  rw [curlb, bhat_fieldSI hB₀,
    show (fun x => bhat (field (1 / 4)) (R₀⁻¹ • x)) = (bhat (field (1 / 4)) <| R₀⁻¹ • ·) from rfl,
    fderiv_comp_smul, curl_smul, curlb]

/-- **Scaling of the modified field**: `B̃_SI(x) = B₀ · B̃_{ρ/(B₀R₀)}(x/R₀)`. -/
theorem fieldSI_modField {B₀ R₀ : ℝ} (hB₀ : 0 < B₀) (hR₀ : 0 < R₀) (ρ : ℝ) (x : Space) :
    modField ρ (fieldSI B₀ R₀) x = B₀ • modField (ρ / (B₀ * R₀)) (field (1 / 4)) (R₀⁻¹ • x) := by
  rw [modField, modField, curlb_fieldSI hB₀, fieldSI, smul_add, smul_smul, smul_smul]
  congr 2
  field_simp

/-- `B*_∥` in SI units: `B*_∥ = |B_SI| = B₀ |B(x/R₀)|`. -/
theorem BstarPar_fieldSI {B₀ R₀ : ℝ} (hB₀ : 0 < B₀) (hR₀ : 0 < R₀) (m q v : ℝ) (x : Space) :
    BstarPar m q (fieldSI B₀ R₀) v x = B₀ * ‖field (1 / 4) (R₀⁻¹ • x)‖ := by
  rw [BstarPar, Bstar_eq_modField, fieldSI_modField hB₀ hR₀, bhat_fieldSI hB₀]
  beta_reduce
  rw [inner_smul_right, modField, inner_add_right, inner_smul_right, inner_bhat_curlb, mul_zero,
    add_zero, bhat, inner_smul_left, real_inner_self_eq_norm_sq]
  by_cases hB : field (1 / 4) (R₀⁻¹ • x) = 0
  · rw [hB]; simp
  have hn : ‖field (1 / 4) (R₀⁻¹ • x)‖ ≠ 0 := norm_ne_zero_iff.2 hB
  simp only [RCLike.conj_to_real]
  field_simp

/-- In SI units, a `μ = 0` Littlejohn orbit with `m v_∥/(q B₀ R₀) = 1/256` is, after rescaling
`Y = X/R₀`, a field line of `Vgc (v_∥/R₀)`. -/
theorem littlejohnSI_isFieldLine {m q B₀ R₀ : ℝ} (hB₀ : 0 < B₀) (hR₀ : 0 < R₀) {X : ℝ → Space}
    {v : ℝ → ℝ} (h : LittlejohnOrbit m q 0 (fieldSI B₀ R₀) X v)
    (hρ : m * v 0 / q / (B₀ * R₀) = 1 / 256) :
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

/-- The 3.5 MeV alpha: `B₀R₀ = 256 m v/q` lies in `[68.9, 69.0] T·m` for the CODATA-rounded
mass and charge intervals, with `v = √(2K/m)`, `K = 3.5 MeV`, `q = 2e`. -/
theorem alpha_B0R0_bounds {m e : ℝ} (hm1 : 6.6446e-27 ≤ m) (hm2 : m ≤ 6.6447e-27)
    (he1 : 1.6021e-19 ≤ e) (he2 : e ≤ 1.6022e-19) :
    68.9 ≤ 256 * m * √(2 * (3.5e6 * e) / m) / (2 * e) ∧
      256 * m * √(2 * (3.5e6 * e) / m) / (2 * e) ≤ 69 := by
  have hm : 0 < m := by linarith
  have he : 0 < e := by linarith
  have hx : 0 < 2 * (3.5e6 * e) / m := by positivity
  set s := √(2 * (3.5e6 * e) / m) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 2 * (3.5e6 * e) / m := Real.sq_sqrt hx.le
  have hs2' : s ^ 2 * m = 7e6 * e := by rw [hs2]; field_simp; ring
  rw [le_div_iff₀ (by positivity), div_le_iff₀ (by positivity)]
  constructor <;> nlinarith [sq_nonneg (s * m - 0.2694 * 2 * e), mul_pos hm he,
    mul_pos (mul_pos hm he) he, mul_pos (mul_pos hm hm) he]

/-- **All-time confinement of passing 3.5 MeV alpha guiding centres in SI units** (Littlejohn
guiding-centre model — a supplied model, not derived from the Lorentz force — with magnetic moment
`μ = 0`). Let `m ∈ [6.6446, 6.6447] × 10⁻²⁷ kg` (alpha mass), `e ∈ [1.6021, 1.6022] × 10⁻¹⁹ C`,
`q = 2e`, kinetic energy `K = 3.5 MeV = 3.5 × 10⁶ e` J, all of it parallel:
`v_∥ = √(2K/m) > 0` (≈ 1.299 × 10⁷ m/s). Consider the rational stellarator field in SI units
`fieldSI B₀ R₀ x = B₀ · field (1/4) (x/R₀)` (the normalized field `field (1/4)` with `B₀ = R₀ = 1`
scaled to axis field `B₀` and major radius `R₀`), with `B₀ R₀ = 256 m v_∥/q` — which lies in
`[68.9, 69.0] T·m` (`alpha_B0R0_bounds`) — so that `ρ_s = m v_∥/(q B₀ R₀) = 1/256` exactly.

Then there is a torus profile `ρ` (`0.03 ≤ ρ ≤ 0.253`, in units of `R₀`; the exact KAM torus of the
guiding-centre field) such that

* (non-vacuity) from every point `x₀` with `x₀/R₀` on the axis or inside the torus there is such a
  guiding-centre orbit `(X, v_∥ ≡ √(2K/m))` with `X 0 = x₀`; and
* every such guiding-centre orbit `(X, v_∥)` starting on the magnetic axis or inside the torus (in
  the scaled coordinates `X/R₀`) stays inside it, in particular within distance `0.253 R₀` of the
  magnetic axis, for all time. -/
theorem alpha_gc_confined_forever :
    ∃ ρ : ℝ → ℝ → ℝ, TorusProfile ρ ∧ (∀ a b, 3 / 100 ≤ ρ a b) ∧ (∀ a b, ρ a b ≤ 253 / 1000) ∧
      (∀ (m e B₀ R₀ : ℝ), 6.6446e-27 ≤ m → m ≤ 6.6447e-27 → 1.6021e-19 ≤ e → e ≤ 1.6022e-19 →
        0 < B₀ → 0 < R₀ → B₀ * R₀ = 256 * m * √(2 * (3.5e6 * e) / m) / (2 * e) →
        ∀ x₀ : Space,
          (rt (R₀⁻¹ • x₀) = 0 ∨ rt (R₀⁻¹ • x₀) < ρ (θs (R₀⁻¹ • x₀)) (φs (R₀⁻¹ • x₀))) →
          ∃ X : ℝ → Space, LittlejohnOrbit m (2 * e) 0 (fieldSI B₀ R₀) X
            (fun _ => √(2 * (3.5e6 * e) / m)) ∧ X 0 = x₀) ∧
      ∀ (m e B₀ R₀ : ℝ), 6.6446e-27 ≤ m → m ≤ 6.6447e-27 → 1.6021e-19 ≤ e → e ≤ 1.6022e-19 →
        0 < B₀ → 0 < R₀ → B₀ * R₀ = 256 * m * √(2 * (3.5e6 * e) / m) / (2 * e) →
        ∀ (X : ℝ → Space) (v : ℝ → ℝ), LittlejohnOrbit m (2 * e) 0 (fieldSI B₀ R₀) X v →
          v 0 = √(2 * (3.5e6 * e) / m) →
          (rt (R₀⁻¹ • X 0) = 0 ∨ rt (R₀⁻¹ • X 0) < ρ (θs (R₀⁻¹ • X 0)) (φs (R₀⁻¹ • X 0))) →
          ∀ t, rt (R₀⁻¹ • X t) ≤ 253 / 1000 ∧
            (rt (R₀⁻¹ • X t) = 0 ∨ rt (R₀⁻¹ • X t) < ρ (θs (R₀⁻¹ • X t)) (φs (R₀⁻¹ • X t))) := by
  obtain ⟨ρ, hρ, hlo, hhi, -, -, hE, hV⟩ := gc_master
  refine ⟨ρ, hρ, hlo, hhi, fun m e B₀ R₀ hm1 hm2 he1 he2 hB₀ hR₀ hBR x₀ h0 => ?_,
    fun m e B₀ R₀ hm1 hm2 he1 he2 hB₀ hR₀ hBR X v h hv0 h0 t => ?_⟩
  · -- existence of the orbits (non-vacuity)
    have hm : 0 < m := by linarith
    have he : 0 < e := by linarith
    set v₀ := √(2 * (3.5e6 * e) / m) with hv₀
    have hvpos : 0 < v₀ := Real.sqrt_pos.2 (by positivity)
    have hs : m * v₀ / (2 * e) / (B₀ * R₀) = 1 / 256 := by
      rw [hBR]
      have : 0 < m * v₀ := by positivity
      field_simp
    obtain ⟨Y, ⟨hY, hY0⟩, -⟩ := hE (v₀ / R₀) (div_ne_zero hvpos.ne' hR₀.ne') _ h0
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
    · simpa using hasDerivAt_const t v₀
    · change R₀ • Y 0 = x₀
      rw [hY0, smul_smul, mul_inv_cancel₀ hR₀.ne', one_smul]
  · have hm : 0 < m := by linarith
    have he : 0 < e := by linarith
    have hvpos : 0 < v 0 := by rw [hv0]; exact Real.sqrt_pos.2 (by positivity)
    have hs : m * v 0 / (2 * e) / (B₀ * R₀) = 1 / 256 := by
      rw [hBR, ← hv0]
      have : 0 < m * v 0 := by positivity
      field_simp
    exact hV (v 0 / R₀) (div_ne_zero hvpos.ne' hR₀.ne') _
      (littlejohnSI_isFieldLine hB₀ hR₀ h hs) h0 t

end PlasmaLean.Design.RationalStellaratorGC
