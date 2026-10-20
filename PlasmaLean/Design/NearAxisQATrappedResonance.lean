/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedBounce
public import PlasmaLean.Design.NearAxisQATrappedCellsRows1
public import PlasmaLean.Design.NearAxisQATrappedCellsRows2
public import PlasmaLean.Design.NearAxisQATrappedCellsRows3
public import PlasmaLean.Theory.Kinetic.BounceIntegrals
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Non-resonance of trapped 3.5 MeV alphas in exact QA: certified precession per bounce

Companion to `notes/theory/near-qa-trapped-particles.md` (target T4, steps 2–3). Model only:
the exactly quasi-axisymmetric member `exactQA` of the reactor near-axis family in the vacuum
Boozer guiding-centre model; orbits are supplied.

**Setting** (`Setup`): a 3.5 MeV alpha with tip field `E/μ ∈ [5.4, 5.5] T` starting at an upper
turning point with `ψ(0) ∈ [4.75, 5.79] T m²` (the exact-QA start window of
`NearAxisQATrappedBounce.exactQA_band`), `θ(0) ∈ (0, π/2)`, on `[0, T]` with
`T ≥ 2 · 8 × 10⁻⁴ s`.

Results:

* `exactQA_bounce_precession`: **the bounce closes and its toroidal precession is enclosed.**
  There are times `0 < P₁ < P ≤ 1.6 ms` with `ρ < 0` on `(0, P₁)`, `ρ > 0` on `(P₁, P)`,
  `ρ(P₁) = ρ(P) = 0`, the reduced state returns, `(ψ, θ, ρ)(P) = (ψ, θ, ρ)(0)`, and the toroidal
  advance per bounce satisfies
  `Δφ_b = φ(P) − φ(0) ∈ [0.7, 2.6]` (RK4, untrusted: `1.88–2.31` on the window).
* `exactQA_nonresonant`: hence `|sin Δφ_b| ≥ 1/2` (the bounce map is uniformly non-resonant on
  the exact-QA start window; the resonance `Δφ_b ≈ π` seen numerically near `r₀ ≈ 0.95 m` lies
  outside it).

**Method** (no singular integrals). By the precession identity (`precession_step`)
`ι₀ Δφ_b = ∫₀ᴾ Ω dt` with `Ω = −(μ/q + qρ²B/m) ∂_ψB`. The bounce is cut at `|θ| = δ = 3/5` into
four flank pieces and two bottom crossings (`inner_leg`, `outer_leg`). On a flank piece
`Ω dt = (∂_ψB/∂_θB) dψ` exactly and `x = |ψ − ψ₀|` is monotone (even where `θ̇ = 0`), so the cell
bounds of `NearAxisQATrappedCells` (`flank_bound`) integrate by `integral_le_cell_sum(_rev)`;
on a bottom crossing `θ` is monotone and `Ω = (Ω/|θ̇|) |θ̇|` (`bottom_bound`, via the identity
`bottom_alg`) integrates by `integral_le_mul_drop`. The closing of the bounce (`bounce_closes`)
uses first zeros of `ρ` (`first_zero_after`), momentum conservation and the single-well
structure of `B` (`Bred_strictAnti`). The parameter window is covered by an adaptive binary
subdivision into 24 boxes (`window_cover`, built by the `box_cover` tactic; leaf kernel checks
in `NearAxisQATrappedCellsRows1`–`3`).

Not proved here: the near-QA remainder (Grönwall comparison and phase shear) — see
`NearAxisQATrappedPeriodic` for the reference periodicity and the conditional composition.
-/
public section
noncomputable section
namespace PlasmaLean.Design.NearAxisQATrappedResonance
open PlasmaLean.Kinetic.Boozer PlasmaLean.Design.NearAxisQA
  PlasmaLean.Design.NearAxisQATrappedBounce
  PlasmaLean.Design.NearAxisQATrappedCells Real Set

/-! ## The exact-QA field in reduced form -/

/-- `r = √(2ψ/B₀) = √((20/57) ψ)`. -/
theorem radius_eq (x : ℝ) : radius (57 / 10) x = √(20 / 57 * x) := by
  unfold radius; congr 1; ring

/-- `B` of exact QA in reduced form. -/
theorem exactQA_B_eq (x θ φ : ℝ) : exactQA.B x θ φ = Bred x (cos θ) := by
  have h2 : cos (2 * θ) = 2 * cos θ ^ 2 - 1 := by rw [cos_two_mul]
  rw [exactQA, qaField_B, radius_eq, h2]; unfold Bred; ring

/-- `∂_ψB` of exact QA in reduced form. -/
theorem exactQA_Bψ_eq (x θ φ : ℝ) : exactQA.Bψ x θ φ =
    -(7 / 100 * cos θ * (√(20 / 57 * x))⁻¹ + 20 / 57 * (302 / 10000 - 33 / 1000 * cos θ ^ 2)) := by
  have h2 : cos (2 * θ) = 2 * cos θ ^ 2 - 1 := by rw [cos_two_mul]
  rw [exactQA, qaField_Bψ, radius_eq, h2]; ring

/-- `∂_θB` of exact QA in reduced form. -/
theorem exactQA_Bθ_eq (x θ φ : ℝ) : exactQA.Bθ x θ φ =
    sin θ * (399 / 1000 * √(20 / 57 * x) - 66 / 1000 * (20 / 57 * x) * cos θ) := by
  rw [exactQA, qaField_Bθ, radius_eq, sin_two_mul]; ring

/-- `numR = −∂_ψB` at the orbit point. -/
theorem numR_eq {inner : Bool} {ψ₀ x y : ℝ} (hψ : psiR inner ψ₀ x = y) (θ φ : ℝ) :
    numR inner ψ₀ x (cos θ) = -exactQA.Bψ y θ φ := by
  unfold numR wR; rw [hψ, exactQA_Bψ_eq]; ring

/-- `denR` with `s = sin θ` is `∂_θB`. -/
theorem denR_eq {inner : Bool} {ψ₀ x y : ℝ} (hψ : psiR inner ψ₀ x = y) (θ φ : ℝ) :
    denR inner ψ₀ x (cos θ) (sin θ) = exactQA.Bθ y θ φ := by
  unfold denR wR; rw [hψ, exactQA_Bθ_eq]

/-- `|sin θ| = √(1 − cos² θ)`. -/
theorem abs_sin_eq_sqrt (θ : ℝ) : |sin θ| = √(1 - cos θ ^ 2) := by
  rw [← sqrt_sq_eq_abs, sin_sq]

/-- `|∂_θB| = denR (cos θ) (√(1 − cos² θ))` on an orbit point. -/
theorem abs_Bθ_eq {inner : Bool} {x ψ₀ Bt y θ : ℝ} (hrel : OrbitRel inner x ψ₀ Bt (cos θ))
    (hψ : psiR inner ψ₀ x = y) (φ : ℝ) :
    |exactQA.Bθ y θ φ| = denR inner ψ₀ x (cos θ) (√(1 - cos θ ^ 2)) := by
  rw [← denR_eq hψ θ φ, ← abs_sin_eq_sqrt]
  unfold denR
  rw [abs_mul]
  congr 1
  have := denR_nonneg hrel (zero_le_one)
  unfold denR at this
  rw [abs_of_nonneg (by linarith)]

/-- **Single well.** At fixed flux, `Bred ψ` is strictly decreasing in `c = cos θ ∈ [0, 1]`
(for `0 < ψ ≤ 10`). -/
theorem Bred_strictAnti {ψ : ℝ} (h0 : 0 < ψ) (h1 : ψ ≤ 10) :
    StrictAntiOn (Bred ψ) (Icc 0 1) := by
  intro a ha b hb hab
  set r := √(20 / 57 * ψ)
  have hr0 : 0 < r := sqrt_pos.mpr (by positivity)
  have hr2 : r ^ 2 = 20 / 57 * ψ := sq_sqrt (by positivity)
  have hr : r ≤ 2 := by rw [sqrt_le_left (by norm_num)]; linarith
  have e : Bred ψ a - Bred ψ b = (b - a) * (399 / 1000 * r - 33 / 1000 * r ^ 2 * (a + b)) := by
    unfold Bred; rw [hr2]; ring
  have : 0 < 399 / 1000 * r - 33 / 1000 * r ^ 2 * (a + b) := by
    have hab2 : a + b ≤ 2 := by linarith [ha.2, hb.2]
    nlinarith
  have := mul_pos (sub_pos.mpr hab) this
  linarith

/-! ## Setting and pointwise facts -/

/-- The flux-momentum ratio `ι₀/G = 211/29050` (`x = |ψ − ψ₀| = (G/ι₀) |ρ|`). -/
@[expose] def kinv : ℝ := 211 / 29050

/-- The exact identity `λ E · 2m = q² (ι₀/G)²` behind the reduced energy relation. -/
theorem lam_identity : lam * Eα * (2 * mα) = qα ^ 2 * kinv ^ 2 := by
  norm_num [lam, Eα, mα, qα, kinv]

/-- **Bottom algebra.** With `A = μ/q + qρ²B/m`, energy `q²ρ²B²/(2m) + μB = E` and
`R = 2λ B_t x B³/((2B_t − B) n)` (`B_t = E/μ`, `n = −∂_ψB`): `A n R = q kinv² x B²/m`, i.e. the
drift rate times `R` is the parallel-streaming rate of `θ`. -/
theorem bottom_alg {μ ρ B nr x : ℝ} (hμ : 0 < μ) (hB : 0 < B) (hnr : 0 < nr)
    (hE : qα ^ 2 * ρ ^ 2 * B ^ 2 / (2 * mα) + μ * B = Eα) :
    (μ / qα + qα * ρ ^ 2 * B / mα) * nr *
      (2 * lam * (Eα / μ * x) * (B * B ^ 2) * ((2 * (Eα / μ) - B) * nr)⁻¹) =
      qα * kinv ^ 2 * x * B ^ 2 / mα := by
  have hq : (0 : ℝ) < qα := by norm_num [qα]
  have hm : (0 : ℝ) < mα := by norm_num [mα]
  have hkin : 0 ≤ qα ^ 2 * ρ ^ 2 * B ^ 2 / (2 * mα) := by positivity
  have hK : 0 < 2 * Eα - μ * B := by
    have : (0 : ℝ) < Eα := by norm_num [Eα]
    nlinarith
  have hAq : (μ / qα + qα * ρ ^ 2 * B / mα) * (qα * B) = 2 * Eα - μ * B := by
    have e : qα ^ 2 * ρ ^ 2 * B ^ 2 / mα = 2 * (Eα - μ * B) := by
      rw [← hE]; field_simp; ring
    have e2 : (μ / qα + qα * ρ ^ 2 * B / mα) * (qα * B) = μ * B + qα ^ 2 * ρ ^ 2 * B ^ 2 / mα := by
      field_simp
    rw [e2, e]; ring
  have h2 : 2 * (Eα / μ) - B = (2 * Eα - μ * B) / μ := by field_simp
  have key := lam_identity
  rw [h2]
  have e3 : (μ / qα + qα * ρ ^ 2 * B / mα) = (2 * Eα - μ * B) / (qα * B) := by
    rw [eq_div_iff (by positivity)]; exact hAq
  rw [e3]
  field_simp
  linear_combination x * key

/-- **Setting**: an exact-QA 3.5 MeV alpha in the pitch window, starting at an upper turning
point in the exact-QA start window. -/
structure Setup (μ T : ℝ) (ψ θ φ ρ : ℝ → ℝ) : Prop where
  /-- Pitch window `E/μ ∈ [5.4, 5.5] T`. -/
  hμ : μ ∈ Icc muLo muHi
  /-- The orbit. -/
  orbit : BoozerGCOrbitOn exactQA mα qα μ ψ θ φ ρ T
  /-- Energy `3.5 MeV`. -/
  energy : boozerEnergy exactQA mα qα μ ψ θ φ ρ 0 = Eα
  /-- Start at a turning point. -/
  rho0 : ρ 0 = 0
  /-- Start in the exact-QA window. -/
  psi0 : ψ 0 ∈ Icc (475 / 100) (579 / 100)
  /-- Upper flank. -/
  theta0 : θ 0 ∈ Ioo 0 (π / 2)

namespace Setup
variable {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ} (S : Setup μ T ψ θ φ ρ)
include S

theorem mu_pos : 0 < μ := muLo_pos.trans_le S.hμ.1

/-- The tip field `B_t = E/μ ∈ [5.4, 5.5]`. -/
theorem Bt_mem : Eα / μ ∈ Icc (27 / 5 : ℝ) (11 / 2) := by
  have hμ0 := S.mu_pos
  have h1 := S.hμ.1; have h2 := S.hμ.2
  unfold muLo at h1; unfold muHi at h2
  have hE : (0 : ℝ) < Eα := by norm_num [Eα]
  constructor
  · rw [le_div_iff₀ hμ0]; rw [le_div_iff₀ (by norm_num)] at h2; linarith
  · rw [div_le_iff₀ hμ0]; rw [div_le_iff₀ (by norm_num)] at h1; linarith

/-- Band and gyroradius bound. -/
theorem band {t : ℝ} (ht : t ∈ Icc 0 T) : ψ t ∈ Icc psiLo psiEdge ∧ |ρ t| ≤ rhoMax :=
  exactQA_band S.hμ S.orbit S.energy S.rho0 S.psi0 t ht

/-- Momentum: `ρ = (ι₀/G)(ψ − ψ₀)`. -/
theorem mom {t : ℝ} (ht : t ∈ Icc 0 T) : ρ t = kinv * (ψ t - ψ 0) := by
  have := exactQA_momentum S.orbit ht
  rw [S.rho0, sub_zero] at this
  unfold kinv; linarith

/-- `|ψ − ψ₀| < 5/2` (from `|ρ| ≤ ρ_max`). -/
theorem x_lt {t : ℝ} (ht : t ∈ Icc 0 T) : |ψ t - ψ 0| < 5 / 2 := by
  have h1 := (S.band ht).2
  rw [S.mom ht, abs_mul, abs_of_pos (by norm_num [kinv])] at h1
  unfold kinv rhoMax at h1
  have : |ψ t - ψ 0| ≤ 177 / 10000 * (29050 / 211) := by linarith
  linarith [show (177 / 10000 * (29050 / 211) : ℝ) < 5 / 2 by norm_num]

/-- Confinement of the poloidal angle to `(−π/2, π/2)`. -/
theorem theta {t : ℝ} (ht : t ∈ Icc 0 T) : θ t ∈ Ioo (-(π / 2)) (π / 2) := by
  have hb0 : |(0 : ℝ)| ≤ 43 / 100000 := by norm_num
  have W := qaField_window hb0 S.hμ
  have hθ0 := S.theta0
  exact theta_confined (by norm_num [mα]) (by norm_num [qα])
    (by rw [exactQA, qaField_G]; norm_num) S.orbit S.energy (fun s hs => (S.band hs).1)
    W.forbid_pos W.forbid_neg ⟨by linarith [hθ0.1, pi_pos], hθ0.2⟩ t ht

/-- `0 ≤ cos θ ≤ 1` along the orbit. -/
theorem cos_mem {t : ℝ} (ht : t ∈ Icc 0 T) : 0 ≤ cos (θ t) ∧ cos (θ t) ≤ 1 :=
  ⟨cos_nonneg_of_mem_Icc ⟨(S.theta ht).1.le, (S.theta ht).2.le⟩, cos_le_one _⟩

/-- **Reduced orbit relation** at time `t` on the leg `inner` (with `x = ±(ψ₀ − ψ)`). -/
theorem rel {t : ℝ} (ht : t ∈ Icc 0 T) (inner : Bool) {x : ℝ}
    (hx : psiR inner (ψ 0) x = ψ t) (hx0 : 0 ≤ x) :
    OrbitRel inner x (ψ 0) (Eα / μ) (cos (θ t)) := by
  have hμ0 := S.mu_pos
  have hb := S.band ht
  have hpos : 0 < ψ t := lt_of_lt_of_le (by norm_num [psiLo]) hb.1.1
  have hB : 493 / 100 ≤ exactQA.B (ψ t) (θ t) (φ t) :=
    qaField_B_ge (by norm_num) hpos.le hb.1.2 _ _
  have hEn := energy_along (by norm_num [mα]) (by norm_num [qα])
    (by rw [exactQA, qaField_G]; norm_num) S.orbit S.energy ht
  simp only [along] at hEn
  rw [exactQA_B_eq] at hB hEn
  have hxsq : x ^ 2 = (ψ t - ψ 0) ^ 2 := by
    have : x = ψ t - ψ 0 ∨ x = ψ 0 - ψ t := by
      cases inner <;> simp [psiR] at hx <;> [left; right] <;> linarith
    rcases this with h | h <;> subst h <;> ring
  have hρ := S.mom ht
  refine ⟨hx0, hx ▸ hpos, hx ▸ hb.1.2.trans (by norm_num [psiEdge]),
    div_pos (by norm_num [Eα]) hμ0, hx ▸ (lt_of_lt_of_le (by norm_num) hB), ?_,
    (S.cos_mem ht).1, (S.cos_mem ht).2⟩
  rw [hx]
  set B := Bred (ψ t) (cos (θ t))
  have key := lam_identity
  rw [hρ] at hEn
  have hm : (0 : ℝ) < mα := by norm_num [mα]
  field_simp
  rw [hxsq]
  have e1 : qα ^ 2 * (kinv * (ψ t - ψ 0)) ^ 2 * B ^ 2 =
      lam * Eα * (2 * mα) * (ψ t - ψ 0) ^ 2 * B ^ 2 := by rw [key]; ring
  rw [e1] at hEn
  field_simp at hEn
  linear_combination hEn

end Setup

namespace Setup
variable {μ : ℝ} {ψ θ φ ρ : ℝ → ℝ}

/-- The drift factor `A = μ/q + qρ²B/m` (`ψ̇ = −A ∂_θB`, `Ω = −A ∂_ψB`). -/
@[expose] def Afac (t : ℝ) : ℝ := μ / qα + qα * ρ t ^ 2 * along exactQA.B ψ θ φ t / mα

/-- The precession rate `Ω = −(μ/q + qρ²B/m) ∂_ψB`. -/
@[expose] def Om (t : ℝ) : ℝ := -poloidalDrift exactQA mα qα μ ψ θ φ ρ t

/-- The poloidal velocity `θ̇` from the equations of motion. -/
@[expose] def thetaDot (t : ℝ) : ℝ :=
  (μ / qα + qα * ρ t ^ 2 * along exactQA.B ψ θ φ t / mα) * along exactQA.Bψ ψ θ φ t +
    qα * ρ t * along exactQA.B ψ θ φ t ^ 2 * exactQA.ι (ψ t) / (exactQA.G * mα)

/-- The flux velocity `ψ̇` from the equations of motion. -/
@[expose] def psiDot (t : ℝ) : ℝ :=
  -(mα * μ + qα ^ 2 * ρ t ^ 2 * along exactQA.B ψ θ φ t) * along exactQA.Bθ ψ θ φ t /
    (mα * qα)

/-- `ψ̇ = −A ∂_θB`. -/
theorem psiDot_eq (t : ℝ) : psiDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
    -(Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * along exactQA.Bθ ψ θ φ t) := by
  unfold psiDot Afac
  have hq : (qα : ℝ) ≠ 0 := by norm_num [qα]
  have hm : (mα : ℝ) ≠ 0 := by norm_num [mα]
  field_simp

/-- `Ω = A (−∂_ψB)`. -/
theorem Om_eq (t : ℝ) : Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
    Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * -along exactQA.Bψ ψ θ φ t := by
  unfold Om Afac poloidalDrift; ring


end Setup

namespace Setup
variable {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ} (S : Setup μ T ψ θ φ ρ)
include S

theorem Afac_pos {t : ℝ} (ht : t ∈ Icc 0 T) :
    0 < Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t := by
  have hb := S.band ht
  have hpos : 0 < ψ t := lt_of_lt_of_le (by norm_num [psiLo]) hb.1.1
  have hB : 493 / 100 ≤ along exactQA.B ψ θ φ t :=
    qaField_B_ge (by norm_num) hpos.le hb.1.2 _ _
  have hμ := S.mu_pos
  unfold Afac
  have hq : (0 : ℝ) < qα := by norm_num [qα]
  have hm : (0 : ℝ) < mα := by norm_num [mα]
  have : 0 ≤ qα * ρ t ^ 2 * along exactQA.B ψ θ φ t / mα := by
    apply div_nonneg _ hm.le; apply mul_nonneg (mul_nonneg hq.le (sq_nonneg _)); linarith
  have : 0 < μ / qα := div_pos hμ hq
  linarith

theorem hasDerivAt_psi {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivAt ψ (psiDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) t := S.orbit.dψ t ht

theorem hasDerivAt_theta {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivAt θ (thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) t := S.orbit.dθ t ht

/-- The bracket of `∂_θB` is positive: `∂_θB` has the sign of `sin θ`. -/
theorem Bθ_bracket_pos {t : ℝ} (ht : t ∈ Icc 0 T) :
    0 < 399 / 1000 * √(20 / 57 * ψ t) - 66 / 1000 * (20 / 57 * ψ t) * cos (θ t) := by
  have hb := S.band ht
  have hpos : 0 < ψ t := lt_of_lt_of_le (by norm_num [psiLo]) hb.1.1
  set r := √(20 / 57 * ψ t)
  have hr0 : 0 < r := sqrt_pos.mpr (by positivity)
  have hw : 20 / 57 * ψ t = r * r := (mul_self_sqrt (by positivity)).symm
  have hr : r ≤ 2 := by
    rw [sqrt_le_left (by norm_num)]; have := hb.1.2; unfold psiEdge at this; linarith
  have hc := S.cos_mem ht
  rw [hw]
  have : r * r * cos (θ t) ≤ 2 * r := by nlinarith
  nlinarith

theorem Bθ_pos {t : ℝ} (ht : t ∈ Icc 0 T) (hθ : 0 < θ t) : 0 < along exactQA.Bθ ψ θ φ t := by
  simp only [along]; rw [exactQA_Bθ_eq]
  exact mul_pos (sin_pos_of_pos_of_lt_pi hθ (by linarith [(S.theta ht).2, pi_pos]))
    (S.Bθ_bracket_pos ht)

theorem Bθ_neg {t : ℝ} (ht : t ∈ Icc 0 T) (hθ : θ t < 0) : along exactQA.Bθ ψ θ φ t < 0 := by
  simp only [along]; rw [exactQA_Bθ_eq]
  exact mul_neg_of_neg_of_pos
    (sin_neg_of_neg_of_neg_pi_lt hθ (by linarith [(S.theta ht).1, pi_pos]))
    (S.Bθ_bracket_pos ht)

/-- `ρ̇ < 0` on the upper flank, `> 0` on the lower one (sign of `−∂_θB`). -/
theorem hasDerivAt_rho {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∃ d, HasDerivAt ρ d t ∧ (0 < θ t → d < 0) ∧ (θ t < 0 → 0 < d) := by
  refine ⟨_, S.orbit.dρ t ht, fun hθ => ?_, fun hθ => ?_⟩
  all_goals
    have hb := S.band ht
    have hpos : 0 < ψ t := lt_of_lt_of_le (by norm_num [psiLo]) hb.1.1
    have hB : 493 / 100 ≤ along exactQA.B ψ θ φ t :=
      qaField_B_ge (by norm_num) hpos.le hb.1.2 _ _
    have hμ := S.mu_pos
    have hφ : along exactQA.Bφ ψ θ φ t = 0 := by simp only [along]; exact exactQA_Bφ _ _ _
    rw [hφ, zero_add, show exactQA.ι (ψ t) = 211 / 500 from rfl,
      show exactQA.G = 581 / 10 from rfl]
    have hK : 0 < mα * μ + qα ^ 2 * ρ t ^ 2 * along exactQA.B ψ θ φ t := by
      have : 0 ≤ qα ^ 2 * ρ t ^ 2 * along exactQA.B ψ θ φ t := by
        apply mul_nonneg (by positivity); linarith
      have : 0 < mα * μ := mul_pos (by norm_num [mα]) hμ
      linarith
    have hden : (0 : ℝ) < 581 / 10 * mα * qα := by norm_num [mα, qα]
  · have := S.Bθ_pos ht hθ
    apply div_neg_of_neg_of_pos _ hden
    nlinarith
  · have := S.Bθ_neg ht hθ
    apply div_pos _ hden
    nlinarith

/-- **Flank bound at a time `t`.** If `|θ t| ≥ δ` and `x` is the leg coordinate
(`psiR inner ψ₀ x = ψ t`), then `Ω ≥ 0` and `Ω ≤ M_f i · A |∂_θB|` whenever `x` is in cell `i`. -/
theorem flank_bound {inner : Bool} {Mf : ℕ → ℝ} {Mb mb : ℝ}
    (cert : LegBounds inner (ψ 0) (Eα / μ) Mf Mb mb) {t x : ℝ} (ht : t ∈ Icc 0 T)
    (hx : psiR inner (ψ 0) x = ψ t) (hx0 : 0 ≤ x) (hθ : 3 / 5 ≤ |θ t|) :
    0 ≤ Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t ∧
      ∀ i : ℕ, x ∈ Icc ((i : ℝ) / 40) (((i : ℝ) + 1) / 40) →
        Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t ≤
          Mf i * (Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
            |along exactQA.Bθ ψ θ φ t|) := by
  have hrel := S.rel ht inner hx hx0
  have hA := S.Afac_pos ht
  have hc : cos (θ t) ≤ cos (3 / 5) := by
    rw [← cos_abs (θ t)]
    have := S.theta ht
    exact cos_le_cos_of_nonneg_of_le_pi (by norm_num)
      ((abs_lt.mpr ⟨this.1, this.2⟩).le.trans (by linarith [pi_pos])) hθ
  have hnum := numR_eq hx (θ t) (φ t)
  have hden := abs_Bθ_eq hrel hx (φ t)
  have hxlt : x < 5 / 2 := by
    have := S.x_lt ht
    have e : |ψ t - ψ 0| = x := by
      cases inner <;> simp only [psiR, Bool.false_eq_true, ite_false, ite_true] at hx <;>
        rw [← hx] <;> simp [abs_of_nonneg hx0]
    linarith
  have hOm := Om_eq (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t
  simp only [along] at hOm hden ⊢
  rw [hOm, ← hnum]
  obtain ⟨i0, hi0, hxi0⟩ := exists_cell ⟨hx0, hxlt.le⟩
  obtain ⟨hn0, -⟩ := cert.flank i0 hi0 x hxi0 _ hrel hc
  refine ⟨mul_nonneg hA.le hn0, fun i hi => ?_⟩
  rcases lt_or_ge i 100 with h100 | h100
  · obtain ⟨-, hb⟩ := cert.flank i h100 x hi _ hrel hc
    rw [hden]
    calc Afac t * numR inner (ψ 0) x (cos (θ t)) ≤ Afac t * |numR inner (ψ 0) x (cos (θ t))| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hA.le
      _ ≤ Afac t * (Mf i * denR inner (ψ 0) x (cos (θ t)) (√(1 - cos (θ t) ^ 2))) :=
          mul_le_mul_of_nonneg_left hb hA.le
      _ = _ := by ring
  · exfalso
    have : (100 : ℝ) ≤ i := by exact_mod_cast h100
    have := hi.1
    rw [div_le_iff₀ (by norm_num)] at this
    linarith

/-- **Bottom bound at a time `t`.** If `|θ t| ≤ δ` and `x` is the leg coordinate, then `x > 0`
(so `ρ ≠ 0`), `θ̇` has the sign of the leg (`< 0` on the inner leg, `> 0` on the outer leg), and
`m_b |θ̇| ≤ Ω ≤ M_b |θ̇|`. -/
theorem bottom_bound {inner : Bool} {Mf : ℕ → ℝ} {Mb mb : ℝ}
    (cert : LegBounds inner (ψ 0) (Eα / μ) Mf Mb mb) {t x : ℝ} (ht : t ∈ Icc 0 T)
    (hx : psiR inner (ψ 0) x = ψ t) (hx0 : 0 ≤ x) (hθ : |θ t| ≤ 3 / 5) :
    0 < x ∧
      (inner = true → 0 < -thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t ∧
        Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t ≤
          Mb * -thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t ∧
        mb * -thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t ≤
          Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) ∧
      (inner = false → 0 < thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t ∧
        Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t ≤
          Mb * thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t ∧
        mb * thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t ≤
          Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) := by
  have hrel := S.rel ht inner hx hx0
  have hA := S.Afac_pos ht
  have hμ := S.mu_pos
  have hc : cos (3 / 5) ≤ cos (θ t) := by
    rw [← cos_abs (θ t)]
    exact cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [pi_gt_three]) hθ
  have hxlt : x < 5 / 2 := by
    have := S.x_lt ht
    have e : |ψ t - ψ 0| = x := by
      cases inner <;> simp only [psiR, Bool.false_eq_true, ite_false, ite_true] at hx <;>
        rw [← hx] <;> simp [abs_of_nonneg hx0]
    linarith
  obtain ⟨hxpos, hnr, hsign, hmb, hMb⟩ := cert.bottom x ⟨hx0, hxlt.le⟩ _ hrel hc
  have hnum := numR_eq hx (θ t) (φ t)
  have hBs := BsR_eq hrel
  rw [hx] at hBs
  have hBeq : along exactQA.B ψ θ φ t = Bred (ψ t) (cos (θ t)) := by
    simp only [along]; exact exactQA_B_eq _ _ _
  have hρ := S.mom ht
  have hEn := energy_along (by norm_num [mα]) (by norm_num [qα])
    (by rw [exactQA, qaField_G]; norm_num) S.orbit S.energy ht
  have hB0 : 0 < along exactQA.B ψ θ φ t := by
    have := hrel.B_pos; rw [hx] at this; rw [hBeq]; exact this
  -- the key identity `A n R = q kinv² x B²/m`
  have halg := bottom_alg (x := x) hμ hB0 hnr hEn
  have hRR : RR inner (ψ 0) x (Eα / μ) (cos (θ t)) =
      2 * lam * (Eα / μ * x) * (along exactQA.B ψ θ φ t * along exactQA.B ψ θ φ t ^ 2) *
        ((2 * (Eα / μ) - along exactQA.B ψ θ φ t) * numR inner (ψ 0) x (cos (θ t)))⁻¹ := by
    unfold RR; rw [hBs, ← hBeq]
  have hOm : Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
      Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * numR inner (ψ 0) x (cos (θ t)) := by
    rw [Om_eq, hnum]; simp only [along]
  have hTD : thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
      -(Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * numR inner (ψ 0) x (cos (θ t))) +
        qα * ρ t * along exactQA.B ψ θ φ t ^ 2 * kinv / mα := by
    unfold thetaDot Afac
    rw [hnum, show exactQA.ι (ψ t) = 211 / 500 from rfl, show exactQA.G = 581 / 10 from rfl]
    simp only [along]
    unfold kinv
    field_simp
    ring
  have hOmR : Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
      RR inner (ψ 0) x (Eα / μ) (cos (θ t)) =
        qα * kinv ^ 2 * x * along exactQA.B ψ θ φ t ^ 2 / mα := by
    rw [hOm, hRR]; unfold Afac; exact halg
  have hOmpos : 0 < Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t := by
    rw [hOm]; exact mul_pos hA hnr
  refine ⟨hxpos, fun hin => ?_, fun hout => ?_⟩
  · subst hin
    simp only [ite_true] at hsign
    have hρx : ρ t = -(kinv * x) := by rw [hρ, ← hx]; simp [psiR]
    have hrat : ratR true (ψ 0) x (Eα / μ) (cos (θ t)) =
        (1 + RR true (ψ 0) x (Eα / μ) (cos (θ t)))⁻¹ := by simp [ratR]
    have hneg : -thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
        Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
          (1 + RR true (ψ 0) x (Eα / μ) (cos (θ t))) := by
      rw [hTD, mul_add, mul_one, hOmR, hOm, hρx]; ring
    have hpos : 0 < -thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t := by
      rw [hneg]; exact mul_pos hOmpos hsign
    have hOm' : Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
        -thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
          ratR true (ψ 0) x (Eα / μ) (cos (θ t)) := by
      rw [hrat, hneg, mul_assoc, mul_inv_cancel₀ hsign.ne', mul_one]
    refine ⟨hpos, ?_, ?_⟩
    · rw [hOm', mul_comm Mb]; exact mul_le_mul_of_nonneg_left hMb hpos.le
    · rw [hOm', mul_comm mb]; exact mul_le_mul_of_nonneg_left hmb hpos.le
  · subst hout
    simp only [Bool.false_eq_true, ite_false] at hsign
    have hρx : ρ t = kinv * x := by rw [hρ, ← hx]; simp [psiR]
    have hrat : ratR false (ψ 0) x (Eα / μ) (cos (θ t)) =
        (RR false (ψ 0) x (Eα / μ) (cos (θ t)) - 1)⁻¹ := by simp [ratR]
    have hposeq : thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
        Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
          (RR false (ψ 0) x (Eα / μ) (cos (θ t)) - 1) := by
      rw [hTD, mul_sub, mul_one, hOmR, hOm, hρx]; ring
    have hpos : 0 < thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t := by
      rw [hposeq]; exact mul_pos hOmpos hsign
    have hOm' : Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
        thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
          ratR false (ψ 0) x (Eα / μ) (cos (θ t)) := by
      rw [hrat, hposeq, mul_assoc, mul_inv_cancel₀ hsign.ne', mul_one]
    refine ⟨hpos, ?_, ?_⟩
    · rw [hOm', mul_comm Mb]; exact mul_le_mul_of_nonneg_left hMb hpos.le
    · rw [hOm', mul_comm mb]; exact mul_le_mul_of_nonneg_left hmb hpos.le

end Setup

namespace Setup
variable {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ} (S : Setup μ T ψ θ φ ρ)
include S

theorem cont_psi : ContinuousOn ψ (Icc 0 T) :=
  fun t ht => (S.orbit.dψ t ht).continuousAt.continuousWithinAt

theorem cont_theta : ContinuousOn θ (Icc 0 T) :=
  fun t ht => (S.orbit.dθ t ht).continuousAt.continuousWithinAt

theorem cont_rho : ContinuousOn ρ (Icc 0 T) :=
  fun t ht => (S.orbit.dρ t ht).continuousAt.continuousWithinAt

theorem cont_B : ContinuousOn (along exactQA.B ψ θ φ) (Icc 0 T) :=
  fun _ ht => (S.orbit.hasDerivAt_B ht).continuousAt.continuousWithinAt

theorem psi_pos {t : ℝ} (ht : t ∈ Icc 0 T) : 0 < ψ t :=
  lt_of_lt_of_le (by norm_num [psiLo]) (S.band ht).1.1

theorem cont_Bψ : ContinuousOn (along exactQA.Bψ ψ θ φ) (Icc 0 T) := by
  have e : along exactQA.Bψ ψ θ φ = fun t => -(7 / 100 * cos (θ t) * (√(20 / 57 * ψ t))⁻¹ +
      20 / 57 * (302 / 10000 - 33 / 1000 * cos (θ t) ^ 2)) := by
    funext t; simp only [along]; exact exactQA_Bψ_eq _ _ _
  rw [e]
  have hc := continuous_cos.comp_continuousOn S.cont_theta
  have hs : ContinuousOn (fun t => √(20 / 57 * ψ t)) (Icc 0 T) :=
    (continuousOn_const.mul S.cont_psi).sqrt
  have hsi := hs.inv₀ (fun t ht => (sqrt_pos.mpr (by have := S.psi_pos ht; positivity)).ne')
  exact (((continuousOn_const.mul hc).mul hsi).add
    (continuousOn_const.mul (continuousOn_const.sub (continuousOn_const.mul (hc.pow 2))))).neg

theorem cont_Bθ : ContinuousOn (along exactQA.Bθ ψ θ φ) (Icc 0 T) := by
  have e : along exactQA.Bθ ψ θ φ = fun t => sin (θ t) * (399 / 1000 * √(20 / 57 * ψ t) -
      66 / 1000 * (20 / 57 * ψ t) * cos (θ t)) := by
    funext t; simp only [along]; exact exactQA_Bθ_eq _ _ _
  rw [e]
  have hc := continuous_cos.comp_continuousOn S.cont_theta
  have hsn := continuous_sin.comp_continuousOn S.cont_theta
  have hs : ContinuousOn (fun t => √(20 / 57 * ψ t)) (Icc 0 T) :=
    (continuousOn_const.mul S.cont_psi).sqrt
  exact hsn.mul ((continuousOn_const.mul hs).sub
    ((continuousOn_const.mul (continuousOn_const.mul S.cont_psi)).mul hc))

theorem cont_Afac : ContinuousOn (Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ)) (Icc 0 T) := by
  unfold Afac
  exact continuousOn_const.add
    (((continuousOn_const.mul (S.cont_rho.pow 2)).mul S.cont_B).div_const _)

theorem cont_Om : ContinuousOn (Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ)) (Icc 0 T) := by
  have e : Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) =
      fun t => Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * -along exactQA.Bψ ψ θ φ t := by
    funext t; exact Om_eq t
  rw [e]; exact S.cont_Afac.mul S.cont_Bψ.neg

theorem cont_psiDot :
    ContinuousOn (psiDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ)) (Icc 0 T) := by
  have e : psiDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) =
      fun t => -(Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
        along exactQA.Bθ ψ θ φ t) := by
    funext t; exact psiDot_eq t
  rw [e]; exact (S.cont_Afac.mul S.cont_Bθ).neg

theorem cont_thetaDot :
    ContinuousOn (thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ)) (Icc 0 T) := by
  unfold thetaDot
  have hA : ContinuousOn (fun t => μ / qα + qα * ρ t ^ 2 * along exactQA.B ψ θ φ t / mα)
      (Icc 0 T) :=
    continuousOn_const.add (((continuousOn_const.mul (S.cont_rho.pow 2)).mul S.cont_B).div_const _)
  exact (hA.mul S.cont_Bψ).add ((((continuousOn_const.mul S.cont_rho).mul (S.cont_B.pow 2)).mul
    continuousOn_const).div_const _)

end Setup

/-! ## The two legs of a bounce -/

namespace Setup
variable {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ} (S : Setup μ T ψ θ φ ρ)
include S

omit S in
/-- Cell membership in the form used by `integral_le_cell_sum`. -/
theorem cell_iff {x : ℝ} (i : ℕ) :
    x ∈ Icc ((i : ℝ) * (1 / 40)) (((i : ℝ) + 1) * (1 / 40)) ↔
      x ∈ Icc ((i : ℝ) / 40) (((i : ℝ) + 1) / 40) := by
  constructor <;> intro h <;> constructor <;> [linarith [h.1]; linarith [h.2]; linarith [h.1];
    linarith [h.2]]

omit S in
/-- `θ ≥ δ` on a flank piece gives `|θ| ≥ δ`. -/
theorem abs_ge_of_ge {y : ℝ} (h : 3 / 5 ≤ y) : 3 / 5 ≤ |y| := h.trans (le_abs_self y)

omit S in
/-- `θ ≤ −δ` on a flank piece gives `|θ| ≥ δ`. -/
theorem abs_ge_of_le {y : ℝ} (h : y ≤ -(3 / 5)) : 3 / 5 ≤ |y| := by
  rw [abs_of_neg (by linarith)]; linarith

/-- **Inner leg.** On a stretch `[a, b]` with `ρ(a) = ρ(b) = 0`, `ρ < 0` in between,
`θ(a) > δ` and `θ(b) < −δ`, the precession integral satisfies
`(6/5) m_b ≤ ∫_a^b Ω ≤ 2 (1/40) Σ M_f + (6/5) M_b`. -/
theorem inner_leg {Mf : ℕ → ℝ} {Mb mb : ℝ} (cert : LegBounds true (ψ 0) (Eα / μ) Mf Mb mb)
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a < b) (hbT : b ≤ T) (hρa : ρ a = 0) (hρb : ρ b = 0)
    (hneg : ∀ t ∈ Ioo a b, ρ t < 0) (hθa : 3 / 5 < θ a) (hθb : θ b < -(3 / 5)) :
    6 / 5 * mb ≤ ∫ t in a..b, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t ∧
      ∫ t in a..b, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t ≤
        2 * (1 / 40 * ∑ i ∈ Finset.range 100, Mf i) + 6 / 5 * Mb := by
  have hI : ∀ t ∈ Icc a b, t ∈ Icc 0 T := fun t ht => ⟨ha0.trans ht.1, ht.2.trans hbT⟩
  have hsub : Icc a b ⊆ Icc 0 T := fun t ht => hI t ht
  have hρle : ∀ t ∈ Icc a b, ρ t ≤ 0 := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, hρa]
    rcases eq_or_lt_of_le ht.2 with h' | h'
    · rw [h', hρb]
    · exact (hneg t ⟨h, h'⟩).le
  -- the leg coordinate `x = ψ₀ − ψ`
  have hxψ : ∀ t ∈ Icc a b, psiR true (ψ 0) (ψ 0 - ψ t) = ψ t := fun t _ => by simp [psiR]
  have hx0 : ∀ t ∈ Icc a b, 0 ≤ ψ 0 - ψ t := by
    intro t ht
    have h1 := S.mom (hI t ht); have h2 := hρle t ht
    unfold kinv at h1; nlinarith
  have hxlt : ∀ t ∈ Icc a b, ψ 0 - ψ t ≤ (99 + 1) * (1 / 40) := by
    intro t ht; have := S.x_lt (hI t ht)
    rw [abs_sub_comm] at this; norm_num; linarith [le_abs_self (ψ 0 - ψ t)]
  have hθc : ContinuousOn θ (Icc a b) := S.cont_theta.mono hsub
  have hΩc := S.cont_Om.mono hsub
  have hdc := S.cont_psiDot.mono hsub
  have htc := S.cont_thetaDot.mono hsub
  -- first hits of `±δ`
  obtain ⟨s1, hs1, hθs1, hbef1⟩ := first_hit (g := θ) (c := 3 / 5) hab.le hθc hθa (by linarith)
  obtain ⟨s2, hs2, hθs2, hbef2⟩ := first_hit (g := θ) (c := -(3 / 5)) hs1.2 (hθc.mono
    (Icc_subset_Icc hs1.1.le le_rfl)) (by linarith) hθb.le
  have hs2b : s2 < b := lt_of_le_of_ne hs2.2 (fun h => by rw [h] at hθs2; linarith)
  -- `θ̇ < 0` at bottom points of the inner leg
  have hdown : ∀ t ∈ Ioo a b, |θ t| ≤ 3 / 5 → thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ)
      (ρ := ρ) t < 0 := by
    intro t ht hθt
    have htI : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
    have := ((S.bottom_bound cert (hI t htI) (hxψ t htI) (hx0 t htI) hθt).2.1 rfl).1
    linarith
  have hlt1 : ∀ t ∈ Ioc s1 b, θ t < 3 / 5 := by
    refine lt_of_level_deriv_neg (hθc.mono (Icc_subset_Icc hs1.1.le le_rfl)) hθs1.le ?_
    intro t ht hθt
    have htb : t < b := lt_of_le_of_ne ht.2 (fun h => by rw [h] at hθt; linarith)
    have hta : a < t := lt_of_lt_of_le hs1.1 ht.1
    exact ⟨_, hdown t ⟨hta, htb⟩ (by rw [hθt, abs_of_pos (by norm_num)]),
      S.hasDerivAt_theta (hI t ⟨hta.le, htb.le⟩)⟩
  have hlt2 : ∀ t ∈ Ioc s2 b, θ t < -(3 / 5) := by
    refine lt_of_level_deriv_neg (hθc.mono (Icc_subset_Icc (hs1.1.le.trans hs2.1.le) le_rfl))
      hθs2.le ?_
    intro t ht hθt
    have htb : t < b := lt_of_le_of_ne ht.2 (fun h => by rw [h] at hθt; linarith)
    have hta : a < t := lt_of_lt_of_le (hs1.1.trans hs2.1) ht.1
    exact ⟨_, hdown t ⟨hta, htb⟩ (by rw [hθt, abs_neg, abs_of_pos (by norm_num)]),
      S.hasDerivAt_theta (hI t ⟨hta.le, htb.le⟩)⟩
  -- piece 1: upper flank `[a, s1]`
  have hsa1 : Icc a s1 ⊆ Icc a b := Icc_subset_Icc le_rfl hs1.2
  have hθ1 : ∀ t ∈ Icc a s1, 3 / 5 ≤ θ t := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h, hθs1]
    · exact (hbef1 t ⟨ht.1, h⟩).le
  have hx1 : ∀ t ∈ Icc a s1, HasDerivAt (fun s => ψ 0 - ψ s)
      (-psiDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) t :=
    fun t ht => (S.hasDerivAt_psi (hI t (hsa1 ht))).const_sub (ψ 0)
  have hψa : ψ a = ψ 0 := by
    have := S.mom (hI a ⟨le_rfl, hab.le⟩); rw [hρa] at this; unfold kinv at this; linarith
  have hψb : ψ b = ψ 0 := by
    have := S.mom (hI b ⟨hab.le, le_rfl⟩); rw [hρb] at this; unfold kinv at this; linarith
  have P1 := integral_le_cell_sum (Ω := Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ))
    (h := 1 / 40) (M := Mf) (n := 99) hs1.1.le (by norm_num) hx1
    (fun t ht => by
      rw [psiDot_eq, neg_neg]
      exact mul_nonneg (S.Afac_pos (hI t (hsa1 ht))).le
        (S.Bθ_pos (hI t (hsa1 ht)) (by linarith [hθ1 t ht])).le)
    (hΩc.mono hsa1) (hdc.mono hsa1).neg (by simp [hψa]) (hxlt s1 ⟨hs1.1.le, hs1.2⟩)
    cert.Mf_nonneg
    (fun t ht i hi => by
      have htI := hI t (hsa1 ht)
      have := ((S.flank_bound cert htI (hxψ t (hsa1 ht)) (hx0 t (hsa1 ht))
        (abs_ge_of_ge (hθ1 t ht))).2 i ((cell_iff i).mp hi))
      rw [psiDot_eq, neg_neg]
      rwa [abs_of_pos (S.Bθ_pos htI (by linarith [hθ1 t ht]))] at this)
  have P1' : 0 ≤ ∫ t in a..s1, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t :=
    intervalIntegral.integral_nonneg hs1.1.le (fun t ht =>
      (S.flank_bound cert (hI t (hsa1 ht)) (hxψ t (hsa1 ht)) (hx0 t (hsa1 ht))
        (abs_ge_of_ge (hθ1 t ht))).1)
  -- piece 2: bottom `[s1, s2]`
  have hs12 : Icc s1 s2 ⊆ Icc a b := Icc_subset_Icc hs1.1.le hs2.2
  have hbot : ∀ t ∈ Icc s1 s2, |θ t| ≤ 3 / 5 ∧ t ∈ Ioo a b := by
    intro t ht
    refine ⟨abs_le.mpr ⟨?_, ?_⟩, lt_of_lt_of_le hs1.1 ht.1, lt_of_le_of_lt ht.2 hs2b⟩
    · rcases eq_or_lt_of_le ht.2 with h | h
      · rw [h, hθs2]
      · exact (hbef2 t ⟨ht.1, h⟩).le
    · rcases eq_or_lt_of_le ht.1 with h | h
      · rw [← h, hθs1]
      · exact (hlt1 t ⟨h, ht.2.trans hs2.2⟩).le
  have hBB : ∀ t ∈ Icc s1 s2, _ := fun t ht =>
    ((S.bottom_bound cert (hI t (hs12 ht)) (hxψ t (hs12 ht)) (hx0 t (hs12 ht)) (hbot t ht).1).2.1
      rfl)
  have P2 := integral_le_mul_drop (M := Mb) hs2.1.le
    (fun t ht => S.hasDerivAt_theta (hI t (hs12 ht))) (hΩc.mono hs12) (htc.mono hs12)
    (fun t ht => (hBB t ht).2.1)
  have P2' := mul_drop_le_integral (M := mb) hs2.1.le
    (fun t ht => S.hasDerivAt_theta (hI t (hs12 ht))) (hΩc.mono hs12) (htc.mono hs12)
    (fun t ht => (hBB t ht).2.2)
  rw [hθs1, hθs2] at P2 P2'
  -- piece 3: lower flank `[s2, b]`
  have hs2b' : Icc s2 b ⊆ Icc a b := Icc_subset_Icc (hs1.1.le.trans hs2.1.le) le_rfl
  have hθ3 : ∀ t ∈ Icc s2 b, θ t ≤ -(3 / 5) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, hθs2]
    · exact (hlt2 t ⟨h, ht.2⟩).le
  have hx3 : ∀ t ∈ Icc s2 b, HasDerivAt (fun s => ψ 0 - ψ s)
      (-psiDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) t :=
    fun t ht => (S.hasDerivAt_psi (hI t (hs2b' ht))).const_sub (ψ 0)
  have P3 := integral_le_cell_sum_rev (Ω := Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ))
    (h := 1 / 40) (M := Mf) (n := 99) hs2b.le (by norm_num) hx3
    (fun t ht => by
      rw [psiDot_eq, neg_neg]
      exact mul_nonpos_of_nonneg_of_nonpos (S.Afac_pos (hI t (hs2b' ht))).le
        (S.Bθ_neg (hI t (hs2b' ht)) (by linarith [hθ3 t ht])).le)
    (hΩc.mono hs2b') (hdc.mono hs2b').neg (by simp [hψb]) (hxlt s2 (hs2b' ⟨le_rfl, hs2b.le⟩))
    cert.Mf_nonneg
    (fun t ht i hi => by
      have htI := hI t (hs2b' ht)
      have := ((S.flank_bound cert htI (hxψ t (hs2b' ht)) (hx0 t (hs2b' ht))
        (abs_ge_of_le (hθ3 t ht))).2 i ((cell_iff i).mp hi))
      rw [neg_neg, psiDot_eq, ← mul_neg]
      rwa [abs_of_neg (S.Bθ_neg htI (by linarith [hθ3 t ht]))] at this)
  have P3' : 0 ≤ ∫ t in s2..b, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t :=
    intervalIntegral.integral_nonneg hs2b.le (fun t ht =>
      (S.flank_bound cert (hI t (hs2b' ht)) (hxψ t (hs2b' ht)) (hx0 t (hs2b' ht))
        (abs_ge_of_le (hθ3 t ht))).1)
  -- assemble
  have hint : ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b →
      IntervalIntegrable (Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ))
        MeasureTheory.volume u v := by
    intro u v hau huv hvb
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le huv]; exact hΩc.mono (Icc_subset_Icc hau hvb)
  have hsplit : ∫ t in a..b, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
      (∫ t in a..s1, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) +
      (∫ t in s1..s2, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) +
      ∫ t in s2..b, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint a s1 le_rfl hs1.1.le hs1.2)
      (hint s1 s2 hs1.1.le hs2.1.le hs2.2),
      intervalIntegral.integral_add_adjacent_intervals (hint a s2 le_rfl (hs1.1.le.trans hs2.1.le)
        hs2.2) (hint s2 b (hs1.1.le.trans hs2.1.le) hs2b.le le_rfl)]
  rw [hsplit]
  constructor
  · nlinarith
  · have : (99 : ℕ) + 1 = 100 := rfl
    rw [this] at P1 P3
    nlinarith

/-- **Outer leg.** On a stretch `[a, b]` with `ρ(a) = ρ(b) = 0`, `ρ > 0` in between,
`θ(a) < −δ` and `θ(b) > δ`, the precession integral satisfies
`(6/5) m_b ≤ ∫_a^b Ω ≤ 2 (1/40) Σ M_f + (6/5) M_b`. -/
theorem outer_leg {Mf : ℕ → ℝ} {Mb mb : ℝ} (cert : LegBounds false (ψ 0) (Eα / μ) Mf Mb mb)
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a < b) (hbT : b ≤ T) (hρa : ρ a = 0) (hρb : ρ b = 0)
    (hpos : ∀ t ∈ Ioo a b, 0 < ρ t) (hθa : θ a < -(3 / 5)) (hθb : 3 / 5 < θ b) :
    6 / 5 * mb ≤ ∫ t in a..b, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t ∧
      ∫ t in a..b, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t ≤
        2 * (1 / 40 * ∑ i ∈ Finset.range 100, Mf i) + 6 / 5 * Mb := by
  have hI : ∀ t ∈ Icc a b, t ∈ Icc 0 T := fun t ht => ⟨ha0.trans ht.1, ht.2.trans hbT⟩
  have hsub : Icc a b ⊆ Icc 0 T := fun t ht => hI t ht
  have hρge : ∀ t ∈ Icc a b, 0 ≤ ρ t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, hρa]
    rcases eq_or_lt_of_le ht.2 with h' | h'
    · rw [h', hρb]
    · exact (hpos t ⟨h, h'⟩).le
  have hxψ : ∀ t ∈ Icc a b, psiR false (ψ 0) (ψ t - ψ 0) = ψ t := fun t _ => by simp [psiR]
  have hx0 : ∀ t ∈ Icc a b, 0 ≤ ψ t - ψ 0 := by
    intro t ht
    have h1 := S.mom (hI t ht); have h2 := hρge t ht
    unfold kinv at h1; nlinarith
  have hxlt : ∀ t ∈ Icc a b, ψ t - ψ 0 ≤ (99 + 1) * (1 / 40) := by
    intro t ht; have := S.x_lt (hI t ht)
    norm_num; linarith [le_abs_self (ψ t - ψ 0)]
  have hθc : ContinuousOn θ (Icc a b) := S.cont_theta.mono hsub
  have hΩc := S.cont_Om.mono hsub
  have hdc := S.cont_psiDot.mono hsub
  have htc := S.cont_thetaDot.mono hsub
  have hnθ : ∀ t ∈ Icc a b, HasDerivAt (fun s => -θ s)
      (-thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) t :=
    fun t ht => (S.hasDerivAt_theta (hI t ht)).neg
  -- first hits of `∓δ` (from below)
  obtain ⟨s1, hs1, hθs1, hbef1⟩ := first_hit (g := fun t => -θ t) (c := 3 / 5) hab.le hθc.neg
    (by linarith) (by linarith)
  obtain ⟨s2, hs2, hθs2, hbef2⟩ := first_hit (g := fun t => -θ t) (c := -(3 / 5)) hs1.2
    (hθc.mono (Icc_subset_Icc hs1.1.le le_rfl)).neg (by linarith)
    (by linarith)
  have hs2b : s2 < b := lt_of_le_of_ne hs2.2 (fun h => by rw [h] at hθs2; linarith)
  -- `θ̇ > 0` at bottom points of the outer leg
  have hup : ∀ t ∈ Ioo a b, |θ t| ≤ 3 / 5 → 0 < thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ)
      (ρ := ρ) t := by
    intro t ht hθt
    have htI : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
    exact ((S.bottom_bound cert (hI t htI) (hxψ t htI) (hx0 t htI) hθt).2.2 rfl).1
  have hlt1 : ∀ t ∈ Ioc s1 b, -θ t < 3 / 5 := by
    refine lt_of_level_deriv_neg (f := fun t => -θ t)
      (hθc.mono (Icc_subset_Icc hs1.1.le le_rfl)).neg hθs1.le ?_
    intro t ht hθt
    have htb : t < b := lt_of_le_of_ne ht.2 (fun h => by rw [h] at hθt; linarith)
    have hta : a < t := lt_of_lt_of_le hs1.1 ht.1
    exact ⟨_, by linarith [hup t ⟨hta, htb⟩ (by rw [abs_le]; constructor <;> linarith)],
      hnθ t ⟨hta.le, htb.le⟩⟩
  have hlt2 : ∀ t ∈ Ioc s2 b, -θ t < -(3 / 5) := by
    refine lt_of_level_deriv_neg (f := fun t => -θ t)
      (hθc.mono (Icc_subset_Icc (hs1.1.le.trans hs2.1.le) le_rfl)).neg hθs2.le ?_
    intro t ht hθt
    have htb : t < b := lt_of_le_of_ne ht.2 (fun h => by rw [h] at hθt; linarith)
    have hta : a < t := lt_of_lt_of_le (hs1.1.trans hs2.1) ht.1
    exact ⟨_, by linarith [hup t ⟨hta, htb⟩ (by rw [abs_le]; constructor <;> linarith)],
      hnθ t ⟨hta.le, htb.le⟩⟩
  have hψa : ψ a = ψ 0 := by
    have := S.mom (hI a ⟨le_rfl, hab.le⟩); rw [hρa] at this; unfold kinv at this; linarith
  have hψb : ψ b = ψ 0 := by
    have := S.mom (hI b ⟨hab.le, le_rfl⟩); rw [hρb] at this; unfold kinv at this; linarith
  -- piece 1: lower flank `[a, s1]`
  have hsa1 : Icc a s1 ⊆ Icc a b := Icc_subset_Icc le_rfl hs1.2
  have hθ1 : ∀ t ∈ Icc a s1, θ t ≤ -(3 / 5) := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h]; linarith
    · linarith [hbef1 t ⟨ht.1, h⟩]
  have hx1 : ∀ t ∈ Icc a s1, HasDerivAt (fun s => ψ s - ψ 0)
      (psiDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) t :=
    fun t ht => (S.hasDerivAt_psi (hI t (hsa1 ht))).sub_const (ψ 0)
  have P1 := integral_le_cell_sum (Ω := Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ))
    (h := 1 / 40) (M := Mf) (n := 99) hs1.1.le (by norm_num) hx1
    (fun t ht => by
      rw [psiDot_eq, ← mul_neg]
      exact mul_nonneg (S.Afac_pos (hI t (hsa1 ht))).le
        (neg_nonneg.mpr (S.Bθ_neg (hI t (hsa1 ht)) (by linarith [hθ1 t ht])).le))
    (hΩc.mono hsa1) (hdc.mono hsa1) (by simp [hψa]) (hxlt s1 ⟨hs1.1.le, hs1.2⟩)
    cert.Mf_nonneg
    (fun t ht i hi => by
      have htI := hI t (hsa1 ht)
      have := ((S.flank_bound cert htI (hxψ t (hsa1 ht)) (hx0 t (hsa1 ht))
        (abs_ge_of_le (hθ1 t ht))).2 i ((cell_iff i).mp hi))
      rw [psiDot_eq, ← mul_neg]
      rwa [abs_of_neg (S.Bθ_neg htI (by linarith [hθ1 t ht]))] at this)
  have P1' : 0 ≤ ∫ t in a..s1, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t :=
    intervalIntegral.integral_nonneg hs1.1.le (fun t ht =>
      (S.flank_bound cert (hI t (hsa1 ht)) (hxψ t (hsa1 ht)) (hx0 t (hsa1 ht))
        (abs_ge_of_le (hθ1 t ht))).1)
  -- piece 2: bottom `[s1, s2]`
  have hs12 : Icc s1 s2 ⊆ Icc a b := Icc_subset_Icc hs1.1.le hs2.2
  have hbot : ∀ t ∈ Icc s1 s2, |θ t| ≤ 3 / 5 := by
    intro t ht
    refine abs_le.mpr ⟨?_, ?_⟩
    · rcases eq_or_lt_of_le ht.1 with h | h
      · rw [← h]; linarith
      · linarith [hlt1 t ⟨h, ht.2.trans hs2.2⟩]
    · rcases eq_or_lt_of_le ht.2 with h | h
      · rw [h]; linarith
      · linarith [hbef2 t ⟨ht.1, h⟩]
  have hBB : ∀ t ∈ Icc s1 s2, _ := fun t ht =>
    ((S.bottom_bound cert (hI t (hs12 ht)) (hxψ t (hs12 ht)) (hx0 t (hs12 ht)) (hbot t ht)).2.2
      rfl)
  have P2 := integral_le_mul_drop (M := Mb) hs2.1.le (fun t ht => hnθ t (hs12 ht))
    (hΩc.mono hs12) (htc.mono hs12).neg (fun t ht => by rw [neg_neg]; exact (hBB t ht).2.1)
  have P2' := mul_drop_le_integral (M := mb) hs2.1.le (fun t ht => hnθ t (hs12 ht))
    (hΩc.mono hs12) (htc.mono hs12).neg (fun t ht => by rw [neg_neg]; exact (hBB t ht).2.2)
  rw [show -θ s1 - -θ s2 = 6 / 5 by linarith] at P2 P2'
  -- piece 3: upper flank `[s2, b]`
  have hs2b' : Icc s2 b ⊆ Icc a b := Icc_subset_Icc (hs1.1.le.trans hs2.1.le) le_rfl
  have hθ3 : ∀ t ∈ Icc s2 b, 3 / 5 ≤ θ t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]; linarith
    · linarith [hlt2 t ⟨h, ht.2⟩]
  have hx3 : ∀ t ∈ Icc s2 b, HasDerivAt (fun s => ψ s - ψ 0)
      (psiDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) t :=
    fun t ht => (S.hasDerivAt_psi (hI t (hs2b' ht))).sub_const (ψ 0)
  have P3 := integral_le_cell_sum_rev (Ω := Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ))
    (h := 1 / 40) (M := Mf) (n := 99) hs2b.le (by norm_num) hx3
    (fun t ht => by
      rw [psiDot_eq, neg_nonpos]
      exact mul_nonneg (S.Afac_pos (hI t (hs2b' ht))).le
        (S.Bθ_pos (hI t (hs2b' ht)) (by linarith [hθ3 t ht])).le)
    (hΩc.mono hs2b') (hdc.mono hs2b') (by simp [hψb]) (hxlt s2 (hs2b' ⟨le_rfl, hs2b.le⟩))
    cert.Mf_nonneg
    (fun t ht i hi => by
      have htI := hI t (hs2b' ht)
      have := ((S.flank_bound cert htI (hxψ t (hs2b' ht)) (hx0 t (hs2b' ht))
        (abs_ge_of_ge (hθ3 t ht))).2 i ((cell_iff i).mp hi))
      rw [psiDot_eq, neg_neg]
      rwa [abs_of_pos (S.Bθ_pos htI (by linarith [hθ3 t ht]))] at this)
  have P3' : 0 ≤ ∫ t in s2..b, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t :=
    intervalIntegral.integral_nonneg hs2b.le (fun t ht =>
      (S.flank_bound cert (hI t (hs2b' ht)) (hxψ t (hs2b' ht)) (hx0 t (hs2b' ht))
        (abs_ge_of_ge (hθ3 t ht))).1)
  -- assemble
  have hint : ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b →
      IntervalIntegrable (Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ))
        MeasureTheory.volume u v := by
    intro u v hau huv hvb
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le huv]; exact hΩc.mono (Icc_subset_Icc hau hvb)
  have hsplit : ∫ t in a..b, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
      (∫ t in a..s1, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) +
      (∫ t in s1..s2, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) +
      ∫ t in s2..b, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint a s1 le_rfl hs1.1.le hs1.2)
      (hint s1 s2 hs1.1.le hs2.1.le hs2.2),
      intervalIntegral.integral_add_adjacent_intervals (hint a s2 le_rfl (hs1.1.le.trans hs2.1.le)
        hs2.2) (hint s2 b (hs1.1.le.trans hs2.1.le) hs2b.le le_rfl)]
  rw [hsplit]
  constructor
  · nlinarith
  · have : (99 : ℕ) + 1 = 100 := rfl
    rw [this] at P1 P3
    nlinarith

end Setup

/-- **First zero after a downward start.** If `g(a) = 0`, `g'(a) < 0`, `g` is continuous on
`[a, b]` and `g(b) = 0`, then there is a first zero `z ∈ (a, b]` with `g < 0` on `(a, z)`. -/
theorem first_zero_after {g : ℝ → ℝ} {a b d : ℝ} (hab : a < b) (hg : ContinuousOn g (Icc a b))
    (ha : g a = 0) (hd : HasDerivAt g d a) (hneg : d < 0) (hb : g b = 0) :
    ∃ z ∈ Ioc a b, g z = 0 ∧ ∀ t ∈ Ioo a z, g t < 0 := by
  have hev := eventually_lt_right_of_hasDerivAt_neg hd hneg
  rw [ha] at hev
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  set e := min ((a + u) / 2) ((a + b) / 2) with he
  have hu' : a < u := hu
  have he1 : a < e := lt_min (by linarith) (by linarith)
  have he2 : e < u := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have he3 : e < b := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hge : g e < 0 := hsub ⟨he1, he2⟩
  obtain ⟨z, hz, hgz, hbefore⟩ := first_hit (g := fun t => -g t) (c := 0) he3.le
    (hg.mono (Icc_subset_Icc he1.le le_rfl)).neg (by simp; linarith) (by simp [hb])
  refine ⟨z, ⟨he1.trans hz.1, hz.2⟩, by simpa using hgz, fun t ht => ?_⟩
  rcases lt_or_ge t e with h | h
  · exact hsub ⟨ht.1, h.trans he2⟩
  · have := hbefore t ⟨h, ht.2⟩; simp at this; linarith

/-! ## The bounce closes -/

namespace Setup
variable {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ} (S : Setup μ T ψ θ φ ρ)
include S

/-- At a time with `ρ = 0` the orbit is not at the bottom of the well (`|θ| > δ`). -/
theorem not_bottom_of_turning {Mf : ℕ → ℝ} {Mb mb : ℝ}
    (cert : LegBounds true (ψ 0) (Eα / μ) Mf Mb mb) {t : ℝ} (ht : t ∈ Icc 0 T) (hρ : ρ t = 0) :
    ¬ |θ t| ≤ 3 / 5 := by
  intro hθ
  have hψ : ψ t = ψ 0 := by
    have := S.mom ht; rw [hρ] at this; unfold kinv at this; linarith
  have hx : psiR true (ψ 0) (ψ 0 - ψ t) = ψ t := by simp [psiR]
  have := (S.bottom_bound cert ht hx (by rw [hψ, sub_self]) hθ).1
  rw [hψ, sub_self] at this
  exact lt_irrefl _ this

/-- **The bounce closes.** There are times `0 < z₁ < z₂ ≤ 2 · 8 × 10⁻⁴ s` with `ρ(z₁) = ρ(z₂) = 0`,
`ρ < 0` on `(0, z₁)`, `ρ > 0` on `(z₁, z₂)`, `θ(0) > δ`, `θ(z₁) < −δ`, `θ(z₂) > δ`, and the reduced
state returns: `ψ(z₂) = ψ(0)`, `θ(z₂) = θ(0)` (and `ρ(z₂) = ρ(0) = 0`). -/
theorem bounce_closes {Mf : ℕ → ℝ} {Mb mb : ℝ} (cert : LegBounds true (ψ 0) (Eα / μ) Mf Mb mb)
    (hT : 2 * Lhalf ≤ T) :
    ∃ z₁ z₂ : ℝ, 0 < z₁ ∧ z₁ < z₂ ∧ z₂ ≤ 2 * Lhalf ∧ ρ z₁ = 0 ∧ ρ z₂ = 0 ∧
      (∀ t ∈ Ioo 0 z₁, ρ t < 0) ∧ (∀ t ∈ Ioo z₁ z₂, 0 < ρ t) ∧
      3 / 5 < θ 0 ∧ θ z₁ < -(3 / 5) ∧ 3 / 5 < θ z₂ ∧ ψ z₂ = ψ 0 ∧ θ z₂ = θ 0 := by
  have hm : (mα : ℝ) ≠ 0 := by norm_num [mα]
  have hq : (qα : ℝ) ≠ 0 := by norm_num [qα]
  obtain ⟨τ, h0, hmono, hstep, htp, hle, -, -⟩ := exactQA_turning_points S.hμ S.orbit S.energy
    S.rho0 S.psi0 S.theta0 2 (by push_cast; exact hT)
  have hL : (0 : ℝ) < Lhalf := by norm_num [Lhalf]
  have h01 := hstep 0 (by norm_num)
  have h12 := hstep 1 (by norm_num)
  have hτ2 : τ 2 ≤ 2 * Lhalf := by have := hle 2 le_rfl; push_cast at this; exact this
  rw [h0] at h01
  have hτ1 : 0 < τ 1 := h01.1
  have hT0 : 0 ≤ T := by linarith
  have hI : ∀ t, 0 ≤ t → t ≤ τ 2 → t ∈ Icc 0 T := fun t h1 h2 => ⟨h1, by linarith⟩
  have hρτ : ∀ k ≤ 2, ρ (τ k) = 0 := fun k hk =>
    rho_eq_zero_of_turning hm hq (htp k hk).2.1.ne' (htp k hk).1
  have hθ0pos := S.theta0.1
  have hθ0 : 3 / 5 < θ 0 := by
    by_contra h
    exact S.not_bottom_of_turning cert ⟨le_rfl, hT0⟩ S.rho0
      (abs_le.mpr ⟨by linarith, by linarith⟩)
  -- first zero of `ρ` after `0`
  obtain ⟨d0, hd0, hd0n, -⟩ := S.hasDerivAt_rho (t := 0) ⟨le_rfl, hT0⟩
  obtain ⟨z₁, hz₁, hρz₁, hneg⟩ := first_zero_after hτ1
    (S.cont_rho.mono (Icc_subset_Icc le_rfl (by linarith))) S.rho0 hd0 (hd0n hθ0pos)
    (hρτ 1 (by norm_num))
  have hz₁I : z₁ ∈ Icc 0 T := hI z₁ hz₁.1.le (by linarith [hz₁.2])
  have hθz₁ : θ z₁ < -(3 / 5) := by
    by_contra h
    push Not at h
    rcases le_or_gt (θ z₁) (3 / 5) with h' | h'
    · exact S.not_bottom_of_turning cert hz₁I hρz₁ (abs_le.mpr ⟨h, h'⟩)
    · obtain ⟨d, hd, hdn, -⟩ := S.hasDerivAt_rho hz₁I
      exact false_of_hasDerivAt_neg_left hd (hdn (by linarith)) (by linarith [hz₁.1] :
        z₁ / 2 < z₁) (fun y hy => by
          rw [hρz₁]; exact hneg y ⟨by linarith [hy.1, hz₁.1], hy.2⟩)
  -- first zero after `z₁`
  have hz₁τ2 : z₁ < τ 2 := lt_of_le_of_lt hz₁.2 h12.1
  obtain ⟨d1, hd1, -, hd1p⟩ := S.hasDerivAt_rho hz₁I
  obtain ⟨z₂, hz₂, hρz₂, hpos⟩ := first_zero_after (g := fun t => -ρ t) hz₁τ2
    (S.cont_rho.mono (Icc_subset_Icc hz₁.1.le (by linarith))).neg (by simp [hρz₁]) hd1.neg
    (by linarith [hd1p (by linarith)]) (by simp [hρτ 2 le_rfl])
  simp only [neg_eq_zero] at hρz₂
  have hpos' : ∀ t ∈ Ioo z₁ z₂, 0 < ρ t := fun t ht => by linarith [hpos t ht]
  have hz₂I : z₂ ∈ Icc 0 T := hI z₂ (by linarith [hz₁.1, hz₂.1]) hz₂.2
  have hθz₂ : 3 / 5 < θ z₂ := by
    by_contra h
    push Not at h
    rcases le_or_gt (-(3 / 5)) (θ z₂) with h' | h'
    · exact S.not_bottom_of_turning cert hz₂I hρz₂ (abs_le.mpr ⟨h', h⟩)
    · obtain ⟨d, hd, -, hdp⟩ := S.hasDerivAt_rho hz₂I
      exact false_of_hasDerivAt_neg_left (f := fun t => -ρ t) hd.neg
        (by linarith [hdp (by linarith)]) (by linarith [hz₂.1] : (z₁ + z₂) / 2 < z₂)
        (fun y hy => by
          simp only [hρz₂, neg_zero]
          linarith [hpos' y ⟨by linarith [hy.1, hz₂.1], hy.2⟩])
  -- the reduced state returns
  have hψz₂ : ψ z₂ = ψ 0 := by
    have := S.mom hz₂I; rw [hρz₂] at this; unfold kinv at this; linarith
  have hBt : ∀ t ∈ Icc 0 T, ψ t = ψ 0 → Bred (ψ 0) (cos (θ t)) = Eα / μ := by
    intro t ht hψt
    have hx : psiR true (ψ 0) (ψ 0 - ψ t) = ψ t := by simp [psiR]
    have hrel := S.rel ht true hx (by rw [hψt, sub_self])
    have hE := hrel.energy
    rw [hx, hψt, sub_self] at hE
    simpa using hE
  have hc : cos (θ z₂) = cos (θ 0) := by
    have h1 := hBt z₂ hz₂I hψz₂
    have h2 := hBt 0 ⟨le_rfl, hT0⟩ rfl
    have hb := S.band ⟨le_rfl, hT0⟩
    have hp0 : 0 < ψ 0 := lt_of_lt_of_le (by norm_num [psiLo]) hb.1.1
    exact (Bred_strictAnti hp0 (hb.1.2.trans (by norm_num [psiEdge]))).injOn
      ⟨(S.cos_mem hz₂I).1, (S.cos_mem hz₂I).2⟩ ⟨(S.cos_mem ⟨le_rfl, hT0⟩).1,
        (S.cos_mem ⟨le_rfl, hT0⟩).2⟩ (h1.trans h2.symm)
  have hθz₂' : θ z₂ = θ 0 :=
    injOn_cos ⟨by linarith, by linarith [(S.theta hz₂I).2, pi_pos]⟩
      ⟨hθ0pos.le, by linarith [S.theta0.2, pi_pos]⟩ hc
  exact ⟨z₁, z₂, hz₁.1, hz₂.1, by linarith [hz₂.2], hρz₁, hρz₂, hneg, hpos', hθ0, hθz₁,
    hθz₂, hψz₂, hθz₂'⟩

end Setup

/-! ## Certified precession per bounce -/

/-- **Certified precession per bounce, given the precession bounds on the window.** For an orbit
in the setting `Setup` with `T ≥ 2 · 8 × 10⁻⁴ s`, the bounce closes at a time `P ≤ 1.6 ms` (after
a lower turning point at `P₁`), the reduced state returns, and `φ(P) − φ(0) ∈ [0.7, 2.6]`. -/
theorem exactQA_bounce_precession_of_cert
    (hcert : ∀ ψ₀ Bt : ℝ, ψ₀ ∈ Icc (19 / 4 : ℝ) (47 / 8) → Bt ∈ Icc (27 / 5 : ℝ) (11 / 2) →
      PrecessionBounds ψ₀ Bt)
    {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ} (S : Setup μ T ψ θ φ ρ) (hT : 2 * Lhalf ≤ T) :
    ∃ P₁ P : ℝ, 0 < P₁ ∧ P₁ < P ∧ P ≤ 2 * Lhalf ∧ ρ P₁ = 0 ∧ ρ P = 0 ∧
      (∀ t ∈ Ioo 0 P₁, ρ t < 0) ∧ (∀ t ∈ Ioo P₁ P, 0 < ρ t) ∧
      ψ P = ψ 0 ∧ θ P = θ 0 ∧ φ P - φ 0 ∈ Icc (7 / 10 : ℝ) (13 / 5) := by
  have hψ0 : ψ 0 ∈ Icc (19 / 4 : ℝ) (47 / 8) := ⟨by linarith [S.psi0.1], by linarith [S.psi0.2]⟩
  obtain ⟨Mfi, Mfo, Mbi, mbi, Mbo, mbo, ci, co, hup, hlow⟩ :=
    hcert _ _ hψ0 S.Bt_mem
  obtain ⟨z₁, z₂, hz₁, hz₁₂, hz₂, hρz₁, hρz₂, hneg, hpos, hθ0, hθz₁, hθz₂, hψz₂, hθz₂'⟩ :=
    S.bounce_closes ci hT
  have hz₂T : z₂ ≤ T := hz₂.trans hT
  have Pin := S.inner_leg ci le_rfl hz₁ (hz₁₂.le.trans hz₂T) S.rho0 hρz₁ hneg hθ0 hθz₁
  have Pout := S.outer_leg co hz₁.le hz₁₂ hz₂T hρz₁ hρz₂ hpos hθz₁ hθz₂
  have hΩc := S.cont_Om.mono (Icc_subset_Icc le_rfl hz₂T)
  have hint : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ z₂ →
      IntervalIntegrable (Setup.Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ))
        MeasureTheory.volume u v := by
    intro u v hu huv hv
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le huv]; exact hΩc.mono (Icc_subset_Icc hu hv)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hint 0 z₁ le_rfl hz₁.le hz₁₂.le) (hint z₁ z₂ hz₁.le hz₁₂.le le_rfl)
  have hprec := precession_step (ι₀ := 211 / 500) (fun _ => rfl) S.orbit le_rfl
    (hz₁.le.trans hz₁₂.le) hz₂T (S.cont_Bψ.mono (Icc_subset_Icc le_rfl hz₂T))
  have hOm : ∫ t in (0 : ℝ)..z₂, Setup.Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
      -∫ t in (0 : ℝ)..z₂, poloidalDrift exactQA mα qα μ ψ θ φ ρ t := by
    unfold Setup.Om; rw [intervalIntegral.integral_neg]
  rw [hθz₂', sub_self, zero_sub, ← hOm, ← hsplit] at hprec
  refine ⟨z₁, z₂, hz₁, hz₁₂, hz₂, hρz₁, hρz₂, hneg, hpos, hψz₂, hθz₂', ?_, ?_⟩
  · nlinarith [Pin.1, Pout.1]
  · nlinarith [Pin.2, Pout.2]

/-- **Certified precession per bounce, given the uniform `9 × 16` box certificate** (reference
form; see `exactQA_bounce_precession_of_cert`). -/
theorem exactQA_bounce_precession_of_boxes
    (hboxes : ∀ j < 9, ∀ l < 16, boxOk (PB j) (TB l) = true)
    {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ} (S : Setup μ T ψ θ φ ρ) (hT : 2 * Lhalf ≤ T) :
    ∃ P₁ P : ℝ, 0 < P₁ ∧ P₁ < P ∧ P ≤ 2 * Lhalf ∧ ρ P₁ = 0 ∧ ρ P = 0 ∧
      (∀ t ∈ Ioo 0 P₁, ρ t < 0) ∧ (∀ t ∈ Ioo P₁ P, 0 < ρ t) ∧
      ψ P = ψ 0 ∧ θ P = θ 0 ∧ φ P - φ 0 ∈ Icc (7 / 10 : ℝ) (13 / 5) :=
  exactQA_bounce_precession_of_cert (fun _ _ h1 h2 => precession_cert_of_boxes hboxes h1 h2) S hT

/-- **Uniform non-resonance, given the box certificate**: `|sin Δφ_b| ≥ 1/2`. -/
theorem abs_sin_ge_half_of_mem {x : ℝ} (hx : x ∈ Icc (7 / 10 : ℝ) (13 / 5)) :
    1 / 2 ≤ |sin x| := by
  apply abs_sin_ge_half
  have h1 := pi_gt_d2; have h2 := pi_lt_d2
  constructor <;> linarith [hx.1, hx.2]

/-! ## The unconditional statements -/

/-- **The adaptive cover of the start window**: `[4.75, 5.875] × [5.4, 5.5]` (index box
`[0, 128] × [0, 128]`) is covered by 24 boxes that pass the kernel check (plan found by an untrusted
search; leaf checks `boxLeaf_…` in `NearAxisQATrappedCellsRows1`–`3`). -/
theorem window_cover : BoxCover 0 128 0 128 := by
  box_cover "XXYYXYXLLLYLLYXLLLXYLLYLLYYYLLLYLLYXYLLYLLYLXLL"

/-- **The precession certificate on the start window**: every `ψ₀ ∈ [4.75, 5.875]`,
`B_t ∈ [5.4, 5.5]` carries leg bounds for both legs with
`2 (1/40) Σ M_f + (6/5)(M_b^in + M_b^out) ≤ ι₀ · 13/5` and `ι₀ · 7/10 ≤ (6/5)(m_b^in + m_b^out)`. -/
theorem precession_cert {ψ₀ Bt : ℝ} (hψ : ψ₀ ∈ Icc (19 / 4 : ℝ) (47 / 8))
    (hB : Bt ∈ Icc (27 / 5 : ℝ) (11 / 2)) : PrecessionBounds ψ₀ Bt :=
  precession_cert_of_cover window_cover hψ hB

/-- **Certified precession per bounce (trapped 3.5 MeV alphas, exact QA, start window).** For an
orbit in the setting `Setup` (tip field `E/μ ∈ [5.4, 5.5] T`, start at an upper turning point with
`ψ(0) ∈ [4.75, 5.79] T m²`) on `[0, T]` with `T ≥ 1.6 ms`: there are times
`0 < P₁ < P ≤ 1.6 ms` with `ρ(P₁) = ρ(P) = 0`, `ρ < 0` on `(0, P₁)`, `ρ > 0` on `(P₁, P)`, the
reduced state returns (`ψ(P) = ψ(0)`, `θ(P) = θ(0)`, `ρ(P) = ρ(0) = 0`), and the toroidal
precession per bounce satisfies `0.7 ≤ φ(P) − φ(0) ≤ 2.6` (RK4: `1.88–2.31`). -/
theorem exactQA_bounce_precession {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ} (S : Setup μ T ψ θ φ ρ)
    (hT : 2 * Lhalf ≤ T) :
    ∃ P₁ P : ℝ, 0 < P₁ ∧ P₁ < P ∧ P ≤ 2 * Lhalf ∧ ρ P₁ = 0 ∧ ρ P = 0 ∧
      (∀ t ∈ Ioo 0 P₁, ρ t < 0) ∧ (∀ t ∈ Ioo P₁ P, 0 < ρ t) ∧
      ψ P = ψ 0 ∧ θ P = θ 0 ∧ φ P - φ 0 ∈ Icc (7 / 10 : ℝ) (13 / 5) :=
  exactQA_bounce_precession_of_cert (fun _ _ => precession_cert) S hT

/-- **Uniform non-resonance on the exact-QA start window**: the bounce of every such orbit has
`|sin Δφ_b| ≥ 1/2`, where `Δφ_b = φ(P) − φ(0)` is the toroidal precession per bounce. -/
theorem exactQA_nonresonant {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ} (S : Setup μ T ψ θ φ ρ)
    (hT : 2 * Lhalf ≤ T) :
    ∃ P : ℝ, 0 < P ∧ P ≤ 2 * Lhalf ∧ ψ P = ψ 0 ∧ θ P = θ 0 ∧ ρ P = ρ 0 ∧
      1 / 2 ≤ |sin (φ P - φ 0)| := by
  obtain ⟨P₁, P, hP₁, hP₁P, hP, -, hρP, -, -, hψ, hθ, hφ⟩ := exactQA_bounce_precession S hT
  exact ⟨P, hP₁.trans hP₁P, hP, hψ, hθ, by rw [hρP, S.rho0], abs_sin_ge_half_of_mem hφ⟩

/-! ## Sanity checks -/

/-- Sanity (special case): at the outboard midplane `θ = 0` the reduced field is `Bred x 1`. -/
theorem exactQA_B_midplane (x φ : ℝ) : exactQA.B x 0 φ = Bred x 1 := by
  rw [exactQA_B_eq, cos_zero]

/-- Sanity (degenerate case): the flux-momentum ratio inverts `G/ι₀ = 29050/211`. -/
theorem kinv_mul : kinv * (29050 / 211) = 1 := by norm_num [kinv]

/-- Sanity (rejected fixture): the resonant value `Δφ_b = π` (observed numerically for tips near
`r₀ ≈ 0.95 m`, outside the window) is excluded by the certified interval `[0.7, 2.6]`. -/
theorem resonance_excluded : π ∉ Icc (7 / 10 : ℝ) (13 / 5) := by
  intro h; linarith [h.2, pi_gt_d2]

end PlasmaLean.Design.NearAxisQATrappedResonance
