/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrapped
public import PlasmaLean.Theory.Kinetic.BounceOrbits

/-!
# Turning points of trapped 3.5 MeV alphas in the reactor-scale near-axis QA model

Companion to `notes/theory/near-qa-trapped-particles.md` (target T4, step 1). Model only: the
truncated near-axis field `reactorQA` (`Design/NearAxisQA`) in the vacuum Boozer guiding-centre
model; orbits are supplied.

**Pitch window.** Alpha of energy `E = 3.5 MeV` with magnetic moment `μ` such that the field at
the turning points `E/μ` lies in `[5.40, 5.50] T`, i.e. `μ ∈ [E/5.5, E/5.4]`. Equivalently
`λ = μB₀/E ∈ [1.036, 1.056]`: moderately trapped bananas with tips at `|θ| ≈ 40°–80°`
(simulated), safely away from the trapped–passing boundary (O1: a passing orbit would need
`E/μ > max B ≈ 6.1 T`) and with turning points inside `|θ| < π/2`, where `∂_ψB < 0` in the
model so the precession rate has a definite sign (O2; the sign is not used or proved here).

**Flux band.** `ψ ∈ [ψ_lo, ψ_a]` (`r ∈ [0.9, 1.7] m`).

Results:

* `qaField b₁`: the model family with symmetry-breaking coefficient `b₁` (`reactorQA` is
  `qaField (−4.3 × 10⁻⁴)`, `exactQA = qaField 0` is exactly quasi-axisymmetric).
* `qaField_window`: for every `|b₁| ≤ 4.3 × 10⁻⁴` and `μ` in the pitch window, the
  `Kinetic.Boozer.BounceWindow` inequalities hold on the band with `δ = 0.2`, `θ₊ = π/2`,
  `κ = 0.018 T`, `c₂ = 5000 s⁻¹`, `B_lo = 4.93 T`, `ρ_max = 1.77 cm`.
* `halfBounce_le`: every half bounce lasts at most `8 × 10⁻⁴ s` (crude; the simulated half
  bounce is `≈ 3.3 × 10⁻⁵ s`).
* `qaField_turning_points`, `reactorQA_turning_points`: **turning points exist** for every
  model orbit in the window that stays in the band and starts at an upper turning point: a
  monotone sequence `τ 0 = 0 < τ 1 < … < τ N` of turning points on alternating flanks, with
  `τ (k+1) − τ k ≤ 8 × 10⁻⁴ s`, for every `N` with `N · 8 × 10⁻⁴ ≤ T`.
* `exactQA_band`: for the exactly symmetric field, the band is **proved** (momentum
  conservation plus energy) for starts `ψ(0) ∈ [4.75, 5.79] T m²` (`r₀ ∈ [1.29, 1.43] m`);
  `exactQA_turning_points`: turning points with no band hypothesis, and **tip rigidity**:
  `ψ(τ k) = ψ(0)` for all `k` and `θ(τ (2j)) = θ(0)` — the reduced state returns exactly at every
  upper turning point.
* `reactorQA_trapped_drift`: step 3 combination — for `reactorQA` in the window (band assumed),
  the turning-point hypotheses of `reactorQA_bounce_drift_nonresonant` are discharged; the kick
  form and non-resonance remain hypotheses.

**What remains (precise).**
1. *Periodicity of the exact-QA reference bounce.* Tip rigidity is proved; the missing step is
   uniqueness of solutions of the reduced `(ψ, θ, ρ)` ODE (a local Lipschitz bound for the
   `qaField 0` vector field on the band), which with `periodic_kick_form` gives the kick form
   with `R = 0` for the reference orbit and `α = 2Δφ_b`.
2. *Non-resonance.* `|sin Δφ_b| ≥ c` needs an enclosure of the precession per bounce
   `Δφ_b = (1/ι₀) ∫_bounce (−(μ/q + qρ²B/m) ∂_ψB) dt` (`precession_step`, using `θ` returning
   at the next upper tip). Simulated (RK4, exact QA): for the exact-QA start window
   `r₀ ∈ [1.29, 1.43] m`, `Δφ_b ≈ 1.87–2.32` (`|sin Δφ_b| ≥ 0.73`), so an enclosure with an
   upper bound below `π` (about `35 %` margin) would suffice; but for tips near `r₀ ≈ 0.95 m`
   (inside the near-QA band) `Δφ_b ≈ π`, a genuine resonance. The bounce-time bounds proved
   here (`8 × 10⁻⁴ s` vs simulated `≈ 3.3 × 10⁻⁵ s` per half bounce) are far too weak; a
   validated bounce-time quadrature is required.
3. *Remainder `R`.* A Grönwall comparison of the near-QA orbit with the exact-QA reference over
   one bounce, and control of the bounce-to-bounce change of `Δφ_b` (phase shear; the
   GWB/Chirikov parameter), are not attempted.

No trapped-alpha confinement time is claimed; compare passing alphas `0.19 s`
(`NearAxisQAAveraged`) and the slowing-down time `≈ 0.4 s`.
-/
public section
noncomputable section
namespace PlasmaLean.Design.NearAxisQATrappedBounce
open PlasmaLean.Kinetic.Boozer PlasmaLean.Design.NearAxisQA Real Set

/-! ## The model family and the window constants -/

/-- The reactor-scale near-axis model with symmetry-breaking coefficient `b₁` (all other
coefficients as in `reactorQA`). -/
@[expose] def qaField (b₁ : ℝ) : BoozerField :=
  field (57 / 10) (-7 / 100) (-137 / 10000) b₁ (33 / 2000) (211 / 500) (581 / 10) (by norm_num)

/-- `reactorQA` is the member `b₁ = −4.3 × 10⁻⁴` of the family. -/
theorem reactorQA_eq : reactorQA = qaField (-43 / 100000) := rfl

/-- The exactly quasi-axisymmetric member `b₁ = 0`. -/
@[expose] def exactQA : BoozerField := qaField 0

/-- Inner edge of the flux band, `ψ_lo = B₀ (0.9)²/2 = 2.3085 T m²`. -/
@[expose] def psiLo : ℝ := 57 / 10 * (9 / 10) ^ 2 / 2

/-- Lower end of the magnetic-moment window, `μ_lo = E/5.5` (tip field `5.5 T`). -/
@[expose] def muLo : ℝ := Eα / (11 / 2)

/-- Upper end of the magnetic-moment window, `μ_hi = E/5.4` (tip field `5.4 T`). -/
@[expose] def muHi : ℝ := Eα / (27 / 5)

/-- Gyroradius bound `ρ_max = 1.77 cm`. -/
@[expose] def rhoMax : ℝ := 177 / 10000

/-- Uniform bound on a half bounce, `8 × 10⁻⁴ s`. -/
@[expose] def Lhalf : ℝ := 8 / 10000

/-- `μ_lo > 0`. -/
theorem muLo_pos : 0 < muLo := by norm_num [muLo, Eα]

/-- On the band, `0.9 ≤ r ≤ 1.7` and `r² = 2ψ/B₀`. -/
theorem radius_band {x : ℝ} (hx : x ∈ Icc psiLo psiEdge) :
    9 / 10 ≤ radius (57 / 10) x ∧ radius (57 / 10) x ≤ 17 / 10 ∧
      radius (57 / 10) x ^ 2 = 2 * x / (57 / 10) := by
  have hx0 : 0 ≤ x := le_trans (by norm_num [psiLo]) hx.1
  refine ⟨?_, radius_le_edge hx.2, radius_sq (by norm_num) hx0⟩
  rw [radius, show (9 / 10 : ℝ) = √((9 / 10) ^ 2) by rw [sqrt_sq (by norm_num)]]
  apply sqrt_le_sqrt
  have := hx.1
  unfold psiLo at this
  linarith

/-! ## Field values -/

section Values
variable (b₁ x θ φ : ℝ)

/-- `B` of the family. -/
theorem qaField_B : (qaField b₁).B x θ φ = 57 / 10 + -(399 / 1000) * radius (57 / 10) x * cos θ +
    2 * x / (57 / 10) * (-137 / 10000 + b₁ * cos (2 * φ) + 33 / 2000 * cos (2 * θ)) := by
  simp only [qaField, field, nearAxisB]; ring

/-- `∂_θB` of the family. -/
theorem qaField_Bθ : (qaField b₁).Bθ x θ φ =
    399 / 1000 * radius (57 / 10) x * sin θ - 2 * x / (57 / 10) * (33 / 1000 * sin (2 * θ)) := by
  simp only [qaField, field, nearAxisBθ]; ring

/-- `∂_φB` of the family. -/
theorem qaField_Bφ : (qaField b₁).Bφ x θ φ = -(2 * x / (57 / 10) * (2 * b₁ * sin (2 * φ))) := by
  simp only [qaField, field, nearAxisBφ]

/-- `∂_ψB` of the family. -/
theorem qaField_Bψ : (qaField b₁).Bψ x θ φ = -7 / 100 * cos θ / radius (57 / 10) x +
    2 / (57 / 10) * (-137 / 10000 + b₁ * cos (2 * φ) + 33 / 2000 * cos (2 * θ)) := by
  simp only [qaField, field, nearAxisBψ]

/-- `G` of the family. -/
theorem qaField_G : (qaField b₁).G = 581 / 10 := rfl

/-- `ι` of the family. -/
theorem qaField_ι : (qaField b₁).ι x = 211 / 500 := rfl

end Values

/-- Bounds on the `r²` coefficient `K = b₀ + b₁ cos 2φ + B₂c cos 2θ` for `|b₁| ≤ 4.3 × 10⁻⁴`. -/
theorem coefK_bounds {b₁ : ℝ} (hb : |b₁| ≤ 43 / 100000) (θ φ : ℝ) :
    -(30630 / 1000000) ≤ -137 / 10000 + b₁ * cos (2 * φ) + 33 / 2000 * cos (2 * θ) ∧
      -137 / 10000 + b₁ * cos (2 * φ) + 33 / 2000 * cos (2 * θ) ≤ 3230 / 1000000 := by
  have h1 := abs_le.mp ((abs_mul_sin_cos_le b₁ (2 * φ)).2.trans hb)
  have h2 := neg_one_le_cos (2 * θ)
  have h3 := cos_le_one (2 * θ)
  constructor <;> nlinarith

/-- `|∂_φB| ≤ 2|b₁| r² ≤ 0.0024854` on the band. -/
theorem abs_Bφ_le {b₁ x : ℝ} (hb : |b₁| ≤ 43 / 100000) (hx : x ∈ Icc psiLo psiEdge) (θ φ : ℝ) :
    |(qaField b₁).Bφ x θ φ| ≤ 24854 / 10000000 := by
  obtain ⟨_, hr2, hrr⟩ := radius_band hx
  rw [qaField_Bφ, ← hrr, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg _), abs_mul, abs_mul,
    abs_two]
  have h1 : |sin (2 * φ)| ≤ 1 := abs_sin_le_one _
  have hr0 : 0 ≤ radius (57 / 10) x := by linarith [radius_band hx]
  have : radius (57 / 10) x ^ 2 ≤ (17 / 10) ^ 2 := pow_le_pow_left₀ hr0 hr2 2
  have hb0 := abs_nonneg b₁
  have : |b₁| * |sin (2 * φ)| ≤ 43 / 100000 := by nlinarith [abs_nonneg (sin (2 * φ))]
  nlinarith [mul_nonneg hb0 (abs_nonneg (sin (2 * φ)))]

/-- `B ≥ 4.93 T` for `0 ≤ ψ ≤ ψ_a` (`r ≤ 1.7 m`), all angles. -/
theorem qaField_B_ge {b₁ x : ℝ} (hb : |b₁| ≤ 43 / 100000) (hx0 : 0 ≤ x) (hx : x ≤ psiEdge)
    (θ φ : ℝ) : 493 / 100 ≤ (qaField b₁).B x θ φ := by
  have hr2 := radius_le_edge hx
  have hrr := radius_sq (by norm_num : (0 : ℝ) < 57 / 10) hx0
  have hr0 : 0 ≤ radius (57 / 10) x := sqrt_nonneg _
  rw [qaField_B, ← hrr]
  obtain ⟨hK1, -⟩ := coefK_bounds hb θ φ
  have hc : radius (57 / 10) x * cos θ ≤ 17 / 10 := by
    nlinarith [mul_le_mul_of_nonneg_left (cos_le_one θ) hr0]
  have hsq : radius (57 / 10) x ^ 2 ≤ (17 / 10) ^ 2 := pow_le_pow_left₀ hr0 hr2 2
  nlinarith [mul_le_mul_of_nonneg_left hK1 (sq_nonneg (radius (57 / 10) x))]

/-- `sin (1/5) ≥ 0.1986`. -/
theorem sin_fifth_ge : 1986 / 10000 ≤ sin (1 / 5) := by
  have := sin_gt_sub_cube (x := 1 / 5) (by norm_num)
  norm_num at this ⊢; linarith

/-- On `θ ∈ [1/5, π/2]`: `sin θ ≥ 0.1986`, `0 ≤ cos θ ≤ 1`. -/
theorem flank_trig {θ : ℝ} (hθ : θ ∈ Icc (1 / 5) (π / 2)) :
    1986 / 10000 ≤ sin θ ∧ 0 ≤ cos θ := by
  have hπ := pi_gt_three
  refine ⟨sin_fifth_ge.trans (sin_le_sin_of_le_of_le_pi_div_two (by linarith) hθ.2 hθ.1),
    cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], hθ.2⟩⟩

/-- Mirror force on the upper flank: `∂_φB + ι₀ ∂_θB ≥ 0.018` for `θ ∈ [1/5, π/2]`. -/
theorem flank_pos_bound {b₁ x θ φ : ℝ} (hb : |b₁| ≤ 43 / 100000) (hx : x ∈ Icc psiLo psiEdge)
    (hθ : θ ∈ Icc (1 / 5) (π / 2)) :
    9 / 500 ≤ (qaField b₁).Bφ x θ φ + 211 / 500 * (qaField b₁).Bθ x θ φ := by
  obtain ⟨hr1, hr2, hrr⟩ := radius_band hx
  obtain ⟨hs, hc0⟩ := flank_trig hθ
  have hφ := (abs_le.mp (abs_Bφ_le hb hx θ φ)).1
  set r := radius (57 / 10) x
  have e : (qaField b₁).Bθ x θ φ = r * sin θ * (399 / 1000 - 66 / 1000 * (r * cos θ)) := by
    rw [qaField_Bθ, ← hrr, sin_two_mul]; ring
  rw [e]
  have hc1 := cos_le_one θ
  have hrc : r * cos θ ≤ 17 / 10 := by nlinarith
  have hrs : 9 / 10 * (1986 / 10000) ≤ r * sin θ := by nlinarith
  have hf : 2868 / 10000 ≤ 399 / 1000 - 66 / 1000 * (r * cos θ) := by linarith
  have := mul_le_mul hrs hf (by norm_num) (by nlinarith)
  nlinarith

/-- Mirror force on the lower flank: `∂_φB + ι₀ ∂_θB ≤ −0.018` for `θ ∈ [−π/2, −1/5]`. -/
theorem flank_neg_bound {b₁ x θ φ : ℝ} (hb : |b₁| ≤ 43 / 100000) (hx : x ∈ Icc psiLo psiEdge)
    (hθ : θ ∈ Icc (-(π / 2)) (-(1 / 5))) :
    (qaField b₁).Bφ x θ φ + 211 / 500 * (qaField b₁).Bθ x θ φ ≤ -(9 / 500) := by
  obtain ⟨hr1, hr2, hrr⟩ := radius_band hx
  obtain ⟨hs, hc0⟩ := flank_trig (θ := -θ) ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  rw [sin_neg, cos_neg] at *
  have hφ := (abs_le.mp (abs_Bφ_le hb hx θ φ)).2
  set r := radius (57 / 10) x
  have e : (qaField b₁).Bθ x θ φ = -(r * (-sin θ) * (399 / 1000 - 66 / 1000 * (r * cos θ))) := by
    rw [qaField_Bθ, ← hrr, sin_two_mul]; ring
  rw [e]
  have hc1 := cos_le_one θ
  have hrc : r * cos θ ≤ 17 / 10 := by nlinarith
  have hrs : 9 / 10 * (1986 / 10000) ≤ r * (-sin θ) := by nlinarith
  have hf : 2868 / 10000 ≤ 399 / 1000 - 66 / 1000 * (r * cos θ) := by linarith
  have := mul_le_mul hrs hf (by norm_num) (by nlinarith)
  nlinarith

/-- At the bottom of the well (`|θ| ≤ 1/5`) on the band: `B ≤ 5.358 T`. -/
theorem bottom_B_le {b₁ x θ φ : ℝ} (hb : |b₁| ≤ 43 / 100000) (hx : x ∈ Icc psiLo psiEdge)
    (hθ : θ ∈ Icc (-(1 / 5)) (1 / 5)) : (qaField b₁).B x θ φ ≤ 5358 / 1000 := by
  obtain ⟨hr1, hr2, hrr⟩ := radius_band hx
  obtain ⟨-, hK2⟩ := coefK_bounds hb θ φ
  have hc : 98 / 100 ≤ cos θ := by
    have := one_sub_sq_div_two_le_cos (x := θ)
    nlinarith [hθ.1, hθ.2]
  rw [qaField_B, ← hrr]
  set r := radius (57 / 10) x
  have hr0 : 0 ≤ r := by linarith
  have hrc : 9 / 10 * (98 / 100) ≤ r * cos θ := by nlinarith
  have hsq : r ^ 2 ≤ (17 / 10) ^ 2 := pow_le_pow_left₀ hr0 hr2 2
  nlinarith [mul_le_mul_of_nonneg_left hK2 (sq_nonneg r)]

/-- At the bottom of the well on the band: `|∂_ψB| ≤ 0.0886 T/(T m²)`. -/
theorem bottom_Bψ_le {b₁ x θ φ : ℝ} (hb : |b₁| ≤ 43 / 100000) (hx : x ∈ Icc psiLo psiEdge) :
    |(qaField b₁).Bψ x θ φ| ≤ 886 / 10000 := by
  obtain ⟨hr1, hr2, hrr⟩ := radius_band hx
  obtain ⟨hK1, hK2⟩ := coefK_bounds hb θ φ
  rw [qaField_Bψ]
  set r := radius (57 / 10) x
  have hr0 : 0 < r := by linarith
  have h1 : |-7 / 100 * cos θ / r| ≤ 7 / 100 / (9 / 10) := by
    rw [abs_div, abs_of_pos hr0, abs_mul]
    have := abs_cos_le_one θ
    apply div_le_div₀ (by norm_num) (by norm_num at this ⊢; linarith) (by norm_num) hr1
  have h2 : |2 / (57 / 10) * (-137 / 10000 + b₁ * cos (2 * φ) + 33 / 2000 * cos (2 * θ))| ≤
      2 / (57 / 10) * (30630 / 1000000) := by
    rw [abs_mul, abs_of_pos (by norm_num)]
    gcongr
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ 7 / 100 / (9 / 10) + 2 / (57 / 10) * (30630 / 1000000) := add_le_add h1 h2
    _ ≤ 886 / 10000 := by norm_num

/-- **The bounce window holds for the whole family** `|b₁| ≤ 4.3 × 10⁻⁴` and every magnetic
moment in the pitch window `μ ∈ [E/5.5, E/5.4]`, on the band `ψ ∈ [ψ_lo, ψ_a]`, with `δ = 1/5`,
`θ₊ = π/2`, `κ = 0.018`, `c₂ = 5000`, `B_lo = 4.93`, `ρ_max = 0.0177`. -/
theorem qaField_window {b₁ μ : ℝ} (hb : |b₁| ≤ 43 / 100000) (hμ : μ ∈ Icc muLo muHi) :
    BounceWindow (qaField b₁) mα qα μ Eα (211 / 500) psiLo psiEdge (1 / 5) (π / 2) (9 / 500)
      5000 (493 / 100) rhoMax := by
  have hμ0 : 0 < μ := muLo_pos.trans_le hμ.1
  have hμlo : Eα ≤ 11 / 2 * μ := by
    have := hμ.1; unfold muLo at this; rw [div_le_iff₀ (by norm_num)] at this; linarith
  have hμhi : 27 / 5 * μ ≤ Eα := by
    have := hμ.2; unfold muHi at this; rw [le_div_iff₀ (by norm_num)] at this; linarith
  have hE0 : 0 < Eα := by norm_num [Eα]
  have hband0 : ∀ x ∈ Icc psiLo psiEdge, 0 ≤ x := fun x hx => le_trans (by norm_num [psiLo]) hx.1
  -- forbidden tips `θ = ±π/2`
  have forbid : ∀ x ∈ Icc psiLo psiEdge, ∀ φ, ∀ θ, cos θ = 0 → cos (2 * θ) = -1 →
      Eα < μ * (qaField b₁).B x θ φ := by
    intro x hx φ θ hc hc2
    obtain ⟨hr1, hr2, hrr⟩ := radius_band hx
    obtain ⟨hK1, -⟩ := coefK_bounds hb θ φ
    have hB : 56 / 10 ≤ (qaField b₁).B x θ φ := by
      rw [qaField_B, ← hrr, hc, hc2] at *
      have hr0 : 0 ≤ radius (57 / 10) x := by linarith
      have hsq : radius (57 / 10) x ^ 2 ≤ (17 / 10) ^ 2 := pow_le_pow_left₀ hr0 hr2 2
      rw [hc2] at hK1
      nlinarith [mul_le_mul_of_nonneg_left hK1 (sq_nonneg (radius (57 / 10) x))]
    nlinarith
  refine ⟨by norm_num, fun x hx θ _ φ => qaField_B_ge hb (hband0 x hx) hx.2 θ φ, ?_, ?_,
    fun x hx θ hθ φ => flank_pos_bound hb hx hθ, fun x hx θ hθ φ => flank_neg_bound hb hx hθ,
    ?_, ?_, ?_⟩
  · intro x hx φ
    exact forbid x hx φ _ cos_pi_div_two (by rw [mul_div_cancel₀ _ two_ne_zero, cos_pi])
  · intro x hx φ
    exact forbid x hx φ _ (by rw [cos_neg, cos_pi_div_two])
      (by rw [show 2 * -(π / 2) = -π by ring, cos_neg, cos_pi])
  · intro x hx θ hθ φ
    have := bottom_B_le (φ := φ) hb hx hθ
    nlinarith
  · intro x hx θ hθ φ
    set B := (qaField b₁).B x θ φ
    have hBlo : 493 / 100 ≤ B := qaField_B_ge hb (hband0 x hx) hx.2 θ φ
    have hBhi : B ≤ 5358 / 1000 := bottom_B_le hb hx hθ
    have hψ : |(qaField b₁).Bψ x θ φ| ≤ 886 / 10000 := bottom_Bψ_le hb hx
    have hB0 : 0 < B := by linarith
    rw [qaField_G]
    -- left side
    have hA : 2 * Eα / B - μ ≤ 2 * Eα / (493 / 100) - Eα / (11 / 2) := by
      have : 2 * Eα / B ≤ 2 * Eα / (493 / 100) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hBlo
      have : Eα / (11 / 2) ≤ μ := by rw [div_le_iff₀ (by norm_num)]; linarith
      linarith
    have hA0 : 0 ≤ 2 * Eα / B - μ := by
      have : μ * B ≤ μ * (5358 / 1000) := mul_le_mul_of_nonneg_left hBhi hμ0.le
      have : μ ≤ 2 * Eα / B := by rw [le_div_iff₀ hB0]; nlinarith
      linarith
    have hq0 : (0 : ℝ) < qα := by norm_num [qα]
    have hL : (2 * Eα / B - μ) * |(qaField b₁).Bψ x θ φ| / qα + 5000 ≤
        (2 * Eα / (493 / 100) - Eα / (11 / 2)) * (886 / 10000) / qα + 5000 := by
      have : 0 ≤ 2 * Eα / (493 / 100) - Eα / (11 / 2) := by norm_num [Eα]
      gcongr
    have hL0 : 0 ≤ (2 * Eα / B - μ) * |(qaField b₁).Bψ x θ φ| / qα + 5000 := by positivity
    -- right side
    have hR1 : (493 / 100 * (211 / 500) / (581 / 10)) ^ 2 ≤ (B * (211 / 500) / (581 / 10)) ^ 2 := by
      gcongr
    have hR2 : 2 * (Eα - Eα / (27 / 5) * (5358 / 1000)) / mα ≤ 2 * (Eα - μ * B) / mα := by
      have : μ ≤ Eα / (27 / 5) := by rw [le_div_iff₀ (by norm_num)]; linarith
      have : μ * B ≤ Eα / (27 / 5) * (5358 / 1000) :=
        mul_le_mul this hBhi hB0.le (by positivity)
      have hm : (0 : ℝ) < mα := by norm_num [mα]
      gcongr
    have hnum : ((2 * Eα / (493 / 100) - Eα / (11 / 2)) * (886 / 10000) / qα + 5000) ^ 2 ≤
        (493 / 100 * (211 / 500) / (581 / 10)) ^ 2 *
          (2 * (Eα - Eα / (27 / 5) * (5358 / 1000)) / mα) := by
      norm_num [Eα, qα, mα]
    have hR2' : 0 ≤ 2 * (Eα - Eα / (27 / 5) * (5358 / 1000)) / mα := by norm_num [Eα, mα]
    calc _ ≤ ((2 * Eα / (493 / 100) - Eα / (11 / 2)) * (886 / 10000) / qα + 5000) ^ 2 :=
          pow_le_pow_left₀ hL0 hL 2
      _ ≤ _ := hnum
      _ ≤ _ := mul_le_mul hR1 hR2 hR2' (sq_nonneg _)
  · have hnum : 2 * mα * (Eα - Eα / (11 / 2) * (493 / 100)) / (qα ^ 2 * (493 / 100) ^ 2) ≤
        rhoMax ^ 2 := by norm_num [Eα, qα, mα, rhoMax]
    refine le_trans ?_ hnum
    have : Eα / (11 / 2) ≤ μ := by rw [div_le_iff₀ (by norm_num)]; linarith
    have hm : (0 : ℝ) < mα := by norm_num [mα]
    gcongr

/-- The window for `reactorQA` itself (accepted fixture). -/
theorem reactorQA_window {μ : ℝ} (hμ : μ ∈ Icc muLo muHi) :
    BounceWindow reactorQA mα qα μ Eα (211 / 500) psiLo psiEdge (1 / 5) (π / 2) (9 / 500)
      5000 (493 / 100) rhoMax :=
  qaField_window (by norm_num [abs_of_neg]) hμ

/-- **Uniform half-bounce bound**: for `μ ≥ μ_lo`,
`halfBounceTime ρ_max (μκ/(Gq)) c₂ δ ≤ 8 × 10⁻⁴ s`. -/
theorem halfBounce_le {b₁ μ : ℝ} (hμ : muLo ≤ μ) :
    halfBounceTime rhoMax (μ * (9 / 500) / ((qaField b₁).G * qα)) 5000 (1 / 5) ≤ Lhalf := by
  have hμ0 : 0 < μ := muLo_pos.trans_le hμ
  have hq0 : (0 : ℝ) < qα := by norm_num [qα]
  rw [qaField_G]
  unfold halfBounceTime
  have h1 : 4 * rhoMax / (μ * (9 / 500) / (581 / 10 * qα)) ≤
      4 * rhoMax / (muLo * (9 / 500) / (581 / 10 * qα)) := by
    apply div_le_div_of_nonneg_left (by norm_num [rhoMax])
      (by have := muLo_pos; positivity)
    gcongr
  have h2 : 4 * rhoMax / (muLo * (9 / 500) / (581 / 10 * qα)) + 2 * (1 / 5) / 5000 ≤ Lhalf := by
    norm_num [rhoMax, muLo, Eα, qα, Lhalf]
  linarith

/-! ## Turning points -/

/-- **Turning points of trapped alphas in the model family** (`|b₁| ≤ 4.3 × 10⁻⁴`, near-QA
included). A 3.5 MeV alpha guiding-centre orbit on `[0, T]` with `μ ∈ [E/5.5, E/5.4]`, staying in
the band `ψ ∈ [ψ_lo, ψ_a]`, and starting at a turning point `ρ(0) = 0` with `θ(0) ∈ (0, π/2)` has,
for every `N` with `N · 8 × 10⁻⁴ s ≤ T`, a monotone sequence of turning points
`τ 0 = 0 < τ 1 < … < τ N` (`v_∥ = 0`, `B > 0`) on alternating flanks
(`(−1)^k θ(τ k) > 0`), with `τ (k+1) − τ k ≤ 8 × 10⁻⁴ s` and `τ k ≤ k · 8 × 10⁻⁴ s`. -/
theorem qaField_turning_points {b₁ μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ} (hb : |b₁| ≤ 43 / 100000)
    (hμ : μ ∈ Icc muLo muHi) (h : BoozerGCOrbitOn (qaField b₁) mα qα μ ψ θ φ ρ T)
    (hE : boozerEnergy (qaField b₁) mα qα μ ψ θ φ ρ 0 = Eα)
    (hband : ∀ t ∈ Icc 0 T, ψ t ∈ Icc psiLo psiEdge) (hρ0 : ρ 0 = 0)
    (hθ0 : θ 0 ∈ Ioo 0 (π / 2)) (N : ℕ) (hN : N * Lhalf ≤ T) :
    ∃ τ : ℕ → ℝ, τ 0 = 0 ∧ Monotone τ ∧
      (∀ k < N, τ k < τ (k + 1) ∧ τ (k + 1) ≤ τ k + Lhalf) ∧
      (∀ k ≤ N, parallelVelocity (qaField b₁) mα qα ψ θ φ ρ (τ k) = 0 ∧
        0 < along (qaField b₁).B ψ θ φ (τ k) ∧ 0 < (-1) ^ k * θ (τ k)) ∧
      (∀ k ≤ N, τ k ≤ k * Lhalf) ∧ (∀ k, N ≤ k → τ k = τ N) := by
  have hμ0 : 0 < μ := muLo_pos.trans_le hμ.1
  have hL := halfBounce_le (b₁ := b₁) hμ.1
  have hLp : 0 < halfBounceTime rhoMax (μ * (9 / 500) / ((qaField b₁).G * qα)) 5000 (1 / 5) :=
    halfBounceTime_pos (by norm_num [rhoMax]) (by rw [qaField_G]; norm_num [qα]; positivity)
      (by norm_num) (by norm_num)
  have hN' : N * halfBounceTime rhoMax (μ * (9 / 500) / ((qaField b₁).G * qα)) 5000 (1 / 5) ≤ T :=
    le_trans (mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg N)) hN
  obtain ⟨τ, h0, hmono, hstep, htp, hle, hconst⟩ := boozer_bounce_sequence (by norm_num [mα])
    (by norm_num [qα]) (by rw [qaField_G]; norm_num) (fun x => qaField_ι b₁ x) (by norm_num)
    hμ0 (by norm_num) (by norm_num) (by norm_num) (by norm_num [rhoMax]) (qaField_window hb hμ)
    h hE hband hρ0 hθ0 N hN'
  refine ⟨τ, h0, hmono, fun k hk => ⟨(hstep k hk).1, (hstep k hk).2.trans (by linarith)⟩, htp,
    fun k hk => (hle k hk).trans (mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg k)), hconst⟩

/-- **Turning points for `reactorQA`** (the near-QA reactor model, band assumed). -/
theorem reactorQA_turning_points {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ}
    (hμ : μ ∈ Icc muLo muHi) (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T)
    (hE : boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα)
    (hband : ∀ t ∈ Icc 0 T, ψ t ∈ Icc psiLo psiEdge) (hρ0 : ρ 0 = 0)
    (hθ0 : θ 0 ∈ Ioo 0 (π / 2)) (N : ℕ) (hN : N * Lhalf ≤ T) :
    ∃ τ : ℕ → ℝ, τ 0 = 0 ∧ Monotone τ ∧
      (∀ k < N, τ k < τ (k + 1) ∧ τ (k + 1) ≤ τ k + Lhalf) ∧
      (∀ k ≤ N, parallelVelocity reactorQA mα qα ψ θ φ ρ (τ k) = 0 ∧
        0 < along reactorQA.B ψ θ φ (τ k) ∧ 0 < (-1) ^ k * θ (τ k)) ∧
      (∀ k ≤ N, τ k ≤ k * Lhalf) ∧ (∀ k, N ≤ k → τ k = τ N) :=
  qaField_turning_points (b₁ := -43 / 100000) (by norm_num [abs_of_neg]) hμ h hE hband hρ0 hθ0 N
    hN

/-- **Step 3 combination for `reactorQA`** (band assumed). For an alpha in the pitch window
starting at an upper turning point and staying in the band on `[0, T]`, and every `N` with
`N · 8 × 10⁻⁴ s ≤ T`, there are turning points `τ 0 = 0 ≤ … ≤ τ N ≤ T` (each half bounce at most
`8 × 10⁻⁴ s`) such that, **if** the per-bounce kicks have the form `A sin(kα + β)` up to `R` and
`sin(α/2) ≠ 0`, then `|ψ(τ N) − ψ(τ 0)| ≤ (|A|/|sin(α/2)| + N R)/(|q| ι₀)`. The turning-point
hypotheses of `reactorQA_bounce_drift_nonresonant` are discharged; the kick form and the
non-resonance are not. -/
theorem reactorQA_trapped_drift {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ}
    (hμ : μ ∈ Icc muLo muHi) (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T)
    (hE : boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα)
    (hband : ∀ t ∈ Icc 0 T, ψ t ∈ Icc psiLo psiEdge) (hρ0 : ρ 0 = 0)
    (hθ0 : θ 0 ∈ Ioo 0 (π / 2)) (N : ℕ) (hN : N * Lhalf ≤ T) :
    ∃ τ : ℕ → ℝ, τ 0 = 0 ∧ Monotone τ ∧ τ N ≤ T ∧
      (∀ k < N, τ k < τ (k + 1) ∧ τ (k + 1) ≤ τ k + Lhalf) ∧
      ∀ A α β R : ℝ, sin (α / 2) ≠ 0 →
        (∀ k < N, |(∫ t in τ k..τ (k + 1), qaKick reactorQA mα qα μ ψ θ φ ρ t) -
          A * sin (k * α + β)| ≤ R) →
        |ψ (τ N) - ψ (τ 0)| ≤ (|A| / |sin (α / 2)| + N * R) / (|qα| * (211 / 500)) := by
  obtain ⟨τ, h0, hmono, hstep, htp, hle, -⟩ :=
    reactorQA_turning_points hμ h hE hband hρ0 hθ0 N hN
  have hNT : τ N ≤ T := (hle N le_rfl).trans hN
  refine ⟨τ, h0, hmono, hNT, hstep, fun A α β R hα hkick => ?_⟩
  exact reactorQA_bounce_drift_nonresonant (by norm_num [mα]) (by norm_num [qα]) h hmono
    (by rw [h0]) hNT (fun k hk => (htp k hk).2.1) (fun k hk => (htp k hk).1) hα hkick

/-! ## Exact QA: the band is proved -/

/-- In exact QA the symmetry-breaking derivative vanishes identically. -/
theorem exactQA_Bφ (x θ φ : ℝ) : exactQA.Bφ x θ φ = 0 := by
  rw [exactQA, qaField_Bφ]; ring

/-- **Exact momentum conservation along an exact-QA orbit** (no band needed):
`ι₀ (ψ(t) − ψ(0)) = G (ρ(t) − ρ(0))` for `t ∈ [0, T]`. -/
theorem exactQA_momentum {μ T t : ℝ} {ψ θ φ ρ : ℝ → ℝ}
    (h : BoozerGCOrbitOn exactQA mα qα μ ψ θ φ ρ T) (ht : t ∈ Icc 0 T) :
    211 / 500 * (ψ t - ψ 0) = 581 / 10 * (ρ t - ρ 0) := by
  have hzero : along exactQA.Bφ ψ θ φ = fun _ => 0 := by
    funext s; simp only [along, exactQA_Bφ]
  have hc : ContinuousOn (along exactQA.Bφ ψ θ φ) (Icc 0 t) := by
    rw [hzero]; exact continuousOn_const
  have hq : qα ≠ 0 := by norm_num [qα]
  have := psip_step (by norm_num [mα]) hq (by rw [exactQA, qaField_G]; norm_num) h le_rfl ht.1
    ht.2 hc
  have hk : ∫ s in (0 : ℝ)..t, qaKick exactQA mα qα μ ψ θ φ ρ s = 0 := by
    simp only [qaKick, hzero, mul_zero, intervalIntegral.integral_zero]
  rw [hk, add_zero] at this
  have e1 : exactQA.ψp (ψ t) - exactQA.ψp (ψ 0) = 211 / 500 * (ψ t - ψ 0) := by
    simp only [exactQA, qaField, field]; ring
  rw [e1, show exactQA.G = 581 / 10 from rfl, mul_assoc] at this
  exact mul_left_cancel₀ hq this

/-- **The flux band for exact QA.** An exact-QA alpha orbit on `[0, T]` in the pitch window,
starting at a turning point (`ρ(0) = 0`) with `ψ(0) ∈ [4.75, 5.79] T m²` (`r₀ ∈ [1.29, 1.43] m`),
stays in `ψ ∈ [ψ_lo, ψ_a]` (in fact `ψ ≤ 8.23`) for all `t ∈ [0, T]`; and `|ρ| ≤ ρ_max` there. -/
theorem exactQA_band {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ} (hμ : μ ∈ Icc muLo muHi)
    (h : BoozerGCOrbitOn exactQA mα qα μ ψ θ φ ρ T)
    (hE : boozerEnergy exactQA mα qα μ ψ θ φ ρ 0 = Eα) (hρ0 : ρ 0 = 0)
    (hψ0 : ψ 0 ∈ Icc (475 / 100) (579 / 100)) :
    ∀ t ∈ Icc 0 T, ψ t ∈ Icc psiLo psiEdge ∧ |ρ t| ≤ rhoMax := by
  have hm : (0 : ℝ) < mα := by norm_num [mα]
  have hq : qα ≠ 0 := by norm_num [qα]
  have hG : exactQA.G ≠ 0 := by rw [exactQA, qaField_G]; norm_num
  have hμ0 : 0 < μ := muLo_pos.trans_le hμ.1
  have hb0 : |(0 : ℝ)| ≤ 43 / 100000 := by norm_num
  have W := qaField_window hb0 hμ
  -- `|ρ| ≤ ρ_max` wherever `0 < ψ ≤ ψ_a`
  have hρ : ∀ t ∈ Icc 0 T, ψ t ≤ psiEdge → |ρ t| ≤ rhoMax := fun t ht hψt =>
    abs_rho_le_of_energy hm hq hμ0.le (by norm_num) (by norm_num [rhoMax])
      (qaField_B_ge hb0 (h.pos t ht).le hψt (θ t) (φ t))
      (energy_along hm.ne' hq hG h hE ht) W.rho_bound
  have hup := boozerGC_trapped_until (N := 0) (M := 1) (c := psiEdge) (c' := 823 / 100)
    (ιmin := 211 / 500) (Bmin := 493 / 100) (ε := 0) (Δρ := rhoMax) hm hq hG hμ0.le h
    (by norm_num [psiEdge]) (by linarith [hψ0.2]) (by norm_num) le_rfl (by norm_num)
    (fun x θ φ hx hxc => qaField_B_ge hb0 hx.le hxc θ φ)
    (fun x θ φ _ _ => by simp [symmetryDefect, exactQA_Bφ])
    (fun x hx _ => by
      have hp : ∀ y, exactQA.ψp y = 211 / 500 * y := fun _ => rfl
      rw [hp, hp, le_abs]; right; linarith)
    (fun t ht hhist => by rw [hρ0, sub_zero]; exact hρ t ht (hhist t ⟨ht.1, le_rfl⟩))
    (by rw [show exactQA.G = 581 / 10 from rfl]; norm_num [rhoMax]; linarith [hψ0.2])
  intro t ht
  have hψt : ψ t ≤ psiEdge := (hup t ht).trans (by norm_num [psiEdge])
  have hρt := hρ t ht hψt
  have hmom := exactQA_momentum h ht
  rw [hρ0, sub_zero] at hmom
  refine ⟨⟨?_, hψt⟩, hρt⟩
  have := (abs_le.mp hρt).1
  unfold psiLo
  unfold rhoMax at this
  nlinarith [hψ0.1]

/-- In exact QA, at fixed `ψ` the field is `c + A cos θ + C cos 2θ` (the `reactorQA` form with
`b₁ = 0`). -/
theorem exactQA_B_theta (x φ : ℝ) :
    (fun θ => exactQA.B x θ φ) = fun θ =>
      (57 / 10 + 2 * x / (57 / 10) * (-137 / 10000)) +
        (57 / 10 * (-7 / 100) * radius (57 / 10) x) * cos θ +
        (2 * x / (57 / 10) * (33 / 2000)) * cos (2 * θ) := by
  funext θ; rw [exactQA, qaField_B]; ring

/-- **Turning points and tip rigidity for exact QA** (no band hypothesis). For an exact-QA
3.5 MeV alpha in the pitch window starting at an upper turning point (`ρ(0) = 0`,
`θ(0) ∈ (0, π/2)`) with `ψ(0) ∈ [4.75, 5.79] T m²`: for every `N` with `N · 8 × 10⁻⁴ s ≤ T`,
turning points `τ 0 = 0 < … < τ N` exist as in `qaField_turning_points`, and moreover all of them
have the same flux `ψ(τ k) = ψ(0)` and all upper ones the same angle `θ(τ (2j)) = θ(0)`: the
reduced state `(ψ, θ, ρ)` returns exactly to its initial value at every upper turning point. -/
theorem exactQA_turning_points {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ} (hμ : μ ∈ Icc muLo muHi)
    (h : BoozerGCOrbitOn exactQA mα qα μ ψ θ φ ρ T)
    (hE : boozerEnergy exactQA mα qα μ ψ θ φ ρ 0 = Eα) (hρ0 : ρ 0 = 0)
    (hψ0 : ψ 0 ∈ Icc (475 / 100) (579 / 100)) (hθ0 : θ 0 ∈ Ioo 0 (π / 2))
    (N : ℕ) (hN : N * Lhalf ≤ T) :
    ∃ τ : ℕ → ℝ, τ 0 = 0 ∧ Monotone τ ∧
      (∀ k < N, τ k < τ (k + 1) ∧ τ (k + 1) ≤ τ k + Lhalf) ∧
      (∀ k ≤ N, parallelVelocity exactQA mα qα ψ θ φ ρ (τ k) = 0 ∧
        0 < along exactQA.B ψ θ φ (τ k) ∧ 0 < (-1) ^ k * θ (τ k)) ∧
      (∀ k ≤ N, τ k ≤ k * Lhalf) ∧
      (∀ k ≤ N, ψ (τ k) = ψ 0) ∧ (∀ j, 2 * j ≤ N → θ (τ (2 * j)) = θ 0) := by
  have hm : (0 : ℝ) < mα := by norm_num [mα]
  have hq : qα ≠ 0 := by norm_num [qα]
  have hG : exactQA.G ≠ 0 := by rw [exactQA, qaField_G]; norm_num
  have hb0 : |(0 : ℝ)| ≤ 43 / 100000 := by norm_num
  have hband := fun t ht => (exactQA_band hμ h hE hρ0 hψ0 t ht).1
  obtain ⟨τ, h0, hmono, hstep, htp, hle, -⟩ :=
    qaField_turning_points hb0 hμ h hE hband hρ0 hθ0 N hN
  have hT : ∀ k ≤ N, τ k ∈ Icc 0 T := fun k hk =>
    ⟨h0 ▸ hmono (Nat.zero_le k), (hle k hk).trans
      (le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (by norm_num [Lhalf])) hN)⟩
  have hQA : ∀ x θ φ, 0 < x → exactQA.Bφ x θ φ = 0 := fun x θ φ _ => exactQA_Bφ x θ φ
  have hpsi : ∀ k ≤ N, ψ (τ k) = ψ 0 := by
    intro k hk
    have := tip_psi_eq hm.ne' hq hG (fun x => qaField_ι 0 x) (by norm_num) hQA h
      (hT 0 (Nat.zero_le N))
      (hT k hk) (hmono (Nat.zero_le k)) (htp 0 (Nat.zero_le N)).2.1 (htp k hk).2.1
      (htp 0 (Nat.zero_le N)).1 (htp k hk).1
    rwa [h0] at this
  refine ⟨τ, h0, hmono, hstep, htp, hle, hpsi, fun j hj => ?_⟩
  -- confinement of `θ` to `(−π/2, π/2)`
  have W := qaField_window hb0 hμ
  have hθin := theta_confined hm hq hG h hE hband W.forbid_pos W.forbid_neg
    ⟨by linarith [hθ0.1, pi_pos], hθ0.2⟩
  have hψ00 : 0 < ψ 0 := by linarith [hψ0.1]
  have hmono' : StrictMonoOn (fun θ => exactQA.B (ψ (τ 0)) θ 0) (Icc 0 π) := by
    rw [h0, exactQA_B_theta]
    exact (cos_two_well (reactorQA_well_condition hψ00
      (by linarith [hψ0.2, show (579 / 100 : ℝ) ≤ psiEdge by norm_num [psiEdge]])) _).1
  have hk := htp (2 * j) hj
  rw [pow_mul, neg_one_sq, one_pow, one_mul] at hk
  have hθ2 := hθin (τ (2 * j)) (hT (2 * j) hj)
  have := tip_theta_eq hm.ne' hq hG (muLo_pos.trans_le hμ.1).ne' hQA h (hT 0 (Nat.zero_le N))
    (hT (2 * j) hj) ((hpsi (2 * j) hj).trans (by rw [h0])) (htp 0 (Nat.zero_le N)).2.1 hk.2.1
    (htp 0 (Nat.zero_le N)).1 hk.1 hmono'
    (by rw [h0]; exact ⟨hθ0.1.le, by linarith [hθ0.2, pi_pos]⟩)
    ⟨hk.2.2.le, by linarith [hθ2.2, pi_pos]⟩
  rwa [h0] at this

/-! ## Sanity checks -/

/-- `r = 0.9 m` at `ψ_lo`. -/
theorem radius_psiLo : radius (57 / 10) psiLo = 9 / 10 := by
  rw [radius, show 2 * psiLo / (57 / 10) = (9 / 10) ^ 2 by norm_num [psiLo],
    sqrt_sq (by norm_num)]

/-- **Rejected fixture (barely trapped / passing side).** For `μ = E/6` (tip field `6 T`) the
trapping condition `μ B > E` at `θ = π/2` fails at `ψ_lo` in `reactorQA`: such alphas reach
`θ = π/2`, so they are outside the window. -/
theorem window_rejects_shallow :
    ¬ ∀ x ∈ Icc psiLo psiEdge, ∀ φ, Eα < Eα / 6 * reactorQA.B x (π / 2) φ := by
  intro h
  have := h psiLo ⟨le_rfl, by norm_num [psiLo, psiEdge]⟩ 0
  rw [reactorQA_eq, qaField_B, radius_psiLo, cos_pi_div_two,
    show 2 * (π / 2) = π by ring, cos_pi, mul_zero, mul_zero, cos_zero] at this
  norm_num [psiLo, Eα] at this

/-- **Rejected fixture (deeply trapped side).** For `μ = E/5.3` (tip field `5.3 T`) the
condition "`μ B < E` at the bottom of the well" fails at `ψ_lo`, `θ = 0` in `reactorQA`: such
alphas can turn near `θ = 0`, where the streaming/drift ordering used here breaks down. -/
theorem window_rejects_deep :
    ¬ ∀ x ∈ Icc psiLo psiEdge, ∀ θ ∈ Icc (-(1 / 5 : ℝ)) (1 / 5), ∀ φ,
      Eα / (53 / 10) * reactorQA.B x θ φ < Eα := by
  intro h
  have := h psiLo ⟨le_rfl, by norm_num [psiLo, psiEdge]⟩ 0 (by norm_num) 0
  rw [reactorQA_eq, qaField_B, radius_psiLo, mul_zero, cos_zero] at this
  norm_num [psiLo, Eα] at this

end PlasmaLean.Design.NearAxisQATrappedBounce
