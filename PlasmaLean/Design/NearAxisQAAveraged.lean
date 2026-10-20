/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.AveragedTrapping
public import PlasmaLean.Design.NearAxisQA
public meta import Lean

/-!
# Averaged confinement of passing 3.5 MeV alphas in the reactor-scale near-axis QA model

Source: `notes/theory/guiding-centre-averaging.md` §1, §4 (iterated Lemma A); the model is
`Design/NearAxisQA.reactorQA` in the vacuum Boozer guiding-centre model of
`Theory/Kinetic/BoozerGuidingCentre`.

**Main result** (`alpha_trapped_reactorQA_averaged`): with the hypotheses of
`NearAxisQA.alpha_trapped_reactorQA` (3.5 MeV alpha, any `μ ≥ 0`, `|v_∥/v| ≥ 0.9` at `t = 0`,
start at `r ≤ a/4`; only the orbit horizon is longer), the orbit stays at `ψ ≤ 8.2 T m² < ψ_a`
for `0 ≤ t ≤ T = 0.19 s` (`Tav`), instead of `0.8 ms`. `alpha_trapped_reactorQA_averaged_of_le`
gives every horizon `T ≤ 0.19 s`; the earlier `0.11 s` statement is the corollary
`alpha_trapped_reactorQA_averaged_011`.

**Structure of the forcing.** The only symmetry-breaking term of the model is `r² b₁ cos 2φ`, so
`dP/dt = −(q²ρ²B/m + μ) ∂_φB = 2 b₁ c R² sin 2φ` with `c = μ + m v_∥²/B`: the defect is purely in
`φ` and the phase is `Φ = 2σφ` (`σ = sign v_∥`, constant for passing alphas), with phase speed
`Ω = 2|v_∥|B/G ≥ Ω₀ = 2 · 1.12 × 10⁷ · 4.93/58.1 ≈ 1.90 × 10⁶ s⁻¹`. The `θ`-dependence of `B`
(the `η r cos θ` and `B₂c r² cos 2θ` terms) does **not** create resonances at this order: Lemma A
only divides by the full phase speed `Ω`, never by `Ω − j ι φ̇`. The `θ` coupling enters through
the amplitudes, which contain `θ`-harmonics (frequency `ι φ̇ ≈ 0.4 Ω/2`); these are included
exactly in the Lie derivatives and are why the amplitudes decrease only by factors `≈ 0.1–0.5`
per step instead of `ν/Ω`.

**Method.**
1. State variables `x = r cos θ, y = r sin θ, R² = 2ψ/B₀, C = cos 2φ, S = sin 2φ,
   W = σ v_∥/10⁷, 1/W, B, 1/B, U = μ/10⁻¹⁴, σ` (`orbX`). Along every model orbit they satisfy a
   **polynomial** ODE `ẋᵢ = flowsᵢ(x)` (`hasDerivAt_orbX`, proved from the Boozer equations; the
   `1/r` singularities of the `(ψ, θ)` chart cancel exactly).
2. The amplitudes `amp 0 = σ 2 b₁ c R²`, `amp (j+1) = ± L(amp j · 1/Ω)` (`amp`) are computed
   exactly in `ℚ` by the kernel (`LiePoly.lie`, 2, 15, 121 and 458 monomials). The expensive
   one, `amp 3`, is evaluated **once**: `amp3Lit_eq` checks it against a literal.
3. Bounds (in units of `q` T m²/s): `|amp 0| ≤ 1935`, `|amp 1| ≤ 218`, `|amp 2| ≤ 93` (one
   ball over the whole region, `glob_j`) and `|amp 3| ≤ 11` (`amp3_bound`). The last is a
   two-stage enclosure: `LiePoly.stage1` encloses the dependence on `cos 2φ, sin 2φ, W, 1/W, U`
   once per sign of `σ` (a `214`-term polynomial in `x, y, R², B, 1/B` with ball
   coefficients, `S3pos_eq`, `S3neg_eq`), which is then enclosed on the `324` rectangles of an
   adaptive bisection of the disc `r ≤ a` (`CoverCert`, proof term built by the `meta`
   tactic `cover_cert` from an untrusted plan; `cover_pos`, `cover_neg`). All checks are
   kernel evaluations of exact integer/rational arithmetic.
4. `Kinetic.Boozer.boozerGC_trapped_until_averaged` with `k = 3`: gap
   `|G| Δρ + (2 (1935 + 218 + 93)/Ω₀ + 11 T) ≤ ι₀ (8.2 − ψ(0))`, `Δρ ≈ 1.88 cm`
   (`averaged_gap`), which holds for `T = 0.19 s` and fails for `T = 0.20 s`
   (`averaged_gap_fails_late`).

**Caveats (model only).**
* The Boozer guiding-centre equations are a supplied model (not derived from the Lorentz
  force); orbits are supplied and must stay in the chart `ψ > 0` (off the magnetic axis).
* The field is the truncated second-order near-axis expansion, which agrees with a real vacuum
  field only to the order of the expansion; the `O(r³)` remainder has no rigorous bound.
* Passing particles only (`|v_∥/v| ≥ 0.9` at `t = 0`, hence `|v_∥| ≥ 1.12 × 10⁷ m/s` throughout):
  trapped and barely passing alphas have a phase speed that changes sign and are not covered.
* No collisions or slowing down; `T = 0.19 s` is about half of the slowing-down time
  (`≈ 0.4 s`), not the full time.

**What limits `T`.** The secular rate `11` is a sup over the whole disc and both `σ` (the
sampled sup along the region is `≈ 6`). Refining the cover further stalls near `10.5`, because
the variables `cos 2φ, sin 2φ, W, U` are enclosed globally in stage one. A fourth integration
by parts would need `amp 4` (`1901` monomials); its exact kernel evaluation did not finish
within 15 minutes in experiments, so it is not used. The constant term
`2 ∑ Aⱼ/Ω₀ ≈ 2.4 × 10⁻³ T m²` is negligible; the orbit-width term `|G| Δρ ≈ 1.09 T m²` uses
about a third of the gap `ι₀ (8.2 − ψ(0)) ≈ 3.24 T m²`.
-/
public section
noncomputable section
namespace PlasmaLean.Design.NearAxisQAAveraged
open PlasmaLean.Kinetic PlasmaLean.Kinetic.Boozer PlasmaLean.Kinetic.LiePoly
  PlasmaLean.Design.NearAxisQA Real

/-! ## Model constants and the polynomial vector field -/

/-- `B₀ = 5.7 T`. -/
@[expose] def cB0 : ℚ := 57 / 10
/-- `η = −0.07 m⁻¹`. -/
@[expose] def cEta : ℚ := -7 / 100
/-- `b₀ = −0.0137 T/m²`. -/
@[expose] def cb0 : ℚ := -137 / 10000
/-- `b₁ = −4.3 × 10⁻⁴ T/m²`. -/
@[expose] def cb1 : ℚ := -43 / 100000
/-- `B₂c = 0.0165 T/m²`. -/
@[expose] def cB2c : ℚ := 33 / 2000
/-- `ι₀ = 211/500`. -/
@[expose] def cIo : ℚ := 211 / 500
/-- `G = 58.1 T m`. -/
@[expose] def cG : ℚ := 581 / 10
/-- Alpha mass `6.6447 × 10⁻²⁷ kg`. -/
@[expose] def cm : ℚ := 66447 / 10 ^ 31
/-- Alpha charge `3.2044 × 10⁻¹⁹ C`. -/
@[expose] def cq : ℚ := 32044 / 10 ^ 23
/-- Velocity scale `10⁷ m/s`. -/
@[expose] def cvs : ℚ := 10 ^ 7
/-- Magnetic-moment scale `10⁻¹⁴ J/T`. -/
@[expose] def cmus : ℚ := 1 / 10 ^ 14

/-- Variable `i` (of the 11 state variables). -/
@[expose] def V (i : ℕ) : Poly := varP 11 i 1
/-- Constant polynomial. -/
@[expose] def K (c : ℚ) : Poly := cstP 11 c

/-- `c = μ + m v²/B = mus·U + m vs² W² IB` (the factor `q²ρ²B/m + μ`). -/
@[expose] def cP : Poly :=
  addP (scP cmus (V 9)) (scP (cm * cvs ^ 2) (mulP (mulP (V 5) (V 5)) (V 8)))
/-- `D = ∂_φB + ι ∂_θB = −2b₁ R² S − ι B₀ η y − 4 ι B₂c x y`. -/
@[expose] def DP : Poly :=
  addP (scP (-2 * cb1) (mulP (V 2) (V 4)))
    (addP (scP (-cIo * cB0 * cEta) (V 1)) (scP (-4 * cIo * cB2c) (mulP (V 0) (V 1))))
/-- `v = vs σ W`. -/
@[expose] def vP : Poly := scP cvs (mulP (V 10) (V 5))
/-- `dv/dt = −μ B D/(G m)`. -/
@[expose] def dvP : Poly := scP (-cmus / (cG * cm)) (mulP (V 9) (mulP (V 7) DP))

/-- The guiding-centre vector field in the variables
`(x, y, R², cos 2φ, sin 2φ, W, 1/W, B, 1/B, U, σ)`. -/
@[expose] def flows : List Poly :=
  [ addP (scP (2 / (cq * cB0)) (mulP cP (mulP (V 1) (addP (K (cB2c - cb0)) (scP (-cb1) (V 3))))))
      (scP (-cIo / cG) (mulP vP (mulP (V 7) (V 1)))),
    addP (scP (1 / cq) (mulP cP (addP (K cEta)
        (scP (2 / cB0) (mulP (V 0) (addP (K (cB2c + cb0)) (scP cb1 (V 3))))))))
      (scP (cIo / cG) (mulP vP (mulP (V 7) (V 0)))),
    scP (2 / cq) (mulP cP (addP (scP cEta (V 1)) (scP (4 * cB2c / cB0) (mulP (V 0) (V 1))))),
    scP (-2 / cG) (mulP (V 4) (mulP vP (V 7))),
    scP (2 / cG) (mulP (V 3) (mulP vP (V 7))),
    scP (1 / cvs) (mulP (V 10) dvP),
    scP (-1 / cvs) (mulP (mulP (V 6) (V 6)) (mulP (V 10) dvP)),
    scP (1 / cG) (mulP vP (mulP (V 7) DP)),
    scP (-1 / cG) (mulP vP (mulP (V 8) DP)),
    [], [] ]

/-! ## Orbit variables -/

/-- Parallel velocity along the orbit. -/
@[expose] def vel (ψ θ φ ρ : ℝ → ℝ) (t : ℝ) : ℝ := parallelVelocity reactorQA mα qα ψ θ φ ρ t

/-- Field strength along the orbit. -/
@[expose] def Bt (ψ θ φ : ℝ → ℝ) (t : ℝ) : ℝ := along reactorQA.B ψ θ φ t

/-- The state variables along an orbit (index `i ≥ 11` gives `0`). -/
@[expose] def orbX (σ μ : ℝ) (ψ θ φ ρ : ℝ → ℝ) (t : ℝ) (i : ℕ) : ℝ :=
  [radius (57 / 10) (ψ t) * cos (θ t), radius (57 / 10) (ψ t) * sin (θ t), 2 * ψ t / (57 / 10),
    cos (2 * φ t), sin (2 * φ t), σ * vel ψ θ φ ρ t / 10 ^ 7, (σ * vel ψ θ φ ρ t / 10 ^ 7)⁻¹,
    Bt ψ θ φ t, (Bt ψ θ φ t)⁻¹, μ * 10 ^ 14, σ].getD i 0

theorem eval_flow0 (x : ℕ → ℝ) : eval (flows.getD 0 []) x =
    2 / (cq * cB0) * (cmus * x 9 + cm * cvs ^ 2 * x 5 ^ 2 * x 8) * x 1 * (cB2c - cb0 - cb1 * x 3) -
      cIo / cG * cvs * (x 10 * x 5) * x 7 * x 1 := by
  simp [flows, cP, vP, V, K, eval_varP]
  ring

theorem eval_flow1 (x : ℕ → ℝ) : eval (flows.getD 1 []) x =
    1 / cq * (cmus * x 9 + cm * cvs ^ 2 * x 5 ^ 2 * x 8) *
        (cEta + 2 / cB0 * x 0 * (cB2c + cb0 + cb1 * x 3)) +
      cIo / cG * cvs * (x 10 * x 5) * x 7 * x 0 := by
  simp [flows, cP, vP, V, K, eval_varP]
  ring

theorem eval_flow2 (x : ℕ → ℝ) : eval (flows.getD 2 []) x =
    2 / cq * (cmus * x 9 + cm * cvs ^ 2 * x 5 ^ 2 * x 8) *
      (cEta * x 1 + 4 * cB2c / cB0 * x 0 * x 1) := by
  simp [flows, cP, V, K, eval_varP]
  ring

theorem eval_flow3 (x : ℕ → ℝ) : eval (flows.getD 3 []) x =
    -2 / cG * x 4 * cvs * (x 10 * x 5) * x 7 := by
  simp [flows, vP, V, eval_varP]
  ring

theorem eval_flow4 (x : ℕ → ℝ) : eval (flows.getD 4 []) x =
    2 / cG * x 3 * cvs * (x 10 * x 5) * x 7 := by
  simp [flows, vP, V, eval_varP]
  ring

/-- `D` in the state variables. -/
@[expose] def Dfun (x : ℕ → ℝ) : ℝ :=
  -2 * cb1 * x 2 * x 4 - cIo * cB0 * cEta * x 1 - 4 * cIo * cB2c * x 0 * x 1

theorem eval_DP (x : ℕ → ℝ) : eval DP x = Dfun x := by
  simp [DP, Dfun, V, eval_varP]
  ring

theorem eval_flow5 (x : ℕ → ℝ) : eval (flows.getD 5 []) x =
    1 / cvs * x 10 * (-cmus / (cG * cm)) * x 9 * x 7 * Dfun x := by
  simp [flows, dvP, V, eval_varP, eval_DP]
  ring

theorem eval_flow6 (x : ℕ → ℝ) : eval (flows.getD 6 []) x =
    -1 / cvs * x 6 ^ 2 * x 10 * (-cmus / (cG * cm)) * x 9 * x 7 * Dfun x := by
  simp [flows, dvP, V, eval_varP, eval_DP]
  ring

theorem eval_flow7 (x : ℕ → ℝ) : eval (flows.getD 7 []) x =
    1 / cG * cvs * (x 10 * x 5) * x 7 * Dfun x := by
  simp [flows, vP, V, eval_varP, eval_DP]
  ring

theorem eval_flow8 (x : ℕ → ℝ) : eval (flows.getD 8 []) x =
    -1 / cG * cvs * (x 10 * x 5) * x 8 * Dfun x := by
  simp [flows, vP, V, eval_varP, eval_DP]
  ring

theorem eval_flow_ge9 (x : ℕ → ℝ) (i : ℕ) (hi : 9 ≤ i) : eval (flows.getD i []) x = 0 := by
  rcases Nat.lt_or_ge i 11 with h | h
  · interval_cases i <;> simp [flows]
  · rw [List.getD_eq_default _ _ (show flows.length ≤ i by simp [flows]; omega)]; simp

theorem mα_eq : mα = (cm : ℝ) := by norm_num [mα, cm]
theorem qα_eq : qα = (cq : ℝ) := by norm_num [qα, cq]

variable {μ σ : ℝ} {ψ θ φ ρ : ℝ → ℝ} {T : ℝ}

theorem orbX_sq5 (hσ : σ ^ 2 = 1) (t : ℝ) :
    orbX σ μ ψ θ φ ρ t 5 ^ 2 = vel ψ θ φ ρ t ^ 2 / 10 ^ 14 := by
  simp only [orbX, List.getD_cons_succ, List.getD_cons_zero]
  rw [div_pow, mul_pow, hσ]; ring

theorem orbX_105 (hσ : σ ^ 2 = 1) (t : ℝ) :
    orbX σ μ ψ θ φ ρ t 10 * orbX σ μ ψ θ φ ρ t 5 = vel ψ θ φ ρ t / 10 ^ 7 := by
  simp only [orbX, List.getD_cons_succ, List.getD_cons_zero]
  rw [← mul_div_assoc, ← mul_assoc, ← sq, hσ, one_mul]

/-- The radial-like variable `x = r cos θ` has derivative `flows[0]`. -/
theorem hasDerivAt_x (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T) {s : ℝ}
    (hs : s ∈ Set.Icc 0 T) (hσ : σ ^ 2 = 1) (_hB : Bt ψ θ φ s ≠ 0) :
    HasDerivAt (fun r => orbX σ μ ψ θ φ ρ r 0)
      (eval (flows.getD 0 []) (orbX σ μ ψ θ φ ρ s)) s := by
  have hψ := h.pos s hs
  have h2 : HasDerivAt (fun r => 2 * ψ r / (57 / 10))
      (2 * (-(mα * μ + qα ^ 2 * ρ s ^ 2 * along reactorQA.B ψ θ φ s) *
        along reactorQA.Bθ ψ θ φ s / (mα * qα)) / (57 / 10)) s :=
    ((h.dψ s hs).const_mul 2).div_const _
  have hr := (h2.sqrt (by positivity)).mul (h.dθ s hs).cos
  refine hr.congr_deriv ?_
  rw [eval_flow0, orbX_sq5 hσ, orbX_105 hσ]
  simp only [orbX, List.getD_cons_succ, List.getD_cons_zero, vel, Bt, parallelVelocity, along,
    radius, reactorQA, field, nearAxisBθ, nearAxisBψ, mα_eq, qα_eq]
  have hr0 : 0 < √(2 * ψ s / (57 / 10)) := sqrt_pos.mpr (by positivity)
  have hr2 : √(2 * ψ s / (57 / 10)) ^ 2 = 2 * ψ s / (57 / 10) := sq_sqrt (by positivity)
  generalize √(2 * ψ s / (57 / 10)) = r at hr0 hr2 ⊢
  have hψr : ψ s = 57 / 10 * r ^ 2 / 2 := by linarith
  rw [hψr]
  simp only [cos_two_mul (θ s), sin_two_mul (θ s)]
  simp only [cm, cq, cmus, cvs, cB0, cB2c, cb0, cb1, cIo, cG]
  push_cast
  field_simp
  ring

/-- `y = r sin θ` has derivative `flows[1]`. -/
theorem hasDerivAt_y (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T) {s : ℝ}
    (hs : s ∈ Set.Icc 0 T) (hσ : σ ^ 2 = 1) (_hB : Bt ψ θ φ s ≠ 0) :
    HasDerivAt (fun r => orbX σ μ ψ θ φ ρ r 1)
      (eval (flows.getD 1 []) (orbX σ μ ψ θ φ ρ s)) s := by
  have hψ := h.pos s hs
  have h2 : HasDerivAt (fun r => 2 * ψ r / (57 / 10))
      (2 * (-(mα * μ + qα ^ 2 * ρ s ^ 2 * along reactorQA.B ψ θ φ s) *
        along reactorQA.Bθ ψ θ φ s / (mα * qα)) / (57 / 10)) s :=
    ((h.dψ s hs).const_mul 2).div_const _
  have hr := (h2.sqrt (by positivity)).mul (h.dθ s hs).sin
  refine hr.congr_deriv ?_
  rw [eval_flow1, orbX_sq5 hσ, orbX_105 hσ]
  simp only [orbX, List.getD_cons_succ, List.getD_cons_zero, vel, Bt, parallelVelocity, along,
    radius, reactorQA, field, nearAxisBθ, nearAxisBψ, nearAxisBφ, mα_eq, qα_eq]
  have hr0 : 0 < √(2 * ψ s / (57 / 10)) := sqrt_pos.mpr (by positivity)
  have hr2 : √(2 * ψ s / (57 / 10)) ^ 2 = 2 * ψ s / (57 / 10) := sq_sqrt (by positivity)
  generalize √(2 * ψ s / (57 / 10)) = r at hr0 hr2 ⊢
  have hψr : ψ s = 57 / 10 * r ^ 2 / 2 := by linarith
  rw [hψr]
  simp only [cos_two_mul (θ s), sin_two_mul (θ s)]
  simp only [cm, cq, cmus, cvs, cB0, cB2c, cb0, cb1, cIo, cG, cEta]
  push_cast
  have hc2 : cos (θ s) ^ 2 = 1 - sin (θ s) ^ 2 := by linarith [sin_sq_add_cos_sq (θ s)]
  have hc3 : cos (θ s) ^ 3 = cos (θ s) * (1 - sin (θ s) ^ 2) := by rw [← hc2]; ring
  field_simp
  ring_nf
  simp only [hc2, hc3]
  ring

/-- `R² = 2ψ/B₀` has derivative `flows[2]`. -/
theorem hasDerivAt_R2 (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T) {s : ℝ}
    (hs : s ∈ Set.Icc 0 T) (hσ : σ ^ 2 = 1) (_hB : Bt ψ θ φ s ≠ 0) :
    HasDerivAt (fun r => orbX σ μ ψ θ φ ρ r 2)
      (eval (flows.getD 2 []) (orbX σ μ ψ θ φ ρ s)) s := by
  have hψ := h.pos s hs
  have h2 : HasDerivAt (fun r => 2 * ψ r / (57 / 10))
      (2 * (-(mα * μ + qα ^ 2 * ρ s ^ 2 * along reactorQA.B ψ θ φ s) *
        along reactorQA.Bθ ψ θ φ s / (mα * qα)) / (57 / 10)) s :=
    ((h.dψ s hs).const_mul 2).div_const _
  refine h2.congr_deriv ?_
  rw [eval_flow2, orbX_sq5 hσ]
  simp only [orbX, List.getD_cons_succ, List.getD_cons_zero, vel, Bt, parallelVelocity, along,
    radius, reactorQA, field, nearAxisBθ, nearAxisBφ, mα_eq, qα_eq]
  have hr0 : 0 < √(2 * ψ s / (57 / 10)) := sqrt_pos.mpr (by positivity)
  have hr2 : √(2 * ψ s / (57 / 10)) ^ 2 = 2 * ψ s / (57 / 10) := sq_sqrt (by positivity)
  generalize √(2 * ψ s / (57 / 10)) = r at hr0 hr2 ⊢
  have hψr : ψ s = 57 / 10 * r ^ 2 / 2 := by linarith
  rw [hψr]
  simp only [sin_two_mul (θ s)]
  simp only [cm, cq, cmus, cvs, cB0, cB2c, cEta]
  push_cast
  field_simp
  ring

/-- `cos 2φ` has derivative `flows[3]`. -/
theorem hasDerivAt_C (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T) {s : ℝ}
    (hs : s ∈ Set.Icc 0 T) (hσ : σ ^ 2 = 1) (_hB : Bt ψ θ φ s ≠ 0) :
    HasDerivAt (fun r => orbX σ μ ψ θ φ ρ r 3)
      (eval (flows.getD 3 []) (orbX σ μ ψ θ φ ρ s)) s := by
  have h2 := ((h.dφ s hs).const_mul 2).cos
  refine h2.congr_deriv ?_
  rw [eval_flow3, orbX_105 hσ]
  simp only [orbX, List.getD_cons_succ, List.getD_cons_zero, vel, Bt, parallelVelocity, along,
    radius, reactorQA, field, nearAxisBθ, nearAxisBφ, mα_eq, qα_eq]
  simp only [cm, cq, cvs, cG]
  push_cast
  field_simp

/-- `sin 2φ` has derivative `flows[4]`. -/
theorem hasDerivAt_S (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T) {s : ℝ}
    (hs : s ∈ Set.Icc 0 T) (hσ : σ ^ 2 = 1) (_hB : Bt ψ θ φ s ≠ 0) :
    HasDerivAt (fun r => orbX σ μ ψ θ φ ρ r 4)
      (eval (flows.getD 4 []) (orbX σ μ ψ θ φ ρ s)) s := by
  have h2 := ((h.dφ s hs).const_mul 2).sin
  refine h2.congr_deriv ?_
  rw [eval_flow4, orbX_105 hσ]
  simp only [orbX, List.getD_cons_succ, List.getD_cons_zero, vel, Bt, parallelVelocity, along,
    radius, reactorQA, field, nearAxisBθ, nearAxisBφ, mα_eq, qα_eq]
  simp only [cm, cq, cvs, cG]
  push_cast
  field_simp

/-- The field strength `B` has derivative `flows[7]`. -/
theorem hasDerivAt_B7 (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T) {s : ℝ}
    (hs : s ∈ Set.Icc 0 T) (hσ : σ ^ 2 = 1) (_hB : Bt ψ θ φ s ≠ 0) :
    HasDerivAt (fun r => orbX σ μ ψ θ φ ρ r 7)
      (eval (flows.getD 7 []) (orbX σ μ ψ θ φ ρ s)) s := by
  have hψ := h.pos s hs
  refine (h.hasDerivAt_B hs).congr_deriv ?_
  rw [eval_flow7, orbX_105 hσ]
  simp only [Dfun]
  simp only [orbX, List.getD_cons_succ, List.getD_cons_zero, vel, Bt, parallelVelocity, along,
    radius, reactorQA, field, nearAxisBθ, nearAxisBψ, nearAxisBφ, mα_eq, qα_eq]
  have hr0 : 0 < √(2 * ψ s / (57 / 10)) := sqrt_pos.mpr (by positivity)
  have hr2 : √(2 * ψ s / (57 / 10)) ^ 2 = 2 * ψ s / (57 / 10) := sq_sqrt (by positivity)
  generalize √(2 * ψ s / (57 / 10)) = r at hr0 hr2 ⊢
  have hψr : ψ s = 57 / 10 * r ^ 2 / 2 := by linarith
  rw [hψr]
  simp only [cos_two_mul (θ s), sin_two_mul (θ s)]
  simp only [cm, cq, cvs, cB0, cB2c, cb1, cIo, cG, cEta]
  push_cast
  field_simp
  ring

/-- `W = σ v/10⁷` has derivative `flows[5]`. -/
theorem hasDerivAt_W (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T) {s : ℝ}
    (hs : s ∈ Set.Icc 0 T) (_hσ : σ ^ 2 = 1) (_hB : Bt ψ θ φ s ≠ 0) :
    HasDerivAt (fun r => orbX σ μ ψ θ φ ρ r 5)
      (eval (flows.getD 5 []) (orbX σ μ ψ θ φ ρ s)) s := by
  have hψ := h.pos s hs
  have hv := ((((h.dρ s hs).const_mul qα).mul (h.hasDerivAt_B hs)).div_const mα).const_mul σ
    |>.div_const ((10 : ℝ) ^ 7)
  refine hv.congr_deriv ?_
  rw [eval_flow5]
  simp only [Dfun]
  simp only [orbX, List.getD_cons_succ, List.getD_cons_zero, vel, Bt, parallelVelocity, along,
    radius, reactorQA, field, nearAxisBθ, nearAxisBψ, nearAxisBφ, mα_eq, qα_eq]
  have hr0 : 0 < √(2 * ψ s / (57 / 10)) := sqrt_pos.mpr (by positivity)
  have hr2 : √(2 * ψ s / (57 / 10)) ^ 2 = 2 * ψ s / (57 / 10) := sq_sqrt (by positivity)
  generalize √(2 * ψ s / (57 / 10)) = r at hr0 hr2 ⊢
  have hψr : ψ s = 57 / 10 * r ^ 2 / 2 := by linarith
  rw [hψr]
  simp only [cos_two_mul (θ s), sin_two_mul (θ s)]
  simp only [cm, cq, cmus, cvs, cB0, cB2c, cb1, cIo, cG, cEta]
  push_cast
  field_simp
  ring

theorem orbX_6 (t : ℝ) : orbX σ μ ψ θ φ ρ t 6 = (orbX σ μ ψ θ φ ρ t 5)⁻¹ := by
  simp [orbX]

theorem orbX_8 (t : ℝ) : orbX σ μ ψ θ φ ρ t 8 = (orbX σ μ ψ θ φ ρ t 7)⁻¹ := by
  simp [orbX]

theorem orbX_ge11 (t : ℝ) {i : ℕ} (hi : 11 ≤ i) : orbX σ μ ψ θ φ ρ t i = 0 := by
  unfold orbX
  rw [List.getD_eq_default _ _ (by simp; omega)]

/-- `1/W` has derivative `flows[6]`. -/
theorem hasDerivAt_IW (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T) {s : ℝ}
    (hs : s ∈ Set.Icc 0 T) (hσ : σ ^ 2 = 1) (hB : Bt ψ θ φ s ≠ 0)
    (hW : orbX σ μ ψ θ φ ρ s 5 ≠ 0) :
    HasDerivAt (fun r => orbX σ μ ψ θ φ ρ r 6)
      (eval (flows.getD 6 []) (orbX σ μ ψ θ φ ρ s)) s := by
  have := (hasDerivAt_W h hs hσ hB).inv hW
  refine this.congr_deriv ?_
  rw [eval_flow5, eval_flow6, orbX_6]
  field_simp

/-- `1/B` has derivative `flows[8]`. -/
theorem hasDerivAt_IB (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T) {s : ℝ}
    (hs : s ∈ Set.Icc 0 T) (hσ : σ ^ 2 = 1) (hB : Bt ψ θ φ s ≠ 0) :
    HasDerivAt (fun r => orbX σ μ ψ θ φ ρ r 8)
      (eval (flows.getD 8 []) (orbX σ μ ψ θ φ ρ s)) s := by
  have hB' : orbX σ μ ψ θ φ ρ s 7 ≠ 0 := by simpa [orbX] using hB
  have := (hasDerivAt_B7 h hs hσ hB).inv hB'
  refine this.congr_deriv ?_
  rw [eval_flow7, eval_flow8, orbX_8]
  field_simp

/-- **All state variables** satisfy `ẋᵢ = flowsᵢ(x)` along the orbit (where `B ≠ 0`, `W ≠ 0`). -/
theorem hasDerivAt_orbX (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T) {s : ℝ}
    (hs : s ∈ Set.Icc 0 T) (hσ : σ ^ 2 = 1) (hB : Bt ψ θ φ s ≠ 0)
    (hW : orbX σ μ ψ θ φ ρ s 5 ≠ 0) (i : ℕ) :
    HasDerivAt (fun r => orbX σ μ ψ θ φ ρ r i)
      (eval (flows.getD i []) (orbX σ μ ψ θ φ ρ s)) s := by
  match i with
  | 0 => exact hasDerivAt_x h hs hσ hB
  | 1 => exact hasDerivAt_y h hs hσ hB
  | 2 => exact hasDerivAt_R2 h hs hσ hB
  | 3 => exact hasDerivAt_C h hs hσ hB
  | 4 => exact hasDerivAt_S h hs hσ hB
  | 5 => exact hasDerivAt_W h hs hσ hB
  | 6 => exact hasDerivAt_IW h hs hσ hB hW
  | 7 => exact hasDerivAt_B7 h hs hσ hB
  | 8 => exact hasDerivAt_IB h hs hσ hB
  | 9 =>
    rw [eval_flow_ge9 _ 9 le_rfl]
    simpa [orbX] using hasDerivAt_const s (μ * 10 ^ 14)
  | 10 =>
    rw [eval_flow_ge9 _ 10 (by norm_num)]
    simpa [orbX] using hasDerivAt_const s σ
  | n + 11 =>
    rw [eval_flow_ge9 _ (n + 11) (by omega)]
    have : (fun r => orbX σ μ ψ θ φ ρ r (n + 11)) = fun _ => 0 :=
      funext fun r => orbX_ge11 r (by omega)
    rw [this]
    exact hasDerivAt_const s 0

/-! ## Iterated amplitudes -/

/-- Exponent reduction using `W·(1/W) = 1`, `B·(1/B) = 1` and `σ² = 1`. -/
@[expose] def redE (e : List ℕ) : List ℕ :=
  match e with
  | [x, y, r, c, s, w, iw, b, ib, u, sg] =>
    [x, y, r, c, s, w - min w iw, iw - min w iw, b - min b ib, ib - min b ib, u, sg % 2]
  | e => e

theorem pow_cancel_pair {a b : ℝ} (hab : a * b = 1) (m n : ℕ) :
    a ^ (m - min m n) * b ^ (n - min m n) = a ^ m * b ^ n := by
  rcases le_total m n with h | h
  · rw [min_eq_left h, Nat.sub_self, pow_zero, one_mul]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [show m + k - m = k by omega, pow_add,
      show a ^ m * (b ^ m * b ^ k) = b ^ k * (a * b) ^ m by ring, hab, one_pow, mul_one]
  · rw [min_eq_right h, Nat.sub_self, pow_zero, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [show n + k - n = k by omega, pow_add,
      show a ^ n * a ^ k * b ^ n = a ^ k * (a * b) ^ n by ring, hab, one_pow, mul_one]

theorem pow_mod_two {a : ℝ} (ha : a ^ 2 = 1) (n : ℕ) : a ^ (n % 2) = a ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 2, pow_add, pow_mul, ha, one_pow, one_mul]

theorem evalMono_redE (e : List ℕ) {x : ℕ → ℝ} (h56 : x 5 * x 6 = 1) (h78 : x 7 * x 8 = 1)
    (h10 : x 10 ^ 2 = 1) : evalMono (redE e) x = evalMono e x := by
  unfold redE
  split
  · rename_i a0 a1 a2 a3 a4 w iw b ib u sg
    simp only [evalMono, mul_one]
    have e1 := pow_cancel_pair h56 w iw
    have e2 := pow_cancel_pair h78 b ib
    have e3 := pow_mod_two h10 sg
    simp only [zero_add] at *
    rw [e3]
    calc _ = x 0 ^ a0 * (x 1 ^ a1 * (x 2 ^ a2 * (x 3 ^ a3 * (x 4 ^ a4 *
          ((x 5 ^ (w - min w iw) * x 6 ^ (iw - min w iw)) *
          ((x 7 ^ (b - min b ib) * x 8 ^ (ib - min b ib)) * (x 9 ^ u * x 10 ^ sg))))))) := by ring
      _ = _ := by rw [e1, e2]; ring
  · rfl

/-- `1/Ω = G/(2 vs W B)` as a polynomial. -/
@[expose] def iOm : Poly := scP (cG / (2 * cvs)) (mulP (V 6) (V 8))

/-- The iterated amplitudes: `amp 0 = σ 2 b₁ c R²` (the coefficient of `sin Φ` in `dP/dt`) and
`amp (j+1) = ± L_X(amp j / Ω)` (sign `+` for even `j`, `−` for odd `j`), normalized by
`redE`. -/
@[expose] def amp : ℕ → Poly
  | 0 => scP (2 * cb1) (mulP (V 10) (mulP cP (V 2)))
  | j + 1 => normWith redE (scP (if j % 2 = 0 then 1 else -1) (lie (mulP (amp j) iOm) flows))

/-- Phase speed `Ω = 2 vs W B/G`. -/
@[expose] def Omf (σ μ : ℝ) (ψ θ φ ρ : ℝ → ℝ) (t : ℝ) : ℝ :=
  2 * 10 ^ 7 * orbX σ μ ψ θ φ ρ t 5 * orbX σ μ ψ θ φ ρ t 7 / (581 / 10)

theorem amp_div_Om (j : ℕ) (t : ℝ) :
    eval (amp j) (orbX σ μ ψ θ φ ρ t) / Omf σ μ ψ θ φ ρ t =
      eval (mulP (amp j) iOm) (orbX σ μ ψ θ φ ρ t) := by
  rw [eval_mulP]
  simp only [iOm, eval_scP, eval_mulP, V, eval_varP (show 6 < 11 by norm_num),
    eval_varP (show 8 < 11 by norm_num), orbX_6, orbX_8, Omf, cG, cvs]
  push_cast
  rw [div_eq_mul_inv]
  congr 1
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- Derivative of `amp j / Ω` along the orbit: `± amp (j+1)`. -/
theorem amp_ratio_hasDerivAt (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T) {s : ℝ}
    (hs : s ∈ Set.Icc 0 T) (hσ : σ ^ 2 = 1) (hB : Bt ψ θ φ s ≠ 0)
    (hW : orbX σ μ ψ θ φ ρ s 5 ≠ 0) (j : ℕ) :
    HasDerivAt (fun r => eval (amp j) (orbX σ μ ψ θ φ ρ r) / Omf σ μ ψ θ φ ρ r)
      ((if j % 2 = 0 then 1 else -1) * eval (amp (j + 1)) (orbX σ μ ψ θ φ ρ s)) s := by
  have hfun : (fun r => eval (amp j) (orbX σ μ ψ θ φ ρ r) / Omf σ μ ψ θ φ ρ r) =
      fun r => eval (mulP (amp j) iOm) (orbX σ μ ψ θ φ ρ r) := funext fun r => amp_div_Om j r
  rw [hfun]
  refine (hasDerivAt_eval _ flows (hasDerivAt_orbX h hs hσ hB hW)).congr_deriv ?_
  have h56 : orbX σ μ ψ θ φ ρ s 5 * orbX σ μ ψ θ φ ρ s 6 = 1 := by
    rw [orbX_6]; exact mul_inv_cancel₀ hW
  have h78 : orbX σ μ ψ θ φ ρ s 7 * orbX σ μ ψ θ φ ρ s 8 = 1 := by
    rw [orbX_8]; exact mul_inv_cancel₀ (by simpa [orbX] using hB)
  have h10 : orbX σ μ ψ θ φ ρ s 10 ^ 2 = 1 := by simpa [orbX] using hσ
  rw [amp, eval_normWith _ _ _ (fun e => evalMono_redE e h56 h78 h10), eval_scP]
  split_ifs <;> push_cast <;> ring

/-! ## Ball-arithmetic certificate for the amplitudes -/

/-- The field strength `B₀ + B₀ η x + R² (b₀ + b₁ C) + B₂c (x² − y²)` as a polynomial. -/
@[expose] def Bpoly : Poly :=
  addP (K cB0) (addP (scP (cB0 * cEta) (V 0)) (addP (mulP (V 2) (addP (K cb0) (scP cb1 (V 3))))
    (scP cB2c (addP (mulP (V 0) (V 0)) (scP (-1) (mulP (V 1) (V 1)))))))

theorem eval_Bpoly (x : ℕ → ℝ) : eval Bpoly x =
    cB0 + cB0 * cEta * x 0 + x 2 * (cb0 + cb1 * x 3) + cB2c * (x 0 ^ 2 - x 1 ^ 2) := by
  simp [Bpoly, V, K, eval_varP]
  ring

/-- Minor radius `a = 1.7 m`. -/
@[expose] def aR : ℚ := 17 / 10
/-- Lower bound for `W = |v_∥|/10⁷` (passing alphas). -/
@[expose] def Wlo : ℚ := 112 / 100
/-- Upper bound for `W`. -/
@[expose] def Whi : ℚ := 13 / 10
/-- Upper bound for `U = μ/10⁻¹⁴`. -/
@[expose] def Umax : ℚ := 21612 / 10000
/-- Field range `B_min`. -/
@[expose] def Bmin : ℚ := 493 / 100
/-- Field range `B_max`. -/
@[expose] def Bmax : ℚ := 647 / 100

/-- Point of `[lo, hi]` closest to `0`. -/
@[expose] def closest (lo hi : ℚ) : ℚ := if 0 < lo then lo else if hi < 0 then hi else 0
/-- Largest square on `[lo, hi]`. -/
@[expose] def farthest (lo hi : ℚ) : ℚ := max (lo ^ 2) (hi ^ 2)

/-- Lower bound for `R²` on the rectangle `[x₀, x₁] × [y₀, y₁]`. -/
@[expose] def r2lo (x0 x1 y0 y1 : ℚ) : ℚ := closest x0 x1 ^ 2 + closest y0 y1 ^ 2
/-- Upper bound for `R²` on the rectangle (intersected with the disc `r ≤ a`). -/
@[expose] def r2hi (x0 x1 y0 y1 : ℚ) : ℚ := min (aR ^ 2) (farthest x0 x1 + farthest y0 y1)
/-- Enclosure of `B` on the rectangle. -/
@[expose] def Bball (x0 x1 y0 y1 : ℚ) : QBall :=
  evalQ Bpoly [ivQ x0 x1, ivQ y0 y1, ivQ (r2lo x0 x1 y0 y1) (r2hi x0 x1 y0 y1), ⟨0, 1⟩]
/-- Fixed-point enclosures of all variables on the rectangle (`σ ∈ [−1, 1]`; only the cell
variables `x, y, R², B, 1/B` are used by `evalB`). -/
@[expose] def rectF (x0 x1 y0 y1 : ℚ) : List FBall :=
  [ofQ (ivQ x0 x1), ofQ (ivQ y0 y1), ofQ (ivQ (r2lo x0 x1 y0 y1) (r2hi x0 x1 y0 y1)),
    ofQ ⟨0, 1⟩, ofQ ⟨0, 1⟩, ofQ (ivQ Wlo Whi), ofQ (ivQ (1 / Whi) (1 / Wlo)),
    ofQ (Bball x0 x1 y0 y1),
    ofQ (ivQ (1 / ((Bball x0 x1 y0 y1).c + (Bball x0 x1 y0 y1).r))
      (1 / ((Bball x0 x1 y0 y1).c - (Bball x0 x1 y0 y1).r))),
    ofQ (ivQ 0 Umax), ofQ ⟨0, 1⟩]

/-- `|c| + r ≤ A D` for a fixed-point ball. -/
@[expose] def boundOK (b : FBall) (A : ℕ) : Bool := decide (b.c.natAbs + b.r ≤ A * Dk)

/-- Rectangle check for a ball polynomial `S`: the rectangle misses the disc, or `B > 0` on it
and the enclosure of `S` is bounded by `A`. -/
@[expose] def rectOK (S : BPoly) (A : ℕ) (x0 x1 y0 y1 : ℚ) : Bool :=
  decide (aR ^ 2 < r2lo x0 x1 y0 y1) ||
    (decide (0 < (Bball x0 x1 y0 y1).c - (Bball x0 x1 y0 y1).r) &&
      boundOK (evalB S (rectF x0 x1 y0 y1)) A)

/-- Global enclosures (whole region, `σ ∈ [−1, 1]`). -/
@[expose] def globalF : List FBall :=
  [ofQ ⟨0, aR⟩, ofQ ⟨0, aR⟩, ofQ (ivQ 0 (aR ^ 2)), ofQ ⟨0, 1⟩, ofQ ⟨0, 1⟩, ofQ (ivQ Wlo Whi),
    ofQ (ivQ (1 / Whi) (1 / Wlo)), ofQ (ivQ Bmin Bmax), ofQ (ivQ (1 / Bmax) (1 / Bmin)),
    ofQ (ivQ 0 Umax), ofQ ⟨0, 1⟩]

/-- Global enclosures with the sign fixed, `σ = sg` (input of `stage1`). -/
@[expose] def globalS (sg : ℚ) : List FBall :=
  [ofQ ⟨0, aR⟩, ofQ ⟨0, aR⟩, ofQ (ivQ 0 (aR ^ 2)), ofQ ⟨0, 1⟩, ofQ ⟨0, 1⟩, ofQ (ivQ Wlo Whi),
    ofQ (ivQ (1 / Whi) (1 / Wlo)), ofQ (ivQ Bmin Bmax), ofQ (ivQ (1 / Bmax) (1 / Bmin)),
    ofQ (ivQ 0 Umax), ⟨⌊sg * Dk⌋, 1⟩]

/-- The cell variables `x, y, R², B, 1/B` (the others are enclosed once by `stage1`). -/
@[expose] def cellMask : List Bool :=
  [true, true, true, false, false, false, false, true, true, false, false]

/-- Region constraints on the state variables (radius `≤ a`, passing speed range, field range,
`U ≤ U_max`, `σ = ±1`, and the identities linking `R²`, `1/W`, `B`, `1/B`). -/
@[expose] def InRegion (x : ℕ → ℝ) : Prop :=
  |x 0| ≤ 17 / 10 ∧ |x 1| ≤ 17 / 10 ∧ x 2 = x 0 ^ 2 + x 1 ^ 2 ∧ x 2 ≤ (17 / 10) ^ 2 ∧
  |x 3| ≤ 1 ∧ |x 4| ≤ 1 ∧ 112 / 100 ≤ x 5 ∧ x 5 ≤ 13 / 10 ∧ x 6 = (x 5)⁻¹ ∧
  x 7 = eval Bpoly x ∧ 493 / 100 ≤ x 7 ∧ x 7 ≤ 647 / 100 ∧ x 8 = (x 7)⁻¹ ∧
  0 ≤ x 9 ∧ x 9 ≤ 21612 / 10000 ∧ (x 10 = 1 ∨ x 10 = -1) ∧ ∀ i, 11 ≤ i → x i = 0

/-- `closest lo hi` gives a lower bound for `x²` on `[lo, hi]`. -/
theorem closest_sq_le {lo hi : ℚ} {x : ℝ} (h1 : (lo : ℝ) ≤ x) (h2 : x ≤ hi) :
    ((closest lo hi : ℚ) : ℝ) ^ 2 ≤ x ^ 2 := by
  unfold closest
  split_ifs with ha hb
  · have : (0 : ℝ) < lo := by exact_mod_cast ha
    nlinarith
  · have : (hi : ℝ) < 0 := by exact_mod_cast hb
    nlinarith
  · simp only [Rat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity

/-- `farthest lo hi` gives an upper bound for `x²` on `[lo, hi]`. -/
theorem sq_le_farthest {lo hi : ℚ} {x : ℝ} (h1 : (lo : ℝ) ≤ x) (h2 : x ≤ hi) :
    x ^ 2 ≤ ((farthest lo hi : ℚ) : ℝ) := by
  unfold farthest
  push_cast
  rcases le_total 0 x with hx | hx
  · exact le_max_of_le_right (by nlinarith)
  · exact le_max_of_le_left (by nlinarith)

/-- Ball for the reciprocal of a positive interval. -/
theorem inv_mem_ivQ {x : ℝ} {l h : ℚ} (hl : (0 : ℝ) < l) (h1 : (l : ℝ) ≤ x) (h2 : x ≤ h) :
    (ivQ (1 / h) (1 / l)).Mem x⁻¹ := by
  have hx : 0 < x := lt_of_lt_of_le hl h1
  refine QBall.mem_ivQ ?_ ?_
  · push_cast; rw [one_div]; exact inv_anti₀ hx h2
  · push_cast; rw [one_div]; exact inv_anti₀ hl h1

/-- The zero ball contains `0`. -/
theorem FBall.mem_zero : (FBall.mk 0 0).Mem 0 := by simp [FBall.Mem]

/-- **Rectangle soundness**: on a checked rectangle, `|amp 3 (x)/q| ≤ A` at every point of the
region, provided `amp 3 (x)/q` is a value of the ball polynomial `S` at `x`. -/
theorem rect_sound {S : BPoly} {A : ℕ} {x0 x1 y0 y1 : ℚ} (hok : rectOK S A x0 x1 y0 y1 = true)
    {x : ℕ → ℝ} (hx : InRegion x) (hS : S.Holds (eval (amp 3) x / cq) x)
    (hxi : (x0 : ℝ) ≤ x 0 ∧ x 0 ≤ x1) (hyj : (y0 : ℝ) ≤ x 1 ∧ x 1 ≤ y1) :
    |eval (amp 3) x / cq| ≤ A := by
  obtain ⟨hx0, hx1, hx2, hx2a, hx3, hx4, hx5l, hx5h, hx6, hx7, hx7l, hx7h, hx8, hx9l, hx9h,
    hx10, hx11⟩ := hx
  have hr2l : ((r2lo x0 x1 y0 y1 : ℚ) : ℝ) ≤ x 2 := by
    rw [hx2, r2lo]; push_cast
    exact add_le_add (closest_sq_le hxi.1 hxi.2) (closest_sq_le hyj.1 hyj.2)
  have hr2h : x 2 ≤ ((r2hi x0 x1 y0 y1 : ℚ) : ℝ) := by
    unfold r2hi; push_cast
    refine le_min (by simpa [aR] using hx2a) ?_
    rw [hx2]
    exact add_le_add (sq_le_farthest hxi.1 hxi.2) (sq_le_farthest hyj.1 hyj.2)
  simp only [rectOK, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
  rcases hok with hc | ⟨hBpos, hbd⟩
  · exfalso
    have : ((aR ^ 2 : ℚ) : ℝ) < r2lo x0 x1 y0 y1 := by exact_mod_cast hc
    push_cast [aR] at this
    linarith
  -- memberships of all variables
  have hxb : (ivQ x0 x1).Mem (x 0) := QBall.mem_ivQ hxi.1 hxi.2
  have hyb : (ivQ y0 y1).Mem (x 1) := QBall.mem_ivQ hyj.1 hyj.2
  have hrb : (ivQ (r2lo x0 x1 y0 y1) (r2hi x0 x1 y0 y1)).Mem (x 2) := QBall.mem_ivQ hr2l hr2h
  have hCb : (QBall.mk 0 1).Mem (x 3) := QBall.mem_of_abs_le (by simpa using hx3)
  have hBb : (Bball x0 x1 y0 y1).Mem (x 7) := by
    set x' : ℕ → ℝ := fun k => if k < 4 then x k else 0
    have hev : eval Bpoly x' = eval Bpoly x := by simp [eval_Bpoly, x']
    rw [hx7, ← hev]
    refine QBall.mem_eval Bpoly fun k => ?_
    match k with
    | 0 => simpa [x'] using hxb
    | 1 => simpa [x'] using hyb
    | 2 => simpa [x'] using hrb
    | 3 => simpa [x'] using hCb
    | n + 4 => simp [x', QBall.Mem]
  obtain ⟨hBl, hBh⟩ := QBall.bounds_of_mem hBb
  have hBpos' : (0 : ℝ) < (((Bball x0 x1 y0 y1).c - (Bball x0 x1 y0 y1).r : ℚ) : ℝ) := by
    exact_mod_cast hBpos
  have hall : ∀ k, ((rectF x0 x1 y0 y1).getD k ⟨0, 0⟩).Mem (x k) := by
    intro k
    match k with
    | 0 => exact FBall.mem_ofQ hxb
    | 1 => exact FBall.mem_ofQ hyb
    | 2 => exact FBall.mem_ofQ hrb
    | 3 => exact FBall.mem_ofQ hCb
    | 4 => exact FBall.mem_ofQ (QBall.mem_of_abs_le (by simpa using hx4))
    | 5 =>
      exact FBall.mem_ofQ
        (QBall.mem_ivQ (by simpa [Wlo] using hx5l) (by simpa [Whi] using hx5h))
    | 6 =>
      simp only [rectF, List.getD_cons_succ, List.getD_cons_zero]
      rw [hx6]
      exact FBall.mem_ofQ (inv_mem_ivQ (by norm_num [Wlo])
        (by simpa [Wlo] using hx5l) (by simpa [Whi] using hx5h))
    | 7 => exact FBall.mem_ofQ hBb
    | 8 =>
      simp only [rectF, List.getD_cons_succ, List.getD_cons_zero]
      rw [hx8]
      exact FBall.mem_ofQ (inv_mem_ivQ hBpos' hBl hBh)
    | 9 => exact FBall.mem_ofQ (QBall.mem_ivQ (by simpa using hx9l) (by simpa [Umax] using hx9h))
    | 10 => exact FBall.mem_ofQ (QBall.mem_of_abs_le (by rcases hx10 with h | h <;> simp [h]))
    | n + 11 =>
      rw [hx11 (n + 11) (by omega)]
      simpa [rectF] using FBall.mem_zero
  exact FBall.abs_le_of_mem (FBall.mem_evalB S hall hS) (by simpa [boundOK] using hbd)

/-- Memberships of a region point in the global enclosures `globalF`. -/
theorem globalF_mem {x : ℕ → ℝ} (hx : InRegion x) : ∀ k, (globalF.getD k ⟨0, 0⟩).Mem (x k) := by
  obtain ⟨hx0, hx1, hx2, hx2a, hx3, hx4, hx5l, hx5h, hx6, hx7, hx7l, hx7h, hx8, hx9l, hx9h,
    hx10, hx11⟩ := hx
  intro k
  match k with
  | 0 => exact FBall.mem_ofQ (QBall.mem_of_abs_le (by simpa [aR] using hx0))
  | 1 => exact FBall.mem_ofQ (QBall.mem_of_abs_le (by simpa [aR] using hx1))
  | 2 => exact FBall.mem_ofQ (QBall.mem_ivQ (by rw [hx2]; push_cast; positivity)
      (by simpa [aR] using hx2a))
  | 3 => exact FBall.mem_ofQ (QBall.mem_of_abs_le (by simpa using hx3))
  | 4 => exact FBall.mem_ofQ (QBall.mem_of_abs_le (by simpa using hx4))
  | 5 =>
    exact FBall.mem_ofQ
      (QBall.mem_ivQ (by simpa [Wlo] using hx5l) (by simpa [Whi] using hx5h))
  | 6 =>
    simp only [globalF, List.getD_cons_succ, List.getD_cons_zero]
    rw [hx6]
    exact FBall.mem_ofQ (inv_mem_ivQ (by norm_num [Wlo])
      (by simpa [Wlo] using hx5l) (by simpa [Whi] using hx5h))
  | 7 =>
    exact FBall.mem_ofQ
      (QBall.mem_ivQ (by simpa [Bmin] using hx7l) (by simpa [Bmax] using hx7h))
  | 8 =>
    simp only [globalF, List.getD_cons_succ, List.getD_cons_zero]
    rw [hx8]
    exact FBall.mem_ofQ (inv_mem_ivQ (by norm_num [Bmin])
      (by simpa [Bmin] using hx7l) (by simpa [Bmax] using hx7h))
  | 9 => exact FBall.mem_ofQ (QBall.mem_ivQ (by simpa using hx9l) (by simpa [Umax] using hx9h))
  | 10 => exact FBall.mem_ofQ (QBall.mem_of_abs_le (by rcases hx10 with h | h <;> simp [h]))
  | n + 11 =>
    rw [hx11 (n + 11) (by omega)]
    simpa [globalF] using FBall.mem_zero

/-- Memberships of a region point with `σ = sg` in the enclosures `globalS sg`. -/
theorem globalS_mem {x : ℕ → ℝ} (hx : InRegion x) {sg : ℚ} (hsg : x 10 = sg) :
    ∀ k, ((globalS sg).getD k ⟨0, 0⟩).Mem (x k) := by
  intro k
  rcases Nat.lt_or_ge k 10 with hk | hk
  · have h := globalF_mem hx k
    interval_cases k <;> simpa [globalF, globalS] using h
  · rcases Nat.lt_or_ge k 11 with hk' | hk'
    · obtain rfl : k = 10 := by omega
      simpa [globalS, hsg] using FBall.mem_coeff sg
    · have h := globalF_mem hx k
      have e1 : globalF.getD k ⟨0, 0⟩ = ⟨0, 0⟩ :=
        List.getD_eq_default _ _ (by simp [globalF]; omega)
      have e2 : (globalS sg).getD k ⟨0, 0⟩ = ⟨0, 0⟩ :=
        List.getD_eq_default _ _ (by simp [globalS]; omega)
      rw [e2]; rw [e1] at h; exact h

/-- Soundness of the global enclosure on the region. -/
theorem global_bound {j A : ℕ} (hok : boundOK (evalT (toFix cq (amp j)) globalF) A = true)
    {x : ℕ → ℝ} (hx : InRegion x) : |eval (amp j) x| ≤ A * cq := by
  have hm := FBall.mem_evalT_toFix cq (by norm_num [cq]) (amp j) (globalF_mem hx)
  have := FBall.abs_le_of_mem hm (by simpa [boundOK] using hok)
  have hq : (0 : ℝ) < cq := by norm_num [cq]
  rw [abs_div, abs_of_pos hq, div_le_iff₀ hq] at this
  exact this

/-! ### Adaptive cover certificates

`CoverCert S A x₀ x₁ y₀ y₁` certifies `rectOK S A` on the leaves of a binary subdivision of the
rectangle (bisecting in `x` or in `y`). The subdivision plan is found by an untrusted search
(a floating-point evaluation of the same enclosures) and passed to the `meta` proof builder
`cover_cert` as a string (`X`/`Y`: bisect in `x`/`y`, `L`: leaf); every leaf becomes a goal
`rectOK S A x₀ x₁ y₀ y₁ = true`, closed by a small kernel computation. -/

/-- Certificate that `rectOK S A` holds on every leaf of a binary subdivision. -/
inductive CoverCert (S : BPoly) (A : ℕ) : ℚ → ℚ → ℚ → ℚ → Prop where
  | leaf (x0 x1 y0 y1 : ℚ) : rectOK S A x0 x1 y0 y1 = true → CoverCert S A x0 x1 y0 y1
  | splitX (x0 xm x1 y0 y1 : ℚ) : CoverCert S A x0 xm y0 y1 → CoverCert S A xm x1 y0 y1 →
      CoverCert S A x0 x1 y0 y1
  | splitY (x0 x1 y0 ym y1 : ℚ) : CoverCert S A x0 x1 y0 ym → CoverCert S A x0 x1 ym y1 →
      CoverCert S A x0 x1 y0 y1

/-- **Soundness of a cover certificate.** -/
theorem CoverCert.sound {S : BPoly} {A : ℕ} {x0 x1 y0 y1 : ℚ} (h : CoverCert S A x0 x1 y0 y1) :
    ∀ x : ℕ → ℝ, InRegion x → S.Holds (eval (amp 3) x / cq) x →
      ((x0 : ℝ) ≤ x 0 ∧ x 0 ≤ x1) → ((y0 : ℝ) ≤ x 1 ∧ x 1 ≤ y1) →
      |eval (amp 3) x / cq| ≤ A := by
  induction h with
  | leaf x0 x1 y0 y1 hok => exact fun x hx hS hxi hyj => rect_sound hok hx hS hxi hyj
  | splitX x0 xm x1 y0 y1 _ _ ih1 ih2 =>
    intro x hx hS hxi hyj
    rcases le_total (x 0) xm with h | h
    · exact ih1 x hx hS ⟨hxi.1, h⟩ hyj
    · exact ih2 x hx hS ⟨h, hxi.2⟩ hyj
  | splitY x0 x1 y0 ym y1 _ _ ih1 ih2 =>
    intro x hx hS hxi hyj
    rcases le_total (x 1) ym with h | h
    · exact ih1 x hx hS hxi ⟨hyj.1, h⟩
    · exact ih2 x hx hS hxi ⟨h, hyj.2⟩

open Lean Meta Elab Tactic in
/-- Proof builder for `CoverCert` from a plan (`meta`, outside the trusted kernel): returns the
proof term, the unused plan suffix and the leaf goals. -/
meta partial def mkCoverCert (S A : Expr) (plan : List Char) (x0 x1 y0 y1 : Expr) :
    MetaM (Expr × List Char × List MVarId) := do
  let mid (a b : Expr) : MetaM Expr := do
    mkAppM ``HDiv.hDiv #[← mkAppM ``HAdd.hAdd #[a, b], ← mkNumeral (Lean.mkConst ``Rat) 2]
  match plan with
  | 'L' :: rest =>
    let ty ← mkEq (mkAppN (Lean.mkConst ``rectOK) #[S, A, x0, x1, y0, y1])
      (Lean.mkConst ``Bool.true)
    let mv ← mkFreshExprMVar ty
    return (← mkAppM ``CoverCert.leaf #[x0, x1, y0, y1, mv], rest, [mv.mvarId!])
  | 'X' :: rest =>
    let xm ← mid x0 x1
    let (p1, r1, g1) ← mkCoverCert S A rest x0 xm y0 y1
    let (p2, r2, g2) ← mkCoverCert S A r1 xm x1 y0 y1
    return (← mkAppM ``CoverCert.splitX #[x0, xm, x1, y0, y1, p1, p2], r2, g1 ++ g2)
  | 'Y' :: rest =>
    let ym ← mid y0 y1
    let (p1, r1, g1) ← mkCoverCert S A rest x0 x1 y0 ym
    let (p2, r2, g2) ← mkCoverCert S A r1 x0 x1 ym y1
    return (← mkAppM ``CoverCert.splitY #[x0, x1, y0, ym, y1, p1, p2], r2, g1 ++ g2)
  | _ => throwError "cover_cert: malformed plan"

open Lean Meta Elab Tactic in
/-- `cover_cert "plan"` proves a goal `CoverCert S A x₀ x₁ y₀ y₁` from a subdivision plan,
leaving one goal `rectOK S A … = true` per leaf. -/
elab "cover_cert" s:str : tactic => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let_expr CoverCert S A x0 x1 y0 y1 := ty | throwError "cover_cert: expected a CoverCert goal"
  let plan := s.getString.toList.filter (!·.isWhitespace)
  let (pf, rest, gs) ← mkCoverCert S A plan x0 x1 y0 y1
  unless rest.isEmpty do throwError "cover_cert: unused plan suffix"
  g.assign (← mkExpectedTypeHint pf ty)
  replaceMainGoal gs

/-! ### Kernel-checked certificates

Each `decide +kernel` below evaluates exact `ℚ`/`ℤ`/`ℕ` arithmetic in the Lean kernel. The
expensive step, the exact Lie derivatives `amp 3` (458 monomials), is evaluated **once**
(`amp3Lit_eq`); `stage1` is evaluated once per sign of `σ` (`S3pos_eq`, `S3neg_eq`); each of the
`324` leaves of the cover then only evaluates a `214`-term ball polynomial in the cell variables.
The literals are produced by the `fpoly%`/`bpoly%` parsers and are checked against the computed
values by these equations. -/

/-- `toFix q (amp 3)`, the third amplitude divided by `q` in fixed point, as a literal. -/
@[expose] def amp3Lit : FPoly := fpoly% "-39875691874650367 0 0 1 0 1 0 0 0 4 2 0;
1806289974354 0 0 1 0 1 0 4 0 2 4 0;
-3179544117593871500 0 0 1 0 1 2 0 0 5 1 0;
-70423722660586659838 0 0 1 0 1 4 0 0 6 0 0;
425764945603407326 0 0 2 0 1 0 0 0 1 1 0;
-1023611650677857 0 0 2 0 1 0 1 0 3 2 1;
-3203793591910902 0 0 2 0 1 0 2 0 0 2 0;
6846637341225 0 0 2 0 1 0 3 0 2 3 1;
-257597684667 0 0 2 0 1 0 5 0 1 4 1;
-332522291946002879 0 0 2 0 1 1 0 0 4 1 1;
28290803340509606633 0 0 2 0 1 2 0 0 2 0 0;
-11047554366468026630 0 0 2 0 1 3 0 0 5 0 1;
1647710339485186 0 0 3 1 1 0 0 0 2 1 0;
-12398681200696 0 0 3 1 1 0 2 0 1 2 0;
186595048695 0 0 3 1 1 0 4 0 0 3 0;
109485408927772177 0 0 3 1 1 2 0 0 3 0 0;
-944687261305 0 0 4 0 3 0 0 0 3 1 0;
7108577221 0 0 4 0 3 0 2 0 2 2 0;
-106981162 0 0 4 0 3 0 4 0 1 3 0;
2012528 0 0 4 0 3 0 6 0 0 4 0;
-62771634451923 0 0 4 0 3 2 0 0 4 0 0;
601929410801556595 0 1 0 0 0 0 0 0 3 2 0;
-11153138283172557217 0 1 0 0 0 0 0 0 4 2 0;
279745951821449770 0 1 0 0 0 0 1 0 1 2 1;
-5195150071454585 0 1 0 0 0 0 1 0 4 3 1;
3019596624886784 0 1 0 0 0 0 2 0 2 3 0;
-19546217554798 0 1 0 0 0 0 3 0 3 4 1;
505215105152694 0 1 0 0 0 0 4 0 2 4 0;
37176558521359745734 0 1 0 0 0 1 0 0 2 1 1;
-517803205196914161 0 1 0 0 0 1 0 0 5 2 1;
39996403559531031118 0 1 0 0 0 2 0 0 4 1 0;
-889311095402360291206 0 1 0 0 0 2 0 0 5 1 0;
1235135392034395512419 0 1 0 0 0 3 0 0 3 0 1;
-22937646383812903465 0 1 0 0 0 3 0 0 6 1 1;
885880342440052808234 0 1 0 0 0 4 0 0 5 0 0;
-19697351452066878089911 0 1 0 0 0 4 0 0 6 0 0;
-381034447316303999124 0 1 0 0 0 5 0 0 7 0 1;
-7229878397895792 0 1 0 1 0 0 0 0 3 2 0;
-52026529228830 0 1 0 1 0 0 1 0 4 3 1;
-36268898008417 0 1 0 1 0 0 2 0 2 3 0;
-195744462613 0 1 0 1 0 0 3 0 3 4 1;
-5185510181502034 0 1 0 1 0 1 0 0 5 2 1;
-480403729904981659 0 1 0 1 0 2 0 0 4 1 0;
-229707730020177101 0 1 0 1 0 3 0 0 6 1 1;
-10640462213665438759 0 1 0 1 0 4 0 0 5 0 0;
-3815847384162676956 0 1 0 1 0 5 0 0 7 0 1;
312449826374 0 1 0 2 0 0 1 0 4 3 1;
1175560320 0 1 0 2 0 0 3 0 3 4 1;
31142030419635 0 1 0 2 0 1 0 0 5 2 1;
1379529663528996 0 1 0 2 0 3 0 0 6 1 1;
22916401888127808 0 1 0 2 0 5 0 0 7 0 1;
3711262795268947801 0 1 1 0 0 0 0 0 1 1 0;
-43076063859214934 0 1 1 0 0 0 0 0 4 2 0;
20029810150415803 0 1 1 0 0 0 1 0 2 2 1;
-200411258741669812 0 1 1 0 0 0 1 0 3 2 1;
-27926488744931659 0 1 1 0 0 0 2 0 0 2 0;
-301440398368863 0 1 1 0 0 0 3 0 1 3 1;
1340491979349756 0 1 1 0 0 0 3 0 2 3 1;
1951260495445 0 1 1 0 0 0 4 0 2 4 0;
-50434631335868 0 1 1 0 0 0 5 0 1 4 1;
5323683180258715589 0 1 1 0 0 1 0 0 3 1 1;
-65103998224748921688 0 1 1 0 0 1 0 0 4 1 1;
246602278957235774588 0 1 1 0 0 2 0 0 2 0 0;
-3434730258303905610 0 1 1 0 0 2 0 0 5 1 0;
176871388139325437378 0 1 1 0 0 3 0 0 4 0 1;
-2162982685019945799699 0 1 1 0 0 3 0 0 5 0 1;
-76075840491173205350 0 1 1 0 0 4 0 0 6 0 0;
-431382744407783 0 1 1 1 0 0 0 0 4 2 0;
15970746971344840 0 1 1 1 0 0 1 0 2 2 1;
-240353168259588 0 1 1 1 0 0 3 0 1 3 1;
19540785117 0 1 1 1 0 0 4 0 2 4 0;
4244832896019802375 0 1 1 1 0 1 0 0 3 1 1;
-34396907061196687 0 1 1 1 0 2 0 0 5 1 0;
141028205720913904206 0 1 1 1 0 3 0 0 4 0 1;
-761857094498445416 0 1 1 1 0 4 0 0 6 0 0;
2590706425912 0 1 1 2 0 0 0 0 4 2 0;
-117353878 0 1 1 2 0 0 4 0 2 4 0;
206573603859142 0 1 1 2 0 2 0 0 5 1 0;
4575398751876138 0 1 1 2 0 4 0 0 6 0 0;
-24398049377317 0 1 2 0 2 0 1 0 3 2 1;
279756648182 0 1 2 0 2 0 3 0 2 3 1;
-6578472509 0 1 2 0 2 0 5 0 1 4 1;
-8955073985192745 0 1 2 0 2 1 0 0 4 1 1;
-297518900547051153 0 1 2 0 2 3 0 0 5 0 1;
322602525048647334 0 1 2 1 0 0 0 0 2 1 0;
-2427517608384482 0 1 2 1 0 0 2 0 1 2 0;
36533140824784 0 1 2 1 0 0 4 0 0 3 0;
21435969981907469456 0 1 2 1 0 2 0 0 3 0 0;
-554876343083674 0 1 3 0 2 0 0 0 3 1 0;
4175330286421 0 1 3 0 2 0 2 0 2 2 0;
-62837002219 0 1 3 0 2 0 4 0 1 3 0;
1182088774 0 1 3 0 2 0 6 0 0 4 0;
-36869868368880848 0 1 3 0 2 2 0 0 4 0 0;
-2833933021303985 0 2 0 0 1 0 0 0 3 2 0;
-45572219285314705 0 2 0 0 1 0 0 0 4 2 0;
-14216508502035 0 2 0 0 1 0 2 0 2 3 0;
2064331399262 0 2 0 0 1 0 4 0 2 4 0;
-188306347466585834 0 2 0 0 1 2 0 0 4 1 0;
-3633764705821567428 0 2 0 0 1 2 0 0 5 1 0;
-4170797290037409627 0 2 0 0 1 4 0 0 5 0 0;
-80484254469241896958 0 2 0 0 1 4 0 0 6 0 0;
-998489067839438 0 2 1 0 1 0 0 0 4 2 0;
471509942670226 0 2 1 0 1 0 1 0 2 2 1;
-7506485438304278 0 2 1 0 1 0 1 0 3 2 1;
-7096030560752 0 2 1 0 1 0 3 0 1 3 1;
95852922777150 0 2 1 0 1 0 3 0 2 3 1;
45229579925 0 2 1 0 1 0 4 0 2 4 0;
-2060781477336 0 2 1 0 1 0 5 0 1 4 1;
125321684642434235 0 2 1 0 1 1 0 0 3 1 1;
-2841554131174933688 0 2 1 0 1 1 0 0 4 1 1;
-79615923708872491 0 2 1 0 1 2 0 0 5 1 0;
4163624989717913818 0 2 1 0 1 3 0 0 4 0 1;
-94406373677090409376 0 2 1 0 1 3 0 0 5 0 1;
-1763413094227816790 0 2 1 0 1 4 0 0 6 0 0;
-14216897323542 0 2 1 1 1 0 0 0 4 2 0;
643997330 0 2 1 1 1 0 4 0 2 4 0;
-1133604211748847 0 2 1 1 1 2 0 0 5 1 0;
-25108199686025206 0 2 1 1 1 4 0 0 6 0 0;
11259555799066322 0 2 2 0 1 0 0 0 2 1 0;
-108638335925282282 0 2 2 0 1 0 0 0 3 1 0;
-25631280483554 0 2 2 0 1 0 1 0 3 2 1;
-84725840136247 0 2 2 0 1 0 2 0 1 2 0;
817481119729124 0 2 2 0 1 0 2 0 2 2 0;
171440098347 0 2 2 0 1 0 3 0 2 3 1;
1275089020365 0 2 2 0 1 0 4 0 0 3 0;
-12302754371592 0 2 2 0 1 0 4 0 1 3 0;
-6450257286 0 2 2 0 1 0 5 0 1 4 1;
231439236752 0 2 2 0 1 0 6 0 0 4 0;
-8326372727643331 0 2 2 0 1 1 0 0 4 1 1;
748163704180559948 0 2 2 0 1 2 0 0 3 0 0;
-7218691507227231785 0 2 2 0 1 2 0 0 4 0 0;
-276631244316858195 0 2 2 0 1 3 0 0 5 0 1;
-364948695627 0 2 2 1 1 0 1 0 3 2 1;
2441034512 0 2 2 1 1 0 3 0 2 3 1;
-91841412 0 2 2 1 1 0 5 0 1 4 1;
-118554313671743 0 2 2 1 1 1 0 0 4 1 1;
-3938789240273147 0 2 2 1 1 3 0 0 5 0 1;
-279275070207090924 0 3 0 0 0 0 0 0 4 2 0;
166169095381941163 0 3 0 0 0 0 1 0 2 2 1;
-534430023311119499 0 3 0 0 0 0 1 0 3 2 1;
-2500776489261234 0 3 0 0 0 0 3 0 1 3 1;
8042951876098537 0 3 0 0 0 0 3 0 2 3 1;
12650608320178 0 3 0 0 0 0 4 0 2 4 0;
-151303894007603 0 3 0 0 0 0 5 0 1 4 1;
44165751523375377932 0 3 0 0 0 1 0 0 3 1 1;
-213067630553723743706 0 3 0 0 0 1 0 0 4 1 1;
-22268388708060684700 0 3 0 0 0 2 0 0 5 1 0;
1467340845736861868753 0 3 0 0 0 3 0 0 4 0 1;
-7078852423701640799015 0 3 0 0 0 3 0 0 5 0 1;
-493222541494836105412 0 3 0 0 0 4 0 0 6 0 0;
-3976433118842686 0 3 0 1 0 0 0 0 4 2 0;
180124555552 0 3 0 1 0 0 4 0 2 4 0;
-317066461737287895 0 3 0 1 0 2 0 0 5 1 0;
-7022705061019189581 0 3 0 1 0 4 0 0 6 0 0;
2204490100389754994 0 3 1 0 0 0 0 0 2 1 0;
-7090040979235341108 0 3 1 0 0 0 0 0 3 1 0;
-5018306680534624 0 3 1 0 0 0 1 0 3 2 1;
-16588334314489406 0 3 1 0 0 0 2 0 1 2 0;
53351099216182379 0 3 1 0 0 0 2 0 2 2 0;
33565977766972 0 3 1 0 0 0 3 0 2 3 1;
249647603571107 0 3 1 0 0 0 4 0 0 3 0;
-802912083558060 0 3 1 0 0 0 4 0 1 3 0;
-1262885373568 0 3 1 0 0 0 5 0 1 4 1;
15104370467403 0 3 1 0 0 0 6 0 0 4 0;
-1630206961785033395 0 3 1 0 0 1 0 0 4 1 1;
146481753700598050105 0 3 1 0 0 2 0 0 3 0 0;
-471111952947250710604 0 3 1 0 0 2 0 0 4 0 0;
-54161180994865056978 0 3 1 0 0 3 0 0 5 0 1;
-71452711014235 0 3 1 1 0 0 1 0 3 2 1;
477926173503 0 3 1 1 0 0 3 0 2 3 1;
-17981480485 0 3 1 1 0 0 5 0 1 4 1;
-23211556078396171 0 3 1 1 0 1 0 0 4 1 1;
-771169133370595183 0 3 1 1 0 3 0 0 5 0 1;
-17132413265155905 1 0 0 0 1 0 0 0 3 2 0;
-85945255944116 1 0 0 0 1 0 2 0 2 3 0;
-1138397464229814358 1 0 0 0 1 2 0 0 4 1 0;
-25214365435226158195 1 0 0 0 1 4 0 0 5 0 0;
7155637940413449 1 0 1 0 1 0 0 0 4 2 0;
2850491926142734 1 0 1 0 1 0 1 0 2 2 1;
-42898730208177 1 0 1 0 1 0 3 0 1 3 1;
-324136246025 1 0 1 0 1 0 4 0 2 4 0;
757626548065625150 1 0 1 0 1 1 0 0 3 1 1;
570564809071982955 1 0 1 0 1 2 0 0 5 1 0;
25171005619658297172 1 0 1 0 1 3 0 0 4 0 1;
12637439956135350487 1 0 1 0 1 4 0 0 6 0 0;
-85947606546866 1 0 1 1 1 0 0 0 4 2 0;
3893256586 1 0 1 1 1 0 4 0 2 4 0;
-6853152734663483 1 0 1 1 1 2 0 0 5 1 0;
-151790479920061473 1 0 1 1 1 4 0 0 6 0 0;
68069132785264587 1 0 2 0 1 0 0 0 2 1 0;
183685699720637 1 0 2 0 1 0 1 0 3 2 1;
-512206215369126 1 0 2 0 1 0 2 0 1 2 0;
-1228619633163 1 0 2 0 1 0 3 0 2 3 1;
7708492714029 1 0 2 0 1 0 4 0 0 3 0;
46225549428 1 0 2 0 1 0 5 0 1 4 1;
59670666925648636 1 0 2 0 1 1 0 0 4 1 1;
4522989666182476055 1 0 2 0 1 2 0 0 3 0 0;
1982468402604287485 1 0 2 0 1 3 0 0 5 0 1;
-2206280750835 1 0 2 1 1 0 1 0 3 2 1;
14757163191 1 0 2 1 1 0 3 0 2 3 1;
-555223080 1 0 2 1 1 0 5 0 1 4 1;
-716714714470082 1 0 2 1 1 1 0 0 4 1 1;
-23811771316196750 1 0 2 1 1 3 0 0 5 0 1;
152410235994110268 1 1 0 0 0 0 0 0 3 2 0;
3846295307680561085 1 1 0 0 0 0 0 0 4 2 0;
-185095065866823908 1 1 0 0 0 0 1 0 1 2 1;
1004567712990826124 1 1 0 0 0 0 1 0 2 2 1;
94545177600662 1 1 0 0 0 0 1 0 4 3 1;
764570439568930 1 1 0 0 0 0 2 0 2 3 0;
-15118330594170183 1 1 0 0 0 0 3 0 1 3 1;
355716501876 1 1 0 0 0 0 3 0 3 4 1;
-174229570097772 1 1 0 0 0 0 4 0 2 4 0;
-24598023683305696427 1 1 0 0 0 1 0 0 2 1 1;
267002043300405693867 1 1 0 0 0 1 0 0 3 1 1;
9423365124046829 1 1 0 0 0 1 0 0 5 2 1;
10127202951100645002 1 1 0 0 0 2 0 0 4 1 0;
306689741171340290901 1 1 0 0 0 2 0 0 5 1 0;
-817232439842306805210 1 1 0 0 0 3 0 0 3 0 1;
8870742385591028570193 1 1 0 0 0 3 0 0 4 0 1;
417436228265026471 1 1 0 0 0 3 0 0 6 1 1;
224307418163928186165 1 1 0 0 0 4 0 0 5 0 0;
6792871077204016103187 1 1 0 0 0 4 0 0 6 0 0;
6934346264881553494 1 1 0 0 0 5 0 0 7 0 1;
4783678939961125 1 1 0 1 0 0 0 0 3 2 0;
-24039345673003507 1 1 0 1 0 0 0 0 4 2 0;
-13173264930121 1 1 0 1 0 0 1 0 4 3 1;
23997466351433 1 1 0 1 0 0 2 0 2 3 0;
-49563053751 1 1 0 1 0 0 3 0 3 4 1;
1088934813111 1 1 0 1 0 0 4 0 2 4 0;
-1312985902217595 1 1 0 1 0 1 0 0 5 2 1;
317861114523596886 1 1 0 1 0 2 0 0 4 1 0;
-1916810882320876819 1 1 0 1 0 2 0 0 5 1 0;
-58162649496434980 1 1 0 1 0 3 0 0 6 1 1;
7040305825583147448 1 1 0 1 0 4 0 0 5 0 0;
-42455444232525100645 1 1 0 1 0 4 0 0 6 0 0;
-966183392772403776 1 1 0 1 0 5 0 0 7 0 1;
-206733719707 1 1 0 2 0 0 1 0 4 3 1;
-777814348 1 1 0 2 0 0 3 0 3 4 1;
-20605253209985 1 1 0 2 0 1 0 0 5 2 1;
-912771506695878 1 1 0 2 0 3 0 0 6 1 1;
-15162732076355242 1 1 0 2 0 5 0 0 7 0 1;
-2455572375817048170 1 1 1 0 0 0 0 0 1 1 0;
13327144697810791556 1 1 1 0 0 0 0 0 2 1 0;
783930021633939 1 1 1 0 0 0 0 0 4 2 0;
5071604804750975 1 1 1 0 0 0 1 0 2 2 1;
69114258653768837 1 1 1 0 0 0 1 0 3 2 1;
18477676763563804 1 1 1 0 0 0 2 0 0 2 0;
-100284021083049586 1 1 1 0 0 0 2 0 1 2 0;
-76325564807305 1 1 1 0 0 0 3 0 1 3 1;
-462284953279515 1 1 1 0 0 0 3 0 2 3 1;
1509233239770788 1 1 1 0 0 0 4 0 0 3 0;
-35510479496 1 1 1 0 0 0 4 0 2 4 0;
17392995668710 1 1 1 0 0 0 5 0 1 4 1;
1347971697845152164 1 1 1 0 0 1 0 0 3 1 1;
22451905152194114346 1 1 1 0 0 1 0 0 4 1 1;
-163165417655915399728 1 1 1 0 0 2 0 0 2 0 0;
885548783735433666547 1 1 1 0 0 2 0 0 3 0 0;
62507757777012448 1 1 1 0 0 2 0 0 5 1 0;
44784337703358412925 1 1 1 0 0 3 0 0 4 0 1;
745930870823921157991 1 1 1 0 0 3 0 0 5 0 1;
1384484327003048716 1 1 1 0 0 4 0 0 6 0 0;
-109227335795780 1 1 1 1 0 0 0 0 4 2 0;
-2522391377024068 1 1 1 1 0 0 1 0 2 2 1;
-431964116586056 1 1 1 1 0 0 1 0 3 2 1;
37960951992175 1 1 1 1 0 0 3 0 1 3 1;
2889280957996 1 1 1 1 0 0 3 0 2 3 1;
4947782277 1 1 1 1 0 0 4 0 2 4 0;
-108706222930 1 1 1 1 0 0 5 0 1 4 1;
-670421359316472887 1 1 1 1 0 1 0 0 3 1 1;
-140324407201213215 1 1 1 1 0 1 0 0 4 1 1;
-8709394537946555 1 1 1 1 0 2 0 0 5 1 0;
-22273744031250836948 1 1 1 1 0 3 0 0 4 0 1;
-4662067942649507238 1 1 1 1 0 3 0 0 5 0 1;
-192904379620978241 1 1 1 1 0 4 0 0 6 0 0;
-1714151620153 1 1 1 2 0 0 0 0 4 2 0;
77647678 1 1 1 2 0 0 4 0 2 4 0;
-136680279245147 1 1 1 2 0 2 0 0 5 1 0;
-3027331505000754 1 1 1 2 0 4 0 0 6 0 0;
4035767566172 1 1 2 0 2 0 1 0 3 2 1;
-46275535790 1 1 2 0 2 0 3 0 2 3 1;
1088168384 1 1 2 0 2 0 5 0 1 4 1;
1481290433640905 1 1 2 0 2 1 0 0 4 1 1;
49213652722068611 1 1 2 0 2 3 0 0 5 0 1;
-53362823692257454 1 1 2 1 0 0 0 0 2 1 0;
401544266048560 1 1 2 1 0 0 2 0 1 2 0;
-6043075925905 1 1 2 1 0 0 4 0 0 3 0;
-3545799545879431038 1 1 2 1 0 2 0 0 3 0 0;
91784056750682 1 1 3 0 2 0 0 0 3 1 0;
-690656137604 1 1 3 0 2 0 2 0 2 2 0;
10394090592 1 1 3 0 2 0 4 0 1 3 0;
-195533482 1 1 3 0 2 0 6 0 0 4 0;
6098775218912621 1 1 3 0 2 2 0 0 4 0 0;
15076523673337195 1 2 0 0 1 0 0 0 4 2 0;
-682936703516 1 2 0 0 1 0 4 0 2 4 0;
1202147722226683961 1 2 0 0 1 2 0 0 5 1 0;
26626369899598823053 1 2 0 0 1 4 0 0 6 0 0;
2483348566055550 1 2 1 0 1 0 1 0 3 2 1;
-31710741369885 1 2 1 0 1 0 3 0 2 3 1;
681762293253 1 2 1 0 1 0 5 0 1 4 1;
940063020839827686 1 2 1 0 1 1 0 0 4 1 1;
31232183772872015131 1 2 1 0 1 3 0 0 5 0 1;
35940502110619702 1 2 2 0 1 0 0 0 3 1 0;
-270444881714899 1 2 2 0 1 0 2 0 2 2 0;
4070084153007 1 2 2 0 1 0 4 0 1 3 0;
-76566364039 1 2 2 0 1 0 6 0 0 4 0;
2388138543744347357 1 2 2 0 1 2 0 0 4 0 0;
46195876274857145 1 3 0 0 0 0 0 0 4 2 0;
-27486617281223351 1 3 0 0 0 0 1 0 2 2 1;
265205876229578096 1 3 0 0 0 0 1 0 3 2 1;
413662276419151 1 3 0 0 0 0 3 0 1 3 1;
-3991239276860929 1 3 0 0 0 0 3 0 2 3 1;
-2092581827398 1 3 0 0 0 0 4 0 2 4 0;
75083135372193 1 3 0 0 0 0 5 0 1 4 1;
-7305613033941791839 1 3 0 0 0 1 0 0 3 1 1;
105732809146960654771 1 3 0 0 0 1 0 0 4 1 1;
3683492869002519273 1 3 0 0 0 2 0 0 5 1 0;
-242718034633165121148 1 3 0 0 0 3 0 0 4 0 1;
3512813984694047313796 1 3 0 0 0 3 0 0 5 0 1;
81585683555536799391 1 3 0 0 0 4 0 0 6 0 0;
657755854244654 1 3 0 1 0 0 0 0 4 2 0;
-29795039265 1 3 0 1 0 0 4 0 2 4 0;
52447083896393486 1 3 0 1 0 2 0 0 5 1 0;
1161650461221219329 1 3 0 1 0 4 0 0 6 0 0;
-364652497808831654 1 3 1 0 0 0 0 0 2 1 0;
3518366200222048970 1 3 1 0 0 0 0 0 3 1 0;
830095841892945 1 3 1 0 0 0 1 0 3 2 1;
2743934999389224 1 3 1 0 0 0 2 0 1 2 0;
-26474981565925091 1 3 1 0 0 0 2 0 2 2 0;
-5552266999049 1 3 1 0 0 0 3 0 2 3 1;
-41295092320033 1 3 1 0 0 0 4 0 0 3 0;
398437575299488 1 3 1 0 0 0 4 0 1 3 0;
208898332469 1 3 1 0 0 0 5 0 1 4 1;
-7495401886081 1 3 1 0 0 0 6 0 0 4 0;
269658294430607027 1 3 1 0 0 1 0 0 4 1 1;
-24230064521903436860 1 3 1 0 0 2 0 0 3 0 0;
233784878906154487968 1 3 1 0 0 2 0 0 4 0 0;
8958992345015272582 1 3 1 0 0 3 0 0 5 0 1;
11819245430926 1 3 1 1 0 0 1 0 3 2 1;
-79055457272 1 3 1 1 0 0 3 0 2 3 1;
2974380230 1 3 1 1 0 0 5 0 1 4 1;
3839505516727186 1 3 1 1 0 1 0 0 4 1 1;
127561811534985669 1 3 1 1 0 3 0 0 5 0 1;
2833933021303984 2 0 0 0 1 0 0 0 3 2 0;
14216508502034 2 0 0 0 1 0 2 0 2 3 0;
188306347466585833 2 0 0 0 1 2 0 0 4 1 0;
4170797290037409626 2 0 0 0 1 4 0 0 5 0 0;
-92575145362597 2 0 1 0 1 0 0 0 4 2 0;
-471509942670227 2 0 1 0 1 0 1 0 2 2 1;
7096030560751 2 0 1 0 1 0 3 0 1 3 1;
4193470986 2 0 1 0 1 0 4 0 2 4 0;
-125321684642434236 2 0 1 0 1 1 0 0 3 1 1;
-7381608820690165 2 0 1 0 1 2 0 0 5 1 0;
-4163624989717913819 2 0 1 0 1 3 0 0 4 0 1;
-163495253769466458 2 0 1 0 1 4 0 0 6 0 0;
14216897323541 2 0 1 1 1 0 0 0 4 2 0;
-643997331 2 0 1 1 1 0 4 0 2 4 0;
1133604211748846 2 0 1 1 1 2 0 0 5 1 0;
25108199686025205 2 0 1 1 1 4 0 0 6 0 0;
-11259555799066323 2 0 2 0 1 0 0 0 2 1 0;
-2376410111058 2 0 2 0 1 0 1 0 3 2 1;
84725840136246 2 0 2 0 1 0 2 0 1 2 0;
15895108456 2 0 2 0 1 0 3 0 2 3 1;
-1275089020366 2 0 2 0 1 0 4 0 0 3 0;
-598037100 2 0 2 0 1 0 5 0 1 4 1;
-771981577397395 2 0 2 0 1 1 0 0 4 1 1;
-748163704180559949 2 0 2 0 1 2 0 0 3 0 0;
-25647929936662350 2 0 2 0 1 3 0 0 5 0 1;
364948695626 2 0 2 1 1 0 1 0 3 2 1;
-2441034513 2 0 2 1 1 0 3 0 2 3 1;
91841411 2 0 2 1 1 0 5 0 1 4 1;
118554313671742 2 0 2 1 1 1 0 0 4 1 1;
3938789240273146 2 0 2 1 1 3 0 0 5 0 1;
-356954228807738730 2 1 0 0 0 0 0 0 4 2 0;
-332338190763882327 2 1 0 0 0 0 1 0 2 2 1;
5001552978522466 2 1 0 0 0 0 3 0 1 3 1;
16169320568174 2 1 0 0 0 0 4 0 2 4 0;
-88331503046750755866 2 1 0 0 0 1 0 0 3 1 1;
-28462245169905378458 2 1 0 0 0 2 0 0 5 1 0;
-2934681691473723737508 2 1 0 0 0 3 0 0 4 0 1;
-630410268268234227447 2 1 0 0 0 4 0 0 6 0 0;
7952866237685370 2 1 0 1 0 0 0 0 4 2 0;
-360249111105 2 1 0 1 0 0 4 0 2 4 0;
634132923474575789 2 1 0 1 0 2 0 0 5 1 0;
14045410122038379160 2 1 0 1 0 4 0 0 6 0 0;
-4408980200779509989 2 1 1 0 0 0 0 0 2 1 0;
-6414127081742929 2 1 1 0 0 0 1 0 3 2 1;
33176668628978810 2 1 1 0 0 0 2 0 1 2 0;
42902209993548 2 1 1 0 0 0 3 0 2 3 1;
-499295207142216 2 1 1 0 0 0 4 0 0 3 0;
-1614151503964 2 1 1 0 0 0 5 0 1 4 1;
-2083642010758353942 2 1 1 0 0 1 0 0 4 1 1;
-292963507401196100212 2 1 1 0 0 2 0 0 3 0 0;
-69225880344430172164 2 1 1 0 0 3 0 0 5 0 1;
142905422028469 2 1 1 1 0 0 1 0 3 2 1;
-955852347007 2 1 1 1 0 0 3 0 2 3 1;
35962960969 2 1 1 1 0 0 5 0 1 4 1;
46423112156792341 2 1 1 1 0 1 0 0 4 1 1;
1542338266741190364 2 1 1 1 0 3 0 0 5 0 1;
-1246930529373754 2 2 0 0 1 0 0 0 4 2 0;
56483486756 2 2 0 0 1 0 4 0 2 4 0;
-99425751462357321 2 2 0 0 1 2 0 0 5 1 0;
-2202180969139752283 2 2 0 0 1 4 0 0 6 0 0;
-205389731027151 2 2 1 0 1 0 1 0 3 2 1;
2622692895253 2 2 1 0 1 0 3 0 2 3 1;
-56386355082 2 2 1 0 1 0 5 0 1 4 1;
-77749573152166200 2 2 1 0 1 1 0 0 4 1 1;
-2583112943620993733 2 2 1 0 1 3 0 0 5 0 1;
-2972522730953510 2 2 2 0 1 0 0 0 3 1 0;
22367621795969 2 2 2 0 1 0 2 0 2 2 0;
-336623501377 2 2 2 0 1 0 4 0 1 3 0;
6332556424 2 2 2 0 1 0 6 0 0 4 0;
-197515217903667827 2 2 2 0 1 2 0 0 4 0 0;
-43868641180832468 2 3 0 0 0 0 1 0 3 2 1;
660204993164965 2 3 0 0 0 0 3 0 2 3 1;
-12419766753296 2 3 0 0 0 0 5 0 1 4 1;
-17489637603256649662 2 3 0 0 0 1 0 0 4 1 1;
-581066974911797300027 2 3 0 0 0 3 0 0 5 0 1;
-581985386502895319 2 3 1 0 0 0 0 0 3 1 0;
4379320259025202 2 3 1 0 0 0 2 0 2 2 0;
-65906967342773 2 3 1 0 0 0 4 0 1 3 0;
1239840913486 2 3 1 0 0 0 6 0 0 4 0;
-38671182976957885228 2 3 1 0 0 2 0 0 4 0 0;
4283061376476821 3 1 0 0 0 0 0 0 4 2 0;
27486617281223350 3 1 0 0 0 0 1 0 2 2 1;
-413662276419152 3 1 0 0 0 0 3 0 1 3 1;
-194014209163 3 1 0 0 0 0 4 0 2 4 0;
7305613033941791838 3 1 0 0 0 1 0 0 3 1 1;
341515895139306422 3 1 0 0 0 2 0 0 5 1 0;
242718034633165121147 3 1 0 0 0 3 0 0 4 0 1;
7564235561440497956 3 1 0 0 0 4 0 0 6 0 0;
-657755854244655 3 1 0 1 0 0 0 0 4 2 0;
29795039264 3 1 0 1 0 0 4 0 2 4 0;
-52447083896393487 3 1 0 1 0 2 0 0 5 1 0;
-1161650461221219330 3 1 0 1 0 4 0 0 6 0 0;
364652497808831653 3 1 1 0 0 0 0 0 2 1 0;
76962528387425 3 1 1 0 0 0 1 0 3 2 1;
-2743934999389225 3 1 1 0 0 0 2 0 1 2 0;
-514779721767 3 1 1 0 0 0 3 0 2 3 1;
41295092320032 3 1 1 0 0 0 4 0 0 3 0;
19368057315 3 1 1 0 0 0 5 0 1 4 1;
25001431271711909 3 1 1 0 0 1 0 0 4 1 1;
24230064521903436859 3 1 1 0 0 2 0 0 3 0 0;
830635051855720636 3 1 1 0 0 3 0 0 5 0 1;
-11819245430927 3 1 1 1 0 0 1 0 3 2 1;
79055457271 3 1 1 1 0 0 3 0 2 3 1;
-2974380231 3 1 1 1 0 0 5 0 1 4 1;
-3839505516727187 3 1 1 1 0 1 0 0 4 1 1;
-127561811534985670 3 1 1 1 0 3 0 0 5 0 1;
2418822320747654 3 3 0 0 0 0 1 0 3 2 1;
-36402280324886 3 3 0 0 0 0 3 0 2 3 1;
684799169354 3 3 0 0 0 0 5 0 1 4 1;
964340920480316522 3 3 0 0 0 1 0 0 4 1 1;
32038780571577795991 3 3 0 0 0 3 0 0 5 0 1;
32089419807177185 3 3 1 0 0 0 0 0 3 1 0;
-241466279946252 3 3 1 0 0 0 2 0 2 2 0;
3633968124162 3 3 1 0 0 0 4 0 1 3 0;
-68362155631 3 3 1 0 0 0 6 0 0 4 0;
2132245677927502443 3 3 1 0 0 2 0 0 4 0 0;"

/-- The literal is the computed amplitude (one kernel evaluation of `amp 3`). -/
theorem amp3Lit_eq : toFix cq (amp 3) = amp3Lit := by decide +kernel

/-- `stage1` of the third amplitude for `σ = +1`, as a literal. -/
@[expose] def S3pos : BPoly := bpoly% "3121820897053656326 481674298643822806 3 3 1 0 0 0 0 0 4 0 0;
-30705740374 724886428449 3 3 1 0 0 0 0 0 0 0 0;
2187116839886 21125654255995 3 3 1 0 0 0 0 0 1 0 0;
-194730692578441 704374205878132 3 3 1 0 0 0 0 0 2 0 0;
34675827043635666 34675827043635670 3 3 1 0 0 0 0 0 3 0 0;
56758654148164931839 13630546767591485998 3 3 0 0 0 0 0 0 5 0 0;
1260900826391946340 1448472850152731753 3 3 0 0 0 0 0 0 4 0 0;
370120426878 8107089675288 3 3 0 0 0 0 0 0 1 0 0;
-26363038590049 235189776277017 3 3 0 0 0 0 0 0 2 0 0;
2347242117790373 7740079380151733 3 3 0 0 0 0 0 0 3 0 0;
1471520663100572305 633637845768809458 3 1 1 0 0 0 0 0 5 0 0;
32690021424976385 48340320938350570 3 1 1 0 0 0 0 0 4 0 0;
-2212838311247986 8004518451154847 3 1 1 0 0 0 0 0 1 0 0;
394043116321576755 394047383066991027 3 1 1 0 0 0 0 0 2 0 0;
35475312151495297050 5473867141071947098 3 1 1 0 0 0 0 0 3 0 0;
24853600453265 240064252909006 3 1 1 0 0 0 0 0 0 0 0;
16214610705707918897 8707392363616211862 3 1 0 0 0 0 0 0 6 0 0;
540314503892579290 898606911700824068 3 1 0 0 0 0 0 0 5 0 0;
26673079704315950 87958424350624441 3 1 0 0 0 0 0 0 2 0 0;
429994805467943603725 103279794118303122752 3 1 0 0 0 0 0 0 4 0 0;
9552278987817775314 10973279167823725377 3 1 0 0 0 0 0 0 3 0 0;
-299579983977824 2672611094056878 3 1 0 0 0 0 0 0 1 0 0;
-56618478996564039761 8735820234494786297 2 3 1 0 0 0 0 0 4 0 0;
556890473144 13146803861156 2 3 1 0 0 0 0 0 0 0 0;
-39666346323413 383142547642780 2 3 1 0 0 0 0 0 1 0 0;
3531706651763536 12774786733880555 2 3 1 0 0 0 0 0 2 0 0;
-628893408655028682 628893408655028686 2 3 1 0 0 0 0 0 3 0 0;
-1029395591141718536558 247208552739500132350 2 3 0 0 0 0 0 0 5 0 0;
-22868155896835754105 26270030327769998550 2 3 0 0 0 0 0 0 4 0 0;
-6712638651129 147033126383538 2 3 0 0 0 0 0 0 1 0 0;
478129654428604 4265487306114762 2 3 0 0 0 0 0 0 2 0 0;
-42570436590834514 140376894212751831 2 3 0 0 0 0 0 0 3 0 0;
0 333800718257198631 2 2 2 0 0 0 0 0 4 0 0;
0 69992381007 2 2 2 0 0 0 0 0 0 0 0;
0 2159519942111 2 2 2 0 0 0 0 0 1 0 0;
0 83286321916490 2 2 2 0 0 0 0 0 2 0 0;
0 6424216126136729 2 2 2 0 0 0 0 0 3 0 0;
0 5675099137135323240 2 2 1 0 0 0 0 0 5 0 0;
0 218442090745400073 2 2 1 0 0 0 0 0 4 0 0;
0 698013374323 2 2 1 0 0 0 0 0 1 0 0;
0 18844223580593 2 2 1 0 0 0 0 0 2 0 0;
0 856545861792089 2 2 1 0 0 0 0 0 3 0 0;
0 6289649065960046503 2 2 0 0 0 0 0 0 6 0 0;
0 363145398562154831 2 2 0 0 0 0 0 0 5 0 0;
0 783121672290 2 2 0 0 0 0 0 0 2 0 0;
0 5824144961290429 2 2 0 0 0 0 0 0 4 0 0;
-122637869808859060221 32839906479884423353 2 1 1 0 0 0 0 0 5 0 0;
-2724416103758827497 3260129662978650907 2 1 1 0 0 0 0 0 4 0 0;
26754481005441162 96798241923459891 2 1 1 0 0 0 0 0 1 0 0;
-4764312934584121418 4764628057690624876 2 1 1 0 0 0 0 0 2 0 0;
-428934095499926082321 66201577090191954150 2 1 1 0 0 0 0 0 3 0 0;
-300502623662215 2902595057899776 2 1 1 0 0 0 0 0 0 0 0;
-1351340396768884968272 489289466281572624192 2 1 0 0 0 0 0 0 6 0 0;
-45030301949411096844 61242124097436462737 2 1 0 0 0 0 0 0 5 0 0;
-322492791578284499 1063679979948542071 2 1 0 0 0 0 0 0 2 0 0;
-5199384446182546901418 1249815632731715016691 2 1 0 0 0 0 0 0 4 0 0;
-115495736852705828809 132676920847323224980 2 1 0 0 0 0 0 0 3 0 0;
3622194351731854 32314297773596653 2 1 0 0 0 0 0 0 1 0 0;
0 65002022031727292 2 0 2 0 0 0 0 0 5 0 0;
0 2502014018112213 2 0 2 0 0 0 0 0 4 0 0;
0 315487032195805 2 0 2 0 0 0 0 0 1 0 0;
0 24334283739353772 2 0 2 0 0 0 0 0 2 0 0;
0 1264408092474789254 2 0 2 0 0 0 0 0 3 0 0;
0 8179999780691 2 0 2 0 0 0 0 0 0 0 0;
0 538670323414229747 2 0 1 0 0 0 0 0 6 0 0;
0 31101202505645162 2 0 1 0 0 0 0 0 5 0 0;
0 1966425797338770 2 0 1 0 0 0 0 0 2 0 0;
0 9147982905128342955 2 0 1 0 0 0 0 0 4 0 0;
0 352098792303997537 2 0 1 0 0 0 0 0 3 0 0;
0 50985453410691 2 0 1 0 0 0 0 0 1 0 0;
0 11912214140075845644 2 0 0 0 0 0 0 0 5 0 0;
0 687775376064687166 2 0 0 0 0 0 0 0 4 0 0;
0 114404150428904 2 0 0 0 0 0 0 0 2 0 0;
0 13236693093841864 2 0 0 0 0 0 0 0 3 0 0;
15871401437727601309 4091758044213316087 1 3 1 0 0 0 0 0 5 0 0;
342637026437584459704 53227827392636657398 1 3 1 0 0 0 0 0 4 0 0;
2452762778406056 10323033087733620 1 3 1 0 0 0 0 0 1 0 0;
-415398282192457698 471309322058531504 1 3 1 0 0 0 0 0 2 0 0;
-31672485419741179549 9278223636293440460 1 3 1 0 0 0 0 0 3 0 0;
-28220256495464 319542658069645 1 3 1 0 0 0 0 0 0 0 0;
174886158325849696699 61448502359412880669 1 3 0 0 0 0 0 0 6 0 0;
6228991933401983972317 1502305642661124650746 1 3 0 0 0 0 0 0 5 0 0;
-29565077914485075 113770322120660044 1 3 0 0 0 0 0 0 2 0 0;
-291687464383502597026 262240892696731600468 1 3 0 0 0 0 0 0 4 0 0;
-9294921348427730310 11821921301018997761 1 3 0 0 0 0 0 0 3 0 0;
340160935823276 3561493176284492 1 3 0 0 0 0 0 0 1 0 0;
0 4035954138927947039 1 2 2 0 0 0 0 0 4 0 0;
0 846271515709 1 2 2 0 0 0 0 0 0 0 0;
0 26110559299940 1 2 2 0 0 0 0 0 1 0 0;
0 1007007346808418 1 2 2 0 0 0 0 0 2 0 0;
0 77674613161471304 1 2 2 0 0 0 0 0 3 0 0;
0 68617107748999817300 1 2 1 0 0 0 0 0 5 0 0;
0 2641163460830746280 1 2 1 0 0 0 0 0 4 0 0;
0 8439616252883 1 2 1 0 0 0 0 0 1 0 0;
0 227843794201674 1 2 1 0 0 0 0 0 2 0 0;
0 10356418147122453 1 2 1 0 0 0 0 0 3 0 0;
0 76047575070244198570 1 2 0 0 0 0 0 0 6 0 0;
0 4390758000796962854 1 2 0 0 0 0 0 0 5 0 0;
0 9468652946769 1 2 0 0 0 0 0 0 2 0 0;
0 70419207259238693 1 2 0 0 0 0 0 0 4 0 0;
0 10306930119962333 1 1 3 0 0 0 0 0 4 0 0;
0 2161189436 1 1 3 0 0 0 0 0 0 0 0;
0 66680566937 1 1 3 0 0 0 0 0 1 0 0;
0 2571673016242 1 1 3 0 0 0 0 0 2 0 0;
0 198363703449578 1 1 3 0 0 0 0 0 3 0 0;
0 5992418063075869984 1 1 2 0 0 0 0 0 3 0 0;
0 38767771472439 1 1 2 0 0 0 0 0 0 0 0;
0 1495172200934631 1 1 2 0 0 0 0 0 1 0 0;
0 115328067056521484 1 1 2 0 0 0 0 0 2 0 0;
0 108122395030384742 1 1 2 0 0 0 0 0 5 0 0;
0 4161774350740145 1 1 2 0 0 0 0 0 4 0 0;
2967765110984116063 1546061135516199997 1 1 1 0 0 0 0 0 6 0 0;
1321560933375075717107 327752367831154419262 1 1 1 0 0 0 0 0 5 0 0;
-224484588725053795026 51290136519257485411 1 1 1 0 0 0 0 0 2 0 0;
108695551214359851577 102109458590286548029 1 1 1 0 0 0 0 0 4 0 0;
1298361551269813426331 204176721323536673456 1 1 1 0 0 0 0 0 3 0 0;
-2734411521256186561 2947000222352847472 1 1 1 0 0 0 0 0 1 0 0;
15809676057217767 62674442398241851 1 1 1 0 0 0 0 0 0 0 0;
17985908340259126792 11404503404342242480 1 1 0 0 0 0 0 0 7 0 0;
14561921547416760125209 4962717082295292371256 1 1 0 0 0 0 0 0 6 0 0;
966052006690369350030 821928755965523073454 1 1 0 0 0 0 0 0 5 0 0;
-1098487035534894963875 749284955279115309659 1 1 0 0 0 0 0 0 3 0 0;
15735574968743094196098 3809674372326262380253 1 1 0 0 0 0 0 0 4 0 0;
-31187162998329442844 40169618387771133274 1 1 0 0 0 0 0 0 2 0 0;
-190566453694378187 689969884948467319 1 1 0 0 0 0 0 0 1 0 0;
0 4407797542103303875 1 0 2 0 0 0 0 0 5 0 0;
0 169661971960811954 1 0 2 0 0 0 0 0 4 0 0;
0 1907789988835730 1 0 2 0 0 0 0 0 1 0 0;
0 147119943520821128 1 0 2 0 0 0 0 0 2 0 0;
0 7644627769380347869 1 0 2 0 0 0 0 0 3 0 0;
0 49451816855944 1 0 2 0 0 0 0 0 0 0 0;
0 36527321048417862129 1 0 1 0 0 0 0 0 6 0 0;
0 2108977531405526048 1 0 1 0 0 0 0 0 5 0 0;
0 11892080310484722 1 0 1 0 0 0 0 0 2 0 0;
0 55334523238724535622 1 0 1 0 0 0 0 0 4 0 0;
0 2128597244383257802 1 0 1 0 0 0 0 0 3 0 0;
0 308230241073685 1 0 1 0 0 0 0 0 1 0 0;
0 72014749119549430467 1 0 0 0 0 0 0 0 5 0 0;
0 4157914773481972403 1 0 0 0 0 0 0 0 4 0 0;
0 691625091229249 1 0 0 0 0 0 0 0 2 0 0;
0 80021826430953067 1 0 0 0 0 0 0 0 3 0 0;
-95949835964444135198 24736537267289592678 0 3 1 0 0 0 0 0 5 0 0;
-691886548297984702946 108938030713917375391 0 3 1 0 0 0 0 0 4 0 0;
-13861594813098280 53072153852355180 0 3 1 0 0 0 0 0 1 0 0;
2425221352038087614 2538021228621599877 0 3 1 0 0 0 0 0 2 0 0;
206797567510940550083 40768082691450561675 0 3 1 0 0 0 0 0 3 0 0;
157035633855532 1611458557531120 0 3 1 0 0 0 0 0 0 0 0;
-1057266320788091348234 371484127900086960365 0 3 0 0 0 0 0 0 6 0 0;
-12575849840214116337960 3058880683513303376047 0 3 0 0 0 0 0 0 5 0 0;
167084699048880702 583864654035416992 0 3 0 0 0 0 0 0 2 0 0;
2320566240824132992661 945295745975249986423 0 3 0 0 0 0 0 0 4 0 0;
57229253789400247947 68048602904191479566 0 3 0 0 0 0 0 0 3 0 0;
-1892873942463588 17948380961590368 0 3 0 0 0 0 0 0 1 0 0;
0 616412363725017567 0 2 2 0 0 0 0 0 5 0 0;
0 12223315176432218914 0 2 2 0 0 0 0 0 4 0 0;
0 394484577225392 0 2 2 0 0 0 0 0 1 0 0;
0 27379309911527035 0 2 2 0 0 0 0 0 2 0 0;
0 1499294244888960169 0 2 2 0 0 0 0 0 3 0 0;
0 10738047771301 0 2 2 0 0 0 0 0 0 0 0;
0 5108195667547324136 0 2 1 0 0 0 0 0 6 0 0;
0 207705734805331688728 0 2 1 0 0 0 0 0 5 0 0;
0 2655704397754171 0 2 1 0 0 0 0 0 2 0 0;
0 17135731059471187778 0 2 1 0 0 0 0 0 4 0 0;
0 383403419885072218 0 2 1 0 0 0 0 0 3 0 0;
0 76496111629651 0 2 1 0 0 0 0 0 1 0 0;
0 229871079189601782039 0 2 0 0 0 0 0 0 6 0 0;
0 25184278097030301537 0 2 0 0 0 0 0 0 5 0 0;
0 900633434371022306 0 2 0 0 0 0 0 0 4 0 0;
0 143025305927038 0 2 0 0 0 0 0 0 2 0 0;
0 13236693093841869 0 2 0 0 0 0 0 0 3 0 0;
0 62310077543408636 0 1 3 0 0 0 0 0 4 0 0;
0 13065372399 0 1 3 0 0 0 0 0 0 0 0;
0 403114336466 0 1 3 0 0 0 0 0 1 0 0;
0 15546932325425 0 1 3 0 0 0 0 0 2 0 0;
0 1199198752672440 0 1 3 0 0 0 0 0 3 0 0;
0 36226891017685941241 0 1 2 0 0 0 0 0 3 0 0;
0 234368800265123 0 1 2 0 0 0 0 0 0 0 0;
0 9038995578377535 0 1 2 0 0 0 0 0 1 0 0;
0 697210587205334342 0 1 2 0 0 0 0 0 2 0 0;
0 653649024501871387 0 1 2 0 0 0 0 0 5 0 0;
0 25159817665838133 0 1 2 0 0 0 0 0 4 0 0;
-163075320388223786743 56393895482588248546 0 1 1 0 0 0 0 0 6 0 0;
-3837289877386640278290 927454573291735572337 0 1 1 0 0 0 0 0 5 0 0;
361070805761312707428 55846839239353658525 0 1 1 0 0 0 0 0 2 0 0;
228162983097706919737 483028299622756943826 0 1 1 0 0 0 0 0 4 0 0;
6766373685093707437 20563769283516815755 0 1 1 0 0 0 0 0 3 0 0;
4010145010309075603 4014662169543590383 0 1 1 0 0 0 0 0 1 0 0;
-22521341264689429 81463541563874565 0 1 1 0 0 0 0 0 0 0 0;
-988305224765034177397 440702066933232045631 0 1 0 0 0 0 0 0 7 0 0;
-42266932815498252741851 14100681437679221537849 0 1 0 0 0 0 0 0 6 0 0;
491246749397050008091 2505193974615116985081 0 1 0 0 0 0 0 0 5 0 0;
2188820545733227755037 527617438890469370543 0 1 0 0 0 0 0 0 3 0 0;
50249641724808895646 123672340370787505353 0 1 0 0 0 0 0 0 4 0 0;
48612276860356311688 55869090900293311059 0 1 0 0 0 0 0 0 2 0 0;
271467430560877158 895169461105702371 0 1 0 0 0 0 0 0 1 0 0;
0 106084062223753 0 0 4 0 0 0 0 0 4 0 0;
0 22244051 0 0 4 0 0 0 0 0 0 0 0;
0 686309644 0 0 4 0 0 0 0 0 1 0 0;
0 26468940521 0 0 4 0 0 0 0 0 2 0 0;
0 2041658109136 0 0 4 0 0 0 0 0 3 0 0;
0 185030341087934982 0 0 3 0 0 0 0 0 3 0 0;
0 1197051682692 0 0 3 0 0 0 0 0 0 0 0;
0 46166756718287 0 0 3 0 0 0 0 0 1 0 0;
0 3561031585695388 0 0 3 0 0 0 0 0 2 0 0;
0 24271476943130254529 0 0 2 0 0 0 0 0 5 0 0;
0 47811506839007710604 0 0 2 0 0 0 0 0 2 0 0;
0 934241330559811854 0 0 2 0 0 0 0 0 4 0 0;
0 920166389270361298 0 0 2 0 0 0 0 0 1 0 0;
0 11929394500847217 0 0 2 0 0 0 0 0 0 0 0;
0 4268812851964738 0 0 2 0 0 0 0 0 3 0 0;
0 201137194290901559284 0 0 1 0 0 0 0 0 6 0 0;
0 11613055962335148907 0 0 1 0 0 0 0 0 5 0 0;
0 25043511060858 0 0 1 0 0 0 0 0 2 0 0;
0 186250801018043246 0 0 1 0 0 0 0 0 4 0 0"

/-- `stage1` of the third amplitude for `σ = −1`, as a literal. -/
@[expose] def S3neg : BPoly := bpoly% "3121820897053656326 481674298643822806 3 3 1 0 0 0 0 0 4 0 0;
-30705740374 724886428449 3 3 1 0 0 0 0 0 0 0 0;
2187116839886 21125654255995 3 3 1 0 0 0 0 0 1 0 0;
-194730692578441 704374205878132 3 3 1 0 0 0 0 0 2 0 0;
34675827043635666 34675827043635670 3 3 1 0 0 0 0 0 3 0 0;
-56758654148164931840 13630546767591485998 3 3 0 0 0 0 0 0 5 0 0;
-1260900826391946341 1448472850152731753 3 3 0 0 0 0 0 0 4 0 0;
-370120426879 8107089675288 3 3 0 0 0 0 0 0 1 0 0;
26363038590048 235189776277017 3 3 0 0 0 0 0 0 2 0 0;
-2347242117790374 7740079380151733 3 3 0 0 0 0 0 0 3 0 0;
-1471520663100572306 633637845768809458 3 1 1 0 0 0 0 0 5 0 0;
-32690021424976386 48340320938350570 3 1 1 0 0 0 0 0 4 0 0;
-2212859247352941 8004518451154847 3 1 1 0 0 0 0 0 1 0 0;
394043861942870212 394047383066991027 3 1 1 0 0 0 0 0 2 0 0;
35475162781542346755 5473867141071947098 3 1 1 0 0 0 0 0 3 0 0;
24853600453265 240064252909006 3 1 1 0 0 0 0 0 0 0 0;
16214610705707918897 8707392363616211862 3 1 0 0 0 0 0 0 6 0 0;
540314503892579290 898606911700824068 3 1 0 0 0 0 0 0 5 0 0;
-26673332063647097 87958424350624441 3 1 0 0 0 0 0 0 2 0 0;
-429984802837585666580 103279794118303122752 3 1 0 0 0 0 0 0 4 0 0;
-9552278987817775315 10973279167823725377 3 1 0 0 0 0 0 0 3 0 0;
299579983977823 2672611094056878 3 1 0 0 0 0 0 0 1 0 0;
-56618478996564039761 8735820234494786297 2 3 1 0 0 0 0 0 4 0 0;
556890473144 13146803861156 2 3 1 0 0 0 0 0 0 0 0;
-39666346323413 383142547642780 2 3 1 0 0 0 0 0 1 0 0;
3531706651763536 12774786733880555 2 3 1 0 0 0 0 0 2 0 0;
-628893408655028682 628893408655028686 2 3 1 0 0 0 0 0 3 0 0;
1029395591141718536557 247208552739500132350 2 3 0 0 0 0 0 0 5 0 0;
22868155896835754105 26270030327769998550 2 3 0 0 0 0 0 0 4 0 0;
6712638651128 147033126383538 2 3 0 0 0 0 0 0 1 0 0;
-478129654428605 4265487306114762 2 3 0 0 0 0 0 0 2 0 0;
42570436590834513 140376894212751831 2 3 0 0 0 0 0 0 3 0 0;
0 333800718257198631 2 2 2 0 0 0 0 0 4 0 0;
0 69992381007 2 2 2 0 0 0 0 0 0 0 0;
0 2159519942111 2 2 2 0 0 0 0 0 1 0 0;
0 83286321916490 2 2 2 0 0 0 0 0 2 0 0;
0 6424216126136729 2 2 2 0 0 0 0 0 3 0 0;
0 5675099137135323240 2 2 1 0 0 0 0 0 5 0 0;
0 218442090745400073 2 2 1 0 0 0 0 0 4 0 0;
0 698013374323 2 2 1 0 0 0 0 0 1 0 0;
0 18844223580593 2 2 1 0 0 0 0 0 2 0 0;
0 856545861792089 2 2 1 0 0 0 0 0 3 0 0;
0 6289649065960046503 2 2 0 0 0 0 0 0 6 0 0;
0 363145398562154831 2 2 0 0 0 0 0 0 5 0 0;
0 783121672290 2 2 0 0 0 0 0 0 2 0 0;
0 5824144961290429 2 2 0 0 0 0 0 0 4 0 0;
122637869808859060220 32839906479884423353 2 1 1 0 0 0 0 0 5 0 0;
2724416103758827496 3260129662978650907 2 1 1 0 0 0 0 0 4 0 0;
26756225839460917 96798241923459891 2 1 1 0 0 0 0 0 1 0 0;
-4764375075340555573 4764628057690624876 2 1 1 0 0 0 0 0 2 0 0;
-428921646872256338290 66201577090191954150 2 1 1 0 0 0 0 0 3 0 0;
-300502623662215 2902595057899776 2 1 1 0 0 0 0 0 0 0 0;
-1351340396768884968272 489289466281572624192 2 1 0 0 0 0 0 0 6 0 0;
-45030301949411096844 61242124097436462737 2 1 0 0 0 0 0 0 5 0 0;
322513823434359630 1063679979948542071 2 1 0 0 0 0 0 0 2 0 0;
5198550817875216094107 1249815632731715016691 2 1 0 0 0 0 0 0 4 0 0;
115495736852705828813 132676920847323224980 2 1 0 0 0 0 0 0 3 0 0;
-3622194351731855 32314297773596653 2 1 0 0 0 0 0 0 1 0 0;
0 65002022031727292 2 0 2 0 0 0 0 0 5 0 0;
0 2502014018112213 2 0 2 0 0 0 0 0 4 0 0;
0 315487032195805 2 0 2 0 0 0 0 0 1 0 0;
0 24334283739353772 2 0 2 0 0 0 0 0 2 0 0;
0 1264408092474789254 2 0 2 0 0 0 0 0 3 0 0;
0 8179999780691 2 0 2 0 0 0 0 0 0 0 0;
0 538670323414229747 2 0 1 0 0 0 0 0 6 0 0;
0 31101202505645162 2 0 1 0 0 0 0 0 5 0 0;
0 1966425797338770 2 0 1 0 0 0 0 0 2 0 0;
0 9147982905128342955 2 0 1 0 0 0 0 0 4 0 0;
0 352098792303997537 2 0 1 0 0 0 0 0 3 0 0;
0 50985453410691 2 0 1 0 0 0 0 0 1 0 0;
0 11912214140075845644 2 0 0 0 0 0 0 0 5 0 0;
0 687775376064687166 2 0 0 0 0 0 0 0 4 0 0;
0 114404150428904 2 0 0 0 0 0 0 0 2 0 0;
0 13236693093841864 2 0 0 0 0 0 0 0 3 0 0;
-15871401437727601310 4091758044213316087 1 3 1 0 0 0 0 0 5 0 0;
341931855975417111937 53227827392636657398 1 3 1 0 0 0 0 0 4 0 0;
2452536967559759 10323033087733620 1 3 1 0 0 0 0 0 1 0 0;
-415390240134221137 471309322058531504 1 3 1 0 0 0 0 0 2 0 0;
-31674096481376572032 9278223636293440460 1 3 1 0 0 0 0 0 3 0 0;
-28220256495464 319542658069645 1 3 1 0 0 0 0 0 0 0 0;
174886158325849696699 61448502359412880669 1 3 0 0 0 0 0 0 6 0 0;
-6217336577675158333324 1502305642661124650746 1 3 0 0 0 0 0 0 5 0 0;
29562356038842017 113770322120660044 1 3 0 0 0 0 0 0 2 0 0;
291795349896648919112 262240892696731600468 1 3 0 0 0 0 0 0 4 0 0;
9294921348427730308 11821921301018997761 1 3 0 0 0 0 0 0 3 0 0;
-340160935823278 3561493176284492 1 3 0 0 0 0 0 0 1 0 0;
0 4035954138927947039 1 2 2 0 0 0 0 0 4 0 0;
0 846271515709 1 2 2 0 0 0 0 0 0 0 0;
0 26110559299940 1 2 2 0 0 0 0 0 1 0 0;
0 1007007346808418 1 2 2 0 0 0 0 0 2 0 0;
0 77674613161471304 1 2 2 0 0 0 0 0 3 0 0;
0 68617107748999817300 1 2 1 0 0 0 0 0 5 0 0;
0 2641163460830746280 1 2 1 0 0 0 0 0 4 0 0;
0 8439616252883 1 2 1 0 0 0 0 0 1 0 0;
0 227843794201674 1 2 1 0 0 0 0 0 2 0 0;
0 10356418147122453 1 2 1 0 0 0 0 0 3 0 0;
0 76047575070244198570 1 2 0 0 0 0 0 0 6 0 0;
0 4390758000796962854 1 2 0 0 0 0 0 0 5 0 0;
0 9468652946769 1 2 0 0 0 0 0 0 2 0 0;
0 70419207259238693 1 2 0 0 0 0 0 0 4 0 0;
0 10306930119962333 1 1 3 0 0 0 0 0 4 0 0;
0 2161189436 1 1 3 0 0 0 0 0 0 0 0;
0 66680566937 1 1 3 0 0 0 0 0 1 0 0;
0 2571673016242 1 1 3 0 0 0 0 0 2 0 0;
0 198363703449578 1 1 3 0 0 0 0 0 3 0 0;
0 5992418063075869984 1 1 2 0 0 0 0 0 3 0 0;
0 38767771472439 1 1 2 0 0 0 0 0 0 0 0;
0 1495172200934631 1 1 2 0 0 0 0 0 1 0 0;
0 115328067056521484 1 1 2 0 0 0 0 0 2 0 0;
0 108122395030384742 1 1 2 0 0 0 0 0 5 0 0;
0 4161774350740145 1 1 2 0 0 0 0 0 4 0 0;
2967765110984116063 1546061135516199997 1 1 1 0 0 0 0 0 6 0 0;
-1321363145520317463842 327752367831154419262 1 1 1 0 0 0 0 0 5 0 0;
-224493762180278400588 51290136519257485411 1 1 1 0 0 0 0 0 2 0 0;
-108693720429894338239 102109458590286548029 1 1 1 0 0 0 0 0 4 0 0;
1294702397264283435955 204176721323536673456 1 1 1 0 0 0 0 0 3 0 0;
-2734319770322617419 2947000222352847472 1 1 1 0 0 0 0 0 1 0 0;
15809676057217767 62674442398241851 1 1 1 0 0 0 0 0 0 0 0;
-17985908340259126793 11404503404342242480 1 1 0 0 0 0 0 0 7 0 0;
14560323310317589883418 4962717082295292371256 1 1 0 0 0 0 0 0 6 0 0;
966025377907815942987 821928755965523073454 1 1 0 0 0 0 0 0 5 0 0;
1098842973290489090939 749284955279115309659 1 1 0 0 0 0 0 0 3 0 0;
-15694547732261232064526 3809674372326262380253 1 1 0 0 0 0 0 0 4 0 0;
31188268944458265458 40169618387771133274 1 1 0 0 0 0 0 0 2 0 0;
190566453694378185 689969884948467319 1 1 0 0 0 0 0 0 1 0 0;
0 4407797542103303875 1 0 2 0 0 0 0 0 5 0 0;
0 169661971960811954 1 0 2 0 0 0 0 0 4 0 0;
0 1907789988835730 1 0 2 0 0 0 0 0 1 0 0;
0 147119943520821128 1 0 2 0 0 0 0 0 2 0 0;
0 7644627769380347869 1 0 2 0 0 0 0 0 3 0 0;
0 49451816855944 1 0 2 0 0 0 0 0 0 0 0;
0 36527321048417862129 1 0 1 0 0 0 0 0 6 0 0;
0 2108977531405526048 1 0 1 0 0 0 0 0 5 0 0;
0 11892080310484722 1 0 1 0 0 0 0 0 2 0 0;
0 55334523238724535622 1 0 1 0 0 0 0 0 4 0 0;
0 2128597244383257802 1 0 1 0 0 0 0 0 3 0 0;
0 308230241073685 1 0 1 0 0 0 0 0 1 0 0;
0 72014749119549430467 1 0 0 0 0 0 0 0 5 0 0;
0 4157914773481972403 1 0 0 0 0 0 0 0 4 0 0;
0 691625091229249 1 0 0 0 0 0 0 0 2 0 0;
0 80021826430953067 1 0 0 0 0 0 0 0 3 0 0;
95949835964444135197 24736537267289592678 0 3 1 0 0 0 0 0 5 0 0;
-687623472322154827797 108938030713917375391 0 3 1 0 0 0 0 0 4 0 0;
-13860229683891113 53072153852355180 0 3 1 0 0 0 0 0 1 0 0;
2425172734140566593 2538021228621599877 0 3 1 0 0 0 0 0 2 0 0;
206807307110827241012 40768082691450561675 0 3 1 0 0 0 0 0 3 0 0;
157035633855532 1611458557531120 0 3 1 0 0 0 0 0 0 0 0;
-1057266320788091348234 371484127900086960365 0 3 0 0 0 0 0 0 6 0 0;
12505387916956488611291 3058880683513303376047 0 3 0 0 0 0 0 0 5 0 0;
-167068244073402232 583864654035416992 0 3 0 0 0 0 0 0 2 0 0;
-2321218457789972121690 945295745975249986423 0 3 0 0 0 0 0 0 4 0 0;
-57229253789400247952 68048602904191479566 0 3 0 0 0 0 0 0 3 0 0;
1892873942463586 17948380961590368 0 3 0 0 0 0 0 0 1 0 0;
0 616412363725017567 0 2 2 0 0 0 0 0 5 0 0;
0 12223315176432218914 0 2 2 0 0 0 0 0 4 0 0;
0 394484577225392 0 2 2 0 0 0 0 0 1 0 0;
0 27379309911527035 0 2 2 0 0 0 0 0 2 0 0;
0 1499294244888960169 0 2 2 0 0 0 0 0 3 0 0;
0 10738047771301 0 2 2 0 0 0 0 0 0 0 0;
0 5108195667547324136 0 2 1 0 0 0 0 0 6 0 0;
0 207705734805331688728 0 2 1 0 0 0 0 0 5 0 0;
0 2655704397754171 0 2 1 0 0 0 0 0 2 0 0;
0 17135731059471187778 0 2 1 0 0 0 0 0 4 0 0;
0 383403419885072218 0 2 1 0 0 0 0 0 3 0 0;
0 76496111629651 0 2 1 0 0 0 0 0 1 0 0;
0 229871079189601782039 0 2 0 0 0 0 0 0 6 0 0;
0 25184278097030301537 0 2 0 0 0 0 0 0 5 0 0;
0 900633434371022306 0 2 0 0 0 0 0 0 4 0 0;
0 143025305927038 0 2 0 0 0 0 0 0 2 0 0;
0 13236693093841869 0 2 0 0 0 0 0 0 3 0 0;
0 62310077543408636 0 1 3 0 0 0 0 0 4 0 0;
0 13065372399 0 1 3 0 0 0 0 0 0 0 0;
0 403114336466 0 1 3 0 0 0 0 0 1 0 0;
0 15546932325425 0 1 3 0 0 0 0 0 2 0 0;
0 1199198752672440 0 1 3 0 0 0 0 0 3 0 0;
0 36226891017685941241 0 1 2 0 0 0 0 0 3 0 0;
0 234368800265123 0 1 2 0 0 0 0 0 0 0 0;
0 9038995578377535 0 1 2 0 0 0 0 0 1 0 0;
0 697210587205334342 0 1 2 0 0 0 0 0 2 0 0;
0 653649024501871387 0 1 2 0 0 0 0 0 5 0 0;
0 25159817665838133 0 1 2 0 0 0 0 0 4 0 0;
-163075320388223786743 56393895482588248546 0 1 1 0 0 0 0 0 6 0 0;
3826421659526600122871 927454573291735572337 0 1 1 0 0 0 0 0 5 0 0;
361029990019320396340 55846839239353658525 0 1 1 0 0 0 0 0 2 0 0;
-228263582623649985397 483028299622756943826 0 1 1 0 0 0 0 0 4 0 0;
-6766373685093707440 20563769283516815755 0 1 1 0 0 0 0 0 3 0 0;
4010636142826174381 4014662169543590383 0 1 1 0 0 0 0 0 1 0 0;
-22521341264689429 81463541563874565 0 1 1 0 0 0 0 0 0 0 0;
988305224765034177396 440702066933232045631 0 1 0 0 0 0 0 0 7 0 0;
-42179111503077369739569 14100681437679221537849 0 1 0 0 0 0 0 0 6 0 0;
492709970738379550884 2505193974615116985081 0 1 0 0 0 0 0 0 5 0 0;
-2187414804169287910403 527617438890469370543 0 1 0 0 0 0 0 0 3 0 0;
50260537220118693519 123672340370787505353 0 1 0 0 0 0 0 0 4 0 0;
-48606356854042534111 55869090900293311059 0 1 0 0 0 0 0 0 2 0 0;
-271467430560877159 895169461105702371 0 1 0 0 0 0 0 0 1 0 0;
0 106084062223753 0 0 4 0 0 0 0 0 4 0 0;
0 22244051 0 0 4 0 0 0 0 0 0 0 0;
0 686309644 0 0 4 0 0 0 0 0 1 0 0;
0 26468940521 0 0 4 0 0 0 0 0 2 0 0;
0 2041658109136 0 0 4 0 0 0 0 0 3 0 0;
0 185030341087934982 0 0 3 0 0 0 0 0 3 0 0;
0 1197051682692 0 0 3 0 0 0 0 0 0 0 0;
0 46166756718287 0 0 3 0 0 0 0 0 1 0 0;
0 3561031585695388 0 0 3 0 0 0 0 0 2 0 0;
0 24271476943130254529 0 0 2 0 0 0 0 0 5 0 0;
0 47811506839007710604 0 0 2 0 0 0 0 0 2 0 0;
0 934241330559811854 0 0 2 0 0 0 0 0 4 0 0;
0 920166389270361298 0 0 2 0 0 0 0 0 1 0 0;
0 11929394500847217 0 0 2 0 0 0 0 0 0 0 0;
0 4268812851964738 0 0 2 0 0 0 0 0 3 0 0;
0 201137194290901559284 0 0 1 0 0 0 0 0 6 0 0;
0 11613055962335148907 0 0 1 0 0 0 0 0 5 0 0;
0 25043511060858 0 0 1 0 0 0 0 0 2 0 0;
0 186250801018043246 0 0 1 0 0 0 0 0 4 0 0"

/-- The literal `S3pos` is the computed stage-one enclosure. -/
theorem S3pos_eq : stage1 cellMask amp3Lit (globalS 1) = S3pos := by decide +kernel

/-- The literal `S3neg` is the computed stage-one enclosure. -/
theorem S3neg_eq : stage1 cellMask amp3Lit (globalS (-1)) = S3neg := by decide +kernel

set_option maxHeartbeats 4000000 in
-- The `244` leaf goals are elaborated (and kernel-checked) within one tactic block.
/-- Kernel-checked cover of the disc for `σ = +1` (`244` leaves, `|amp 3/q| ≤ 11`). -/
theorem cover_pos : CoverCert S3pos 11 (-17 / 10) (17 / 10) (-17 / 10) (17 / 10) := by
  cover_cert
    "XYXYXYLLYYLLLLYXYYXLLLLYYXLLLLLXYLXYLLYLYLLYLXYLYLXLLYLYLXLLYXYXYYXLYXLXLLLLLYYXYXXYLLYL
    LXYLYLLYLYLLXLYXLLLYLXYXYLLYLXLLXLYLLYLXXLYLLYLXLLXLXYLLYXYLLYYLLLLXLLLYXYYLXXYXYYXLLLLY
    XYLLLXLLXLLYXYLXLYLLLXYLLYXLLLXYLXYLLYLLLXYXLYLLLYXYXLYLLLYXYLLYLLLYLLYLXYXYLXLLLYXLLLLX
    LYXYLLYLLLXYLXYLYLXLYLXLXLLYXLLYXLXYLLYLXYLLYLYLLXYXLYLXLLXXYLLYLLXYYLLLYYLLLYXYXLYLLXYL
    LYXLLLYXXLYLLYXLLLLLYXLYLXYLLYLLXYXYLXLYLLYYLLXYLXLYLLYLXYLLYLLYXXYXLLXYLYLXLLYXLLXYLLLY
    XYLLYLXLLXYXLYLLLLXYXYLLYLLLLLYXYYLXLLXYXLLLLLL"
  all_goals decide +kernel

/-- Kernel-checked cover of the disc for `σ = −1` (`80` leaves, `|amp 3/q| ≤ 11`). -/
theorem cover_neg : CoverCert S3neg 11 (-17 / 10) (17 / 10) (-17 / 10) (17 / 10) := by
  cover_cert
    "XYXYXYLLYYLLLLYXYYXLLLLYLLLXYLXYLLYLYLLYLXYLYLXLLYLLYXYXYYLLLYYXLYLLXLLLLYXYYLXXLLXLLXLY
    LLYLXYXLLLLXLYXLLLXYLXYLYLLYLYXLLXLYLLYXLYLXLLXYXLYLLYXXLLXLLLYXYLXLLLL"
  all_goals decide +kernel

/-- **Secular amplitude bound**: `|amp 3| ≤ 11 q` on the region. -/
theorem amp3_bound {x : ℕ → ℝ} (hx : InRegion x) : |eval (amp 3) x| ≤ 11 * cq := by
  have hq : (0 : ℝ) < cq := by norm_num [cq]
  have hxi : ((-17 / 10 : ℚ) : ℝ) ≤ x 0 ∧ x 0 ≤ ((17 / 10 : ℚ) : ℝ) := by
    have := abs_le.mp hx.1; push_cast; constructor <;> linarith
  have hyj : ((-17 / 10 : ℚ) : ℝ) ≤ x 1 ∧ x 1 ≤ ((17 / 10 : ℚ) : ℝ) := by
    have := abs_le.mp hx.2.1; push_cast; constructor <;> linarith
  have hσ : x 10 = 1 ∨ x 10 = -1 := hx.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have key : |eval (amp 3) x / cq| ≤ ((11 : ℕ) : ℝ) := by
    rcases hσ with h | h
    · have hS := BPoly.holds_stage1 cellMask cq (by norm_num [cq]) (amp 3)
        (globalS_mem hx (sg := 1) (by simp [h]))
      rw [amp3Lit_eq, S3pos_eq] at hS
      exact cover_pos.sound x hx hS hxi hyj
    · have hS := BPoly.holds_stage1 cellMask cq (by norm_num [cq]) (amp 3)
        (globalS_mem hx (sg := -1) (by simp [h]))
      rw [amp3Lit_eq, S3neg_eq] at hS
      exact cover_neg.sound x hx hS hxi hyj
  rw [abs_div, abs_of_pos hq, div_le_iff₀ hq] at key
  simpa using key

/-- Global bound `|amp 0/q| ≤ 1935`. -/
theorem glob_0 : boundOK (evalT (toFix cq (amp 0)) globalF) 1935 = true := by decide +kernel
/-- Global bound `|amp 1/q| ≤ 218`. -/
theorem glob_1 : boundOK (evalT (toFix cq (amp 1)) globalF) 218 = true := by decide +kernel
/-- Global bound `|amp 2/q| ≤ 93`. -/
theorem glob_2 : boundOK (evalT (toFix cq (amp 2)) globalF) 93 = true := by decide +kernel

/-! ## Passing-alpha analysis along the orbit -/

/-- Sign of the initial parallel velocity (`σ = ±1`). -/
@[expose] def sgn0 (ψ θ φ ρ : ℝ → ℝ) : ℝ := if 0 < vel ψ θ φ ρ 0 then 1 else -1

theorem sgn0_sq : sgn0 ψ θ φ ρ ^ 2 = 1 := by unfold sgn0; split_ifs <;> norm_num

theorem sgn0_cases : sgn0 ψ θ φ ρ = 1 ∨ sgn0 ψ θ φ ρ = -1 := by
  unfold sgn0; split_ifs <;> simp

theorem mα_pos : (0 : ℝ) < mα := by norm_num [mα]
theorem qα_ne : qα ≠ 0 := by norm_num [qα]
theorem G_ne : reactorQA.G ≠ 0 := by
  change (581 / 10 : ℝ) ≠ 0; norm_num

/-- Energy conservation in the form `m v²/2 + μ B = E`. -/
theorem energy_eq (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T)
    (hE : boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα) {s : ℝ} (hs : s ∈ Set.Icc 0 T) :
    mα * vel ψ θ φ ρ s ^ 2 / 2 + μ * Bt ψ θ φ s = Eα := by
  have := boozerEnergy_eq_on mα_pos.ne' qα_ne G_ne h hs
  rw [boozerEnergy_eq_parallel mα_pos.ne', hE] at this
  simpa [vel, Bt] using this

/-- Sign persistence by the intermediate value theorem. -/
theorem sign_persist {u : ℝ → ℝ} {t w : ℝ} (hc : ContinuousOn u (Set.Icc 0 t)) (hw : 0 < w)
    (ht : 0 ≤ t) (hlow : ∀ s ∈ Set.Icc 0 t, w ^ 2 ≤ u s ^ 2) : 0 < u t * u 0 := by
  by_contra hneg
  push Not at hneg
  have h00 : 0 < u 0 * u 0 := by nlinarith [hlow 0 ⟨le_rfl, ht⟩]
  have hg : ContinuousOn (fun r => u r * u 0) (Set.Icc 0 t) := hc.mul continuousOn_const
  obtain ⟨σ, hσ, hσ0⟩ := intermediate_value_Icc' ht hg
    (show (0 : ℝ) ∈ Set.Icc (u t * u 0) (u 0 * u 0) from ⟨hneg, h00.le⟩)
  have hu0 : u 0 ≠ 0 := by rintro h0; simp [h0] at h00
  have huσ : u σ = 0 := by
    rcases mul_eq_zero.mp hσ0 with h' | h'
    · exact h'
    · exact absurd h' hu0
  have := hlow σ hσ
  rw [huσ] at this
  nlinarith

/-- Numerical facts used for the passing analysis. -/
theorem passing_numerics :
    19 / 100 * Eα / 4.93 * 10 ^ 14 ≤ (21612 / 10000 : ℝ) ∧
    ((112 / 100 : ℝ) * 10 ^ 7) ^ 2 ≤ 2 / mα * (Eα - 19 / 100 * Eα / 4.93 * 6.47) ∧
    2 * Eα / mα ≤ ((13 / 10 : ℝ) * 10 ^ 7) ^ 2 := by
  norm_num [Eα, mα]

/-- **Region facts** for a passing alpha whose orbit has stayed in `ψ ≤ ψ_a` up to time `s`:
the state vector satisfies `InRegion` (with `σ = sgn0`), and `B ≠ 0`, `W ≠ 0`. -/
theorem region_facts {μ : ℝ} {ψ θ φ ρ : ℝ → ℝ} {T : ℝ} (hμ : 0 ≤ μ)
    (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T)
    (hE : boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα)
    (hpitch : 81 / 100 * (2 * Eα / mα) ≤ parallelVelocity reactorQA mα qα ψ θ φ ρ 0 ^ 2)
    {s : ℝ} (hs : s ∈ Set.Icc 0 T) (hhist : ∀ s' ∈ Set.Icc 0 s, ψ s' ≤ psiEdge) :
    InRegion (orbX (sgn0 ψ θ φ ρ) μ ψ θ φ ρ s) ∧ Bt ψ θ φ s ≠ 0 ∧
      orbX (sgn0 ψ θ φ ρ) μ ψ θ φ ρ s 5 ≠ 0 := by
  set σ := sgn0 ψ θ φ ρ with hσdef
  have hsub : ∀ s' ∈ Set.Icc 0 s, s' ∈ Set.Icc 0 T := fun s' hs' => ⟨hs'.1, hs'.2.trans hs.2⟩
  have hBb : ∀ s' ∈ Set.Icc 0 s, 4.93 ≤ Bt ψ θ φ s' ∧ Bt ψ θ φ s' ≤ 6.47 := fun s' hs' =>
    reactorQA_B_bounds (h.pos s' (hsub s' hs')) (hhist s' hs')
  have h0s : (0 : ℝ) ∈ Set.Icc 0 s := ⟨le_rfl, hs.1⟩
  obtain ⟨n1, n2, n3⟩ := passing_numerics
  -- magnetic moment bound from the initial pitch
  have hE0 := energy_eq h hE (hsub 0 h0s)
  have hB0 := hBb 0 h0s
  have hμle : μ ≤ 19 / 100 * Eα / 4.93 := by
    have hv0 : 81 / 100 * (2 * Eα / mα) ≤ vel ψ θ φ ρ 0 ^ 2 := hpitch
    have hm := mα_pos
    have : μ * Bt ψ θ φ 0 ≤ 19 / 100 * Eα := by
      have : mα * (81 / 100 * (2 * Eα / mα)) ≤ mα * vel ψ θ φ ρ 0 ^ 2 :=
        mul_le_mul_of_nonneg_left hv0 hm.le
      field_simp at this
      nlinarith
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left hB0.1 hμ]
  -- speed bounds
  have hvsq : ∀ s' ∈ Set.Icc 0 s, ((112 / 100 : ℝ) * 10 ^ 7) ^ 2 ≤ vel ψ θ φ ρ s' ^ 2 ∧
      vel ψ θ φ ρ s' ^ 2 ≤ ((13 / 10 : ℝ) * 10 ^ 7) ^ 2 := by
    intro s' hs'
    have hEs := energy_eq h hE (hsub s' hs')
    have hB := hBb s' hs'
    have hm := mα_pos
    have hv : vel ψ θ φ ρ s' ^ 2 = 2 / mα * (Eα - μ * Bt ψ θ φ s') := by
      field_simp; linarith
    have hμB : μ * Bt ψ θ φ s' ≤ 19 / 100 * Eα / 4.93 * 6.47 := by
      have := mul_le_mul hμle hB.2 (by linarith) (by norm_num [Eα])
      linarith
    have hμB0 : 0 ≤ μ * Bt ψ θ φ s' := mul_nonneg hμ (by linarith)
    constructor
    · rw [hv]; refine n2.trans ?_
      gcongr
    · rw [hv]; refine le_trans ?_ n3
      rw [show 2 * Eα / mα = 2 / mα * Eα by ring]
      gcongr; linarith
  -- sign persistence
  have hvc : ContinuousOn (vel ψ θ φ ρ) (Set.Icc 0 s) := by
    intro s' hs'
    have hd := (((h.dρ s' (hsub s' hs')).const_mul qα).mul
      (h.hasDerivAt_B (hsub s' hs'))).div_const mα
    exact (show ContinuousAt (fun r => qα * ρ r * along reactorQA.B ψ θ φ r / mα) s' from
      hd.continuousAt).continuousWithinAt
  have hsign := sign_persist hvc (by norm_num : (0 : ℝ) < 112 / 100 * 10 ^ 7) hs.1
    (fun s' hs' => (hvsq s' hs').1)
  have hσv : 0 < σ * vel ψ θ φ ρ s := by
    rw [hσdef]; unfold sgn0
    split_ifs with hp
    · nlinarith
    · have : vel ψ θ φ ρ 0 ≠ 0 := by
        intro h0; rw [h0] at hsign; simp at hsign
      have hneg : vel ψ θ φ ρ 0 < 0 := lt_of_le_of_ne (not_lt.mp hp) this
      nlinarith
  have hσ2 : σ ^ 2 = 1 := sgn0_sq
  have hW2 : (σ * vel ψ θ φ ρ s) ^ 2 = vel ψ θ φ ρ s ^ 2 := by rw [mul_pow, hσ2, one_mul]
  obtain ⟨hvl, hvh⟩ := hvsq s ⟨hs.1, le_rfl⟩
  have hWl : 112 / 100 * 10 ^ 7 ≤ σ * vel ψ θ φ ρ s := by
    rw [← hW2] at hvl
    nlinarith
  have hWh : σ * vel ψ θ φ ρ s ≤ 13 / 10 * 10 ^ 7 := by
    rw [← hW2] at hvh
    nlinarith
  have hψs := h.pos s hs
  have hψc := hhist s ⟨hs.1, le_rfl⟩
  have hr := radius_le_edge hψc
  have hr0 : 0 ≤ radius (57 / 10) (ψ s) := sqrt_nonneg _
  have hr2 := radius_sq (by norm_num : (0 : ℝ) < 57 / 10) hψs.le
  have hBs := hBb s ⟨hs.1, le_rfl⟩
  refine ⟨?_, by linarith [hBs.1], ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [orbX, List.getD_cons_zero]
      rw [abs_mul, abs_of_nonneg hr0]
      nlinarith [abs_cos_le_one (θ s), abs_nonneg (cos (θ s))]
    · simp only [orbX, List.getD_cons_succ, List.getD_cons_zero]
      rw [abs_mul, abs_of_nonneg hr0]
      nlinarith [abs_sin_le_one (θ s), abs_nonneg (sin (θ s))]
    · simp only [orbX, List.getD_cons_succ, List.getD_cons_zero]
      rw [mul_pow, mul_pow, ← mul_add, cos_sq_add_sin_sq, mul_one, hr2]
    · simp only [orbX, List.getD_cons_succ, List.getD_cons_zero]
      unfold psiEdge at hψc
      linarith
    · simpa [orbX] using abs_cos_le_one _
    · simpa [orbX] using abs_sin_le_one _
    · simp only [orbX, List.getD_cons_succ, List.getD_cons_zero]; linarith
    · simp only [orbX, List.getD_cons_succ, List.getD_cons_zero]; linarith
    · exact orbX_6 s
    · rw [eval_Bpoly]
      simp only [orbX, List.getD_cons_succ, List.getD_cons_zero, Bt, along, reactorQA, field,
        nearAxisB, cB0, cEta, cb0, cb1, cB2c]
      push_cast
      rw [cos_two_mul (θ s)]
      have hsc := sin_sq_add_cos_sq (θ s)
      have : radius (57 / 10) (ψ s) ^ 2 = 2 * ψ s / (57 / 10) := hr2
      linear_combination (33 / 2000 * (2 * ψ s / (57 / 10))) * hsc -
        (33 / 2000 * (cos (θ s) ^ 2 - sin (θ s) ^ 2)) * this
    · have h1 := hBs.1; norm_num at h1; simpa [orbX, Bt] using h1
    · have h1 := hBs.2; norm_num at h1; simpa [orbX, Bt] using h1
    · exact orbX_8 s
    · simp only [orbX, List.getD_cons_succ, List.getD_cons_zero]; positivity
    · simp only [orbX, List.getD_cons_succ, List.getD_cons_zero]
      nlinarith
    · simp only [orbX, List.getD_cons_succ, List.getD_cons_zero]
      exact sgn0_cases
    · intro i hi; exact orbX_ge11 s hi
  · simp only [orbX, List.getD_cons_succ, List.getD_cons_zero]
    positivity

theorem eval_amp0 (x : ℕ → ℝ) : eval (amp 0) x =
    2 * cb1 * (x 10 * ((cmus * x 9 + cm * cvs ^ 2 * x 5 ^ 2 * x 8) * x 2)) := by
  simp only [amp, cP, V, eval_scP, eval_mulP, eval_addP, eval_varP (show 10 < 11 by norm_num),
    eval_varP (show 9 < 11 by norm_num), eval_varP (show 8 < 11 by norm_num),
    eval_varP (show 5 < 11 by norm_num), eval_varP (show 2 < 11 by norm_num)]
  push_cast; ring

/-- Orbit-width constant `Δρ = (m/q) 10⁷ (W_hi/B_min − W_lo/B_max) ≈ 1.88 cm`. -/
@[expose] def Δρv : ℝ :=
  (cm / cq : ℚ) * 10 ^ 7 * ((13 / 10) / (493 / 100) - (112 / 100) / (647 / 100))

/-- Lower bound for the phase speed `Ω = 2 v_∥ B/G ≥ Ω₀ ≈ 1.90 × 10⁶ s⁻¹`. -/
@[expose] def Om0 : ℝ := 2 * 10 ^ 7 * (112 / 100) * (493 / 100) / (581 / 10)

theorem rho_eq {σ : ℝ} (hσ : σ ^ 2 = 1) {s : ℝ} (hB : Bt ψ θ φ s ≠ 0) :
    ρ s = (cm / cq : ℚ) * 10 ^ 7 * σ * (orbX σ μ ψ θ φ ρ s 5 / orbX σ μ ψ θ φ ρ s 7) := by
  simp only [orbX, List.getD_cons_succ, List.getD_cons_zero, vel, parallelVelocity, mα_eq, qα_eq,
    Bt] at hB ⊢
  have hq : (cq : ℝ) ≠ 0 := by norm_num [cq]
  have hm : (cm : ℝ) ≠ 0 := by norm_num [cm]
  push_cast
  field_simp
  rw [hσ]; ring

/-- **Orbit width** for passing alphas: `|ρ(t) − ρ(0)| ≤ Δρ` while the orbit stays in `ψ ≤ ψ_a`. -/
theorem rho_dev {μ : ℝ} {ψ θ φ ρ : ℝ → ℝ} {T : ℝ} (hμ : 0 ≤ μ)
    (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T)
    (hE : boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα)
    (hpitch : 81 / 100 * (2 * Eα / mα) ≤ parallelVelocity reactorQA mα qα ψ θ φ ρ 0 ^ 2)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (hhist : ∀ s ∈ Set.Icc 0 t, ψ s ≤ psiEdge) :
    |ρ t - ρ 0| ≤ Δρv := by
  set σ := sgn0 ψ θ φ ρ
  have hσ2 : σ ^ 2 = 1 := sgn0_sq
  obtain ⟨⟨-, -, -, -, -, -, ht5l, ht5h, -, -, ht7l, ht7h, -⟩, hBt, -⟩ :=
    region_facts hμ h hE hpitch ht hhist
  obtain ⟨⟨-, -, -, -, -, -, h05l, h05h, -, -, h07l, h07h, -⟩, hB0, -⟩ :=
    region_facts hμ h hE hpitch ⟨le_rfl, ht.1.trans ht.2⟩
      (fun s hs => hhist s ⟨hs.1, hs.2.trans ht.1⟩)
  rw [rho_eq (μ := μ) (ρ := ρ) hσ2 hBt, rho_eq (μ := μ) (ρ := ρ) hσ2 hB0, ← mul_sub, abs_mul]
  have hσ1 : |σ| = 1 := by
    rcases sgn0_cases (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) with h1 | h1 <;> simp [σ, h1]
  have hk : |((cm / cq : ℚ) : ℝ) * 10 ^ 7 * σ| = ((cm / cq : ℚ) : ℝ) * 10 ^ 7 := by
    rw [abs_mul, hσ1, mul_one, abs_of_pos (by norm_num [cm, cq])]
  rw [hk, Δρv]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num [cm, cq])
  have hb1 : ∀ w b : ℝ, 112 / 100 ≤ w → w ≤ 13 / 10 → 493 / 100 ≤ b → b ≤ 647 / 100 →
      (112 / 100) / (647 / 100) ≤ w / b ∧ w / b ≤ (13 / 10) / (493 / 100) := by
    intro w b hw1 hw2 hb1 hb2
    constructor
    · rw [div_le_div_iff₀ (by norm_num) (by linarith)]; nlinarith
    · rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
  obtain ⟨a1, a2⟩ := hb1 _ _ ht5l ht5h ht7l ht7h
  obtain ⟨b1, b2⟩ := hb1 _ _ h05l h05h h07l h07h
  rw [abs_le]; constructor <;> linarith

/-- The averaged confinement time `T = 0.19 s`. -/
@[expose] def Tav : ℝ := 19 / 100

/-- Numerical gap: `|G| Δρ + (2 (1935 + 218 + 93)/Ω₀ + 11 T) ≤ ι₀ (8.2 − ψ_start)` at `T = Tav`. -/
theorem averaged_gap :
    |(1 : ℝ) * (581 / 10)| * Δρv + (2 * ((1935 + 218 + 93) * cq) / Om0 + (11 * cq + 0) * Tav) /
      |qα| ≤ 211 / 500 * (8.2 - psiStart) := by
  norm_num [Δρv, Om0, cq, cm, qα, psiStart, Tav, abs_of_pos]

/-- **Averaged confinement of passing 3.5 MeV alphas in the reactor-scale near-axis QA model,
for every horizon `T ≤ 0.19 s`.** Every guiding-centre orbit (solving the vacuum Boozer equations
on `[0, T]`) of the model with field `reactorQA` (a = 1.7 m, B₀ = 5.7 T) for an alpha
(`m = 6.6447 × 10⁻²⁷ kg`, `q = 2e`) of energy `3.5 MeV`, any `μ ≥ 0`, passing pitch
`v_∥² ≥ 0.81 v²` at `t = 0`, starting at `ψ ≤ B₀(a/4)²/2`, satisfies `ψ(t) ≤ 8.2 T m² < ψ_a` for
`0 ≤ t ≤ T`. The hypotheses are exactly those of the worst-case bound
`NearAxisQA.alpha_trapped_reactorQA`, except that the orbit is supplied on `[0, T]` instead of
`[0, 0.8 ms]`.

Proof: `dP/dt = a₀ sin(2σφ)` with `Ω = 2|v_∥|B/G ≥ Ω₀ ≈ 1.9 × 10⁶ s⁻¹`; three oscillatory
integrations by parts (`osc_ibp_drift_iter`, `k = 3`) with exact polynomial Lie-derivative
amplitudes bounded by `1935, 218, 93` (global) and `11` T m²/s (`amp3_bound`: kernel-checked
adaptive ball cover of the disc, `324` rectangles, both signs of `v_∥`); the gap
`|G| Δρ + (2 ∑_{j<3} Aⱼ/Ω₀ + A₃ T)/|q| ≤ ι₀ (8.2 − ψ(0))` with `Δρ ≈ 1.88 cm`.

**Caveats.** This is a theorem about the model only: (i) the Boozer guiding-centre equations are
assumed (their derivation from the Lorentz force is not formalized), orbits are supplied and
must stay off the magnetic axis; (ii) the field is the truncated second-order near-axis expansion,
accurate only to the order of the expansion (no bound on the `O(r³)` remainder); (iii) passing
particles only (`|v_∥/v| ≥ 0.9` initially): the phase speed must stay positive, so trapped and
barely passing alphas are not covered; (iv) collisions and slowing down are ignored. -/
theorem alpha_trapped_reactorQA_averaged_of_le {μ : ℝ} {ψ θ φ ρ : ℝ → ℝ} {T : ℝ} (hT : T ≤ Tav)
    (hμ : 0 ≤ μ) (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T)
    (hE : boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα)
    (hpitch : 81 / 100 * (2 * Eα / mα) ≤ parallelVelocity reactorQA mα qα ψ θ φ ρ 0 ^ 2)
    (hstart : ψ 0 ≤ psiStart) :
    ∀ t ∈ Set.Icc 0 T, ψ t ≤ 8.2 := by
  set σ := sgn0 ψ θ φ ρ with hσdef
  have hσ2 : σ ^ 2 = 1 := sgn0_sq
  set X := orbX σ μ ψ θ φ ρ with hX
  let a : ℕ → ℝ → ℝ := fun j r => if j % 2 = 0 then eval (amp j) (X r) else 0
  let b : ℕ → ℝ → ℝ := fun j r => if j % 2 = 1 then eval (amp j) (X r) else 0
  let A : ℕ → ℝ := fun j => ([1935, 218, 93, 11] : List ℝ).getD j 0 * cq
  have hs0 : ψ 0 ≤ 0.51478125 := by norm_num [psiStart] at hstart; linarith
  refine boozerGC_trapped_until_averaged (F := reactorQA) (N := 0) (M := 1) (c := psiEdge)
    (ιmin := 211 / 500) (Δρ := Δρv) (Ω₀ := Om0) (η := 0) (k := 3) (Φ := fun r => 2 * σ * φ r)
    (Ω := Omf σ μ ψ θ φ ρ) (e := fun _ => 0) (a := a) (b := b) (A := A) qα_ne h
    (by norm_num [psiEdge]) (by linarith) (by norm_num) (by norm_num [Om0])
    (by simp [A, cq]; norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- twist
    intro x hx _
    have hp : ∀ y, reactorQA.ψp y = 211 / 500 * y := fun _ => rfl
    rw [hp, hp, le_abs]
    right; linarith
  · exact fun t ht hhist => rho_dev hμ h hE hpitch ht hhist
  · -- `dP/dt = a₀ sin Φ`
    intro s hs hhist
    obtain ⟨-, hB, -⟩ := region_facts hμ h hE hpitch hs hhist
    refine (helicalMomentum_hasDerivAt_on mα_pos.ne' qα_ne G_ne 0 1 h hs).congr_deriv ?_
    simp only [a, b, Nat.zero_mod, ite_true, show ¬ (0 % 2 = 1) by norm_num, ite_false, zero_mul,
      add_zero]
    rw [hX, eval_amp0, orbX_sq5 hσ2, orbX_8]
    simp only [orbX, List.getD_cons_succ, List.getD_cons_zero, vel, parallelVelocity, Bt, along,
      symmetryDefect, reactorQA, field, nearAxisBφ, mα_eq, qα_eq, cm, cq, cmus, cvs, cb1]
    simp only [Bt, along] at hB
    rcases sgn0_cases (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) with h1 | h1
    · rw [show σ = 1 from hσdef.trans h1]; push_cast; field_simp; ring
    · rw [show σ = -1 from hσdef.trans h1]
      simp only [mul_neg, neg_mul, mul_one, sin_neg]
      push_cast; field_simp; ring
  · intro s _ _; simp
  · -- phase speed
    intro s hs hhist
    obtain ⟨-, hB, -⟩ := region_facts hμ h hE hpitch hs hhist
    refine ((h.dφ s hs).const_mul (2 * σ)).congr_deriv ?_
    simp only [Omf, orbX, List.getD_cons_succ, List.getD_cons_zero, vel, parallelVelocity, Bt,
      along, reactorQA, field]
    field_simp
  · intro s hs hhist
    obtain ⟨⟨-, -, -, -, -, -, h5, -, -, -, h7, -⟩, -, -⟩ := region_facts hμ h hE hpitch hs hhist
    simp only [Om0, Omf]
    gcongr
  · intro j hj s hs hhist
    obtain ⟨-, hB, hW⟩ := region_facts hμ h hE hpitch hs hhist
    have hd := amp_ratio_hasDerivAt h hs hσ2 hB hW j
    interval_cases j
    · simpa [a, b] using hd
    · simpa [a, b] using hasDerivAt_const s (0 : ℝ)
    · simpa [a, b] using hd
  · intro j hj s hs hhist
    obtain ⟨-, hB, hW⟩ := region_facts hμ h hE hpitch hs hhist
    have hd := amp_ratio_hasDerivAt h hs hσ2 hB hW j
    interval_cases j
    · simpa [a, b] using hasDerivAt_const s (0 : ℝ)
    · simpa [a, b] using hd
    · simpa [a, b] using hasDerivAt_const s (0 : ℝ)
  · intro j hj s hs hhist
    obtain ⟨hreg, -, -⟩ := region_facts hμ h hE hpitch hs hhist
    interval_cases j
    · simpa [a, b, A] using global_bound glob_0 hreg
    · simpa [a, b, A] using global_bound glob_1 hreg
    · simpa [a, b, A] using global_bound glob_2 hreg
    · simpa [a, b, A] using amp3_bound hreg
  · have hG : reactorQA.G = 581 / 10 := rfl
    have hc : (0 : ℝ) ≤ 11 * cq + 0 := by norm_num [cq]
    have hmono : |(1 : ℝ) * (581 / 10)| * Δρv +
        (2 * ((1935 + 218 + 93) * cq) / Om0 + (11 * cq + 0) * T) / |qα| ≤
        |(1 : ℝ) * (581 / 10)| * Δρv +
        (2 * ((1935 + 218 + 93) * cq) / Om0 + (11 * cq + 0) * Tav) / |qα| := by
      gcongr
    have h2 : 211 / 500 * (8.2 - psiStart) ≤ 211 / 500 * (8.2 - ψ 0) := by linarith
    refine le_trans (le_of_eq ?_) (hmono.trans (averaged_gap.trans h2))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, A, hG]
    norm_num
    ring

/-- **Averaged confinement of passing 3.5 MeV alphas in the reactor-scale near-axis QA model**
on `[0, 0.19 s]`: the case `T = Tav` of `alpha_trapped_reactorQA_averaged_of_le`. The hypotheses
are exactly those of the worst-case bound `NearAxisQA.alpha_trapped_reactorQA`, except for the
longer orbit horizon (`0.19 s` instead of `0.8 ms`): `237.5` times the worst-case time. See
`alpha_trapped_reactorQA_averaged_of_le` for the proof outline and the caveats (model only:
assumed guiding-centre equations, truncated near-axis field, passing alphas only, no
collisions or slowing down). -/
theorem alpha_trapped_reactorQA_averaged {μ : ℝ} {ψ θ φ ρ : ℝ → ℝ} (hμ : 0 ≤ μ)
    (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ Tav)
    (hE : boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα)
    (hpitch : 81 / 100 * (2 * Eα / mα) ≤ parallelVelocity reactorQA mα qα ψ θ φ ρ 0 ^ 2)
    (hstart : ψ 0 ≤ psiStart) :
    ∀ t ∈ Set.Icc 0 Tav, ψ t ≤ 8.2 :=
  alpha_trapped_reactorQA_averaged_of_le le_rfl hμ h hE hpitch hstart

/-- The earlier `0.11 s` statement, as a corollary (`0.11 ≤ Tav`). -/
theorem alpha_trapped_reactorQA_averaged_011 {μ : ℝ} {ψ θ φ ρ : ℝ → ℝ} (hμ : 0 ≤ μ)
    (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ (11 / 100))
    (hE : boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα)
    (hpitch : 81 / 100 * (2 * Eα / mα) ≤ parallelVelocity reactorQA mα qα ψ θ φ ρ 0 ^ 2)
    (hstart : ψ 0 ≤ psiStart) :
    ∀ t ∈ Set.Icc 0 (11 / 100), ψ t ≤ 8.2 :=
  alpha_trapped_reactorQA_averaged_of_le (by norm_num [Tav]) hμ h hE hpitch hstart

/-! ## Sanity checks and fixtures -/

/-- Rejected fixture: the bound `10` fails on the leaf `[51/80, 221/320] × [1003/640, 51/32]`
of the `σ = +1` cover (its enclosure is `≈ 10.98`): the cover does not certify `|amp 3/q| ≤ 10`.
-/
theorem rect_rejected : rectOK S3pos 10 (51 / 80) (221 / 320) (1003 / 640) (51 / 32) = false := by
  decide +kernel

/-- Rejected fixture: a single rectangle (the whole square `[−a, a]²`) does not certify the bound
`11`; the subdivision is needed (its enclosure is `≈ 50`). -/
theorem rect_whole_rejected :
    rectOK S3pos 11 (-17 / 10) (17 / 10) (-17 / 10) (17 / 10) = false := by
  decide +kernel

/-- Accepted fixture: a rectangle outside the disc `r ≤ a` passes trivially. -/
theorem rect_outside : rectOK [] 0 (3 / 2) (17 / 10) (3 / 2) (17 / 10) = true := by
  decide +kernel

/-- Rejected fixture: the global bound `1900` for `amp 0` (true sup `≈ 1934`) is not certified. -/
theorem glob_0_rejected : boundOK (evalT (toFix cq (amp 0)) globalF) 1900 = false := by
  decide +kernel

/-- The gap of the main theorem fails at `T = 0.20 s`: `0.19 s` is essentially what the
certified constants give (the exact limit is `≈ 0.195 s`). -/
theorem averaged_gap_fails_late :
    ¬ (|(1 : ℝ) * (581 / 10)| * Δρv + (2 * ((1935 + 218 + 93) * cq) / Om0 + (11 * cq + 0) * 0.2) /
      |qα| ≤ 211 / 500 * (8.2 - psiStart)) := by
  norm_num [Δρv, Om0, cq, cm, qα, psiStart, abs_of_pos]

/-- Comparison: the averaged time is `237.5` times the worst-case `0.8 ms`. -/
theorem averaged_vs_worstCase : Tav = 237.5 * 8e-4 := by norm_num [Tav]

/-- Honest comparison: the averaged time is still below the `0.4 s` slowing-down time. -/
theorem averaged_vs_slowingDown : Tav < 0.4 := by norm_num [Tav]

/-- Special case: the zeroth amplitude is the `sin 2φ` forcing `σ 2 b₁ c R²` with
`c = μ + m v_∥²/B`; it vanishes on the magnetic axis (`R² = 0`). -/
theorem amp0_axis (x : ℕ → ℝ) (h2 : x 2 = 0) : eval (amp 0) x = 0 := by
  rw [eval_amp0, h2]; ring

end PlasmaLean.Design.NearAxisQAAveraged
