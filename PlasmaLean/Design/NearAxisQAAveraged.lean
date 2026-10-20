/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.AveragedTrapping
public import PlasmaLean.Design.NearAxisQA

/-!
# Averaged confinement of passing 3.5 MeV alphas in the reactor-scale near-axis QA model

Source: `notes/theory/guiding-centre-averaging.md` §1, §4 (iterated Lemma A); the model is
`Design/NearAxisQA.reactorQA` in the vacuum Boozer guiding-centre model of
`Theory/Kinetic/BoozerGuidingCentre`.

**Main result** (`alpha_trapped_reactorQA_averaged`): with exactly the hypotheses of
`NearAxisQA.alpha_trapped_reactorQA` (3.5 MeV alpha, any `μ ≥ 0`, `|v_∥/v| ≥ 0.9` at `t = 0`,
start at `r ≤ a/4`), the orbit stays at `ψ ≤ 8.2 T m² < ψ_a` for `0 ≤ t ≤ T = 0.11 s`
(`Tav`), instead of `0.8 ms`.

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
   exactly in `ℚ` by the kernel (`LiePoly.lie`, 2, 15, 121 and 458 monomials).
3. Bounds (in units of `q` T m²/s): `|amp 0| ≤ 1935`, `|amp 1| ≤ 218`, `|amp 2| ≤ 93` (one
   ball over the whole region, `glob_j`) and `|amp 3| ≤ 19` (`12 × 12` cover of the disc
   `r ≤ a`, both signs of `σ`, fixed-point ball arithmetic, `rows_k`). All are `decide +kernel`
   checks of exact integer/rational arithmetic.
4. `Kinetic.Boozer.boozerGC_trapped_until_averaged` with `k = 3`: gap
   `|G| Δρ + (2 (1935 + 218 + 93)/Ω₀ + 19 T) ≤ ι₀ (8.2 − ψ(0))`, `Δρ ≈ 1.88 cm`
   (`averaged_gap`), which holds for `T = 0.11 s` and fails for `T = 0.12 s`
   (`averaged_gap_fails_late`).

**Caveats (model only).**
* The Boozer guiding-centre equations are a supplied model (not derived from the Lorentz
  force); orbits are supplied and must stay in the chart `ψ > 0` (off the magnetic axis).
* The field is the truncated second-order near-axis expansion, which agrees with a real vacuum
  field only to the order of the expansion; the `O(r³)` remainder has no rigorous bound.
* Passing particles only (`|v_∥/v| ≥ 0.9` at `t = 0`, hence `|v_∥| ≥ 1.12 × 10⁷ m/s` throughout):
  trapped and barely passing alphas have a phase speed that changes sign and are not covered.
* No collisions or slowing down; `T = 0.11 s` is about a quarter of the slowing-down time
  (`≈ 0.4 s`), not the full time.

**What limits `T`.** The secular rate `19` is a sup over the whole disc and both `σ` (the
sampled sup along the region is `≈ 6`); a finer cover (`24 × 24` gives `≈ 13.8`, i.e.
`T ≈ 0.155 s`) or a fourth integration by parts would increase `T`, at higher kernel cost. The
constant term `2 ∑ Aⱼ/Ω₀ ≈ 2.4 × 10⁻³ T m²` is negligible; the orbit-width term
`|G| Δρ ≈ 1.09 T m²` uses about a third of the gap `ι₀ (8.2 − ψ(0)) ≈ 3.24 T m²`.
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
/-- Number of cells per side of the square grid covering the disc `r ≤ a`. -/
@[expose] def Nc : ℕ := 12
/-- Cell side. -/
@[expose] def hc : ℚ := 2 * aR / Nc
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

/-- Left end of cell column `i`. -/
@[expose] def xlo (i : ℕ) : ℚ := -aR + i * hc
/-- Lower bound for `R²` on cell `(i, j)`. -/
@[expose] def r2lo (i j : ℕ) : ℚ :=
  closest (xlo i) (xlo i + hc) ^ 2 + closest (xlo j) (xlo j + hc) ^ 2
/-- Upper bound for `R²` on cell `(i, j)` (intersected with the disc). -/
@[expose] def r2hi (i j : ℕ) : ℚ :=
  min (aR ^ 2) (farthest (xlo i) (xlo i + hc) + farthest (xlo j) (xlo j + hc))
/-- Enclosure of `B` on cell `(i, j)`. -/
@[expose] def Bball (i j : ℕ) : QBall :=
  evalQ Bpoly
    [ivQ (xlo i) (xlo i + hc), ivQ (xlo j) (xlo j + hc), ivQ (r2lo i j) (r2hi i j), ⟨0, 1⟩]
/-- Fixed-point enclosures of all variables on cell `(i, j)` with `σ = sg`. -/
@[expose] def cellF (i j : ℕ) (sg : ℚ) : List FBall :=
  [ofQ (ivQ (xlo i) (xlo i + hc)), ofQ (ivQ (xlo j) (xlo j + hc)), ofQ (ivQ (r2lo i j) (r2hi i j)),
    ofQ ⟨0, 1⟩, ofQ ⟨0, 1⟩, ofQ (ivQ Wlo Whi), ofQ (ivQ (1 / Whi) (1 / Wlo)), ofQ (Bball i j),
    ofQ (ivQ (1 / ((Bball i j).c + (Bball i j).r)) (1 / ((Bball i j).c - (Bball i j).r))),
    ofQ (ivQ 0 Umax), ofQ ⟨sg, 0⟩]

/-- `|c| + r ≤ A D` for a fixed-point ball. -/
@[expose] def boundOK (b : FBall) (A : ℕ) : Bool := decide (b.c.natAbs + b.r ≤ A * Dk)

/-- The third amplitude divided by `q`, in fixed point. -/
@[expose] def amp3F : FPoly := toFix cq (amp 3)

/-- Cell check: the cell misses the disc, or `B > 0` on it and `|amp 3/q| ≤ A`. -/
@[expose] def cellOK (A : ℕ) (i j : ℕ) (sg : ℚ) : Bool :=
  decide (aR ^ 2 < r2lo i j) ||
    (decide (0 < (Bball i j).c - (Bball i j).r) && boundOK (evalT amp3F (cellF i j sg)) A)

/-- Row check for both signs of `σ`. -/
@[expose] def rowOK (A : ℕ) (i : ℕ) : Bool :=
  (List.range Nc).all fun j => cellOK A i j 1 && cellOK A i j (-1)

/-- Global enclosures (whole region, `σ ∈ [−1, 1]`). -/
@[expose] def globalF : List FBall :=
  [ofQ ⟨0, aR⟩, ofQ ⟨0, aR⟩, ofQ (ivQ 0 (aR ^ 2)), ofQ ⟨0, 1⟩, ofQ ⟨0, 1⟩, ofQ (ivQ Wlo Whi),
    ofQ (ivQ (1 / Whi) (1 / Wlo)), ofQ (ivQ Bmin Bmax), ofQ (ivQ (1 / Bmax) (1 / Bmin)),
    ofQ (ivQ 0 Umax), ofQ ⟨0, 1⟩]

/-- Region constraints on the state variables (radius `≤ a`, passing speed range, field range,
`U ≤ U_max`, `σ = ±1`, and the identities linking `R²`, `1/W`, `B`, `1/B`). -/
@[expose] def InRegion (x : ℕ → ℝ) : Prop :=
  |x 0| ≤ 17 / 10 ∧ |x 1| ≤ 17 / 10 ∧ x 2 = x 0 ^ 2 + x 1 ^ 2 ∧ x 2 ≤ (17 / 10) ^ 2 ∧
  |x 3| ≤ 1 ∧ |x 4| ≤ 1 ∧ 112 / 100 ≤ x 5 ∧ x 5 ≤ 13 / 10 ∧ x 6 = (x 5)⁻¹ ∧
  x 7 = eval Bpoly x ∧ 493 / 100 ≤ x 7 ∧ x 7 ≤ 647 / 100 ∧ x 8 = (x 7)⁻¹ ∧
  0 ≤ x 9 ∧ x 9 ≤ 21612 / 10000 ∧ (x 10 = 1 ∨ x 10 = -1) ∧ ∀ i, 11 ≤ i → x i = 0

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

theorem sq_le_farthest {lo hi : ℚ} {x : ℝ} (h1 : (lo : ℝ) ≤ x) (h2 : x ≤ hi) :
    x ^ 2 ≤ ((farthest lo hi : ℚ) : ℝ) := by
  unfold farthest
  push_cast
  rcases le_total 0 x with hx | hx
  · exact le_max_of_le_right (by nlinarith)
  · exact le_max_of_le_left (by nlinarith)

theorem inv_mem_ivQ {x : ℝ} {l h : ℚ} (hl : (0 : ℝ) < l) (h1 : (l : ℝ) ≤ x) (h2 : x ≤ h) :
    (ivQ (1 / h) (1 / l)).Mem x⁻¹ := by
  have hx : 0 < x := lt_of_lt_of_le hl h1
  refine QBall.mem_ivQ ?_ ?_
  · push_cast; rw [one_div]; exact inv_anti₀ hx h2
  · push_cast; rw [one_div]; exact inv_anti₀ hl h1

theorem FBall.mem_zero : (FBall.mk 0 0).Mem 0 := by simp [FBall.Mem]

/-- **Cell soundness**: on a checked cell, `|amp 3 (x)/q| ≤ A` at every point of the region. -/
theorem cell_sound {A i j : ℕ} (h1 : cellOK A i j 1 = true) (h2 : cellOK A i j (-1) = true)
    {x : ℕ → ℝ} (hx : InRegion x) (hxi : (xlo i : ℝ) ≤ x 0 ∧ x 0 ≤ ((xlo i + hc : ℚ) : ℝ))
    (hyj : (xlo j : ℝ) ≤ x 1 ∧ x 1 ≤ ((xlo j + hc : ℚ) : ℝ)) :
    |eval (amp 3) x / cq| ≤ A := by
  obtain ⟨hx0, hx1, hx2, hx2a, hx3, hx4, hx5l, hx5h, hx6, hx7, hx7l, hx7h, hx8, hx9l, hx9h,
    hx10, hx11⟩ := hx
  have hr2l : ((r2lo i j : ℚ) : ℝ) ≤ x 2 := by
    rw [hx2, r2lo]; push_cast
    exact add_le_add (closest_sq_le hxi.1 hxi.2) (closest_sq_le hyj.1 hyj.2)
  have hr2h : x 2 ≤ ((r2hi i j : ℚ) : ℝ) := by
    unfold r2hi; push_cast
    refine le_min (by simpa [aR] using hx2a) ?_
    rw [hx2]
    exact add_le_add (sq_le_farthest hxi.1 hxi.2) (sq_le_farthest hyj.1 hyj.2)
  -- choose the check for the actual sign
  obtain ⟨sg, hsg, hc⟩ : ∃ sg : ℚ, x 10 = sg ∧ cellOK A i j sg = true := by
    rcases hx10 with h | h
    · exact ⟨1, by simp [h], h1⟩
    · exact ⟨-1, by simp [h], h2⟩
  simp only [cellOK, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc with hc | ⟨hBpos, hbd⟩
  · exfalso
    have : ((aR ^ 2 : ℚ) : ℝ) < r2lo i j := by exact_mod_cast hc
    push_cast [aR] at this
    linarith
  -- memberships of all variables
  have hxb : (ivQ (xlo i) (xlo i + hc)).Mem (x 0) := QBall.mem_ivQ hxi.1 hxi.2
  have hyb : (ivQ (xlo j) (xlo j + hc)).Mem (x 1) := QBall.mem_ivQ hyj.1 hyj.2
  have hrb : (ivQ (r2lo i j) (r2hi i j)).Mem (x 2) := QBall.mem_ivQ hr2l hr2h
  have hCb : (QBall.mk 0 1).Mem (x 3) := QBall.mem_of_abs_le (by simpa using hx3)
  have hBb : (Bball i j).Mem (x 7) := by
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
  have hBpos' : (0 : ℝ) < (((Bball i j).c - (Bball i j).r : ℚ) : ℝ) := by exact_mod_cast hBpos
  have hall : ∀ k, ((cellF i j sg).getD k ⟨0, 0⟩).Mem (x k) := by
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
      simp only [cellF, List.getD_cons_succ, List.getD_cons_zero]
      rw [hx6]
      exact FBall.mem_ofQ (inv_mem_ivQ (by norm_num [Wlo])
        (by simpa [Wlo] using hx5l) (by simpa [Whi] using hx5h))
    | 7 => exact FBall.mem_ofQ hBb
    | 8 =>
      simp only [cellF, List.getD_cons_succ, List.getD_cons_zero]
      rw [hx8]
      exact FBall.mem_ofQ (inv_mem_ivQ hBpos' hBl hBh)
    | 9 => exact FBall.mem_ofQ (QBall.mem_ivQ (by simpa using hx9l) (by simpa [Umax] using hx9h))
    | 10 => exact FBall.mem_ofQ (by simp [QBall.Mem, hsg])
    | n + 11 =>
      rw [hx11 (n + 11) (by omega)]
      simpa [cellF] using FBall.mem_zero
  have hm := FBall.mem_evalT_toFix cq (by norm_num [cq]) (amp 3) hall
  rw [show toFix cq (amp 3) = amp3F from rfl] at hm
  exact FBall.abs_le_of_mem hm (by simpa [boundOK] using hbd)

/-- The square grid covers `[−a, a]`. -/
theorem grid_cover {x : ℝ} (hx : |x| ≤ 17 / 10) :
    ∃ i < Nc, (xlo i : ℝ) ≤ x ∧ x ≤ ((xlo i + hc : ℚ) : ℝ) := by
  have hh : ((hc : ℚ) : ℝ) = 17 / 60 := by norm_num [hc, aR, Nc]
  have hxl : ∀ i : ℕ, ((xlo i : ℚ) : ℝ) = -17 / 10 + i * (17 / 60) := by
    intro i; simp only [xlo, hc, aR, Nc]; push_cast; ring
  rw [abs_le] at hx
  set u := (x + 17 / 10) / (17 / 60) with hu
  have hu0 : 0 ≤ u := by rw [hu]; apply div_nonneg <;> linarith
  have hu12 : u ≤ 12 := by rw [hu, div_le_iff₀ (by norm_num)]; linarith
  rcases lt_or_ge (⌊u⌋₊) 12 with h | h
  · refine ⟨⌊u⌋₊, by simpa [Nc] using h, ?_, ?_⟩
    · rw [hxl]
      have := Nat.floor_le hu0
      have : (⌊u⌋₊ : ℝ) * (17 / 60) ≤ x + 17 / 10 := by
        rw [hu] at this; rwa [le_div_iff₀ (by norm_num)] at this
      linarith
    · push_cast; rw [hxl, hh]
      have := Nat.lt_floor_add_one u
      have : x + 17 / 10 < ((⌊u⌋₊ : ℝ) + 1) * (17 / 60) := by
        rw [hu] at this; rwa [div_lt_iff₀ (by norm_num)] at this
      linarith
  · refine ⟨11, by norm_num [Nc], ?_, ?_⟩
    · rw [hxl]
      have : (12 : ℝ) ≤ u := by
        have := Nat.floor_le hu0
        exact le_trans (by exact_mod_cast h) this
      have : (12 : ℝ) * (17 / 60) ≤ x + 17 / 10 := by
        rw [hu] at this; rwa [le_div_iff₀ (by norm_num)] at this
      push_cast; linarith
    · push_cast; rw [hxl, hh]; push_cast; linarith

/-- Soundness of the full cover: if all rows check, `|amp 3| ≤ A q` on the region. -/
theorem amp3_bound_of_rows {A : ℕ} (hrows : ∀ i < Nc, rowOK A i = true) {x : ℕ → ℝ}
    (hx : InRegion x) : |eval (amp 3) x| ≤ A * cq := by
  obtain ⟨i, hi, hxi⟩ := grid_cover hx.1
  obtain ⟨j, hj, hyj⟩ := grid_cover hx.2.1
  have hrow := hrows i hi
  simp only [rowOK, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hrow
  have := cell_sound (hrow j hj).1 (hrow j hj).2 hx hxi hyj
  have hq : (0 : ℝ) < cq := by norm_num [cq]
  rw [abs_div, abs_of_pos hq, div_le_iff₀ hq] at this
  exact this

/-- Soundness of the global enclosure on the region. -/
theorem global_bound {j A : ℕ} (hok : boundOK (evalT (toFix cq (amp j)) globalF) A = true)
    {x : ℕ → ℝ} (hx : InRegion x) : |eval (amp j) x| ≤ A * cq := by
  obtain ⟨hx0, hx1, hx2, hx2a, hx3, hx4, hx5l, hx5h, hx6, hx7, hx7l, hx7h, hx8, hx9l, hx9h,
    hx10, hx11⟩ := hx
  have hall : ∀ k, (globalF.getD k ⟨0, 0⟩).Mem (x k) := by
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
  have hm := FBall.mem_evalT_toFix cq (by norm_num [cq]) (amp j) hall
  have := FBall.abs_le_of_mem hm (by simpa [boundOK] using hok)
  have hq : (0 : ℝ) < cq := by norm_num [cq]
  rw [abs_div, abs_of_pos hq, div_le_iff₀ hq] at this
  exact this

/-! ### Kernel-checked certificates

Each `decide +kernel` below evaluates exact `ℚ`/`ℤ`/`ℕ` arithmetic in the Lean kernel: the
amplitudes `amp j` (exact Lie derivatives) and their fixed-point ball enclosures. -/

/-- Kernel-checked row 0 of the cover (both signs of `σ`, `|amp 3/q| ≤ 19`). -/
theorem row_0 : rowOK 19 0 = true := by decide +kernel

/-- Kernel-checked row 1 of the cover (both signs of `σ`, `|amp 3/q| ≤ 19`). -/
theorem row_1 : rowOK 19 1 = true := by decide +kernel

/-- Kernel-checked row 2 of the cover (both signs of `σ`, `|amp 3/q| ≤ 19`). -/
theorem row_2 : rowOK 19 2 = true := by decide +kernel

/-- Kernel-checked row 3 of the cover (both signs of `σ`, `|amp 3/q| ≤ 19`). -/
theorem row_3 : rowOK 19 3 = true := by decide +kernel

/-- Kernel-checked row 4 of the cover (both signs of `σ`, `|amp 3/q| ≤ 19`). -/
theorem row_4 : rowOK 19 4 = true := by decide +kernel

/-- Kernel-checked row 5 of the cover (both signs of `σ`, `|amp 3/q| ≤ 19`). -/
theorem row_5 : rowOK 19 5 = true := by decide +kernel

/-- Kernel-checked row 6 of the cover (both signs of `σ`, `|amp 3/q| ≤ 19`). -/
theorem row_6 : rowOK 19 6 = true := by decide +kernel

/-- Kernel-checked row 7 of the cover (both signs of `σ`, `|amp 3/q| ≤ 19`). -/
theorem row_7 : rowOK 19 7 = true := by decide +kernel

/-- Kernel-checked row 8 of the cover (both signs of `σ`, `|amp 3/q| ≤ 19`). -/
theorem row_8 : rowOK 19 8 = true := by decide +kernel

/-- Kernel-checked row 9 of the cover (both signs of `σ`, `|amp 3/q| ≤ 19`). -/
theorem row_9 : rowOK 19 9 = true := by decide +kernel

/-- Kernel-checked row 10 of the cover (both signs of `σ`, `|amp 3/q| ≤ 19`). -/
theorem row_10 : rowOK 19 10 = true := by decide +kernel

/-- Kernel-checked row 11 of the cover (both signs of `σ`, `|amp 3/q| ≤ 19`). -/
theorem row_11 : rowOK 19 11 = true := by decide +kernel

/-- All rows of the cover check. -/
theorem rows_ok : ∀ i < Nc, rowOK 19 i = true := by
  intro i hi
  simp only [Nc] at hi
  interval_cases i
  exacts [row_0, row_1, row_2, row_3, row_4, row_5, row_6, row_7, row_8, row_9, row_10, row_11]

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

/-- The averaged confinement time `T = 0.11 s`. -/
@[expose] def Tav : ℝ := 11 / 100

/-- Numerical gap: `|G| Δρ + (2 (1935 + 218 + 93)/Ω₀ + 19 T) ≤ ι₀ (8.2 − ψ_start)`. -/
theorem averaged_gap :
    |(1 : ℝ) * (581 / 10)| * Δρv + (2 * ((1935 + 218 + 93) * cq) / Om0 + (19 * cq + 0) * Tav) /
      |qα| ≤ 211 / 500 * (8.2 - psiStart) := by
  norm_num [Δρv, Om0, cq, cm, qα, psiStart, Tav, abs_of_pos]

/-- **Averaged confinement of passing 3.5 MeV alphas in the reactor-scale near-axis QA model.**
Every guiding-centre orbit (solving the vacuum Boozer equations on `[0, 0.11 s]`) of the model with
field `reactorQA` (a = 1.7 m, B₀ = 5.7 T) for an alpha (`m = 6.6447 × 10⁻²⁷ kg`, `q = 2e`) of energy
`3.5 MeV`, any `μ ≥ 0`, passing pitch `v_∥² ≥ 0.81 v²` at `t = 0`, starting at `ψ ≤ B₀(a/4)²/2`,
satisfies `ψ(t) ≤ 8.2 T m² < ψ_a` for `0 ≤ t ≤ 0.11 s`: 137 times the `0.8 ms` of the
worst-case bound `NearAxisQA.alpha_trapped_reactorQA`, with the same hypotheses.

Proof: `dP/dt = a₀ sin(2σφ)` with `Ω = 2|v_∥|B/G ≥ Ω₀ ≈ 1.9 × 10⁶ s⁻¹`; three oscillatory
integrations by parts (`osc_ibp_drift_iter`, `k = 3`) with exact polynomial Lie-derivative
amplitudes bounded by `1935, 218, 93` (global) and `19` T m²/s (kernel-checked ball cover of the
disc, `12 × 12` cells, both signs of `v_∥`); the gap
`|G| Δρ + (2 ∑_{j<3} Aⱼ/Ω₀ + A₃ T)/|q| ≤ ι₀ (8.2 − ψ(0))` with `Δρ ≈ 1.88 cm`.

**Caveats.** This is a theorem about the model only: (i) the Boozer guiding-centre equations are
assumed (their derivation from the Lorentz force is not formalized), orbits are supplied and
must stay off the magnetic axis; (ii) the field is the truncated second-order near-axis expansion,
accurate only to the order of the expansion (no bound on the `O(r³)` remainder); (iii) passing
particles only (`|v_∥/v| ≥ 0.9` initially): the phase speed must stay positive, so trapped and
barely passing alphas are not covered; (iv) collisions and slowing down are ignored. -/
theorem alpha_trapped_reactorQA_averaged {μ : ℝ} {ψ θ φ ρ : ℝ → ℝ} (hμ : 0 ≤ μ)
    (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ Tav)
    (hE : boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα)
    (hpitch : 81 / 100 * (2 * Eα / mα) ≤ parallelVelocity reactorQA mα qα ψ θ φ ρ 0 ^ 2)
    (hstart : ψ 0 ≤ psiStart) :
    ∀ t ∈ Set.Icc 0 Tav, ψ t ≤ 8.2 := by
  set σ := sgn0 ψ θ φ ρ with hσdef
  have hσ2 : σ ^ 2 = 1 := sgn0_sq
  set X := orbX σ μ ψ θ φ ρ with hX
  let a : ℕ → ℝ → ℝ := fun j r => if j % 2 = 0 then eval (amp j) (X r) else 0
  let b : ℕ → ℝ → ℝ := fun j r => if j % 2 = 1 then eval (amp j) (X r) else 0
  let A : ℕ → ℝ := fun j => ([1935, 218, 93, 19] : List ℝ).getD j 0 * cq
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
    · simpa [a, b, A] using amp3_bound_of_rows rows_ok hreg
  · have hG : reactorQA.G = 581 / 10 := rfl
    have h1 := averaged_gap
    have h2 : 211 / 500 * (8.2 - psiStart) ≤ 211 / 500 * (8.2 - ψ 0) := by linarith
    refine le_trans (le_of_eq ?_) (h1.trans h2)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, A, hG]
    norm_num
    ring

/-! ## Sanity checks and fixtures -/

/-- Rejected fixture: the bound `18` fails on cell `(9, 0)` for `σ = +1`, so the cover does not
certify `|amp 3/q| ≤ 18`. -/
theorem cell_rejected : cellOK 18 9 0 1 = false := by decide +kernel

/-- Rejected fixture: the global bound `1900` for `amp 0` (true sup `≈ 1934`) is not certified. -/
theorem glob_0_rejected : boundOK (evalT (toFix cq (amp 0)) globalF) 1900 = false := by
  decide +kernel

/-- The gap of the main theorem fails at `T = 0.12 s`: `0.11 s` is essentially what the
certified constants give (the exact limit is `≈ 0.113 s`). -/
theorem averaged_gap_fails_late :
    ¬ (|(1 : ℝ) * (581 / 10)| * Δρv + (2 * ((1935 + 218 + 93) * cq) / Om0 + (19 * cq + 0) * 0.12) /
      |qα| ≤ 211 / 500 * (8.2 - psiStart)) := by
  norm_num [Δρv, Om0, cq, cm, qα, psiStart, abs_of_pos]

/-- Comparison: the averaged time is `137.5` times the worst-case `0.8 ms`. -/
theorem averaged_vs_worstCase : Tav = 137.5 * 8e-4 := by norm_num [Tav]

/-- Honest comparison: the averaged time is still below the `0.4 s` slowing-down time. -/
theorem averaged_vs_slowingDown : Tav < 0.4 := by norm_num [Tav]

/-- Special case: the zeroth amplitude is the `sin 2φ` forcing `σ 2 b₁ c R²` with
`c = μ + m v_∥²/B`; it vanishes on the magnetic axis (`R² = 0`). -/
theorem amp0_axis (x : ℕ → ℝ) (h2 : x 2 = 0) : eval (amp 0) x = 0 := by
  rw [eval_amp0, h2]; ring

end PlasmaLean.Design.NearAxisQAAveraged
