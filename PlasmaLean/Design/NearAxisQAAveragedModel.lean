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
# Averaged confinement in the near-axis QA model: model, amplitudes and enclosures

First part of the averaged-confinement certificate of `Design/NearAxisQAAveraged` (the module
docstring there describes the method): the polynomial vector field along the orbits
(`flows`, `hasDerivAt_orbX`), the iterated amplitudes `amp`, the ball-arithmetic enclosures
(`evalT`, `stage1`, `rectOK`) and the cover certificate `CoverCert` with its `meta` builder
`cover_cert`. Split from `NearAxisQAAveraged` so that the heavy kernel checks
(`NearAxisQAAveragedAmp3`, `NearAxisQAAveragedStage`) run in separate processes.
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

end PlasmaLean.Design.NearAxisQAAveraged
