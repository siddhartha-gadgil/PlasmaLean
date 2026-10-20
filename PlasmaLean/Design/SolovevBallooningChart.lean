/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevBallooningBall
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Algebra.BigOperators.Field

/-!
# Ballooning certificate: the `(τ, s)` chart and soundness of the box cover

The half circle `x ≥ 0` of the poloidal angle is parametrised by `τ ∈ [−1, 1]`,
`(x, y) = (κ − 1, κ τ)`, `κ = 2/(1 + τ²)`; the surface label `s` is the second coordinate.
`chartEnv τ s` is the assignment of the nine tree variables
`(x, y, R, √2, 1/R, 1/|B|², s, τ, κ)` with `R = √(L² + 2 s y)`. We prove:

* `hasDerivAt_chart_tau`, `hasDerivAt_chart_s`: the chart variables satisfy the polynomial ODEs
  encoded by the derivative trees `Dt`, `Ds` (for `|s| < 50`);
* `mem_boxVars`: the box balls enclose the chart variables;
* `chord_min`, `cornerOK_sound`, `reserve_ge`: the bilinear chord bound on a box, the Pólya
  corner test and the reserve;
* `boxOK_sound`, `axisOK_sound`, `leaf2_sound`, `axis2_sound`, `Cover.sound`: if the cover
  certificate holds (and the coefficients vanish on the axis), the numerator
  `Ψ(τ, s, σ̃) = Σₖ eₖ(τ, s) σ̃ᵏ` is positive for all `τ ∈ [−1, 1]`, `0 < s ≤ 25`, `σ̃ ∈ ℝ`.
-/

public section
noncomputable section

namespace PlasmaLean.Design.SolovevBallooning

open Real Set Tm

/-! ## The chart -/

/-- A real assignment of the nine tree variables. -/
@[expose] def envR (x y R r iR iB s t k : ℝ) : ℕ → ℝ
  | 0 => x
  | 1 => y
  | 2 => R
  | 3 => r
  | 4 => iR
  | 5 => iB
  | 6 => s
  | 7 => t
  | 8 => k
  | _ => 0

/-- `κ(τ) = 2/(1 + τ²)`. -/
@[expose] def kc (τ : ℝ) : ℝ := 2 * (1 + τ ^ 2)⁻¹

/-- `x(τ) = κ − 1 = (1 − τ²)/(1 + τ²)`. -/
@[expose] def xcc (τ : ℝ) : ℝ := kc τ - 1

/-- `y(τ) = κ τ = 2τ/(1 + τ²)`. -/
@[expose] def ycc (τ : ℝ) : ℝ := kc τ * τ

/-- `R(τ, s) = √(L² + 2 s y(τ))`. -/
@[expose] def Rcc (τ s : ℝ) : ℝ := √(100 + 2 * (s * ycc τ))

/-- The chart variables with the slot `1/|B|²` set to `0`. -/
@[expose] def env0 (τ s : ℝ) : ℕ → ℝ :=
  envR (xcc τ) (ycc τ) (Rcc τ s) √2 (Rcc τ s)⁻¹ 0 s τ (kc τ)

/-- `|B|²` along the chart (`tB2` does not use the slot `5`). -/
@[expose] def B2c (τ s : ℝ) : ℝ := tB2.eval (env0 τ s)

/-- **The chart variables** `(x, y, R, √2, 1/R, 1/|B|², s, τ, κ)`. -/
@[expose] def chartEnv (τ s : ℝ) : ℕ → ℝ :=
  envR (xcc τ) (ycc τ) (Rcc τ s) √2 (Rcc τ s)⁻¹ (B2c τ s)⁻¹ s τ (kc τ)

/-- `κ > 0`. -/
theorem kc_pos (τ : ℝ) : 0 < kc τ := by unfold kc; positivity

/-- `κ (1 + τ²) = 2`. -/
theorem kc_mul (τ : ℝ) : kc τ * (1 + τ ^ 2) = 2 := by
  unfold kc; field_simp

/-- The chart parametrises the unit circle: `x² + y² = 1`. -/
theorem xcc_sq_add (τ : ℝ) : xcc τ ^ 2 + ycc τ ^ 2 = 1 := by
  unfold xcc ycc kc; field_simp; ring

/-- `|y(τ)| ≤ 1`. -/
theorem ycc_abs_le (τ : ℝ) : |ycc τ| ≤ 1 := by
  have h := xcc_sq_add τ
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (xcc τ), sq_nonneg (ycc τ + 1),
    sq_nonneg (ycc τ - 1)]

/-- The radicand is positive for `|s| < 50`. -/
theorem radicand_pos {s : ℝ} (hs : |s| < 50) (τ : ℝ) : 0 < 100 + 2 * (s * ycc τ) := by
  have h1 := ycc_abs_le τ
  have h2 : |s * ycc τ| < 50 := by
    rw [abs_mul]; calc |s| * |ycc τ| ≤ |s| * 1 := by gcongr
      _ < 50 := by linarith
  rw [abs_lt] at h2; linarith

/-- `R > 0` along the chart for `|s| < 50`. -/
theorem Rcc_pos {s : ℝ} (hs : |s| < 50) (τ : ℝ) : 0 < Rcc τ s :=
  Real.sqrt_pos.mpr (radicand_pos hs τ)

/-- `R² = L² + 2 s y` along the chart. -/
theorem Rcc_sq {s : ℝ} (hs : |s| < 50) (τ : ℝ) : Rcc τ s ^ 2 = 100 + 2 * (s * ycc τ) :=
  Real.sq_sqrt (radicand_pos hs τ).le

/-- `|B|² > 0` along the chart (the toroidal field never vanishes). -/
theorem B2c_pos {s : ℝ} (hs : |s| < 50) (τ : ℝ) : 0 < B2c τ s := by
  have hR := Rcc_pos hs τ
  have hBP : 0 < tBP.eval (env0 τ s) := by
    simp only [tBP, tiR, eval, env0, envR]; push_cast; positivity
  have : B2c τ s = (tBR.eval (env0 τ s)) ^ 2 + (tBP.eval (env0 τ s)) ^ 2 +
      (tBZ.eval (env0 τ s)) ^ 2 := by
    simp only [B2c, tB2, eval]
  rw [this]; positivity

/-! ## Variables used by the trees -/

theorem usesOnly_tB2 : tB2.UsesOnly (· ≠ 5) := by
  simp [tB2, tBR, tBP, tBZ, tzh, tWh, tX, tY, tR, tr, tiR, tS, UsesOnly]

/-- The `τ`-derivative trees (other than for `1/|B|²`) do not use the slot `5`. -/
theorem usesOnly_Dt0 (i : ℕ) : (Dt0 i).UsesOnly (· ≠ 5) := by
  unfold Dt0
  split <;> simp [tK, tY, tX, tS, tiR, tT, UsesOnly]

/-- The `s`-derivative trees (other than for `1/|B|²`) do not use the slot `5`. -/
theorem usesOnly_Ds0 (i : ℕ) : (Ds0 i).UsesOnly (· ≠ 5) := by
  unfold Ds0
  split <;> simp [tY, tiR, tiR3, UsesOnly]

/-- `chartEnv` and `env0` agree off the slot `5`. -/
theorem chartEnv_eq_env0 (τ s : ℝ) : ∀ i, i ≠ 5 → chartEnv τ s i = env0 τ s i := by
  intro i hi
  rcases i with _ | _ | _ | _ | _ | _ | i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact absurd rfl hi
  · unfold chartEnv env0 envR
    split <;> simp_all

/-- `tB2` along the chart is `B2c`. -/
theorem B2c_eq (τ s : ℝ) : tB2.eval (chartEnv τ s) = B2c τ s :=
  eval_congr tB2 usesOnly_tB2 (chartEnv_eq_env0 τ s)

/-! ## Derivatives of the chart variables -/

theorem hasDerivAt_kc (τ : ℝ) : HasDerivAt kc (-(τ * kc τ ^ 2)) τ := by
  have h1 : 0 < 1 + τ ^ 2 := by positivity
  have hd : HasDerivAt (fun τ => 1 + τ ^ 2) (2 * τ) τ := by
    simpa using ((hasDerivAt_id τ).pow 2).const_add 1
  have := (hd.inv h1.ne').const_mul 2
  unfold kc
  convert this using 1
  field_simp

/-- `y(τ)` has derivative `κ x`. -/
theorem hasDerivAt_ycc (τ : ℝ) : HasDerivAt ycc (kc τ * xcc τ) τ := by
  have := (hasDerivAt_kc τ).mul (hasDerivAt_id' τ)
  unfold ycc
  refine this.congr_deriv ?_
  have hk := kc_mul τ
  unfold xcc; linear_combination (-kc τ) * hk

/-- `x(τ)` has derivative `−κ y`. -/
theorem hasDerivAt_xcc (τ : ℝ) : HasDerivAt xcc (-(kc τ * ycc τ)) τ := by
  have := (hasDerivAt_kc τ).sub_const 1
  unfold xcc
  convert this using 1
  unfold ycc; ring

/-- `τ`-derivatives of the chart variables other than `1/|B|²`. -/
theorem hasDerivAt_env0_tau {s : ℝ} (hs : |s| < 50) (τ : ℝ) (i : ℕ) :
    HasDerivAt (fun τ => env0 τ s i) ((Dt0 i).eval (env0 τ s)) τ := by
  have hR := Rcc_pos hs τ
  have hRd : HasDerivAt (fun τ => Rcc τ s) (s * kc τ * xcc τ * (Rcc τ s)⁻¹) τ := by
    have hu : HasDerivAt (fun τ => 100 + 2 * (s * ycc τ)) (2 * (s * (kc τ * xcc τ))) τ := by
      simpa using (((hasDerivAt_ycc τ).const_mul s).const_mul 2).const_add 100
    have := hu.sqrt (radicand_pos hs τ).ne'
    unfold Rcc
    convert this using 1
    rw [← Rcc]; field_simp
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i
  · simpa [env0, envR, Dt0, eval, tK, tY, mul_comm] using hasDerivAt_xcc τ
  · simpa [env0, envR, Dt0, eval, tK, tX] using hasDerivAt_ycc τ
  · simp only [env0, envR, Dt0, eval, tK, tX, tS, tiR]
    convert hRd using 1; ring
  · simpa [env0, envR, Dt0, eval] using hasDerivAt_const τ √2
  · simp only [env0, envR, Dt0, eval, tK, tX, tS, tiR]
    convert hRd.inv hR.ne' using 1; field_simp
  · simpa [env0, envR, Dt0, eval] using hasDerivAt_const τ (0 : ℝ)
  · simpa [env0, envR, Dt0, eval] using hasDerivAt_const τ s
  · simpa [env0, envR, Dt0, eval] using hasDerivAt_id' τ
  · simpa [env0, envR, Dt0, eval, tT, tK, mul_comm] using hasDerivAt_kc τ
  · simpa [env0, envR, Dt0, eval] using hasDerivAt_const τ (0 : ℝ)

/-- **`τ`-derivatives of the chart variables**: `d/dτ chartEnv = Dt(chartEnv)`. -/
theorem hasDerivAt_chart_tau {s : ℝ} (hs : |s| < 50) (τ : ℝ) (i : ℕ) :
    HasDerivAt (fun τ => chartEnv τ s i) ((Dt i).eval (chartEnv τ s)) τ := by
  have e0 : ∀ τ, ∀ j, j ≠ 5 → chartEnv τ s j = env0 τ s j := fun τ => chartEnv_eq_env0 τ s
  by_cases hi : i = 5
  · subst hi
    have hB := (tB2.hasDerivAt (ρ := fun τ => env0 τ s) (ρ' := fun τ j => (Dt0 j).eval (env0 τ s))
      (t := τ) (hasDerivAt_env0_tau hs τ)).inv (B2c_pos hs τ).ne'
    change HasDerivAt (fun τ => (B2c τ s)⁻¹) _ τ
    refine hB.congr_deriv ?_
    have hd : (diff Dt0 tB2).eval (chartEnv τ s) =
        tB2.deriv (env0 τ s) (fun j => (Dt0 j).eval (env0 τ s)) := by
      rw [eval_diff]
      apply deriv_congr tB2 usesOnly_tB2 (e0 τ)
      intro j hj
      exact eval_congr _ (usesOnly_Dt0 j) (e0 τ)
    simp only [Dt, eval, hd, tiB]
    simp only [chartEnv, envR]
    rw [show (B2c τ s) = tB2.eval (env0 τ s) from rfl]
    field_simp
  · have h := hasDerivAt_env0_tau hs τ i
    have e1 : (fun τ => chartEnv τ s i) = fun τ => env0 τ s i := funext fun τ => e0 τ i hi
    rw [e1]
    have e2 : (Dt i).eval (chartEnv τ s) = (Dt0 i).eval (env0 τ s) := by
      have : Dt i = Dt0 i := by
        unfold Dt; split
        · exact absurd rfl hi
        · rfl
      rw [this]; exact eval_congr _ (usesOnly_Dt0 i) (e0 τ)
    rw [e2]; exact h

/-- `s`-derivatives of the chart variables other than `1/|B|²`. -/
theorem hasDerivAt_env0_s {s : ℝ} (hs : |s| < 50) (τ : ℝ) (i : ℕ) :
    HasDerivAt (fun s => env0 τ s i) ((Ds0 i).eval (env0 τ s)) s := by
  have hR := Rcc_pos hs τ
  have hRd : HasDerivAt (fun s => Rcc τ s) (ycc τ * (Rcc τ s)⁻¹) s := by
    have hu : HasDerivAt (fun s => 100 + 2 * (s * ycc τ)) (2 * ycc τ) s := by
      simpa using (((hasDerivAt_id s).mul_const (ycc τ)).const_mul 2).const_add 100
    have := hu.sqrt (radicand_pos hs τ).ne'
    unfold Rcc
    convert this using 1
    rw [← Rcc]; field_simp
  rcases i with _ | _ | _ | _ | _ | _ | _ | i
  · simpa [env0, envR, Ds0, eval] using hasDerivAt_const s (xcc τ)
  · simpa [env0, envR, Ds0, eval] using hasDerivAt_const s (ycc τ)
  · simpa [env0, envR, Ds0, eval, tY, tiR] using hRd
  · simpa [env0, envR, Ds0, eval] using hasDerivAt_const s √2
  · simp only [env0, envR, Ds0, eval, tY, tiR, tiR3]
    convert hRd.inv hR.ne' using 1; field_simp
  · simpa [env0, envR, Ds0, eval] using hasDerivAt_const s (0 : ℝ)
  · simpa [env0, envR, Ds0, eval] using hasDerivAt_id' s
  · rcases i with _ | _ | i
    · simpa [env0, envR, Ds0, eval] using hasDerivAt_const s τ
    · simpa [env0, envR, Ds0, eval] using hasDerivAt_const s (kc τ)
    · simpa [env0, envR, Ds0, eval] using hasDerivAt_const s (0 : ℝ)

/-- **`s`-derivatives of the chart variables**: `d/ds chartEnv = Ds(chartEnv)`. -/
theorem hasDerivAt_chart_s {s : ℝ} (hs : |s| < 50) (τ : ℝ) (i : ℕ) :
    HasDerivAt (fun s => chartEnv τ s i) ((Ds i).eval (chartEnv τ s)) s := by
  have e0 : ∀ s, ∀ j, j ≠ 5 → chartEnv τ s j = env0 τ s j := fun s => chartEnv_eq_env0 τ s
  have hev : ∀ᶠ s' in nhds s, |s'| < 50 :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds hs
  by_cases hi : i = 5
  · subst hi
    have hB := (tB2.hasDerivAt (ρ := fun s => env0 τ s) (ρ' := fun s j => (Ds0 j).eval (env0 τ s))
      (t := s) (hasDerivAt_env0_s hs τ)).inv (B2c_pos hs τ).ne'
    change HasDerivAt (fun s => (B2c τ s)⁻¹) _ s
    refine hB.congr_deriv ?_
    have hd : (diff Ds0 tB2).eval (chartEnv τ s) =
        tB2.deriv (env0 τ s) (fun j => (Ds0 j).eval (env0 τ s)) := by
      rw [eval_diff]
      apply deriv_congr tB2 usesOnly_tB2 (e0 s)
      intro j hj
      exact eval_congr _ (usesOnly_Ds0 j) (e0 s)
    simp only [Ds, eval, hd, tiB]
    simp only [chartEnv, envR]
    rw [show (B2c τ s) = tB2.eval (env0 τ s) from rfl]
    field_simp
  · have h := hasDerivAt_env0_s hs τ i
    have e1 : (fun s => chartEnv τ s i) = fun s => env0 τ s i := funext fun s => e0 s i hi
    rw [e1]
    have e2 : (Ds i).eval (chartEnv τ s) = (Ds0 i).eval (env0 τ s) := by
      have : Ds i = Ds0 i := by
        unfold Ds; split
        · exact absurd rfl hi
        · rfl
      rw [this]; exact eval_congr _ (usesOnly_Ds0 i) (e0 s)
    rw [e2]; exact h

end PlasmaLean.Design.SolovevBallooning

namespace PlasmaLean.Design.SolovevBallooning

open Real Set Tm

/-! ## Ball enclosures of the chart variables -/

theorem mem_one : (Bl.ofInt 1).Mem 1 := Bl.mem_of_eq (Bl.mem_ofInt 1) (by norm_num)

/-- The ball of `2`. -/
theorem mem_two : (Bl.ofInt 2).Mem 2 := Bl.mem_of_eq (Bl.mem_ofInt 2) (by norm_num)

/-- The ball `kapB T` encloses `κ(τ)`. -/
theorem mem_kapB {T : Bl} {τ : ℝ} (hT : T.Mem τ) : (kapB T).Mem (kc τ) :=
  Bl.mem_mul mem_two (Bl.mem_inv (Bl.mem_add mem_one (Bl.mem_sq hT)))

/-- The ball `RB T S` encloses `R(τ, s)`. -/
theorem mem_RB {T S : Bl} {τ s : ℝ} (hT : T.Mem τ) (hS : S.Mem s) : (RB T S).Mem (Rcc τ s) :=
  Bl.mem_sqrt (Bl.mem_add (Bl.mem_of_eq (Bl.mem_ofInt 100) (by norm_num))
    (Bl.mem_mul mem_two (Bl.mem_mul hS (Bl.mem_mul (mem_kapB hT) hT))))

/-- The ball of `√2`. -/
theorem mem_sqrt2B : sqrt2B.Mem √2 := Bl.mem_sqrt mem_two

/-- Soundness of a ball assignment of the nine variables. -/
theorem mem_envI {x y R r iR iB s t k : Bl} {x' y' R' r' iR' iB' s' t' k' : ℝ} (hx : x.Mem x')
    (hy : y.Mem y') (hR : R.Mem R') (hr : r.Mem r') (hiR : iR.Mem iR') (hiB : iB.Mem iB')
    (hs : s.Mem s') (ht : t.Mem t') (hk : k.Mem k') :
    ∀ i, (envI x y R r iR iB s t k i).Mem (envR x' y' R' r' iR' iB' s' t' k' i) := by
  intro i
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i
  exacts [hx, hy, hR, hr, hiR, hiB, hs, ht, hk, Bl.mem_zero]

/-- The box balls enclose the chart variables (slot `5` set to `0`). -/
theorem mem_boxVars0 {T S : Bl} {τ s : ℝ} (hT : T.Mem τ) (hS : S.Mem s) :
    ∀ i, (boxVars0 T S i).Mem (env0 τ s i) :=
  mem_envI (Bl.mem_sub (mem_kapB hT) mem_one) (Bl.mem_mul (mem_kapB hT) hT) (mem_RB hT hS)
    mem_sqrt2B (Bl.mem_inv (mem_RB hT hS)) Bl.mem_zero hS hT (mem_kapB hT)

/-- **The box balls enclose the chart variables.** -/
theorem mem_boxVars {T S : Bl} {τ s : ℝ} (hT : T.Mem τ) (hS : S.Mem s) :
    ∀ i, (boxVars T S i).Mem (chartEnv τ s i) :=
  mem_envI (Bl.mem_sub (mem_kapB hT) mem_one) (Bl.mem_mul (mem_kapB hT) hT) (mem_RB hT hS)
    mem_sqrt2B (Bl.mem_inv (mem_RB hT hS))
    (Bl.mem_inv (tB2.ieval_mem (mem_boxVars0 hT hS))) hS hT (mem_kapB hT)

/-- Soundness of the hull ball of a scaled interval. -/
theorem mem_ivHull {p0 p1 q : ℤ} (hq : 0 < q) {x : ℝ} (h0 : (p0 : ℝ) / q ≤ x)
    (h1 : x ≤ (p1 : ℝ) / q) : (ivHull p0 p1 q).Mem x := by
  have hS := Sc_pos
  unfold ivHull
  apply Bl.mem_ofLoHi
  · intro _
    have hok : (Bl.ofFrac p0 q).ok = true := by simp [Bl.ofFrac, hq]
    exact ((Bl.mem_ofFrac p0 q).lo_le hok).trans (by gcongr)
  · intro _
    have hok : (Bl.ofFrac p1 q).ok = true := by simp [Bl.ofFrac, hq]
    exact (by gcongr : Sc * x ≤ Sc * ((p1 : ℝ) / q)).trans ((Bl.mem_ofFrac p1 q).le_hi hok)

/-- The `τ`-grid denominator is positive. -/
theorem NT_pos : (0 : ℤ) < NT := by norm_num [NT]
/-- The `s`-grid denominator is positive. -/
theorem NS_pos : (0 : ℤ) < NS := by norm_num [NS]

/-! ## Lists -/

theorem lk_map_range (f : ℕ → Bl) (n j : ℕ) :
    lk ((List.range n).map f) j = if j < n then f j else Bl.zero := by
  unfold lk
  split_ifs with h <;> simp [List.getD_eq_getElem?_getD, h]

/-- Lookup in a mapped range list. -/
theorem getD_map_range {α : Type} (f : ℕ → α) (n j : ℕ) (d : α) :
    ((List.range n).map f).getD j d = if j < n then f j else d := by
  split_ifs with h <;> simp [List.getD_eq_getElem?_getD, h]

/-! ## Base coefficients, the numerator and its derivatives -/

/-- Base coefficients at a variable assignment. -/
@[expose] def bAt (D : Data) (ρ : ℕ → ℝ) : ℕ → ℝ := fun j => (baseT D j).eval ρ

/-- The coefficient `eₖ` along the chart. -/
@[expose] def ecE (D : Data) (k : ℕ) (τ s : ℝ) : ℝ := (etree k).eval (bAt D (chartEnv τ s))

/-- **The numerator** `Ψ(τ, s, σ̃) = Σₖ eₖ(τ, s) σ̃ᵏ` along the chart. -/
@[expose] def Psi (D : Data) (τ s σ : ℝ) : ℝ := ∑ k ∈ Finset.range 7, ecE D k τ s * σ ^ k

/-- Base trees beyond index `11` are the constant `0`. -/
theorem baseT_big (D : Data) {j : ℕ} (hj : 12 ≤ j) : baseT D j = c 0 1 := by
  unfold baseT; split <;> first | omega | rfl

/-- The base-value balls enclose the base coefficients. -/
theorem mem_baseVals (D : Data) {V : ℕ → Bl} {ρ : ℕ → ℝ} (hV : ∀ i, (V i).Mem (ρ i)) (j : ℕ) :
    (lk (baseVals D V) j).Mem (bAt D ρ j) := by
  unfold baseVals
  rw [lk_map_range]
  split_ifs with h
  · exact (baseT D j).ieval_mem hV
  · simp only [bAt, baseT_big D (not_lt.mp h)]; simpa [eval] using Bl.mem_zero

/-- Corner balls enclose the exact coefficients. -/
theorem mem_eCorner (D : Data) (t n : ℤ) {k : ℕ} (hk : k < 7) :
    (lk (eCorner D t n) k).Mem (ecE D k ((t : ℝ) / (NT : ℤ)) ((n : ℝ) / (NS : ℤ))) := by
  unfold eCorner
  rw [lk_map_range]; simp only [hk, ↓reduceIte]
  exact (etree k).ieval_mem (mem_baseVals D (mem_boxVars (Bl.mem_ofFrac t NT)
    (Bl.mem_ofFrac n NS)))

section deriv
variable (D : Data) (Dv : ℕ → Tm) (ρ : ℝ → ℕ → ℝ)

/-- First derivatives of the variables along a curve solving `ρ' = Dv(ρ)`. -/
@[expose] def vd1 (u : ℝ) (i : ℕ) : ℝ := (Dv i).eval (ρ u)
/-- Second derivatives of the variables. -/
@[expose] def vd2 (u : ℝ) (i : ℕ) : ℝ := (Dv i).deriv (ρ u) (vd1 Dv ρ u)
/-- First derivatives of the base coefficients. -/
@[expose] def bd1 (u : ℝ) (j : ℕ) : ℝ := (baseT D j).deriv (ρ u) (vd1 Dv ρ u)
/-- Second derivatives of the base coefficients. -/
@[expose] def bd2 (u : ℝ) (j : ℕ) : ℝ := (baseT D j).deriv2 (ρ u) (vd1 Dv ρ u) (vd2 Dv ρ u)
/-- First derivative of `eₖ`. -/
@[expose] def ed1 (k : ℕ) (u : ℝ) : ℝ := (etree k).deriv (bAt D (ρ u)) (bd1 D Dv ρ u)
/-- Second derivative of `eₖ`. -/
@[expose] def ed2 (k : ℕ) (u : ℝ) : ℝ :=
  (etree k).deriv2 (bAt D (ρ u)) (bd1 D Dv ρ u) (bd2 D Dv ρ u)

end deriv

/-- Derivatives of `eₖ` along a solution of `ρ' = Dv(ρ)`. -/
theorem hasDerivAt_ed (D : Data) (Dv : ℕ → Tm) {ρ : ℝ → ℕ → ℝ} {u : ℝ}
    (hρ : ∀ i, HasDerivAt (fun u => ρ u i) ((Dv i).eval (ρ u)) u) (k : ℕ) :
    HasDerivAt (fun u => (etree k).eval (bAt D (ρ u))) (ed1 D Dv ρ k u) u ∧
      HasDerivAt (ed1 D Dv ρ k) (ed2 D Dv ρ k u) u := by
  have h1 : ∀ i, HasDerivAt (fun u => vd1 Dv ρ u i) (vd2 Dv ρ u i) u :=
    fun i => (Dv i).hasDerivAt hρ
  have hb : ∀ j, HasDerivAt (fun u => bAt D (ρ u) j) (bd1 D Dv ρ u j) u :=
    fun j => (baseT D j).hasDerivAt hρ
  have hb' : ∀ j, HasDerivAt (fun u => bd1 D Dv ρ u j) (bd2 D Dv ρ u j) u :=
    fun j => (baseT D j).hasDerivAt_deriv hρ h1
  exact ⟨(etree k).hasDerivAt hb, (etree k).hasDerivAt_deriv hb hb'⟩

/-- `τ`-derivative trees beyond index `8` are the constant `0`. -/
theorem Dt_big {i : ℕ} (hi : 9 ≤ i) : Dt i = c 0 1 := by
  unfold Dt Dt0; split
  · omega
  · split <;> first | omega | rfl

/-- `s`-derivative trees beyond index `8` are the constant `0`. -/
theorem Ds_big {i : ℕ} (hi : 9 ≤ i) : Ds i = c 0 1 := by
  unfold Ds Ds0; split
  · omega
  · split <;> first | omega | rfl

/-- **Second-derivative balls**: `e2` encloses `ed2`. -/
theorem mem_e2 (D : Data) (Dv : ℕ → Tm) (hDv : ∀ i, 9 ≤ i → Dv i = c 0 1) {V : ℕ → Bl}
    {ρ : ℝ → ℕ → ℝ} {u : ℝ} (hV : ∀ i, (V i).Mem (ρ u i)) {k : ℕ} (hk : k < 7) :
    (lk (e2 D Dv V) k).Mem (ed2 D Dv ρ k u) := by
  have h1 : ∀ i, (lk ((List.range 9).map fun i => (Dv i).ieval V) i).Mem (vd1 Dv ρ u i) := by
    intro i
    rw [lk_map_range]
    split_ifs with h
    · exact (Dv i).ieval_mem hV
    · simp only [vd1, hDv i (not_lt.mp h)]; simpa [eval] using Bl.mem_zero
  have h2 : ∀ i, (lk ((List.range 9).map fun i => ((Dv i).idual V
      (lk ((List.range 9).map fun i => (Dv i).ieval V))).2) i).Mem (vd2 Dv ρ u i) := by
    intro i
    rw [lk_map_range]
    split_ifs with h
    · exact ((Dv i).idual_mem hV h1).2
    · simp only [vd2, hDv i (not_lt.mp h)]; simpa [Tm.deriv] using Bl.mem_zero
  have hB : ∀ j, (((List.range 12).map fun j => (baseT D j).ihd V
      (lk ((List.range 9).map fun i => (Dv i).ieval V))
      (lk ((List.range 9).map fun i => ((Dv i).idual V
        (lk ((List.range 9).map fun i => (Dv i).ieval V))).2))).getD j
        (Bl.zero, Bl.zero, Bl.zero)).1.Mem (bAt D (ρ u) j) ∧
      (((List.range 12).map fun j => (baseT D j).ihd V
      (lk ((List.range 9).map fun i => (Dv i).ieval V))
      (lk ((List.range 9).map fun i => ((Dv i).idual V
        (lk ((List.range 9).map fun i => (Dv i).ieval V))).2))).getD j
        (Bl.zero, Bl.zero, Bl.zero)).2.1.Mem (bd1 D Dv ρ u j) ∧
      (((List.range 12).map fun j => (baseT D j).ihd V
      (lk ((List.range 9).map fun i => (Dv i).ieval V))
      (lk ((List.range 9).map fun i => ((Dv i).idual V
        (lk ((List.range 9).map fun i => (Dv i).ieval V))).2))).getD j
        (Bl.zero, Bl.zero, Bl.zero)).2.2.Mem (bd2 D Dv ρ u j) := by
    intro j
    rw [getD_map_range]
    split_ifs with h
    · exact (baseT D j).ihd_mem hV h1 h2
    · simp only [bAt, bd1, bd2, baseT_big D (not_lt.mp h)]
      exact ⟨by simpa [eval] using Bl.mem_zero, by simpa [Tm.deriv] using Bl.mem_zero,
        by simpa [Tm.deriv2] using Bl.mem_zero⟩
  unfold e2
  simp only
  rw [lk_map_range]; simp only [hk, ↓reduceIte]
  exact ((etree k).ihd_mem (fun j => (hB j).1) (fun j => (hB j).2.1) (fun j => (hB j).2.2)).2.2


/-! ## The corner test -/

theorem pow2_getD {k : ℕ} (hk : k < 7) : ((pow2.getD k 0 : ℤ) : ℝ) = 2 ^ k := by
  interval_cases k <;> norm_num [pow2]

/-- **Soundness of the corner test**: `Ψ(c, σ̃) > Σₖ (Rₖ/2³²) |σ̃|ᵏ` for every `σ̃`. -/
theorem cornerOK_sound {D : Data} {t n : ℤ} {R : List ℕ} (h : cornerOK D t n R = true) (σ : ℝ) :
    ∑ k ∈ Finset.range 7, ((R.getD k 0 : ℕ) : ℝ) / Sc * |σ| ^ k <
      Psi D ((t : ℝ) / (NT : ℤ)) ((n : ℝ) / (NS : ℤ)) σ := by
  have hS := Sc_pos
  simp only [cornerOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hok, hp⟩, hm⟩ := h
  set E := eCorner D t n
  set e := fun k => ecE D k ((t : ℝ) / (NT : ℤ)) ((n : ℝ) / (NS : ℤ))
  have hlo : ∀ k < 7, ((lk E k).lo : ℝ) ≤ Sc * e k := fun k hk =>
    (mem_eCorner D t n hk).lo_le (hok k hk)
  have hhi : ∀ k < 7, Sc * e k ≤ (lk E k).hi := fun k hk =>
    (mem_eCorner D t n hk).le_hi (hok k hk)
  suffices key : 0 < ∑ k ∈ Finset.range 7, (Sc * e k * σ ^ k - (R.getD k 0 : ℝ) * |σ| ^ k) by
    have e1 : ∑ k ∈ Finset.range 7, (Sc * e k * σ ^ k - (R.getD k 0 : ℝ) * |σ| ^ k) =
        Sc * (Psi D ((t : ℝ) / (NT : ℤ)) ((n : ℝ) / (NS : ℤ)) σ -
          ∑ k ∈ Finset.range 7, ((R.getD k 0 : ℕ) : ℝ) / Sc * |σ| ^ k) := by
      simp only [Psi, mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [e]; field_simp
    rw [e1] at key
    have := pos_of_mul_pos_right key hS.le
    linarith
  rcases le_or_gt 0 σ with hσ | hσ
  · have hz := zpoly_pos_of_polyaOK hp (u := σ / 2) (by linarith)
    rw [zpoly_range7] at hz
    calc (0 : ℝ) < _ := hz
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        have hk7 := Finset.mem_range.mp hk
        simp only [int_mul_eq, int_sub_eq]; push_cast
        rw [pow2_getD hk7, abs_of_nonneg hσ]
        have e2 : ((lk E k).lo - (R.getD k 0 : ℝ)) * 2 ^ k * (σ / 2) ^ k =
            ((lk E k).lo - (R.getD k 0 : ℝ)) * σ ^ k := by
          rw [div_pow]; field_simp
        rw [e2]
        have := mul_le_mul_of_nonneg_right (hlo k hk7) (pow_nonneg hσ k)
        nlinarith
  · have hz := zpoly_pos_of_polyaOK hm (u := -σ / 2) (by linarith)
    rw [zpoly_range7] at hz
    calc (0 : ℝ) < _ := hz
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        have hk7 := Finset.mem_range.mp hk
        rw [abs_of_neg hσ]
        rcases Nat.even_or_odd k with he | ho
        · have hk2 : k % 2 = 0 := Nat.even_iff.mp he
          simp only [hk2, ↓reduceIte, int_mul_eq, int_sub_eq]; push_cast
          rw [pow2_getD hk7]
          have e2 : ((lk E k).lo - (R.getD k 0 : ℝ)) * 2 ^ k * (-σ / 2) ^ k =
              ((lk E k).lo - (R.getD k 0 : ℝ)) * σ ^ k := by
            rw [div_pow, he.neg_pow]; field_simp
          rw [e2, he.neg_pow]
          have := mul_le_mul_of_nonneg_right (hlo k hk7) (he.pow_nonneg σ)
          nlinarith
        · have hk2 : ¬ k % 2 = 0 := by rw [Nat.odd_iff] at ho; omega
          simp only [hk2, ↓reduceIte, int_mul_eq, int_sub_eq, int_neg_eq]; push_cast
          rw [pow2_getD hk7]
          have e2 : (-((lk E k).hi : ℝ) - (R.getD k 0 : ℝ)) * 2 ^ k * (-σ / 2) ^ k =
              ((lk E k).hi + (R.getD k 0 : ℝ)) * σ ^ k := by
            rw [div_pow, ho.neg_pow]; field_simp; ring
          rw [e2, ho.neg_pow]
          have hneg : σ ^ k ≤ 0 := (ho.pow_neg hσ).le
          have := mul_le_mul_of_nonpos_right (hhi k hk7) hneg
          nlinarith

/-! ## The reserve -/

theorem toNat_cast_real {x : ℤ} (hx : 0 ≤ x) : ((x.toNat : ℕ) : ℝ) = x := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hx]

/-- The reserve dominates the chord errors `Mτ Δτ²/8 + Ms Δs²/8` (or `Ms s₁²/2`). -/
theorem reserve_ge (Mt Ms : List Bl) (dt ds : ℤ) (axis : Bool) {k : ℕ} (hk : k < 7) :
    ((lk Mt k).mag : ℝ) * dt ^ 2 / (8 * (NT : ℝ) ^ 2) +
        ((lk Ms k).mag : ℝ) * ds ^ 2 * (if axis then 4 else 1) / (8 * (NS : ℝ) ^ 2) ≤
      ((reserve Mt Ms dt ds axis).getD k 0 : ℝ) := by
  unfold reserve
  rw [getD_map_range]; simp only [hk, ↓reduceIte, nat_add_eq, nat_div_eq, nat_mul_eq]
  set N : ℕ := (lk Mt k).mag * (dt * dt).toNat * (NS * NS).toNat +
    (lk Ms k).mag * (ds * ds).toNat * (if axis then (4 * NT * NT).toNat else (NT * NT).toNat)
  have hd := nat_div_bound N (8 * NT * NT * NS * NS).toNat (by norm_num [NT, NS])
  have hN : (N : ℝ) = (lk Mt k).mag * (dt * dt : ℤ) * (NS * NS : ℤ) +
      (lk Ms k).mag * (ds * ds : ℤ) * (if axis then (4 * NT * NT : ℤ) else (NT * NT : ℤ)) := by
    simp only [N]; push_cast
    rw [toNat_cast_real (mul_self_nonneg dt), toNat_cast_real (mul_self_nonneg ds),
      toNat_cast_real (by norm_num [NS])]
    split_ifs
    · rw [toNat_cast_real (by norm_num [NT])]; push_cast; ring
    · rw [toNat_cast_real (by norm_num [NT])]; push_cast; ring
  have hD : (((8 * NT * NT * NS * NS).toNat : ℕ) : ℝ) = 8 * (NT : ℝ) ^ 2 * (NS : ℝ) ^ 2 := by
    rw [toNat_cast_real (by norm_num [NT, NS])]; push_cast; ring
  rw [hN, hD] at hd
  push_cast
  have hNT : (0 : ℝ) < NT := by norm_num [NT]
  have hNS : (0 : ℝ) < NS := by norm_num [NS]
  calc _ = ((lk Mt k).mag * (dt * dt : ℤ) * (NS * NS : ℤ) +
        (lk Ms k).mag * (ds * ds : ℤ) * (if axis then (4 * NT * NT : ℤ) else (NT * NT : ℤ))) /
        (8 * (NT : ℝ) ^ 2 * (NS : ℝ) ^ 2) := by
          split_ifs <;> (push_cast; field_simp; try ring)
    _ ≤ _ := hd

/-! ## Soundness of the box checks -/

/-- Chord form used below: a `C²` function with `|g''| ≤ M` on `[a, b]` is at least
`min (g a) (g b) − M (b − a)²/8` on `[a, b]`. -/
theorem chord_min {g g' g'' : ℝ → ℝ} {a b M x : ℝ} (hab : a < b)
    (hg : ∀ y ∈ Icc a b, HasDerivAt g (g' y) y) (hg' : ∀ y ∈ Icc a b, HasDerivAt g' (g'' y) y)
    (hM : ∀ y ∈ Icc a b, |g'' y| ≤ M) (hx : x ∈ Icc a b) :
    min (g a) (g b) - M * (b - a) ^ 2 / 8 ≤ g x := by
  have h := chord_lower hab hg hg' hM hx
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM a (left_mem_Icc.mpr hab.le))
  have hba : 0 < b - a := by linarith
  have h1 : ((b - x) * g a + (x - a) * g b) / (b - a) ≥ min (g a) (g b) := by
    rw [ge_iff_le, le_div_iff₀ hba]
    have := min_le_left (g a) (g b); have := min_le_right (g a) (g b)
    nlinarith [hx.1, hx.2]
  have h2 : M * (x - a) * (b - x) / 2 ≤ M * (b - a) ^ 2 / 8 := by
    have : (x - a) * (b - x) ≤ (b - a) ^ 2 / 4 := by nlinarith [sq_nonneg (2 * x - a - b)]
    nlinarith
  linarith

/-- Bound on the second derivative of `Ψ` from the coefficient bounds. -/
theorem sum_ed2_le (D : Data) (Dv : ℕ → Tm) (hDv : ∀ i, 9 ≤ i → Dv i = c 0 1) {V : ℕ → Bl}
    {ρ : ℝ → ℕ → ℝ} {u : ℝ} (hV : ∀ i, (V i).Mem (ρ u i))
    (hok : ∀ k < 7, (lk (e2 D Dv V) k).ok = true) (σ : ℝ) :
    |∑ k ∈ Finset.range 7, ed2 D Dv ρ k u * σ ^ k| ≤
      ∑ k ∈ Finset.range 7, ((lk (e2 D Dv V) k).mag : ℝ) / Sc * |σ| ^ k := by
  have hS := Sc_pos
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  have hk7 := Finset.mem_range.mp hk
  have := (mem_e2 D Dv hDv hV hk7).abs_le_mag (hok k hk7)
  rw [abs_mul, abs_pow]
  gcongr
  rw [le_div_iff₀ hS]; linarith

/-- Membership in a hull ball from interval membership. -/
theorem ivHull_mem_of {p0 p1 q : ℤ} (hq : 0 < q) {x : ℝ}
    (hx : x ∈ Icc ((p0 : ℝ) / q) ((p1 : ℝ) / q)) : (ivHull p0 p1 q).Mem x :=
  mem_ivHull hq hx.1 hx.2

/-- `τ`-direction chord at fixed `s` over a box. -/
theorem psi_chord_tau (D : Data) {T S : Bl} {τ0 τ1 s σ τ : ℝ} (h01 : τ0 < τ1) (hs : |s| < 50)
    (hT : ∀ u ∈ Icc τ0 τ1, T.Mem u) (hSs : S.Mem s)
    (hok : ∀ k < 7, (lk (e2 D Dt (boxVars T S)) k).ok = true) (hτ : τ ∈ Icc τ0 τ1) :
    min (Psi D τ0 s σ) (Psi D τ1 s σ) - (∑ k ∈ Finset.range 7,
      ((lk (e2 D Dt (boxVars T S)) k).mag : ℝ) / Sc * |σ| ^ k) * (τ1 - τ0) ^ 2 / 8 ≤
      Psi D τ s σ := by
  set ρ : ℝ → ℕ → ℝ := fun u => chartEnv u s
  have hρ : ∀ u, ∀ i, HasDerivAt (fun u => ρ u i) ((Dt i).eval (ρ u)) u :=
    fun u i => hasDerivAt_chart_tau hs u i
  refine chord_min (g := fun u => Psi D u s σ)
    (g' := fun u => ∑ k ∈ Finset.range 7, ed1 D Dt ρ k u * σ ^ k)
    (g'' := fun u => ∑ k ∈ Finset.range 7, ed2 D Dt ρ k u * σ ^ k) h01 ?_ ?_ ?_ hτ
  · intro y _
    exact HasDerivAt.fun_sum fun k _ => ((hasDerivAt_ed D Dt (hρ y) k).1).mul_const _
  · intro y _
    exact HasDerivAt.fun_sum fun k _ => ((hasDerivAt_ed D Dt (hρ y) k).2).mul_const _
  · intro y hy
    exact sum_ed2_le D Dt (fun i hi => Dt_big hi) (mem_boxVars (hT y hy) hSs) hok σ

/-- `s`-direction chord at fixed `τ` over a box. -/
theorem psi_chord_s (D : Data) {T S : Bl} {s0 s1 τ σ s : ℝ} (h01 : s0 < s1)
    (hs : ∀ u ∈ Icc s0 s1, |u| < 50) (hTt : T.Mem τ) (hS : ∀ u ∈ Icc s0 s1, S.Mem u)
    (hok : ∀ k < 7, (lk (e2 D Ds (boxVars T S)) k).ok = true) (hsm : s ∈ Icc s0 s1) :
    ((s1 - s) * Psi D τ s0 σ + (s - s0) * Psi D τ s1 σ) / (s1 - s0) - (∑ k ∈ Finset.range 7,
      ((lk (e2 D Ds (boxVars T S)) k).mag : ℝ) / Sc * |σ| ^ k) * (s - s0) * (s1 - s) / 2 ≤
      Psi D τ s σ := by
  set ρ : ℝ → ℕ → ℝ := fun u => chartEnv τ u
  have hρ : ∀ u ∈ Icc s0 s1, ∀ i, HasDerivAt (fun u => ρ u i) ((Ds i).eval (ρ u)) u :=
    fun u hu i => hasDerivAt_chart_s (hs u hu) τ i
  refine chord_lower (g := fun u => Psi D τ u σ)
    (g' := fun u => ∑ k ∈ Finset.range 7, ed1 D Ds ρ k u * σ ^ k)
    (g'' := fun u => ∑ k ∈ Finset.range 7, ed2 D Ds ρ k u * σ ^ k) h01 ?_ ?_ ?_ hsm
  · intro y hy
    exact HasDerivAt.fun_sum fun k _ => ((hasDerivAt_ed D Ds (hρ y hy) k).1).mul_const _
  · intro y hy
    exact HasDerivAt.fun_sum fun k _ => ((hasDerivAt_ed D Ds (hρ y hy) k).2).mul_const _
  · intro y hy
    exact sum_ed2_le D Ds (fun i hi => Ds_big hi) (mem_boxVars hTt (hS y hy)) hok σ

/-- `NT = 4096`. -/
theorem NT_real : ((NT : ℤ) : ℝ) = 4096 := by norm_num [NT]
/-- `NS = 1024`. -/
theorem NS_real : ((NS : ℤ) : ℝ) = 1024 := by norm_num [NS]

/-- **Soundness of a box check.** -/
theorem box_core {D : Data} {t0 t1 n0 n1 : ℤ} (ht01 : t0 < t1) (hn0 : 0 ≤ n0)
    (hn01 : n0 < n1) (hn1 : n1 ≤ 25 * NS)
    (hok : ∀ k < 7, (lk (e2 D Dt (boxVars (ivHull t0 t1 NT) (ivHull n0 n1 NS))) k).ok = true ∧
      (lk (e2 D Ds (boxVars (ivHull t0 t1 NT) (ivHull n0 n1 NS))) k).ok = true)
    (hc : ∀ t n : ℤ, (t = t0 ∨ t = t1) → (n = n0 ∨ n = n1) → ∀ σ : ℝ,
      ∑ k ∈ Finset.range 7, (((reserve (e2 D Dt (boxVars (ivHull t0 t1 NT) (ivHull n0 n1 NS)))
        (e2 D Ds (boxVars (ivHull t0 t1 NT) (ivHull n0 n1 NS))) (t1 - t0) (n1 - n0)
          false).getD k 0 : ℕ) : ℝ) / Sc * |σ| ^ k <
        Psi D ((t : ℝ) / (NT : ℤ)) ((n : ℝ) / (NS : ℤ)) σ)
    {τ s : ℝ} (hτ : τ ∈ Icc ((t0 : ℝ) / (NT : ℤ)) ((t1 : ℝ) / (NT : ℤ)))
    (hs : s ∈ Icc ((n0 : ℝ) / (NS : ℤ)) ((n1 : ℝ) / (NS : ℤ))) (σ : ℝ) : 0 < Psi D τ s σ := by
  set T := ivHull t0 t1 NT
  set S := ivHull n0 n1 NS
  set V := boxVars T S
  set R := reserve (e2 D Dt V) (e2 D Ds V) (t1 - t0) (n1 - n0) false
  set τ0 : ℝ := (t0 : ℝ) / (NT : ℤ)
  set τ1 : ℝ := (t1 : ℝ) / (NT : ℤ)
  set s0 : ℝ := (n0 : ℝ) / (NS : ℤ)
  set s1 : ℝ := (n1 : ℝ) / (NS : ℤ)
  have hNT : (0 : ℝ) < (NT : ℤ) := by rw [NT_real]; norm_num
  have hNS : (0 : ℝ) < (NS : ℤ) := by rw [NS_real]; norm_num
  have hτ01 : τ0 < τ1 := by
    simp only [τ0, τ1]; rw [div_lt_div_iff_of_pos_right hNT]; exact_mod_cast ht01
  have hs01 : s0 < s1 := by
    simp only [s0, s1]; rw [div_lt_div_iff_of_pos_right hNS]; exact_mod_cast hn01
  have hs0 : 0 ≤ s0 := by simp only [s0]; positivity
  have hs1 : s1 ≤ 25 := by
    simp only [s1]; rw [div_le_iff₀ hNS, NS_real]
    have : (n1 : ℝ) ≤ 25 * (NS : ℤ) := by exact_mod_cast hn1
    rw [NS_real] at this; linarith
  have hsabs : ∀ u ∈ Icc s0 s1, |u| < 50 := fun u hu => by
    rw [abs_lt]; constructor <;> linarith [hu.1, hu.2]
  have hT : ∀ u ∈ Icc τ0 τ1, T.Mem u := fun u hu => ivHull_mem_of NT_pos hu
  have hS : ∀ u ∈ Icc s0 s1, S.Mem u := fun u hu => ivHull_mem_of NS_pos hu
  have hokt : ∀ k < 7, (lk (e2 D Dt V) k).ok = true := fun k hk => (hok k hk).1
  have hoks : ∀ k < 7, (lk (e2 D Ds V) k).ok = true := fun k hk => (hok k hk).2
  set Mt := ∑ k ∈ Finset.range 7, ((lk (e2 D Dt V) k).mag : ℝ) / Sc * |σ| ^ k
  set Ms := ∑ k ∈ Finset.range 7, ((lk (e2 D Ds V) k).mag : ℝ) / Sc * |σ| ^ k
  set Rs := ∑ k ∈ Finset.range 7, ((R.getD k 0 : ℕ) : ℝ) / Sc * |σ| ^ k
  -- the reserve dominates the chord errors
  have hR : Mt * (τ1 - τ0) ^ 2 / 8 + Ms * (s1 - s0) ^ 2 / 8 ≤ Rs := by
    have e1 : Mt * (τ1 - τ0) ^ 2 / 8 + Ms * (s1 - s0) ^ 2 / 8 = ∑ k ∈ Finset.range 7,
        (((lk (e2 D Dt V) k).mag : ℝ) * ((t1 - t0 : ℤ) : ℝ) ^ 2 / (8 * (NT : ℝ) ^ 2) +
        ((lk (e2 D Ds V) k).mag : ℝ) * ((n1 - n0 : ℤ) : ℝ) ^ 2 * (if false then 4 else 1) /
          (8 * (NS : ℝ) ^ 2)) / Sc * |σ| ^ k := by
      simp only [Mt, Ms, Finset.sum_mul, Finset.sum_div, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [τ0, τ1, s0, s1]; push_cast; field_simp
    rw [e1]
    refine Finset.sum_le_sum fun k hk => ?_
    have := reserve_ge (e2 D Dt V) (e2 D Ds V) (t1 - t0) (n1 - n0) false (Finset.mem_range.mp hk)
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right this Sc_pos.le) (by positivity)
  have hc1 := hc t0 n0 (Or.inl rfl) (Or.inl rfl) σ
  have hc2 := hc t1 n0 (Or.inr rfl) (Or.inl rfl) σ
  have hc3 := hc t0 n1 (Or.inl rfl) (Or.inr rfl) σ
  have hc4 := hc t1 n1 (Or.inr rfl) (Or.inr rfl) σ
  -- s-chords at the two τ-edges
  have hedge : ∀ τ' ∈ ({τ0, τ1} : Set ℝ), min (Psi D τ' s0 σ) (Psi D τ' s1 σ) -
      Ms * (s1 - s0) ^ 2 / 8 ≤ Psi D τ' s σ := by
    intro τ' hτ'
    have hTt : T.Mem τ' := by
      rcases hτ' with rfl | rfl
      · exact hT _ (left_mem_Icc.mpr hτ01.le)
      · exact hT _ (right_mem_Icc.mpr hτ01.le)
    have := psi_chord_s D (σ := σ) hs01 hsabs hTt hS hoks hs
    have hMs0 : 0 ≤ Ms := Finset.sum_nonneg fun k _ =>
      mul_nonneg (div_nonneg (Nat.cast_nonneg _) Sc_pos.le) (by positivity)
    have h1 : ((s1 - s) * Psi D τ' s0 σ + (s - s0) * Psi D τ' s1 σ) / (s1 - s0) ≥
        min (Psi D τ' s0 σ) (Psi D τ' s1 σ) := by
      rw [ge_iff_le, le_div_iff₀ (by linarith)]
      have := min_le_left (Psi D τ' s0 σ) (Psi D τ' s1 σ)
      have := min_le_right (Psi D τ' s0 σ) (Psi D τ' s1 σ)
      nlinarith [hs.1, hs.2]
    have h2 : Ms * (s - s0) * (s1 - s) / 2 ≤ Ms * (s1 - s0) ^ 2 / 8 := by
      have : (s - s0) * (s1 - s) ≤ (s1 - s0) ^ 2 / 4 := by nlinarith [sq_nonneg (2 * s - s0 - s1)]
      nlinarith
    linarith
  have hS's : S.Mem s := hS s hs
  have hmid := psi_chord_tau D (σ := σ) hτ01 (hsabs s hs) hT hS's hokt hτ
  have e0 := hedge τ0 (by simp)
  have e1 := hedge τ1 (by simp)
  have hm0 : Rs < min (Psi D τ0 s0 σ) (Psi D τ0 s1 σ) := lt_min hc1 hc3
  have hm1 : Rs < min (Psi D τ1 s0 σ) (Psi D τ1 s1 σ) := lt_min hc2 hc4
  have : Rs - Ms * (s1 - s0) ^ 2 / 8 - Mt * (τ1 - τ0) ^ 2 / 8 < Psi D τ s σ := by
    have := min_le_left (Psi D τ0 s σ) (Psi D τ1 s σ)
    have := min_le_right (Psi D τ0 s σ) (Psi D τ1 s σ)
    rcases min_choice (Psi D τ0 s σ) (Psi D τ1 s σ) with hmin | hmin <;> rw [hmin] at hmid <;>
      linarith
  linarith

/-- **Soundness of an axis-box check**, given that the coefficients vanish on the axis. -/
theorem axis_core {D : Data} (hvan : ∀ τ k, ecE D k τ 0 = 0) {t0 t1 n1 : ℤ} (ht01 : t0 < t1)
    (hn1p : 0 < n1) (hn1 : n1 ≤ 25 * NS)
    (hok : ∀ k < 7, (lk (e2 D Dt (boxVars (ivHull t0 t1 NT) (ivHull 0 n1 NS))) k).ok = true ∧
      (lk (e2 D Ds (boxVars (ivHull t0 t1 NT) (ivHull 0 n1 NS))) k).ok = true)
    (hc : ∀ t : ℤ, (t = t0 ∨ t = t1) → ∀ σ : ℝ,
      ∑ k ∈ Finset.range 7, (((reserve (e2 D Dt (boxVars (ivHull t0 t1 NT) (ivHull 0 n1 NS)))
        (e2 D Ds (boxVars (ivHull t0 t1 NT) (ivHull 0 n1 NS))) (t1 - t0) n1
          true).getD k 0 : ℕ) : ℝ) / Sc * |σ| ^ k <
        Psi D ((t : ℝ) / (NT : ℤ)) ((n1 : ℝ) / (NS : ℤ)) σ)
    {τ s : ℝ} (hτ : τ ∈ Icc ((t0 : ℝ) / (NT : ℤ)) ((t1 : ℝ) / (NT : ℤ)))
    (hs : s ∈ Ioc 0 ((n1 : ℝ) / (NS : ℤ))) (σ : ℝ) : 0 < Psi D τ s σ := by
  set T := ivHull t0 t1 NT
  set S := ivHull 0 n1 NS
  set V := boxVars T S
  set R := reserve (e2 D Dt V) (e2 D Ds V) (t1 - t0) n1 true
  set τ0 : ℝ := (t0 : ℝ) / (NT : ℤ)
  set τ1 : ℝ := (t1 : ℝ) / (NT : ℤ)
  set s1 : ℝ := (n1 : ℝ) / (NS : ℤ)
  have hNT : (0 : ℝ) < (NT : ℤ) := by rw [NT_real]; norm_num
  have hNS : (0 : ℝ) < (NS : ℤ) := by rw [NS_real]; norm_num
  have hτ01 : τ0 < τ1 := by
    simp only [τ0, τ1]; rw [div_lt_div_iff_of_pos_right hNT]; exact_mod_cast ht01
  have hs1p : 0 < s1 := by
    have : (0 : ℝ) < n1 := by exact_mod_cast hn1p
    simp only [s1]; positivity
  have hs1 : s1 ≤ 25 := by
    simp only [s1]; rw [div_le_iff₀ hNS, NS_real]
    have : (n1 : ℝ) ≤ 25 * (NS : ℤ) := by exact_mod_cast hn1
    rw [NS_real] at this; linarith
  have hsabs : ∀ u ∈ Icc 0 s1, |u| < 50 := fun u hu => by
    rw [abs_lt]; constructor <;> linarith [hu.1, hu.2]
  have hT : ∀ u ∈ Icc τ0 τ1, T.Mem u := fun u hu => ivHull_mem_of NT_pos hu
  have hS : ∀ u ∈ Icc 0 s1, S.Mem u := fun u hu =>
    ivHull_mem_of NS_pos (by simpa using hu)
  have hokt : ∀ k < 7, (lk (e2 D Dt V) k).ok = true := fun k hk => (hok k hk).1
  have hoks : ∀ k < 7, (lk (e2 D Ds V) k).ok = true := fun k hk => (hok k hk).2
  set Mt := ∑ k ∈ Finset.range 7, ((lk (e2 D Dt V) k).mag : ℝ) / Sc * |σ| ^ k
  set Ms := ∑ k ∈ Finset.range 7, ((lk (e2 D Ds V) k).mag : ℝ) / Sc * |σ| ^ k
  set Rs := ∑ k ∈ Finset.range 7, ((R.getD k 0 : ℕ) : ℝ) / Sc * |σ| ^ k
  have hR : Mt * (τ1 - τ0) ^ 2 / 8 + Ms * s1 ^ 2 / 2 ≤ Rs := by
    have e1 : Mt * (τ1 - τ0) ^ 2 / 8 + Ms * s1 ^ 2 / 2 = ∑ k ∈ Finset.range 7,
        (((lk (e2 D Dt V) k).mag : ℝ) * ((t1 - t0 : ℤ) : ℝ) ^ 2 / (8 * (NT : ℝ) ^ 2) +
        ((lk (e2 D Ds V) k).mag : ℝ) * ((n1 : ℤ) : ℝ) ^ 2 * (if true then 4 else 1) /
          (8 * (NS : ℝ) ^ 2)) / Sc * |σ| ^ k := by
      simp only [Mt, Ms, Finset.sum_mul, Finset.sum_div, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [τ0, τ1, s1]; push_cast; field_simp; ring
    rw [e1]
    refine Finset.sum_le_sum fun k hk => ?_
    have := reserve_ge (e2 D Dt V) (e2 D Ds V) (t1 - t0) n1 true (Finset.mem_range.mp hk)
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right this Sc_pos.le) (by positivity)
  have hc1 := hc t0 (Or.inl rfl) σ
  have hc2 := hc t1 (Or.inr rfl) σ
  -- the τ-chord at `s = s₁`
  have hmid := psi_chord_tau D (σ := σ) hτ01 (hsabs s1 ⟨hs1p.le, le_rfl⟩) hT
    (hS s1 ⟨hs1p.le, le_rfl⟩) hokt hτ
  have hTt : T.Mem τ := hT τ hτ
  -- the s-chord from the axis
  have hch := psi_chord_s D (σ := σ) hs1p hsabs hTt hS hoks ⟨hs.1.le, hs.2⟩
  have h0 : Psi D τ 0 σ = 0 := by simp [Psi, hvan]
  rw [h0] at hch
  have hMs0 : 0 ≤ Ms := Finset.sum_nonneg fun k _ =>
      mul_nonneg (div_nonneg (Nat.cast_nonneg _) Sc_pos.le) (by positivity)
  have hmin : Rs - Mt * (τ1 - τ0) ^ 2 / 8 < Psi D τ s1 σ := by
    have := min_le_left (Psi D τ0 s1 σ) (Psi D τ1 s1 σ)
    have := min_le_right (Psi D τ0 s1 σ) (Psi D τ1 s1 σ)
    rcases min_choice (Psi D τ0 s1 σ) (Psi D τ1 s1 σ) with hm | hm <;> rw [hm] at hmid <;>
      linarith
  have hpos : 0 < Psi D τ s1 σ - Ms * s1 ^ 2 / 2 := by linarith
  have hsp := hs.1
  have key : s / s1 * (Psi D τ s1 σ - Ms * s1 ^ 2 / 2) ≤ Psi D τ s σ := by
    have e : ((s1 - s) * 0 + (s - 0) * Psi D τ s1 σ) / (s1 - 0) = s / s1 * Psi D τ s1 σ := by
      simp only [sub_zero, mul_zero, zero_add]; field_simp
    rw [e] at hch
    have e2 : s / s1 * (Psi D τ s1 σ - Ms * s1 ^ 2 / 2) =
        s / s1 * Psi D τ s1 σ - Ms * s * s1 / 2 := by field_simp
    have h2 : Ms * (s - 0) * (s1 - s) / 2 ≤ Ms * s * s1 / 2 := by
      have : 0 ≤ Ms * s := mul_nonneg hMs0 hsp.le
      nlinarith
    linarith
  have : 0 < s / s1 * (Psi D τ s1 σ - Ms * s1 ^ 2 / 2) := mul_pos (div_pos hsp hs1p) hpos
  linarith


/-- **Soundness of a box check.** -/
theorem boxOK_sound {D : Data} {t0 t1 n0 n1 : ℤ} (h : boxOK D t0 t1 n0 n1 = true) {τ s : ℝ}
    (hτ : τ ∈ Icc ((t0 : ℝ) / (NT : ℤ)) ((t1 : ℝ) / (NT : ℤ)))
    (hs : s ∈ Icc ((n0 : ℝ) / (NS : ℤ)) ((n1 : ℝ) / (NS : ℤ))) (σ : ℝ) : 0 < Psi D τ s σ := by
  simp only [boxOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨ht01, hn0⟩, hn01⟩, hn1⟩, hok⟩, c1⟩, c2⟩, c3⟩, c4⟩ := h
  refine box_core ht01 hn0 hn01 hn1 hok ?_ hτ hs σ
  rintro t n (rfl | rfl) (rfl | rfl) σ
  exacts [cornerOK_sound c1 σ, cornerOK_sound c3 σ, cornerOK_sound c2 σ, cornerOK_sound c4 σ]

/-- **Soundness of an axis-box check**, given that the coefficients vanish on the axis. -/
theorem axisOK_sound {D : Data} (hvan : ∀ τ k, ecE D k τ 0 = 0) {t0 t1 n1 : ℤ}
    (h : axisOK D t0 t1 n1 = true) {τ s : ℝ}
    (hτ : τ ∈ Icc ((t0 : ℝ) / (NT : ℤ)) ((t1 : ℝ) / (NT : ℤ)))
    (hs : s ∈ Ioc 0 ((n1 : ℝ) / (NS : ℤ))) (σ : ℝ) : 0 < Psi D τ s σ := by
  simp only [axisOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨ht01, hn1p⟩, hn1⟩, hok⟩, c1⟩, c2⟩ := h
  refine axis_core hvan ht01 hn1p hn1 hok ?_ hτ hs σ
  rintro t (rfl | rfl) σ
  exacts [cornerOK_sound c1 σ, cornerOK_sound c2 σ]

/-- A dominated reserve gives a smaller weighted sum. -/
theorem reserve_sum_le {R R' : List ℕ} (h : leList R R' = true) (σ : ℝ) :
    ∑ k ∈ Finset.range 7, ((R.getD k 0 : ℕ) : ℝ) / Sc * |σ| ^ k ≤
      ∑ k ∈ Finset.range 7, ((R'.getD k 0 : ℕ) : ℝ) / Sc * |σ| ^ k := by
  simp only [leList, List.all_eq_true, List.mem_range, Nat.ble_eq] at h
  refine Finset.sum_le_sum fun k hk => ?_
  have := h k (Finset.mem_range.mp hk)
  have h' : ((R.getD k 0 : ℕ) : ℝ) ≤ (R'.getD k 0 : ℕ) := by exact_mod_cast this
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h' Sc_pos.le) (by positivity)

/-- Corner test with a dominating reserve. -/
theorem corner_of_le {D : Data} {t n : ℤ} {R R' : List ℕ} (hle : leList R R' = true)
    (hc : cornerOK D t n R' = true) (σ : ℝ) :
    ∑ k ∈ Finset.range 7, ((R.getD k 0 : ℕ) : ℝ) / Sc * |σ| ^ k <
      Psi D ((t : ℝ) / (NT : ℤ)) ((n : ℝ) / (NS : ℤ)) σ :=
  lt_of_le_of_lt (reserve_sum_le hle σ) (cornerOK_sound hc σ)

/-- **Soundness of a box with shared corner tests.** -/
theorem leaf2_sound {D : Data} {t0 t1 n0 n1 : ℤ} {R00 R10 R01 R11 : List ℕ}
    (h : hessOK D t0 t1 n0 n1 false [R00, R10, R01, R11] = true)
    (c1 : cornerOK D t0 n0 R00 = true) (c2 : cornerOK D t1 n0 R10 = true)
    (c3 : cornerOK D t0 n1 R01 = true) (c4 : cornerOK D t1 n1 R11 = true) {τ s : ℝ}
    (hτ : τ ∈ Icc ((t0 : ℝ) / (NT : ℤ)) ((t1 : ℝ) / (NT : ℤ)))
    (hs : s ∈ Icc ((n0 : ℝ) / (NS : ℤ)) ((n1 : ℝ) / (NS : ℤ))) (σ : ℝ) : 0 < Psi D τ s σ := by
  simp only [hessOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨⟨⟨⟨⟨ht01, hn0⟩, hn01⟩, hn1⟩, hok⟩, l1, l2, l3, l4⟩ := h
  refine box_core ht01 hn0 hn01 hn1 hok ?_ hτ hs σ
  rintro t n (rfl | rfl) (rfl | rfl) σ
  exacts [corner_of_le l1 c1 σ, corner_of_le l3 c3 σ, corner_of_le l2 c2 σ, corner_of_le l4 c4 σ]

/-- **Soundness of an axis box with shared corner tests.** -/
theorem axis2_sound {D : Data} (hvan : ∀ τ k, ecE D k τ 0 = 0) {t0 t1 n1 : ℤ} {R0 R1 : List ℕ}
    (h : hessOK D t0 t1 0 n1 true [R0, R1] = true)
    (c1 : cornerOK D t0 n1 R0 = true) (c2 : cornerOK D t1 n1 R1 = true) {τ s : ℝ}
    (hτ : τ ∈ Icc ((t0 : ℝ) / (NT : ℤ)) ((t1 : ℝ) / (NT : ℤ)))
    (hs : s ∈ Ioc 0 ((n1 : ℝ) / (NS : ℤ))) (σ : ℝ) : 0 < Psi D τ s σ := by
  simp only [hessOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  obtain ⟨⟨⟨⟨⟨ht01, -⟩, hn1p⟩, hn1⟩, hok⟩, l1, l2⟩ := h
  have hok' : ∀ k < 7, (lk (e2 D Dt (boxVars (ivHull t0 t1 NT) (ivHull 0 n1 NS))) k).ok = true ∧
      (lk (e2 D Ds (boxVars (ivHull t0 t1 NT) (ivHull 0 n1 NS))) k).ok = true := hok
  refine axis_core hvan ht01 hn1p hn1 hok' ?_ hτ hs σ
  rintro t (rfl | rfl) σ
  · have := corner_of_le l1 c1 σ; simpa using this
  · have := corner_of_le l2 c2 σ; simpa using this

/-- **Soundness of a cover certificate**: if the coefficients vanish on the axis, then
`Ψ > 0` at every point of the covered rectangle with `s > 0`. -/
theorem Cover.sound {D : Data} (hvan : ∀ τ k, ecE D k τ 0 = 0) {t0 t1 n0 n1 : ℤ}
    (h : Cover D t0 t1 n0 n1) {τ s : ℝ}
    (hτ : τ ∈ Icc ((t0 : ℝ) / (NT : ℤ)) ((t1 : ℝ) / (NT : ℤ)))
    (hs : s ∈ Icc ((n0 : ℝ) / (NS : ℤ)) ((n1 : ℝ) / (NS : ℤ))) (hs0 : 0 < s) (σ : ℝ) :
    0 < Psi D τ s σ := by
  induction h generalizing τ s with
  | leaf t0 t1 n0 n1 hok => exact boxOK_sound hok hτ hs σ
  | axis t0 t1 n1 hok => exact axisOK_sound hvan hok hτ ⟨hs0, hs.2⟩ σ
  | leaf2 t0 t1 n0 n1 R00 R10 R01 R11 h c1 c2 c3 c4 => exact leaf2_sound h c1 c2 c3 c4 hτ hs σ
  | axis2 t0 t1 n1 R0 R1 h c1 c2 => exact axis2_sound hvan h c1 c2 hτ ⟨hs0, hs.2⟩ σ
  | splitT t0 tm t1 n0 n1 _ _ ih1 ih2 =>
    rcases le_total τ ((tm : ℝ) / (NT : ℤ)) with h | h
    · exact ih1 ⟨hτ.1, h⟩ hs hs0
    · exact ih2 ⟨h, hτ.2⟩ hs hs0
  | splitS t0 t1 n0 nm n1 _ _ ih1 ih2 =>
    rcases le_total s ((nm : ℝ) / (NS : ℤ)) with h | h
    · exact ih1 hτ ⟨hs.1, h⟩ hs0
    · exact ih2 hτ ⟨h, hs.2⟩ hs0

end PlasmaLean.Design.SolovevBallooning
