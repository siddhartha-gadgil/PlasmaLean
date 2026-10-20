/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevBallooningGeom

/-!
# Ballooning certificate: from the scaled numerator to the stability of the reactor lines

* Link lemmas: along the field line the scaled certificate trees of `SolovevBallooningDefs`
  equal the physical trees of `SolovevBallooningGeom` up to powers of `s`
  (`tp0 = s² p₀`, `tp1 = s p₁`, `tp2 = p₂`, `tsq0 = s q₀`, `tq1 = q₁`, `td = s d`), and the
  scaled secular coefficient satisfies `a' = q₁` (`hasDerivAt_line_a`).
* `riccatiScaled`: the two-variable Riccati certificate of the SCALED line problem
  (`P/s = Π(σ̃)/s`, `Q = Θ(σ̃)`, secular variable `σ̃ = s σ`, rate `s d`), assuming the
  numerator `N̂ = Π · I − s G² = Σₖ eₖ σ̃ᵏ` is positive (`Nsum_eq`, `riccati_scaled`).
* `reactorLine_stable_of_N`: positivity of `N̂` along the line implies ballooning stability of
  every eikonal family of the surface (the line energy of `reactorLine` is `1/s` times the
  scaled energy).
* `Nline_pos_of_psi`: positivity of the chart numerator `Psi` on `τ ∈ [−1, 1]` gives positivity
  of `N̂` along the whole line (the half `x < 0` by up–down symmetry, `baseT_negx`,
  `Nsum_negx`).
-/

public section
noncomputable section

namespace PlasmaLean.Design.SolovevBallooning

open Real Set PlasmaLean.Fields
open PlasmaLean.Stability.BallooningInfinite PlasmaLean.Stability.BallooningReduction
open PlasmaLean.Design.Solovev PlasmaLean.Design.SolovevMercier PlasmaLean.Design.SolovevAlpha
open Tm

/-! ## Link between scaled and physical trees -/

section link
variable {s x y R r iB : ℝ}

/-- Scaled and physical `B_R` agree. -/
theorem link_BR : tBR.eval (envP s x y R r R⁻¹ iB) = pBR.eval (envP s x y R r R⁻¹ iB) := by
  simp only [tBR, pBR, tzh, pz, tS, tR, tr, tX, tiR, Tm.eval, envP, envR]; ring

/-- Scaled and physical `B_φ` agree. -/
theorem link_BP : tBP.eval (envP s x y R r R⁻¹ iB) = pBP.eval (envP s x y R r R⁻¹ iB) := rfl

/-- Scaled and physical `B_z` agree (using `R² = L² + 2 s y`). -/
theorem link_BZ (hR : R ^ 2 = 100 + 2 * s * y) :
    tBZ.eval (envP s x y R r R⁻¹ iB) = pBZ.eval (envP s x y R r R⁻¹ iB) := by
  simp only [tBZ, pBZ, tWh, pW, tzh, pz, tS, tR, tr, tX, tY, tiR, Tm.eval, envP, envR]
  push_cast
  linear_combination (-(7 : ℝ) / 400) * hR

/-- Scaled and physical `(∇√ψ̃)_R` agree. -/
theorem link_gsR (hR : R ^ 2 = 100 + 2 * s * y) (hRne : R ≠ 0) (hs : s ≠ 0) :
    tgsR.eval (envP s x y R r R⁻¹ iB) = pgsR.eval (envP s x y R r R⁻¹ iB) := by
  simp only [tgsR, pgsR, tWh, pW, tzh, pz, tS, tIs, tR, tr, tX, tY, tiR, Tm.eval, envP, envR]
  push_cast
  field_simp
  linear_combination (-R ^ 2) * hR

/-- Scaled and physical `(∇√ψ̃)_z` agree. -/
theorem link_gsZ (hRne : R ≠ 0) (hs : s ≠ 0) :
    tgsZ.eval (envP s x y R r R⁻¹ iB) = pgsZ.eval (envP s x y R r R⁻¹ iB) := by
  simp only [tgsZ, pgsZ, pz, tS, tIs, tR, tr, tX, tiR, Tm.eval, envP, envR]
  push_cast
  field_simp

/-- The scaled `k̂_R` is `s k₀_R`. -/
theorem link_kR (hs : s ≠ 0) :
    tkR.eval (envP s x y R r R⁻¹ iB) = s * pkR.eval (envP s x y R r R⁻¹ iB) := by
  simp only [tkR, pkR, pPhit, tgtR, pgtR, trate, tiR3, tS, tIs, tr, tX, tY, tiR, Tm.eval,
    envP, envR]
  push_cast
  field_simp

/-- The scaled `k̂_φ` is `s k₀_φ`. -/
theorem link_kP : tkP.eval (envP s x y R r R⁻¹ iB) = s * pkP.eval (envP s x y R r R⁻¹ iB) := by
  simp only [tkP, pkP, tS, tiR, Tm.eval, envP, envR]

/-- The scaled `k̂_z` is `s k₀_z`. -/
theorem link_kZ (hs : s ≠ 0) :
    tkZ.eval (envP s x y R r R⁻¹ iB) = s * pkZ.eval (envP s x y R r R⁻¹ iB) := by
  simp only [tkZ, pkZ, pPhit, tgtZ, pgtZ, trate, tiR3, tIs, tR, tr, tY, tiR, Tm.eval,
    envP, envR]
  push_cast
  field_simp

/-- Scaled and physical `(DB B)_R` agree. -/
theorem link_GR (hR : R ^ 2 = 100 + 2 * s * y) :
    tGR.eval (envP s x y R r R⁻¹ iB) = pGR.eval (envP s x y R r R⁻¹ iB) := by
  simp only [tGR, pGR, tiR3, pW, pz, tS, tR, tr, tX, tY, tiR, Tm.eval, Tm.sub, envP, envR]
  push_cast
  linear_combination ((49 : ℝ) / 160000 * R) * hR

/-- Scaled and physical `(DB B)_z` agree. -/
theorem link_GZ (hR : R ^ 2 = 100 + 2 * s * y) :
    tGZ.eval (envP s x y R r R⁻¹ iB) = pGZ.eval (envP s x y R r R⁻¹ iB) := by
  simp only [tGZ, pGZ, tWh, pW, tzh, pz, tS, tR, tr, tX, tY, tiR, Tm.eval, Tm.sub, envP, envR]
  push_cast
  linear_combination (-(49 : ℝ) / 80000 * (r * s * (x * R⁻¹))) * hR

/-- Scaled and physical `|B|²` agree. -/
theorem link_B2 (hR : R ^ 2 = 100 + 2 * s * y) :
    tB2.eval (envP s x y R r R⁻¹ iB) = pB2.eval (envP s x y R r R⁻¹ iB) := by
  have h1 := link_BR (s := s) (x := x) (y := y) (R := R) (r := r) (iB := iB)
  have h3 := link_BZ (x := x) (r := r) (iB := iB) hR
  simp only [tB2, pB2, Tm.eval] at h1 h3 ⊢
  rw [h1, h3]; rfl

end link


/-! ## The scaled coefficients along the line -/

theorem envL_eq (s t : ℝ) : envL s t =
    envP s (Real.cos t) (Real.sin t) (RS 10 s t) √2 (RS 10 s t)⁻¹ (B2v s t)⁻¹ := rfl

section alongline
variable {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (t : ℝ)
include hs0 hs

/-- `|B|²` along the line from the scaled tree. -/
theorem line_tB2 : tB2.eval (envL s t) = B2v s t := by
  obtain ⟨hx, hR, hr, hRne⟩ := line_relations hs0 hs t
  rw [envL_eq, link_B2 hR, ← envL_eq, tB2_env]

omit hs in
/-- `p̂₀ = s² p₀` along the line. -/
theorem line_p0 : tp0.eval (envL s t) = s ^ 2 * pp0.eval (envL s t) := by
  have hsne := hs0.ne'
  rw [envL_eq]
  simp only [tp0, pp0, Tm.eval]
  rw [link_kR hsne, link_kP, link_kZ hsne]; ring

/-- `p̂₁ = s p₁` along the line. -/
theorem line_p1 : tp1.eval (envL s t) = s * pp1.eval (envL s t) := by
  have hsne := hs0.ne'
  obtain ⟨hx, hR, hr, hRne⟩ := line_relations hs0 hs t
  rw [envL_eq]
  simp only [tp1, pp1, Tm.eval]
  rw [link_kR hsne, link_kZ hsne, link_gsR hR hRne hsne, link_gsZ hRne hsne]; ring

/-- `p̂₂ = p₂` along the line. -/
theorem line_p2 : tp2.eval (envL s t) = pp2.eval (envL s t) := by
  have hsne := hs0.ne'
  obtain ⟨hx, hR, hr, hRne⟩ := line_relations hs0 hs t
  rw [envL_eq]
  simp only [tp2, pp2, Tm.eval]
  rw [link_gsR hR hRne hsne, link_gsZ hRne hsne]

omit hs0 hs in
/-- `d̂ = s d` along the line. -/
theorem line_d : td.eval (envL s t) = s * pd.eval (envL s t) := by
  simp only [td, pd, Tm.eval, tY, tS, envL, envP, envR]; ring

omit hs0 hs in
/-- The slot `5` along the line is `1/|B|²`. -/
theorem line_iB : tiB.eval (envL s t) = (B2v s t)⁻¹ := by
  simp only [tiB, Tm.eval, envL, envP, envR]

omit hs0 hs in
/-- `B_R` along the line (scaled = physical). -/
theorem line_BR : tBR.eval (envL s t) = pBR.eval (envL s t) := by
  rw [envL_eq, link_BR]

omit hs0 hs in
/-- `B_φ` along the line (scaled = physical). -/
theorem line_BP : tBP.eval (envL s t) = pBP.eval (envL s t) := rfl

/-- `B_z` along the line (scaled = physical). -/
theorem line_BZ : tBZ.eval (envL s t) = pBZ.eval (envL s t) := by
  obtain ⟨hx, hR, hr, hRne⟩ := line_relations hs0 hs t
  rw [envL_eq, link_BZ hR]

/-- `(∇√ψ̃)_R` along the line (scaled = physical). -/
theorem line_gsR : tgsR.eval (envL s t) = pgsR.eval (envL s t) := by
  obtain ⟨hx, hR, hr, hRne⟩ := line_relations hs0 hs t
  rw [envL_eq, link_gsR hR hRne hs0.ne']

/-- `(∇√ψ̃)_z` along the line (scaled = physical). -/
theorem line_gsZ : tgsZ.eval (envL s t) = pgsZ.eval (envL s t) := by
  obtain ⟨hx, hR, hr, hRne⟩ := line_relations hs0 hs t
  rw [envL_eq, link_gsZ hRne hs0.ne']

omit hs in
/-- `k̂_R = s k₀_R` along the line. -/
theorem line_kR : tkR.eval (envL s t) = s * pkR.eval (envL s t) := by
  rw [envL_eq, link_kR hs0.ne']

omit hs0 hs in
/-- `k̂_φ = s k₀_φ` along the line. -/
theorem line_kP : tkP.eval (envL s t) = s * pkP.eval (envL s t) := by
  rw [envL_eq, link_kP]

omit hs in
/-- `k̂_z = s k₀_z` along the line. -/
theorem line_kZ : tkZ.eval (envL s t) = s * pkZ.eval (envL s t) := by
  rw [envL_eq, link_kZ hs0.ne']

/-- `(DB B)_R` along the line (scaled = physical). -/
theorem line_GR : tGR.eval (envL s t) = pGR.eval (envL s t) := by
  obtain ⟨hx, hR, hr, hRne⟩ := line_relations hs0 hs t
  rw [envL_eq, link_GR hR]

/-- `(DB B)_z` along the line (scaled = physical). -/
theorem line_GZ : tGZ.eval (envL s t) = pGZ.eval (envL s t) := by
  obtain ⟨hx, hR, hr, hRne⟩ := line_relations hs0 hs t
  rw [envL_eq, link_GZ hR]

/-- `B × k₀ · μ₀∇p = 3c|B|²` along the line. -/
theorem line_Bk0gp : pBk0gp.eval (envL s t) = 3 * (7 / 400) * B2v s t := by
  obtain ⟨hx, hR, hr, hRne⟩ := line_relations hs0 hs t
  have hI := Bk0gp_eq s ((B2v s t)⁻¹) hx hR hr hRne hs0.ne'
  rw [← envL_eq, tB2_env] at hI
  exact hI

/-- `s q₀` along the line: the scaled drive tree is `s` times the physical `q₀`. -/
theorem line_sq0 : tsq0.eval (envL s t) = s * pq0.eval (envL s t) := by
  have hB := (B2v_pos hs0 hs t).ne'
  simp only [tsq0, pq0, tcross, pBk0G, pcross, Tm.sub, Tm.eval]
  rw [line_Bk0gp hs0 hs, line_iB, line_BR, line_BP, line_BZ hs0 hs,
    line_kR hs0, line_kP, line_kZ hs0, line_GR hs0 hs, line_GZ hs0 hs]
  field_simp
  ring

/-- `q₁` along the line: the scaled and physical trees agree. -/
theorem line_q1 : tq1.eval (envL s t) = pq1.eval (envL s t) := by
  have hB := (B2v_pos hs0 hs t).ne'
  simp only [tq1, pq1, pBgsG, pcross, Tm.sub, Tm.eval]
  rw [line_Bk0gp hs0 hs, line_iB, line_BP,
    line_gsR hs0 hs, line_gsZ hs0 hs, line_GR hs0 hs, line_GZ hs0 hs]
  field_simp
  ring

end alongline


/-! ## Certificate data and profiles -/

/-- The variables of the profiles: `x, y, √2, s`. -/
@[expose] def PV (i : ℕ) : Prop := i ≤ 1 ∨ i = 3 ∨ i = 6

/-- **Admissible certificate data**: the coefficient trees involve only `√2` and `s`. -/
@[expose] def DataOK (D : Data) : Prop :=
  D.dl.UsesOnly (fun i => i = 3 ∨ i = 6) ∧ (∀ e ∈ D.A0, e.UsesOnly (fun i => i = 3 ∨ i = 6)) ∧
    (∀ e ∈ D.A1, e.UsesOnly (fun i => i = 3 ∨ i = 6)) ∧
    (∀ e ∈ D.A2, e.UsesOnly (fun i => i = 3 ∨ i = 6))

/-- Variables of a Horner tree. -/
theorem usesOnly_ptree {P : ℕ → Prop} {l : List Tm} (hl : ∀ e ∈ l, e.UsesOnly P) {y : Tm}
    (hy : y.UsesOnly P) : (ptree l y).UsesOnly P := by
  induction l with
  | nil => trivial
  | cons a l ih =>
    exact ⟨hl a (by simp), hy, ih (fun e he => hl e (by simp [he]))⟩

/-- Variables of a symbolic derivative tree. -/
theorem usesOnly_diff {P Q : ℕ → Prop} {dv : ℕ → Tm} (e : Tm) (he : e.UsesOnly P)
    (hdv : ∀ i, P i → (dv i).UsesOnly Q) (hPQ : ∀ i, P i → Q i) : (diff dv e).UsesOnly Q := by
  induction e with
  | c p q => trivial
  | v i => exact hdv i he
  | add a b iha ihb => exact ⟨iha he.1, ihb he.2⟩
  | mul a b iha ihb => exact ⟨⟨iha he.1, he.2.mono hPQ⟩, ⟨he.1.mono hPQ, ihb he.2⟩⟩
  | neg a iha => exact iha he
  | sq a iha => exact ⟨trivial, he.mono hPQ, iha he⟩

/-- The derivative trees of `x, y` use only the profile variables. -/
theorem dvT_usesOnly (i : ℕ) (hi : PV i) : (dvT i).UsesOnly PV := by
  rcases i with _ | _ | i
  · simp [dvT, UsesOnly, tY, PV]
  · simp [dvT, UsesOnly, tX, PV]
  · simp [dvT, UsesOnly]

/-- `f₀` uses only `x, y, √2, s`. -/
theorem tf0_usesOnly {D : Data} (hD : DataOK D) : (tf0 D).UsesOnly PV :=
  ⟨by simp [tX, UsesOnly, PV], usesOnly_ptree (fun e he => (hD.2.1 e he).mono
    (fun i hi => by rcases hi with rfl | rfl <;> simp [PV])) (by simp [tY, UsesOnly, PV])⟩

/-- `f₁` uses only `x, y, √2, s`. -/
theorem tf1_usesOnly {D : Data} (hD : DataOK D) : (tf1 D).UsesOnly PV :=
  ⟨by simp [tX, UsesOnly, PV], usesOnly_ptree (fun e he => (hD.2.2.1 e he).mono
    (fun i hi => by rcases hi with rfl | rfl <;> simp [PV])) (by simp [tY, UsesOnly, PV])⟩

/-- `f₂` uses only `x, y, √2, s`. -/
theorem tf2_usesOnly {D : Data} (hD : DataOK D) : (tf2 D).UsesOnly PV :=
  usesOnly_ptree (fun e he => (hD.2.2.2 e he).mono
    (fun i hi => by rcases hi with rfl | rfl <;> simp [PV])) (by simp [tY, UsesOnly, PV])

/-- The `t`-derivative of a profile uses only the profile variables. -/
theorem diff_usesOnly {e : Tm} (he : e.UsesOnly PV) : (diff dvT e).UsesOnly PV :=
  usesOnly_diff e he dvT_usesOnly (fun _ h => h)

section alongline2
variable {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (t : ℝ)
include hs0 hs

/-- **Derivatives of the profiles along the line** (`x' = −y`, `y' = x`, `√2, s` constant). -/
theorem hasDerivAt_prof (e : Tm) (he : e.UsesOnly PV) :
    HasDerivAt (fun t => e.eval (envL s t)) ((diff dvT e).eval (envL s t)) t := by
  refine (hasDerivAt_tree hs0 hs e t).congr_deriv ?_
  rw [Tm.eval_diff]
  apply Tm.deriv_congr e he (fun _ _ => rfl)
  intro i hi
  rcases hi with hi | rfl | rfl
  · interval_cases i <;> simp [denv, envD, envR, dvT, tY, tX, Tm.eval, envL, envP]
  · simp [denv, envD, envR, dvT, Tm.eval]
  · simp [denv, envD, envR, dvT, Tm.eval]

/-- `s β̂ + 25 = |B|²` along the line. -/
theorem line_beta : tbeta.eval (envL s t) * s + 25 = B2v s t := by
  obtain ⟨hx, hR, hr, hRne⟩ := line_relations hs0 hs t
  rw [← tB2_env]
  simp only [tbeta, pB2, pBR, pBP, pBZ, pW, pz, tWh, tzh, tS, tX, tY, tR, tr, tiR, Tm.eval,
    Tm.sub, envL, envP, envR]
  push_cast
  field_simp
  linear_combination (-7840000*(RS 10 s t)^6 - 15680000*(RS 10 s t)^4*s*(Real.sin t) +
      784000000*(RS 10 s t)^4 - 23520000*(RS 10 s t)^2*√2^2*s^2*(Real.cos t)^2 +
      15680000*(RS 10 s t)^2*s^2*(Real.cos t)^2 + 640000000000*(RS 10 s t)^2 -
      15680000*√2^2*s^3*(Real.cos t)^2*(Real.sin t) - 784000000*√2^2*s^2*(Real.cos t)^2 +
      31360000*s^3*(Real.cos t)^2*(Real.sin t) + 1568000000*s^2*(Real.cos t)^2) * hR +
      (-31360000*s^4*(Real.cos t)^2*(Real.sin t)^2 -
      3136000000*s^3*(Real.cos t)^2*(Real.sin t) - 78400000000*s^2*(Real.cos t)^2) * hr

end alongline2


section alongline3
variable {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (t : ℝ)
include hs0 hs

/-- The secular coefficient `a = δ + 3 β̂/|B|²` is the physical `a₀ − (75/s)/|B|²` with
`a₀ = δ + 3/s`. -/
theorem line_a (D : Data) : (baseT D 7).eval (envL s t) =
    (pa (add D.dl (mul (c 3 1) tIs))).eval (envL s t) := by
  have hB := (B2v_pos hs0 hs t).ne'
  have hb := line_beta hs0 hs t
  have hsne := hs0.ne'
  simp only [baseT, pa, Tm.sub, Tm.eval, tIs, tiB, envL, envP, envR] at hb ⊢
  have e : tbeta.eval (envR (Real.cos t) (Real.sin t) (RS 10 s t) √2 (RS 10 s t)⁻¹
      (B2v s t)⁻¹ s s⁻¹ 0) = (B2v s t - 25) / s := by
    rw [eq_div_iff hsne]; linarith
  rw [e]
  push_cast
  field_simp
  ring

/-- `a' = q₁` for the scaled coefficient `a` of the certificate. -/
theorem hasDerivAt_line_a (D : Data) (hD : DataOK D) :
    HasDerivAt (fun t => (baseT D 7).eval (envL s t)) (tq1.eval (envL s t)) t := by
  have ha0 : (add D.dl (mul (c 3 1) tIs)).UsesOnly fun i => i = 3 ∨ 6 ≤ i :=
    ⟨hD.1.mono fun i hi => by rcases hi with rfl | rfl <;> simp, trivial, by simp [tIs, UsesOnly]⟩
  have h := hasDerivAt_a _ ha0 hs0 hs t
  rw [← line_q1 hs0 hs] at h
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => line_a hs0 hs t D)

end alongline3

/-- The bending coefficient `P(t, σ)` is positive for every `(t, σ)`. -/
theorem Pc_pos {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25) (t σ : ℝ) : 0 < Pc s t σ := by
  rw [← P_geom hs0 hs t σ, ballooningP]
  have hR := RS_pos_r hs0 hs t
  have hk : lnK0 s t - σ • lnGs s t ≠ 0 := by
    rw [lnK0, lnGs, smul_cyl, cyl_sub]
    apply cyl_ne_zero
    simp only [Tm.eval, pkP, tiR, envL, envP, envR, mul_zero, sub_zero]
    exact inv_ne_zero hR.ne'
  have hl : 0 < lnEll s t := by
    simp only [lnEll, Tm.eval, tell, tr, tiR, envL, envP, envR]; push_cast; positivity
  have hB : 0 < ‖lnB s t‖ := norm_pos_iff.mpr (lnB_ne hs0 hs t)
  have hk' : 0 < ‖lnK0 s t - σ • lnGs s t‖ := norm_pos_iff.mpr hk
  positivity


/-! ## The scaled two-variable Riccati certificate -/

/-- `ρ(u) = w²/(w² + u²)` (`w = 2`). -/ @[expose] def rhoW (u : ℝ) : ℝ := 4 / (4 + u ^ 2)
/-- `ν(u) = w u/(w² + u²)`. -/ @[expose] def nuW (u : ℝ) : ℝ := 2 * u / (4 + u ^ 2)
/-- `ρ'(u)`. -/ @[expose] def drhoW (u : ℝ) : ℝ := -(8 * u) / (4 + u ^ 2) ^ 2
/-- `ν'(u)`. -/ @[expose] def dnuW (u : ℝ) : ℝ := 2 * (4 - u ^ 2) / (4 + u ^ 2) ^ 2

/-- Derivative of `ρ`. -/
theorem hasDerivAt_rhoW (u : ℝ) : HasDerivAt rhoW (drhoW u) u := by
  have hpos : (0 : ℝ) < 4 + u ^ 2 := by positivity
  have hd : HasDerivAt (fun u => 4 + u ^ 2) (2 * u) u := by
    simpa using ((hasDerivAt_id u).pow 2).const_add 4
  have := (hasDerivAt_const u (4 : ℝ)).div hd hpos.ne'
  unfold rhoW drhoW
  convert this using 1
  ring

/-- Derivative of `ν`. -/
theorem hasDerivAt_nuW (u : ℝ) : HasDerivAt nuW (dnuW u) u := by
  have hpos : (0 : ℝ) < 4 + u ^ 2 := by positivity
  have hd : HasDerivAt (fun u => 4 + u ^ 2) (2 * u) u := by
    simpa using ((hasDerivAt_id u).pow 2).const_add 4
  have hn : HasDerivAt (fun u => 2 * u) 2 u := by simpa using (hasDerivAt_id u).const_mul 2
  have := hn.div hd hpos.ne'
  unfold nuW dnuW
  convert this using 1
  field_simp
  ring

/-- Continuity of `ρ, ν, ρ', ν'`. -/
theorem continuous_W : Continuous rhoW ∧ Continuous nuW ∧ Continuous drhoW ∧ Continuous dnuW := by
  have h1 : ∀ u : ℝ, 4 + u ^ 2 ≠ 0 := fun u => by positivity
  have h2 : ∀ u : ℝ, (4 + u ^ 2) ^ 2 ≠ 0 := fun u => by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Continuous.div (by fun_prop) (by fun_prop) h1
  · exact Continuous.div (by fun_prop) (by fun_prop) h1
  · exact Continuous.div (by fun_prop) (by fun_prop) h2
  · exact Continuous.div (by fun_prop) (by fun_prop) h2

/-- **The numerator identity**: `Σ eₖ uᵏ = Π · I − s G²`. -/
theorem Nsum_eq (b : ℕ → ℝ) (u : ℝ) :
    ∑ k ∈ Finset.range 7, (etree k).eval b * u ^ k =
      (b 0 + u * b 1 + u ^ 2 * b 2) * (b 3 * (4 + u ^ 2) ^ 2 -
        (b 4 * 4 + b 5 * 2 * u) * (4 + u ^ 2) -
        b 6 * (b 7 * (4 + u ^ 2) ^ 2 - 8 * u * b 9 + 2 * (4 - u ^ 2) * b 10)) -
      b 11 * ((u * b 7 + b 8) * (4 + u ^ 2) + 4 * b 9 + 2 * u * b 10) ^ 2 := by
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, etree, tin, tgg,
    Tm.eval, Tm.sub]
  push_cast
  ring

/-- **The scaled Riccati defect from the numerator.** -/
theorem riccati_scaled {s p0 p1 p2 sq0 q1 A g1 g2 d a f0 f1 f2 u : ℝ}
    (hP : 0 < p0 + u * p1 + u ^ 2 * p2)
    (hN : 0 < (p0 + u * p1 + u ^ 2 * p2) * (A * (4 + u ^ 2) ^ 2 -
        (g1 * 4 + g2 * 2 * u) * (4 + u ^ 2) -
        d * (a * (4 + u ^ 2) ^ 2 - 8 * u * f1 + 2 * (4 - u ^ 2) * f2)) -
      s * ((u * a + f0) * (4 + u ^ 2) + 4 * f1 + 2 * u * f2) ^ 2) :
    u * q1 + (sq0 - A) + g1 * rhoW u + g2 * nuW u +
        d * (a + f1 * drhoW u + f2 * dnuW u) +
        (u * a + f0 + f1 * rhoW u + f2 * nuW u) ^ 2 / ((p0 + u * p1 + u ^ 2 * p2) / s) ≤
      sq0 + u * q1 := by
  set P := p0 + u * p1 + u ^ 2 * p2 with hPdef
  have hW : (0 : ℝ) < 4 + u ^ 2 := by positivity
  rw [← sub_nonneg]
  have key : sq0 + u * q1 - (u * q1 + (sq0 - A) + g1 * rhoW u + g2 * nuW u +
        d * (a + f1 * drhoW u + f2 * dnuW u) +
        (u * a + f0 + f1 * rhoW u + f2 * nuW u) ^ 2 / (P / s)) =
      (P * (A * (4 + u ^ 2) ^ 2 - (g1 * 4 + g2 * 2 * u) * (4 + u ^ 2) -
        d * (a * (4 + u ^ 2) ^ 2 - 8 * u * f1 + 2 * (4 - u ^ 2) * f2)) -
      s * ((u * a + f0) * (4 + u ^ 2) + 4 * f1 + 2 * u * f2) ^ 2) / (P * (4 + u ^ 2) ^ 2) := by
    simp only [rhoW, nuW, drhoW, dnuW]
    field_simp
    ring
  rw [key]
  positivity

/-- Product rule on the `(t, u)` plane. -/
theorem hasFDerivAt_prod {g h : ℝ → ℝ} {g' h' t σ : ℝ} (hg : HasDerivAt g g' t)
    (hh : HasDerivAt h h' σ) :
    HasFDerivAt (fun p : ℝ × ℝ => g p.1 * h p.2)
      ((h σ * g') • ContinuousLinearMap.fst ℝ ℝ ℝ + (g t * h') • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (t, σ) := by
  have h1 := hg.hasFDerivAt.comp (t, σ) (hasFDerivAt_fst (𝕜 := ℝ) (p := (t, σ)))
  have h2 := hh.hasFDerivAt.comp (t, σ) (hasFDerivAt_snd (𝕜 := ℝ) (p := (t, σ)))
  refine (h1.mul h2).congr_fderiv ?_
  ext <;> simp

section ric
variable (D : Data) (s : ℝ)

/-- Base coefficients along the line. -/
@[expose] def bL (t : ℝ) (j : ℕ) : ℝ := (baseT D j).eval (envL s t)
/-- The numerator `N̂(t, u) = Σ eₖ uᵏ` along the line. -/
@[expose] def Nline (t u : ℝ) : ℝ := ∑ k ∈ Finset.range 7, (etree k).eval (bL D s t) * u ^ k
/-- Scaled bending coefficient `Π/s`. -/
@[expose] def Psc (t u : ℝ) : ℝ := (bL D s t 0 + u * bL D s t 1 + u ^ 2 * bL D s t 2) / s
/-- Scaled drive `Θ = s q₀ + u q₁`. -/
@[expose] def Qsc (t u : ℝ) : ℝ := tsq0.eval (envL s t) + u * tq1.eval (envL s t)
/-- Scaled secular rate `s d`. -/
@[expose] def dsc (t : ℝ) : ℝ := td.eval (envL s t)
/-- The scaled flux `Φ = u a + f₀ + f₁ ρ + f₂ ν`. -/
@[expose] def Fsc (t u : ℝ) : ℝ :=
  u * bL D s t 7 + bL D s t 8 + bL D s t 9 * rhoW u + bL D s t 10 * nuW u
/-- `∂ₜΦ`. -/
@[expose] def Ftsc (t u : ℝ) : ℝ := u * tq1.eval (envL s t) + (tsq0.eval (envL s t) - bL D s t 3) +
  bL D s t 4 * rhoW u + bL D s t 5 * nuW u
/-- `∂ᵤΦ`. -/
@[expose] def Fssc (t u : ℝ) : ℝ := bL D s t 7 + bL D s t 9 * drhoW u + bL D s t 10 * dnuW u

end ric

section ric2
variable {D : Data} (hD : DataOK D) {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25)
include hD hs0 hs

omit hD in
/-- Continuity of the base coefficients along the line. -/
theorem continuous_bL (j : ℕ) : Continuous fun t => bL D s t j := continuous_tree hs0 hs _

/-- **The scaled two-variable Riccati certificate of the surface `ψ̃ = s²`**, assuming the
positivity of the numerator `N̂` along the line. -/
@[expose] def riccatiScaled (hN : ∀ t u, 0 < Nline D s t u) :
    Riccati2D (Psc D s) (Qsc s) (dsc s) where
  F := Fsc D s
  Ft := Ftsc D s
  Fs := Fssc D s
  hasFDeriv t u := by
    have ha := hasDerivAt_line_a hs0 hs t D hD
    have hf0 := hasDerivAt_prof hs0 hs t (tf0 D) (tf0_usesOnly hD)
    have hf1 := hasDerivAt_prof hs0 hs t (tf1 D) (tf1_usesOnly hD)
    have hf2 := hasDerivAt_prof hs0 hs t (tf2 D) (tf2_usesOnly hD)
    have T1 := hasFDerivAt_prod ha (hasDerivAt_id u)
    have T2 := hasFDerivAt_prod hf0 (hasDerivAt_const u (1 : ℝ))
    have T3 := hasFDerivAt_prod hf1 (hasDerivAt_rhoW u)
    have T4 := hasFDerivAt_prod hf2 (hasDerivAt_nuW u)
    have hsum := ((T1.add T2).add T3).add T4
    refine (hsum.congr_fderiv ?_).congr_of_eventuallyEq ?_
    · ext <;> simp [Ftsc, Fssc, bL, baseT, Tm.eval]
      ring
    · exact Filter.Eventually.of_forall fun p => by simp [Fsc, bL, baseT]; ring
  Ft_cont := by
    obtain ⟨hρ, hν, -, -⟩ := continuous_W
    have hf : Continuous fun p : ℝ × ℝ => p.1 := continuous_fst
    have hs' : Continuous fun p : ℝ × ℝ => p.2 := continuous_snd
    have c1 := (continuous_tree hs0 hs tq1).comp hf
    have c2 := (continuous_tree hs0 hs tsq0).comp hf
    have c3 := (continuous_bL (D := D) hs0 hs 3).comp hf
    have c4 := (continuous_bL (D := D) hs0 hs 4).comp hf
    have c5 := (continuous_bL (D := D) hs0 hs 5).comp hf
    exact (((hs'.mul c1).add (c2.sub c3)).add (c4.mul (hρ.comp hs'))).add (c5.mul (hν.comp hs'))
  Fs_cont := by
    obtain ⟨-, -, hρ', hν'⟩ := continuous_W
    have hf : Continuous fun p : ℝ × ℝ => p.1 := continuous_fst
    have hs' : Continuous fun p : ℝ × ℝ => p.2 := continuous_snd
    have c7 := (continuous_bL (D := D) hs0 hs 7).comp hf
    have c9 := (continuous_bL (D := D) hs0 hs 9).comp hf
    have c10 := (continuous_bL (D := D) hs0 hs 10).comp hf
    exact (c7.add (c9.mul (hρ'.comp hs'))).add (c10.mul (hν'.comp hs'))
  P_pos t u := by
    have h := Pc_pos hs0 hs t (u / s)
    have e : Psc D s t u = s * Pc s t (u / s) := by
      simp only [Psc, Pc, bL, baseT]
      rw [line_p0 hs0, line_p1 hs0 hs, line_p2 hs0 hs]
      field_simp
    rw [e]; exact mul_pos hs0 h
  ineq t u := by
    have hN' := hN t u
    simp only [Nline] at hN'
    rw [Nsum_eq] at hN'
    have hP : 0 < bL D s t 0 + u * bL D s t 1 + u ^ 2 * bL D s t 2 := by
      have h := Pc_pos hs0 hs t (u / s)
      have e : bL D s t 0 + u * bL D s t 1 + u ^ 2 * bL D s t 2 = s ^ 2 * Pc s t (u / s) := by
        simp only [Pc, bL, baseT]
        rw [line_p0 hs0, line_p1 hs0 hs, line_p2 hs0 hs]
        field_simp
      rw [e]; positivity
    have h11 : bL D s t 11 = s := by simp [bL, baseT, tS, Tm.eval, envL, envP, envR]
    rw [h11] at hN'
    have := riccati_scaled (q1 := tq1.eval (envL s t)) (sq0 := tsq0.eval (envL s t)) hP hN'
    simpa [Ftsc, Fssc, Fsc, Psc, Qsc, dsc, bL, baseT] using this

end ric2


/-! ## Stability of the reactor lines from the positivity of the numerator -/

/-- **Ideal-ballooning stability of a reactor surface from the numerator.** If the numerator
`N̂(t, u)` of the scaled Riccati defect is positive along the line of the surface `ψ̃ = s²`,
then for every shift `c` (eikonal family, `θ_k`) the ballooning line is stable. -/
theorem reactorLine_stable_of_N {D : Data} (hD : DataOK D) {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25)
    (hN : ∀ t u, 0 < Nline D s t u) (c : ℝ) : (reactorLine hs0 hs c).Stable := by
  intro ξ ξ' a b hA
  have hf : Continuous fun p : ℝ × ℝ => p.1 := continuous_fst
  have hs' : Continuous fun p : ℝ × ℝ => p.2 := continuous_snd
  have hPc : Continuous fun p : ℝ × ℝ => Psc D s p.1 p.2 := by
    have c0 := (continuous_bL (D := D) hs0 hs 0).comp hf
    have c1 := (continuous_bL (D := D) hs0 hs 1).comp hf
    have c2 := (continuous_bL (D := D) hs0 hs 2).comp hf
    exact ((c0.add (hs'.mul c1)).add ((hs'.pow 2).mul c2)).div_const s
  have hQc : Continuous fun p : ℝ × ℝ => Qsc s p.1 p.2 := by
    have c0 := (continuous_tree hs0 hs tsq0).comp hf
    have c1 := (continuous_tree hs0 hs tq1).comp hf
    exact c0.add (hs'.mul c1)
  have hσ : ∀ t, HasDerivAt (fun t => s * lnSig s t) (dsc s t) t := fun t => by
    have := (hasDerivAt_lnSig hs0 hs t).const_mul s
    simp only [dsc]; rw [line_d]; exact this
  have hd : Continuous (dsc s) := continuous_tree hs0 hs td
  have h := riccati2D_energy_nonneg (riccatiScaled hD hs0 hs hN) hPc hQc hσ hd (s * c) hA
  have eP : ∀ t, Psc D s t (s * lnSig s t - s * c) = s * (reactorLine hs0 hs c).P t := by
    intro t
    rw [reactorLine_P hs0 hs]
    simp only [Psc, Pc, bL, baseT]
    rw [line_p0 hs0, line_p1 hs0 hs, line_p2 hs0 hs]
    field_simp
  have eQ : ∀ t, Qsc s t (s * lnSig s t - s * c) = s * (reactorLine hs0 hs c).Q t := by
    intro t
    rw [reactorLine_Q hs0 hs]
    simp only [Qsc, Qc]
    rw [line_sq0 hs0 hs, line_q1 hs0 hs]
    ring
  simp only [lineEnergy, eP, eQ] at h ⊢
  have e : (fun x => s * (reactorLine hs0 hs c).P x * ξ' x ^ 2 +
      s * (reactorLine hs0 hs c).Q x * ξ x ^ 2) = fun x => s * ((reactorLine hs0 hs c).P x *
      ξ' x ^ 2 + (reactorLine hs0 hs c).Q x * ξ x ^ 2) := by
    funext x; ring
  rw [e, MeasureTheory.integral_const_mul] at h
  exact (mul_nonneg_iff_of_pos_left hs0).mp h


/-! ## Variables of the base trees and up–down symmetry -/

/-- Variable predicate of the data trees. -/
@[expose] def DV (i : ℕ) : Prop := i = 3 ∨ i = 6

/-- Data variables are among `0, …, 6`. -/
theorem DV_lt {i : ℕ} (h : DV i) : i < 7 := by rcases h with rfl | rfl <;> norm_num

/-- Profile variables are among `0, …, 6`. -/
theorem PV_lt {i : ℕ} (h : PV i) : i < 7 := by rcases h with h | rfl | rfl <;> omega

/-- The base trees only use the variables `0, …, 6`. -/
theorem baseT_usesOnly {D : Data} (hD : DataOK D) (j : ℕ) : (baseT D j).UsesOnly (· < 7) := by
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j
  · simp [baseT, UsesOnly, tp0, tkR, tkP, tkZ, tgtR, tgtZ, tiR3, trate, tden, tX, tY, tR, tr,
      tiR, tiB, tS]
  · simp [baseT, UsesOnly, tp1, tkR, tkZ, tgtR, tgtZ, tgsR, tgsZ, tWh, tzh, tiR3, trate, tden,
      tX, tY, tR, tr, tiR, tiB, tS]
  · simp [baseT, UsesOnly, tp2, tgsR, tgsZ, tWh, tzh, tden, tX, tY, tR, tr, tiR, tiB, tS]
  · refine ⟨?_, (diff_usesOnly (tf0_usesOnly hD)).mono fun i hi => PV_lt hi⟩
    simp [UsesOnly, tsq0, tcross, tkR, tkP, tkZ, tgtR, tgtZ, tGR, tGZ, tBR, tBP, tBZ, tWh, tzh,
      tiR3, trate, tell, tX, tY, tR, tr, tiR, tiB, tS, Tm.sub]
  · exact (diff_usesOnly (tf1_usesOnly hD)).mono fun i hi => PV_lt hi
  · exact (diff_usesOnly (tf2_usesOnly hD)).mono fun i hi => PV_lt hi
  · simp [baseT, UsesOnly, td, trate, tY, tr, tiR, tS]
  · refine ⟨hD.1.mono fun i hi => DV_lt hi, ?_⟩
    simp [UsesOnly, tbeta, tWh, tzh, tX, tY, tr, tiR, tiB, tS, Tm.sub]
  · exact (tf0_usesOnly hD).mono fun i hi => PV_lt hi
  · exact (tf1_usesOnly hD).mono fun i hi => PV_lt hi
  · exact (tf2_usesOnly hD).mono fun i hi => PV_lt hi
  · simp [baseT, tS, UsesOnly]
  · simp [baseT, UsesOnly]

/-- Signs of the base coefficients under `x ↦ −x` (`p̂₁, g₂, f₀, f₁` are odd). -/
@[expose] def sgnB : ℕ → ℝ
  | 1 => -1
  | 5 => -1
  | 8 => -1
  | 9 => -1
  | _ => 1

section parity
variable (x y R r iR iB s a b : ℝ)

/-- Data trees are even in `x`. -/
theorem data_negx {e : Tm} (he : e.UsesOnly DV) :
    e.eval (envR (-x) y R r iR iB s a b) = e.eval (envR x y R r iR iB s a b) :=
  eval_congr e he fun i hi => by rcases hi with rfl | rfl <;> rfl

/-- Data trees are constant along the line. -/
theorem diff_data_zero {e : Tm} (he : e.UsesOnly DV) (ρ : ℕ → ℝ) : (diff dvT e).eval ρ = 0 := by
  rw [eval_diff]
  exact deriv_eq_zero_of_usesOnly e he fun i hi => by
    rcases hi with rfl | rfl <;> simp [dvT, Tm.eval]

/-- Horner trees in `y` with data coefficients are even in `x`. -/
theorem ptree_negx {l : List Tm} (hl : ∀ e ∈ l, e.UsesOnly DV) :
    (ptree l tY).eval (envR (-x) y R r iR iB s a b) =
      (ptree l tY).eval (envR x y R r iR iB s a b) := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [ptree, Tm.eval, ih (fun e' he' => hl e' (by simp [he'])),
      data_negx x y R r iR iB s a b (hl e (by simp))]
    rfl

/-- The `t`-derivative of a Horner tree in `y` is odd in `x`. -/
theorem diff_ptree_negx {l : List Tm} (hl : ∀ e ∈ l, e.UsesOnly DV) :
    (diff dvT (ptree l tY)).eval (envR (-x) y R r iR iB s a b) =
      -(diff dvT (ptree l tY)).eval (envR x y R r iR iB s a b) := by
  induction l with
  | nil => simp [ptree, diff, Tm.eval]
  | cons e l ih =>
    have hl' : ∀ e' ∈ l, e'.UsesOnly DV := fun e' he' => hl e' (by simp [he'])
    simp only [ptree, diff, Tm.eval, ih hl', ptree_negx x y R r iR iB s a b hl',
      diff_data_zero (hl e (by simp))]
    simp only [diff, dvT, tX, tY, Tm.eval, envR]
    ring

/-- `|B|²` is even in `x`. -/
theorem tB2_negx :
    tB2.eval (envR (-x) y R r iR iB s a b) = tB2.eval (envR x y R r iR iB s a b) := by
  simp only [tB2, tBR, tBP, tBZ, tWh, tzh, tX, tY, tR, tr, tiR, tS, Tm.eval, envR]
  ring

end parity

/-- The profile coefficients of admissible data use only `√2, s`. -/
theorem dataA_DV {D : Data} (hD : DataOK D) : (∀ e ∈ D.A0, e.UsesOnly DV) ∧
    (∀ e ∈ D.A1, e.UsesOnly DV) ∧ (∀ e ∈ D.A2, e.UsesOnly DV) :=
  ⟨hD.2.1, hD.2.2.1, hD.2.2.2⟩

/-- **Parity of the base coefficients** under `x ↦ −x`. -/
theorem baseT_negx {D : Data} (hD : DataOK D) (j : ℕ) (x y R r iR iB s a b : ℝ) :
    (baseT D j).eval (envR (-x) y R r iR iB s a b) =
      sgnB j * (baseT D j).eval (envR x y R r iR iB s a b) := by
  obtain ⟨h0, h1, h2⟩ := dataA_DV hD
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j
  · simp only [baseT, sgnB, tp0, tden, tkR, tkP, tkZ, tgtR, tgtZ, tiR3, trate, tX, tY, tR, tr,
      tiR, tiB, tS, Tm.eval, envR]
    ring
  · simp only [baseT, sgnB, tp1, tden, tkR, tkZ, tgtR, tgtZ, tgsR, tgsZ, tWh, tzh, tiR3, trate,
      tX, tY, tR, tr, tiR, tiB, tS, Tm.eval, envR]
    ring
  · simp only [baseT, sgnB, tp2, tden, tgsR, tgsZ, tWh, tzh, tX, tY, tR, tr, tiR, tiB, tS,
      Tm.eval, envR]
    ring
  · have hd : (diff dvT (tf0 D)).eval (envR (-x) y R r iR iB s a b) =
        (diff dvT (tf0 D)).eval (envR x y R r iR iB s a b) := by
      simp only [tf0, diff, Tm.eval, diff_ptree_negx x y R r iR iB s a b h0,
        ptree_negx x y R r iR iB s a b h0]
      simp only [diff, dvT, tX, tY, Tm.eval, envR]
      ring
    have hq : tsq0.eval (envR (-x) y R r iR iB s a b) = tsq0.eval (envR x y R r iR iB s a b) := by
      simp only [tsq0, tcross, tkR, tkP, tkZ, tgtR, tgtZ, tGR, tGZ, tBR, tBP, tBZ, tWh, tzh,
        tiR3, trate, tell, tX, tY, tR, tr, tiR, tiB, tS, Tm.sub, Tm.eval, envR]
      ring
    simp only [baseT, sgnB, Tm.sub, Tm.eval, hd, hq]
    ring
  · simp only [baseT, sgnB, tf1, diff, Tm.eval, diff_ptree_negx x y R r iR iB s a b h1,
      ptree_negx x y R r iR iB s a b h1]
    simp only [diff, dvT, tX, tY, Tm.eval, envR]
    ring
  · simp only [baseT, sgnB, tf2, diff_ptree_negx x y R r iR iB s a b h2]
    ring
  · simp only [baseT, sgnB, td, trate, tY, tr, tiR, tS, Tm.eval, envR]
    ring
  · simp only [baseT, sgnB, Tm.eval, data_negx x y R r iR iB s a b hD.1]
    simp only [tiB, tbeta, tWh, tzh, tX, tY, tr, tiR, tS, Tm.sub, Tm.eval, envR]
    ring
  · simp only [baseT, sgnB, tf0, Tm.eval, ptree_negx x y R r iR iB s a b h0]
    simp only [tX, Tm.eval, envR]
    ring
  · simp only [baseT, sgnB, tf1, Tm.eval, ptree_negx x y R r iR iB s a b h1]
    simp only [tX, Tm.eval, envR]
    ring
  · simp only [baseT, sgnB, tf2, ptree_negx x y R r iR iB s a b h2]
    ring
  · simp [baseT, sgnB, tS, Tm.eval, envR]
  · simp [baseT, sgnB, Tm.eval]

/-- **Parity of the numerator**: flipping the odd base coefficients and `u` leaves it fixed. -/
theorem Nsum_negx (b : ℕ → ℝ) (u : ℝ) :
    ∑ k ∈ Finset.range 7, (etree k).eval (fun j => sgnB j * b j) * (-u) ^ k =
      ∑ k ∈ Finset.range 7, (etree k).eval b * u ^ k := by
  rw [Nsum_eq, Nsum_eq]
  simp only [sgnB]
  ring


/-! ## From the chart to the line -/

theorem RS_eq_sqrt (s t : ℝ) : RS 10 s t = √(100 + 2 * (s * Real.sin t)) := by
  unfold RS uS; congr 1; ring

/-- `tB2` only uses `x, y, R, √2, 1/R, s`. -/
theorem tB2_uses : tB2.UsesOnly fun i => i < 5 ∨ i = 6 := by
  simp [tB2, tBR, tBP, tBZ, tWh, tzh, tX, tY, tR, tr, tiR, tS, UsesOnly]

/-- The chart point of `t` with `cos t ≥ 0`: `x = cos t`. -/
theorem xcc_of (t : ℝ) (h1 : 0 < 1 + Real.cos t) :
    xcc (Real.sin t / (1 + Real.cos t)) = Real.cos t := by
  have hc2 := Real.sin_sq_add_cos_sq t
  unfold xcc kc; rw [div_pow]; field_simp; linear_combination (-1 - Real.cos t) * hc2

/-- The chart point of `t` with `cos t ≥ 0`: `y = sin t`. -/
theorem ycc_of (t : ℝ) (h1 : 0 < 1 + Real.cos t) :
    ycc (Real.sin t / (1 + Real.cos t)) = Real.sin t := by
  have hc2 := Real.sin_sq_add_cos_sq t
  unfold ycc kc; rw [div_pow]; field_simp; linear_combination (-Real.sin t) * hc2

/-- The chart point of `t` with `cos t < 0`: `x = −cos t`. -/
theorem xcc_of' (t : ℝ) (h1 : 0 < 1 - Real.cos t) :
    xcc (Real.sin t / (1 - Real.cos t)) = -Real.cos t := by
  have hc2 := Real.sin_sq_add_cos_sq t
  unfold xcc kc; rw [div_pow]; field_simp; linear_combination (-1 + Real.cos t) * hc2

/-- The chart point of `t` with `cos t < 0`: `y = sin t`. -/
theorem ycc_of' (t : ℝ) (h1 : 0 < 1 - Real.cos t) :
    ycc (Real.sin t / (1 - Real.cos t)) = Real.sin t := by
  have hc2 := Real.sin_sq_add_cos_sq t
  unfold ycc kc; rw [div_pow]; field_simp; linear_combination (-Real.sin t) * hc2

/-- A quotient bounded by its positive denominator lies in `[−1, 1]`. -/
theorem tau_mem {a b : ℝ} (h1 : 0 < b) (hab : |a| ≤ b) : a / b ∈ Icc (-1 : ℝ) 1 := by
  constructor
  · rw [le_div_iff₀ h1]; linarith [neg_abs_le a]
  · rw [div_le_iff₀ h1]; linarith [le_abs_self a]

/-- **From the chart cover to the line**: if `Ψ > 0` on the half circle `τ ∈ [−1, 1]` of the
surface `s`, then the numerator `N̂(t, u)` is positive along the whole field line (the half
`x < 0` by up–down symmetry). -/
theorem Nline_pos_of_psi {D : Data} (hD : DataOK D) {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 25)
    (hpsi : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ σ, 0 < Psi D τ s σ) (t u : ℝ) : 0 < Nline D s t u := by
  have hc2 := Real.sin_sq_add_cos_sq t
  have hsin := Real.abs_sin_le_one t
  have hlt : ∀ i, i < 5 ∨ i = 6 → i < 7 := fun i hi => by omega
  rcases le_or_gt 0 (Real.cos t) with hc | hc
  · have h1 : 0 < 1 + Real.cos t := by linarith
    set τ := Real.sin t / (1 + Real.cos t) with hτdef
    have hx : xcc τ = Real.cos t := xcc_of t h1
    have hy : ycc τ = Real.sin t := ycc_of t h1
    have hτ : τ ∈ Icc (-1 : ℝ) 1 := tau_mem h1 (by linarith)
    have hR : Rcc τ s = RS 10 s t := by rw [Rcc, hy, RS_eq_sqrt]
    have hB : B2c τ s = B2v s t := by
      rw [← line_tB2 hs0 hs t]
      unfold B2c
      apply eval_congr tB2 tB2_uses
      intro i hi
      rcases hi with hi | rfl
      · interval_cases i <;> simp [env0, envL, envP, envR, hx, hy, hR]
      · simp [env0, envL, envP, envR]
    have he : ∀ i, i < 7 → chartEnv τ s i = envL s t i := by
      intro i hi
      interval_cases i <;> simp [chartEnv, envL, envP, envR, hx, hy, hR, hB]
    have hb : bAt D (chartEnv τ s) = bL D s t := by
      funext j; exact eval_congr _ (baseT_usesOnly hD j) he
    have := hpsi τ hτ u
    simp only [Psi, ecE, hb] at this
    exact this
  · have h1 : 0 < 1 - Real.cos t := by linarith
    set τ := Real.sin t / (1 - Real.cos t) with hτdef
    have hx : xcc τ = -Real.cos t := xcc_of' t h1
    have hy : ycc τ = Real.sin t := ycc_of' t h1
    have hτ : τ ∈ Icc (-1 : ℝ) 1 := tau_mem h1 (by linarith)
    have hR : Rcc τ s = RS 10 s t := by rw [Rcc, hy, RS_eq_sqrt]
    have hB : B2c τ s = B2v s t := by
      rw [← line_tB2 hs0 hs t]
      unfold B2c
      have e0 : env0 τ s = envR (-Real.cos t) (Real.sin t) (RS 10 s t) √2 (RS 10 s t)⁻¹ 0 s τ
          (kc τ) := by
        unfold env0; rw [hx, hy, hR]
      rw [e0, tB2_negx]
      apply eval_congr tB2 tB2_uses
      intro i hi
      rcases hi with hi | rfl
      · interval_cases i <;> simp [envL, envP, envR]
      · simp [envL, envP, envR]
    have he : chartEnv τ s = envR (-Real.cos t) (Real.sin t) (RS 10 s t) √2 (RS 10 s t)⁻¹
        (B2v s t)⁻¹ s τ (kc τ) := by
      unfold chartEnv; rw [hx, hy, hR, hB]
    have hb : bAt D (chartEnv τ s) = fun j => sgnB j * bL D s t j := by
      funext j
      simp only [bAt, he, baseT_negx hD, bL]
      congr 1
      apply eval_congr _ (baseT_usesOnly hD j)
      intro i hi
      interval_cases i <;> simp [envL, envP, envR]
    have := hpsi τ hτ (-u)
    simp only [Psi, ecE, hb] at this
    rw [Nsum_negx] at this
    exact this

end PlasmaLean.Design.SolovevBallooning
