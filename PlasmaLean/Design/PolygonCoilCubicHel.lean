/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCubicGeom
public import PlasmaLean.Design.PolygonCoilHel

/-!
# Cubic interpolation of the helical target field on the faces

Crude (but sufficient) fourth-derivative bounds for `⟨n, hel⟩`, `‖n‖ ≤ 1`, along the grid
directions of the cubic certificate (`hel` contributes `< 10⁻³` of the remainder):

* `hel_t_interp`: along the circles `t ↦ circ ρ ζ t` (`ρ ∈ [17/20, 23/20]`, `|ζ| ≤ 3/25`,
  `|t| ≤ 1/2`): `|g⁗| ≤ 2000`. Here `g = H ∘ φ` with `φ = π/2 + 2 arctan t`, `H` a trigonometric
  polynomial of degree `3` with coefficients `≤ 1/10`, and Faà di Bruno with
  `|φ'| ≤ 2`, `|φ''| ≤ 2`, `|φ'''| ≤ 4`, `|φ⁗| ≤ 24`;
* `hel_rho_interp4`: along `ρ` (plane faces, `ρ ∈ [17/20, 23/20]`, `|ζ| ≤ 3/25`):
  `|g⁗| ≤ 1000` (a Laurent polynomial in `ρ`);
* `hel_zeta_interp4`: along `ζ` (cylinder faces) the error vanishes (a cubic in `ζ`).
-/

public section
noncomputable section

namespace PlasmaLean.Design.PolygonCoil
open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator
  PlasmaLean.Design.RationalStellarator.Coils PlasmaLean.Design.RationalStellarator.CoilsTF Set Real
open scoped RealInnerProductSpace

/-- The circle is the polar point at angle `φ(t)`. -/
theorem circ_eq_polar (ρ ζ t : ℝ) : circ ρ ζ t = polarPt ρ ζ (phiT t) := by
  rw [polarPt_eq, cos_phiT, sin_phiT]; rfl

/-! ## Coefficient bounds -/

/-- The six coefficients are at most `1/8` in absolute value for `ρ ∈ [17/20, 23/20]`,
`|ζ| ≤ 3/25`. -/
theorem coef_bounds {ρ ζ : ℝ} (h1 : 17 / 20 ≤ ρ) (h2 : ρ ≤ 23 / 20) (hζ : |ζ| ≤ 3 / 25) :
    |cA ρ| ≤ 1 / 8 ∧ |cB ρ ζ| ≤ 1 / 8 ∧ |cG ρ ζ| ≤ 1 / 8 ∧ |cD ρ ζ| ≤ 1 / 8 ∧
      |cE ρ ζ| ≤ 1 / 8 ∧ |cF ρ ζ| ≤ 1 / 8 := by
  have hρ : 0 < ρ := by linarith
  obtain ⟨hz1, hz2⟩ := abs_le.mp hζ
  have hz2' : ζ ^ 2 ≤ 9 / 625 := by nlinarith
  have hr3 : (17 / 20 : ℝ) ^ 3 ≤ ρ ^ 3 := pow_le_pow_left₀ (by norm_num) h1 3
  have hr2 : (17 / 20 : ℝ) ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
  have hr2' : ρ ^ 2 ≤ (23 / 20 : ℝ) ^ 2 := pow_le_pow_left₀ hρ.le h2 2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold cA; rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 8 * ρ), div_le_iff₀ (by
      positivity)]
    rw [abs_le]; constructor <;> nlinarith
  · unfold cB; rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 8 * ρ), div_le_iff₀ (by
      positivity),
      abs_mul]
    have : |3 - ρ ^ 2| ≤ 3 := by rw [abs_le]; constructor <;> nlinarith
    nlinarith [abs_nonneg ζ, abs_nonneg (3 - ρ ^ 2)]
  · unfold cG; rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 8 * ρ ^ 3),
      div_le_iff₀ (by positivity)]
    rw [abs_le]; constructor <;> nlinarith
  · unfold cD; rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 8 * ρ ^ 3),
      div_le_iff₀ (by positivity), abs_mul]
    have : |5 - 3 * ρ ^ 2 - 4 * ζ ^ 2| ≤ 3 := by rw [abs_le]; constructor <;> nlinarith
    nlinarith [abs_nonneg ζ, abs_nonneg (5 - 3 * ρ ^ 2 - 4 * ζ ^ 2)]
  · unfold cE; rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 16 * ρ ^ 2),
      div_le_iff₀ (by positivity)]
    have hr4 : ρ ^ 4 = ρ ^ 2 * ρ ^ 2 := by ring
    rw [abs_le]; constructor <;> nlinarith
  · unfold cF; rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * ρ ^ 2), abs_neg,
      div_le_iff₀ (by positivity)]
    nlinarith

/-! ## Along the circles -/

/-- The trigonometric polynomial of `⟨n, helP⟩` with general coefficients and its derivative. -/
@[expose] def trigH (n0 n1 n2 A B G D E F φ : ℝ) : ℝ :=
  n0 * (tp A B 1 φ + tp G D 3 φ) + n1 * (tp B (-A) 1 φ + tp (-D) G 3 φ) + n2 * tp F E 2 φ

/-- Derivative of the trigonometric polynomial `trigH`. -/
theorem hasDerivAt_trigH (n0 n1 n2 A B G D E F φ : ℝ) :
    HasDerivAt (trigH n0 n1 n2 A B G D E F) (trigH n0 n1 n2 B (-A) (3 * D) (-(3 * G)) (-(2 * F))
      (2 * E) φ) φ := by
  have := (((hasDerivAt_tp A B 1 φ).add (hasDerivAt_tp G D 3 φ)).const_mul n0).add
    (((hasDerivAt_tp B (-A) 1 φ).add (hasDerivAt_tp (-D) G 3 φ)).const_mul n1) |>.add
    ((hasDerivAt_tp F E 2 φ).const_mul n2)
  unfold trigH
  convert this using 1
  simp only [tp]; ring

/-- `|α cos kφ + β sin kφ| ≤ |α| + |β|`. -/
theorem abs_tp_le (α β k φ : ℝ) : |tp α β k φ| ≤ |α| + |β| := by
  unfold tp
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
  · exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)
  · exact mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _)

/-- Crude bound on `trigH` for unit-bounded `n`. -/
theorem abs_trigH_le {n0 n1 n2 : ℝ} (h0 : |n0| ≤ 1) (h1 : |n1| ≤ 1) (h2 : |n2| ≤ 1)
    (A B G D E F φ : ℝ) :
    |trigH n0 n1 n2 A B G D E F φ| ≤ 2 * (|A| + |B|) + 2 * (|G| + |D|) + (|E| + |F|) := by
  unfold trigH
  have t1 := abs_tp_le A B 1 φ
  have t2 := abs_tp_le G D 3 φ
  have t3 := abs_tp_le B (-A) 1 φ
  have t4 := abs_tp_le (-D) G 3 φ
  have t5 := abs_tp_le F E 2 φ
  rw [abs_neg] at t3 t4
  have a1 : |n0 * (tp A B 1 φ + tp G D 3 φ)| ≤ (|A| + |B|) + (|G| + |D|) := by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) h0).trans ((abs_add_le _ _).trans (add_le_add t1
        t2))
  have a2 : |n1 * (tp B (-A) 1 φ + tp (-D) G 3 φ)| ≤ (|A| + |B|) + (|G| + |D|) := by
    rw [abs_mul]
    refine (mul_le_of_le_one_left (abs_nonneg _) h1).trans ((abs_add_le _ _).trans ?_)
    linarith
  have a3 : |n2 * tp F E 2 φ| ≤ |E| + |F| := by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) h2).trans (by linarith)
  calc _ ≤ |n0 * (tp A B 1 φ + tp G D 3 φ)| + |n1 * (tp B (-A) 1 φ + tp (-D) G 3 φ)| +
        |n2 * tp F E 2 φ| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by linarith

/-- The derivatives of the angle `φ(t) = π/2 + 2 arctan t`: `φ' = 1 + B₀`, `φ'' = B₁`,
`φ''' = B₂`, `φ⁗ = B₃`. -/
theorem hasDerivAt_phiT (t : ℝ) : HasDerivAt phiT (1 + cB0 t) t := by
  have := ((hasDerivAt_arctan t).const_mul 2).const_add (π / 2)
  unfold phiT
  refine this.congr_deriv ?_
  unfold cB0
  have h0 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  field_simp; ring

/-- Bounds on the derivatives of `φ(t)` for `|t| ≤ 1/2`. -/
theorem phi_derivs_bound {s : ℝ} (hs1 : |s| ≤ 1 / 2) :
    |1 + cB0 s| ≤ 2 ∧ |cB1 s| ≤ 2 ∧ |cB2 s| ≤ 4 ∧ |cB3 s| ≤ 24 := by
  have hs2 : s ^ 2 ≤ 1 / 4 := by nlinarith [abs_nonneg s, sq_abs s]
  have h0 : (0 : ℝ) < 1 + s ^ 2 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold cB0
    rw [abs_le]; constructor
    · have : 0 ≤ (1 - s ^ 2) / (1 + s ^ 2) + 1 := by
        rw [div_add_one h0.ne']; apply div_nonneg <;> nlinarith
      linarith
    · have : (1 - s ^ 2) / (1 + s ^ 2) ≤ 1 := by rw [div_le_one h0]; nlinarith
      linarith
  · unfold cB1; rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (1 + s ^ 2) ^ 2),
      div_le_iff₀ (by positivity), abs_mul]
    have : (1 : ℝ) ≤ (1 + s ^ 2) ^ 2 := one_le_pow₀ (by nlinarith)
    norm_num; nlinarith [abs_nonneg s]
  · unfold cB2; rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (1 + s ^ 2) ^ 3),
      div_le_iff₀ (by positivity), abs_mul]
    have : (1 : ℝ) ≤ (1 + s ^ 2) ^ 3 := one_le_pow₀ (by nlinarith)
    have : |1 - 3 * s ^ 2| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith
    norm_num; nlinarith [abs_nonneg (1 - 3 * s ^ 2)]
  · unfold cB3; rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (1 + s ^ 2) ^ 4),
      div_le_iff₀ (by positivity), abs_mul]
    have : (1 : ℝ) ≤ (1 + s ^ 2) ^ 4 := one_le_pow₀ (by nlinarith)
    have : |4 * s - 4 * s ^ 3| ≤ 2 := by
      have e : 4 * s - 4 * s ^ 3 = 4 * s * (1 - s ^ 2) := by ring
      rw [e, abs_mul, abs_mul, abs_of_nonneg (by nlinarith : (0:ℝ) ≤ 1 - s ^ 2)]
      norm_num; nlinarith [abs_nonneg s]
    norm_num; nlinarith [abs_nonneg (4 * s - 4 * s ^ 3)]

/-- The Faà di Bruno combination for the fourth derivative of `H ∘ φ`. -/
theorem faa4_bound {H1 H2 H3 H4 P1 P2 P3 P4 : ℝ} (b4 : |H4| ≤ 45) (b3 : |H3| ≤ 16) (b2 : |H2| ≤ 6)
    (b1 : |H1| ≤ 5 / 2) (q1 : |P1| ≤ 2) (q2 : |P2| ≤ 2) (q3 : |P3| ≤ 4) (q4 : |P4| ≤ 24) :
    |H4 * P1 ^ 4 + 6 * H3 * P1 ^ 2 * P2 + H2 * (4 * P1 * P3 + 3 * P2 ^ 2) + H1 * P4| ≤ 2000 := by
  have u1 : |P1| ^ 4 ≤ 16 := by
    have := pow_le_pow_left₀ (abs_nonneg _) q1 4; norm_num at this; linarith
  have u2 : |P1| ^ 2 ≤ 4 := by nlinarith [abs_nonneg P1]
  have u3 : |P2| ^ 2 ≤ 4 := by nlinarith [abs_nonneg P2]
  have v1 : |H4 * P1 ^ 4| ≤ 45 * 16 := by
    rw [abs_mul, abs_pow]; exact mul_le_mul b4 u1 (by positivity) (by norm_num)
  have v2 : |6 * H3 * P1 ^ 2 * P2| ≤ 6 * 16 * 4 * 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_pos (by norm_num : (0:ℝ) < 6)]
    have := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left b3 (by norm_num : (0:ℝ) ≤ 6)) u2
      (by positivity) (by positivity)) q2 (abs_nonneg _) (by positivity)
    linarith
  have v3 : |H2 * (4 * P1 * P3 + 3 * P2 ^ 2)| ≤ 6 * (4 * 2 * 4 + 3 * 4) := by
    rw [abs_mul]
    apply mul_le_mul b2 _ (abs_nonneg _) (by norm_num)
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_pos (by norm_num : (0:ℝ) < 4),
      abs_of_pos (by norm_num : (0:ℝ) < 3)]
    have := mul_le_mul (mul_le_mul_of_nonneg_left q1 (by norm_num : (0:ℝ) ≤ 4)) q3 (abs_nonneg _)
      (by positivity)
    linarith
  have v4 : |H1 * P4| ≤ 5 / 2 * 24 := by
    rw [abs_mul]; exact mul_le_mul b1 q4 (abs_nonneg _) (by norm_num)
  have := abs_add_le (H4 * P1 ^ 4 + 6 * H3 * P1 ^ 2 * P2 + H2 * (4 * P1 * P3 + 3 * P2 ^ 2)) (H1 *
      P4)
  have := abs_add_le (H4 * P1 ^ 4 + 6 * H3 * P1 ^ 2 * P2) (H2 * (4 * P1 * P3 + 3 * P2 ^ 2))
  have := abs_add_le (H4 * P1 ^ 4) (6 * H3 * P1 ^ 2 * P2)
  linarith

/-- **Fourth derivative of `⟨n, hel⟩` along the circles.** -/
theorem hel_t_interp {n : Space} (hn : ‖n‖ ≤ 1) {ρ ζ : ℝ} (h1 : 17 / 20 ≤ ρ) (h2 : ρ ≤ 23 / 20)
    (hζ : |ζ| ≤ 3 / 25) {t0 t1 t2 t3 t : ℝ} (h01 : t0 < t1) (h12 : t1 < t2) (h23 : t2 < t3)
    (hlo : -1 / 2 ≤ t0) (hhi : t3 ≤ 1 / 2) (ht : t ∈ Icc t1 t2) :
    |⟪n, hel (circ ρ ζ t)⟫ - newt t0 t1 t2 t3 ⟪n, hel (circ ρ ζ t0)⟫ ⟪n, hel (circ ρ ζ t1)⟫
      ⟪n, hel (circ ρ ζ t2)⟫ ⟪n, hel (circ ρ ζ t3)⟫ t| ≤ 2000 * |omega4 t0 t1 t2 t3 t| / 24 := by
  have hρ : 0 < ρ := by linarith
  have hn3 := coords_sq_le hn
  have hn0 : |n 0| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [sq_nonneg (n 1), sq_nonneg (n
      2)]
  have hn1 : |n 1| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [sq_nonneg (n 0), sq_nonneg (n
      2)]
  have hn2 : |n 2| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [sq_nonneg (n 0), sq_nonneg (n
      1)]
  obtain ⟨bA, bB, bG, bD, bE, bF⟩ := coef_bounds h1 h2 hζ
  set A := cA ρ; set B := cB ρ ζ; set G := cG ρ ζ; set D := cD ρ ζ; set E := cE ρ ζ
  set F := cF ρ ζ
  -- the coefficient sequences of `H, H', H'', H''', H⁗`
  set T := trigH (n 0) (n 1) (n 2)
  have hH : ∀ s, ⟪n, hel (circ ρ ζ s)⟫ = T A B G D E F (phiT s) := by
    intro s; rw [circ_eq_polar, hel_polar hρ, inner_helP_tp]; rfl
  simp only [hH]
  -- derivatives of `H`
  have dH : ∀ (a b g d e f φ : ℝ), HasDerivAt (T a b g d e f)
      (T b (-a) (3 * d) (-(3 * g)) (-(2 * f)) (2 * e) φ) φ := fun a b g d e f φ =>
    hasDerivAt_trigH _ _ _ a b g d e f φ
  -- the chain for `g = H ∘ φ`
  set p1 : ℝ → ℝ := fun s => 1 + cB0 s
  have dp1 : ∀ s, HasDerivAt p1 (cB1 s) s := fun s => (hasDerivAt_cB0 s).const_add 1
  set H1 := fun φ => T B (-A) (3 * D) (-(3 * G)) (-(2 * F)) (2 * E) φ
  set H2 := fun φ => T (-A) (-B) (-(9 * G)) (-(9 * D)) (-(4 * E)) (-(4 * F)) φ
  set H3 := fun φ => T (-B) A (-(27 * D)) (27 * G) (8 * F) (-(8 * E)) φ
  set H4 := fun φ => T A B (81 * G) (81 * D) (16 * E) (16 * F) φ
  have e1 : ∀ φ, T B (-A) (3 * D) (-(3 * G)) (-(2 * F)) (2 * E) φ = H1 φ := fun _ => rfl
  have dH0 : ∀ φ, HasDerivAt (T A B G D E F) (H1 φ) φ := fun φ => dH A B G D E F φ
  have dH1 : ∀ φ, HasDerivAt H1 (H2 φ) φ := by
    intro φ
    have := dH B (-A) (3 * D) (-(3 * G)) (-(2 * F)) (2 * E) φ
    convert this using 2 <;> ring
  have dH2 : ∀ φ, HasDerivAt H2 (H3 φ) φ := by
    intro φ
    have := dH (-A) (-B) (-(9 * G)) (-(9 * D)) (-(4 * E)) (-(4 * F)) φ
    convert this using 2 <;> ring
  have dH3 : ∀ φ, HasDerivAt H3 (H4 φ) φ := by
    intro φ
    have := dH (-B) A (-(27 * D)) (27 * G) (8 * F) (-(8 * E)) φ
    convert this using 2 <;> ring
  set g1 := fun s => H1 (phiT s) * p1 s
  set g2 := fun s => H2 (phiT s) * p1 s ^ 2 + H1 (phiT s) * cB1 s
  set g3 := fun s => H3 (phiT s) * p1 s ^ 3 + 3 * H2 (phiT s) * p1 s * cB1 s + H1 (phiT s) * cB2 s
  set g4 := fun s => H4 (phiT s) * p1 s ^ 4 + 6 * H3 (phiT s) * p1 s ^ 2 * cB1 s +
    H2 (phiT s) * (4 * p1 s * cB2 s + 3 * cB1 s ^ 2) + H1 (phiT s) * cB3 s
  have dphi : ∀ s, HasDerivAt phiT (p1 s) s := hasDerivAt_phiT
  have c0 : ∀ s, HasDerivAt (fun s => T A B G D E F (phiT s)) (g1 s) s := fun s =>
    (dH0 (phiT s)).comp s (dphi s)
  have dHc : ∀ (Hf Hf' : ℝ → ℝ), (∀ φ, HasDerivAt Hf (Hf' φ) φ) → ∀ s,
      HasDerivAt (fun s => Hf (phiT s)) (Hf' (phiT s) * p1 s) s := fun Hf Hf' h s =>
    (h (phiT s)).comp s (dphi s)
  have dpow : ∀ (k : ℕ) s, HasDerivAt (fun s => p1 s ^ k) (k * p1 s ^ (k - 1) * cB1 s) s :=
    fun k s => (dp1 s).pow k
  have c1 : ∀ s, HasDerivAt g1 (g2 s) s := by
    intro s
    have := HasDerivAt.fun_mul (dHc H1 H2 dH1 s) (dp1 s)
    refine this.congr_deriv ?_
    simp only [g2]; ring
  have c2 : ∀ s, HasDerivAt g2 (g3 s) s := by
    intro s
    have a := HasDerivAt.fun_mul (dHc H2 H3 dH2 s) (dpow 2 s)
    have b := HasDerivAt.fun_mul (dHc H1 H2 dH1 s) (hasDerivAt_cB1 s)
    have := HasDerivAt.fun_add a b
    refine this.congr_deriv ?_
    simp only [g3]; push_cast; ring
  have c3 : ∀ s, HasDerivAt g3 (g4 s) s := by
    intro s
    have a := HasDerivAt.fun_mul (dHc H3 H4 dH3 s) (dpow 3 s)
    have b := HasDerivAt.fun_mul (HasDerivAt.fun_mul ((dHc H2 H3 dH2 s).const_mul 3) (dp1 s))
      (hasDerivAt_cB1 s)
    have c := HasDerivAt.fun_mul (dHc H1 H2 dH1 s) (hasDerivAt_cB2 s)
    have := HasDerivAt.fun_add (HasDerivAt.fun_add a b) c
    refine this.congr_deriv ?_
    simp only [g4]; push_cast; ring
  -- bounds
  have hM : ∀ s ∈ Icc t0 t3, |g4 s| ≤ 2000 := by
    intro s hs
    have hs1 : |s| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
    obtain ⟨q1, q2, q3, q4⟩ := phi_derivs_bound hs1
    have hb : ∀ (a b g d e f : ℝ) (φ : ℝ), |T a b g d e f φ| ≤
        2 * (|a| + |b|) + 2 * (|g| + |d|) + (|e| + |f|) := fun a b g d e f φ =>
      abs_trigH_le hn0 hn1 hn2 a b g d e f φ
    have b4 : |H4 (phiT s)| ≤ 45 := by
      refine (hb _ _ _ _ _ _ _).trans ?_
      simp only [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 81),
        abs_of_pos (by norm_num : (0:ℝ) < 16)]
      linarith
    have b3 : |H3 (phiT s)| ≤ 16 := by
      refine (hb _ _ _ _ _ _ _).trans ?_
      simp only [abs_neg, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 27),
        abs_of_pos (by norm_num : (0:ℝ) < 8)]
      linarith
    have b2 : |H2 (phiT s)| ≤ 6 := by
      refine (hb _ _ _ _ _ _ _).trans ?_
      simp only [abs_neg, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 9),
        abs_of_pos (by norm_num : (0:ℝ) < 4)]
      linarith
    have b1 : |H1 (phiT s)| ≤ 5 / 2 := by
      refine (hb _ _ _ _ _ _ _).trans ?_
      simp only [abs_neg, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3),
        abs_of_pos (by norm_num : (0:ℝ) < 2)]
      linarith
    exact faa4_bound b4 b3 b2 b1 q1 q2 q3 q4
  exact newt_interp_bound h01 h12 h23 ht (fun s _ => c0 s) (fun s _ => c1 s) (fun s _ => c2 s)
    (fun s _ => c3 s) hM

/-! ## Along `ζ` (cylinder faces) and along `ρ` (plane faces) -/

/-- **Along `ζ` the interpolation error of `⟨n, hel⟩` vanishes** (a cubic polynomial in `ζ`). -/
theorem hel_zeta_interp4 (n : Space) {ρ : ℝ} (hρ : 0 < ρ) (t : ℝ) {z0 z1 z2 z3 z : ℝ}
    (h01 : z0 < z1) (h12 : z1 < z2) (h23 : z2 < z3) (hz : z ∈ Icc z1 z2) :
    |⟪n, hel (circ ρ z t)⟫ - newt z0 z1 z2 z3 ⟪n, hel (circ ρ z0 t)⟫ ⟪n, hel (circ ρ z1 t)⟫
      ⟪n, hel (circ ρ z2 t)⟫ ⟪n, hel (circ ρ z3 t)⟫ z| ≤ 1000 * |omega4 z0 z1 z2 z3 z| / 24 := by
  set c1 := cos (phiT t); set s1 := sin (phiT t); set c3 := cos (3 * phiT t)
  set s3 := sin (3 * phiT t); set c2 := cos (2 * phiT t); set s2 := sin (2 * phiT t)
  set k0 := n 0 * ((ρ ^ 2 - 1) / (8 * ρ) * c1 + (ρ ^ 2 - 1) / (8 * ρ ^ 3) * c3) +
    n 1 * (-((ρ ^ 2 - 1) / (8 * ρ)) * s1 + (ρ ^ 2 - 1) / (8 * ρ ^ 3) * s3) +
    n 2 * ((6 * ρ ^ 2 - ρ ^ 4 - 5) / (16 * ρ ^ 2) * s2)
  set k1 := n 0 * ((3 - ρ ^ 2) / (8 * ρ) * s1 + (5 - 3 * ρ ^ 2) / (8 * ρ ^ 3) * s3) +
    n 1 * ((3 - ρ ^ 2) / (8 * ρ) * c1 - (5 - 3 * ρ ^ 2) / (8 * ρ ^ 3) * c3) +
    n 2 * (-1 / (2 * ρ ^ 2) * c2)
  set k2 := n 0 * (1 / (2 * ρ ^ 3) * c3) + n 1 * (1 / (2 * ρ ^ 3) * s3) + n 2 * (3 / (4 * ρ ^ 2) *
      s2)
  set k3 := n 0 * (-1 / (2 * ρ ^ 3) * s3) - n 1 * (-1 / (2 * ρ ^ 3) * c3)
  have hpoly : ∀ ζ, ⟪n, hel (circ ρ ζ t)⟫ = k0 + k1 * ζ + k2 * ζ ^ 2 + k3 * ζ ^ 3 + 0 * ζ ^ 4 := by
    intro ζ
    rw [circ_eq_polar, hel_polar hρ, inner_helP]
    simp only [cA, cB, cG, cD, cE, cF, k0, k1, k2, k3, c1, s1, c2, s2, c3, s3]
    field_simp
    ring
  simp only [hpoly]
  have h := newt_interp_bound (g := fun ζ => k0 + k1 * ζ + k2 * ζ ^ 2 + k3 * ζ ^ 3 + 0 * ζ ^ 4)
    (g1 := fun ζ => k1 + 2 * k2 * ζ + 3 * k3 * ζ ^ 2 + 4 * 0 * ζ ^ 3)
    (g2 := fun ζ => 2 * k2 + 2 * (3 * k3) * ζ + 3 * (4 * 0) * ζ ^ 2 + 4 * 0 * ζ ^ 3)
    (g3 := fun ζ => 2 * (3 * k3) + 2 * (3 * (4 * 0)) * ζ + 3 * 0 * ζ ^ 2 + 4 * 0 * ζ ^ 3)
    (g4 := fun ζ => 2 * (3 * (4 * 0)) + 2 * 0 * ζ + 3 * 0 * ζ ^ 2 + 4 * 0 * ζ ^ 3) (M := 1000)
    h01 h12 h23 hz (fun y _ => hasDerivAt_quartic _ _ _ _ _ y) (fun y _ => by
      have := hasDerivAt_quartic k1 (2 * k2) (3 * k3) (4 * 0) 0 y
      simp only [zero_mul, add_zero, mul_zero] at this ⊢; exact this)
    (fun y _ => by
      have := hasDerivAt_quartic (2 * k2) (2 * (3 * k3)) (3 * (4 * 0)) (4 * 0) 0 y
      simp only [zero_mul, add_zero, mul_zero] at this ⊢; exact this)
    (fun y _ => by
      have := hasDerivAt_quartic (2 * (3 * k3)) (2 * (3 * (4 * 0))) (3 * 0) (4 * 0) 0 y
      simp only [zero_mul, add_zero, mul_zero] at this ⊢; exact this)
    (fun y _ => by simp)
  exact h

/-- Fourth derivative of `ρ⁻ʲ`-terms: the Laurent polynomial and its derivatives. -/
theorem laur_chain {l2 l1 l0 lm1 lm2 lm3 y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (laur l2 l1 l0 lm1 lm2 lm3)
      (2 * l2 * y + l1 - lm1 * (y ^ 2)⁻¹ - 2 * lm2 * (y ^ 3)⁻¹ - 3 * lm3 * (y ^ 4)⁻¹) y ∧
    HasDerivAt (fun y => 2 * l2 * y + l1 - lm1 * (y ^ 2)⁻¹ - 2 * lm2 * (y ^ 3)⁻¹ -
      3 * lm3 * (y ^ 4)⁻¹)
      (2 * l2 + 2 * lm1 * (y ^ 3)⁻¹ + 6 * lm2 * (y ^ 4)⁻¹ + 12 * lm3 * (y ^ 5)⁻¹) y ∧
    HasDerivAt (fun y => 2 * l2 + 2 * lm1 * (y ^ 3)⁻¹ + 6 * lm2 * (y ^ 4)⁻¹ + 12 * lm3 * (y ^ 5)⁻¹)
      (-6 * lm1 * (y ^ 4)⁻¹ - 24 * lm2 * (y ^ 5)⁻¹ - 60 * lm3 * (y ^ 6)⁻¹) y ∧
    HasDerivAt (fun y => -6 * lm1 * (y ^ 4)⁻¹ - 24 * lm2 * (y ^ 5)⁻¹ - 60 * lm3 * (y ^ 6)⁻¹)
      (24 * lm1 * (y ^ 5)⁻¹ + 120 * lm2 * (y ^ 6)⁻¹ + 360 * lm3 * (y ^ 7)⁻¹) y := by
  have i0 := hasDerivAt_inv_pow' hy 0
  have i1 := hasDerivAt_inv_pow' hy 1
  have i2 := hasDerivAt_inv_pow' hy 2
  have i3 := hasDerivAt_inv_pow' hy 3
  have i4 := hasDerivAt_inv_pow' hy 4
  have i5 := hasDerivAt_inv_pow' hy 5
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := HasDerivAt.fun_add (HasDerivAt.fun_add (HasDerivAt.fun_add (HasDerivAt.fun_add
      (HasDerivAt.fun_add ((hasDerivAt_pow 2 y).const_mul l2) ((hasDerivAt_id' y).const_mul l1))
      (hasDerivAt_const y l0)) (i0.const_mul lm1)) (i1.const_mul lm2)) (i2.const_mul lm3)
    unfold laur
    refine this.congr_deriv ?_
    push_cast; ring
  · have := HasDerivAt.fun_sub (HasDerivAt.fun_sub (HasDerivAt.fun_sub (HasDerivAt.fun_add
      ((hasDerivAt_id' y).const_mul (2 * l2)) (hasDerivAt_const y l1)) (i1.const_mul lm1))
      (i2.const_mul (2 * lm2))) (i3.const_mul (3 * lm3))
    refine this.congr_deriv ?_
    push_cast; ring
  · have := HasDerivAt.fun_add (HasDerivAt.fun_add (HasDerivAt.fun_add (hasDerivAt_const y (2 * l2))
      (i2.const_mul (2 * lm1))) (i3.const_mul (6 * lm2))) (i4.const_mul (12 * lm3))
    refine this.congr_deriv ?_
    push_cast; ring
  · have := HasDerivAt.fun_sub (HasDerivAt.fun_sub (i3.const_mul (-6 * lm1)) (i4.const_mul (24 *
      lm2)))
      (i5.const_mul (60 * lm3))
    refine this.congr_deriv ?_
    push_cast; ring

/-- `|ax + by + cz + dw| ≤ |a||x| + |b||y| + |c||z| + |d||w|`. -/
theorem abs_lin4 (a b c d x y z w : ℝ) :
    |a * x + b * y + c * z + d * w| ≤ |a| * |x| + |b| * |y| + |c| * |z| + |d| * |w| := by
  rw [← abs_mul, ← abs_mul, ← abs_mul, ← abs_mul]
  exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _)
    le_rfl)) le_rfl)

/-- Bounds on the Laurent coefficients of `⟨n, hel⟩` along `ρ`. -/
theorem lm_bounds {n0 n1 n2 ζ c1 s1 c2 s2 c3 s3 : ℝ} (hn0 : |n0| ≤ 1) (hn1 : |n1| ≤ 1)
    (hn2 : |n2| ≤ 1) (hζ : |ζ| ≤ 3 / 25) (hc1 : |c1| ≤ 1) (hs1 : |s1| ≤ 1) (hc2 : |c2| ≤ 1)
    (hs2 : |s2| ≤ 1) (hc3 : |c3| ≤ 1) (hs3 : |s3| ≤ 1) :
    |n0 * (-(c1 / 8) + 3 * ζ * s1 / 8 + c3 / 8 - 3 * ζ * s3 / 8) +
      n1 * (s1 / 8 + 3 * ζ * c1 / 8 + s3 / 8 + 3 * ζ * c3 / 8)| ≤ 1 ∧
    |n2 * ((12 * ζ ^ 2 - 5) / 16 * s2 - ζ / 2 * c2)| ≤ 1 / 2 ∧
    |n0 * ((4 * ζ ^ 2 - 1) / 8 * c3 + ζ * (5 - 4 * ζ ^ 2) / 8 * s3) +
      n1 * ((4 * ζ ^ 2 - 1) / 8 * s3 - ζ * (5 - 4 * ζ ^ 2) / 8 * c3)| ≤ 1 / 2 := by
  have hz0 := abs_nonneg ζ
  obtain ⟨hz1, hz2⟩ := abs_le.mp hζ
  have hz2' : ζ ^ 2 ≤ 9 / 625 := by nlinarith
  have k1 : |3 * ζ / 8| ≤ 9 / 200 := by rw [abs_div, abs_mul]; norm_num; linarith
  have k2 : |(4 * ζ ^ 2 - 1) / 8| ≤ 1 / 8 := by rw [abs_le]; constructor <;> nlinarith
  have k3 : |ζ * (5 - 4 * ζ ^ 2) / 8| ≤ 3 / 40 := by
    rw [abs_div, abs_mul]; norm_num
    have : |5 - 4 * ζ ^ 2| ≤ 5 := by rw [abs_le]; constructor <;> nlinarith
    nlinarith [abs_nonneg (5 - 4 * ζ ^ 2)]
  have k4 : |(12 * ζ ^ 2 - 5) / 16| ≤ 5 / 16 := by rw [abs_le]; constructor <;> nlinarith
  have k5 : |ζ / 2| ≤ 3 / 50 := by rw [abs_div]; norm_num; linarith
  have hm : ∀ {u v U : ℝ}, |u| ≤ 1 → |v| ≤ U → |u * v| ≤ U := fun hu hv => by
    rw [abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) hu).trans hv
  refine ⟨?_, ?_, ?_⟩
  · have e1 : -(c1 / 8) + 3 * ζ * s1 / 8 + c3 / 8 - 3 * ζ * s3 / 8 =
        (-1 / 8) * c1 + (3 * ζ / 8) * s1 + (1 / 8) * c3 + (-(3 * ζ / 8)) * s3 := by ring
    have e2 : s1 / 8 + 3 * ζ * c1 / 8 + s3 / 8 + 3 * ζ * c3 / 8 =
        (1 / 8) * s1 + (3 * ζ / 8) * c1 + (1 / 8) * s3 + (3 * ζ / 8) * c3 := by ring
    have b1 := abs_lin4 (-1 / 8) (3 * ζ / 8) (1 / 8) (-(3 * ζ / 8)) c1 s1 c3 s3
    have b2 := abs_lin4 (1 / 8) (3 * ζ / 8) (1 / 8) (3 * ζ / 8) s1 c1 s3 c3
    rw [abs_neg] at b1
    have f1 : |-(c1 / 8) + 3 * ζ * s1 / 8 + c3 / 8 - 3 * ζ * s3 / 8| ≤ 1 / 2 := by
      rw [e1]; refine b1.trans ?_
      have := mul_le_mul k1 hs1 (abs_nonneg _) (by norm_num)
      have := mul_le_mul k1 hs3 (abs_nonneg _) (by norm_num)
      norm_num; nlinarith [abs_nonneg c1, abs_nonneg c3]
    have f2 : |s1 / 8 + 3 * ζ * c1 / 8 + s3 / 8 + 3 * ζ * c3 / 8| ≤ 1 / 2 := by
      rw [e2]; refine b2.trans ?_
      have := mul_le_mul k1 hc1 (abs_nonneg _) (by norm_num)
      have := mul_le_mul k1 hc3 (abs_nonneg _) (by norm_num)
      norm_num; nlinarith [abs_nonneg s1, abs_nonneg s3]
    refine (abs_add_le _ _).trans ?_
    have := hm hn0 f1
    have := hm hn1 f2
    linarith
  · refine hm hn2 ((abs_sub _ _).trans ?_)
    have := mul_le_mul k4 hs2 (abs_nonneg _) (by norm_num)
    have := mul_le_mul k5 hc2 (abs_nonneg _) (by norm_num)
    rw [abs_mul, abs_mul]; linarith
  · have f1 : |(4 * ζ ^ 2 - 1) / 8 * c3 + ζ * (5 - 4 * ζ ^ 2) / 8 * s3| ≤ 1 / 4 := by
      refine (abs_add_le _ _).trans ?_
      have := mul_le_mul k2 hc3 (abs_nonneg _) (by norm_num)
      have := mul_le_mul k3 hs3 (abs_nonneg _) (by norm_num)
      rw [abs_mul, abs_mul]; linarith
    have f2 : |(4 * ζ ^ 2 - 1) / 8 * s3 - ζ * (5 - 4 * ζ ^ 2) / 8 * c3| ≤ 1 / 4 := by
      refine (abs_sub _ _).trans ?_
      have := mul_le_mul k2 hs3 (abs_nonneg _) (by norm_num)
      have := mul_le_mul k3 hc3 (abs_nonneg _) (by norm_num)
      rw [abs_mul, abs_mul]; linarith
    refine (abs_add_le _ _).trans ?_
    have := hm hn0 f1
    have := hm hn1 f2
    linarith

/-- **Fourth derivative of `⟨n, hel⟩` along `ρ`** (plane faces). -/
theorem hel_rho_interp4 {n : Space} (hn : ‖n‖ ≤ 1) {ζ : ℝ} (hζ : |ζ| ≤ 3 / 25) (t : ℝ)
    {r0 r1 r2 r3 r : ℝ} (h01 : r0 < r1) (h12 : r1 < r2) (h23 : r2 < r3) (hlo : 17 / 20 ≤ r0)
    (hr : r ∈ Icc r1 r2) :
    |⟪n, hel (circ r ζ t)⟫ - newt r0 r1 r2 r3 ⟪n, hel (circ r0 ζ t)⟫ ⟪n, hel (circ r1 ζ t)⟫
      ⟪n, hel (circ r2 ζ t)⟫ ⟪n, hel (circ r3 ζ t)⟫ r| ≤ 1000 * |omega4 r0 r1 r2 r3 r| / 24 := by
  have hn3 := coords_sq_le hn
  have hn0 : |n 0| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [sq_nonneg (n 1), sq_nonneg (n
      2)]
  have hn1 : |n 1| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [sq_nonneg (n 0), sq_nonneg (n
      2)]
  have hn2 : |n 2| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith [sq_nonneg (n 0), sq_nonneg (n
      1)]
  set c1 := cos (phiT t); set s1 := sin (phiT t); set c3 := cos (3 * phiT t)
  set s3 := sin (3 * phiT t); set c2 := cos (2 * phiT t); set s2 := sin (2 * phiT t)
  set l2 := n 2 * (-1 / 16 * s2)
  set l1 := n 0 * (c1 / 8 - ζ * s1 / 8) + n 1 * (-(s1 / 8) - ζ * c1 / 8)
  set l0 := n 2 * (3 / 8 * s2)
  set lm1 := n 0 * (-(c1 / 8) + 3 * ζ * s1 / 8 + c3 / 8 - 3 * ζ * s3 / 8) +
    n 1 * (s1 / 8 + 3 * ζ * c1 / 8 + s3 / 8 + 3 * ζ * c3 / 8)
  set lm2 := n 2 * ((12 * ζ ^ 2 - 5) / 16 * s2 - ζ / 2 * c2)
  set lm3 := n 0 * ((4 * ζ ^ 2 - 1) / 8 * c3 + ζ * (5 - 4 * ζ ^ 2) / 8 * s3) +
    n 1 * ((4 * ζ ^ 2 - 1) / 8 * s3 - ζ * (5 - 4 * ζ ^ 2) / 8 * c3)
  have hl : ∀ y, 0 < y → ⟪n, hel (circ y ζ t)⟫ = laur l2 l1 l0 lm1 lm2 lm3 y := by
    intro y hy
    rw [circ_eq_polar, hel_polar hy, inner_helP]
    simp only [cA, cB, cG, cD, cE, cF, laur, l2, l1, l0, lm1, lm2, lm3, c1, s1, c2, s2, c3, s3]
    field_simp
    ring
  have hpos : ∀ y ∈ Icc r0 r3, 0 < y := fun y hy => by linarith [hy.1]
  have m0 : r0 ∈ Icc r0 r3 := ⟨le_rfl, by linarith⟩
  have m1 : r1 ∈ Icc r0 r3 := ⟨h01.le, by linarith⟩
  have m2 : r2 ∈ Icc r0 r3 := ⟨by linarith, h23.le⟩
  have m3 : r3 ∈ Icc r0 r3 := ⟨by linarith, le_rfl⟩
  have mr : r ∈ Icc r0 r3 := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  rw [hl r (hpos r mr), hl r0 (hpos r0 m0), hl r1 (hpos r1 m1), hl r2 (hpos r2 m2),
    hl r3 (hpos r3 m3)]
  obtain ⟨hb1, hb2, hb3⟩ := lm_bounds hn0 hn1 hn2 hζ (abs_cos_le_one (phiT t))
    (abs_sin_le_one (phiT t)) (abs_cos_le_one (2 * phiT t)) (abs_sin_le_one (2 * phiT t))
    (abs_cos_le_one (3 * phiT t)) (abs_sin_le_one (3 * phiT t))
  have LC := fun y (hy : y ≠ 0) =>
    laur_chain (l2 := l2) (l1 := l1) (l0 := l0) (lm1 := lm1) (lm2 := lm2) (lm3 := lm3) hy
  refine newt_interp_bound (g := laur l2 l1 l0 lm1 lm2 lm3)
    (g1 := fun y => 2 * l2 * y + l1 - lm1 * (y ^ 2)⁻¹ - 2 * lm2 * (y ^ 3)⁻¹ - 3 * lm3 * (y ^ 4)⁻¹)
    (g2 := fun y => 2 * l2 + 2 * lm1 * (y ^ 3)⁻¹ + 6 * lm2 * (y ^ 4)⁻¹ + 12 * lm3 * (y ^ 5)⁻¹)
    (g3 := fun y => -6 * lm1 * (y ^ 4)⁻¹ - 24 * lm2 * (y ^ 5)⁻¹ - 60 * lm3 * (y ^ 6)⁻¹)
    (g4 := fun y => 24 * lm1 * (y ^ 5)⁻¹ + 120 * lm2 * (y ^ 6)⁻¹ + 360 * lm3 * (y ^ 7)⁻¹)
    h01 h12 h23 hr (fun y hy => (LC y (hpos y hy).ne').1)
    (fun y hy => (LC y (hpos y hy).ne').2.1) (fun y hy => (LC y (hpos y hy).ne').2.2.1)
    (fun y hy => (LC y (hpos y hy).ne').2.2.2) ?_
  intro y hy
  have hy0 : 17 / 20 ≤ y := by linarith [hy.1]
  have hyp : 0 < y := by linarith
  have i5 : (y ^ 5)⁻¹ ≤ (20 / 17) ^ 5 := by
    rw [inv_le_comm₀ (by positivity) (by positivity), ← inv_pow]
    exact pow_le_pow_left₀ (by norm_num) (by rw [inv_div]; exact hy0) 5
  have i6 : (y ^ 6)⁻¹ ≤ (20 / 17) ^ 6 := by
    rw [inv_le_comm₀ (by positivity) (by positivity), ← inv_pow]
    exact pow_le_pow_left₀ (by norm_num) (by rw [inv_div]; exact hy0) 6
  have i7 : (y ^ 7)⁻¹ ≤ (20 / 17) ^ 7 := by
    rw [inv_le_comm₀ (by positivity) (by positivity), ← inv_pow]
    exact pow_le_pow_left₀ (by norm_num) (by rw [inv_div]; exact hy0) 7
  have p5 : 0 ≤ (y ^ 5)⁻¹ := by positivity
  have p6 : 0 ≤ (y ^ 6)⁻¹ := by positivity
  have p7 : 0 ≤ (y ^ 7)⁻¹ := by positivity
  calc |24 * lm1 * (y ^ 5)⁻¹ + 120 * lm2 * (y ^ 6)⁻¹ + 360 * lm3 * (y ^ 7)⁻¹|
      ≤ 24 * |lm1| * (y ^ 5)⁻¹ + 120 * |lm2| * (y ^ 6)⁻¹ + 360 * |lm3| * (y ^ 7)⁻¹ := by
        have a1 : |24 * lm1 * (y ^ 5)⁻¹| = 24 * |lm1| * (y ^ 5)⁻¹ := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 24), abs_of_nonneg p5]
        have a2 : |120 * lm2 * (y ^ 6)⁻¹| = 120 * |lm2| * (y ^ 6)⁻¹ := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 120), abs_of_nonneg p6]
        have a3 : |360 * lm3 * (y ^ 7)⁻¹| = 360 * |lm3| * (y ^ 7)⁻¹ := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 360), abs_of_nonneg p7]
        rw [← a1, ← a2, ← a3]
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 24 * 1 * (20 / 17) ^ 5 + 120 * (1 / 2) * (20 / 17) ^ 6 + 360 * (1 / 2) * (20 / 17) ^ 7 := by
        gcongr
    _ ≤ 1000 := by norm_num

end PlasmaLean.Design.PolygonCoil
