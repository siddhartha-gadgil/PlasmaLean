/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorCoilsGrad

/-!
# Coil fields for the rational stellarator: gradient bound and perturbed confinement

Step 1 of the coil link of `notes/theory/first-stellarator-rung.md` §3.

* `grad_bound`: `‖DI‖ ≤ Gc = 6.17 × 10¹¹` on the tube `T` for the certified approximate
  first integral `I = Confined.Ifun` (scaled by `2⁴⁰`; physically `‖DÎ‖ ≤ 0.562`). The proof
  writes `DI` in the orthogonal frame `(x, y, 0)`, `e_z`, `(-y, x, 0)`
  (`fderiv_Ifun_apply`, Cauchy–Schwarz `grad_core`) and uses the kernel-checked bounds on the
  partial derivatives of `P(s, z, C, S)` from `RationalStellaratorCoilsGrad` (the true maximum
  of `‖DÎ‖` on `T` is about `0.31`, so `Gc` is conservative by a factor `≈ 1.8`).
* `confined_of_error`: **every field `B'` that is continuous on `T` and within `η` of
  `field (1/4)` on `T`** inherits finite-length confinement: a curve that is a field line of `B'`
  on `[0, L]` and starts in the start tube stays in `T` for `s ∈ [0, L]`, provided
  `(δ + η Gc) L < I_b - I_a` (`defect_of_perturbation` + the local first-exit theorem), and its
  toroidal angle advances by at least `(4/5 - 9η/8) L`.
* `confined_of_error_transits`: with `L = 8N` this gives `N` toroidal transits whenever
  `(δ + η Gc) 8N < I_b - I_a`; e.g. `η ≤ 5.9 × 10⁻⁵` gives 10 transits
  (`confined_of_error_ten`) and `η ≤ 6.6 × 10⁻⁴` gives 1 transit (`confined_of_error_one`).

Scope: field lines only (no particle drifts); `B'` is any field (no Maxwell equations are
used here). The worst-case linear drift bound is what makes the field-error budget small;
coils and the maximum-principle transfer are in `RationalStellaratorCoilsTransfer`.
-/

public section
noncomputable section

namespace PlasmaLean.Design.RationalStellarator.Coils
open PlasmaLean.Design.RationalStellarator PlasmaLean.Design.RationalStellarator.Cover
  PlasmaLean.Design.RationalStellarator.Confined PlasmaLean.Kinetic.LiePoly PlasmaLean.Fields

/-! ## The derivative of `I` in the frame `(x, y, 0)`, `e_z`, `(-y, x, 0)` -/

/-- Derivative of `f` along the line `r ↦ x + r E`. -/
theorem line_hasDerivAt {f : Space → ℝ} {L : Space →L[ℝ] ℝ} {x : Space}
    (hf : HasFDerivAt f L x) (E : Space) :
    HasDerivAt (fun r : ℝ => f (x + r • E)) (L E) 0 := by
  have := curve_hasDerivAt hf 1 E
  simpa using this

/-- Transport of a derivative statement along equalities. -/
theorem hasDerivAt_of_eq {f g : ℝ → ℝ} {a b : ℝ} (h : HasDerivAt f a 0) (hfg : f = g)
    (hab : a = b) : HasDerivAt g b 0 := hfg ▸ hab ▸ h

/-- Directional derivative of `I` along a vector `E` whose action on the variables
`(s, z, C, S)` is given by the polynomials `F` (evaluated at the base point). -/
theorem fderiv_Ifun_of_rates (x : Space) (hx : r2 x ≠ 0) (E : Space) (F : List Poly)
    (hF : ∀ i, HasDerivAt (fun r : ℝ => W (x + r • E) i) (eval (F.getD i []) (W x)) 0) :
    fderiv ℝ Ifun x E = ∑ j ∈ Finset.range F.length,
      eval (pderiv PQ j) (W x) * eval (F.getD j []) (W x) := by
  have h1 := hasDerivAt_eval PQ F (X := fun r => W (x + r • E)) (t := 0)
    (fun i => by simpa using hF i)
  have h2 := line_hasDerivAt (differentiableAt_Ifun x hx).hasFDerivAt E
  have h3 := h2.unique h1
  rw [h3]
  simp only [zero_smul, add_zero, lie, eval_lieAux, zero_add]

/-- The radial frame vector `(x, y, 0)`. -/
@[expose] def E1 (x : Space) : Space := WithLp.toLp 2 ![x 0, x 1, 0]
/-- The vertical frame vector `e_z`. -/
@[expose] def E2 : Space := WithLp.toLp 2 ![0, 0, 1]
/-- The toroidal frame vector `(-y, x, 0)`. -/
@[expose] def E3 (x : Space) : Space := WithLp.toLp 2 ![-x 1, x 0, 0]

/-- Rates of `(s, z, C, S)` along `E1`: `(1 + 2s, 0, 0, 0)`. -/
@[expose] def F1 : List Poly := [[(1, []), (2, [1])], [], [], []]
/-- Rates of `(s, z, C, S)` along `E2`: `(0, 1, 0, 0)`. -/
@[expose] def F2 : List Poly := [[], [(1, [])], [], []]
/-- Rates of `(s, z, C, S)` along `E3`: `(0, 0, -2S, 2C)`. -/
@[expose] def F3 : List Poly := [[], [], [(-2, [0, 0, 0, 1])], [(2, [0, 0, 1])]]

/-- Variables beyond index `3` have zero rate. -/
theorem hasDerivAt_W_ge4 (x E : Space) (F : List Poly) (hF : F.length = 4) {i : ℕ}
    (hi : 4 ≤ i) :
    HasDerivAt (fun r : ℝ => W (x + r • E) i) (eval (F.getD i []) (W x)) 0 := by
  have h1 : (fun r : ℝ => W (x + r • E) i) = fun _ => 0 := funext fun r => W_ge4 _ hi
  have h2 : F.getD i [] = [] := List.getD_eq_default _ _ (by omega)
  rw [h1, h2]
  simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)

/-- Rates along `E1`. -/
theorem rates_E1 (x : Space) (hx : r2 x ≠ 0) (i : ℕ) :
    HasDerivAt (fun r : ℝ => W (x + r • E1 x) i) (eval (F1.getD i []) (W x)) 0 := by
  have hw : winv x * r2 x = 1 := inv_mul_cancel₀ hx
  have hr : r2 x = x 0 ^ 2 + x 1 ^ 2 := rfl
  rcases Nat.lt_or_ge i 4 with hi | hi
  · interval_cases i
    · refine hasDerivAt_of_eq (line_hasDerivAt (hasFDerivAt_sc x) (E1 x)) rfl ?_
      simp only [F1, List.getD_cons_zero, eval_cons, eval_nil, evalMono, lin_apply, E1, W, sc]
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, mul_zero,
        add_zero, Rat.cast_one, mul_one, Rat.cast_ofNat, pow_one]
      rw [hr]; ring
    · refine hasDerivAt_of_eq (line_hasDerivAt (hasFDerivAt_coord x 2) (E1 x)) rfl ?_
      simp [F1, E1]
    · refine hasDerivAt_of_eq (line_hasDerivAt (hasFDerivAt_cc x hx) (E1 x)) rfl ?_
      simp only [F1, List.getD_cons_zero, List.getD_cons_succ, eval_nil, lin_apply, E1]
      simp
      linear_combination (-(2 * (x 0 ^ 2 - x 1 ^ 2)) * winv x) * hw +
        2 * winv x ^ 2 * (x 0 ^ 2 - x 1 ^ 2) * hr
    · refine hasDerivAt_of_eq (line_hasDerivAt (hasFDerivAt_ss x hx) (E1 x)) rfl ?_
      simp only [F1, List.getD_cons_zero, List.getD_cons_succ, eval_nil, lin_apply, E1]
      simp
      linear_combination (-(4 * x 0 * x 1) * winv x) * hw + 4 * x 0 * x 1 * winv x ^ 2 * hr
  · exact hasDerivAt_W_ge4 x _ F1 rfl hi

/-- Rates along `E2`. -/
theorem rates_E2 (x : Space) (hx : r2 x ≠ 0) (i : ℕ) :
    HasDerivAt (fun r : ℝ => W (x + r • E2) i) (eval (F2.getD i []) (W x)) 0 := by
  rcases Nat.lt_or_ge i 4 with hi | hi
  · interval_cases i
    · refine hasDerivAt_of_eq (line_hasDerivAt (hasFDerivAt_sc x) E2) rfl ?_
      simp [F2, lin_apply, E2]
    · refine hasDerivAt_of_eq (line_hasDerivAt (hasFDerivAt_coord x 2) E2) rfl ?_
      simp [F2, E2, evalMono]
    · refine hasDerivAt_of_eq (line_hasDerivAt (hasFDerivAt_cc x hx) E2) rfl ?_
      simp [F2, lin_apply, E2]
    · refine hasDerivAt_of_eq (line_hasDerivAt (hasFDerivAt_ss x hx) E2) rfl ?_
      simp [F2, lin_apply, E2]
  · exact hasDerivAt_W_ge4 x _ F2 rfl hi

/-- Rates along `E3`. -/
theorem rates_E3 (x : Space) (hx : r2 x ≠ 0) (i : ℕ) :
    HasDerivAt (fun r : ℝ => W (x + r • E3 x) i) (eval (F3.getD i []) (W x)) 0 := by
  have hw : winv x * r2 x = 1 := inv_mul_cancel₀ hx
  have hr : r2 x = x 0 ^ 2 + x 1 ^ 2 := rfl
  rcases Nat.lt_or_ge i 4 with hi | hi
  · interval_cases i
    · refine hasDerivAt_of_eq (line_hasDerivAt (hasFDerivAt_sc x) (E3 x)) rfl ?_
      simp [F3, lin_apply, E3]; ring
    · refine hasDerivAt_of_eq (line_hasDerivAt (hasFDerivAt_coord x 2) (E3 x)) rfl ?_
      simp [F3, E3]
    · refine hasDerivAt_of_eq (line_hasDerivAt (hasFDerivAt_cc x hx) (E3 x)) rfl ?_
      simp only [F3, List.getD_cons_zero, List.getD_cons_succ, eval_cons, eval_nil, evalMono,
        lin_apply, E3, W, ss]
      simp
      ring
    · refine hasDerivAt_of_eq (line_hasDerivAt (hasFDerivAt_ss x hx) (E3 x)) rfl ?_
      simp only [F3, List.getD_cons_zero, List.getD_cons_succ, eval_cons, eval_nil, evalMono,
        lin_apply, E3, W, cc]
      simp
      linear_combination (4 * x 0 ^ 2 * x 1 ^ 2 * winv x - 4 * x 0 ^ 2 * x 1 ^ 2 * winv x) * hw
  · exact hasDerivAt_W_ge4 x _ F3 rfl hi

/-- `x = α E1 + β E2 + γ E3` off the axis. -/
theorem frame_decomp (x v : Space) (hx : r2 x ≠ 0) :
    v = ((x 0 * v 0 + x 1 * v 1) / r2 x) • E1 x + v 2 • E2 +
      ((x 0 * v 1 - x 1 * v 0) / r2 x) • E3 x := by
  have hr : r2 x = x 0 ^ 2 + x 1 ^ 2 := rfl
  ext i
  fin_cases i <;> simp [E1, E2, E3] <;> field_simp <;> rw [hr] <;> ring

/-- **The derivative of `I`** in the orthogonal frame:
`DI·v = (x v₀ + y v₁) ∂ₛP + v₂ ∂_zP + ((x v₁ - y v₀)/r₂) · 2(C ∂_SP - S ∂_CP)`. -/
theorem fderiv_Ifun_apply (x : Space) (hx : r2 x ≠ 0) (v : Space) :
    fderiv ℝ Ifun x v = (x 0 * v 0 + x 1 * v 1) * eval (pderiv PQ 0) (W x) +
      v 2 * eval (pderiv PQ 1) (W x) + ((x 0 * v 1 - x 1 * v 0) / r2 x) *
        (2 * cc x * eval (pderiv PQ 3) (W x) - 2 * ss x * eval (pderiv PQ 2) (W x)) := by
  have hr2 : r2 x = 1 + 2 * sc x := r2_eq x
  conv_lhs => rw [frame_decomp x v hx]
  rw [map_add, map_add, map_smul, map_smul, map_smul,
    fderiv_Ifun_of_rates x hx _ F1 (rates_E1 x hx), fderiv_Ifun_of_rates x hx _ F2 (rates_E2 x hx),
    fderiv_Ifun_of_rates x hx _ F3 (rates_E3 x hx)]
  simp only [F1, F2, F3, List.length_cons, List.length_nil, Finset.sum_range_succ,
    Finset.sum_range_zero, List.getD_cons_zero, List.getD_cons_succ, eval_cons, eval_nil,
    evalMono, smul_eq_mul]
  simp only [W, List.getD_cons_zero, List.getD_cons_succ]
  push_cast
  field_simp
  rw [hr2]
  ring

/-- Weighted Cauchy–Schwarz inequality with weights `(p, 1, p)`. -/
theorem weighted_cs (p a b c α β γ : ℝ) (hp : 0 ≤ p) :
    (p * a * α + b * β + p * c * γ) ^ 2 ≤
      (p * a ^ 2 + b ^ 2 + p * c ^ 2) * (p * α ^ 2 + β ^ 2 + p * γ ^ 2) := by
  nlinarith [mul_nonneg hp (sq_nonneg (a * β - b * α)),
    mul_nonneg (mul_nonneg hp hp) (sq_nonneg (a * γ - c * α)),
    mul_nonneg hp (sq_nonneg (b * γ - c * β))]

/-- The gradient bound `Gc = 6.17 × 10¹¹` for `I` (scaled by `2⁴⁰`; `‖DÎ‖ ≤ 0.562`). -/
@[expose] def Gc : ℝ := 617 * 10 ^ 9

/-- `C, S` are bounded by `1`. -/
theorem abs_cc_ss_le (y : Space) (hy : r2 y ≠ 0) : |cc y| ≤ 1 ∧ |ss y| ≤ 1 := by
  have h := cc_sq_add_ss_sq y hy
  constructor <;> rw [abs_le] <;> constructor <;>
    nlinarith [sq_nonneg (cc y), sq_nonneg (ss y), sq_nonneg (cc y + 1), sq_nonneg (cc y - 1),
      sq_nonneg (ss y + 1), sq_nonneg (ss y - 1)]

/-- Bounds on the four partial derivatives of `P` on the tube (`pderivZ_bounds`). -/
theorem pderiv_bounds {y : Space} (hy : y ∈ tubeT) :
    |eval (pderiv PQ 0) (W y)| ≤ 445302209249 ∧ |eval (pderiv PQ 1) (W y)| ≤ 373833953443 ∧
    |eval (pderiv PQ 2) (W y)| ≤ 12644383718 ∧ |eval (pderiv PQ 3) (W y)| ≤ 7696581393 := by
  have hr := (r2_pos_of_tube hy).ne'
  obtain ⟨b0, b1, b2, b3⟩ := pderivZ_bounds hy.1 hy.2 (cc_sq_add_ss_sq y hr)
  simp only [toQ_pderivZ, ← W_eq_vars4] at b0 b1 b2 b3
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact b0.trans_eq (by norm_num)
  · exact b1.trans_eq (by norm_num)
  · exact b2.trans_eq (by norm_num)
  · exact b3.trans_eq (by norm_num)

/-- The numerical inequality behind `Gc`. -/
theorem Gc_sq_bound : 6 / 5 * (445302209249 : ℝ) ^ 2 + 373833953443 ^ 2 +
    5 / 4 * (2 * (12644383718 + 7696581393) : ℝ) ^ 2 ≤ Gc ^ 2 := by
  norm_num [Gc]

/-- Algebraic core of the gradient bound. -/
theorem grad_core {p a b c A B K G u1 v2 u3 N : ℝ} (hp1 : 4 / 5 ≤ p) (hp2 : p ≤ 6 / 5)
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ K) (hG : 0 ≤ G)
    (hAG : 6 / 5 * A ^ 2 + B ^ 2 + 5 / 4 * K ^ 2 ≤ G ^ 2) (hN : 0 ≤ N)
    (hlag : p * (u1 / p) ^ 2 + v2 ^ 2 + p * (u3 / p) ^ 2 = N ^ 2) :
    |u1 * a + v2 * b + u3 / p * c| ≤ G * N := by
  have hpos : 0 < p := by linarith
  have hcs := weighted_cs p a b (c / p) (u1 / p) v2 (u3 / p) hpos.le
  rw [hlag] at hcs
  have heq : p * a * (u1 / p) + b * v2 + p * (c / p) * (u3 / p) = u1 * a + v2 * b + u3 / p * c := by
    field_simp
  rw [heq] at hcs
  have ha2 : a ^ 2 ≤ A ^ 2 := sq_le_sq' (abs_le.mp ha).1 (abs_le.mp ha).2
  have hb2 : b ^ 2 ≤ B ^ 2 := sq_le_sq' (abs_le.mp hb).1 (abs_le.mp hb).2
  have hc2 : c ^ 2 ≤ K ^ 2 := sq_le_sq' (abs_le.mp hc).1 (abs_le.mp hc).2
  have hpc : p * (c / p) ^ 2 = c ^ 2 / p := by field_simp
  have h3 : c ^ 2 / p ≤ 5 / 4 * c ^ 2 := by
    rw [div_le_iff₀ hpos]
    have := mul_le_mul_of_nonneg_left hp1 (sq_nonneg c)
    linarith
  have h1 : p * a ^ 2 ≤ 6 / 5 * a ^ 2 := mul_le_mul_of_nonneg_right hp2 (sq_nonneg a)
  have hfirst : p * a ^ 2 + b ^ 2 + p * (c / p) ^ 2 ≤ G ^ 2 := by
    rw [hpc]; linarith
  have hsq : (u1 * a + v2 * b + u3 / p * c) ^ 2 ≤ (G * N) ^ 2 := by
    rw [mul_pow]
    exact hcs.trans (mul_le_mul_of_nonneg_right hfirst (sq_nonneg N))
  exact abs_le_of_sq_le_sq hsq (mul_nonneg hG hN)

/-- **Gradient bound**: `‖DI‖ ≤ Gc` on the tube. -/
theorem grad_bound {y : Space} (hy : y ∈ tubeT) : ‖fderiv ℝ Ifun y‖ ≤ Gc := by
  have hpos := r2_pos_of_tube hy
  have hr := hpos.ne'
  have hs := abs_le.mp hy.1
  have hp1 : 4 / 5 ≤ r2 y := by rw [r2_eq]; linarith
  have hp2 : r2 y ≤ 6 / 5 := by rw [r2_eq]; linarith
  obtain ⟨hC, hS⟩ := abs_cc_ss_le y hr
  obtain ⟨ba, bb, b2, b3⟩ := pderiv_bounds hy
  have hG0 : (0 : ℝ) ≤ Gc := by norm_num [Gc]
  have hc : |2 * cc y * eval (pderiv PQ 3) (W y) - 2 * ss y * eval (pderiv PQ 2) (W y)| ≤
      2 * (12644383718 + 7696581393) := by
    have e1 : |2 * cc y * eval (pderiv PQ 3) (W y)| ≤ 2 * 7696581393 := by
      rw [abs_mul, abs_mul, abs_two]
      calc 2 * |cc y| * |eval (pderiv PQ 3) (W y)| ≤ 2 * 1 * 7696581393 := by gcongr
        _ = _ := by ring
    have e2 : |2 * ss y * eval (pderiv PQ 2) (W y)| ≤ 2 * 12644383718 := by
      rw [abs_mul, abs_mul, abs_two]
      calc 2 * |ss y| * |eval (pderiv PQ 2) (W y)| ≤ 2 * 1 * 12644383718 := by gcongr
        _ = _ := by ring
    calc _ ≤ |2 * cc y * eval (pderiv PQ 3) (W y)| + |2 * ss y * eval (pderiv PQ 2) (W y)| :=
          abs_sub _ _
      _ ≤ _ := by linarith
  refine ContinuousLinearMap.opNorm_le_bound _ hG0 fun v => ?_
  rw [Real.norm_eq_abs, fderiv_Ifun_apply y hr v]
  refine grad_core hp1 hp2 ba bb hc hG0 Gc_sq_bound (norm_nonneg v) ?_
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  have : r2 y = y 0 ^ 2 + y 1 ^ 2 := rfl
  field_simp
  rw [this]; ring

/-! ## Confinement for a perturbed field -/

/-- The toroidal rate `B · ∇φ = (x B_y - y B_x)/r₂` of an arbitrary field `B`. -/
@[expose] def phiRateOf (B : Space → Space) (y : Space) : ℝ := (y 0 * B y 1 - y 1 * B y 0) / r2 y

/-- `phiRateOf (field (1/4)) = phiRate`. -/
theorem phiRateOf_field : phiRateOf (field (1 / 4)) = phiRate := rfl

/-- **Toroidal rate under a field error**: `B'·∇φ ≥ 4/5 - 9η/8` on the tube if
`‖B' - B‖ ≤ η` there. -/
theorem phiRateOf_lower {B' : Space → Space} {η : ℝ} {y : Space} (hy : y ∈ tubeT)
    (hη : ‖B' y - field (1 / 4) y‖ ≤ η) : 4 / 5 - 9 / 8 * η ≤ phiRateOf B' y := by
  have hpos := r2_pos_of_tube hy
  have hs := abs_le.mp hy.1
  have hp1 : 4 / 5 ≤ r2 y := by rw [r2_eq]; linarith
  have hφ := phiRate_lower hy
  set d := B' y - field (1 / 4) y with hd
  have hd0 : B' y 0 = field (1 / 4) y 0 + d 0 := by simp [hd]
  have hd1 : B' y 1 = field (1 / 4) y 1 + d 1 := by simp [hd]
  have hsplit : phiRateOf B' y = phiRate y + (y 0 * d 1 - y 1 * d 0) / r2 y := by
    unfold phiRateOf phiRate
    rw [hd0, hd1]
    field_simp
    ring
  have hnorm : d 0 ^ 2 + d 1 ^ 2 ≤ ‖d‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]; nlinarith [sq_nonneg (d 2)]
  have hr : r2 y = y 0 ^ 2 + y 1 ^ 2 := rfl
  have hlag : (y 0 * d 1 - y 1 * d 0) ^ 2 ≤ r2 y * ‖d‖ ^ 2 := by
    have : (y 0 * d 1 - y 1 * d 0) ^ 2 ≤ r2 y * (d 0 ^ 2 + d 1 ^ 2) := by
      rw [hr]; nlinarith [sq_nonneg (y 0 * d 0 + y 1 * d 1)]
    exact this.trans (mul_le_mul_of_nonneg_left hnorm hpos.le)
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hη
  have habs : |y 0 * d 1 - y 1 * d 0| ≤ 9 / 8 * r2 y * η := by
    apply abs_le_of_sq_le_sq _ (by positivity)
    have h1 : r2 y * ‖d‖ ^ 2 ≤ (9 / 8 * r2 y) ^ 2 * ‖d‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      nlinarith
    have h2 : (9 / 8 * r2 y) ^ 2 * ‖d‖ ^ 2 ≤ (9 / 8 * r2 y * η) ^ 2 := by
      rw [mul_pow (9 / 8 * r2 y) η]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hη 2) (sq_nonneg _)
    linarith
  have hq : -(9 / 8 * η) ≤ (y 0 * d 1 - y 1 * d 0) / r2 y := by
    rw [le_div_iff₀ hpos]
    nlinarith [(abs_le.mp habs).1]
  linarith

/-- The defect budget: `I_b - I_a = 3298534883` (`I_b = 4398046511`, `I_a = 1099511628`), the
defect bound of the exact field `δ = 17592186/4`. -/
@[expose] def budget : ℝ := 3298534883

/-- **Confinement of a perturbed field.** If `B'` is continuous on the tube `T` and within `η` of
`field (1/4)` there, then every curve that is a field line of `B'` on `[0, L]` starting in the
start tube stays in `T` for `s ∈ [0, L]`, provided `(δ + η Gc) L < I_b - I_a`; and its toroidal
angle `∫ (x ẏ - y ẋ)/r₂` advances by at least `(4/5 - 9η/8) L`. -/
theorem confined_of_error {B' : Space → Space} {η L : ℝ} (hη0 : 0 ≤ η)
    (hη : ∀ y ∈ tubeT, ‖B' y - field (1 / 4) y‖ ≤ η) (hcont : ContinuousOn B' tubeT)
    (hL : 0 ≤ L) (hbud : (17592186 / 4 + η * Gc) * L < budget)
    {γ : ℝ → Space} (hγ : ∀ t ∈ Set.Icc 0 L, HasDerivAt γ (B' (γ t)) t)
    (h0 : γ 0 ∈ startTube) :
    (∀ s ∈ Set.Icc 0 L, γ s ∈ tubeT) ∧
      (4 / 5 - 9 / 8 * η) * L ≤ ∫ u in (0 : ℝ)..L, phiRateOf B' (γ u) := by
  have hdef := defect_of_perturbation (B := field (1 / 4)) (B' := B') (I := Ifun) (K := tubeT)
    (fun x hx => defect_bound hx) (fun x hx => hη x hx) (fun x hx => grad_bound hx)
  have hG0 : (0 : ℝ) ≤ Gc := by norm_num [Gc]
  have hconf := fieldLine_confined_of_defect_local (B := B') (I := Ifun) (T := tubeT)
    (Ia := 1099511628) (Ib := 4398046511) (δ := 17592186 / 4 + η * Gc) (by positivity)
    isClosed_tubeT (fun x hx => differentiableAt_Ifun x (r2_pos_of_tube hx).ne')
    (fun x hx => front_bound hx) (fun x hx _ => hdef x hx) hγ (startTube_sub h0) (start_bound h0)
  have hT : ∀ s ∈ Set.Icc 0 L, γ s ∈ tubeT := by
    intro s hs
    refine (hconf s hs ?_).1
    have : (17592186 / 4 + η * Gc) * s ≤ (17592186 / 4 + η * Gc) * L :=
      mul_le_mul_of_nonneg_left hs.2 (by positivity)
    unfold budget at hbud
    linarith
  refine ⟨hT, ?_⟩
  have hrate : ContinuousOn (phiRateOf B') tubeT := by
    have h0' : ContinuousOn (fun y : Space => B' y 0) tubeT :=
      (PiLp.continuous_apply 2 (fun _ => ℝ) 0).comp_continuousOn hcont
    have h1' : ContinuousOn (fun y : Space => B' y 1) tubeT :=
      (PiLp.continuous_apply 2 (fun _ => ℝ) 1).comp_continuousOn hcont
    have hr : Continuous r2 := by unfold r2; fun_prop
    unfold phiRateOf
    refine ContinuousOn.div ?_ hr.continuousOn fun y hy => (r2_pos_of_tube hy).ne'
    exact (((PiLp.continuous_apply 2 _ 0).continuousOn).mul h1').sub
      (((PiLp.continuous_apply 2 _ 1).continuousOn).mul h0')
  have hγc : ContinuousOn γ (Set.Icc 0 L) := fun u hu => (hγ u hu).continuousAt.continuousWithinAt
  have hcont' : ContinuousOn (fun u => phiRateOf B' (γ u)) (Set.Icc 0 L) :=
    hrate.comp hγc (fun u hu => hT u hu)
  have hint : IntervalIntegrable (fun u => phiRateOf B' (γ u)) MeasureTheory.volume 0 L :=
    hcont'.intervalIntegrable_of_Icc hL
  have hmono := intervalIntegral.integral_mono_on hL
    (intervalIntegrable_const (c := (4 / 5 - 9 / 8 * η : ℝ))) hint
    (fun u hu => phiRateOf_lower (hT u hu) (hη _ (hT u hu)))
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using hmono

/-- Along a field line of `B'`, `phiRateOf B' (γ u)` is the derivative of the toroidal angle,
`(x ẏ - y ẋ)/(x² + y²)`. -/
theorem phiRateOf_eq_deriv {B' : Space → Space} {γ : ℝ → Space} {u : ℝ}
    (hγ : HasDerivAt γ (B' (γ u)) u) :
    phiRateOf B' (γ u) =
      (γ u 0 * deriv (fun v => γ v 1) u - γ u 1 * deriv (fun v => γ v 0) u) / r2 (γ u) := by
  have hd : ∀ i : Fin 3, deriv (fun v => γ v i) u = B' (γ u) i := fun i =>
    (((PiLp.proj 2 (fun _ => ℝ) i : Space →L[ℝ] ℝ).hasFDerivAt).comp_hasDerivAt u hγ).deriv
  rw [hd 0, hd 1]
  rfl

/-- **`N` toroidal transits under a field error**: with `L = 8N`, if `η ≤ 1/100` and
`(δ + η Gc) 8N < I_b - I_a`, field lines of `B'` from the start tube stay in `T` and their
toroidal angle advances by at least `2πN`. -/
theorem confined_of_error_transits {B' : Space → Space} {η : ℝ} (N : ℕ) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1 / 100) (hη : ∀ y ∈ tubeT, ‖B' y - field (1 / 4) y‖ ≤ η)
    (hcont : ContinuousOn B' tubeT) (hbud : (17592186 / 4 + η * Gc) * (8 * N) < budget)
    {γ : ℝ → Space} (hγ : ∀ t ∈ Set.Icc 0 (8 * (N : ℝ)), HasDerivAt γ (B' (γ t)) t)
    (h0 : γ 0 ∈ startTube) :
    (∀ s ∈ Set.Icc 0 (8 * (N : ℝ)), γ s ∈ tubeT) ∧
      2 * Real.pi * N ≤ ∫ u in (0 : ℝ)..(8 * N), phiRateOf B' (γ u) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  obtain ⟨hT, hadv⟩ := confined_of_error hη0 hη hcont (by positivity) hbud hγ h0
  refine ⟨hT, le_trans ?_ hadv⟩
  have hpi := Real.pi_lt_d2
  nlinarith

/-- **10 transits** for every field within `η = 5.9 × 10⁻⁵` of `field (1/4)` on the tube. -/
theorem confined_of_error_ten {B' : Space → Space} {η : ℝ} (hη0 : 0 ≤ η)
    (hη1 : η ≤ 59 / 1000000) (hη : ∀ y ∈ tubeT, ‖B' y - field (1 / 4) y‖ ≤ η)
    (hcont : ContinuousOn B' tubeT)
    {γ : ℝ → Space} (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 80, HasDerivAt γ (B' (γ t)) t)
    (h0 : γ 0 ∈ startTube) :
    (∀ s ∈ Set.Icc (0 : ℝ) 80, γ s ∈ tubeT) ∧
      2 * Real.pi * 10 ≤ ∫ u in (0 : ℝ)..80, phiRateOf B' (γ u) := by
  have h := confined_of_error_transits (B' := B') 10 hη0 (by linarith) hη hcont
    (by unfold budget Gc; push_cast; nlinarith) (γ := γ)
    (by rw [show (8 * ((10 : ℕ) : ℝ)) = 80 by norm_num]; exact hγ) h0
  rw [show (8 * ((10 : ℕ) : ℝ)) = 80 by norm_num, show ((10 : ℕ) : ℝ) = 10 by norm_num] at h
  simpa using h

/-- **One transit** for every field within `η = 6.6 × 10⁻⁴` of `field (1/4)` on the tube. -/
theorem confined_of_error_one {B' : Space → Space} {η : ℝ} (hη0 : 0 ≤ η)
    (hη1 : η ≤ 66 / 100000) (hη : ∀ y ∈ tubeT, ‖B' y - field (1 / 4) y‖ ≤ η)
    (hcont : ContinuousOn B' tubeT)
    {γ : ℝ → Space} (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 8, HasDerivAt γ (B' (γ t)) t)
    (h0 : γ 0 ∈ startTube) :
    (∀ s ∈ Set.Icc (0 : ℝ) 8, γ s ∈ tubeT) ∧
      2 * Real.pi ≤ ∫ u in (0 : ℝ)..8, phiRateOf B' (γ u) := by
  have h := confined_of_error_transits (B' := B') 1 hη0 (by linarith) hη hcont
    (by unfold budget Gc; push_cast; nlinarith) (γ := γ)
    (by rw [show (8 * ((1 : ℕ) : ℝ)) = 8 by norm_num]; exact hγ) h0
  rw [show (8 * ((1 : ℕ) : ℝ)) = 8 by norm_num, show ((1 : ℕ) : ℝ) = 1 by norm_num] at h
  simpa using h

/-- Sanity (degenerate case `η = 0`): the exact field itself satisfies the hypotheses, and the
perturbed theorem recovers 10 transits for its field lines (a weaker statement than the
95 transits of `rationalStellarator_confined_local`, since `L = 80`). -/
theorem exact_field_ten {γ : ℝ → Space}
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 80, HasDerivAt γ (field (1 / 4) (γ t)) t)
    (h0 : γ 0 ∈ startTube) :
    (∀ s ∈ Set.Icc (0 : ℝ) 80, γ s ∈ tubeT) ∧
      2 * Real.pi * 10 ≤ ∫ u in (0 : ℝ)..80, phiRate (γ u) := by
  have hc : ContinuousOn (field (1 / 4)) tubeT :=
    (field_contDiffOn (1 / 4)).continuousOn.mono fun y hy => r2_pos_of_tube hy
  exact confined_of_error_ten le_rfl (by norm_num) (fun y _ => by simp) hc hγ h0

/-- Non-vacuous instance: the magnetic axis is a field line of the exact field from the start
tube (10 transits by the perturbed theorem with `η = 0`). -/
theorem axis_ten : (∀ s ∈ Set.Icc (0 : ℝ) 80, axis s ∈ tubeT) ∧
    2 * Real.pi * 10 ≤ ∫ u in (0 : ℝ)..80, phiRate (axis u) :=
  exact_field_ten (fun t ht => axis_fieldLine (1 / 4) t ht.1) (axis_mem_startTube 0)

/-- Rejected fixture: the budget hypothesis of `confined_of_error_transits` fails for 10 transits
at `η = 6.1 × 10⁻⁵` (the threshold is `≈ 5.97 × 10⁻⁵` with the certified `Gc`). -/
theorem budget_fails_ten : ¬ ((17592186 / 4 + 61 / 1000000 * Gc) * (8 * 10) < budget) := by
  unfold budget Gc; norm_num

end PlasmaLean.Design.RationalStellarator.Coils
