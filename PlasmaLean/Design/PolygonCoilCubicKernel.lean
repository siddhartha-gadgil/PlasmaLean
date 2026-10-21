/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilInterp
public import PlasmaLean.Design.PolygonCoilCubicInterp

/-!
# Fourth derivatives of the Biot–Savart kernel along curves

For the cubic-interpolation certificate (`Design/PolygonCoilCubic*`) we need bounds on the fourth
derivative of the scalar kernel `g(τ) = ⟨m, u(τ)⟩/|u(τ)|³` (`kg`) along straight lines and along
circles. Writing `Gⱼ(x)[a₁, …, aⱼ] = Dʲ_x ⟨m, x/|x|³⟩[a₁, …, aⱼ]` (explicit symmetric forms
`kg1`, `kG2`, `kG3`, and the diagonal `kG4d`), Faà di Bruno gives

`g⁗ = G₄[u₁⁴] + 6 G₃[u₁, u₁, u₂] + 4 G₂[u₁, u₃] + 3 G₂[u₂, u₂] + G₁[u₄]`

(`hasDerivAt_g3`, `kgD4`). The bounds:

* **line bounds** (sharp, `abs_kg1_le`, `abs_kG2d_le`, `abs_kG3d_le`, `abs_kG4d_le`):
  `|Gⱼ[aʲ]| ≤ (j+1)! |m| |a|ʲ/|x|^{j+2}`. Each `Gⱼ[aʲ] = ⟨m, αx + βa⟩`, and
  `((j+1)!|a|ʲ/|x|^{j+2})² - |αx + βa|²` is `(|x|²|a|² - ⟨x, a⟩²)` times a positive polynomial;
* **polarization** (`abs_kG2_le`, `abs_kG3_perp_le`): `|G₂[a, b]| ≤ 3|m|(λ²|a|² + |b|²/λ²)/|x|⁴`
  and, for `a ⊥ b`, `|G₃[a, a, b]| ≤ 1.002 · 24 |m| |a|²|b|/|x|⁵`;
* `abs_kgD4_line`: along a line (`u₂ = u₃ = u₄ = 0`) `|g⁗| ≤ 120|m||u₁|⁴/|u|⁶`.
-/

public section
noncomputable section

namespace PlasmaLean.Design.PolygonCoil
open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator.CoilsTF Set
open scoped RealInnerProductSpace

/-! ## The symmetric forms -/

/-- The second derivative form `G₂(x)[a, b]` of `⟨m, x/|x|³⟩`. -/
@[expose] def kG2 (m x a b : Space) : ℝ :=
  -3 * (⟪x, b⟫ * ⟪m, a⟫ + ⟪x, a⟫ * ⟪m, b⟫ + ⟪a, b⟫ * ⟪m, x⟫) * (‖x‖ ^ 5)⁻¹ +
    15 * ⟪x, a⟫ * ⟪x, b⟫ * ⟪m, x⟫ * (‖x‖ ^ 7)⁻¹

/-- The third derivative form `G₃(x)[a, b, c]` of `⟨m, x/|x|³⟩`. -/
@[expose] def kG3 (m x a b c : Space) : ℝ :=
  -3 * (⟪a, b⟫ * ⟪m, c⟫ + ⟪a, c⟫ * ⟪m, b⟫ + ⟪b, c⟫ * ⟪m, a⟫) * (‖x‖ ^ 5)⁻¹ +
    15 * (⟪x, a⟫ * ⟪x, b⟫ * ⟪m, c⟫ + ⟪x, a⟫ * ⟪x, c⟫ * ⟪m, b⟫ + ⟪x, b⟫ * ⟪x, c⟫ * ⟪m, a⟫ +
      (⟪a, b⟫ * ⟪x, c⟫ + ⟪a, c⟫ * ⟪x, b⟫ + ⟪b, c⟫ * ⟪x, a⟫) * ⟪m, x⟫) * (‖x‖ ^ 7)⁻¹ -
    105 * ⟪x, a⟫ * ⟪x, b⟫ * ⟪x, c⟫ * ⟪m, x⟫ * (‖x‖ ^ 9)⁻¹

/-- The diagonal of the fourth derivative form, `G₄(x)[a, a, a, a]`. -/
@[expose] def kG4d (m x a : Space) : ℝ :=
  45 * (‖a‖ ^ 4 * ‖x‖ ^ 4 - 14 * ‖a‖ ^ 2 * ⟪x, a⟫ ^ 2 * ‖x‖ ^ 2 + 21 * ⟪x, a⟫ ^ 4) * ⟪m, x⟫ *
      (‖x‖ ^ 11)⁻¹ +
    60 * ⟪x, a⟫ * (3 * ‖a‖ ^ 2 * ‖x‖ ^ 2 - 7 * ⟪x, a⟫ ^ 2) * ⟪m, a⟫ * (‖x‖ ^ 9)⁻¹

/-- Third derivative of the kernel along a curve. -/
@[expose] def kgD3 (m u u1 u2 u3 : Space) : ℝ :=
  kG3 m u u1 u1 u1 + 3 * kG2 m u u1 u2 + kg1 m u u3

/-- Fourth derivative of the kernel along a curve. -/
@[expose] def kgD4 (m u u1 u2 u3 u4 : Space) : ℝ :=
  kG4d m u u1 + 6 * kG3 m u u1 u1 u2 + 4 * kG2 m u u1 u3 + 3 * kG2 m u u2 u2 + kg1 m u u4

/-! ## Derivatives along curves -/

theorem hasDerivAt_inner_const (m : Space) {a : ℝ → Space} {a1 : Space} {τ : ℝ}
    (ha : HasDerivAt a a1 τ) : HasDerivAt (fun s => ⟪m, a s⟫) ⟪m, a1⟫ τ := by
  simpa using (hasDerivAt_const τ m).inner ℝ ha

/-- `d/dτ G₁(u)[a] = G₂(u)[a, u'] + G₁(u)[a']`. -/
theorem hasDerivAt_kg1_gen (m : Space) {u a : ℝ → Space} {u1 a1 : Space} {τ : ℝ}
    (hu : HasDerivAt u u1 τ) (ha : HasDerivAt a a1 τ) (h0 : u τ ≠ 0) :
    HasDerivAt (fun s => kg1 m (u s) (a s)) (kG2 m (u τ) (a τ) u1 + kg1 m (u τ) a1) τ := by
  have hA := hasDerivAt_inner_const m ha
  have hM := hasDerivAt_inner_const m hu
  have hC : HasDerivAt (fun s => ⟪u s, a s⟫) (⟪u τ, a1⟫ + ⟪u1, a τ⟫) τ := hu.inner ℝ ha
  have h3 := hasDerivAt_norm_inv_pow hu h0 2
  have h5 := hasDerivAt_norm_inv_pow hu h0 4
  have h := HasDerivAt.fun_sub (HasDerivAt.fun_mul hA h3)
    (HasDerivAt.fun_mul (HasDerivAt.fun_mul (hM.const_mul 3) hC) h5)
  simp only [kg1]
  refine h.congr_deriv ?_
  simp only [kG2]
  have hpos : 0 < ‖u τ‖ := norm_pos_iff.mpr h0
  rw [real_inner_comm u1 (a τ)]
  push_cast
  field_simp
  ring

/-- `d/dτ G₂(u)[a, b] = G₃(u)[a, b, u'] + G₂(u)[a', b] + G₂(u)[a, b']`. -/
theorem hasDerivAt_kG2 (m : Space) {u a b : ℝ → Space} {u1 a1 b1 : Space} {τ : ℝ}
    (hu : HasDerivAt u u1 τ) (ha : HasDerivAt a a1 τ) (hb : HasDerivAt b b1 τ) (h0 : u τ ≠ 0) :
    HasDerivAt (fun s => kG2 m (u s) (a s) (b s))
      (kG3 m (u τ) (a τ) (b τ) u1 + kG2 m (u τ) a1 (b τ) + kG2 m (u τ) (a τ) b1) τ := by
  have hMa := hasDerivAt_inner_const m ha
  have hMb := hasDerivAt_inner_const m hb
  have hMx := hasDerivAt_inner_const m hu
  have hXa : HasDerivAt (fun s => ⟪u s, a s⟫) (⟪u τ, a1⟫ + ⟪u1, a τ⟫) τ := hu.inner ℝ ha
  have hXb : HasDerivAt (fun s => ⟪u s, b s⟫) (⟪u τ, b1⟫ + ⟪u1, b τ⟫) τ := hu.inner ℝ hb
  have hab : HasDerivAt (fun s => ⟪a s, b s⟫) (⟪a τ, b1⟫ + ⟪a1, b τ⟫) τ := ha.inner ℝ hb
  have h5 := hasDerivAt_norm_inv_pow hu h0 4
  have h7 := hasDerivAt_norm_inv_pow hu h0 6
  have hS : HasDerivAt (fun s => ⟪u s, b s⟫ * ⟪m, a s⟫ + ⟪u s, a s⟫ * ⟪m, b s⟫ +
      ⟪a s, b s⟫ * ⟪m, u s⟫) _ τ :=
    HasDerivAt.fun_add (HasDerivAt.fun_add (HasDerivAt.fun_mul hXb hMa) (HasDerivAt.fun_mul hXa
        hMb))
      (HasDerivAt.fun_mul hab hMx)
  have h := HasDerivAt.fun_add (HasDerivAt.fun_mul (hS.const_mul (-3)) h5)
    (HasDerivAt.fun_mul (HasDerivAt.fun_mul (HasDerivAt.fun_mul (hXa.const_mul 15) hXb) hMx) h7)
  simp only [kG2]
  refine h.congr_deriv ?_
  simp only [kG3]
  have hpos : 0 < ‖u τ‖ := norm_pos_iff.mpr h0
  rw [real_inner_comm u1 (a τ), real_inner_comm u1 (b τ)]
  push_cast
  field_simp
  ring

/-- `d/dτ G₃(u)[u', u', u'] = G₄(u)[u'⁴] + 3 G₃(u)[u'', u', u']`. -/
theorem hasDerivAt_kG3d (m : Space) {u a : ℝ → Space} {a1 : Space} {τ : ℝ}
    (hu : HasDerivAt u (a τ) τ) (ha : HasDerivAt a a1 τ) (h0 : u τ ≠ 0) :
    HasDerivAt (fun s => kG3 m (u s) (a s) (a s) (a s))
      (kG4d m (u τ) (a τ) + 3 * kG3 m (u τ) a1 (a τ) (a τ)) τ := by
  have hMa := hasDerivAt_inner_const m ha
  have hMx := hasDerivAt_inner_const m hu
  have hXa : HasDerivAt (fun s => ⟪u s, a s⟫) (⟪u τ, a1⟫ + ⟪a τ, a τ⟫) τ := hu.inner ℝ ha
  have haa : HasDerivAt (fun s => ⟪a s, a s⟫) (⟪a τ, a1⟫ + ⟪a1, a τ⟫) τ := ha.inner ℝ ha
  have h5 := hasDerivAt_norm_inv_pow hu h0 4
  have h7 := hasDerivAt_norm_inv_pow hu h0 6
  have h9 := hasDerivAt_norm_inv_pow hu h0 8
  -- `G₃[a, a, a] = -9 A Mₐ r⁻⁵ + 45 (X² Mₐ + A X Mₓ) r⁻⁷ - 105 X³ Mₓ r⁻⁹`
  have e : (fun s => kG3 m (u s) (a s) (a s) (a s)) = fun s =>
      -9 * (⟪a s, a s⟫ * ⟪m, a s⟫) * (‖u s‖ ^ 5)⁻¹ +
        45 * (⟪u s, a s⟫ * ⟪u s, a s⟫ * ⟪m, a s⟫ + ⟪a s, a s⟫ * ⟪u s, a s⟫ * ⟪m, u s⟫) *
          (‖u s‖ ^ 7)⁻¹ -
        105 * (⟪u s, a s⟫ * ⟪u s, a s⟫ * ⟪u s, a s⟫ * ⟪m, u s⟫) * (‖u s‖ ^ 9)⁻¹ := by
    funext s; unfold kG3; ring
  rw [e]
  have t1 := HasDerivAt.fun_mul ((HasDerivAt.fun_mul haa hMa).const_mul (-9)) h5
  have t2 := HasDerivAt.fun_mul ((HasDerivAt.fun_add
    (HasDerivAt.fun_mul (HasDerivAt.fun_mul hXa hXa) hMa)
    (HasDerivAt.fun_mul (HasDerivAt.fun_mul haa hXa) hMx)).const_mul 45) h7
  have t3 := HasDerivAt.fun_mul ((HasDerivAt.fun_mul (HasDerivAt.fun_mul
    (HasDerivAt.fun_mul hXa hXa) hXa) hMx).const_mul 105) h9
  refine (HasDerivAt.fun_sub (HasDerivAt.fun_add t1 t2) t3).congr_deriv ?_
  unfold kG4d kG3
  have hpos : 0 < ‖u τ‖ := norm_pos_iff.mpr h0
  rw [real_inner_comm a1 (a τ), real_inner_self_eq_norm_sq]
  push_cast
  field_simp
  ring

/-- Symmetry of `G₂`. -/
theorem kG2_comm (m x a b : Space) : kG2 m x a b = kG2 m x b a := by
  unfold kG2; rw [real_inner_comm a b]; ring

/-- Symmetry of `G₃` (the permutations used below). -/
theorem kG3_perm (m x a b c : Space) : kG3 m x a b c = kG3 m x b c a ∧ kG3 m x a b c = kG3 m x b a
    c := by
  unfold kG3
  constructor
  · rw [real_inner_comm a c, real_inner_comm a b]; ring
  · rw [real_inner_comm a b]; ring

/-- **Third derivative of the kernel** along a curve: `d/dτ g'' = g'''`. -/
theorem hasDerivAt_g2 (m : Space) {u u1 u2 : ℝ → Space} {u3 : Space} {τ : ℝ}
    (hu : HasDerivAt u (u1 τ) τ) (hu1 : HasDerivAt u1 (u2 τ) τ) (hu2 : HasDerivAt u2 u3 τ)
    (h0 : u τ ≠ 0) :
    HasDerivAt (fun s => kG2 m (u s) (u1 s) (u1 s) + kg1 m (u s) (u2 s))
      (kgD3 m (u τ) (u1 τ) (u2 τ) u3) τ := by
  have h1 := hasDerivAt_kG2 m hu hu1 hu1 h0
  have h2 := hasDerivAt_kg1_gen m hu hu2 h0
  refine (HasDerivAt.fun_add h1 h2).congr_deriv ?_
  unfold kgD3
  rw [kG2_comm m (u τ) (u2 τ) (u1 τ), kG2_comm m (u τ) (u1 τ) (u2 τ)]
  ring

/-- `kg2` in terms of the forms. -/
theorem kg2_eq (m u u1 u2 : Space) : kg2 m u u1 u2 = kG2 m u u1 u1 + kg1 m u u2 := by
  unfold kg2 kG2 kg1
  rw [real_inner_self_eq_norm_sq]
  ring

/-- **Fourth derivative of the kernel** along a curve: `d/dτ g''' = g⁗`. -/
theorem hasDerivAt_g3 (m : Space) {u u1 u2 u3 : ℝ → Space} {u4 : Space} {τ : ℝ}
    (hu : HasDerivAt u (u1 τ) τ) (hu1 : HasDerivAt u1 (u2 τ) τ) (hu2 : HasDerivAt u2 (u3 τ) τ)
    (hu3 : HasDerivAt u3 u4 τ) (h0 : u τ ≠ 0) :
    HasDerivAt (fun s => kgD3 m (u s) (u1 s) (u2 s) (u3 s))
      (kgD4 m (u τ) (u1 τ) (u2 τ) (u3 τ) u4) τ := by
  have h1 := hasDerivAt_kG3d m hu hu1 h0
  have h2 := hasDerivAt_kG2 m hu hu1 hu2 h0
  have h3 := hasDerivAt_kg1_gen m hu hu3 h0
  unfold kgD3
  refine (HasDerivAt.fun_add (HasDerivAt.fun_add h1 (h2.const_mul 3)) h3).congr_deriv ?_
  unfold kgD4
  have p1 := (kG3_perm m (u τ) (u2 τ) (u1 τ) (u1 τ)).1
  have p2 := (kG3_perm m (u τ) (u1 τ) (u2 τ) (u1 τ)).2
  have p3 := (kG3_perm m (u τ) (u1 τ) (u1 τ) (u2 τ)).1
  rw [kG2_comm m (u τ) (u3 τ) (u1 τ)]
  linarith

/-! ## Line bounds -/

/-- `|⟨m, αx + βa⟩| ≤ |m| B` once `|αx + βa|² ≤ B²`. -/
theorem abs_inner_comb_le (m x a : Space) {α β B : ℝ} (hB : 0 ≤ B)
    (h : α ^ 2 * ‖x‖ ^ 2 + 2 * α * β * ⟪x, a⟫ + β ^ 2 * ‖a‖ ^ 2 ≤ B ^ 2) :
    |⟪m, α • x + β • a⟫| ≤ ‖m‖ * B := by
  refine (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  rw [← norm_comb_sq] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hB two_ne_zero).mp h

/-- Cauchy–Schwarz in the form `⟨x, a⟩² ≤ |x|²|a|²`. -/
theorem inner_sq_le (x a : Space) : ⟪x, a⟫ ^ 2 ≤ ‖x‖ ^ 2 * ‖a‖ ^ 2 := by
  have := abs_real_inner_le_norm x a
  have h2 := sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2
  simpa [mul_pow] using h2

/-- **Line bound, `j = 1`**: `|G₁(x)[a]| ≤ 2|m||a|/|x|³`. -/
theorem abs_kg1_le (m x a : Space) (hx : x ≠ 0) : |kg1 m x a| ≤ ‖m‖ * (2 * ‖a‖ / ‖x‖ ^ 3) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set r := ‖x‖
  set c := ⟪x, a⟫
  have e : kg1 m x a = ⟪m, (-3 * c / r ^ 5) • x + (1 / r ^ 3) • a⟫ := by
    simp only [kg1, inner_add_right, inner_smul_right, c, r]; field_simp; ring
  rw [e]
  refine abs_inner_comb_le m x a (by positivity) ?_
  have hcs := inner_sq_le x a
  have key : (2 * ‖a‖ / r ^ 3) ^ 2 - ((-3 * c / r ^ 5) ^ 2 * r ^ 2 +
      2 * (-3 * c / r ^ 5) * (1 / r ^ 3) * c + (1 / r ^ 3) ^ 2 * ‖a‖ ^ 2) =
      3 * (r ^ 2 * ‖a‖ ^ 2 - c ^ 2) / r ^ 8 := by field_simp; ring
  have : 0 ≤ 3 * (r ^ 2 * ‖a‖ ^ 2 - c ^ 2) / r ^ 8 := by
    apply div_nonneg _ (by positivity); linarith
  linarith

/-- **Line bound, `j = 2`**: `|G₂(x)[a, a]| ≤ 6|m||a|²/|x|⁴`. -/
theorem abs_kG2d_le (m x a : Space) (hx : x ≠ 0) : |kG2 m x a a| ≤ ‖m‖ *
    (6 * ‖a‖ ^ 2 / ‖x‖ ^ 4) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set r := ‖x‖
  set c := ⟪x, a⟫
  have e : kG2 m x a a = ⟪m, ((15 * c ^ 2 - 3 * ‖a‖ ^ 2 * r ^ 2) / r ^ 7) • x + (-6 * c / r ^ 5) •
      a⟫
      := by
    simp only [kG2, inner_add_right, inner_smul_right, c, r]
    rw [real_inner_self_eq_norm_sq]; field_simp; ring
  rw [e]
  refine abs_inner_comb_le m x a (by positivity) ?_
  have hcs := inner_sq_le x a
  have key : (6 * ‖a‖ ^ 2 / r ^ 4) ^ 2 - (((15 * c ^ 2 - 3 * ‖a‖ ^ 2 * r ^ 2) / r ^ 7) ^ 2 * r ^ 2 +
      2 * ((15 * c ^ 2 - 3 * ‖a‖ ^ 2 * r ^ 2) / r ^ 7) * (-6 * c / r ^ 5) * c +
      (-6 * c / r ^ 5) ^ 2 * ‖a‖ ^ 2) =
      9 * (r ^ 2 * ‖a‖ ^ 2 - c ^ 2) * (3 * ‖a‖ ^ 2 * r ^ 2 + 5 * c ^ 2) / r ^ 12 := by
    field_simp; ring
  have : 0 ≤ 9 * (r ^ 2 * ‖a‖ ^ 2 - c ^ 2) * (3 * ‖a‖ ^ 2 * r ^ 2 + 5 * c ^ 2) / r ^ 12 := by
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)
  linarith

/-- **Line bound, `j = 3`**: `|G₃(x)[a, a, a]| ≤ 24|m||a|³/|x|⁵`. -/
theorem abs_kG3d_le (m x a : Space) (hx : x ≠ 0) :
    |kG3 m x a a a| ≤ ‖m‖ * (24 * ‖a‖ ^ 3 / ‖x‖ ^ 5) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set r := ‖x‖
  set c := ⟪x, a⟫
  set A := ‖a‖ ^ 2
  have e : kG3 m x a a a = ⟪m, ((45 * A * c * r ^ 2 - 105 * c ^ 3) / r ^ 9) • x +
      ((45 * c ^ 2 - 9 * A * r ^ 2) / r ^ 7) • a⟫ := by
    simp only [kG3, inner_add_right, inner_smul_right, c, r, A]
    rw [real_inner_self_eq_norm_sq]; field_simp; ring
  rw [e]
  refine abs_inner_comb_le m x a (by positivity) ?_
  have hcs := inner_sq_le x a
  have hA : ‖a‖ ^ 2 = A := rfl
  have key : (24 * ‖a‖ ^ 3 / r ^ 5) ^ 2 - (((45 * A * c * r ^ 2 - 105 * c ^ 3) / r ^ 9) ^ 2 * r ^
      2 +
      2 * ((45 * A * c * r ^ 2 - 105 * c ^ 3) / r ^ 9) * ((45 * c ^ 2 - 9 * A * r ^ 2) / r ^ 7) *
          c +
      ((45 * c ^ 2 - 9 * A * r ^ 2) / r ^ 7) ^ 2 * ‖a‖ ^ 2) =
      45 * (r ^ 2 * A - c ^ 2) * (11 * A ^ 2 * r ^ 4 + 2 * A * c ^ 2 * r ^ 2 + 35 * c ^ 4) / r ^
      16 := by
    have h6 : ‖a‖ ^ 6 = A ^ 3 := by rw [← hA]; ring
    rw [div_pow, mul_pow, show (‖a‖ ^ 3) ^ 2 = ‖a‖ ^ 6 by ring, h6, hA]
    field_simp; ring
  have : 0 ≤ 45 * (r ^ 2 * A - c ^ 2) * (11 * A ^ 2 * r ^ 4 + 2 * A * c ^ 2 * r ^ 2 + 35 * c ^ 4) /
      r ^ 16 := by
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)
  linarith

/-- **Line bound, `j = 4`**: `|G₄(x)[a, a, a, a]| ≤ 120|m||a|⁴/|x|⁶`. -/
theorem abs_kG4d_le (m x a : Space) (hx : x ≠ 0) :
    |kG4d m x a| ≤ ‖m‖ * (120 * ‖a‖ ^ 4 / ‖x‖ ^ 6) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set r := ‖x‖
  set c := ⟪x, a⟫
  set A := ‖a‖ ^ 2
  have hA : ‖a‖ ^ 2 = A := rfl
  have h4 : ‖a‖ ^ 4 = A ^ 2 := by rw [← hA]; ring
  have e : kG4d m x a = ⟪m, (45 * (A ^ 2 * r ^ 4 - 14 * A * c ^ 2 * r ^ 2 + 21 * c ^ 4) / r ^ 11) •
      x +
      (60 * c * (3 * A * r ^ 2 - 7 * c ^ 2) / r ^ 9) • a⟫ := by
    simp only [kG4d, inner_add_right, inner_smul_right, c, r]
    rw [h4, hA]; field_simp
  rw [e, h4]
  refine abs_inner_comb_le m x a (by positivity) ?_
  have hcs := inner_sq_le x a
  rw [hA] at hcs ⊢
  have key : (120 * A ^ 2 / r ^ 6) ^ 2 -
      ((45 * (A ^ 2 * r ^ 4 - 14 * A * c ^ 2 * r ^ 2 + 21 * c ^ 4) / r ^ 11) ^ 2 * r ^ 2 +
      2 * (45 * (A ^ 2 * r ^ 4 - 14 * A * c ^ 2 * r ^ 2 + 21 * c ^ 4) / r ^ 11) *
        (60 * c * (3 * A * r ^ 2 - 7 * c ^ 2) / r ^ 9) * c +
      (60 * c * (3 * A * r ^ 2 - 7 * c ^ 2) / r ^ 9) ^ 2 * A) =
      225 * (r ^ 2 * A - c ^ 2) * (55 * A ^ 3 * r ^ 6 + 91 * A ^ 2 * c ^ 2 * r ^ 4 -
        203 * A * c ^ 4 * r ^ 2 + 441 * c ^ 6) / r ^ 20 := by
    field_simp; ring
  have hP : 0 ≤ 55 * A ^ 3 * r ^ 6 + 91 * A ^ 2 * c ^ 2 * r ^ 4 - 203 * A * c ^ 4 * r ^ 2 +
      441 * c ^ 6 := by
    have hA0 : 0 ≤ A := by positivity
    set P := A * r ^ 2
    have hP0 : 0 ≤ P := by positivity
    set Y := c ^ 2
    have hY0 : 0 ≤ Y := sq_nonneg _
    have e2 : 55 * A ^ 3 * r ^ 6 + 91 * A ^ 2 * c ^ 2 * r ^ 4 - 203 * A * c ^ 4 * r ^ 2 +
        441 * c ^ 6 = 55 * P ^ 3 + Y * (91 * P ^ 2 - 203 * P * Y + 441 * Y ^ 2) := by
      simp only [P, Y]; ring
    rw [e2]
    have : 0 ≤ 91 * P ^ 2 - 203 * P * Y + 441 * Y ^ 2 := by
      nlinarith [sq_nonneg (182 * P - 203 * Y), sq_nonneg Y]
    positivity
  have : 0 ≤ 225 * (r ^ 2 * A - c ^ 2) * (55 * A ^ 3 * r ^ 6 + 91 * A ^ 2 * c ^ 2 * r ^ 4 -
        203 * A * c ^ 4 * r ^ 2 + 441 * c ^ 6) / r ^ 20 := by
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hP
  linarith

/-! ## Polarization -/

/-- Bilinearity of `G₂` under opposite scalings. -/
theorem kG2_scale (m x a b : Space) {l : ℝ} (hl : l ≠ 0) : kG2 m x a b = kG2 m x (l • a)
    (l⁻¹ • b) := by
  simp only [kG2, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  field_simp

/-- Polarization identity for `G₂`. -/
theorem kG2_polar (m x a b : Space) :
    kG2 m x a b = (kG2 m x (a + b) (a + b) - kG2 m x (a - b) (a - b)) / 4 := by
  simp only [kG2, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  rw [real_inner_comm b a]
  ring

/-- **Polarization bound for `G₂`**: `|G₂[a, b]| ≤ 3|m|(λ²|a|² + |b|²/λ²)/|x|⁴`. -/
theorem abs_kG2_le (m x a b : Space) (hx : x ≠ 0) {l : ℝ} (hl : 0 < l) :
    |kG2 m x a b| ≤ ‖m‖ * (3 * (l ^ 2 * ‖a‖ ^ 2 + ‖b‖ ^ 2 / l ^ 2) / ‖x‖ ^ 4) := by
  rw [kG2_scale m x a b hl.ne', kG2_polar]
  set a' := l • a
  set b' := l⁻¹ • b
  have h1 := abs_kG2d_le m x (a' + b') hx
  have h2 := abs_kG2d_le m x (a' - b') hx
  have hpar : ‖a' + b'‖ ^ 2 + ‖a' - b'‖ ^ 2 = 2 * (‖a'‖ ^ 2 + ‖b'‖ ^ 2) := by
    rw [norm_add_sq_real, norm_sub_sq_real]; ring
  have ha' : ‖a'‖ ^ 2 = l ^ 2 * ‖a‖ ^ 2 := by
    simp only [a', norm_smul, Real.norm_eq_abs, abs_of_pos hl]; ring
  have hb' : ‖b'‖ ^ 2 = ‖b‖ ^ 2 / l ^ 2 := by
    simp only [b', norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hl]; field_simp
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have := abs_sub (kG2 m x (a' + b') (a' + b')) (kG2 m x (a' - b') (a' - b'))
  have hm := norm_nonneg m
  calc |kG2 m x (a' + b') (a' + b') - kG2 m x (a' - b') (a' - b')| / 4
      ≤ (‖m‖ * (6 * ‖a' + b'‖ ^ 2 / ‖x‖ ^ 4) + ‖m‖ * (6 * ‖a' - b'‖ ^ 2 / ‖x‖ ^ 4)) / 4 := by
        gcongr; linarith
    _ = ‖m‖ * (3 * (l ^ 2 * ‖a‖ ^ 2 + ‖b‖ ^ 2 / l ^ 2) / ‖x‖ ^ 4) := by
        rw [← ha', ← hb']
        have : 6 * ‖a' + b'‖ ^ 2 / ‖x‖ ^ 4 + 6 * ‖a' - b'‖ ^ 2 / ‖x‖ ^ 4 =
            12 * (‖a'‖ ^ 2 + ‖b'‖ ^ 2) / ‖x‖ ^ 4 := by
          rw [← add_div, ← mul_add, hpar]; ring
        rw [← mul_add, this]; ring

/-- Polarization identity for `G₃[a, a, b]`. -/
theorem kG3_polar (m x a b : Space) (s : ℝ) :
    6 * s * kG3 m x a a b = kG3 m x (a + s • b) (a + s • b) (a + s • b) -
      kG3 m x (a - s • b) (a - s • b) (a - s • b) - 2 * s ^ 3 * kG3 m x b b b := by
  simp only [kG3, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  rw [real_inner_comm b a]
  ring

/-- **Polarization bound for `G₃[a, a, b]` with `a ⊥ b`**:
`|G₃[a, a, b]| ≤ (1001/1000)·24|m| A²B/|x|⁵` for `|a| ≤ A`, `|b| ≤ B`. -/
theorem abs_kG3_perp_le (m x a b : Space) (hx : x ≠ 0) (hab : ⟪a, b⟫ = 0) {A B : ℝ} (hA : 0 < A)
    (hB : 0 < B) (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) :
    |kG3 m x a a b| ≤ ‖m‖ * (1002 / 1000 * 24 * A ^ 2 * B / ‖x‖ ^ 5) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set s := 3 / 5 * A / B with hs
  have hs0 : 0 < s := by positivity
  have hpol := kG3_polar m x a b s
  have hsb : ‖s • b‖ ≤ 3 / 5 * A := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
    calc s * ‖b‖ ≤ s * B := mul_le_mul_of_nonneg_left hb hs0.le
      _ = 3 / 5 * A := by simp only [hs]; field_simp
  have hnorm : ∀ v : Space, (v = a + s • b ∨ v = a - s • b) → ‖v‖ ≤ 5831 / 5000 * A := by
    intro v hv
    have hsq : ‖v‖ ^ 2 = ‖a‖ ^ 2 + ‖s • b‖ ^ 2 := by
      rcases hv with rfl | rfl
      · rw [norm_add_sq_real, inner_smul_right, hab]; ring
      · rw [norm_sub_sq_real, inner_smul_right, hab]; ring
    have h1 : ‖v‖ ^ 2 ≤ (5831 / 5000 * A) ^ 2 := by
      rw [hsq]
      have := pow_le_pow_left₀ (norm_nonneg _) ha 2
      have := pow_le_pow_left₀ (norm_nonneg _) hsb 2
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h1
  have hp := abs_kG3d_le m x (a + s • b) hx
  have hq := abs_kG3d_le m x (a - s • b) hx
  have hbb := abs_kG3d_le m x b hx
  have hv1 := hnorm _ (Or.inl rfl)
  have hv2 := hnorm _ (Or.inr rfl)
  have c1 : ‖a + s • b‖ ^ 3 ≤ (5831 / 5000 * A) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hv1 3
  have c2 : ‖a - s • b‖ ^ 3 ≤ (5831 / 5000 * A) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hv2 3
  have c3 : s ^ 3 * ‖b‖ ^ 3 ≤ (3 / 5 * A) ^ 3 := by
    rw [← mul_pow]
    have : s * ‖b‖ ≤ 3 / 5 * A := by
      calc s * ‖b‖ ≤ s * B := mul_le_mul_of_nonneg_left hb hs0.le
        _ = 3 / 5 * A := by simp only [hs]; field_simp
    exact pow_le_pow_left₀ (by positivity) this 3
  have hm := norm_nonneg m
  have h6 : |6 * s * kG3 m x a a b| ≤ ‖m‖ * (24 / ‖x‖ ^ 5) *
      (‖a + s • b‖ ^ 3 + ‖a - s • b‖ ^ 3 + 2 * (s ^ 3 * ‖b‖ ^ 3)) := by
    rw [hpol]
    have e1 : ‖m‖ * (24 * ‖a + s • b‖ ^ 3 / ‖x‖ ^ 5) = ‖m‖ * (24 / ‖x‖ ^ 5) * ‖a + s • b‖ ^ 3 := by
      ring
    have e2 : ‖m‖ * (24 * ‖a - s • b‖ ^ 3 / ‖x‖ ^ 5) = ‖m‖ * (24 / ‖x‖ ^ 5) * ‖a - s • b‖ ^ 3 := by
      ring
    have e3 : ‖m‖ * (24 * ‖b‖ ^ 3 / ‖x‖ ^ 5) = ‖m‖ * (24 / ‖x‖ ^ 5) * ‖b‖ ^ 3 := by ring
    rw [e1] at hp; rw [e2] at hq; rw [e3] at hbb
    have hs3 : 0 ≤ 2 * s ^ 3 := by positivity
    calc |kG3 m x (a + s • b) (a + s • b) (a + s • b) -
            kG3 m x (a - s • b) (a - s • b) (a - s • b) - 2 * s ^ 3 * kG3 m x b b b|
        ≤ |kG3 m x (a + s • b) (a + s • b) (a + s • b)| +
          |kG3 m x (a - s • b) (a - s • b) (a - s • b)| + 2 * s ^ 3 * |kG3 m x b b b| := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_of_nonneg hs3]
          exact add_le_add (abs_sub _ _) le_rfl
      _ ≤ ‖m‖ * (24 / ‖x‖ ^ 5) * ‖a + s • b‖ ^ 3 + ‖m‖ * (24 / ‖x‖ ^ 5) * ‖a - s • b‖ ^ 3 +
          2 * s ^ 3 * (‖m‖ * (24 / ‖x‖ ^ 5) * ‖b‖ ^ 3) := by
          gcongr
      _ = _ := by ring
  have hK : 0 ≤ ‖m‖ * (24 / ‖x‖ ^ 5) := by positivity
  have hfin : ‖m‖ * (24 / ‖x‖ ^ 5) * (‖a + s • b‖ ^ 3 + ‖a - s • b‖ ^ 3 + 2 * (s ^ 3 * ‖b‖ ^ 3)) ≤
      ‖m‖ * (24 / ‖x‖ ^ 5) * (2 * (5831 / 5000 * A) ^ 3 + 2 * (3 / 5 * A) ^ 3) := by
    apply mul_le_mul_of_nonneg_left _ hK; linarith
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 6 * s)] at h6
  have hfin2 : 6 * s * |kG3 m x a a b| ≤ 6 * s *
      (‖m‖ * (1002 / 1000 * 24 * A ^ 2 * B / ‖x‖ ^ 5)) := by
    refine h6.trans (hfin.trans (le_of_eq_of_le rfl ?_))
    simp only [hs]
    rw [show 6 * (3 / 5 * A / B) * (‖m‖ * (1002 / 1000 * 24 * A ^ 2 * B / ‖x‖ ^ 5)) =
      ‖m‖ * (24 / ‖x‖ ^ 5) * (A ^ 3 * (6 * (3 / 5) * (1002 / 1000))) by field_simp]
    apply mul_le_mul_of_nonneg_left _ hK
    nlinarith [pow_pos hA 3]
  exact le_of_mul_le_mul_left hfin2 (by positivity)

/-- Linearity of `G₃` in its last argument. -/
theorem kG3_last_comb (m x a b : Space) (α : ℝ) :
    kG3 m x a a b = α * kG3 m x a a a + kG3 m x a a (b - α • a) := by
  simp only [kG3, inner_sub_right, inner_smul_right]
  ring

/-- **Fourth derivative of the kernel along a curve**: with `u₂ = αu₁ + u₂^⊥`, `u₂^⊥ ⊥ u₁`,
and bounds on `|u₁|, |u₂^⊥|, |u₂|, |u₃|, |u₄|`. -/
theorem abs_kgD4_le (m x u1 u2 u3 u4 : Space) (hx : x ≠ 0) {S1 Sp S2 S3 S4 α l : ℝ}
    (hS1p : 0 < S1) (hSpp : 0 < Sp) (hl : 0 < l) (hS1 : ‖u1‖ ≤ S1)
    (hperp : ⟪u1, u2 - α • u1⟫ = 0) (hSp : ‖u2 - α • u1‖ ≤ Sp) (hS2 : ‖u2‖ ≤ S2)
    (hS3 : ‖u3‖ ≤ S3) (hS4 : ‖u4‖ ≤ S4) :
    |kgD4 m x u1 u2 u3 u4| ≤ ‖m‖ * (120 * S1 ^ 4 / ‖x‖ ^ 6 +
      6 * (24 * |α| * S1 ^ 3 + 1002 / 1000 * 24 * S1 ^ 2 * Sp) / ‖x‖ ^ 5 +
      12 * (l ^ 2 * S1 ^ 2 + S3 ^ 2 / l ^ 2) / ‖x‖ ^ 4 + 18 * S2 ^ 2 / ‖x‖ ^ 4 +
      2 * S4 / ‖x‖ ^ 3) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hm := norm_nonneg m
  have t1 := abs_kG4d_le m x u1 hx
  have t2a := abs_kG3d_le m x u1 hx
  have t2b := abs_kG3_perp_le m x u1 (u2 - α • u1) hx hperp hS1p hSpp hS1 hSp
  have t3 := abs_kG2_le m x u1 u3 hx hl
  have t4 := abs_kG2d_le m x u2 hx
  have t5 := abs_kg1_le m x u4 hx
  have p1 : ‖u1‖ ^ 4 ≤ S1 ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hS1 4
  have p2 : ‖u1‖ ^ 3 ≤ S1 ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hS1 3
  have p3 : ‖u1‖ ^ 2 ≤ S1 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hS1 2
  have p4 : ‖u3‖ ^ 2 ≤ S3 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hS3 2
  have p5 : ‖u2‖ ^ 2 ≤ S2 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hS2 2
  have q1 : ‖m‖ * (120 * ‖u1‖ ^ 4 / ‖x‖ ^ 6) ≤ ‖m‖ * (120 * S1 ^ 4 / ‖x‖ ^ 6) := by gcongr
  have q2 : ‖m‖ * (24 * ‖u1‖ ^ 3 / ‖x‖ ^ 5) ≤ ‖m‖ * (24 * S1 ^ 3 / ‖x‖ ^ 5) := by gcongr
  have q3 : ‖m‖ * (3 * (l ^ 2 * ‖u1‖ ^ 2 + ‖u3‖ ^ 2 / l ^ 2) / ‖x‖ ^ 4) ≤
      ‖m‖ * (3 * (l ^ 2 * S1 ^ 2 + S3 ^ 2 / l ^ 2) / ‖x‖ ^ 4) := by gcongr
  have q4 : ‖m‖ * (6 * ‖u2‖ ^ 2 / ‖x‖ ^ 4) ≤ ‖m‖ * (6 * S2 ^ 2 / ‖x‖ ^ 4) := by gcongr
  have q5 : ‖m‖ * (2 * ‖u4‖ / ‖x‖ ^ 3) ≤ ‖m‖ * (2 * S4 / ‖x‖ ^ 3) := by gcongr
  have h3 : |kG3 m x u1 u1 u2| ≤ |α| * (‖m‖ * (24 * S1 ^ 3 / ‖x‖ ^ 5)) +
      ‖m‖ * (1002 / 1000 * 24 * S1 ^ 2 * Sp / ‖x‖ ^ 5) := by
    rw [kG3_last_comb m x u1 u2 α]
    refine (abs_add_le _ _).trans (add_le_add ?_ t2b)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (t2a.trans q2) (abs_nonneg _)
  unfold kgD4
  have hsum : |kG4d m x u1 + 6 * kG3 m x u1 u1 u2 + 4 * kG2 m x u1 u3 + 3 * kG2 m x u2 u2 +
      kg1 m x u4| ≤ |kG4d m x u1| + 6 * |kG3 m x u1 u1 u2| + 4 * |kG2 m x u1 u3| +
        3 * |kG2 m x u2 u2| + |kg1 m x u4| := by
    have := abs_add_le (kG4d m x u1 + 6 * kG3 m x u1 u1 u2 + 4 * kG2 m x u1 u3 + 3 * kG2 m x u2 u2)
      (kg1 m x u4)
    have := abs_add_le (kG4d m x u1 + 6 * kG3 m x u1 u1 u2 + 4 * kG2 m x u1 u3) (3 * kG2 m x u2 u2)
    have := abs_add_le (kG4d m x u1 + 6 * kG3 m x u1 u1 u2) (4 * kG2 m x u1 u3)
    have := abs_add_le (kG4d m x u1) (6 * kG3 m x u1 u1 u2)
    rw [abs_mul 6, abs_mul 4, abs_mul 3] at *
    norm_num at *
    linarith
  refine hsum.trans ?_
  have e : ‖m‖ * (120 * S1 ^ 4 / ‖x‖ ^ 6 +
      6 * (24 * |α| * S1 ^ 3 + 1002 / 1000 * 24 * S1 ^ 2 * Sp) / ‖x‖ ^ 5 +
      12 * (l ^ 2 * S1 ^ 2 + S3 ^ 2 / l ^ 2) / ‖x‖ ^ 4 + 18 * S2 ^ 2 / ‖x‖ ^ 4 +
      2 * S4 / ‖x‖ ^ 3) = ‖m‖ * (120 * S1 ^ 4 / ‖x‖ ^ 6) +
      6 * (|α| * (‖m‖ * (24 * S1 ^ 3 / ‖x‖ ^ 5)) +
        ‖m‖ * (1002 / 1000 * 24 * S1 ^ 2 * Sp / ‖x‖ ^ 5)) +
      4 * (‖m‖ * (3 * (l ^ 2 * S1 ^ 2 + S3 ^ 2 / l ^ 2) / ‖x‖ ^ 4)) +
      3 * (‖m‖ * (6 * S2 ^ 2 / ‖x‖ ^ 4)) + ‖m‖ * (2 * S4 / ‖x‖ ^ 3) := by ring
  rw [e]
  linarith [t1.trans q1, t3.trans q3, t4.trans q4, t5.trans q5]

/-- **Fourth derivative along a line** (`u₂ = u₃ = u₄ = 0`): `|g⁗| ≤ 120|m||u₁|⁴/|u|⁶`. -/
theorem abs_kgD4_line (m x u1 : Space) (hx : x ≠ 0) :
    |kgD4 m x u1 0 0 0| ≤ ‖m‖ * (120 * ‖u1‖ ^ 4 / ‖x‖ ^ 6) := by
  have e : kgD4 m x u1 0 0 0 = kG4d m x u1 := by
    simp [kgD4, kG3, kG2, kg1]
  rw [e]; exact abs_kG4d_le m x u1 hx

/-! ## Segment fields along curves: the cubic remainder -/

/-- The cubic interpolant in Lagrange form is linear: interpolating integrals. -/
theorem newt_integral {x0 x1 x2 x3 : ℝ} (h01 : x0 < x1) (h12 : x1 < x2) (h23 : x2 < x3)
    (f0 f1 f2 f3 : ℝ → ℝ) (hf0 : IntervalIntegrable f0 MeasureTheory.volume 0 1)
    (hf1 : IntervalIntegrable f1 MeasureTheory.volume 0 1)
    (hf2 : IntervalIntegrable f2 MeasureTheory.volume 0 1)
    (hf3 : IntervalIntegrable f3 MeasureTheory.volume 0 1) (y : ℝ) :
    newt x0 x1 x2 x3 (∫ t in (0 : ℝ)..1, f0 t) (∫ t in (0 : ℝ)..1, f1 t) (∫ t in (0 : ℝ)..1, f2 t)
      (∫ t in (0 : ℝ)..1, f3 t) y =
    ∫ t in (0 : ℝ)..1, newt x0 x1 x2 x3 (f0 t) (f1 t) (f2 t) (f3 t) y := by
  simp_rw [newt_lagrange h01 h12 h23]
  rw [intervalIntegral.integral_add (((hf0.const_mul _).add (hf1.const_mul _)).add (hf2.const_mul
      _))
      (hf3.const_mul _), intervalIntegral.integral_add ((hf0.const_mul _).add (hf1.const_mul _))
      (hf2.const_mul _), intervalIntegral.integral_add (hf0.const_mul _) (hf1.const_mul _)]
  simp only [intervalIntegral.integral_const_mul]

/-- **Cubic interpolation bound for the field of a segment along a curve.** If the curve `σ`
(four derivatives on `[x₀, x₃]`) stays at distance `≥ d > 0` from the segment `p → q` and the
fourth derivative of the kernel is bounded by `|n||q - p| K` there, then for `y ∈ [x₁, x₂]` the
cubic interpolation error of `τ ↦ ⟨n, F(σ τ)⟩` is at most `|κ||n||q - p| K |ω(y)|/24`. -/
theorem segField_cubic_bound (μ₀ I : ℝ) (p q n : Space) {σ σ1 σ2 σ3 σ4 : ℝ → Space}
    {x0 x1 x2 x3 y d K : ℝ} (h01 : x0 < x1) (h12 : x1 < x2) (h23 : x2 < x3) (hy : y ∈ Icc x1 x2)
    (hd : 0 < d)
    (hσ : ∀ τ ∈ Icc x0 x3, HasDerivAt σ (σ1 τ) τ) (hσ1 : ∀ τ ∈ Icc x0 x3, HasDerivAt σ1 (σ2 τ) τ)
    (hσ2 : ∀ τ ∈ Icc x0 x3, HasDerivAt σ2 (σ3 τ) τ) (hσ3 : ∀ τ ∈ Icc x0 x3, HasDerivAt σ3 (σ4 τ) τ)
    (hsep : ∀ τ ∈ Icc x0 x3, ∀ t ∈ Icc (0 : ℝ) 1, d ≤ ‖σ τ - seg p q t‖)
    (hK : ∀ τ ∈ Icc x0 x3, ∀ t ∈ Icc (0 : ℝ) 1,
      |kgD4 (cross n (q - p)) (σ τ - seg p q t) (σ1 τ) (σ2 τ) (σ3 τ) (σ4 τ)| ≤
        ‖n‖ * ‖q - p‖ * K) :
    |⟪n, filamentField μ₀ I (seg p q) 0 1 (σ y)⟫ -
        newt x0 x1 x2 x3 ⟪n, filamentField μ₀ I (seg p q) 0 1 (σ x0)⟫
          ⟪n, filamentField μ₀ I (seg p q) 0 1 (σ x1)⟫ ⟪n, filamentField μ₀ I (seg p q) 0 1 (σ x2)⟫
          ⟪n, filamentField μ₀ I (seg p q) 0 1 (σ x3)⟫ y| ≤
      |μ₀ * I / (4 * Real.pi)| * (‖n‖ * ‖q - p‖ * K) * |omega4 x0 x1 x2 x3 y| / 24 := by
  set κ := μ₀ * I / (4 * Real.pi)
  set m := cross n (q - p)
  have h01' : (0 : ℝ) ≤ 1 := zero_le_one
  have hcont : ∀ z : Space, (∀ t ∈ Icc (0 : ℝ) 1, d ≤ ‖z - seg p q t‖) →
      ContinuousOn (fun t => kg m (z - seg p q t)) (Icc 0 1) := by
    intro z hz
    unfold kg
    have hc : Continuous (fun t => z - seg p q t) := continuous_const.sub (continuous_seg p q)
    refine (continuous_const.inner hc).continuousOn.mul ?_
    refine (hc.norm.pow 3).continuousOn.inv₀ fun t ht => ?_
    exact pow_ne_zero _ (lt_of_lt_of_le hd (hz t ht)).ne'
  have hF : ∀ z : Space, (∀ t ∈ Icc (0 : ℝ) 1, d ≤ ‖z - seg p q t‖) →
      ⟪n, filamentField μ₀ I (seg p q) 0 1 z⟫ = κ * ∫ t in (0 : ℝ)..1, kg m (z - seg p q t) := by
    intro z hz
    unfold filamentField
    have hdc : deriv (seg p q) = fun _ => q - p := funext (deriv_seg p q)
    have hint : IntervalIntegrable (fun t => filamentKernel (seg p q) t z) MeasureTheory.volume 0
        1 := by
      refine (filamentKernel_continuousOn (seg p q) z (uIcc 0 1) (continuous_seg p q).continuousOn
        (by rw [hdc]; exact continuousOn_const) fun t ht => ?_).intervalIntegrable
      rw [uIcc_of_le h01'] at ht
      exact norm_pos_iff.mp (lt_of_lt_of_le hd (hz t ht))
    have hcomm := (innerSL ℝ n).intervalIntegral_comp_comm hint
    simp only [innerSL_apply_apply] at hcomm
    rw [inner_smul_right, ← hcomm]
    simp_rw [inner_seg_kernel]
    rfl
  have hI : ∀ z : Space, (∀ t ∈ Icc (0 : ℝ) 1, d ≤ ‖z - seg p q t‖) →
      IntervalIntegrable (fun t => kg m (z - seg p q t)) MeasureTheory.volume 0 1 := by
    intro z hz
    have : ContinuousOn (fun t => kg m (z - seg p q t)) (uIcc 0 1) := by
      rw [uIcc_of_le h01']; exact hcont z hz
    exact this.intervalIntegrable
  have m0 : x0 ∈ Icc x0 x3 := ⟨le_rfl, by linarith⟩
  have m1 : x1 ∈ Icc x0 x3 := ⟨h01.le, by linarith⟩
  have m2 : x2 ∈ Icc x0 x3 := ⟨by linarith, h23.le⟩
  have m3 : x3 ∈ Icc x0 x3 := ⟨by linarith, le_rfl⟩
  have my : y ∈ Icc x0 x3 := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  rw [hF _ (hsep _ m0), hF _ (hsep _ m1), hF _ (hsep _ m2), hF _ (hsep _ m3), hF _ (hsep _ my)]
  have hlin : ∀ a0 a1 a2 a3 : ℝ, newt x0 x1 x2 x3 (κ * a0) (κ * a1) (κ * a2) (κ * a3) y =
      κ * newt x0 x1 x2 x3 a0 a1 a2 a3 y := by
    intro a0 a1 a2 a3; unfold newt dd3 dd2; ring
  rw [hlin, newt_integral h01 h12 h23 _ _ _ _ (hI _ (hsep _ m0)) (hI _ (hsep _ m1))
    (hI _ (hsep _ m2)) (hI _ (hsep _ m3)), ← mul_sub,
    ← intervalIntegral.integral_sub (hI _ (hsep _ my)), abs_mul]
  swap
  · -- integrability of the interpolant
    have : ContinuousOn (fun t => newt x0 x1 x2 x3 (kg m (σ x0 - seg p q t)) (kg m (σ x1 - seg p q
        t))
        (kg m (σ x2 - seg p q t)) (kg m (σ x3 - seg p q t)) y) (uIcc 0 1) := by
      rw [uIcc_of_le h01']
      simp_rw [newt_lagrange h01 h12 h23]
      exact (((continuousOn_const.mul (hcont _ (hsep _ m0))).add
        (continuousOn_const.mul (hcont _ (hsep _ m1)))).add
        (continuousOn_const.mul (hcont _ (hsep _ m2)))).add
        (continuousOn_const.mul (hcont _ (hsep _ m3)))
    exact this.intervalIntegrable
  have hpt : ∀ t ∈ uIoc (0 : ℝ) 1,
      ‖kg m (σ y - seg p q t) - newt x0 x1 x2 x3 (kg m (σ x0 - seg p q t)) (kg m (σ x1 - seg p q t))
        (kg m (σ x2 - seg p q t)) (kg m (σ x3 - seg p q t)) y‖ ≤
      ‖n‖ * ‖q - p‖ * K * |omega4 x0 x1 x2 x3 y| / 24 := by
    intro t ht
    rw [uIoc_of_le h01'] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    rw [Real.norm_eq_abs]
    have hne : ∀ τ ∈ Icc x0 x3, σ τ - seg p q t ≠ 0 := fun τ hτ =>
      norm_pos_iff.mp (lt_of_lt_of_le hd (hsep τ hτ t ht'))
    refine newt_interp_bound (g := fun τ => kg m (σ τ - seg p q t))
      (g1 := fun τ => kg1 m (σ τ - seg p q t) (σ1 τ))
      (g2 := fun τ => kG2 m (σ τ - seg p q t) (σ1 τ) (σ1 τ) + kg1 m (σ τ - seg p q t) (σ2 τ))
      (g3 := fun τ => kgD3 m (σ τ - seg p q t) (σ1 τ) (σ2 τ) (σ3 τ))
      (g4 := fun τ => kgD4 m (σ τ - seg p q t) (σ1 τ) (σ2 τ) (σ3 τ) (σ4 τ)) h01 h12 h23 hy
      ?_ ?_ ?_ ?_ (fun τ hτ => hK τ hτ t ht')
    · intro τ hτ
      exact hasDerivAt_kg m ((hσ τ hτ).sub_const _) (hne τ hτ)
    · intro τ hτ
      exact hasDerivAt_kg1_gen m (u := fun s => σ s - seg p q t) ((hσ τ hτ).sub_const _)
        (hσ1 τ hτ) (hne τ hτ)
    · intro τ hτ
      exact hasDerivAt_g2 m (u := fun s => σ s - seg p q t) ((hσ τ hτ).sub_const _) (hσ1 τ hτ)
        (hσ2 τ hτ) (hne τ hτ)
    · intro τ hτ
      exact hasDerivAt_g3 m (u := fun s => σ s - seg p q t) ((hσ τ hτ).sub_const _) (hσ1 τ hτ)
        (hσ2 τ hτ) (hσ3 τ hτ) (hne τ hτ)
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [Real.norm_eq_abs, sub_zero, abs_one, mul_one] at hint
  calc |κ| * |∫ t in (0 : ℝ)..1, (kg m (σ y - seg p q t) - newt x0 x1 x2 x3
        (kg m (σ x0 - seg p q t)) (kg m (σ x1 - seg p q t)) (kg m (σ x2 - seg p q t))
        (kg m (σ x3 - seg p q t)) y)|
      ≤ |κ| * (‖n‖ * ‖q - p‖ * K * |omega4 x0 x1 x2 x3 y| / 24) :=
        mul_le_mul_of_nonneg_left hint (abs_nonneg _)
    _ = _ := by ring

end PlasmaLean.Design.PolygonCoil
