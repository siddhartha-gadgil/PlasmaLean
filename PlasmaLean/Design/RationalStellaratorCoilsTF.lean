/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellarator
public import PlasmaLean.Theory.Fields.BiotSavart
public import PlasmaLean.Theory.Fields.FilamentSmooth

/-!
# A closed filament for the line-current part of the rational stellarator field

The field `field (1/4) = ∇φ + (1/4)∇h` of `Design/RationalStellarator` contains `∇φ`, the field of
an infinite straight current on the `z`-axis. This module realises it by a **closed** filament:
the rectangle `tfLoop` with corners `(0, 0, ∓Λ)`, `(Λ, 0, ±Λ)`, `Λ = 10⁶` (current up the
`z`-axis, return far away), carrying `μ₀ I = 2π` (units `B₀ = R₀ = 1`). Its Biot–Savart field
`tfField` (the sum of the four straight-segment filament fields `Fields.filamentField`) satisfies

* `tfField_error`: `‖tfField x - ∇φ(x)‖ ≤ 1/400000` (`2.5 × 10⁻⁶`) at every point of the
  region `|x| ≤ 11/10` horizontally, `|z| ≤ 1/10` with `x² + y² ≥ 4/5`, which contains the
  confinement tube `T` of `RationalStellaratorConfined`.

Method: the axis segment is integrated exactly (antiderivative of `(ρ² + u²)^(-3/2)`,
`axisSeg_eq`), giving `∇φ` times `(cos θ₁ + cos θ₂)/2` with an explicit end correction
`≤ (11/10)/(2(Λ - 1/10)²)`; the three return segments are bounded crudely by
`Fields.filamentField_bound` (distance `≥ Λ - 11/10`), `≈ 2/Λ` in total.

Scope: thin-filament Biot–Savart model; the closure at `10⁶ R₀` is a mathematical device (a
physical machine would use several symmetric returns at moderate distance, whose error decays
like a power of `R₀/D` but is not certified here).
-/

public section
noncomputable section

namespace PlasmaLean.Design.RationalStellarator.CoilsTF
open PlasmaLean.Design.RationalStellarator PlasmaLean.Fields

/-- The straight segment from `p` to `q`, parametrised by `t ∈ [0, 1]`. -/
@[expose] def seg (p q : Space) (t : ℝ) : Space := p + t • (q - p)

/-- Derivative of a segment. -/
theorem hasDerivAt_seg (p q : Space) (t : ℝ) : HasDerivAt (seg p q) (q - p) t := by
  have := ((hasDerivAt_id t).smul_const (q - p)).const_add p
  simp only [id, one_smul] at this
  exact this

/-- The tangent of a segment is constant. -/
theorem deriv_seg (p q : Space) (t : ℝ) : deriv (seg p q) t = q - p :=
  (hasDerivAt_seg p q t).deriv

/-- Segments are continuous. -/
theorem continuous_seg (p q : Space) : Continuous (seg p q) := by
  unfold seg; fun_prop

/-- Field of a straight segment carrying `μ₀ I = 2π` (so `μ₀ I/(4π) = 1/2`). -/
@[expose] def segField (p q : Space) (x : Space) : Space :=
  filamentField 1 (2 * Real.pi) (seg p q) 0 1 x

/-- The closure distance `Λ = 10⁶`. -/
@[expose] def Λ : ℝ := 10 ^ 6

/-- Lower corner on the axis `(0, 0, -Λ)`. -/
@[expose] def P0 : Space := WithLp.toLp 2 ![0, 0, -Λ]
/-- Upper corner on the axis `(0, 0, Λ)`. -/
@[expose] def P1 : Space := WithLp.toLp 2 ![0, 0, Λ]
/-- Upper far corner `(Λ, 0, Λ)`. -/
@[expose] def P2 : Space := WithLp.toLp 2 ![Λ, 0, Λ]
/-- Lower far corner `(Λ, 0, -Λ)`. -/
@[expose] def P3 : Space := WithLp.toLp 2 ![Λ, 0, -Λ]

/-- **The field of the closed rectangular filament** `P0 → P1 → P2 → P3 → P0`. -/
@[expose] def tfField (x : Space) : Space :=
  segField P0 P1 x + segField P1 P2 x + segField P2 P3 x + segField P3 P0 x

/-- The rectangle is closed: the four segments chain end to start. -/
theorem tfLoop_closed : seg P0 P1 1 = seg P1 P2 0 ∧ seg P1 P2 1 = seg P2 P3 0 ∧
    seg P2 P3 1 = seg P3 P0 0 ∧ seg P3 P0 1 = seg P0 P1 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [seg]

/-! ## The observation region -/

/-- The observation region: `4/5 ≤ x² + y² ≤ 6/5`, `|z| ≤ 1/10` (contains the tube `T`). -/
@[expose] def obsRegion : Set Space := {x | 4 / 5 ≤ r2 x ∧ r2 x ≤ 6 / 5 ∧ |x 2| ≤ 1 / 10}

/-- Horizontal coordinates are at most `11/10` in the observation region. -/
theorem coord_le {x : Space} (hx : x ∈ obsRegion) : |x 0| ≤ 11 / 10 ∧ |x 1| ≤ 11 / 10 := by
  have h := hx.2.1
  have hr : r2 x = x 0 ^ 2 + x 1 ^ 2 := rfl
  constructor <;> apply abs_le_of_sq_le_sq _ (by norm_num) <;> nlinarith [sq_nonneg (x 0),
    sq_nonneg (x 1)]

/-! ## The axis segment, integrated exactly -/

/-- The antiderivative `u / (ρ² √(ρ² + u²))` with `u = 2Λt - Λ - z`. -/
@[expose] def axisF (ρ2 z t : ℝ) : ℝ :=
  (2 * Λ * t - Λ - z) / (ρ2 * Real.sqrt (ρ2 + (2 * Λ * t - Λ - z) ^ 2))

/-- The scalar integrand `2Λ / (√(ρ² + u²))³`. -/
@[expose] def axisf (ρ2 z t : ℝ) : ℝ :=
  2 * Λ / Real.sqrt (ρ2 + (2 * Λ * t - Λ - z) ^ 2) ^ 3

/-- `axisF' = axisf`. -/
theorem hasDerivAt_axisF {ρ2 : ℝ} (hρ : 0 < ρ2) (z t : ℝ) :
    HasDerivAt (axisF ρ2 z) (axisf ρ2 z t) t := by
  have hq : 0 < ρ2 + (2 * Λ * t - Λ - z) ^ 2 := by positivity
  have hu : HasDerivAt (fun t => 2 * Λ * t - Λ - z) (2 * Λ) t := by
    simpa using (((hasDerivAt_id t).const_mul (2 * Λ)).sub_const Λ).sub_const z
  have hsq : HasDerivAt (fun t => ρ2 + (2 * Λ * t - Λ - z) ^ 2)
      (2 * (2 * Λ * t - Λ - z) * (2 * Λ)) t := by
    have := (hu.pow 2).const_add ρ2
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  have hs := hsq.sqrt hq.ne'
  have hden := hs.const_mul ρ2
  have hsqrt_pos : 0 < Real.sqrt (ρ2 + (2 * Λ * t - Λ - z) ^ 2) := Real.sqrt_pos.mpr hq
  have hd := hu.div hden (by positivity)
  have h2 : Real.sqrt (ρ2 + (2 * Λ * t - Λ - z) ^ 2) ^ 2 = ρ2 + (2 * Λ * t - Λ - z) ^ 2 :=
    Real.sq_sqrt hq.le
  unfold axisF axisf
  convert hd using 1
  generalize Real.sqrt (ρ2 + (2 * Λ * t - Λ - z) ^ 2) = S at h2 hsqrt_pos ⊢
  generalize 2 * Λ * t - Λ - z = w at h2 ⊢
  have hρ2 : ρ2 = S ^ 2 - w ^ 2 := by linarith
  subst hρ2
  have hne : S ^ 2 - w ^ 2 ≠ 0 := by linarith
  field_simp

/-- The integrand is continuous. -/
theorem continuous_axisf {ρ2 : ℝ} (hρ : 0 < ρ2) (z : ℝ) : Continuous (axisf ρ2 z) := by
  unfold axisf
  refine Continuous.div continuous_const (by fun_prop) fun t => ?_
  have : 0 < ρ2 + (2 * Λ * t - Λ - z) ^ 2 := by positivity
  exact pow_ne_zero _ (Real.sqrt_pos.mpr this).ne'

/-- The vector `(-y, x, 0)`. -/
@[expose] def Vt (x : Space) : Space := WithLp.toLp 2 ![-x 1, x 0, 0]

/-- The axis kernel is the scalar integrand times `(-y, x, 0)`. -/
theorem axis_kernel (x : Space) (t : ℝ) :
    filamentKernel (seg P0 P1) t x = axisf (r2 x) (x 2) t • Vt x := by
  have hc : seg P0 P1 t = WithLp.toLp 2 ![0, 0, 2 * Λ * t - Λ] := by
    ext i; fin_cases i <;> simp [seg, P0, P1]; ring
  have hn : ‖x - seg P0 P1 t‖ = Real.sqrt (r2 x + (2 * Λ * t - Λ - x 2) ^ 2) := by
    rw [EuclideanSpace.norm_eq, hc, Fin.sum_univ_three]
    congr 1
    simp [r2]; ring
  unfold filamentKernel axisf
  rw [deriv_seg, hn, hc]
  ext i
  fin_cases i <;> simp [cross, Vt, P0, P1, crossProduct, div_eq_mul_inv, Matrix.vecHead,
    Matrix.vecTail] <;> ring

/-- **Exact field of the axis segment**: `(1/2)(F(1) - F(0)) (-y, x, 0)`. -/
theorem axisSeg_eq (x : Space) (hx : 0 < r2 x) :
    segField P0 P1 x = ((1 / 2) * (axisF (r2 x) (x 2) 1 - axisF (r2 x) (x 2) 0)) • Vt x := by
  unfold segField filamentField
  simp_rw [axis_kernel]
  rw [intervalIntegral.integral_smul_const,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_axisF hx (x 2) t)
      ((continuous_axisf hx (x 2)).intervalIntegrable 0 1), smul_smul]
  congr 1
  field_simp
  ring

/-- End correction: `0 ≤ 1/ρ² - a/(ρ² √(ρ² + a²)) ≤ 1/(2a²)` for `a > 0`. -/
theorem end_correction {ρ2 a : ℝ} (hρ : 0 < ρ2) (ha : 0 < a) :
    0 ≤ 1 / ρ2 - a / (ρ2 * Real.sqrt (ρ2 + a ^ 2)) ∧
      1 / ρ2 - a / (ρ2 * Real.sqrt (ρ2 + a ^ 2)) ≤ 1 / (2 * a ^ 2) := by
  set q := Real.sqrt (ρ2 + a ^ 2)
  have hq2 : q ^ 2 = ρ2 + a ^ 2 := Real.sq_sqrt (by positivity)
  have hq0 : 0 < q := Real.sqrt_pos.mpr (by positivity)
  have hqa : a ≤ q := by nlinarith
  have heq : 1 / ρ2 - a / (ρ2 * q) = 1 / (q * (q + a)) := by
    field_simp
    nlinarith
  rw [heq]
  constructor
  · positivity
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

/-- The axis segment differs from `∇φ` by at most `(11/10) / (2(Λ - 1/10)²)`. -/
theorem axisSeg_error {x : Space} (hx : x ∈ obsRegion) :
    ‖segField P0 P1 x - toroidal x‖ ≤ 11 / 10 / (2 * (Λ - 1 / 10) ^ 2) := by
  obtain ⟨h1, h2, h3⟩ := hx
  have hρ : 0 < r2 x := by linarith
  have hz := abs_le.mp h3
  have hΛ : (1 : ℝ) ≤ Λ := by norm_num [Λ]
  have ha : 0 < Λ - x 2 := by linarith
  have hb : 0 < Λ + x 2 := by linarith
  have htor : toroidal x = (1 / r2 x) • Vt x := by
    ext i; fin_cases i <;> simp [toroidal, Vt, winv] <;> ring
  rw [axisSeg_eq x hρ, htor, ← sub_smul, norm_smul, Real.norm_eq_abs]
  have hF1 : axisF (r2 x) (x 2) 1 = (Λ - x 2) / (r2 x * Real.sqrt (r2 x + (Λ - x 2) ^ 2)) := by
    unfold axisF; ring_nf
  have hF0 : axisF (r2 x) (x 2) 0 = -((Λ + x 2) / (r2 x * Real.sqrt (r2 x + (Λ + x 2) ^ 2))) := by
    unfold axisF
    rw [show 2 * Λ * 0 - Λ - x 2 = -(Λ + x 2) by ring, neg_sq, neg_div]
  obtain ⟨a0, a1⟩ := end_correction hρ ha
  obtain ⟨b0, b1⟩ := end_correction hρ hb
  have hV : ‖Vt x‖ ≤ 11 / 10 := by
    have : ‖Vt x‖ ^ 2 = r2 x := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]; simp [Vt, r2]; ring
    nlinarith [norm_nonneg (Vt x)]
  have hsa : 1 / (2 * (Λ - x 2) ^ 2) ≤ 1 / (2 * (Λ - 1 / 10) ^ 2) := by
    apply one_div_le_one_div_of_le (by nlinarith)
    nlinarith
  have hsb : 1 / (2 * (Λ + x 2) ^ 2) ≤ 1 / (2 * (Λ - 1 / 10) ^ 2) := by
    apply one_div_le_one_div_of_le (by nlinarith)
    nlinarith
  have hcoef : |1 / 2 * (axisF (r2 x) (x 2) 1 - axisF (r2 x) (x 2) 0) - 1 / r2 x| ≤
      1 / (2 * (Λ - 1 / 10) ^ 2) := by
    rw [hF1, hF0, abs_le]
    constructor <;> nlinarith
  have hpos : (0 : ℝ) ≤ 1 / (2 * (Λ - 1 / 10) ^ 2) := by positivity
  calc |1 / 2 * (axisF (r2 x) (x 2) 1 - axisF (r2 x) (x 2) 0) - 1 / r2 x| * ‖Vt x‖
      ≤ 1 / (2 * (Λ - 1 / 10) ^ 2) * (11 / 10) :=
        mul_le_mul hcoef hV (norm_nonneg _) hpos
    _ = 11 / 10 / (2 * (Λ - 1 / 10) ^ 2) := by ring

/-! ## The return segments, bounded crudely -/

/-- Crude bound for a straight segment at distance `≥ d` from `x`, of length `≤ V`:
`‖segField p q x‖ ≤ V/(2d²)`. -/
theorem segField_bound (p q x : Space) {d V : ℝ} (hd : 0 < d)
    (hsep : ∀ t ∈ Set.Icc (0 : ℝ) 1, d ≤ ‖x - seg p q t‖) (hV : ‖q - p‖ ≤ V) :
    ‖segField p q x‖ ≤ V / (2 * d ^ 2) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hne : ∀ t ∈ Set.uIcc (0 : ℝ) 1, x - seg p q t ≠ 0 := by
    intro t ht
    rw [Set.uIcc_of_le h01] at ht
    exact norm_pos_iff.mp (lt_of_lt_of_le hd (hsep t ht))
  have hdc : deriv (seg p q) = fun _ => q - p := funext (deriv_seg p q)
  have hcont := filamentKernel_continuousOn (seg p q) x (Set.uIcc 0 1)
    (continuous_seg p q).continuousOn (by rw [hdc]; exact continuousOn_const) hne
  have hsep' : ∀ t ∈ Set.uIoc (0 : ℝ) 1, d ≤ ‖x - seg p q t‖ := by
    intro t ht
    rw [Set.uIoc_of_le h01] at ht
    exact hsep t ⟨ht.1.le, ht.2⟩
  have hb := filamentField_bound 1 (2 * Real.pi) (seg p q) 0 1 x (V := V) hd
    hcont.intervalIntegrable
    hsep' (fun t _ => by rw [deriv_seg]; exact hV)
  have hc : |1 * (2 * Real.pi) / (4 * Real.pi)| = 1 / 2 := by
    rw [abs_of_pos (by positivity)]; field_simp; norm_num
  change ‖filamentField 1 (2 * Real.pi) (seg p q) 0 1 x‖ ≤ _
  rw [hc] at hb
  calc _ ≤ 1 / 2 * (V / d ^ 2 * |1 - 0|) := hb
    _ = V / (2 * d ^ 2) := by rw [sub_zero, abs_one]; ring

/-- `|w i| ≤ ‖w‖`. -/
theorem abs_coord_le (w : Space) (i : Fin 3) : |w i| ≤ ‖w‖ := by
  have := PiLp.norm_apply_le w i
  rwa [Real.norm_eq_abs] at this

/-- The norm from the coordinates. -/
theorem norm_of_coords {v : Space} {a b c : ℝ} (h0 : v 0 = a) (h1 : v 1 = b) (h2 : v 2 = c) :
    ‖v‖ = Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, h0, h1, h2]
  simp only [Real.norm_eq_abs, sq_abs]

/-- Top segment `P1 → P2` (at height `Λ`). -/
theorem top_bound {x : Space} (hx : x ∈ obsRegion) :
    ‖segField P1 P2 x‖ ≤ Λ / (2 * (Λ - 1 / 10) ^ 2) := by
  have hz := abs_le.mp hx.2.2
  have hΛ : (1 : ℝ) ≤ Λ := by norm_num [Λ]
  refine segField_bound P1 P2 x (by linarith) (fun t _ => ?_) (le_of_eq ?_)
  · have := abs_coord_le (x - seg P1 P2 t) 2
    have e : (x - seg P1 P2 t) 2 = x 2 - Λ := by simp [seg, P1, P2]
    rw [e, abs_sub_comm, abs_of_pos (by linarith)] at this
    linarith
  · rw [norm_of_coords (a := Λ) (b := 0) (c := 0) (by simp [P1, P2]) (by simp [P1, P2])
      (by simp [P1, P2])]
    rw [show Λ ^ 2 + 0 ^ 2 + 0 ^ 2 = Λ ^ 2 by ring, Real.sqrt_sq (by linarith)]

/-- Far return segment `P2 → P3` (at `x = Λ`). -/
theorem far_bound {x : Space} (hx : x ∈ obsRegion) :
    ‖segField P2 P3 x‖ ≤ 2 * Λ / (2 * (Λ - 11 / 10) ^ 2) := by
  have hx0 := abs_le.mp (coord_le hx).1
  have hΛ : (2 : ℝ) ≤ Λ := by norm_num [Λ]
  refine segField_bound P2 P3 x (by linarith) (fun t _ => ?_) (le_of_eq ?_)
  · have := abs_coord_le (x - seg P2 P3 t) 0
    have e : (x - seg P2 P3 t) 0 = x 0 - Λ := by simp [seg, P2, P3]
    rw [e, abs_sub_comm, abs_of_pos (by linarith)] at this
    linarith
  · rw [norm_of_coords (a := 0) (b := 0) (c := -(2 * Λ)) (by simp [P2, P3]) (by simp [P2, P3])
      (by simp [P2, P3]; ring)]
    rw [show (0 : ℝ) ^ 2 + 0 ^ 2 + (-(2 * Λ)) ^ 2 = (2 * Λ) ^ 2 by ring, Real.sqrt_sq (by linarith)]

/-- Bottom segment `P3 → P0` (at height `-Λ`). -/
theorem bottom_bound {x : Space} (hx : x ∈ obsRegion) :
    ‖segField P3 P0 x‖ ≤ Λ / (2 * (Λ - 1 / 10) ^ 2) := by
  have hz := abs_le.mp hx.2.2
  have hΛ : (1 : ℝ) ≤ Λ := by norm_num [Λ]
  refine segField_bound P3 P0 x (by linarith) (fun t _ => ?_) (le_of_eq ?_)
  · have := abs_coord_le (x - seg P3 P0 t) 2
    have e : (x - seg P3 P0 t) 2 = x 2 + Λ := by simp [seg, P3, P0]
    rw [e, abs_of_pos (by linarith)] at this
    linarith
  · rw [norm_of_coords (a := -Λ) (b := 0) (c := 0) (by simp [P3, P0]) (by simp [P3, P0])
      (by simp [P3, P0])]
    rw [show (-Λ) ^ 2 + 0 ^ 2 + 0 ^ 2 = Λ ^ 2 by ring, Real.sqrt_sq (by linarith)]

/-- The TF closure error bound `ζ = 1/400000 = 2.5 × 10⁻⁶`. -/
@[expose] def ζ : ℝ := 1 / 400000

/-- **The closed rectangular filament reproduces `∇φ` to `2.5 × 10⁻⁶`** on the observation
region (which contains the confinement tube). -/
theorem tfField_error {x : Space} (hx : x ∈ obsRegion) : ‖tfField x - toroidal x‖ ≤ ζ := by
  have e : tfField x - toroidal x = (segField P0 P1 x - toroidal x) + segField P1 P2 x +
      segField P2 P3 x + segField P3 P0 x := by unfold tfField; abel
  rw [e]
  have h1 := axisSeg_error hx
  have h2 := top_bound hx
  have h3 := far_bound hx
  have h4 := bottom_bound hx
  have hnum : 11 / 10 / (2 * (Λ - 1 / 10) ^ 2) + Λ / (2 * (Λ - 1 / 10) ^ 2) +
      2 * Λ / (2 * (Λ - 11 / 10) ^ 2) + Λ / (2 * (Λ - 1 / 10) ^ 2) ≤ ζ := by
    norm_num [Λ, ζ]
  calc _ ≤ ‖segField P0 P1 x - toroidal x + segField P1 P2 x + segField P2 P3 x‖ +
        ‖segField P3 P0 x‖ := norm_add_le _ _
    _ ≤ ‖segField P0 P1 x - toroidal x + segField P1 P2 x‖ + ‖segField P2 P3 x‖ +
        ‖segField P3 P0 x‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖segField P0 P1 x - toroidal x‖ + ‖segField P1 P2 x‖ + ‖segField P2 P3 x‖ +
        ‖segField P3 P0 x‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by linarith

end PlasmaLean.Design.RationalStellarator.CoilsTF
