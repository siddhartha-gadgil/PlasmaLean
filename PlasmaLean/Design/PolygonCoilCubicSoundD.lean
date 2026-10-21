/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCubicSoundC

/-!
# Soundness of the cubic checker, part D: one cell

* `corr4_sound`: the divided-difference corrections of `⟨n, E⟩` on a `4`-node stencil are bounded
  by `corr4/2⁴⁰`, computed from the rounded vectors `Ê` (with their rounding errors);
* `leb4_sound`: `leb4 C ≥ (1 + 2(B₀ + B₃)) C`;
* `cell_sound4` (**cell bound**): if the `16` stencil records carry their value bounds, the four
  `w`-remainders of column `1` and the `t`-remainder of the corner `(1, 1)` are valid, and
  `cellOK4` accepts, then `‖Bseg - hel‖ ≤ η·2⁻⁴⁰` on the whole cell.
-/

public section
noncomputable section

namespace PlasmaLean.Design.PolygonCoil
open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator
  PlasmaLean.Design.RationalStellarator.Coils PlasmaLean.Design.RationalStellarator.CoilsTF Set Real
open scoped RealInnerProductSpace

/-! ## Rounded vectors -/

/-- A record carries a rounded version of the vector `e` (scale `2⁴⁰`, componentwise error
`ρ`). -/
@[expose] def BoxOK (v : CRec) (e : Space) : Prop :=
  |e 0 * ((two40 : ℕ) : ℝ) - v.ex| ≤ v.rho ∧ |e 1 * ((two40 : ℕ) : ℝ) - v.ey| ≤ v.rho ∧
    |e 2 * ((two40 : ℕ) : ℝ) - v.ez| ≤ v.rho

/-- The Euclidean norm is at most the `ℓ¹` norm. -/
theorem norm_le_l1 (v : Space) : ‖v‖ ≤ |v 0| + |v 1| + |v 2| := by
  have h : ‖v‖ ^ 2 ≤ (|v 0| + |v 1| + |v 2|) ^ 2 := by
    rw [norm_sq_coords]
    nlinarith [abs_nonneg (v 0), abs_nonneg (v 1), abs_nonneg (v 2), sq_abs (v 0), sq_abs (v 1),
      sq_abs (v 2), mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 1)),
      mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 2)),
      mul_nonneg (abs_nonneg (v 1)) (abs_nonneg (v 2))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

/-- Cast of `l1`. -/
theorem l1_cast (x y z : ℤ) : ((l1 x y z : ℕ) : ℝ) = |(x : ℝ)| + |(y : ℝ)| + |(z : ℝ)| := by
  unfold l1; push_cast [Nat.add_eq, iabs_cast]; rfl

/-- A linear combination of three rounded vectors with integer coefficients. -/
theorem comb3_bound {n : Space} (hn : ‖n‖ ≤ 1) {e0 e1 e2 : Space} {v0 v1 v2 : CRec}
    (h0 : BoxOK v0 e0) (h1 : BoxOK v1 e1) (h2 : BoxOK v2 e2) (c0 c1 c2 : ℤ) :
    |(c0 : ℝ) * ⟪n, e0⟫ + c1 * ⟪n, e1⟫ + c2 * ⟪n, e2⟫| * ((two40 : ℕ) : ℝ) ≤
      (l1 (c0 * v0.ex + c1 * v1.ex + c2 * v2.ex) (c0 * v0.ey + c1 * v1.ey + c2 * v2.ey)
        (c0 * v0.ez + c1 * v1.ez + c2 * v2.ez) : ℝ) +
      3 * ((iabs c0 : ℝ) * v0.rho + (iabs c1 : ℝ) * v1.rho + (iabs c2 : ℝ) * v2.rho) := by
  set V := (c0 : ℝ) • e0 + (c1 : ℝ) • e1 + (c2 : ℝ) • e2
  have hV : (c0 : ℝ) * ⟪n, e0⟫ + c1 * ⟪n, e1⟫ + c2 * ⟪n, e2⟫ = ⟪n, V⟫ := by
    simp only [V, inner_add_right, inner_smul_right]
  rw [hV]
  have h40 : (0 : ℝ) < ((two40 : ℕ) : ℝ) := by norm_num [two40]
  have hnV : |⟪n, V⟫| ≤ ‖V‖ := (abs_real_inner_le_norm _ _).trans
    (by nlinarith [norm_nonneg V, norm_nonneg n])
  refine (mul_le_mul_of_nonneg_right (hnV.trans (norm_le_l1 V)) h40.le).trans ?_
  have comp : ∀ (k : Fin 3) (a0 a1 a2 : ℤ), |e0 k * ((two40 : ℕ) : ℝ) - a0| ≤ v0.rho →
      |e1 k * ((two40 : ℕ) : ℝ) - a1| ≤ v1.rho → |e2 k * ((two40 : ℕ) : ℝ) - a2| ≤ v2.rho →
      |V k| * ((two40 : ℕ) : ℝ) ≤ |((c0 * a0 + c1 * a1 + c2 * a2 : ℤ) : ℝ)| +
        ((iabs c0 : ℝ) * v0.rho + (iabs c1 : ℝ) * v1.rho + (iabs c2 : ℝ) * v2.rho) := by
    intro k a0 a1 a2 b0 b1 b2
    have eV : V k * ((two40 : ℕ) : ℝ) = (c0 : ℝ) * (e0 k * ((two40 : ℕ) : ℝ)) +
        c1 * (e1 k * ((two40 : ℕ) : ℝ)) + c2 * (e2 k * ((two40 : ℕ) : ℝ)) := by
      simp only [V, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    have ea : |V k| * ((two40 : ℕ) : ℝ) = |V k * ((two40 : ℕ) : ℝ)| := by
      rw [abs_mul, abs_of_pos h40]
    rw [ea, eV]
    have ed : (c0 : ℝ) * (e0 k * ((two40 : ℕ) : ℝ)) + c1 * (e1 k * ((two40 : ℕ) : ℝ)) +
        c2 * (e2 k * ((two40 : ℕ) : ℝ)) = ((c0 * a0 + c1 * a1 + c2 * a2 : ℤ) : ℝ) +
        ((c0 : ℝ) * (e0 k * ((two40 : ℕ) : ℝ) - a0) + c1 * (e1 k * ((two40 : ℕ) : ℝ) - a1) +
          c2 * (e2 k * ((two40 : ℕ) : ℝ) - a2)) := by push_cast; ring
    rw [ed]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    refine (abs_add_le _ _).trans ?_
    refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
    rw [abs_mul, abs_mul, abs_mul, iabs_cast, iabs_cast, iabs_cast]
    have := mul_le_mul_of_nonneg_left b0 (abs_nonneg (c0 : ℝ))
    have := mul_le_mul_of_nonneg_left b1 (abs_nonneg (c1 : ℝ))
    have := mul_le_mul_of_nonneg_left b2 (abs_nonneg (c2 : ℝ))
    linarith
  have k0 := comp 0 v0.ex v1.ex v2.ex h0.1 h1.1 h2.1
  have k1 := comp 1 v0.ey v1.ey v2.ey h0.2.1 h1.2.1 h2.2.1
  have k2 := comp 2 v0.ez v1.ez v2.ez h0.2.2 h1.2.2 h2.2.2
  rw [l1_cast]
  rw [add_mul, add_mul]
  linarith

/-- A linear combination of four rounded vectors with integer coefficients. -/
theorem comb4_bound {n : Space} (hn : ‖n‖ ≤ 1) {e0 e1 e2 e3 : Space} {v0 v1 v2 v3 : CRec}
    (h0 : BoxOK v0 e0) (h1 : BoxOK v1 e1) (h2 : BoxOK v2 e2) (h3 : BoxOK v3 e3) (c0 c1 c2 c3 : ℤ) :
    |(c0 : ℝ) * ⟪n, e0⟫ + c1 * ⟪n, e1⟫ + c2 * ⟪n, e2⟫ + c3 * ⟪n, e3⟫| * ((two40 : ℕ) : ℝ) ≤
      (l1 (c0 * v0.ex + c1 * v1.ex + c2 * v2.ex + c3 * v3.ex)
        (c0 * v0.ey + c1 * v1.ey + c2 * v2.ey + c3 * v3.ey)
        (c0 * v0.ez + c1 * v1.ez + c2 * v2.ez + c3 * v3.ez) : ℝ) +
      3 * ((iabs c0 : ℝ) * v0.rho + (iabs c1 : ℝ) * v1.rho + (iabs c2 : ℝ) * v2.rho +
        (iabs c3 : ℝ) * v3.rho) := by
  set V := (c0 : ℝ) • e0 + (c1 : ℝ) • e1 + (c2 : ℝ) • e2 + (c3 : ℝ) • e3
  have hV : (c0 : ℝ) * ⟪n, e0⟫ + c1 * ⟪n, e1⟫ + c2 * ⟪n, e2⟫ + c3 * ⟪n, e3⟫ = ⟪n, V⟫ := by
    simp only [V, inner_add_right, inner_smul_right]
  rw [hV]
  have h40 : (0 : ℝ) < ((two40 : ℕ) : ℝ) := by norm_num [two40]
  have hnV : |⟪n, V⟫| ≤ ‖V‖ := (abs_real_inner_le_norm _ _).trans
    (by nlinarith [norm_nonneg V, norm_nonneg n])
  refine (mul_le_mul_of_nonneg_right (hnV.trans (norm_le_l1 V)) h40.le).trans ?_
  have comp : ∀ (k : Fin 3) (a0 a1 a2 a3 : ℤ), |e0 k * ((two40 : ℕ) : ℝ) - a0| ≤ v0.rho →
      |e1 k * ((two40 : ℕ) : ℝ) - a1| ≤ v1.rho → |e2 k * ((two40 : ℕ) : ℝ) - a2| ≤ v2.rho →
      |e3 k * ((two40 : ℕ) : ℝ) - a3| ≤ v3.rho →
      |V k| * ((two40 : ℕ) : ℝ) ≤ |((c0 * a0 + c1 * a1 + c2 * a2 + c3 * a3 : ℤ) : ℝ)| +
        ((iabs c0 : ℝ) * v0.rho + (iabs c1 : ℝ) * v1.rho + (iabs c2 : ℝ) * v2.rho +
          (iabs c3 : ℝ) * v3.rho) := by
    intro k a0 a1 a2 a3 b0 b1 b2 b3
    have eV : V k * ((two40 : ℕ) : ℝ) = (c0 : ℝ) * (e0 k * ((two40 : ℕ) : ℝ)) +
        c1 * (e1 k * ((two40 : ℕ) : ℝ)) + c2 * (e2 k * ((two40 : ℕ) : ℝ)) +
        c3 * (e3 k * ((two40 : ℕ) : ℝ)) := by
      simp only [V, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    have ea : |V k| * ((two40 : ℕ) : ℝ) = |V k * ((two40 : ℕ) : ℝ)| := by
      rw [abs_mul, abs_of_pos h40]
    rw [ea, eV]
    have ed : (c0 : ℝ) * (e0 k * ((two40 : ℕ) : ℝ)) + c1 * (e1 k * ((two40 : ℕ) : ℝ)) +
        c2 * (e2 k * ((two40 : ℕ) : ℝ)) + c3 * (e3 k * ((two40 : ℕ) : ℝ)) =
        ((c0 * a0 + c1 * a1 + c2 * a2 + c3 * a3 : ℤ) : ℝ) +
        ((c0 : ℝ) * (e0 k * ((two40 : ℕ) : ℝ) - a0) + c1 * (e1 k * ((two40 : ℕ) : ℝ) - a1) +
          c2 * (e2 k * ((two40 : ℕ) : ℝ) - a2) + c3 * (e3 k * ((two40 : ℕ) : ℝ) - a3)) := by
      push_cast; ring
    rw [ed]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    refine (abs_add_le _ _).trans ?_
    refine (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl).trans
        ?_
    rw [abs_mul, abs_mul, abs_mul, abs_mul, iabs_cast, iabs_cast, iabs_cast, iabs_cast]
    have := mul_le_mul_of_nonneg_left b0 (abs_nonneg (c0 : ℝ))
    have := mul_le_mul_of_nonneg_left b1 (abs_nonneg (c1 : ℝ))
    have := mul_le_mul_of_nonneg_left b2 (abs_nonneg (c2 : ℝ))
    have := mul_le_mul_of_nonneg_left b3 (abs_nonneg (c3 : ℝ))
    linarith
  have k0 := comp 0 v0.ex v1.ex v2.ex v3.ex h0.1 h1.1 h2.1 h3.1
  have k1 := comp 1 v0.ey v1.ey v2.ey v3.ey h0.2.1 h1.2.1 h2.2.1 h3.2.1
  have k2 := comp 2 v0.ez v1.ez v2.ez v3.ez h0.2.2 h1.2.2 h2.2.2 h3.2.2
  rw [l1_cast]
  rw [add_mul, add_mul]
  linarith

/-- The second-difference correction. -/
theorem corrA_sound {X0 X1 X2 : ℤ} (h01 : X0 < X1) (h12 : X1 < X2) {S : ℝ}
    (hS : 0 < S) {n : Space} (hn : ‖n‖ ≤ 1) {e0 e1 e2 : Space} {v0 v1 v2 : CRec}
    (h0 : BoxOK v0 e0) (h1 : BoxOK v1 e1) (h2 : BoxOK v2 e2) :
    ((X2 : ℝ) / S - X1 / S) ^ 2 / 4 *
        |dd2 ((X0 : ℝ) / S) (X1 / S) (X2 / S) ⟪n, e0⟫ ⟪n, e1⟫ ⟪n, e2⟫| ≤
      (corrA X0 X1 X2 v0 v1 v2 : ℝ) / ((two40 : ℕ) : ℝ) := by
  have h40 : (0 : ℝ) < ((two40 : ℕ) : ℝ) := by norm_num [two40]
  have ha' : (0 : ℝ) < (X1 : ℝ) - X0 := by have : (X0 : ℝ) < X1 := by exact_mod_cast h01
                                           linarith
  have hb' : (0 : ℝ) < (X2 : ℝ) - X1 := by have : (X1 : ℝ) < X2 := by exact_mod_cast h12
                                           linarith
  have hac' : (0 : ℝ) < (X2 : ℝ) - X0 := by linarith
  set g0 := ⟪n, e0⟫
  set g1 := ⟪n, e1⟫
  set g2 := ⟪n, e2⟫
  have e : ((X2 : ℝ) / S - X1 / S) ^ 2 / 4 * dd2 ((X0 : ℝ) / S) (X1 / S) (X2 / S) g0 g1 g2 =
      ((X2 : ℝ) - X1) * (((X2 - X1 : ℤ) : ℝ) * g0 + ((-(X2 - X0) : ℤ) : ℝ) * g1 +
        ((X1 - X0 : ℤ) : ℝ) * g2) / (4 * (((X1 : ℝ) - X0) * ((X2 : ℝ) - X0))) := by
    unfold dd2
    have hS0 : S ≠ 0 := hS.ne'
    rw [← sub_div, ← sub_div, ← sub_div]
    push_cast
    field_simp
    ring
  have hpos : 0 ≤ ((X2 : ℝ) / S - X1 / S) ^ 2 / 4 := by positivity
  rw [← abs_of_nonneg hpos, ← abs_mul, e, abs_div, abs_mul, abs_of_pos hb',
    abs_of_pos (by positivity : (0 : ℝ) < 4 * (((X1 : ℝ) - X0) * ((X2 : ℝ) - X0)))]
  have hb := comb3_bound hn h0 h1 h2 (X2 - X1) (-(X2 - X0)) (X1 - X0)
  set N := |((X2 - X1 : ℤ) : ℝ) * g0 + ((-(X2 - X0) : ℤ) : ℝ) * g1 + ((X1 - X0 : ℤ) : ℝ) * g2|
  set L := l1 ((X2 - X1) * v0.ex + -(X2 - X0) * v1.ex + (X1 - X0) * v2.ex)
    ((X2 - X1) * v0.ey + -(X2 - X0) * v1.ey + (X1 - X0) * v2.ey)
    ((X2 - X1) * v0.ez + -(X2 - X0) * v1.ez + (X1 - X0) * v2.ez)
  set r := Nat.mul 3 (Nat.add (Nat.add (Nat.mul (iabs (X2 - X1)) v0.rho)
    (Nat.mul (iabs (-(X2 - X0))) v1.rho)) (Nat.mul (iabs (X1 - X0)) v2.rho))
  have hr : (r : ℝ) = 3 * ((iabs (X2 - X1) : ℝ) * v0.rho + (iabs (-(X2 - X0)) : ℝ) * v1.rho +
      (iabs (X1 - X0) : ℝ) * v2.rho) := by
    simp only [r]; push_cast [Nat.mul_eq, Nat.add_eq]; ring
  have hN : N ≤ ((L : ℝ) + r) / ((two40 : ℕ) : ℝ) := by
    rw [le_div_iff₀ h40, hr]; exact hb
  have hden : 0 < Nat.mul 4 (iabs ((X1 - X0) * (X2 - X0))) := by
    apply Nat.mul_pos (by norm_num); simp only [iabs]
    have : 0 < (X1 - X0) * (X2 - X0) := Int.mul_pos (by omega) (by omega)
    omega
  have c1 : ((Nat.mul (iabs (X2 - X1)) (Nat.add L r) : ℕ) : ℝ) = ((X2 : ℝ) - X1) *
      ((L : ℝ) + r) := by
    push_cast [Nat.mul_eq, Nat.add_eq]; rw [iabs_cast]; push_cast; rw [abs_of_pos hb']
  have c2 : ((Nat.mul 4 (iabs ((X1 - X0) * (X2 - X0))) : ℕ) : ℝ) =
      4 * (((X1 : ℝ) - X0) * ((X2 : ℝ) - X0)) := by
    push_cast [Nat.mul_eq]; rw [iabs_cast]; push_cast
    rw [abs_of_pos (by positivity : (0 : ℝ) < ((X1 : ℝ) - X0) * ((X2 : ℝ) - X0))]
  have hcd := cdiv_ge (Nat.mul (iabs (X2 - X1)) (Nat.add L r)) hden
  rw [c1, c2] at hcd
  calc ((X2 : ℝ) - X1) * N / (4 * (((X1 : ℝ) - X0) * ((X2 : ℝ) - X0)))
      ≤ ((X2 : ℝ) - X1) * (((L : ℝ) + r) / ((two40 : ℕ) : ℝ)) /
          (4 * (((X1 : ℝ) - X0) * ((X2 : ℝ) - X0))) := by gcongr
    _ = ((X2 : ℝ) - X1) * ((L : ℝ) + r) / (4 * (((X1 : ℝ) - X0) * ((X2 : ℝ) - X0))) /
          ((two40 : ℕ) : ℝ) := by ring
    _ ≤ (corrA X0 X1 X2 v0 v1 v2 : ℝ) / ((two40 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hcd h40.le

/-- The third-difference correction. -/
theorem corrB_sound {X0 X1 X2 X3 : ℤ} (h01 : X0 < X1) (h12 : X1 < X2) (h23 : X2 < X3) {S : ℝ}
    (hS : 0 < S) {n : Space} (hn : ‖n‖ ≤ 1) {e0 e1 e2 e3 : Space} {v0 v1 v2 v3 : CRec}
    (h0 : BoxOK v0 e0) (h1 : BoxOK v1 e1) (h2 : BoxOK v2 e2) (h3 : BoxOK v3 e3) :
    ((X2 : ℝ) / S - X1 / S) ^ 2 * ((X2 : ℝ) / S - X0 / S) / 4 *
        |dd3 ((X0 : ℝ) / S) (X1 / S) (X2 / S) (X3 / S) ⟪n, e0⟫ ⟪n, e1⟫ ⟪n, e2⟫ ⟪n, e3⟫| ≤
      (corrB X0 X1 X2 X3 v0 v1 v2 v3 : ℝ) / ((two40 : ℕ) : ℝ) := by
  have h40 : (0 : ℝ) < ((two40 : ℕ) : ℝ) := by norm_num [two40]
  have ha' : (0 : ℝ) < (X1 : ℝ) - X0 := by have : (X0 : ℝ) < X1 := by exact_mod_cast h01
                                           linarith
  have hb' : (0 : ℝ) < (X2 : ℝ) - X1 := by have : (X1 : ℝ) < X2 := by exact_mod_cast h12
                                           linarith
  have hc' : (0 : ℝ) < (X3 : ℝ) - X2 := by have : (X2 : ℝ) < X3 := by exact_mod_cast h23
                                           linarith
  set g0 := ⟪n, e0⟫
  set g1 := ⟪n, e1⟫
  set g2 := ⟪n, e2⟫
  set g3 := ⟪n, e3⟫
  set a := X1 - X0
  set b := X2 - X1
  set c := X3 - X2
  set ac := X2 - X0
  set bc := X3 - X1
  set abc := X3 - X0
  have e : ((X2 : ℝ) / S - X1 / S) ^ 2 * ((X2 : ℝ) / S - X0 / S) / 4 *
      dd3 ((X0 : ℝ) / S) (X1 / S) (X2 / S) (X3 / S) g0 g1 g2 g3 =
      ((X2 : ℝ) - X1) * (((-(c * bc * b) : ℤ) : ℝ) * g0 + ((a * ac * c + c * bc * ac : ℤ) : ℝ) *
          g1 +
        ((-(a * ac * bc + c * bc * a) : ℤ) : ℝ) * g2 + ((a * ac * b : ℤ) : ℝ) * g3) /
        (4 * (((X1 : ℝ) - X0) * ((X3 : ℝ) - X2) * ((X3 : ℝ) - X1) * ((X3 : ℝ) - X0))) := by
    unfold dd3 dd2
    have hS0 : S ≠ 0 := hS.ne'
    have q1 : (X1 : ℝ) - X0 ≠ 0 := ha'.ne'
    have q2 : (X2 : ℝ) - X1 ≠ 0 := hb'.ne'
    have q3 : (X2 : ℝ) - X0 ≠ 0 := by linarith
    have q4 : (X3 : ℝ) - X2 ≠ 0 := hc'.ne'
    have q5 : (X3 : ℝ) - X1 ≠ 0 := by linarith
    have q6 : (X3 : ℝ) - X0 ≠ 0 := by linarith
    simp only [a, b, c, ac, bc]
    rw [← sub_div, ← sub_div, ← sub_div, ← sub_div, ← sub_div, ← sub_div]
    push_cast
    field_simp
    ring
  have hpos : 0 ≤ ((X2 : ℝ) / S - X1 / S) ^ 2 * ((X2 : ℝ) / S - X0 / S) / 4 := by
    have : 0 ≤ (X2 : ℝ) / S - X0 / S := by rw [← sub_div]; apply div_nonneg _ hS.le; linarith
    positivity
  have hD : (0 : ℝ) < 4 *
      (((X1 : ℝ) - X0) * ((X3 : ℝ) - X2) * ((X3 : ℝ) - X1) * ((X3 : ℝ) - X0)) := by
    have : (0 : ℝ) < (X3 : ℝ) - X1 := by linarith
    have : (0 : ℝ) < (X3 : ℝ) - X0 := by linarith
    positivity
  rw [← abs_of_nonneg hpos, ← abs_mul, e, abs_div, abs_mul, abs_of_pos hb', abs_of_pos hD]
  have hb := comb4_bound hn h0 h1 h2 h3 (-(c * bc * b)) (a * ac * c + c * bc * ac)
    (-(a * ac * bc + c * bc * a)) (a * ac * b)
  set N := |((-(c * bc * b) : ℤ) : ℝ) * g0 + ((a * ac * c + c * bc * ac : ℤ) : ℝ) * g1 +
      ((-(a * ac * bc + c * bc * a) : ℤ) : ℝ) * g2 + ((a * ac * b : ℤ) : ℝ) * g3|
  set L := l1 (-(c * bc * b) * v0.ex + (a * ac * c + c * bc * ac) * v1.ex +
      -(a * ac * bc + c * bc * a) * v2.ex + a * ac * b * v3.ex)
    (-(c * bc * b) * v0.ey + (a * ac * c + c * bc * ac) * v1.ey +
      -(a * ac * bc + c * bc * a) * v2.ey + a * ac * b * v3.ey)
    (-(c * bc * b) * v0.ez + (a * ac * c + c * bc * ac) * v1.ez +
      -(a * ac * bc + c * bc * a) * v2.ez + a * ac * b * v3.ez)
  set r := Nat.mul 3 (Nat.add (Nat.add (Nat.mul (iabs (-(c * bc * b))) v0.rho)
    (Nat.mul (iabs (a * ac * c + c * bc * ac)) v1.rho))
    (Nat.add (Nat.mul (iabs (-(a * ac * bc + c * bc * a))) v2.rho) (Nat.mul (iabs (a * ac * b))
        v3.rho)))
  have hr : (r : ℝ) = 3 * ((iabs (-(c * bc * b)) : ℝ) * v0.rho +
      (iabs (a * ac * c + c * bc * ac) : ℝ) * v1.rho +
      (iabs (-(a * ac * bc + c * bc * a)) : ℝ) * v2.rho + (iabs (a * ac * b) : ℝ) * v3.rho) := by
    simp only [r]; push_cast [Nat.mul_eq, Nat.add_eq]; ring
  have hN : N ≤ ((L : ℝ) + r) / ((two40 : ℕ) : ℝ) := by
    rw [le_div_iff₀ h40, hr]; exact hb
  have hden : 0 < Nat.mul 4 (iabs (a * c * bc * abc)) := by
    apply Nat.mul_pos (by norm_num); simp only [iabs]
    have : 0 < a * c * bc * abc := Int.mul_pos (Int.mul_pos (Int.mul_pos (by omega) (by omega))
      (by omega)) (by omega)
    omega
  have c1 : ((Nat.mul (iabs b) (Nat.add L r) : ℕ) : ℝ) = ((X2 : ℝ) - X1) * ((L : ℝ) + r) := by
    push_cast [Nat.mul_eq, Nat.add_eq]; rw [iabs_cast]; simp only [b]; push_cast
    rw [abs_of_pos hb']
  have c2 : ((Nat.mul 4 (iabs (a * c * bc * abc)) : ℕ) : ℝ) =
      4 * (((X1 : ℝ) - X0) * ((X3 : ℝ) - X2) * ((X3 : ℝ) - X1) * ((X3 : ℝ) - X0)) := by
    push_cast [Nat.mul_eq]; rw [iabs_cast]; simp only [a, c, bc, abc]; push_cast
    have : (0 : ℝ) < (X3 : ℝ) - X1 := by linarith
    have : (0 : ℝ) < (X3 : ℝ) - X0 := by linarith
    rw [abs_of_pos (by positivity)]
  have hcd := cdiv_ge (Nat.mul (iabs b) (Nat.add L r)) hden
  rw [c1, c2] at hcd
  calc ((X2 : ℝ) - X1) * N /
        (4 * (((X1 : ℝ) - X0) * ((X3 : ℝ) - X2) * ((X3 : ℝ) - X1) * ((X3 : ℝ) - X0)))
      ≤ ((X2 : ℝ) - X1) * (((L : ℝ) + r) / ((two40 : ℕ) : ℝ)) /
          (4 * (((X1 : ℝ) - X0) * ((X3 : ℝ) - X2) * ((X3 : ℝ) - X1) * ((X3 : ℝ) - X0))) := by
        gcongr
    _ = ((X2 : ℝ) - X1) * ((L : ℝ) + r) /
          (4 * (((X1 : ℝ) - X0) * ((X3 : ℝ) - X2) * ((X3 : ℝ) - X1) * ((X3 : ℝ) - X0))) /
          ((two40 : ℕ) : ℝ) := by ring
    _ ≤ (corrB X0 X1 X2 X3 v0 v1 v2 v3 : ℝ) / ((two40 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hcd h40.le

/-- **The divided-difference corrections** of `⟨n, E⟩` on a `4`-node stencil `Xₖ/S` are bounded
by `corr4/2⁴⁰`. -/
theorem corr4_sound {X0 X1 X2 X3 : ℤ} (h01 : X0 < X1) (h12 : X1 < X2) (h23 : X2 < X3) {S : ℝ}
    (hS : 0 < S) {n : Space} (hn : ‖n‖ ≤ 1) {e0 e1 e2 e3 : Space} {v0 v1 v2 v3 : CRec}
    (h0 : BoxOK v0 e0) (h1 : BoxOK v1 e1) (h2 : BoxOK v2 e2) (h3 : BoxOK v3 e3) :
    ((X2 : ℝ) / S - X1 / S) ^ 2 / 4 *
        |dd2 ((X0 : ℝ) / S) (X1 / S) (X2 / S) ⟪n, e0⟫ ⟪n, e1⟫ ⟪n, e2⟫| +
      ((X2 : ℝ) / S - X1 / S) ^ 2 * ((X2 : ℝ) / S - X0 / S) / 4 *
        |dd3 ((X0 : ℝ) / S) (X1 / S) (X2 / S) (X3 / S) ⟪n, e0⟫ ⟪n, e1⟫ ⟪n, e2⟫ ⟪n, e3⟫| ≤
      (corr4 X0 X1 X2 X3 v0 v1 v2 v3 : ℝ) / ((two40 : ℕ) : ℝ) := by
  have hA := corrA_sound h01 h12 hS hn h0 h1 h2
  have hB := corrB_sound h01 h12 h23 hS hn h0 h1 h2 h3
  unfold corr4
  push_cast [Nat.add_eq]
  rw [add_div]
  exact add_le_add hA hB

/-! ## Lebesgue factors -/

/-- The Lebesgue constants of a stencil `Xₖ/S` (scale-free). -/
@[expose] def lebB0 (X0 X1 X2 X3 : ℤ) : ℝ :=
  ((X2 : ℝ) - X1) ^ 2 * ((X3 : ℝ) - X1) / (4 * (((X1 : ℝ) - X0) * ((X2 : ℝ) - X0) * ((X3 : ℝ) -
      X0)))
/-- The second Lebesgue constant. -/
@[expose] def lebB3 (X0 X1 X2 X3 : ℤ) : ℝ :=
  ((X2 : ℝ) - X1) ^ 2 * ((X2 : ℝ) - X0) / (4 * (((X3 : ℝ) - X0) * ((X3 : ℝ) - X1) * ((X3 : ℝ) -
      X2)))

/-- Closed form of the Lebesgue-type factor `lebB0`. -/
theorem lebB0_eq {X0 X1 X2 X3 : ℤ} (h01 : X0 < X1) (h12 : X1 < X2) (h23 : X2 < X3) {S : ℝ}
    (hS : 0 < S) :
    ((X2 : ℝ) / S - X1 / S) ^ 2 * ((X3 : ℝ) / S - X1 / S) /
      (4 * (((X1 : ℝ) / S - X0 / S) * ((X2 : ℝ) / S - X0 / S) * ((X3 : ℝ) / S - X0 / S))) =
      lebB0 X0 X1 X2 X3 := by
  unfold lebB0
  have ha : (X1 : ℝ) - X0 ≠ 0 := by have : (X0 : ℝ) < X1 := by exact_mod_cast h01
                                    linarith
  have hb : (X2 : ℝ) - X0 ≠ 0 := by have : (X0 : ℝ) < X2 := by exact_mod_cast h01.trans h12
                                    linarith
  have hc : (X3 : ℝ) - X0 ≠ 0 := by
    have : (X0 : ℝ) < X3 := by exact_mod_cast (h01.trans h12).trans h23
    linarith
  rw [← sub_div, ← sub_div, ← sub_div, ← sub_div, ← sub_div]
  have hS0 : S ≠ 0 := hS.ne'
  field_simp

/-- Closed form of the Lebesgue-type factor `lebB3`. -/
theorem lebB3_eq {X0 X1 X2 X3 : ℤ} (h01 : X0 < X1) (h12 : X1 < X2) (h23 : X2 < X3) {S : ℝ}
    (hS : 0 < S) :
    ((X2 : ℝ) / S - X1 / S) ^ 2 * ((X2 : ℝ) / S - X0 / S) /
      (4 * (((X3 : ℝ) / S - X0 / S) * ((X3 : ℝ) / S - X1 / S) * ((X3 : ℝ) / S - X2 / S))) =
      lebB3 X0 X1 X2 X3 := by
  unfold lebB3
  have ha : (X3 : ℝ) - X0 ≠ 0 := by
    have : (X0 : ℝ) < X3 := by exact_mod_cast (h01.trans h12).trans h23
    linarith
  have hb : (X3 : ℝ) - X1 ≠ 0 := by have : (X1 : ℝ) < X3 := by exact_mod_cast h12.trans h23
                                    linarith
  have hc : (X3 : ℝ) - X2 ≠ 0 := by have : (X2 : ℝ) < X3 := by exact_mod_cast h23
                                    linarith
  rw [← sub_div, ← sub_div, ← sub_div, ← sub_div, ← sub_div]
  have hS0 : S ≠ 0 := hS.ne'
  field_simp

/-- **`leb4` dominates the Lebesgue factor.** -/
theorem leb4_sound {X0 X1 X2 X3 : ℤ} (h01 : X0 < X1) (h12 : X1 < X2) (h23 : X2 < X3) (C : ℕ) :
    (1 + 2 * (lebB0 X0 X1 X2 X3 + lebB3 X0 X1 X2 X3)) * C ≤ (leb4 X0 X1 X2 X3 C : ℝ) := by
  have ha : (0 : ℝ) < (X1 : ℝ) - X0 := by have : (X0 : ℝ) < X1 := by exact_mod_cast h01
                                          linarith
  have hb : (0 : ℝ) < (X2 : ℝ) - X1 := by have : (X1 : ℝ) < X2 := by exact_mod_cast h12
                                          linarith
  have hc : (0 : ℝ) < (X3 : ℝ) - X2 := by have : (X2 : ℝ) < X3 := by exact_mod_cast h23
                                          linarith
  have hd0 : 0 < Nat.mul 4 (iabs ((X1 - X0) * (X2 - X0) * (X3 - X0))) := by
    apply Nat.mul_pos (by norm_num); simp only [iabs]
    have : 0 < (X1 - X0) * (X2 - X0) * (X3 - X0) :=
      Int.mul_pos (Int.mul_pos (by omega) (by omega)) (by omega)
    omega
  have hd3 : 0 < Nat.mul 4 (iabs ((X3 - X0) * (X3 - X1) * (X3 - X2))) := by
    apply Nat.mul_pos (by norm_num); simp only [iabs]
    have : 0 < (X3 - X0) * (X3 - X1) * (X3 - X2) :=
      Int.mul_pos (Int.mul_pos (by omega) (by omega)) (by omega)
    omega
  unfold leb4
  simp only
  refine le_trans ?_ (cdiv_ge _ (Nat.mul_pos hd0 hd3))
  have i0 : ((iabs ((X1 - X0) * (X2 - X0) * (X3 - X0)) : ℕ) : ℝ) =
      ((X1 : ℝ) - X0) * ((X2 : ℝ) - X0) * ((X3 : ℝ) - X0) := by
    rw [iabs_cast]; push_cast
    have : (0 : ℝ) < (X2 : ℝ) - X0 := by linarith
    have : (0 : ℝ) < (X3 : ℝ) - X0 := by linarith
    rw [abs_of_pos (by positivity)]
  have i3 : ((iabs ((X3 - X0) * (X3 - X1) * (X3 - X2)) : ℕ) : ℝ) =
      ((X3 : ℝ) - X0) * ((X3 : ℝ) - X1) * ((X3 : ℝ) - X2) := by
    rw [iabs_cast]; push_cast
    have : (0 : ℝ) < (X3 : ℝ) - X0 := by linarith
    have : (0 : ℝ) < (X3 : ℝ) - X1 := by linarith
    rw [abs_of_pos (by positivity)]
  have j0 : ((iabs (X2 - X1) : ℕ) : ℝ) = (X2 : ℝ) - X1 := by
    rw [iabs_cast]; push_cast; rw [abs_of_pos hb]
  have j1 : ((iabs (X3 - X1) : ℕ) : ℝ) = (X3 : ℝ) - X1 := by
    rw [iabs_cast]; push_cast; rw [abs_of_pos (by linarith)]
  have j2 : ((iabs (X2 - X0) : ℕ) : ℝ) = (X2 : ℝ) - X0 := by
    rw [iabs_cast]; push_cast; rw [abs_of_pos (by linarith)]
  push_cast [Nat.mul_eq, Nat.add_eq, sq_cast]
  rw [i0, i3, j0, j1, j2]
  unfold lebB0 lebB3
  apply le_of_eq
  have : (0 : ℝ) < (X2 : ℝ) - X0 := by linarith
  have : (0 : ℝ) < (X3 : ℝ) - X0 := by linarith
  have : (0 : ℝ) < (X3 : ℝ) - X1 := by linarith
  field_simp

/-! ## The cell -/

/-- Value facts of a record at a face point. -/
@[expose] def ValGood (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (kind : ℕ) (t w : ℝ) (r : CRec) : Prop :=
  ‖errF fils (ptF kind t w)‖ * ((two40 : ℕ) : ℝ) ≤ r.e ∧ BoxOK r (errF fils (ptF kind t w))

/-- The `w`-interpolation remainder on the line `t`, cell `[W₁, W₂]`, is at most `B`. -/
@[expose] def WGood (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (kind : ℕ) (t W0 W1 W2 W3 B : ℝ) : Prop :=
  ∀ n : Space, ‖n‖ ≤ 1 → ∀ w ∈ Icc W1 W2,
    |⟪n, errF fils (ptF kind t w)⟫ - newt W0 W1 W2 W3 ⟪n, errF fils (ptF kind t W0)⟫
      ⟪n, errF fils (ptF kind t W1)⟫ ⟪n, errF fils (ptF kind t W2)⟫
      ⟪n, errF fils (ptF kind t W3)⟫ w| ≤ B

/-- The `t`-interpolation remainder on the strip `[T₁, T₂] × [W₁, W₂]` is at most `B`. -/
@[expose] def TGood (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (kind : ℕ) (T0 T1 T2 T3 W1 W2 B : ℝ) :
    Prop :=
  ∀ n : Space, ‖n‖ ≤ 1 → ∀ w ∈ Icc W1 W2, ∀ t ∈ Icc T1 T2,
    |⟪n, errF fils (ptF kind t w)⟫ - newt T0 T1 T2 T3 ⟪n, errF fils (ptF kind T0 w)⟫
      ⟪n, errF fils (ptF kind T1 w)⟫ ⟪n, errF fils (ptF kind T2 w)⟫
      ⟪n, errF fils (ptF kind T3 w)⟫ t| ≤ B

/-- Each of four naturals is at most their maximum. -/
theorem le_nmax4 (f : Fin 4 → ℕ) : ∀ i : Fin 4, f i ≤ nmax4 (f 0) (f 1) (f 2) (f 3)
  | ⟨0, _⟩ => (nmax_ge_left _ _).trans (nmax_ge_left _ _)
  | ⟨1, _⟩ => (nmax_ge_right _ _).trans (nmax_ge_left _ _)
  | ⟨2, _⟩ => (nmax_ge_left _ _).trans (nmax_ge_right _ _)
  | ⟨3, _⟩ => (nmax_ge_right _ _).trans (nmax_ge_right _ _)

/-- Strict monotonicity of `m ↦ m/4096`. -/
theorem div4096_lt {a b : ℤ} (h : a < b) : (a : ℝ) / 4096 < (b : ℝ) / 4096 := by
  have : (a : ℝ) < b := by exact_mod_cast h
  linarith

/-- **The cell bound.** -/
theorem cell_sound4 (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (F : Face4) (eta : ℕ) (hwd : 0 < F.wd)
    (M W : Fin 4 → ℤ) (Rm : Fin 4 → Fin 4 → CRec)
    (hM : M 0 < M 1 ∧ M 1 < M 2 ∧ M 2 < M 3) (hW : W 0 < W 1 ∧ W 1 < W 2 ∧ W 2 < W 3)
    (hV : ∀ i j, ValGood fils F.kind ((M i : ℝ) / 4096) ((W j : ℝ) / F.wd) (Rm i j))
    (hWr : ∀ i, WGood fils F.kind ((M i : ℝ) / 4096) ((W 0 : ℝ) / F.wd) ((W 1 : ℝ) / F.wd)
      ((W 2 : ℝ) / F.wd) ((W 3 : ℝ) / F.wd) ((Rm i 1).rw / ((two40 : ℕ) : ℝ)))
    (hTr : TGood fils F.kind ((M 0 : ℝ) / 4096) ((M 1 : ℝ) / 4096) ((M 2 : ℝ) / 4096)
      ((M 3 : ℝ) / 4096) ((W 1 : ℝ) / F.wd) ((W 2 : ℝ) / F.wd) ((Rm 1 1).rt / ((two40 : ℕ) : ℝ)))
    (hok : cellOK4 F eta (M 0) (M 1) (M 2) (M 3) (W 0) (W 1) (W 2) (W 3) (Rm 0 0) (Rm 0 1)
      (Rm 0 2) (Rm 0 3) (Rm 1 0) (Rm 1 1) (Rm 1 2) (Rm 1 3) (Rm 2 0) (Rm 2 1) (Rm 2 2) (Rm 2 3)
      (Rm 3 0) (Rm 3 1) (Rm 3 2) (Rm 3 3) = true)
    {t w : ℝ} (ht : t ∈ Icc ((M 1 : ℝ) / 4096) ((M 2 : ℝ) / 4096))
    (hw : w ∈ Icc ((W 1 : ℝ) / F.wd) ((W 2 : ℝ) / F.wd)) :
    ‖errF fils (ptF F.kind t w)‖ ≤ (eta : ℝ) / ((two40 : ℕ) : ℝ) := by
  obtain ⟨hM01, hM12, hM23⟩ := hM
  obtain ⟨hW01, hW12, hW23⟩ := hW
  have h40 : (0 : ℝ) < ((two40 : ℕ) : ℝ) := by norm_num [two40]
  have hwd' : (0 : ℝ) < F.wd := by exact_mod_cast hwd
  have hq : (0 : ℝ) < 4096 := by norm_num
  set T : Fin 4 → ℝ := fun i => (M i : ℝ) / 4096
  set X : Fin 4 → ℝ := fun j => (W j : ℝ) / F.wd
  have t01 : T 0 < T 1 := div4096_lt hM01
  have t12 : T 1 < T 2 := div4096_lt hM12
  have t23 : T 2 < T 3 := div4096_lt hM23
  have x01 : X 0 < X 1 := div_lt_div_wd hwd hW01
  have x12 : X 1 < X 2 := div_lt_div_wd hwd hW12
  have x23 : X 2 < X 3 := div_lt_div_wd hwd hW23
  -- unpack the cell check
  unfold cellOK4 at hok
  simp only [Bool.and_eq_true, Nat.ble_eq] at hok
  obtain ⟨-, htot⟩ := hok
  set e := errF fils (ptF F.kind t w)
  by_cases he : e = 0
  · rw [he, norm_zero]; positivity
  set n : Space := ‖e‖⁻¹ • e
  have hn : ‖n‖ ≤ 1 := by
    simp only [n, norm_smul, norm_inv, norm_norm]
    rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr he)]
  have hne : ⟪n, e⟫ = ‖e‖ := by
    simp only [n, inner_smul_left, conj_trivial, real_inner_self_eq_norm_sq]
    field_simp [norm_ne_zero_iff.mpr he]
  set G : Fin 4 → Fin 4 → ℝ := fun i j => ⟪n, errF fils (ptF F.kind (T i) (X j))⟫
  -- the `t`-remainder
  have hT := hTr n hn w hw t ht
  -- the `w`-remainders
  set ε : Fin 4 → ℝ := fun i => ⟪n, errF fils (ptF F.kind (T i) w)⟫ -
    newt (X 0) (X 1) (X 2) (X 3) (G i 0) (G i 1) (G i 2) (G i 3) w
  have hε : ∀ i, |ε i| ≤ (Rm i 1).rw / ((two40 : ℕ) : ℝ) := fun i => hWr i n hn w hw
  set RW := nmax4 (Rm 0 1).rw (Rm 1 1).rw (Rm 2 1).rw (Rm 3 1).rw
  have hεRW : ∀ i, |ε i| ≤ (RW : ℝ) / ((two40 : ℕ) : ℝ) := by
    intro i
    refine (hε i).trans (div_le_div_of_nonneg_right ?_ h40.le)
    exact_mod_cast le_nmax4 (fun i => (Rm i 1).rw) i
  -- decomposition
  have hdec : newt (T 0) (T 1) (T 2) (T 3) ⟪n, errF fils (ptF F.kind (T 0) w)⟫
      ⟪n, errF fils (ptF F.kind (T 1) w)⟫ ⟪n, errF fils (ptF F.kind (T 2) w)⟫
      ⟪n, errF fils (ptF F.kind (T 3) w)⟫ t =
      bicubic (T 0) (T 1) (T 2) (T 3) (X 0) (X 1) (X 2) (X 3) G t w +
        newt (T 0) (T 1) (T 2) (T 3) (ε 0) (ε 1) (ε 2) (ε 3) t := by
    unfold bicubic
    rw [← newt_add]
    congr 1 <;> simp only [ε] <;> ring
  -- bound of the interpolant of the `ε`
  have hεt := abs_newt_le t01 t12 t23 ht (hεRW 0) (hεRW 1) (hεRW 2) (hεRW 3)
    (le_of_eq (lebB0_eq hM01 hM12 hM23 hq)) (le_of_eq (lebB3_eq hM01 hM12 hM23 hq))
  have hleb_t := leb4_sound hM01 hM12 hM23 RW
  -- the bicubic part
  set E := nmax4 (Rm 1 1).e (Rm 1 2).e (Rm 2 1).e (Rm 2 2).e
  set Cw := nmax (corr4 (W 0) (W 1) (W 2) (W 3) (Rm 1 0) (Rm 1 1) (Rm 1 2) (Rm 1 3))
    (corr4 (W 0) (W 1) (W 2) (W 3) (Rm 2 0) (Rm 2 1) (Rm 2 2) (Rm 2 3))
  set Cs := nmax4 (corr4 (M 0) (M 1) (M 2) (M 3) (Rm 0 0) (Rm 1 0) (Rm 2 0) (Rm 3 0))
    (corr4 (M 0) (M 1) (M 2) (M 3) (Rm 0 1) (Rm 1 1) (Rm 2 1) (Rm 3 1))
    (corr4 (M 0) (M 1) (M 2) (M 3) (Rm 0 2) (Rm 1 2) (Rm 2 2) (Rm 3 2))
    (corr4 (M 0) (M 1) (M 2) (M 3) (Rm 0 3) (Rm 1 3) (Rm 2 3) (Rm 3 3))
  have hE : ∀ i j : Fin 4, (i = 1 ∨ i = 2) → (j = 1 ∨ j = 2) →
      |G i j| ≤ (E : ℝ) / ((two40 : ℕ) : ℝ) := by
    intro i j hi hj
    have h1 : |G i j| ≤ ‖errF fils (ptF F.kind (T i) (X j))‖ :=
      (abs_real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (errF fils (ptF F.kind (T i) (X
          j)))])
    have h2 := (hV i j).1
    have h3 : ‖errF fils (ptF F.kind (T i) (X j))‖ ≤ ((Rm i j).e : ℝ) / ((two40 : ℕ) : ℝ) := by
      rw [le_div_iff₀ h40]; exact h2
    refine h1.trans (h3.trans (div_le_div_of_nonneg_right ?_ h40.le))
    have := nmax_ge_left (nmax (Rm 1 1).e (Rm 1 2).e) (nmax (Rm 2 1).e (Rm 2 2).e)
    have := nmax_ge_right (nmax (Rm 1 1).e (Rm 1 2).e) (nmax (Rm 2 1).e (Rm 2 2).e)
    have := nmax_ge_left (Rm 1 1).e (Rm 1 2).e
    have := nmax_ge_right (Rm 1 1).e (Rm 1 2).e
    have := nmax_ge_left (Rm 2 1).e (Rm 2 2).e
    have := nmax_ge_right (Rm 2 1).e (Rm 2 2).e
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simp only [E, nmax4] <;>
      exact_mod_cast (by omega)
  have hCw : ∀ i : Fin 4, (i = 1 ∨ i = 2) →
      (X 2 - X 1) ^ 2 / 4 * |dd2 (X 0) (X 1) (X 2) (G i 0) (G i 1) (G i 2)| +
        (X 2 - X 1) ^ 2 * (X 2 - X 0) / 4 * |dd3 (X 0) (X 1) (X 2) (X 3) (G i 0) (G i 1) (G i 2)
          (G i 3)| ≤ (Cw : ℝ) / ((two40 : ℕ) : ℝ) := by
    intro i hi
    have hc := corr4_sound hW01 hW12 hW23 hwd' hn (hV i 0).2 (hV i 1).2 (hV i 2).2 (hV i 3).2
    refine hc.trans (div_le_div_of_nonneg_right ?_ h40.le)
    rcases hi with rfl | rfl
    · exact_mod_cast nmax_ge_left _ _
    · exact_mod_cast nmax_ge_right _ _
  have hCs : ∀ j : Fin 4,
      (T 2 - T 1) ^ 2 / 4 * |dd2 (T 0) (T 1) (T 2) (G 0 j) (G 1 j) (G 2 j)| +
        (T 2 - T 1) ^ 2 * (T 2 - T 0) / 4 * |dd3 (T 0) (T 1) (T 2) (T 3) (G 0 j) (G 1 j) (G 2 j)
          (G 3 j)| ≤ (Cs : ℝ) / ((two40 : ℕ) : ℝ) := by
    intro j
    have hc := corr4_sound hM01 hM12 hM23 hq hn (hV 0 j).2 (hV 1 j).2 (hV 2 j).2 (hV 3 j).2
    refine hc.trans (div_le_div_of_nonneg_right ?_ h40.le)
    exact_mod_cast le_nmax4 (fun j => corr4 (M 0) (M 1) (M 2) (M 3) (Rm 0 j) (Rm 1 j) (Rm 2 j)
      (Rm 3 j)) j
  have hbic := tensor_bound t01 t12 t23 x01 x12 x23 G ht hw hE hCw hCs
    (le_of_eq (lebB0_eq hW01 hW12 hW23 hwd')) (le_of_eq (lebB3_eq hW01 hW12 hW23 hwd'))
  have hleb_w := leb4_sound hW01 hW12 hW23 Cs
  -- assemble
  have htot' : (E : ℝ) + Cw + leb4 (W 0) (W 1) (W 2) (W 3) Cs + leb4 (M 0) (M 1) (M 2) (M 3) RW +
      (Rm 1 1).rt ≤ eta := by exact_mod_cast htot
  rw [← hne]
  have hsplit : ⟪n, e⟫ = (⟪n, e⟫ - newt (T 0) (T 1) (T 2) (T 3)
      ⟪n, errF fils (ptF F.kind (T 0) w)⟫ ⟪n, errF fils (ptF F.kind (T 1) w)⟫
      ⟪n, errF fils (ptF F.kind (T 2) w)⟫ ⟪n, errF fils (ptF F.kind (T 3) w)⟫ t) +
      (bicubic (T 0) (T 1) (T 2) (T 3) (X 0) (X 1) (X 2) (X 3) G t w +
        newt (T 0) (T 1) (T 2) (T 3) (ε 0) (ε 1) (ε 2) (ε 3) t) := by rw [← hdec]; ring
  rw [hsplit]
  refine (le_abs_self _).trans ((abs_add_le _ _).trans ?_)
  refine (add_le_add hT ((abs_add_le _ _).trans (add_le_add hbic hεt))).trans ?_
  have hlt := div_le_div_of_nonneg_right htot' h40.le
  have e1 : (1 + 2 * (lebB0 (W 0) (W 1) (W 2) (W 3) + lebB3 (W 0) (W 1) (W 2) (W 3))) *
      ((Cs : ℝ) / ((two40 : ℕ) : ℝ)) ≤ (leb4 (W 0) (W 1) (W 2) (W 3) Cs : ℝ) /
          ((two40 : ℕ) : ℝ) := by
    rw [mul_div_assoc']; exact div_le_div_of_nonneg_right hleb_w h40.le
  have e2 : (1 + 2 * (lebB0 (M 0) (M 1) (M 2) (M 3) + lebB3 (M 0) (M 1) (M 2) (M 3))) *
      ((RW : ℝ) / ((two40 : ℕ) : ℝ)) ≤ (leb4 (M 0) (M 1) (M 2) (M 3) RW : ℝ) /
          ((two40 : ℕ) : ℝ) := by
    rw [mul_div_assoc']; exact div_le_div_of_nonneg_right hleb_t h40.le
  have : ((Rm 1 1).rt : ℝ) / ((two40 : ℕ) : ℝ) + ((E : ℝ) / ((two40 : ℕ) : ℝ) +
      (Cw : ℝ) / ((two40 : ℕ) : ℝ) + (leb4 (W 0) (W 1) (W 2) (W 3) Cs : ℝ) / ((two40 : ℕ) : ℝ) +
      (leb4 (M 0) (M 1) (M 2) (M 3) RW : ℝ) / ((two40 : ℕ) : ℝ)) =
      ((E : ℝ) + Cw + leb4 (W 0) (W 1) (W 2) (W 3) Cs + leb4 (M 0) (M 1) (M 2) (M 3) RW +
        (Rm 1 1).rt) / ((two40 : ℕ) : ℝ) := by ring
  linarith

end PlasmaLean.Design.PolygonCoil
