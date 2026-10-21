/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCubicSoundA
public import PlasmaLean.Design.PolygonCoilCubicHel
public import PlasmaLean.Design.PolygonCoilSoundC

/-!
# Soundness of the cubic checker, part B: the interpolation remainders

* `segClosed_cubic`: the cubic interpolation error of `⟨n, segClosed⟩` along a curve is at most
  `|κ||q - p| K |ω|/24` if `|g⁗| ≤ |n||q - p| K` for the kernel (`segField_cubic_bound`);
* `BL_cubic`: the same for a list of segments (sum of the bounds);
* `remTW_ge`, `remTT_ge`: the checker terms dominate `2⁴⁰ |κ||q - p| K(d)` with `d = √L/λ`;
* `kt_bound`: the fourth derivative of the kernel along the rational circle is at most
  `c₆/d⁶ + c₄/d⁴ + c₂/d²` (from `abs_kgD4_le` and the circle facts of `PolygonCoilCubicGeom`).
-/

public section
noncomputable section

namespace PlasmaLean.Design.PolygonCoil
open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator
  PlasmaLean.Design.RationalStellarator.Coils PlasmaLean.Design.RationalStellarator.CoilsTF Set Real
open scoped RealInnerProductSpace

/-! ## Linearity of the interpolant -/

theorem newt_add (x0 x1 x2 x3 a0 a1 a2 a3 b0 b1 b2 b3 y : ℝ) :
    newt x0 x1 x2 x3 (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3) y =
      newt x0 x1 x2 x3 a0 a1 a2 a3 y + newt x0 x1 x2 x3 b0 b1 b2 b3 y := by
  unfold newt dd3 dd2; ring

/-- `newt` is additive in the data (difference). -/
theorem newt_sub (x0 x1 x2 x3 a0 a1 a2 a3 b0 b1 b2 b3 y : ℝ) :
    newt x0 x1 x2 x3 (a0 - b0) (a1 - b1) (a2 - b2) (a3 - b3) y =
      newt x0 x1 x2 x3 a0 a1 a2 a3 y - newt x0 x1 x2 x3 b0 b1 b2 b3 y := by
  unfold newt dd3 dd2; ring

/-- `newt` of zero data is zero. -/
theorem newt_zero (x0 x1 x2 x3 y : ℝ) : newt x0 x1 x2 x3 0 0 0 0 y = 0 := by
  unfold newt dd3 dd2; ring

/-! ## Segment fields -/

/-- **Cubic interpolation bound for the closed-form field of one segment.** -/
theorem segClosed_cubic (n : Space) (hn : ‖n‖ ≤ 1) (z : ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ))
    {σ σ1 σ2 σ3 σ4 : ℝ → Space} {x0 x1 x2 x3 y d K : ℝ} (h01 : x0 < x1) (h12 : x1 < x2)
    (h23 : x2 < x3) (hy : y ∈ Icc x1 x2) (hd : 0 < d) (hK0 : 0 ≤ K)
    (hσ : ∀ τ ∈ Icc x0 x3, HasDerivAt σ (σ1 τ) τ) (hσ1 : ∀ τ ∈ Icc x0 x3, HasDerivAt σ1 (σ2 τ) τ)
    (hσ2 : ∀ τ ∈ Icc x0 x3, HasDerivAt σ2 (σ3 τ) τ) (hσ3 : ∀ τ ∈ Icc x0 x3, HasDerivAt σ3 (σ4 τ) τ)
    (hsep : ∀ τ ∈ Icc x0 x3, ∀ s ∈ Icc (0 : ℝ) 1, d ≤ ‖σ τ - seg (ptR z.2.1) (ptR z.2.2) s‖)
    (hK : ∀ τ ∈ Icc x0 x3, ∀ s ∈ Icc (0 : ℝ) 1,
      |kgD4 (cross n (ptR z.2.2 - ptR z.2.1)) (σ τ - seg (ptR z.2.1) (ptR z.2.2) s) (σ1 τ) (σ2 τ)
        (σ3 τ) (σ4 τ)| ≤ ‖n‖ * ‖ptR z.2.2 - ptR z.2.1‖ * K) :
    |⟪n, segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2) (σ y)⟫ -
        newt x0 x1 x2 x3 ⟪n, segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2) (σ x0)⟫
          ⟪n, segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2) (σ x1)⟫
          ⟪n, segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2) (σ x2)⟫
          ⟪n, segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2) (σ x3)⟫ y| ≤
      kvR z * K * |omega4 x0 x1 x2 x3 y| / 24 := by
  have hκ : (1 : ℝ) * (4 * π * ((z.1 : ℝ) / S32)) / (4 * π) = (z.1 : ℝ) / S32 := by
    field_simp
  have e : ∀ y, segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2) y =
      filamentField 1 (4 * π * ((z.1 : ℝ) / S32)) (seg (ptR z.2.1) (ptR z.2.2)) 0 1 y := by
    intro y; rw [segField_eq_closed, hκ]
  simp only [e]
  have h := segField_cubic_bound 1 (4 * π * ((z.1 : ℝ) / S32)) (ptR z.2.1) (ptR z.2.2) n h01 h12 h23
    hy hd hσ hσ1 hσ2 hσ3 hsep hK
  rw [hκ] at h
  refine h.trans ?_
  have hω := abs_nonneg (omega4 x0 x1 x2 x3 y)
  unfold kvR
  have hq := norm_nonneg (ptR z.2.2 - ptR z.2.1)
  have : |(z.1 : ℝ) / S32| * (‖n‖ * ‖ptR z.2.2 - ptR z.2.1‖ * K) ≤
      |(z.1 : ℝ) / S32| * ‖ptR z.2.2 - ptR z.2.1‖ * K := by
    have : ‖n‖ * ‖ptR z.2.2 - ptR z.2.1‖ * K ≤ ‖ptR z.2.2 - ptR z.2.1‖ * K := by
      have := mul_le_mul_of_nonneg_right hn hq
      nlinarith [mul_nonneg hq hK0]
    nlinarith [abs_nonneg ((z.1 : ℝ) / S32)]
  have := mul_le_mul_of_nonneg_right this hω
  linarith

/-- **Cubic interpolation bound for a list of segments** (indexed by any type, with a
distance `dd i` and a kernel constant `Kf i` per index). -/
theorem BL_cubic {ι : Type} (n : Space) (hn : ‖n‖ ≤ 1)
    (sg : ι → ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)) (dd Kf : ι → ℝ)
    {σ σ1 σ2 σ3 σ4 : ℝ → Space} {x0 x1 x2 x3 y : ℝ} (h01 : x0 < x1) (h12 : x1 < x2)
    (h23 : x2 < x3) (hy : y ∈ Icc x1 x2)
    (hσ : ∀ τ ∈ Icc x0 x3, HasDerivAt σ (σ1 τ) τ) (hσ1 : ∀ τ ∈ Icc x0 x3, HasDerivAt σ1 (σ2 τ) τ)
    (hσ2 : ∀ τ ∈ Icc x0 x3, HasDerivAt σ2 (σ3 τ) τ)
        (hσ3 : ∀ τ ∈ Icc x0 x3, HasDerivAt σ3 (σ4 τ) τ) :
    ∀ L : List ι, (∀ i ∈ L, 0 < dd i) → (∀ i ∈ L, 0 ≤ Kf i) →
      (∀ i ∈ L, ∀ τ ∈ Icc x0 x3, ∀ s ∈ Icc (0 : ℝ) 1,
        dd i ≤ ‖σ τ - seg (ptR (sg i).2.1) (ptR (sg i).2.2) s‖) →
      (∀ i ∈ L, ∀ τ ∈ Icc x0 x3, ∀ s ∈ Icc (0 : ℝ) 1,
        |kgD4 (cross n (ptR (sg i).2.2 - ptR (sg i).2.1))
          (σ τ - seg (ptR (sg i).2.1) (ptR (sg i).2.2) s) (σ1 τ) (σ2 τ) (σ3 τ) (σ4 τ)| ≤
          ‖n‖ * ‖ptR (sg i).2.2 - ptR (sg i).2.1‖ * Kf i) →
      |⟪n, BL (L.map sg) (σ y)⟫ - newt x0 x1 x2 x3 ⟪n, BL (L.map sg) (σ x0)⟫
          ⟪n, BL (L.map sg) (σ x1)⟫ ⟪n, BL (L.map sg) (σ x2)⟫ ⟪n, BL (L.map sg) (σ x3)⟫ y| ≤
        (L.map fun i => kvR (sg i) * Kf i).sum * |omega4 x0 x1 x2 x3 y| / 24
  | [], _, _, _, _ => by simp [BL, newt_zero]
  | i :: L, hdd, hKf, hsep, hK => by
    have h1 := segClosed_cubic n hn (sg i) h01 h12 h23 hy (hdd i (by simp)) (hKf i (by simp)) hσ
      hσ1 hσ2 hσ3 (hsep i (by simp)) (hK i (by simp))
    have h2 := BL_cubic n hn sg dd Kf h01 h12 h23 hy hσ hσ1 hσ2 hσ3 L
      (fun w hw => hdd w (by simp [hw])) (fun w hw => hKf w (by simp [hw]))
      (fun w hw => hsep w (by simp [hw])) (fun w hw => hK w (by simp [hw]))
    have eBL : ∀ v, BL ((i :: L).map sg) v =
        segClosed (((sg i).1 : ℝ) / S32) (ptR (sg i).2.1) (ptR (sg i).2.2) v + BL (L.map sg) v := by
      intro v; simp [BL]
    simp only [eBL, inner_add_right, newt_add]
    simp only [List.map_cons, List.sum_cons]
    set A := ⟪n, segClosed (((sg i).1 : ℝ) / S32) (ptR (sg i).2.1) (ptR (sg i).2.2) (σ y)⟫ -
      newt x0 x1 x2 x3 ⟪n, segClosed (((sg i).1 : ℝ) / S32) (ptR (sg i).2.1) (ptR (sg i).2.2) (σ
          x0)⟫
        ⟪n, segClosed (((sg i).1 : ℝ) / S32) (ptR (sg i).2.1) (ptR (sg i).2.2) (σ x1)⟫
        ⟪n, segClosed (((sg i).1 : ℝ) / S32) (ptR (sg i).2.1) (ptR (sg i).2.2) (σ x2)⟫
        ⟪n, segClosed (((sg i).1 : ℝ) / S32) (ptR (sg i).2.1) (ptR (sg i).2.2) (σ x3)⟫ y
    set B := ⟪n, BL (L.map sg) (σ y)⟫ - newt x0 x1 x2 x3 ⟪n, BL (L.map sg) (σ x0)⟫
      ⟪n, BL (L.map sg) (σ x1)⟫ ⟪n, BL (L.map sg) (σ x2)⟫ ⟪n, BL (L.map sg) (σ x3)⟫ y
    have e : ⟪n, segClosed (((sg i).1 : ℝ) / S32) (ptR (sg i).2.1) (ptR (sg i).2.2) (σ y)⟫ +
        ⟪n, BL (L.map sg) (σ y)⟫ -
        (newt x0 x1 x2 x3
          ⟪n, segClosed (((sg i).1 : ℝ) / S32) (ptR (sg i).2.1) (ptR (sg i).2.2) (σ x0)⟫
          ⟪n, segClosed (((sg i).1 : ℝ) / S32) (ptR (sg i).2.1) (ptR (sg i).2.2) (σ x1)⟫
          ⟪n, segClosed (((sg i).1 : ℝ) / S32) (ptR (sg i).2.1) (ptR (sg i).2.2) (σ x2)⟫
          ⟪n, segClosed (((sg i).1 : ℝ) / S32) (ptR (sg i).2.1) (ptR (sg i).2.2) (σ x3)⟫ y +
        newt x0 x1 x2 x3 ⟪n, BL (L.map sg) (σ x0)⟫ ⟪n, BL (L.map sg) (σ x1)⟫
          ⟪n, BL (L.map sg) (σ x2)⟫ ⟪n, BL (L.map sg) (σ x3)⟫ y) = A + B := by
      simp only [A, B]; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have : (kvR (sg i) * Kf i + (L.map fun i => kvR (sg i) * Kf i).sum) *
        |omega4 x0 x1 x2 x3 y| / 24 = kvR (sg i) * Kf i * |omega4 x0 x1 x2 x3 y| / 24 +
          (L.map fun i => kvR (sg i) * Kf i).sum * |omega4 x0 x1 x2 x3 y| / 24 := by ring
    rw [this]
    exact add_le_add h1 h2

/-! ## Distances from the records -/

/-- **Distance bound from a corner record**: if `L = cellL rc d2Low > 0`, every point `x` with
`λ|x - y| ≤ rBD` is at distance `≥ √L/λ` from the segment. -/
theorem rec_dist {o : Offs} {Xt Yt Zt D : ℕ} (hD : 0 < D) {z : SRec}
    (hva : VRok Xt Yt Zt D z.2.1 z.2.2.2.1) (hvb : VRok Xt Yt Zt D z.2.2.1 z.2.2.2.2)
    (hs : segOK o z.1 z.2.1 z.2.2.1 = true) (rc : RC) (hrs : rc.rBD ≤ rc.s0l) (hs0 : 0 < rc.s0l)
    (hL : 0 < cellL rc (d2Low z.2.2.2.1.n z.2.2.2.2.n
      (Nat.mul (Nat.mul D D) (mkSeg o z.1 z.2.1 z.2.2.1).vv)))
    {x : Space} (hx : (D : ℝ) * S32 * ‖x - cornerR Xt Yt Zt D‖ ≤ rc.rBD) {s : ℝ}
    (hs' : s ∈ Icc (0 : ℝ) 1) :
    (cellL rc (d2Low z.2.2.2.1.n z.2.2.2.2.n (Nat.mul (Nat.mul D D) (mkSeg o z.1 z.2.1 z.2.2.1).vv))
      : ℝ) ≤ ((D : ℝ) * S32) ^ 2 * ‖x - seg (ptR z.2.1) (ptR z.2.2.1) s‖ ^ 2 := by
  set lam := (D : ℝ) * S32
  have hlam : 0 < lam := mul_pos (by exact_mod_cast hD) S32_pos
  set y := cornerR Xt Yt Zt D
  set A := lam • (ptR z.2.1 - y)
  set B := lam • (ptR z.2.2.1 - y)
  have hnA : ‖A‖ ^ 2 = lam ^ 2 * ‖ptR z.2.1 - y‖ ^ 2 := by
    simp only [A, norm_smul, Real.norm_eq_abs, abs_of_pos hlam]; ring
  have hnB : ‖B‖ ^ 2 = lam ^ 2 * ‖ptR z.2.2.1 - y‖ ^ 2 := by
    simp only [B, norm_smul, Real.norm_eq_abs, abs_of_pos hlam]; ring
  have hna : (z.2.2.2.1.n : ℝ) = ‖A‖ ^ 2 := by rw [hnA, hva.1]
  have hnb : (z.2.2.2.2.n : ℝ) = ‖B‖ ^ 2 := by rw [hnB, hvb.1]
  have hw := mkSeg_weights hs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hvv⟩ := hw
  have hdv : ((Nat.mul (Nat.mul D D) (mkSeg o z.1 z.2.1 z.2.2.1).vv : ℕ) : ℝ) = ‖B - A‖ ^ 2 := by
    rw [lam_diff_norm Xt Yt Zt D hD z.2.1 z.2.2.1]
    push_cast [Nat.mul_eq]
    rw [hvv]; push_cast; ring
  have hvpos : 0 < Nat.mul (Nat.mul D D) (mkSeg o z.1 z.2.1 z.2.2.1).vv := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hpos, -⟩ := segOK_spec hs
    apply Nat.mul_pos (Nat.mul_pos hD hD)
    have hpos' := (Int.cast_pos (R := ℝ)).mpr hpos
    have : (0 : ℝ) < (mkSeg o z.1 z.2.1 z.2.2.1).vv := by
      rw [hvv]; push_cast at hpos' ⊢; nlinarith
    exact_mod_cast this
  have hd2 := d2Low_sound hna hnb hdv hvpos hs'
  have eAB : A + s • (B - A) = lam • (seg (ptR z.2.1) (ptR z.2.2.1) s - y) := by
    simp only [A, B, seg, smul_sub, smul_add]
    rw [smul_comm s lam]; module
  rw [eAB, norm_smul, Real.norm_eq_abs, abs_of_pos hlam, mul_pow] at hd2
  have hd2' : (d2Low z.2.2.2.1.n z.2.2.2.2.n (Nat.mul (Nat.mul D D) (mkSeg o z.1 z.2.1 z.2.2.1).vv)
      : ℝ) ≤ lam ^ 2 * ‖y - seg (ptR z.2.1) (ptR z.2.2.1) s‖ ^ 2 := by
    rw [norm_sub_rev]; exact hd2
  exact cellL_sound rc hlam hd2' hx hrs hs0 hL

/-! ## The checker terms -/

/-- `kv ≥ 2⁶⁴|κ||q - p|`. -/
theorem kv_ge {o : Offs} {K : ℤ} {p q : ℤ × ℤ × ℤ} (h : segOK o K p q = true) :
    ((two64 : ℕ) : ℝ) * kvR (K, p, q) ≤ ((mkSeg o K p q).kv : ℝ) := by
  have := kvR_le h
  have h64 : (0 : ℝ) < ((two64 : ℕ) : ℝ) := by norm_num [two64]
  rw [le_div_iff₀ h64] at this; linarith

/-- **The `t`-term dominates the kernel bound** at `d = √L/λ`. -/
theorem term_ge {kv L A6 A4 A2 : ℕ} {lam kvr c6 c4 c2 : ℝ} (hL : 0 < L) (hlam : 0 < lam)
    (hkv : ((two64 : ℕ) : ℝ) * kvr ≤ kv) (hc6 : 0 ≤ c6) (hc4 : 0 ≤ c4)
    (hc2 : 0 ≤ c2) (h6 : c6 * lam ^ 6 ≤ A6) (h4 : c4 * lam ^ 4 ≤ A4) (h2 : c2 * lam ^ 2 ≤ A2) :
    ((two40 : ℕ) : ℝ) * (kvr * (c6 / (Real.sqrt L / lam) ^ 6 + c4 / (Real.sqrt L / lam) ^ 4 +
      c2 / (Real.sqrt L / lam) ^ 2)) ≤
      (cdiv (Nat.mul kv (Nat.add A6 (Nat.mul L (Nat.add A4 (Nat.mul L A2)))))
        (Nat.mul (Nat.mul (Nat.mul L L) L) two24) : ℝ) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hs2 : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL'.le
  have hsp : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL'
  have hden : 0 < Nat.mul (Nat.mul (Nat.mul L L) L) two24 := by
    apply Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hL hL) hL); norm_num [two24]
  refine le_trans ?_ (cdiv_ge _ hden)
  push_cast [Nat.mul_eq, Nat.add_eq]
  have e6 : (Real.sqrt L / lam) ^ 6 = L ^ 3 / lam ^ 6 := by
    rw [div_pow, show Real.sqrt L ^ 6 = (Real.sqrt L ^ 2) ^ 3 by ring, hs2]
  have e4 : (Real.sqrt L / lam) ^ 4 = L ^ 2 / lam ^ 4 := by
    rw [div_pow, show Real.sqrt L ^ 4 = (Real.sqrt L ^ 2) ^ 2 by ring, hs2]
  have e2 : (Real.sqrt L / lam) ^ 2 = L / lam ^ 2 := by rw [div_pow, hs2]
  rw [e6, e4, e2]
  have h40 : ((two40 : ℕ) : ℝ) * ((two24 : ℕ) : ℝ) = ((two64 : ℕ) : ℝ) := by
    norm_num [two40, two24, two64]
  have h24 : (0 : ℝ) < ((two24 : ℕ) : ℝ) := by norm_num [two24]
  rw [div_div_eq_mul_div, div_div_eq_mul_div, div_div_eq_mul_div, le_div_iff₀ (by positivity)]
  have key : ((two40 : ℕ) : ℝ) * (kvr * (c6 * lam ^ 6 / L ^ 3 + c4 * lam ^ 4 / L ^ 2 +
      c2 * lam ^ 2 / L)) * (L * L * L * ((two24 : ℕ) : ℝ)) =
      (((two64 : ℕ) : ℝ) * kvr) * (c6 * lam ^ 6 + L * (c4 * lam ^ 4 + L * (c2 * lam ^ 2))) := by
    rw [← h40]; field_simp; ring
  rw [key]
  apply mul_le_mul hkv _ (by positivity) (Nat.cast_nonneg _)
  have := mul_le_mul_of_nonneg_left h2 hL'.le
  have := mul_le_mul_of_nonneg_left (add_le_add h4 this) hL'.le
  linarith

/-- **The `w`-term dominates `120/d⁶`** at `d = √L/λ`. -/
theorem termW_ge {kv L A6 : ℕ} {lam kvr : ℝ} (hL : 0 < L) (hlam : 0 < lam)
    (hkv : ((two64 : ℕ) : ℝ) * kvr ≤ kv) (h6 : 120 * lam ^ 6 ≤ A6) :
    ((two40 : ℕ) : ℝ) * (kvr * (120 / (Real.sqrt L / lam) ^ 6)) ≤
      (cdiv (Nat.mul kv A6) (Nat.mul (Nat.mul (Nat.mul L L) L) two24) : ℝ) := by
  have h := term_ge (A4 := 0) (A2 := 0) (c4 := 0) (c2 := 0) hL hlam hkv (by norm_num) le_rfl
    le_rfl h6 (by simp) (by simp)
  simp only [zero_div, add_zero] at h
  exact h

/-! ## The kernel along the rational circle -/

theorem amgm5 {r : ℝ} (hr : 0 < r) : 1 / r ^ 5 ≤ 1 / (6 * r ^ 6) + 3 / (2 * r ^ 4) := by
  rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
    (by positivity)]
  nlinarith [sq_nonneg (3 * r - 1), pow_pos hr 9, pow_pos hr 10, pow_pos hr 8,
    mul_nonneg (sq_nonneg (3 * r - 1)) (pow_pos hr 9).le]

/-- AM-GM: `1/r³ ≤ 1/(6r⁴) + 3/(2r²)`. -/
theorem amgm3 {r : ℝ} (hr : 0 < r) : 1 / r ^ 3 ≤ 1 / (6 * r ^ 4) + 3 / (2 * r ^ 2) := by
  rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
    (by positivity)]
  nlinarith [sq_nonneg (3 * r - 1), pow_pos hr 5, pow_pos hr 4, pow_pos hr 3,
    mul_nonneg (sq_nonneg (3 * r - 1)) (pow_pos hr 5).le]

/-- `c/r^k ≤ c/d^k` for `0 < d ≤ r`. -/
theorem div_pow_anti {c d r : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (hdr : d ≤ r) (k : ℕ) :
    c / r ^ k ≤ c / d ^ k :=
  div_le_div_of_nonneg_left hc (by positivity) (pow_le_pow_left₀ hd.le hdr k)

/-- The fifth-power coefficient of the circle bound. -/
@[expose] def kc5 (ρ Tm tm : ℝ) : ℝ := (2304 * tm + 2309) * ρ ^ 3 * Tm ^ 4
/-- The `d⁻⁶` coefficient of the circle bound. -/
@[expose] def kc6 (ρ Tm tm : ℝ) : ℝ := 1920 * ρ ^ 4 * Tm ^ 4 + kc5 ρ Tm tm / 6
/-- The `d⁻⁴` coefficient of the circle bound. -/
@[expose] def kc4 (ρ Tm tm : ℝ) : ℝ := 3 * kc5 ρ Tm tm / 2 + 864 * ρ ^ 2 + 16 * ρ
/-- The `d⁻²` coefficient of the circle bound. -/
@[expose] def kc2 (ρ : ℝ) : ℝ := 144 * ρ

/-- **Fourth derivative of the kernel along the rational circle.** -/
theorem kt_bound (m y : Space) {ρ ζ τ d Tm tm : ℝ} (hρ : 0 < ρ) (hd : 0 < d)
    (hdist : d ≤ ‖circ ρ ζ τ - y‖) (hT : 1 / (1 + τ ^ 2) ≤ Tm) (hTm : Tm ≤ 1) (htm : |τ| ≤ tm) :
    |kgD4 m (circ ρ ζ τ - y) (U1 ρ τ) (U2 ρ τ) (U3 ρ τ) (U4 ρ τ)| ≤
      ‖m‖ * (kc6 ρ Tm tm / d ^ 6 + kc4 ρ Tm tm / d ^ 4 + kc2 ρ / d ^ 2) := by
  set r := ‖circ ρ ζ τ - y‖
  have hr : 0 < r := lt_of_lt_of_le hd hdist
  have hx : circ ρ ζ τ - y ≠ 0 := norm_pos_iff.mp hr
  have h0 : (0 : ℝ) < 1 + τ ^ 2 := by positivity
  have hT0 : 0 < Tm := lt_of_lt_of_le (by positivity) hT
  have htm0 : 0 ≤ tm := (abs_nonneg _).trans htm
  set l := Real.sqrt 6
  have hl : 0 < l := Real.sqrt_pos.mpr (by norm_num)
  have hl2 : l ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hS1 : ‖U1 ρ τ‖ ≤ 2 * ρ * Tm := by
    rw [norm_U1 hρ.le]
    have : 2 * ρ / (1 + τ ^ 2) = 2 * ρ * (1 / (1 + τ ^ 2)) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_left hT (by positivity)
  have hSp : ‖U2 ρ τ - alT τ • U1 ρ τ‖ ≤ 4 * ρ * Tm ^ 2 := by
    rw [norm_U2perp hρ.le]
    have : 4 * ρ / (1 + τ ^ 2) ^ 2 = 4 * ρ * (1 / (1 + τ ^ 2)) ^ 2 := by
      rw [div_pow, one_pow]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hT 2) (by positivity)
  have h := abs_kgD4_le m (circ ρ ζ τ - y) (U1 ρ τ) (U2 ρ τ) (U3 ρ τ) (U4 ρ τ) hx
    (S1 := 2 * ρ * Tm) (Sp := 4 * ρ * Tm ^ 2) (S2 := 4 * ρ) (S3 := 12 * ρ) (S4 := 48 * ρ)
    (α := alT τ) (l := l) (by positivity) (by positivity) hl hS1 (U1_perp ρ τ) hSp
    (norm_U2_le hρ.le τ) (norm_U3_le hρ.le τ) (norm_U4_le hρ.le τ)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  -- `|α| ≤ 2 tm Tm`
  have hα : |alT τ| ≤ 2 * tm * Tm := by
    unfold alT
    rw [abs_div, abs_of_pos h0, abs_mul, abs_neg, abs_two]
    have : 2 * |τ| / (1 + τ ^ 2) = 2 * |τ| * (1 / (1 + τ ^ 2)) := by ring
    rw [this]
    exact mul_le_mul (by linarith) hT (by positivity) (by positivity)
  have t5 : 6 * (24 * |alT τ| * (2 * ρ * Tm) ^ 3 + 1002 / 1000 * 24 * (2 * ρ * Tm) ^ 2 *
      (4 * ρ * Tm ^ 2)) ≤ kc5 ρ Tm tm := by
    unfold kc5
    have : 24 * |alT τ| * (2 * ρ * Tm) ^ 3 ≤ 24 * (2 * tm * Tm) * (2 * ρ * Tm) ^ 3 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith [pow_pos hρ 3, pow_pos hT0 4, mul_pos (pow_pos hρ 3) (pow_pos hT0 4)]
  have t4 : 12 * (l ^ 2 * (2 * ρ * Tm) ^ 2 + (12 * ρ) ^ 2 / l ^ 2) + 18 * (4 * ρ) ^ 2 ≤
      864 * ρ ^ 2 := by
    rw [hl2]
    have : Tm ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg ρ, mul_le_mul_of_nonneg_left this (sq_nonneg ρ)]
  have b6 := div_pow_anti (c := 120 * (2 * ρ * Tm) ^ 4) (by positivity) hd hdist 6
  have b5 := div_pow_anti (c := kc5 ρ Tm tm) (by unfold kc5; positivity) hd hdist 5
  have b4 := div_pow_anti (c := 864 * ρ ^ 2) (by positivity) hd hdist 4
  have b3 := div_pow_anti (c := 2 * (48 * ρ)) (by positivity) hd hdist 3
  have a5 := amgm5 hd
  have a3 := amgm3 hd
  have k5 : 0 ≤ kc5 ρ Tm tm := by unfold kc5; positivity
  -- assemble
  have e1 : 6 * (24 * |alT τ| * (2 * ρ * Tm) ^ 3 + 1002 / 1000 * 24 * (2 * ρ * Tm) ^ 2 *
      (4 * ρ * Tm ^ 2)) / r ^ 5 ≤ kc5 ρ Tm tm / r ^ 5 :=
    div_le_div_of_nonneg_right t5 (by positivity)
  have e2 : 12 * (l ^ 2 * (2 * ρ * Tm) ^ 2 + (12 * ρ) ^ 2 / l ^ 2) / r ^ 4 + 18 * (4 * ρ) ^ 2 / r ^
      4
      ≤ 864 * ρ ^ 2 / r ^ 4 := by
    rw [← add_div]; exact div_le_div_of_nonneg_right t4 (by positivity)
  have e5 : kc5 ρ Tm tm / d ^ 5 ≤ kc5 ρ Tm tm / (6 * d ^ 6) + 3 * kc5 ρ Tm tm / (2 * d ^ 4) := by
    have := mul_le_mul_of_nonneg_left a5 k5
    calc kc5 ρ Tm tm / d ^ 5 = kc5 ρ Tm tm * (1 / d ^ 5) := by ring
      _ ≤ kc5 ρ Tm tm * (1 / (6 * d ^ 6) + 3 / (2 * d ^ 4)) := this
      _ = _ := by ring
  have e3 : 2 * (48 * ρ) / d ^ 3 ≤ 16 * ρ / d ^ 4 + 144 * ρ / d ^ 2 := by
    have := mul_le_mul_of_nonneg_left a3 (by positivity : (0 : ℝ) ≤ 96 * ρ)
    calc 2 * (48 * ρ) / d ^ 3 = 96 * ρ * (1 / d ^ 3) := by ring
      _ ≤ 96 * ρ * (1 / (6 * d ^ 4) + 3 / (2 * d ^ 2)) := this
      _ = 16 * ρ / d ^ 4 + 144 * ρ / d ^ 2 := by field_simp; ring
  have e6 : 120 * (2 * ρ * Tm) ^ 4 / d ^ 6 = 1920 * ρ ^ 4 * Tm ^ 4 / d ^ 6 := by ring
  unfold kc6 kc4 kc2
  have : (1920 * ρ ^ 4 * Tm ^ 4 + kc5 ρ Tm tm / 6) / d ^ 6 +
      (3 * kc5 ρ Tm tm / 2 + 864 * ρ ^ 2 + 16 * ρ) / d ^ 4 + 144 * ρ / d ^ 2 =
      1920 * ρ ^ 4 * Tm ^ 4 / d ^ 6 + (kc5 ρ Tm tm / (6 * d ^ 6) + 3 * kc5 ρ Tm tm / (2 * d ^ 4)) +
        864 * ρ ^ 2 / d ^ 4 + (16 * ρ / d ^ 4 + 144 * ρ / d ^ 2) := by field_simp; ring
  rw [this]
  linarith

end PlasmaLean.Design.PolygonCoil
