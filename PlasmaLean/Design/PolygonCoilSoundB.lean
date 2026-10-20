/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilSoundA
public import PlasmaLean.Design.PolygonCoilCurve

/-!
# Soundness of the polygonal-coil checker, part B: `hel`, faces, remainders, cells

* `helAt_val`: the exact-rational evaluation of `hel` at a grid corner is `hel` there;
* `cornerR_cornerXYZ`: the grid corners are the points `σ_F(φ_m, w_j)` of the face
  parametrisations `faceSigma` (`φ_m = 2 arctan(m/4096)`);
* `d2Low_sound`, `cellL_sound`, `remTerm_sound`: the remainder term of one segment dominates its
  contribution to the bilinear interpolation error on the cell;
* `cell_sound` (**cell bound**): if the four corners pass and `max e + rem ≤ η`, then
  `‖Bseg - hel‖ ≤ η` on the whole cell.
-/

public section
noncomputable section

namespace PlasmaLean.Design.PolygonCoil
open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator
    PlasmaLean.Design.RationalStellarator.Coils
  PlasmaLean.Design.RationalStellarator.CoilsTF Set Real
open scoped RealInnerProductSpace

/-! ## Exact rationals -/

theorem QQ.val_add (x y : QQ) (hx : 0 < x.den) (hy : 0 < y.den) :
    (x.add y).val = x.val + y.val := by
  have hx' : (x.den : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
  have hy' : (y.den : ℝ) ≠ 0 := by exact_mod_cast hy.ne'
  simp only [QQ.add, QQ.val]; push_cast; field_simp

theorem QQ.val_sub (x y : QQ) (hx : 0 < x.den) (hy : 0 < y.den) :
    (x.sub y).val = x.val - y.val := by
  have hx' : (x.den : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
  have hy' : (y.den : ℝ) ≠ 0 := by exact_mod_cast hy.ne'
  simp only [QQ.sub, QQ.val]; push_cast; field_simp

theorem QQ.val_mul (x y : QQ) : (x.mul y).val = x.val * y.val := by
  simp only [QQ.mul, QQ.val]; push_cast; rw [div_mul_div_comm]

theorem QQ.val_ofInt (a : ℤ) : (QQ.ofInt a).val = a := by simp [QQ.ofInt, QQ.val]

theorem QQ.val_inv (x : QQ) (hn : 0 < x.num) : (x.inv).val = 1 / x.val := by
  simp only [QQ.inv, QQ.val]
  rw [toNat_cast_real hn.le]
  rw [one_div_div]
  simp

theorem QQ.den_add (x y : QQ) (hx : 0 < x.den) (hy : 0 < y.den) : 0 < (x.add y).den :=
  Nat.mul_pos hx hy
theorem QQ.den_sub (x y : QQ) (hx : 0 < x.den) (hy : 0 < y.den) : 0 < (x.sub y).den :=
  Nat.mul_pos hx hy
theorem QQ.den_mul (x y : QQ) (hx : 0 < x.den) (hy : 0 < y.den) : 0 < (x.mul y).den :=
  Nat.mul_pos hx hy
theorem QQ.den_inv (x : QQ) (hn : 0 < x.num) : 0 < (x.inv).den := by
  simp only [QQ.inv]; omega

/-! ## `hel` at a grid corner -/

/-- **The exact-rational `hel` of the checker** is the polar formula. -/
theorem helAt_val (rn zn cn sn : ℤ) (rd zd cd sd : ℕ) (hrn : 0 < rn) (hrd : 0 < rd) (hzd : 0 < zd)
    (hcd : 0 < cd) (hsd : 0 < sd) :
    let ρ : ℝ := rn / rd
    let ζ : ℝ := zn / zd
    let c : ℝ := cn / cd
    let s : ℝ := sn / sd
    let h := helAt (helCoef ⟨rn, rd⟩ ⟨zn, zd⟩) (mkTrig ⟨cn, cd⟩ ⟨sn, sd⟩)
    (0 < h.1.den ∧ 0 < h.2.1.den ∧ 0 < h.2.2.den) ∧
    h.1.val = cA ρ * c + cB ρ ζ * s + cG ρ ζ * (4 * c ^ 3 - 3 * c) + cD ρ ζ * (3 * s - 4 * s ^ 3) ∧
    h.2.1.val = -cA ρ * s + cB ρ ζ * c + cG ρ ζ * (3 * s - 4 * s ^ 3) - cD ρ ζ * (4 * c ^ 3 - 3 *
        c) ∧
    h.2.2.val = cE ρ ζ * (2 * c * s) + cF ρ ζ * (c ^ 2 - s ^ 2) := by
  intro ρ ζ c s h
  have p8 : 0 < 8 * rn := by positivity
  have p83 : 0 < 8 * rn * rn * rn := by positivity
  have p16 : 0 < 16 * rn * rn := by positivity
  have p2 : 0 < 2 * rn * rn := by positivity
  have t8 : (((8 * rn).toNat : ℕ) : ℝ) = 8 * rn := by rw [toNat_cast_real p8.le]; push_cast; ring
  have t83 : (((8 * (rn * rn) * rn).toNat : ℕ) : ℝ) = 8 * rn * rn * rn := by
    rw [toNat_cast_real (by positivity)]; push_cast; ring
  have t16 : (((16 * (rn * rn)).toNat : ℕ) : ℝ) = 16 * rn * rn := by
    rw [toNat_cast_real (by positivity)]; push_cast; ring
  have t2 : (((2 * (rn * rn)).toNat : ℕ) : ℝ) = 2 * rn * rn := by
    rw [toNat_cast_real (by positivity)]; push_cast; ring
  have n8 : ((8 * rn).toNat) ≠ 0 := by omega
  have n83 : ((8 * (rn * rn) * rn).toNat) ≠ 0 := by
    have : 0 < 8 * (rn * rn) * rn := by positivity
    omega
  have n16 : ((16 * (rn * rn)).toNat) ≠ 0 := by
    have : 0 < 16 * (rn * rn) := by positivity
    omega
  have n2 : ((2 * (rn * rn)).toNat) ≠ 0 := by
    have : 0 < 2 * (rn * rn) := by positivity
    omega
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [h, helAt, helCoef, mkTrig, QQ.add, QQ.sub, QQ.mul, QQ.ofInt, QQ.inv]
    positivity
  · simp only [h, helAt, helCoef, mkTrig, QQ.add, QQ.sub, QQ.mul, QQ.ofInt, QQ.inv]
    positivity
  · simp only [h, helAt, helCoef, mkTrig, QQ.add, QQ.sub, QQ.mul, QQ.ofInt, QQ.inv]
    positivity
  all_goals
    simp only [h, helAt, helCoef, mkTrig, QQ.add, QQ.sub, QQ.mul, QQ.ofInt, QQ.inv, QQ.val,
      ρ, ζ, c, s, cA, cB, cG, cD, cE, cF, Int.ofNat_eq_natCast]
    push_cast [t8, t83, t16, t2]
    have : (rn : ℝ) ≠ 0 := by exact_mod_cast hrn.ne'
    have : (rd : ℝ) ≠ 0 := by exact_mod_cast hrd.ne'
    have : (zd : ℝ) ≠ 0 := by exact_mod_cast hzd.ne'
    have : (cd : ℝ) ≠ 0 := by exact_mod_cast hcd.ne'
    have : (sd : ℝ) ≠ 0 := by exact_mod_cast hsd.ne'
    field_simp
    try ring

/-! ## Faces -/

/-- The height of the plane faces: `+a` for kind `2`, `-a` otherwise. -/
@[expose] def planeZ (kind : ℕ) : ℝ := if kind = 2 then aF else -aF

/-- The parametrisation of the faces: cylinders `(R cos φ, R sin φ, w)`, planes
`(w cos φ, w sin φ, ±a)`. -/
@[expose] def faceSigma (kind : ℕ) (φ w : ℝ) : Space :=
  if kind < 2 then polarPt ((cylR kind : ℝ) / 181) w φ else polarPt w (planeZ kind) φ

/-- The grid angle `φ_m = 2 arctan(m/4096)`. -/
@[expose] def phiM (m : ℕ) : ℝ := 2 * arctan ((m : ℝ) / 4096)

theorem cos_phiM (m : ℕ) : cos (phiM m) = ((4096 : ℝ) ^ 2 - m ^ 2) / (4096 ^ 2 + m ^ 2) := by
  unfold phiM
  rw [cos_two_mul, cos_arctan]
  have h : 0 < 1 + ((m : ℝ) / 4096) ^ 2 := by positivity
  rw [div_pow, one_pow, sq_sqrt h.le]
  field_simp
  ring

theorem sin_phiM (m : ℕ) : sin (phiM m) = 2 * 4096 * (m : ℝ) / (4096 ^ 2 + m ^ 2) := by
  unfold phiM
  rw [sin_two_mul, cos_arctan, sin_arctan]
  have h : 0 < 1 + ((m : ℝ) / 4096) ^ 2 := by positivity
  have hs : sqrt (1 + ((m : ℝ) / 4096) ^ 2) * sqrt (1 + ((m : ℝ) / 4096) ^ 2) =
      1 + ((m : ℝ) / 4096) ^ 2 := mul_self_sqrt h.le
  calc 2 * ((m : ℝ) / 4096 / sqrt (1 + ((m : ℝ) / 4096) ^ 2)) * (1 / sqrt (1 + ((m : ℝ) / 4096) ^
      2))
      = 2 * ((m : ℝ) / 4096) / (sqrt (1 + ((m : ℝ) / 4096) ^ 2) *
          sqrt (1 + ((m : ℝ) / 4096) ^ 2)) := by ring
    _ = 2 * ((m : ℝ) / 4096) / (1 + ((m : ℝ) / 4096) ^ 2) := by rw [hs]
    _ = _ := by field_simp

/-- **The grid corners lie on the faces.** -/
theorem cornerR_cornerXYZ (F : Face) (hwd : 0 < F.wd) (m : ℕ) (wn : ℤ)
    (hok : (cornerXYZ F m wn).2 = true) :
    cornerR (cornerXYZ F m wn).1.1 (cornerXYZ F m wn).1.2.1 (cornerXYZ F m wn).1.2.2.1
      (cornerXYZ F m wn).1.2.2.2 = faceSigma F.kind (phiM m) ((wn : ℝ) / F.wd) ∧
      0 < (cornerXYZ F m wn).1.2.2.2 := by
  have hq : (0 : ℝ) < 4096 ^ 2 + (m : ℝ) ^ 2 := by positivity
  simp only [cornerXYZ, Bool.and_eq_true, decide_eq_true_eq] at hok ⊢
  obtain ⟨⟨hX, hY⟩, hZ⟩ := hok
  have hwd' : (0 : ℝ) < F.wd := by exact_mod_cast hwd
  by_cases hc : F.kind < 2
  · simp only [faceRZ, hc, ite_true] at hX hY hZ ⊢
    have hD : (0 : ℤ) < ((181 : ℕ) : ℤ) * ((qT : ℤ) * qT + (m : ℤ) * m) * (F.wd : ℤ) := by
      simp only [qT]; positivity
    refine ⟨?_, by omega⟩
    simp only [cornerR]
    rw [toNat_cast_real hX, toNat_cast_real hY, toNat_cast_real hZ, toNat_cast_real hD.le]
    simp only [faceSigma, hc, ite_true, polarPt, cos_phiM, sin_phiM, qT]
    ext i; fin_cases i <;> simp <;> field_simp <;> ring
  · simp only [faceRZ, hc, ite_false] at hX hY hZ ⊢
    have hD : (0 : ℤ) < (F.wd : ℤ) * ((qT : ℤ) * qT + (m : ℤ) * m) * ((32761 : ℕ) : ℤ) := by
      simp only [qT]; positivity
    refine ⟨?_, by omega⟩
    simp only [cornerR]
    rw [toNat_cast_real hX, toNat_cast_real hY, toNat_cast_real hZ, toNat_cast_real hD.le]
    simp only [faceSigma, hc, ite_false, polarPt, cos_phiM, sin_phiM, qT, planeZ, aF]
    by_cases h2 : F.kind = 2
    · simp only [h2, ite_true]
      ext i; fin_cases i <;> simp <;> field_simp <;> ring
    · simp only [h2, ite_false]
      ext i; fin_cases i <;> simp <;> field_simp <;> ring

/-! ## The remainder of one segment -/

/-- **Distance lower bound** from the corner–vertex distances: for `t ∈ [0, 1]`,
`d2Low ≤ |A + t(B - A)|²`. -/
theorem d2Low_sound {na nb dvv : ℕ} {A B : Space} (hna : (na : ℝ) = ‖A‖ ^ 2)
    (hnb : (nb : ℝ) = ‖B‖ ^ 2) (hdv : (dvv : ℝ) = ‖B - A‖ ^ 2) (hd : 0 < dvv) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : (d2Low na nb dvv : ℝ) ≤ ‖A + t • (B - A)‖ ^ 2 := by
  have hdv' : (0 : ℝ) < dvv := by exact_mod_cast hd
  have hg : ‖A + t • (B - A)‖ ^ 2 = na + t * ((nb : ℝ) - na - dvv) + t ^ 2 * dvv := by
    rw [norm_add_smul_sq, hna, hdv]
    have : ⟪A, B - A⟫ = (‖B‖ ^ 2 - ‖A‖ ^ 2 - ‖B - A‖ ^ 2) / 2 := by
      rw [norm_sub_sq_real]; rw [inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm B A]
      ring
    rw [this, ← hna, ← hnb, ← hdv]; ring
  obtain ⟨t0, t1⟩ := ht
  have hg0 : 0 ≤ ‖A + t • (B - A)‖ ^ 2 := by positivity
  unfold d2Low
  by_cases c1 : na + dvv ≤ nb
  · have hb : Nat.ble (Nat.add na dvv) nb = true := Nat.ble_eq_true_of_le c1
    rw [hb]
    simp only [Bool.cond_true]
    have : ((na : ℝ) + dvv) ≤ nb := by exact_mod_cast c1
    rw [hg]; nlinarith
  · have hb1 : Nat.ble (Nat.add na dvv) nb = false := by
      cases hb : Nat.ble (Nat.add na dvv) nb
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true hb) c1
    rw [hb1]
    simp only [Bool.cond_false]
    by_cases c2 : nb + dvv ≤ na
    · have hb : Nat.ble (Nat.add nb dvv) na = true := Nat.ble_eq_true_of_le c2
      rw [hb]
      simp only [Bool.cond_true]
      have : ((nb : ℝ) + dvv) ≤ na := by exact_mod_cast c2
      rw [hg]
      have e : (na : ℝ) + t * ((nb : ℝ) - na - dvv) + t ^ 2 * dvv - nb =
          (1 - t) * (((na : ℝ) - nb - dvv) + (1 - t) * dvv) := by ring
      have : 0 ≤ (1 - t) * (((na : ℝ) - nb - dvv) + (1 - t) * dvv) := by
        apply mul_nonneg (by linarith)
        nlinarith
      linarith
    · have hb2 : Nat.ble (Nat.add nb dvv) na = false := by
        cases hb : Nat.ble (Nat.add nb dvv) na
        · rfl
        · exact absurd (Nat.le_of_ble_eq_true hb) c2
      rw [hb2]
      simp only [Bool.cond_false]
      have hlt : nb < na + dvv := by omega
      have hsub : ((Nat.sub (Nat.add na dvv) nb : ℕ) : ℝ) = na + dvv - nb := by
        rw [nat_sub_cast (a := Nat.add na dvv) hlt.le]; push_cast [Nat.add_eq]; ring
      have h4 : 0 < Nat.mul 4 dvv := Nat.mul_pos (by norm_num) hd
      have hcd := cdiv_ge (sq (Nat.sub (Nat.add na dvv) nb)) h4
      have h4r : ((Nat.mul 4 dvv : ℕ) : ℝ) = 4 * dvv := by push_cast [Nat.mul_eq]; ring
      rw [sq_cast, hsub, h4r] at hcd
      -- minimum of the quadratic
      have hmin : (na : ℝ) - ((na : ℝ) + dvv - nb) ^ 2 / (4 * dvv) ≤ ‖A + t • (B - A)‖ ^ 2 := by
        rw [hg]
        have : (na : ℝ) + t * ((nb : ℝ) - na - dvv) + t ^ 2 * dvv -
            ((na : ℝ) - ((na : ℝ) + dvv - nb) ^ 2 / (4 * dvv)) =
            (2 * t * dvv + ((nb : ℝ) - na - dvv)) ^ 2 / (4 * dvv) := by
          field_simp; ring
        have : 0 ≤ (2 * t * dvv + ((nb : ℝ) - na - dvv)) ^ 2 / (4 * dvv) := by positivity
        linarith
      by_cases c3 : cdiv (sq (Nat.sub (Nat.add na dvv) nb)) (Nat.mul 4 dvv) ≤ na
      · rw [nat_sub_cast c3]; linarith
      · have : Nat.sub na (cdiv (sq (Nat.sub (Nat.add na dvv) nb)) (Nat.mul 4 dvv)) = 0 :=
          Nat.sub_eq_zero_of_le (by omega)
        rw [this]; simp only [Nat.cast_zero]; exact hg0

/-- **Cell distance**: if `d2 ≤ λ²|y - z|²`, `λ|x - y| ≤ rBD ≤ s₀λ` and `L = cellL r d2 > 0`, then
`L ≤ λ²|x - z|²`. -/
theorem cellL_sound (r : RC) {d2 : ℕ} {lam : ℝ} (hlam : 0 < lam) {x y z : Space}
    (hd2 : (d2 : ℝ) ≤ lam ^ 2 * ‖y - z‖ ^ 2) (hxy : lam * ‖x - y‖ ≤ r.rBD)
    (hrs : r.rBD ≤ r.s0l) (hs0 : 0 < r.s0l) (hL : 0 < cellL r d2) :
    (cellL r d2 : ℝ) ≤ lam ^ 2 * ‖x - z‖ ^ 2 := by
  unfold cellL at hL ⊢
  set c := cdiv (Nat.mul r.rBD d2) r.s0l
  have h1 : c ≤ d2 := by
    by_contra h; push Not at h
    have : Nat.sub d2 c = 0 := Nat.sub_eq_zero_of_le h.le
    rw [this] at hL; simp at hL
  have h2 : Nat.mul r.rBD r.s0l ≤ Nat.sub d2 c := by
    by_contra h; push Not at h
    have : Nat.sub (Nat.sub d2 c) (Nat.mul r.rBD r.s0l) = 0 := Nat.sub_eq_zero_of_le h.le
    rw [this] at hL; exact lt_irrefl _ hL
  rw [nat_sub_cast h2, nat_sub_cast h1]
  have hc := cdiv_ge (Nat.mul r.rBD d2) hs0
  push_cast [Nat.mul_eq] at hc ⊢
  have hs0' : (0 : ℝ) < r.s0l := by exact_mod_cast hs0
  have hrs' : (r.rBD : ℝ) ≤ r.s0l := by exact_mod_cast hrs
  have hr0 : (0 : ℝ) ≤ r.rBD := Nat.cast_nonneg _
  set X := lam * ‖y - z‖
  have hX0 : 0 ≤ X := by positivity
  have hd2X : (d2 : ℝ) ≤ X ^ 2 := by simp only [X]; rw [mul_pow]; exact hd2
  -- `L ≤ X² - 2 rBD X`
  have hL1 : (d2 : ℝ) - c - r.rBD * r.s0l ≤ X ^ 2 - 2 * r.rBD * X := by
    have hcc : (r.rBD : ℝ) * d2 / r.s0l ≤ c := hc
    have hmono : (d2 : ℝ) - r.rBD * d2 / r.s0l ≤ X ^ 2 - r.rBD * X ^ 2 / r.s0l := by
      have : (d2 : ℝ) - r.rBD * d2 / r.s0l = d2 * (1 - r.rBD / r.s0l) := by field_simp
      have h' : X ^ 2 - r.rBD * X ^ 2 / r.s0l = X ^ 2 * (1 - r.rBD / r.s0l) := by field_simp
      rw [this, h']
      have : 0 ≤ 1 - (r.rBD : ℝ) / r.s0l := by rw [sub_nonneg, div_le_one hs0']; exact hrs'
      exact mul_le_mul_of_nonneg_right hd2X this
    have hamgm : 2 * X ≤ X ^ 2 / r.s0l + r.s0l := by
      have : 0 ≤ (X - r.s0l) ^ 2 / r.s0l := by positivity
      have e : (X - r.s0l) ^ 2 / r.s0l = X ^ 2 / r.s0l + r.s0l - 2 * X := by field_simp; ring
      linarith
    have : (r.rBD : ℝ) * X ^ 2 / r.s0l + r.rBD * r.s0l ≥ 2 * r.rBD * X := by
      have := mul_le_mul_of_nonneg_left hamgm hr0
      have e : (r.rBD : ℝ) * (X ^ 2 / r.s0l + r.s0l) = r.rBD * X ^ 2 / r.s0l + r.rBD * r.s0l := by
        ring
      linarith
    linarith
  have hLpos : (0 : ℝ) < (d2 : ℝ) - c - r.rBD * r.s0l := by
    have := (by exact_mod_cast hL : (0 : ℝ) < ((Nat.sub (Nat.sub d2 c) (Nat.mul r.rBD r.s0l) : ℕ) :
        ℝ))
    rw [nat_sub_cast h2, nat_sub_cast h1] at this; push_cast [Nat.mul_eq] at this; linarith
  have hXr : 2 * r.rBD < X := by nlinarith
  have htri : X - r.rBD ≤ lam * ‖x - z‖ := by
    have : ‖y - z‖ ≤ ‖x - y‖ + ‖x - z‖ := by
      calc ‖y - z‖ = ‖(y - x) + (x - z)‖ := by congr 1; abel
        _ ≤ ‖y - x‖ + ‖x - z‖ := norm_add_le _ _
        _ = ‖x - y‖ + ‖x - z‖ := by rw [norm_sub_rev]
    have := mul_le_mul_of_nonneg_left this hlam.le
    simp only [X]; nlinarith
  have hsq : (X - r.rBD) ^ 2 ≤ (lam * ‖x - z‖) ^ 2 := by
    apply pow_le_pow_left₀ (by linarith) htri
  rw [mul_pow] at hsq
  nlinarith

/-- **Remainder term of one segment.** If the checks of `remTerm` pass, then `L > 0`,
`λ² ≤ 25 L`, and for every `d > 0` with `L ≤ λ² d²` the term dominates
`2⁴⁰ (kv/2⁶⁴)(C_a/d⁴ + C_b/d²)/8`. -/
theorem remTerm_sound (r : RC) (na nb dvv kv : ℕ) (hok : (remTerm r na nb dvv kv).2 = true)
    {D : ℝ} (hD : 0 < D) {Can Cbn Cd : ℝ} (hCd : 0 < Cd)
    (hK1 : (r.K1 : ℝ) = D ^ 2 * ((two40 : ℕ) : ℝ))
    (hK2 : (r.K2 : ℝ) = Can * D ^ 2 * ((two64 : ℕ) : ℝ)) (hK3 : (r.K3 : ℝ) = 8 * Cd)
    (hCbn : (r.Cbn : ℝ) = Cbn) (hCan : 0 ≤ Can) (hCbn0 : 0 ≤ Cbn)
    (hlam2 : (r.lam2 : ℝ) = (D * S32) ^ 2) :
    let L := cellL r (d2Low na nb dvv)
    0 < L ∧ (D * S32) ^ 2 ≤ 25 * L ∧
      ∀ d : ℝ, 0 < d → (L : ℝ) ≤ (D * S32) ^ 2 * d ^ 2 →
        (kv : ℝ) / ((two64 : ℕ) : ℝ) * ((two40 : ℕ) : ℝ) * (Can / Cd / d ^ 4 + Cbn / Cd / d ^ 2) /
            8 ≤
          ((remTerm r na nb dvv kv).1 : ℝ) := by
  intro L
  simp only [remTerm, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hok
  obtain ⟨hL, h25⟩ := hok
  refine ⟨hL, ?_, ?_⟩
  · rw [← hlam2]; exact_mod_cast (by simpa [Nat.mul_eq] using h25)
  · intro d hd hLd
    have hLr : (0 : ℝ) < L := by exact_mod_cast hL
    have h64 : (0 : ℝ) < ((two64 : ℕ) : ℝ) := by norm_num [two64]
    have h40 : (0 : ℝ) < ((two40 : ℕ) : ℝ) := by norm_num [two40]
    have hS : (two64 : ℕ) = (S32 : ℝ) ^ 2 := by norm_num [two64, S32]
    simp only [remTerm]
    have hden : 0 < Nat.mul r.K3 (sq L) := by
      have : (0 : ℝ) < r.K3 := by rw [hK3]; positivity
      exact Nat.mul_pos (by exact_mod_cast this) (by simp only [sq]; exact Nat.mul_pos hL hL)
    refine le_trans ?_ (cdiv_ge _ hden)
    push_cast [Nat.mul_eq, Nat.add_eq, sq_cast]
    rw [hK1, hK2, hK3, hCbn]
    have hd2 : 0 < d ^ 2 := by positivity
    -- `1/L ≥ 1/(λ²d²)`, `1/L² ≥ 1/(λ⁴d⁴)`
    have i1 : 1 / ((D * S32) ^ 2 * d ^ 2) ≤ 1 / (L : ℝ) := one_div_le_one_div_of_le hLr hLd
    have i2 : 1 / ((D * S32) ^ 2 * d ^ 2) ^ 2 ≤ 1 / (L : ℝ) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hLr.le hLd 2)
    have hkv : (0 : ℝ) ≤ kv := Nat.cast_nonneg _
    have e : (kv : ℝ) * (D ^ 2 * ((two40 : ℕ) : ℝ)) * (Can * D ^ 2 * ((two64 : ℕ) : ℝ) + Cbn * L) /
        (8 * Cd * (L : ℝ) ^ 2) =
        (kv : ℝ) * ((two40 : ℕ) : ℝ) / (8 * Cd) * (D ^ 4 * ((two64 : ℕ) : ℝ) * Can * (1 / (L : ℝ) ^
            2) +
          D ^ 2 * Cbn * (1 / (L : ℝ))) := by
      field_simp
    rw [e]
    have e2 : (kv : ℝ) / ((two64 : ℕ) : ℝ) * ((two40 : ℕ) : ℝ) * (Can / Cd / d ^ 4 + Cbn / Cd / d ^
        2) / 8 =
        (kv : ℝ) * ((two40 : ℕ) : ℝ) / (8 * Cd) * (D ^ 4 * ((two64 : ℕ) : ℝ) * Can *
          (1 / ((D * S32) ^ 2 * d ^ 2) ^ 2) + D ^ 2 * Cbn * (1 / ((D * S32) ^ 2 * d ^ 2))) := by
      rw [hS]
      have hS0 : S32 ≠ 0 := S32_pos.ne'
      field_simp
    rw [e2]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left i2 (by positivity)
    · exact mul_le_mul_of_nonneg_left i1 (by positivity)

/-! ## Derivatives of the face parametrisations -/

/-- Unit vectors. -/
@[expose] def eV (i : Fin 3) : Space := EuclideanSpace.single i 1

theorem polarPt_eq (ρ ζ φ : ℝ) :
    polarPt ρ ζ φ = (ρ * cos φ) • eV 0 + (ρ * sin φ) • eV 1 + ζ • eV 2 := by
  ext i; fin_cases i <;> simp [polarPt, eV]

/-- `∂_φ` of a polar point. -/
@[expose] def polarD (ρ φ : ℝ) : Space := (-(ρ * sin φ)) • eV 0 + (ρ * cos φ) • eV 1

/-- `∂²_φ` of a polar point. -/
@[expose] def polarDD (ρ φ : ℝ) : Space := (-(ρ * cos φ)) • eV 0 + (-(ρ * sin φ)) • eV 1

theorem hasDerivAt_polar_phi (ρ ζ φ : ℝ) :
    HasDerivAt (fun φ => polarPt ρ ζ φ) (polarD ρ φ) φ := by
  have h1 := ((hasDerivAt_cos φ).const_mul ρ).smul_const (eV 0)
  have h2 := ((hasDerivAt_sin φ).const_mul ρ).smul_const (eV 1)
  have := (h1.add h2).add_const (ζ • eV 2)
  simp only [polarPt_eq, polarD]
  convert this using 1
  simp [neg_smul, mul_neg]

theorem hasDerivAt_polarD (ρ φ : ℝ) : HasDerivAt (polarD ρ) (polarDD ρ φ) φ := by
  have h1 := (((hasDerivAt_sin φ).const_mul ρ).neg).smul_const (eV 0)
  have h2 := ((hasDerivAt_cos φ).const_mul ρ).smul_const (eV 1)
  have := h1.add h2
  unfold polarD polarDD
  convert this using 1
  simp [neg_smul, mul_neg]

theorem norm_polarD (ρ φ : ℝ) : ‖polarD ρ φ‖ = |ρ| := by
  have : ‖polarD ρ φ‖ ^ 2 = ρ ^ 2 := by
    rw [norm_sq_coords]; simp [polarD, eV]; nlinarith [sin_sq_add_cos_sq φ]
  rw [← sq_abs ρ] at this
  exact (pow_left_inj₀ (norm_nonneg _) (abs_nonneg _) two_ne_zero).mp this

theorem norm_polarDD (ρ φ : ℝ) : ‖polarDD ρ φ‖ = |ρ| := by
  have : ‖polarDD ρ φ‖ ^ 2 = ρ ^ 2 := by
    rw [norm_sq_coords]; simp [polarDD, eV]; nlinarith [sin_sq_add_cos_sq φ]
  rw [← sq_abs ρ] at this
  exact (pow_left_inj₀ (norm_nonneg _) (abs_nonneg _) two_ne_zero).mp this

/-- The `w`-direction of a face. -/
@[expose] def faceW (kind : ℕ) (φ : ℝ) : Space :=
  if kind < 2 then eV 2 else cos φ • eV 0 + sin φ • eV 1

theorem hasDerivAt_face_w (kind : ℕ) (φ w : ℝ) :
    HasDerivAt (fun w => faceSigma kind φ w) (faceW kind φ) w := by
  unfold faceSigma faceW
  by_cases hk : kind < 2
  · simp only [hk, ite_true, polarPt_eq]
    have := ((hasDerivAt_id' w).smul_const (eV 2)).const_add
      (((cylR kind : ℝ) / 181 * cos φ) • eV 0 + ((cylR kind : ℝ) / 181 * sin φ) • eV 1)
    convert this using 1
    simp
  · simp only [hk, ite_false, polarPt_eq]
    have := (((hasDerivAt_id' w).mul_const (cos φ)).smul_const (eV 0)).add
      (((hasDerivAt_id' w).mul_const (sin φ)).smul_const (eV 1)) |>.add_const (planeZ kind • eV 2)
    convert this using 1
    simp

theorem norm_faceW (kind : ℕ) (φ : ℝ) : ‖faceW kind φ‖ = 1 := by
  unfold faceW
  by_cases hk : kind < 2
  · simp only [hk, ite_true, eV]; simp
  · simp only [hk, ite_false]
    have : ‖cos φ • eV 0 + sin φ • eV 1‖ ^ 2 = 1 := by
      rw [norm_sq_coords]; simp [eV]
    nlinarith [norm_nonneg (cos φ • eV 0 + sin φ • eV 1)]

theorem faceSigma_polar (kind : ℕ) (φ w : ℝ) :
    faceSigma kind φ w = polarPt (if kind < 2 then (cylR kind : ℝ) / 181 else w)
      (if kind < 2 then w else planeZ kind) φ := by
  unfold faceSigma; split_ifs <;> rfl

/-! ## The `hel` part of the interpolation error on a face -/

/-- The `w`-range of the faces. -/
@[expose] def inFace (kind : ℕ) (w : ℝ) : Prop :=
  if kind < 2 then |w| ≤ aF else 161 / 181 ≤ w ∧ w ≤ 199 / 181

/-- `H_φ` of the faces. -/
@[expose] def helPhiC (kind : ℕ) : ℝ := if kind = 0 then 19 / 25 else if kind = 1 then 3 / 2 else
    147 / 100
/-- `H_w` of the faces. -/
@[expose] def helWC (kind : ℕ) : ℝ := if kind = 0 then 223 / 100 else if kind = 1 then 19 / 5 else
    17 / 2

theorem aF_pos : 0 < aF := by norm_num [aF]

theorem planeZ_abs (kind : ℕ) : |planeZ kind| = aF := by
  unfold planeZ; split_ifs <;> simp [abs_of_pos aF_pos]

/-- Interpolation of `⟨n, hel⟩` along `φ` on a face. -/
theorem hel_face_phi {n : Space} (hn : ‖n‖ ≤ 1) {kind : ℕ} (hk : kind < 4) {w : ℝ}
    (hw : inFace kind w) {a b x : ℝ} (hab : a ≤ b) (hx : x ∈ Icc a b) :
    |(b - a) * ⟪n, hel (faceSigma kind x w)⟫ - ((b - x) * ⟪n, hel (faceSigma kind a w)⟫ +
        (x - a) * ⟪n, hel (faceSigma kind b w)⟫)| ≤ helPhiC kind * (x - a) * (b - x) * (b - a) / 2
            := by
  simp only [faceSigma_polar]
  unfold inFace at hw
  have hpos : 0 ≤ (x - a) * (b - x) * (b - a) := by
    have := hx.1; have := hx.2; positivity
  by_cases hc : kind < 2
  · simp only [hc, ite_true] at hw ⊢
    have hρ : 0 < (cylR kind : ℝ) / 181 := by unfold cylR; split_ifs <;> norm_num
    have h := hel_phi_interp hn hρ w hab hx
    refine h.trans ?_
    have hC : |cA ((cylR kind : ℝ) / 181)| + |cB ((cylR kind : ℝ) / 181) w| +
        9 * |cG ((cylR kind : ℝ) / 181) w| + 9 * |cD ((cylR kind : ℝ) / 181) w| +
        4 * |cE ((cylR kind : ℝ) / 181) w| + 4 * |cF ((cylR kind : ℝ) / 181) w| ≤ helPhiC kind := by
      unfold cylR helPhiC
      by_cases h0 : kind = 0
      · simp only [h0, ite_true]; push_cast; exact hel_phi_face0 hw
      · simp only [h0, ite_false]
        have h1 : kind = 1 := by omega
        simp only [h1, ite_true]; push_cast; exact hel_phi_face1 hw
    have := mul_le_mul_of_nonneg_right hC hpos
    nlinarith
  · simp only [hc, ite_false] at hw ⊢
    have hρ : 0 < w := by linarith [hw.1]
    have h := hel_phi_interp hn hρ (planeZ kind) hab hx
    refine h.trans ?_
    have hC := hel_phi_plane hw.1 hw.2 (planeZ_abs kind).le
    have hC' : helPhiC kind = 147 / 100 := by
      have h0 : kind ≠ 0 := by omega
      have h1 : kind ≠ 1 := by omega
      simp [helPhiC, h0, h1]
    rw [hC']
    have := mul_le_mul_of_nonneg_right hC hpos
    nlinarith

/-- Interpolation of `⟨n, hel⟩` along `w` on a face. -/
theorem hel_face_w {n : Space} (hn : ‖n‖ ≤ 1) {kind : ℕ} (hk : kind < 4) (φ : ℝ) {a b x : ℝ}
    (hab : a ≤ b) (hx : x ∈ Icc a b) (ha : inFace kind a) (hb : inFace kind b) :
    |(b - a) * ⟪n, hel (faceSigma kind φ x)⟫ - ((b - x) * ⟪n, hel (faceSigma kind φ a)⟫ +
        (x - a) * ⟪n, hel (faceSigma kind φ b)⟫)| ≤ helWC kind * (x - a) * (b - x) * (b - a) / 2 :=
            by
  simp only [faceSigma_polar]
  unfold inFace at ha hb
  have hpos : 0 ≤ (x - a) * (b - x) * (b - a) := by
    have := hx.1; have := hx.2; positivity
  by_cases hc : kind < 2
  · simp only [hc, ite_true] at ha hb ⊢
    have hρ : 0 < (cylR kind : ℝ) / 181 := by unfold cylR; split_ifs <;> norm_num
    have hZ : ∀ y ∈ Icc a b, |y| ≤ aF := by
      intro y hy
      rw [abs_le] at ha hb ⊢
      constructor <;> linarith [hy.1, hy.2]
    have h := hel_zeta_interp hn hρ φ hab hx hZ
    refine h.trans ?_
    have hC : 1 / ((cylR kind : ℝ) / 181) ^ 3 + 3 * aF / ((cylR kind : ℝ) / 181) ^ 3 +
        3 / (2 * ((cylR kind : ℝ) / 181) ^ 2) ≤ helWC kind := by
      unfold cylR helWC
      by_cases h0 : kind = 0
      · simp only [h0, ite_true]; push_cast; exact hel_w_face0
      · simp only [h0, ite_false]
        have h1 : kind = 1 := by omega
        simp only [h1, ite_true]; push_cast; exact hel_w_face1
    have := mul_le_mul_of_nonneg_right hC hpos
    nlinarith
  · simp only [hc, ite_false] at ha hb ⊢
    have ha0 : 0 < a := by linarith [ha.1]
    have hC' : helWC kind = 17 / 2 := by
      have h0 : kind ≠ 0 := by omega
      have h1 : kind ≠ 1 := by omega
      simp [helWC, h0, h1]
    rw [hC']
    refine hel_rho_interp hn (planeZ kind) φ ha0 hab hx fun y hy => ?_
    exact hel_w_plane (by linarith [ha.1, hy.1]) (planeZ_abs kind)

/-! ## The coil part of the interpolation error -/

/-- The closed-form field of a list of segments. -/
@[expose] def BL (segs : List (ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ))) (y : Space) : Space :=
  (segs.map fun z => segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2) y).sum

theorem Bseg_eq_BL (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (y : Space) :
    Bseg fils y = BL (allSegs fils) y := rfl

/-- The coefficient `|κ| |q - p|` of a segment. -/
@[expose] def kvR (z : ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)) : ℝ :=
  |(z.1 : ℝ) / S32| * ‖ptR z.2.2 - ptR z.2.1‖

/-- Interpolation bound for the closed-form field of one segment along a curve. -/
theorem segClosed_interp (n : Space) (hn : ‖n‖ ≤ 1) (z : ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ))
    {σ σ1 σ2 : ℝ → Space} {a b x d S1 S2 : ℝ} (hab : a ≤ b) (hx : x ∈ Icc a b) (hd : 0 < d)
    (_hS1n : 0 ≤ S1) (hS2n : 0 ≤ S2)
    (hσ : ∀ τ ∈ Icc a b, HasDerivAt σ (σ1 τ) τ) (hσ1 : ∀ τ ∈ Icc a b, HasDerivAt σ1 (σ2 τ) τ)
    (hS1 : ∀ τ ∈ Icc a b, ‖σ1 τ‖ ≤ S1) (hS2 : ∀ τ ∈ Icc a b, ‖σ2 τ‖ ≤ S2)
    (hsep : ∀ τ ∈ Icc a b, ∀ t ∈ Icc (0 : ℝ) 1, d ≤ ‖σ τ - seg (ptR z.2.1) (ptR z.2.2) t‖) :
    |(b - a) * ⟪n, segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2) (σ x)⟫ -
        ((b - x) * ⟪n, segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2) (σ a)⟫ +
          (x - a) * ⟪n, segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2) (σ b)⟫)| ≤
      kvR z * (6 * S1 ^ 2 / d ^ 4 + 2 * S2 / d ^ 3) * (x - a) * (b - x) * (b - a) / 2 := by
  have hκ : (1 : ℝ) * (4 * π * ((z.1 : ℝ) / S32)) / (4 * π) = (z.1 : ℝ) / S32 := by
    field_simp
  have e : ∀ y, segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2) y =
      filamentField 1 (4 * π * ((z.1 : ℝ) / S32)) (seg (ptR z.2.1) (ptR z.2.2)) 0 1 y := by
    intro y; rw [segField_eq_closed, hκ]
  simp only [e]
  have h := segField_interp_bound 1 (4 * π * ((z.1 : ℝ) / S32)) (ptR z.2.1) (ptR z.2.2) n hab hx hd
    hσ hσ1 hS1 hS2 hsep
  rw [hκ] at h
  refine h.trans ?_
  have hpos : 0 ≤ (x - a) * (b - x) * (b - a) := by
    have := hx.1; have := hx.2; positivity
  have hM : 0 ≤ 6 * S1 ^ 2 / d ^ 4 + 2 * S2 / d ^ 3 := by positivity
  unfold kvR
  have : |(z.1 : ℝ) / S32| * (‖n‖ * ‖ptR z.2.2 - ptR z.2.1‖ * (6 * S1 ^ 2 / d ^ 4 + 2 * S2 / d ^
      3)) ≤
      |(z.1 : ℝ) / S32| * ‖ptR z.2.2 - ptR z.2.1‖ * (6 * S1 ^ 2 / d ^ 4 + 2 * S2 / d ^ 3) := by
    have : ‖n‖ * ‖ptR z.2.2 - ptR z.2.1‖ ≤ ‖ptR z.2.2 - ptR z.2.1‖ := by
      have := norm_nonneg (ptR z.2.2 - ptR z.2.1); nlinarith
    have := mul_le_mul_of_nonneg_right this hM
    have := mul_le_mul_of_nonneg_left this (abs_nonneg ((z.1 : ℝ) / S32))
    linarith
  have := mul_le_mul_of_nonneg_right this hpos
  nlinarith

/-- Interpolation of a sum. -/
theorem interp_sum {ι : Type} (L : List ι) (g : ι → ℝ → ℝ) (c : ι → ℝ) {a b x P : ℝ}
    (h : ∀ i ∈ L, |(b - a) * g i x - ((b - x) * g i a + (x - a) * g i b)| ≤ c i * P) :
    |(b - a) * (L.map fun i => g i x).sum - ((b - x) * (L.map fun i => g i a).sum +
        (x - a) * (L.map fun i => g i b).sum)| ≤ (L.map c).sum * P := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h i (by simp)
    have h2 := ih (fun j hj => h j (by simp [hj]))
    calc |(b - a) * (g i x + (L.map fun i => g i x).sum) - ((b - x) * (g i a +
          (L.map fun i => g i a).sum) + (x - a) * (g i b + (L.map fun i => g i b).sum))|
        = |((b - a) * g i x - ((b - x) * g i a + (x - a) * g i b)) + ((b - a) *
            (L.map fun i => g i x).sum - ((b - x) * (L.map fun i => g i a).sum +
            (x - a) * (L.map fun i => g i b).sum))| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ c i * P + (L.map c).sum * P := add_le_add h1 h2
      _ = (c i + (L.map c).sum) * P := by ring

theorem inner_list_sum {ι : Type} (L : List ι) (n : Space) (v : ι → Space) :
    ⟪n, (L.map v).sum⟫ = (L.map fun i => ⟪n, v i⟫).sum := by
  induction L with
  | nil => simp
  | cons i L ih => simp [inner_add_right, ih]

/-! ## The analytic cell bound -/

theorem inFace_mid {kind : ℕ} {w0 w1 w : ℝ} (h0 : inFace kind w0) (h1 : inFace kind w1)
    (hw : w ∈ Icc w0 w1) : inFace kind w := by
  unfold inFace at *
  split_ifs at * with hc
  · rw [abs_le] at *; constructor <;> linarith [hw.1, hw.2]
  · constructor <;> linarith [hw.1, hw.2, h0.1, h1.2]

/-- **Bilinear bound on one cell of a face** for the closed-form field of a list of segments. -/
theorem cell_analytic {kind : ℕ} (hk : kind < 4) (segs : List (ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)))
    (dd : ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) → ℝ) {φ0 φ1 w0 w1 ρm e : ℝ}
    (hφ : φ0 < φ1) (hw : w0 < w1) (hw0 : inFace kind w0) (hw1 : inFace kind w1) (hρm0 : 0 ≤ ρm)
    (hρm : ∀ w ∈ Icc w0 w1, |(if kind < 2 then (cylR kind : ℝ) / 181 else w)| ≤ ρm)
    (hdd : ∀ z ∈ segs, 0 < dd z)
    (hsep : ∀ z ∈ segs, ∀ φ ∈ Icc φ0 φ1, ∀ w ∈ Icc w0 w1, ∀ t ∈ Icc (0 : ℝ) 1,
      dd z ≤ ‖faceSigma kind φ w - seg (ptR z.2.1) (ptR z.2.2) t‖)
    (hc00 : ‖BL segs (faceSigma kind φ0 w0) - hel (faceSigma kind φ0 w0)‖ ≤ e)
    (hc10 : ‖BL segs (faceSigma kind φ1 w0) - hel (faceSigma kind φ1 w0)‖ ≤ e)
    (hc01 : ‖BL segs (faceSigma kind φ0 w1) - hel (faceSigma kind φ0 w1)‖ ≤ e)
    (hc11 : ‖BL segs (faceSigma kind φ1 w1) - hel (faceSigma kind φ1 w1)‖ ≤ e)
    {φ w : ℝ} (hφm : φ ∈ Icc φ0 φ1) (hwm : w ∈ Icc w0 w1) :
    ‖BL segs (faceSigma kind φ w) - hel (faceSigma kind φ w)‖ ≤
      e + ((segs.map fun z => kvR z * (6 * ρm ^ 2 / dd z ^ 4 + 2 * ρm / dd z ^ 3)).sum +
        helPhiC kind) * (φ1 - φ0) ^ 2 / 8 +
      ((segs.map fun z => kvR z * (6 / dd z ^ 4)).sum + helWC kind) * (w1 - w0) ^ 2 / 8 := by
  set Ev := BL segs (faceSigma kind φ w) - hel (faceSigma kind φ w)
  have he0 : 0 ≤ e := (norm_nonneg _).trans hc00
  set Mφ := (segs.map fun z => kvR z * (6 * ρm ^ 2 / dd z ^ 4 + 2 * ρm / dd z ^ 3)).sum + helPhiC
      kind
  set Mw := (segs.map fun z => kvR z * (6 / dd z ^ 4)).sum + helWC kind
  have hkv : ∀ z, 0 ≤ kvR z := fun z => by unfold kvR; positivity
  have hMφ : 0 ≤ Mφ := by
    have : 0 ≤ helPhiC kind := by unfold helPhiC; split_ifs <;> norm_num
    have : 0 ≤ (segs.map fun z => kvR z * (6 * ρm ^ 2 / dd z ^ 4 + 2 * ρm / dd z ^ 3)).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
        have := hdd z hz; have := hkv z; positivity
    linarith
  have hMw : 0 ≤ Mw := by
    have : 0 ≤ helWC kind := by unfold helWC; split_ifs <;> norm_num
    have : 0 ≤ (segs.map fun z => kvR z * (6 / dd z ^ 4)).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
        have := hdd z hz; have := hkv z; positivity
    linarith
  have hfin : 0 ≤ e + Mφ * (φ1 - φ0) ^ 2 / 8 + Mw * (w1 - w0) ^ 2 / 8 := by positivity
  by_cases hE : Ev = 0
  · rw [hE, norm_zero]; exact hfin
  set n : Space := ‖Ev‖⁻¹ • Ev
  have hn : ‖n‖ ≤ 1 := by
    simp only [n, norm_smul, norm_inv, norm_norm]
    rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hE)]
  set Φ : ℝ → ℝ → ℝ := fun φ' w' =>
    ⟪n, BL segs (faceSigma kind φ' w') - hel (faceSigma kind φ' w')⟫
  have hΦ : Φ φ w = ‖Ev‖ := by
    simp only [Φ, n, inner_smul_left, conj_trivial]
    rw [show BL segs (faceSigma kind φ w) - hel (faceSigma kind φ w) = Ev from rfl,
      real_inner_self_eq_norm_sq]
    field_simp [norm_ne_zero_iff.mpr hE]
  have hcorner : ∀ φ' w', ‖BL segs (faceSigma kind φ' w') - hel (faceSigma kind φ' w')‖ ≤ e →
      |Φ φ' w'| ≤ e := by
    intro φ' w' h
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖n‖ * ‖BL segs (faceSigma kind φ' w') - hel (faceSigma kind φ' w')‖ ≤ 1 * e :=
          mul_le_mul hn h (norm_nonneg _) zero_le_one
      _ = e := one_mul e
  -- the decomposition of `Φ`
  have hΦsum : ∀ φ' w', Φ φ' w' =
      (segs.map fun z => ⟪n, segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2)
        (faceSigma kind φ' w')⟫).sum - ⟪n, hel (faceSigma kind φ' w')⟫ := by
    intro φ' w'
    simp only [Φ, inner_sub_right, BL, inner_list_sum]
  have hρ : ∀ w' ∈ Icc w0 w1, |(if kind < 2 then (cylR kind : ℝ) / 181 else w')| ≤ ρm := hρm
  -- along `φ`
  have hφi : ∀ w' ∈ Icc w0 w1, ∀ φ' ∈ Icc φ0 φ1,
      |(φ1 - φ0) * Φ φ' w' - ((φ1 - φ') * Φ φ0 w' + (φ' - φ0) * Φ φ1 w')| ≤
        Mφ * (φ' - φ0) * (φ1 - φ') * (φ1 - φ0) / 2 := by
    intro w' hw' φ' hφ'
    simp only [hΦsum]
    set P := (φ' - φ0) * (φ1 - φ') * (φ1 - φ0) / 2
    have hP : 0 ≤ P := by have := hφ'.1; have := hφ'.2; positivity
    have hseg := interp_sum segs (fun z τ => ⟪n, segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2)
        (faceSigma kind τ w')⟫) (fun z => kvR z * (6 * ρm ^ 2 / dd z ^ 4 + 2 * ρm / dd z ^ 3))
      (P := P) (a := φ0) (b := φ1) (x := φ') fun z hz => by
        have h := segClosed_interp n hn z (σ := fun τ => faceSigma kind τ w')
          (σ1 := fun τ => polarD (if kind < 2 then (cylR kind : ℝ) / 181 else w') τ)
          (σ2 := fun τ => polarDD (if kind < 2 then (cylR kind : ℝ) / 181 else w') τ)
          hφ.le hφ' (hdd z hz) hρm0 hρm0
          (fun τ _ => by simp only [faceSigma_polar]; exact hasDerivAt_polar_phi _ _ τ)
          (fun τ _ => hasDerivAt_polarD _ τ)
          (fun τ _ => by rw [norm_polarD]; exact hρ w' hw')
          (fun τ _ => by rw [norm_polarDD]; exact hρ w' hw')
          (fun τ hτ t ht => hsep z hz τ hτ w' hw' t ht)
        simp only [P]
        linarith [h]
    have hhel := hel_face_phi hn hk (inFace_mid hw0 hw1 hw') hφ.le hφ'
    have e1 : (φ1 - φ0) * ((segs.map fun z => ⟪n, segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR
        z.2.2)
          (faceSigma kind φ' w')⟫).sum - ⟪n, hel (faceSigma kind φ' w')⟫) -
        ((φ1 - φ') * ((segs.map fun z => ⟪n, segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2)
          (faceSigma kind φ0 w')⟫).sum - ⟪n, hel (faceSigma kind φ0 w')⟫) +
        (φ' - φ0) * ((segs.map fun z => ⟪n, segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2)
          (faceSigma kind φ1 w')⟫).sum - ⟪n, hel (faceSigma kind φ1 w')⟫)) =
        ((φ1 - φ0) * (segs.map fun z => ⟪n, segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2)
          (faceSigma kind φ' w')⟫).sum - ((φ1 - φ') * (segs.map fun z => ⟪n, segClosed
          ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2) (faceSigma kind φ0 w')⟫).sum + (φ' - φ0) *
          (segs.map fun z => ⟪n, segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2)
          (faceSigma kind φ1 w')⟫).sum)) -
        ((φ1 - φ0) * ⟪n, hel (faceSigma kind φ' w')⟫ - ((φ1 - φ') * ⟪n, hel (faceSigma kind φ0 w')⟫
            +
          (φ' - φ0) * ⟪n, hel (faceSigma kind φ1 w')⟫)) := by ring
    rw [e1]
    refine (abs_sub _ _).trans ?_
    have : helPhiC kind * (φ' - φ0) * (φ1 - φ') * (φ1 - φ0) / 2 = helPhiC kind * P := by
      simp only [P]; ring
    rw [this] at hhel
    calc _ ≤ (segs.map fun z => kvR z * (6 * ρm ^ 2 / dd z ^ 4 + 2 * ρm / dd z ^ 3)).sum * P +
          helPhiC kind * P := add_le_add hseg hhel
      _ = Mφ * (φ' - φ0) * (φ1 - φ') * (φ1 - φ0) / 2 := by simp only [Mφ, P]; ring
  -- along `w`
  have hwi : ∀ φ', (φ' = φ0 ∨ φ' = φ1) → ∀ w' ∈ Icc w0 w1,
      |(w1 - w0) * Φ φ' w' - ((w1 - w') * Φ φ' w0 + (w' - w0) * Φ φ' w1)| ≤
        Mw * (w' - w0) * (w1 - w') * (w1 - w0) / 2 := by
    intro φ' hφor w' hw'
    have hφmem : φ' ∈ Icc φ0 φ1 := by
      rcases hφor with rfl | rfl
      · exact ⟨le_rfl, hφ.le⟩
      · exact ⟨hφ.le, le_rfl⟩
    simp only [hΦsum]
    set P := (w' - w0) * (w1 - w') * (w1 - w0) / 2
    have hP : 0 ≤ P := by have := hw'.1; have := hw'.2; positivity
    have hseg := interp_sum segs (fun z τ => ⟪n, segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2)
        (faceSigma kind φ' τ)⟫) (fun z => kvR z * (6 / dd z ^ 4))
      (P := P) (a := w0) (b := w1) (x := w') fun z hz => by
        have h := segClosed_interp n hn z (σ := fun τ => faceSigma kind φ' τ)
          (σ1 := fun _ => faceW kind φ') (σ2 := fun _ => 0) hw.le hw' (hdd z hz) zero_le_one le_rfl
          (fun τ _ => hasDerivAt_face_w kind φ' τ) (fun τ _ => hasDerivAt_const τ _)
          (fun τ _ => by rw [norm_faceW]) (fun τ _ => by simp)
          (fun τ hτ t ht => hsep z hz φ' hφmem τ hτ t ht)
        simp only [P]
        have e2 : kvR z * (6 * 1 ^ 2 / dd z ^ 4 + 2 * 0 / dd z ^ 3) = kvR z * (6 / dd z ^ 4) := by
            ring
        rw [e2] at h
        linarith [h]
    have hhel := hel_face_w hn hk φ' hw.le hw' hw0 hw1
    have e1 : (w1 - w0) * ((segs.map fun z => ⟪n, segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR
        z.2.2)
          (faceSigma kind φ' w')⟫).sum - ⟪n, hel (faceSigma kind φ' w')⟫) -
        ((w1 - w') * ((segs.map fun z => ⟪n, segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2)
          (faceSigma kind φ' w0)⟫).sum - ⟪n, hel (faceSigma kind φ' w0)⟫) +
        (w' - w0) * ((segs.map fun z => ⟪n, segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2)
          (faceSigma kind φ' w1)⟫).sum - ⟪n, hel (faceSigma kind φ' w1)⟫)) =
        ((w1 - w0) * (segs.map fun z => ⟪n, segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2)
          (faceSigma kind φ' w')⟫).sum - ((w1 - w') * (segs.map fun z => ⟪n, segClosed
          ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2) (faceSigma kind φ' w0)⟫).sum + (w' - w0) *
          (segs.map fun z => ⟪n, segClosed ((z.1 : ℝ) / S32) (ptR z.2.1) (ptR z.2.2)
          (faceSigma kind φ' w1)⟫).sum)) -
        ((w1 - w0) * ⟪n, hel (faceSigma kind φ' w')⟫ - ((w1 - w') * ⟪n, hel (faceSigma kind φ' w0)⟫
            +
          (w' - w0) * ⟪n, hel (faceSigma kind φ' w1)⟫)) := by ring
    rw [e1]
    refine (abs_sub _ _).trans ?_
    have : helWC kind * (w' - w0) * (w1 - w') * (w1 - w0) / 2 = helWC kind * P := by
      simp only [P]; ring
    rw [this] at hhel
    calc _ ≤ (segs.map fun z => kvR z * (6 / dd z ^ 4)).sum * P + helWC kind * P :=
          add_le_add hseg hhel
      _ = Mw * (w' - w0) * (w1 - w') * (w1 - w0) / 2 := by simp only [Mw, P]; ring
  have hbil := bilinear_cell_bound hφ hw hMφ hMw (hcorner _ _ hc00) (hcorner _ _ hc10)
    (hcorner _ _ hc01) (hcorner _ _ hc11) hφi hwi hφm hwm
  rw [hΦ, abs_of_nonneg (norm_nonneg _)] at hbil
  linarith

/-! ## The remainder data of a corner -/

/-- **The remainder output of a corner.** If a corner with an attached cell passes, its
remainder is the sum of the `remTerm` values of all segment records, each of which passed. -/
theorem cornerEval_rem (o : Offs) (fils : List (ℤ × List (ℤ × ℤ × ℤ)))
    (hne : ∀ f ∈ fils, f.2 ≠ []) (hfok : ∀ f ∈ fils, filOK o f.1 f.2 = true)
    (Xt Yt Zt D : ℕ) (hD : 0 < D) (h : QQ × QQ × QQ) (r : RC) (hr : r.doRem = true)
    (gs : List (List ℕ))
    (hok : (cornerEval o (fils.map fun f => mkFil o f.1 f.2) Xt Yt Zt D h r gs).ok = true) :
    ∃ R : List SRec, R.map (fun z => (z.1, z.2.1, z.2.2.1)) = allSegs fils ∧
      (∀ z ∈ R, VRok Xt Yt Zt D z.2.1 z.2.2.2.1 ∧ VRok Xt Yt Zt D z.2.2.1 z.2.2.2.2 ∧
        segOK o z.1 z.2.1 z.2.2.1 = true ∧
        (remTerm r z.2.2.2.1.n z.2.2.2.2.n (Nat.mul (Nat.mul D D) (mkSeg o z.1 z.2.1 z.2.2.1).vv)
          (mkSeg o z.1 z.2.1 z.2.2.1).kv).2 = true) ∧
      (cornerEval o (fils.map fun f => mkFil o f.1 f.2) Xt Yt Zt D h r gs).rem =
        (R.map fun z => (remTerm r z.2.2.2.1.n z.2.2.2.2.n
          (Nat.mul (Nat.mul D D) (mkSeg o z.1 z.2.1 z.2.2.1).vv) (mkSeg o z.1 z.2.1
              z.2.2.1).kv).1).sum
      ∧ (cornerEval o (fils.map fun f => mkFil o f.1 f.2) Xt Yt Zt D h r gs).ok = true := by
  set fs := fils.map fun f => mkFil o f.1 f.2
  set c := mkCD Xt Yt Zt D
  set vss := allVerts c fs gs
  set D3S := Nat.mul (Nat.mul (Nat.mul D D) D) two136
  set R := allRecs fils vss
  have hwalk := allWalk_eq o (Nat.mul D D) D3S r c fils gs ⟨0, 0, 0, 0, 0, 0, 0, 0, true⟩ hne
  set acc := walkL (Nat.mul D D) D3S r (R.map (srTriple o)) ⟨0, 0, 0, 0, 0, 0, 0, 0, true⟩
  have hce : (cornerEval o fs Xt Yt Zt D h r gs).ok = (((acc.ok &&
        (cornerFinal o Xt Yt Zt D (Nat.mul D two32) acc h).1) &&
          Nat.ble (Nat.mul 1000 KT) (Nat.mul D two32)) && (!r.doRem || Nat.ble r.rBD r.s0l)) ∧
      (cornerEval o fs Xt Yt Zt D h r gs).rem = acc.rem := by
    have hwalk' : allWalk (Nat.mul D D) (Nat.mul (Nat.mul (Nat.mul D D) D) two136) r
        ⟨0, 0, 0, 0, 0, 0, 0, 0, true⟩ fs
        (allVerts ⟨D, Nat.mul D D, Nat.mul Xt two32, Nat.mul Yt two32, Nat.mul Zt two32,
          Nat.add (Nat.add (sq (Nat.mul Xt two32)) (sq (Nat.mul Yt two32))) (sq (Nat.mul Zt two32)),
          Nat.mul D two32⟩ fs gs) = acc := hwalk
    simp only [cornerEval]
    rw [hwalk']
    exact ⟨rfl, rfl⟩
  obtain ⟨hceok, hcerem⟩ := hce
  have hok' := hok
  rw [hceok] at hok'
  simp only [Bool.and_eq_true] at hok'
  obtain ⟨⟨⟨hacc, -⟩, -⟩, -⟩ := hok'
  obtain ⟨-, -, -, -, -, -, -, hrem, hall⟩ :=
    fold_segStep (Nat.mul D D) D3S r (R.map (srTriple o)) ⟨0, 0, 0, 0, 0, 0, 0, 0, true⟩
  have hchk := (hall hacc).2
  have hrec := allRecs_sound o Xt Yt Zt D hD fils gs hfok
  refine ⟨R, allRecs_segs o c fils gs, fun z hz => ?_, ?_, hok⟩
  · obtain ⟨ha, hb, hs⟩ := hrec z hz
    have hx := hchk (srTriple o z) (List.mem_map_of_mem hz)
    simp only [srTriple, segChk, segRT, hr, Bool.cond_true, Bool.and_eq_true] at hx
    exact ⟨ha, hb, hs, hx.2⟩
  · rw [hcerem, hrem, zero_add, List.map_map]
    congr 1
    refine List.map_congr_left fun z _ => ?_
    simp only [Function.comp, srTriple, segRT, hr, Bool.cond_true]

/-! ## Corners of a face -/

/-- Validity of the face data used below. -/
@[expose] def FaceValid (F : Face) : Prop := F.kind < 4 ∧ 0 < F.wd

/-- The checker's `hel` at a grid corner is `hel` there. -/
theorem helAt_corner (F : Face) (hF : FaceValid F) (m : ℕ) (wn : ℤ)
    (hw : inFace F.kind ((wn : ℝ) / F.wd)) :
    let h := helAt (helCoef (faceRZ F wn).1 (faceRZ F wn).2) (trigOf m)
    (0 < h.1.den ∧ 0 < h.2.1.den ∧ 0 < h.2.2.den) ∧
    hel (faceSigma F.kind (phiM m) ((wn : ℝ) / F.wd)) =
      WithLp.toLp 2 ![h.1.val, h.2.1.val, h.2.2.val] := by
  intro h
  obtain ⟨hk, hwd⟩ := hF
  have hwd' : (0 : ℝ) < F.wd := by exact_mod_cast hwd
  set q : ℤ := (qT : ℤ)
  have hcd : 0 < ((q * q + (m : ℤ) * m).toNat) := by
    have : 0 < q * q + (m : ℤ) * m := by simp only [q, qT]; positivity
    omega
  have hcdR : (((q * q + (m : ℤ) * m).toNat : ℕ) : ℝ) = 4096 ^ 2 + (m : ℝ) ^ 2 := by
    rw [toNat_cast_real (by simp only [q, qT]; positivity)]; simp [q, qT]; ring
  have hc : ((q * q - (m : ℤ) * m : ℤ) : ℝ) / (((q * q + (m : ℤ) * m).toNat : ℕ) : ℝ) = cos (phiM
      m) := by
    rw [hcdR, cos_phiM]; simp [q, qT]; ring
  have hs : ((2 * (m : ℤ) * q : ℤ) : ℝ) / (((q * q + (m : ℤ) * m).toNat : ℕ) : ℝ) = sin (phiM m) :=
      by
    rw [hcdR, sin_phiM]; simp [q, qT]; ring
  have htrig : trigOf m = mkTrig ⟨q * q - (m : ℤ) * m, (q * q + (m : ℤ) * m).toNat⟩
      ⟨2 * (m : ℤ) * q, (q * q + (m : ℤ) * m).toNat⟩ := rfl
  -- radius and height
  obtain ⟨ρn, ρd, ζn, ζd, hρn, hρd, hζd, hrz, hρv, hζv⟩ : ∃ ρn ρd ζn ζd, 0 < ρn ∧ 0 < ρd ∧ 0 < ζd ∧
      faceRZ F wn = (⟨ρn, ρd⟩, ⟨ζn, ζd⟩) ∧
      (ρn : ℝ) / ρd = (if F.kind < 2 then (cylR F.kind : ℝ) / 181 else (wn : ℝ) / F.wd) ∧
      (ζn : ℝ) / ζd = (if F.kind < 2 then (wn : ℝ) / F.wd else planeZ F.kind) := by
    by_cases hc2 : F.kind < 2
    · refine ⟨cylR F.kind, 181, wn, F.wd, by unfold cylR; split_ifs <;> norm_num, by norm_num, hwd,
        by simp [faceRZ, hc2], by simp [hc2], by simp [hc2]⟩
    · have hwpos : 0 < wn := by
        unfold inFace at hw; simp only [hc2, ite_false] at hw
        have : (0 : ℝ) < (wn : ℝ) / F.wd := by linarith [hw.1]
        have : (0 : ℝ) < wn := by
          rwa [lt_div_iff₀ hwd', zero_mul] at this
        exact_mod_cast this
      by_cases h2 : F.kind = 2
      · refine ⟨wn, F.wd, 3420, 32761, hwpos, hwd, by norm_num, by simp [faceRZ, h2],
          by simp [hc2], ?_⟩
        simp [planeZ, h2, aF]
      · refine ⟨wn, F.wd, -3420, 32761, hwpos, hwd, by norm_num, by simp [faceRZ, hc2, h2],
          by simp [hc2], ?_⟩
        simp [hc2, planeZ, h2, aF]; ring
  have hρpos : (0 : ℝ) < (ρn : ℝ) / ρd := by
    have : (0 : ℝ) < ρn := by exact_mod_cast hρn
    have : (0 : ℝ) < ρd := by exact_mod_cast hρd
    positivity
  simp only [h, hrz, htrig]
  obtain ⟨hden, h1, h2, h3⟩ := helAt_val ρn ζn (q * q - (m : ℤ) * m) (2 * (m : ℤ) * q) ρd ζd
    ((q * q + (m : ℤ) * m).toNat) ((q * q + (m : ℤ) * m).toNat) hρn hρd hζd hcd hcd
  refine ⟨hden, ?_⟩
  rw [faceSigma_polar, ← hρv, ← hζv, hel_polar hρpos]
  rw [h1, h2, h3, hc, hs]
  have hcs : cos (phiM m) ^ 2 + sin (phiM m) ^ 2 = 1 := by rw [add_comm]; exact sin_sq_add_cos_sq _
  ext i; fin_cases i
  · simp [helP, cos_three_mul, sin_three_mul]
  · simp [helP, cos_three_mul, sin_three_mul]
  · simp only [helP, sin_two_mul, cos_two_mul, Fin.reduceFinMk, Fin.isValue,
      Nat.succ_eq_add_one, Nat.reduceAdd, neg_mul, Matrix.cons_val]
    have : 2 * cos (phiM m) ^ 2 - 1 = cos (phiM m) ^ 2 - sin (phiM m) ^ 2 := by linarith
    rw [this]; ring

/-! ## Geometry of a cell -/

theorem phiM_lt {m m' : ℕ} (h : m < m') : phiM m < phiM m' := by
  unfold phiM
  have : arctan ((m : ℝ) / 4096) < arctan ((m' : ℝ) / 4096) :=
    arctan_strictMono (by have : (m : ℝ) < m' := by exact_mod_cast h
                          linarith)
  linarith

/-- `φ_{m'} - φ_m ≤ 2(m' - m)·4096/(4096² + m²)`. -/
theorem phiM_sub_le {m m' : ℕ} (h : m ≤ m') :
    phiM m' - phiM m ≤ 2 * ((m' : ℝ) - m) * 4096 / (4096 ^ 2 + (m : ℝ) ^ 2) := by
  set t := (m : ℝ) / 4096
  set t' := (m' : ℝ) / 4096
  have htt : t ≤ t' := by simp only [t, t']; gcongr
  have ht0 : 0 ≤ t := by positivity
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := arctan)
    (f' := fun x => 1 / (1 + x ^ 2)) (C := 1 / (1 + t ^ 2)) (a := t) (b := t')
    (fun x _ => by
      have := (hasDerivAt_arctan x).hasDerivWithinAt (s := Icc t t')
      simpa using this)
    (fun x hx => by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      apply one_div_le_one_div_of_le (by positivity)
      have : t ≤ x := hx.1
      nlinarith) t' ⟨htt, le_rfl⟩
  rw [Real.norm_eq_abs] at hmvt
  have hd : arctan t' - arctan t ≤ 1 / (1 + t ^ 2) * (t' - t) := (le_abs_self _).trans hmvt
  unfold phiM
  have e : 2 * ((m' : ℝ) - m) * 4096 / (4096 ^ 2 + (m : ℝ) ^ 2) = 2 * (1 / (1 + t ^ 2) * (t' - t))
      := by
    simp only [t, t']; field_simp
  rw [e]; linarith

/-- Chord bound along `φ`. -/
theorem faceSigma_phi_dist (kind : ℕ) {w φ0 φ : ℝ} (hφ : φ0 ≤ φ) :
    ‖faceSigma kind φ w - faceSigma kind φ0 w‖ ≤
      |(if kind < 2 then (cylR kind : ℝ) / 181 else w)| * (φ - φ0) := by
  simp only [faceSigma_polar]
  exact norm_image_sub_le_of_norm_deriv_le_segment' (f := fun τ => polarPt _ _ τ)
    (f' := fun τ => polarD _ τ) (fun x _ => (hasDerivAt_polar_phi _ _ x).hasDerivWithinAt)
    (fun x _ => by rw [norm_polarD]) φ ⟨hφ, le_rfl⟩

/-- Distance along `w`. -/
theorem faceSigma_w_dist (kind : ℕ) {φ w0 w : ℝ} (hw : w0 ≤ w) :
    ‖faceSigma kind φ w - faceSigma kind φ w0‖ ≤ w - w0 := by
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun τ => faceSigma kind φ τ)
    (f' := fun _ => faceW kind φ) (C := 1) (a := w0) (b := w)
    (fun x _ => (hasDerivAt_face_w kind φ x).hasDerivWithinAt)
    (fun x _ => by rw [norm_faceW]) w ⟨hw, le_rfl⟩
  simpa using this

end PlasmaLean.Design.PolygonCoil
