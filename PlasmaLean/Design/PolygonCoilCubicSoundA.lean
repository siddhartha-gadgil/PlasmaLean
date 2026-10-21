/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCubicGeom

/-!
# Soundness of the cubic checker, part A: corners

* `cornerFinalV_spec`: the final assembly of `cornerFinalV` gives `2⁴⁰‖B - hel‖ ≤ e` and the
  componentwise bounds `|2⁴⁰(B - hel)ₖ - Êₖ| ≤ ρ` (adapted from `cornerFinal_spec`, with the
  segment count bound `nS`);
* `cornerEval4_sound`: if `cornerEval4` accepts, these hold at the corner for `Bseg fils`, and the
  remainder sums are the sums of the `remStep` terms over the segment records, each of which
  passed its checks.
-/

public section
noncomputable section

namespace PlasmaLean.Design.PolygonCoil
open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator
    PlasmaLean.Design.RationalStellarator.Coils Set
open scoped RealInnerProductSpace

/-- The maximum of three naturals dominates each. -/
theorem rmax_ge (a b c : ℕ) : a ≤ nmax (nmax a b) c ∧ b ≤ nmax (nmax a b) c ∧ c ≤ nmax (nmax a b)
    c :=
  ⟨(nmax_ge_left a b).trans (nmax_ge_left _ _), (nmax_ge_right a b).trans (nmax_ge_left _ _),
    nmax_ge_right _ _⟩

/-- One component of the rounded error vector. -/
theorem box_comp {SE hd : ℕ} {B : ℝ} {T : ℤ} {Rn Rm : ℕ} {hn : ℤ} (hSE : 0 < SE) (hhd : 0 < hd)
    (hBT : |(SE : ℝ) * B - T| ≤ ((Rn : ℤ) : ℝ)) (hR : Rn ≤ Rm) :
    |(B - (hn : ℝ) / hd) * ((two40 : ℕ) : ℝ) -
        ((Int.fdiv ((T * (hd : ℤ) - hn * (SE : ℤ)) * (two40 : ℤ)) ((SE * hd : ℕ) : ℤ) : ℤ) : ℝ)| ≤
      ((Nat.add (cdiv (Nat.mul Rm two40) SE) 1 : ℕ) : ℝ) := by
  have hSE' : (0 : ℝ) < SE := by exact_mod_cast hSE
  have hd' : (0 : ℝ) < hd := by exact_mod_cast hhd
  have hpos : 0 < SE * hd := Nat.mul_pos hSE hhd
  have f1 := fdiv_le_real ((T * (hd : ℤ) - hn * (SE : ℤ)) * (two40 : ℤ)) hpos
  have f2 := real_lt_fdiv_succ ((T * (hd : ℤ) - hn * (SE : ℤ)) * (two40 : ℤ)) hpos
  have h40 : ((two40 : ℕ) : ℝ) = 1099511627776 := by norm_num [two40]
  have e : (((T * (hd : ℤ) - hn * (SE : ℤ)) * (two40 : ℤ) : ℤ) : ℝ) / ((SE * hd : ℕ) : ℝ) =
      ((T : ℝ) / SE - (hn : ℝ) / hd) * ((two40 : ℕ) : ℝ) := by
    push_cast; field_simp
  rw [e] at f1 f2
  have hc := cdiv_ge (Nat.mul Rm two40) hSE
  push_cast [Nat.mul_eq] at hc
  simp only [Nat.add_eq, Nat.mul_eq, Nat.cast_add, Nat.cast_one]
  have hRm : ((Rn : ℤ) : ℝ) ≤ (Rm : ℝ) := by push_cast; exact_mod_cast hR
  have hB : |B - (T : ℝ) / SE| ≤ (Rm : ℝ) / SE := by
    rw [show B - (T : ℝ) / SE = ((SE : ℝ) * B - T) / SE by field_simp, abs_div,
      abs_of_pos hSE']
    exact div_le_div_of_nonneg_right (hBT.trans hRm) hSE'.le
  have h40p : (0 : ℝ) < ((two40 : ℕ) : ℝ) := by norm_num [two40]
  have hB40 : |(B - (T : ℝ) / SE) * ((two40 : ℕ) : ℝ)| ≤ (Rm : ℝ) * ((two40 : ℕ) : ℝ) / SE := by
    rw [abs_mul, abs_of_pos h40p, mul_div_right_comm]
    exact mul_le_mul_of_nonneg_right hB h40p.le
  have eX : (B - (hn : ℝ) / hd) * ((two40 : ℕ) : ℝ) = (B - (T : ℝ) / SE) * ((two40 : ℕ) : ℝ) +
      ((T : ℝ) / SE - (hn : ℝ) / hd) * ((two40 : ℕ) : ℝ) := by ring
  rw [eX]
  rw [abs_le] at hB40 ⊢
  constructor <;> linarith [hB40.1, hB40.2]

/-- **The final assembly of a corner with the rounded vector.** If the true weighted sums `Σ₁`,
`Σ₂` are within the bracket errors of the accumulators, then `2⁴⁰ ‖B - hel‖ ≤ e` and every
component of `2⁴⁰ (B - hel)` is within `ρ` of the rounded vector `Ê`. -/
theorem cornerFinalV_spec (o : Offs) (nS : ℕ) (Xt Yt Zt D : ℕ) (hD : 0 < D) (acc : Acc) (h : QQ × QQ
    × QQ)
    (hh0 : 0 < h.1.den ∧ 0 < h.2.1.den ∧ 0 < h.2.2.den) (B H S1v S2v : Space)
    (hB : ((D : ℝ) * ((two136 : ℕ) : ℝ)) • B = (D : ℝ) • S1v - S32 • cross (vecZ Xt Yt Zt) S2v)
    (hH : H = WithLp.toLp 2 ![h.1.val, h.2.1.val, h.2.2.val]) (n : ℕ) (hn : n ≤ nS)
    (e1 : ℝ) (he1 : e1 = (o.c1m : ℝ) * (7 * (10 * (KT : ℝ) / ((D : ℝ) * S32)) * acc.sf + n))
    (e2 : ℝ) (he2 : e2 = (o.c2m : ℝ) * (7 * (10 * (KT : ℝ) / ((D : ℝ) * S32)) * acc.sf + n))
    (h1x : |S1v 0 - ((acc.sx : ℝ) - o.c1x * acc.sf)| ≤ e1)
    (h1y : |S1v 1 - ((acc.sy : ℝ) - o.c1y * acc.sf)| ≤ e1)
    (h1z : |S1v 2 - ((acc.sz : ℝ) - o.c1z * acc.sf)| ≤ e1)
    (h2x : |S2v 0 - ((acc.tx : ℝ) - o.c2x * acc.sf)| ≤ e2)
    (h2y : |S2v 1 - ((acc.ty : ℝ) - o.c2y * acc.sf)| ≤ e2)
    (h2z : |S2v 2 - ((acc.tz : ℝ) - o.c2z * acc.sf)| ≤ e2)
    (hfin : (cornerFinalV o nS Xt Yt Zt D (Nat.mul D two32) acc h).ok = true) :
    ‖B - H‖ * ((two40 : ℕ) : ℝ) ≤ (cornerFinalV o nS Xt Yt Zt D (Nat.mul D two32) acc h).e ∧
      |(B - H) 0 * ((two40 : ℕ) : ℝ) - (cornerFinalV o nS Xt Yt Zt D (Nat.mul D two32) acc h).ex| ≤
        (cornerFinalV o nS Xt Yt Zt D (Nat.mul D two32) acc h).rho ∧
      |(B - H) 1 * ((two40 : ℕ) : ℝ) - (cornerFinalV o nS Xt Yt Zt D (Nat.mul D two32) acc h).ey| ≤
        (cornerFinalV o nS Xt Yt Zt D (Nat.mul D two32) acc h).rho ∧
      |(B - H) 2 * ((two40 : ℕ) : ℝ) - (cornerFinalV o nS Xt Yt Zt D (Nat.mul D two32) acc h).ez| ≤
        (cornerFinalV o nS Xt Yt Zt D (Nat.mul D two32) acc h).rho := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hS := S32_pos
  have h136 : (0 : ℝ) < ((two136 : ℕ) : ℝ) := by norm_num [two136]
  set SE : ℝ := (D : ℝ) * ((two136 : ℕ) : ℝ)
  have hSE : 0 < SE := mul_pos hD' h136
  have hSEn : ((Nat.mul D two136 : ℕ) : ℝ) = SE := by push_cast [Nat.mul_eq]; rfl
  -- components of `SE • B`
  have hBc : ∀ k : Fin 3, SE * B k = ((D : ℝ) • S1v - S32 • cross (vecZ Xt Yt Zt) S2v) k := by
    intro k; rw [← hB]; simp [SE]
  have hB0 : SE * B 0 = D * S1v 0 - S32 * (Yt * S2v 2 - Zt * S2v 1) := by
    rw [hBc 0]; simp [cross, crossProduct, vecZ]
  have hB1 : SE * B 1 = D * S1v 1 - S32 * (Zt * S2v 0 - Xt * S2v 2) := by
    rw [hBc 1]; simp [cross, crossProduct, vecZ]
  have hB2 : SE * B 2 = D * S1v 2 - S32 * (Xt * S2v 1 - Yt * S2v 0) := by
    rw [hBc 2]; simp [cross, crossProduct, vecZ]
  -- error radii
  have hE : ∀ (cm : ℕ), (cm : ℝ) * (7 * (10 * (KT : ℝ) / ((D : ℝ) * S32)) * acc.sf + n) ≤
      ((Nat.add (cdiv (Nat.mul (Nat.mul (Nat.mul 70 KT) cm) acc.sf) (Nat.mul D two32))
        (Nat.mul nS cm) : ℕ) : ℝ) := by
    intro cm
    have hlam0 : 0 < Nat.mul D two32 := Nat.mul_pos hD (by norm_num [two32])
    have hc := cdiv_ge (Nat.mul (Nat.mul (Nat.mul 70 KT) cm) acc.sf) hlam0
    push_cast [Nat.mul_eq, Nat.add_eq, two32_cast] at hc ⊢
    have hnn : (n : ℝ) ≤ nS := by exact_mod_cast hn
    have : (cm : ℝ) * (7 * (10 * (KT : ℝ) / ((D : ℝ) * S32)) * acc.sf) =
        70 * KT * cm * acc.sf / (D * S32) := by field_simp; ring
    nlinarith [Nat.cast_nonneg (α := ℝ) cm]
  have hE1 := hE o.c1m
  have hE2 := hE o.c2m
  rw [← he1] at hE1
  rw [← he2] at hE2
  have he20 : 0 ≤ e2 := (abs_nonneg _).trans h2x
  have hfl := fun (x : QQ) (hx : 0 < x.den) => QQ.floor_ceil x hx (Nat.mul D two136)
  obtain ⟨fx1, fx2⟩ := hfl h.1 hh0.1
  obtain ⟨fy1, fy2⟩ := hfl h.2.1 hh0.2.1
  obtain ⟨fz1, fz2⟩ := hfl h.2.2 hh0.2.2
  rw [hSEn] at fx1 fx2 fy1 fy2 fz1 fz2
  simp only [cornerFinalV] at hfin ⊢
  simp only [Nat.ble_eq] at hfin
  -- name the checker quantities
  generalize hE1n : Nat.add (cdiv (Nat.mul (Nat.mul (Nat.mul 70 KT) o.c1m) acc.sf) (Nat.mul D
      two32))
    (Nat.mul nS o.c1m) = E1n at hfin ⊢ hE1
  generalize hE2n : Nat.add (cdiv (Nat.mul (Nat.mul (Nat.mul 70 KT) o.c2m) acc.sf) (Nat.mul D
      two32))
    (Nat.mul nS o.c2m) = E2n at hfin ⊢ hE2
  set Tx : ℤ := (D : ℤ) * unoff acc.sx o.c1x acc.sf -
    4294967296 * ((Yt : ℤ) * unoff acc.tz o.c2z acc.sf - (Zt : ℤ) * unoff acc.ty o.c2y acc.sf)
  set Ty : ℤ := (D : ℤ) * unoff acc.sy o.c1y acc.sf -
    4294967296 * ((Zt : ℤ) * unoff acc.tx o.c2x acc.sf - (Xt : ℤ) * unoff acc.tz o.c2z acc.sf)
  set Tz : ℤ := (D : ℤ) * unoff acc.sz o.c1z acc.sf -
    4294967296 * ((Xt : ℤ) * unoff acc.ty o.c2y acc.sf - (Yt : ℤ) * unoff acc.tx o.c2x acc.sf)
  set Rx : ℤ := ((Nat.add (Nat.mul D E1n) (Nat.mul two32 (Nat.mul (Nat.add Yt Zt) E2n)) : ℕ) : ℤ)
  set Ry : ℤ := ((Nat.add (Nat.mul D E1n) (Nat.mul two32 (Nat.mul (Nat.add Zt Xt) E2n)) : ℕ) : ℤ)
  set Rz : ℤ := ((Nat.add (Nat.mul D E1n) (Nat.mul two32 (Nat.mul (Nat.add Xt Yt) E2n)) : ℕ) : ℤ)
  have hun : ∀ x c : ℕ, ((unoff x c acc.sf : ℤ) : ℝ) = (x : ℝ) - c * acc.sf := by
    intro x c; simp [unoff]
  have hTx : (Tx : ℝ) = D * ((acc.sx : ℝ) - o.c1x * acc.sf) -
      S32 * (Yt * ((acc.tz : ℝ) - o.c2z * acc.sf) - Zt * ((acc.ty : ℝ) - o.c2y * acc.sf)) := by
    simp only [Tx]; push_cast [hun]; simp only [S32]
  have hTy : (Ty : ℝ) = D * ((acc.sy : ℝ) - o.c1y * acc.sf) -
      S32 * (Zt * ((acc.tx : ℝ) - o.c2x * acc.sf) - Xt * ((acc.tz : ℝ) - o.c2z * acc.sf)) := by
    simp only [Ty]; push_cast [hun]; simp only [S32]
  have hTz : (Tz : ℝ) = D * ((acc.sz : ℝ) - o.c1z * acc.sf) -
      S32 * (Xt * ((acc.ty : ℝ) - o.c2y * acc.sf) - Yt * ((acc.tx : ℝ) - o.c2x * acc.sf)) := by
    simp only [Tz]; push_cast [hun]; simp only [S32]
  have hRx : (Rx : ℝ) = D * E1n + S32 * ((Yt + Zt) * E2n) := by
    simp only [Rx]; push_cast [Nat.mul_eq, Nat.add_eq, two32_cast]; ring
  have hRy : (Ry : ℝ) = D * E1n + S32 * ((Zt + Xt) * E2n) := by
    simp only [Ry]; push_cast [Nat.mul_eq, Nat.add_eq, two32_cast]; ring
  have hRz : (Rz : ℝ) = D * E1n + S32 * ((Xt + Yt) * E2n) := by
    simp only [Rz]; push_cast [Nat.mul_eq, Nat.add_eq, two32_cast]; ring
  have hXt : (0 : ℝ) ≤ Xt := Nat.cast_nonneg _
  have hYt : (0 : ℝ) ≤ Yt := Nat.cast_nonneg _
  have hZt : (0 : ℝ) ≤ Zt := Nat.cast_nonneg _
  have cxb : ∀ (a b : ℝ) (P Q : ℝ), 0 ≤ P → 0 ≤ Q → |a| ≤ e2 → |b| ≤ e2 →
      |P * a - Q * b| ≤ (P + Q) * e2 := by
    intro a b P Q hP hQ ha hb
    calc |P * a - Q * b| ≤ |P * a| + |Q * b| := abs_sub _ _
      _ = P * |a| + Q * |b| := by rw [abs_mul, abs_mul, abs_of_nonneg hP, abs_of_nonneg hQ]
      _ ≤ P * e2 + Q * e2 := by gcongr
      _ = (P + Q) * e2 := by ring
  have bx : |SE * B 0 - Tx| ≤ Rx := by
    rw [hB0, hTx, hRx]
    have h1 : |(D : ℝ) * (S1v 0 - ((acc.sx : ℝ) - o.c1x * acc.sf))| ≤ D * E1n := by
      rw [abs_mul, abs_of_pos hD']; exact mul_le_mul_of_nonneg_left (h1x.trans hE1) hD'.le
    have h2 := cxb (S2v 2 - ((acc.tz : ℝ) - o.c2z * acc.sf)) (S2v 1 - ((acc.ty : ℝ) - o.c2y *
        acc.sf))
      Yt Zt hYt hZt h2z h2y
    have h3 : |S32 * (Yt * (S2v 2 - ((acc.tz : ℝ) - o.c2z * acc.sf)) -
        Zt * (S2v 1 - ((acc.ty : ℝ) - o.c2y * acc.sf)))| ≤ S32 * ((Yt + Zt) * E2n) := by
      rw [abs_mul, abs_of_pos hS]
      exact mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left hE2 (by positivity)))
          hS.le
    calc |D * S1v 0 - S32 * (Yt * S2v 2 - Zt * S2v 1) - (D * ((acc.sx : ℝ) - o.c1x * acc.sf) -
          S32 * (Yt * ((acc.tz : ℝ) - o.c2z * acc.sf) - Zt * ((acc.ty : ℝ) - o.c2y * acc.sf)))|
        = |(D : ℝ) * (S1v 0 - ((acc.sx : ℝ) - o.c1x * acc.sf)) - S32 * (Yt * (S2v 2 -
            ((acc.tz : ℝ) - o.c2z * acc.sf))
            - Zt * (S2v 1 - ((acc.ty : ℝ) - o.c2y * acc.sf)))| := by
          ring_nf
      _ ≤ _ := (abs_sub _ _).trans (add_le_add h1 h3)
  have by' : |SE * B 1 - Ty| ≤ Ry := by
    rw [hB1, hTy, hRy]
    have h1 : |(D : ℝ) * (S1v 1 - ((acc.sy : ℝ) - o.c1y * acc.sf))| ≤ D * E1n := by
      rw [abs_mul, abs_of_pos hD']; exact mul_le_mul_of_nonneg_left (h1y.trans hE1) hD'.le
    have h2 := cxb (S2v 0 - ((acc.tx : ℝ) - o.c2x * acc.sf)) (S2v 2 - ((acc.tz : ℝ) - o.c2z *
        acc.sf))
      Zt Xt hZt hXt h2x h2z
    have h3 : |S32 * (Zt * (S2v 0 - ((acc.tx : ℝ) - o.c2x * acc.sf)) -
        Xt * (S2v 2 - ((acc.tz : ℝ) - o.c2z * acc.sf)))| ≤ S32 * ((Zt + Xt) * E2n) := by
      rw [abs_mul, abs_of_pos hS]
      exact mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left hE2 (by positivity)))
          hS.le
    calc |D * S1v 1 - S32 * (Zt * S2v 0 - Xt * S2v 2) - (D * ((acc.sy : ℝ) - o.c1y * acc.sf) -
          S32 * (Zt * ((acc.tx : ℝ) - o.c2x * acc.sf) - Xt * ((acc.tz : ℝ) - o.c2z * acc.sf)))|
        = |(D : ℝ) * (S1v 1 - ((acc.sy : ℝ) - o.c1y * acc.sf)) - S32 * (Zt * (S2v 0 -
            ((acc.tx : ℝ) - o.c2x * acc.sf))
            - Xt * (S2v 2 - ((acc.tz : ℝ) - o.c2z * acc.sf)))| := by
          ring_nf
      _ ≤ _ := (abs_sub _ _).trans (add_le_add h1 h3)
  have bz : |SE * B 2 - Tz| ≤ Rz := by
    rw [hB2, hTz, hRz]
    have h1 : |(D : ℝ) * (S1v 2 - ((acc.sz : ℝ) - o.c1z * acc.sf))| ≤ D * E1n := by
      rw [abs_mul, abs_of_pos hD']; exact mul_le_mul_of_nonneg_left (h1z.trans hE1) hD'.le
    have h2 := cxb (S2v 1 - ((acc.ty : ℝ) - o.c2y * acc.sf)) (S2v 0 - ((acc.tx : ℝ) - o.c2x *
        acc.sf))
      Xt Yt hXt hYt h2y h2x
    have h3 : |S32 * (Xt * (S2v 1 - ((acc.ty : ℝ) - o.c2y * acc.sf)) -
        Yt * (S2v 0 - ((acc.tx : ℝ) - o.c2x * acc.sf)))| ≤ S32 * ((Xt + Yt) * E2n) := by
      rw [abs_mul, abs_of_pos hS]
      exact mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left hE2 (by positivity)))
          hS.le
    calc |D * S1v 2 - S32 * (Xt * S2v 1 - Yt * S2v 0) - (D * ((acc.sz : ℝ) - o.c1z * acc.sf) -
          S32 * (Xt * ((acc.ty : ℝ) - o.c2y * acc.sf) - Yt * ((acc.tx : ℝ) - o.c2x * acc.sf)))|
        = |(D : ℝ) * (S1v 2 - ((acc.sz : ℝ) - o.c1z * acc.sf)) - S32 * (Xt * (S2v 1 -
            ((acc.ty : ℝ) - o.c2y * acc.sf))
            - Yt * (S2v 0 - ((acc.tx : ℝ) - o.c2x * acc.sf)))| := by
          ring_nf
      _ ≤ _ := (abs_sub _ _).trans (add_le_add h1 h3)
  -- the three component bounds
  have hH0 : H 0 = h.1.val := by rw [hH]; simp
  have hH1 : H 1 = h.2.1.val := by rw [hH]; simp
  have hH2 : H 2 = h.2.2.val := by rw [hH]; simp
  obtain ⟨mx1, mx2⟩ := nmax_natAbs (Tx - Rx - h.1.ceilMul (Nat.mul D two136))
    (Tx + Rx - h.1.floorMul (Nat.mul D two136))
  obtain ⟨my1, my2⟩ := nmax_natAbs (Ty - Ry - h.2.1.ceilMul (Nat.mul D two136))
    (Ty + Ry - h.2.1.floorMul (Nat.mul D two136))
  obtain ⟨mz1, mz2⟩ := nmax_natAbs (Tz - Rz - h.2.2.ceilMul (Nat.mul D two136))
    (Tz + Rz - h.2.2.floorMul (Nat.mul D two136))
  generalize nmax (Tx - Rx - h.1.ceilMul (Nat.mul D two136)).natAbs
    (Tx + Rx - h.1.floorMul (Nat.mul D two136)).natAbs = mx at mx1 mx2 hfin ⊢
  generalize nmax (Ty - Ry - h.2.1.ceilMul (Nat.mul D two136)).natAbs
    (Ty + Ry - h.2.1.floorMul (Nat.mul D two136)).natAbs = my at my1 my2 hfin ⊢
  generalize nmax (Tz - Rz - h.2.2.ceilMul (Nat.mul D two136)).natAbs
    (Tz + Rz - h.2.2.floorMul (Nat.mul D two136)).natAbs = mz at mz1 mz2 hfin ⊢
  push_cast at mx1 mx2 my1 my2 mz1 mz2
  have c0 : |(B - H) 0 * SE| ≤ mx := by
    rw [PiLp.sub_apply, hH0, sub_mul, mul_comm (B 0)]
    exact comp_bound bx fx1 fx2 mx1 mx2
  have c1 : |(B - H) 1 * SE| ≤ my := by
    rw [PiLp.sub_apply, hH1, sub_mul, mul_comm (B 1)]
    exact comp_bound by' fy1 fy2 my1 my2
  have c2 : |(B - H) 2 * SE| ≤ mz := by
    rw [PiLp.sub_apply, hH2, sub_mul, mul_comm (B 2)]
    exact comp_bound bz fz1 fz2 mz1 mz2
  generalize hsN : sqrtUpFrom (Nat.mul (Nat.add (Nat.add (sq mx) (sq my)) (sq mz)) (sq two40))
    (Nat.mul (Nat.add (Nat.add mx my) mz) two40) = sN at hfin ⊢
  have hN : ((mx : ℝ) ^ 2 + (my : ℝ) ^ 2 + (mz : ℝ) ^ 2) * ((two40 : ℕ) : ℝ) ^ 2 ≤ (sN : ℝ) ^
      2 := by
    have := (by exact_mod_cast hfin : ((Nat.mul (Nat.add (Nat.add (sq mx) (sq my)) (sq mz))
      (sq two40) : ℕ) : ℝ) ≤ ((sq sN : ℕ) : ℝ))
    push_cast [Nat.mul_eq, Nat.add_eq, sq_cast] at this
    linarith
  have h40 : (0 : ℝ) < ((two40 : ℕ) : ℝ) := by norm_num [two40]
  have hfinal := norm_from_comps hSE h40 c0 c1 c2 hN (Nat.cast_nonneg _)
  have hSEpos : 0 < Nat.mul D two136 := Nat.mul_pos hD (by norm_num [two136])
  have hcd := cdiv_ge sN hSEpos
  rw [hSEn] at hcd
  refine ⟨by linarith, ?_, ?_, ?_⟩
  · rw [PiLp.sub_apply, hH0]
    exact box_comp hSEpos hh0.1 (by rw [hSEn]; exact bx) (rmax_ge _ _ _).1
  · rw [PiLp.sub_apply, hH1]
    exact box_comp hSEpos hh0.2.1 (by rw [hSEn]; exact by') (rmax_ge _ _ _).2.1
  · rw [PiLp.sub_apply, hH2]
    exact box_comp hSEpos hh0.2.2 (by rw [hSEn]; exact bz) (rmax_ge _ _ _).2.2


/-! ## The remainder walk -/

/-- The `w`-term of `remStep`. -/
@[expose] def remTW (D2 : ℕ) (P : RemP) (x : Seg × VR × VR) : ℕ :=
  let Lw := cellL P.rcW (d2Low x.2.1.n x.2.2.n (Nat.mul D2 x.1.vv))
  cdiv (Nat.mul x.1.kv P.w6) (Nat.mul (Nat.mul (Nat.mul Lw Lw) Lw) two24)

/-- The `t`-term of `remStep`. -/
@[expose] def remTT (D2 : ℕ) (P : RemP) (x : Seg × VR × VR) : ℕ :=
  let Lt := cellL P.rcT (d2Low x.2.1.n x.2.2.n (Nat.mul D2 x.1.vv))
  cdiv (Nat.mul x.1.kv (Nat.add P.t6 (Nat.mul Lt (Nat.add P.t4 (Nat.mul Lt P.t2)))))
    (Nat.mul (Nat.mul (Nat.mul Lt Lt) Lt) two24)

/-- The checks of `remStep`. -/
@[expose] def remChk (D2 : ℕ) (P : RemP) (x : Seg × VR × VR) : Bool :=
  let d2 := d2Low x.2.1.n x.2.2.n (Nat.mul D2 x.1.vv)
  (Nat.blt 0 (cellL P.rcW d2) && Nat.blt 0 (cellL P.rcT d2)) &&
    Nat.ble P.lam2 (Nat.mul 25 (cellL P.rcT d2))

/-- Folding `remStep`. -/
theorem fold_remStep (D2 : ℕ) (P : RemP) (L : List (Seg × VR × VR)) (a b : ℕ) (c : Bool) :
    L.foldl (remStep D2 P) (a, b, c) = (a + (L.map (remTW D2 P)).sum, b + (L.map (remTT D2 P)).sum,
      c && L.all (remChk D2 P)) := by
  induction L generalizing a b c with
  | nil => simp
  | cons x L ih =>
    simp only [List.foldl_cons]
    have e : remStep D2 P (a, b, c) x =
        (a + remTW D2 P x, b + remTT D2 P x, c && remChk D2 P x) := by
      simp only [remStep, remTW, remTT, remChk, Bool.and_assoc]; rfl
    rw [e, ih]
    simp only [List.map_cons, List.sum_cons, List.all_cons, Bool.and_assoc]
    refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> simp <;> ring

/-- The segment triples of the corner are the checker triples of the semantic records. -/
theorem triples4_eq (o : Offs) : ∀ (fils : List (ℤ × List (ℤ × ℤ × ℤ))) (vss : List (List VR)),
    triples4 (fils.map fun f => mkFil o f.1 f.2) vss = (allRecs fils vss).map (srTriple o)
  | [], vss => by simp [triples4, allRecs]
  | f :: fils, [] => by simp [triples4, allRecs]
  | f :: fils, v :: vss => by
    have ih := triples4_eq o fils vss
    simp only [triples4, allRecs, List.map_cons, List.zip_cons_cons, List.flatMap_cons,
      List.map_append] at ih ⊢
    rw [ih, filWalk_list]

/-- **Soundness of one corner of the cubic checker.** -/
theorem cornerEval4_sound (o : Offs) (nS : ℕ) (fils : List (ℤ × List (ℤ × ℤ × ℤ)))
    (hne : ∀ f ∈ fils, f.2 ≠ []) (hfok : ∀ f ∈ fils, filOK o f.1 f.2 = true)
    (hlen : (allSegs fils).length ≤ nS) (Xt Yt Zt D : ℕ) (hD : 0 < D) (h : QQ × QQ × QQ)
    (hh0 : 0 < h.1.den ∧ 0 < h.2.1.den ∧ 0 < h.2.2.den)
    (hhel : hel (cornerR Xt Yt Zt D) = WithLp.toLp 2 ![h.1.val, h.2.1.val, h.2.2.val])
    (P : Option RemP) (gs : List (List ℕ))
    (hok : (cornerEval4 o nS (fils.map fun f => mkFil o f.1 f.2) Xt Yt Zt D h P gs).ok = true) :
    let co := cornerEval4 o nS (fils.map fun f => mkFil o f.1 f.2) Xt Yt Zt D h P gs
    let E := Bseg fils (cornerR Xt Yt Zt D) - hel (cornerR Xt Yt Zt D)
    (‖E‖ * ((two40 : ℕ) : ℝ) ≤ co.fin.e ∧ |E 0 * ((two40 : ℕ) : ℝ) - co.fin.ex| ≤ co.fin.rho ∧
      |E 1 * ((two40 : ℕ) : ℝ) - co.fin.ey| ≤ co.fin.rho ∧
      |E 2 * ((two40 : ℕ) : ℝ) - co.fin.ez| ≤ co.fin.rho) ∧
    ∀ Q : RemP, P = some Q →
      ∃ R : List SRec, R.map (fun z => (z.1, z.2.1, z.2.2.1)) = allSegs fils ∧
        (∀ z ∈ R, VRok Xt Yt Zt D z.2.1 z.2.2.2.1 ∧ VRok Xt Yt Zt D z.2.2.1 z.2.2.2.2 ∧
          segOK o z.1 z.2.1 z.2.2.1 = true ∧ remChk (Nat.mul D D) Q (srTriple o z) = true) ∧
        co.rw = (R.map fun z => remTW (Nat.mul D D) Q (srTriple o z)).sum ∧
        co.rt = (R.map fun z => remTT (Nat.mul D D) Q (srTriple o z)).sum ∧
        Q.rcW.rBD ≤ Q.rcW.s0l ∧ Q.rcT.rBD ≤ Q.rcT.s0l ∧ Q.nt ≤ sq Q.rcT.rBD := by
  intro co E
  set y := cornerR Xt Yt Zt D
  set fs := fils.map fun f => mkFil o f.1 f.2
  set c := mkCD Xt Yt Zt D with hc
  set vss := allVerts c fs gs
  set D3S := Nat.mul (Nat.mul (Nat.mul D D) D) two136
  set R := allRecs fils vss
  have hwalk := allWalk_eq o (Nat.mul D D) D3S noRC c fils gs ⟨0, 0, 0, 0, 0, 0, 0, 0, true⟩ hne
  set acc := walkL (Nat.mul D D) D3S noRC (R.map (srTriple o)) ⟨0, 0, 0, 0, 0, 0, 0, 0, true⟩
  have htri : triples4 fs vss = R.map (srTriple o) := triples4_eq o fils vss
  have hwalk' : allWalk (Nat.mul D D) (Nat.mul (Nat.mul (Nat.mul D D) D) two136) noRC
      ⟨0, 0, 0, 0, 0, 0, 0, 0, true⟩ fs
      (allVerts ⟨D, Nat.mul D D, Nat.mul Xt two32, Nat.mul Yt two32, Nat.mul Zt two32,
        Nat.add (Nat.add (sq (Nat.mul Xt two32)) (sq (Nat.mul Yt two32))) (sq (Nat.mul Zt two32)),
        Nat.mul D two32⟩ fs gs) = acc := hwalk
  have hfin_eq : co.fin = cornerFinalV o nS Xt Yt Zt D (Nat.mul D two32) acc h := by
    simp only [co, cornerEval4]
    rw [hwalk']
  have hok' : (acc.ok = true ∧ (cornerFinalV o nS Xt Yt Zt D (Nat.mul D two32) acc h).ok = true) ∧
      1000 * KT ≤ D * two32 := by
    have := hok
    simp only [cornerEval4, Bool.and_eq_true, Nat.ble_eq] at this
    rw [hwalk'] at this
    exact ⟨⟨this.1.1.1, this.1.1.2⟩, by simpa [Nat.mul_eq] using this.1.2⟩
  obtain ⟨⟨hacc, hfin⟩, hlamK⟩ := hok'
  obtain ⟨hsx, hsy, hsz, htx, hty, htz, hsf, -, hall⟩ :=
    fold_segStep (Nat.mul D D) D3S noRC (R.map (srTriple o)) ⟨0, 0, 0, 0, 0, 0, 0, 0, true⟩
  have hchk := (hall hacc).2
  -- per-record facts
  have hrec := allRecs_sound o Xt Yt Zt D hD fils gs hfok
  have hRsegs : R.map (fun z => (z.1, z.2.1, z.2.2.1)) = allSegs fils := allRecs_segs o c fils gs
  have hRlen : R.length ≤ nS := by
    have := congrArg List.length hRsegs; rw [List.length_map] at this; omega
  set f : SRec → ℕ := fun z => segF (Nat.mul D D) D3S (mkSeg o z.1 z.2.1 z.2.2.1) z.2.2.2.1
      z.2.2.2.2
  set u : ℝ := 10 * (KT : ℝ) / ((D : ℝ) * S32)
  have hlamR : (0 : ℝ) < D * S32 := mul_pos (by exact_mod_cast hD) S32_pos
  have hu0 : 0 ≤ u := by positivity
  have hbr : ∀ z ∈ R, FR Xt Yt Zt D z ≤ f z + 1 ∧ (1 - 7 * u) * f z ≤ FR Xt Yt Zt D z := by
    intro z hz
    obtain ⟨ha, hb, hs⟩ := hrec z hz
    have hx := hchk (srTriple o z) (List.mem_map_of_mem hz)
    simp only [srTriple, segChk, segRT, noRC, Bool.cond_false, Bool.and_eq_true, Nat.ble_eq] at hx
    obtain ⟨⟨⟨hoka, hokb⟩, hcmp⟩, -⟩ := hx
    have hw := mkSeg_weights hs
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hvv⟩ := hw
    have hlam' : 1000 * KT ≤ D * two32 := by simpa [Nat.mul_eq] using hlamK
    have := segFactor_sound Xt Yt Zt D hD ha hb hoka hokb hlam' hvv
      (by simpa [Nat.mul_eq, Nat.add_eq] using hcmp)
    exact this
  -- accumulators as sums over records
  have hmem : ∀ z ∈ R, segOK o z.1 z.2.1 z.2.2.1 = true := fun z hz => (hrec z hz).2.2
  have hsum : ∀ (g : Seg → ℕ) (G : SRec → ℝ), (∀ z ∈ R, ((g (mkSeg o z.1 z.2.1 z.2.2.1) : ℕ) : ℝ) =
      G z) →
      (((R.map (srTriple o)).map fun x => segF (Nat.mul D D) D3S x.1 x.2.1 x.2.2 * g x.1).sum : ℝ) =
        (R.map fun z => (f z : ℝ) * G z).sum := by
    intro g G hg
    rw [Nat.cast_list_sum, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun z hz => ?_
    simp only [Function.comp, srTriple, f]
    push_cast
    rw [hg z hz]
  have hwz : ∀ z ∈ R, ((mkSeg o z.1 z.2.1 z.2.2.1).w1x : ℝ) = W1R z 0 + o.c1x ∧
      ((mkSeg o z.1 z.2.1 z.2.2.1).w1y : ℝ) = W1R z 1 + o.c1y ∧
      ((mkSeg o z.1 z.2.1 z.2.2.1).w1z : ℝ) = W1R z 2 + o.c1z ∧
      ((mkSeg o z.1 z.2.1 z.2.2.1).w2x : ℝ) = W2R z 0 + o.c2x ∧
      ((mkSeg o z.1 z.2.1 z.2.2.1).w2y : ℝ) = W2R z 1 + o.c2y ∧
      ((mkSeg o z.1 z.2.1 z.2.2.1).w2z : ℝ) = W2R z 2 + o.c2z ∧
      |W1R z 0| ≤ o.c1m ∧ |W1R z 1| ≤ o.c1m ∧ |W1R z 2| ≤ o.c1m ∧
      |W2R z 0| ≤ o.c2m ∧ |W2R z 1| ≤ o.c2m ∧ |W2R z 2| ≤ o.c2m := by
    intro z hz
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, -⟩ := mkSeg_weights (hmem z hz)
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩
  have hsf' : ((acc.sf : ℕ) : ℝ) = (R.map fun z => (f z : ℝ)).sum := by
    rw [hsf]
    simp only [zero_add]
    rw [Nat.cast_list_sum, List.map_map, List.map_map]
    rfl
  -- the six weighted sums of the checker
  have key : ∀ (g : Seg → ℕ) (W : SRec → ℝ) (cw : ℕ),
      (∀ z ∈ R, ((g (mkSeg o z.1 z.2.1 z.2.2.1) : ℕ) : ℝ) = W z + cw) →
      (((R.map (srTriple o)).map fun x => segF (Nat.mul D D) D3S x.1 x.2.1 x.2.2 * g x.1).sum : ℝ) -
        (cw : ℝ) * acc.sf = (R.map fun z => (f z : ℝ) * W z).sum := by
    intro g W cw hg
    rw [hsum g (fun z => W z + cw) hg, hsf']
    simp only [mul_add, List.sum_map_add]
    rw [List.sum_map_mul_right]
    ring
  have hux : u ≤ 1 / 100 := by
    have : (1000 * KT : ℝ) ≤ D * S32 := by
      have := (by exact_mod_cast hlamK : ((Nat.mul 1000 KT : ℕ) : ℝ) ≤ ((Nat.mul D two32 : ℕ) : ℝ))
      push_cast [Nat.mul_eq, two32_cast] at this; linarith
    simp only [u]; rw [div_le_iff₀ hlamR]; linarith
  have b1x := sum_bracket R (FR Xt Yt Zt D) f (fun z => W1R z 0) hu0 hbr (fun z hz => (hwz z
      hz).2.2.2.2.2.2.1)
  have b1y := sum_bracket R (FR Xt Yt Zt D) f (fun z => W1R z 1) hu0 hbr (fun z hz => (hwz z
      hz).2.2.2.2.2.2.2.1)
  have b1z := sum_bracket R (FR Xt Yt Zt D) f (fun z => W1R z 2) hu0 hbr
    (fun z hz => (hwz z hz).2.2.2.2.2.2.2.2.1)
  have b2x := sum_bracket R (FR Xt Yt Zt D) f (fun z => W2R z 0) hu0 hbr
    (fun z hz => (hwz z hz).2.2.2.2.2.2.2.2.2.1)
  have b2y := sum_bracket R (FR Xt Yt Zt D) f (fun z => W2R z 1) hu0 hbr
    (fun z hz => (hwz z hz).2.2.2.2.2.2.2.2.2.2.1)
  have b2z := sum_bracket R (FR Xt Yt Zt D) f (fun z => W2R z 2) hu0 hbr
    (fun z hz => (hwz z hz).2.2.2.2.2.2.2.2.2.2.2)
  rw [← hsf'] at b1x b1y b1z b2x b2y b2z
  have hacc0 : ∀ (g : Seg → ℕ) (W : SRec → ℝ) (cw : ℕ) (val : ℕ),
      val = 0 + ((R.map (srTriple o)).map fun x => segF (Nat.mul D D) D3S x.1 x.2.1 x.2.2 * g
          x.1).sum →
      (∀ z ∈ R, ((g (mkSeg o z.1 z.2.1 z.2.2.1) : ℕ) : ℝ) = W z + cw) →
      (val : ℝ) - cw * acc.sf = (R.map fun z => (f z : ℝ) * W z).sum := by
    intro g W cw val hv hg
    rw [hv, zero_add]
    exact key g W cw hg
  have a1x := hacc0 Seg.w1x (fun z => W1R z 0) o.c1x acc.sx hsx (fun z hz => (hwz z hz).1)
  have a1y := hacc0 Seg.w1y (fun z => W1R z 1) o.c1y acc.sy hsy (fun z hz => (hwz z hz).2.1)
  have a1z := hacc0 Seg.w1z (fun z => W1R z 2) o.c1z acc.sz hsz (fun z hz => (hwz z hz).2.2.1)
  have a2x := hacc0 Seg.w2x (fun z => W2R z 0) o.c2x acc.tx htx (fun z hz => (hwz z hz).2.2.2.1)
  have a2y := hacc0 Seg.w2y (fun z => W2R z 1) o.c2y acc.ty hty (fun z hz => (hwz z hz).2.2.2.2.1)
  have a2z := hacc0 Seg.w2z (fun z => W2R z 2) o.c2z acc.tz htz
    (fun z hz => (hwz z hz).2.2.2.2.2.1)
  have l1 : ∀ k, (R.map fun z => FR Xt Yt Zt D z • W1R z).sum k =
      (R.map fun z => FR Xt Yt Zt D z * W1R z k).sum := by
    intro k; rw [list_sum_apply]; simp
  have l2 : ∀ k, (R.map fun z => FR Xt Yt Zt D z • W2R z).sum k =
      (R.map fun z => FR Xt Yt Zt D z * W2R z k).sum := by
    intro k; rw [list_sum_apply]; simp
  have hspec := cornerFinalV_spec o nS Xt Yt Zt D hD acc h hh0 (Bseg fils y) (hel y)
    (R.map fun z => FR Xt Yt Zt D z • W1R z).sum (R.map fun z => FR Xt Yt Zt D z • W2R z).sum
    (Bseg_scaled fils R hRsegs Xt Yt Zt D hD) hhel R.length hRlen _ rfl _ rfl
    (by rw [l1, a1x]; exact b1x) (by rw [l1, a1y]; exact b1y) (by rw [l1, a1z]; exact b1z)
    (by rw [l2, a2x]; exact b2x) (by rw [l2, a2y]; exact b2y) (by rw [l2, a2z]; exact b2z) hfin
  rw [hfin_eq]
  refine ⟨hspec, fun Q hQ => ?_⟩
  subst hQ
  have hfold := fold_remStep (Nat.mul D D) Q (R.map (srTriple o)) 0 0
    ((Nat.ble Q.rcW.rBD Q.rcW.s0l && Nat.ble Q.rcT.rBD Q.rcT.s0l) && Nat.ble Q.nt (sq Q.rcT.rBD))
  have hco : co.rw = 0 + ((R.map (srTriple o)).map (remTW (Nat.mul D D) Q)).sum ∧
      co.rt = 0 + ((R.map (srTriple o)).map (remTT (Nat.mul D D) Q)).sum ∧
      (co.ok = true → (((Nat.ble Q.rcW.rBD Q.rcW.s0l && Nat.ble Q.rcT.rBD Q.rcT.s0l) &&
        Nat.ble Q.nt (sq Q.rcT.rBD)) && (R.map (srTriple o)).all (remChk (Nat.mul D D) Q)) =
            true) := by
    have htri2 := htri
    simp only [fs, vss, c, mkCD] at htri2
    simp only [co, cornerEval4]
    rw [htri2, hfold]
    refine ⟨rfl, rfl, fun hh => ?_⟩
    simp only [Bool.and_eq_true] at hh ⊢
    exact hh.2
  obtain ⟨hrw, hrt, hrok⟩ := hco
  have hremok := hrok hok
  simp only [Bool.and_eq_true, Nat.ble_eq, List.all_eq_true] at hremok
  obtain ⟨⟨⟨hW, hT⟩, hN⟩, hchkR⟩ := hremok
  refine ⟨R, hRsegs, fun z hz => ?_, by rw [hrw]; simp [List.map_map]; rfl,
    by rw [hrt]; simp [List.map_map]; rfl, hW, hT, hN⟩
  obtain ⟨ha, hb, hs⟩ := hrec z hz
  exact ⟨ha, hb, hs, hchkR _ (List.mem_map_of_mem hz)⟩

end PlasmaLean.Design.PolygonCoil
