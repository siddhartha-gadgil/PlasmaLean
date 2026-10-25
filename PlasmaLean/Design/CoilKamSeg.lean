/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.CoilKamArith
public import PlasmaLean.Design.CoilFieldComplex
public import PlasmaLean.Certificates.KernelFact

/-!
# Exact sampled evaluation of the coil field at dyadic points

Stage 2 of the coil-field KAM (`notes/theory/coil-kam-status.md`). The real coil field
`tfField + polyCoilFieldC` (TF rectangle and the 192 segments of `filsC`) is evaluated at a
dyadic point `ỹ = Y/D` (`D = 2³² D₀`) by integer arithmetic only:

* every segment `p → q` gives integer vectors `a = p - Y`, `b = q - Y` (scale `D`), the exact
  integers `|a|²`, `|b|²`, `a·b`, `a × b`, `|a × b|²`, and checked square-root brackets
  `A ≤ D|a| ≤ A'` (`sqrtBr`);
* the closed-form factor `f = (α+β)/(αβ(αβ + a·b))` of `segClosed` is bracketed by monotonicity,
  in the direct form for `a·b ≥ 0` (`fac_bounds_direct`) and, for `a·b < 0` (the long TF legs,
  where `αβ + a·b` cancels), in the stable form `f = (α+β)(αβ - a·b)/(αβ|a×b|²)`
  (`segFac'_stable`, `fac_bounds_stable`);
* `segAP` returns the three components as approximants (`Approx`), or `none` if a check fails;
  `segAP_sound` is the soundness theorem;
* `fieldAP` sums over the 196 segments (`allSegsD`); `fieldAP_sound`: if `fieldAP D₀ Y = some r`
  and `ỹ` lies in the real tube `realTube w` (`w < 7/20`), then `r` approximates every component
  of `tfField ỹ + polyCoilFieldC ỹ`.

**Sanity.** `ptD_scale` (coil vertices are the `ptR` points), `segAP_degenerate` (a segment
through the point is rejected) and `fieldAP_fixture` (the field at `(1,0,0)` is accepted, computed
by the kernel at scale `2³²`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.CoilKam

open PlasmaLean.Fields PlasmaLean.Design.PolygonCoil PlasmaLean.Design.RationalStellarator
  PlasmaLean.Design.RationalStellarator.CoilsTF PlasmaLean.Design.CoilFieldComplex
open scoped RealInnerProductSpace

/-! ## Integer vectors -/

/-- The point `v/D` of an integer triple. -/
def ptD (D : ℕ) (v : ℤ × ℤ × ℤ) : Space :=
  WithLp.toLp 2 ![(v.1 : ℝ) / D, (v.2.1 : ℝ) / D, (v.2.2 : ℝ) / D]

/-- Difference of integer triples. -/
def sub3 (p y : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (p.1 - y.1, p.2.1 - y.2.1, p.2.2 - y.2.2)

/-- Dot product of integer triples. -/
def dot3 (a b : ℤ × ℤ × ℤ) : ℤ := a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

/-- Cross product of integer triples. -/
def cross3 (a b : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (a.2.1 * b.2.2 - a.2.2 * b.2.1, a.2.2 * b.1 - a.1 * b.2.2, a.1 * b.2.1 - a.2.1 * b.1)

/-- Scale an integer triple. -/
def scl3 (c : ℤ) (v : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (c * v.1, c * v.2.1, c * v.2.2)

theorem ptD_apply (D : ℕ) (v : ℤ × ℤ × ℤ) :
    ptD D v 0 = (v.1 : ℝ) / D ∧ ptD D v 1 = (v.2.1 : ℝ) / D ∧ ptD D v 2 = (v.2.2 : ℝ) / D := by
  simp [ptD]

theorem ptD_sub_apply (D : ℕ) (p y : ℤ × ℤ × ℤ) :
    (ptD D p - ptD D y) 0 = ((sub3 p y).1 : ℝ) / D ∧
    (ptD D p - ptD D y) 1 = ((sub3 p y).2.1 : ℝ) / D ∧
    (ptD D p - ptD D y) 2 = ((sub3 p y).2.2 : ℝ) / D := by
  simp only [PiLp.sub_apply, ptD, sub3]
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> ring

theorem cross_coords' (u v : Space) :
    cross u v 0 = u 1 * v 2 - u 2 * v 1 ∧
    cross u v 1 = u 2 * v 0 - u 0 * v 2 ∧
    cross u v 2 = u 0 * v 1 - u 1 * v 0 := by
  simp [cross, cross_apply]

theorem norm_sq_space' (v : Space) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
  simp [sq_abs]

theorem inner_space' (u v : Space) : ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

theorem dot3_self_nonneg (v : ℤ × ℤ × ℤ) : 0 ≤ dot3 v v := by
  unfold dot3; nlinarith [mul_self_nonneg v.1, mul_self_nonneg v.2.1, mul_self_nonneg v.2.2]

/-- `‖ptD p - ptD y‖ = √(|p - y|²)/D`. -/
theorem norm_ptD_sub (D : ℕ) (hD : 0 < D) (p y : ℤ × ℤ × ℤ) :
    ‖ptD D p - ptD D y‖ = Real.sqrt ((dot3 (sub3 p y) (sub3 p y)).toNat) / D := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hnn := dot3_self_nonneg (sub3 p y)
  have hcast : (((dot3 (sub3 p y) (sub3 p y)).toNat : ℕ) : ℝ) =
      ((dot3 (sub3 p y) (sub3 p y) : ℤ) : ℝ) := by
    rw [show (((dot3 (sub3 p y) (sub3 p y)).toNat : ℕ) : ℝ) =
      (((dot3 (sub3 p y) (sub3 p y)).toNat : ℤ) : ℝ) by norm_cast, Int.toNat_of_nonneg hnn]
  obtain ⟨h0, h1, h2⟩ := ptD_sub_apply D p y
  rw [hcast, ← Real.sqrt_sq (norm_nonneg (ptD D p - ptD D y)), norm_sq_space', h0, h1, h2]
  have e : (((sub3 p y).1 : ℝ) / D) ^ 2 + (((sub3 p y).2.1 : ℝ) / D) ^ 2 +
      (((sub3 p y).2.2 : ℝ) / D) ^ 2 = ((dot3 (sub3 p y) (sub3 p y) : ℤ) : ℝ) / D ^ 2 := by
    unfold dot3; push_cast; field_simp
  rw [e, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hD'.le]

/-- `⟪ptD p - ptD y, ptD q - ptD y⟫ = (a·b)/D²`. -/
theorem inner_ptD_sub (D : ℕ) (hD : 0 < D) (p q y : ℤ × ℤ × ℤ) :
    ⟪ptD D p - ptD D y, ptD D q - ptD D y⟫ = (dot3 (sub3 p y) (sub3 q y) : ℝ) / D ^ 2 := by
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  obtain ⟨a0, a1, a2⟩ := ptD_sub_apply D p y
  obtain ⟨b0, b1, b2⟩ := ptD_sub_apply D q y
  rw [inner_space', a0, a1, a2, b0, b1, b2]
  unfold dot3; push_cast; field_simp

/-- Components of `cross (ptD p - ptD y) (ptD q - ptD y)` are `(a × b)ᵢ/D²`. -/
theorem cross_ptD_sub (D : ℕ) (hD : 0 < D) (p q y : ℤ × ℤ × ℤ) :
    cross (ptD D p - ptD D y) (ptD D q - ptD D y) 0 =
      ((cross3 (sub3 p y) (sub3 q y)).1 : ℝ) / D ^ 2 ∧
    cross (ptD D p - ptD D y) (ptD D q - ptD D y) 1 =
      ((cross3 (sub3 p y) (sub3 q y)).2.1 : ℝ) / D ^ 2 ∧
    cross (ptD D p - ptD D y) (ptD D q - ptD D y) 2 =
      ((cross3 (sub3 p y) (sub3 q y)).2.2 : ℝ) / D ^ 2 := by
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  obtain ⟨a0, a1, a2⟩ := ptD_sub_apply D p y
  obtain ⟨b0, b1, b2⟩ := ptD_sub_apply D q y
  obtain ⟨c0, c1, c2⟩ := cross_coords' (ptD D p - ptD D y) (ptD D q - ptD D y)
  rw [c0, c1, c2, a0, a1, a2, b0, b1, b2]
  unfold cross3
  refine ⟨?_, ?_, ?_⟩ <;> push_cast <;> field_simp

/-- Lagrange's identity in integers: `|a|²|b|² - (a·b)² = |a × b|²`. -/
theorem lagrange3 (a b : ℤ × ℤ × ℤ) :
    dot3 a a * dot3 b b - dot3 a b ^ 2 = dot3 (cross3 a b) (cross3 a b) := by
  unfold dot3 cross3; ring

/-! ## The segment factor -/

/-- The direct-form bracket of `segFac' α β c` for `c ≥ 0`. -/
theorem fac_bounds_direct {α β c al ah bl bh : ℝ} (hal : 0 < al) (hbl : 0 < bl)
    (ha1 : al ≤ α) (ha2 : α ≤ ah) (hb1 : bl ≤ β) (hb2 : β ≤ bh) (hc : 0 ≤ c) :
    (al + bl) / (ah * bh * (ah * bh + c)) ≤ segFac' α β c ∧
      segFac' α β c ≤ (ah + bh) / (al * bl * (al * bl + c)) := by
  unfold segFac'
  have hα : 0 < α := hal.trans_le ha1
  have hβ : 0 < β := hbl.trans_le hb1
  have h1 : al * bl ≤ α * β := mul_le_mul ha1 hb1 hbl.le hα.le
  have h2 : α * β ≤ ah * bh := mul_le_mul ha2 hb2 hβ.le (hα.le.trans ha2)
  have hp : 0 < al * bl := mul_pos hal hbl
  constructor
  · apply div_le_div₀ (by positivity) (by linarith) (by positivity)
    exact mul_le_mul h2 (by linarith) (by positivity) (by nlinarith)
  · apply div_le_div₀ (by nlinarith) (by linarith) (by positivity)
    exact mul_le_mul h1 (by linarith) (by positivity) (by positivity)

/-- The stable form of the segment factor: if `α²β² - c² = cc > 0` and `c < 0` then
`segFac' α β c = (α+β)(αβ - c)/(αβ cc)`. -/
theorem segFac'_stable {α β c cc : ℝ} (hα : 0 < α) (hβ : 0 < β) (hc : c < 0)
    (hcc : α ^ 2 * β ^ 2 - c ^ 2 = cc) (hcc0 : 0 < cc) :
    segFac' α β c = (α + β) * (α * β - c) / (α * β * cc) := by
  unfold segFac'
  have hab : 0 < α * β := mul_pos hα hβ
  have hpos : 0 < α * β + c := by
    by_contra h
    push Not at h
    have : (α * β + c) * (α * β - c) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h (by linarith)
    nlinarith
  rw [div_eq_div_iff (by positivity) (by positivity)]
  rw [← hcc]; ring

/-- The stable-form bracket of `segFac' α β c` for `c < 0`. -/
theorem fac_bounds_stable {α β c cc al ah bl bh : ℝ} (hal : 0 < al) (hbl : 0 < bl)
    (ha1 : al ≤ α) (ha2 : α ≤ ah) (hb1 : bl ≤ β) (hb2 : β ≤ bh) (hc : c < 0)
    (hcc : α ^ 2 * β ^ 2 - c ^ 2 = cc) (hcc0 : 0 < cc) :
    (al + bl) * (al * bl - c) / (ah * bh * cc) ≤ segFac' α β c ∧
      segFac' α β c ≤ (ah + bh) * (ah * bh - c) / (al * bl * cc) := by
  have hα : 0 < α := hal.trans_le ha1
  have hβ : 0 < β := hbl.trans_le hb1
  rw [segFac'_stable hα hβ hc hcc hcc0]
  have h1 : al * bl ≤ α * β := mul_le_mul ha1 hb1 hbl.le hα.le
  have h2 : α * β ≤ ah * bh := mul_le_mul ha2 hb2 hβ.le (hα.le.trans ha2)
  have hp : 0 < al * bl := mul_pos hal hbl
  constructor
  · apply div_le_div₀ (by nlinarith) (mul_le_mul (by linarith) (by linarith) (by linarith)
      (by linarith)) (by positivity) (mul_le_mul_of_nonneg_right h2 hcc0.le)
  · apply div_le_div₀ (by nlinarith) (mul_le_mul (by linarith) (by linarith) (by linarith)
      (by nlinarith)) (by positivity) (mul_le_mul_of_nonneg_right h1 hcc0.le)

/-! ## The segment approximant -/

/-- The initial guess for `√n` (`n` at scale `D²`): `8D` below `64D²`, else `2²²D`. -/
def guess (D n : ℕ) : ℕ := if n < 64 * D * D then 8 * D else 4194304 * D

/-- One component `(K x F_lo)/(2³² D³)` of the segment field, with the error of the bracket
`[F_lo, F_hi]` (of `D² f`) and the rounding. -/
def compAP (D : ℕ) (K x : ℤ) (FL FH : ℕ) : ℤ × ℕ :=
  (Int.fdiv (K * x * FL) (4294967296 * D * D * D),
    cdivN ((K * x).natAbs * (FH - FL)) (4294967296 * D * D * D) + 1)

/-- The bracket `[F_lo, F_hi]` of `D² f` from the integer data, or `none`. -/
def facBr (D Al Ah Bl Bh : ℕ) (C : ℤ) (CC : ℕ) : Option (ℕ × ℕ) :=
  if Al = 0 ∨ Bl = 0 then none
  else if 0 ≤ C then
    some (((Al + Bl) * D ^ 5 : ℕ) / (Ah * Bh * (Ah * Bh + C).toNat),
      cdivN ((Ah + Bh) * D ^ 5) (Al * Bl * (Al * Bl + C).toNat))
  else if CC = 0 then none
  else some (((Al + Bl) * (Al * Bl + (-C).toNat) * D ^ 5) / (Ah * Bh * CC),
      cdivN ((Ah + Bh) * (Ah * Bh + (-C).toNat) * D ^ 5) (Al * Bl * CC))

/-- **The segment approximant**: the three components of `segClosed (K/2³²) p q ỹ` at scale `D`
(all points integer triples at scale `D`), or `none`. -/
def segAP (D : ℕ) (K : ℤ) (p q y : ℤ × ℤ × ℤ) : Option ((ℤ × ℕ) × (ℤ × ℕ) × (ℤ × ℕ)) :=
  let a := sub3 p y
  let b := sub3 q y
  let na := (dot3 a a).toNat
  let nb := (dot3 b b).toNat
  let X := cross3 a b
  let A := sqrtBr (guess D na) na
  let B := sqrtBr (guess D nb) nb
  match facBr D A.1 A.2 B.1 B.2 (dot3 a b) (dot3 X X).toNat with
  | none => none
  | some F => some (compAP D K X.1 F.1 F.2, compAP D K X.2.1 F.1 F.2, compAP D K X.2.2 F.1 F.2)

theorem toNat_cast_real {z : ℤ} (h : 0 ≤ z) : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
  have : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg h
  exact_mod_cast this

/-- Soundness of `facBr`: the bracket contains `D · segFac' α β c`. -/
theorem facBr_sound {D Al Ah Bl Bh : ℕ} (hD : 0 < D) {C : ℤ} {CC : ℕ} {FL FH : ℕ}
    (h : facBr D Al Ah Bl Bh C CC = some (FL, FH)) {α β : ℝ}
    (ha1 : (Al : ℝ) / D ≤ α) (ha2 : α ≤ (Ah : ℝ) / D) (hb1 : (Bl : ℝ) / D ≤ β)
    (hb2 : β ≤ (Bh : ℝ) / D) (hcc : α ^ 2 * β ^ 2 - ((C : ℝ) / D ^ 2) ^ 2 = (CC : ℝ) / D ^ 4) :
    (FL : ℝ) ≤ (D : ℝ) ^ 2 * segFac' α β ((C : ℝ) / D ^ 2) ∧
      (D : ℝ) ^ 2 * segFac' α β ((C : ℝ) / D ^ 2) ≤ (FH : ℝ) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  unfold facBr at h
  split_ifs at h with h0 hC hCC
  · -- direct form
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    push Not at h0
    have hAl : (0 : ℝ) < Al := by exact_mod_cast Nat.pos_of_ne_zero h0.1
    have hBl : (0 : ℝ) < Bl := by exact_mod_cast Nat.pos_of_ne_zero h0.2
    have hC' : (0 : ℝ) ≤ C := by exact_mod_cast hC
    have hAh : (Al : ℝ) ≤ Ah := by
      have := ha1.trans ha2; rwa [div_le_div_iff_of_pos_right hD'] at this
    have hBh : (Bl : ℝ) ≤ Bh := by
      have := hb1.trans hb2; rwa [div_le_div_iff_of_pos_right hD'] at this
    obtain ⟨l, u⟩ := fac_bounds_direct (div_pos hAl hD') (div_pos hBl hD') ha1 ha2 hb1 hb2
      (by positivity : (0 : ℝ) ≤ (C : ℝ) / D ^ 2)
    have e1 : (0 : ℤ) ≤ Ah * Bh + C := by positivity
    have e2 : (0 : ℤ) ≤ Al * Bl + C := by positivity
    constructor
    · refine le_trans ?_ (mul_le_mul_of_nonneg_left l (by positivity))
      have hden : (0 : ℝ) < Ah * Bh * (Ah * Bh + C) := by
        have : (0 : ℝ) < Ah := hAl.trans_le hAh
        have : (0 : ℝ) < Bh := hBl.trans_le hBh
        positivity
      have key : (((Al + Bl) * D ^ 5 / (Ah * Bh * (Ah * Bh + C).toNat) : ℕ) : ℝ) ≤
          ((Al + Bl) * D ^ 5 : ℕ) / ((Ah * Bh * (Ah * Bh + C).toNat : ℕ) : ℝ) := Nat.cast_div_le
      refine key.trans (le_of_eq ?_)
      push_cast [toNat_cast_real e1]
      field_simp
    · refine le_trans (mul_le_mul_of_nonneg_left u (by positivity)) ?_
      have hden : (0 : ℝ) < Al * Bl * (Al * Bl + C) := by positivity
      have hpos : 0 < Al * Bl * (Al * Bl + C).toNat := by
        have : (0 : ℝ) < ((Al * Bl * (Al * Bl + C).toNat : ℕ) : ℝ) := by
          push_cast [toNat_cast_real e2]; exact hden
        exact_mod_cast this
      have key := cdivN_ge ((Ah + Bh) * D ^ 5) hpos
      refine le_trans (le_of_eq ?_) key
      push_cast [toNat_cast_real e2]
      field_simp
  · -- stable form
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    push Not at h0 hC
    have hAl : (0 : ℝ) < Al := by exact_mod_cast Nat.pos_of_ne_zero h0.1
    have hBl : (0 : ℝ) < Bl := by exact_mod_cast Nat.pos_of_ne_zero h0.2
    have hC' : (C : ℝ) < 0 := by exact_mod_cast hC
    have hCC' : (0 : ℝ) < CC := by exact_mod_cast Nat.pos_of_ne_zero hCC
    have hAh : (Al : ℝ) ≤ Ah := by
      have := ha1.trans ha2; rwa [div_le_div_iff_of_pos_right hD'] at this
    have hBh : (Bl : ℝ) ≤ Bh := by
      have := hb1.trans hb2; rwa [div_le_div_iff_of_pos_right hD'] at this
    obtain ⟨l, u⟩ := fac_bounds_stable (div_pos hAl hD') (div_pos hBl hD') ha1 ha2 hb1 hb2
      (by have : (0 : ℝ) < (D : ℝ) ^ 2 := by positivity
          exact div_neg_of_neg_of_pos hC' this) hcc (by positivity)
    have hnC : ((-C).toNat : ℝ) = -(C : ℝ) := by
      rw [toNat_cast_real (by omega)]; push_cast; ring
    have hAh0 : (0 : ℝ) < Ah := hAl.trans_le hAh
    have hBh0 : (0 : ℝ) < Bh := hBl.trans_le hBh
    constructor
    · refine le_trans ?_ (mul_le_mul_of_nonneg_left l (by positivity))
      have key : (((Al + Bl) * (Al * Bl + (-C).toNat) * D ^ 5 / (Ah * Bh * CC) : ℕ) : ℝ) ≤
          ((Al + Bl) * (Al * Bl + (-C).toNat) * D ^ 5 : ℕ) / ((Ah * Bh * CC : ℕ) : ℝ) :=
        Nat.cast_div_le
      refine key.trans (le_of_eq ?_)
      push_cast [hnC]
      field_simp
      ring
    · refine le_trans (mul_le_mul_of_nonneg_left u (by positivity)) ?_
      have hpos : 0 < Al * Bl * CC := by
        have : (0 : ℝ) < ((Al * Bl * CC : ℕ) : ℝ) := by push_cast; positivity
        exact_mod_cast this
      have key := cdivN_ge ((Ah + Bh) * (Ah * Bh + (-C).toNat) * D ^ 5) hpos
      refine le_trans (le_of_eq ?_) key
      push_cast [hnC]
      field_simp
      ring

/-- Soundness of `compAP`: from `F_lo ≤ D f ≤ F_hi`, the component `κ f x/D²`
(`κ = K/2³²`) is approximated at scale `D`. -/
theorem compAP_sound {D : ℕ} (hD : 0 < D) (K x : ℤ) {FL FH : ℕ} {f : ℝ}
    (h1 : (FL : ℝ) ≤ (D : ℝ) ^ 2 * f) (h2 : (D : ℝ) ^ 2 * f ≤ FH) :
    Approx D ((K : ℝ) / 4294967296 * f * ((x : ℝ) / D ^ 2)) (compAP D K x FL FH) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hFLH : FL ≤ FH := by exact_mod_cast h1.trans h2
  set M : ℕ := 4294967296 * D * D * D
  have hM : 0 < M := by positivity
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  unfold Approx compAP
  simp only
  -- exact part: |κ f x/D² - K x FL/(M D)| ≤ |K x| (FH - FL)/(M D)
  have hexact : |(K : ℝ) / 4294967296 * f * ((x : ℝ) / D ^ 2) - ((K * x * FL : ℤ) : ℝ) / M / D| ≤
      (((K * x).natAbs * (FH - FL) : ℕ) : ℝ) / M / D := by
    have e : (K : ℝ) / 4294967296 * f * ((x : ℝ) / D ^ 2) - ((K * x * FL : ℤ) : ℝ) / M / D =
        ((K * x : ℤ) : ℝ) * ((D : ℝ) ^ 2 * f - FL) / M / D := by
      simp only [M]; push_cast; field_simp
    rw [e, abs_div, abs_div, abs_mul, Nat.abs_cast, Nat.abs_cast]
    gcongr
    rw [Nat.cast_mul, natAbs_cast, Nat.cast_sub hFLH]
    gcongr
    rw [abs_le]; constructor <;> linarith
  have hr := fdiv_approx (K * x * FL) hM
  have hc := cdivN_ge ((K * x).natAbs * (FH - FL)) hM
  calc |(K : ℝ) / 4294967296 * f * ((x : ℝ) / D ^ 2) - ((Int.fdiv (K * x * FL) M : ℤ) : ℝ) / D|
      ≤ |(K : ℝ) / 4294967296 * f * ((x : ℝ) / D ^ 2) - ((K * x * FL : ℤ) : ℝ) / M / D| +
        |((K * x * FL : ℤ) : ℝ) / M / D - ((Int.fdiv (K * x * FL) M : ℤ) : ℝ) / D| := by
        have := abs_add_le
          ((K : ℝ) / 4294967296 * f * ((x : ℝ) / D ^ 2) - ((K * x * FL : ℤ) : ℝ) / M / D)
          (((K * x * FL : ℤ) : ℝ) / M / D - ((Int.fdiv (K * x * FL) M : ℤ) : ℝ) / D)
        simpa using this
    _ ≤ (((K * x).natAbs * (FH - FL) : ℕ) : ℝ) / M / D + 1 / D := by
        refine add_le_add hexact ?_
        have e : ((K * x * FL : ℤ) : ℝ) / M / D - ((Int.fdiv (K * x * FL) M : ℤ) : ℝ) / D =
            (((K * x * FL : ℤ) : ℝ) / M - ((Int.fdiv (K * x * FL) M : ℤ) : ℝ)) / D := by ring
        have e2 : ((K * x * FL : ℤ) : ℝ) / M / M - ((Int.fdiv (K * x * FL) M : ℤ) : ℝ) / M =
            (((K * x * FL : ℤ) : ℝ) / M - ((Int.fdiv (K * x * FL) M : ℤ) : ℝ)) / M := by ring
        rw [e2, abs_div, Nat.abs_cast, div_le_div_iff_of_pos_right hM'] at hr
        rw [e, abs_div, Nat.abs_cast]
        exact div_le_div_of_nonneg_right hr hD'.le
    _ ≤ (((cdivN ((K * x).natAbs * (FH - FL)) M + 1 : ℕ) : ℝ)) / D := by
        rw [Nat.cast_add, Nat.cast_one, add_div]
        exact add_le_add (div_le_div_of_nonneg_right hc hD'.le) le_rfl

/-- **Soundness of the segment approximant.** -/
theorem segAP_sound {D : ℕ} (hD : 0 < D) {K : ℤ} {p q y : ℤ × ℤ × ℤ}
    {r : (ℤ × ℕ) × (ℤ × ℕ) × (ℤ × ℕ)} (h : segAP D K p q y = some r) :
    Approx D (segClosed ((K : ℝ) / 4294967296) (ptD D p) (ptD D q) (ptD D y) 0) r.1 ∧
    Approx D (segClosed ((K : ℝ) / 4294967296) (ptD D p) (ptD D q) (ptD D y) 1) r.2.1 ∧
    Approx D (segClosed ((K : ℝ) / 4294967296) (ptD D p) (ptD D q) (ptD D y) 2) r.2.2 := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  unfold segAP at h
  simp only at h
  split at h
  · exact absurd h (by simp)
  · rename_i F hF
    simp only [Option.some.injEq] at h
    subst h
    have hα := norm_ptD_sub D hD p y
    have hβ := norm_ptD_sub D hD q y
    set a := sub3 p y
    set b := sub3 q y
    set X := cross3 a b
    -- the real quantities
    set α := ‖ptD D p - ptD D y‖
    set β := ‖ptD D q - ptD D y‖
    obtain ⟨la, ua⟩ := sqrtBr_sound (guess D (dot3 a a).toNat) (dot3 a a).toNat
    obtain ⟨lb, ub⟩ := sqrtBr_sound (guess D (dot3 b b).toNat) (dot3 b b).toNat
    have ha1 : ((sqrtBr (guess D (dot3 a a).toNat) (dot3 a a).toNat).1 : ℝ) / D ≤ α := by
      rw [hα]; exact div_le_div_of_nonneg_right la hD'.le
    have ha2 : α ≤ ((sqrtBr (guess D (dot3 a a).toNat) (dot3 a a).toNat).2 : ℝ) / D := by
      rw [hα]; exact div_le_div_of_nonneg_right ua hD'.le
    have hb1 : ((sqrtBr (guess D (dot3 b b).toNat) (dot3 b b).toNat).1 : ℝ) / D ≤ β := by
      rw [hβ]; exact div_le_div_of_nonneg_right lb hD'.le
    have hb2 : β ≤ ((sqrtBr (guess D (dot3 b b).toNat) (dot3 b b).toNat).2 : ℝ) / D := by
      rw [hβ]; exact div_le_div_of_nonneg_right ub hD'.le
    have hnn : ∀ v : ℤ × ℤ × ℤ, 0 ≤ dot3 v v := dot3_self_nonneg
    have hcc : α ^ 2 * β ^ 2 - ((dot3 a b : ℝ) / D ^ 2) ^ 2 = ((dot3 X X).toNat : ℝ) / D ^ 4 := by
      rw [hα, hβ, div_pow, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
        toNat_cast_real (hnn a), toNat_cast_real (hnn b), toNat_cast_real (hnn X)]
      have := lagrange3 a b
      have e : ((dot3 a a : ℤ) : ℝ) * dot3 b b - (dot3 a b : ℝ) ^ 2 = dot3 X X := by
        exact_mod_cast this
      field_simp
      linear_combination e
    obtain ⟨hF1, hF2⟩ := facBr_sound hD hF ha1 ha2 hb1 hb2 hcc
    have hseg : ∀ i : Fin 3, segClosed ((K : ℝ) / 4294967296) (ptD D p) (ptD D q) (ptD D y) i =
        (K : ℝ) / 4294967296 * segFac' α β ((dot3 a b : ℝ) / D ^ 2) *
          cross (ptD D p - ptD D y) (ptD D q - ptD D y) i := by
      intro i
      unfold segClosed
      rw [PiLp.smul_apply, smul_eq_mul, inner_ptD_sub D hD p q y]
    obtain ⟨c0, c1, c2⟩ := cross_ptD_sub D hD p q y
    refine ⟨?_, ?_, ?_⟩
    · rw [hseg 0, c0]; exact compAP_sound hD K _ hF1 hF2
    · rw [hseg 1, c1]; exact compAP_sound hD K _ hF1 hF2
    · rw [hseg 2, c2]; exact compAP_sound hD K _ hF1 hF2

/-! ## The coil field -/

/-- The TF rectangle as segment records at scale `D` (`κ = 2³¹/2³² = 1/2`). -/
def tfSegsD (D : ℕ) : List (ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)) :=
  let L : ℤ := 1000000 * D
  [(2147483648, (0, 0, -L), (0, 0, L)), (2147483648, (0, 0, L), (L, 0, L)),
   (2147483648, (L, 0, L), (L, 0, -L)), (2147483648, (L, 0, -L), (0, 0, -L))]

/-- All 196 segment records at scale `D = 2³² D₀`: the TF rectangle and `allSegs filsC` with
vertices scaled by `D₀`. -/
def allSegsD (D₀ : ℕ) : List (ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)) :=
  tfSegsD (4294967296 * D₀) ++
    (allSegs filsC).map fun z => (z.1, scl3 D₀ z.2.1, scl3 D₀ z.2.2)

/-- Componentwise sum of triples of approximants. -/
def ap3Add (r s : (ℤ × ℕ) × (ℤ × ℕ) × (ℤ × ℕ)) : (ℤ × ℕ) × (ℤ × ℕ) × (ℤ × ℕ) :=
  (apAdd r.1 s.1, apAdd r.2.1 s.2.1, apAdd r.2.2 s.2.2)

/-- Sum of the segment approximants over a list of records (`none` if one fails). -/
def sumSegAP (D : ℕ) (y : ℤ × ℤ × ℤ) :
    List (ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ)) → Option ((ℤ × ℕ) × (ℤ × ℕ) × (ℤ × ℕ))
  | [] => some ((0, 0), (0, 0), (0, 0))
  | z :: zs =>
    match segAP D z.1 z.2.1 z.2.2 y with
    | none => none
    | some r => match sumSegAP D y zs with
      | none => none
      | some s => some (ap3Add r s)

/-- **The coil-field approximant** at the dyadic point `Y/D`, `D = 2³² D₀`. -/
def fieldAP (D₀ : ℕ) (Y : ℤ × ℤ × ℤ) : Option ((ℤ × ℕ) × (ℤ × ℕ) × (ℤ × ℕ)) :=
  sumSegAP (4294967296 * D₀) Y (allSegsD D₀)

/-- The closed-form field of a list of records at scale `D`. -/
def segSumD (D : ℕ) (l : List (ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ))) (y : Space) : Space :=
  (l.map fun z => segClosed ((z.1 : ℝ) / 4294967296) (ptD D z.2.1) (ptD D z.2.2) y).sum

theorem sumSegAP_sound {D : ℕ} (hD : 0 < D) (y : ℤ × ℤ × ℤ) :
    ∀ (l : List (ℤ × (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ))) {r}, sumSegAP D y l = some r →
      Approx D (segSumD D l (ptD D y) 0) r.1 ∧ Approx D (segSumD D l (ptD D y) 1) r.2.1 ∧
        Approx D (segSumD D l (ptD D y) 2) r.2.2
  | [], r, h => by
    simp only [sumSegAP, Option.some.injEq] at h
    subst h
    simp [segSumD, Approx]
  | z :: zs, r, h => by
    simp only [sumSegAP] at h
    split at h
    · exact absurd h (by simp)
    · rename_i r1 h1
      split at h
      · exact absurd h (by simp)
      · rename_i s hs
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨a0, a1, a2⟩ := segAP_sound hD h1
        obtain ⟨b0, b1, b2⟩ := sumSegAP_sound hD y zs hs
        simp only [segSumD, List.map_cons, List.sum_cons, PiLp.add_apply] at b0 b1 b2 ⊢
        exact ⟨a0.add b0, a1.add b1, a2.add b2⟩

/-- Coil vertices: `ptD (2³² D₀) (D₀ p) = ptR p`. -/
theorem ptD_scale {D₀ : ℕ} (hD₀ : 0 < D₀) (p : ℤ × ℤ × ℤ) :
    ptD (4294967296 * D₀) (scl3 D₀ p) = ptR p := by
  have h : (D₀ : ℝ) ≠ 0 := by exact_mod_cast hD₀.ne'
  ext i
  fin_cases i <;> simp [ptD, ptR, scl3, S32] <;> field_simp

theorem ptD_TF {D : ℕ} (hD : 0 < D) :
    ptD D (0, 0, -(1000000 * D)) = P0 ∧ ptD D (0, 0, 1000000 * D) = P1 ∧
      ptD D (1000000 * D, 0, 1000000 * D) = P2 ∧ ptD D (1000000 * D, 0, -(1000000 * D)) = P3 := by
  have h : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;> simp [ptD, P0, P1, P2, P3, Λ] <;>
    field_simp <;> norm_num

/-- The closed-form sum over `allSegsD` is the real coil field off the coils. -/
theorem segSumD_allSegsD {D₀ : ℕ} (hD₀ : 0 < D₀) {y : Space} (hy : ¬ coilPt filsC y) :
    segSumD (4294967296 * D₀) (allSegsD D₀) y = tfField y + polyCoilFieldC y := by
  have hD : 0 < 4294967296 * D₀ := by positivity
  obtain ⟨e0, e1, e2, e3⟩ := ptD_TF hD
  rw [polyCoilFieldC_eq hy, Bseg]
  unfold segSumD allSegsD tfSegsD tfField
  simp only [List.map_append, List.sum_append, List.map_map]
  congr 1
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      segField_eq_half, e0, e1, e2, e3]
    norm_num [add_assoc]
  · congr 1
    apply List.map_congr_left
    intro z _
    simp only [Function.comp_apply, ptD_scale hD₀, S32]

/-- **Soundness of the coil-field approximant**: at a dyadic point `ỹ = Y/D` of the real tube
`realTube w` (`w < 7/20`), `fieldAP D₀ Y = some r` approximates the three components of
`tfField ỹ + polyCoilFieldC ỹ`. -/
theorem fieldAP_sound {D₀ : ℕ} (hD₀ : 0 < D₀) {Y : ℤ × ℤ × ℤ} {w : ℝ} (hw : w < 7 / 20)
    (hY : ptD (4294967296 * D₀) Y ∈ realTube w) {r} (h : fieldAP D₀ Y = some r) :
    Approx (4294967296 * D₀) ((tfField (ptD (4294967296 * D₀) Y) +
        polyCoilFieldC (ptD (4294967296 * D₀) Y)) 0) r.1 ∧
    Approx (4294967296 * D₀) ((tfField (ptD (4294967296 * D₀) Y) +
        polyCoilFieldC (ptD (4294967296 * D₀) Y)) 1) r.2.1 ∧
    Approx (4294967296 * D₀) ((tfField (ptD (4294967296 * D₀) Y) +
        polyCoilFieldC (ptD (4294967296 * D₀) Y)) 2) r.2.2 := by
  rw [← segSumD_allSegsD hD₀ (not_coilPt_of_realTube hw hY)]
  exact sumSegAP_sound (by positivity) Y _ h

/-! ## Sanity -/

/-- Accepted fixture: the field at `(1, 0, 0)` (scale `2³²`) passes all checks. -/
theorem fieldAP_fixture : (fieldAP 1 (4294967296, 0, 0)).isSome = true := by kernel_fact

/-- Rejected fixture: a segment through the evaluation point is rejected. -/
theorem segAP_degenerate : segAP 4 1 (0, 0, 0) (4, 0, 0) (0, 0, 0) = none := by kernel_fact

end PlasmaLean.Design.CoilKam
