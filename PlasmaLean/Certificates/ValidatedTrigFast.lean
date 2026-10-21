/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.ValidatedTrig
public import Mathlib.Data.List.GetD

/-!
# Fast validated `arctan`, `arcsin`, `cosh`, `sinh` on fixed-point enclosures

Cheaper variants of the enclosures in `PlasmaLean.Certificates.ValidatedTrig`, intended for
certificates that evaluate them `10⁴`–`10⁵` times under `decide +kernel`. Results are `FIv`
enclosures (scale `2³²`) and every soundness lemma is unconditional (an invalid enclosure
contains every real), but the computation itself runs on **natural numbers**: the kernel
evaluates `Nat` literal arithmetic natively (GMP), whereas each `Int` operation costs several
reduction steps (measured: `Int` comparisons and corner-product `FIv.mul` are 5–50× slower
than the corresponding `Nat` operations). Signs are handled once, by matching on the `Int`
constructors of the endpoints and using oddness/evenness.

**`atanFast` (no square roots).** `arctan` is increasing, so it is enclosed endpoint-wise
(`atanLoZ`, `atanHiZ`). At a point `x = w/2³² ≥ 0`:
* if `x > 4`, `arctan x = π/2 - arctan (1/x)` (`atanLoN`, `atanHiN`);
* otherwise, with `j = ⌊8x⌋ ≤ 32`, `c = j/8`, `arctan x = arctan c + arctan r` where
  `r = (x - c)/(1 + x c) = (8w - j 2³²)/(8 · 2³² + w j) ∈ [0, 1/8)` (`arctan_eq_add_red`,
  from `Real.arctan_add`); `r` is obtained by ONE exact integer division;
* `arctan c` comes from the literal table `atanTabN` (33 entries of width one unit of
  `2⁻³²`). Its soundness (`tab_spec`) is proved once: rational bounds
  `atanTabLoQ j ≤ arctan (j/8) ≤ atanTabHiQ j` (`atanTabQ_bounds`: Taylor sums `S₂₀`, `S₂₁`,
  after the exact rational reduction `arctan u = π/4 + arctan ((u-1)/(u+1))` for `j ≥ 4`,
  with `Real.pi_gt_d20`, `Real.pi_lt_d20`), and one `decide +kernel` check `atanTabN_check`;
* `S₆(r) ≤ arctan r ≤ S₇(r)` (`atanSeries_bound`), evaluated by the alternating nested
  Horner chain `altH` with one-sided rounding (`altH_spec`; all partial sums stay positive
  because `r² ≤ 1`). The gap `r¹³/13 < 2⁻⁴⁰` is negligible.

**`asinFast`.** At each endpoint `t = m/2³²` (`m < 2³²`), `s2 = 2⁶⁴ - m²`, an integer square
root `q` (Newton, CHECKED: `q² ≤ s2 < (q+1)²`), then `arcsin t = arctan (m/√s2)` is bounded
by `atanLoN ⌊m 2³²/(q+1)⌋` and `atanHiN (⌊m 2³²/q⌋ + 1)` (`asinPtN_spec`). Invalid unless
both endpoints lie strictly inside `(-1, 1)`.

**`coshSmall`, `sinhSmall`.** Even and odd parts of the degree-8 exponential Taylor
polynomial in nested form `1 + v/d₀ (1 + v/d₁ (…))` with one-sided rounding (`hUp_spec`),
widened by one unit for the `Real.exp_bound` remainder (`|x| ≤ 1/4`, `n = 9`:
`(1/4)⁹ · 10/(9!·9) < 2⁻³²`, `exp_sub_expPoly9`). Invalid unless the enclosure lies in
`[-1/4, 1/4]`. `sinh` is increasing; `cosh` is even and increasing in `|x|`.

**Accuracy and cost** (thin inputs, `decide +kernel`): `atanFast` width `≤ 6 · 2⁻³²`
(`≈ 1.4e-9`, typically 3 units), about `0.8 ms` per call; `asinFast` width `≤ 6 · 2⁻³²` for
`|x| ≤ 0.95`, about `1 ms` per call; `coshSmall`, `sinhSmall` width `≤ 4 · 2⁻³²`, about
`0.3 ms` per call.

Sanity fixtures: `fixture_atanFast_one` (contains `π/4`), `fixture_atanFast_large`,
`fixture_asinFast_half` (contains `π/6`), `fixture_asinFast_edge`, `fixture_coshSmall`,
`fixture_sinhSmall`, the degenerate `fixture_coshSmall_straddle`; rejected fixtures
`fixture_asinFast_rejected`, `fixture_coshSmall_rejected`.
-/

public section

namespace PlasmaLean.Certificates.ValidatedQuadrature

open Real

/-! ## Rational bounds for the table `arctan (j/8)` -/

/-- The Taylor sum `S_N` of `arctan` on rationals (computable). -/
@[expose] def atanSeriesQ (N : ℕ) (a : ℚ) : ℚ :=
  ∑ k ∈ Finset.range N, (-1) ^ k * a ^ (2 * k + 1) / (2 * k + 1)

/-- The rational Taylor sum casts to the real one. -/
theorem atanSeriesQ_cast (N : ℕ) (a : ℚ) : ((atanSeriesQ N a : ℚ) : ℝ) = atanSeries N a := by
  unfold atanSeriesQ atanSeries
  push_cast
  rfl

/-- Rational lower bound for `π` (20 digits). -/
@[expose] def piLoQ : ℚ := 314159265358979323846 / 10 ^ 20

/-- Rational upper bound for `π` (20 digits). -/
@[expose] def piHiQ : ℚ := 314159265358979323847 / 10 ^ 20

/-- The reduced argument `|u - 1|/(u + 1)` for `u = j/8`. -/
@[expose] def atanTabArg (j : ℕ) : ℚ :=
  if 8 ≤ j then ((j : ℚ) - 8) / (j + 8) else (8 - (j : ℚ)) / (j + 8)

/-- Rational lower bound for `arctan (j/8)`. -/
@[expose] def atanTabLoQ (j : ℕ) : ℚ :=
  if j ≤ 3 then atanSeriesQ 20 ((j : ℚ) / 8) else
    piLoQ / 4 + if 8 ≤ j then atanSeriesQ 20 (atanTabArg j) else -atanSeriesQ 21 (atanTabArg j)

/-- Rational upper bound for `arctan (j/8)`. -/
@[expose] def atanTabHiQ (j : ℕ) : ℚ :=
  if j ≤ 3 then atanSeriesQ 21 ((j : ℚ) / 8) else
    piHiQ / 4 + if 8 ≤ j then atanSeriesQ 21 (atanTabArg j) else -atanSeriesQ 20 (atanTabArg j)

/-- `S₂₀(u) ≤ arctan u ≤ S₂₁(u)` for `u ≥ 0`. -/
theorem atan_bounds_20 {u : ℝ} (hu : 0 ≤ u) :
    atanSeries 20 u ≤ arctan u ∧ arctan u ≤ atanSeries 21 u := by
  have l := atanSeries_bound 20 hu
  have r := atanSeries_bound 21 hu
  norm_num at l r
  constructor <;> linarith

/-- `arctan u = π/4 + arctan ((u - 1)/(u + 1))` for `u ≥ 0`. -/
theorem arctan_eq_quarter_add {u : ℝ} (hu : 0 ≤ u) :
    arctan u = π / 4 + arctan ((u - 1) / (u + 1)) := by
  have hp : 0 < u + 1 := by linarith
  have hw : 1 * ((u - 1) / (u + 1)) < 1 := by rw [one_mul, div_lt_one hp]; linarith
  rw [← arctan_one, arctan_add hw]
  congr 1
  field_simp
  ring

/-- **Rational table bounds.** `atanTabLoQ j ≤ arctan (j/8) ≤ atanTabHiQ j` for every `j`. -/
theorem atanTabQ_bounds (j : ℕ) :
    ((atanTabLoQ j : ℚ) : ℝ) ≤ arctan ((j : ℝ) / 8) ∧
      arctan ((j : ℝ) / 8) ≤ ((atanTabHiQ j : ℚ) : ℝ) := by
  have hpl : ((piLoQ : ℚ) : ℝ) ≤ π := by
    have := Real.pi_gt_d20; simp only [piLoQ]; push_cast; linarith
  have hph : π ≤ ((piHiQ : ℚ) : ℝ) := by
    have := Real.pi_lt_d20; simp only [piHiQ]; push_cast; linarith
  have hu : (0 : ℝ) ≤ j / 8 := by positivity
  have hj0 : (0 : ℝ) ≤ j := by positivity
  unfold atanTabLoQ atanTabHiQ
  split_ifs with h1 h2
  · obtain ⟨l, r⟩ := atan_bounds_20 hu
    rw [atanSeriesQ_cast, atanSeriesQ_cast]
    push_cast
    exact ⟨l, r⟩
  · have ha : ((atanTabArg j : ℚ) : ℝ) = ((j : ℝ) / 8 - 1) / ((j : ℝ) / 8 + 1) := by
      simp only [atanTabArg, h2, ↓reduceIte]
      push_cast
      field_simp
    have hj8 : (8 : ℝ) ≤ j := by exact_mod_cast h2
    have ha0 : (0 : ℝ) ≤ ((atanTabArg j : ℚ) : ℝ) := by
      rw [ha]; apply div_nonneg <;> linarith
    obtain ⟨l, r⟩ := atan_bounds_20 ha0
    rw [arctan_eq_quarter_add hu, ← ha]
    push_cast
    rw [atanSeriesQ_cast, atanSeriesQ_cast]
    constructor <;> linarith
  · have ha : ((atanTabArg j : ℚ) : ℝ) = -(((j : ℝ) / 8 - 1) / ((j : ℝ) / 8 + 1)) := by
      simp only [atanTabArg, h2, ↓reduceIte]
      push_cast
      field_simp
      ring
    have hj8 : (j : ℝ) < 8 := by exact_mod_cast not_le.mp h2
    have ha0 : (0 : ℝ) ≤ ((atanTabArg j : ℚ) : ℝ) := by
      rw [ha, neg_nonneg]; apply div_nonpos_of_nonpos_of_nonneg <;> linarith
    obtain ⟨l, r⟩ := atan_bounds_20 ha0
    have e : ((j : ℝ) / 8 - 1) / ((j : ℝ) / 8 + 1) = -((atanTabArg j : ℚ) : ℝ) := by
      rw [ha, neg_neg]
    rw [arctan_eq_quarter_add hu, e, arctan_neg]
    push_cast
    rw [atanSeriesQ_cast, atanSeriesQ_cast]
    constructor <;> linarith


/-! ## Exponential remainder -/

/-- The degree-8 exponential Taylor polynomial `Σ_{m<9} x^m/m!`. -/
@[expose] noncomputable def expPoly9 (x : ℝ) : ℝ :=
  ∑ m ∈ Finset.range 9, x ^ m / m.factorial

/-- For `|x| ≤ 1/4` the remainder `|exp x - expPoly9 x|` is below one unit of `2⁻³²`. -/
theorem exp_sub_expPoly9 {x : ℝ} (hx : |x| ≤ 1 / 4) : |exp x - expPoly9 x| ≤ 1 / fxScale := by
  have h := Real.exp_bound (hx.trans (by norm_num)) (n := 9) (by norm_num)
  have hp : |x| ^ 9 ≤ (1 / 4) ^ 9 := pow_le_pow_left₀ (abs_nonneg x) hx 9
  have hc0 : (0 : ℝ) ≤ ((Nat.succ 9 : ℕ) : ℝ) / ((Nat.factorial 9 : ℕ) * (9 : ℕ)) := by
    positivity
  have hc : (1 / 4 : ℝ) ^ 9 * (((Nat.succ 9 : ℕ) : ℝ) / ((Nat.factorial 9 : ℕ) * (9 : ℕ))) ≤
      1 / fxScale := by
    rw [fxScale_real]; norm_num [Nat.factorial]
  unfold expPoly9
  exact h.trans ((mul_le_mul_of_nonneg_right hp hc0).trans hc)

/-- `arctan x = arctan c + arctan ((x - c)/(1 + x c))` for `x, c ≥ 0`. -/
theorem arctan_eq_add_red {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) :
    arctan x = arctan c + arctan ((x - c) * (1 + x * c)⁻¹) := by
  have hp : 0 < 1 + x * c := by positivity
  have h : c * ((x - c) * (1 + x * c)⁻¹) < 1 := by
    rw [← mul_assoc, ← div_eq_mul_inv, div_lt_one hp]; nlinarith
  rw [arctan_add h]
  congr 1
  have hden : 1 - c * ((x - c) * (1 + x * c)⁻¹) ≠ 0 := by linarith
  symm
  rw [div_eq_iff hden]
  field_simp
  ring

/-! ## Natural-number fixed-point helpers -/

/-- The scale `2³²` as a natural number (kernel arithmetic on `ℕ` literals is fastest). -/
@[expose] def sN : ℕ := 4294967296

/-- The natural scale agrees with `fxScale` as a real number. -/
theorem sN_real : ((sN : ℕ) : ℝ) = (fxScale : ℝ) := by rw [fxScale_real]; norm_num [sN]

/-- The natural scale is positive. -/
theorem sN_pos : (0 : ℝ) < (sN : ℝ) := by norm_num [sN]

/-- Floor division rounds down. -/
theorem nd_le (a d : ℕ) (hd : 0 < d) : ((a / d : ℕ) : ℝ) ≤ (a : ℝ) / d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [le_div_iff₀ hd']
  exact_mod_cast Nat.div_mul_le_self a d

/-- Floor division plus one rounds up (strictly). -/
theorem lt_nd (a d : ℕ) (hd : 0 < d) : (a : ℝ) / d < ((a / d : ℕ) : ℝ) + 1 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_lt_iff₀ hd']
  have h := Nat.lt_div_mul_add (a := a) hd
  have h' : (a : ℝ) < ((a / d : ℕ) : ℝ) * d + d := by exact_mod_cast h
  linarith

/-- Truncated subtraction is at least the real difference. -/
theorem natsub_ge (a b : ℕ) : (a : ℝ) - b ≤ ((a - b : ℕ) : ℝ) := by
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h]
    have : (a : ℝ) ≤ b := by exact_mod_cast h
    simp only [CharP.cast_eq_zero]
    linarith

/-- Truncated subtraction is a lower bound of a nonnegative real above the real difference. -/
theorem natsub_le {a b : ℕ} {y : ℝ} (h0 : 0 ≤ y) (h : (a : ℝ) - b ≤ y) :
    ((a - b : ℕ) : ℝ) ≤ y := by
  rcases le_total b a with hb | hb
  · rw [Nat.cast_sub hb]; exact h
  · rw [Nat.sub_eq_zero_of_le hb]; simpa using h0

/-- Bounds of a product of nonnegative reals from bounds of the factors, after division by the
scale: `⌊a b / 2³²⌋ ≤ 2³² x y` when `a ≤ 2³² x`, `b ≤ 2³² y`. -/
theorem mulDiv_le {a b : ℕ} {x y : ℝ} (ha : (a : ℝ) ≤ sN * x) (hb : (b : ℝ) ≤ sN * y) :
    ((a * b / sN : ℕ) : ℝ) ≤ sN * (x * y) := by
  have hS := sN_pos
  have h1 := nd_le (a * b) sN (by norm_num [sN])
  have h2 : (a : ℝ) * b ≤ (sN * x) * (sN * y) :=
    mul_le_mul ha hb (by positivity) (le_trans (by positivity) ha)
  push_cast at h1
  calc _ ≤ (a : ℝ) * b / sN := h1
    _ ≤ (sN * x) * (sN * y) / sN := div_le_div_of_nonneg_right h2 hS.le
    _ = _ := by field_simp

/-- Upper version of `mulDiv_le`: `2³² x y ≤ ⌊a b / 2³²⌋ + 1` when `2³² x ≤ a`, `2³² y ≤ b`,
`y ≥ 0`. -/
theorem le_mulDiv {a b : ℕ} {x y : ℝ} (hy : 0 ≤ y) (ha : sN * x ≤ (a : ℝ))
    (hb : sN * y ≤ (b : ℝ)) : sN * (x * y) ≤ ((a * b / sN : ℕ) : ℝ) + 1 := by
  have hS := sN_pos
  have h1 := lt_nd (a * b) sN (by norm_num [sN])
  have h2 : (sN * x) * (sN * y) ≤ (a : ℝ) * b :=
    mul_le_mul ha hb (by positivity) (by positivity)
  push_cast at h1
  calc sN * (x * y) = (sN * x) * (sN * y) / sN := by field_simp
    _ ≤ (a : ℝ) * b / sN := div_le_div_of_nonneg_right h2 hS.le
    _ ≤ _ := h1.le

/-! ## Alternating Horner chain for the `arctan` Taylor sums -/

/-- Lower/upper fixed-point bounds of the alternating nested sum
`B_k = 1/(2k+1) - v (1/(2k+3) - v (…))` with `n` terms, given `vl ≤ 2³² v ≤ vh`. -/
@[expose] def altH (vl vh : ℕ) : ℕ → ℕ → ℕ × ℕ
  | _, 0 => (0, 0)
  | k, n + 1 =>
    (sN / (2 * k + 1) - (vh * (altH vl vh (k + 1) n).2 / sN + 1),
      sN / (2 * k + 1) + 1 - vl * (altH vl vh (k + 1) n).1 / sN)

/-- The real alternating nested sum computed by `altH`. -/
@[expose] noncomputable def altR (v : ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | k, n + 1 => 1 / (2 * k + 1) - v * altR v (k + 1) n

/-- Soundness of `altH` for `0 ≤ v ≤ 1` (all partial sums stay in `[0, 1/(2k+1)]`). -/
theorem altH_spec {v : ℝ} {vl vh : ℕ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hl : (vl : ℝ) ≤ sN * v)
    (hh : sN * v ≤ (vh : ℝ)) (n : ℕ) : ∀ k : ℕ,
    0 ≤ altR v k n ∧ altR v k n ≤ 1 / (2 * k + 1) ∧
      ((altH vl vh k n).1 : ℝ) ≤ sN * altR v k n ∧ sN * altR v k n ≤ (altH vl vh k n).2 := by
  have hS := sN_pos
  induction n with
  | zero => intro k; simp only [altR, altH]; norm_num; positivity
  | succ n ih =>
    intro k
    obtain ⟨b0, b1, bl, bh⟩ := ih (k + 1)
    simp only [altR, altH]
    set B := altR v (k + 1) n
    push_cast at b1
    have hk : (0 : ℝ) < 2 * k + 1 := by positivity
    have hvB : v * B ≤ 1 / (2 * k + 1) := by
      calc v * B ≤ 1 * (1 / (2 * (k + 1) + 1)) := mul_le_mul hv1 b1 b0 zero_le_one
        _ ≤ 1 / (2 * k + 1) := by
          rw [one_mul]; apply one_div_le_one_div_of_le hk; linarith
    have hpos : 0 ≤ 1 / (2 * (k : ℝ) + 1) - v * B := by linarith
    have hd : 0 < 2 * k + 1 := by omega
    have c1 := nd_le sN (2 * k + 1) hd
    have c2 := lt_nd sN (2 * k + 1) hd
    push_cast at c1 c2
    have e : (sN : ℝ) * (1 / (2 * k + 1) - v * B) = sN / (2 * k + 1) - v * (sN * B) := by
      field_simp
    refine ⟨hpos, by nlinarith [mul_nonneg hv0 b0], ?_, ?_⟩
    · apply natsub_le (by positivity)
      have m := le_mulDiv b0 hh bh
      push_cast
      rw [e]
      nlinarith
    · refine le_trans ?_ (natsub_ge _ _)
      have m := mulDiv_le (x := v) (y := B) hl bl
      push_cast
      rw [e]
      nlinarith

/-- `r · B₀ = S_N(r)` with `v = r²`, `N = 6`. -/
theorem altR_six (r : ℝ) : r * altR (r ^ 2) 0 6 = atanSeries 6 r := by
  simp only [altR, atanSeries, Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  ring

/-- `r · B₀ = S_N(r)` with `v = r²`, `N = 7`. -/
theorem altR_seven (r : ℝ) : r * altR (r ^ 2) 0 7 = atanSeries 7 r := by
  simp only [altR, atanSeries, Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  ring

/-- Lower bound of `2³² arctan r` from `rl ≤ 2³² r < rl + 1` (`S_6(r) ≤ arctan r`). -/
@[expose] def polyLo (rl : ℕ) : ℕ :=
  rl * (altH (rl * rl / sN) ((rl + 1) * (rl + 1) / sN + 1) 0 6).1 / sN

/-- Upper bound of `2³² arctan r` from `rl ≤ 2³² r < rl + 1` (`arctan r ≤ S_7(r)`). -/
@[expose] def polyHi (rl : ℕ) : ℕ :=
  (rl + 1) * (altH (rl * rl / sN) ((rl + 1) * (rl + 1) / sN + 1) 0 7).2 / sN + 1

/-- Soundness of `polyLo`, `polyHi` for `0 ≤ r ≤ 1`. -/
theorem poly_spec {r : ℝ} {rl : ℕ} (h0 : 0 ≤ r) (h1 : r ≤ 1) (hl : (rl : ℝ) ≤ sN * r)
    (hh : sN * r < rl + 1) :
    (polyLo rl : ℝ) ≤ sN * arctan r ∧ sN * arctan r ≤ polyHi rl := by
  have hS := sN_pos
  have hv0 : 0 ≤ r ^ 2 := sq_nonneg r
  have hv1 : r ^ 2 ≤ 1 := by nlinarith
  have hrl0 : (0 : ℝ) ≤ rl := Nat.cast_nonneg rl
  have vl : ((rl * rl / sN : ℕ) : ℝ) ≤ sN * r ^ 2 := by
    have := mulDiv_le (x := r) (y := r) hl hl
    rw [show r * r = r ^ 2 by ring] at this; exact this
  have vh : sN * r ^ 2 ≤ (((rl + 1) * (rl + 1) / sN + 1 : ℕ) : ℝ) := by
    have := le_mulDiv (a := rl + 1) (b := rl + 1) h0 (by push_cast; linarith)
      (by push_cast; linarith)
    rw [show r * r = r ^ 2 by ring] at this; push_cast at this ⊢; exact this
  obtain ⟨-, -, l6, -⟩ := altH_spec hv0 hv1 vl vh 6 0
  obtain ⟨b7, -, -, h7⟩ := altH_spec hv0 hv1 vl vh 7 0
  have s6 := atanSeries_bound 6 h0
  have s7 := atanSeries_bound 7 h0
  norm_num at s6 s7
  rw [← altR_six] at s6
  rw [← altR_seven] at s7
  constructor
  · have m := mulDiv_le (x := r) (y := altR (r ^ 2) 0 6) hl l6
    unfold polyLo
    nlinarith
  · have m := le_mulDiv (a := rl + 1) (x := r) (y := altR (r ^ 2) 0 7) b7
      (by push_cast; linarith) h7
    unfold polyHi
    push_cast at m ⊢
    nlinarith

/-! ## The table of `arctan (j/8)` -/

/-- Fixed-point bounds `(⌊2³² arctan (j/8)⌋, ⌈2³² arctan (j/8)⌉)`, `j = 0, …, 32` (generated
from `atanTabLoQ`, `atanTabHiQ`; checked by `atanTabN_check`). -/
@[expose] def atanTabN : List (ℕ × ℕ) :=
  [(0, 0), (534100634, 534100635), (1052175346, 1052175347), (1540908295, 1540908296),
    (1991351317, 1991351318), (2399165790, 2399165791), (2763816217, 2763816218),
    (3087351339, 3087351340), (3373259426, 3373259427), (3625613763, 3625613764),
    (3848528572, 3848528573), (4045859366, 4045859367), (4221066900, 4221066901),
    (4377178743, 4377178744), (4516803269, 4516803270), (4642168159, 4642168160),
    (4755167534, 4755167535), (4857409343, 4857409344), (4950259034, 4950259035),
    (5034877981, 5034877982), (5112256406, 5112256407), (5183241137, 5183241138),
    (5248558798, 5248558799), (5308835083, 5308835084), (5364610743, 5364610744),
    (5416354833, 5416354834), (5464475703, 5464475704), (5509330127, 5509330128),
    (5551230918, 5551230919), (5590453273, 5590453274), (5627240102, 5627240103),
    (5661806497, 5661806498), (5694343505, 5694343506)]

/-- Lower table bound (`0` beyond the table). -/
@[expose] def tabLo (j : ℕ) : ℕ := (atanTabN.getD j (0, 2 * sN)).1

/-- Upper table bound (`2 · 2³²` beyond the table). -/
@[expose] def tabHi (j : ℕ) : ℕ := (atanTabN.getD j (0, 2 * sN)).2

/-- Each table entry brackets the rational bounds of `arctan (j/8)`. -/
theorem atanTabN_check : (List.range 33).all (fun j =>
    decide (((tabLo j : ℕ) : ℚ) ≤ (sN : ℚ) * atanTabLoQ j) &&
    decide ((sN : ℚ) * atanTabHiQ j ≤ ((tabHi j : ℕ) : ℚ))) = true := by
  decide +kernel

/-- **Table soundness.** `tabLo j ≤ 2³² arctan (j/8) ≤ tabHi j` for every `j`. -/
theorem tab_spec (j : ℕ) :
    (tabLo j : ℝ) ≤ sN * arctan ((j : ℝ) / 8) ∧ sN * arctan ((j : ℝ) / 8) ≤ tabHi j := by
  have hS := sN_pos
  by_cases hj : j < 33
  · have h := List.all_eq_true.mp atanTabN_check j (List.mem_range.mpr hj)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have h1 : ((tabLo j : ℕ) : ℝ) ≤ sN * ((atanTabLoQ j : ℚ) : ℝ) := by exact_mod_cast h.1
    have h2 : (sN : ℝ) * ((atanTabHiQ j : ℚ) : ℝ) ≤ ((tabHi j : ℕ) : ℝ) := by
      exact_mod_cast h.2
    obtain ⟨l, r⟩ := atanTabQ_bounds j
    constructor <;> nlinarith
  · have e : atanTabN.getD j (0, 2 * sN) = (0, 2 * sN) :=
      List.getD_eq_default _ _ (by simp only [atanTabN, List.length_cons, List.length_nil]; omega)
    simp only [tabLo, tabHi, e]
    have a0 : 0 ≤ arctan ((j : ℝ) / 8) := arctan_nonneg.mpr (by positivity)
    have a1 : arctan ((j : ℝ) / 8) < 2 := by
      linarith [arctan_lt_pi_div_two ((j : ℝ) / 8), Real.pi_lt_d2]
    push_cast
    constructor <;> nlinarith

/-! ## Fast pointwise `arctan` on natural numbers -/

/-- Lower bound of `2³² arctan (w/2³²)` (intended for `w ≤ 4 · 2³²`): table value at
`c = j/8`, `j = ⌊8w/2³²⌋`, plus `polyLo` of the residual `r = (8w - j 2³²)/(8 · 2³² + w j)`. -/
@[expose] def midLo (w : ℕ) : ℕ :=
  tabLo (8 * w / sN) +
    polyLo ((8 * w - 8 * w / sN * sN) * sN / (8 * sN + w * (8 * w / sN)))

/-- Upper bound of `2³² arctan (w/2³²)` (same reduction as `midLo`). -/
@[expose] def midHi (w : ℕ) : ℕ :=
  tabHi (8 * w / sN) +
    polyHi ((8 * w - 8 * w / sN * sN) * sN / (8 * sN + w * (8 * w / sN)))

/-- Soundness of `midLo`, `midHi` (for every `w`). -/
theorem mid_spec (w : ℕ) :
    (midLo w : ℝ) ≤ sN * arctan (w / sN) ∧ sN * arctan (w / sN) ≤ midHi w := by
  have hS := sN_pos
  set j := 8 * w / sN with hj
  have hjS : j * sN ≤ 8 * w := Nat.div_mul_le_self _ _
  have hjS' : 8 * w < j * sN + sN := Nat.lt_div_mul_add (by norm_num [sN])
  have hjS1 : (j : ℝ) * sN ≤ 8 * w := by exact_mod_cast hjS
  have hjS2 : (8 * w : ℝ) < j * sN + sN := by exact_mod_cast hjS'
  set num := 8 * w - j * sN with hnum
  set den := 8 * sN + w * j with hden
  have hnumR : (num : ℝ) = 8 * w - j * sN := by rw [hnum, Nat.cast_sub hjS]; push_cast; ring
  have hdenR : (den : ℝ) = 8 * sN + w * j := by rw [hden]; push_cast; ring
  have hden0 : (0 : ℝ) < den := by rw [hdenR]; positivity
  have hden0' : 0 < den := by exact_mod_cast hden0
  set r : ℝ := num / den with hr
  have hx : (0 : ℝ) ≤ w / sN := by positivity
  have hc : (0 : ℝ) ≤ (j : ℝ) / 8 := by positivity
  have hred := arctan_eq_add_red hx hc
  have hrr : ((w : ℝ) / sN - (j : ℝ) / 8) * (1 + (w : ℝ) / sN * ((j : ℝ) / 8))⁻¹ = r := by
    rw [hr, hnumR, hdenR]; field_simp
  rw [hrr] at hred
  have hr0 : 0 ≤ r := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hr1 : r ≤ 1 := by
    refine (div_le_one hden0).mpr ?_
    rw [hnumR, hdenR]
    have : (0 : ℝ) ≤ w * j := by positivity
    linarith
  set rl := num * sN / den with hrl
  have e : (sN : ℝ) * r = (num * sN : ℝ) / den := by rw [hr]; ring
  have l1 : (rl : ℝ) ≤ sN * r := by
    have := nd_le (num * sN) den hden0'
    rw [e]; push_cast at this; exact this
  have l2 : sN * r < rl + 1 := by
    have := lt_nd (num * sN) den hden0'
    rw [e]; push_cast at this; exact this
  obtain ⟨p1, p2⟩ := poly_spec hr0 hr1 l1 l2
  obtain ⟨t1, t2⟩ := tab_spec j
  unfold midLo midHi
  rw [← hj]
  push_cast
  rw [hred]
  constructor <;> nlinarith

/-- Lower bound of `2³² arctan (w/2³²)` for every `w` (`π/2 - arctan (1/x)` above `4`;
`6746518852 = ⌊2³² π/2⌋`). -/
@[expose] def atanLoN (w : ℕ) : ℕ :=
  if w ≤ 4 * sN then midLo w else 6746518852 - midHi (sN * sN / w + 1)

/-- Upper bound of `2³² arctan (w/2³²)` for every `w` (`6746518853 = ⌈2³² π/2⌉`). -/
@[expose] def atanHiN (w : ℕ) : ℕ :=
  if w ≤ 4 * sN then midHi w else 6746518853 - midLo (sN * sN / w)

/-- Soundness of `atanLoN`, `atanHiN`. -/
theorem atanN_spec (w : ℕ) :
    (atanLoN w : ℝ) ≤ sN * arctan (w / sN) ∧ sN * arctan (w / sN) ≤ atanHiN w := by
  have hS := sN_pos
  have hpl : (6746518852 : ℝ) ≤ sN * (π / 2) := by
    have := Real.pi_gt_d20; norm_num [sN]; linarith
  have hph : sN * (π / 2) ≤ (6746518853 : ℝ) := by
    have := Real.pi_lt_d20; norm_num [sN]; linarith
  unfold atanLoN atanHiN
  split_ifs with h
  · exact mid_spec w
  · have hw : (4 * sN : ℝ) < w := by exact_mod_cast not_le.mp h
    have hw0 : (0 : ℝ) < w := by linarith
    have hx : 0 < (w : ℝ) / sN := by positivity
    have e : arctan ((w : ℝ) / sN) = π / 2 - arctan ((w : ℝ) / sN)⁻¹ := by
      rw [arctan_inv_of_pos hx]; ring
    have hinv : ((w : ℝ) / sN)⁻¹ = (sN * sN / w : ℝ) / sN := by field_simp
    have hw' : 0 < w := by exact_mod_cast hw0
    have a1 := nd_le (sN * sN) w hw'
    have a2 := lt_nd (sN * sN) w hw'
    push_cast at a1 a2
    obtain ⟨m1, -⟩ := mid_spec (sN * sN / w)
    obtain ⟨-, m2⟩ := mid_spec (sN * sN / w + 1)
    have mono1 : arctan ((((sN * sN / w : ℕ) : ℕ) : ℝ) / sN) ≤ arctan ((w : ℝ) / sN)⁻¹ := by
      apply arctan_mono; rw [hinv]; exact div_le_div_of_nonneg_right a1 hS.le
    have mono2 : arctan ((w : ℝ) / sN)⁻¹ ≤ arctan ((((sN * sN / w + 1 : ℕ) : ℕ) : ℝ) / sN) := by
      apply arctan_mono; rw [hinv]; push_cast; exact div_le_div_of_nonneg_right a2.le hS.le
    have hpos : 0 ≤ sN * arctan ((w : ℝ) / sN) :=
      mul_nonneg hS.le (arctan_nonneg.mpr hx.le)
    constructor
    · apply natsub_le hpos
      rw [e]; push_cast at mono2 m2 ⊢; nlinarith
    · refine le_trans ?_ (natsub_ge _ _)
      rw [e]; push_cast; nlinarith

/-! ## Fast `arcsin` on natural numbers -/

/-- Bounds `(lo, hi, ok)` of `2³² arcsin (m/2³²)`: `s2 = 2⁶⁴ - m²`, `q ≈ √s2` (Newton,
checked: `q² ≤ s2 < (q+1)²`), then `arctan` bounds at `⌊m 2³²/(q+1)⌋` and `⌊m 2³²/q⌋ + 1`. -/
@[expose] def asinPtN (m : ℕ) : ℕ × ℕ × Bool :=
  (atanLoN (m * sN / (FIv.isqrtAux 40 (sN * sN - m * m) sN + 1)),
    atanHiN (m * sN / FIv.isqrtAux 40 (sN * sN - m * m) sN + 1),
    decide (m < sN) &&
      decide (FIv.isqrtAux 40 (sN * sN - m * m) sN * FIv.isqrtAux 40 (sN * sN - m * m) sN ≤
        sN * sN - m * m) &&
      decide (sN * sN - m * m < (FIv.isqrtAux 40 (sN * sN - m * m) sN + 1) *
        (FIv.isqrtAux 40 (sN * sN - m * m) sN + 1)) &&
      decide (0 < FIv.isqrtAux 40 (sN * sN - m * m) sN))

/-- Soundness of `asinPtN`. -/
theorem asinPtN_spec (m : ℕ) (hok : (asinPtN m).2.2 = true) :
    ((asinPtN m).1 : ℝ) ≤ sN * arcsin (m / sN) ∧ sN * arcsin (m / sN) ≤ (asinPtN m).2.1 := by
  have hS := sN_pos
  simp only [asinPtN, Bool.and_eq_true, decide_eq_true_eq] at hok ⊢
  obtain ⟨⟨⟨hm, hq1⟩, hq2⟩, hq0⟩ := hok
  set q := FIv.isqrtAux 40 (sN * sN - m * m) sN
  have hmm : m * m ≤ sN * sN := Nat.mul_le_mul hm.le hm.le
  have hs2 : ((sN * sN - m * m : ℕ) : ℝ) = (sN : ℝ) ^ 2 - (m : ℝ) ^ 2 := by
    rw [Nat.cast_sub hmm]; push_cast; ring
  have hmR : (m : ℝ) < sN := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hq0' : (0 : ℝ) < q := by exact_mod_cast hq0
  set s := √((sN : ℝ) ^ 2 - (m : ℝ) ^ 2) with hs
  have hql : (q : ℝ) ≤ s := by
    rw [hs, Real.le_sqrt (by positivity) (by nlinarith), ← hs2]
    have : ((q * q : ℕ) : ℝ) ≤ ((sN * sN - m * m : ℕ) : ℝ) := by exact_mod_cast hq1
    push_cast at this; nlinarith
  have hqh : s < q + 1 := by
    rw [hs, Real.sqrt_lt' (by positivity), ← hs2]
    have : ((sN * sN - m * m : ℕ) : ℝ) < (((q + 1) * (q + 1) : ℕ) : ℝ) := by exact_mod_cast hq2
    push_cast at this; nlinarith
  have hs0 : 0 < s := lt_of_lt_of_le hq0' hql
  have hx1 : -1 < (m : ℝ) / sN := by
    have : (0 : ℝ) ≤ m / sN := by positivity
    linarith
  have hx2 : (m : ℝ) / sN < 1 := by rw [div_lt_one hS]; exact hmR
  have key : (m : ℝ) / sN / √(1 - ((m : ℝ) / sN) ^ 2) = (m * sN / s : ℝ) / sN := by
    have e1 : 1 - ((m : ℝ) / sN) ^ 2 = ((sN : ℝ) ^ 2 - (m : ℝ) ^ 2) / (sN : ℝ) ^ 2 := by
      field_simp
    rw [e1, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hS.le, ← hs]
    field_simp
  rw [arcsin_eq_arctan ⟨hx1, hx2⟩, key]
  have hq1' : 0 < q + 1 := by omega
  obtain ⟨l, -⟩ := atanN_spec (m * sN / (q + 1))
  obtain ⟨-, u⟩ := atanN_spec (m * sN / q + 1)
  have a1 := nd_le (m * sN) (q + 1) hq1'
  have a2 := lt_nd (m * sN) q hq0
  push_cast at a1 a2 u
  constructor
  · refine le_trans l (mul_le_mul_of_nonneg_left (arctan_mono ?_) hS.le)
    apply div_le_div_of_nonneg_right _ hS.le
    refine le_trans a1 ?_
    exact div_le_div_of_nonneg_left (by positivity) hs0 hqh.le
  · refine le_trans (mul_le_mul_of_nonneg_left (arctan_mono ?_) hS.le) u
    apply div_le_div_of_nonneg_right _ hS.le
    refine le_trans ?_ a2.le
    exact div_le_div_of_nonneg_left (by positivity) hq0' hql

/-! ## Small-argument `cosh` and `sinh` on natural numbers -/

/-- Lower bound of `2³² (1 + v/d₀ (1 + v/d₁ (…)))` from `vl ≤ 2³² v`. -/
@[expose] def hUpLo (vl : ℕ) : List ℕ → ℕ
  | [] => sN
  | d :: ds => sN + vl * hUpLo vl ds / (sN * d)

/-- Upper bound of `2³² (1 + v/d₀ (1 + v/d₁ (…)))` from `2³² v ≤ vh`. -/
@[expose] def hUpHi (vh : ℕ) : List ℕ → ℕ
  | [] => sN
  | d :: ds => sN + vh * hUpHi vh ds / (sN * d) + 1

/-- The real nested sum `1 + v/d₀ (1 + v/d₁ (…))`. -/
@[expose] noncomputable def hUpR (v : ℝ) : List ℕ → ℝ
  | [] => 1
  | d :: ds => 1 + v * hUpR v ds / d

/-- Soundness of `hUpLo`, `hUpHi` for `v ≥ 0` and positive divisors. -/
theorem hUp_spec {v : ℝ} {vl vh : ℕ} (hv0 : 0 ≤ v) (hl : (vl : ℝ) ≤ sN * v)
    (hh : sN * v ≤ (vh : ℝ)) (ds : List ℕ) (hds : ∀ d ∈ ds, 0 < d) :
    0 ≤ hUpR v ds ∧ (hUpLo vl ds : ℝ) ≤ sN * hUpR v ds ∧ sN * hUpR v ds ≤ hUpHi vh ds := by
  have hS := sN_pos
  induction ds with
  | nil => simp [hUpR, hUpLo, hUpHi]
  | cons d ds ih =>
    obtain ⟨h0, hlo, hhi⟩ := ih (fun e he => hds e (List.mem_cons_of_mem d he))
    have hd : 0 < d := hds d List.mem_cons_self
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have hSd : 0 < sN * d := Nat.mul_pos (by norm_num [sN]) hd
    simp only [hUpR, hUpLo, hUpHi]
    set H := hUpR v ds
    have e : (sN : ℝ) * (1 + v * H / d) = sN + (sN * v) * (sN * H) / (sN * d) := by
      field_simp
    refine ⟨by positivity, ?_, ?_⟩
    · have a := nd_le (vl * hUpLo vl ds) (sN * d) hSd
      have p : (vl : ℝ) * (hUpLo vl ds) ≤ (sN * v) * (sN * H) :=
        mul_le_mul hl hlo (Nat.cast_nonneg _) (by positivity)
      push_cast at a ⊢
      rw [e]
      have := div_le_div_of_nonneg_right p (by positivity : (0 : ℝ) ≤ sN * d)
      linarith
    · have a := lt_nd (vh * hUpHi vh ds) (sN * d) hSd
      have p : (sN * v) * (sN * H) ≤ (vh : ℝ) * (hUpHi vh ds) :=
        mul_le_mul hh hhi (by positivity) (Nat.cast_nonneg _)
      push_cast at a ⊢
      rw [e]
      have := div_le_div_of_nonneg_right p (by positivity : (0 : ℝ) ≤ sN * d)
      linarith

/-- The even part of `expPoly9` in nested form. -/
theorem hUpR_cosh (x : ℝ) : hUpR (x ^ 2) [2, 12, 30, 56] = (expPoly9 x + expPoly9 (-x)) / 2 := by
  simp only [hUpR, expPoly9, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  push_cast
  ring

/-- The odd part of `expPoly9` in nested form. -/
theorem hUpR_sinh (x : ℝ) :
    x * hUpR (x ^ 2) [6, 20, 42] = (expPoly9 x - expPoly9 (-x)) / 2 := by
  simp only [hUpR, expPoly9, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  push_cast
  ring

/-- Bounds `(lo, hi)` of `2³² cosh (m/2³²)`, sound for `4m ≤ 2³²`. -/
@[expose] def coshN (m : ℕ) : ℕ × ℕ :=
  (hUpLo (m * m / sN) [2, 12, 30, 56] - 1, hUpHi (m * m / sN + 1) [2, 12, 30, 56] + 1)

/-- Bounds `(lo, hi)` of `2³² sinh (m/2³²)`, sound for `4m ≤ 2³²`. -/
@[expose] def sinhN (m : ℕ) : ℕ × ℕ :=
  (m * hUpLo (m * m / sN) [6, 20, 42] / sN - 1,
    m * hUpHi (m * m / sN + 1) [6, 20, 42] / sN + 2)

/-- The squared-argument bounds used by `coshN`, `sinhN`. -/
theorem sq_bounds (m : ℕ) :
    ((m * m / sN : ℕ) : ℝ) ≤ sN * ((m : ℝ) / sN) ^ 2 ∧
      sN * ((m : ℝ) / sN) ^ 2 ≤ ((m * m / sN + 1 : ℕ) : ℝ) := by
  have hS := sN_pos
  have e : (sN : ℝ) * ((m : ℝ) / sN) ^ 2 = (m * m : ℝ) / sN := by field_simp
  have a := nd_le (m * m) sN (by norm_num [sN])
  have b := lt_nd (m * m) sN (by norm_num [sN])
  push_cast at a b ⊢
  rw [e]
  exact ⟨a, b.le⟩

/-- `|m/2³²| ≤ 1/4` from `4m ≤ 2³²`. -/
theorem abs_quarter {m : ℕ} (h : 4 * m ≤ sN) : |(m : ℝ) / sN| ≤ 1 / 4 := by
  have hS := sN_pos
  have h' : (4 * m : ℝ) ≤ sN := by exact_mod_cast h
  rw [abs_of_nonneg (by positivity), div_le_iff₀ hS]
  linarith

/-- Soundness of `coshN`. -/
theorem coshN_spec {m : ℕ} (h : 4 * m ≤ sN) :
    ((coshN m).1 : ℝ) ≤ sN * Real.cosh (m / sN) ∧ sN * Real.cosh (m / sN) ≤ (coshN m).2 := by
  have hS := sN_pos
  set x : ℝ := m / sN
  obtain ⟨v1, v2⟩ := sq_bounds m
  obtain ⟨-, l, u⟩ := hUp_spec (sq_nonneg x) v1 v2 [2, 12, 30, 56] (by simp)
  rw [hUpR_cosh] at l u
  have hx := abs_quarter h
  have hx' : |-x| ≤ 1 / 4 := by rwa [abs_neg]
  have a := abs_le.mp (exp_sub_expPoly9 hx)
  have b := abs_le.mp (exp_sub_expPoly9 hx')
  rw [← sN_real] at a b
  have ec := Real.cosh_eq x
  have e1 : (sN : ℝ) * (1 / sN) = 1 := by field_simp
  have c1 : 0 ≤ sN * Real.cosh x := mul_nonneg hS.le (by linarith [Real.one_le_cosh x])
  constructor
  · apply natsub_le c1
    rw [ec]; push_cast; nlinarith
  · simp only [coshN]; push_cast; rw [ec]; nlinarith

/-- Soundness of `sinhN`. -/
theorem sinhN_spec {m : ℕ} (h : 4 * m ≤ sN) :
    ((sinhN m).1 : ℝ) ≤ sN * Real.sinh (m / sN) ∧ sN * Real.sinh (m / sN) ≤ (sinhN m).2 := by
  have hS := sN_pos
  set x : ℝ := m / sN with hxdef
  have hx0 : 0 ≤ x := by positivity
  obtain ⟨v1, v2⟩ := sq_bounds m
  obtain ⟨H0, l, u⟩ := hUp_spec (sq_nonneg x) v1 v2 [6, 20, 42] (by simp)
  have hm : (m : ℝ) ≤ sN * x := by rw [hxdef]; field_simp; rfl
  have hm' : sN * x ≤ (m : ℝ) := by rw [hxdef]; field_simp; rfl
  have ml := mulDiv_le hm l
  have mu := le_mulDiv H0 hm' u
  rw [hUpR_sinh] at ml mu
  have hx := abs_quarter h
  have hx' : |-x| ≤ 1 / 4 := by rwa [abs_neg]
  have a := abs_le.mp (exp_sub_expPoly9 hx)
  have b := abs_le.mp (exp_sub_expPoly9 hx')
  rw [← sN_real] at a b
  have es := Real.sinh_eq x
  have e1 : (sN : ℝ) * (1 / sN) = 1 := by field_simp
  have c1 : 0 ≤ sN * Real.sinh x := mul_nonneg hS.le (Real.sinh_nonneg_iff.mpr hx0)
  constructor
  · apply natsub_le c1
    rw [es]; nlinarith
  · simp only [sinhN]; push_cast; rw [es]; nlinarith

/-! ## Interval versions -/

/-- `fxVal` of a natural number is its quotient by the natural scale. -/
theorem fxVal_nat (m : ℕ) : fxVal (m : ℤ) = (m : ℝ) / sN := by
  rw [fxVal, sN_real]; push_cast; ring

/-- `fxVal` of `Int.negSucc m` is `-(m+1)/2³²`. -/
theorem fxVal_negSucc (m : ℕ) : fxVal (Int.negSucc m) = -(((m + 1 : ℕ) : ℝ) / sN) := by
  rw [fxVal, sN_real, Int.cast_negSucc]; ring

/-- From `a ≤ 2³² y` to `fxVal a ≤ y`. -/
theorem fxVal_le_of {a : ℤ} {y : ℝ} (h : (a : ℝ) ≤ sN * y) : fxVal a ≤ y := by
  have hS := sN_pos
  rw [fxVal, ← sN_real, div_le_iff₀ hS]; linarith

/-- From `2³² y ≤ a` to `y ≤ fxVal a`. -/
theorem le_fxVal_of {a : ℤ} {y : ℝ} (h : sN * y ≤ (a : ℝ)) : y ≤ fxVal a := by
  have hS := sN_pos
  rw [fxVal, ← sN_real, le_div_iff₀ hS]; linarith

namespace FIv

/-- Lower end of the fast `arctan` at a fixed-point number (oddness for negatives). -/
@[expose] def atanLoZ (n : ℤ) : ℤ :=
  match n with
  | .ofNat m => (atanLoN m : ℤ)
  | .negSucc m => -((atanHiN (m + 1) : ℕ) : ℤ)

/-- Upper end of the fast `arctan` at a fixed-point number. -/
@[expose] def atanHiZ (n : ℤ) : ℤ :=
  match n with
  | .ofNat m => (atanHiN m : ℤ)
  | .negSucc m => -((atanLoN (m + 1) : ℕ) : ℤ)

/-- Soundness of `atanLoZ`, `atanHiZ`. -/
theorem atanZ_spec (n : ℤ) :
    fxVal (atanLoZ n) ≤ Real.arctan (fxVal n) ∧ Real.arctan (fxVal n) ≤ fxVal (atanHiZ n) := by
  cases n with
  | ofNat m =>
    obtain ⟨l, u⟩ := atanN_spec m
    have e : fxVal (Int.ofNat m) = (m : ℝ) / sN := fxVal_nat m
    rw [e]
    exact ⟨fxVal_le_of (by simpa [atanLoZ] using l), le_fxVal_of (by simpa [atanHiZ] using u)⟩
  | negSucc m =>
    obtain ⟨l, u⟩ := atanN_spec (m + 1)
    rw [fxVal_negSucc, Real.arctan_neg]
    refine ⟨fxVal_le_of ?_, le_fxVal_of ?_⟩
    · simp only [atanLoZ]; push_cast at u ⊢; linarith
    · simp only [atanHiZ]; push_cast at l ⊢; linarith

/-- **Fast interval `arctan`** (no square roots, natural-number kernel arithmetic):
endpoint-wise, valid for all finite inputs. -/
@[expose] def atanFast (I : FIv) : FIv := ⟨atanLoZ I.lo, atanHiZ I.hi, I.ok⟩

/-- Soundness of `atanFast`. -/
theorem mem_atanFast {I : FIv} {x : ℝ} (h : I.Mem x) : (atanFast I).Mem (Real.arctan x) :=
  mem_mono_endpoints arctan_mono h (fun hok => hok) (fun _ => (atanZ_spec I.lo).1)
    (fun _ => (atanZ_spec I.hi).2)

/-- Enclosure of `arcsin (n/2³²)` at a fixed-point number (oddness for negatives); valid only
for `|n| < 2³²` (and a successful square-root check). -/
@[expose] def asinPtZ (n : ℤ) : FIv :=
  match n with
  | .ofNat m => ⟨(asinPtN m).1, (asinPtN m).2.1, (asinPtN m).2.2⟩
  | .negSucc m => ⟨-((asinPtN (m + 1)).2.1 : ℤ), -((asinPtN (m + 1)).1 : ℤ),
      (asinPtN (m + 1)).2.2⟩

/-- Soundness of `asinPtZ`. -/
theorem mem_asinPtZ (n : ℤ) : (asinPtZ n).Mem (Real.arcsin (fxVal n)) := by
  intro hok
  cases n with
  | ofNat m =>
    obtain ⟨l, u⟩ := asinPtN_spec m hok
    have e : fxVal (Int.ofNat m) = (m : ℝ) / sN := fxVal_nat m
    rw [e]
    exact ⟨fxVal_le_of l, le_fxVal_of u⟩
  | negSucc m =>
    obtain ⟨l, u⟩ := asinPtN_spec (m + 1) hok
    rw [fxVal_negSucc, Real.arcsin_neg]
    refine ⟨fxVal_le_of ?_, le_fxVal_of ?_⟩
    · simp only [asinPtZ]; push_cast at u ⊢; linarith
    · simp only [asinPtZ]; push_cast at l ⊢; linarith

/-- **Fast interval `arcsin`** (one square root per endpoint): endpoint-wise; valid only when
both endpoints lie strictly inside `(-1, 1)`. -/
@[expose] def asinFast (I : FIv) : FIv :=
  ⟨(asinPtZ I.lo).lo, (asinPtZ I.hi).hi, I.ok && (asinPtZ I.lo).ok && (asinPtZ I.hi).ok⟩

/-- Unfolding equation for `asinFast` (keeps the kernel from comparing projections of two
unevaluated enclosures). -/
theorem asinFast_eq (I : FIv) : asinFast I =
    ⟨(asinPtZ I.lo).lo, (asinPtZ I.hi).hi, I.ok && (asinPtZ I.lo).ok && (asinPtZ I.hi).ok⟩ :=
  rfl

/-- Soundness of `asinFast`. -/
theorem mem_asinFast {I : FIv} {x : ℝ} (h : I.Mem x) : (asinFast I).Mem (Real.arcsin x) := by
  rw [asinFast_eq]
  refine mem_mono_endpoints monotone_arcsin h ?_ ?_ ?_ <;> intro hok <;> dsimp only at hok ⊢ <;>
    simp only [Bool.and_eq_true] at hok
  · exact hok.1.1
  · exact (mem_asinPtZ I.lo hok.1.2).1
  · exact (mem_asinPtZ I.hi hok.2).2

/-- Lower end of the fast `sinh` at a fixed-point number. -/
@[expose] def sinhLoZ (n : ℤ) : ℤ :=
  match n with
  | .ofNat m => ((sinhN m).1 : ℤ)
  | .negSucc m => -((sinhN (m + 1)).2 : ℤ)

/-- Upper end of the fast `sinh` at a fixed-point number. -/
@[expose] def sinhHiZ (n : ℤ) : ℤ :=
  match n with
  | .ofNat m => ((sinhN m).2 : ℤ)
  | .negSucc m => -((sinhN (m + 1)).1 : ℤ)

/-- Soundness of `sinhLoZ`, `sinhHiZ` for `4|n| ≤ 2³²`. -/
theorem sinhZ_spec {n : ℤ} (h : 4 * n.natAbs ≤ sN) :
    fxVal (sinhLoZ n) ≤ Real.sinh (fxVal n) ∧ Real.sinh (fxVal n) ≤ fxVal (sinhHiZ n) := by
  cases n with
  | ofNat m =>
    obtain ⟨l, u⟩ := sinhN_spec (m := m) (by simpa using h)
    have e : fxVal (Int.ofNat m) = (m : ℝ) / sN := fxVal_nat m
    rw [e]
    exact ⟨fxVal_le_of (by simpa [sinhLoZ] using l), le_fxVal_of (by simpa [sinhHiZ] using u)⟩
  | negSucc m =>
    obtain ⟨l, u⟩ := sinhN_spec (m := m + 1) (by simpa [Int.natAbs_negSucc] using h)
    rw [fxVal_negSucc, Real.sinh_neg]
    refine ⟨fxVal_le_of ?_, le_fxVal_of ?_⟩
    · simp only [sinhLoZ]; push_cast at u ⊢; linarith
    · simp only [sinhHiZ]; push_cast at l ⊢; linarith

/-- **Fast interval `sinh`** (increasing; endpoint-wise), valid only for enclosures in
`[-1/4, 1/4]`. -/
@[expose] def sinhSmall (I : FIv) : FIv :=
  ⟨sinhLoZ I.lo, sinhHiZ I.hi,
    I.ok && decide (4 * I.lo.natAbs ≤ sN) && decide (4 * I.hi.natAbs ≤ sN)⟩

/-- Soundness of `sinhSmall`. -/
theorem mem_sinhSmall {I : FIv} {x : ℝ} (h : I.Mem x) : (sinhSmall I).Mem (Real.sinh x) := by
  refine mem_mono_endpoints Real.sinh_strictMono.monotone h ?_ ?_ ?_ <;> intro hok <;>
    simp only [sinhSmall, Bool.and_eq_true, decide_eq_true_eq] at hok
  · exact hok.1.1
  · exact (sinhZ_spec hok.1.2).1
  · exact (sinhZ_spec hok.2).2

/-- Sign test `n < 0` by constructor matching (cheap in the kernel). -/
@[expose] def isNeg (n : ℤ) : Bool :=
  match n with
  | .ofNat _ => false
  | .negSucc _ => true

/-- Sign test `0 < n` by constructor matching. -/
@[expose] def isPos (n : ℤ) : Bool :=
  match n with
  | .ofNat k => decide (0 < k)
  | .negSucc _ => false

/-- `isNeg n = false → 0 ≤ n`. -/
theorem nonneg_of_isNeg {n : ℤ} (h : isNeg n = false) : 0 ≤ n := by
  cases n with
  | ofNat k => exact Int.natCast_nonneg k
  | negSucc k => simp [isNeg] at h

/-- `isPos n = false → n ≤ 0`. -/
theorem nonpos_of_isPos {n : ℤ} (h : isPos n = false) : n ≤ 0 := by
  cases n with
  | ofNat k =>
    simp only [isPos, decide_eq_false_iff_not, not_lt, Nat.le_zero] at h
    subst h; rfl
  | negSucc k => exact Int.le_of_lt (Int.negSucc_lt_zero k)

/-- **Fast interval `cosh`** (even, increasing in `|x|`), valid only for enclosures in
`[-1/4, 1/4]`: lower end at the smaller absolute endpoint (or `1` if straddling `0`), upper
end at the larger. -/
@[expose] def coshSmall (I : FIv) : FIv :=
  ⟨if isNeg I.lo && isPos I.hi then (sN : ℤ) else ((coshN (min I.lo.natAbs I.hi.natAbs)).1 : ℤ),
    ((coshN (max I.lo.natAbs I.hi.natAbs)).2 : ℤ),
    I.ok && decide (4 * max I.lo.natAbs I.hi.natAbs ≤ sN)⟩

/-- `fxVal` of a natural absolute value. -/
theorem fxVal_natAbs (n : ℤ) : ((n.natAbs : ℕ) : ℝ) / sN = |fxVal n| := by
  have hS := sN_pos
  rw [Nat.cast_natAbs, Int.cast_abs, fxVal, ← sN_real, abs_div, abs_of_pos hS]

/-- Soundness of `coshSmall`. -/
theorem mem_coshSmall {I : FIv} {x : ℝ} (h : I.Mem x) : (coshSmall I).Mem (Real.cosh x) := by
  intro hok
  have hS := sN_pos
  have ha : (I.lo.natAbs : ℝ) / sN = |fxVal I.lo| := fxVal_natAbs I.lo
  have hb : (I.hi.natAbs : ℝ) / sN = |fxVal I.hi| := fxVal_natAbs I.hi
  unfold coshSmall at hok ⊢
  generalize I.lo.natAbs = a at ha hok ⊢
  generalize I.hi.natAbs = b at hb hok ⊢
  have hM : (max a b : ℝ) = ((max a b : ℕ) : ℝ) := by push_cast; rfl
  have hm' : (min a b : ℝ) = ((min a b : ℕ) : ℝ) := by push_cast; rfl
  generalize hMd : max a b = M at hok hM ⊢
  generalize hmd : min a b = m at hm' ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hI, hmax⟩ := hok
  obtain ⟨a1, a2⟩ := h hI
  have hMa : a ≤ M := hMd ▸ le_max_left a b
  have hMb : b ≤ M := hMd ▸ le_max_right a b
  have hma : m ≤ a := hmd ▸ min_le_left a b
  have hmb : m ≤ b := hmd ▸ min_le_right a b
  have hmin : 4 * m ≤ sN := le_trans (Nat.mul_le_mul_left 4 (hma.trans hMa)) hmax
  have hMa' : (a : ℝ) ≤ M := by exact_mod_cast hMa
  have hMb' : (b : ℝ) ≤ M := by exact_mod_cast hMb
  have hma' : (m : ℝ) ≤ a := by exact_mod_cast hma
  have hmb' : (m : ℝ) ≤ b := by exact_mod_cast hmb
  have habs : |x| ≤ (M : ℝ) / sN := by
    have l1 : (a : ℝ) / sN ≤ M / sN := div_le_div_of_nonneg_right hMa' hS.le
    have l2 : (b : ℝ) / sN ≤ M / sN := div_le_div_of_nonneg_right hMb' hS.le
    rw [ha] at l1
    rw [hb] at l2
    rw [abs_le]
    constructor <;> cases abs_cases (fxVal I.lo) <;> cases abs_cases (fxVal I.hi) <;> linarith
  constructor
  · split_ifs with c
    · rw [show fxVal (sN : ℤ) = 1 by rw [fxVal, ← sN_real]; push_cast; field_simp]
      exact Real.one_le_cosh x
    · obtain ⟨l, -⟩ := coshN_spec hmin
      refine fxVal_le_of (le_trans (by exact_mod_cast l) ?_)
      apply mul_le_mul_of_nonneg_left _ hS.le
      apply Real.cosh_le_cosh.mpr
      rw [abs_of_nonneg (by positivity)]
      simp only [Bool.and_eq_true, not_and_or, Bool.not_eq_true] at c
      rcases c with c | c
      · have h0 : (0 : ℝ) ≤ I.lo := by exact_mod_cast nonneg_of_isNeg c
        have hlo : 0 ≤ fxVal I.lo := by rw [fxVal]; positivity
        calc (m : ℝ) / sN ≤ (a : ℝ) / sN := div_le_div_of_nonneg_right hma' hS.le
          _ = fxVal I.lo := by rw [ha, abs_of_nonneg hlo]
          _ ≤ |x| := a1.trans (le_abs_self x)
      · have h0 : (I.hi : ℝ) ≤ 0 := by exact_mod_cast nonpos_of_isPos c
        have hhi : fxVal I.hi ≤ 0 := by
          rw [fxVal]; exact div_nonpos_of_nonpos_of_nonneg h0 (by rw [fxScale_real]; norm_num)
        calc (m : ℝ) / sN ≤ (b : ℝ) / sN := div_le_div_of_nonneg_right hmb' hS.le
          _ = -fxVal I.hi := by rw [hb, abs_of_nonpos hhi]
          _ ≤ |x| := by rw [abs_of_nonpos (a2.trans hhi)]; linarith
  · obtain ⟨-, u⟩ := coshN_spec hmax
    refine le_fxVal_of (le_trans ?_ (by exact_mod_cast u))
    apply mul_le_mul_of_nonneg_left _ hS.le
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (M : ℝ) / sN)]
    exact habs

end FIv

/-! ## Sanity fixtures -/

/-- Accepted fixture: `atanFast 1` is valid, has width at most `8 · 2⁻³²` and contains
`π/4`. -/
theorem fixture_atanFast_one : (FIv.atanFast (FIv.ofInt 1)).ok = true ∧
    (FIv.atanFast (FIv.ofInt 1)).hi - (FIv.atanFast (FIv.ofInt 1)).lo ≤ 8 ∧
    (FIv.atanFast (FIv.ofInt 1)).Mem (Real.pi / 4) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  simpa [Real.arctan_one] using FIv.mem_atanFast (FIv.mem_ofInt 1)

/-- Accepted fixture: large and negative arguments are valid and tight. -/
theorem fixture_atanFast_large : (FIv.atanFast (FIv.ofInt 10000)).ok = true ∧
    (FIv.atanFast (FIv.ofInt 10000)).hi - (FIv.atanFast (FIv.ofInt 10000)).lo ≤ 8 ∧
    (FIv.atanFast (FIv.ofInt (-37))).hi - (FIv.atanFast (FIv.ofInt (-37))).lo ≤ 8 := by
  decide +kernel

/-- Accepted fixture: `asinFast (1/2)` is valid, has width at most `8 · 2⁻³²` and contains
`π/6`. -/
theorem fixture_asinFast_half : (FIv.asinFast (FIv.ofFrac 1 2)).ok = true ∧
    (FIv.asinFast (FIv.ofFrac 1 2)).hi - (FIv.asinFast (FIv.ofFrac 1 2)).lo ≤ 8 ∧
    (FIv.asinFast (FIv.ofFrac 1 2)).Mem (Real.pi / 6) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  have := FIv.mem_asinFast (FIv.mem_ofFrac 1 2)
  have e : Real.arcsin 2⁻¹ = Real.pi / 6 := by
    rw [← one_div, ← Real.sin_pi_div_six, Real.arcsin_sin] <;> linarith [Real.pi_pos]
  simpa [e] using this

/-- Accepted fixture: `asinFast` at `±0.95` is valid and tight. -/
theorem fixture_asinFast_edge : (FIv.asinFast (FIv.ofFrac 95 100)).ok = true ∧
    (FIv.asinFast (FIv.ofFrac 95 100)).hi - (FIv.asinFast (FIv.ofFrac 95 100)).lo ≤ 8 ∧
    (FIv.asinFast (FIv.ofFrac (-95) 100)).hi - (FIv.asinFast (FIv.ofFrac (-95) 100)).lo ≤ 8 := by
  decide +kernel

/-- Accepted fixture: `coshSmall (1/4)` is valid, has width at most `5 · 2⁻³²` and contains
`cosh (1/4)`. -/
theorem fixture_coshSmall : (FIv.coshSmall (FIv.ofFrac 1 4)).ok = true ∧
    (FIv.coshSmall (FIv.ofFrac 1 4)).hi - (FIv.coshSmall (FIv.ofFrac 1 4)).lo ≤ 5 ∧
    (FIv.coshSmall (FIv.ofFrac 1 4)).Mem (Real.cosh (1 / 4)) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  simpa using FIv.mem_coshSmall (FIv.mem_ofFrac 1 4)

/-- Accepted fixture: `sinhSmall (-1/4)` is valid, has width at most `5 · 2⁻³²` and contains
`sinh (-1/4)`. -/
theorem fixture_sinhSmall : (FIv.sinhSmall (FIv.ofFrac (-1) 4)).ok = true ∧
    (FIv.sinhSmall (FIv.ofFrac (-1) 4)).hi - (FIv.sinhSmall (FIv.ofFrac (-1) 4)).lo ≤ 5 ∧
    (FIv.sinhSmall (FIv.ofFrac (-1) 4)).Mem (Real.sinh (-1 / 4)) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  simpa [neg_div] using FIv.mem_sinhSmall (FIv.mem_ofFrac (-1) 4)

/-- Degenerate fixture: `coshSmall` of an enclosure straddling `0` has lower end exactly
`1`. -/
theorem fixture_coshSmall_straddle :
    (FIv.coshSmall ⟨-fxScale / 5, fxScale / 6, true⟩).ok = true ∧
    (FIv.coshSmall ⟨-fxScale / 5, fxScale / 6, true⟩).lo = fxScale := by
  decide +kernel

/-- Rejected fixture: `asinFast` of an enclosure reaching `1` is invalid. -/
theorem fixture_asinFast_rejected : (FIv.asinFast ⟨fxScale / 2, fxScale, true⟩).ok = false := by
  decide +kernel

/-- Rejected fixture: `coshSmall`, `sinhSmall` of `[0, 1/2]` (outside `[-1/4, 1/4]`) are
invalid. -/
theorem fixture_coshSmall_rejected : (FIv.coshSmall ⟨0, fxScale / 2, true⟩).ok = false ∧
    (FIv.sinhSmall ⟨0, fxScale / 2, true⟩).ok = false := by
  decide +kernel

end PlasmaLean.Certificates.ValidatedQuadrature
