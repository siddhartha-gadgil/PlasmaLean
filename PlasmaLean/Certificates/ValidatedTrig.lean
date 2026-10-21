/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.ValidatedQuadrature
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Validated transcendental functions on fixed-point enclosures

This module extends the fixed-point interval type `FIv` of
`PlasmaLean.Certificates.ValidatedQuadrature` (endpoints `lo/2³²`, `hi/2³²`, validity flag
`ok`) by rigorous enclosures of `π`, `arctan`, `arcsin`, `cosh` and `sinh`, plus an
intersection `meet`. Every operation is straight-line or structurally recursive code on
`Int` (no `Rat`, no `Float`, no well-founded recursion), so it evaluates quickly under
`decide +kernel`. As for the base operations, an invalid enclosure (`ok = false`) contains
every real number, so each soundness lemma `mem_*` is unconditional.

**Method.**
* `pi`: outward rounding of Mathlib's 20-digit bounds `Real.pi_gt_d20`, `Real.pi_lt_d20`.
* `arctan`: `arctan` is increasing, so the lower end is a lower bound at `lo` and the upper
  end an upper bound at `hi` (`mem_mono_endpoints`). At a point `t ≥ 0` we use
  `arctan t = π/2 - arctan (1/t)` when `t > 1`, then one half-angle reduction
  `arctan y = 2 arctan (y / (1 + √(1 + y²)))` (`arctan_eq_two_mul_red`), so the reduced
  argument lies in `[0, tan (π/8)] ⊆ [0, 0.415]`. There the alternating Taylor sums
  `S_N(u) = Σ_{k<N} (-1)^k u^{2k+1}/(2k+1)` satisfy `S_12(u) ≤ arctan u ≤ S_13(u)` for
  `u ≥ 0` (`atanSeries_bound`, proved from the derivative identity
  `(arctan - S_N)' = (-u²)^N / (1 + u²)`). Negative points use oddness.
* `arcsin`: increasing, endpoint-wise, `arcsin t = arctan (t / √(1 - t²))` for `|t| < 1`
  (`Real.arcsin_eq_arctan`); invalid unless the enclosure lies strictly inside `(-1, 1)`.
* `cosh`, `sinh`: the even and odd parts of the degree-13 exponential Taylor polynomial,
  evaluated in nested Horner form `1 + v/(1·2) (1 + v/(3·4) (…))` (`v = x²`) with exact
  integer divisions, plus one unit of the last place for the remainder from
  `Real.exp_bound` (`|x| ≤ 1`, `n = 14`, remainder `≤ 15/(14!·14) < 2⁻³²`). `sinh` is
  increasing; `cosh` is even and increasing in `|x|`. Invalid unless the enclosure lies in
  `[-1, 1]`.

**Accuracy and cost.** On thin inputs the enclosures have width at most about ten units of
`2⁻³²` (`≈ 2e-9`) for `arctan` (all arguments, including `10⁴` and beyond) and `arcsin`
(`|x| ≤ 0.99`; about 20 units at `0.999`), and about three units for `cosh`, `sinh`. One
`decide +kernel` evaluation of any of the four interval functions takes about 10–25 ms.

Sanity fixtures: accepted fixtures `fixture_arctan_one` (enclosure of `π/4` within `1e-8`),
`fixture_arctan_large`, `fixture_arcsin_half` (enclosure of `π/6`), `fixture_arcsin_edge`,
`fixture_cosh_one`, `fixture_sinh_one`, `fixture_pi`, `fixture_meet`; a degenerate case
`fixture_cosh_straddle`; rejected fixtures `fixture_arcsin_rejected` (an enclosure containing
`1`) and `fixture_cosh_rejected` (`[2, 3]`).
-/

public section

namespace PlasmaLean.Certificates.ValidatedQuadrature

open Real

namespace FIv

/-! ## Basic helpers -/

/-- The thin enclosure `[n/2³², n/2³²]` of a fixed-point number. -/
@[expose] def thin (n : ℤ) : FIv := ⟨n, n, true⟩

/-- Soundness of thin enclosures. -/
theorem mem_thin (n : ℤ) : (thin n).Mem (fxVal n) := by
  intro _
  exact ⟨le_rfl, le_rfl⟩

/-- The enclosure `ofInt 1` contains `1`. -/
theorem mem_one : (ofInt 1).Mem 1 := by simpa using mem_ofInt 1

/-- Exact (outward-rounded) division by an integer; valid only for a positive divisor. -/
@[expose] def divInt (I : FIv) (k : ℤ) : FIv := ⟨I.lo / k, -((-I.hi) / k), I.ok && decide (0 < k)⟩

/-- Soundness of division by a positive integer. -/
theorem mem_divInt {I : FIv} {x : ℝ} (hx : I.Mem x) (k : ℤ) : (I.divInt k).Mem (x / k) := by
  rw [mem_iff] at *
  intro hok
  simp only [divInt, Bool.and_eq_true, decide_eq_true_eq] at hok ⊢
  obtain ⟨a1, a2⟩ := hx hok.1
  have hk : (0 : ℝ) < k := by exact_mod_cast hok.2
  have l1 := fdiv_le I.lo k hok.2
  have l2 := le_cdiv I.hi k hok.2
  have e : (fxScale : ℝ) * (x / k) = fxScale * x / k := by ring
  rw [e]
  exact ⟨le_trans l1 (div_le_div_of_nonneg_right a1 hk.le),
    le_trans (div_le_div_of_nonneg_right a2 hk.le) l2⟩

/-- Monotone functions are enclosed endpoint-wise: if `J` is valid only when `I` is, and
`J.lo` (`J.hi`) bounds `f` at the lower (upper) end of `I`, then `J` encloses `f x`. -/
theorem mem_mono_endpoints {f : ℝ → ℝ} (hf : Monotone f) {I J : FIv} {x : ℝ} (hx : I.Mem x)
    (hok : J.ok = true → I.ok = true) (hL : J.ok = true → fxVal J.lo ≤ f (fxVal I.lo))
    (hU : J.ok = true → f (fxVal I.hi) ≤ fxVal J.hi) : J.Mem (f x) := by
  intro hJ
  obtain ⟨h1, h2⟩ := hx (hok hJ)
  exact ⟨le_trans (hL hJ) (hf h1), le_trans (hf h2) (hU hJ)⟩

/-! ## `π` and intersection -/

/-- An enclosure of `π` (from the 20-digit bounds `Real.pi_gt_d20`, `Real.pi_lt_d20`). -/
@[expose] def pi : FIv := ⟨13493037704, 13493037705, true⟩

/-- Soundness of the enclosure of `π`. -/
theorem mem_pi : pi.Mem Real.pi := by
  intro _
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  simp only [pi, fxVal, fxScale_real]
  constructor <;> norm_num <;> linarith

/-- Intersection of two enclosures. If both are valid and the intersection is empty, the
result is marked invalid (this can only happen when no real lies in both). -/
@[expose] def meet (I J : FIv) : FIv :=
  if I.ok then
    if J.ok then ⟨max I.lo J.lo, min I.hi J.hi, decide (max I.lo J.lo ≤ min I.hi J.hi)⟩ else I
  else J

/-- Soundness of the intersection. -/
theorem mem_meet {I J : FIv} {x : ℝ} (hI : I.Mem x) (hJ : J.Mem x) : (I.meet J).Mem x := by
  unfold meet
  split_ifs with h1 h2
  · intro _
    obtain ⟨a1, a2⟩ := hI h1
    obtain ⟨b1, b2⟩ := hJ h2
    unfold fxVal at *
    have hS := fxScale_pos
    constructor
    · rw [div_le_iff₀ hS] at *
      rcases le_total I.lo J.lo with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    · rw [le_div_iff₀ hS] at *
      rcases le_total I.hi J.hi with h | h
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right h]; linarith
  · exact hI
  · exact hJ

/-! ## Horner evaluation -/

/-- Horner evaluation `p₀/q₀ + X (p₁/q₁ + X (…))` with rational coefficients `(pᵢ, qᵢ)`. -/
@[expose] def hornerQ : List (ℤ × ℤ) → FIv → FIv
  | [], _ => ofInt 0
  | c :: cs, X => (ofFrac c.1 c.2).add (X.mul (hornerQ cs X))

/-- The real polynomial evaluated by `hornerQ`. -/
@[expose] noncomputable def hornerR : List (ℤ × ℤ) → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => (c.1 : ℝ) / c.2 + x * hornerR cs x

/-- Soundness of `hornerQ`. -/
theorem mem_hornerQ (cs : List (ℤ × ℤ)) {X : FIv} {x : ℝ} (hX : X.Mem x) :
    (hornerQ cs X).Mem (hornerR cs x) := by
  induction cs with
  | nil => simpa [hornerQ, hornerR] using mem_ofInt 0
  | cons c cs ih => exact mem_add (mem_ofFrac c.1 c.2) (mem_mul hX ih)

/-- Nested Horner evaluation `1 + X (1 + X (…)/k₁)/k₀` with exact integer divisions. -/
@[expose] def hornerN : List ℤ → FIv → FIv
  | [], _ => ofInt 1
  | k :: ks, X => (ofInt 1).add ((X.mul (hornerN ks X)).divInt k)

/-- The real polynomial evaluated by `hornerN`. -/
@[expose] noncomputable def hornerNR : List ℤ → ℝ → ℝ
  | [], _ => 1
  | k :: ks, x => 1 + x * hornerNR ks x / k

/-- Soundness of `hornerN`. -/
theorem mem_hornerN (ks : List ℤ) {X : FIv} {x : ℝ} (hX : X.Mem x) :
    (hornerN ks X).Mem (hornerNR ks x) := by
  induction ks with
  | nil => exact mem_one
  | cons k ks ih => exact mem_add mem_one (mem_divInt (mem_mul hX ih) k)

end FIv

/-! ## Alternating Taylor bounds for `arctan` -/

/-- The Taylor sum `S_N(u) = Σ_{k<N} (-1)^k u^{2k+1}/(2k+1)` of `arctan`. -/
@[expose] noncomputable def atanSeries (N : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, (-1) ^ k * u ^ (2 * k + 1) / (2 * k + 1)

/-- The derivative of `S_N` is the geometric sum `Σ_{k<N} (-u²)^k`. -/
theorem hasDerivAt_atanSeries (N : ℕ) (u : ℝ) :
    HasDerivAt (atanSeries N) (∑ k ∈ Finset.range N, (-u ^ 2) ^ k) u := by
  have h : ∀ k ∈ Finset.range N, HasDerivAt
      (fun u : ℝ => (-1) ^ k * u ^ (2 * k + 1) / (2 * k + 1)) ((-u ^ 2) ^ k) u := by
    intro k _
    have h := ((hasDerivAt_pow (2 * k + 1) u).const_mul ((-1 : ℝ) ^ k)).div_const
      (2 * k + 1 : ℝ)
    convert h using 1
    have hk : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    rw [neg_pow, ← pow_mul]
    push_cast
    field_simp
  have := HasDerivAt.sum h
  unfold atanSeries
  convert this using 1
  ext v
  simp

/-- **Alternating bounds.** For `u ≥ 0`, `(-1)^N (arctan u - S_N(u)) ≥ 0`: even truncations
are lower bounds and odd truncations upper bounds. -/
theorem atanSeries_bound (N : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ (-1) ^ N * (arctan u - atanSeries N u) := by
  set g : ℝ → ℝ := fun v => (-1) ^ N * (arctan v - atanSeries N v) with hgdef
  have hg : ∀ x, HasDerivAt g ((x ^ 2) ^ N / (1 + x ^ 2)) x := by
    intro x
    have h := ((hasDerivAt_arctan x).sub (hasDerivAt_atanSeries N x)).const_mul
      ((-1 : ℝ) ^ N)
    convert h using 1
    have hgeom := geom_sum_mul (-x ^ 2) N
    have hp : (1 + x ^ 2) ≠ 0 := by positivity
    have e : ((-1 : ℝ) ^ N) * (-x ^ 2) ^ N = (x ^ 2) ^ N := by
      rw [← mul_pow]; ring
    have hG : ∑ i ∈ Finset.range N, (-x ^ 2) ^ i = (1 - (-x ^ 2) ^ N) / (1 + x ^ 2) := by
      field_simp
      linear_combination (-1 : ℝ) * hgeom
    rw [hG, ← e]
    field_simp
    ring
  have hmono : Monotone g := monotone_of_deriv_nonneg
    (fun x => (hg x).differentiableAt) (fun x => by rw [(hg x).deriv]; positivity)
  have h0 : g 0 = 0 := by simp [hgdef, atanSeries]
  have := hmono hu
  rw [h0] at this
  exact this

/-- **Half-angle reduction.** `arctan y = 2 arctan (y / (1 + √(1 + y²)))` for every real `y`. -/
theorem arctan_eq_two_mul_red (y : ℝ) :
    arctan y = 2 * arctan (y * (1 + √(1 + y ^ 2))⁻¹) := by
  set s := √(1 + y ^ 2) with hsdef
  have hs2 : s ^ 2 = 1 + y ^ 2 := Real.sq_sqrt (by positivity)
  have hys : |y| < s := by
    rw [hsdef, Real.lt_sqrt (abs_nonneg y), sq_abs]; linarith
  have hpos : 0 < 1 + s := by linarith [abs_nonneg y]
  have hy := abs_lt.mp hys
  have hu1 : -1 < y * (1 + s)⁻¹ := by
    rw [← div_eq_mul_inv, lt_div_iff₀ hpos]; linarith
  have hu2 : y * (1 + s)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_iff₀ hpos]; linarith
  rw [two_mul_arctan hu1 hu2]
  congr 1
  have h1 : 1 - (y * (1 + s)⁻¹) ^ 2 = 2 / (1 + s) := by
    field_simp
    linear_combination hs2
  rw [h1]
  field_simp

namespace FIv

/-! ## `arctan` -/

/-- Coefficients of `S_12` (lower Taylor bound) as polynomial in `u²` after factoring `u`. -/
@[expose] def atanLoCoeffs : List (ℤ × ℤ) :=
  [(1, 1), (-1, 3), (1, 5), (-1, 7), (1, 9), (-1, 11), (1, 13), (-1, 15), (1, 17), (-1, 19),
    (1, 21), (-1, 23)]

/-- Coefficients of `S_13` (upper Taylor bound) as polynomial in `u²` after factoring `u`. -/
@[expose] def atanHiCoeffs : List (ℤ × ℤ) := atanLoCoeffs ++ [(1, 25)]

/-- `u · P_lo(u²) = S_12(u)`. -/
theorem atanLo_eq (u : ℝ) : u * hornerR atanLoCoeffs (u ^ 2) = atanSeries 12 u := by
  simp only [atanLoCoeffs, hornerR, atanSeries, Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  ring

/-- `u · P_hi(u²) = S_13(u)`. -/
theorem atanHi_eq (u : ℝ) : u * hornerR atanHiCoeffs (u ^ 2) = atanSeries 13 u := by
  simp only [atanHiCoeffs, atanLoCoeffs, List.cons_append, List.nil_append, hornerR,
    atanSeries, Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  ring

/-- Enclosure of `arctan u` for `u` in a nonnegative enclosure `R` (Taylor bounds `S_12`,
`S_13`; accurate when `R ⊆ [0, 0.42]`). -/
@[expose] def atanSmall (R : FIv) : FIv :=
  ⟨(R.mul (hornerQ atanLoCoeffs R.sq)).lo, (R.mul (hornerQ atanHiCoeffs R.sq)).hi,
    R.ok && decide (0 ≤ R.lo) && (R.mul (hornerQ atanLoCoeffs R.sq)).ok &&
      (R.mul (hornerQ atanHiCoeffs R.sq)).ok⟩

/-- Soundness of `atanSmall`. -/
theorem mem_atanSmall {R : FIv} {u : ℝ} (hR : R.Mem u) : (atanSmall R).Mem (arctan u) := by
  intro hok
  simp only [atanSmall, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hRok, h0⟩, hA⟩, hB⟩ := hok
  have hu : 0 ≤ u := by
    obtain ⟨a1, _⟩ := (mem_iff R u).mp hR hRok
    have : (0 : ℝ) ≤ R.lo := by exact_mod_cast h0
    have hS := fxScale_pos
    nlinarith
  obtain ⟨a1, _⟩ := mem_mul hR (mem_hornerQ atanLoCoeffs (mem_sq hR)) hA
  obtain ⟨_, b2⟩ := mem_mul hR (mem_hornerQ atanHiCoeffs (mem_sq hR)) hB
  rw [atanLo_eq] at a1
  rw [atanHi_eq] at b2
  have l := atanSeries_bound 12 hu
  have r := atanSeries_bound 13 hu
  norm_num at l r
  exact ⟨by simpa [atanSmall] using a1.trans l, by simpa [atanSmall] using r.trans b2⟩

/-- The half-angle reduction `y ↦ y / (1 + √(1 + y²))` on enclosures. -/
@[expose] def red (Y : FIv) : FIv := Y.mul ((ofInt 1).add ((ofInt 1).add Y.sq).sqrt).inv

/-- Soundness of the reduction. -/
theorem mem_red {Y : FIv} {y : ℝ} (hY : Y.Mem y) : (red Y).Mem (y * (1 + √(1 + y ^ 2))⁻¹) :=
  mem_mul hY (mem_inv (mem_add mem_one (mem_sqrt (mem_add mem_one (mem_sq hY)))))

/-- The enclosure `π/2`. -/
@[expose] def halfPi : FIv := pi.mul (ofFrac 1 2)

/-- Soundness of `halfPi`. -/
theorem mem_halfPi : halfPi.Mem (Real.pi / 2) := by
  have := mem_mul mem_pi (mem_ofFrac 1 2)
  simpa [halfPi, div_eq_mul_inv] using this

/-- Enclosure of `arctan (n/2³²)` intended for `n ≥ 0` (sound for every `n`): reduction
`π/2 - arctan (1/t)` for `t > 1`, then one half-angle step and `atanSmall`. -/
@[expose] def atanNN (n : ℤ) : FIv :=
  if n ≤ fxScale then (ofInt 2).mul (atanSmall (red (thin n)))
  else halfPi.sub ((ofInt 2).mul (atanSmall (red (thin n).inv)))

/-- Soundness of `atanNN`. -/
theorem mem_atanNN (n : ℤ) : (atanNN n).Mem (arctan (fxVal n)) := by
  unfold atanNN
  split_ifs with h
  · rw [arctan_eq_two_mul_red (fxVal n)]
    simpa using mem_mul (mem_ofInt 2) (mem_atanSmall (mem_red (mem_thin n)))
  · have hn : 0 < fxVal n := by
      unfold fxVal
      have : (0 : ℝ) < n := by
        have : (0 : ℤ) < n := lt_trans fxScale_pos' (not_le.mp h)
        exact_mod_cast this
      exact div_pos this fxScale_pos
    have e : arctan (fxVal n) = Real.pi / 2 - arctan (fxVal n)⁻¹ := by
      rw [arctan_inv_of_pos hn]; ring
    rw [e, arctan_eq_two_mul_red (fxVal n)⁻¹]
    have := mem_mul (mem_ofInt 2) (mem_atanSmall (mem_red (mem_inv (mem_thin n))))
    push_cast at this
    exact mem_sub mem_halfPi this

/-- Enclosure of `arctan (n/2³²)` at a fixed-point number, using oddness for `n < 0`. -/
@[expose] def atanPt (n : ℤ) : FIv := if 0 ≤ n then atanNN n else (atanNN (-n)).neg

/-- Soundness of `atanPt`. -/
theorem mem_atanPt (n : ℤ) : (atanPt n).Mem (arctan (fxVal n)) := by
  unfold atanPt
  split_ifs
  · exact mem_atanNN n
  · have e : arctan (fxVal n) = -arctan (fxVal (-n)) := by
      simp [fxVal, neg_div, arctan_neg]
    rw [e]
    exact mem_neg (mem_atanNN (-n))

/-- Interval `arctan`: a lower bound at `lo` and an upper bound at `hi` (monotonicity).
Valid for all finite inputs. -/
@[expose] def arctan (I : FIv) : FIv :=
  ⟨(atanPt I.lo).lo, (atanPt I.hi).hi, I.ok && (atanPt I.lo).ok && (atanPt I.hi).ok⟩

/-- Soundness of the interval `arctan`. -/
theorem mem_arctan {I : FIv} {x : ℝ} (h : I.Mem x) : (FIv.arctan I).Mem (Real.arctan x) := by
  refine mem_mono_endpoints arctan_mono h ?_ ?_ ?_ <;> intro hok <;>
    simp only [FIv.arctan, Bool.and_eq_true] at hok
  · exact hok.1.1
  · exact (mem_atanPt I.lo hok.1.2).1
  · exact (mem_atanPt I.hi hok.2).2

/-! ## `arcsin` -/

/-- Enclosure of `t / √(1 - t²)` at the fixed-point number `t = n/2³²`. -/
@[expose] def asinArg (n : ℤ) : FIv := (thin n).mul ((ofInt 1).sub (thin n).sq).sqrt.inv

/-- Enclosure of `arcsin (n/2³²)`, sound when `|n/2³²| < 1`. -/
@[expose] def asinPt (n : ℤ) : FIv := FIv.arctan (asinArg n)

/-- Soundness of `asinPt` inside `(-1, 1)`. -/
theorem mem_asinPt {n : ℤ} (h1 : -1 < fxVal n) (h2 : fxVal n < 1) :
    (asinPt n).Mem (arcsin (fxVal n)) := by
  rw [arcsin_eq_arctan ⟨h1, h2⟩, div_eq_mul_inv]
  exact mem_arctan (mem_mul (mem_thin n) (mem_inv (mem_sqrt (mem_sub mem_one
    (mem_sq (mem_thin n))))))

/-- Interval `arcsin`, valid only when the enclosure lies strictly inside `(-1, 1)`. -/
@[expose] def arcsin (I : FIv) : FIv :=
  ⟨(asinPt I.lo).lo, (asinPt I.hi).hi,
    I.ok && decide (-fxScale < I.lo) && decide (I.hi < fxScale) && (asinPt I.lo).ok &&
      (asinPt I.hi).ok⟩

/-- Soundness of the interval `arcsin`. -/
theorem mem_arcsin {I : FIv} {x : ℝ} (h : I.Mem x) : (FIv.arcsin I).Mem (Real.arcsin x) := by
  have hS := fxScale_pos
  have key : (FIv.arcsin I).ok = true → -1 < fxVal I.lo ∧ fxVal I.hi < 1 ∧
      fxVal I.lo ≤ fxVal I.hi := by
    intro hok
    simp only [FIv.arcsin, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨a1, a2⟩ := h hok.1.1.1.1
    have l : (-fxScale : ℝ) < I.lo := by exact_mod_cast hok.1.1.1.2
    have r : (I.hi : ℝ) < fxScale := by exact_mod_cast hok.1.1.2
    refine ⟨?_, ?_, a1.trans a2⟩
    · unfold fxVal; rw [lt_div_iff₀ hS]; linarith
    · unfold fxVal; rw [div_lt_iff₀ hS]; linarith
  refine mem_mono_endpoints monotone_arcsin h ?_ ?_ ?_ <;> intro hok
  · simp only [FIv.arcsin, Bool.and_eq_true] at hok; exact hok.1.1.1.1
  · obtain ⟨k1, k2, k3⟩ := key hok
    simp only [FIv.arcsin, Bool.and_eq_true] at hok
    exact (mem_asinPt k1 (lt_of_le_of_lt k3 k2) hok.1.2).1
  · obtain ⟨k1, k2, k3⟩ := key hok
    simp only [FIv.arcsin, Bool.and_eq_true] at hok
    exact (mem_asinPt (lt_of_lt_of_le k1 k3) k2 hok.2).2

end FIv

/-! ## `cosh` and `sinh` -/

/-- The degree-13 exponential Taylor polynomial `Σ_{m<14} x^m/m!`. -/
@[expose] noncomputable def expPoly (x : ℝ) : ℝ :=
  ∑ m ∈ Finset.range 14, x ^ m / m.factorial

/-- The exponential remainder for `|x| ≤ 1` is below one unit of `2⁻³²`. -/
theorem exp_sub_expPoly {x : ℝ} (hx : |x| ≤ 1) : |exp x - expPoly x| ≤ 1 / fxScale := by
  have h := Real.exp_bound hx (n := 14) (by norm_num)
  have hp : |x| ^ 14 ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
  have hc : ((Nat.succ 14 : ℕ) : ℝ) / ((Nat.factorial 14 : ℕ) * (14 : ℕ)) ≤ 1 / fxScale := by
    rw [fxScale_real]; norm_num [Nat.factorial]
  have hc0 : (0 : ℝ) ≤ ((Nat.succ 14 : ℕ) : ℝ) / ((Nat.factorial 14 : ℕ) * (14 : ℕ)) := by
    positivity
  unfold expPoly
  calc _ ≤ _ := h
    _ ≤ 1 * (((Nat.succ 14 : ℕ) : ℝ) / ((Nat.factorial 14 : ℕ) * (14 : ℕ))) :=
        mul_le_mul_of_nonneg_right hp hc0
    _ ≤ _ := by rw [one_mul]; exact hc

namespace FIv

/-- Nested Horner divisors `(2k-1)(2k)` of the even part `Σ_{k≤6} v^k/(2k)!`. -/
@[expose] def coshKs : List ℤ := [2, 12, 30, 56, 90, 132]

/-- Nested Horner divisors `(2k)(2k+1)` of the odd part `Σ_{k≤6} v^k/(2k+1)!`. -/
@[expose] def sinhKs : List ℤ := [6, 20, 42, 72, 110, 156]

/-- The even part of `expPoly` in nested Horner form. -/
theorem coshKs_eq (x : ℝ) : hornerNR coshKs (x ^ 2) = (expPoly x + expPoly (-x)) / 2 := by
  simp only [coshKs, hornerNR, expPoly, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.factorial]
  push_cast
  ring

/-- The odd part of `expPoly` in nested Horner form. -/
theorem sinhKs_eq (x : ℝ) : x * hornerNR sinhKs (x ^ 2) = (expPoly x - expPoly (-x)) / 2 := by
  simp only [sinhKs, hornerNR, expPoly, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.factorial]
  push_cast
  ring

/-- Enclosure of `cosh (n/2³²)`, valid only for `|n| ≤ 2³²`. -/
@[expose] def coshPt (n : ℤ) : FIv :=
  ⟨(hornerN coshKs (thin n).sq).lo - 1, (hornerN coshKs (thin n).sq).hi + 1,
    (hornerN coshKs (thin n).sq).ok && decide (-fxScale ≤ n) && decide (n ≤ fxScale)⟩

/-- Enclosure of `sinh (n/2³²)`, valid only for `|n| ≤ 2³²`. -/
@[expose] def sinhPt (n : ℤ) : FIv :=
  ⟨((thin n).mul (hornerN sinhKs (thin n).sq)).lo - 1,
    ((thin n).mul (hornerN sinhKs (thin n).sq)).hi + 1,
    ((thin n).mul (hornerN sinhKs (thin n).sq)).ok && decide (-fxScale ≤ n) &&
      decide (n ≤ fxScale)⟩

/-- If `J` encloses `p`, `K` is `J` widened by one unit (valid only if `J` is) and
`|f - p| ≤ 2⁻³²` whenever `K` is valid, then `K` encloses `f`. -/
theorem mem_widen {J K : FIv} {p f : ℝ} (hJ : J.Mem p) (hok : K.ok = true → J.ok = true)
    (hf : K.ok = true → |f - p| ≤ 1 / fxScale) (hlo : K.lo = J.lo - 1) (hhi : K.hi = J.hi + 1) :
    K.Mem f := by
  rw [mem_iff] at *
  intro hK
  obtain ⟨a1, a2⟩ := hJ (hok hK)
  have hf := hf hK
  rw [hlo, hhi]
  have hS := fxScale_pos
  have hf' := abs_le.mp hf
  have e : (fxScale : ℝ) * (1 / fxScale) = 1 := by field_simp
  have k1 : fxScale * (f - p) ≥ fxScale * (-(1 / fxScale)) :=
    mul_le_mul_of_nonneg_left hf'.1 hS.le
  have k2 : fxScale * (f - p) ≤ fxScale * (1 / fxScale) :=
    mul_le_mul_of_nonneg_left hf'.2 hS.le
  push_cast
  constructor <;> nlinarith

/-- `|n/2³²| ≤ 1` from the integer bounds. -/
theorem abs_fxVal_le_one {n : ℤ} (h1 : -fxScale ≤ n) (h2 : n ≤ fxScale) : |fxVal n| ≤ 1 := by
  have hS := fxScale_pos
  have l : (-fxScale : ℝ) ≤ n := by exact_mod_cast h1
  have r : (n : ℝ) ≤ fxScale := by exact_mod_cast h2
  unfold fxVal
  rw [abs_le, le_div_iff₀ hS, div_le_iff₀ hS]
  constructor <;> linarith

/-- Soundness of `coshPt`. -/
theorem mem_coshPt (n : ℤ) : (coshPt n).Mem (Real.cosh (fxVal n)) := by
  have hJ := mem_hornerN coshKs (mem_sq (mem_thin n))
  rw [coshKs_eq] at hJ
  refine mem_widen hJ ?_ ?_ rfl rfl
  · intro hok; simp only [coshPt, Bool.and_eq_true] at hok; exact hok.1.1
  intro hok
  simp only [coshPt, Bool.and_eq_true, decide_eq_true_eq] at hok
  have hx := abs_fxVal_le_one hok.1.2 hok.2
  have hx' : |-fxVal n| ≤ 1 := by rwa [abs_neg]
  have a := abs_le.mp (exp_sub_expPoly hx)
  have b := abs_le.mp (exp_sub_expPoly hx')
  rw [Real.cosh_eq, abs_le]
  constructor <;> linarith [a.1, a.2, b.1, b.2]

/-- Soundness of `sinhPt`. -/
theorem mem_sinhPt (n : ℤ) : (sinhPt n).Mem (Real.sinh (fxVal n)) := by
  have hJ := mem_mul (mem_thin n) (mem_hornerN sinhKs (mem_sq (mem_thin n)))
  rw [sinhKs_eq] at hJ
  refine mem_widen hJ ?_ ?_ rfl rfl
  · intro hok; simp only [sinhPt, Bool.and_eq_true] at hok; exact hok.1.1
  intro hok
  simp only [sinhPt, Bool.and_eq_true, decide_eq_true_eq] at hok
  have hx := abs_fxVal_le_one hok.1.2 hok.2
  have hx' : |-fxVal n| ≤ 1 := by rwa [abs_neg]
  have a := abs_le.mp (exp_sub_expPoly hx)
  have b := abs_le.mp (exp_sub_expPoly hx')
  rw [Real.sinh_eq, abs_le]
  constructor <;> linarith [a.1, a.2, b.1, b.2]

/-- Interval `sinh` (increasing; endpoint-wise), valid only for enclosures in `[-1, 1]`. -/
@[expose] def sinh (I : FIv) : FIv :=
  ⟨(sinhPt I.lo).lo, (sinhPt I.hi).hi, I.ok && (sinhPt I.lo).ok && (sinhPt I.hi).ok⟩

/-- Soundness of the interval `sinh`. -/
theorem mem_sinh {I : FIv} {x : ℝ} (h : I.Mem x) : (FIv.sinh I).Mem (Real.sinh x) := by
  refine mem_mono_endpoints Real.sinh_strictMono.monotone h ?_ ?_ ?_ <;> intro hok <;>
    simp only [FIv.sinh, Bool.and_eq_true] at hok
  · exact hok.1.1
  · exact (mem_sinhPt I.lo hok.1.2).1
  · exact (mem_sinhPt I.hi hok.2).2

/-- Interval `cosh` (even, increasing in `|x|`), valid only for enclosures in `[-1, 1]`.
The lower end is taken at the endpoint nearest `0` (or is `1` if the enclosure straddles
`0`); the upper end is the larger of the two endpoint upper bounds. -/
@[expose] def cosh (I : FIv) : FIv :=
  ⟨if 0 ≤ I.lo then (coshPt I.lo).lo else if I.hi ≤ 0 then (coshPt I.hi).lo else fxScale,
    max (coshPt I.lo).hi (coshPt I.hi).hi,
    I.ok && (coshPt I.lo).ok && (coshPt I.hi).ok⟩

/-- Soundness of the interval `cosh`. -/
theorem mem_cosh {I : FIv} {x : ℝ} (h : I.Mem x) : (FIv.cosh I).Mem (Real.cosh x) := by
  intro hok
  simp only [FIv.cosh, Bool.and_eq_true] at hok
  obtain ⟨⟨hI, hL⟩, hU⟩ := hok
  obtain ⟨a1, a2⟩ := h hI
  obtain ⟨l1, l2⟩ := mem_coshPt I.lo hL
  obtain ⟨u1, u2⟩ := mem_coshPt I.hi hU
  have hS := fxScale_pos
  constructor
  · simp only [FIv.cosh]
    split_ifs with c1 c2
    · have : 0 ≤ fxVal I.lo := div_nonneg (by exact_mod_cast c1) hS.le
      refine l1.trans (Real.cosh_le_cosh.mpr ?_)
      rw [abs_of_nonneg this, abs_of_nonneg (this.trans a1)]
      exact a1
    · have : fxVal I.hi ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast c2) hS.le
      refine u1.trans (Real.cosh_le_cosh.mpr ?_)
      rw [abs_of_nonpos this, abs_of_nonpos (a2.trans this)]
      linarith
    · have : fxVal fxScale = 1 := by unfold fxVal; field_simp
      rw [this]
      exact Real.one_le_cosh x
  · simp only [FIv.cosh]
    have hmax : fxVal (coshPt I.lo).hi ≤ fxVal (max (coshPt I.lo).hi (coshPt I.hi).hi) ∧
        fxVal (coshPt I.hi).hi ≤ fxVal (max (coshPt I.lo).hi (coshPt I.hi).hi) := by
      unfold fxVal
      constructor <;> apply div_le_div_of_nonneg_right _ hS.le <;> exact_mod_cast
        (by omega)
    rcases le_or_gt |x| |fxVal I.hi| with c | c
    · exact (Real.cosh_le_cosh.mpr c).trans (u2.trans hmax.2)
    · have : |x| ≤ |fxVal I.lo| := by
        cases abs_cases (fxVal I.lo) <;> cases abs_cases (fxVal I.hi) <;>
          cases abs_cases x <;> linarith
      exact (Real.cosh_le_cosh.mpr this).trans (l2.trans hmax.1)

end FIv

/-! ## Sanity fixtures -/

/-- Accepted fixture: the enclosure of `arctan 1` is valid, contains `π/4` and has width at
most `43 · 2⁻³² < 1e-8`; hence both ends lie within `1e-8` of `π/4`. -/
theorem fixture_arctan_one : (FIv.arctan (FIv.ofInt 1)).ok = true ∧
    (FIv.arctan (FIv.ofInt 1)).hi - (FIv.arctan (FIv.ofInt 1)).lo ≤ 43 ∧
    (FIv.arctan (FIv.ofInt 1)).Mem (Real.pi / 4) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  have := FIv.mem_arctan (FIv.mem_ofInt 1)
  simpa [Real.arctan_one] using this

/-- Accepted fixture: large arguments (`arctan 10⁴`, via `π/2 - arctan 10⁻⁴`) are valid and
tight. -/
theorem fixture_arctan_large : (FIv.arctan (FIv.ofInt 10000)).ok = true ∧
    (FIv.arctan (FIv.ofInt 10000)).hi - (FIv.arctan (FIv.ofInt 10000)).lo ≤ 43 := by
  decide +kernel

/-- Accepted fixture: the enclosure of `arcsin (1/2)` is valid, contains `π/6` and has width
at most `43 · 2⁻³²`. -/
theorem fixture_arcsin_half : (FIv.arcsin (FIv.ofFrac 1 2)).ok = true ∧
    (FIv.arcsin (FIv.ofFrac 1 2)).hi - (FIv.arcsin (FIv.ofFrac 1 2)).lo ≤ 43 ∧
    (FIv.arcsin (FIv.ofFrac 1 2)).Mem (Real.pi / 6) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  have := FIv.mem_arcsin (FIv.mem_ofFrac 1 2)
  have e : Real.arcsin 2⁻¹ = Real.pi / 6 := by
    rw [← one_div, ← Real.sin_pi_div_six, Real.arcsin_sin] <;> linarith [Real.pi_pos]
  simpa [e] using this

/-- Accepted fixture: `arcsin` near the edge of its domain (`x = 0.99`) is still tight. -/
theorem fixture_arcsin_edge : (FIv.arcsin (FIv.ofFrac 99 100)).ok = true ∧
    (FIv.arcsin (FIv.ofFrac 99 100)).hi - (FIv.arcsin (FIv.ofFrac 99 100)).lo ≤ 43 := by
  decide +kernel

/-- Accepted fixture: the enclosure of `cosh 1` is valid with width at most `5 · 2⁻³²`. -/
theorem fixture_cosh_one : (FIv.cosh (FIv.ofInt 1)).ok = true ∧
    (FIv.cosh (FIv.ofInt 1)).hi - (FIv.cosh (FIv.ofInt 1)).lo ≤ 5 ∧
    (FIv.cosh (FIv.ofInt 1)).Mem (Real.cosh 1) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  simpa using FIv.mem_cosh (FIv.mem_ofInt 1)

/-- Accepted fixture: the enclosure of `sinh 1` is valid with width at most `5 · 2⁻³²`. -/
theorem fixture_sinh_one : (FIv.sinh (FIv.ofInt 1)).ok = true ∧
    (FIv.sinh (FIv.ofInt 1)).hi - (FIv.sinh (FIv.ofInt 1)).lo ≤ 5 ∧
    (FIv.sinh (FIv.ofInt 1)).Mem (Real.sinh 1) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  simpa using FIv.mem_sinh (FIv.mem_ofInt 1)

/-- Degenerate fixture: `cosh` of an enclosure straddling `0` has lower end exactly `1`. -/
theorem fixture_cosh_straddle :
    (FIv.cosh ⟨-fxScale / 2, fxScale / 3, true⟩).ok = true ∧
    (FIv.cosh ⟨-fxScale / 2, fxScale / 3, true⟩).lo = fxScale := by
  decide +kernel

/-- Rejected fixture: `arcsin` of an enclosure containing `1` is invalid. -/
theorem fixture_arcsin_rejected : (FIv.arcsin ⟨fxScale / 2, fxScale, true⟩).ok = false := by
  decide +kernel

/-- Rejected fixture: `cosh` (and `sinh`) of `[2, 3]` (outside `[-1, 1]`) is invalid. -/
theorem fixture_cosh_rejected : (FIv.cosh ⟨2 * fxScale, 3 * fxScale, true⟩).ok = false ∧
    (FIv.sinh ⟨2 * fxScale, 3 * fxScale, true⟩).ok = false := by
  decide +kernel

/-- Fixture for `meet`: intersecting `[0, 1]` with `[1/2, 2]` gives `[1/2, 1]`; disjoint
valid enclosures give an invalid result. -/
theorem fixture_meet :
    (FIv.meet ⟨0, fxScale, true⟩ ⟨fxScale / 2, 2 * fxScale, true⟩).lo = fxScale / 2 ∧
    (FIv.meet ⟨0, fxScale, true⟩ ⟨fxScale / 2, 2 * fxScale, true⟩).hi = fxScale ∧
    (FIv.meet ⟨0, fxScale, true⟩ ⟨fxScale / 2, 2 * fxScale, true⟩).ok = true ∧
    (FIv.meet (FIv.ofInt 0) (FIv.ofInt 1)).ok = false := by
  decide +kernel

/-- Fixture for `pi`: the enclosure has width one unit of `2⁻³²`. -/
theorem fixture_pi : FIv.pi.hi - FIv.pi.lo = 1 := by decide +kernel

end PlasmaLean.Certificates.ValidatedQuadrature
