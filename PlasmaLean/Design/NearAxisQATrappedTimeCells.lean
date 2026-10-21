/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedCells

/-!
# Cell certificates for the bounce time and the kick-amplitude integral (exact QA)

Companion to `Design/NearAxisQATrappedCells` (precession cells) and
`notes/theory/trapped-alpha-status.md` §3 item 3. Model only: the exactly quasi-axisymmetric
member `exactQA` of the reactor near-axis family, vacuum Boozer guiding-centre equations.

Along an exact-QA orbit with constants of motion `ψ₀, B_t = E/μ`, the drift factor
`A = μ/q + qρ²B/m` is an explicit function of `x = |ψ − ψ₀|`: from energy conservation
`A · qB = 2E − μB`, so `A = (E/q)(2B_t − B)/(B_t B)` with `B = BsR x B_t`. In units of `10⁶ s⁻¹`
this is `AmR x B_t = (7/4)(2B_t − B)/(B_t B)` (`E/q = 1.75 × 10⁶ V`).

The two integrals bounded here are the **bounce time** `∫ dt` and the **amplitude integral**
`J = ∫ A (2ψ/B₀) dt` (the near-QA kick amplitude is `|g| = q A (2ψ/B₀) · 2|b₁|`). With the same
flank / bottom split at `|θ| = δ = 3/5` as the precession certificate:

* flank (`|θ| ≥ δ`): `ẋ = A |∂_θB|`, so `dt = dx / (A |∂_θB|)` and `A (2ψ/B₀) dt = w dx / |∂_θB|`
  (`w = 2ψ/B₀`; `A` cancels). `flankCellT` encloses `1 / (AmR · |∂_θB|)` (microseconds per unit
  of `x`) and `w / |∂_θB|` on an `x`-cell;
* bottom (`|θ| ≤ δ`): `|θ̇| = A (−∂_ψB) / ratR` (`ratR = Ω/|θ̇|`), so
  `dt = ratR dθ / (A (−∂_ψB))` and `A w dt = w ratR dθ / (−∂_ψB)`. `bottomCellT` encloses
  `ratR / (AmR (−∂_ψB))` and `w ratR / (−∂_ψB)`.

No singular integral occurs: on the flank `|∂_θB| ≥ sin δ · (…) > 0`, and at the bottom `θ̇` is
bounded away from zero (`ρ ≠ 0` there).

`timeBoxOk P T Pμ J` runs both legs over the 100 cells of `[0, 5/2]` and checks
`(1/20) Σ M_t + (6/5)(M_bt^in + M_bt^out) ≤ Pμ` (microseconds) and the same for `J`.
`timeBox_sound` turns a passing box into real leg bounds (`TimeLegBounds`) for every
`(ψ₀, B_t)` in the box; `time_cert_of_grid` covers the start window by the uniform `4 × 4` grid
`TPB j × TTB l` (kernel checks in `NearAxisQATrappedTimeRows`).
-/
public section
noncomputable section
namespace PlasmaLean.Design.NearAxisQATrappedCells
open PlasmaLean.Certificates.ValidatedQuadrature Real Set
open FIvX

/-! ## Real formulas -/

/-- The drift factor in units of `10⁶ s⁻¹`: `A/10⁶ = (7/4)(2B_t − B)/(B_t B)`, `B = BsR x B_t`. -/
@[expose] def AmR (x Bt : ℝ) : ℝ := 7 / 4 * (2 * Bt - BsR x Bt) * (Bt * BsR x Bt)⁻¹

/-! ## Interval versions -/

/-- Interval drift factor. -/
@[expose] def AmI (X T : FIv) : FIv :=
  dv ((C 7 4).mul (((C 2 1).mul T).sub (BsI X T))) (T.mul (BsI X T))

/-- Soundness of `AmI`. -/
theorem mem_AmI {X T : FIv} {x b : ℝ} (hX : X.Mem x) (hT : T.Mem b) : (AmI X T).Mem (AmR x b) := by
  have h1 := mem_BsI hX hT
  unfold AmI AmR
  fiv_mem

/-- Flank cosine clamped to `[0, cos δ]`. -/
@[expose] def flankC (inner : Bool) (X P T : FIv) : FIv := meetLo (meetHi (cI inner X P T) cdHi) 0

/-- Flank `|sin θ|`, clamped below by `sin δ`. -/
@[expose] def flankS (inner : Bool) (X P T : FIv) : FIv :=
  meetLo ((C 1 1).sub (flankC inner X P T).sq).sqrt sdLo

/-- Flank `|∂_θB|`. -/
@[expose] def flankDen (inner : Bool) (X P T : FIv) : FIv :=
  denI inner X P (flankC inner X P T) (flankS inner X P T)

/-- Flank time density `1 / (A_μ |∂_θB|)`. -/
@[expose] def flankTI (inner : Bool) (X P T : FIv) : FIv :=
  dv (C 1 1) ((AmI X T).mul (flankDen inner X P T))

/-- Flank amplitude density `w / |∂_θB|`. -/
@[expose] def flankJI (inner : Bool) (X P T : FIv) : FIv :=
  dv (wI inner X P) (flankDen inner X P T)

/-- **Flank time cell** on `X`: validity, scaled bound on the time density, scaled bound on the
amplitude density (`(true, 0, 0)` for a dead cell, where no orbit point has `|θ| ≥ δ`). -/
@[expose] def flankCellT (inner : Bool) (X P T : FIv) : Bool × ℤ × ℤ :=
  if (cI inner X P T).ok && decide (cdHi < (cI inner X P T).lo) then (true, 0, 0) else
    ((flankTI inner X P T).ok && (flankJI inner X P T).ok, (flankTI inner X P T).hi,
      (flankJI inner X P T).hi)

/-- Bottom cosine clamped to `[cos δ, 1]`. -/
@[expose] def bottomC (inner : Bool) (X P T : FIv) : FIv :=
  meetHi (meetLo (cI inner X P T) cdLo) fxScale

/-- Bottom time density `ratR / (A_μ (−∂_ψB))`. -/
@[expose] def bottomTI (inner : Bool) (X P T : FIv) : FIv :=
  dv (ratI inner X P T (bottomC inner X P T)) ((AmI X T).mul (numI inner X P (bottomC inner X P T)))

/-- Bottom amplitude density `w ratR / (−∂_ψB)`. -/
@[expose] def bottomJI (inner : Bool) (X P T : FIv) : FIv :=
  dv ((wI inner X P).mul (ratI inner X P T (bottomC inner X P T)))
    (numI inner X P (bottomC inner X P T))

/-- **Bottom time cell** on `X`: validity and scaled bounds on the two bottom densities
(`(true, 0, 0)` for a dead cell, where no orbit point has `|θ| ≤ δ`). -/
@[expose] def bottomCellT (inner : Bool) (X P T : FIv) : Bool × ℤ × ℤ :=
  if (cI inner X P T).ok && (decide ((cI inner X P T).hi < cdLo) ||
      decide (fxScale < (cI inner X P T).lo)) then (true, 0, 0) else
    ((bottomTI inner X P T).ok && (bottomJI inner X P T).ok, (bottomTI inner X P T).hi,
      (bottomJI inner X P T).hi)

/-- A valid quotient `I/J` with `I ∋ u`, `J ∋ v` gives `u ≤ hi · v` and `v > 0`. -/
theorem le_of_dv {I J : FIv} {u v : ℝ} (hok : (dv I J).ok = true) (hu : I.Mem u) (hv : J.Mem v) :
    u ≤ fxVal (dv I J).hi * v ∧ 0 < v := by
  have hpos := dv_pos hok hv
  have h := (mem_dv hu hv) hok
  refine ⟨?_, hpos⟩
  have := h.2
  rw [← div_eq_mul_inv, div_le_iff₀ hpos] at this
  exact this

/-- **Soundness of a flank time cell.** For an orbit point with `x ∈ X`, constants in `P × T`
and `|θ| ≥ δ`: `1 ≤ M_t · A_μ |∂_θB|` and `w ≤ M_J · |∂_θB|`. -/
theorem flankCellT_sound {inner : Bool} {X P T : FIv} {x p b c : ℝ}
    (hok : (flankCellT inner X P T).1 = true) (hX : X.Mem x) (hP : P.Mem p) (hT : T.Mem b)
    (hrel : OrbitRel inner x p b c) (hc : c ≤ cos (3 / 5)) :
    (1 ≤ fxVal (flankCellT inner X P T).2.1 * (AmR x b * denR inner p x c (√(1 - c ^ 2))) ∧
      0 < AmR x b * denR inner p x c (√(1 - c ^ 2))) ∧
      wR inner p x ≤ fxVal (flankCellT inner X P T).2.2 * denR inner p x c (√(1 - c ^ 2)) := by
  have hcI := mem_cI (inner := inner) hX hP hT
  rw [cR_eq hrel] at hcI
  unfold flankCellT at hok ⊢
  split_ifs at hok ⊢ with hdead
  · exfalso
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hdead
    obtain ⟨h1, _⟩ := hcI hdead.1
    have : fxVal cdHi < fxVal (cI inner X P T).lo := by
      unfold fxVal; exact div_lt_div_of_pos_right (by exact_mod_cast hdead.2) fxScale_pos
    linarith [le_cdHi]
  · simp only [Bool.and_eq_true] at hok
    obtain ⟨ht, hj⟩ := hok
    have hc2 : (flankC inner X P T).Mem c :=
      mem_meetLo (mem_meetHi hcI (hc.trans le_cdHi)) (by simp [fxVal, hrel.c_nonneg])
    have hs : (flankS inner X P T).Mem (√(1 - c ^ 2)) :=
      mem_meetLo (FIv.mem_sqrt (FIv.mem_sub (mem_C (by norm_num)) (FIv.mem_sq hc2)))
        (sdLo_le.trans (sqrt_one_sub_sq_ge hrel.c_nonneg hc))
    have hden : (flankDen inner X P T).Mem (denR inner p x c (√(1 - c ^ 2))) :=
      mem_denI hX hP hc2 hs
    have hA := mem_AmI hX hT
    have h1 : (C 1 1).Mem 1 := mem_C (by norm_num)
    exact ⟨le_of_dv ht h1 (FIv.mem_mul hA hden), (le_of_dv hj (mem_wI hX hP) hden).1⟩

/-- **Soundness of a bottom time cell.** For an orbit point with `x ∈ X`, constants in `P × T`
and `|θ| ≤ δ`: `ratR ≤ M_t · A_μ (−∂_ψB)` and `w ratR ≤ M_J · (−∂_ψB)`. -/
theorem bottomCellT_sound {inner : Bool} {X P T : FIv} {x p b c : ℝ}
    (hok : (bottomCellT inner X P T).1 = true) (hX : X.Mem x) (hP : P.Mem p) (hT : T.Mem b)
    (hrel : OrbitRel inner x p b c) (hc : cos (3 / 5) ≤ c) :
    (ratR inner p x b c ≤ fxVal (bottomCellT inner X P T).2.1 * (AmR x b * numR inner p x c) ∧
      0 < AmR x b * numR inner p x c) ∧
      (wR inner p x * ratR inner p x b c ≤ fxVal (bottomCellT inner X P T).2.2 * numR inner p x c ∧
      0 < numR inner p x c) := by
  have hcI := mem_cI (inner := inner) hX hP hT
  rw [cR_eq hrel] at hcI
  unfold bottomCellT at hok ⊢
  split_ifs at hok ⊢ with hdead
  · exfalso
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hdead
    obtain ⟨h1, h2⟩ := hcI hdead.1
    rcases hdead.2 with h | h
    · have : fxVal (cI inner X P T).hi < fxVal cdLo := by
        unfold fxVal; exact div_lt_div_of_pos_right (by exact_mod_cast h) fxScale_pos
      linarith [cdLo_le]
    · have : (1 : ℝ) < fxVal (cI inner X P T).lo := by
        unfold fxVal
        rw [lt_div_iff₀ fxScale_pos, one_mul]; exact_mod_cast h
      linarith [hrel.c_le]
  · simp only [Bool.and_eq_true] at hok
    obtain ⟨ht, hj⟩ := hok
    have hc2 : (bottomC inner X P T).Mem c :=
      mem_meetHi (mem_meetLo hcI (cdLo_le.trans hc))
        (by rw [show fxVal fxScale = 1 by unfold fxVal; exact div_self fxScale_pos.ne']
            exact hrel.c_le)
    have hnum := mem_numI (inner := inner) hX hP hc2
    have hrat := mem_ratI (inner := inner) hX hP hT hc2
    have hA := mem_AmI hX hT
    exact ⟨le_of_dv ht hrat (FIv.mem_mul hA hnum),
      le_of_dv hj (FIv.mem_mul (mem_wI hX hP) hrat) hnum⟩

/-! ## Legs and boxes -/

/-- Run a leg over the first `n` cells: validity, the sums of the (nonnegative parts of the)
flank time and amplitude bounds, and the maxima of the two bottom bounds. -/
@[expose] def legLoopT (inner : Bool) (P T : FIv) : ℕ → Bool × ℤ × ℤ × ℤ × ℤ
  | 0 => (true, 0, 0, 0, 0)
  | n + 1 =>
    ((legLoopT inner P T n).1 && (flankCellT inner (cellX n) P T).1 &&
        (bottomCellT inner (cellX n) P T).1,
      (legLoopT inner P T n).2.1 + max 0 (flankCellT inner (cellX n) P T).2.1,
      (legLoopT inner P T n).2.2.1 + max 0 (flankCellT inner (cellX n) P T).2.2,
      max (legLoopT inner P T n).2.2.2.1 (bottomCellT inner (cellX n) P T).2.1,
      max (legLoopT inner P T n).2.2.2.2 (bottomCellT inner (cellX n) P T).2.2)

/-- Properties of `legLoopT`: all cells valid, the two sums, and the bottom maxima. -/
theorem legLoopT_spec (inner : Bool) (P T : FIv) (n : ℕ) (h : (legLoopT inner P T n).1 = true) :
    (∀ i < n, (flankCellT inner (cellX i) P T).1 = true ∧
      (bottomCellT inner (cellX i) P T).1 = true ∧
      (bottomCellT inner (cellX i) P T).2.1 ≤ (legLoopT inner P T n).2.2.2.1 ∧
      (bottomCellT inner (cellX i) P T).2.2 ≤ (legLoopT inner P T n).2.2.2.2) ∧
    (legLoopT inner P T n).2.1 =
      ∑ i ∈ Finset.range n, max 0 (flankCellT inner (cellX i) P T).2.1 ∧
    (legLoopT inner P T n).2.2.1 =
      ∑ i ∈ Finset.range n, max 0 (flankCellT inner (cellX i) P T).2.2 := by
  induction n with
  | zero => exact ⟨fun i hi => absurd hi (Nat.not_lt_zero i), rfl, rfl⟩
  | succ n ih =>
    simp only [legLoopT, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨ih1, ih2, ih3⟩ := ih h1
    refine ⟨fun i hi => ?_, by simp only [legLoopT]; rw [ih2, Finset.sum_range_succ],
      by simp only [legLoopT]; rw [ih3, Finset.sum_range_succ]⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
    · obtain ⟨a, b, c, d⟩ := ih1 i hi'
      exact ⟨a, b, le_trans c (le_max_left _ _), le_trans d (le_max_left _ _)⟩
    · subst hi'
      exact ⟨h2, h3, le_max_right _ _, le_max_right _ _⟩

/-- **The time box check**: both legs valid, and in scaled integers
`(1/20) Σ M_t + (6/5)(M_bt^in + M_bt^out) ≤ Pμ`, `(1/20) Σ M_J + (6/5)(M_bJ^in + M_bJ^out) ≤ J`. -/
@[expose] def timeBoxOk (P T : FIv) (Pμ J : ℤ) : Bool :=
  (legLoopT true P T 100).1 && (legLoopT false P T 100).1 &&
    decide ((legLoopT true P T 100).2.1 + (legLoopT false P T 100).2.1 +
      24 * ((legLoopT true P T 100).2.2.2.1 + (legLoopT false P T 100).2.2.2.1) ≤
        20 * Pμ * fxScale) &&
    decide ((legLoopT true P T 100).2.2.1 + (legLoopT false P T 100).2.2.1 +
      24 * ((legLoopT true P T 100).2.2.2.2 + (legLoopT false P T 100).2.2.2.2) ≤
        20 * J * fxScale)

/-- **Real time / amplitude leg bounds** for the leg `inner` of an orbit with constants
`ψ₀, B_t`: flank cell bounds `Mt i, MJ i ≥ 0` with `1 ≤ Mt i · A_μ |∂_θB|` and
`w ≤ MJ i · |∂_θB|`, and bottom bounds `ratR ≤ Mbt · A_μ (−∂_ψB)`, `w ratR ≤ MbJ · (−∂_ψB)`. -/
structure TimeLegBounds (inner : Bool) (ψ₀ Bt : ℝ) (Mt MJ : ℕ → ℝ) (Mbt MbJ : ℝ) : Prop where
  /-- Nonnegative flank time bounds. -/
  Mt_nonneg : ∀ i, 0 ≤ Mt i
  /-- Nonnegative flank amplitude bounds. -/
  MJ_nonneg : ∀ i, 0 ≤ MJ i
  /-- Flank cells. -/
  flank : ∀ i : ℕ, i < 100 → ∀ x ∈ Icc ((i : ℝ) / 40) (((i : ℝ) + 1) / 40), ∀ c,
    OrbitRel inner x ψ₀ Bt c → c ≤ cos (3 / 5) →
    1 ≤ Mt i * (AmR x Bt * denR inner ψ₀ x c (√(1 - c ^ 2))) ∧
      wR inner ψ₀ x ≤ MJ i * denR inner ψ₀ x c (√(1 - c ^ 2))
  /-- Bottom cells. -/
  bottom : ∀ x ∈ Icc (0 : ℝ) (5 / 2), ∀ c, OrbitRel inner x ψ₀ Bt c → cos (3 / 5) ≤ c →
    ratR inner ψ₀ x Bt c ≤ Mbt * (AmR x Bt * numR inner ψ₀ x c) ∧
      wR inner ψ₀ x * ratR inner ψ₀ x Bt c ≤ MbJ * numR inner ψ₀ x c

/-- **Time bounds at `(ψ₀, B_t)`** with targets `Pμ` (microseconds) and `J`: leg bounds for
both legs whose cell sums satisfy `2 (1/40) Σ M_t + (6/5)(M_bt^in + M_bt^out) ≤ Pμ` and the same
for the amplitude bounds with `J`. -/
@[expose] def TimeBounds (Pμ J : ℝ) (ψ₀ Bt : ℝ) : Prop :=
  ∃ (Mti Mto MJi MJo : ℕ → ℝ) (Mbti Mbto MbJi MbJo : ℝ),
    TimeLegBounds true ψ₀ Bt Mti MJi Mbti MbJi ∧ TimeLegBounds false ψ₀ Bt Mto MJo Mbto MbJo ∧
    2 * (1 / 40) * (∑ i ∈ Finset.range 100, Mti i + ∑ i ∈ Finset.range 100, Mto i) +
      6 / 5 * (Mbti + Mbto) ≤ Pμ ∧
    2 * (1 / 40) * (∑ i ∈ Finset.range 100, MJi i + ∑ i ∈ Finset.range 100, MJo i) +
      6 / 5 * (MbJi + MbJo) ≤ J

/-- Sum of scaled values as a scaled sum. -/
theorem sum_fxVal (f : ℕ → ℤ) (n : ℕ) :
    ∑ i ∈ Finset.range n, fxVal (f i) = ((∑ i ∈ Finset.range n, f i : ℤ) : ℝ) / fxScale := by
  unfold fxVal; push_cast; rw [Finset.sum_div]

/-- **Time box soundness.** If `timeBoxOk P T Pμ J = true`, every `(ψ₀, B_t) ∈ P × T` carries
time bounds with targets `Pμ`, `J`. -/
theorem timeBox_sound {P T : FIv} {Pμ J : ℤ} (h : timeBoxOk P T Pμ J = true) {p b : ℝ}
    (hP : P.Mem p) (hT : T.Mem b) : TimeBounds Pμ J p b := by
  simp only [timeBoxOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hi, ho⟩, hup⟩, hJ⟩ := h
  have leg : ∀ inner : Bool, (legLoopT inner P T 100).1 = true →
      TimeLegBounds inner p b (fun i => fxVal (max 0 (flankCellT inner (cellX i) P T).2.1))
        (fun i => fxVal (max 0 (flankCellT inner (cellX i) P T).2.2))
        (fxVal (legLoopT inner P T 100).2.2.2.1) (fxVal (legLoopT inner P T 100).2.2.2.2) := by
    intro inner hl
    obtain ⟨hs, -, -⟩ := legLoopT_spec inner P T 100 hl
    refine ⟨fun i => div_nonneg (by exact_mod_cast le_max_left _ _) fxScale_pos.le,
      fun i => div_nonneg (by exact_mod_cast le_max_left _ _) fxScale_pos.le, ?_, ?_⟩
    · intro i hi x hx c hrel hc
      obtain ⟨h1, h2⟩ := flankCellT_sound (hs i hi).1 (mem_cellX hx) hP hT hrel hc
      have hmax : ∀ z : ℤ, fxVal z ≤ fxVal (max 0 z) := fun z => by
        unfold fxVal; exact div_le_div_of_nonneg_right (by exact_mod_cast le_max_right _ _)
          fxScale_pos.le
      have hd : 0 ≤ denR inner p x c (√(1 - c ^ 2)) := denR_nonneg hrel (sqrt_nonneg _)
      exact ⟨h1.1.trans (mul_le_mul_of_nonneg_right (hmax _) h1.2.le),
        h2.trans (mul_le_mul_of_nonneg_right (hmax _) hd)⟩
    · intro x hx c hrel hc
      obtain ⟨i, hi, hxi⟩ := exists_cell hx
      obtain ⟨h1, h2⟩ := bottomCellT_sound (hs i hi).2.1 (mem_cellX hxi) hP hT hrel hc
      have hle1 : fxVal (bottomCellT inner (cellX i) P T).2.1 ≤
          fxVal (legLoopT inner P T 100).2.2.2.1 := by
        unfold fxVal; exact div_le_div_of_nonneg_right (by exact_mod_cast (hs i hi).2.2.1)
          fxScale_pos.le
      have hle2 : fxVal (bottomCellT inner (cellX i) P T).2.2 ≤
          fxVal (legLoopT inner P T 100).2.2.2.2 := by
        unfold fxVal; exact div_le_div_of_nonneg_right (by exact_mod_cast (hs i hi).2.2.2)
          fxScale_pos.le
      exact ⟨h1.1.trans (mul_le_mul_of_nonneg_right hle1 h1.2.le),
        h2.1.trans (mul_le_mul_of_nonneg_right hle2 h2.2.le)⟩
  refine ⟨_, _, _, _, _, _, _, _, leg true hi, leg false ho, ?_, ?_⟩
  · have e1 := (legLoopT_spec true P T 100 hi).2.1
    have e2 := (legLoopT_spec false P T 100 ho).2.1
    rw [sum_fxVal (fun i => max 0 (flankCellT true (cellX i) P T).2.1),
      sum_fxVal (fun i => max 0 (flankCellT false (cellX i) P T).2.1), ← e1, ← e2]
    have hup' : ((legLoopT true P T 100).2.1 + (legLoopT false P T 100).2.1 +
        24 * ((legLoopT true P T 100).2.2.2.1 + (legLoopT false P T 100).2.2.2.1) : ℝ) ≤
        20 * Pμ * fxScale := by exact_mod_cast hup
    have hS := fxScale_pos
    unfold fxVal
    rw [show (fxScale : ℝ) = ((fxScale : ℤ) : ℝ) from rfl] at *
    field_simp
    linarith
  · have e1 := (legLoopT_spec true P T 100 hi).2.2
    have e2 := (legLoopT_spec false P T 100 ho).2.2
    rw [sum_fxVal (fun i => max 0 (flankCellT true (cellX i) P T).2.2),
      sum_fxVal (fun i => max 0 (flankCellT false (cellX i) P T).2.2), ← e1, ← e2]
    have hJ' : ((legLoopT true P T 100).2.2.1 + (legLoopT false P T 100).2.2.1 +
        24 * ((legLoopT true P T 100).2.2.2.2 + (legLoopT false P T 100).2.2.2.2) : ℝ) ≤
        20 * J * fxScale := by exact_mod_cast hJ
    have hS := fxScale_pos
    unfold fxVal
    rw [show (fxScale : ℝ) = ((fxScale : ℤ) : ℝ) from rfl] at *
    field_simp
    linarith

/-! ## The `4 × 4` grid of the start window -/

/-- The `j`-th flux quarter `ψ₀ ∈ [4.75 + 9j/32, 4.75 + 9(j+1)/32]` (index box `[32j, 32(j+1)]`). -/
@[expose] def TPB (j : ℕ) : FIv := PBI (32 * j) (32 * (j + 1))

/-- The `l`-th tip-field quarter `B_t ∈ [5.4 + l/40, 5.4 + (l+1)/40]`. -/
@[expose] def TTB (l : ℕ) : FIv := TBI (32 * l) (32 * (l + 1))

/-- **Time certificate from the grid.** If all `4 × 4` boxes pass `timeBoxOk … Pμ J`, every
`(ψ₀, B_t) ∈ [4.75, 5.875] × [5.4, 5.5]` carries time bounds with targets `Pμ`, `J`. -/
theorem time_cert_of_grid {Pμ J : ℤ}
    (hgrid : ∀ j < 4, ∀ l < 4, timeBoxOk (TPB j) (TTB l) Pμ J = true)
    {ψ₀ Bt : ℝ} (hψ : ψ₀ ∈ Icc (19 / 4 : ℝ) (47 / 8)) (hB : Bt ∈ Icc (27 / 5 : ℝ) (11 / 2)) :
    TimeBounds Pμ J ψ₀ Bt := by
  obtain ⟨j, hj, hψj⟩ := exists_index (a := 19 / 4) (d := 9 / 32) (n := 3) (by norm_num)
    (by norm_num at hψ ⊢; exact hψ)
  obtain ⟨l, hl, hBl⟩ := exists_index (a := 27 / 5) (d := 1 / 40) (n := 3) (by norm_num)
    (by norm_num at hB ⊢; exact hB)
  refine timeBox_sound (hgrid j (by omega) l (by omega)) ?_ ?_
  · refine mem_hull (by norm_num) (by norm_num) ?_ ?_
    · push_cast; linarith [hψj.1]
    · push_cast; linarith [hψj.2]
  · refine mem_hull (by norm_num) (by norm_num) ?_ ?_
    · push_cast; linarith [hBl.1]
    · push_cast; linarith [hBl.2]

/-! ## Sanity checks -/

/-- Sanity (degenerate case): at a turning point (`x = 0`, `B = B_t`) the drift factor is
`A = μ/q`, i.e. `A/10⁶ = 7/(4 B_t)`. -/
theorem AmR_zero {Bt : ℝ} (hB : Bt ≠ 0) : AmR 0 Bt = 7 / (4 * Bt) := by
  unfold AmR; rw [BsR_zero]; field_simp; ring

set_option maxRecDepth 100000 in
/-- Sanity (accepted fixture): a flank time cell near the tip of the first box is alive, valid and
gives a positive time density. -/
theorem fixture_flankT_alive : (flankCellT true (cellX 10) (PB 0) (TB 0)).1 = true ∧
    0 < (flankCellT true (cellX 10) (PB 0) (TB 0)).2.1 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Sanity (rejected fixture): the whole window as a single box fails the time check with the
grid targets `83 μs`, `J ≤ 58` (interval over-estimation gives about `113 μs`). -/
theorem fixture_timeBox_rejected : timeBoxOk (PBI 0 128) (TBI 0 128) 83 58 = false := by
  decide +kernel

end PlasmaLean.Design.NearAxisQATrappedCells
