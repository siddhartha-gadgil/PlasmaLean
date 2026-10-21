/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedOscCells
public import PlasmaLean.Design.NearAxisQATrappedBouncePeriod
public import PlasmaLean.Theory.Kinetic.BounceClamp

/-!
# The oscillatory kick integrals along one exact-QA bounce: pointwise identities and pieces

Companion to `Design/NearAxisQATrappedOscCells` (the cell checker) and
`Design/NearAxisQATrappedOscKick` (the assembled enclosure). Model only: `exactQA`, vacuum Boozer
guiding-centre equations; orbits are those of `NearAxisQATrappedResonance.Setup`.

**Pointwise identities** along a `Setup` orbit at a point of the leg `inner` with leg coordinate
`x = |ψ − ψ₀|` (`Setup.rates`): with `A = μ/q + qρ²B/m`, `K = KR x B_t`, `n = −∂_ψB`,

* `A K = q (ι₀/G)² x B²/m` (`Afac_mul_KR`), hence `φ̇ = ∓ A K/ι₀`;
* `θ̇ = −A (n + K)` on the inner leg and `θ̇ = A (K − n)` on the outer leg;
* `Ω = A n`, `A w = A wR`, and `A = 10⁶ A_μ`.

**Generic pieces** (`piece_tot`, `piece_acc` and the reversed versions): on a stretch where a
cell coordinate `y` moves monotonically from or to `0`, an integrand `Q = r · |ẏ|` with `r` in the
cell enclosure `D i` has `∫ Q ∈ totI D F (n+1)`, and the partial integrals up to a point of cell
`i` lie in `accI D i`. These are `Theory/Kinetic/BounceClamp` with the cell enclosures of the
checker.

**Leg splits** (`inner_split`, `outer_split`): the decomposition of a leg into flank, bottom and
flank pieces at `|θ| = 3/5`, as in `Setup.inner_leg_gen`.

**Flank and bottom points** (`flank_point`, `bottom_point`): the cell soundness lemmas of the
checker turned into statements about the orbit at a time `t`.

**Legs** (`inner_leg_osc`, `outer_leg_osc`): the leg checks `legAOk`, `legBOk` of the cell
checker enclose, for one leg, the integrals of `A w cos 2(φ − φ₀)`, `A w sin 2(φ − φ₀)`, the
precession integral up to the leg's end tip and the leg's duration. The phase is
`2(φ − φ₀) = −2 ∫|φ̇|` on the first flank (from the starting tip),
`(2/ι₀)(θ − θ₀ + ∫Ω)` on the bottom (`prec_eq`), and is accumulated backward from the end tip on
the last flank, where `θ = −θ₀` (inner leg, `inner_leg_osc`) or `θ = θ₀` (outer leg).

Sanity: `xOf_zero`, `sgnL_values`, `yB_ends`.
-/
public section
noncomputable section

namespace PlasmaLean.Design.NearAxisQATrappedOsc
open PlasmaLean.Certificates.ValidatedQuadrature PlasmaLean.Design.NearAxisQATrappedCells
  PlasmaLean.Kinetic.Boozer PlasmaLean.Design.NearAxisQA PlasmaLean.Design.NearAxisQATrappedBounce
  FIvX Real Set

/-! ## Generic pieces -/

/-- `fxVal` is additive. -/
theorem fxVal_add_of (a b : ℤ) : fxVal (a + b) = fxVal a + fxVal b := by
  unfold fxVal; push_cast; ring

/-- `fxVal` of a recursive integer sum. -/
theorem fxVal_sumF (f : ℕ → ℤ) (n : ℕ) : fxVal (sumF f n) = ∑ i ∈ Finset.range n, fxVal (f i) := by
  rw [sumF_eq, sum_fxVal]; rfl

/-- `fxVal` of a flagged upper weight. -/
theorem fxVal_wb (f : Bool) (u : ℤ) :
    fxVal (if f then u else max u 0) = if f then fxVal u else max (fxVal u) 0 := by
  cases f
  · simp only [Bool.false_eq_true, ite_false]
    rcases le_total u 0 with h | h
    · rw [max_eq_right h, max_eq_right (by rw [← fxVal_zero]; exact fxVal_le_of_le h), fxVal_zero]
    · rw [max_eq_left h, max_eq_left (by rw [← fxVal_zero]; exact fxVal_le_of_le h)]
  · rfl

/-- `fxVal` of a flagged lower weight. -/
theorem fxVal_wbLo (f : Bool) (u : ℤ) :
    fxVal (if f then u else min u 0) = if f then fxVal u else min (fxVal u) 0 := by
  cases f
  · simp only [Bool.false_eq_true, ite_false]
    rcases le_total u 0 with h | h
    · rw [min_eq_left h, min_eq_left (by rw [← fxVal_zero]; exact fxVal_le_of_le h)]
    · rw [min_eq_right h, min_eq_right (by rw [← fxVal_zero]; exact fxVal_le_of_le h), fxVal_zero]
  · rfl

/-- `fxVal (max u 0) = max (fxVal u) 0`. -/
theorem fxVal_max0 (u : ℤ) : fxVal (max u 0) = max (fxVal u) 0 := by
  have := fxVal_wb false u; simpa using this

/-- `fxVal (min u 0) = min (fxVal u) 0`. -/
theorem fxVal_min0 (u : ℤ) : fxVal (min u 0) = min (fxVal u) 0 := by
  have := fxVal_wbLo false u; simpa using this

/-- Real bounds from a valid enclosure. -/
theorem le_hi_of_mem {I : FIv} {r : ℝ} (h : I.Mem r) (hok : I.ok = true) :
    fxVal I.lo ≤ r ∧ r ≤ fxVal I.hi := h hok

/-- **Generic increasing piece.** If `y` increases on `[a, b]` from `y a = 0` to
`y b ≤ (n+1)/40`, the integrand is `Q = r ẏ` with `r ∈ D i` whenever `y` is in cell `i ≤ n`, all
`D i` are valid, and the flagged cells are fully swept, then `∫_a^b Q ∈ totI D F (n+1)`. -/
theorem piece_tot {a b : ℝ} {y y' Q : ℝ → ℝ} {D : ℕ → FIv} {Fl : ℕ → Bool} {n : ℕ}
    (hab : a ≤ b) (hy : ∀ t ∈ Icc a b, HasDerivAt y (y' t) t) (hy'0 : ∀ t ∈ Icc a b, 0 ≤ y' t)
    (hQ : ContinuousOn Q (Icc a b)) (hy'c : ContinuousOn y' (Icc a b)) (hya : y a = 0)
    (hyb : y b ≤ (n + 1) * (1 / 40))
    (hD : ∀ t ∈ Icc a b, ∀ i : ℕ, i ≤ n →
      y t ∈ Icc ((i : ℝ) * (1 / 40)) (((i : ℝ) + 1) * (1 / 40)) →
      ∃ r, (D i).Mem r ∧ Q t = r * y' t)
    (hok : ∀ i ≤ n, (D i).ok = true)
    (hFl : ∀ i ≤ n, Fl i = true → ((i : ℝ) + 1) * (1 / 40) ≤ y b) :
    (totI D Fl (n + 1)).Mem (∫ t in a..b, Q t) := by
  have h40 : (0 : ℝ) < 1 / 40 := by norm_num
  have up := integral_le_clamp_sum (U := fun i => fxVal (D i).hi) hab h40 hy hy'0 hQ hy'c hya hyb
    (fun t ht i hi hyi => by
      obtain ⟨r, hr, hQt⟩ := hD t ht i hi hyi
      rw [hQt]; exact mul_le_mul_of_nonneg_right (hr (hok i hi)).2 (hy'0 t ht))
  have lo := clamp_sum_le_integral (L := fun i => fxVal (D i).lo) hab h40 hy hy'0 hQ hy'c hya hyb
    (fun t ht i hi hyi => by
      obtain ⟨r, hr, hQt⟩ := hD t ht i hi hyi
      rw [hQt]; exact mul_le_mul_of_nonneg_right (hr (hok i hi)).1 (hy'0 t ht))
  have f1 := clamp_sum_le_flags h40.le (fun i => fxVal (D i).hi) Fl n hFl
  have f2 := flags_le_clamp_sum h40.le (fun i => fxVal (D i).lo) Fl n hFl
  unfold totI
  apply mem_div40
  · rw [fxVal_sumF]
    simp only [fxVal_wbLo]
    linarith
  · rw [fxVal_sumF]
    simp only [fxVal_wb]
    linarith

/-- **Generic increasing piece, partial integrals.** Under the hypotheses of `piece_tot`, for a
point `t` whose coordinate lies in cell `i ≤ n`, `∫_a^t Q ∈ accI D i`. -/
theorem piece_acc {a b : ℝ} {y y' Q : ℝ → ℝ} {D : ℕ → FIv} {n : ℕ}
    (hy : ∀ t ∈ Icc a b, HasDerivAt y (y' t) t) (hy'0 : ∀ t ∈ Icc a b, 0 ≤ y' t)
    (hQ : ContinuousOn Q (Icc a b)) (hy'c : ContinuousOn y' (Icc a b)) (hya : y a = 0)
    (hD : ∀ t ∈ Icc a b, ∀ i : ℕ, i ≤ n →
      y t ∈ Icc ((i : ℝ) * (1 / 40)) (((i : ℝ) + 1) * (1 / 40)) →
      ∃ r, (D i).Mem r ∧ Q t = r * y' t)
    (hok : ∀ i ≤ n, (D i).ok = true)
    {t : ℝ} (ht : t ∈ Icc a b) {i : ℕ} (hi : i ≤ n)
    (hyt : y t ∈ Icc ((i : ℝ) * (1 / 40)) (((i : ℝ) + 1) * (1 / 40))) :
    (accI D i).Mem (∫ s in a..t, Q s) := by
  have h40 : (0 : ℝ) < 1 / 40 := by norm_num
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hD' : ∀ s ∈ Icc a t, ∀ j : ℕ, j ≤ i →
      y s ∈ Icc ((j : ℝ) * (1 / 40)) (((j : ℝ) + 1) * (1 / 40)) →
      ∃ r, (D j).Mem r ∧ Q s = r * y' s := fun s hs j hj hys =>
    hD s (hsub hs) j (hj.trans hi) hys
  have up := integral_le_clamp_sum (U := fun j => fxVal (D j).hi) (n := i) ht.1 h40
    (fun s hs => hy s (hsub hs)) (fun s hs => hy'0 s (hsub hs)) (hQ.mono hsub)
    (hy'c.mono hsub) hya hyt.2
    (fun s hs j hj hys => by
      obtain ⟨r, hr, hQs⟩ := hD' s hs j hj hys
      rw [hQs]; exact mul_le_mul_of_nonneg_right (hr (hok j (hj.trans hi))).2 (hy'0 s (hsub hs)))
  have lo := clamp_sum_le_integral (L := fun j => fxVal (D j).lo) (n := i) ht.1 h40
    (fun s hs => hy s (hsub hs)) (fun s hs => hy'0 s (hsub hs)) (hQ.mono hsub)
    (hy'c.mono hsub) hya hyt.2
    (fun s hs j hj hys => by
      obtain ⟨r, hr, hQs⟩ := hD' s hs j hj hys
      rw [hQs]; exact mul_le_mul_of_nonneg_right (hr (hok j (hj.trans hi))).1 (hy'0 s (hsub hs)))
  have p1 := clamp_sum_le_partial h40.le (fun j => fxVal (D j).hi) i hyt
  have p2 := partial_le_clamp_sum h40.le (fun j => fxVal (D j).lo) i hyt
  unfold accI
  apply mem_div40
  · rw [fxVal_add_of, fxVal_sumF, fxVal_min0]
    linarith
  · rw [fxVal_add_of, fxVal_sumF, fxVal_max0]
    linarith

/-- **Generic decreasing piece.** If `y` decreases on `[a, b]` from `y a ≤ (n+1)/40` to
`y b = 0`, the integrand is `Q = r (−ẏ)` with `r ∈ D i` whenever `y` is in cell `i ≤ n`, all
`D i` are valid, and the flagged cells are fully swept, then `∫_a^b Q ∈ totI D F (n+1)`. -/
theorem piece_tot_rev {a b : ℝ} {y y' Q : ℝ → ℝ} {D : ℕ → FIv} {Fl : ℕ → Bool} {n : ℕ}
    (hab : a ≤ b) (hy : ∀ t ∈ Icc a b, HasDerivAt y (y' t) t) (hy'0 : ∀ t ∈ Icc a b, y' t ≤ 0)
    (hQ : ContinuousOn Q (Icc a b)) (hy'c : ContinuousOn y' (Icc a b)) (hyb : y b = 0)
    (hya : y a ≤ (n + 1) * (1 / 40))
    (hD : ∀ t ∈ Icc a b, ∀ i : ℕ, i ≤ n →
      y t ∈ Icc ((i : ℝ) * (1 / 40)) (((i : ℝ) + 1) * (1 / 40)) →
      ∃ r, (D i).Mem r ∧ Q t = r * -y' t)
    (hok : ∀ i ≤ n, (D i).ok = true)
    (hFl : ∀ i ≤ n, Fl i = true → ((i : ℝ) + 1) * (1 / 40) ≤ y a) :
    (totI D Fl (n + 1)).Mem (∫ t in a..b, Q t) := by
  have h40 : (0 : ℝ) < 1 / 40 := by norm_num
  have hn0 : ∀ t ∈ Icc a b, 0 ≤ -y' t := fun t ht => by linarith [hy'0 t ht]
  have up := integral_le_clamp_sum_rev (U := fun i => fxVal (D i).hi) hab h40 hy hy'0 hQ hy'c
    hyb hya
    (fun t ht i hi hyi => by
      obtain ⟨r, hr, hQt⟩ := hD t ht i hi hyi
      rw [hQt]; exact mul_le_mul_of_nonneg_right (hr (hok i hi)).2 (hn0 t ht))
  have lo := clamp_sum_le_integral_rev (L := fun i => fxVal (D i).lo) hab h40 hy hy'0 hQ hy'c
    hyb hya
    (fun t ht i hi hyi => by
      obtain ⟨r, hr, hQt⟩ := hD t ht i hi hyi
      rw [hQt]; exact mul_le_mul_of_nonneg_right (hr (hok i hi)).1 (hn0 t ht))
  have f1 := clamp_sum_le_flags h40.le (fun i => fxVal (D i).hi) Fl n hFl
  have f2 := flags_le_clamp_sum h40.le (fun i => fxVal (D i).lo) Fl n hFl
  unfold totI
  apply mem_div40
  · rw [fxVal_sumF]
    simp only [fxVal_wbLo]
    linarith
  · rw [fxVal_sumF]
    simp only [fxVal_wb]
    linarith

/-- **Generic decreasing piece, partial integrals.** Under the hypotheses of `piece_tot_rev`, for
a point `t` whose coordinate lies in cell `i ≤ n`, `∫_t^b Q ∈ accI D i`. -/
theorem piece_acc_rev {a b : ℝ} {y y' Q : ℝ → ℝ} {D : ℕ → FIv} {n : ℕ}
    (hy : ∀ t ∈ Icc a b, HasDerivAt y (y' t) t) (hy'0 : ∀ t ∈ Icc a b, y' t ≤ 0)
    (hQ : ContinuousOn Q (Icc a b)) (hy'c : ContinuousOn y' (Icc a b)) (hyb : y b = 0)
    (hD : ∀ t ∈ Icc a b, ∀ i : ℕ, i ≤ n →
      y t ∈ Icc ((i : ℝ) * (1 / 40)) (((i : ℝ) + 1) * (1 / 40)) →
      ∃ r, (D i).Mem r ∧ Q t = r * -y' t)
    (hok : ∀ i ≤ n, (D i).ok = true)
    {t : ℝ} (ht : t ∈ Icc a b) {i : ℕ} (hi : i ≤ n)
    (hyt : y t ∈ Icc ((i : ℝ) * (1 / 40)) (((i : ℝ) + 1) * (1 / 40))) :
    (accI D i).Mem (∫ s in t..b, Q s) := by
  have h40 : (0 : ℝ) < 1 / 40 := by norm_num
  have hsub : Icc t b ⊆ Icc a b := Icc_subset_Icc ht.1 le_rfl
  have hn0 : ∀ s ∈ Icc t b, 0 ≤ -y' s := fun s hs => by linarith [hy'0 s (hsub hs)]
  have hD' : ∀ s ∈ Icc t b, ∀ j : ℕ, j ≤ i →
      y s ∈ Icc ((j : ℝ) * (1 / 40)) (((j : ℝ) + 1) * (1 / 40)) →
      ∃ r, (D j).Mem r ∧ Q s = r * -y' s := fun s hs j hj hys =>
    hD s (hsub hs) j (hj.trans hi) hys
  have up := integral_le_clamp_sum_rev (U := fun j => fxVal (D j).hi) (n := i) ht.2 h40
    (fun s hs => hy s (hsub hs)) (fun s hs => hy'0 s (hsub hs)) (hQ.mono hsub)
    (hy'c.mono hsub) hyb hyt.2
    (fun s hs j hj hys => by
      obtain ⟨r, hr, hQs⟩ := hD' s hs j hj hys
      rw [hQs]; exact mul_le_mul_of_nonneg_right (hr (hok j (hj.trans hi))).2 (hn0 s hs))
  have lo := clamp_sum_le_integral_rev (L := fun j => fxVal (D j).lo) (n := i) ht.2 h40
    (fun s hs => hy s (hsub hs)) (fun s hs => hy'0 s (hsub hs)) (hQ.mono hsub)
    (hy'c.mono hsub) hyb hyt.2
    (fun s hs j hj hys => by
      obtain ⟨r, hr, hQs⟩ := hD' s hs j hj hys
      rw [hQs]; exact mul_le_mul_of_nonneg_right (hr (hok j (hj.trans hi))).1 (hn0 s hs))
  have p1 := clamp_sum_le_partial h40.le (fun j => fxVal (D j).hi) i hyt
  have p2 := partial_le_clamp_sum h40.le (fun j => fxVal (D j).lo) i hyt
  unfold accI
  apply mem_div40
  · rw [fxVal_add_of, fxVal_sumF, fxVal_min0]
    linarith
  · rw [fxVal_add_of, fxVal_sumF, fxVal_max0]
    linarith

/-- The leg coordinate `x = ψ₀ − ψ` (inner leg) or `ψ − ψ₀` (outer leg). -/
@[expose] def xOf (inner : Bool) (ψ : ℝ → ℝ) (t : ℝ) : ℝ := if inner then ψ 0 - ψ t else ψ t - ψ 0

/-- `psiR` of the leg coordinate is the flux. -/
theorem psiR_xOf (inner : Bool) (ψ : ℝ → ℝ) (t : ℝ) : psiR inner (ψ 0) (xOf inner ψ t) = ψ t := by
  cases inner <;> simp [xOf, psiR]

/-- The sign of the leg: `−1` (inner) or `+1` (outer). -/
@[expose] def sgnL (inner : Bool) : ℝ := if inner then -1 else 1

/-- Sanity (degenerate case): the leg coordinate vanishes at the starting tip. -/
theorem xOf_zero (inner : Bool) (ψ : ℝ → ℝ) : xOf inner ψ 0 = 0 := by
  cases inner <;> simp [xOf]

/-- Sanity (special case): the leg signs. -/
theorem sgnL_values : sgnL true = -1 ∧ sgnL false = 1 := by norm_num [sgnL]

/-- `|∂_θB|` at the orbit point, in reduced form (flank divisor: `|ẋ| = A · denT`). -/
@[expose] def denT (ψ θ : ℝ → ℝ) (inner : Bool) (t : ℝ) : ℝ :=
  denR inner (ψ 0) (xOf inner ψ t) (cos (θ t)) (√(1 - cos (θ t) ^ 2))

/-- `|θ̇|/A` at the orbit point, in reduced form (bottom divisor: `|θ̇| = A · bDenT`). -/
@[expose] def bDenT (μ : ℝ) (ψ θ : ℝ → ℝ) (inner : Bool) (t : ℝ) : ℝ :=
  bDenR inner (ψ 0) (xOf inner ψ t) (Eα / μ) (cos (θ t))

/-- The bottom cell coordinate `y = 3/5 − θ` (inner leg) or `θ + 3/5` (outer leg). -/
@[expose] def yB (inner : Bool) (θ : ℝ → ℝ) (t : ℝ) : ℝ :=
  if inner then 3 / 5 - θ t else θ t + 3 / 5

/-- Sanity (special case): at `θ = ±3/5` the bottom coordinate is `0` at the start and `6/5` at
the end of the crossing. -/
theorem yB_ends (θ : ℝ → ℝ) (t : ℝ) :
    (θ t = 3 / 5 → yB true θ t = 0) ∧ (θ t = -(3 / 5) → yB true θ t = 6 / 5) ∧
      (θ t = -(3 / 5) → yB false θ t = 0) ∧ (θ t = 3 / 5 → yB false θ t = 6 / 5) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> simp [yB, h] <;> norm_num

/-- The toroidal velocity `φ̇ = qρB²/(Gm)` along an exact-QA orbit. -/
@[expose] def phiDotF (ψ θ φ ρ : ℝ → ℝ) (t : ℝ) : ℝ :=
  qα * ρ t * along exactQA.B ψ θ φ t ^ 2 / (exactQA.G * mα)

/-- Prefix flags give the flag of every earlier cell. -/
theorem fullPre_spec {inner : Bool} {P Tb : FIv} {i : ℕ} (h : fullPre inner P Tb i = true) :
    ∀ j ≤ i, (fcell inner P Tb j).full = true := by
  induction i with
  | zero => intro j hj; rw [Nat.le_zero.mp hj]; exact h
  | succ i ih =>
    simp only [fullPre, Bool.and_eq_true] at h
    intro j hj
    rcases Nat.lt_or_ge j (i + 1) with h' | h'
    · exact ih h.1 j (by omega)
    · rw [show j = i + 1 by omega]; exact h.2

/-- A point of `[0, (i+1)/40)` lies in a cell `j ≤ i`. -/
theorem exists_cell_le {y : ℝ} {i : ℕ} (h0 : 0 ≤ y) (h1 : y < ((i : ℝ) + 1) * (1 / 40)) :
    ∃ j ≤ i, y ∈ Icc ((j : ℝ) * (1 / 40)) (((j : ℝ) + 1) * (1 / 40)) := by
  have h40 : 0 ≤ 40 * y := by linarith
  refine ⟨⌊40 * y⌋₊, ?_, ?_, ?_⟩
  · have := (Nat.floor_lt h40 (n := i + 1)).mpr (by push_cast; linarith)
    omega
  · have := Nat.floor_le h40; linarith
  · have := Nat.lt_floor_add_one (40 * y); linarith

/-- A point of `[0, (n+1)/40]` lies in a cell `j ≤ n`. -/
theorem exists_cell_le' {y : ℝ} {n : ℕ} (h0 : 0 ≤ y) (h1 : y ≤ ((n : ℝ) + 1) * (1 / 40)) :
    ∃ j ≤ n, y ∈ Icc ((j : ℝ) * (1 / 40)) (((j : ℝ) + 1) * (1 / 40)) := by
  rcases lt_or_eq_of_le h1 with h | h
  · exact exists_cell_le h0 h
  · exact ⟨n, le_rfl, ⟨by rw [h]; linarith, by rw [h]⟩⟩

/-- Validity of a flank cell gives validity of its four densities. -/
theorem fcell_ok_fields {inner : Bool} {P Tb : FIv} {i : ℕ} (h : (fcell inner P Tb i).ok = true) :
    (fcell inner P Tb i).om.ok = true ∧ (fcell inner P Tb i).ph.ok = true ∧
      (fcell inner P Tb i).g.ok = true ∧ (fcell inner P Tb i).tt.ok = true := by
  unfold fcell flankCellO at h ⊢
  split_ifs at h ⊢
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · simp only [Bool.and_eq_true] at h
    exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2⟩

/-- Validity of a bottom cell gives validity of its densities. -/
theorem bcell_ok_fields {inner : Bool} {P Tb : FIv} {j : ℕ} (h : (bcell inner P Tb j).ok = true) :
    (bcell inner P Tb j).om.ok = true ∧ (bcell inner P Tb j).g.ok = true ∧
      (bcell inner P Tb j).tt.ok = true := by
  unfold bcell bottomCellO at h ⊢
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2⟩

/-- Splitting a continuous integrand at two interior points. -/
theorem integral_split3 {f : ℝ → ℝ} {a s1 s2 b : ℝ} (hf : ContinuousOn f (Icc a b))
    (h1 : a ≤ s1) (h12 : s1 ≤ s2) (h2 : s2 ≤ b) :
    ∫ t in a..b, f t = (∫ t in a..s1, f t) + (∫ t in s1..s2, f t) + ∫ t in s2..b, f t := by
  have hi : ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b →
      IntervalIntegrable f MeasureTheory.volume u v := by
    intro u v hu huv hv
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le huv]; exact hf.mono (Icc_subset_Icc hu hv)
  rw [intervalIntegral.integral_add_adjacent_intervals (hi a s1 le_rfl h1 (h12.trans h2))
      (hi s1 s2 h1 h12 h2),
    intervalIntegral.integral_add_adjacent_intervals (hi a s2 le_rfl (h1.trans h12) h2)
      (hi s2 b (h1.trans h12) h2 le_rfl)]

/-- Twice an enclosure contains the sum of two of its members. -/
theorem mem_two {I : FIv} {x y : ℝ} (hx : I.Mem x) (hy : I.Mem y) :
    (I.mul (C 2 1)).Mem (x + y) := by
  have hm : I.Mem ((x + y) / 2) := by
    intro hok; obtain ⟨a1, a2⟩ := hx hok; obtain ⟨b1, b2⟩ := hy hok
    constructor <;> linarith
  have := FIv.mem_mul hm (mem_C (p := 2) (q := 1) (r := 2) (by norm_num))
  rwa [show (x + y) / 2 * 2 = x + y by ring] at this

end PlasmaLean.Design.NearAxisQATrappedOsc

namespace PlasmaLean.Design.NearAxisQATrappedResonance.Setup
open PlasmaLean.Certificates.ValidatedQuadrature PlasmaLean.Design.NearAxisQATrappedCells
  PlasmaLean.Kinetic.Boozer PlasmaLean.Design.NearAxisQA PlasmaLean.Design.NearAxisQATrappedBounce
  PlasmaLean.Design.NearAxisQATrappedOsc FIvX Real Set
variable {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ} (S : Setup μ T ψ θ φ ρ)
include S

/-! ## Pointwise identities -/

/-- `ρ = sgn · kinv · x` with the leg coordinate `x`. -/
theorem rho_xOf {t : ℝ} (ht : t ∈ Icc 0 T) (inner : Bool) :
    ρ t = sgnL inner * kinv * xOf inner ψ t := by
  rw [S.mom ht]
  cases inner <;> simp only [sgnL, xOf, Bool.false_eq_true, ite_true, ite_false] <;> ring

/-- The orbit field at `t` is the explicit `BsR x B_t`. -/
theorem B_eq_BsR {t : ℝ} (ht : t ∈ Icc 0 T) (inner : Bool) {x : ℝ}
    (hx : psiR inner (ψ 0) x = ψ t) (hx0 : 0 ≤ x) :
    along exactQA.B ψ θ φ t = BsR x (Eα / μ) := by
  have hrel := S.rel ht inner hx hx0
  have hBs := BsR_eq hrel
  rw [hx] at hBs
  rw [hBs]; simp only [along]; exact exactQA_B_eq _ _ _

/-- **`A K = q (ι₀/G)² x B²/m`** along the orbit. -/
theorem Afac_mul_KR {t : ℝ} (ht : t ∈ Icc 0 T) (inner : Bool) {x : ℝ}
    (hx : psiR inner (ψ 0) x = ψ t) (hx0 : 0 ≤ x) :
    Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * KR x (Eα / μ) =
      qα * kinv ^ 2 * x * along exactQA.B ψ θ φ t ^ 2 / mα := by
  have hrel := S.rel ht inner hx hx0
  have hB := S.B_eq_BsR ht inner hx hx0
  have hEn := energy_along (by norm_num [mα]) (by norm_num [qα])
    (by rw [exactQA, qaField_G]; norm_num) S.orbit S.energy ht
  have hB0 : 0 < along exactQA.B ψ θ φ t := by
    rw [hB, BsR_eq hrel]; exact hrel.B_pos
  have key := bottom_alg (x := x) S.mu_pos hB0 one_pos hEn
  unfold Afac KR
  rw [← hB]
  simpa using key

/-- **`φ̇ = sgn · A K/ι₀`** along the orbit. -/
theorem phiDot_eq {t : ℝ} (ht : t ∈ Icc 0 T) (inner : Bool) (hx0 : 0 ≤ xOf inner ψ t) :
    phiDotF ψ θ φ ρ t = sgnL inner *
      (Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * KR (xOf inner ψ t) (Eα / μ)) /
        (211 / 500) := by
  rw [S.Afac_mul_KR ht inner (psiR_xOf inner ψ t) hx0]
  unfold phiDotF
  rw [S.rho_xOf ht inner, show exactQA.G = 581 / 10 from rfl]
  have hm : (mα : ℝ) ≠ 0 := by norm_num [mα]
  unfold kinv
  field_simp
  ring

/-- **`θ̇ = A (−n + sgn · K)`** along the orbit (`n = −∂_ψB`). -/
theorem thetaDot_eq {t : ℝ} (ht : t ∈ Icc 0 T) (inner : Bool) (hx0 : 0 ≤ xOf inner ψ t) :
    thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
      Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
        (-numR inner (ψ 0) (xOf inner ψ t) (cos (θ t)) +
          sgnL inner * KR (xOf inner ψ t) (Eα / μ)) := by
  have hK := S.Afac_mul_KR ht inner (psiR_xOf inner ψ t) hx0
  have hn := numR_eq (psiR_xOf inner ψ t) (θ t) (φ t)
  rw [hn, neg_neg, mul_add, mul_left_comm _ (sgnL inner), hK]
  unfold thetaDot
  have hρ := S.rho_xOf ht inner
  rw [show exactQA.ι (ψ t) = 211 / 500 from rfl, show exactQA.G = 581 / 10 from rfl]
  simp only [along, Afac]
  rw [hρ]
  have hm : (mα : ℝ) ≠ 0 := by norm_num [mα]
  unfold kinv
  field_simp
  ring

omit S in
/-- **`Ω = A n`** along the orbit. -/
theorem Om_eq_num {t : ℝ} (inner : Bool) :
    Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
      Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
        numR inner (ψ 0) (xOf inner ψ t) (cos (θ t)) := by
  rw [Om_eq, numR_eq (psiR_xOf inner ψ t) (θ t) (φ t)]; simp only [along]

/-- **`|∂_θB| = denT`** along the orbit. -/
theorem abs_Bθ_denT {t : ℝ} (ht : t ∈ Icc 0 T) (inner : Bool) (hx0 : 0 ≤ xOf inner ψ t) :
    |along exactQA.Bθ ψ θ φ t| = denT ψ θ inner t := by
  have hrel := S.rel ht inner (psiR_xOf inner ψ t) hx0
  simp only [along]
  exact abs_Bθ_eq hrel (psiR_xOf inner ψ t) (φ t)

omit S in
/-- **`A w = A wR`**: the amplitude integrand in reduced form. -/
theorem Aw_eq {t : ℝ} (inner : Bool) :
    Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * (20 / 57 * ψ t) =
      Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * wR inner (ψ 0) (xOf inner ψ t) := by
  unfold wR; rw [psiR_xOf]

/-! ## Leg splits -/

/-- **Split of an inner leg** `[a, b]` (`ρ(a) = ρ(b) = 0`, `ρ < 0` inside, `θ(a) > 3/5`,
`θ(b) < −3/5`) at the first times `s₁ < s₂` where `θ = 3/5` and `θ = −3/5`: `θ ≥ 3/5` on
`[a, s₁]`, `|θ| ≤ 3/5` with `θ̇ < 0` on `[s₁, s₂]`, `θ ≤ −3/5` on `[s₂, b]`, and the inner leg
coordinate is nonnegative on `[a, b]`. -/
theorem inner_split {Mf : ℕ → ℝ} {Mb mb : ℝ} (cert : LegBounds true (ψ 0) (Eα / μ) Mf Mb mb)
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a < b) (hbT : b ≤ T) (hρa : ρ a = 0) (hρb : ρ b = 0)
    (hneg : ∀ t ∈ Ioo a b, ρ t < 0) (hθa : 3 / 5 < θ a) (hθb : θ b < -(3 / 5)) :
    ∃ s1 s2 : ℝ, a < s1 ∧ s1 ≤ s2 ∧ s2 < b ∧ θ s1 = 3 / 5 ∧ θ s2 = -(3 / 5) ∧
      (∀ t ∈ Icc a s1, 3 / 5 ≤ θ t) ∧ (∀ t ∈ Icc s1 s2, |θ t| ≤ 3 / 5) ∧
      (∀ t ∈ Icc s2 b, θ t ≤ -(3 / 5)) ∧ (∀ t ∈ Icc a b, 0 ≤ xOf true ψ t) ∧
      (∀ t ∈ Icc s1 s2, thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t < 0) ∧
      ψ a = ψ 0 ∧ ψ b = ψ 0 := by
  have hI : ∀ t ∈ Icc a b, t ∈ Icc 0 T := fun t ht => ⟨ha0.trans ht.1, ht.2.trans hbT⟩
  have hρle : ∀ t ∈ Icc a b, ρ t ≤ 0 := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, hρa]
    rcases eq_or_lt_of_le ht.2 with h' | h'
    · rw [h', hρb]
    · exact (hneg t ⟨h, h'⟩).le
  have hxψ : ∀ t ∈ Icc a b, psiR true (ψ 0) (ψ 0 - ψ t) = ψ t := fun t _ => by simp [psiR]
  have hx0 : ∀ t ∈ Icc a b, 0 ≤ ψ 0 - ψ t := by
    intro t ht
    have h1 := S.mom (hI t ht); have h2 := hρle t ht
    unfold kinv at h1; nlinarith
  have hθc : ContinuousOn θ (Icc a b) := S.cont_theta.mono (fun t ht => hI t ht)
  obtain ⟨s1, hs1, hθs1, hbef1⟩ := first_hit (g := θ) (c := 3 / 5) hab.le hθc hθa (by linarith)
  obtain ⟨s2, hs2, hθs2, hbef2⟩ := first_hit (g := θ) (c := -(3 / 5)) hs1.2 (hθc.mono
    (Icc_subset_Icc hs1.1.le le_rfl)) (by linarith) hθb.le
  have hs2b : s2 < b := lt_of_le_of_ne hs2.2 (fun h => by rw [h] at hθs2; linarith)
  have hdown : ∀ t ∈ Ioo a b, |θ t| ≤ 3 / 5 → thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ)
      (ρ := ρ) t < 0 := by
    intro t ht hθt
    have htI : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
    have := ((S.bottom_bound cert (hI t htI) (hxψ t htI) (hx0 t htI) hθt).2.1 rfl).1
    linarith
  have hlt1 : ∀ t ∈ Ioc s1 b, θ t < 3 / 5 := by
    refine lt_of_level_deriv_neg (hθc.mono (Icc_subset_Icc hs1.1.le le_rfl)) hθs1.le ?_
    intro t ht hθt
    have htb : t < b := lt_of_le_of_ne ht.2 (fun h => by rw [h] at hθt; linarith)
    have hta : a < t := lt_of_lt_of_le hs1.1 ht.1
    exact ⟨_, hdown t ⟨hta, htb⟩ (by rw [hθt, abs_of_pos (by norm_num)]),
      S.hasDerivAt_theta (hI t ⟨hta.le, htb.le⟩)⟩
  have hlt2 : ∀ t ∈ Ioc s2 b, θ t < -(3 / 5) := by
    refine lt_of_level_deriv_neg (hθc.mono (Icc_subset_Icc (hs1.1.le.trans hs2.1.le) le_rfl))
      hθs2.le ?_
    intro t ht hθt
    have htb : t < b := lt_of_le_of_ne ht.2 (fun h => by rw [h] at hθt; linarith)
    have hta : a < t := lt_of_lt_of_le (hs1.1.trans hs2.1) ht.1
    exact ⟨_, hdown t ⟨hta, htb⟩ (by rw [hθt, abs_neg, abs_of_pos (by norm_num)]),
      S.hasDerivAt_theta (hI t ⟨hta.le, htb.le⟩)⟩
  have hbot : ∀ t ∈ Icc s1 s2, |θ t| ≤ 3 / 5 := by
    intro t ht
    refine abs_le.mpr ⟨?_, ?_⟩
    · rcases eq_or_lt_of_le ht.2 with h | h
      · rw [h, hθs2]
      · exact (hbef2 t ⟨ht.1, h⟩).le
    · rcases eq_or_lt_of_le ht.1 with h | h
      · rw [← h, hθs1]
      · exact (hlt1 t ⟨h, ht.2.trans hs2.2⟩).le
  have hψa : ψ a = ψ 0 := by
    have := S.mom (hI a ⟨le_rfl, hab.le⟩); rw [hρa] at this; unfold kinv at this; linarith
  have hψb : ψ b = ψ 0 := by
    have := S.mom (hI b ⟨hab.le, le_rfl⟩); rw [hρb] at this; unfold kinv at this; linarith
  refine ⟨s1, s2, hs1.1, hs2.1.le, hs2b, hθs1, hθs2, ?_, hbot, ?_, ?_, ?_, hψa, hψb⟩
  · intro t ht
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h, hθs1]
    · exact (hbef1 t ⟨ht.1, h⟩).le
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, hθs2]
    · exact (hlt2 t ⟨h, ht.2⟩).le
  · intro t ht; simp only [xOf, ite_true]; exact hx0 t ht
  · intro t ht
    exact hdown t ⟨lt_of_lt_of_le hs1.1 ht.1, lt_of_le_of_lt ht.2 hs2b⟩ (hbot t ht)

/-- **Split of an outer leg** `[a, b]` (`ρ(a) = ρ(b) = 0`, `ρ > 0` inside, `θ(a) < −3/5`,
`θ(b) > 3/5`): `θ ≤ −3/5` on `[a, s₁]`, `|θ| ≤ 3/5` with `θ̇ > 0` on `[s₁, s₂]`, `θ ≥ 3/5` on
`[s₂, b]`, and the outer leg coordinate is nonnegative on `[a, b]`. -/
theorem outer_split {Mf : ℕ → ℝ} {Mb mb : ℝ} (cert : LegBounds false (ψ 0) (Eα / μ) Mf Mb mb)
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a < b) (hbT : b ≤ T) (hρa : ρ a = 0) (hρb : ρ b = 0)
    (hpos : ∀ t ∈ Ioo a b, 0 < ρ t) (hθa : θ a < -(3 / 5)) (hθb : 3 / 5 < θ b) :
    ∃ s1 s2 : ℝ, a < s1 ∧ s1 ≤ s2 ∧ s2 < b ∧ θ s1 = -(3 / 5) ∧ θ s2 = 3 / 5 ∧
      (∀ t ∈ Icc a s1, θ t ≤ -(3 / 5)) ∧ (∀ t ∈ Icc s1 s2, |θ t| ≤ 3 / 5) ∧
      (∀ t ∈ Icc s2 b, 3 / 5 ≤ θ t) ∧ (∀ t ∈ Icc a b, 0 ≤ xOf false ψ t) ∧
      (∀ t ∈ Icc s1 s2, 0 < thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) ∧
      ψ a = ψ 0 ∧ ψ b = ψ 0 := by
  have hI : ∀ t ∈ Icc a b, t ∈ Icc 0 T := fun t ht => ⟨ha0.trans ht.1, ht.2.trans hbT⟩
  have hρge : ∀ t ∈ Icc a b, 0 ≤ ρ t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, hρa]
    rcases eq_or_lt_of_le ht.2 with h' | h'
    · rw [h', hρb]
    · exact (hpos t ⟨h, h'⟩).le
  have hxψ : ∀ t ∈ Icc a b, psiR false (ψ 0) (ψ t - ψ 0) = ψ t := fun t _ => by simp [psiR]
  have hx0 : ∀ t ∈ Icc a b, 0 ≤ ψ t - ψ 0 := by
    intro t ht
    have h1 := S.mom (hI t ht); have h2 := hρge t ht
    unfold kinv at h1; nlinarith
  have hθc : ContinuousOn θ (Icc a b) := S.cont_theta.mono (fun t ht => hI t ht)
  have hnθ : ∀ t ∈ Icc a b, HasDerivAt (fun s => -θ s)
      (-thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) t :=
    fun t ht => (S.hasDerivAt_theta (hI t ht)).neg
  obtain ⟨s1, hs1, hθs1, hbef1⟩ := first_hit (g := fun t => -θ t) (c := 3 / 5) hab.le hθc.neg
    (by linarith) (by linarith)
  obtain ⟨s2, hs2, hθs2, hbef2⟩ := first_hit (g := fun t => -θ t) (c := -(3 / 5)) hs1.2
    (hθc.mono (Icc_subset_Icc hs1.1.le le_rfl)).neg (by linarith)
    (by linarith)
  have hs2b : s2 < b := lt_of_le_of_ne hs2.2 (fun h => by rw [h] at hθs2; linarith)
  have hup : ∀ t ∈ Ioo a b, |θ t| ≤ 3 / 5 → 0 < thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ)
      (ρ := ρ) t := by
    intro t ht hθt
    have htI : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
    exact ((S.bottom_bound cert (hI t htI) (hxψ t htI) (hx0 t htI) hθt).2.2 rfl).1
  have hlt1 : ∀ t ∈ Ioc s1 b, -θ t < 3 / 5 := by
    refine lt_of_level_deriv_neg (f := fun t => -θ t)
      (hθc.mono (Icc_subset_Icc hs1.1.le le_rfl)).neg hθs1.le ?_
    intro t ht hθt
    have htb : t < b := lt_of_le_of_ne ht.2 (fun h => by rw [h] at hθt; linarith)
    have hta : a < t := lt_of_lt_of_le hs1.1 ht.1
    exact ⟨_, by linarith [hup t ⟨hta, htb⟩ (by rw [abs_le]; constructor <;> linarith)],
      hnθ t ⟨hta.le, htb.le⟩⟩
  have hlt2 : ∀ t ∈ Ioc s2 b, -θ t < -(3 / 5) := by
    refine lt_of_level_deriv_neg (f := fun t => -θ t)
      (hθc.mono (Icc_subset_Icc (hs1.1.le.trans hs2.1.le) le_rfl)).neg hθs2.le ?_
    intro t ht hθt
    have htb : t < b := lt_of_le_of_ne ht.2 (fun h => by rw [h] at hθt; linarith)
    have hta : a < t := lt_of_lt_of_le (hs1.1.trans hs2.1) ht.1
    exact ⟨_, by linarith [hup t ⟨hta, htb⟩ (by rw [abs_le]; constructor <;> linarith)],
      hnθ t ⟨hta.le, htb.le⟩⟩
  have hbot : ∀ t ∈ Icc s1 s2, |θ t| ≤ 3 / 5 := by
    intro t ht
    refine abs_le.mpr ⟨?_, ?_⟩
    · rcases eq_or_lt_of_le ht.1 with h | h
      · rw [← h]; linarith
      · linarith [hlt1 t ⟨h, ht.2.trans hs2.2⟩]
    · rcases eq_or_lt_of_le ht.2 with h | h
      · rw [h]; linarith
      · linarith [hbef2 t ⟨ht.1, h⟩]
  have hψa : ψ a = ψ 0 := by
    have := S.mom (hI a ⟨le_rfl, hab.le⟩); rw [hρa] at this; unfold kinv at this; linarith
  have hψb : ψ b = ψ 0 := by
    have := S.mom (hI b ⟨hab.le, le_rfl⟩); rw [hρb] at this; unfold kinv at this; linarith
  refine ⟨s1, s2, hs1.1, hs2.1.le, hs2b, by linarith, by linarith, ?_, hbot, ?_, ?_, ?_,
    hψa, hψb⟩
  · intro t ht
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h]; linarith
    · linarith [hbef1 t ⟨ht.1, h⟩]
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]; linarith
    · linarith [hlt2 t ⟨h, ht.2⟩]
  · intro t ht; simp only [xOf, Bool.false_eq_true, ite_false]; exact hx0 t ht
  · intro t ht
    exact hup t ⟨lt_of_lt_of_le hs1.1 ht.1, lt_of_le_of_lt ht.2 hs2b⟩ (hbot t ht)

/-! ## Flank and bottom points -/

omit S in
/-- `sgnL² = 1`. -/
theorem sgnL_sq (inner : Bool) : sgnL inner * sgnL inner = 1 := by cases inner <;> norm_num [sgnL]

omit S in
/-- `c ≤ cos(3/5)` on the flanks, for `|θ| < π/2`. -/
theorem cos_le_of_flank {θt : ℝ} (hθ : 3 / 5 ≤ |θt|) (hlt : |θt| < π / 2) :
    cos θt ≤ cos (3 / 5) := by
  rw [← cos_abs θt]
  exact cos_le_cos_of_nonneg_of_le_pi (by norm_num) (by linarith [pi_pos]) hθ

omit S in
/-- `cos(3/5) ≤ c` at the bottom. -/
theorem le_cos_of_bottom {θt : ℝ} (hθ : |θt| ≤ 3 / 5) : cos (3 / 5) ≤ cos θt := by
  rw [← cos_abs θt]
  exact cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [pi_gt_three]) hθ

/-- **A flank point.** At a time `t` with `|θ| ≥ 3/5` whose leg coordinate lies in the `x`-cell
`i` of a valid flank cell: the cell is alive, `|∂_θB| = denT > 0`, and `Ω`, `sgn · φ̇`, `A w` and
`10⁶` are each a density of the cell times `A · denT`. -/
theorem flank_point {P Tb : FIv} (hP : P.Mem (ψ 0)) (hTb : Tb.Mem (Eα / μ)) {inner : Bool}
    {t : ℝ} (ht : t ∈ Icc 0 T) (hx0 : 0 ≤ xOf inner ψ t) (hθ : 3 / 5 ≤ |θ t|) {i : ℕ}
    (hxi : xOf inner ψ t ∈ Icc ((i : ℝ) * (1 / 40)) (((i : ℝ) + 1) * (1 / 40)))
    (hok : (fcell inner P Tb i).ok = true) :
    (fcell inner P Tb i).dead = false ∧ 0 < denT ψ θ inner t ∧
      |along exactQA.Bθ ψ θ φ t| = denT ψ θ inner t ∧
      (∃ r, (fcell inner P Tb i).om.Mem r ∧
        Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
          r * (Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * denT ψ θ inner t)) ∧
      (∃ r, (fcell inner P Tb i).ph.Mem r ∧ sgnL inner * phiDotF ψ θ φ ρ t =
          r * (Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * denT ψ θ inner t)) ∧
      (∃ r, (fcell inner P Tb i).g.Mem r ∧
        Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * (20 / 57 * ψ t) =
          r * (Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * denT ψ θ inner t)) ∧
      (∃ r, (fcell inner P Tb i).tt.Mem r ∧ (10 : ℝ) ^ 6 =
          r * (Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * denT ψ θ inner t)) ∧
      (fcell inner P Tb i).om.ok = true ∧ (fcell inner P Tb i).ph.ok = true ∧
      (fcell inner P Tb i).g.ok = true ∧ (fcell inner P Tb i).tt.ok = true ∧
      0 ≤ fxVal (fcell inner P Tb i).om.lo ∧ 0 ≤ fxVal (fcell inner P Tb i).ph.lo := by
  have hrel := S.rel ht inner (psiR_xOf inner ψ t) hx0
  have hθlt : |θ t| < π / 2 := abs_lt.mpr ⟨(S.theta ht).1, (S.theta ht).2⟩
  have hc := cos_le_of_flank hθ hθlt
  have hX : (cellX i).Mem (xOf inner ψ t) := mem_cellX ((cell_iff i).mp hxi)
  obtain ⟨hdead, hden, hom, hph, hg, htt, okom, okph, okg, oktt, hom0, hph0⟩ :=
    flankCellO_sound hok hX hP hTb hrel hc
  have hA := S.Afac_pos ht
  have hAe := S.Afac_eq_AmR ht inner (psiR_xOf inner ψ t) hx0
  set d := denT ψ θ inner t with hd
  have hd' : denR inner (ψ 0) (xOf inner ψ t) (cos (θ t)) (√(1 - cos (θ t) ^ 2)) = d := rfl
  rw [hd'] at hden hom hph hg htt
  have hdne : d ≠ 0 := hden.ne'
  refine ⟨hdead, hden, S.abs_Bθ_denT ht inner hx0, ⟨_, hom, ?_⟩, ⟨_, hph, ?_⟩, ⟨_, hg, ?_⟩,
    ⟨_, htt, ?_⟩, okom, okph, okg, oktt, hom0, hph0⟩
  · rw [Om_eq_num inner]; field_simp
  · rw [S.phiDot_eq ht inner hx0]
    have h2 := sgnL_sq inner
    field_simp
    linear_combination KR (xOf inner ψ t) (Eα / μ) * h2
  · rw [Aw_eq inner]; field_simp
  · have hAm : AmR (xOf inner ψ t) (Eα / μ) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hAe; exact hA.ne' hAe
    rw [hAe]; field_simp

omit S in
/-- **Real interval of a bottom `θ`-cell.** If the bottom coordinate `yB` lies in cell `j < 48`,
then `θ ∈ thI inner j` and `|θ| ∈ [k/40, (k+1)/40]` with `k = kOf j < 24`. -/
theorem bottom_cell_theta {inner : Bool} {θ : ℝ → ℝ} {t : ℝ} {j : ℕ} (hj : j < 48)
    (hy : yB inner θ t ∈ Icc ((j : ℝ) * (1 / 40)) (((j : ℝ) + 1) * (1 / 40))) :
    (thI inner j).Mem (θ t) ∧ kOf j < 24 ∧ ((kOf j : ℕ) : ℝ) / 40 ≤ |θ t| ∧
      |θ t| ≤ ((kOf j : ℕ) + 1 : ℝ) / 40 := by
  have hj' : (j : ℝ) < 48 := by exact_mod_cast hj
  cases inner
  · simp only [yB, Bool.false_eq_true, ite_false] at hy
    obtain ⟨h1, h2⟩ := hy
    refine ⟨?_, ?_⟩
    · simp only [thI, Bool.false_eq_true, ite_false]
      exact mem_hull (by norm_num) (by norm_num) (by push_cast; linarith)
        (by push_cast; linarith)
    · unfold kOf
      split_ifs with hj23
      · have : (j : ℝ) ≤ 23 := by exact_mod_cast hj23
        refine ⟨by omega, ?_, ?_⟩ <;> push_cast [Nat.cast_sub hj23] <;>
          rw [abs_of_nonpos (by linarith)] <;> linarith
      · have hj24 : 24 ≤ j := by omega
        have : (24 : ℝ) ≤ j := by exact_mod_cast hj24
        refine ⟨by omega, ?_, ?_⟩ <;> push_cast [Nat.cast_sub hj24] <;>
          rw [abs_of_nonneg (by linarith)] <;> linarith
  · simp only [yB, ite_true] at hy
    obtain ⟨h1, h2⟩ := hy
    refine ⟨?_, ?_⟩
    · simp only [thI, ite_true]
      exact mem_hull (by norm_num) (by norm_num) (by push_cast; linarith)
        (by push_cast; linarith)
    · unfold kOf
      split_ifs with hj23
      · have : (j : ℝ) ≤ 23 := by exact_mod_cast hj23
        refine ⟨by omega, ?_, ?_⟩ <;> push_cast [Nat.cast_sub hj23] <;>
          rw [abs_of_nonneg (by linarith)] <;> linarith
      · have hj24 : 24 ≤ j := by omega
        have : (24 : ℝ) ≤ j := by exact_mod_cast hj24
        refine ⟨by omega, ?_, ?_⟩ <;> push_cast [Nat.cast_sub hj24] <;>
          rw [abs_of_nonpos (by linarith)] <;> linarith

/-- **A bottom point.** At a time `t` with `|θ| ≤ 3/5` whose bottom coordinate lies in the
`θ`-cell `j` of a valid bottom cell: `bDenT > 0`, `θ̇ = sgn · A · bDenT`, `θ ∈ thI inner j`, and
`Ω`, `A w` and `10⁶` are each a density of the cell times `A · bDenT`. -/
theorem bottom_point {P Tb : FIv} (hP : P.Mem (ψ 0)) (hTb : Tb.Mem (Eα / μ)) {inner : Bool}
    {t : ℝ} (ht : t ∈ Icc 0 T) (hx0 : 0 ≤ xOf inner ψ t) (hθ : |θ t| ≤ 3 / 5) {j : ℕ}
    (hj : j < 48) (hy : yB inner θ t ∈ Icc ((j : ℝ) * (1 / 40)) (((j : ℝ) + 1) * (1 / 40)))
    (hok : (bcell inner P Tb j).ok = true) :
    0 < bDenT μ ψ θ inner t ∧
      thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
        sgnL inner * (Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * bDenT μ ψ θ inner t) ∧
      (thI inner j).Mem (θ t) ∧
      (∃ r, (bcell inner P Tb j).om.Mem r ∧
        Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
          r * (Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * bDenT μ ψ θ inner t)) ∧
      (∃ r, (bcell inner P Tb j).g.Mem r ∧
        Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * (20 / 57 * ψ t) =
          r * (Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * bDenT μ ψ θ inner t)) ∧
      (∃ r, (bcell inner P Tb j).tt.Mem r ∧ (10 : ℝ) ^ 6 =
          r * (Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * bDenT μ ψ θ inner t)) ∧
      (bcell inner P Tb j).om.ok = true ∧ (bcell inner P Tb j).g.ok = true ∧
      (bcell inner P Tb j).tt.ok = true ∧ 0 ≤ fxVal (bcell inner P Tb j).om.lo := by
  have hrel := S.rel ht inner (psiR_xOf inner ψ t) hx0
  have hc := le_cos_of_bottom hθ
  obtain ⟨hthI, hk, hk1, hk2⟩ := bottom_cell_theta hj hy
  have hCT := mem_CTL hk hk1 hk2
  have hxlt : xOf inner ψ t ∈ Icc (0 : ℝ) (5 / 2) := by
    refine ⟨hx0, ?_⟩
    have := S.x_lt ht
    cases inner <;> simp only [xOf, Bool.false_eq_true, ite_true, ite_false] at hx0 ⊢ <;>
      [skip; rw [abs_sub_comm] at this] <;>
      linarith [le_abs_self (ψ t - ψ 0), le_abs_self (ψ 0 - ψ t)]
  obtain ⟨hden, hom, hg, htt, okom, okg, oktt, hom0⟩ :=
    bottomCellO_sound hok hP hTb hxlt hrel hc hCT
  have hA := S.Afac_pos ht
  have hAe := S.Afac_eq_AmR ht inner (psiR_xOf inner ψ t) hx0
  set d := bDenT μ ψ θ inner t with hd
  have hd' : bDenR inner (ψ 0) (xOf inner ψ t) (Eα / μ) (cos (θ t)) = d := rfl
  rw [hd'] at hden hom hg htt
  have hdne : d ≠ 0 := hden.ne'
  refine ⟨hden, ?_, hthI, ⟨_, hom, ?_⟩, ⟨_, hg, ?_⟩, ⟨_, htt, ?_⟩, okom, okg, oktt, hom0⟩
  · rw [S.thetaDot_eq ht inner hx0, hd]
    unfold bDenT bDenR
    cases inner <;> simp only [sgnL, Bool.false_eq_true, ite_true, ite_false] <;> ring
  · rw [Om_eq_num inner]; field_simp
  · rw [Aw_eq inner]; field_simp
  · have hAm : AmR (xOf inner ψ t) (Eα / μ) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hAe; exact hA.ne' hAe
    rw [hAe]; field_simp

/-! ## Generic flank and bottom pieces -/

/-- The amplitude integrand `A w` along the orbit. -/
theorem cont_Aw : ContinuousOn (fun t => Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
    (20 / 57 * ψ t)) (Icc 0 T) := S.cont_Afac.mul (continuousOn_const.mul S.cont_psi)

/-- `φ̇` is continuous along the orbit. -/
theorem cont_phiDotF : ContinuousOn (phiDotF ψ θ φ ρ) (Icc 0 T) := by
  unfold phiDotF
  exact (((continuousOn_const.mul S.cont_rho).mul (S.cont_B.pow 2)).div_const _)

/-- `φ` is continuous along the orbit. -/
theorem cont_phi : ContinuousOn φ (Icc 0 T) :=
  fun t ht => (S.orbit.dφ t ht).continuousAt.continuousWithinAt

/-- **Fundamental theorem for `φ`**: `φ b − φ a = ∫_a^b φ̇`. -/
theorem phi_sub_eq {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T) :
    φ b - φ a = ∫ t in a..b, phiDotF ψ θ φ ρ t := by
  have hsub : Icc a b ⊆ Icc 0 T := Icc_subset_Icc ha hbT
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := φ)]
  · intro t ht; rw [uIcc_of_le hab] at ht; exact S.orbit.dφ t (hsub ht)
  · apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hab]; exact S.cont_phiDotF.mono hsub

/-- **The flank end is past every flagged cell.** At a time `s` with `|θ s| = 3/5`, every cell
`i` with `fullPre i` lies below the leg coordinate. -/
theorem flag_of_end {P Tb : FIv} (hP : P.Mem (ψ 0)) (hTb : Tb.Mem (Eα / μ)) {inner : Bool}
    {s : ℝ} (hs : s ∈ Icc 0 T) (hx0 : 0 ≤ xOf inner ψ s) (hθs : |θ s| = 3 / 5) {i : ℕ}
    (hfull : fullPre inner P Tb i = true) : ((i : ℝ) + 1) * (1 / 40) ≤ xOf inner ψ s := by
  by_contra hcon
  push Not at hcon
  obtain ⟨j, hj, hyj⟩ := exists_cell_le hx0 hcon
  have hrel := S.rel hs inner (psiR_xOf inner ψ s) hx0
  have := flankCellO_full (fullPre_spec hfull j hj) (mem_cellX ((cell_iff j).mp hyj)) hP hTb hrel
  rw [← cos_abs, hθs] at this
  exact lt_irrefl _ this

/-- **Generic increasing flank piece.** On `[a, b] ⊆ [0, T]` with `|θ| ≥ 3/5`, where the leg
coordinate rises from `0` with `ẋ = A · denT`, and `|θ b| = 3/5`: the precession integral, the
time (in microseconds), the partial `|φ̇|`-integrals from `a` and, for any phase `Φ` enclosed by
`phF A σ`, the integrals of `A w cos Φ`, `A w sin Φ` are enclosed by the flank cells. -/
theorem flank_inc {P Tb : FIv} (hP : P.Mem (ψ 0)) (hTb : Tb.Mem (Eα / μ)) {inner : Bool}
    (hcells : okAll (fun i => (fcell inner P Tb i).ok) 100 = true)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T) {y' : ℝ → ℝ}
    (hy : ∀ t ∈ Icc a b, HasDerivAt (xOf inner ψ) (y' t) t) (hy'c : ContinuousOn y' (Icc a b))
    (hy'eq : ∀ t ∈ Icc a b,
      y' t = Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * denT ψ θ inner t)
    (hflank : ∀ t ∈ Icc a b, 3 / 5 ≤ |θ t|) (hx0 : ∀ t ∈ Icc a b, 0 ≤ xOf inner ψ t)
    (hya : xOf inner ψ a = 0) (hθb : |θ b| = 3 / 5) :
    (flankI inner P Tb).Mem (∫ t in a..b, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) ∧
      (flankTm inner P Tb).Mem (∫ _t in a..b, (10 : ℝ) ^ 6) ∧
      (∀ t ∈ Icc a b, ∀ i : ℕ, i ≤ 99 →
        xOf inner ψ t ∈ Icc ((i : ℝ) * (1 / 40)) (((i : ℝ) + 1) * (1 / 40)) →
        (accI (fun j => (fcell inner P Tb j).ph) i).Mem
          (∫ s in a..t, sgnL inner * phiDotF ψ θ φ ρ s)) ∧
      (∀ (Φ : ℝ → ℝ) (A : FIv) (σ : Bool), ContinuousOn Φ (Icc a b) →
        flankCSok A σ inner P Tb = true →
        (∀ t ∈ Icc a b, ∀ i : ℕ, i ≤ 99 →
          xOf inner ψ t ∈ Icc ((i : ℝ) * (1 / 40)) (((i : ℝ) + 1) * (1 / 40)) →
          (phF A σ inner P Tb i).Mem (Φ t)) →
        (flankCS A σ inner P Tb).1.Mem (∫ t in a..b,
          Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * (20 / 57 * ψ t) * cos (Φ t)) ∧
        (flankCS A σ inner P Tb).2.Mem (∫ t in a..b,
          Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * (20 / 57 * ψ t) * sin (Φ t))) := by
  have hsub : Icc a b ⊆ Icc 0 T := Icc_subset_Icc ha hbT
  have hI : ∀ t ∈ Icc a b, t ∈ Icc 0 T := fun t ht => hsub ht
  have hy'0 : ∀ t ∈ Icc a b, 0 ≤ y' t := fun t ht => by
    rw [hy'eq t ht, ← S.abs_Bθ_denT (hI t ht) inner (hx0 t ht)]
    exact mul_nonneg (S.Afac_pos (hI t ht)).le (abs_nonneg _)
  have hyb : xOf inner ψ b ≤ ((99 : ℕ) + 1 : ℝ) * (1 / 40) := by
    have := S.leg_x_lt (hI b ⟨hab, le_rfl⟩) (psiR_xOf inner ψ b) (hx0 b ⟨hab, le_rfl⟩)
    norm_num; linarith
  have hok : ∀ i : ℕ, i ≤ 99 → (fcell inner P Tb i).ok = true := fun i hi =>
    okAll_spec hcells i (by omega)
  have pt := fun t (ht : t ∈ Icc a b) (i : ℕ) (hi : i ≤ 99)
      (hyi : xOf inner ψ t ∈ Icc ((i : ℝ) * (1 / 40)) (((i : ℝ) + 1) * (1 / 40))) =>
    S.flank_point (φ := φ) hP hTb (hI t ht) (hx0 t ht) (hflank t ht) hyi (hok i hi)
  have hFl : ∀ i ≤ 99, fullPre inner P Tb i = true → ((i : ℝ) + 1) * (1 / 40) ≤ xOf inner ψ b :=
    fun i _ hf => S.flag_of_end hP hTb (hI b ⟨hab, le_rfl⟩) (hx0 b ⟨hab, le_rfl⟩) hθb hf
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact piece_tot hab hy hy'0 (S.cont_Om.mono hsub) hy'c hya hyb
      (fun t ht i hi hyi => by
        obtain ⟨-, -, -, ⟨r, hr, he⟩, -⟩ := pt t ht i hi hyi
        exact ⟨r, hr, by rw [he, hy'eq t ht]⟩)
      (fun i hi => (fcell_ok_fields (hok i hi)).1) hFl
  · exact piece_tot hab hy hy'0 continuousOn_const hy'c hya hyb
      (fun t ht i hi hyi => by
        obtain ⟨-, -, -, -, -, -, ⟨r, hr, he⟩, -⟩ := pt t ht i hi hyi
        exact ⟨r, hr, by rw [he, hy'eq t ht]⟩)
      (fun i hi => (fcell_ok_fields (hok i hi)).2.2.2) hFl
  · intro t ht i hi hyi
    exact piece_acc (Q := fun s => sgnL inner * phiDotF ψ θ φ ρ s) (n := 99) hy hy'0
      (continuousOn_const.mul (S.cont_phiDotF.mono hsub)) hy'c hya
      (fun t ht i hi hyi => by
        obtain ⟨-, -, -, -, ⟨r, hr, he⟩, -⟩ := pt t ht i hi hyi
        exact ⟨r, hr, by rw [he, hy'eq t ht]⟩)
      (fun i hi => (fcell_ok_fields (hok i hi)).2.1) ht hi hyi
  · intro Φ A σ hΦc hcs hΦ
    have hokD := okAll_spec hcs
    have hFc : ContinuousOn (fun t => Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
        (20 / 57 * ψ t)) (Icc a b) := S.cont_Aw.mono hsub
    have key : ∀ t ∈ Icc a b, ∀ i : ℕ, i ≤ 99 →
        xOf inner ψ t ∈ Icc ((i : ℝ) * (1 / 40)) (((i : ℝ) + 1) * (1 / 40)) →
        ∃ rg, (fcell inner P Tb i).g.Mem rg ∧
          Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * (20 / 57 * ψ t) = rg * y' t ∧
          flankD A σ inner P Tb i = ((fcell inner P Tb i).g.mul (cosSinC (phF A σ inner P Tb i)).1,
            (fcell inner P Tb i).g.mul (cosSinC (phF A σ inner P Tb i)).2) := by
      intro t ht i hi hyi
      obtain ⟨hdead, -, -, -, -, ⟨r, hr, he⟩, -⟩ := pt t ht i hi hyi
      refine ⟨r, hr, by rw [he, hy'eq t ht], ?_⟩
      unfold flankD; rw [hdead]; rfl
    constructor
    · refine piece_tot (D := fun i => (flankD A σ inner P Tb i).1) hab hy hy'0
        (hFc.mul (continuous_cos.comp_continuousOn hΦc)) hy'c hya hyb ?_
        (fun i hi => by have := hokD i (by omega); simp only [Bool.and_eq_true] at this
                        exact this.1) hFl
      intro t ht i hi hyi
      obtain ⟨rg, hrg, he, hD⟩ := key t ht i hi hyi
      refine ⟨rg * cos (Φ t), ?_, by rw [he]; ring⟩
      rw [hD]; exact FIv.mem_mul hrg (mem_cosSinC (hΦ t ht i hi hyi)).1
    · refine piece_tot (D := fun i => (flankD A σ inner P Tb i).2) hab hy hy'0
        (hFc.mul (continuous_sin.comp_continuousOn hΦc)) hy'c hya hyb ?_
        (fun i hi => by have := hokD i (by omega); simp only [Bool.and_eq_true] at this
                        exact this.2) hFl
      intro t ht i hi hyi
      obtain ⟨rg, hrg, he, hD⟩ := key t ht i hi hyi
      refine ⟨rg * sin (Φ t), ?_, by rw [he]; ring⟩
      rw [hD]; exact FIv.mem_mul hrg (mem_cosSinC (hΦ t ht i hi hyi)).2

/-- **Generic decreasing flank piece.** On `[a, b] ⊆ [0, T]` with `|θ| ≥ 3/5`, where the leg
coordinate falls to `0` at `b` with `ẋ = −A · denT`, and `|θ a| = 3/5`: as `flank_inc`, with the
partial `|φ̇|`-integrals taken up to the tip `b`. -/
theorem flank_dec {P Tb : FIv} (hP : P.Mem (ψ 0)) (hTb : Tb.Mem (Eα / μ)) {inner : Bool}
    (hcells : okAll (fun i => (fcell inner P Tb i).ok) 100 = true)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T) {y' : ℝ → ℝ}
    (hy : ∀ t ∈ Icc a b, HasDerivAt (xOf inner ψ) (y' t) t) (hy'c : ContinuousOn y' (Icc a b))
    (hy'eq : ∀ t ∈ Icc a b,
      y' t = -(Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * denT ψ θ inner t))
    (hflank : ∀ t ∈ Icc a b, 3 / 5 ≤ |θ t|) (hx0 : ∀ t ∈ Icc a b, 0 ≤ xOf inner ψ t)
    (hyb : xOf inner ψ b = 0) (hθa : |θ a| = 3 / 5) :
    (flankI inner P Tb).Mem (∫ t in a..b, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) ∧
      (flankTm inner P Tb).Mem (∫ _t in a..b, (10 : ℝ) ^ 6) ∧
      (∀ t ∈ Icc a b, ∀ i : ℕ, i ≤ 99 →
        xOf inner ψ t ∈ Icc ((i : ℝ) * (1 / 40)) (((i : ℝ) + 1) * (1 / 40)) →
        (accI (fun j => (fcell inner P Tb j).ph) i).Mem
          (∫ s in t..b, sgnL inner * phiDotF ψ θ φ ρ s)) ∧
      (∀ (Φ : ℝ → ℝ) (A : FIv) (σ : Bool), ContinuousOn Φ (Icc a b) →
        flankCSok A σ inner P Tb = true →
        (∀ t ∈ Icc a b, ∀ i : ℕ, i ≤ 99 →
          xOf inner ψ t ∈ Icc ((i : ℝ) * (1 / 40)) (((i : ℝ) + 1) * (1 / 40)) →
          (phF A σ inner P Tb i).Mem (Φ t)) →
        (flankCS A σ inner P Tb).1.Mem (∫ t in a..b,
          Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * (20 / 57 * ψ t) * cos (Φ t)) ∧
        (flankCS A σ inner P Tb).2.Mem (∫ t in a..b,
          Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * (20 / 57 * ψ t) * sin (Φ t))) := by
  have hsub : Icc a b ⊆ Icc 0 T := Icc_subset_Icc ha hbT
  have hI : ∀ t ∈ Icc a b, t ∈ Icc 0 T := fun t ht => hsub ht
  have hy'0 : ∀ t ∈ Icc a b, y' t ≤ 0 := fun t ht => by
    rw [hy'eq t ht, ← S.abs_Bθ_denT (hI t ht) inner (hx0 t ht), neg_nonpos]
    exact mul_nonneg (S.Afac_pos (hI t ht)).le (abs_nonneg _)
  have hya : xOf inner ψ a ≤ ((99 : ℕ) + 1 : ℝ) * (1 / 40) := by
    have := S.leg_x_lt (hI a ⟨le_rfl, hab⟩) (psiR_xOf inner ψ a) (hx0 a ⟨le_rfl, hab⟩)
    norm_num; linarith
  have hok : ∀ i : ℕ, i ≤ 99 → (fcell inner P Tb i).ok = true := fun i hi =>
    okAll_spec hcells i (by omega)
  have pt := fun t (ht : t ∈ Icc a b) (i : ℕ) (hi : i ≤ 99)
      (hyi : xOf inner ψ t ∈ Icc ((i : ℝ) * (1 / 40)) (((i : ℝ) + 1) * (1 / 40))) =>
    S.flank_point (φ := φ) hP hTb (hI t ht) (hx0 t ht) (hflank t ht) hyi (hok i hi)
  have hFl : ∀ i ≤ 99, fullPre inner P Tb i = true → ((i : ℝ) + 1) * (1 / 40) ≤ xOf inner ψ a :=
    fun i _ hf => S.flag_of_end hP hTb (hI a ⟨le_rfl, hab⟩) (hx0 a ⟨le_rfl, hab⟩) hθa hf
  have hneg : ∀ t ∈ Icc a b, -y' t =
      Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * denT ψ θ inner t := fun t ht => by
    rw [hy'eq t ht, neg_neg]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact piece_tot_rev hab hy hy'0 (S.cont_Om.mono hsub) hy'c hyb hya
      (fun t ht i hi hyi => by
        obtain ⟨-, -, -, ⟨r, hr, he⟩, -⟩ := pt t ht i hi hyi
        exact ⟨r, hr, by rw [he, hneg t ht]⟩)
      (fun i hi => (fcell_ok_fields (hok i hi)).1) hFl
  · exact piece_tot_rev hab hy hy'0 continuousOn_const hy'c hyb hya
      (fun t ht i hi hyi => by
        obtain ⟨-, -, -, -, -, -, ⟨r, hr, he⟩, -⟩ := pt t ht i hi hyi
        exact ⟨r, hr, by rw [he, hneg t ht]⟩)
      (fun i hi => (fcell_ok_fields (hok i hi)).2.2.2) hFl
  · intro t ht i hi hyi
    exact piece_acc_rev (Q := fun s => sgnL inner * phiDotF ψ θ φ ρ s) (n := 99) hy hy'0
      (continuousOn_const.mul (S.cont_phiDotF.mono hsub)) hy'c hyb
      (fun t ht i hi hyi => by
        obtain ⟨-, -, -, -, ⟨r, hr, he⟩, -⟩ := pt t ht i hi hyi
        exact ⟨r, hr, by rw [he, hneg t ht]⟩)
      (fun i hi => (fcell_ok_fields (hok i hi)).2.1) ht hi hyi
  · intro Φ A σ hΦc hcs hΦ
    have hokD := okAll_spec hcs
    have hFc : ContinuousOn (fun t => Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
        (20 / 57 * ψ t)) (Icc a b) := S.cont_Aw.mono hsub
    have key : ∀ t ∈ Icc a b, ∀ i : ℕ, i ≤ 99 →
        xOf inner ψ t ∈ Icc ((i : ℝ) * (1 / 40)) (((i : ℝ) + 1) * (1 / 40)) →
        ∃ rg, (fcell inner P Tb i).g.Mem rg ∧
          Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * (20 / 57 * ψ t) = rg * -y' t ∧
          flankD A σ inner P Tb i = ((fcell inner P Tb i).g.mul (cosSinC (phF A σ inner P Tb i)).1,
            (fcell inner P Tb i).g.mul (cosSinC (phF A σ inner P Tb i)).2) := by
      intro t ht i hi hyi
      obtain ⟨hdead, -, -, -, -, ⟨r, hr, he⟩, -⟩ := pt t ht i hi hyi
      refine ⟨r, hr, by rw [he, hneg t ht], ?_⟩
      unfold flankD; rw [hdead]; rfl
    constructor
    · refine piece_tot_rev (D := fun i => (flankD A σ inner P Tb i).1) hab hy hy'0
        (hFc.mul (continuous_cos.comp_continuousOn hΦc)) hy'c hyb hya ?_
        (fun i hi => by have := hokD i (by omega); simp only [Bool.and_eq_true] at this
                        exact this.1) hFl
      intro t ht i hi hyi
      obtain ⟨rg, hrg, he, hD⟩ := key t ht i hi hyi
      refine ⟨rg * cos (Φ t), ?_, by rw [he]; ring⟩
      rw [hD]; exact FIv.mem_mul hrg (mem_cosSinC (hΦ t ht i hi hyi)).1
    · refine piece_tot_rev (D := fun i => (flankD A σ inner P Tb i).2) hab hy hy'0
        (hFc.mul (continuous_sin.comp_continuousOn hΦc)) hy'c hyb hya ?_
        (fun i hi => by have := hokD i (by omega); simp only [Bool.and_eq_true] at this
                        exact this.2) hFl
      intro t ht i hi hyi
      obtain ⟨rg, hrg, he, hD⟩ := key t ht i hi hyi
      refine ⟨rg * sin (Φ t), ?_, by rw [he]; ring⟩
      rw [hD]; exact FIv.mem_mul hrg (mem_cosSinC (hΦ t ht i hi hyi)).2

/-- **Generic bottom piece.** On `[a, b] ⊆ [0, T]` with `|θ| ≤ 3/5`, where the bottom coordinate
`yB` rises from `0` to `6/5` with `ẏ = A · bDenT`: the precession integral, the time (in
microseconds), the partial precession integrals from `a` together with the `θ`-cell of each point
and, for any phase `Φ` enclosed by `phB`, the integrals of `A w cos Φ`, `A w sin Φ` are enclosed by
the bottom cells. -/
theorem bottom_piece {P Tb : FIv} (hP : P.Mem (ψ 0)) (hTb : Tb.Mem (Eα / μ)) {inner : Bool}
    (hcells : okAll (fun j => (bcell inner P Tb j).ok) 48 = true)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T) {y' : ℝ → ℝ}
    (hy : ∀ t ∈ Icc a b, HasDerivAt (yB inner θ) (y' t) t) (hy'c : ContinuousOn y' (Icc a b))
    (hy'eq : ∀ t ∈ Icc a b, y' t = sgnL inner * thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ)
      (ρ := ρ) t)
    (hbot : ∀ t ∈ Icc a b, |θ t| ≤ 3 / 5) (hx0 : ∀ t ∈ Icc a b, 0 ≤ xOf inner ψ t)
    (hya : yB inner θ a = 0) (hyb : yB inner θ b = 6 / 5) :
    (botI inner P Tb).Mem (∫ t in a..b, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) ∧
      (botTm inner P Tb).Mem (∫ _t in a..b, (10 : ℝ) ^ 6) ∧
      (∀ t ∈ Icc a b, ∀ j : ℕ, j ≤ 47 →
        yB inner θ t ∈ Icc ((j : ℝ) * (1 / 40)) (((j : ℝ) + 1) * (1 / 40)) →
        (accI (fun k => (bcell inner P Tb k).om) j).Mem
          (∫ s in a..t, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) s) ∧
        (thI inner j).Mem (θ t)) ∧
      (∀ (Φ : ℝ → ℝ) (Θ0 Is : FIv), ContinuousOn Φ (Icc a b) →
        botCSok Θ0 Is inner P Tb = true →
        (∀ t ∈ Icc a b, ∀ j : ℕ, j ≤ 47 →
          yB inner θ t ∈ Icc ((j : ℝ) * (1 / 40)) (((j : ℝ) + 1) * (1 / 40)) →
          (phB Θ0 Is inner P Tb j).Mem (Φ t)) →
        (botCS Θ0 Is inner P Tb).1.Mem (∫ t in a..b,
          Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * (20 / 57 * ψ t) * cos (Φ t)) ∧
        (botCS Θ0 Is inner P Tb).2.Mem (∫ t in a..b,
          Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * (20 / 57 * ψ t) * sin (Φ t))) := by
  have hsub : Icc a b ⊆ Icc 0 T := Icc_subset_Icc ha hbT
  have hI : ∀ t ∈ Icc a b, t ∈ Icc 0 T := fun t ht => hsub ht
  have hok : ∀ j : ℕ, j ≤ 47 → (bcell inner P Tb j).ok = true := fun j hj =>
    okAll_spec hcells j (by omega)
  have pt := fun t (ht : t ∈ Icc a b) (j : ℕ) (hj : j ≤ 47)
      (hyj : yB inner θ t ∈ Icc ((j : ℝ) * (1 / 40)) (((j : ℝ) + 1) * (1 / 40))) =>
    S.bottom_point (φ := φ) hP hTb (hI t ht) (hx0 t ht) (hbot t ht) (by omega) hyj (hok j hj)
  have hyeq : ∀ t ∈ Icc a b, ∀ j : ℕ, j ≤ 47 →
      yB inner θ t ∈ Icc ((j : ℝ) * (1 / 40)) (((j : ℝ) + 1) * (1 / 40)) →
      y' t = Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * bDenT μ ψ θ inner t := by
    intro t ht j hj hyj
    obtain ⟨-, hθd, -⟩ := pt t ht j hj hyj
    rw [hy'eq t ht, hθd, ← mul_assoc, sgnL_sq, one_mul]
  have hyr : ∀ t ∈ Icc a b, yB inner θ t ∈ Icc (0 : ℝ) ((((47 : ℕ) : ℝ) + 1) * (1 / 40)) := by
    intro t ht
    have := abs_le.mp (hbot t ht)
    cases inner <;> simp only [yB, Bool.false_eq_true, ite_true, ite_false] <;> push_cast <;>
      constructor <;> linarith
  have hy'0 : ∀ t ∈ Icc a b, 0 ≤ y' t := by
    intro t ht
    obtain ⟨j, hj, hyj⟩ := exists_cell_le' (hyr t ht).1 (hyr t ht).2
    rw [hyeq t ht j hj hyj]
    exact mul_nonneg (S.Afac_pos (hI t ht)).le (pt t ht j hj hyj).1.le
  have hyb' : yB inner θ b ≤ (((47 : ℕ) : ℝ) + 1) * (1 / 40) := by rw [hyb]; norm_num
  have hFl : ∀ j : ℕ, j ≤ 47 → true = true → ((j : ℝ) + 1) * (1 / 40) ≤ yB inner θ b := by
    intro j hj _
    rw [hyb]
    have : (j : ℝ) ≤ 47 := by exact_mod_cast hj
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact piece_tot hab hy hy'0 (S.cont_Om.mono hsub) hy'c hya hyb'
      (fun t ht j hj hyj => by
        obtain ⟨-, -, -, ⟨r, hr, he⟩, -⟩ := pt t ht j hj hyj
        exact ⟨r, hr, by rw [he, hyeq t ht j hj hyj]⟩)
      (fun j hj => (bcell_ok_fields (hok j hj)).1) hFl
  · exact piece_tot hab hy hy'0 continuousOn_const hy'c hya hyb'
      (fun t ht j hj hyj => by
        obtain ⟨-, -, -, -, -, ⟨r, hr, he⟩, -⟩ := pt t ht j hj hyj
        exact ⟨r, hr, by rw [he, hyeq t ht j hj hyj]⟩)
      (fun j hj => (bcell_ok_fields (hok j hj)).2.2) hFl
  · intro t ht j hj hyj
    refine ⟨piece_acc (n := 47) hy hy'0 (S.cont_Om.mono hsub) hy'c hya
      (fun t ht j hj hyj => by
        obtain ⟨-, -, -, ⟨r, hr, he⟩, -⟩ := pt t ht j hj hyj
        exact ⟨r, hr, by rw [he, hyeq t ht j hj hyj]⟩)
      (fun j hj => (bcell_ok_fields (hok j hj)).1) ht hj hyj, (pt t ht j hj hyj).2.2.1⟩
  · intro Φ Θ0 Is hΦc hcs hΦ
    have hokD := okAll_spec hcs
    have hFc : ContinuousOn (fun t => Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
        (20 / 57 * ψ t)) (Icc a b) := S.cont_Aw.mono hsub
    constructor
    · refine piece_tot hab hy hy'0 (hFc.mul (continuous_cos.comp_continuousOn hΦc)) hy'c hya
        hyb' ?_ (fun j hj => by have := hokD j (by omega); simp only [Bool.and_eq_true] at this
                                exact this.1) hFl
      intro t ht j hj hyj
      obtain ⟨-, -, -, -, ⟨r, hr, he⟩, -⟩ := pt t ht j hj hyj
      refine ⟨r * cos (Φ t), FIv.mem_mul hr (mem_cosSinC (hΦ t ht j hj hyj)).1, ?_⟩
      rw [he, hyeq t ht j hj hyj]; ring
    · refine piece_tot hab hy hy'0 (hFc.mul (continuous_sin.comp_continuousOn hΦc)) hy'c hya
        hyb' ?_ (fun j hj => by have := hokD j (by omega); simp only [Bool.and_eq_true] at this
                                exact this.2) hFl
      intro t ht j hj hyj
      obtain ⟨-, -, -, -, ⟨r, hr, he⟩, -⟩ := pt t ht j hj hyj
      refine ⟨r * sin (Φ t), FIv.mem_mul hr (mem_cosSinC (hΦ t ht j hj hyj)).2, ?_⟩
      rw [he, hyeq t ht j hj hyj]; ring

/-! ## The inner leg -/

/-- `Om` integrates to `θ`-and-`φ` differences: `ι₀ (φ t − φ a) = θ t − θ a + ∫_a^t Ω`. -/
theorem prec_eq {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) (htT : t ≤ T) :
    211 / 500 * (φ t - φ a) =
      θ t - θ a + ∫ s in a..t, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) s := by
  have h := precession_step (ι₀ := 211 / 500) (fun _ => rfl) S.orbit ha hat htT
    (S.cont_Bψ.mono (Icc_subset_Icc ha htT))
  have hOm : ∫ s in a..t, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) s =
      -∫ s in a..t, poloidalDrift exactQA mα qα μ ψ θ φ ρ s := by
    unfold Om; rw [intervalIntegral.integral_neg]
  rw [hOm, h]; ring

/-- At a turning point (`ψ = ψ₀`) the cosine of `θ` is the tip cosine. -/
theorem cos_tip_mem {P Tb : FIv} (hP : P.Mem (ψ 0)) (hTb : Tb.Mem (Eα / μ)) {t : ℝ}
    (ht : t ∈ Icc 0 T) (hψ : ψ t = ψ 0) : (c0I P Tb).Mem (cos (θ t)) := by
  have hx : psiR true (ψ 0) 0 = ψ t := by simp [psiR, hψ]
  have hrel := S.rel ht true hx le_rfl
  have := mem_cI (inner := true) (X := C 0 1) (x := 0) (mem_C (by norm_num)) hP hTb
  rwa [cR_eq hrel] at this

/-- **The inner leg.** For the inner leg `[0, z₁]` of an orbit of the start window
(`ρ(0) = ρ(z₁) = 0`, `ρ < 0` inside, `θ(0) > 3/5`, `θ(z₁) < −3/5`) with constants of motion in
`P × Tb`, if `legAOk P Tb Θ0 Cin Sin J1 Tin` holds then `θ(0) ∈ Θ0`, `θ(z₁) = −θ(0)`, and
`∫₀^{z₁} A w cos 2(φ − φ₀) ∈ Cin`, `∫₀^{z₁} A w sin 2(φ − φ₀) ∈ Sin`, `∫₀^{z₁} Ω ∈ J1`,
`10⁶ z₁ ∈ Tin`. -/
theorem inner_leg_osc {P Tb Θ0 Cin Sin J1 Tin : FIv} (hP : P.Mem (ψ 0))
    (hTb : Tb.Mem (Eα / μ)) (hA : legAOk P Tb Θ0 Cin Sin J1 Tin = true)
    {Mf : ℕ → ℝ} {Mb mb : ℝ} (cert : LegBounds true (ψ 0) (Eα / μ) Mf Mb mb)
    {z₁ : ℝ} (hz₁ : 0 < z₁) (hz₁T : z₁ ≤ T) (hρz₁ : ρ z₁ = 0)
    (hneg : ∀ t ∈ Ioo 0 z₁, ρ t < 0) (hθ0 : 3 / 5 < θ 0) (hθz₁ : θ z₁ < -(3 / 5)) :
    Θ0.Mem (θ 0) ∧ θ z₁ = -θ 0 ∧
      Cin.Mem (∫ t in (0 : ℝ)..z₁, Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
        (20 / 57 * ψ t) * cos (2 * (φ t - φ 0))) ∧
      Sin.Mem (∫ t in (0 : ℝ)..z₁, Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
        (20 / 57 * ψ t) * sin (2 * (φ t - φ 0))) ∧
      J1.Mem (∫ t in (0 : ℝ)..z₁, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) ∧
      Tin.Mem (10 ^ 6 * z₁) := by
  simp only [legAOk, legOk, Bool.and_eq_true] at hA
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hfc, hbc⟩, hth⟩, hcs0⟩, hcs1⟩, hcs2⟩, hC⟩, hS⟩, hJ⟩, hTm⟩ := hA
  rw [← eq_of_eqI hC, ← eq_of_eqI hS, ← eq_of_eqI hJ, ← eq_of_eqI hTm]
  have hT0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hz₁.le.trans hz₁T⟩
  obtain ⟨s1, s2, hs1, hs12, hs2, hθs1, hθs2, hfl1, hbot, hfl3, hx0, hθd, -, hψz₁⟩ :=
    S.inner_split cert le_rfl hz₁ hz₁T S.rho0 hρz₁ hneg hθ0 hθz₁
  have hI : ∀ t ∈ Icc 0 z₁, t ∈ Icc 0 T := fun t ht => ⟨ht.1, ht.2.trans hz₁T⟩
  -- the tip angle
  have hθ0mem : Θ0.Mem (θ 0) := theta0_sound hth (S.cos_tip_mem hP hTb hT0 rfl)
    ⟨S.theta0.1.le, by linarith [S.theta0.2, pi_lt_d2]⟩
  have hθz₁eq : θ z₁ = -θ 0 := by
    have hc : cos (θ z₁) = cos (θ 0) := by
      have h1 := S.cos_tip_mem hP hTb (hI z₁ ⟨hz₁.le, le_rfl⟩) hψz₁
      have hx : psiR true (ψ 0) 0 = ψ z₁ := by simp [psiR, hψz₁]
      have hx' : psiR true (ψ 0) 0 = ψ 0 := by simp [psiR]
      rw [← cR_eq (S.rel (hI z₁ ⟨hz₁.le, le_rfl⟩) true hx le_rfl),
        ← cR_eq (S.rel hT0 true hx' le_rfl)]
    have := (S.theta (hI z₁ ⟨hz₁.le, le_rfl⟩)).1
    have h2 := injOn_cos (x₁ := -θ z₁) (x₂ := θ 0) ⟨by linarith, by linarith [pi_pos]⟩
      ⟨S.theta0.1.le, by linarith [S.theta0.2, pi_pos]⟩ (by rw [cos_neg, hc])
    linarith
  -- piece 1: upper flank `[0, s1]`
  have hxd : ∀ t ∈ Icc 0 T, HasDerivAt (xOf true ψ)
      (-psiDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) t := by
    intro t ht
    have : xOf true ψ = fun s => ψ 0 - ψ s := by funext s; simp [xOf]
    rw [this]; exact (S.hasDerivAt_psi ht).const_sub (ψ 0)
  have hBθ : ∀ t ∈ Icc 0 z₁, -psiDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
      Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * along exactQA.Bθ ψ θ φ t := by
    intro t _; rw [psiDot_eq, neg_neg]
  have hden : ∀ t ∈ Icc 0 z₁, |along exactQA.Bθ ψ θ φ t| = denT ψ θ true t := fun t ht =>
    S.abs_Bθ_denT (hI t ht) true (hx0 t ht)
  have hs1z : s1 ≤ z₁ := hs12.trans hs2.le
  have F1 := S.flank_inc (φ := φ) hP hTb hfc le_rfl hs1.le (hs1z.trans hz₁T)
    (y' := fun t => -psiDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t)
    (fun t ht => hxd t ⟨ht.1, ht.2.trans (hs1z.trans hz₁T)⟩)
    (S.cont_psiDot.neg.mono (Icc_subset_Icc le_rfl (hs1z.trans hz₁T)))
    (fun t ht => by
      have ht' : t ∈ Icc 0 z₁ := ⟨ht.1, ht.2.trans hs1z⟩
      rw [hBθ t ht', ← hden t ht', abs_of_pos (S.Bθ_pos (hI t ht') (by linarith [hfl1 t ht]))])
    (fun t ht => (hfl1 t ht).trans (le_abs_self _))
    (fun t ht => hx0 t ⟨ht.1, ht.2.trans hs1z⟩) (by simp [xOf])
    (by rw [hθs1]; norm_num)
  -- piece 2: bottom `[s1, s2]`
  have hs10 : 0 ≤ s1 := hs1.le
  have hs2T : s2 ≤ T := hs2.le.trans hz₁T
  have hyd : ∀ t ∈ Icc 0 T, HasDerivAt (yB true θ)
      (-thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) t := by
    intro t ht
    have : yB true θ = fun s => 3 / 5 - θ s := by funext s; simp [yB]
    rw [this]; exact (S.hasDerivAt_theta ht).const_sub (3 / 5)
  have B2 := S.bottom_piece (φ := φ) hP hTb hbc hs10 hs12 hs2T
    (y' := fun t => -thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t)
    (fun t ht => hyd t ⟨hs10.trans ht.1, ht.2.trans hs2T⟩)
    (S.cont_thetaDot.neg.mono (Icc_subset_Icc hs10 hs2T))
    (fun t _ => by simp [sgnL])
    hbot (fun t ht => hx0 t ⟨hs10.trans ht.1, ht.2.trans hs2.le⟩)
    (by simp [yB, hθs1]) (by simp [yB, hθs2]; norm_num)
  -- piece 3: lower flank `[s2, z₁]`
  have hs20 : 0 ≤ s2 := hs10.trans hs12
  have F3 := S.flank_dec (φ := φ) hP hTb hfc hs20 hs2.le hz₁T
    (y' := fun t => -psiDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t)
    (fun t ht => hxd t ⟨hs20.trans ht.1, ht.2.trans hz₁T⟩)
    (S.cont_psiDot.neg.mono (Icc_subset_Icc hs20 hz₁T))
    (fun t ht => by
      have ht' : t ∈ Icc 0 z₁ := ⟨hs20.trans ht.1, ht.2⟩
      rw [hBθ t ht', ← hden t ht', abs_of_neg (S.Bθ_neg (hI t ht') (by linarith [hfl3 t ht]))]
      ring)
    (fun t ht => by rw [abs_of_neg (by linarith [hfl3 t ht])]; linarith [hfl3 t ht])
    (fun t ht => hx0 t ⟨hs20.trans ht.1, ht.2⟩) (by simp [xOf, hψz₁])
    (by rw [hθs2]; norm_num)
  -- the precession integrals
  have hOmc : ContinuousOn (Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ)) (Icc 0 z₁) :=
    S.cont_Om.mono (Icc_subset_Icc le_rfl hz₁T)
  have hIz1 : (Iz1 P Tb).Mem (∫ t in (0 : ℝ)..z₁,
      Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) := by
    rw [integral_split3 hOmc hs10 hs12 hs2.le]
    exact FIv.mem_add (FIv.mem_add F1.1 B2.1) F3.1
  -- the phase `Φ = 2 (φ − φ₀)`
  have hΦc : ContinuousOn (fun t => 2 * (φ t - φ 0)) (Icc 0 T) :=
    continuousOn_const.mul (S.cont_phi.sub continuousOn_const)
  have h2 : (C 2 1).Mem 2 := mem_C (by norm_num)
  have hκ : (C 1000 211).Mem (1000 / 211) := mem_C (by norm_num)
  have hphase1 : ∀ t ∈ Icc 0 s1, ∀ i : ℕ, i ≤ 99 →
      xOf true ψ t ∈ Icc ((i : ℝ) * (1 / 40)) (((i : ℝ) + 1) * (1 / 40)) →
      (phF zeroI false true P Tb i).Mem (2 * (φ t - φ 0)) := by
    intro t ht i hi hyi
    have hacc := F1.2.2.1 t ht i hi hyi
    have he : ∫ s in (0 : ℝ)..t, sgnL true * phiDotF ψ θ φ ρ s = -(φ t - φ 0) := by
      rw [intervalIntegral.integral_const_mul, S.phi_sub_eq le_rfl ht.1 (ht.2.trans
        (hs1z.trans hz₁T))]
      simp [sgnL]
    rw [he] at hacc
    have := FIv.mem_sub (I := zeroI) (x := 0) (fun _ => ⟨by simp [zeroI, fxVal], by
      simp [zeroI, fxVal]⟩) (FIv.mem_mul h2 hacc)
    simp only [phF, Bool.false_eq_true, ite_false]
    convert this using 1; ring
  have hphase2 : ∀ t ∈ Icc s1 s2, ∀ j : ℕ, j ≤ 47 →
      yB true θ t ∈ Icc ((j : ℝ) * (1 / 40)) (((j : ℝ) + 1) * (1 / 40)) →
      (phB Θ0 (Is1 P Tb) true P Tb j).Mem (2 * (φ t - φ 0)) := by
    intro t ht j hj hyj
    obtain ⟨hacc, hth⟩ := B2.2.2.1 t ht j hj hyj
    have hp := S.prec_eq le_rfl (hs10.trans ht.1) (ht.2.trans hs2T)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume) (f := Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ))
      (a := 0) (b := s1) (c := t)
      (by apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hs10]
          exact hOmc.mono (Icc_subset_Icc le_rfl hs1z))
      (by apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le ht.1]
          exact hOmc.mono (Icc_subset_Icc hs10 (ht.2.trans hs2.le)))
    have := FIv.mem_mul hκ (FIv.mem_add (FIv.mem_sub hth hθ0mem) (FIv.mem_add F1.1 hacc))
    have hval : 2 * (φ t - φ 0) = 1000 / 211 * (θ t - θ 0 +
        ((∫ s in (0 : ℝ)..s1, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) s) +
          ∫ s in s1..t, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) s)) := by
      rw [hsplit]; linarith
    rw [hval]; exact this
  have hz1mem : (phZ1 Θ0 (Iz1 P Tb)).Mem (2 * (φ z₁ - φ 0)) := by
    have hp := S.prec_eq le_rfl hz₁.le hz₁T
    have := FIv.mem_mul hκ (FIv.mem_add (FIv.mem_mul hθ0mem
      (mem_C (p := -2) (q := 1) (r := -2) (by norm_num))) hIz1)
    unfold phZ1
    convert this using 1
    rw [hθz₁eq] at hp
    linarith
  have hphase3 : ∀ t ∈ Icc s2 z₁, ∀ i : ℕ, i ≤ 99 →
      xOf true ψ t ∈ Icc ((i : ℝ) * (1 / 40)) (((i : ℝ) + 1) * (1 / 40)) →
      (phF (phZ1 Θ0 (Iz1 P Tb)) true true P Tb i).Mem (2 * (φ t - φ 0)) := by
    intro t ht i hi hyi
    have hacc := F3.2.2.1 t ht i hi hyi
    have he : ∫ s in t..z₁, sgnL true * phiDotF ψ θ φ ρ s = φ t - φ z₁ := by
      rw [intervalIntegral.integral_const_mul, ← S.phi_sub_eq (hs20.trans ht.1) ht.2 hz₁T]
      simp [sgnL]
    rw [he] at hacc
    have := FIv.mem_add hz1mem (FIv.mem_mul h2 hacc)
    simp only [phF, ite_true]
    convert this using 1; ring
  -- the oscillatory integrals
  have hz₁s : Icc 0 z₁ ⊆ Icc 0 T := Icc_subset_Icc le_rfl hz₁T
  obtain ⟨C1, S1⟩ := F1.2.2.2 (fun t => 2 * (φ t - φ 0)) zeroI false
    (hΦc.mono (Icc_subset_Icc le_rfl (hs1z.trans hz₁T))) hcs0 hphase1
  obtain ⟨C2, S2⟩ := B2.2.2.2 (fun t => 2 * (φ t - φ 0)) Θ0 (Is1 P Tb)
    (hΦc.mono (Icc_subset_Icc hs10 hs2T)) hcs1 hphase2
  obtain ⟨C3, S3⟩ := F3.2.2.2 (fun t => 2 * (φ t - φ 0)) (phZ1 Θ0 (Iz1 P Tb)) true
    (hΦc.mono (Icc_subset_Icc hs20 hz₁T)) hcs2 hphase3
  have hGc : ∀ f : ℝ → ℝ, Continuous f → ContinuousOn (fun t =>
      Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * (20 / 57 * ψ t) *
        f (2 * (φ t - φ 0))) (Icc 0 z₁) := fun f hf =>
    (S.cont_Aw.mono hz₁s).mul (hf.comp_continuousOn (hΦc.mono hz₁s))
  refine ⟨hθ0mem, hθz₁eq, ?_, ?_, hIz1, ?_⟩
  · rw [integral_split3 (hGc cos continuous_cos) hs10 hs12 hs2.le]
    exact FIv.mem_add (FIv.mem_add C1 C2) C3
  · rw [integral_split3 (hGc sin continuous_sin) hs10 hs12 hs2.le]
    exact FIv.mem_add (FIv.mem_add S1 S2) S3
  · have hT1 := F1.2.1
    have hT2 := B2.2.1
    have hT3 := F3.2.1
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hT1 hT2 hT3
    have := FIv.mem_add (mem_two hT1 hT3) hT2
    unfold legTm
    convert this using 1; ring

/-! ## The outer leg -/

/-- **The outer leg.** For the outer leg `[z₁, z₂]` (`ρ(z₁) = ρ(z₂) = 0`, `ρ > 0` inside,
`θ(z₁) < −3/5`, `θ(z₂) > 3/5`, `θ(z₂) = θ(0)`) of an orbit with constants of motion in `P × Tb`,
given `θ(0) ∈ Θ0`, `θ(z₁) = −θ(0)` and `∫₀^{z₁} Ω ∈ J1` (from `inner_leg_osc`), if
`legBOk P Tb Θ0 J1 Cout Sout J2 Tout` holds then the outer-leg integrals of `A w cos 2(φ − φ₀)`,
`A w sin 2(φ − φ₀)` lie in `Cout`, `Sout`, `∫₀^{z₂} Ω ∈ J2` and `10⁶ (z₂ − z₁) ∈ Tout`. -/
theorem outer_leg_osc {P Tb Θ0 J1 Cout Sout J2 Tout : FIv} (hP : P.Mem (ψ 0))
    (hTb : Tb.Mem (Eα / μ)) (hB : legBOk P Tb Θ0 J1 Cout Sout J2 Tout = true)
    {Mf : ℕ → ℝ} {Mb mb : ℝ} (cert : LegBounds false (ψ 0) (Eα / μ) Mf Mb mb)
    {z₁ z₂ : ℝ} (hz₁ : 0 < z₁) (hz₁₂ : z₁ < z₂) (hz₂T : z₂ ≤ T) (hρz₁ : ρ z₁ = 0)
    (hρz₂ : ρ z₂ = 0) (hpos : ∀ t ∈ Ioo z₁ z₂, 0 < ρ t) (hθz₁ : θ z₁ < -(3 / 5))
    (hθz₂ : 3 / 5 < θ z₂) (hθz₂eq : θ z₂ = θ 0) (hΘ : Θ0.Mem (θ 0)) (hθz₁eq : θ z₁ = -θ 0)
    (hJ1 : J1.Mem (∫ t in (0 : ℝ)..z₁, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t)) :
    Cout.Mem (∫ t in z₁..z₂, Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
        (20 / 57 * ψ t) * cos (2 * (φ t - φ 0))) ∧
      Sout.Mem (∫ t in z₁..z₂, Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
        (20 / 57 * ψ t) * sin (2 * (φ t - φ 0))) ∧
      J2.Mem (∫ t in (0 : ℝ)..z₂, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) ∧
      Tout.Mem (10 ^ 6 * (z₂ - z₁)) := by
  simp only [legBOk, legOk, Bool.and_eq_true] at hB
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hfc, hbc⟩, hcs0⟩, hcs1⟩, hcs2⟩, hJ⟩, hC⟩, hS⟩, hTm⟩ := hB
  rw [← eq_of_eqI hC, ← eq_of_eqI hS, ← eq_of_eqI hTm]
  obtain ⟨s1, s2, hs1, hs12, hs2, hθs1, hθs2, hfl1, hbot, hfl3, hx0, -, hψz₁, hψz₂⟩ :=
    S.outer_split cert hz₁.le hz₁₂ hz₂T hρz₁ hρz₂ hpos hθz₁ hθz₂
  have hI : ∀ t ∈ Icc z₁ z₂, t ∈ Icc 0 T := fun t ht => ⟨hz₁.le.trans ht.1, ht.2.trans hz₂T⟩
  have hxd : ∀ t ∈ Icc 0 T, HasDerivAt (xOf false ψ)
      (psiDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) t := by
    intro t ht
    have : xOf false ψ = fun s => ψ s - ψ 0 := by funext s; simp [xOf]
    rw [this]; exact (S.hasDerivAt_psi ht).sub_const (ψ 0)
  have hBθ : ∀ t ∈ Icc z₁ z₂, psiDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
      -(Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * along exactQA.Bθ ψ θ φ t) :=
    fun t _ => psiDot_eq t
  have hden : ∀ t ∈ Icc z₁ z₂, |along exactQA.Bθ ψ θ φ t| = denT ψ θ false t := fun t ht =>
    S.abs_Bθ_denT (hI t ht) false (hx0 t ht)
  have hs1z : s1 ≤ z₂ := hs12.trans hs2.le
  have hs10 : 0 ≤ s1 := hz₁.le.trans hs1.le
  have hs20 : 0 ≤ s2 := hs10.trans hs12
  have hs2T : s2 ≤ T := hs2.le.trans hz₂T
  -- piece 1: lower flank `[z₁, s1]`
  have F1 := S.flank_inc (φ := φ) hP hTb hfc hz₁.le hs1.le (hs1z.trans hz₂T)
    (y' := fun t => psiDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t)
    (fun t ht => hxd t ⟨hz₁.le.trans ht.1, ht.2.trans (hs1z.trans hz₂T)⟩)
    (S.cont_psiDot.mono (Icc_subset_Icc hz₁.le (hs1z.trans hz₂T)))
    (fun t ht => by
      have ht' : t ∈ Icc z₁ z₂ := ⟨ht.1, ht.2.trans hs1z⟩
      rw [hBθ t ht', ← hden t ht', abs_of_neg (S.Bθ_neg (hI t ht') (by linarith [hfl1 t ht]))]
      ring)
    (fun t ht => by rw [abs_of_neg (by linarith [hfl1 t ht])]; linarith [hfl1 t ht])
    (fun t ht => hx0 t ⟨ht.1, ht.2.trans hs1z⟩) (by simp [xOf, hψz₁])
    (by rw [hθs1]; norm_num)
  -- piece 2: bottom `[s1, s2]`
  have B2 := S.bottom_piece (φ := φ) hP hTb hbc hs10 hs12 hs2T
    (y' := fun t => thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t)
    (fun t ht => by
      have : yB false θ = fun s => θ s + 3 / 5 := by funext s; simp [yB]
      rw [this]; exact (S.hasDerivAt_theta ⟨hs10.trans ht.1, ht.2.trans hs2T⟩).add_const _)
    (S.cont_thetaDot.mono (Icc_subset_Icc hs10 hs2T))
    (fun t _ => by simp [sgnL])
    hbot (fun t ht => hx0 t ⟨hs1.le.trans ht.1, ht.2.trans hs2.le⟩)
    (by simp [yB, hθs1]) (by simp [yB, hθs2]; norm_num)
  -- piece 3: upper flank `[s2, z₂]`
  have F3 := S.flank_dec (φ := φ) hP hTb hfc hs20 hs2.le hz₂T
    (y' := fun t => psiDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t)
    (fun t ht => hxd t ⟨hs20.trans ht.1, ht.2.trans hz₂T⟩)
    (S.cont_psiDot.mono (Icc_subset_Icc hs20 hz₂T))
    (fun t ht => by
      have ht' : t ∈ Icc z₁ z₂ := ⟨hs1.le.trans (hs12.trans ht.1), ht.2⟩
      rw [hBθ t ht', ← hden t ht', abs_of_pos (S.Bθ_pos (hI t ht') (by linarith [hfl3 t ht]))])
    (fun t ht => (hfl3 t ht).trans (le_abs_self _))
    (fun t ht => hx0 t ⟨hs1.le.trans (hs12.trans ht.1), ht.2⟩) (by simp [xOf, hψz₂])
    (by rw [hθs2]; norm_num)
  -- the precession integrals
  have hOmc : ContinuousOn (Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ)) (Icc 0 z₂) :=
    S.cont_Om.mono (Icc_subset_Icc le_rfl hz₂T)
  have hii : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ z₂ →
      IntervalIntegrable (Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ))
        MeasureTheory.volume u v := by
    intro u v hu huv hv
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le huv]; exact hOmc.mono (Icc_subset_Icc hu hv)
  have hsplitz : ∀ v, z₁ ≤ v → v ≤ z₂ →
      ∫ t in (0 : ℝ)..v, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
        (∫ t in (0 : ℝ)..z₁, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) +
          ∫ t in z₁..v, Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t := fun v hv1 hv2 =>
    (intervalIntegral.integral_add_adjacent_intervals (hii 0 z₁ le_rfl hz₁.le (hv1.trans hv2))
      (hii z₁ v hz₁.le hv1 hv2)).symm
  have hIz2 : (Iz2 J1 P Tb).Mem (∫ t in (0 : ℝ)..z₂,
      Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) := by
    rw [hsplitz z₂ hz₁₂.le le_rfl, integral_split3 (hOmc.mono (Icc_subset_Icc hz₁.le le_rfl))
      hs1.le hs12 hs2.le]
    have := FIv.mem_add (FIv.mem_add (FIv.mem_add hJ1 F1.1) B2.1) F3.1
    unfold Iz2 Is3
    convert this using 1; ring
  rw [eq_of_eqI hJ] at hIz2
  -- the phase
  have hΦc : ContinuousOn (fun t => 2 * (φ t - φ 0)) (Icc 0 T) :=
    continuousOn_const.mul (S.cont_phi.sub continuousOn_const)
  have h2 : (C 2 1).Mem 2 := mem_C (by norm_num)
  have hκ : (C 1000 211).Mem (1000 / 211) := mem_C (by norm_num)
  have hz1mem : (phZ1 Θ0 J1).Mem (2 * (φ z₁ - φ 0)) := by
    have hp := S.prec_eq le_rfl hz₁.le (hz₁₂.le.trans hz₂T)
    have := FIv.mem_mul hκ (FIv.mem_add (FIv.mem_mul hΘ
      (mem_C (p := -2) (q := 1) (r := -2) (by norm_num))) hJ1)
    unfold phZ1
    convert this using 1
    rw [hθz₁eq] at hp
    linarith
  have hz2mem : (phZ2 J2).Mem (2 * (φ z₂ - φ 0)) := by
    have hp := S.prec_eq le_rfl (hz₁.le.trans hz₁₂.le) hz₂T
    have := FIv.mem_mul hκ hIz2
    unfold phZ2
    convert this using 1
    rw [hθz₂eq] at hp
    linarith
  have hphase1 : ∀ t ∈ Icc z₁ s1, ∀ i : ℕ, i ≤ 99 →
      xOf false ψ t ∈ Icc ((i : ℝ) * (1 / 40)) (((i : ℝ) + 1) * (1 / 40)) →
      (phF (phZ1 Θ0 J1) true false P Tb i).Mem (2 * (φ t - φ 0)) := by
    intro t ht i hi hyi
    have hacc := F1.2.2.1 t ht i hi hyi
    have he : ∫ s in z₁..t, sgnL false * phiDotF ψ θ φ ρ s = φ t - φ z₁ := by
      rw [intervalIntegral.integral_const_mul, ← S.phi_sub_eq hz₁.le ht.1
        (ht.2.trans (hs1z.trans hz₂T))]
      simp [sgnL]
    rw [he] at hacc
    have := FIv.mem_add hz1mem (FIv.mem_mul h2 hacc)
    simp only [phF, ite_true]
    convert this using 1; ring
  have hphase2 : ∀ t ∈ Icc s1 s2, ∀ j : ℕ, j ≤ 47 →
      yB false θ t ∈ Icc ((j : ℝ) * (1 / 40)) (((j : ℝ) + 1) * (1 / 40)) →
      (phB Θ0 (Is3 J1 P Tb) false P Tb j).Mem (2 * (φ t - φ 0)) := by
    intro t ht j hj hyj
    obtain ⟨hacc, hth⟩ := B2.2.2.1 t ht j hj hyj
    have hp := S.prec_eq le_rfl (hs10.trans ht.1) (ht.2.trans hs2T)
    have hsp1 := hsplitz t (hs1.le.trans ht.1) (ht.2.trans hs2.le)
    have hsp2 := intervalIntegral.integral_add_adjacent_intervals
      (hii z₁ s1 hz₁.le hs1.le hs1z) (hii s1 t hs10 ht.1 (ht.2.trans hs2.le))
    have := FIv.mem_mul hκ (FIv.mem_add (FIv.mem_sub hth hΘ)
      (FIv.mem_add (FIv.mem_add hJ1 F1.1) hacc))
    unfold phB Is3
    convert this using 1
    linarith
  have hphase3 : ∀ t ∈ Icc s2 z₂, ∀ i : ℕ, i ≤ 99 →
      xOf false ψ t ∈ Icc ((i : ℝ) * (1 / 40)) (((i : ℝ) + 1) * (1 / 40)) →
      (phF (phZ2 J2) false false P Tb i).Mem (2 * (φ t - φ 0)) := by
    intro t ht i hi hyi
    have hacc := F3.2.2.1 t ht i hi hyi
    have he : ∫ s in t..z₂, sgnL false * phiDotF ψ θ φ ρ s = φ z₂ - φ t := by
      rw [intervalIntegral.integral_const_mul, ← S.phi_sub_eq (hs20.trans ht.1) ht.2 hz₂T]
      simp [sgnL]
    rw [he] at hacc
    have := FIv.mem_sub hz2mem (FIv.mem_mul h2 hacc)
    simp only [phF, Bool.false_eq_true, ite_false]
    convert this using 1; ring
  -- the oscillatory integrals
  have hzs : Icc z₁ z₂ ⊆ Icc 0 T := Icc_subset_Icc hz₁.le hz₂T
  obtain ⟨C1, S1⟩ := F1.2.2.2 (fun t => 2 * (φ t - φ 0)) (phZ1 Θ0 J1) true
    (hΦc.mono (Icc_subset_Icc hz₁.le (hs1z.trans hz₂T))) hcs0 hphase1
  obtain ⟨C2, S2⟩ := B2.2.2.2 (fun t => 2 * (φ t - φ 0)) Θ0 (Is3 J1 P Tb)
    (hΦc.mono (Icc_subset_Icc hs10 hs2T)) hcs1 hphase2
  obtain ⟨C3, S3⟩ := F3.2.2.2 (fun t => 2 * (φ t - φ 0)) (phZ2 J2) false
    (hΦc.mono (Icc_subset_Icc hs20 hz₂T)) hcs2 hphase3
  have hGc : ∀ f : ℝ → ℝ, Continuous f → ContinuousOn (fun t =>
      Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * (20 / 57 * ψ t) *
        f (2 * (φ t - φ 0))) (Icc z₁ z₂) := fun f hf =>
    (S.cont_Aw.mono hzs).mul (hf.comp_continuousOn (hΦc.mono hzs))
  refine ⟨?_, ?_, hIz2, ?_⟩
  · rw [integral_split3 (hGc cos continuous_cos) hs1.le hs12 hs2.le]
    exact FIv.mem_add (FIv.mem_add C1 C2) C3
  · rw [integral_split3 (hGc sin continuous_sin) hs1.le hs12 hs2.le]
    exact FIv.mem_add (FIv.mem_add S1 S2) S3
  · have hT1 := F1.2.1
    have hT2 := B2.2.1
    have hT3 := F3.2.1
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hT1 hT2 hT3
    have := FIv.mem_add (mem_two hT1 hT3) hT2
    unfold legTm
    convert this using 1; ring

end PlasmaLean.Design.NearAxisQATrappedResonance.Setup
