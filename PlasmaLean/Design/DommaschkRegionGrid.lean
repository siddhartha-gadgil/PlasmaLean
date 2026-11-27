/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkRegionEnclosure

/-!
# An adaptive grid on the spatial envelope of QA2R, for all angles

The envelope `7/8 ≤ R ≤ 1`, `|z| ≤ 5/64` and the unit circle of `(cos 2φ, sin 2φ)` are covered by
boxes, on each of which the Boolean check `good` of `DommaschkRegionEnclosure` is evaluated by the
kernel (in the generated modules `DommaschkRegionRows00`–`23`), after subdivision in `(u, z)`
where the check fails on the whole box (`Cert`).

* `thresholds`: `b₀ = 47/50`, `c₁ = 13/10`, `M = 9/25`.
* `cell i j f m`: `u`-cell `i < 4` of width `1/32`, `z`-cell `j < 2` of width `5/128` in
  `0 ≤ z ≤ 5/64`, and the arc `m < 12` of the family `f < 8` of the unit circle: one coordinate
  (in absolute value) lies in `[m/16, (m+1)/16]`, the other is positive or negative and is enclosed
  by checked integer square roots (`arc_valid`).
* `cover`: these boxes cover the half `z ≥ 0` of the envelope and the whole circle.
* `reflect_even`, `reflect_odd`: the reflection `(z, s) ↦ (−z, −s)` (stellarator symmetry) gives
  the half `z ≤ 0`.
* `bounds_of_rows`: if every cell has a subdivision certificate then `b₀ R⁷ ≤ D ≤ c₁ R⁷` and
  `n_R² + n_z² ≤ M² D²` on the envelope at all angles.

**Sanity.** `exists_cell_fixture`, `arc_valid` (the checked square roots), and the parity checks
`parity_D`, `parity_R`, `parity_Z`; `parity_reject` shows that the parity test is not vacuous.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkRegionGrid
open DommaschkKam DommaschkKam.DkPoly DommaschkBounceField Certificates.ValidatedQuadrature
open DommaschkRegionEnclosure

/-! ## Thresholds and subdivision -/

/-- Lower bound of the toroidal component. -/
def b₀ : ℚ := 47 / 50
/-- Upper bound of the toroidal component. -/
def c₁ : ℚ := 13 / 10
/-- Bound of the planar speed of the field-line equation. -/
def M : ℚ := 9 / 25

/-- The lower half of an interval. -/
def lower (I : FIv) : FIv := ⟨I.lo, mid I, I.ok⟩
/-- The upper half of an interval. -/
def upper (I : FIv) : FIv := ⟨mid I, I.hi, I.ok⟩

theorem mem_lower_or_upper {I : FIv} {x : ℝ} (h : I.Mem x) : (lower I).Mem x ∨ (upper I).Mem x := by
  by_cases hx : x ≤ fxVal (mid I)
  · exact Or.inl fun ok => ⟨(h ok).1, hx⟩
  · exact Or.inr fun ok => ⟨(not_le.mp hx).le, (h ok).2⟩

/-- The four quarters of a box in `(u, z)`. -/
def quad (B : Box) : ℕ → Box
  | 0 => ⟨lower B.u, lower B.z, B.c, B.s⟩
  | 1 => ⟨lower B.u, upper B.z, B.c, B.s⟩
  | 2 => ⟨upper B.u, lower B.z, B.c, B.s⟩
  | _ => ⟨upper B.u, upper B.z, B.c, B.s⟩

/-- A subdivision certificate: the check holds on the box, or each of its four quarters has a
certificate. -/
inductive Cert : Box → Prop where
  | leaf {B : Box} : good b₀ c₁ M B = true → Cert B
  | split {B : Box} : Cert (quad B 0) → Cert (quad B 1) → Cert (quad B 2) → Cert (quad B 3) →
      Cert B

/-- The three bounds at a point. -/
def Bounds (u z c s : ℝ) : Prop :=
  (b₀ : ℝ) * (u + dkR0) ^ 7 ≤ evR u z c s dD ∧ evR u z c s dD ≤ (c₁ : ℝ) * (u + dkR0) ^ 7 ∧
    evR u z c s dnR ^ 2 + evR u z c s dnZ ^ 2 ≤ (M : ℝ) ^ 2 * evR u z c s dD ^ 2

/-- Soundness of a subdivision certificate. -/
theorem Cert.sound {u z c s : ℝ} {B : Box} (h : Cert B) : B.Mem u z c s → Bounds u z c s := by
  induction h with
  | leaf h => exact fun hm => good_sound (by norm_num [b₀]) (by norm_num [c₁]) h hm
  | split _ _ _ _ i0 i1 i2 i3 =>
    rintro ⟨mu, mz, mc, ms⟩
    rcases mem_lower_or_upper mu with a | a <;> rcases mem_lower_or_upper mz with b | b
    · exact i0 ⟨a, b, mc, ms⟩
    · exact i1 ⟨a, b, mc, ms⟩
    · exact i2 ⟨a, b, mc, ms⟩
    · exact i3 ⟨a, b, mc, ms⟩

/-! ## The cells -/

/-- The `u`-cell `[(i − 1)/32, i/32]`. -/
def uCell (i : ℕ) : FIv := ⟨-134217728 + i * 134217728, -134217728 + (i + 1) * 134217728, true⟩

/-- The `z`-cell `[5j/128, 5(j + 1)/128]`. -/
def zCell (j : ℕ) : FIv := ⟨j * 167772160, (j + 1) * 167772160, true⟩

/-- The cell `[m/16, (m + 1)/16]` of the smaller coordinate on the circle. -/
def xCell (m : ℕ) : FIv := ⟨m * 268435456, (m + 1) * 268435456, true⟩

/-- Lower fixed-point bound of `√(1 − x²)` on the cell `m`. -/
def yLo (m : ℕ) : ℕ := FIv.isqrt (18446744073709551616 - ((m + 1) * 268435456) ^ 2)

/-- Upper fixed-point bound of `√(1 − x²)` on the cell `m`. -/
def yHi (m : ℕ) : ℕ := FIv.isqrt (18446744073709551616 - (m * 268435456) ^ 2) + 1

/-- The enclosure of the larger coordinate on the circle. -/
def yCell (m : ℕ) : FIv := ⟨yLo m, yHi m, true⟩

/-- The integer square roots of the cell `m` are valid bounds. -/
def arcOK (m : ℕ) : Prop :=
  yLo m ^ 2 + ((m + 1) * 268435456) ^ 2 ≤ 18446744073709551616 ∧
    18446744073709551616 ≤ yHi m ^ 2 + (m * 268435456) ^ 2

/-- The enclosures `(c, s)` of the arc `m` of the family `f`. -/
def arc (f m : ℕ) : FIv × FIv :=
  match f with
  | 0 => (yCell m, xCell m)
  | 1 => (yCell m, (xCell m).neg)
  | 2 => ((yCell m).neg, xCell m)
  | 3 => ((yCell m).neg, (xCell m).neg)
  | 4 => (xCell m, yCell m)
  | 5 => ((xCell m).neg, yCell m)
  | 6 => (xCell m, (yCell m).neg)
  | _ => ((xCell m).neg, (yCell m).neg)

/-- The box of the grid with the given indices. -/
def cell (i j f m : ℕ) : Box := ⟨uCell i, zCell j, (arc f m).1, (arc f m).2⟩

/-! ## The cover -/

/-- A point of `[0, N w]` lies in one of the `N` cells of width `w`. -/
theorem exists_cell {w : ℝ} (hw : 0 < w) : ∀ (N : ℕ) {x : ℝ}, 0 < N → 0 ≤ x → x ≤ N * w →
    ∃ m < N, m * w ≤ x ∧ x ≤ (m + 1) * w
  | 0, _, h, _, _ => absurd h (lt_irrefl 0)
  | 1, x, _, h0, h1 => ⟨0, Nat.one_pos, by simpa using h0, by simpa using h1⟩
  | N + 2, x, _, h0, h1 => by
    by_cases hx : x ≤ (N + 1 : ℕ) * w
    · obtain ⟨m, hm, a, b⟩ := exists_cell hw (N + 1) (Nat.succ_pos N) h0 hx
      exact ⟨m, by omega, a, b⟩
    · refine ⟨N + 1, by omega, (not_le.mp hx).le, ?_⟩
      push_cast at h1 ⊢
      linarith

/-- **Sanity**: the point `1/2` lies in a cell of width `1/3` of `[0, 1]`. -/
theorem exists_cell_fixture :
    ∃ m : ℕ, m < 3 ∧ (m : ℝ) * (1 / 3) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ (m + 1) * (1 / 3) :=
  exists_cell (by norm_num) 3 (by norm_num) (by norm_num) (by norm_num)

theorem uCell_cover {u : ℝ} (lo : -1 / 32 ≤ u) (hi : u ≤ 3 / 32) : ∃ i < 4, (uCell i).Mem u := by
  obtain ⟨i, hi', a, b⟩ := exists_cell (w := 1 / 32) (by norm_num) 4 (x := u + 1 / 32)
    (by norm_num) (by linarith) (by norm_num; linarith)
  refine ⟨i, hi', fun _ => ?_⟩
  simp only [uCell, fxVal, fxScale]
  push_cast
  constructor <;> linarith

theorem zCell_cover {z : ℝ} (lo : 0 ≤ z) (hi : z ≤ 5 / 64) : ∃ j < 2, (zCell j).Mem z := by
  obtain ⟨j, hj, a, b⟩ := exists_cell (w := 5 / 128) (by norm_num) 2 (x := z)
    (by norm_num) lo (by norm_num; linarith)
  refine ⟨j, hj, fun _ => ?_⟩
  simp only [zCell, fxVal, fxScale]
  push_cast
  constructor <;> linarith

/-- The checked square roots of all twelve cells. -/
theorem arc_valid : ∀ m < 12, arcOK m := by kernel_fact

/-- On the quarter circle, a point with smaller coordinate in `[0, 3/4]` lies in an arc box. -/
theorem quarter {x y : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 3 / 4) (hy : 0 ≤ y) (circ : x ^ 2 + y ^ 2 = 1) :
    ∃ m < 12, (xCell m).Mem x ∧ (yCell m).Mem y := by
  obtain ⟨m, hm, a, b⟩ := exists_cell (w := 1 / 16) (by norm_num) 12 (x := x)
    (by norm_num) hx (by norm_num; linarith)
  obtain ⟨lo, hi⟩ := arc_valid m hm
  have lo' : ((yLo m : ℕ) : ℝ) ^ 2 + (((m : ℝ) + 1) * 268435456) ^ 2 ≤ 18446744073709551616 := by
    exact_mod_cast lo
  have hi' : (18446744073709551616 : ℝ) ≤ ((yHi m : ℕ) : ℝ) ^ 2 + ((m : ℝ) * 268435456) ^ 2 := by
    exact_mod_cast hi
  have xa : ((m : ℝ) * 268435456) ^ 2 ≤ (4294967296 * x) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have xb : (4294967296 * x) ^ 2 ≤ (((m : ℝ) + 1) * 268435456) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have ylo : ((yLo m : ℕ) : ℝ) ^ 2 ≤ (4294967296 * y) ^ 2 := by nlinarith
  have yhi : (4294967296 * y) ^ 2 ≤ ((yHi m : ℕ) : ℝ) ^ 2 := by nlinarith
  have ylo' := (sq_le_sq₀ (by positivity) (by positivity)).mp ylo
  have yhi' := (sq_le_sq₀ (by positivity) (by positivity)).mp yhi
  refine ⟨m, hm, fun _ => ?_, fun _ => ?_⟩
  · simp only [xCell, fxVal, fxScale]
    push_cast
    constructor <;> linarith
  · simp only [yCell, fxVal, fxScale]
    push_cast
    constructor <;> linarith

/-- A point enclosed after negation is enclosed by the negated interval. -/
theorem mem_neg' {I : FIv} {x : ℝ} (h : I.Mem (-x)) : I.neg.Mem x := by
  simpa using FIv.mem_neg h

/-- Every point of the unit circle lies in one of the arc boxes. -/
theorem arc_cover {c s : ℝ} (circ : c ^ 2 + s ^ 2 = 1) :
    ∃ f < 8, ∃ m < 12, (arc f m).1.Mem c ∧ (arc f m).2.Mem s := by
  by_cases small : |s| ≤ 3 / 4
  · obtain ⟨m, hm, mx, my⟩ := quarter (x := |s|) (y := |c|) (abs_nonneg s) small (abs_nonneg c)
      (by simpa only [sq_abs, add_comm] using circ)
    rcases le_total 0 c with hc | hc <;> rcases le_total 0 s with hs | hs
    · rw [abs_of_nonneg hc] at my; rw [abs_of_nonneg hs] at mx
      exact ⟨0, by norm_num, m, hm, my, mx⟩
    · rw [abs_of_nonneg hc] at my; rw [abs_of_nonpos hs] at mx
      exact ⟨1, by norm_num, m, hm, my, mem_neg' mx⟩
    · rw [abs_of_nonpos hc] at my; rw [abs_of_nonneg hs] at mx
      exact ⟨2, by norm_num, m, hm, mem_neg' my, mx⟩
    · rw [abs_of_nonpos hc] at my; rw [abs_of_nonpos hs] at mx
      exact ⟨3, by norm_num, m, hm, mem_neg' my, mem_neg' mx⟩
  · have big : (3 / 4 : ℝ) ^ 2 < s ^ 2 := by
      rw [← sq_abs s]
      exact pow_lt_pow_left₀ (not_le.mp small) (by norm_num) (by norm_num)
    have small' : |c| ≤ 3 / 4 := abs_le_of_sq_le_sq (by nlinarith) (by norm_num)
    obtain ⟨m, hm, mx, my⟩ := quarter (x := |c|) (y := |s|) (abs_nonneg c) small' (abs_nonneg s)
      (by simpa only [sq_abs] using circ)
    rcases le_total 0 c with hc | hc <;> rcases le_total 0 s with hs | hs
    · rw [abs_of_nonneg hc] at mx; rw [abs_of_nonneg hs] at my
      exact ⟨4, by norm_num, m, hm, mx, my⟩
    · rw [abs_of_nonneg hc] at mx; rw [abs_of_nonpos hs] at my
      exact ⟨6, by norm_num, m, hm, mx, mem_neg' my⟩
    · rw [abs_of_nonpos hc] at mx; rw [abs_of_nonneg hs] at my
      exact ⟨5, by norm_num, m, hm, mem_neg' mx, my⟩
    · rw [abs_of_nonpos hc] at mx; rw [abs_of_nonpos hs] at my
      exact ⟨7, by norm_num, m, hm, mem_neg' mx, mem_neg' my⟩

/-- **The cells cover** the half `z ≥ 0` of the envelope and the whole circle. -/
theorem cover {u z c s : ℝ} (lo : -1 / 32 ≤ u) (hi : u ≤ 3 / 32) (hz : 0 ≤ z) (hz' : z ≤ 5 / 64)
    (circ : c ^ 2 + s ^ 2 = 1) :
    ∃ i < 4, ∃ j < 2, ∃ f < 8, ∃ m < 12, (cell i j f m).Mem u z c s := by
  obtain ⟨i, hi, mu⟩ := uCell_cover lo hi
  obtain ⟨j, hj, mz⟩ := zCell_cover hz hz'
  obtain ⟨f, hf, m, hm, mc, ms⟩ := arc_cover circ
  exact ⟨i, hi, j, hj, f, hf, m, hm, mu, mz, mc, ms⟩

/-! ## The reflection `(z, s) ↦ (−z, −s)` -/

/-- All terms have `z`-degree plus `s`-degree of the given parity. -/
def parity (e : ℕ) (p : SP) : Bool := p.all fun t => (t.b + t.d) % 2 == e

theorem reflect_even : ∀ (p : SP), parity 0 p = true → ∀ u z c s : ℝ,
    evR u (-z) c (-s) p = evR u z c s p
  | [], _, _, _, _, _ => rfl
  | t :: p, h, u, z, c, s => by
    simp only [parity, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    rw [evR_cons, evR_cons, reflect_even p h.2]
    have e : (-z) ^ t.b * (-s) ^ t.d = z ^ t.b * s ^ t.d := by
      rw [neg_pow z, neg_pow s]
      have : (-1 : ℝ) ^ t.b * (-1) ^ t.d = 1 := by
        rw [← pow_add]
        exact Even.neg_one_pow (Nat.even_iff.mpr h.1)
      linear_combination z ^ t.b * s ^ t.d * this
    linear_combination (t.q : ℝ) * u ^ t.a * c ^ t.c * e

theorem reflect_odd : ∀ (p : SP), parity 1 p = true → ∀ u z c s : ℝ,
    evR u (-z) c (-s) p = -evR u z c s p
  | [], _, _, _, _, _ => by simp [evR]
  | t :: p, h, u, z, c, s => by
    simp only [parity, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    rw [evR_cons, evR_cons, reflect_odd p h.2]
    have e : (-z) ^ t.b * (-s) ^ t.d = -(z ^ t.b * s ^ t.d) := by
      rw [neg_pow z, neg_pow s]
      have : (-1 : ℝ) ^ t.b * (-1) ^ t.d = -1 := by
        rw [← pow_add]
        exact Odd.neg_one_pow (Nat.odd_iff.mpr h.1)
      linear_combination z ^ t.b * s ^ t.d * this
    linear_combination (t.q : ℝ) * u ^ t.a * c ^ t.c * e

theorem parity_D : parity 0 dD = true := by kernel_fact
theorem parity_R : parity 1 dnR = true := by kernel_fact
theorem parity_Z : parity 0 dnZ = true := by kernel_fact

/-- **Sanity**: the radial numerator is not even, so the parity test is not vacuous. -/
theorem parity_reject : parity 0 dnR = false := by kernel_fact

/-- The bounds are invariant under the reflection. -/
theorem bounds_reflect {u z c s : ℝ} (h : Bounds u (-z) c (-s)) : Bounds u z c s := by
  unfold Bounds at h ⊢
  rw [reflect_even dD parity_D, reflect_odd dnR parity_R, reflect_even dnZ parity_Z] at h
  simpa using h

/-- **From the grid to the envelope**: if every cell has a subdivision certificate, the three
bounds hold on the whole envelope, for every point of the unit circle. -/
theorem bounds_of_rows (rows : ∀ i < 4, ∀ j < 2, ∀ f < 8, ∀ m < 12, Cert (cell i j f m))
    {u z c s : ℝ} (lo : -1 / 32 ≤ u) (hi : u ≤ 3 / 32) (hz : |z| ≤ 5 / 64)
    (circ : c ^ 2 + s ^ 2 = 1) : Bounds u z c s := by
  obtain ⟨zl, zh⟩ := abs_le.mp hz
  rcases le_total 0 z with pos | neg
  · obtain ⟨i, hi, j, hj, f, hf, m, hm, mem⟩ := cover lo hi pos zh circ
    exact (rows i hi j hj f hf m hm).sound mem
  · apply bounds_reflect
    obtain ⟨i, hi, j, hj, f, hf, m, hm, mem⟩ := cover (z := -z) (s := -s) lo hi (by linarith)
      (by linarith) (by simpa using circ)
    exact (rows i hi j hj f hf m hm).sound mem

end PlasmaLean.Design.DommaschkRegionGrid
