/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.ValidatedQuadrature
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Cell certificates for the precession of trapped alphas in exact QA

Companion to `Design/NearAxisQATrappedResonance` (target T4, step 2 of
`notes/theory/near-qa-trapped-particles.md`). Model only: the exactly quasi-axisymmetric member
`exactQA` of the reactor near-axis family, vacuum Boozer guiding-centre equations.

**Reduction.** Along an exact-QA orbit that starts at a turning point with flux `ψ₀`, momentum
conservation gives `ψ = ψ₀ ∓ x` with `x = k|ρ|`, `k = G/ι = 29050/211`, and energy conservation
reads `λ B_t x² B² + B = B_t`, where `B_t = E/μ` is the field at the tips and
`λ = q²/(2 m E k²)`. Solving the quadratic gives `B = 2B_t/(1 + √(1 + 4λB_t²x²))`, and solving
`B(ψ, θ) = B` (a quadratic in `c = cos θ`) gives `c` explicitly. Hence `c`, `B`, `∂_ψB`,
`|∂_θB|` are **explicit algebraic functions of `x` and of the two constants of motion
`ψ₀, B_t`** (real formulas `cR`, `BsR`, `numR = −∂_ψB`, `denR = |∂_θB|`).

**Cells.** For a parameter box `(ψ₀, B_t) ∈ P × T` and an `x`-cell `X = [i/40, (i+1)/40]`,
fixed-point interval arithmetic (`ValidatedQuadrature.FIv`, kernel-evaluated) encloses:

* `cI`: the cosine of the poloidal angle of every orbit point with `x ∈ X`;
* flank (`|θ| ≥ δ = 3/5`, i.e. `c ≤ cos δ`): the ratio `|∂_ψB| / |∂_θB|` (`flankCell`). Along the
  orbit `Ω dt = (∂_ψB/∂_θB) dψ` exactly, so this bounds the precession per unit change of `x`;
  a cell whose `c`-enclosure lies above `cos δ` is *dead* (no flank point there);
* bottom (`|θ| ≤ δ`): the ratio `Ω/|θ̇| = 1/(1 + R)` (inner leg) or `1/(R − 1)` (outer leg),
  `R = 2λB_t x B³/((2B_t − B)(−∂_ψB))` (`bottomCell`).

`boxOk P T` runs both legs over the 100 cells of `[0, 5/2]` and checks the final inequalities
`2·(1/40)·Σ M_f + (6/5)(M_b^in + M_b^out) ≤ ι₀ · 13/5` and `ι₀ · 7/10 ≤ (6/5)(m_b^in + m_b^out)`.

**Soundness.** `box_sound`: if `boxOk P T = true` then every `(ψ₀, B_t)` in the box carries real
leg bounds (`LegBounds`) with these sums. The physics link (orbit point ↦ reduced variables) is
`OrbitRel`, with `BsR_eq` and `cR_eq` proving that the explicit formulas are the orbit's `B` and
`cos θ`. The window coverage (`9 × 16` boxes `PB j × TB l` covering `ψ₀ ∈ [4.75, 5.875]`,
`B_t ∈ [5.4, 5.5]`) is `precession_cert_of_boxes`; the kernel checks of the 144 boxes are in
`NearAxisQATrappedCellsRows1`–`3`.

Certificate data: none besides the box grid; all bounds are recomputed by the kernel. An
untrusted Python mirror of the checker was used only to choose `δ`, the grid and the targets.
-/
public section
noncomputable section
namespace PlasmaLean.Design.NearAxisQATrappedCells
open PlasmaLean.Certificates.ValidatedQuadrature Real Set

/-! ## Extra enclosure operations -/

namespace FIvX

/-- Shorthand for the outward-rounded rational constant `p/q`. -/
@[expose] def C (p q : ℤ) : FIv := FIv.ofFrac p q

/-- Soundness of `C` with the real value given in any form equal to `p/q`. -/
theorem mem_C {p q : ℤ} {r : ℝ} (h : r = (p : ℝ) / (q : ℝ)) : (C p q).Mem r := by
  rw [h]; exact FIv.mem_ofFrac p q

/-- Interval quotient `I · J⁻¹`. -/
@[expose] def dv (I J : FIv) : FIv := I.mul J.inv

/-- Soundness of `dv`. -/
theorem mem_dv {I J : FIv} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) : (dv I J).Mem (x * y⁻¹) :=
  FIv.mem_mul hx (FIv.mem_inv hy)

/-- A valid quotient has a strictly positive divisor. -/
theorem dv_pos {I J : FIv} {y : ℝ} (hok : (dv I J).ok = true) (hy : J.Mem y) : 0 < y := by
  unfold dv FIv.mul FIv.inv at hok
  split_ifs at hok with h0
  · simp only [Bool.and_eq_true] at hok
    obtain ⟨h1, _⟩ := hy hok.2
    have h0' : (0 : ℝ) < J.lo := by exact_mod_cast h0
    have : 0 < fxVal J.lo := div_pos h0' fxScale_pos
    linarith
  · simp at hok

/-- Clamp from above by a known upper bound `b` (scaled). -/
@[expose] def meetHi (I : FIv) (b : ℤ) : FIv := ⟨I.lo, min I.hi b, I.ok⟩

/-- Clamp from below by a known lower bound `b` (scaled). -/
@[expose] def meetLo (I : FIv) (b : ℤ) : FIv := ⟨max I.lo b, I.hi, I.ok⟩

/-- Soundness of `meetHi`. -/
theorem mem_meetHi {I : FIv} {x : ℝ} {b : ℤ} (hx : I.Mem x) (hb : x ≤ fxVal b) :
    (meetHi I b).Mem x := by
  intro hok
  obtain ⟨h1, h2⟩ := hx hok
  refine ⟨h1, ?_⟩
  unfold meetHi fxVal at *
  rcases le_total I.hi b with h | h
  · rw [min_eq_left h]; exact h2
  · rw [min_eq_right h]; exact hb

/-- Soundness of `meetLo`. -/
theorem mem_meetLo {I : FIv} {x : ℝ} {b : ℤ} (hx : I.Mem x) (hb : fxVal b ≤ x) :
    (meetLo I b).Mem x := by
  intro hok
  obtain ⟨h1, h2⟩ := hx hok
  refine ⟨?_, h2⟩
  unfold meetLo fxVal at *
  rcases le_total I.lo b with h | h
  · rw [max_eq_right h]; exact hb
  · rw [max_eq_left h]; exact h1

/-- Interval absolute value. -/
@[expose] def absI (I : FIv) : FIv :=
  if 0 ≤ I.lo then I else if I.hi ≤ 0 then I.neg else ⟨0, max (-I.lo) I.hi, I.ok⟩

/-- Soundness of `absI`. -/
theorem mem_abs {I : FIv} {x : ℝ} (hx : I.Mem x) : (absI I).Mem |x| := by
  unfold absI
  have hS := fxScale_pos
  split_ifs with h1 h2
  · intro hok
    obtain ⟨a, b⟩ := hx hok
    have : 0 ≤ fxVal I.lo := div_nonneg (by exact_mod_cast h1) hS.le
    rw [abs_of_nonneg (by linarith)]; exact ⟨a, b⟩
  · intro hok
    obtain ⟨a, b⟩ := hx hok
    have : fxVal I.hi ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h2) hS.le
    rw [abs_of_nonpos (by linarith)]
    exact FIv.mem_neg hx hok
  · intro hok
    obtain ⟨a, b⟩ := hx hok
    have hm1 : ((-I.lo : ℤ) : ℝ) ≤ ((max (-I.lo) I.hi : ℤ) : ℝ) := by
      exact_mod_cast le_max_left (-I.lo) I.hi
    have hm2 : ((I.hi : ℤ) : ℝ) ≤ ((max (-I.lo) I.hi : ℤ) : ℝ) := by
      exact_mod_cast le_max_right (-I.lo) I.hi
    simp only [fxVal] at a b ⊢
    push_cast at hm1 hm2 ⊢
    refine ⟨by rw [zero_div]; exact abs_nonneg x, ?_⟩
    rw [div_le_iff₀ hS] at a
    rw [le_div_iff₀ hS] at b ⊢
    rcases le_total 0 x with hx0 | hx0
    · rw [abs_of_nonneg hx0]; linarith
    · rw [abs_of_nonpos hx0]; linarith

/-- The closed hull `[⌊2³² p₁/q₁⌋, ⌈2³² p₂/q₂⌉]` of two rationals. -/
@[expose] def hull (p₁ q₁ p₂ q₂ : ℤ) : FIv := ⟨(FIv.ofFrac p₁ q₁).lo, (FIv.ofFrac p₂ q₂).hi, true⟩

/-- Soundness of `hull` (for positive denominators). -/
theorem mem_hull {p₁ q₁ p₂ q₂ : ℤ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) {x : ℝ}
    (h1 : (p₁ : ℝ) / q₁ ≤ x) (h2 : x ≤ (p₂ : ℝ) / q₂) : (hull p₁ q₁ p₂ q₂).Mem x := by
  intro _
  have hok1 : (FIv.ofFrac p₁ q₁).ok = true := by simp [FIv.ofFrac, hq₁]
  have hok2 : (FIv.ofFrac p₂ q₂).ok = true := by simp [FIv.ofFrac, hq₂]
  exact ⟨((FIv.mem_ofFrac p₁ q₁) hok1).1.trans h1, h2.trans ((FIv.mem_ofFrac p₂ q₂) hok2).2⟩

end FIvX

open FIvX

/-- Repeatedly apply the enclosure soundness lemmas. -/
macro "fiv_mem" : tactic => `(tactic| repeat (first
  | with_reducible apply mem_dv | with_reducible apply FIv.mem_add
  | with_reducible apply FIv.mem_sub | with_reducible apply FIv.mem_mul
  | with_reducible apply FIv.mem_sq | with_reducible apply FIv.mem_sqrt
  | with_reducible apply FIv.mem_inv | with_reducible apply FIv.mem_neg
  | (with_reducible apply mem_C; norm_num) | with_reducible assumption))

/-! ## Reduced real formulas -/

/-- `λ = q²/(2 m E k²)` as an exact rational (`k = G/ι = 29050/211`). -/
@[expose] def lam : ℝ := 6408800 * 44521 / (465129 * 843902500)

/-- Flux on the leg: `ψ₀ − x` on the inner leg (`ρ ≤ 0`), `ψ₀ + x` on the outer leg. -/
@[expose] def psiR (inner : Bool) (ψ₀ x : ℝ) : ℝ := if inner then ψ₀ - x else ψ₀ + x

/-- `w = r² = 2ψ/B₀ = (20/57) ψ`. -/
@[expose] def wR (inner : Bool) (ψ₀ x : ℝ) : ℝ := 20 / 57 * psiR inner ψ₀ x

/-- The exact-QA field strength at flux `ψ` and `cos θ = c`:
`B = 5.7 − 0.399 r c + w (−0.0302 + 0.033 c²)`, `r = √w`. -/
@[expose] def Bred (ψ c : ℝ) : ℝ :=
  57 / 10 - 399 / 1000 * √(20 / 57 * ψ) * c + 20 / 57 * ψ * (-302 / 10000 + 33 / 1000 * c ^ 2)

/-- The orbit field `B = 2B_t/(1 + √(1 + 4λB_t²x²))` (positive root of the energy relation). -/
@[expose] def BsR (x Bt : ℝ) : ℝ := 2 * Bt * (1 + √(1 + 4 * lam * (Bt ^ 2 * x ^ 2)))⁻¹

/-- `cc = 5.7 − 0.0302 w − B`. -/
@[expose] def ccR (inner : Bool) (ψ₀ x Bt : ℝ) : ℝ :=
  57 / 10 - 302 / 10000 * wR inner ψ₀ x - BsR x Bt

/-- The explicit cosine `c = 2 cc / (r (0.399 + √(0.159201 − 0.132 cc)))`. -/
@[expose] def cR (inner : Bool) (ψ₀ x Bt : ℝ) : ℝ :=
  2 * ccR inner ψ₀ x Bt *
    (√(wR inner ψ₀ x) * (399 / 1000 + √(159201 / 1000000 - 132 / 1000 * ccR inner ψ₀ x Bt)))⁻¹

/-- `−∂_ψB = 0.07 c/r + (20/57)(0.0302 − 0.033 c²)`. -/
@[expose] def numR (inner : Bool) (ψ₀ x c : ℝ) : ℝ :=
  7 / 100 * c * (√(wR inner ψ₀ x))⁻¹ + 20 / 57 * (302 / 10000 - 33 / 1000 * c ^ 2)

/-- `|∂_θB| = s (0.399 r − 0.066 w c)` with `s = |sin θ|`. -/
@[expose] def denR (inner : Bool) (ψ₀ x c s : ℝ) : ℝ :=
  s * (399 / 1000 * √(wR inner ψ₀ x) - 66 / 1000 * wR inner ψ₀ x * c)

/-- `R = 2λB_t x B³/((2B_t − B)(−∂_ψB))`: streaming over drift in `θ̇`. -/
@[expose] def RR (inner : Bool) (ψ₀ x Bt c : ℝ) : ℝ :=
  2 * lam * (Bt * x) * (BsR x Bt * BsR x Bt ^ 2) *
    ((2 * Bt - BsR x Bt) * numR inner ψ₀ x c)⁻¹

/-- `Ω/|θ̇|` at the bottom: `1/(1 + R)` (inner leg) or `1/(R − 1)` (outer leg). -/
@[expose] def ratR (inner : Bool) (ψ₀ x Bt c : ℝ) : ℝ :=
  if inner then (1 + RR inner ψ₀ x Bt c)⁻¹ else (RR inner ψ₀ x Bt c - 1)⁻¹

/-- **Reduced orbit relation**: `(x, c)` is a point of the exact-QA orbit with constants of motion
`ψ₀, B_t` on the given leg (energy in reduced form, flux in range, `0 ≤ c ≤ 1`). -/
structure OrbitRel (inner : Bool) (x ψ₀ Bt c : ℝ) : Prop where
  /-- `x ≥ 0`. -/
  x_nonneg : 0 ≤ x
  /-- Flux positive. -/
  psi_pos : 0 < psiR inner ψ₀ x
  /-- Flux bounded (`r ≤ 1.88 m`). -/
  psi_le : psiR inner ψ₀ x ≤ 10
  /-- Tip field positive. -/
  Bt_pos : 0 < Bt
  /-- Field positive. -/
  B_pos : 0 < Bred (psiR inner ψ₀ x) c
  /-- Reduced energy relation `λ B_t x² B² + B = B_t`. -/
  energy : lam * Bt * x ^ 2 * Bred (psiR inner ψ₀ x) c ^ 2 + Bred (psiR inner ψ₀ x) c = Bt
  /-- `c ≥ 0` (`|θ| ≤ π/2`). -/
  c_nonneg : 0 ≤ c
  /-- `c ≤ 1`. -/
  c_le : c ≤ 1

/-- **The explicit orbit field.** Under the reduced energy relation, `B = BsR x B_t`. -/
theorem BsR_eq {inner : Bool} {x ψ₀ Bt c : ℝ} (h : OrbitRel inner x ψ₀ Bt c) :
    BsR x Bt = Bred (psiR inner ψ₀ x) c := by
  have hB := h.B_pos
  have hE := h.energy
  set B := Bred (psiR inner ψ₀ x) c
  have hl : 0 ≤ lam := by norm_num [lam]
  have ha0 : 0 ≤ lam * Bt * x ^ 2 := by have := h.Bt_pos.le; positivity
  have hs : √(1 + 4 * lam * (Bt ^ 2 * x ^ 2)) = 2 * (lam * Bt * x ^ 2) * B + 1 := by
    rw [sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    have : 1 + 4 * lam * (Bt ^ 2 * x ^ 2) =
        1 + 4 * (lam * Bt * x ^ 2) * (lam * Bt * x ^ 2 * B ^ 2 + B) := by rw [hE]; ring
    rw [this]; ring
  unfold BsR
  rw [hs]
  have hne : (1 + (2 * (lam * Bt * x ^ 2) * B + 1)) ≠ 0 := by positivity
  rw [mul_inv_eq_iff_eq_mul₀ hne]
  linear_combination (-2) * hE

/-- **The explicit cosine.** Under the reduced orbit relation, `c = cR`. -/
theorem cR_eq {inner : Bool} {x ψ₀ Bt c : ℝ} (h : OrbitRel inner x ψ₀ Bt c) :
    cR inner ψ₀ x Bt = c := by
  have hψ := h.psi_pos
  set ψ := psiR inner ψ₀ x with hψdef
  have hw : wR inner ψ₀ x = 20 / 57 * ψ := rfl
  set r := √(20 / 57 * ψ) with hr
  have hr0 : 0 < r := sqrt_pos.mpr (by positivity)
  have hr2 : r ^ 2 = 20 / 57 * ψ := sq_sqrt (by positivity)
  have hr1 : r ≤ 2 := by
    rw [hr, sqrt_le_left (by norm_num)]; have := h.psi_le; nlinarith
  have hc0 := h.c_nonneg
  have hc1 := h.c_le
  have hcc : ccR inner ψ₀ x Bt = 399 / 1000 * r * c - 33 / 1000 * r ^ 2 * c ^ 2 := by
    unfold ccR; rw [BsR_eq h, hw, hr2.symm]; unfold Bred; rw [← hr, hr2]; ring
  have hD : √(159201 / 1000000 - 132 / 1000 * ccR inner ψ₀ x Bt) =
      399 / 1000 - 66 / 1000 * r * c := by
    rw [hcc, sqrt_eq_iff_mul_self_eq (by nlinarith) (by nlinarith)]
    ring
  unfold cR
  rw [hD, hcc, hw, ← hr]
  have hpos : 0 < 399 / 1000 - 33 / 1000 * r * c := by nlinarith
  have hne : r * (399 / 1000 + (399 / 1000 - 66 / 1000 * r * c)) ≠ 0 :=
    mul_ne_zero hr0.ne' (by nlinarith)
  rw [mul_inv_eq_iff_eq_mul₀ hne]
  ring

/-! ## Interval versions -/

/-- Enclosure of `λ`. -/
@[expose] def lamI : FIv := C (6408800 * 44521) (465129 * 843902500)

/-- `λ ∈ lamI`. -/
theorem mem_lamI : lamI.Mem lam := mem_C (by norm_num [lam])

/-- Interval flux on the leg. -/
@[expose] def psiI (inner : Bool) (X P : FIv) : FIv := if inner then P.sub X else P.add X

/-- Soundness of `psiI`. -/
theorem mem_psiI {inner : Bool} {X P : FIv} {x p : ℝ} (hX : X.Mem x) (hP : P.Mem p) :
    (psiI inner X P).Mem (psiR inner p x) := by
  cases inner
  · exact FIv.mem_add hP hX
  · exact FIv.mem_sub hP hX

/-- Interval `w`. -/
@[expose] def wI (inner : Bool) (X P : FIv) : FIv := (C 20 57).mul (psiI inner X P)

/-- Soundness of `wI`. -/
theorem mem_wI {inner : Bool} {X P : FIv} {x p : ℝ} (hX : X.Mem x) (hP : P.Mem p) :
    (wI inner X P).Mem (wR inner p x) :=
  FIv.mem_mul (mem_C (by norm_num)) (mem_psiI hX hP)

/-- Interval orbit field. -/
@[expose] def BsI (X T : FIv) : FIv :=
  dv ((C 2 1).mul T) ((C 1 1).add ((C 1 1).add (((C 4 1).mul lamI).mul (T.sq.mul X.sq))).sqrt)

/-- Soundness of `BsI`. -/
theorem mem_BsI {X T : FIv} {x b : ℝ} (hX : X.Mem x) (hT : T.Mem b) :
    (BsI X T).Mem (BsR x b) := by
  have hl := mem_lamI
  unfold BsI BsR
  fiv_mem

/-- Interval `cc`. -/
@[expose] def ccI (inner : Bool) (X P T : FIv) : FIv :=
  ((C 57 10).sub ((C 302 10000).mul (wI inner X P))).sub (BsI X T)

/-- Soundness of `ccI`. -/
theorem mem_ccI {inner : Bool} {X P T : FIv} {x p b : ℝ} (hX : X.Mem x) (hP : P.Mem p)
    (hT : T.Mem b) : (ccI inner X P T).Mem (ccR inner p x b) := by
  have h1 := mem_wI (inner := inner) hX hP
  have h2 := mem_BsI hX hT
  unfold ccI ccR
  fiv_mem

/-- Interval cosine. -/
@[expose] def cI (inner : Bool) (X P T : FIv) : FIv :=
  dv ((C 2 1).mul (ccI inner X P T))
    ((wI inner X P).sqrt.mul ((C 399 1000).add
      ((C 159201 1000000).sub ((C 132 1000).mul (ccI inner X P T))).sqrt))

/-- Soundness of `cI`. -/
theorem mem_cI {inner : Bool} {X P T : FIv} {x p b : ℝ} (hX : X.Mem x) (hP : P.Mem p)
    (hT : T.Mem b) : (cI inner X P T).Mem (cR inner p x b) := by
  have h1 := mem_wI (inner := inner) hX hP
  have h2 := mem_ccI (inner := inner) hX hP hT
  unfold cI cR
  fiv_mem

/-- Interval `−∂_ψB`. -/
@[expose] def numI (inner : Bool) (X P c : FIv) : FIv :=
  (dv ((C 7 100).mul c) (wI inner X P).sqrt).add
    ((C 20 57).mul ((C 302 10000).sub ((C 33 1000).mul c.sq)))

/-- Soundness of `numI`. -/
theorem mem_numI {inner : Bool} {X P c : FIv} {x p cr : ℝ} (hX : X.Mem x) (hP : P.Mem p)
    (hc : c.Mem cr) : (numI inner X P c).Mem (numR inner p x cr) := by
  have h1 := mem_wI (inner := inner) hX hP
  unfold numI numR
  fiv_mem

/-- Interval `|∂_θB|`. -/
@[expose] def denI (inner : Bool) (X P c s : FIv) : FIv :=
  s.mul (((C 399 1000).mul (wI inner X P).sqrt).sub (((C 66 1000).mul (wI inner X P)).mul c))

/-- Soundness of `denI`. -/
theorem mem_denI {inner : Bool} {X P c s : FIv} {x p cr sr : ℝ} (hX : X.Mem x) (hP : P.Mem p)
    (hc : c.Mem cr) (hs : s.Mem sr) : (denI inner X P c s).Mem (denR inner p x cr sr) := by
  have h1 := mem_wI (inner := inner) hX hP
  unfold denI denR
  fiv_mem

/-- Interval `R`. -/
@[expose] def RI (inner : Bool) (X P T c : FIv) : FIv :=
  dv ((((C 2 1).mul lamI).mul (T.mul X)).mul ((BsI X T).mul (BsI X T).sq))
    ((((C 2 1).mul T).sub (BsI X T)).mul (numI inner X P c))

/-- Soundness of `RI`. -/
theorem mem_RI {inner : Bool} {X P T c : FIv} {x p b cr : ℝ} (hX : X.Mem x) (hP : P.Mem p)
    (hT : T.Mem b) (hc : c.Mem cr) : (RI inner X P T c).Mem (RR inner p x b cr) := by
  have h1 := mem_BsI hX hT
  have h2 := mem_numI (inner := inner) hX hP hc
  have hl := mem_lamI
  unfold RI RR
  fiv_mem

/-- Interval bottom ratio. -/
@[expose] def ratI (inner : Bool) (X P T c : FIv) : FIv :=
  if inner then ((C 1 1).add (RI inner X P T c)).inv else ((RI inner X P T c).sub (C 1 1)).inv

/-- Soundness of `ratI`. -/
theorem mem_ratI {inner : Bool} {X P T c : FIv} {x p b cr : ℝ} (hX : X.Mem x) (hP : P.Mem p)
    (hT : T.Mem b) (hc : c.Mem cr) : (ratI inner X P T c).Mem (ratR inner p x b cr) := by
  have h1 := mem_RI (inner := inner) hX hP hT hc
  cases inner
  · simp only [ratI, ratR, Bool.false_eq_true, ite_false]; fiv_mem
  · simp only [ratI, ratR, ite_true]; fiv_mem

/-! ## The flank / bottom split at `δ = 3/5` -/

/-- `0.8248 ≤ cos(3/5) ≤ 0.8254` (double angle and the cubic Taylor bounds for `sin (3/10)`). -/
theorem cos_delta_bounds : 8248 / 10000 ≤ cos (3 / 5) ∧ cos (3 / 5) ≤ 8254 / 10000 := by
  have e : cos (3 / 5) = 1 - 2 * sin (3 / 10) ^ 2 := by
    rw [show (3 / 5 : ℝ) = 2 * (3 / 10) by norm_num, cos_two_mul, cos_sq']; ring
  have h1 := sin_ge_sub_cube (x := 3 / 10) (by norm_num)
  have h2 := sin_bound (x := 3 / 10) (by rw [abs_of_pos (by norm_num)]; norm_num)
  rw [abs_le, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 10)] at h2
  rw [e]
  constructor <;> nlinarith [h2.1, h2.2]

/-- `sin(3/5) ≥ 0.564`. -/
theorem sin_delta_ge : 564 / 1000 ≤ sin (3 / 5) := by
  have := sin_ge_sub_cube (x := 3 / 5) (by norm_num)
  norm_num at this ⊢; linarith

/-- Scaled lower bound for `cos δ`. -/
@[expose] def cdLo : ℤ := (C 8248 10000).lo

/-- Scaled upper bound for `cos δ`. -/
@[expose] def cdHi : ℤ := (C 8254 10000).hi

/-- Scaled lower bound for `sin δ`. -/
@[expose] def sdLo : ℤ := (C 564 1000).lo

/-- `fxVal cdLo ≤ cos δ`. -/
theorem cdLo_le : fxVal cdLo ≤ cos (3 / 5) :=
  ((mem_C (p := 8248) (q := 10000) (r := 8248 / 10000) (by norm_num)) rfl).1.trans
    cos_delta_bounds.1

/-- `cos δ ≤ fxVal cdHi`. -/
theorem le_cdHi : cos (3 / 5) ≤ fxVal cdHi :=
  cos_delta_bounds.2.trans ((mem_C (p := 8254) (q := 10000) (r := 8254 / 10000)
    (by norm_num)) rfl).2

/-- `fxVal sdLo ≤ sin δ`. -/
theorem sdLo_le : fxVal sdLo ≤ sin (3 / 5) :=
  ((mem_C (p := 564) (q := 1000) (r := 564 / 1000) (by norm_num)) rfl).1.trans sin_delta_ge

/-! ## Cell checks -/

/-- `(absI I).ok = I.ok`. -/
theorem absI_ok (I : FIv) : (absI I).ok = I.ok := by
  unfold absI; split_ifs <;> rfl

/-- Validity of a quotient gives validity of the numerator. -/
theorem dv_ok_left {I J : FIv} (h : (dv I J).ok = true) : I.ok = true := by
  unfold dv FIv.mul at h; simp only [Bool.and_eq_true] at h; exact h.1

/-- A valid reciprocal has a strictly positive argument. -/
theorem inv_pos_of_ok {I : FIv} {y : ℝ} (hok : I.inv.ok = true) (hy : I.Mem y) : 0 < y := by
  unfold FIv.inv at hok
  split_ifs at hok with h0
  · obtain ⟨h1, _⟩ := hy hok
    have h0' : (0 : ℝ) < I.lo := by exact_mod_cast h0
    have : 0 < fxVal I.lo := div_pos h0' fxScale_pos
    linarith

/-- **Flank cell** on the `x`-cell `X`: returns validity and the scaled bound on
`|∂_ψB|/|∂_θB|` (`0` for a dead cell, where no orbit point has `|θ| ≥ δ`). -/
@[expose] def flankCell (inner : Bool) (X P T : FIv) : Bool × ℤ :=
  if (cI inner X P T).ok && decide (cdHi < (cI inner X P T).lo) then (true, 0) else
    ((dv (absI (numI inner X P (meetLo (meetHi (cI inner X P T) cdHi) 0)))
        (denI inner X P (meetLo (meetHi (cI inner X P T) cdHi) 0)
          (meetLo ((C 1 1).sub (meetLo (meetHi (cI inner X P T) cdHi) 0).sq).sqrt sdLo))).ok &&
      (numI inner X P (meetLo (meetHi (cI inner X P T) cdHi) 0)).ok &&
      decide (0 ≤ (numI inner X P (meetLo (meetHi (cI inner X P T) cdHi) 0)).lo),
     (dv (absI (numI inner X P (meetLo (meetHi (cI inner X P T) cdHi) 0)))
        (denI inner X P (meetLo (meetHi (cI inner X P T) cdHi) 0)
          (meetLo ((C 1 1).sub (meetLo (meetHi (cI inner X P T) cdHi) 0).sq).sqrt sdLo))).hi)

/-- **Bottom cell** on `X`: validity, and scaled upper / lower bounds on `Ω/|θ̇|` (dead cells,
where no orbit point has `|θ| ≤ δ`, return `(true, 0, 1000 · 2³²)`). -/
@[expose] def bottomCell (inner : Bool) (X P T : FIv) : Bool × ℤ × ℤ :=
  if (cI inner X P T).ok && (decide ((cI inner X P T).hi < cdLo) ||
      decide (fxScale < (cI inner X P T).lo)) then (true, 0, fxScale * 1000) else
    ((ratI inner X P T (meetHi (meetLo (cI inner X P T) cdLo) fxScale)).ok &&
      (numI inner X P (meetHi (meetLo (cI inner X P T) cdLo) fxScale)).ok && X.ok &&
      decide (0 < (numI inner X P (meetHi (meetLo (cI inner X P T) cdLo) fxScale)).lo) &&
      decide (0 < X.lo),
     (ratI inner X P T (meetHi (meetLo (cI inner X P T) cdLo) fxScale)).hi,
     (ratI inner X P T (meetHi (meetLo (cI inner X P T) cdLo) fxScale)).lo)

/-- `√(1 − c²) ≥ sin δ` for `0 ≤ c ≤ cos δ`. -/
theorem sqrt_one_sub_sq_ge {c : ℝ} (h0 : 0 ≤ c) (hc : c ≤ cos (3 / 5)) :
    sin (3 / 5) ≤ √(1 - c ^ 2) := by
  have hs0 : 0 ≤ sin (3 / 5) := by linarith [sin_delta_ge]
  apply le_sqrt_of_sq_le
  have := sin_sq_add_cos_sq (3 / 5 : ℝ)
  nlinarith

/-- **Soundness of a flank cell.** For an orbit point with `x ∈ X`, constants of motion in
`P × T`, and `|θ| ≥ δ` (`c ≤ cos δ`): `−∂_ψB ≥ 0` and `|∂_ψB| ≤ M |∂_θB|`. -/
theorem flankCell_sound {inner : Bool} {X P T : FIv} {x p b c : ℝ}
    (hok : (flankCell inner X P T).1 = true) (hX : X.Mem x) (hP : P.Mem p) (hT : T.Mem b)
    (hrel : OrbitRel inner x p b c) (hc : c ≤ cos (3 / 5)) :
    0 ≤ numR inner p x c ∧
      |numR inner p x c| ≤ fxVal (flankCell inner X P T).2 * denR inner p x c (√(1 - c ^ 2)) := by
  have hcI := mem_cI (inner := inner) hX hP hT
  rw [cR_eq hrel] at hcI
  unfold flankCell at hok ⊢
  split_ifs at hok ⊢ with hdead
  · exfalso
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hdead
    obtain ⟨h1, _⟩ := hcI hdead.1
    have : fxVal cdHi < fxVal (cI inner X P T).lo := by
      unfold fxVal; exact div_lt_div_of_pos_right (by exact_mod_cast hdead.2) fxScale_pos
    linarith [le_cdHi]
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hg, hn⟩, hlo⟩ := hok
    have hc2 : (meetLo (meetHi (cI inner X P T) cdHi) 0).Mem c :=
      mem_meetLo (mem_meetHi hcI (hc.trans le_cdHi)) (by simp [fxVal, hrel.c_nonneg])
    have hs : (meetLo ((C 1 1).sub (meetLo (meetHi (cI inner X P T) cdHi) 0).sq).sqrt sdLo).Mem
        (√(1 - c ^ 2)) :=
      mem_meetLo (FIv.mem_sqrt (FIv.mem_sub (mem_C (by norm_num)) (FIv.mem_sq hc2)))
        (sdLo_le.trans (sqrt_one_sub_sq_ge hrel.c_nonneg hc))
    have hnum := mem_numI (inner := inner) hX hP hc2
    have hden := mem_denI (inner := inner) hX hP hc2 hs
    have hgm := mem_dv (mem_abs hnum) hden
    have hdpos := dv_pos hg hden
    obtain ⟨hn1, _⟩ := hnum hn
    obtain ⟨_, hg2⟩ := hgm hg
    refine ⟨le_trans (div_nonneg (by exact_mod_cast hlo) fxScale_pos.le) hn1, ?_⟩
    rw [← div_le_iff₀ hdpos, div_eq_mul_inv]
    exact hg2

/-- **Soundness of a bottom cell.** For an orbit point with `x ∈ X`, constants in `P × T`, and
`|θ| ≤ δ` (`cos δ ≤ c`): `x > 0` (so `ρ ≠ 0`), `−∂_ψB > 0`, the sign condition on `R`, and
`Ω/|θ̇| = ratR` lies in the returned enclosure. -/
theorem bottomCell_sound {inner : Bool} {X P T : FIv} {x p b c : ℝ}
    (hok : (bottomCell inner X P T).1 = true) (hX : X.Mem x) (hP : P.Mem p) (hT : T.Mem b)
    (hrel : OrbitRel inner x p b c) (hc : cos (3 / 5) ≤ c) :
    0 < x ∧ 0 < numR inner p x c ∧
      (if inner then 0 < 1 + RR inner p x b c else 0 < RR inner p x b c - 1) ∧
      fxVal (bottomCell inner X P T).2.2 ≤ ratR inner p x b c ∧
      ratR inner p x b c ≤ fxVal (bottomCell inner X P T).2.1 := by
  have hcI := mem_cI (inner := inner) hX hP hT
  rw [cR_eq hrel] at hcI
  by_cases hdead : ((cI inner X P T).ok && (decide ((cI inner X P T).hi < cdLo) ||
      decide (fxScale < (cI inner X P T).lo))) = true
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
  · have e : bottomCell inner X P T =
        ((ratI inner X P T (meetHi (meetLo (cI inner X P T) cdLo) fxScale)).ok &&
          (numI inner X P (meetHi (meetLo (cI inner X P T) cdLo) fxScale)).ok && X.ok &&
          decide (0 < (numI inner X P (meetHi (meetLo (cI inner X P T) cdLo) fxScale)).lo) &&
          decide (0 < X.lo),
         (ratI inner X P T (meetHi (meetLo (cI inner X P T) cdLo) fxScale)).hi,
         (ratI inner X P T (meetHi (meetLo (cI inner X P T) cdLo) fxScale)).lo) := by
      unfold bottomCell; simp only [hdead, Bool.false_eq_true, ite_false]
    rw [e] at hok ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨hr, hn⟩, hXok⟩, hnlo⟩, hXlo⟩ := hok
    have hc2 : (meetHi (meetLo (cI inner X P T) cdLo) fxScale).Mem c :=
      mem_meetHi (mem_meetLo hcI (cdLo_le.trans hc))
        (by rw [show fxVal fxScale = 1 by unfold fxVal; exact div_self fxScale_pos.ne']
            exact hrel.c_le)
    have hnum := mem_numI (inner := inner) hX hP hc2
    have hrat := mem_ratI (inner := inner) hX hP hT hc2
    have hR := mem_RI (inner := inner) hX hP hT hc2
    obtain ⟨hx1, _⟩ := hX hXok
    obtain ⟨hn1, _⟩ := hnum hn
    obtain ⟨hr1, hr2⟩ := hrat hr
    refine ⟨lt_of_lt_of_le (div_pos (by exact_mod_cast hXlo) fxScale_pos) hx1,
      lt_of_lt_of_le (div_pos (by exact_mod_cast hnlo) fxScale_pos) hn1, ?_, hr1, hr2⟩
    have h1 : (C 1 1).Mem 1 := mem_C (by norm_num)
    cases inner
    · simp only [ratI, Bool.false_eq_true, ite_false] at hr ⊢
      exact inv_pos_of_ok hr (FIv.mem_sub hR h1)
    · simp only [ratI, ite_true] at hr ⊢
      exact inv_pos_of_ok hr (FIv.mem_add h1 hR)

/-! ## Legs and boxes -/

/-- The `i`-th `x`-cell `[i/40, (i+1)/40]`. -/
@[expose] def cellX (i : ℕ) : FIv := hull i 40 (i + 1) 40

/-- `x ∈ cellX i` for `x ∈ [i/40, (i+1)/40]`. -/
theorem mem_cellX {i : ℕ} {x : ℝ} (hx : x ∈ Icc ((i : ℝ) / 40) (((i : ℝ) + 1) / 40)) :
    (cellX i).Mem x :=
  mem_hull (by norm_num) (by norm_num) (by push_cast; exact hx.1) (by push_cast; exact hx.2)

/-- Run a leg over the first `n` cells: validity, the sum of the (nonnegative parts of the)
flank bounds, the maximum and the minimum of the bottom bounds. -/
@[expose] def legLoop (inner : Bool) (P T : FIv) : ℕ → Bool × ℤ × ℤ × ℤ
  | 0 => (true, 0, 0, fxScale * 1000)
  | n + 1 =>
    ((legLoop inner P T n).1 && (flankCell inner (cellX n) P T).1 &&
        (bottomCell inner (cellX n) P T).1,
      (legLoop inner P T n).2.1 + max 0 (flankCell inner (cellX n) P T).2,
      max (legLoop inner P T n).2.2.1 (bottomCell inner (cellX n) P T).2.1,
      min (legLoop inner P T n).2.2.2 (bottomCell inner (cellX n) P T).2.2)

/-- Properties of `legLoop`: all cells valid, the sum, and the extremal bottom bounds. -/
theorem legLoop_spec (inner : Bool) (P T : FIv) (n : ℕ) (h : (legLoop inner P T n).1 = true) :
    (∀ i < n, (flankCell inner (cellX i) P T).1 = true ∧
      (bottomCell inner (cellX i) P T).1 = true ∧
      (bottomCell inner (cellX i) P T).2.1 ≤ (legLoop inner P T n).2.2.1 ∧
      (legLoop inner P T n).2.2.2 ≤ (bottomCell inner (cellX i) P T).2.2) ∧
    (legLoop inner P T n).2.1 =
      ∑ i ∈ Finset.range n, max 0 (flankCell inner (cellX i) P T).2 := by
  induction n with
  | zero => exact ⟨fun i hi => absurd hi (Nat.not_lt_zero i), rfl⟩
  | succ n ih =>
    simp only [legLoop, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨ih1, ih2⟩ := ih h1
    refine ⟨fun i hi => ?_, by simp only [legLoop]; rw [ih2, Finset.sum_range_succ]⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
    · obtain ⟨a, b, c, d⟩ := ih1 i hi'
      exact ⟨a, b, le_trans c (le_max_left _ _), le_trans (min_le_left _ _) d⟩
    · subst hi'
      exact ⟨h2, h3, le_max_right _ _, min_le_right _ _⟩

/-- **The box check**: both legs valid over the 100 cells of `[0, 5/2]`, and
`2 (1/40) Σ M_f + (6/5)(M_b^in + M_b^out) ≤ ι₀ · 13/5`, `ι₀ · 7/10 ≤ (6/5)(m_b^in + m_b^out)`
(in scaled integers). -/
@[expose] def boxOk (P T : FIv) : Bool :=
  (legLoop true P T 100).1 && (legLoop false P T 100).1 &&
    decide (500 * ((legLoop true P T 100).2.1 + (legLoop false P T 100).2.1) +
      12000 * ((legLoop true P T 100).2.2.1 + (legLoop false P T 100).2.2.1) ≤
        10972 * fxScale) &&
    decide (1477 * fxScale ≤
      6000 * ((legLoop true P T 100).2.2.2 + (legLoop false P T 100).2.2.2))

/-- **Real leg bounds** for the leg `inner` of an orbit with constants `ψ₀, B_t`: flank cell
bounds `M_f i ≥ 0` on `|∂_ψB|/|∂_θB|` (with `−∂_ψB ≥ 0`), and bottom bounds
`m_b ≤ Ω/|θ̇| ≤ M_b` (with `x > 0`, `−∂_ψB > 0` and the sign of `θ̇` fixed). -/
structure LegBounds (inner : Bool) (ψ₀ Bt : ℝ) (Mf : ℕ → ℝ) (Mb mb : ℝ) : Prop where
  /-- Nonnegative flank bounds. -/
  Mf_nonneg : ∀ i, 0 ≤ Mf i
  /-- Flank cells. -/
  flank : ∀ i : ℕ, i < 100 → ∀ x ∈ Icc ((i : ℝ) / 40) (((i : ℝ) + 1) / 40), ∀ c,
    OrbitRel inner x ψ₀ Bt c → c ≤ cos (3 / 5) →
    0 ≤ numR inner ψ₀ x c ∧ |numR inner ψ₀ x c| ≤ Mf i * denR inner ψ₀ x c (√(1 - c ^ 2))
  /-- Bottom cells. -/
  bottom : ∀ x ∈ Icc (0 : ℝ) (5 / 2), ∀ c, OrbitRel inner x ψ₀ Bt c → cos (3 / 5) ≤ c →
    0 < x ∧ 0 < numR inner ψ₀ x c ∧
    (if inner then 0 < 1 + RR inner ψ₀ x Bt c else 0 < RR inner ψ₀ x Bt c - 1) ∧
    mb ≤ ratR inner ψ₀ x Bt c ∧ ratR inner ψ₀ x Bt c ≤ Mb

/-- Every `x ∈ [0, 5/2]` lies in one of the 100 cells. -/
theorem exists_cell {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (5 / 2)) :
    ∃ i : ℕ, i < 100 ∧ x ∈ Icc ((i : ℝ) / 40) (((i : ℝ) + 1) / 40) := by
  refine ⟨min (⌊40 * x⌋₊) 99, min_lt_of_right_lt (by norm_num), ?_⟩
  have h40 : 0 ≤ 40 * x := by linarith [hx.1]
  have h1 := Nat.floor_le h40
  have h2 := Nat.lt_floor_add_one (40 * x)
  rcases le_total (⌊40 * x⌋₊) 99 with h | h
  · have hc : ((min ⌊40 * x⌋₊ 99 : ℕ) : ℝ) = ⌊40 * x⌋₊ := by rw [min_eq_left h]
    rw [hc]
    constructor
    · rw [div_le_iff₀ (by norm_num)]; linarith
    · rw [le_div_iff₀ (by norm_num)]; linarith
  · have hc : ((min ⌊40 * x⌋₊ 99 : ℕ) : ℝ) = 99 := by rw [min_eq_right h]; norm_num
    have : (99 : ℝ) ≤ ⌊40 * x⌋₊ := by exact_mod_cast h
    rw [hc]
    constructor
    · rw [div_le_iff₀ (by norm_num)]; linarith
    · rw [le_div_iff₀ (by norm_num)]; linarith [hx.2]

/-- `|∂_θB| ≥ 0` in the reduced form, for `s ≥ 0`. -/
theorem denR_nonneg {inner : Bool} {x p b c s : ℝ} (hrel : OrbitRel inner x p b c) (hs0 : 0 ≤ s) :
    0 ≤ denR inner p x c s := by
  unfold denR
  have hw := hrel.psi_pos
  have hw0 : 0 ≤ wR inner p x := by unfold wR; exact mul_nonneg (by norm_num) hw.le
  have hr : √(wR inner p x) ≤ 2 := by
    rw [sqrt_le_left (by norm_num)]; unfold wR; have := hrel.psi_le; linarith
  have hr0 : 0 ≤ √(wR inner p x) := sqrt_nonneg _
  have hw2 : √(wR inner p x) ^ 2 = wR inner p x := sq_sqrt hw0
  have h1 : wR inner p x * c ≤ wR inner p x := mul_le_of_le_one_right hw0 hrel.c_le
  have h2 : wR inner p x ≤ 2 * √(wR inner p x) := by
    calc wR inner p x = √(wR inner p x) * √(wR inner p x) := (mul_self_sqrt hw0).symm
      _ ≤ 2 * √(wR inner p x) := mul_le_mul_of_nonneg_right hr hr0
  apply mul_nonneg hs0
  linarith

/-- **Box soundness.** If `boxOk P T = true`, every `(ψ₀, B_t) ∈ P × T` carries real leg bounds
for both legs whose sums satisfy the target inequalities. -/
theorem box_sound {P T : FIv} (h : boxOk P T = true) {p b : ℝ} (hP : P.Mem p) (hT : T.Mem b) :
    ∃ (Mfi Mfo : ℕ → ℝ) (Mbi mbi Mbo mbo : ℝ),
      LegBounds true p b Mfi Mbi mbi ∧ LegBounds false p b Mfo Mbo mbo ∧
      2 * (1 / 40) * (∑ i ∈ Finset.range 100, Mfi i + ∑ i ∈ Finset.range 100, Mfo i) +
        6 / 5 * (Mbi + Mbo) ≤ 211 / 500 * (13 / 5) ∧
      211 / 500 * (7 / 10) ≤ 6 / 5 * (mbi + mbo) := by
  simp only [boxOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hi, ho⟩, hup⟩, hlow⟩ := h
  -- generic leg
  have leg : ∀ inner : Bool, (legLoop inner P T 100).1 = true →
      LegBounds inner p b (fun i => fxVal (max 0 (flankCell inner (cellX i) P T).2))
        (fxVal (legLoop inner P T 100).2.2.1) (fxVal (legLoop inner P T 100).2.2.2) := by
    intro inner hl
    obtain ⟨hs, -⟩ := legLoop_spec inner P T 100 hl
    refine ⟨fun i => div_nonneg (by exact_mod_cast le_max_left _ _) fxScale_pos.le, ?_, ?_⟩
    · intro i hi x hx c hrel hc
      obtain ⟨h1, h2⟩ := flankCell_sound (hs i hi).1 (mem_cellX hx) hP hT hrel hc
      refine ⟨h1, h2.trans ?_⟩
      have hd : 0 ≤ denR inner p x c (√(1 - c ^ 2)) := denR_nonneg hrel (sqrt_nonneg _)
      apply mul_le_mul_of_nonneg_right _ hd
      unfold fxVal; push_cast
      exact div_le_div_of_nonneg_right (le_max_right _ _) fxScale_pos.le
    · intro x hx c hrel hc
      obtain ⟨i, hi, hxi⟩ := exists_cell hx
      obtain ⟨h1, h2, h3, h4, h5⟩ := bottomCell_sound (hs i hi).2.1 (mem_cellX hxi) hP hT hrel hc
      refine ⟨h1, h2, h3, le_trans ?_ h4, h5.trans ?_⟩
      · unfold fxVal; exact div_le_div_of_nonneg_right (by exact_mod_cast (hs i hi).2.2.2)
          fxScale_pos.le
      · unfold fxVal; exact div_le_div_of_nonneg_right (by exact_mod_cast (hs i hi).2.2.1)
          fxScale_pos.le
  refine ⟨_, _, _, _, _, _, leg true hi, leg false ho, ?_, ?_⟩
  · have e1 := (legLoop_spec true P T 100 hi).2
    have e2 := (legLoop_spec false P T 100 ho).2
    have hS := fxScale_pos
    have hsum : ∀ inner : Bool, ∑ i ∈ Finset.range 100,
        fxVal (max 0 (flankCell inner (cellX i) P T).2) =
        ((∑ i ∈ Finset.range 100, max 0 (flankCell inner (cellX i) P T).2 : ℤ) : ℝ) / fxScale := by
      intro inner; unfold fxVal; push_cast; rw [Finset.sum_div]
    rw [hsum, hsum, ← e1, ← e2]
    unfold fxVal
    have hup' : (500 * ((legLoop true P T 100).2.1 + (legLoop false P T 100).2.1) +
        12000 * ((legLoop true P T 100).2.2.1 + (legLoop false P T 100).2.2.1) : ℝ) ≤
        10972 * fxScale := by exact_mod_cast hup
    rw [show (fxScale : ℝ) = ((fxScale : ℤ) : ℝ) from rfl] at *
    field_simp
    linarith
  · have hS := fxScale_pos
    unfold fxVal
    have hlow' : (1477 * fxScale : ℝ) ≤
        6000 * ((legLoop true P T 100).2.2.2 + (legLoop false P T 100).2.2.2) := by
      exact_mod_cast hlow
    field_simp
    linarith

/-! ## The parameter grid -/

/-- The `j`-th flux box `ψ₀ ∈ [(38 + j)/8, (39 + j)/8]` (`j < 9` covers `[4.75, 5.875]`). -/
@[expose] def PB (j : ℕ) : FIv := hull (38 + j) 8 (39 + j) 8

/-- The `l`-th tip-field box `B_t ∈ [(864 + l)/160, (865 + l)/160]` (`l < 16` covers
`[5.4, 5.5]`). -/
@[expose] def TB (l : ℕ) : FIv := hull (864 + l) 160 (865 + l) 160

/-- Every `y ∈ [a, a + (n+1) d]` lies in one of the `n + 1` subintervals of length `d`. -/
theorem exists_index {y a d : ℝ} {n : ℕ} (hd : 0 < d) (hy : y ∈ Icc a (a + (n + 1) * d)) :
    ∃ j : ℕ, j ≤ n ∧ y ∈ Icc (a + j * d) (a + (j + 1) * d) := by
  set u := (y - a) / d with hu
  have hu0 : 0 ≤ u := div_nonneg (by linarith [hy.1]) hd.le
  have hu1 : u ≤ n + 1 := by rw [hu, div_le_iff₀ hd]; linarith [hy.2]
  refine ⟨min (⌊u⌋₊) n, min_le_right _ _, ?_⟩
  have h1 := Nat.floor_le hu0
  have h2 := Nat.lt_floor_add_one u
  have hyu : y = a + u * d := by rw [hu]; field_simp; ring
  rcases le_total (⌊u⌋₊) n with h | h
  · have hc : ((min ⌊u⌋₊ n : ℕ) : ℝ) = ⌊u⌋₊ := by rw [min_eq_left h]
    rw [hc, hyu]
    constructor <;> nlinarith
  · have hc : ((min ⌊u⌋₊ n : ℕ) : ℝ) = n := by rw [min_eq_right h]
    have : (n : ℝ) ≤ ⌊u⌋₊ := by exact_mod_cast h
    rw [hc, hyu]
    constructor <;> nlinarith

/-- **Precession certificate from the boxes.** If all `9 × 16` boxes pass, every
`(ψ₀, B_t) ∈ [4.75, 5.875] × [5.4, 5.5]` carries leg bounds for both legs with
`2 (1/40) Σ M_f + (6/5)(M_b^in + M_b^out) ≤ ι₀ · 13/5` and `ι₀ · 7/10 ≤ (6/5)(m_b^in + m_b^out)`. -/
theorem precession_cert_of_boxes (hboxes : ∀ j < 9, ∀ l < 16, boxOk (PB j) (TB l) = true)
    {ψ₀ Bt : ℝ}
    (hψ : ψ₀ ∈ Icc (19 / 4 : ℝ) (47 / 8)) (hB : Bt ∈ Icc (27 / 5 : ℝ) (11 / 2)) :
    ∃ (Mfi Mfo : ℕ → ℝ) (Mbi mbi Mbo mbo : ℝ),
      LegBounds true ψ₀ Bt Mfi Mbi mbi ∧ LegBounds false ψ₀ Bt Mfo Mbo mbo ∧
      2 * (1 / 40) * (∑ i ∈ Finset.range 100, Mfi i + ∑ i ∈ Finset.range 100, Mfo i) +
        6 / 5 * (Mbi + Mbo) ≤ 211 / 500 * (13 / 5) ∧
      211 / 500 * (7 / 10) ≤ 6 / 5 * (mbi + mbo) := by
  obtain ⟨j, hj, hψj⟩ := exists_index (a := 19 / 4) (d := 1 / 8) (n := 8) (by norm_num)
    (by norm_num at hψ ⊢; exact hψ)
  obtain ⟨l, hl, hBl⟩ := exists_index (a := 27 / 5) (d := 1 / 160) (n := 15) (by norm_num)
    (by norm_num at hB ⊢; exact hB)
  have hbox := hboxes j (by omega) l (by omega)
  refine box_sound hbox ?_ ?_
  · refine mem_hull (by norm_num) (by norm_num) ?_ ?_
    · push_cast; linarith [hψj.1]
    · push_cast; linarith [hψj.2]
  · refine mem_hull (by norm_num) (by norm_num) ?_ ?_
    · push_cast; linarith [hBl.1]
    · push_cast; linarith [hBl.2]

/-! ## Sanity checks -/

/-- Sanity (degenerate case): at a turning point (`x = 0`) the orbit field is the tip field. -/
theorem BsR_zero (Bt : ℝ) : BsR 0 Bt = Bt := by
  unfold BsR; norm_num; ring

/-- Sanity (special case): on the magnetic axis (`ψ = 0`) the reduced field is `B₀ = 5.7 T`
for every poloidal angle. -/
theorem Bred_axis (c : ℝ) : Bred 0 c = 57 / 10 := by
  unfold Bred; simp

set_option maxRecDepth 100000 in
/-- Sanity (accepted fixture): a flank cell near the tip of the first box is alive and valid. -/
theorem fixture_flank_alive : (flankCell true (cellX 10) (PB 0) (TB 0)).1 = true ∧
    0 < (flankCell true (cellX 10) (PB 0) (TB 0)).2 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Sanity (dead cell): far from the tips (`x ≈ 2.25`) there is no flank point of the inner leg. -/
theorem fixture_flank_dead : flankCell true (cellX 90) (PB 0) (TB 0) = (true, 0) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Sanity (rejected fixture): the whole window as a single box fails the check (interval
over-estimation pushes the upper bound past `ι₀ · 13/5`). -/
theorem fixture_box_rejected : boxOk (hull 38 8 46 8) (hull 864 160 880 160) = false := by
  decide +kernel

end PlasmaLean.Design.NearAxisQATrappedCells
