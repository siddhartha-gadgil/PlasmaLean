/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkGradientBridge

/-!
# A box check for the gradient of the QA2R field strength

On a box in `(u, z, c, s) = (R − R₀, z, cos 2φ, sin 2φ)` the twelve polynomials that enter the
gradient of `|B|²` (`DommaschkGradientBridge`) are enclosed in centred form
(`DommaschkRegionEnclosure.centred`), the three numerators are enclosed by rational interval
arithmetic, and one rational inequality certifies `‖∇|B|‖ ≤ g` on the box.

* `QI`: closed rational intervals with `add`, `mul`, `mag` and their soundness.
* `encl`, `mem_encl`: the centred enclosure of a sparse polynomial on a box.
* `fine g s b c m β B`: the Boolean check (the check `good β c m B` of `DommaschkRegionEnclosure`
  with a lower bound `β ≥ b` of the toroidal component on this box,
  the validity of the nine further enclosures, and the gradient inequality).
* `Fine g s b c m u z c' s'`: the polynomial inequalities at a point; `fine_sound`: they hold at the
  points of an accepted box; `Fine.reflect`: they are invariant under the stellarator reflection
  `(z, s) ↦ (−z, −s)`; `Fine.field`: at `(R − R₀, z, cos 2φ, sin 2φ)` with `R > 0` they give
  `‖∇|B|‖ ≤ g`, `s ≤ |B|` and `PolyBounds b c m` (hence the bound `m` for the planar speed).
* `Cert`: subdivision certificates in `(u, z)`, with `Cert.sound`.

**Sanity.** `QI.mul_fixture` (a product of intervals of both signs), `QI.mag_fixture`, and the
parity facts `parity_reject` (the test is not vacuous). Accepted and rejected boxes of `fine`
are in `DommaschkGradientCheckSanity`.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkGradientCheck
open DommaschkKam DommaschkKam.DkPoly DommaschkBounceField Certificates.ValidatedQuadrature
open Certificates.PositionFrameSlabs (leQ leQ_true)
open DommaschkRegionEnclosure DommaschkGradientBridge DommaschkRegionFieldBounds
open DommaschkCartesianAngleFlow Contract

/-! ## Rational intervals -/

/-- A closed interval with rational endpoints. -/
structure QI where
  /-- Lower endpoint. -/
  lo : ℚ
  /-- Upper endpoint. -/
  hi : ℚ

namespace QI

/-- Membership of a real number. -/
def Mem (I : QI) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

/-- Sum of intervals. -/
def add (a b : QI) : QI := ⟨a.lo + b.lo, a.hi + b.hi⟩

/-- Product of intervals. -/
def mul (a b : QI) : QI :=
  ⟨min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi)),
    max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi))⟩

/-- Largest absolute value. -/
def mag (a : QI) : ℚ := max |a.lo| |a.hi|

theorem mem_add {a b : QI} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) : (a.add b).Mem (x + y) := by
  simp only [Mem, add, Rat.cast_add]
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

theorem mem_mul {a b : QI} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) : (a.mul b).Mem (x * y) := by
  obtain ⟨xl, xh⟩ := hx
  obtain ⟨yl, yh⟩ := hy
  simp only [Mem, mul, Rat.cast_min, Rat.cast_max, Rat.cast_mul]
  constructor
  · rcases le_total 0 y with h | h
    · have h1 : (a.lo : ℝ) * y ≤ x * y := mul_le_mul_of_nonneg_right xl h
      rcases le_total 0 (a.lo : ℝ) with ha | ha
      · exact (min_le_left _ _).trans ((min_le_left _ _).trans
          ((mul_le_mul_of_nonneg_left yl ha).trans h1))
      · exact (min_le_left _ _).trans ((min_le_right _ _).trans
          ((mul_le_mul_of_nonpos_left yh ha).trans h1))
    · have h1 : (a.hi : ℝ) * y ≤ x * y := mul_le_mul_of_nonpos_right xh h
      rcases le_total 0 (a.hi : ℝ) with ha | ha
      · exact (min_le_right _ _).trans ((min_le_left _ _).trans
          ((mul_le_mul_of_nonneg_left yl ha).trans h1))
      · exact (min_le_right _ _).trans ((min_le_right _ _).trans
          ((mul_le_mul_of_nonpos_left yh ha).trans h1))
  · rcases le_total 0 y with h | h
    · have h1 : x * y ≤ (a.hi : ℝ) * y := mul_le_mul_of_nonneg_right xh h
      rcases le_total 0 (a.hi : ℝ) with ha | ha
      · exact (h1.trans (mul_le_mul_of_nonneg_left yh ha)).trans
          ((le_max_right _ _).trans (le_max_right _ _))
      · exact (h1.trans (mul_le_mul_of_nonpos_left yl ha)).trans
          ((le_max_left _ _).trans (le_max_right _ _))
    · have h1 : x * y ≤ (a.lo : ℝ) * y := mul_le_mul_of_nonpos_right xl h
      rcases le_total 0 (a.lo : ℝ) with ha | ha
      · exact (h1.trans (mul_le_mul_of_nonneg_left yh ha)).trans
          ((le_max_right _ _).trans (le_max_left _ _))
      · exact (h1.trans (mul_le_mul_of_nonpos_left yl ha)).trans
          ((le_max_left _ _).trans (le_max_left _ _))

theorem abs_le_mag {a : QI} {x : ℝ} (hx : a.Mem x) : |x| ≤ ((a.mag : ℚ) : ℝ) := by
  simp only [mag, Rat.cast_max, Rat.cast_abs]
  exact abs_le_max_abs_abs hx.1 hx.2

/-- **Sanity**: `[−1, 2] · [−3, 5] = [−6, 10]`. -/
theorem mul_fixture : mul ⟨-1, 2⟩ ⟨-3, 5⟩ = ⟨-6, 10⟩ := by
  with_unfolding_all rfl

/-- **Sanity**: the magnitude of `[−3, 2]` is `3`. -/
theorem mag_fixture : mag ⟨-3, 2⟩ = 3 := by
  with_unfolding_all rfl

end QI

/-! ## Centred enclosures as rational intervals -/

/-- The centred enclosure of a sparse polynomial on a box. -/
def encl (B : Box) (p : SP) : QI :=
  ⟨qv (polyBox (ptBox B) p).lo - radius B p, qv (polyBox (ptBox B) p).hi + radius B p⟩

theorem mem_encl (B : Box) (p : SP) {u z c s : ℝ} (hm : B.Mem u z c s)
    (oku : B.u.ok = true) (okz : B.z.ok = true) (okc : B.c.ok = true) (oks : B.s.ok = true)
    (fl : flags B p = true) (hR : 0 ≤ qv B.u.lo + 29 / 32) : (encl B p).Mem (evR u z c s p) := by
  have cen := centred B p 0 hm oku okz okc oks fl le_rfl hR
  have fl' := fl
  simp only [flags, Bool.and_eq_true] at fl'
  obtain ⟨ml, mh⟩ := mem_Icc (mem_midpoint B p) fl'.1.1.1.1
  simp only [Rat.cast_zero, zero_mul, sub_zero] at cen
  obtain ⟨a, b⟩ := abs_le.mp cen
  simp only [QI.Mem, encl, radius, Rat.cast_sub, Rat.cast_add]
  push_cast at a b
  constructor <;> linarith

/-- The interval of `R²` on the box. -/
def r2 (B : Box) : QI := ⟨(qv B.u.lo + 29 / 32) ^ 2, (qv B.u.hi + 29 / 32) ^ 2⟩

/-- Bound of the absolute value of the numerator `2 (R² D x + n_R y + n_z w)` on the box. -/
def comb (B : Box) (x y w : SP) : ℚ :=
  2 * (((r2 B).mul ((encl B dD).mul (encl B x))).add
    (((encl B dnR).mul (encl B y)).add ((encl B dnZ).mul (encl B w)))).mag

/-- Lower bound of `n_R² + n_z²` on the box. -/
def polLower (B : Box) : ℚ :=
  ((encl B dnR).mul (encl B dnR)).lo + ((encl B dnZ).mul (encl B dnZ)).lo

/-- **The check on one box**, with a lower bound `β ≥ b` of the toroidal component on this
box: the check `good β c m` of the region enclosure (`β ≤ B_φ ≤ c`, planar speed at most `m`),
the validity of the nine further enclosures, the strength inequality
`s² R¹⁶ ≤ β² R¹⁶ + n_R² + n_z²` and the gradient inequality
`numR² + numT² + R² numZ² ≤ 4 g² R¹⁸ max (R² D²) (s² R¹⁶)` with the bounds of the box. -/
def fine (g s b c m β : ℚ) (B : Box) : Bool :=
  good β c m B && flags B pDR && flags B pPR && flags B pQR && flags B pDT && flags B pPT &&
    flags B pQT && flags B pDZ && flags B pPZ && flags B pQZ && leQ b β &&
    leQ ((s ^ 2 - β ^ 2) * (qv B.u.hi + 29 / 32) ^ 16) (max 0 (polLower B)) &&
    leQ (comb B pDR pPR pQR ^ 2 + comb B pDT pPT pQT ^ 2 +
        (qv B.u.hi + 29 / 32) ^ 2 * comb B pDZ pPZ pQZ ^ 2)
      (4 * g ^ 2 * (qv B.u.lo + 29 / 32) ^ 18 *
        max ((qv B.u.lo + 29 / 32) ^ 2 * lowerD B ^ 2) (s ^ 2 * (qv B.u.lo + 29 / 32) ^ 16))

/-- The polynomial inequalities at a point: the three bounds of `PolyBounds`, the strength
inequality and the gradient inequality. -/
def Fine (g s b c m u z cs sn : ℝ) : Prop :=
  (b * (u + dkR0) ^ 7 ≤ evR u z cs sn dD ∧ evR u z cs sn dD ≤ c * (u + dkR0) ^ 7 ∧
    evR u z cs sn dnR ^ 2 + evR u z cs sn dnZ ^ 2 ≤ m ^ 2 * evR u z cs sn dD ^ 2) ∧
  s ^ 2 * (u + dkR0) ^ 16 ≤
    (u + dkR0) ^ 2 * evR u z cs sn dD ^ 2 + evR u z cs sn dnR ^ 2 + evR u z cs sn dnZ ^ 2 ∧
  numR u z cs sn ^ 2 + numT u z cs sn ^ 2 + (u + dkR0) ^ 2 * numZ u z cs sn ^ 2 ≤
    4 * g ^ 2 * (u + dkR0) ^ 18 *
      ((u + dkR0) ^ 2 * evR u z cs sn dD ^ 2 + evR u z cs sn dnR ^ 2 + evR u z cs sn dnZ ^ 2)

/-- **Soundness of the check on a box.** -/
theorem fine_sound {g s b c m β : ℚ} (hb : 0 ≤ b) (hc : 0 ≤ c) {B : Box}
    (h : fine g s b c m β B = true) {u z cs sn : ℝ} (hm : B.Mem u z cs sn) :
    Fine g s b c m u z cs sn := by
  simp only [fine, Bool.and_eq_true, leQ_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hgood, fDR⟩, fPR⟩, fQR⟩, fDT⟩, fPT⟩, fQT⟩, fDZ⟩, fPZ⟩, fQZ⟩, bs⟩, str⟩,
    grad⟩ := h
  have gs := good_sound (hb.trans bs) hc hgood hm
  have hgood' := hgood
  simp only [good, Bool.and_eq_true, leQ_true] at hgood'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨oku, okz⟩, okc⟩, oks⟩, fD⟩, fP⟩, fQ⟩, hR⟩, -⟩, -⟩, pos⟩, -⟩ := hgood'
  obtain ⟨ul, uh⟩ := mem_Icc hm.1 oku
  have hR' : (0 : ℝ) ≤ (qv B.u.lo : ℚ) + 29 / 32 := by
    have h := (Rat.cast_nonneg (K := ℝ)).mpr hR
    push_cast at h
    exact h
  have Rl : ((qv B.u.lo : ℚ) : ℝ) + 29 / 32 ≤ u + dkR0 := by unfold dkR0; linarith
  have Rh : u + dkR0 ≤ ((qv B.u.hi : ℚ) : ℝ) + 29 / 32 := by unfold dkR0; linarith
  have R0 : 0 ≤ u + dkR0 := hR'.trans Rl
  have mR : (r2 B).Mem ((u + dkR0) ^ 2) := by
    simp only [QI.Mem, r2, Rat.cast_pow, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat]
    exact ⟨pow_le_pow_left₀ hR' Rl 2, pow_le_pow_left₀ R0 Rh 2⟩
  have me (p : SP) (fl : flags B p = true) := mem_encl B p hm oku okz okc oks fl hR
  -- the strength inequality
  have hb' : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have bs' : (b : ℝ) ≤ (β : ℝ) := by exact_mod_cast bs
  have R7 : 0 ≤ (u + dkR0) ^ 7 := pow_nonneg R0 7
  have gb : (b : ℝ) * (u + dkR0) ^ 7 ≤ evR u z cs sn dD :=
    (mul_le_mul_of_nonneg_right bs' R7).trans gs.1
  have str' := (Rat.cast_le (K := ℝ)).mpr str
  simp only [polLower, Rat.cast_mul, Rat.cast_sub, Rat.cast_pow, Rat.cast_add, Rat.cast_div,
    Rat.cast_ofNat, Rat.cast_max, Rat.cast_zero] at str'
  have pP := (QI.mem_mul (me dnR fP) (me dnR fP)).1
  have pQ := (QI.mem_mul (me dnZ fQ) (me dnZ fQ)).1
  have r16 : (u + dkR0) ^ 16 ≤ (((qv B.u.hi : ℚ) : ℝ) + 29 / 32) ^ 16 := pow_le_pow_left₀ R0 Rh 16
  have dlow : ((β : ℝ) * (u + dkR0) ^ 7) ^ 2 ≤ evR u z cs sn dD ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (hb'.trans bs') R7) gs.1 2
  have h2 := mul_le_mul_of_nonneg_left dlow (sq_nonneg (u + dkR0))
  have e : (u + dkR0) ^ 2 * ((β : ℝ) * (u + dkR0) ^ 7) ^ 2 = (β : ℝ) ^ 2 * (u + dkR0) ^ 16 := by
    ring
  have pol : max (0 : ℝ) (((encl B dnR).mul (encl B dnR)).lo + ((encl B dnZ).mul (encl B dnZ)).lo) ≤
      evR u z cs sn dnR ^ 2 + evR u z cs sn dnZ ^ 2 :=
    max_le (by positivity) (by linarith)
  have strength : (s : ℝ) ^ 2 * (u + dkR0) ^ 16 ≤
      (u + dkR0) ^ 2 * evR u z cs sn dD ^ 2 + evR u z cs sn dnR ^ 2 + evR u z cs sn dnZ ^ 2 := by
    rcases le_total ((s : ℝ) ^ 2) ((β : ℝ) ^ 2) with le | ge
    · have h1 := mul_le_mul_of_nonneg_right le (pow_nonneg R0 16)
      linarith [sq_nonneg (evR u z cs sn dnR), sq_nonneg (evR u z cs sn dnZ)]
    · have h1 := mul_le_mul_of_nonneg_left r16 (sub_nonneg.mpr ge)
      linarith
  refine ⟨⟨gb, gs.2⟩, strength, ?_⟩
  -- the gradient inequality
  have bound (x y w : SP) (fx : flags B x = true) (fy : flags B y = true)
      (fw : flags B w = true) : |num x y w u z cs sn| ≤ ((comb B x y w : ℚ) : ℝ) := by
    have h := QI.abs_le_mag (QI.mem_add (QI.mem_mul mR (QI.mem_mul (me dD fD) (me x fx)))
      (QI.mem_add (QI.mem_mul (me dnR fP) (me y fy)) (QI.mem_mul (me dnZ fQ) (me w fw))))
    have e : num x y w u z cs sn = 2 * ((u + dkR0) ^ 2 * (evR u z cs sn dD * evR u z cs sn x) +
        (evR u z cs sn dnR * evR u z cs sn y + evR u z cs sn dnZ * evR u z cs sn w)) := by
      unfold num
      ring
    rw [e, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [comb, Rat.cast_mul, Rat.cast_ofNat]
    linarith
  have sq {a : ℝ} {q : ℚ} (h : |a| ≤ (q : ℝ)) : a ^ 2 ≤ (q : ℝ) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
  have bR := sq (bound pDR pPR pQR fDR fPR fQR)
  have bT := sq (bound pDT pPT pQT fDT fPT fQT)
  have bZ := sq (bound pDZ pPZ pQZ fDZ fPZ fQZ)
  have grad' := (Rat.cast_le (K := ℝ)).mpr grad
  have pos' := (Rat.cast_le (K := ℝ)).mpr pos
  push_cast at grad' pos'
  have dl : ((lowerD B : ℚ) : ℝ) ≤ evR u z cs sn dD := (me dD fD).1
  have d2 : ((lowerD B : ℚ) : ℝ) ^ 2 ≤ evR u z cs sn dD ^ 2 := pow_le_pow_left₀ pos' dl 2
  have rl2 : (((qv B.u.lo : ℚ) : ℝ) + 29 / 32) ^ 2 ≤ (u + dkR0) ^ 2 := pow_le_pow_left₀ hR' Rl 2
  have rl16 : (((qv B.u.lo : ℚ) : ℝ) + 29 / 32) ^ 16 ≤ (u + dkR0) ^ 16 :=
    pow_le_pow_left₀ hR' Rl 16
  have rl18 : (((qv B.u.lo : ℚ) : ℝ) + 29 / 32) ^ 18 ≤ (u + dkR0) ^ 18 :=
    pow_le_pow_left₀ hR' Rl 18
  have rh2 : (u + dkR0) ^ 2 ≤ (((qv B.u.hi : ℚ) : ℝ) + 29 / 32) ^ 2 := pow_le_pow_left₀ R0 Rh 2
  have zz : (u + dkR0) ^ 2 * numZ u z cs sn ^ 2 ≤
      (((qv B.u.hi : ℚ) : ℝ) + 29 / 32) ^ 2 * ((comb B pDZ pPZ pQZ : ℚ) : ℝ) ^ 2 :=
    mul_le_mul rh2 bZ (sq_nonneg _) (by positivity)
  set K := (u + dkR0) ^ 2 * evR u z cs sn dD ^ 2 + evR u z cs sn dnR ^ 2 + evR u z cs sn dnZ ^ 2
    with hK
  have m1 : (((qv B.u.lo : ℚ) : ℝ) + 29 / 32) ^ 2 * ((lowerD B : ℚ) : ℝ) ^ 2 ≤ K := by
    have h := mul_le_mul rl2 d2 (sq_nonneg _) (sq_nonneg (u + dkR0))
    rw [hK]
    linarith [sq_nonneg (evR u z cs sn dnR), sq_nonneg (evR u z cs sn dnZ)]
  have m2 : (s : ℝ) ^ 2 * (((qv B.u.lo : ℚ) : ℝ) + 29 / 32) ^ 16 ≤ K :=
    (mul_le_mul_of_nonneg_left rl16 (sq_nonneg _)).trans strength
  have mK := max_le m1 m2
  have K0 : 0 ≤ K := (mul_nonneg (sq_nonneg _) (by positivity)).trans m2
  have g2 : (0 : ℝ) ≤ 4 * (g : ℝ) ^ 2 := by positivity
  have low : 4 * (g : ℝ) ^ 2 * (((qv B.u.lo : ℚ) : ℝ) + 29 / 32) ^ 18 *
      max ((((qv B.u.lo : ℚ) : ℝ) + 29 / 32) ^ 2 * ((lowerD B : ℚ) : ℝ) ^ 2)
        ((s : ℝ) ^ 2 * (((qv B.u.lo : ℚ) : ℝ) + 29 / 32) ^ 16) ≤
      4 * (g : ℝ) ^ 2 * (u + dkR0) ^ 18 * K := by
    rw [mul_assoc (4 * (g : ℝ) ^ 2), mul_assoc (4 * (g : ℝ) ^ 2)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul rl18 mK
      (le_max_of_le_left (by positivity)) (by positivity)) g2
  unfold numR numT numZ
  unfold numZ at zz
  linarith

/-! ## The stellarator reflection -/

theorem parity_D : DommaschkRegionGrid.parity 0 dD = true := DommaschkRegionGrid.parity_D
theorem parity_P : DommaschkRegionGrid.parity 1 dnR = true := DommaschkRegionGrid.parity_R
theorem parity_Q : DommaschkRegionGrid.parity 0 dnZ = true := DommaschkRegionGrid.parity_Z
theorem parity_DR : DommaschkRegionGrid.parity 0 pDR = true := by kernel_fact
theorem parity_PR : DommaschkRegionGrid.parity 1 pPR = true := by kernel_fact
theorem parity_QR : DommaschkRegionGrid.parity 0 pQR = true := by kernel_fact
theorem parity_DT : DommaschkRegionGrid.parity 1 pDT = true := by kernel_fact
theorem parity_PT : DommaschkRegionGrid.parity 0 pPT = true := by kernel_fact
theorem parity_QT : DommaschkRegionGrid.parity 1 pQT = true := by kernel_fact
theorem parity_DZ : DommaschkRegionGrid.parity 1 pDZ = true := by kernel_fact
theorem parity_PZ : DommaschkRegionGrid.parity 0 pPZ = true := by kernel_fact
theorem parity_QZ : DommaschkRegionGrid.parity 1 pQZ = true := by kernel_fact

/-- **Sanity**: the angular derivative of `D` is not even, so the parity test is not vacuous. -/
theorem parity_reject : DommaschkRegionGrid.parity 0 pDT = false := by kernel_fact

/-- The polynomial inequalities are invariant under `(z, s) ↦ (−z, −s)`. -/
theorem Fine.reflect {g s b c m u z cs sn : ℝ} (h : Fine g s b c m u z cs sn) :
    Fine g s b c m u (-z) cs (-sn) := by
  open DommaschkRegionGrid in
  unfold Fine numR numT numZ num at h ⊢
  rw [reflect_even dD parity_D, reflect_odd dnR parity_P, reflect_even dnZ parity_Q,
    reflect_even pDR parity_DR, reflect_odd pPR parity_PR, reflect_even pQR parity_QR,
    reflect_odd pDT parity_DT, reflect_even pPT parity_PT, reflect_odd pQT parity_QT,
    reflect_odd pDZ parity_DZ, reflect_even pPZ parity_PZ, reflect_odd pQZ parity_QZ]
  refine ⟨by simpa using h.1, ?_, ?_⟩
  · have e := h.2.1
    ring_nf at e ⊢
    exact e
  · have e := h.2.2
    ring_nf at e ⊢
    exact e

/-! ## From the polynomial inequalities to the field -/

set_option maxRecDepth 8000 in
/-- **The field bounds at a point.** At positive radius the polynomial inequalities at
`(R − R₀, z, cos 2φ, sin 2φ)` give the bound `g` for the gradient of the field strength, the
lower bound `s` for the strength, and `PolyBounds b c m`. -/
theorem Fine.field {g s b c m R t z : ℝ}
    (h : Fine g s b c m (R - dkR0) z (Real.cos (2 * t)) (Real.sin (2 * t))) (hR : 0 < R)
    (hb : 0 < b) (hs : 0 ≤ s) (hg : 0 ≤ g) :
    ‖Kinetic.GCLittlejohn.gradAbsB B (cylPoint R t z)‖ ≤ g ∧ s ≤ ‖B (cylPoint R t z)‖ ∧
      PolyBounds b c m R t z := by
  obtain ⟨pb, str, grad⟩ := h
  rw [sub_add_cancel] at pb str grad
  have pb' : PolyBounds b c m R t z := pb
  have ne : B (cylPoint R t z) ≠ 0 := norm_pos_iff.mp (hb.trans_le (pb'.strength_ge hR hb.le))
  have r16 : 0 < R ^ 16 := by positivity
  have strength : s ≤ ‖B (cylPoint R t z)‖ := by
    apply (sq_le_sq₀ hs (norm_nonneg _)).mp
    refine le_of_mul_le_mul_left ?_ r16
    rw [norm_sq_mul hR t z]
    refine le_trans (le_of_eq ?_) str
    ring
  refine ⟨?_, strength, pb'⟩
  have key := gradAbsB_sq hR t z ne
  have dpos : 0 < atPoint dD R t z := lt_of_lt_of_le (by positivity) pb'.1
  have kpos : 0 < 4 * R ^ 18 * (R ^ 2 * atPoint dD R t z ^ 2 + atPoint dnR R t z ^ 2 +
      atPoint dnZ R t z ^ 2) := by positivity
  have le : 4 * R ^ 18 * (R ^ 2 * atPoint dD R t z ^ 2 + atPoint dnR R t z ^ 2 +
      atPoint dnZ R t z ^ 2) * ‖Kinetic.GCLittlejohn.gradAbsB B (cylPoint R t z)‖ ^ 2 ≤
      4 * R ^ 18 * (R ^ 2 * atPoint dD R t z ^ 2 + atPoint dnR R t z ^ 2 +
      atPoint dnZ R t z ^ 2) * g ^ 2 := by
    rw [key]
    refine grad.trans (le_of_eq ?_)
    simp only [atPoint]
    ring
  exact (sq_le_sq₀ (norm_nonneg _) hg).mp (le_of_mul_le_mul_left le kpos)

/-! ## Subdivision certificates -/

open DommaschkRegionGrid (lower upper quad mem_lower_or_upper) in
/-- A subdivision certificate: the check holds on the box, or on the two halves in `u`, or each
of the four quarters in `(u, z)` has a certificate. -/
inductive Cert (g s b c m : ℚ) : Box → Prop where
  | leaf {B : Box} (β : ℚ) : fine g s b c m β B = true → Cert g s b c m B
  | halves {B : Box} : Cert g s b c m ⟨lower B.u, B.z, B.c, B.s⟩ →
      Cert g s b c m ⟨upper B.u, B.z, B.c, B.s⟩ → Cert g s b c m B
  | split {B : Box} : Cert g s b c m (quad B 0) → Cert g s b c m (quad B 1) →
      Cert g s b c m (quad B 2) → Cert g s b c m (quad B 3) → Cert g s b c m B

open DommaschkRegionGrid (lower upper quad mem_lower_or_upper) in
/-- Soundness of a subdivision certificate. -/
theorem Cert.sound {g s b c m : ℚ} (hb : 0 ≤ b) (hc : 0 ≤ c) {u z cs sn : ℝ} {B : Box}
    (h : Cert g s b c m B) : B.Mem u z cs sn → Fine g s b c m u z cs sn := by
  induction h with
  | leaf β h => exact fun hm => fine_sound hb hc h hm
  | halves _ _ i0 i1 =>
    rintro ⟨mu, mz, mc, ms⟩
    rcases mem_lower_or_upper mu with a | a
    · exact i0 ⟨a, mz, mc, ms⟩
    · exact i1 ⟨a, mz, mc, ms⟩
  | split _ _ _ _ i0 i1 i2 i3 =>
    rintro ⟨mu, mz, mc, ms⟩
    rcases mem_lower_or_upper mu with a | a <;> rcases mem_lower_or_upper mz with b | b
    · exact i0 ⟨a, b, mc, ms⟩
    · exact i1 ⟨a, b, mc, ms⟩
    · exact i2 ⟨a, b, mc, ms⟩
    · exact i3 ⟨a, b, mc, ms⟩

end PlasmaLean.Design.DommaschkGradientCheck
