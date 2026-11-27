/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkBounceField
public import PlasmaLean.Certificates.KernelFact
public import PlasmaLean.Certificates.PositionFrameSlabs
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Centred interval enclosures of the QA2R field polynomials on a box

The monomial-wise interval evaluation `polyBox` of a sparse polynomial in
`(u, z, c, s) = (R − R₀, z, cos 2φ, sin 2φ)` overestimates its range by an amount proportional to
the width of the box. Here the same evaluation is applied to the four formal partial derivatives,
and the polynomial itself is evaluated only at the midpoint of the box (mean-value form): the
overestimate becomes quadratic in the width.

* `hasDerivAt_u`, …, `hasDerivAt_s`: the formal partial derivatives `dU`, `dZ`, `dC`, `dS` are the
  partial derivatives of the real evaluation `evR`.
* `mean_value`: the mean-value inequality on a box for `evR p − h(u)`, with `h` any differentiable
  function of the first variable.
* `centred`: on a box `B`, the function `evR p − κ (u + R₀)⁷` differs from its value at the
  midpoint by at most `slope B (polyBox B (dU p)) κ + tail B p`; `mem_midpoint`: the value at the
  midpoint lies in `polyBox (ptBox B) p`.
* `good`: a Boolean check on a box (evaluated by the kernel) for the three bounds
  `b₀ R⁷ ≤ D ≤ c₁ R⁷` and `n_R² + n_z² ≤ M² D²`; `good_sound` is its soundness.

**Sanity.** `good_fixture` (an accepted box), `good_reject` (a box of the envelope that is too
wide is rejected), and `slope_zero` (without the comparison term the slope is the plain bound).
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkRegionEnclosure
open DommaschkKam DommaschkKam.DkPoly DommaschkBounceField Certificates.ValidatedQuadrature
open Certificates.PositionFrameSlabs (leQ leQ_true)

/-! ## Partial derivatives of the real evaluation -/

theorem evR_cons (m : Tm) (p : SP) (u z c s : ℝ) :
    evR u z c s (m :: p) = (m.q : ℝ) * (u ^ m.a * z ^ m.b * c ^ m.c * s ^ m.d) +
      evR u z c s p := by
  simp [evR]

theorem evR_append (p q : SP) (u z c s : ℝ) :
    evR u z c s (p ++ q) = evR u z c s p + evR u z c s q := by
  simp [evR]

/-- The formal `∂_u` is the derivative in the first variable. -/
theorem hasDerivAt_u (p : SP) (u z c s : ℝ) :
    HasDerivAt (fun x => evR x z c s p) (evR u z c s (dU p)) u := by
  induction p with
  | nil => simpa [evR, dU] using hasDerivAt_const u (0 : ℝ)
  | cons m p ih =>
    simp only [evR_cons, dU, List.flatMap_cons, evR_append]
    refine HasDerivAt.add ?_ ih
    have h := ((hasDerivAt_pow m.a u).mul_const (z ^ m.b * c ^ m.c * s ^ m.d)).const_mul (m.q : ℝ)
    convert h using 1
    · funext x; ring
    · cases ha : m.a <;> simp [Tm.dU, ha, evR]
      ring

/-- The formal `∂_z` is the derivative in the second variable. -/
theorem hasDerivAt_z (p : SP) (u z c s : ℝ) :
    HasDerivAt (fun x => evR u x c s p) (evR u z c s (dZ p)) z := by
  induction p with
  | nil => simpa [evR, dZ] using hasDerivAt_const z (0 : ℝ)
  | cons m p ih =>
    simp only [evR_cons, dZ, List.flatMap_cons, evR_append]
    refine HasDerivAt.add ?_ ih
    have h := ((hasDerivAt_pow m.b z).mul_const (u ^ m.a * c ^ m.c * s ^ m.d)).const_mul (m.q : ℝ)
    convert h using 1
    · funext x; ring
    · cases hb : m.b <;> simp [Tm.dZ, hb, evR]
      ring

/-- The formal `∂_c` is the derivative in the third variable. -/
theorem hasDerivAt_c (p : SP) (u z c s : ℝ) :
    HasDerivAt (fun x => evR u z x s p) (evR u z c s (dC p)) c := by
  induction p with
  | nil => simpa [evR, dC] using hasDerivAt_const c (0 : ℝ)
  | cons m p ih =>
    simp only [evR_cons, dC, List.flatMap_cons, evR_append]
    refine HasDerivAt.add ?_ ih
    have h := ((hasDerivAt_pow m.c c).mul_const (u ^ m.a * z ^ m.b * s ^ m.d)).const_mul (m.q : ℝ)
    convert h using 1
    · funext x; ring
    · cases hc : m.c <;> simp [Tm.dC, hc, evR]
      ring

/-- The formal `∂_s` is the derivative in the fourth variable. -/
theorem hasDerivAt_s (p : SP) (u z c s : ℝ) :
    HasDerivAt (fun x => evR u z c x p) (evR u z c s (dS p)) s := by
  induction p with
  | nil => simpa [evR, dS] using hasDerivAt_const s (0 : ℝ)
  | cons m p ih =>
    simp only [evR_cons, dS, List.flatMap_cons, evR_append]
    refine HasDerivAt.add ?_ ih
    have h := ((hasDerivAt_pow m.d s).mul_const (u ^ m.a * z ^ m.b * c ^ m.c)).const_mul (m.q : ℝ)
    convert h using 1
    · funext x; ring
    · cases hd : m.d <;> simp [Tm.dS, hd, evR]
      ring

/-! ## The mean-value inequality on a box -/

/-- One-variable mean-value inequality on a closed interval. -/
theorem step {g g' : ℝ → ℝ} {x x₀ lo hi A : ℝ} (hx : x ∈ Set.Icc lo hi) (hx₀ : x₀ ∈ Set.Icc lo hi)
    (dg : ∀ y, HasDerivAt g (g' y) y) (bd : ∀ y ∈ Set.Icc lo hi, |g' y| ≤ A) :
    |g x - g x₀| ≤ A * |x - x₀| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g) (f' := g')
    (s := Set.Icc lo hi) (C := A) (fun y _ => (dg y).hasDerivWithinAt)
    (fun y hy => by simpa using bd y hy) (convex_Icc lo hi) hx₀ hx
  simpa [Real.norm_eq_abs] using h

/-- **Mean-value inequality on a box** for a sparse polynomial minus a function of the first
variable. -/
theorem mean_value (p : SP) (h h' : ℝ → ℝ) {u z c s u₀ z₀ c₀ s₀ : ℝ}
    {ul uh zl zh cl ch sl sh Au Az Ac As : ℝ}
    (hu : u ∈ Set.Icc ul uh) (hz : z ∈ Set.Icc zl zh) (hc : c ∈ Set.Icc cl ch)
    (hs : s ∈ Set.Icc sl sh) (hu₀ : u₀ ∈ Set.Icc ul uh) (hz₀ : z₀ ∈ Set.Icc zl zh)
    (hc₀ : c₀ ∈ Set.Icc cl ch) (hs₀ : s₀ ∈ Set.Icc sl sh)
    (dh : ∀ x, HasDerivAt h (h' x) x)
    (bu : ∀ u' ∈ Set.Icc ul uh, ∀ z' ∈ Set.Icc zl zh, ∀ c' ∈ Set.Icc cl ch, ∀ s' ∈ Set.Icc sl sh,
      |evR u' z' c' s' (dU p) - h' u'| ≤ Au)
    (bz : ∀ u' ∈ Set.Icc ul uh, ∀ z' ∈ Set.Icc zl zh, ∀ c' ∈ Set.Icc cl ch, ∀ s' ∈ Set.Icc sl sh,
      |evR u' z' c' s' (dZ p)| ≤ Az)
    (bc : ∀ u' ∈ Set.Icc ul uh, ∀ z' ∈ Set.Icc zl zh, ∀ c' ∈ Set.Icc cl ch, ∀ s' ∈ Set.Icc sl sh,
      |evR u' z' c' s' (dC p)| ≤ Ac)
    (bs : ∀ u' ∈ Set.Icc ul uh, ∀ z' ∈ Set.Icc zl zh, ∀ c' ∈ Set.Icc cl ch, ∀ s' ∈ Set.Icc sl sh,
      |evR u' z' c' s' (dS p)| ≤ As) :
    |(evR u z c s p - h u) - (evR u₀ z₀ c₀ s₀ p - h u₀)| ≤
      Au * |u - u₀| + Az * |z - z₀| + Ac * |c - c₀| + As * |s - s₀| := by
  have e1 : |(evR u z c s p - h u) - (evR u₀ z c s p - h u₀)| ≤ Au * |u - u₀| :=
    step (g := fun x => evR x z c s p - h x) (g' := fun x => evR x z c s (dU p) - h' x) hu hu₀
      (fun y => (hasDerivAt_u p y z c s).sub (dh y)) (fun y hy => bu y hy z hz c hc s hs)
  have e2 : |evR u₀ z c s p - evR u₀ z₀ c s p| ≤ Az * |z - z₀| :=
    step (g := fun x => evR u₀ x c s p) (g' := fun x => evR u₀ x c s (dZ p)) hz hz₀
      (fun y => hasDerivAt_z p u₀ y c s) (fun y hy => bz u₀ hu₀ y hy c hc s hs)
  have e3 : |evR u₀ z₀ c s p - evR u₀ z₀ c₀ s p| ≤ Ac * |c - c₀| :=
    step (g := fun x => evR u₀ z₀ x s p) (g' := fun x => evR u₀ z₀ x s (dC p)) hc hc₀
      (fun y => hasDerivAt_c p u₀ z₀ y s) (fun y hy => bc u₀ hu₀ z₀ hz₀ y hy s hs)
  have e4 : |evR u₀ z₀ c₀ s p - evR u₀ z₀ c₀ s₀ p| ≤ As * |s - s₀| :=
    step (g := fun x => evR u₀ z₀ c₀ x p) (g' := fun x => evR u₀ z₀ c₀ x (dS p)) hs hs₀
      (fun y => hasDerivAt_s p u₀ z₀ c₀ y) (fun y hy => bs u₀ hu₀ z₀ hz₀ c₀ hc₀ y hy)
  rw [abs_le] at e1 e2 e3 e4 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2]

/-! ## Midpoints, radii and magnitudes of fixed-point intervals -/

/-- The rational value `n / 2³²` of a fixed-point integer. -/
def qv (n : ℤ) : ℚ := n / 4294967296

theorem fxVal_eq (n : ℤ) : fxVal n = ((qv n : ℚ) : ℝ) := by
  simp [fxVal, qv, fxScale]

/-- The fixed-point midpoint. -/
def mid (I : FIv) : ℤ := (I.lo + I.hi) / 2

/-- The point interval at the midpoint. -/
def pt (I : FIv) : FIv := ⟨mid I, mid I, true⟩

/-- The largest distance of a point of the interval to the midpoint. -/
def rad (I : FIv) : ℚ := max (qv I.hi - qv (mid I)) (qv (mid I) - qv I.lo)

/-- The largest absolute value of a point of the interval. -/
def mag (I : FIv) : ℚ := max |qv I.lo| |qv I.hi|

/-- The box of the four midpoints. -/
def ptBox (B : Box) : Box := ⟨pt B.u, pt B.z, pt B.c, pt B.s⟩

theorem mem_pt (I : FIv) : (pt I).Mem (fxVal (mid I)) := fun _ => ⟨le_rfl, le_rfl⟩

theorem mem_Icc {I : FIv} {x : ℝ} (h : I.Mem x) (ok : I.ok = true) :
    x ∈ Set.Icc ((qv I.lo : ℚ) : ℝ) (qv I.hi : ℚ) := by
  simpa [fxVal_eq] using h ok

theorem mid_mem_Icc {I : FIv} {x : ℝ} (h : I.Mem x) (ok : I.ok = true) :
    ((qv (mid I) : ℚ) : ℝ) ∈ Set.Icc ((qv I.lo : ℚ) : ℝ) (qv I.hi : ℚ) := by
  obtain ⟨l, r⟩ := mem_Icc h ok
  have le : I.lo ≤ I.hi := by
    have : ((qv I.lo : ℚ) : ℝ) ≤ (qv I.hi : ℚ) := l.trans r
    have h' : qv I.lo ≤ qv I.hi := by exact_mod_cast this
    unfold qv at h'
    have h'' := (div_le_div_iff_of_pos_right (by norm_num : (0 : ℚ) < 4294967296)).mp h'
    exact_mod_cast h''
  have a : I.lo ≤ mid I := by unfold mid; omega
  have b : mid I ≤ I.hi := by unfold mid; omega
  have mono : ∀ {m n : ℤ}, m ≤ n → ((qv m : ℚ) : ℝ) ≤ (qv n : ℚ) := by
    intro m n hmn
    have : qv m ≤ qv n := by
      unfold qv
      exact div_le_div_of_nonneg_right (by exact_mod_cast hmn) (by norm_num)
    exact_mod_cast this
  exact ⟨mono a, mono b⟩

theorem abs_le_mag {I : FIv} {x : ℝ} (h : I.Mem x) (ok : I.ok = true) :
    |x| ≤ ((mag I : ℚ) : ℝ) := by
  obtain ⟨l, r⟩ := mem_Icc h ok
  simp only [mag, Rat.cast_max, Rat.cast_abs]
  exact abs_le_max_abs_abs l r

theorem abs_sub_le_rad {I : FIv} {x : ℝ} (h : I.Mem x) (ok : I.ok = true) :
    |x - ((qv (mid I) : ℚ) : ℝ)| ≤ ((rad I : ℚ) : ℝ) := by
  obtain ⟨l, r⟩ := mem_Icc h ok
  simp only [rad, Rat.cast_max, Rat.cast_sub]
  rw [abs_le]
  constructor
  · have := le_max_right ((qv I.hi : ℝ) - (qv (mid I) : ℝ)) ((qv (mid I) : ℝ) - (qv I.lo : ℝ))
    linarith
  · have := le_max_left ((qv I.hi : ℝ) - (qv (mid I) : ℝ)) ((qv (mid I) : ℝ) - (qv I.lo : ℝ))
    linarith

theorem mag_nonneg (I : FIv) : 0 ≤ mag I := le_max_of_le_left (abs_nonneg _)

theorem rad_nonneg {I : FIv} {x : ℝ} (h : I.Mem x) (ok : I.ok = true) :
    0 ≤ ((rad I : ℚ) : ℝ) := (abs_nonneg _).trans (abs_sub_le_rad h ok)

/-! ## The centred enclosure -/

/-- Bound of `|∂_u p − 7 κ R⁶|` on the box, times the radius in `u`. -/
def slope (B : Box) (g : FIv) (κ : ℚ) : ℚ :=
  max |qv g.lo - 7 * κ * (qv B.u.hi + 29 / 32) ^ 6| |qv g.hi - 7 * κ * (qv B.u.lo + 29 / 32) ^ 6| *
    rad B.u

/-- Contribution of the other three variables to the radius of the centred enclosure. -/
def tail (B : Box) (p : SP) : ℚ :=
  mag (polyBox B (dZ p)) * rad B.z + mag (polyBox B (dC p)) * rad B.c +
    mag (polyBox B (dS p)) * rad B.s

/-- Validity flags of the five interval evaluations for one polynomial. -/
def flags (B : Box) (p : SP) : Bool :=
  (polyBox (ptBox B) p).ok && (polyBox B (dU p)).ok && (polyBox B (dZ p)).ok &&
    (polyBox B (dC p)).ok && (polyBox B (dS p)).ok

/-- **Sanity**: without the comparison term the slope is the magnitude times the radius. -/
theorem slope_zero (B : Box) (g : FIv) : slope B g 0 = mag g * rad B.u := by
  simp [slope, mag]

/-- The value at the midpoint lies in the interval evaluation on the box of midpoints. -/
theorem mem_midpoint (B : Box) (p : SP) :
    (polyBox (ptBox B) p).Mem (evR (qv (mid B.u) : ℚ) (qv (mid B.z) : ℚ) (qv (mid B.c) : ℚ)
      (qv (mid B.s) : ℚ) p) := by
  simp only [← fxVal_eq]
  exact polyBox_mem ⟨mem_pt _, mem_pt _, mem_pt _, mem_pt _⟩ p

/-- **Centred enclosure.** On a box, `evR p − κ (u + R₀)⁷` differs from its value at the midpoint
by at most `slope + tail`. -/
theorem centred (B : Box) (p : SP) (κ : ℚ) {u z c s : ℝ} (hm : B.Mem u z c s)
    (oku : B.u.ok = true) (okz : B.z.ok = true) (okc : B.c.ok = true) (oks : B.s.ok = true)
    (fl : flags B p = true) (hκ : 0 ≤ κ) (hR : 0 ≤ qv B.u.lo + 29 / 32) :
    |(evR u z c s p - κ * (u + dkR0) ^ 7) -
      (evR (qv (mid B.u) : ℚ) (qv (mid B.z) : ℚ) (qv (mid B.c) : ℚ) (qv (mid B.s) : ℚ) p -
        κ * ((qv (mid B.u) : ℚ) + dkR0) ^ 7)| ≤
      ((slope B (polyBox B (dU p)) κ + tail B p : ℚ) : ℝ) := by
  simp only [flags, Bool.and_eq_true] at fl
  obtain ⟨⟨⟨⟨-, fu⟩, fz⟩, fc⟩, fs⟩ := fl
  obtain ⟨mu, mz, mc, ms⟩ := hm
  have box : ∀ u' ∈ Set.Icc ((qv B.u.lo : ℚ) : ℝ) (qv B.u.hi : ℚ),
      ∀ z' ∈ Set.Icc ((qv B.z.lo : ℚ) : ℝ) (qv B.z.hi : ℚ),
      ∀ c' ∈ Set.Icc ((qv B.c.lo : ℚ) : ℝ) (qv B.c.hi : ℚ),
      ∀ s' ∈ Set.Icc ((qv B.s.lo : ℚ) : ℝ) (qv B.s.hi : ℚ), B.Mem u' z' c' s' := by
    intro u' hu' z' hz' c' hc' s' hs'
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩ <;> simpa [fxVal_eq]
  have hR' : (0 : ℝ) ≤ (qv B.u.lo : ℚ) + 29 / 32 := by
    have h := (Rat.cast_nonneg (K := ℝ)).mpr hR
    push_cast at h
    exact h
  have hκ' : (0 : ℝ) ≤ (κ : ℝ) := by exact_mod_cast hκ
  have mv := mean_value p (fun x => (κ : ℝ) * (x + dkR0) ^ 7)
    (fun x => 7 * (κ : ℝ) * (x + dkR0) ^ 6)
    (Au := ((max |qv (polyBox B (dU p)).lo - 7 * κ * (qv B.u.hi + 29 / 32) ^ 6|
      |qv (polyBox B (dU p)).hi - 7 * κ * (qv B.u.lo + 29 / 32) ^ 6| : ℚ) : ℝ))
    (Az := ((mag (polyBox B (dZ p)) : ℚ) : ℝ)) (Ac := ((mag (polyBox B (dC p)) : ℚ) : ℝ))
    (As := ((mag (polyBox B (dS p)) : ℚ) : ℝ))
    (mem_Icc mu oku) (mem_Icc mz okz) (mem_Icc mc okc) (mem_Icc ms oks)
    (mid_mem_Icc mu oku) (mid_mem_Icc mz okz) (mid_mem_Icc mc okc) (mid_mem_Icc ms oks)
    (fun x => by
      have h := (((hasDerivAt_id' x).add_const dkR0).pow 7).const_mul (κ : ℝ)
      convert h using 1
      norm_num
      ring)
    (fun u' hu' z' hz' c' hc' s' hs' => by
      obtain ⟨gl, gh⟩ := mem_Icc (polyBox_mem (box u' hu' z' hz' c' hc' s' hs') (dU p)) fu
      have lo6 : ((qv B.u.lo : ℚ) + 29 / 32 : ℝ) ^ 6 ≤ (u' + dkR0) ^ 6 :=
        pow_le_pow_left₀ hR' (by unfold dkR0; linarith [hu'.1]) 6
      have hi6 : (u' + dkR0) ^ 6 ≤ ((qv B.u.hi : ℚ) + 29 / 32 : ℝ) ^ 6 :=
        pow_le_pow_left₀ (by unfold dkR0; linarith [hu'.1]) (by unfold dkR0; linarith [hu'.2]) 6
      simp only [Rat.cast_max, Rat.cast_abs, Rat.cast_sub, Rat.cast_mul, Rat.cast_pow,
        Rat.cast_add, Rat.cast_div, Rat.cast_ofNat]
      apply abs_le_max_abs_abs
      · nlinarith [mul_le_mul_of_nonneg_left hi6 hκ']
      · nlinarith [mul_le_mul_of_nonneg_left lo6 hκ'])
    (fun u' hu' z' hz' c' hc' s' hs' =>
      abs_le_mag (polyBox_mem (box u' hu' z' hz' c' hc' s' hs') (dZ p)) fz)
    (fun u' hu' z' hz' c' hc' s' hs' =>
      abs_le_mag (polyBox_mem (box u' hu' z' hz' c' hc' s' hs') (dC p)) fc)
    (fun u' hu' z' hz' c' hc' s' hs' =>
      abs_le_mag (polyBox_mem (box u' hu' z' hz' c' hc' s' hs') (dS p)) fs)
  refine mv.trans ?_
  have ru := abs_sub_le_rad mu oku
  have rz := abs_sub_le_rad mz okz
  have rc := abs_sub_le_rad mc okc
  have rs := abs_sub_le_rad ms oks
  have nu : (0 : ℝ) ≤ ((max |qv (polyBox B (dU p)).lo - 7 * κ * (qv B.u.hi + 29 / 32) ^ 6|
      |qv (polyBox B (dU p)).hi - 7 * κ * (qv B.u.lo + 29 / 32) ^ 6| : ℚ) : ℝ) := by
    exact_mod_cast le_max_of_le_left (abs_nonneg _)
  have nz : (0 : ℝ) ≤ ((mag (polyBox B (dZ p)) : ℚ) : ℝ) := by exact_mod_cast mag_nonneg _
  have nc : (0 : ℝ) ≤ ((mag (polyBox B (dC p)) : ℚ) : ℝ) := by exact_mod_cast mag_nonneg _
  have ns : (0 : ℝ) ≤ ((mag (polyBox B (dS p)) : ℚ) : ℝ) := by exact_mod_cast mag_nonneg _
  simp only [slope, tail, Rat.cast_add, Rat.cast_mul]
  linarith [mul_le_mul_of_nonneg_left ru nu, mul_le_mul_of_nonneg_left rz nz,
    mul_le_mul_of_nonneg_left rc nc, mul_le_mul_of_nonneg_left rs ns]

/-! ## The Boolean check on a box -/

/-- Radius of the centred enclosure of a polynomial. -/
def radius (B : Box) (p : SP) : ℚ := slope B (polyBox B (dU p)) 0 + tail B p

/-- Centred lower bound of the toroidal denominator on the box. -/
def lowerD (B : Box) : ℚ := qv (polyBox (ptBox B) dD).lo - radius B dD

/-- Centred bound of the absolute value of a polynomial on the box. -/
def upperAbs (B : Box) (p : SP) : ℚ := mag (polyBox (ptBox B) p) + radius B p

/-- **The check on one box**: validity of all enclosures, positive radius, the comparisons
`b₀ R⁷ ≤ D ≤ c₁ R⁷` in centred form, and `n_R² + n_z² ≤ M² D²`. -/
def good (b₀ c₁ M : ℚ) (B : Box) : Bool :=
  B.u.ok && B.z.ok && B.c.ok && B.s.ok && flags B dD && flags B dnR && flags B dnZ &&
    leQ 0 (qv B.u.lo + 29 / 32) &&
    leQ (b₀ * (qv (mid B.u) + 29 / 32) ^ 7 + (slope B (polyBox B (dU dD)) b₀ + tail B dD))
      (qv (polyBox (ptBox B) dD).lo) &&
    leQ (qv (polyBox (ptBox B) dD).hi + (slope B (polyBox B (dU dD)) c₁ + tail B dD))
      (c₁ * (qv (mid B.u) + 29 / 32) ^ 7) &&
    leQ 0 (lowerD B) &&
    leQ (upperAbs B dnR ^ 2 + upperAbs B dnZ ^ 2) (M ^ 2 * lowerD B ^ 2)

/-- Centred bound of the absolute value of a polynomial at the points of a box. -/
theorem abs_le_upperAbs (B : Box) (p : SP) {u z c s : ℝ} (hm : B.Mem u z c s)
    (oku : B.u.ok = true) (okz : B.z.ok = true) (okc : B.c.ok = true) (oks : B.s.ok = true)
    (fl : flags B p = true) (hR : 0 ≤ qv B.u.lo + 29 / 32) :
    |evR u z c s p| ≤ ((upperAbs B p : ℚ) : ℝ) := by
  have cen := centred B p 0 hm oku okz okc oks fl le_rfl hR
  have fl' := fl
  simp only [flags, Bool.and_eq_true] at fl'
  have val := abs_le_mag (mem_midpoint B p) fl'.1.1.1.1
  simp only [Rat.cast_zero, zero_mul, sub_zero] at cen
  simp only [upperAbs, radius, Rat.cast_add]
  have tri := abs_sub_abs_le_abs_sub (evR u z c s p)
    (evR (qv (mid B.u) : ℚ) (qv (mid B.z) : ℚ) (qv (mid B.c) : ℚ) (qv (mid B.s) : ℚ) p)
  push_cast at cen
  linarith

/-- **Soundness of the check on a box.** -/
theorem good_sound {b₀ c₁ M : ℚ} (hb : 0 ≤ b₀) (hc : 0 ≤ c₁) {B : Box}
    (h : good b₀ c₁ M B = true) {u z c s : ℝ} (hm : B.Mem u z c s) :
    (b₀ : ℝ) * (u + dkR0) ^ 7 ≤ evR u z c s dD ∧ evR u z c s dD ≤ (c₁ : ℝ) * (u + dkR0) ^ 7 ∧
      evR u z c s dnR ^ 2 + evR u z c s dnZ ^ 2 ≤ (M : ℝ) ^ 2 * evR u z c s dD ^ 2 := by
  simp only [good, Bool.and_eq_true, leQ_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨oku, okz⟩, okc⟩, oks⟩, fD⟩, fR⟩, fZ⟩, hR⟩, lo⟩, hi⟩, pos⟩, sp⟩ := h
  have fD' := fD
  simp only [flags, Bool.and_eq_true] at fD'
  obtain ⟨ml, mh⟩ := mem_Icc (mem_midpoint B dD) fD'.1.1.1.1
  have lo' := (Rat.cast_le (K := ℝ)).mpr lo
  have hi' := (Rat.cast_le (K := ℝ)).mpr hi
  have pos' := (Rat.cast_le (K := ℝ)).mpr pos
  have sp' := (Rat.cast_le (K := ℝ)).mpr sp
  have cb := abs_le.mp (centred B dD b₀ hm oku okz okc oks fD hb hR)
  have cc := abs_le.mp (centred B dD c₁ hm oku okz okc oks fD hc hR)
  have c0 := abs_le.mp (centred B dD 0 hm oku okz okc oks fD le_rfl hR)
  have aR := abs_le_upperAbs B dnR hm oku okz okc oks fR hR
  have aZ := abs_le_upperAbs B dnZ hm oku okz okc oks fZ hR
  simp only [lowerD, radius] at pos' sp'
  push_cast at lo' hi' pos' sp' cb cc c0
  simp only [dkR0] at cb cc ⊢
  simp only [zero_mul, sub_zero] at c0
  refine ⟨by linarith [cb.1], by linarith [cc.2], ?_⟩
  have dl : (qv (polyBox (ptBox B) dD).lo : ℝ) -
      ((slope B (polyBox B (dU dD)) 0 : ℝ) + (tail B dD : ℝ)) ≤ evR u z c s dD := by
    linarith [c0.1]
  have sR : evR u z c s dnR ^ 2 ≤ (upperAbs B dnR : ℝ) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) aR 2
  have sZ : evR u z c s dnZ ^ 2 ≤ (upperAbs B dnZ : ℝ) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) aZ 2
  have sD := pow_le_pow_left₀ pos' dl 2
  nlinarith [mul_le_mul_of_nonneg_left sD (sq_nonneg (M : ℝ))]

end PlasmaLean.Design.DommaschkRegionEnclosure
