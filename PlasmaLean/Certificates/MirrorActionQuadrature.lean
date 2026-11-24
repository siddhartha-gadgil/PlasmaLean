/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import PlasmaLean.Certificates.KernelFact
public import PlasmaLean.Theory.Kinetic.MirrorHeightAction

/-!
# Directed quadrature certificates for the clipped mirror action

Each panel stores a one-sided bound on the density (scale 2²⁰), a one-sided
bound on max(2(h−B),0) (scale 2²⁶), and a square-root witness (scale 2²⁰).
Squaring the witness checks the root even on a turning panel. Slabs contain
48 panels of width 1 / 3072, packed least significant panel first.
-/

@[expose] public section
namespace PlasmaLean.Certificates.MirrorActionQuadrature

open Set MeasureTheory

/-- Directed bound on the exact quantity `x` by the proposed number `y`. -/
def Directed (upper : Bool) (x y : ℝ) : Prop := if upper then x ≤ y else y ≤ x

/-- Density column of the least significant panel. -/
def density (p : ℕ) : ℕ := p % 16777216

/-- Clipped squared parallel-speed column. -/
def speedSq (p : ℕ) : ℕ := (p >>> 24) % 16777216

/-- Proposed square root in units of 2⁻²⁰. -/
def speed (p : ℕ) : ℕ := (p >>> 48) % 16777216

/-- Integer comparisons suffice since the square-root and squared-speed scales
differ by the integer factor 2¹⁴ after squaring. -/
def rootTest (upper : Bool) (p : ℕ) : Bool :=
  if upper then (speedSq p * 16384).ble (speed p ^ 2)
  else (speed p ^ 2).ble (speedSq p * 16384)

/-- Check the root of every panel, charge its weighted mass, and reject surplus digits. -/
def read (upper : Bool) : ℕ → ℕ → Bool × ℕ
  | 0, p => (p == 0, 0)
  | n + 1, p =>
    let rest := read upper n (p >>> 72)
    (rootTest upper p && rest.1, density p * speed p + rest.2)

/-- Repeat each of eight coarse panel records six times for the common 48-panel
format. The kernel checks the expanded rectangle weights in exactly the same units. -/
def repeatSix : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, p =>
    let digit := p % 2 ^ 72
    -- Sum of the six place values 2^(72k), k = 0,...,5.
    let copies :=
      0x1000000000000000001000000000000000001000000000000000001000000000000000001000000000000000001
    digit * copies + ((repeatSix n (p >>> 72)) <<< 432)

/-- A root exactly at the turning threshold contributes zero. -/
theorem zero_panel : read true 1 0 = (true, 0) := rfl

/-- A zero upper root witness for a strictly positive squared speed is rejected. -/
theorem reject_bad_upper_root : (read true 1 (2 ^ 24)).1 = false := rfl

/-- Kernel proof for one 1 / 64-radian slab. -/
structure Block (upper : Bool) where
  packed : ℕ
  mass : ℕ
  checked : read upper 48 packed = (true, mass)

/-- One physical input panel. The density and the clipped squared speed are
bounded separately; the weighted integrand is constructed by the soundness proof. -/
def Cell (upper : Bool) (w f : ℝ → ℝ) (h a : ℝ) (p : ℕ) : Prop :=
  ∀ t ∈ Icc a (a + 1 / 3072),
    Directed upper (w t) (density p / 1048576) ∧
    Directed upper (max (2 * (h - f t)) 0) (speedSq p / 67108864)

/-- Successive primitive enclosures, with adjacent geometric-angle intervals. -/
def Cells (upper : Bool) (w f : ℝ → ℝ) (h : ℝ) : ℝ → ℕ → ℕ → Prop
  | _, 0, _ => True
  | a, n + 1, p => Cell upper w f h a p ∧ Cells upper w f h (a + 1 / 3072) n (p >>> 72)

/-- Physical interface of a packet, from its left mirror bracket to its right bracket. -/
def Covers (upper : Bool) (w f : ℝ → ℝ) (h : ℝ) : ℝ → List (Block upper) → Prop
  | _, [] => True
  | a, b :: bs => Cells upper w f h a 48 b.packed ∧ Covers upper w f h (a + 1 / 64) bs

/-- Total scaled rectangle mass of the packet. The proof attached to each block
guarantees that its stored mass is its checked dot product. -/
def total {upper : Bool} (bs : List (Block upper)) : ℕ := (bs.map Block.mass).sum

/-- Length plus strict signed action comparison, checked wholly in natural arithmetic.
The steps per radian and the two 2²⁰ density / speed denominators account for the scale. -/
structure Packet (upper : Bool) (bs : List (Block upper)) (left right num den : ℕ) : Prop where
  len : bs.length = left + right
  sign : if upper then total bs * den < num * 3072 * 1099511627776
    else num * 3072 * 1099511627776 < total bs * den

private theorem directed_add {u : Bool} {x y X Y : ℝ} (hx : Directed u x X)
    (hy : Directed u y Y) : Directed u (x + y) (X + Y) := by
  cases u <;> exact add_le_add hx hy

/-- Directed square-root and product proof for one encoded panel. -/
theorem density_bound (u : Bool) {p : ℕ} {w z : ℝ} (hw : 0 ≤ w)
    (ht : rootTest u p = true) (hd : Directed u w (density p / 1048576))
    (hg : Directed u (max z 0) (speedSq p / 67108864)) :
    Directed u (w * Real.sqrt z) ((density p * speed p : ℕ) / (1099511627776 : ℝ)) := by
  have hwit : 0 ≤ (speed p : ℝ) / 1048576 := by positivity
  have hfactor : ((density p * speed p : ℕ) : ℝ) / 1099511627776 =
      (density p / 1048576 : ℝ) * (speed p / 1048576 : ℝ) := by push_cast; ring
  rw [hfactor]
  cases u
  · change (speed p ^ 2).ble (speedSq p * 16384) = true at ht
    have hi := Nat.le_of_ble_eq_true ht
    have hs : (speed p : ℝ)^2 ≤ speedSq p * 16384 := by exact_mod_cast hi
    change (speedSq p : ℝ) / 67108864 ≤ max z 0 at hg
    have hr : (speed p : ℝ) / 1048576 ≤ Real.sqrt z :=
      (sq_le_sq₀ hwit (Real.sqrt_nonneg z)).mp (by nlinarith only [hs,hg,Real.sq_sqrt' (x := z)])
    exact mul_le_mul hd hr hwit hw
  · change (speedSq p * 16384).ble (speed p ^ 2) = true at ht
    have hi := Nat.le_of_ble_eq_true ht
    have hs : (speedSq p : ℝ) * 16384 ≤ (speed p : ℝ)^2 := by exact_mod_cast hi
    change max z 0 ≤ (speedSq p : ℝ) / 67108864 at hg
    have hr : Real.sqrt z ≤ (speed p : ℝ) / 1048576 :=
      (sq_le_sq₀ (Real.sqrt_nonneg z) hwit).mp (by nlinarith only [hs,hg,Real.sq_sqrt' (x := z)])
    exact mul_le_mul hd hr (Real.sqrt_nonneg _) (by positivity)

private theorem integral_cell {u : Bool} {g : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hi : IntervalIntegrable g volume a b) (h : ∀ x ∈ Icc a b, Directed u (g x) c) :
    Directed u (∫ x in a..b, g x) ((b-a)*c) := by
  have hc : IntervalIntegrable (fun _ : ℝ => c) volume a b := intervalIntegrable_const
  have e : (∫ _ in a..b, c) = (b-a)*c := by simp [smul_eq_mul]
  rw [← e]
  cases u
  · exact intervalIntegral.integral_mono_on hab hc hi h
  · exact intervalIntegral.integral_mono_on hab hi hc h

private theorem cells_sound {u : Bool} {w f : ℝ → ℝ} {h : ℝ} (n p : ℕ) (a : ℝ)
    (C : Cells u w f h a n p) (hr : (read u n p).1 = true)
    (hn : ∀ t ∈ Icc a (a + n / 3072), 0 ≤ w t)
    (hi : IntervalIntegrable (fun t ↦ w t * Real.sqrt (2 * (h - f t))) volume a (a + n / 3072)) :
    Directed u (Kinetic.MirrorHeightAction.action f w a (a + n / 3072) h)
      ((read u n p).2 / (3072 * 1099511627776 : ℝ)) := by
  induction n generalizing a p with
  | zero => cases u <;> simp [Directed, read, Kinetic.MirrorHeightAction.action]
  | succ n ih =>
    obtain ⟨hp,ht⟩ := C
    change rootTest u p && (read u n (p >>> 72)).1 = true at hr
    simp only [Bool.and_eq_true] at hr
    obtain ⟨hok,rest⟩ := hr
    let b := a + 1 / 3072
    let c : ℝ := a + (n + 1 : ℕ) / 3072
    have hab : a ≤ b := by dsimp [b]; linarith
    have hbc : b ≤ c := by dsimp [b,c]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
    have ec : b + n / 3072 = c := by dsimp [b,c]; push_cast; ring
    have sub₁ : Icc a b ⊆ Icc a c := Icc_subset_Icc_right hbc
    have sub₂ : Icc b c ⊆ Icc a c := Icc_subset_Icc_left hab
    have restrict {x y : ℝ} (hxy : x ≤ y) (sub : Icc x y ⊆ Icc a c) :
        IntervalIntegrable (fun t ↦ w t * Real.sqrt (2 * (h - f t))) volume x y :=
      hi.mono_set (by rw [uIcc_of_le hxy, uIcc_of_le (hab.trans hbc)]; exact sub)
    have one := integral_cell hab (restrict hab sub₁) (fun x hx ↦
      density_bound u (hn x (sub₁ hx)) hok (hp x hx).1 (hp x hx).2)
    have tail := ih (p >>> 72) b ht rest (fun t hx ↦ hn t (sub₂ (ec ▸ hx)))
      (ec.symm ▸ restrict hbc sub₂)
    rw [ec, Kinetic.MirrorHeightAction.action] at tail
    have both := directed_add one tail
    rw [intervalIntegral.integral_add_adjacent_intervals
      (restrict hab sub₁) (restrict hbc sub₂)] at both
    change Directed u (∫ t in a..c, w t * Real.sqrt (2 * (h - f t))) _
    convert both using 1
    change ((density p * speed p + (read u n (p >>> 72)).2 : ℕ) : ℝ) / _ = _
    dsimp [b]; push_cast; ring

private theorem covers_sound {u : Bool} {f w : ℝ → ℝ} {h : ℝ} (bs : List (Block u)) (a : ℝ)
    (C : Covers u w f h a bs) (hn : ∀ t ∈ Icc a (a + bs.length / 64), 0 ≤ w t)
    (hi : IntervalIntegrable (fun t ↦ w t * Real.sqrt (2 * (h - f t))) volume
      a (a + bs.length / 64)) :
    Directed u (Kinetic.MirrorHeightAction.action f w a (a + bs.length / 64) h)
      (total bs / (3072 * 1099511627776 : ℝ)) := by
  induction bs generalizing a with
  | nil => cases u <;> simp [Directed, total, Kinetic.MirrorHeightAction.action]
  | cons row bs ih =>
    obtain ⟨head,tail⟩ := C
    let b := a + 1 / 64
    let c : ℝ := a + ((row :: bs).length : ℕ) / 64
    have hab : a ≤ b := by dsimp [b]; linarith
    have hbc : b ≤ c := by dsimp [b,c]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) bs.length]
    have eb : a + (48 : ℕ) / 3072 = b := by dsimp [b]; norm_num
    have ec : b + bs.length / 64 = c := by dsimp [b,c]; push_cast; ring
    have sub₁ : Icc a b ⊆ Icc a c := Icc_subset_Icc_right hbc
    have sub₂ : Icc b c ⊆ Icc a c := Icc_subset_Icc_left hab
    have restrict {x y : ℝ} (hxy : x ≤ y) (sub : Icc x y ⊆ Icc a c) :
        IntervalIntegrable (fun t ↦ w t * Real.sqrt (2 * (h - f t))) volume x y :=
      hi.mono_set (by rw [uIcc_of_le hxy, uIcc_of_le (hab.trans hbc)]; exact sub)
    have one := cells_sound 48 row.packed a head (congrArg Prod.fst row.checked)
      (fun t hx ↦ hn t (sub₁ (eb ▸ hx))) (eb.symm ▸ restrict hab sub₁)
    have rest := ih b tail (fun t hx ↦ hn t (sub₂ (ec ▸ hx))) (ec.symm ▸ restrict hbc sub₂)
    rw [eb, row.checked, Kinetic.MirrorHeightAction.action] at one
    rw [ec, Kinetic.MirrorHeightAction.action] at rest
    have both := directed_add one rest
    rw [intervalIntegral.integral_add_adjacent_intervals
      (restrict hab sub₁) (restrict hbc sub₂)] at both
    change Directed u (∫ t in a..c, w t * Real.sqrt (2 * (h - f t))) _
    convert both using 1
    simp [total, add_div]

/-- An exact packed quadrature certificate proves its strict action comparison
on any continuous trace realizing the primitive enclosures on the full bracket. -/
theorem Packet.sound {u : Bool} {bs : List (Block u)} {l r num den : ℕ}
    (P : Packet u bs l r num den) {w f : ℝ → ℝ} {h : ℝ} (hd : 0 < den)
    (C : Covers u w f h (-(l : ℝ) / 64) bs)
    (hn : ∀ t ∈ Icc (-(l : ℝ) / 64) (r / 64), 0 ≤ w t)
    (cf : ContinuousOn f (Icc (-(l : ℝ) / 64) (r / 64)))
    (cw : ContinuousOn w (Icc (-(l : ℝ) / 64) (r / 64))) :
    if u then Kinetic.MirrorHeightAction.action f w (-(l : ℝ) / 64) (r / 64) h < num / den
    else num / den < Kinetic.MirrorHeightAction.action f w (-(l : ℝ) / 64) (r / 64) h := by
  have er : -(l : ℝ) / 64 + bs.length / 64 = r / 64 := by rw [P.len]; push_cast; ring
  have hab : -(l : ℝ) / 64 ≤ r / 64 := by
    linarith [Nat.cast_nonneg (α := ℝ) l, Nat.cast_nonneg (α := ℝ) r]
  have hi : IntervalIntegrable (fun t ↦ w t * Real.sqrt (2 * (h - f t)))
      volume (-(l : ℝ) / 64) (r / 64) :=
    (cw.mul (continuousOn_const.mul (continuousOn_const.sub cf)).sqrt).intervalIntegrable_of_Icc hab
  have hb := covers_sound bs (-(l : ℝ) / 64) C (er.symm ▸ hn) (er.symm ▸ hi)
  rw [er] at hb
  have hd' : (0 : ℝ) < den := by exact_mod_cast hd
  have sign := P.sign
  cases u
  · apply lt_of_lt_of_le _ hb
    apply (div_lt_div_iff₀ hd' (by norm_num : (0 : ℝ)<3072 * 1099511627776)).mpr
    change num * 3072 * 1099511627776 < total bs * den at sign
    exact_mod_cast (by simpa [Nat.mul_assoc] using sign :
      num * (3072 * 1099511627776) < total bs * den)
  · apply lt_of_le_of_lt hb
    apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ)<3072 * 1099511627776) hd').mpr
    change total bs * den < num * 3072 * 1099511627776 at sign
    exact_mod_cast (by simpa [Nat.mul_assoc] using sign :
      total bs * den < num * (3072 * 1099511627776))

end PlasmaLean.Certificates.MirrorActionQuadrature
