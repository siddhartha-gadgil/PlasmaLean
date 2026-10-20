/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevBallooningDefs
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Ballooning certificate: soundness of balls, trees, the Pólya test and the chord bound

Real semantics and soundness for the computational layer `SolovevBallooningDefs`:

* `Bl.Mem`: `|2³² x − m| ≤ r` (if `ok`); every ball operation is sound (`Bl.mem_add`, …,
  `Bl.mem_inv`, `Bl.mem_sqrt`).
* `Tm.eval`, `Tm.deriv`, `Tm.deriv2`: value, first and second derivative of a tree along a
  curve of variable values; chain rules `Tm.hasDerivAt`, `Tm.hasDerivAt_deriv`; ball soundness
  `Tm.ieval_mem`, `Tm.idual_mem`, `Tm.ihd_mem`; the symbolic derivative `Tm.eval_diff`.
* `zpoly_pos_of_polyaOK`: the Pólya test proves positivity on `[0, ∞)`.
* `chord_lower`: a `C²` function with `|g''| ≤ M` on `[a, b]` lies above its chord minus
  `M (x − a)(b − x)/2`.
-/

public section
noncomputable section

namespace PlasmaLean.Design.SolovevBallooning

open Real Set

/-! ## Explicit integer operations -/

/-- `Int.mul` is multiplication. -/
@[simp] theorem int_mul_eq (a b : ℤ) : Int.mul a b = a * b := rfl
/-- `Int.add` is addition. -/ @[simp] theorem int_add_eq (a b : ℤ) : Int.add a b = a + b := rfl
/-- `Int.sub` is subtraction. -/ @[simp] theorem int_sub_eq (a b : ℤ) : Int.sub a b = a - b := rfl
/-- `Int.neg` is negation. -/ @[simp] theorem int_neg_eq (a : ℤ) : Int.neg a = -a := rfl
/-- `Int.ediv` is division. -/ @[simp] theorem int_ediv_eq (a b : ℤ) : Int.ediv a b = a / b := rfl
/-- `Nat.mul` is multiplication. -/
@[simp] theorem nat_mul_eq (a b : ℕ) : Nat.mul a b = a * b := rfl
/-- `Nat.add` is addition. -/ @[simp] theorem nat_add_eq (a b : ℕ) : Nat.add a b = a + b := rfl
/-- `Nat.div` is division. -/ @[simp] theorem nat_div_eq (a b : ℕ) : Nat.div a b = a / b := rfl

/-- The fixed-point scale as a real number. -/
@[expose] def Sc : ℝ := 4294967296

/-- The fixed-point scale is positive. -/
theorem Sc_pos : (0 : ℝ) < Sc := by norm_num [Sc]

/-- Floor division bounds: `a/d − 1 < ⌊a/d⌋ ≤ a/d` for `d > 0`. -/
theorem ediv_bounds (a d : ℤ) (hd : 0 < d) :
    ((a / d : ℤ) : ℝ) ≤ (a : ℝ) / d ∧ (a : ℝ) / d < ((a / d : ℤ) : ℝ) + 1 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 := Int.ediv_mul_le a hd.ne'
  have h2 := Int.lt_ediv_add_one_mul_self a hd
  constructor
  · rw [le_div_iff₀ hd']; exact_mod_cast h1
  · rw [div_lt_iff₀ hd']; exact_mod_cast h2

/-- Natural division: `n/d ≤ ⌊n/d⌋ + 1`. -/
theorem nat_div_bound (n d : ℕ) (hd : 0 < d) : (n : ℝ) / d ≤ ((n / d : ℕ) : ℝ) + 1 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_le_iff₀ hd']
  have := Nat.lt_div_mul_add (a := n) hd
  have : (n : ℝ) < (n / d : ℕ) * d + d := by exact_mod_cast this
  nlinarith

/-! ## Balls -/

namespace Bl

/-- Membership: if the ball is valid then `|2³² x − m| ≤ r`. -/
@[expose] def Mem (a : Bl) (x : ℝ) : Prop := a.ok = true → |Sc * x - a.m| ≤ a.r

/-- Soundness of integer balls. -/
theorem mem_ofInt (n : ℤ) : (ofInt n).Mem (n : ℝ) := by
  intro _
  simp only [ofInt, int_mul_eq, Nat.cast_zero]; push_cast
  rw [show Sc * (n : ℝ) - (n : ℝ) * 4294967296 = 0 by unfold Sc; ring]; simp

/-- Soundness of rational balls (vacuous for `q ≤ 0`). -/
theorem mem_ofFrac (p q : ℤ) : (ofFrac p q).Mem ((p : ℝ) / q) := by
  intro hok
  simp only [ofFrac, decide_eq_true_eq] at hok
  simp only [ofFrac, int_mul_eq, int_ediv_eq, Nat.cast_one]
  obtain ⟨h1, h2⟩ := ediv_bounds (p * 4294967296) q hok
  have hq : (0 : ℝ) < q := by exact_mod_cast hok
  have e : ((p * 4294967296 : ℤ) : ℝ) / q = Sc * (p / q) := by
    push_cast; unfold Sc; field_simp
  rw [e] at h1 h2
  rw [abs_le]; constructor <;> linarith

/-- The zero ball contains `0`. -/
theorem mem_zero : zero.Mem 0 := by intro _; simp [zero]

/-- Soundness of ball addition. -/
theorem mem_add {a b : Bl} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) : (a.add b).Mem (x + y) := by
  intro hok
  simp only [add, Bool.and_eq_true] at hok
  have h1 := hx hok.1; have h2 := hy hok.2
  simp only [add, int_add_eq, nat_add_eq]; push_cast
  rw [abs_le] at *; constructor <;> nlinarith

/-- Soundness of ball negation. -/
theorem mem_neg {a : Bl} {x : ℝ} (hx : a.Mem x) : a.neg.Mem (-x) := by
  intro hok
  have h1 := hx hok
  simp only [neg, int_neg_eq]; push_cast
  rw [abs_le] at *; constructor <;> nlinarith

/-- Soundness of ball subtraction. -/
theorem mem_sub {a b : Bl} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) : (a.sub b).Mem (x - y) := by
  intro hok
  simp only [sub, Bool.and_eq_true] at hok
  have h1 := hx hok.1; have h2 := hy hok.2
  simp only [sub, int_sub_eq, nat_add_eq]; push_cast
  rw [abs_le] at *; constructor <;> nlinarith

/-- Soundness of ball doubling. -/
theorem mem_dbl {a : Bl} {x : ℝ} (hx : a.Mem x) : a.dbl.Mem (2 * x) := by
  intro hok
  have h1 := hx hok
  simp only [dbl, int_add_eq, nat_add_eq]; push_cast
  rw [abs_le] at *; constructor <;> nlinarith

/-- Core estimate of the rounded product. -/
theorem prod_est {X Y : ℝ} {m1 m2 : ℤ} {r1 r2 : ℕ} (h1 : |X - m1| ≤ r1) (h2 : |Y - m2| ≤ r2) :
    |X * Y / Sc - ((m1 * m2 / 4294967296 : ℤ) : ℝ)| ≤
      (((m1.natAbs * r2 + r1 * m2.natAbs + r1 * r2) / 4294967296 + 2 : ℕ) : ℝ) := by
  have hS := Sc_pos
  set E : ℕ := m1.natAbs * r2 + r1 * m2.natAbs + r1 * r2 with hEdef
  set q : ℤ := m1 * m2 / 4294967296 with hq
  obtain ⟨e1, e2⟩ := ediv_bounds (m1 * m2) 4294967296 (by norm_num)
  rw [← hq] at e1 e2
  have e1' : (q : ℝ) ≤ (m1 : ℝ) * m2 / Sc := by simpa [Sc] using e1
  have e2' : (m1 : ℝ) * m2 / Sc < q + 1 := by simpa [Sc] using e2
  have hn : (E : ℝ) / Sc ≤ ((E / 4294967296 : ℕ) : ℝ) + 1 := by
    simpa [Sc] using nat_div_bound E 4294967296 (by norm_num)
  have hE : (E : ℝ) = |(m1 : ℝ)| * r2 + r1 * |(m2 : ℝ)| + r1 * r2 := by
    simp only [hEdef]; push_cast; rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
  have key : |X * Y - m1 * m2| ≤ (E : ℝ) := by
    rw [hE]
    have e : X * Y - m1 * m2 = m1 * (Y - m2) + m2 * (X - m1) + (X - m1) * (Y - m2) := by ring
    rw [e]
    calc |m1 * (Y - m2) + m2 * (X - m1) + (X - m1) * (Y - m2)|
        ≤ |(m1 : ℝ) * (Y - m2)| + |(m2 : ℝ) * (X - m1)| + |(X - m1) * (Y - m2)| :=
          abs_add_three _ _ _
      _ = |(m1 : ℝ)| * |Y - m2| + |(m2 : ℝ)| * |X - m1| + |X - m1| * |Y - m2| := by
          rw [abs_mul, abs_mul, abs_mul]
      _ ≤ |(m1 : ℝ)| * r2 + |(m2 : ℝ)| * r1 + r1 * r2 := by gcongr
      _ = _ := by ring
  obtain ⟨k1, k2⟩ := abs_le.mp key
  have d1 : (X * Y - m1 * m2) / Sc ≤ E / Sc := div_le_div_of_nonneg_right k2 hS.le
  have d0 : -(E : ℝ) / Sc ≤ (X * Y - m1 * m2) / Sc := div_le_div_of_nonneg_right k1 hS.le
  have split : X * Y / Sc - q = (X * Y - m1 * m2) / Sc + ((m1 : ℝ) * m2 / Sc - q) := by ring
  have hE0 : (0 : ℝ) ≤ E / Sc := by positivity
  rw [split, abs_le]
  push_cast
  constructor
  · rw [neg_div] at d0; linarith
  · linarith

/-- Soundness of the outward-rounded ball product. -/
theorem mem_mul {a b : Bl} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) : (a.mul b).Mem (x * y) := by
  intro hok
  simp only [mul, Bool.and_eq_true] at hok
  have h1 := hx hok.1; have h2 := hy hok.2
  have hS := Sc_pos
  have := prod_est h1 h2
  have e : Sc * (x * y) = Sc * x * (Sc * y) / Sc := by field_simp
  simp only [mul, int_mul_eq, int_ediv_eq, nat_add_eq, nat_mul_eq, nat_div_eq]
  rw [e]; exact this

/-- Soundness of the outward-rounded ball square. -/
theorem mem_sq {a : Bl} {x : ℝ} (hx : a.Mem x) : a.sq.Mem (x ^ 2) := by
  intro hok
  have h1 := hx hok
  have hS := Sc_pos
  have := prod_est h1 h1
  have e : Sc * x ^ 2 = Sc * x * (Sc * x) / Sc := by field_simp
  simp only [sq, int_mul_eq, int_ediv_eq, nat_add_eq, nat_mul_eq, nat_div_eq]
  rw [e]
  have e2 : a.m.natAbs * a.r + a.r * a.m.natAbs + a.r * a.r =
      (a.m.natAbs + a.m.natAbs) * a.r + a.r * a.r := by ring
  rw [e2] at this; exact this

/-- The ball of a scaled interval. -/
theorem mem_ofLoHi {l h : ℤ} {ok : Bool} {x : ℝ} (h1 : ok = true → (l : ℝ) ≤ Sc * x)
    (h2 : ok = true → Sc * x ≤ h) : (ofLoHi l h ok).Mem x := by
  intro hok
  have a1 := h1 hok; have a2 := h2 hok
  have hlh : l ≤ h := by exact_mod_cast a1.trans a2
  simp only [ofLoHi, int_add_eq, int_ediv_eq, int_sub_eq, nat_add_eq, nat_div_eq]
  obtain ⟨e1, e2⟩ := ediv_bounds (l + h) 2 (by norm_num)
  have hn : ((h - l).natAbs : ℝ) = h - l := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast sub_nonneg.mpr hlh)]
    push_cast; ring
  have hd := nat_div_bound (h - l).natAbs 2 (by norm_num)
  rw [hn] at hd
  push_cast at e1 e2 hd ⊢
  rw [abs_le]; constructor <;> linarith

/-- Scaled bounds from membership. -/
theorem Mem.lo_le {a : Bl} {x : ℝ} (h : a.Mem x) (hok : a.ok = true) : (a.lo : ℝ) ≤ Sc * x := by
  have := h hok; rw [abs_le] at this; simp only [lo, int_sub_eq]; push_cast; linarith

/-- Scaled upper bound from membership. -/
theorem Mem.le_hi {a : Bl} {x : ℝ} (h : a.Mem x) (hok : a.ok = true) : Sc * x ≤ a.hi := by
  have := h hok; rw [abs_le] at this; simp only [hi, int_add_eq]; push_cast; linarith

/-- Scaled bound on the absolute value from membership. -/
theorem Mem.abs_le_mag {a : Bl} {x : ℝ} (h : a.Mem x) (hok : a.ok = true) :
    Sc * |x| ≤ a.mag := by
  have := h hok
  have hS := Sc_pos
  simp only [mag, nat_add_eq]; push_cast
  rw [Nat.cast_natAbs, Int.cast_abs]
  calc Sc * |x| = |Sc * x| := by rw [abs_mul, abs_of_pos hS]
    _ ≤ |Sc * x - a.m| + |(a.m : ℝ)| := by
        have := abs_add_le (Sc * x - a.m) (a.m : ℝ); simpa using this
    _ ≤ _ := by linarith

/-- Soundness of the ball reciprocal (invalid unless the ball is strictly positive). -/
theorem mem_inv {a : Bl} {x : ℝ} (hx : a.Mem x) : a.inv.Mem x⁻¹ := by
  have hS := Sc_pos
  unfold inv
  apply mem_ofLoHi
  · intro hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    have a1 := hx.lo_le hok.1; have a2 := hx.le_hi hok.1
    have h0 : (0 : ℝ) < a.lo := by exact_mod_cast hok.2
    have hhi : (0 : ℤ) < a.hi := by exact_mod_cast (lt_of_lt_of_le h0 (a1.trans a2))
    have hhi' : (0 : ℝ) < a.hi := by exact_mod_cast hhi
    have hxpos : 0 < x := by
      have : 0 < Sc * x := lt_of_lt_of_le h0 a1
      exact pos_of_mul_pos_right this hS.le
    obtain ⟨l1, -⟩ := ediv_bounds 18446744073709551616 a.hi hhi
    simp only [int_ediv_eq]
    calc _ ≤ _ := l1
      _ ≤ (18446744073709551616 : ℝ) / (Sc * x) := by push_cast; gcongr
      _ = Sc * x⁻¹ := by unfold Sc; field_simp; norm_num
  · intro hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    have a1 := hx.lo_le hok.1
    have h0 : (0 : ℝ) < a.lo := by exact_mod_cast hok.2
    have hxpos : 0 < x := by
      have : 0 < Sc * x := lt_of_lt_of_le h0 a1
      exact pos_of_mul_pos_right this hS.le
    obtain ⟨-, l2⟩ := ediv_bounds 18446744073709551616 a.lo hok.2
    simp only [int_ediv_eq, int_add_eq]; push_cast at l2 ⊢
    calc Sc * x⁻¹ = (18446744073709551616 : ℝ) / (Sc * x) := by unfold Sc; field_simp; norm_num
      _ ≤ (18446744073709551616 : ℝ) / a.lo := by gcongr
      _ ≤ _ := l2.le

/-- Soundness of the checked ball square root (for every real `x`; `√x = 0` if `x < 0`). -/
theorem mem_sqrt {a : Bl} {x : ℝ} (hx : a.Mem x) : a.sqrt.Mem (√x) := by
  have hS := Sc_pos
  have hsq := Real.sqrt_nonneg x
  unfold sqrt
  apply mem_ofLoHi
  · intro hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    have a1 := hx.lo_le hok.1.1
    split_ifs with h
    · set q : ℤ := (isqrt (a.lo * 4294967296).toNat : ℤ)
      have hq0 : (0 : ℝ) ≤ q := by simp [q]
      have h' : (q : ℝ) * q ≤ a.lo * 4294967296 := by exact_mod_cast h
      have hle : ((q : ℝ) / Sc) ^ 2 ≤ x := by
        rw [div_pow, div_le_iff₀ (by positivity)]
        unfold Sc at a1 ⊢; nlinarith
      have := Real.le_sqrt_of_sq_le hle
      rw [div_le_iff₀ hS] at this
      linarith
    · simp only [Int.cast_zero]; positivity
  · intro hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    have a2 := hx.le_hi hok.1.1
    set q : ℤ := (isqrt (a.hi * 4294967296).toNat : ℤ) + 1
    have hq0 : (0 : ℝ) ≤ q := by simp only [q]; push_cast; positivity
    have h' : (a.hi : ℝ) * 4294967296 ≤ q * q := by exact_mod_cast hok.2
    have hle : x ≤ ((q : ℝ) / Sc) ^ 2 := by
      rw [div_pow, le_div_iff₀ (by positivity)]
      unfold Sc at a2 ⊢; nlinarith
    have := Real.sqrt_le_sqrt hle
    rw [Real.sqrt_sq (by positivity), le_div_iff₀ hS] at this
    linarith

/-- Membership transports along equality of the real number. -/
theorem mem_of_eq {a : Bl} {x y : ℝ} (h : a.Mem x) (e : x = y) : a.Mem y := e ▸ h

end Bl

/-! ## Real semantics of trees -/

namespace Tm

/-- Real value of a tree at the variable assignment `ρ`. -/
@[expose] def eval (ρ : ℕ → ℝ) : Tm → ℝ
  | c p q => (p : ℝ) / q
  | v i => ρ i
  | add a b => a.eval ρ + b.eval ρ
  | mul a b => a.eval ρ * b.eval ρ
  | neg a => -(a.eval ρ)
  | sq a => a.eval ρ ^ 2

/-- Forward-mode derivative of a tree, given the derivatives `ρ'` of the variables. -/
@[expose] def deriv (ρ ρ' : ℕ → ℝ) : Tm → ℝ
  | c _ _ => 0
  | v i => ρ' i
  | add a b => a.deriv ρ ρ' + b.deriv ρ ρ'
  | mul a b => a.deriv ρ ρ' * b.eval ρ + a.eval ρ * b.deriv ρ ρ'
  | neg a => -(a.deriv ρ ρ')
  | sq a => 2 * (a.eval ρ * a.deriv ρ ρ')

/-- Second derivative of a tree, given first and second derivatives of the variables. -/
@[expose] def deriv2 (ρ ρ' ρ'' : ℕ → ℝ) : Tm → ℝ
  | c _ _ => 0
  | v i => ρ'' i
  | add a b => a.deriv2 ρ ρ' ρ'' + b.deriv2 ρ ρ' ρ''
  | mul a b => a.deriv2 ρ ρ' ρ'' * b.eval ρ + 2 * (a.deriv ρ ρ' * b.deriv ρ ρ') +
      a.eval ρ * b.deriv2 ρ ρ' ρ''
  | neg a => -(a.deriv2 ρ ρ' ρ'')
  | sq a => 2 * (a.deriv ρ ρ' ^ 2 + a.eval ρ * a.deriv2 ρ ρ' ρ'')

/-- Value of a difference tree. -/
@[simp] theorem eval_sub (a b : Tm) (ρ : ℕ → ℝ) : (Tm.sub a b).eval ρ = a.eval ρ - b.eval ρ := by
  simp [Tm.sub, eval]; ring

/-- **Chain rule for trees.** -/
theorem hasDerivAt (e : Tm) {ρ ρ' : ℝ → ℕ → ℝ} {t : ℝ}
    (hρ : ∀ i, HasDerivAt (fun t => ρ t i) (ρ' t i) t) :
    HasDerivAt (fun t => e.eval (ρ t)) (e.deriv (ρ t) (ρ' t)) t := by
  induction e with
  | c p q => simpa [eval, deriv] using hasDerivAt_const t ((p : ℝ) / q)
  | v i => simpa [eval, deriv] using hρ i
  | add a b iha ihb => exact iha.add ihb
  | mul a b iha ihb => exact iha.mul ihb
  | neg a iha => exact iha.neg
  | sq a iha =>
    have := iha.pow 2
    simp only [eval, deriv]
    convert this using 1
    simp; ring

/-- **Second-order chain rule for trees.** -/
theorem hasDerivAt_deriv (e : Tm) {ρ ρ' ρ'' : ℝ → ℕ → ℝ} {t : ℝ}
    (hρ : ∀ i, HasDerivAt (fun t => ρ t i) (ρ' t i) t)
    (hρ' : ∀ i, HasDerivAt (fun t => ρ' t i) (ρ'' t i) t) :
    HasDerivAt (fun t => e.deriv (ρ t) (ρ' t)) (e.deriv2 (ρ t) (ρ' t) (ρ'' t)) t := by
  induction e with
  | c p q => simpa [deriv, deriv2] using hasDerivAt_const t (0 : ℝ)
  | v i => simpa [deriv, deriv2] using hρ' i
  | add a b iha ihb => exact iha.add ihb
  | mul a b iha ihb =>
    have h1 := (iha.mul (b.hasDerivAt hρ)).add ((a.hasDerivAt hρ).mul ihb)
    simp only [deriv, deriv2]
    convert h1 using 1; ring
  | neg a iha => exact iha.neg
  | sq a iha =>
    have h1 := ((a.hasDerivAt hρ).mul iha).const_mul 2
    simp only [deriv, deriv2]
    convert h1 using 1; ring

/-- Continuity of a tree along continuous variables. -/
theorem continuous_eval (e : Tm) {ρ : ℝ → ℕ → ℝ} (hρ : ∀ i, Continuous fun t => ρ t i) :
    Continuous fun t => e.eval (ρ t) := by
  induction e with
  | c p q => exact continuous_const
  | v i => exact hρ i
  | add a b iha ihb => exact iha.add ihb
  | mul a b iha ihb => exact iha.mul ihb
  | neg a iha => exact iha.neg
  | sq a iha => exact iha.pow 2

/-- The derivative is linear in the variable derivatives. -/
theorem deriv_smul (e : Tm) (ρ ρ' : ℕ → ℝ) (κ : ℝ) :
    e.deriv ρ (fun i => κ * ρ' i) = κ * e.deriv ρ ρ' := by
  induction e with
  | c p q => simp [deriv]
  | v i => simp [deriv]
  | add a b iha ihb => simp only [deriv, iha, ihb]; ring
  | mul a b iha ihb => simp only [deriv, iha, ihb]; ring
  | neg a iha => simp only [deriv, iha]; ring
  | sq a iha => simp only [deriv, iha]; ring

/-- The symbolic derivative evaluates to the forward derivative. -/
theorem eval_diff (dv : ℕ → Tm) (e : Tm) (ρ : ℕ → ℝ) :
    (diff dv e).eval ρ = e.deriv ρ (fun i => (dv i).eval ρ) := by
  induction e with
  | c p q => simp [diff, eval, deriv]
  | v i => simp [diff, deriv]
  | add a b iha ihb => simp only [diff, eval, deriv, iha, ihb]
  | mul a b iha ihb => simp only [diff, eval, deriv, iha, ihb]
  | neg a iha => simp only [diff, eval, deriv, iha]
  | sq a iha => simp only [diff, eval, deriv, iha]; push_cast; ring

/-- **Soundness of ball evaluation.** -/
theorem ieval_mem (e : Tm) {I : ℕ → Bl} {ρ : ℕ → ℝ} (hI : ∀ i, (I i).Mem (ρ i)) :
    (e.ieval I).Mem (e.eval ρ) := by
  induction e with
  | c p q => exact Bl.mem_ofFrac p q
  | v i => exact hI i
  | add a b iha ihb => exact Bl.mem_add iha ihb
  | mul a b iha ihb => exact Bl.mem_mul iha ihb
  | neg a iha => exact Bl.mem_neg iha
  | sq a iha => exact Bl.mem_sq iha

/-- **Soundness of dual evaluation**: value and derivative balls. -/
theorem idual_mem (e : Tm) {I I' : ℕ → Bl} {ρ ρ' : ℕ → ℝ} (hI : ∀ i, (I i).Mem (ρ i))
    (hI' : ∀ i, (I' i).Mem (ρ' i)) :
    (e.idual I I').1.Mem (e.eval ρ) ∧ (e.idual I I').2.Mem (e.deriv ρ ρ') := by
  induction e with
  | c p q => exact ⟨Bl.mem_ofFrac p q, Bl.mem_zero⟩
  | v i => exact ⟨hI i, hI' i⟩
  | add a b iha ihb => exact ⟨Bl.mem_add iha.1 ihb.1, Bl.mem_add iha.2 ihb.2⟩
  | mul a b iha ihb =>
    exact ⟨Bl.mem_mul iha.1 ihb.1,
      Bl.mem_add (Bl.mem_mul iha.2 ihb.1) (Bl.mem_mul iha.1 ihb.2)⟩
  | neg a iha => exact ⟨Bl.mem_neg iha.1, Bl.mem_neg iha.2⟩
  | sq a iha => exact ⟨Bl.mem_sq iha.1, Bl.mem_dbl (Bl.mem_mul iha.1 iha.2)⟩

/-- **Soundness of second-order dual evaluation.** -/
theorem ihd_mem (e : Tm) {I I' I'' : ℕ → Bl} {ρ ρ' ρ'' : ℕ → ℝ} (hI : ∀ i, (I i).Mem (ρ i))
    (hI' : ∀ i, (I' i).Mem (ρ' i)) (hI'' : ∀ i, (I'' i).Mem (ρ'' i)) :
    (e.ihd I I' I'').1.Mem (e.eval ρ) ∧ (e.ihd I I' I'').2.1.Mem (e.deriv ρ ρ') ∧
      (e.ihd I I' I'').2.2.Mem (e.deriv2 ρ ρ' ρ'') := by
  induction e with
  | c p q => exact ⟨Bl.mem_ofFrac p q, Bl.mem_zero, Bl.mem_zero⟩
  | v i => exact ⟨hI i, hI' i, hI'' i⟩
  | add a b iha ihb =>
    exact ⟨Bl.mem_add iha.1 ihb.1, Bl.mem_add iha.2.1 ihb.2.1, Bl.mem_add iha.2.2 ihb.2.2⟩
  | mul a b iha ihb =>
    refine ⟨Bl.mem_mul iha.1 ihb.1,
      Bl.mem_add (Bl.mem_mul iha.2.1 ihb.1) (Bl.mem_mul iha.1 ihb.2.1), ?_⟩
    exact Bl.mem_add (Bl.mem_add (Bl.mem_mul iha.2.2 ihb.1)
      (Bl.mem_dbl (Bl.mem_mul iha.2.1 ihb.2.1))) (Bl.mem_mul iha.1 ihb.2.2)
  | neg a iha => exact ⟨Bl.mem_neg iha.1, Bl.mem_neg iha.2.1, Bl.mem_neg iha.2.2⟩
  | sq a iha =>
    exact ⟨Bl.mem_sq iha.1, Bl.mem_dbl (Bl.mem_mul iha.1 iha.2.1),
      Bl.mem_dbl (Bl.mem_add (Bl.mem_sq iha.2.1) (Bl.mem_mul iha.1 iha.2.2))⟩

/-- All variables of the tree satisfy `P`. -/
@[expose] def UsesOnly (P : ℕ → Prop) : Tm → Prop
  | c _ _ => True
  | v i => P i
  | add a b => a.UsesOnly P ∧ b.UsesOnly P
  | mul a b => a.UsesOnly P ∧ b.UsesOnly P
  | neg a => a.UsesOnly P
  | sq a => a.UsesOnly P

/-- The value only depends on the variables actually used. -/
theorem eval_congr {P : ℕ → Prop} (e : Tm) (he : e.UsesOnly P) {ρ₁ ρ₂ : ℕ → ℝ}
    (h : ∀ i, P i → ρ₁ i = ρ₂ i) : e.eval ρ₁ = e.eval ρ₂ := by
  induction e with
  | c p q => rfl
  | v i => exact h i he
  | add a b iha ihb => simp only [eval, iha he.1, ihb he.2]
  | mul a b iha ihb => simp only [eval, iha he.1, ihb he.2]
  | neg a iha => simp only [eval, iha he]
  | sq a iha => simp only [eval, iha he]

/-- The derivative only depends on the variables actually used. -/
theorem deriv_congr {P : ℕ → Prop} (e : Tm) (he : e.UsesOnly P) {ρ₁ ρ₂ ρ₁' ρ₂' : ℕ → ℝ}
    (h : ∀ i, P i → ρ₁ i = ρ₂ i) (h' : ∀ i, P i → ρ₁' i = ρ₂' i) :
    e.deriv ρ₁ ρ₁' = e.deriv ρ₂ ρ₂' := by
  induction e with
  | c p q => rfl
  | v i => exact h' i he
  | add a b iha ihb => simp only [deriv, iha he.1, ihb he.2]
  | mul a b iha ihb =>
    simp only [deriv, iha he.1, ihb he.2, eval_congr a he.1 h, eval_congr b he.2 h]
  | neg a iha => simp only [deriv, iha he]
  | sq a iha => simp only [deriv, iha he, eval_congr a he h]

/-- Monotonicity of `UsesOnly` in the variable predicate. -/
theorem UsesOnly.mono {P Q : ℕ → Prop} {e : Tm} (he : e.UsesOnly P) (h : ∀ i, P i → Q i) :
    e.UsesOnly Q := by
  induction e with
  | c p q => trivial
  | v i => exact h i he
  | add a b iha ihb => exact ⟨iha he.1, ihb he.2⟩
  | mul a b iha ihb => exact ⟨iha he.1, ihb he.2⟩
  | neg a iha => exact iha he
  | sq a iha => exact iha he

end Tm

/-! ## Pólya positivity test -/

/-- Value of the integer polynomial `Σ cₖ uᵏ` (coefficients from degree `0`). -/
@[expose] def zpoly : List ℤ → ℝ → ℝ
  | [], _ => 0
  | a :: p, u => (a : ℝ) + u * zpoly p u

/-- Value of the shifted sum used by `mulOnePlus`. -/
theorem zpoly_addShift (b : ℤ) (p : List ℤ) (u : ℝ) :
    zpoly (mulOnePlus.addShift b p) u = zpoly p u + b + u * zpoly p u := by
  induction p generalizing b with
  | nil => simp [mulOnePlus.addShift, zpoly]
  | cons a q ih => simp only [mulOnePlus.addShift, zpoly, ih, int_add_eq]; push_cast; ring

/-- `mulOnePlus` multiplies the polynomial by `1 + u`. -/
theorem zpoly_mulOnePlus (p : List ℤ) (u : ℝ) : zpoly (mulOnePlus p) u = (1 + u) * zpoly p u := by
  cases p with
  | nil => simp [mulOnePlus, zpoly]
  | cons a q => simp only [mulOnePlus, zpoly, zpoly_addShift]; ring

/-- A polynomial with positive coefficients is positive on `[0, ∞)`. -/
theorem zpoly_pos_of_allPos {p : List ℤ} (hp : allPos p = true) {u : ℝ} (hu : 0 ≤ u) :
    0 < zpoly p u := by
  induction p with
  | nil => simp [allPos] at hp
  | cons a q ih =>
    cases q with
    | nil =>
      simp only [allPos, decide_eq_true_eq] at hp
      simp only [zpoly, mul_zero, add_zero]; exact_mod_cast hp
    | cons b r =>
      simp only [allPos, Bool.and_eq_true, decide_eq_true_eq] at hp
      have h1 : (0 : ℝ) < a := by exact_mod_cast hp.1
      have h2 := ih hp.2
      simp only [zpoly] at h2 ⊢
      nlinarith

/-- **The Pólya test proves positivity on `[0, ∞)`.** -/
theorem zpoly_pos_of_polyaOK {M : ℕ} {p : List ℤ} (h : polyaOK M p = true) {u : ℝ}
    (hu : 0 ≤ u) : 0 < zpoly p u := by
  induction M generalizing p with
  | zero => exact zpoly_pos_of_allPos h hu
  | succ M ih =>
    simp only [polyaOK, Bool.or_eq_true] at h
    rcases h with h | h
    · exact zpoly_pos_of_allPos h hu
    · have := ih h
      rw [zpoly_mulOnePlus] at this
      have h1 : 0 < 1 + u := by linarith
      exact pos_of_mul_pos_right this h1.le

/-- `zpoly` of seven mapped coefficients is the corresponding finite sum. -/
theorem zpoly_range7 (f : ℕ → ℤ) (u : ℝ) :
    zpoly ((List.range 7).map f) u = ∑ k ∈ Finset.range 7, (f k : ℝ) * u ^ k := by
  simp [List.range_succ, zpoly, Finset.sum_range_succ]
  ring

/-! ## The chord bound -/

/-- **Chord bound.** If `g` is twice differentiable on a neighbourhood of `[a, b]` with
`|g''| ≤ M` on `[a, b]`, then on `[a, b]`
`g(x) ≥ ((b − x) g(a) + (x − a) g(b))/(b − a) − M (x − a)(b − x)/2`. -/
theorem chord_lower {g g' g'' : ℝ → ℝ} {a b M x : ℝ} (hab : a < b)
    (hg : ∀ y ∈ Icc a b, HasDerivAt g (g' y) y) (hg' : ∀ y ∈ Icc a b, HasDerivAt g' (g'' y) y)
    (hM : ∀ y ∈ Icc a b, |g'' y| ≤ M) (hx : x ∈ Icc a b) :
    ((b - x) * g a + (x - a) * g b) / (b - a) - M * (x - a) * (b - x) / 2 ≤ g x := by
  set φ : ℝ → ℝ := fun y => g y - ((b - y) * g a + (y - a) * g b) / (b - a) +
    M * (y - a) * (b - y) / 2 with hφ
  set φ' : ℝ → ℝ := fun y => g' y + (g a - g b) / (b - a) + M * (a + b - 2 * y) / 2
  set φ'' : ℝ → ℝ := fun y => g'' y - M
  have hba : 0 < b - a := by linarith
  have hφd : ∀ y ∈ Icc a b, HasDerivAt φ (φ' y) y := by
    intro y hy
    have h1 := hg y hy
    have h2 : HasDerivAt (fun y => ((b - y) * g a + (y - a) * g b) / (b - a))
        ((g b - g a) / (b - a)) y := by
      have := ((((hasDerivAt_id y).const_sub b).mul_const (g a)).add
        (((hasDerivAt_id y).sub_const a).mul_const (g b))).div_const (b - a)
      convert this using 1
      · funext z; simp
      · ring
    have h3 : HasDerivAt (fun y => M * (y - a) * (b - y) / 2) (M * (a + b - 2 * y) / 2) y := by
      have := ((((hasDerivAt_id y).sub_const a).const_mul M).mul
        ((hasDerivAt_id y).const_sub b)).div_const 2
      convert this using 1
      · funext z; simp only [id, Pi.mul_apply]
      · simp only [id]; ring
    have := (h1.sub h2).add h3
    convert this using 1; simp only [φ']; ring
  have hφd' : ∀ y ∈ Icc a b, HasDerivAt φ' (φ'' y) y := by
    intro y hy
    have h1 := hg' y hy
    have h3 : HasDerivAt (fun y => M * (a + b - 2 * y) / 2) (-M) y := by
      have := ((((hasDerivAt_id y).const_mul 2).const_sub (a + b)).const_mul M).div_const 2
      convert this using 1
      · funext z; simp
      · ring
    have := (h1.add_const ((g a - g b) / (b - a))).add h3
    convert this using 1
  have hint : interior (Icc a b) = Ioo a b := interior_Icc
  have hconc : ConcaveOn ℝ (Icc a b) φ := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc a b) (f' := φ') (f'' := φ'')
    · intro y hy; exact (hφd y hy).continuousAt.continuousWithinAt
    · intro y hy; rw [hint] at hy ⊢; exact (hφd y (Ioo_subset_Icc_self hy)).hasDerivWithinAt
    · intro y hy; rw [hint] at hy ⊢; exact (hφd' y (Ioo_subset_Icc_self hy)).hasDerivWithinAt
    · intro y hy; rw [hint] at hy
      have := hM y (Ioo_subset_Icc_self hy)
      simp only [φ'']; linarith [le_abs_self (g'' y)]
  have hmin := hconc.min_le_of_mem_Icc (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hx
  have ha : φ a = 0 := by simp only [φ]; field_simp; ring
  have hb : φ b = 0 := by simp only [φ]; field_simp; ring
  rw [ha, hb, min_self] at hmin
  simp only [φ] at hmin
  linarith

end PlasmaLean.Design.SolovevBallooning
