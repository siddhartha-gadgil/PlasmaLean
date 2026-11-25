/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.DyadicTaylorModel

/-! # Integer witnesses for a multiply-add of dyadic Taylor models

All input, coefficient and truncation errors enter one integer inequality.
The output can have any degree, and the four models use a common binary scale.
-/

@[expose] public section
namespace PlasmaLean.Certificates.DyadicHornerStep
open TrajectoryTaylorModel

def plus : List ℤ → List ℤ → List ℤ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: plus p q

def times (c : ℤ) (p : List ℤ) : List ℤ := p.map (c * ·)

/-- Coefficient convolution in ascending order. Trailing zero coefficients have no effect. -/
def convolution : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: p, q => plus (times a q) (0 :: convolution p q)

def magnitude : List ℤ → ℤ
  | [] => 0
  | a :: p => |a| + magnitude p

noncomputable def value (p : List ℤ) (t : ℝ) := QPoly.eval (p.map fun (a : ℤ) => (a : ℚ)) t
@[simp] theorem value_nil (t : ℝ) : value [] t = 0 := rfl
@[simp] theorem value_cons (a : ℤ) (p : List ℤ) (t : ℝ) :
    value (a :: p) t = (a : ℝ) + t * value p t := by simp [value]
@[simp] theorem value_plus (p q : List ℤ) (t : ℝ) :
    value (plus p q) t = value p t + value q t := by
  induction p generalizing q with
  | nil => simp [plus]
  | cons a p ih =>
    cases q with
    | nil => simp [plus]
    | cons b q => simp [plus, ih]; ring

@[simp] theorem value_times (c : ℤ) (p : List ℤ) (t : ℝ) :
    value (times c p) t = (c : ℝ) * value p t := by
  induction p with
  | nil => simp [times]
  | cons x p ih =>
    change value ((c * x) :: times c p) t = _
    simp [ih]; ring

@[simp] theorem value_convolution (p q : List ℤ) (t : ℝ) :
    value (convolution p q) t = value p t * value q t := by
  induction p with
  | nil => simp [convolution]
  | cons a p ih => simp [convolution, ih]; ring

theorem value_bound (p : List ℤ) {t : ℝ} (ht : |t| ≤ 1) :
    |value p t| ≤ (magnitude p : ℝ) := by
  induction p with
  | nil => simp [magnitude]
  | cons a p ih =>
    simp only [value_cons, magnitude, Int.cast_add, Int.cast_abs]
    apply (abs_add_le _ _).trans
    apply add_le_add_right
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right ht (abs_nonneg _)).trans (by simpa using ih)

def errorPoly (d : ℤ) (a x q out : List ℤ) :=
  plus (convolution a x) (times d (plus q (times (-1) out)))

/-- In squared numerator units, charge input errors and the exact coefficient discrepancy. -/
def Fits (bits : ℕ) (a x q out : List ℤ) (ea ex eq eo : ℤ) : Prop :=
  ea * (magnitude x + ex) + ex * magnitude a + 2 ^ bits * eq +
    magnitude (errorPoly (2 ^ bits) a x q out) ≤ 2 ^ bits * eo

/-- A single closed natural-number equality can certify a signed integer bound. -/
theorem le_of_sub_toNat_zero {a b : ℤ} (h : (a - b).toNat = 0) : a ≤ b := by omega

/-- A checked integer inequality encloses the real multiply-add throughout the normalized slab. -/
theorem Fits.mem {bits : ℕ} {a x q out : List ℤ} {ea ex eq eo : ℤ}
    (h : Fits bits a x q out ea ex eq eo) {s av xv qv : ℝ} (hs : |s| ≤ 1)
    (ha : (ofDyadic bits a ea).Mem s av) (hx : (ofDyadic bits x ex).Mem s xv)
    (hq : (ofDyadic bits q eq).Mem s qv) :
    (ofDyadic bits out eo).Mem s (av * xv + qv) := by
  let d : ℤ := 2 ^ bits
  have hd : 0 < (d : ℝ) := by dsimp [d]; positivity
  have da : |(d : ℝ) * av - value a s| ≤ ea := by
    simpa only [d, value, Int.cast_pow, Int.cast_ofNat] using (mem_ofDyadic_iff ..).mp ha
  have dx : |(d : ℝ) * xv - value x s| ≤ ex := by
    simpa only [d, value, Int.cast_pow, Int.cast_ofNat] using (mem_ofDyadic_iff ..).mp hx
  have dq : |(d : ℝ) * qv - value q s| ≤ eq := by
    simpa only [d, value, Int.cast_pow, Int.cast_ofNat] using (mem_ofDyadic_iff ..).mp hq
  have xb : |(d : ℝ) * xv| ≤ (magnitude x : ℝ) + ex := by
    calc
      _ = |value x s + ((d : ℝ) * xv - value x s)| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add (value_bound _ hs) dx)
  have re : value (errorPoly d a x q out) s =
      value a s * value x s + (d : ℝ) * (value q s - value out s) := by
    simp only [errorPoly, value_plus, value_convolution, value_times, Int.cast_neg, Int.cast_one]
    ring
  have bound : (ea : ℝ) * ((magnitude x : ℝ) + ex) + (ex : ℝ) * magnitude a + (d : ℝ) * eq +
      magnitude (errorPoly d a x q out) ≤ (d : ℝ) * eo := by
    change ea * (magnitude x + ex) + ex * magnitude a + d * eq +
        magnitude (errorPoly d a x q out) ≤ d * eo at h
    exact_mod_cast h
  apply (mem_ofDyadic_iff ..).mpr
  change |2 ^ bits * (av * xv + qv) - value out s| ≤ _
  have dEq : (d : ℝ) = 2 ^ bits := by simp [d]
  rw [← dEq, ← mul_le_mul_iff_right₀ hd]
  calc
    _ = |((d : ℝ) * av - value a s) * ((d : ℝ) * xv) +
          ((d : ℝ) * xv - value x s) * value a s + (d : ℝ) * ((d : ℝ) * qv - value q s) +
            value (errorPoly d a x q out) s| := by
      rw [← abs_of_pos hd, ← abs_mul, abs_of_pos hd, re]; congr 1; ring
    _ ≤ |((d : ℝ) * av - value a s) * ((d : ℝ) * xv)| + |((d : ℝ) * xv - value x s) * value a s| +
        |(d : ℝ) * ((d : ℝ) * qv - value q s)| + |value (errorPoly d a x q out) s| :=
      (abs_add_le _ _).trans (add_le_add_left
        ((abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)) _)
    _ ≤ (ea : ℝ) * ((magnitude x : ℝ) + ex) + (ex : ℝ) * magnitude a + (d : ℝ) * eq +
        magnitude (errorPoly d a x q out) := by
      simp only [abs_mul, abs_of_pos hd] at xb ⊢
      exact add_le_add (add_le_add (add_le_add
        (mul_le_mul da xb (mul_nonneg hd.le (abs_nonneg _)) ((abs_nonneg _).trans da))
        (mul_le_mul dx (value_bound a hs) (abs_nonneg _) ((abs_nonneg _).trans dx)))
          (mul_le_mul_of_nonneg_left dq hd.le)) (value_bound _ hs)
    _ ≤ _ := by simpa [mul_comm (eo : ℝ)] using bound

/-- A semantic Horner step whose numerical witness contains only integers. -/
inductive MulAdd : Model → Model → Model → Model → Prop
  | dyadic {bits : ℕ} {a x q out : List ℤ} {ea ex eq eo : ℤ}
      (check : Fits bits a x q out ea ex eq eo) :
      MulAdd (ofDyadic bits a ea) (ofDyadic bits x ex) (ofDyadic bits q eq) (ofDyadic bits out eo)

theorem MulAdd.mem {a x q out : Model} (h : MulAdd a x q out)
    {s av xv qv : ℝ} (hs : |s| ≤ 1) (ha : a.Mem s av) (hx : x.Mem s xv)
    (hq : q.Mem s qv) : out.Mem s (av * xv + qv) := by
  cases h with
  | dyadic check => exact check.mem hs ha hx hq

end PlasmaLean.Certificates.DyadicHornerStep
