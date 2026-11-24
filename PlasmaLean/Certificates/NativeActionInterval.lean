/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.DyadicTaylorModel
public import PlasmaLean.Certificates.ValidatedQuadrature
public import PlasmaLean.Certificates.MirrorActionQuadrature

/-! # Fixed-point intervals used by the archived mirror-action quadrature -/

@[expose] public section
namespace PlasmaLean.Certificates.NativeActionInterval
open TrajectoryTaylorModel Set
open ValidatedQuadrature (fdiv_le le_cdiv)

/-- Fixed-point action interval endpoints use units of two to the minus 52. -/
abbrev scale : ℤ := 4503599627370496

structure Box where
  lo : ℤ
  hi : ℤ
  deriving BEq

def Box.Mem (b : Box) (x : ℝ) : Prop := (b.lo : ℝ) ≤ scale * x ∧ scale * x ≤ b.hi

def rational (x : ℚ) : Box := ⟨⌊x * scale⌋, ⌈x * scale⌉⟩
def add (a b : Box) : Box := ⟨a.lo + b.lo, a.hi + b.hi⟩
def mul (a b : Box) : Box :=
  ⟨min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi)) / scale,
   -(-max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi)) / scale)⟩
def inv (b : Box) : Box := ⟨(scale * scale) / b.hi, -(-(scale * scale) / b.lo)⟩
def div (a b : Box) : Box := mul a (inv b)
def clip (b : Box) : Box := ⟨max b.lo 0, max b.hi 0⟩

theorem mem_rational (q : ℚ) : (rational q).Mem q := by
  have lo := Int.floor_le (q * scale)
  have hi := Int.le_ceil (q * scale)
  rw [mul_comm q] at lo hi
  constructor
  · change ((⌊q * scale⌋ : ℤ) : ℝ) ≤ scale * (q : ℝ)
    rw [mul_comm q]
    exact_mod_cast lo
  · change scale * (q : ℝ) ≤ ((⌈q * scale⌉ : ℤ) : ℝ)
    rw [mul_comm q]
    exact_mod_cast hi

theorem mem_add {a b : Box} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) : (add a b).Mem (x+y) := by
  simp only [Box.Mem, add, Int.cast_add, mul_add] at *
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

theorem mem_mul {a b : Box} {x y : ℝ} (hx : a.Mem x) (hy : b.Mem y) : (mul a b).Mem (x*y) := by
  have hs : (0:ℝ) < scale := by norm_num
  obtain ⟨hl, hu⟩ := ValidatedQuadrature.FIv.corner_bounds hx.1 hx.2 hy.1 hy.2
  have l := fdiv_le
    (min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi))) scale (by norm_num)
  have u := le_cdiv
    (max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))) scale (by norm_num)
  unfold Box.Mem mul
  simp only [Int.cast_min, Int.cast_max, Int.cast_mul, Int.cast_neg] at l u ⊢
  have eq : ((scale : ℝ)*x) * (scale*y) / scale = scale * (x*y) := by norm_num; ring
  rw [← eq]
  exact ⟨l.trans (div_le_div_of_nonneg_right hl hs.le),
    (div_le_div_of_nonneg_right hu hs.le).trans u⟩

theorem pos_of_mem {b : Box} {x : ℝ} (hb : 0 < b.lo) (hx : b.Mem x) : 0 < x := by
  have h : (0:ℝ) < b.lo := by exact_mod_cast hb
  exact pos_of_mul_pos_right (h.trans_le hx.1) (by norm_num)

theorem mem_inv {b : Box} {x : ℝ} (hb : 0 < b.lo) (hx : b.Mem x) : (inv b).Mem x⁻¹ := by
  have hp := pos_of_mem hb hx
  have lb : (0:ℝ) < b.lo := by exact_mod_cast hb
  have ub : (0:ℝ) < b.hi := (lb.trans_le hx.1).trans_le hx.2
  have l := fdiv_le (scale*scale) b.hi (by exact_mod_cast ub)
  have u := le_cdiv (scale*scale) b.lo hb
  unfold Box.Mem inv
  simp only [Int.cast_mul, Int.cast_neg] at l u ⊢
  have e : (scale : ℝ)*scale/(scale*x) = scale*x⁻¹ := by field_simp
  rw [← e]
  constructor
  · apply l.trans
    gcongr
    exact hx.2
  · apply le_trans _ u
    gcongr
    exact hx.1

theorem mem_div {a b : Box} {x y : ℝ} (hb : 0 < b.lo) (hx : a.Mem x) (hy : b.Mem y) :
    (div a b).Mem (x/y) := by simpa only [div, div_eq_mul_inv] using mem_mul hx (mem_inv hb hy)

theorem mem_clip {b : Box} {x : ℝ} (hx : b.Mem x) : (clip b).Mem (max x 0) := by
  simp only [Box.Mem, clip, Int.cast_max, Int.cast_zero] at *
  rw [mul_max_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ scale),mul_zero]
  exact ⟨max_le_max_right 0 hx.1, max_le_max_right 0 hx.2⟩

/-- A root witness brackets the exact root also when the input interval straddles zero. -/
structure Root (a b : Box) : Prop where
  lo : b.lo ^ 2 ≤ max a.lo 0 * scale
  hi : a.hi * scale ≤ b.hi ^ 2
  lo_nonneg : 0 ≤ b.lo
  hi_nonneg : 0 ≤ b.hi
  radicand_nonneg : 0 ≤ a.hi
  lo_maximal : max a.lo 0 * scale < (b.lo + 1)^2
  hi_minimal : 0 < b.hi → (b.hi - 1)^2 < a.hi * scale

theorem Root.mem {a b : Box} {x : ℝ} (w : Root a b) (hx : a.Mem x) (nonneg : 0 ≤ x) :
    b.Mem (Real.sqrt x) := by
  have sc : (0:ℝ) ≤ scale := by norm_num
  have l : (b.lo:ℝ)^2 ≤ max (a.lo:ℝ) 0 * scale := by exact_mod_cast w.lo
  have u : (a.hi:ℝ)*scale ≤ (b.hi:ℝ)^2 := by exact_mod_cast w.hi
  have up : (0:ℝ) ≤ b.hi := by exact_mod_cast w.hi_nonneg
  have l' := mul_le_mul_of_nonneg_right (max_le hx.1 (mul_nonneg sc nonneg)) sc
  have u' := mul_le_mul_of_nonneg_right hx.2 sc
  have eq : ((scale:ℝ) * Real.sqrt x)^2 = scale*x*scale := by
    rw [mul_pow,Real.sq_sqrt nonneg]
    ring
  refine ⟨?_, ?_⟩
  · apply le_of_sq_le_sq _ (mul_nonneg sc (Real.sqrt_nonneg _))
    rw [eq]
    exact l.trans l'
  · apply le_of_sq_le_sq _ up
    rw [eq]
    exact u'.trans u

def horner (p : List ℚ) (t : Box) : Box :=
  p.foldr (fun c rest => add (rational c) (mul t rest)) ⟨0,0⟩

theorem horner_mem {t : Box} {s : ℝ} (ht : t.Mem s) (p : List ℚ) :
    (horner p t).Mem (QPoly.eval p s) := by
  induction p with
  | nil => simp [horner, Box.Mem]
  | cons a p ih => exact mem_add (mem_rational a) (mem_mul ht ih)

/-- An 80-bit Taylor coefficient is rounded outward to 52 bits. The absolute
model error is rounded upward, then added symmetrically after interval Horner. -/
def onPanel (m : Model) (t : Box) : Box :=
  let interval := horner m.poly t
  let error := (rational m.radius).hi
  ⟨interval.lo - error, interval.hi + error⟩

/-- An explicit Horner trace records the result after each multiplication, keeping
kernel reduction of a panel independent of the depth of the interval product tree. -/
inductive HornerRun (t : Box) : List Box → Box → Prop where
  | nil : HornerRun t [] ⟨0, 0⟩
  | cons {b rest out : Box} {bs : List Box} :
      HornerRun t bs rest → add b (mul t rest) = out → HornerRun t (b :: bs) out

theorem horner_of_run {t b : Box} {p : List ℚ} {bs : List Box}
    (hc : p.map rational = bs) (w : HornerRun t bs b) : horner p t = b := by
  subst bs
  induction p generalizing b with
  | nil => cases w; rfl
  | cons a p ih =>
    cases w with
    | cons rest step =>
      change add (rational a) (mul t (horner p t)) = _
      rw [ih rest, step]

theorem onPanel_of_run {m : Model} {t b result : Box} {c : List Box} {e : ℤ}
    (coef : m.poly.map rational = c) (err : (rational m.radius).hi = e)
    (run : HornerRun t c b) (finish : (⟨b.lo - e, b.hi + e⟩ : Box) = result) :
    onPanel m t = result := by
  unfold onPanel
  rw [horner_of_run coef run, err, finish]

theorem onPanel_mem {m : Model} {t : Box} {s x : ℝ} (ht : t.Mem s) (hx : m.Mem s x) :
    (onPanel m t).Mem x := by
  have hp := horner_mem ht m.poly
  have hε := (mem_rational m.radius).2
  have l := mul_le_mul_of_nonneg_left (abs_le.mp hx).1 (by norm_num : (0:ℝ) ≤ scale)
  have u := mul_le_mul_of_nonneg_left (abs_le.mp hx).2 (by norm_num : (0:ℝ) ≤ scale)
  simp only [Box.Mem, onPanel, Int.cast_sub, Int.cast_add]
  constructor <;> linarith only [hp.1, hp.2, l, u, hε]

end PlasmaLean.Certificates.NativeActionInterval
