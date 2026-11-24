/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkReferenceFirstDefectData
public import PlasmaLean.Design.DommaschkBounceFlowStep
public import PlasmaLean.Design.DommaschkHarmonicSlab0

/-! # Physical defect of the first exported forward reference segment

Both components of the defect are estimated after cancelling the reference
slope against the candidate field polynomial on eight normalized subintervals.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkReferenceFirst
open Certificates.QPoly Certificates.TrajectoryTaylorModel DommaschkKam DommaschkBounceField
open Fields.RectangularODEStep Set

/-- Normalized clock of the first 1/64-radian forward integration slab. -/
def clock (t : ℝ) := 128 * t - 1

/-- The central polynomial position in physical cylindrical coordinates. -/
def position (t : ℝ) : State :=
  ![dkR0 + eval reference.u.poly (clock t), eval reference.z.poly (clock t)]

/-- The physical angular derivative includes the factor 128 from the normalized clock. -/
def velocity (t : ℝ) : State :=
  ![128 * eval (Certificates.QPoly.deriv reference.u.poly) (clock t),
    128 * eval (Certificates.QPoly.deriv reference.z.poly) (clock t)]

theorem position_derivative (t : ℝ) : HasDerivAt position (velocity t) t := by
  have hc : HasDerivAt clock 128 t := by
    change HasDerivAt (fun x : ℝ => 128 * x - 1) 128 t
    simpa only [id_eq, mul_one] using (((hasDerivAt_id t).const_mul 128).sub_const 1)
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [position,velocity,mul_comm] using
      (((hasDerivAt_eval reference.u.poly (clock t)).comp t hc).const_add dkR0)
  · simpa [position,velocity,mul_comm,Function.comp_def] using
      ((hasDerivAt_eval reference.z.poly (clock t)).comp t hc)

private theorem input_mem {t : ℝ} (ht : t ∈ Icc 0 (1/64)) :
    reference.Mem (clock t) (position t 0 - dkR0) (position t 1)
      (Real.cos (2*t)) (Real.sin (2*t)) := by
  have zero (m : Model) (e : m.radius = 0) : m.Mem (clock t) (eval m.poly (clock t)) := by
    simp [Model.Mem, e]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [position, Matrix.cons_val_zero, add_sub_cancel_left] using
      zero reference.u (eq_of_beq (by kernel_fact))
  · exact zero reference.z (eq_of_beq (by kernel_fact))
  · change (DommaschkHarmonicSlab0.model false 0 false).Mem _ _
    simpa [Certificates.TrajectoryTrig.wave, clock] using
      DommaschkHarmonicSlab0.physical false 0 false (by simpa using ht)
  · change (DommaschkHarmonicSlab0.model false 0 true).Mem _ _
    simpa [Certificates.TrajectoryTrig.wave, clock] using
      DommaschkHarmonicSlab0.physical false 0 true (by simpa using ht)

private theorem quotient_bound {v p D b : ℝ} (hD : 1 ≤ D) (hb : 0 ≤ b)
    (h : |v - p * D| ≤ b) : |v / D - p| ≤ b := by
  have hd : 0 < D := zero_lt_one.trans_le hD
  rw [show v / D - p = (v - p*D) / D by field_simp, abs_div, abs_of_pos hd, div_le_iff₀ hd]
  exact h.trans (le_mul_of_one_le_right hb hD)

/-- Uniform ordinary cylindrical defect on the central curve. Both the field
and derivative in this comparison are realized, with no flow-existence hypothesis. -/
theorem physical_defect {t : ℝ} (ht : t ∈ Icc 0 (1 / 64)) :
    let v := physicalFlow 0 1 t (position t) - velocity t
    |v 0| ≤ 1 / 10^12 ∧ |v 1| ≤ 1 / 10^13 := by
  let s := clock t
  have hs : |s| ≤ 1 := by
    change |128 * t - 1| ≤ 1
    exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have ha := input_mem ht
  have hr := enclose (c := ⟨[1/10], 1/20⟩) hs ha.1 (by kernel_fact)
  have hR : 0 < position t 0 := by
    norm_num [Model.Mem, dkR0, eval_cons, eval_nil, abs_le] at hr
    linarith
  let val (p : DkPoly.SP) := atPoint p (position t 0) t (position t 1)
  have hd : dD0.Mem s (val dD) := dD_checked.mem hs ha
  have hdlo : 1 ≤ val dD := by
    have low := (dD_range hs hd).1
    norm_num at low
    linarith
  have nr := TaylorResidual.numerator_mem (F := ⟨7,80⟩) 128 reference.u hs
    (show dnR0.Mem s (val dnR) from dnR_checked.mem hs ha) hd
  have nz := TaylorResidual.numerator_mem (F := ⟨7,80⟩) 128 reference.z hs
    (show dnZ0.Mem s (val dnZ) from dnZ_checked.mem hs ha) hd
  rw [radial_match.eq] at nr
  rw [vertical_match.eq] at nz
  have er := quotient_bound hdlo (by positivity) (radial_bound hs nr)
  have ez := quotient_bound hdlo (by positivity) (vertical_bound hs nz)
  have posD : clockPoly 0 1 dD (t,position t) ≠ 0 := by
    simpa only [clockPoly, zero_add, one_mul, atPoint, val] using (zero_lt_one.trans_le hdlo).ne'
  rw [← ratio_eq_physical 0 1 t (position t) hR posD]
  norm_num [ratioFlow, clockPoly, velocity, val, s] at er ez ⊢
  exact ⟨er,ez⟩

/-- The exact affine frame in physical angular time, from the identity to its
exported dyadic value at the end of the slab. -/
def frame (i j : Fin 2) (t : ℝ) : ℝ :=
  let start : ℝ := if i = j then 1 else 0
  start + 64*t*((frameEnd i j : ℝ) - start)

def det (t : ℝ) := frame 0 0 t * frame 1 1 t - frame 0 1 t * frame 1 0 t

/-- The inverse-frame residual in real coordinates. -/
def pullback (t : ℝ) (v : State) : State :=
  ![(frame 1 1 t * v 0 - frame 0 1 t * v 1) / det t,
    (frame 0 0 t * v 1 - frame 1 0 t * v 0) / det t]

private theorem frame_box {t : ℝ} (ht : t ∈ Icc 0 (1 / 64)) :
    99/100 ≤ frame 0 0 t ∧ frame 0 0 t ≤ 101/100 ∧
    99/100 ≤ frame 1 1 t ∧ frame 1 1 t ≤ 101/100 ∧
    |frame 0 1 t| ≤ 1/100 ∧ |frame 1 0 t| ≤ 1/100 := by
  have h0 := ht.1
  have h1 := ht.2
  norm_num [frame,frameEnd,abs_le,abs_of_nonneg h0]
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem det_lower {t : ℝ} (ht : t ∈ Icc 0 (1 / 64)) : 97 / 100 ≤ det t := by
  obtain ⟨a,_,d,_,b,c⟩ := frame_box ht
  have bc := mul_le_mul b c (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1/100)
  rw [← abs_mul] at bc
  have ad := mul_le_mul a d (by norm_num : (0:ℝ) ≤ 99/100)
    (by linarith : 0 ≤ frame 0 0 t)
  unfold det
  linarith [(abs_le.mp bc).2]

/-- The pullback solves the physical frame equation with this actual frame. -/
theorem frame_pullback {t : ℝ} (ht : t ∈ Icc 0 (1 / 64)) (v : State) :
    frame 0 0 t * pullback t v 0 + frame 0 1 t * pullback t v 1 = v 0 ∧
    frame 1 0 t * pullback t v 0 + frame 1 1 t * pullback t v 1 = v 1 := by
  have nz : det t ≠ 0 := by have := det_lower ht; linarith
  constructor <;> simp [pullback] <;> field_simp <;> unfold det <;> ring

/-- The true Euclidean moving-frame residual for the submitted clock and field
is bounded by the claimed external first-step defect. -/
theorem framed_defect {t : ℝ} (ht : t ∈ Icc 0 (1 / 64)) :
    let w := pullback t (physicalFlow 0 1 t (position t) - velocity t)
    Real.sqrt ((w 0)^2 + (w 1)^2) ≤ (recordedDefect : ℝ) := by
  let v := physicalFlow 0 1 t (position t) - velocity t
  obtain ⟨r,z⟩ := physical_defect ht
  change |v 0| ≤ _ at r
  change |v 1| ≤ _ at z
  obtain ⟨al,au,dl,du,b,c⟩ := frame_box ht
  have d := det_lower ht
  have small {a b x y : ℝ} (ha : |a| ≤ 101/100) (hb : |b| ≤ 101/100)
      (hx : |x| ≤ 1/10^12) (hy : |y| ≤ 1/10^12) :
      |(a*x - b*y) / det t| ≤ 3 / 10^12 := by
    rw [abs_div, abs_of_pos (by linarith : 0 < det t), div_le_iff₀ (by linarith)]
    have g := (abs_sub _ _).trans (add_le_add
      (show |a*x| ≤ (101/100)*(1/10^12) by rw [abs_mul]; gcongr)
      (show |b*y| ≤ (101/100)*(1/10^12) by rw [abs_mul]; gcongr))
    linarith
  have z' : |v 1| ≤ 1 / 10^12 := by linarith
  have u : |pullback t v 0| ≤ 3 / 10^12 := small
    (abs_le.mpr ⟨by linarith,du⟩) (by linarith : |frame 0 1 t| ≤ _) r z'
  have w : |pullback t v 1| ≤ 3 / 10^12 := small
    (abs_le.mpr ⟨by linarith,au⟩) (by linarith : |frame 1 0 t| ≤ _) z' r
  have uu := pow_le_pow_left₀ (abs_nonneg _) u 2
  have ww := pow_le_pow_left₀ (abs_nonneg _) w 2
  rw [sq_abs] at uu ww
  apply (Real.sqrt_le_iff).mpr
  norm_num [recordedDefect] at uu ww ⊢
  linarith

end PlasmaLean.Design.DommaschkReferenceFirst
