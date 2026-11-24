/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkTaylorResidual
public import PlasmaLean.Design.DommaschkBounceFlowStep

/-! # Euclidean defect bounds on a signed moving-frame slab

The reference derivative and signed field numerator are subtracted before
applying the frame adjugate. Three Taylor models enclose the resulting two
numerators and their common denominator. Rational Horner bounds then give
a Euclidean defect estimate everywhere on the closed normalized slab.
-/

@[expose] public section
namespace PlasmaLean.Design.FramedTaylorResidual
open Certificates.TrajectoryTaylorModel Certificates.QPoly DommaschkBounceTaylor

/-- Two numerators and the common denominator of the transformed velocity error. -/
structure Quotient where
  x : Model
  y : Model
  den : Model

/-- Separate component and denominator checks with an exact squared norm budget. -/
structure Accepts (q : Quotient) (budget x y lo : ℚ) (grid : List ℚ) : Prop where
  xlow : checkOn q.x.poly (q.x.radius - x) (-1) 1 grid = true
  xhigh : checkOn (scale (-1) q.x.poly) (q.x.radius - x) (-1) 1 grid = true
  ylow : checkOn q.y.poly (q.y.radius - y) (-1) 1 grid = true
  yhigh : checkOn (scale (-1) q.y.poly) (q.y.radius - y) (-1) 1 grid = true
  denLow : checkOn q.den.poly (q.den.radius + lo) (-1) 1 grid = true
  positive : 0 < lo
  nonneg : 0 ≤ budget
  square : x^2 + y^2 ≤ (budget * lo)^2

/-- Every accepted budget controls the true quotient throughout the slab. -/
theorem Accepts.sound {q : Quotient} {b x y l : ℚ} {grid : List ℚ} (h : Accepts q b x y l grid)
    {s X Y D : ℝ} (hs : |s| ≤ 1) (hx : q.x.Mem s X) (hy : q.y.Mem s Y)
    (hd : q.den.Mem s D) : 0 < D ∧ Real.sqrt ((X/D)^2 + (Y/D)^2) ≤ (b : ℝ) := by
  have hI : s ∈ Set.Icc ((-1 : ℚ) : ℝ) ((1 : ℚ) : ℝ) := by
    simpa only [Set.mem_Icc, Rat.cast_neg, Rat.cast_one] using abs_le.mp hs
  have lower := checkOn_sound h.denLow s hI
  push_cast at lower
  have dlo : (l : ℝ) ≤ D := by
    have := (abs_le.mp hd).1
    linarith
  have lp : (0 : ℝ) < l := by exact_mod_cast h.positive
  have dp := lt_of_lt_of_le lp dlo
  have bp : (0 : ℝ) ≤ b := by exact_mod_cast h.nonneg
  have x2 := pow_le_pow_left₀ (abs_nonneg X) (TaylorResidual.abs_bound hs hx h.xlow h.xhigh) 2
  have y2 := pow_le_pow_left₀ (abs_nonneg Y) (TaylorResidual.abs_bound hs hy h.ylow h.yhigh) 2
  rw [sq_abs] at x2 y2
  have b2 : (x:ℝ)^2 + (y:ℝ)^2 ≤ ((b:ℝ) * (l:ℝ))^2 := by exact_mod_cast h.square
  have bD := pow_le_pow_left₀ (mul_nonneg bp lp.le) (mul_le_mul_of_nonneg_left dlo bp) 2
  refine ⟨dp, Real.sqrt_le_iff.mpr ⟨bp, ?_⟩⟩
  rw [div_pow, div_pow, ← add_div, div_le_iff₀ (sq_pos_of_pos dp), ← mul_pow]
  exact ((add_le_add x2 y2).trans b2).trans bD

/-- A constant 3-4-5 triangle attains the submitted budget. -/
theorem constant_triangle :
    Accepts ⟨constant 3, constant 4, constant 1⟩ 5 3 4 1 [1] := by
  constructor <;> kernel_fact

/-- A vanishing common denominator fails for every partition and proposed radius. -/
theorem zero_denominator_rejected (b x y l : ℚ) (grid : List ℚ) :
    ¬ Accepts ⟨constant 0, constant 0, constant 0⟩ b x y l grid := by
  intro h
  have := (h.sound (s := 0) (by norm_num) (constant_mem 0 0) (constant_mem 0 0)
    (constant_mem 0 0)).1
  norm_num at this

/-- Decreasing the attained triangle budget is detected even with arbitrary witnesses. -/
theorem triangle_small_rejected (x y l : ℚ) (grid : List ℚ) :
    ¬ Accepts ⟨constant 3, constant 4, constant 1⟩ 4 x y l grid := by
  intro h
  have := (h.sound (s := 0) (by norm_num) (constant_mem 3 0) (constant_mem 4 0)
    (constant_mem 1 0)).2
  norm_num at this
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 25 by norm_num), Real.sqrt_nonneg 25]

/-- Entries of an oriented two-dimensional frame, in row-major order. -/
structure Frame where
  a : Model
  b : Model
  c : Model
  d : Model

/-- Affine interpolation of one rational frame entry at normalized endpoints −1 and 1. -/
def affine (a b : ℚ) : Model := exactPoly [(a+b)/2, (b-a)/2]

theorem eval_affine (a b : ℚ) (s : ℝ) :
    eval (affine a b).poly s = (a:ℝ) + ((1+s)/2)*((b:ℝ) - a) := by
  simp [affine, exactPoly]
  ring

/-- The affine frame is specified by its two actual endpoint matrices. -/
def Frame.ofEndpoints (a b : Fin 2 → Fin 2 → ℚ) : Frame :=
  ⟨affine (a 0 0) (b 0 0), affine (a 0 1) (b 0 1),
    affine (a 1 0) (b 1 0), affine (a 1 1) (b 1 1)⟩

/-- Signed polynomial numerator for outward traversal. -/
def directed (back : Bool) (p : Model) := if back then TaylorResidual.neg p else p

/-- Multiplicative sign of the outward traversal in geometric azimuth. -/
def sign (back : Bool) : ℝ := if back then -1 else 1

theorem directed_mem (back : Bool) {p : Model} {s n : ℝ} (h : p.Mem s n) :
    (directed back p).Mem s (sign back * n) := by
  cases back <;> simp [directed, sign, h, TaylorResidual.neg_mem h]

/-- Left multiplication by the adjugate, retaining the determinant in the denominator. -/
def transform (F : Format) (m : Frame) (r z den : Model) : Quotient :=
  ⟨F.add (F.mul m.d r) (F.mul (TaylorResidual.neg m.b) z),
   F.add (F.mul (TaylorResidual.neg m.c) r) (F.mul m.a z),
   F.mul (F.add (F.mul m.a m.d) (TaylorResidual.neg (F.mul m.b m.c))) den⟩

/-- Numerators are formed in the common clock before applying the adjugate. -/
def build (F : Format) (back : Bool) (k : ℚ) (m : Frame) (r z nr nz den : Model) : Quotient :=
  transform F m
    (TaylorResidual.numerator F k (directed back nr) den r)
    (TaylorResidual.numerator F k (directed back nz) den z) den

/-- Soundness for an arbitrary field numerator, reference polynomial, frame and signed clock. -/
theorem framed_defect {F : Format} {back : Bool} {k b x y l : ℚ} {grid : List ℚ}
    {m : Frame} {r z nr nz den : Model}
    (h : Accepts (build F back k m r z nr nz den) b x y l grid)
    {s nR nZ D A B C E : ℝ} (hs : |s| ≤ 1)
    (hnR : nr.Mem s nR) (hnZ : nz.Mem s nZ) (hD : den.Mem s D)
    (ha : m.a.Mem s A) (hb : m.b.Mem s B) (hc : m.c.Mem s C) (he : m.d.Mem s E) :
    let vr := sign back * (nR/D) - (k:ℝ) * eval (deriv r.poly) s
    let vz := sign back * (nZ/D) - (k:ℝ) * eval (deriv z.poly) s
    let det := A*E-B*C
    det * D ≠ 0 ∧ Real.sqrt (((E*vr - B*vz)/det)^2 + ((A*vz - C*vr)/det)^2) ≤ (b:ℝ) := by
  have rr := TaylorResidual.numerator_mem (F := F) k r hs (directed_mem back hnR) hD
  have rz := TaylorResidual.numerator_mem (F := F) k z hs (directed_mem back hnZ) hD
  have xx := F.add_mem hs (F.mul_mem hs he rr) (F.mul_mem hs (TaylorResidual.neg_mem hb) rz)
  have yy := F.add_mem hs (F.mul_mem hs (TaylorResidual.neg_mem hc) rr) (F.mul_mem hs ha rz)
  have dd := F.mul_mem hs (F.add_mem hs (F.mul_mem hs ha he)
    (TaylorResidual.neg_mem (F.mul_mem hs hb hc))) hD
  have hbound := h.sound hs xx yy dd
  simp only [← sub_eq_add_neg, neg_mul] at hbound
  have nonzero := hbound.1.ne'
  dsimp only
  refine ⟨nonzero, ?_⟩
  have hdet := left_ne_zero_of_mul nonzero
  have hden := right_ne_zero_of_mul nonzero
  convert hbound.2 using 2
  field_simp
  ring

/-- Central polynomial position in physical cylindrical coordinates. -/
noncomputable def position (r : Inputs) (s : ℝ) : DommaschkBounceField.State :=
  ![DommaschkKam.dkR0 + eval r.u.poly s, eval r.z.poly s]

/-- The actual outward-time derivative when the normalized clock has rate k. -/
noncomputable def velocity (r : Inputs) (k s : ℝ) : DommaschkBounceField.State :=
  ![k * eval (deriv r.u.poly) s, k * eval (deriv r.z.poly) s]

theorem position_derivative (r : Inputs) (k off t : ℝ) :
    HasDerivAt (fun t => position r (k*t-off)) (velocity r k (k*t-off)) t := by
  have hc : HasDerivAt (fun t : ℝ => k*t-off) k t := by
    simpa only [id_eq, mul_one] using (((hasDerivAt_id t).const_mul k).sub_const off)
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [position, velocity, mul_comm, Function.comp_def] using
      (((hasDerivAt_eval r.u.poly (k*t-off)).comp t hc).const_add DommaschkKam.dkR0)
  · simpa [position, velocity, mul_comm, Function.comp_def] using
      ((hasDerivAt_eval r.z.poly (k*t-off)).comp t hc)

/-- Exact inverse-frame velocity error using the four central entry polynomials. -/
noncomputable def pulled (m : Frame) (s : ℝ) (v : DommaschkBounceField.State) :
    DommaschkBounceField.State :=
  let a := eval m.a.poly s
  let b := eval m.b.poly s
  let c := eval m.c.poly s
  let d := eval m.d.poly s
  ![(d*v 0 - b*v 1)/(a*d-b*c), (a*v 1 - c*v 0)/(a*d-b*c)]

/-- An accepted slab controls the physical cylindrical flow at its central curve
throughout the certified harmonic and frame enclosures. -/
theorem physical {F : Format} {back : Bool} {k b x y l : ℚ} {grid : List ℚ}
    {m : Frame} {r : Inputs} {nr nz den : Model}
    (h : Accepts (build F back k m r.u r.z nr nz den) b x y l grid)
    (hNr : Blocks F r DommaschkKam.dnR nr) (hNz : Blocks F r DommaschkKam.dnZ nz)
    (hd : Blocks F r DommaschkKam.dD den) (t phase s : ℝ) (hs : |s| ≤ 1)
    (hr : 0 < position r s 0)
    (hi : r.Mem s (position r s 0 - DommaschkKam.dkR0) (position r s 1)
      (Real.cos (2 * (phase + sign back * t))) (Real.sin (2 * (phase + sign back * t))))
    (hm : 0 ≤ m.a.radius ∧ 0 ≤ m.b.radius ∧ 0 ≤ m.c.radius ∧ 0 ≤ m.d.radius) :
    let v := DommaschkBounceField.physicalFlow phase (sign back) t (position r s) - velocity r k s
    let w := pulled m s v
    Real.sqrt ((w 0)^2 + (w 1)^2) ≤ (b:ℝ) := by
  have own (a : Model) (ha : 0 ≤ a.radius) : a.Mem s (eval a.poly s) := by
    simpa only [Model.Mem, sub_self, abs_zero, Rat.cast_nonneg] using ha
  let field (p : DommaschkKam.DkPoly.SP) :=
    DommaschkBounceField.clockPoly phase (sign back) p (t, position r s)
  have D : den.Mem s (field DommaschkKam.dD) := hd.mem hs hi
  have hbound := framed_defect h hs
    (show nr.Mem s (field DommaschkKam.dnR) from hNr.mem hs hi)
    (show nz.Mem s (field DommaschkKam.dnZ) from hNz.mem hs hi) D
    (own _ hm.1) (own _ hm.2.1) (own _ hm.2.2.1) (own _ hm.2.2.2)
  have hD := right_ne_zero_of_mul hbound.1
  dsimp only
  rw [← DommaschkBounceField.ratio_eq_physical phase (sign back) t _ hr hD]
  exact hbound.2

end PlasmaLean.Design.FramedTaylorResidual
