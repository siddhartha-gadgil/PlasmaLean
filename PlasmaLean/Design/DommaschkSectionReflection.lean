/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkFramedTaylorResidual

/-! # Reflection of a section-zero trajectory and its moving-frame defect

Under simultaneous reversal of height and azimuth, the denominator and vertical
field numerator are even and the radial field numerator is odd. Reflection
therefore intertwines the forward and backward outward-time ODEs.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkSectionReflection
open DommaschkKam DommaschkKam.DkPoly DommaschkBounceField Real
open Certificates.QPoly Certificates.TrajectoryTaylorModel FramedTaylorResidual

/-- Parity of the total exponent of height and of the sine coordinate. -/
def parity (p : SP) (k : ℕ) : Bool := p.all fun m => (m.b+m.d)%2 == k

/-- The sparse parity test implies the corresponding real polynomial identity. -/
theorem evR_reflect {p : SP} {k : ℕ} (h : parity p k = true) (u z c s : ℝ) :
    evR u (-z) c (-s) p = (-1:ℝ)^k * evR u z c s p := by
  induction p with
  | nil => simp [evR]
  | cons m p ih =>
    obtain ⟨hm, hp⟩ : (m.b+m.d)%2 = k ∧ parity p k = true := by simpa [parity] using h
    have signpow : (-1:ℝ)^m.b * (-1:ℝ)^m.d = (-1:ℝ)^k := by
      rw [← pow_add, neg_one_pow_eq_pow_mod_two (m.b + m.d), hm]
    change (m.q:ℝ) * (u^m.a * (-z)^m.b * c^m.c * (-s)^m.d) + evR u (-z) c (-s) p =
      (-1:ℝ)^k * ((m.q:ℝ) * (u^m.a * z^m.b * c^m.c * s^m.d) + evR u z c s p)
    rw [ih hp, neg_pow, neg_pow, ← signpow]
    ring

private theorem den_even : parity dD 0 = true := by kernel_fact
private theorem radial_odd : parity dnR 1 = true := by kernel_fact
private theorem vertical_even : parity dnZ 0 = true := by kernel_fact

/-- The real parity identity at physical cylindrical positions. -/
theorem atPoint_reflect {p : SP} {k : ℕ} (h : parity p k = true) (R φ z : ℝ) :
    atPoint p R (-φ) (-z) = (-1:ℝ)^k * atPoint p R φ z := by
  simpa only [atPoint, mul_neg, cos_neg, sin_neg] using
    evR_reflect h (R-dkR0) z (cos (2*φ)) (sin (2*φ))

/-- Stellarator symmetry for all three true cylindrical candidate field components. -/
theorem field_reflect {R : ℝ} (hR : 0 < R) (φ z : ℝ) :
    cylBphi R (-φ) (-z) = cylBphi R φ z ∧ cylBR R (-φ) (-z) = -cylBR R φ z ∧
    cylBz R (-φ) (-z) = cylBz R φ z := by
  obtain ⟨Dp,Rp,Zp⟩ := field_id hR φ z
  obtain ⟨Dm,Rm,Zm⟩ := field_id hR (-φ) (-z)
  have D := atPoint_reflect den_even R φ z
  have N := atPoint_reflect radial_odd R φ z
  have Z := atPoint_reflect vertical_even R φ z
  rw [Dp, Dm, pow_zero, one_mul] at D
  rw [Rp, Rm, pow_one, neg_one_mul, ← mul_neg] at N
  rw [Zp, Zm, pow_zero, one_mul] at Z
  exact ⟨mul_left_cancel₀ (pow_ne_zero 7 hR.ne') D, mul_left_cancel₀ (pow_ne_zero 8 hR.ne') N,
    mul_left_cancel₀ (pow_ne_zero 8 hR.ne') Z⟩

/-- Reflection in the cylindrical midplane. -/
def reflect (p : State) : State := ![p 0, -p 1]

/-- Forward and backward physical flows are exactly conjugate on the zero section. -/
theorem flow_reflect (t : ℝ) (p : State) (hR : 0 < p 0) :
    physicalFlow 0 (-1) t (reflect p) = reflect (physicalFlow 0 1 t p) := by
  obtain ⟨d,r,z⟩ := field_reflect hR t (p 1)
  funext i
  fin_cases i <;> simp [physicalFlow, reflect, d,r,z, neg_div]

/-- A pair of central references with the same radius and opposite height. -/
structure CurvePair (f b : DommaschkBounceTaylor.Inputs) : Prop where
  radius : b.u.poly = f.u.poly
  height : b.z.poly = scale (-1) f.z.poly

theorem CurvePair.position_eq {f b} (h : CurvePair f b) (s : ℝ) :
    position b s = reflect (position f s) := by
  funext i
  fin_cases i <;> simp [position,reflect,h.radius,h.height]

private theorem deriv_neg (p : List ℚ) (s : ℝ) :
    eval (deriv (scale (-1) p)) s = -eval (deriv p) s := by
  have eq : eval (scale (-1) p) = fun x => -eval p x := by funext x; simp
  exact (eq ▸ hasDerivAt_eval (scale (-1) p) s).unique (hasDerivAt_eval p s).neg

theorem CurvePair.velocity_eq {f b} (h : CurvePair f b) (k s : ℝ) :
    velocity b k s = reflect (velocity f k s) := by
  funext i
  fin_cases i <;> simp [velocity,reflect,h.radius,h.height,deriv_neg]

/-- Equality of the entries after conjugation by the diagonal matrix (1,−1). -/
structure FramePair (f b : Frame) : Prop where
  aa : b.a.poly = f.a.poly
  bb : b.b.poly = scale (-1) f.b.poly
  cc : b.c.poly = scale (-1) f.c.poly
  dd : b.d.poly = f.d.poly

theorem FramePair.pulled_eq {f b : Frame} (h : FramePair f b) (s : ℝ) (v : State) :
    pulled b s (reflect v) = reflect (pulled f s v) := by
  funext i
  fin_cases i <;> simp [pulled,reflect,h.aa,h.bb,h.cc,h.dd]
  ring

private theorem reflect_sub (v w : State) : reflect v - reflect w = reflect (v - w) := by
  funext i
  fin_cases i <;> simp [reflect]
  ring

/-- The actual Euclidean residual agrees exactly on reflected references and frames,
so any proved forward bound can be retested against the backward row's own budget. -/
theorem defect_eq {f b : DommaschkBounceTaylor.Inputs} {mf mb : Frame}
    (p : CurvePair f b) (m : FramePair mf mb) (t k s : ℝ) (hR : 0 < position f s 0) :
    let vb := physicalFlow 0 (-1) t (position b s) - velocity b k s
    let vf := physicalFlow 0 1 t (position f s) - velocity f k s
    let wb := pulled mb s vb
    let wf := pulled mf s vf
    sqrt ((wb 0)^2 + (wb 1)^2) = sqrt ((wf 0)^2 + (wf 1)^2) := by
  dsimp only
  rw [p.position_eq, flow_reflect t _ hR, p.velocity_eq, reflect_sub, m.pulled_eq]
  simp [reflect]

/-- Reuse checked component bounds while recomputing the exact squared-budget inequality. -/
theorem retest {q : Quotient} {old new x y l : ℚ} {grid}
    (h : Accepts q old x y l grid) (hn : 0 ≤ new) (hs : x ^ 2 + y ^ 2 ≤ (new * l) ^ 2) :
    Accepts q new x y l grid :=
  ⟨h.xlow,h.xhigh,h.ylow,h.yhigh,h.denLow,h.positive,hn,hs⟩

end PlasmaLean.Design.DommaschkSectionReflection
