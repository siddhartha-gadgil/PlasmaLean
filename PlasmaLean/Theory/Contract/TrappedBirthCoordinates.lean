/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Contract.TrappedBirthBand
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Lifting regular mirror heights to position, parallel velocity and magnetic moment -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Contract.TrappedBirthCoordinates
open Set MeasureTheory Fields Kinetic.GCLittlejohn

def energy (B : Space → Space) (m : ℝ) (p : GCBirth) : ℝ :=
  hamiltonian m p.2.2 B p.1 p.2.1

/-- Both signs of parallel velocity realize an interior birth of specified energy and height. -/
def lift (B : Space → Space) (m : ℝ) (x : Space) (e h : ℝ) (negative : Bool) : GCBirth :=
  let μ := e / h
  let v := Real.sqrt (2 * (e - μ * ‖B x‖) / m)
  (x, if negative then -v else v, μ)

theorem lift_values {B : Space → Space} {m e h : ℝ} {x : Space} (negative : Bool)
    (hm : 0 < m) (he : 0 < e) (strict : ‖B x‖ < h) :
    let p := lift B m x e h negative
    p.1 = x ∧ 0 < p.2.2 ∧ (if negative then p.2.1 < 0 else 0 < p.2.1) ∧
      energy B m p = e ∧ e / p.2.2 = h ∧ p.2.2 / e = 1 / h := by
  have hh := (norm_nonneg (B x)).trans_lt strict
  have μpos := div_pos he hh
  have split : e / h * h = e := div_mul_cancel₀ e hh.ne'
  have room : 0 < e - e / h * ‖B x‖ := by
    have := mul_lt_mul_of_pos_left strict μpos
    linarith
  have sqpos : 0 < 2 * (e - e / h * ‖B x‖) / m := by positivity
  have sq := Real.sq_sqrt sqpos.le
  have eq : m * (2 * (e - e / h * ‖B x‖) / m) / 2 + e / h * ‖B x‖ = e := by
    field_simp
    ring
  have inv : e / (e / h) = h := by field_simp
  have pitch : (e / h) / e = 1 / h := by field_simp
  cases negative <;> simp only [lift, Bool.false_eq_true, ↓reduceIte, energy, hamiltonian,
    neg_sq, sq, eq, inv, pitch, neg_lt_zero, true_and, and_true] <;>
    exact ⟨μpos, Real.sqrt_pos.mpr sqpos⟩

/-- Continuity of the Hamiltonian and the two quotients transports an open mirror
neighborhood to the exact contracted trapped reference in the five birth coordinates. -/
theorem mem_interior {B : Space → Space} {m : ℝ} {p : GCBirth} {S : Set GCBirth}
    {energies pitches : Set ℝ} (field : ContinuousAt (fun x => ‖B x‖) p.1)
    (supp : p ∈ interior S) (moment : 0 < p.2.2) (positive : 0 < energy B m p)
    (ener : energy B m p ∈ interior energies) (pitch : p.2.2 / energy B m p ∈ interior pitches)
    (mirror : (p.1, energy B m p / p.2.2) ∈
      interior {q : Space × ℝ | RegularMirrorBirth B q.1 q.2}) :
    p ∈ interior (trappedReference B m S energies pitches) := by
  have cx : ContinuousAt (fun q : GCBirth => q.1) p := continuous_fst.continuousAt
  have cv : ContinuousAt (fun q : GCBirth => q.2.1) p :=
    (continuous_fst.comp continuous_snd).continuousAt
  have cm : ContinuousAt (fun q : GCBirth => q.2.2) p :=
    (continuous_snd.comp continuous_snd).continuousAt
  have ce : ContinuousAt (energy B m) p :=
    (((continuousAt_const.mul (cv.pow 2)).div_const 2).add (cm.mul (field.comp cx)))
  have cp := cm.div ce positive.ne'
  have ch := cx.prodMk (ce.div cm moment.ne')
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [mem_interior_iff_mem_nhds.mp supp, cm.eventually_const_lt moment,
    ce.eventually_const_lt positive, ce (mem_interior_iff_mem_nhds.mp ener),
    cp (mem_interior_iff_mem_nhds.mp pitch), ch (mem_interior_iff_mem_nhds.mp mirror)]
    with q qs posμ posE en pi mir
  exact ⟨qs, posμ, posE, en, pi, mir⟩

theorem lift_mem_interior {B : Space → Space} {m e h : ℝ} {x : Space} (negative : Bool)
    {S : Set GCBirth} {energies pitches : Set ℝ} (hm : 0 < m) (he : 0 < e) (strict : ‖B x‖ < h)
    (field : ContinuousAt (fun x => ‖B x‖) x) (supp : lift B m x e h negative ∈ interior S)
    (ener : e ∈ interior energies) (pitch : 1 / h ∈ interior pitches)
    (mirror : (x, h) ∈ interior {q : Space × ℝ | RegularMirrorBirth B q.1 q.2}) :
    lift B m x e h negative ∈ interior (trappedReference B m S energies pitches) := by
  obtain ⟨atx, μpos, _, eq, atH, atP⟩ := lift_values (x := x) negative hm he strict
  apply mem_interior (p := lift B m x e h negative) (atx ▸ field) supp μpos
  · simpa only [eq] using he
  · simpa only [eq] using ener
  · simpa only [eq, atP] using pitch
  · simpa only [eq, atH, atx] using mirror

/-- A five-dimensional open subset with one realized point has positive mass for every
birth law charging nonempty open sets. -/
theorem positive_mass {B : Space → Space} {m : ℝ} {S : Set GCBirth} {E P : Set ℝ} {p : GCBirth}
    (μ : Measure GCBirth) [Measure.IsOpenPosMeasure μ]
    (here : p ∈ interior (trappedReference B m S E P)) :
    0 < μ (interior (trappedReference B m S E P)) := isOpen_interior.measure_pos μ ⟨p, here⟩

end PlasmaLean.Contract.TrappedBirthCoordinates
