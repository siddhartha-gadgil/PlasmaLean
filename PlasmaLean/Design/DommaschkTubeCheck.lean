/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.PositionFrameTube
public import PlasmaLean.Design.DommaschkSignedTraceDomain

/-!
# Executable checks for the tube of a chain of position-frame slabs

Two Boolean checkers on lists of slab records, with soundness theorems feeding
`Certificates.PositionFrameTube`.

* `radiiCheck rows β` checks a list `β` of backward radii, in units of 2⁻⁸⁰ and with one more
  entry than `rows`; `radii_of_check` turns it into `PositionFrameTube.Radii`.
* `trialPacked r` checks that the trial ellipsoid of the record `r`, enlarged from the ranges
  of the reference polynomials, lies in the cylindrical envelope
  `DommaschkSignedTraceDomain.Region`; `region_of_trial` is the statement for one slab and
  `region_of_outer` the statement for the outer tube of a chain.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkTubeCheck

open Certificates Certificates.PositionFrameSlabs Certificates.TrajectoryTaylorModel
open Certificates.PositionFrameTube DommaschkSignedTraceDomain Set

/-! ### Backward radii -/

/-- Backward radii in units of 2⁻⁸⁰: `β` has one more entry than `rows`. For the record `r`
between the radii `b₀` and `b₁`, the radius after removing the reference jump is
`b₀ - r.jumpBound`; it must be below the trial radius and dominate `b₁` propagated back
over the slab. -/
def radiiCheck : List Step → List ℕ → Bool
  | [], _ => true
  | r :: rs, b₀ :: b₁ :: bs =>
    let g := max 0 r.mu
    Nat.ble r.jumpBound b₀ && leQ 0 r.defect && ltQ g 64 &&
      leQ (64 * b₁ + 2 ^ 80 * r.defect) ((b₀ - r.jumpBound : ℕ) * (64 - g)) &&
      (b₀ - r.jumpBound).blt r.trial && radiiCheck rs (b₁ :: bs)
  | _ :: _, _ => false

/-- The conditions checked on the first record. -/
theorem radiiCheck_cons {r : Step} {rs : List Step} {b₀ b₁ : ℕ} {bs : List ℕ}
    (h : radiiCheck (r :: rs) (b₀ :: b₁ :: bs) = true) :
    r.jumpBound ≤ b₀ ∧ 0 ≤ (r.defect : ℝ) ∧ max 0 (r.mu : ℝ) / 64 < 1 ∧
      ((b₁ : ℝ) / 2 ^ 80 + r.defect / 64) / (1 - max 0 (r.mu : ℝ) / 64) ≤
        ((b₀ : ℝ) - r.jumpBound) / 2 ^ 80 ∧
      ((b₀ : ℝ) - r.jumpBound) / 2 ^ 80 < (r.trial : ℝ) / 2 ^ 80 ∧
      radiiCheck rs (b₁ :: bs) = true := by
  simp only [radiiCheck, Bool.and_eq_true, leQ_true, ltQ_true, Nat.blt_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨jump, defect⟩, rate⟩, propagated⟩, trial⟩, tail⟩ := h
  have rate' : max 0 (r.mu : ℝ) < 64 := by exact_mod_cast rate
  have sub : ((b₀ - r.jumpBound : ℕ) : ℝ) = (b₀ : ℝ) - r.jumpBound := Nat.cast_sub jump
  have bound : 64 * (b₁ : ℝ) + 2 ^ 80 * (r.defect : ℝ) ≤
      ((b₀ : ℝ) - r.jumpBound) * (64 - max 0 (r.mu : ℝ)) := by
    rw [← sub]
    exact_mod_cast propagated
  have trial' : ((b₀ - r.jumpBound : ℕ) : ℝ) < r.trial := by exact_mod_cast trial
  rw [sub] at trial'
  refine ⟨jump, by exact_mod_cast defect, by linarith, ?_, ?_, tail⟩
  · apply (div_le_iff₀ (by linarith)).mpr
    nlinarith only [bound]
  · gcongr

/-- **Soundness of the radius check.** The checked list gives backward radii, with the radius
after the backward step obtained by removing the recorded jump. -/
theorem radii_of_check {rows : List Step} {β : List ℕ} (h : radiiCheck rows β = true) :
    PositionFrameTube.Radii rows (fun k => (β.getD k 0 : ℝ) / 2 ^ 80)
      (fun k => ((β.getD k 0 : ℝ) - (PositionFrameTube.rowAt rows k).jumpBound) / 2 ^ 80) := by
  induction rows generalizing β with
  | nil => constructor <;> exact fun k hk => absurd hk (Nat.not_lt_zero k)
  | cons r rs ih =>
    match β, h with
    | b₀ :: b₁ :: bs, h =>
      obtain ⟨-, defect, rate, back, trial, tail⟩ := radiiCheck_cons h
      have rest := ih tail
      constructor
      · intro k _
        positivity
      · rintro (_ | k) hk
        · exact defect
        · exact rest.defect k (Nat.lt_of_succ_lt_succ hk)
      · rintro (_ | k) hk
        · exact rate
        · exact rest.rate k (Nat.lt_of_succ_lt_succ hk)
      · rintro (_ | k) hk
        · exact back
        · exact rest.back k (Nat.lt_of_succ_lt_succ hk)
      · rintro (_ | k) hk
        · exact trial
        · exact rest.trial k (Nat.lt_of_succ_lt_succ hk)
      · rintro (_ | k) hk
        · change ((b₀ : ℝ) - r.jumpBound) / 2 ^ 80 + r.jumpBound / 2 ^ 80 ≤ (b₀ : ℝ) / 2 ^ 80
          rw [← add_div, sub_add_cancel]
        · exact rest.jump k (Nat.lt_of_succ_lt_succ hk)

/-! ### The trial tube in the cylindrical envelope -/

/-- The trial ellipsoid of the record, enlarged from the reference polynomial ranges, lies in
`Region`. -/
def trialPacked (r : Step) : Bool :=
  leQ (r.op * r.trial / 2 ^ 80 + magnitude (difference (polynomial r 0) [15 / 16])) (1 / 16) &&
  leQ (r.op * r.trial / 2 ^ 80 + magnitude (difference (polynomial r 1) [0])) (5 / 64)

/-- **One slab.** A point within the trial radius of the reference, measured in the moving
frame of a record that passes `trialPacked`, lies in the cylindrical envelope. -/
theorem region_of_trial {lim : Limits} {s : State} {r : Step} {a t : ℝ} {x : Plane}
    (geo : geometry lim s r = true) (check : trialPacked r = true)
    (ht : t ∈ Icc a (a + 1 / 64))
    (hx : ‖(moving s r a t).symm (x - reference a r t)‖ ≤ r.trial / (2 : ℝ) ^ 80) :
    Region x := by
  obtain ⟨_, _, _, _, _, op0, _⟩ := geometry_sound geo
  have physical : ‖x - reference a r t‖ ≤ (r.op : ℝ) * (r.trial / (2 : ℝ) ^ 80) := by
    have h := ((moving s r a t).toContinuousLinearMap.le_opNorm
      ((moving s r a t).symm (x - reference a r t))).trans
      (mul_le_mul (frame_op_norm geo (abs_coord_le ht)) hx (norm_nonneg _) op0)
    simpa using h
  have input (j : Fin 2) : (⟨polynomial r j, r.op * r.trial / 2 ^ 80⟩ : Model).Mem
      (coord a t) (x j) := by
    have e : |x j - reference a r t j| ≤ (r.op : ℝ) * (r.trial / (2 : ℝ) ^ 80) :=
      (PiLp.norm_apply_le (x - reference a r t) j).trans physical
    change |x j - QPoly.eval (polynomial r j) (coord a t)| ≤ _ at e
    simpa only [Model.Mem, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_pow,
      Rat.cast_ofNat, mul_div_assoc] using e
  obtain ⟨rad, vert⟩ := Bool.and_eq_true_iff.mp check
  have r0 := enclose (c := ⟨[15 / 16], 1 / 16⟩) (abs_coord_le ht) (input 0) (leQ_true.mp rad)
  have r1 := enclose (c := ⟨[0], 5 / 64⟩) (abs_coord_le ht) (input 1) (leQ_true.mp vert)
  norm_num [Model.Mem, QPoly.eval_cons, QPoly.eval_nil, abs_le] at r0 r1
  exact ⟨⟨by linarith [r0.1], by linarith [r0.2]⟩, abs_le.mpr r1⟩

/-- **The chain.** If every record passes `trialPacked`, the outer tube of the chain lies in
the cylindrical envelope at every time. -/
theorem region_of_outer {s₀ : State} {a : ℝ} {rows : List Step}
    (geo : PositionFrameTube.Geo s₀ rows) (check : rows.all trialPacked = true) {t : ℝ}
    {x : Plane} (hx : x ∈ PositionFrameTube.outer s₀ a rows t) :
    DommaschkSignedTraceDomain.Region x := by
  obtain ⟨k, hk, ht, hg⟩ := hx
  rw [time_succ] at ht
  have row : rowAt rows k ∈ rows := by
    rw [rowAt, List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  exact region_of_trial (geo.at hk) (List.all_eq_true.mp check _ row) ht hg

/-! ### Sanity checks -/

/-- The stationary record has trial radius one unit and no jump, so the zero radii are the
only ones accepted. -/
theorem radiiCheck_stationary : radiiCheck [stationary] [0, 0] = true := by
  with_unfolding_all rfl

/-- A list of radii without an entry for the end of the last slab is rejected. -/
theorem radiiCheck_short : radiiCheck [stationary] [0] = false := by
  with_unfolding_all rfl

/-- A radius equal to the trial radius is rejected. -/
theorem radiiCheck_trial : radiiCheck [stationary] [1, 0] = false := by
  with_unfolding_all rfl

/-- The empty chain is accepted with any list of radii. -/
theorem radiiCheck_nil (β : List ℕ) : radiiCheck [] β = true := rfl

/-- The stationary record placed at the centre `(15/16, 0)` of the envelope. -/
def centred : Step := { stationary with px := 15 * 2 ^ 76 :: List.replicate 7 0 }

/-- The centred stationary record passes the envelope check. -/
theorem trialPacked_centred : trialPacked centred = true := by
  with_unfolding_all rfl

/-- The stationary record sits at the origin, outside the envelope, and is rejected. -/
theorem trialPacked_stationary : trialPacked stationary = false := by
  with_unfolding_all rfl

/-- Non-vacuity of `region_of_outer`: the reference point of the centred record lies in the
envelope. -/
theorem centred_region (a : ℝ) : Region (reference a centred a) := by
  have geo : Geo (next centred) [centred] := ⟨by with_unfolding_all rfl, trivial⟩
  refine region_of_outer (a := a) (t := a) geo (by with_unfolding_all rfl)
    ⟨0, Nat.zero_lt_one, ?_, ?_⟩
  · rw [time_succ, time_zero]
    exact ⟨le_rfl, by linarith⟩
  · change ‖(frameAt (next centred) a [centred] 0 a).symm
      (reference a centred a - reference (time a 0) (rowAt [centred] 0) a)‖ ≤ _
    rw [time_zero]
    change ‖(frameAt (next centred) a [centred] 0 a).symm
      (reference a centred a - reference a centred a)‖ ≤ _
    rw [sub_self, map_zero, norm_zero]
    positivity

end PlasmaLean.Design.DommaschkTubeCheck
