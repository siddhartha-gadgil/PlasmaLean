/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkGroupedMirrorModels
public import PlasmaLean.Design.DommaschkEndpointTraceFamily
public import PlasmaLean.Certificates.PositionFrameObservables

/-! # A shared submirror enclosure at the opposite QA2R section -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkOppositeMirrorExclusion
open Certificates PositionFrameSlabs TrajectoryTaylorModel DommaschkGroupedMirrorModels
open DommaschkMirrorTubeCrossing DommaschkMirrorEndpointSign Set Real

/-- Coordinate radii belong to each original signed row. Reflected backward heights and
opposite-section phases can therefore be compared to the same shared field model. -/
structure FitsRow {i : ℕ} (p : TrajectoryHarmonicPacket.Packet i) (back : Bool)
    (r : Step) (a b : ℚ) (g : Group) : Prop where
  clock : |a| + |b| ≤ 1
  radial : Fits a b (raw false r 0) g.radial
  height : Fits a b (raw back r 1) g.height
  cosine : Fits a b (TrajectoryTrig.negative ((p false 0).model false)) g.cosine
  sine : Fits a b (TrajectoryTrig.negative ((p false 0).model true)) g.sine
  center : magnitude (difference (polynomial r 0) [1]) ≤ 1 / 2
  error : r.physicalOut ≤ 2 ^ 78

private theorem neg_mem {m : Model} {s x : ℝ} (mem : m.Mem s x) :
    (TrajectoryTrig.negative m).Mem s (-x) := by
  change |-x - QPoly.eval (QPoly.scale (-1) m.poly) s| ≤ _
  rw [QPoly.eval_scale]
  simp only [Rat.cast_neg, Rat.cast_one, neg_one_mul, neg_sub_neg]
  rw [abs_sub_comm]
  exact mem

private theorem coord_mem {r : Step} {prev : State} {a t : ℝ} {x : Plane}
    (inside : x ∈ (physicalSlab prev r a).tube t) (back : Bool) (k : Fin 2) :
    (raw back r k).Mem (coord a t) (if back then -(x k) else x k) := by
  have h := coordinate inside k
  change |x k - QPoly.eval (polynomial r k) (coord a t)| ≤ _ at h
  cases back
  · simpa [raw, Model.Mem] using h
  · change (TrajectoryTrig.negative (raw false r k)).Mem (coord a t) (-(x k))
    exact neg_mem (by simpa [raw, Model.Mem] using h)

set_option maxRecDepth 8192 in
theorem FitsRow.below {i : ℕ} {p : TrajectoryHarmonicPacket.Packet i} {back : Bool}
    {r : Step} {a b : ℚ} {g : Group} (h : FitsRow p back r a b g) {H : ℝ} (below : g.Below H)
    {prev : State} {t : ℝ} {x : Plane} (ht : t ∈ Icc ((i : ℝ) / 64) ((i + 1 : ℝ) / 64))
    (hx : x ∈ (physicalSlab prev r (i / 64)).tube t) :
    strength (π / 2 + if back then -t else t) x < H := by
  have row : t ∈ Icc ((i : ℝ) / 64) ((i : ℝ) / 64 + 1 / 64) := by
    rwa [show (i : ℝ) / 64 + 1 / 64 = (i + 1 : ℝ) / 64 by ring]
  have hs := abs_coord_le row
  have cw : coord (i / 64) t = 128 * t-(2*i + 1 : ℝ) := by unfold coord; ring
  have box : |(a : ℝ) + b * coord (i / 64) t| ≤ 1 := calc
    _ ≤ |(a : ℝ)| + |(b : ℝ)| * |coord (i / 64) t| := by
      simpa [abs_mul] using abs_add_le (a : ℝ) ((b : ℝ) * coord (i / 64) t)
    _ ≤ |(a : ℝ)| + |(b : ℝ)| :=
      add_le_add le_rfl (mul_le_of_le_one_right (abs_nonneg _) hs)
    _ ≤ 1 := by exact_mod_cast h.clock
  have R := DommaschkMirrorBracketSlab.positive_radius row hx h.center h.error
  have cs : ((p false 0).model false).Mem (coord (i / 64) t) (cos (2 * t)) := by
    simpa [cw,TrajectoryTrig.wave] using TrajectoryHarmonicPacket.physical p false 0 false ht
  have sn : ((p false 0).model true).Mem (coord (i / 64) t) (sin (2 * t)) := by
    simpa [cw,TrajectoryTrig.wave] using TrajectoryHarmonicPacket.physical p false 0 true ht
  let θ := if back then t - π / 2 else π / 2 + t
  have waves : cos (2 * θ) = -cos (2 * t) ∧ sin (2 * θ) = -sin (2 * t) := by
    cases back <;> simp only [θ, Bool.false_eq_true, ↓reduceIte]
    · rw [show 2 * (π / 2 + t) = π + 2 * t by ring]
      simp [cos_add, sin_add]
    · rw [show 2 * (t - π / 2) = 2 * t - π by ring]
      simp [cos_sub, sin_sub]
  have val := below (t := θ) box R (h.radial.mem hs (coord_mem hx false 0))
    (h.height.mem hs (coord_mem hx back 1)) (waves.1.symm ▸ h.cosine.mem hs (neg_mem cs))
    (waves.2.symm ▸ h.sine.mem hs (neg_mem sn))
  cases back
  · exact val
  · have symmetry := strength_reflected R (t - π / 2) (-(x 1))
    rw [neg_neg, show -(t - π / 2) = π / 2 + -t by ring] at symmetry
    exact symmetry.trans_lt val

open DommaschkMirrorLaunch DommaschkEndpointSignedTrace DommaschkEndpointTraceFamily
open DommaschkBounceField
open DommaschkJacobian (euclideanFlow)

/-- A true trajectory reached by the physical approach from birth, with both original exits,
the complete signed ODE, and a strict field-strength bound on a nominated initial segment. -/
def SubmirrorBirth (c : Checkpoint) (e : MirrorEndpoint) (k : ℕ) (H : ℝ)
    (uC zC uA zA : Theory.KAM.FA) (φ : ℝ) : Prop :=
  let phase := azimuth e.opposite
  let duration := |φ - phase|
  let T : ℝ := c.length / 64
  ∃ (s : ℝ) (a : ℝ → DommaschkBounceField.State) (y : ℝ → Plane),
    |s| = 1 ∧ φ + s * duration = phase ∧ a 0 = birth uC zC uA zA e.radius φ ∧
    (∀ t ∈ Icc 0 duration, HasDerivWithinAt a (physicalFlow φ s t (a t)) (Icc 0 duration) t) ∧
    y 0 = coordinates.symm (a duration) ∧ y (-T) ∈ stateSet c.backwardExit ∧
    y T ∈ stateSet c.forwardExit ∧
    (∀ t ∈ Icc (-T) T, HasDerivWithinAt y (euclideanFlow phase 1 t (y t)) (Icc (-T) T) t) ∧
    ∀ t ∈ Icc (-(k : ℝ) / 64) (k / 64), strength (phase + t) (y t) < H

theorem from_passage {c : Checkpoint} {e : MirrorEndpoint} {k : ℕ} {H φ : ℝ}
    {uC zC uA zA : Theory.KAM.FA} (path : c.Passage e uC zC uA zA φ)
    (positive : 0 < k) (fitsF : k ≤ c.forwardRows.length) (fitsB : k ≤ c.backwardRows.length)
    (fr : OnTubes (fun t x => strength (azimuth e.opposite + t) x < H)
      e.start 0 (c.forwardRows.take k))
    (br : OnTubes (fun t x => strength (azimuth e.opposite + -t) x < H)
      e.start 0 (c.backwardRows.take k)) : SubmirrorBirth c e k H uC zC uA zA φ := by
  obtain ⟨s,a,hs,clock,start,approach,y,ys,ye,yf,ode,ft,bt⟩ := path
  refine ⟨s,a,y,hs,clock,start,approach,ys,ye,yf,ode,?_⟩
  have size {rs : List Step} (fits : k ≤ rs.length) : (rs.take k).length = k := by
    simpa using min_eq_left fits
  have ne {rs : List Step} (fits : k ≤ rs.length) : rs.take k ≠ [] := by
    intro eq
    have h := size fits
    rw [eq] at h
    simp at h
    omega
  have plus := fr.on_nonempty_prefix (post := c.forwardRows.drop k) (y := y) (ne fitsF)
    (by simpa only [List.take_append_drop] using ft)
  have minus := br.on_nonempty_prefix (post := c.backwardRows.drop k) (y := fun t => y (-t))
    (ne fitsB) (by simpa only [List.take_append_drop] using bt)
  rw [size fitsF, zero_add] at plus
  rw [size fitsB, zero_add] at minus
  intro t ht
  rcases le_total 0 t with pos | neg
  · exact plus t ⟨pos, ht.2⟩
  · simpa only [neg_neg] using minus (-t) ⟨neg_nonneg.mpr neg, by linarith [ht.1]⟩

end PlasmaLean.Design.DommaschkOppositeMirrorExclusion
