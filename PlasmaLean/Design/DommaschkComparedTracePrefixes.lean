/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.PairedPositionFrameObservables
public import PlasmaLean.Design.DommaschkCommonPilotObservables
public import PlasmaLean.Design.DommaschkFiniteRadialAction
public import PlasmaLean.Design.DommaschkPairedActionBirth

/-! # Paired observables on the calibrated pilot and a second physical birth -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkComparedTracePrefixes
open Set Certificates.PositionFrameSlabs DommaschkBounceField DommaschkMirrorLaunch
open DommaschkPairedActionProfiles DommaschkEndpointTraceFamily DommaschkPairedActionBirth
open DommaschkJacobian (euclideanFlow)
open Theory.KAM

/-- The short approach from birth only needs uniqueness on the first two signed
tubes, even when the field line continues well past them. -/
private theorem birth_on_path {T φ σ : ℝ} {a : ℝ → DommaschkBounceField.State} {y : ℝ → Plane}
    (wide : halfWidth ≤ T) (small : |φ| ≤ halfWidth) (unit : |σ| = 1)
    (clock : φ + σ * |φ| = 0) (start : y 0 = coordinates.symm (a |φ|))
    (approach : ∀ t ∈ Icc 0 |φ|, HasDerivWithinAt a (physicalFlow φ σ t (a t)) (Icc 0 |φ|) t)
    (ode : ∀ t ∈ Icc (-T) T, HasDerivWithinAt y (euclideanFlow 0 1 t (y t)) (Icc (-T) T) t)
    (regular : ∀ t ∈ window, 0 < y t 0 ∧ 0 < atPoint DommaschkKam.dD (y t 0) t (y t 1)) :
    y φ = coordinates.symm (a 0) := by
  let k := fun t : ℝ => φ + σ * t
  have narrow : MapsTo k (Icc 0 |φ|) window := by
    intro t ht
    apply abs_le.mp
    have eq : k t = σ * (t - |φ|) := by dsimp [k]; linarith only [clock, mul_sub σ t |φ|]
    rw [eq, abs_mul, unit, one_mul, abs_of_nonpos (sub_nonpos.mpr ht.2)]
    linarith only [small, ht.1]
  have contains : MapsTo k (Icc 0 |φ|) (Icc (-T) T) :=
    fun t ht => Icc_subset_Icc (neg_le_neg wide) wide (narrow ht)
  have eq : EqOn a (fun t => coordinates (y (k t))) (Icc 0 |φ|) := by
    apply Fields.ode_eqOn_of_terminal approach
    · intro t ht
      have dy := coordinates.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt
        (k t) (ode (k t) (contains ht))
      have dy' : HasDerivWithinAt (fun u => coordinates (y u))
          (physicalFlow 0 1 (k t) (coordinates (y (k t)))) (Icc (-T) T) (k t) :=
        dy.congr_deriv (coordinates.apply_symm_apply _)
      have dk : HasDerivAt k σ t := by
        simpa only [k, id_eq, mul_one] using ((hasDerivAt_id t).const_mul σ).const_add φ
      apply (dy'.scomp t dk.hasDerivWithinAt contains).congr_deriv
      ext i
      fin_cases i <;> simp [physicalFlow, k]
    · intro t ht
      have reg := regular _ (narrow ht)
      exact DommaschkSignedBirthApproach.physical_smooth φ σ _ reg.1 reg.2.ne'
    · simp only [k, clock, start, coordinates.apply_symm_apply]
  apply coordinates.injective
  simpa only [k, mul_zero, add_zero, coordinates.apply_symm_apply] using
    (eq (show 0 ∈ Icc 0 |φ| from ⟨le_rfl, abs_nonneg _⟩)).symm

def ComparedRows (k : ℕ) (inner outer : Checkpoint) : Prop :=
  OnPairedTubes Compared (MirrorEndpoint.start .q0r470) (MirrorEndpoint.start .q0r478) 0
    (inner.forwardRows.take k) (outer.forwardRows.take k) ∧
  OnPairedTubes (fun t => Compared (-t)) (MirrorEndpoint.start .q0r470)
    (MirrorEndpoint.start .q0r478) 0 (inner.backwardRows.take k) (outer.backwardRows.take k)

/-- The calibrated pilot and the second birth have independent exits. On their common
prefix, compare field and arclength at the same physical azimuth in both directions. -/
theorem compare_birth {k : ℕ} {ci co : Checkpoint} {uC zC uA zA : FA}
    {φ : ℝ} {x : Plane} {y : ℝ → Plane}
    (inner : DommaschkSignedObservable.Path ci.length ci.forwardExit ci.backwardExit
      ci.forwardRows ci.backwardRows x y)
    (outer : co.Passage .q0r478 uC zC uA zA φ) (small : |φ| ≤ halfWidth)
    (duration : 1 ≤ co.length) (pos : 0 < k)
    (hf : k ≤ ci.forwardRows.length) (hb : k ≤ ci.backwardRows.length)
    {f b : Step} {fs bs : List Step} (front : co.forwardRows = f :: fs)
    (back : co.backwardRows = b :: bs) (rf : RegularRow false f) (rb : RegularRow true b)
    (cert : ComparedRows k ci co) :
    ∃ z : ℝ → Plane, z φ = coordinates.symm (birth uC zC uA zA (239/500) φ) ∧
      z (-(co.length : ℝ) / 64) ∈ stateSet co.backwardExit ∧
      z (co.length / 64) ∈ stateSet co.forwardExit ∧
      (∀ t ∈ Icc (-(co.length : ℝ) / 64) (co.length / 64), HasDerivWithinAt z
        (euclideanFlow 0 1 t (z t)) (Icc (-(co.length : ℝ) / 64) (co.length / 64)) t) ∧
      ∀ t ∈ Icc (-(k : ℝ) / 64) (k / 64), Compared t (y t) (z t) := by
  obtain ⟨σ,a,unit,clock,src,approach,z,start,be,fe,ode,ft,bt⟩ := outer
  simp only [MirrorEndpoint.opposite, azimuth, Bool.false_eq_true, ↓reduceIte, sub_zero] at *
  have reg (t : ℝ) (ht : t ∈ window) :
      0 < z t 0 ∧ 0 < atPoint DommaschkKam.dD (z t 0) t (z t 1) := by
    rcases le_total 0 t with h | h
    · have localTime : t ∈ Icc 0 halfWidth := ⟨h, ht.2⟩
      exact rf (prev := MirrorEndpoint.start .q0r478) localTime
        (ft _ (by rw [front]; exact List.mem_cons_self) t (by simpa [physicalSlab] using localTime))
    · have localTime : -t ∈ Icc 0 halfWidth := ⟨neg_nonneg.mpr h, by linarith [ht.1]⟩
      simpa only [↓reduceIte, neg_neg] using
        rb (prev := MirrorEndpoint.start .q0r478) localTime
          (bt _ (by rw [back]; exact List.mem_cons_self) (-t)
            (by simpa [physicalSlab] using localTime))
  have wide : halfWidth ≤ (co.length : ℝ) / 64 := by
    have size : (1 : ℝ) ≤ co.length := by exact_mod_cast duration
    unfold halfWidth
    linarith
  have birthEq := birth_on_path wide small unit clock start approach ode reg
  refine ⟨z, ?_, by simpa only [neg_div] using be, fe, by simpa only [neg_div] using ode, ?_⟩
  · rw [birthEq, src]
    congr 2
    norm_num [MirrorEndpoint.radius]
  have usable {rs : List Step} (fit : k ≤ rs.length) : (rs.take k).length = k := by
    simpa using min_eq_left fit
  have nonempty {rs : List Step} (fit : k ≤ rs.length) : rs.take k ≠ [] := by
    intro h
    have len := usable fit
    rw [h] at len
    simp at len
    omega
  have forward := cert.1.on_nonempty_prefix (moreR := ci.forwardRows.drop k)
    (moreQ := co.forwardRows.drop k) (x := y) (y := z) (nonempty hf)
    (by simpa only [List.take_append_drop] using inner.forward)
    (by simpa only [List.take_append_drop] using ft)
  have backward := cert.2.on_nonempty_prefix (moreR := ci.backwardRows.drop k)
    (moreQ := co.backwardRows.drop k) (x := fun t => y (-t)) (y := fun t => z (-t)) (nonempty hb)
    (by simpa only [List.take_append_drop] using inner.backward)
    (by simpa only [List.take_append_drop] using bt)
  rw [usable hf, zero_add] at forward
  rw [usable hb, zero_add] at backward
  intro t ht
  rcases le_total 0 t with h | h
  · exact forward _ ⟨h, ht.2⟩
  · simpa only [neg_neg] using backward (-t) ⟨neg_nonneg.mpr h, by linarith [ht.1]⟩

open Kinetic.MirrorActionEnvelope Kinetic.MirrorHeightAction DommaschkMirrorBandFlightIdentity
open DommaschkMirrorBandAction (Heights)

/-- Comparing the 325 physical slabs each way suffices for every shifted height in the pilot
band. The second first well may extend beyond that comparison window. -/
theorem increment_of_compared {y z : ℝ → Plane} {φ h L R : ℝ}
    (times : DommaschkActionFlightFloor.TimeBounds φ y)
    (test : DommaschkFiniteRadialAction.PairTest y)
    (full : ∀ t ∈ Icc (-bound) bound, Compared t (y t) (z t))
    (h0 : h ∈ Heights) (h1 : h + 1 / 18000 ∈ Heights)
    (outer : LaunchWell (profile z) 0 h L R)
    (field : ContinuousOn (profile z) (Icc L R)) (arc : ContinuousOn (density z) (Icc L R))
    (nonneg : ∀ t ∈ Icc L R, 0 ≤ density z t) :
    ∃ l r, LaunchWell (profile y) 0 (h + 1 / 18000) l r ∧ L ≤ l ∧ r ≤ R ∧
      1 / 375 < action (profile z) (density z) L R h -
        DommaschkActionHeightInverse.ambient y h := by
  obtain ⟨l,hl,r,hr,_,base,_⟩ := times _ h1
  refine ⟨l,r,base,test h h0 h1 l r base (profile z) (density z) L R outer field arc nonneg ?_⟩
  intro t ht
  have cmp := full t ⟨hl.1.le.trans ht.1.le, ht.2.le.trans hr.2.le⟩
  exact ⟨cmp.2.2.2, cmp.2.2.1⟩

end PlasmaLean.Design.DommaschkComparedTracePrefixes
