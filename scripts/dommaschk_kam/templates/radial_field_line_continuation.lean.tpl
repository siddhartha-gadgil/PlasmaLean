module
public import TopHeightSecantCache.DommaschkTopHeightSecantSUFFIX
public import PlasmaLean.Design.DommaschkRadialFamilyContinuity
public import PlasmaLean.Design.DommaschkRadialRibbonEntry

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkRadialFlowOnSUFFIX
open Set Certificates.PositionFrameSlabs DommaschkMirrorLaunch
open DommaschkLowerActionPath (regions)
open DommaschkEndpointMirrorBranch DommaschkQ0R478MirrorBranch327 DommaschkPhaseZeroRegularBirth
open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2
open DommaschkCommonEndpointTracesSUFFIX (checkpoint all_from_entry)
open DommaschkRadialFamilyContinuity DommaschkRadialActionAlternative DommaschkNativeWellAction
open DommaschkTopHeightSecantSUFFIX (UpperSecant)
set_option maxHeartbeats 3200000
set_option maxRecDepth 65536
set_option linter.style.longLine false

/-- The remaining through-going physical paths and three strict strength signs on each label. -/
def FromRadialPassages (uC zC uA zA : FA) (φ : ℝ) : Prop :=
  ∀ Y : Radius → ℝ → Plane,
    (∀ u, Y u φ = coordinates.symm (birth uC zC uA zA u φ)) →
    (∀ u, Enclosed (Y u) (-(331/64)) (331/64)) →
    (∀ u, field (Y u) 0 < level) → (∀ u, level < field (Y u) (-(331/64))) →
    (∀ u, level < field (Y u) (331/64)) → Alternative Y

theorem from_entries {uC zC uA zA : FA} {φ : ℝ} (small : |φ| ≤ 1/2^19)
    (entryI : SectionEntry .q0r470 uC zC uA zA φ) (entryO : SectionEntry .q0r478 uC zC uA zA φ) :
    FromRadialPassages uC zC uA zA φ := by
  obtain ⟨sign, approach, unit, clock, start, ode, y, ys, ye, yf, dy, ft, bt⟩ :=
    all_from_entry .q0r470 entryI
  simp only [MirrorEndpoint.opposite, azimuth, Bool.false_eq_true, ↓reduceIte, sub_zero] at *
  have p : DommaschkSignedObservable.Path (checkpoint .q0r470).length
      (checkpoint .q0r470).forwardExit (checkpoint .q0r470).backwardExit
      (checkpoint .q0r470).forwardRows (checkpoint .q0r470).backwardRows
      (coordinates.symm (approach |φ|)) y :=
    ⟨ys, by simpa only [neg_div] using ye, yf, by simpa only [neg_div] using dy, ft, bt⟩
  have birth_eq : approach 0 = birth uC zC uA zA (47/100) φ := by
    convert start using 1
    norm_num [MirrorEndpoint.radius]
  have bornI := DommaschkSignedBirthApproach.birth_position p unit clock small birth_eq ode
    (by change 0 < 391; norm_num) (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl
  have obs : DommaschkCalibratedFamilySUFFIX.Observed φ y := by
    apply DommaschkCalibratedFamilySUFFIX.on_326 small (x := coordinates.symm (approach |φ|))
    have pre := p.take_through (i := 325) (by change 325 < 391; norm_num)
      (by change 325 < 391; norm_num) (by change 325 < 391; norm_num)
    with_unfolding_all exact pre
  obtain ⟨z,bornO,signed,_⟩ := DommaschkQ0R478RegularBirths.from_passage
    (extraF := (checkpoint .q0r478).forwardRows.drop 327) (extraB := (checkpoint .q0r478).backwardRows.drop 327)
    small (all_from_entry .q0r478 entryO) (by change 327/64 < (OUTER_LENGTH:ℝ)/64; norm_num)
    rfl rfl (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
  obtain ⟨_,l,hl,r,hr,L,hL,R,hR,innerWell,outerWell,_,_,low,high,_⟩ :=
    DommaschkTopHeightSecantSUFFIX.both_on_paths obs p signed
  have pilot := signed_of_clock p p.forward p.backward
  have reg := DommaschkSignedTraceDomain.on_path p (by change 0 < 391; norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl
  have py : Enclosed y (-(327/64)) (327/64) := by
    constructor <;> intro t ht
    · have inside : t ∈ Ioo (-(391/64)) (391/64) := ⟨by linarith [ht.1],by linarith [ht.2]⟩
      exact (pilot.ode t (Ioo_subset_Icc_self inside)).hasDerivAt (Icc_mem_nhds inside.1 inside.2)
    · apply reg
      change -(391:ℝ)/64 ≤ t ∧ t ≤ 391/64
      exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have front := signed.forward
  have rear := signed.backward
  rw [show (checkpoint .q0r478).forwardRows = fwdRows ++ (checkpoint .q0r478).forwardRows.drop 327 by with_unfolding_all rfl] at front
  rw [show (checkpoint .q0r478).backwardRows = backRows ++ (checkpoint .q0r478).backwardRows.drop 327 by with_unfolding_all rfl] at rear
  have ro := regions front.prefix rear.prefix (n := 327) (by norm_num) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) DommaschkQ0R478PolynomialFirstWell.forward_regular
    DommaschkQ0R478PolynomialFirstWell.backward_regular
  have pz : Enclosed z (-(327/64)) (327/64) := by
    constructor
    · intro t ht
      have inside : t ∈ Ioo (-(OUTER_LENGTH/64)) (OUTER_LENGTH/64) := ⟨by linarith [ht.1],by linarith [ht.2]⟩
      exact (signed.ode t (Ioo_subset_Icc_self inside)).hasDerivAt (Icc_mem_nhds inside.1 inside.2)
    · simpa only [Nat.cast_ofNat, neg_div] using ro
  intro Y born paths early back fwd
  exact alternative_of_passages (by norm_num)
    ⟨by linarith [(abs_le.mp small).1],by linarith [(abs_le.mp small).2]⟩ born py pz bornI bornO
    innerWell outerWell (Icc_subset_Icc (by linarith [hl.1]) (by linarith [hr.2]))
    (Icc_subset_Icc (by linarith [hL.1]) (by linarith [hR.2])) low high paths early back fwd

theorem from_nested_tori : ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
    ∀ φ : ℝ, |φ| ≤ 1/2^19 →
      (∀ u : Radius, ∃ k, (u:ℝ) ∈ DommaschkRadialRibbonEntry.tile k ∧
        DommaschkRadialRibbonEntry.Passage uC zC uA zA u φ k) ∧ FromRadialPassages uC zC uA zA φ := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,entries,tiles⟩ := DommaschkRadialRibbonEntry.from_nested_tori
  refine ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,fun φ small => ⟨fun u => tiles u u.2 φ small,?_⟩⟩
  apply from_entries small
  · exact entries .q0r470 φ (by simpa [MirrorEndpoint.opposite,MirrorEndpoint.width,azimuth] using small)
  · exact entries .q0r478 φ (by simpa [MirrorEndpoint.opposite,MirrorEndpoint.width,azimuth] using small)

end PlasmaLean.Design.DommaschkRadialFlowOnSUFFIX
