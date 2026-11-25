/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkRibbonSlopeCover
public import PlasmaLean.Design.DommaschkLowerActionPath

/-! # Transverse first mirrors on a joined physical radial-ribbon trajectory -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkRibbonFirstMirrors
open Set Certificates.PositionFrameSlabs DommaschkSignedMirrorBand DommaschkSignedMirrorSlope
open DommaschkMirrorTubeCrossing DommaschkSignedTraceDomain DommaschkFirstMirrorLaunchSign

abbrev lowerClock : ℝ := 317/64
abbrev capClock : ℝ := 331/64
abbrev derivativeFloor : ℝ := 1/16384

/-- The signed ODE on the canonical packets supplies both halves of one closed-slab
estimate, independent of the previous frame at the slab entry. -/
theorem attach {i n : ℕ} {fr br : List Step} {y : ℝ → Plane} {k : ℝ}
    (tracks : DommaschkLowerActionPath.Tracks fr br n y) (reached : i < n)
    (hf : i < fr.length) (hb : i < br.length)
    (f : SlabSlope fr[i] 1 (i / 64) (((i : ℝ) + 1) / 64) k)
    (b : SlabSlope br[i] (-1) (i / 64) (((i : ℝ) + 1) / 64) k) :
    Rates y (i / 64) (((i : ℝ) + 1) / 64) k := by
  obtain ⟨pf, forward⟩ := tracks.1 i reached hf
  obtain ⟨pb, backward⟩ := tracks.2 i reached hb
  intro t ht df db
  exact ⟨by simpa only [one_mul] using f t ht y pf (forward t ht) df,
    by simpa only [neg_one_mul] using b t ht (fun v => y (-v)) pb (backward t ht) db⟩

/-- The two signs cover every point, including the common section at zero. -/
def Below (y : ℝ → Plane) (a b h : ℝ) : Prop :=
  ∀ t ∈ Icc a b, strength t (y t) < h ∧ strength (-t) (y (-t)) < h

theorem Below.append {y : ℝ → Plane} {a b c h : ℝ}
    (left : Below y a b h) (right : Below y b c h) : Below y a c h := by
  intro t ht
  rcases le_total t b with early | late
  · exact left t ⟨ht.1,early⟩
  · exact right t ⟨late,ht.2⟩

theorem Below.signed {y : ℝ → Plane} {b h : ℝ} (bound : Below y 0 b h) :
    ∀ t ∈ Icc (-b) b, strength t (y t) < h := by
  intro t ht
  rcases le_total 0 t with pos | neg
  · exact (bound t ⟨pos,ht.2⟩).1
  · simpa only [neg_neg] using (bound (-t) ⟨neg_nonneg.mpr neg,by linarith [ht.1]⟩).2

/-- A slabwise upper-height exclusion on the original row pair transfers to the tracked path. -/
theorem attach_below {i n : ℕ} {fr br : List Step} {y : ℝ → Plane} {h : ℝ}
    (tracks : DommaschkLowerActionPath.Tracks fr br n y) (reached : i < n)
    (hf : i < fr.length) (hb : i < br.length)
    (f : ∀ (prev : State) (t : ℝ) (x : Plane),
      t ∈ Icc ((i : ℝ) / 64) (((i : ℝ) + 1) / 64) →
      x ∈ (physicalSlab prev fr[i] (i / 64)).tube t → strength t x < h)
    (b : ∀ (prev : State) (t : ℝ) (x : Plane),
      t ∈ Icc ((i : ℝ) / 64) (((i : ℝ) + 1) / 64) →
      x ∈ (physicalSlab prev br[i] (i / 64)).tube t → strength (-t) x < h) :
    Below y (i / 64) (((i : ℝ) + 1) / 64) h := by
  obtain ⟨pf, forward⟩ := tracks.1 i reached hf
  obtain ⟨pb, backward⟩ := tracks.2 i reached hb
  intro t ht
  exact ⟨f pf t _ ht (forward t ht),b pb t _ ht (backward t ht)⟩

/-- The full original low prefix, two-sided first contacts and orientations of every level
contact in the checked collar, including the derivative on the signed time variable. -/
def NoGrazing (y : ℝ → Plane) : Prop :=
  let h : ℝ := height true
  (∀ t ∈ Icc (-lowerClock) lowerClock, strength t (y t) < h) ∧
    FirstTransverseBoth lowerClock capClock h derivativeFloor y ∧
    ∀ t ∈ Ioo (-capClock) capClock, strength t (y t) = h →
      (0 < t → 0 < deriv (fun s => strength s (y s)) t) ∧
      (t < 0 → deriv (fun s => strength s (y s)) t < 0)

private theorem reverse_flow (t : ℝ) (x : Plane) :
    -DommaschkJacobian.euclideanFlow 0 1 (-t) x =
      DommaschkJacobian.euclideanFlow 0 (-1) t x := by
  ext j
  fin_cases j <;> simp [DommaschkJacobian.euclideanFlow,DommaschkBounceField.physicalFlow]

set_option maxRecDepth 9000 in
/-- Strict incoming signs and outward growth on the shared physical collar exclude
grazing at either first mirror of the same signed solution. -/
theorem no_grazing {y : ℝ → Plane}
    (ode : ∀ t ∈ Icc (-capClock) capClock, HasDerivWithinAt y
      (DommaschkJacobian.euclideanFlow 0 1 t (y t)) (Icc (-capClock) capClock) t)
    (radial : ∀ t ∈ Icc (-capClock) capClock, 0 < y t 0)
    (early : ∀ t ∈ Icc (-lowerClock) lowerClock, strength t (y t) < height true)
    (high : (height true : ℝ) < strength capClock (y capClock))
    (high' : (height true : ℝ) < strength (-capClock) (y (-capClock)))
    (rates : Rates y lowerClock capClock derivativeFloor) : NoGrazing y := by
  have conty : ContinuousOn y (Icc (-capClock) capClock) :=
    fun t ht => (ode t ht).continuousWithinAt
  have fc : ContinuousOn (fun t => strength t (y t)) (Icc (-capClock) capClock) := by
    simpa only [one_mul] using continuousOn_strength conty 1 radial
  have sub : Icc lowerClock capClock ⊆ Icc (-capClock) capClock :=
    Icc_subset_Icc_left (by norm_num [lowerClock,capClock])
  have negsub : MapsTo (fun t : ℝ => -t) (Icc lowerClock capClock) (Icc (-capClock) capClock) := by
    intro t ht
    exact ⟨neg_le_neg ht.2,by linarith [ht.1,show (0:ℝ) ≤ lowerClock by norm_num [lowerClock],
      show (0:ℝ) ≤ capClock by norm_num [capClock]]⟩
  have bc := fc.comp continuous_neg.continuousOn negsub
  have positive : (0:ℝ) < height true := by norm_num [height]
  have kpos : 0 < derivativeFloor := by norm_num [derivativeFloor]
  have hin : 0 ≤ lowerClock := by norm_num [lowerClock]
  have time : lowerClock < capClock := by norm_num [lowerClock,capClock]
  have growth (s : ℝ) (hr : s ∈ Ioo lowerClock capClock) := by
    have g : s ∈ Ioo (-capClock) capClock := ⟨(by norm_num [capClock,lowerClock] :
      -capClock < lowerClock).trans hr.1,hr.2⟩
    have neg : -s ∈ Ioo (-capClock) capClock := ⟨neg_lt_neg hr.2, by linarith [g.1]⟩
    have ds := (ode s (Ioo_subset_Icc_self g)).hasDerivAt (Icc_mem_nhds g.1 g.2)
    have dn := (ode (-s) (Ioo_subset_Icc_self neg)).hasDerivAt (Icc_mem_nhds neg.1 neg.2)
    have back := dn.scomp s (hasDerivAt_neg s)
    exact rates s (Ioo_subset_Icc_self hr) ds
      (by simpa only [Function.comp_def,neg_one_smul,reverse_flow] using back)
  have ef : ∀ t ∈ Icc 0 lowerClock, strength t (y t) < height true :=
    fun t ht => early t ⟨by linarith [ht.1],ht.2⟩
  have eb : ∀ t ∈ Icc 0 lowerClock, strength (-t) (y (-t)) < height true :=
    fun t ht => early (-t) ⟨neg_le_neg ht.2,by linarith [ht.1]⟩
  have firstF := Fields.TrajectorySlabs.first_contact_in_bracket hin time ef (fc.mono sub) high
  have firstB := Fields.TrajectorySlabs.first_contact_in_bracket hin time eb bc high'
  have rf := regular_of_square (fc.mono sub) (fun _ => norm_nonneg _) positive kpos
    (fun s hs => (growth s hs).1)
  have rb := regular_of_square bc (fun _ => norm_nonneg _) positive kpos
    (fun s hs => (growth s hs).2)
  refine ⟨early,first_transverse ⟨firstF, firstB⟩ ⟨rf,rb⟩,?_⟩
  intro t ht hit
  have outside : t ∉ Icc (-lowerClock) lowerClock := fun h => (early t h).ne hit
  have ratePos : 0 < derivativeFloor / (2 * (height true : ℝ)) := by positivity
  constructor
  · intro pos
    have tc : t ∈ Ioo lowerClock capClock :=
      ⟨lt_of_not_ge (fun h => outside ⟨by linarith,h⟩),ht.2⟩
    obtain ⟨_,v,hv,dv⟩ := rf t tc hit
    rw [dv.deriv]
    exact ratePos.trans hv
  · intro neg
    have tc : -t ∈ Ioo lowerClock capClock :=
      ⟨lt_of_not_ge (fun h => outside ⟨by linarith,by linarith⟩),by linarith [ht.1]⟩
    obtain ⟨_,v,hv,dv⟩ := rb (-t) tc (by simpa only [Function.comp_apply, neg_neg] using hit)
    have d := dv.scomp t (hasDerivAt_neg t)
    have signed : HasDerivAt (fun s => strength s (y s)) (-v) t := by
      simpa only [Function.comp_def,neg_neg,neg_one_smul] using d
    rw [signed.deriv]
    exact neg_neg_of_pos (ratePos.trans hv)

end PlasmaLean.Design.DommaschkRibbonFirstMirrors
