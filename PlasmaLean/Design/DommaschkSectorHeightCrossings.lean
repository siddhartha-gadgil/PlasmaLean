/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkSectorHeightAction

/-! # Connected first-well loci when the prescribed height and action both vary -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkSectorHeightCrossings

open Set Theory.KAM WEll1Z2 DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer
open Certificates.PositionFrameSlabs (Plane coordinates)
open DommaschkRadialFamilyContinuity DommaschkRadialActionAlternative DommaschkNativeWellAction
open DommaschkMirrorLaunch DommaschkSectorAction DommaschkRadialSectionAction
open DommaschkSectorHeightAction DommaschkSectorActionBand DommaschkRadialMirrorHeightBand
open Kinetic.FirstWellContinuation Kinetic.MirrorHeightAction Kinetic.MirrorActionEnvelope

abbrev Domain := Parameter × Heights

attribute [local irreducible] clipped DommaschkNativeWellAction.field
  DommaschkNativeWellAction.density action

/-- A single true path is chosen per angle and radius before height is chosen. Both mirror
locations and the first-well action are jointly continuous in all three coordinates. -/
structure Family (uC zC uA zA : FA) where
  path : Parameter → ℝ → Plane
  born : ∀ p, path p p.1 = coordinates.symm (birth uC zC uA zA p.2 p.1)
  enclosed : ∀ p, Enclosed (path p) (-cap) cap
  verified : ∀ p, Verified (path p)
  L : Domain → ℝ
  R : Domain → ℝ
  continuous_left : Continuous L
  continuous_right : Continuous R
  physical : ∀ q, AtHeight (path q.1) q.2 (L q) (R q)
  continuous_action : Continuous (fun q : Domain => clipped (path q.1) q.2)

/-- The joint family can be constructed from independently enclosed physical trajectories
at the original births of the embedded tori. -/
theorem family_of_paths {uC zC uA zA : FA}
    (ec : EmbeddedTorus (RofC uC) (Zof zC)) (ea : EmbeddedTorus (RofC uA) (Zof zA))
    (Y : Parameter → ℝ → Plane)
    (born : ∀ p, Y p p.1 = coordinates.symm (birth uC zC uA zA p.2 p.1))
    (paths : ∀ p, Enclosed (Y p) (-cap) cap) (good : ∀ p, Verified (Y p)) :
    Nonempty (Family uC zC uA zA) := by
  have facts (p : Parameter) (h : Heights) := at_height (paths p) (good p) h
  have sign (p : Parameter) (h : Heights) :
      field (Y p) 0 < h ∧ h < field (Y p) (-cap) ∧ h < field (Y p) cap := by
    obtain ⟨l,r,fact⟩ := facts p h
    exact fact.signs
  have base := capped_sector ec ea born paths (fun p => ⟨(sign p reference).1,
    (sign p reference).2.1,(sign p reference).2.2⟩)
  have pull : Continuous fun q : Domain × ℝ => (q.1.1, q.2) :=
    (continuous_fst.comp continuous_fst).prodMk continuous_snd
  have maps : MapsTo (fun q : Domain × ℝ => (q.1.1,q.2)) (univ ×ˢ Icc (-cap) cap)
      (univ ×ˢ Icc (-cap) cap) := fun q hq => ⟨mem_univ _,hq.2⟩
  have whole : CappedFamily (fun q : Domain => field (Y q.1)) (fun q => density (Y q.1))
      (fun q => (q.2 : ℝ)) cap :=
    ⟨base.duration,continuous_subtype_val.comp continuous_snd,
      base.field.comp pull.continuousOn maps,base.weight.comp pull.continuousOn maps,
      fun q => (sign q.1 q.2).1,fun q => (sign q.1 q.2).2.1,fun q => (sign q.1 q.2).2.2⟩
  have identify (q : Domain) (l r : ℝ) (w : LaunchWell (field (Y q.1)) 0 q.2 l r) :
      AtHeight (Y q.1) q.2 l r := by
    obtain ⟨l',r',fact⟩ := facts q.1 q.2
    obtain ⟨el,er⟩ := w.unique (fact.well 0 (by norm_num))
    rwa [el,er]
  obtain ⟨L,R,cl,cr,ws,cj⟩ := whole.continuous_first_wells
    (fun q l r w => ⟨(identify q l r w).left.ne,(identify q l r w).right.ne'⟩)
  have each (q : Domain) := identify q (L q) (R q) (ws q)
  refine ⟨⟨Y,born,paths,good,L,R,cl,cr,each,?_⟩⟩
  exact cj.congr (g := fun q : Domain => clipped (Y q.1) q.2) (fun q => (each q).mass.symm)

/-- The original radial faces still have opposite action signs on a closed rectangle of
heights and target actions. The input bounds at the reference height are independent of Y. -/
theorem face_signs {uC zC uA zA : FA} (family : Family uC zC uA zA) (φ : Phase)
    (faces : BandFaces uC zC uA zA φ) (h j : ℝ) (wh : |h - level| ≤ delta)
    (wj : j ∈ Icc lowTarget highTarget) :
    clipped (family.path (φ,inner)) h < j ∧ j < clipped (family.path (φ,outer)) h := by
  let a : Parameter := (φ,inner)
  let b : Parameter := (φ,outer)
  have m := family.physical (a,reference)
  have n := family.physical (b,reference)
  have ends (v : ℝ) (hv : v ∈ Icc lowAction highAction) :=
    faces v hv (fun u => family.path (φ,u)) (fun u => family.born (φ,u))
      (fun u => family.enclosed (φ,u)) _ _ _ _ (m.well 0 (by norm_num)) (n.well 0 (by norm_num))
  have ordered : lowAction ≤ highAction := by unfold lowAction highAction; linarith
  have low := (ends lowAction ⟨le_rfl,ordered⟩).1
  have high := (ends highAction ⟨ordered,le_rfl⟩).2
  rw [← m.mass] at low
  rw [← n.mass] at high
  have move (q : Parameter) : |clipped (family.path q) h - clipped (family.path q) level| ≤
      1/1000 := by
    have estimate := lipschitz (family.enclosed q) (family.verified q) ⟨h,in_band wh⟩ reference
    exact estimate.trans ((mul_le_mul_of_nonneg_left wh (by norm_num : (0:ℝ) ≤ 10000)).trans
      (by norm_num [delta]))
  have ma := (abs_le.mp (move a)).2
  have mb := (abs_le.mp (move b)).1
  change clipped (family.path a) level < lowAction at low
  change highAction < clipped (family.path b) level at high
  change clipped (family.path a) h < j ∧ j < clipped (family.path b) h
  obtain ⟨jl,jr⟩ := wj
  unfold lowAction highAction lowTarget highTarget at *
  constructor <;> linarith

/-- A compact connected subset inside the radial interval realizes the two prescriptions
and has every admitted launch phase in its projection. -/
def Crossing (uC zC uA zA : FA) (height actionTarget : Phase → ℝ) : Prop :=
  ∃ (K : Set Parameter) (L R : Parameter → ℝ) (margin : ℝ),
    IsCompact K ∧ IsConnected K ∧ Prod.fst '' K = univ ∧ 0 < margin ∧
    Continuous L ∧ Continuous R ∧ ∀ p ∈ K,
    (p.2 : ℝ) ∈ Icc (47/100+margin) (239/500-margin) ∧
    ∃ y : ℝ → Plane, y p.1 = coordinates.symm (birth uC zC uA zA p.2 p.1) ∧
      Enclosed y (-cap) cap ∧ LaunchWell (field y) p.1 (height p.1) (L p) (R p) ∧
      deriv (field y) (L p) < 0 ∧ 0 < deriv (field y) (R p) ∧
      action (field y) (density y) (L p) (R p) (height p.1) = actionTarget p.1

theorem crossing {uC zC uA zA : FA} (family : Family uC zC uA zA)
    (faces : ∀ φ : Phase, BandFaces uC zC uA zA φ) (height j : Phase → ℝ)
    (ch : Continuous height) (cj : Continuous j)
    (hh : ∀ φ, |height φ - level| ≤ delta) (hj : ∀ φ, j φ ∈ Icc lowTarget highTarget) :
    Crossing uC zC uA zA height j := by
  let select (p : Parameter) : Domain := (p,⟨height p.1,in_band (hh p.1)⟩)
  have cs : Continuous select :=
    continuous_id.prodMk ((ch.comp continuous_fst).subtype_mk (fun p => in_band (hh p.1)))
  let value (p : Parameter) := clipped (family.path p) (height p.1)
  have cv : Continuous value := by
    change Continuous ((fun q : Domain => clipped (family.path q.1) q.2) ∘ select)
    exact family.continuous_action.comp cs
  have signs (φ : Phase) := face_signs family φ (faces φ) (height φ) (j φ) (hh φ) (hj φ)
  obtain ⟨K,compact,conn,levelSet,projects⟩ :=
    RectangleLevelCrossing.interior_level_crossing_subtype (by norm_num) (by norm_num)
      (fun p => value p - j p.1) (cv.sub (cj.comp continuous_fst))
      (fun φ => sub_neg.mpr (signs φ).1) (fun φ => sub_pos.mpr (signs φ).2)
  have radial : Continuous fun p : Parameter => (p.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  obtain ⟨a,ha,least⟩ := compact.exists_isMinOn conn.nonempty radial.continuousOn
  obtain ⟨b,hb,most⟩ := compact.exists_isMaxOn conn.nonempty radial.continuousOn
  let margin : ℝ := min ((a.2 : ℝ)-47/100) (239/500-(b.2 : ℝ))
  have pos : 0 < margin :=
    lt_min (sub_pos.mpr (levelSet a ha).1.1) (sub_pos.mpr (levelSet b hb).1.2)
  refine ⟨K,family.L ∘ select,family.R ∘ select,margin,compact,conn,projects,pos,
    family.continuous_left.comp cs,family.continuous_right.comp cs,?_⟩
  intro p hp
  have below : (a.2 : ℝ) ≤ (p.2 : ℝ) := least hp
  have above : (p.2 : ℝ) ≤ (b.2 : ℝ) := most hp
  have ml : margin ≤ (a.2 : ℝ)-47/100 := min_le_left _ _
  have mr : margin ≤ 239/500-(b.2 : ℝ) := min_le_right _ _
  have facts := family.physical (select p)
  exact ⟨⟨by linarith,by linarith⟩,family.path p,family.born p,family.enclosed p,
    facts.well p.1 (abs_le.mpr p.1.2),facts.left,facts.right,
    facts.mass.symm.trans (sub_eq_zero.mp (levelSet p hp).2)⟩

end PlasmaLean.Design.DommaschkSectorHeightCrossings
