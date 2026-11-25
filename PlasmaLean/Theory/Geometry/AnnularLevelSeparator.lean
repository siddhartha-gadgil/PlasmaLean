/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Geometry.RectangleLevelCrossing
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Homotopy.Lifting

/-!
# A connected level component separating the two ends of a cylinder

An interval family connecting any finite list of boundary-to-boundary paths
turns the rectangular crossing theorem into a finite intersection property in
the compact space of components of the level.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.AnnularLevelSeparator
open Set
open scoped unitInterval

variable {X : Type*} [TopologicalSpace X]

/-- Paths from the lower to the upper face of the cylinder, with free phase
coordinates at both endpoints. -/
abbrev Passage (X : Type*) [TopologicalSpace X] :=
  {g : C(I, X × I) // (g 0).2 = 0 ∧ (g 1).2 = 1}

private def vertical (x : X) : Passage X :=
  ⟨⟨fun t ↦ (x,t), continuous_const.prodMk continuous_id⟩, rfl, rfl⟩

private theorem continuous_vertical : Continuous (vertical : X → Passage X) :=
  (ContinuousMap.continuous_of_continuous_uncurry (fun x : X ↦ (vertical x).val)
    (show Continuous (fun p : X × I ↦ (p.1,p.2)) from continuous_id)).subtype_mk _

/-- Move a passage to the straight radial path at its initial phase. -/
private def deform (g : Passage X) : Path (vertical (g.val 0).1) g := by
  let H : C(I × I, X × I) := ⟨fun ⟨s,t⟩ ↦ ((g.val (s*t)).1,
    projIcc 0 1 zero_le_one ((1-(s:ℝ))*(t:ℝ) + (s:ℝ)*(g.val t).2)), by fun_prop⟩
  have ends (s : I) : (H.curry s 0).2 = 0 ∧ (H.curry s 1).2 = 1 := by
    change projIcc 0 1 zero_le_one ((1-(s:ℝ))*(0:I) + (s:ℝ)*(g.val 0).2) = 0 ∧
      projIcc 0 1 zero_le_one ((1-(s:ℝ))*(1:I) + (s:ℝ)*(g.val 1).2) = 1
    simp [g.property.1, g.property.2]
  refine ⟨⟨fun s ↦ ⟨H.curry s, ends s⟩, H.curry.continuous.subtype_mk _⟩, ?_, ?_⟩
  · apply Subtype.ext
    ext t : 1
    simp [H,vertical]
  · apply Subtype.ext
    ext t : 1
    simp [H]

private theorem passages_pathConnected [PathConnectedSpace X] : PathConnectedSpace (Passage X) :=
  ⟨⟨vertical (Classical.arbitrary X)⟩, fun x y ↦
    ⟨((deform x).symm.trans ((PathConnectedSpace.somePath (x.val 0).1 (y.val 0).1).map
      continuous_vertical)).trans (deform y)⟩⟩

/-- Every finite collection of points of a path-connected space lies on one
continuous path. This version also accepts the empty collection. -/
private theorem visits {W : Type*} [TopologicalSpace W] [PathConnectedSpace W]
    (s : Finset W) : ∃ g : C(I,W), ∀ w ∈ s, w ∈ range g := by
  classical
  let p : Fin (s.card + 1) → W := Fin.cons (Classical.arbitrary W) fun i ↦ (s.equivFin.symm i).val
  obtain ⟨g, hg⟩ := PathConnectedSpace.exists_path_through_family p
  refine ⟨g.toContinuousMap, ?_⟩
  intro w hw
  simpa [p] using hg (s.equivFin ⟨w,hw⟩).succ

/-- For a compact Hausdorff path-connected phase space, one compact connected
part of a strictly bracketed scalar level meets every continuous passage from
the lower face to the upper face. -/
theorem cylinder_separator [CompactSpace X] [T2Space X] [PathConnectedSpace X]
    (f : X × I → ℝ) (hf : Continuous f) {target : ℝ}
    (low : ∀ x, f (x, 0) < target) (high : ∀ x, target < f (x, 1)) :
    ∃ K : Set (X × I), IsCompact K ∧ IsConnected K ∧
      (∀ z ∈ K, f z = target ∧ 0 < z.2 ∧ z.2 < 1) ∧
      (∀ g : Passage X, ∃ s, g.val s ∈ K) ∧ Prod.fst '' K = univ := by
  classical
  let Z : Set (X × I) := {z | f z = target}
  have hZ : IsClosed Z := isClosed_eq hf continuous_const
  let : CompactSpace Z := isCompact_iff_compactSpace.mp hZ.isCompact
  let : PathConnectedSpace (Passage X) := passages_pathConnected
  let comp := ConnectedComponents.mk (α := Z)
  have ccomp : Continuous comp := ConnectedComponents.continuous_coe
  let hit (g : Passage X) : Set (ConnectedComponents Z) := comp '' (Subtype.val ⁻¹' range g.val)
  have closed_hit (g : Passage X) : IsClosed (hit g) := by
    have hc := (isCompact_range g.val.continuous).isClosed.preimage
      (continuous_subtype_val (p := (· ∈ Z)))
    exact (hc.isCompact.image ccomp).isClosed
  have finite_hit (s : Finset (Passage X)) : (⋂ g ∈ s, hit g).Nonempty := by
    obtain ⟨family, visits_all⟩ := visits s
    let ev (q : I × I) := (family q.1).val q.2
    have cev : Continuous ev := continuous_eval.comp
      ((continuous_subtype_val.comp (family.continuous.comp continuous_fst)).prodMk continuous_snd)
    have lower (r : I) : f (ev (r,0)) < target := by
      change f (((family r).val 0).1, ((family r).val 0).2) < target
      rw [(family r).property.1]
      exact low _
    have upper (r : I) : target < f (ev (r,1)) := by
      change target < f (((family r).val 1).1, ((family r).val 1).2)
      rw [(family r).property.2]
      exact high _
    obtain ⟨A, _, hA, levelA, covers⟩ := RectangleLevelCrossing.interior_level_crossing_subtype
      zero_le_one zero_le_one (f ∘ ev) (hf.comp cev) lower upper
    let : ConnectedSpace A := isConnected_iff_connectedSpace.mp hA
    let lift (q : A) : Z := ⟨ev q, (levelA q q.property).2⟩
    have clift : Continuous lift := (cev.comp continuous_subtype_val).subtype_mk _
    let q₀ := Classical.arbitrary A
    have one := (isPreconnected_range (ccomp.comp clift)).subsingleton
    refine ⟨comp (lift q₀), mem_iInter₂.mpr ?_⟩
    intro g hg
    obtain ⟨t, ht⟩ := visits_all g hg
    obtain ⟨q, hq, hqt⟩ := (eq_univ_iff_forall.mp covers) t
    let v : A := ⟨q,hq⟩
    refine ⟨lift v, ?_, one (mem_range_self v) (mem_range_self q₀)⟩
    change ev q ∈ range g.val
    exact ⟨q.2, by change g.val q.2 = (family q.1).val q.2; rw [hqt, ht]⟩
  obtain ⟨i, hi⟩ := CompactSpace.iInter_nonempty closed_hit finite_hit
  obtain ⟨z, hz⟩ := ConnectedComponents.surjective_coe i
  let K : Set (X × I) := Subtype.val '' connectedComponent z
  have meets (g : Passage X) : ∃ s, g.val s ∈ K := by
    obtain ⟨w, ⟨t, ht⟩, hw⟩ := mem_iInter.mp hi g
    exact ⟨t, w, ConnectedComponents.coe_eq_coe'.mp (hw.trans hz.symm), ht.symm⟩
  refine ⟨K, isClosed_connectedComponent.isCompact.image continuous_subtype_val,
    isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn, ?_, meets,
    eq_univ_of_forall ?_⟩
  · rintro _ ⟨w, _, rfl⟩
    have hw : f w.val = target := w.property
    refine ⟨hw, lt_of_le_of_ne bot_le ?_, lt_of_le_of_ne le_top ?_⟩
    · intro h
      exact (low w.val.1).ne (by rw [h]; exact hw)
    · intro h
      exact (high w.val.1).ne' (by rw [← h]; exact hw)
  · intro x
    obtain ⟨s, hs⟩ := meets (vertical x)
    exact ⟨(x,s), hs, rfl⟩

/-- When the cylinder is locally path-connected, points of its opposite faces
belong to different connected components of the complement of any compact set
which meets every passage. -/
theorem different_complement_components [T2Space X] [LocallyPathConnectedSpace (X × I)]
    {K : Set (X × I)} (hK : IsCompact K) (meets : ∀ g : Passage X, ∃ s, g.val s ∈ K)
    (u v : ↥Kᶜ) (hu : u.val.2 = 0) (hv : v.val.2 = 1) :
    connectedComponent u ≠ connectedComponent v := by
  let : LocallyPathConnectedSpace (↥Kᶜ) := hK.isClosed.isOpen_compl.locallyPathConnectedSpace
  intro eq
  obtain ⟨path⟩ := (connectedComponent_eq_iff_joined u v).mp eq
  let g : Passage X := ⟨⟨fun t ↦ (path t).val, continuous_subtype_val.comp path.continuous⟩,
    by simpa using hu, by simpa using hv⟩
  obtain ⟨s, hs⟩ := meets g
  exact (path s).property hs

/-- On the periodic annulus the same compact connected target set projects
onto the circle, meets every boundary-to-boundary path, and separates the two
boundary circles into different connected components of its complement. -/
theorem annulus_separator (f : UnitAddCircle × I → ℝ) (hf : Continuous f) {target : ℝ}
    (low : ∀ x, f (x, 0) < target) (high : ∀ x, target < f (x, 1)) :
    ∃ K : Set (UnitAddCircle × I), IsCompact K ∧ IsConnected K ∧
      (∀ z ∈ K, f z = target ∧ 0 < z.2 ∧ z.2 < 1) ∧
      (∀ g : Passage UnitAddCircle, ∃ s, g.val s ∈ K) ∧ Prod.fst '' K = univ ∧
      (∀ (u v : ↥Kᶜ), u.val.2 = 0 → v.val.2 = 1 → connectedComponent u ≠ connectedComponent v) := by
  obtain ⟨K, hc, hk, level, meets, proj⟩ := cylinder_separator f hf low high
  let : LocallyPathConnectedSpace I := (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).locallyPathConnectedSpace
  let : LocallyPathConnectedSpace UnitAddCircle :=
    QuotientAddGroup.isOpenQuotientMap_mk.isQuotientMap.locallyPathConnectedSpace
  exact ⟨K, hc, hk, level, meets, proj, different_complement_components hc meets⟩

/-- Period-one data on the real angular cover descend to the same separating
set. The target identity is asserted for every real representative. -/
theorem periodic_separator (f : ℝ × I → ℝ) (hf : Continuous f) {target : ℝ}
    (per : ∀ r, Function.Periodic (fun p ↦ f (p, r)) 1)
    (low : ∀ x, f (x, 0) < target) (high : ∀ x, target < f (x, 1)) :
    ∃ K : Set (UnitAddCircle × I), IsCompact K ∧ IsConnected K ∧
      (∀ (x : ℝ) (r : I), ((x : UnitAddCircle), r) ∈ K → f (x,r) = target ∧ 0 < r ∧ r < 1) ∧
      (∀ g : Passage UnitAddCircle, ∃ s, g.val s ∈ K) ∧ Prod.fst '' K = univ ∧
      (∀ (u v : ↥Kᶜ), u.val.2 = 0 → v.val.2 = 1 → connectedComponent u ≠ connectedComponent v) := by
  let F (z : UnitAddCircle × I) := (per z.2).lift z.1
  have q : IsOpenQuotientMap ((↑) : ℝ → UnitAddCircle) :=
    QuotientAddGroup.isOpenQuotientMap_mk
  have cF : Continuous F := (q.prodMap IsOpenQuotientMap.id).continuous_comp_iff.mp hf
  have lo (z : UnitAddCircle) : F (z, 0) < target := by
    obtain ⟨a,rfl⟩ := q.surjective z
    exact low a
  have hi (z : UnitAddCircle) : target < F (z, 1) := by
    obtain ⟨a,rfl⟩ := q.surjective z
    exact high a
  obtain ⟨K, hc, hk, level, meets, proj, separates⟩ := annulus_separator F cF lo hi
  exact ⟨K, hc, hk, fun x r h ↦ level ((x:UnitAddCircle), r) h, meets, proj, separates⟩

/-- The angular coordinate of a compact annular separator has no globally
continuous real lift. Extending such a lift across the cylinder would produce
a connected crossing of its complement at an offset of half a turn. -/
theorem no_angular_lift {K : Set (UnitAddCircle × I)} (hK : IsCompact K)
    (sep : ∀ (u v : ↥Kᶜ), u.val.2 = 0 → v.val.2 = 1 → connectedComponent u ≠ connectedComponent v) :
    ¬ ∃ G : C(K,ℝ), ∀ z : K, (G z : UnitAddCircle) = z.val.1 := by
  rintro ⟨G, lifts⟩
  obtain ⟨F, extF⟩ := G.exists_restrict_eq hK.isClosed
  obtain ⟨lo, hlo⟩ := (isCompact_range F.continuous).bddBelow
  obtain ⟨hi, hhi⟩ := (isCompact_range F.continuous).bddAbove
  have bounds (z : UnitAddCircle × I) : lo ≤ F z ∧ F z ≤ hi :=
    ⟨hlo (mem_range_self z), hhi (mem_range_self z)⟩
  have width : lo ≤ hi := (bounds (0,0)).1.trans (bounds (0,0)).2
  let R := Icc (lo-1) (hi+1)
  let down (q : I × R) : UnitAddCircle × I := (↑(q.2 : ℝ), q.1)
  have cd : Continuous down := ((AddCircle.continuous_mk' (1 : ℝ)).comp
    (continuous_subtype_val.comp continuous_snd)).prodMk continuous_fst
  let H (q : I × R) := (q.2 : ℝ) - F (down q)
  have cH : Continuous H := (continuous_subtype_val.comp continuous_snd).sub (F.continuous.comp cd)
  have wide : lo-1 ≤ hi+1 := by linarith
  have low (x : I) : H (x, ⟨lo-1, left_mem_Icc.mpr wide⟩) < 1/2 := by
    let r : R := ⟨lo-1, left_mem_Icc.mpr wide⟩
    change lo-1 - F (down (x,r)) < 1/2
    linarith [(bounds (down (x,r))).1]
  have high (x : I) : 1/2 < H (x, ⟨hi+1, right_mem_Icc.mpr wide⟩) := by
    let r : R := ⟨hi+1, right_mem_Icc.mpr wide⟩
    change 1/2 < hi+1 - F (down (x,r))
    linarith [(bounds (down (x,r))).2]
  obtain ⟨A, _, conn, level, proj⟩ := RectangleLevelCrossing.interior_level_crossing_subtype
    zero_le_one wide (target := 1/2) H cH low high
  · have avoid (q : A) : down q ∈ Kᶜ := by
      intro h
      let z : K := ⟨down q,h⟩
      have angle := lifts z
      have extv : F (down q) = G z := congrArg (fun m : C(K,ℝ) ↦ m z) extF
      change (G z : UnitAddCircle) = ↑(q.val.2 : ℝ) at angle
      rw [← extv] at angle
      have hz : (↑((q.val.2:ℝ) - F (down q)) : UnitAddCircle) = 0 := by
        rw [AddCircle.coe_sub, angle, sub_self]
      have hhalf := (level q q.property).2
      change (q.val.2:ℝ) - F (down q) = 1/2 at hhalf
      rw [hhalf] at hz
      have hhalf' : (1/2 : ℝ) ∈ Ico 0 1 := by constructor <;> norm_num
      exact (by norm_num : (1/2 : ℝ) ≠ 0) ((AddCircle.coe_eq_zero_iff_of_mem_Ico hhalf').mp hz)
    let into (q : A) : ↥Kᶜ := ⟨down q, avoid q⟩
    have cinto : Continuous into := (cd.comp continuous_subtype_val).subtype_mk _
    let : ConnectedSpace A := isConnected_iff_connectedSpace.mp conn
    have cr := isConnected_range cinto
    obtain ⟨a, ha, ha0⟩ := eq_univ_iff_forall.mp proj (0 : I)
    obtain ⟨b, hb, hb1⟩ := eq_univ_iff_forall.mp proj (1 : I)
    let u : A := ⟨a,ha⟩
    let v : A := ⟨b,hb⟩
    exact sep (into u) (into v) ha0 hb1
      (connectedComponent_eq_iff_mem.mpr (cr.subset_connectedComponent
        (mem_range_self (f := into) v) (mem_range_self u)))

/-- A compact annular separator is essentially embedded: its inclusion is
never homotopic to a constant in the annulus. The covering homotopy theorem
would otherwise supply the forbidden angular lift. -/
theorem essential_inclusion {K : Set (UnitAddCircle × I)} (hK : IsCompact K)
    (sep : ∀ (u v : ↥Kᶜ), u.val.2 = 0 → v.val.2 = 1 → connectedComponent u ≠ connectedComponent v)
    (base : UnitAddCircle × I) :
    ¬ (ContinuousMap.restrict K (ContinuousMap.id (UnitAddCircle × I))).Homotopic
      (ContinuousMap.const K base) := by
  rintro ⟨shrink⟩
  apply no_angular_lift hK sep
  let H : C(I × K, UnitAddCircle) := ContinuousMap.fst.comp shrink.symm.toContinuousMap
  let cov := AddCircle.isCoveringMap_coe (1 : ℝ)
  obtain ⟨b, hb⟩ := (QuotientAddGroup.mk_surjective base.1 :
    ∃ x : ℝ, (x : UnitAddCircle) = base.1)
  have start (z : K) : H (0,z) = ((ContinuousMap.const K b z : ℝ) : UnitAddCircle) := by
    change (shrink.symm (0, z)).1 = ↑b
    exact (congrArg Prod.fst (shrink.symm.map_zero_left z)).trans hb.symm
  let L := cov.liftHomotopy H (ContinuousMap.const K b) start
  refine ⟨L.comp ((ContinuousMap.const K (1 : I)).prodMk (ContinuousMap.id K)), ?_⟩
  intro z
  have e := congrFun (cov.liftHomotopy_lifts H (ContinuousMap.const K b) start) (1,z)
  change (↑(L (1,z)) : UnitAddCircle) = z.val.1
  calc
    _ = H (1,z) := e
    _ = z.val.1 := congrArg Prod.fst (shrink.symm.map_one_left z)

end PlasmaLean.AnnularLevelSeparator
