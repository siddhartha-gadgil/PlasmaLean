/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.BrouwerFixedPoint
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.Separation.Regular

/-!
# Connected level crossings on a phase–radius rectangle

A compact connected family of solutions persists through a compact parameter
interval. The fixed point argument uses Brouwer's theorem on the product of
the parameter interval and the original convex domain.
-/

@[expose] public section
namespace PlasmaLean.RectangleLevelCrossing

open Set

/-- Separate two closed sets in a compact Hausdorff space if no connected
component meets both. -/
theorem clopen_separator {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {L R : Set X} (hL : IsClosed L) (hR : IsClosed R)
    (apart : ∀ l ∈ L, ∀ r ∈ R, (l : ConnectedComponents X) ≠ r) :
    ∃ U : Set X, IsClopen U ∧ L ⊆ U ∧ Disjoint U R := by
  let c := ConnectedComponents.mk (α := X)
  have hc : Continuous c := ConnectedComponents.continuous_coe
  have sep : c '' L ⊆ (c '' R)ᶜ := by
    rintro _ ⟨l, hl, rfl⟩ ⟨r, hr, he⟩
    exact apart l hl r hr he.symm
  obtain ⟨V, hV, hLV, hVR⟩ := exists_clopen_of_closed_subset_open
    (hL.isCompact.image hc).isClosed (hR.isCompact.image hc).isClosed.isOpen_compl sep
  exact ⟨c ⁻¹' V, hV.preimage hc, fun l hl ↦ hLV ⟨l, hl, rfl⟩,
    Set.disjoint_left.mpr fun r hv hr ↦ hVR hv ⟨r, hr, rfl⟩⟩

/-- Finite-dimensional Browder continuation. A continuous self-map of a
nonempty compact convex set, depending on a real parameter, has a compact
connected set of fixed points projecting onto the entire parameter interval. -/
theorem parameter_fixed_points {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {a b : ℝ} (hab : a ≤ b) {B : Set E} (hB : IsCompact B)
    (hconv : Convex ℝ B) (hne : B.Nonempty) (F : ℝ × E → E)
    (hF : ContinuousOn F (Icc a b ×ˢ B)) (hmap : MapsTo F (Icc a b ×ˢ B) B) :
    ∃ K : Set (ℝ × E), IsCompact K ∧ IsConnected K ∧ K ⊆ Icc a b ×ˢ B ∧
      (∀ p ∈ K, F p = p.2) ∧ Prod.fst '' K = Icc a b := by
  classical
  let D := Icc a b ×ˢ B
  have hD : IsCompact D := isCompact_Icc.prod hB
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD
  let Z : Set D := {p | F p = p.val.2}
  have hZ : IsClosed Z := isClosed_eq hF.domRestrict (continuous_snd.comp continuous_subtype_val)
  let : CompactSpace Z := isCompact_iff_compactSpace.mp hZ.isCompact
  let e : Z → ℝ × E := fun z ↦ z.val.val
  have he : Continuous e := continuous_subtype_val.comp continuous_subtype_val
  let L : Set Z := {z | (e z).1 = a}
  let R : Set Z := {z | (e z).1 = b}
  have hL : IsClosed L := isClosed_eq (continuous_fst.comp he) continuous_const
  have hR : IsClosed R := isClosed_eq (continuous_fst.comp he) continuous_const
  suffices same : ∃ l ∈ L, ∃ r ∈ R, (l : ConnectedComponents Z) = r by
    obtain ⟨l, hl, r, hr, hlr⟩ := same
    let C := connectedComponent r
    have hC : IsConnected (e '' C) := isConnected_connectedComponent.image _ he.continuousOn
    refine ⟨e '' C, isClosed_connectedComponent.isCompact.image he, hC, ?_, ?_, ?_⟩
    · rintro _ ⟨p, _, rfl⟩
      exact p.val.property
    · rintro _ ⟨p, _, rfl⟩
      exact p.property
    · apply Subset.antisymm
      · rintro _ ⟨_, ⟨p, _, rfl⟩, rfl⟩
        exact p.val.property.1
      · apply (hC.image _ continuous_fst.continuousOn).isPreconnected.Icc_subset
        · exact ⟨e l, ⟨l, ConnectedComponents.coe_eq_coe'.mp hlr, rfl⟩, hl⟩
        · exact ⟨e r, ⟨r, mem_connectedComponent, rfl⟩, hr⟩
  by_contra! apart
  obtain ⟨U, hU, hLU, hUR⟩ := clopen_separator hL hR apart
  have disj : Disjoint (e '' Uᶜ) (e '' U) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, h⟩
    have heq : q = p := Subtype.ext (Subtype.ext h)
    exact hp (heq ▸ hq)
  obtain ⟨g, g0, g1, gI⟩ := exists_continuous_zero_one_of_isClosed
    (hU.compl.isClosed.isCompact.image he).isClosed
    (hU.isClosed.isCompact.image he).isClosed disj
  let G : ℝ × E → ℝ × E := fun p ↦ (a + (b-a) * g p, F p)
  have hG : ContinuousOn G D :=
    (continuous_const.add (continuous_const.mul g.continuous)).continuousOn.prodMk hF
  have hGD : MapsTo G D D := by
    intro p hp
    refine ⟨⟨?_, ?_⟩, hmap hp⟩
    · exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hab) (gI p).1)
    · change a + (b-a) * g p ≤ b
      nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr (gI p).2)]
  obtain ⟨p, hp, hfix⟩ := TauCeti.brouwerFixedPoint_compactConvex_continuousOn hD
    ((convex_Icc a b).prod hconv) ((nonempty_Icc.mpr hab).prod hne) hG hGD
  have hphase : a + (b-a) * g p = p.1 := congrArg Prod.fst hfix
  let z : Z := ⟨⟨p, hp⟩, congrArg Prod.snd hfix⟩
  by_cases hu : z ∈ U
  · have hv : g p = 1 := g1 ⟨z, hu, rfl⟩
    have hb : z ∈ R := by change p.1 = b; rw [hv] at hphase; linarith
    exact Set.disjoint_left.mp hUR hu hb
  · have hv : g p = 0 := g0 ⟨z, hu, rfl⟩
    have ha : z ∈ L := by change p.1 = a; rw [hv] at hphase; linarith
    exact hu (hLU ha)

/-- A continuous scalar whose radial faces bracket a target admits a compact
connected subset of that level projecting onto every phase. Weak inequalities
are sufficient, and both intervals may be degenerate. -/
theorem level_crossing {a b c d target : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (f : ℝ × ℝ → ℝ) (hf : ContinuousOn f (Icc a b ×ˢ Icc c d))
    (lower : ∀ p ∈ Icc a b, f (p, c) ≤ target)
    (upper : ∀ p ∈ Icc a b, target ≤ f (p, d)) :
    ∃ K : Set (ℝ × ℝ), IsCompact K ∧ IsConnected K ∧ K ⊆ Icc a b ×ˢ Icc c d ∧
      (∀ z ∈ K, f z = target) ∧ Prod.fst '' K = Icc a b := by
  let update : ℝ × ℝ → ℝ := fun z ↦ min d (max c (z.2 + target - f z))
  have hc : ContinuousOn update (Icc a b ×ˢ Icc c d) :=
    continuousOn_const.inf (continuousOn_const.sup
      ((continuous_snd.continuousOn.add continuousOn_const).sub hf))
  have hm : MapsTo update (Icc a b ×ˢ Icc c d) (Icc c d) := fun z _ ↦
    ⟨le_min hcd (le_max_left _ _), min_le_left _ _⟩
  obtain ⟨K, hK, hconn, hsub, hfix, hproj⟩ := parameter_fixed_points hab
    isCompact_Icc (convex_Icc c d) (nonempty_Icc.mpr hcd) update hc hm
  refine ⟨K, hK, hconn, hsub, ?_, hproj⟩
  rintro ⟨p, r⟩ h
  have ⟨hp, hr⟩ := hsub h
  have he := hfix (p, r) h
  change min d (max c (r + target - f (p, r))) = r at he
  rcases lt_trichotomy (f (p, r)) target with hl | hEq | hg
  · have hrd : r < d := lt_of_le_of_ne hr.2 (fun eq ↦ hl.not_ge (eq ▸ upper p hp))
    have hmove : r < max c (r + target - f (p, r)) :=
      lt_of_lt_of_le (by linarith : r < r + target - f (p, r)) (le_max_right ..)
    exact ((lt_min hrd hmove).ne he.symm).elim
  · exact hEq
  · have hcr : c < r := lt_of_le_of_ne hr.1 (fun eq ↦ hg.not_ge (eq ▸ lower p hp))
    have hmove : max c (r + target - f (p, r)) < r := max_lt hcr (by linarith)
    exact ((lt_of_le_of_lt (min_le_right d _) hmove).ne he).elim

/-- Strict face signs place every point of the crossing in the open radial
interval. Compactness can then be used to obtain a uniform clearance. -/
theorem interior_level_crossing {a b c d target : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (f : ℝ × ℝ → ℝ) (hf : ContinuousOn f (Icc a b ×ˢ Icc c d))
    (lower : ∀ p ∈ Icc a b, f (p, c) < target)
    (upper : ∀ p ∈ Icc a b, target < f (p, d)) :
    ∃ K : Set (ℝ × ℝ), IsCompact K ∧ IsConnected K ∧ K ⊆ Icc a b ×ˢ Ioo c d ∧
      (∀ z ∈ K, f z = target) ∧ Prod.fst '' K = Icc a b := by
  obtain ⟨K, hK, hconn, hsub, hlev, hproj⟩ := level_crossing hab hcd f hf
    (fun p hp ↦ (lower p hp).le) (fun p hp ↦ (upper p hp).le)
  refine ⟨K, hK, hconn, ?_, hlev, hproj⟩
  rintro ⟨p, r⟩ h
  have ⟨hp, hr⟩ := hsub h
  have he := hlev (p, r) h
  exact ⟨hp, lt_of_le_of_ne hr.1 (fun eq ↦ (lower p hp).ne (eq ▸ he)),
    lt_of_le_of_ne hr.2 (fun eq ↦ (upper p hp).ne (eq ▸ he.symm))⟩

/-- Intrinsic version for an action defined only on the product of the two
closed parameter intervals. -/
theorem interior_level_crossing_subtype {a b c d target : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (f : Icc a b × Icc c d → ℝ) (hf : Continuous f)
    (lower : ∀ p, f (p, ⟨c, left_mem_Icc.mpr hcd⟩) < target)
    (upper : ∀ p, target < f (p, ⟨d, right_mem_Icc.mpr hcd⟩)) :
    ∃ K : Set (Icc a b × Icc c d), IsCompact K ∧ IsConnected K ∧
      (∀ p ∈ K, (p.2 : ℝ) ∈ Ioo c d ∧ f p = target) ∧ Prod.fst '' K = univ := by
  let q : ℝ × ℝ → Icc a b × Icc c d := fun z ↦ (projIcc a b hab z.1, projIcc c d hcd z.2)
  have hq : Continuous q := (continuous_projIcc.comp continuous_fst).prodMk
    (continuous_projIcc.comp continuous_snd)
  have low (p : ℝ) (_ : p ∈ Icc a b) : f (q (p,c)) < target := by
    simpa [q] using lower (projIcc a b hab p)
  have high (p : ℝ) (_ : p ∈ Icc a b) : target < f (q (p,d)) := by
    simpa [q] using upper (projIcc a b hab p)
  obtain ⟨K, hc, hconn, hsub, hlev, hproj⟩ :=
    interior_level_crossing hab hcd (f ∘ q) (hf.comp hq).continuousOn low high
  refine ⟨q '' K, hc.image hq, hconn.image _ hq.continuousOn, ?_, eq_univ_of_forall ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨?_, hlev z hz⟩
    change (projIcc c d hcd z.2 : ℝ) ∈ Ioo c d
    rw [projIcc_of_mem hcd (Ioo_subset_Icc_self (hsub hz).2)]
    exact (hsub hz).2
  · intro p
    have hp : (p : ℝ) ∈ Prod.fst '' K := hproj.symm ▸ p.property
    obtain ⟨z, hz, he⟩ := hp
    refine ⟨q z, ⟨z, hz, rfl⟩, ?_⟩
    change projIcc a b hab z.1 = p
    rw [he, projIcc_of_mem hab p.property]

end PlasmaLean.RectangleLevelCrossing
