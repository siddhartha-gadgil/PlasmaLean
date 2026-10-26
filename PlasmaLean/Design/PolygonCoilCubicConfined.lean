/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCubicFrontier

/-!
# Confinement over 52 transits in the field of a concrete polygonal coil set

The windings are the 8 closed polygonal filaments `filsC` (24 vertices each, 192 straight
segments; `Design/PolygonCoilCubicData`, a minimax refit of the design of
`Design/PolygonCoilData`), carrying currents `μ₀I/4π = K/2³²` (`μ₀ = 1`), each parametrised as a
`C¹` closed curve `polyC` (`Design/PolygonCoilCurve`). Their Biot–Savart field is
`polyCoilFieldC`.

* `polyCoilFieldC_eq`: off the coil, `polyCoilFieldC = Bseg filsC`;
* `Ka_sub_UcC`: given the face covers `CoversC`, the closed tube `Ka aF` (`aF = 3420/32761`)
  avoids the coil;
* `polyCoilFieldC_vacuum`: `polyCoilFieldC` is a vacuum field off the coil;
* `polyCoilC_frontier`: given `CoversC`, `‖polyCoilFieldC - hel‖ ≤ etaC·2⁻⁴⁰ ≈ 3.221 × 10⁻⁶` on
  the frontier of `Ωa aF` (`Design/PolygonCoilCubicFrontier`);
* `coil_confined_of_coversC`: given `CoversC`, every field line of `tfField + polyCoilFieldC` on
  `[0, 8·52]` from the start tube stays in the tube `T` and makes at least **52** toroidal
  transits. The covers are proved by the kernel certificates, and the unconditional theorem
  `coil_stellarator_confined_concrete_N` is in `Design/PolygonCoilCubicCover`. (The covers are
  a hypothesis here only so that this module builds in parallel with the certificates.)

**Margins.** With `ζ = 2.5 × 10⁻⁶` (TF filament error) the transit budget
`(δ + (ζ + η) Gc)·8N < I_b - I_a` of `confined_of_error_transits` holds for `N = 52` with
relative margin `≈ 0.016 %`; `N = 53` would need `η < 2.981 × 10⁻⁶`.

**Conditional on the field line.** The theorem is about a given curve `γ` that is a field line
on `[0, 8·52]` (`hγ`); the existence of such a solution is *not* proved in the library.
-/

public section
noncomputable section

namespace PlasmaLean.Design.PolygonCoil
open PlasmaLean.Fields PlasmaLean.Vacuum PlasmaLean.Design.RationalStellarator
  PlasmaLean.Design.RationalStellarator.Coils PlasmaLean.Design.RationalStellarator.CoilsTF
  PlasmaLean.Design.RationalStellarator.Confined Set Real
open scoped RealInnerProductSpace

/-! ## The polygonal filaments as closed curves -/

/-- The vertices of a filament, indexed cyclically. -/
@[expose] def polyVC (vs : List (ℤ × ℤ × ℤ)) (j : ℕ) : Space := ptR (vs.getD (j % vs.length) 0)

/-- The Biot–Savart field (`μ₀ = 1`, `I = 4πK/2³²`) of one closed polygonal filament. -/
@[expose] def polyFieldC (f : ℤ × List (ℤ × ℤ × ℤ)) : Space → Space :=
  filamentField 1 (4 * π * f.1 / S32) (polyC f.2.length (polyVC f.2)) 0 1

/-- **The field of the polygonal coil set.** -/
@[expose] def polyCoilFieldC (y : Space) : Space := (filsC.map fun f => polyFieldC f y).sum

/-- The consecutive pairs of a cyclic list, indexed. -/
theorem zip_rot1_eqC {α : Type} (d : α) (vs : List α) (hne : vs ≠ []) :
    List.zip vs (rot1 vs) = (List.range vs.length).map
      (fun j => (vs.getD j d, vs.getD ((j + 1) % vs.length) d)) := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hne
  apply List.ext_getElem
  · simp [rot1]
  · intro i h1 h2
    simp only [List.getElem_zip, List.getElem_map, List.getElem_range, rot1]
    have hi : i < xs.length + 1 := by simpa using h2
    rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    congr 1
    rw [List.getElem_append]
    split_ifs with h
    · have : (i + 1) % (x :: xs).length = i + 1 := Nat.mod_eq_of_lt (by simp; omega)
      rw [this, List.getD_eq_getElem _ _ (by simp; omega)]
      simp
    · have hi' : i = xs.length := by omega
      have : (i + 1) % (x :: xs).length = 0 := by simp [hi']
      rw [this]; simp

/-- A `Finset.range` sum as a list sum. -/
theorem finset_sum_range_eq_listC {M : Type} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ j ∈ Finset.range n, f j = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append, ih]
    simp

/-- Consecutive cyclic vertices of a filament. -/
theorem polyVC_pair {vs : List (ℤ × ℤ × ℤ)} {j : ℕ} (hj : j < vs.length) :
    (polyVC vs j, polyVC vs (j + 1)) =
      (ptR (vs.getD j 0), ptR (vs.getD ((j + 1) % vs.length) 0)) := by
  simp [polyVC, Nat.mod_eq_of_lt hj]

/-- A point of a polygon is a coil point. -/
theorem coilPt_of_onPolygonC {f : ℤ × List (ℤ × ℤ × ℤ)} (hf : f ∈ filsC) (hne : f.2 ≠ [])
    {y : Space} (hy : onPolygon f.2.length (polyVC f.2) y) : coilPt filsC y := by
  obtain ⟨j, hj, s, hs, rfl⟩ := hy
  have hmem : (f.2.getD j 0, f.2.getD ((j + 1) % f.2.length) 0) ∈ List.zip f.2 (rot1 f.2) := by
    rw [zip_rot1_eqC 0 f.2 hne]
    exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  refine ⟨(f.1, f.2.getD j 0, f.2.getD ((j + 1) % f.2.length) 0),
    mem_allSegs.mpr ⟨f, hf, hmem, rfl⟩, s, hs, ?_⟩
  have := polyVC_pair hj
  simp only [Prod.mk.injEq] at this
  rw [this.1, this.2]

/-- Off the coil, one polygonal filament gives its closed-form segment field. -/
theorem polyFieldC_eq {f : ℤ × List (ℤ × ℤ × ℤ)} (hf : f ∈ filsC) (hne : f.2 ≠ []) {y : Space}
    (hy : ¬ coilPt filsC y) : polyFieldC f y = BF f y := by
  have hN : 0 < f.2.length := List.length_pos_of_ne_nil hne
  unfold polyFieldC
  rw [filamentField_polyC 1 _ hN _ (fun h => hy (coilPt_of_onPolygonC hf hne h))]
  simp only [segField_eq_closed]
  have hκ : 1 * (4 * π * (f.1 : ℝ) / S32) / (4 * π) = (f.1 : ℝ) / S32 := by
    field_simp
  rw [hκ, finset_sum_range_eq_listC, BF, zip_rot1_eqC 0 f.2 hne, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j hj
  have := polyVC_pair (List.mem_range.mp hj)
  simp only [Prod.mk.injEq] at this
  simp only [Function.comp, this.1, this.2]

/-- **Off the coil the polygonal coil field is the closed-form segment field.** -/
theorem polyCoilFieldC_eq {y : Space} (hy : ¬ coilPt filsC y) : polyCoilFieldC y = Bseg filsC
    y := by
  rw [polyCoilFieldC, Bseg_eq_sum]
  congr 1
  apply List.map_congr_left
  intro f hf
  exact polyFieldC_eq hf (filsOK4C.1 f hf) hy

/-! ## The complement of the coil -/

/-- The complement of the coil. -/
@[expose] def UcC : Set Space := {y | ¬ coilPt filsC y}

/-- The complement of the coil is open. -/
theorem isOpen_UcC : IsOpen UcC := by
  have e : {y | coilPt filsC y} = ⋃ z ∈ {z | z ∈ allSegs filsC},
      (seg (ptR z.2.1) (ptR z.2.2)) '' Icc 0 1 := by
    ext y; simp only [coilPt, mem_ofPred_eq, mem_iUnion, mem_image, exists_prop]
    constructor
    · rintro ⟨z, hz, t, ht, rfl⟩; exact ⟨z, hz, t, ht, rfl⟩
    · rintro ⟨z, hz, t, ht, rfl⟩; exact ⟨z, hz, t, ht, rfl⟩
  have hc : IsClosed {y | coilPt filsC y} := by
    rw [e]
    exact (List.finite_toSet _).isClosed_biUnion fun z _ =>
      (isCompact_Icc.image (continuous_seg _ _)).isClosed
  exact hc.isOpen_compl

/-- **The polygonal coil field is a vacuum field off the coil.** -/
theorem polyCoilFieldC_vacuum : VacuumField UcC polyCoilFieldC := by
  have key : ∀ L : List (ℤ × List (ℤ × ℤ × ℤ)), (∀ f ∈ L, f ∈ filsC) →
      VacuumField UcC (fun y => (L.map fun f => polyFieldC f y).sum) := by
    intro L
    induction L with
    | nil => intro _; simpa using vacuumField_zero isOpen_UcC
    | cons f L ih =>
      intro hL
      have hf : f ∈ filsC := hL f (by simp)
      have hne := filsOK4C.1 f hf
      have hN : 0 < f.2.length := List.length_pos_of_ne_nil hne
      have h1 : VacuumField UcC (polyFieldC f) := by
        refine Sanity.filamentField_vacuumField' 1 _ _ 0 1 isOpen_UcC
          (fun t _ => (hasDerivAt_polyC _ _ t).differentiableAt) ?_ ?_ ?_
        · rw [deriv_polyC]; exact (continuous_polyCD _ _).continuousOn
        · intro x hx t ht
          rw [uIcc_of_le zero_le_one] at ht
          exact sub_polyC_ne (fun h => hx (coilPt_of_onPolygonC hf hne h)) ht hN
        · rw [polyC_zero, polyC_one]
          simp [polyVC]
      have h2 := ih fun g hg => hL g (List.mem_cons_of_mem _ hg)
      have := Design.VacuumPair.vacuumField_add h1 h2
      convert this using 1
      funext y; simp
  exact key filsC fun f hf => hf

/-! ## The tube avoids the coil -/

/-- A vertex far from the tube `Ka aF` (integer check). -/
@[expose] def vertFarC (p : ℤ × ℤ × ℤ) : Bool :=
  decide (6840 * 2 ^ 64 < |p.1 * p.1 + p.2.1 * p.2.1 - 2 ^ 64| * 32761) ||
    decide (3420 * 2 ^ 32 < |p.2.2| * 32761)

/-- Every segment starts at a far vertex (explicit certificate `bool_cert`: one comparison leaf
per vertex). -/
theorem vertFarC_all : ((allSegs filsC).all fun z => vertFarC z.2.1) = true := by bool_cert

/-- Meaning of the vertex check `vertFarC`: the vertex lies outside `Ka aF`. -/
theorem vertFarC_sound {p : ℤ × ℤ × ℤ} (h : vertFarC p = true) :
    aF < |sc (ptR p)| ∨ aF < |ptR p 2| := by
  unfold vertFarC at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  have hS : (0 : ℝ) < S32 := S32_pos
  rcases h with h | h
  · left
    have h' : ((6840 * 2 ^ 64 : ℤ) : ℝ) <
        ((|p.1 * p.1 + p.2.1 * p.2.1 - 2 ^ 64| * 32761 : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    have e : sc (ptR p) = ((p.1 : ℝ) * p.1 + p.2.1 * p.2.1 - 2 ^ 64) / (2 * 2 ^ 64) := by
      simp only [sc, r2, ptR, S32]
      simp
      ring
    rw [e, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2 * 2 ^ 64), lt_div_iff₀ (by norm_num),
      aF]
    linarith
  · right
    have h' : ((3420 * 2 ^ 32 : ℤ) : ℝ) < ((|p.2.2| * 32761 : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    have e : ptR p 2 = (p.2.2 : ℝ) / 2 ^ 32 := by simp [ptR, S32]; norm_num
    rw [e, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ 32), lt_div_iff₀ (by norm_num), aF]
    linarith

/-- **The closed tube `Ka aF` avoids the coil.** -/
theorem Ka_sub_UcC (hc : CoversC) : Ka aF ⊆ UcC := by
  intro x hx hc
  obtain ⟨z, hz, t, ht, rfl⟩ := hc
  set c := seg (ptR z.2.1) (ptR z.2.2)
  set F : ℝ → ℝ := fun s => max (|sc (c s)| - aF) (|c s 2| - aF)
  have hFc : Continuous F := by
    have hcc : Continuous c := continuous_seg _ _
    exact ((continuous_abs.comp (continuous_sc.comp hcc)).sub continuous_const).max
      ((continuous_abs.comp ((PiLp.continuous_apply 2 (fun _ => ℝ) 2).comp hcc)).sub
        continuous_const)
  have hF0 : 0 < F 0 := by
    have hv := vertFarC_sound (List.all_eq_true.mp vertFarC_all z hz)
    have e : c 0 = ptR z.2.1 := by simp [c, seg]
    simp only [F, e]
    rcases hv with h | h
    · exact lt_max_of_lt_left (by linarith)
    · exact lt_max_of_lt_right (by linarith)
  have hFt : F t ≤ 0 := max_le (by linarith [hx.1]) (by linarith [hx.2])
  obtain ⟨s, hs, hFs⟩ := intermediate_value_Icc' ht.1 hFc.continuousOn ⟨hFt, hF0.le⟩
  have hfront : FrontPtC (c s) := by
    have h1 : |sc (c s)| - aF ≤ 0 := hFs ▸ le_max_left _ _
    have h2 : |c s 2| - aF ≤ 0 := hFs ▸ le_max_right _ _
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    rcases max_choice (|sc (c s)| - aF) (|c s 2| - aF) with h | h
    · left; have := hFs; simp only [F] at this; rw [h] at this; linarith
    · right; have := hFs; simp only [F] at this; rw [h] at this; linarith
  have hcoil : coilPt filsC (c s) := ⟨z, hz, s, ⟨hs.1, hs.2.trans ht.2⟩, rfl⟩
  have := (frontier_QC hc hfront).2 _ hcoil
  simp at this
  linarith

/-- **The frontier bound for the polygonal coil field.** -/
theorem polyCoilC_frontier (hc : CoversC) :
    ∀ y ∈ frontier (Ωa aF), ‖polyCoilFieldC y - hel y‖ ≤ etaRC := by
  intro y hy
  obtain ⟨hK, hface⟩ := frontier_Ωa hy
  rw [polyCoilFieldC_eq (Ka_sub_UcC hc hK)]
  exact (frontier_QC hc ⟨hK, hface⟩).1

/-- **Confinement over 52 transits, given the face covers.** Every field line of the coil field
`tfField + polyCoilFieldC` (the closed TF filament plus the 8 closed polygonal helical filaments
`filsC`, 192 straight segments) on `[0, 8·52]` starting in the start tube stays in the
confinement tube `T` and its toroidal angle advances by at least `2π·52` (52 transits).

Conditional on the field line: `γ` is assumed to solve the field-line equation on `[0, 8·52]`
(existence is not proved here). The certified winding error is
`etaRC = etaC·2⁻⁴⁰ ≈ 3.221 × 10⁻⁶`. -/
theorem coil_confined_of_coversC (hc : CoversC) {γ : ℝ → Space}
    (hγ : ∀ t ∈ Icc (0 : ℝ) (8 * 52), HasDerivAt γ (coilField polyCoilFieldC (γ t)) t)
    (h0 : γ 0 ∈ startTube) :
    (∀ s ∈ Icc (0 : ℝ) (8 * 52), γ s ∈ tubeT) ∧
      2 * π * 52 ≤ ∫ u in (0 : ℝ)..(8 * 52), phiRateOf (coilField polyCoilFieldC) (γ u) := by
  have ha1 : (1 : ℝ) / 10 < aF := by norm_num [aF]
  have herr := coil_error (helical_error_on_tube ha1 (by norm_num [aF]) etaRC_nonneg
    polyCoilFieldC_vacuum (Ka_sub_UcC hc) (polyCoilC_frontier hc))
  have hcont : ContinuousOn (coilField polyCoilFieldC) tubeT := by
    have hB : ContinuousOn polyCoilFieldC tubeT :=
      polyCoilFieldC_vacuum.contDiffOn.continuousOn.mono fun y hy =>
        Ka_sub_UcC hc ⟨hy.1.trans ha1.le, hy.2.trans ha1.le⟩
    exact continuousOn_tfField.add hB
  have e : (8 * ((52 : ℕ) : ℝ)) = 8 * 52 := by norm_num
  have hη := etaRC_le
  have h := confined_of_error_transits (B' := coilField polyCoilFieldC) 52
    (by unfold ζ; linarith [etaRC_nonneg]) (by unfold ζ; linarith) herr hcont
    (by unfold Gc budget ζ; push_cast; linarith) (γ := γ) (by rw [e]; exact hγ) h0
  rw [e, show ((52 : ℕ) : ℝ) = 52 by norm_num] at h
  exact h

end PlasmaLean.Design.PolygonCoil
