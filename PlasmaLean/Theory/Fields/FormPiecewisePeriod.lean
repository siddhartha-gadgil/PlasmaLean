/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormLoopCurrentInterval

/-!
# Circulation around piecewise `C¹` loops as a de Rham period

`Theory/Fields/FormLoopCurrentInterval` identifies the circulation of a curl-free field around a
closed curve with a de Rham period when the curve is `C¹` on the whole interval of integration.
Coil and boundary curves are usually only piecewise `C¹` (polygons, loops with corners). This
file treats them: each `C¹` piece is reparametrised by the smooth transition parameter
`smoothParam`, the pieces are concatenated as homotopy classes of paths, and TauCeti's integral
over a path class (`TauCeti.pathClassIntegral`) is additive under concatenation.

* `intervalIntegrable_lineIntegrand`: for `γ` of class `C¹` on `[a, b]` and `B` continuous on
  the image, the integrand `t ↦ ⟪B (γ t), deriv γ t⟫` is interval integrable on `[a, b]`. On
  `(a, b)` it is the continuous function built from the one-sided derivative; the values of
  `deriv γ` at the two end points do not enter.
* `lineIntegral_add_adjacent`: additivity of the line integral over `[a, c]` and `[c, b]`, for a
  curve that is `C¹` on each of the two closed pieces (a corner at `c` is allowed).
* `arcPath`, `pathClassIntegral_arcPath`: **one piece, not necessarily closed.** The integral of
  `B♭` over the class of the reparametrised path from `γ a` to `γ b` is `lineIntegral B γ a b`.
* `lineIntegral_eq_periodHom_two_pieces`: **two pieces.** A closed curve that is `C¹` on
  `[a, c]` and on `[c, b]`: its circulation is the period on the class of the concatenated loop.
* `PiecewiseC1In U γ t n`, `chainClass`, `chainLoop`, `pathClassIntegral_chainClass`,
  `lineIntegral_eq_periodHom_piecewise`: **finitely many pieces.** For a partition
  `t 0 < t 1 < … < t n` with `γ` of class `C¹` on each `[t i, t (i + 1)]` and in `U` there, the
  integral of `B♭` over the concatenated class is `lineIntegral B γ (t 0) (t n)`, and for a
  closed curve this is a period.
* `VacuumField.lineIntegral_eq_zero_of_piecewise`,
  `VacuumField.lineIntegral_eq_zero_of_two_pieces`: a vacuum field on a simply connected region
  has zero circulation around every closed piecewise `C¹` loop in it. This is derived from the
  period (the fundamental group is trivial), not from a potential.
* Polygons: `segCurve`, `polyCurve`, `piecewiseC1In_polyCurve`,
  `sum_lineIntegral_segCurve_eq_periodHom`: for points `p 0, …, p n = p 0` with all edges in
  `U`, the sum of the straight-segment line integrals is the period of the polygonal loop;
  `VacuumField.sum_lineIntegral_segCurve_eq_zero` in a simply connected region.
* `not_differentiableAt_polyCurve`, `not_contDiffOn_polyCurve`: at a vertex where the edge
  vectors differ the polygonal curve is not differentiable, so the theorems for curves that are
  `C¹` on the whole interval do not apply to it.

What is not proved: the partition is finite; nothing is said about curves with infinitely many
corners or rectifiable curves. The partition is indexed by `ℕ` (only the indices `≤ n` matter),
not by `Fin (n + 1)`. The homotopy class of the concatenated loop is not compared with the class
of an affine parametrisation of the same curve. The field is required to be `C¹` and curl-free
on the whole region `U`.
-/

@[expose] public section

namespace PlasmaLean.Forms

open PlasmaLean.Vacuum PlasmaLean.Fields PlasmaLean.Contract
open TauCeti TopologicalSpace Topology
open scoped Manifold RealInnerProductSpace

/-! ## The form `B♭` on an open region -/

section Form

variable {U : Opens Space} {B : Space → Space}

/-- The 1-form `B♭` of a `C¹` field on `U` is a `C¹` form on the manifold `U`. -/
theorem isSmoothForm_onOpens_flat (hB : ContDiffOn ℝ 1 B U) :
    IsSmoothForm 𝓘(ℝ, Space) 1 (onOpens U fun y => flat (B y)) :=
  (isSmoothForm_onOpens_iff U _).2 (flat.toContinuousLinearEquiv.contDiff.comp_contDiffOn hB)

/-- The 1-form `B♭` of a curl-free field on `U` is closed on the manifold `U`. -/
theorem mextDeriv_onOpens_flat_eq_zero (hcurl : ∀ x ∈ U, fieldCurl B x = 0) :
    mextDeriv (onOpens U fun y => flat (B y)) = 0 :=
  (mextDeriv_onOpens_eq_zero_iff U _).2 fun y hy => by
    rw [extDeriv_flat, hcurl y hy, map_zero]

end Form

/-! ## One piece -/

section Arc

variable {U : Opens Space} {B : Space → Space} {γ : ℝ → Space} {a b c : ℝ}

/-- **Integrability of the circulation integrand on one piece.** For `γ` of class `C¹` on
`[a, b]` and `B` continuous on the image of `[a, b]`, the function `t ↦ ⟪B (γ t), deriv γ t⟫` is
interval integrable on `[a, b]`. On the open interval it agrees with the function built from the
one-sided derivative, which is continuous on `[a, b]`; the values at `a` and `b` (where
`deriv γ` need not be the one-sided derivative) form a null set. -/
theorem intervalIntegrable_lineIntegrand (hab : a ≤ b) (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b))
    (hB : ContinuousOn B (γ '' Set.Icc a b)) :
    IntervalIntegrable (fun t => ⟪B (γ t), deriv γ t⟫) MeasureTheory.volume a b := by
  rcases hab.eq_or_lt with rfl | hlt
  · exact IntervalIntegrable.refl
  have hud : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hlt
  have hgc : ContinuousOn (fun u => ⟪B (γ u), derivWithin γ (Set.Icc a b) u⟫) (Set.Icc a b) :=
    (hB.comp hγ.continuousOn (Set.mapsTo_image γ _)).inner
      (hγ.continuousOn_derivWithin hud le_rfl)
  have h1 : IntervalIntegrable (fun u => ⟪B (γ u), derivWithin γ (Set.Icc a b) u⟫)
      MeasureTheory.volume a b := hgc.intervalIntegrable_of_Icc hab
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab] at h1 ⊢
  refine h1.congr_fun (fun u hu => ?_) measurableSet_Ioo
  simp only
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hu.1 hu.2)]

/-- **Additivity of the line integral over adjacent pieces.** The curve is `C¹` on `[a, c]` and
on `[c, b]` separately; the one-sided derivatives at `c` need not agree. The field is continuous
on the image of each piece. -/
theorem lineIntegral_add_adjacent (hac : a ≤ c) (hcb : c ≤ b)
    (hγ₁ : ContDiffOn ℝ 1 γ (Set.Icc a c)) (hγ₂ : ContDiffOn ℝ 1 γ (Set.Icc c b))
    (hB₁ : ContinuousOn B (γ '' Set.Icc a c)) (hB₂ : ContinuousOn B (γ '' Set.Icc c b)) :
    lineIntegral B γ a c + lineIntegral B γ c b = lineIntegral B γ a b :=
  intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_lineIntegrand hac hγ₁ hB₁)
    (intervalIntegrable_lineIntegrand hcb hγ₂ hB₂)

/-- The curve `γ` over `[a, b]`, traversed by the smooth parameter, as a path in the open region
`U` from `γ a` to `γ b`. It needs `γ` to be continuous on `[a, b]` and to lie in `U` there; the
curve need not close up. -/
noncomputable def arcPath (hab : a ≤ b) (hU : ∀ t ∈ Set.Icc a b, γ t ∈ U)
    (hcont : ContinuousOn γ (Set.Icc a b)) :
    Path (⟨γ a, hU a (Set.left_mem_Icc.2 hab)⟩ : U) ⟨γ b, hU b (Set.right_mem_Icc.2 hab)⟩ where
  toFun t := intervalCurve γ hab hU t
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact hcont.comp_continuous
      ((contDiff_smoothParam a b).continuous.comp continuous_subtype_val)
      fun t => smoothParam_mem_Icc hab t
  source' := Subtype.ext (by simp)
  target' := Subtype.ext (by simp)

/-- The path `arcPath` follows the reparametrised curve `intervalCurve`. -/
theorem arcPath_apply (hab : a ≤ b) (hU : ∀ t ∈ Set.Icc a b, γ t ∈ U)
    (hcont : ContinuousOn γ (Set.Icc a b)) (t : unitInterval) :
    arcPath hab hU hcont t = intervalCurve γ hab hU t :=
  rfl

/-- **One piece: the integral over the path class is the line integral.** For a field `B` that
is `C¹` and curl-free on the open region `U`, and a curve `γ` that is `C¹` on `[a, b]` and lies
in `U` there, TauCeti's integral of the closed 1-form `B♭` over the homotopy class of the path
`arcPath` from `γ a` to `γ b` is `lineIntegral B γ a b`. The curve need not close up. -/
theorem pathClassIntegral_arcPath (hB : ContDiffOn ℝ 1 B U)
    (hcurl : ∀ x ∈ U, fieldCurl B x = 0) (hab : a < b) (hU : ∀ t ∈ Set.Icc a b, γ t ∈ U)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b)) :
    pathClassIntegral (onOpens U fun y => flat (B y))
        (.mk (arcPath hab.le hU hγ.continuousOn)) = lineIntegral B γ a b := by
  have himg : γ '' Set.Icc a b ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩
    exact hU t ht
  have hcm : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Space) 1 (intervalCurve γ hab.le hU) :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, Space)) (n := 1) U
      (intervalCurve γ hab.le hU)).1 (contDiff_comp_smoothParam hab.le hγ).contMDiff
  rw [pathClassIntegral_mk_eq_pathIntegral (isSmoothForm_onOpens_flat hB)
    (mextDeriv_onOpens_flat_eq_zero hcurl) hcm (fun _ => rfl), pathIntegral_onOpens_flat]
  exact lineIntegral_comp_smoothParam hab hγ (hB.continuousOn.mono himg)

/-- **Two pieces: the circulation around a closed curve with one corner is a de Rham period.**
For a field `B` that is `C¹` and curl-free on the open region `U`, and a curve `γ` that is `C¹`
on `[a, c]` and on `[c, b]` (so continuous on `[a, b]`, with a corner allowed at `c`), lies in
`U` on both pieces and closes up, the circulation over `[a, b]` is the period of `B♭` on the
class of the concatenation of the two reparametrised pieces. -/
theorem lineIntegral_eq_periodHom_two_pieces (hB : ContDiffOn ℝ 1 B U)
    (hcurl : ∀ x ∈ U, fieldCurl B x = 0) (hac : a < c) (hcb : c < b)
    (hU₁ : ∀ t ∈ Set.Icc a c, γ t ∈ U) (hU₂ : ∀ t ∈ Set.Icc c b, γ t ∈ U)
    (hγ₁ : ContDiffOn ℝ 1 γ (Set.Icc a c)) (hγ₂ : ContDiffOn ℝ 1 γ (Set.Icc c b))
    (hclosed : γ a = γ b) :
    lineIntegral B γ a b
      = periodHom (onOpens U fun y => flat (B y)) ⟨γ a, hU₁ a (Set.left_mem_Icc.2 hac.le)⟩
          (Additive.ofMul (.of (.mk (((arcPath hac.le hU₁ hγ₁.continuousOn).trans
            (arcPath hcb.le hU₂ hγ₂.continuousOn)).cast rfl (Subtype.ext hclosed))))) := by
  have himg₁ : γ '' Set.Icc a c ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩
    exact hU₁ t ht
  have himg₂ : γ '' Set.Icc c b ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩
    exact hU₂ t ht
  rw [periodHom_apply]
  change _ = pathClassIntegral _ (.mk _)
  rw [Path.Homotopic.Quotient.mk_cast, pathClassIntegral_cast,
    Path.Homotopic.Quotient.mk_trans, pathClassIntegral_trans,
    pathClassIntegral_arcPath hB hcurl hac hU₁ hγ₁,
    pathClassIntegral_arcPath hB hcurl hcb hU₂ hγ₂]
  exact (lineIntegral_add_adjacent hac.le hcb.le hγ₁ hγ₂ (hB.continuousOn.mono himg₁)
    (hB.continuousOn.mono himg₂)).symm

/-- **A vacuum field in a simply connected region has zero circulation around a closed curve
with one corner.** Derived from the period: the fundamental group of the region is trivial. -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.lineIntegral_eq_zero_of_two_pieces
    [SimplyConnectedSpace U] (h : VacuumField U B) (hac : a < c) (hcb : c < b)
    (hU₁ : ∀ t ∈ Set.Icc a c, γ t ∈ U) (hU₂ : ∀ t ∈ Set.Icc c b, γ t ∈ U)
    (hγ₁ : ContDiffOn ℝ 1 γ (Set.Icc a c)) (hγ₂ : ContDiffOn ℝ 1 γ (Set.Icc c b))
    (hclosed : γ a = γ b) : lineIntegral B γ a b = 0 := by
  rw [lineIntegral_eq_periodHom_two_pieces (h.contDiffOn.of_le (by norm_num)) h.curl_eq_zero hac
    hcb hU₁ hU₂ hγ₁ hγ₂ hclosed]
  have h1 (x : U) (g : FundamentalGroup U x) :
      periodHom (onOpens U fun y => flat (B y)) x (Additive.ofMul g) = 0 := by
    rw [Subsingleton.elim g 1, ofMul_one, map_zero]
  exact h1 _ _

end Arc

/-! ## Finitely many pieces -/

section Piecewise

variable {U : Opens Space} {B : Space → Space} {γ : ℝ → Space} {t : ℕ → ℝ} {n : ℕ}

/-- **A piecewise `C¹` curve in `U`.** The partition points are `t 0 < t 1 < … < t n`; on each
closed piece `[t i, t (i + 1)]`, `i < n`, the curve `γ` is `C¹` (one-sided at the end points)
and lies in `U`. Corners are allowed at the partition points. Only the values `t i` with `i ≤ n`
matter. The field `mem_zero` follows from `mem` when `0 < n`; it is listed so that the trivial
partition `n = 0` has a base point. -/
structure PiecewiseC1In (U : Opens Space) (γ : ℝ → Space) (t : ℕ → ℝ) (n : ℕ) : Prop where
  /-- The partition is strictly increasing. -/
  lt : ∀ i < n, t i < t (i + 1)
  /-- Each piece lies in `U`. -/
  mem : ∀ i < n, ∀ s ∈ Set.Icc (t i) (t (i + 1)), γ s ∈ U
  /-- The curve is `C¹` on each closed piece. -/
  contDiffOn : ∀ i < n, ContDiffOn ℝ 1 γ (Set.Icc (t i) (t (i + 1)))
  /-- The starting point lies in `U`. -/
  mem_zero : γ (t 0) ∈ U

namespace PiecewiseC1In

/-- Forgetting the last piece. -/
theorem pred (h : PiecewiseC1In U γ t (n + 1)) : PiecewiseC1In U γ t n :=
  ⟨fun i hi => h.lt i (hi.trans n.lt_succ_self), fun i hi => h.mem i (hi.trans n.lt_succ_self),
    fun i hi => h.contDiffOn i (hi.trans n.lt_succ_self), h.mem_zero⟩

/-- The end point lies in `U`. -/
theorem mem_last (h : PiecewiseC1In U γ t n) : γ (t n) ∈ U := by
  cases n with
  | zero => exact h.mem_zero
  | succ n =>
    exact h.mem n n.lt_succ_self _ (Set.right_mem_Icc.2 (h.lt n n.lt_succ_self).le)

/-- Each partition point lies in `U`. -/
theorem mem_point (h : PiecewiseC1In U γ t n) {i : ℕ} (hi : i ≤ n) : γ (t i) ∈ U := by
  rcases hi.eq_or_lt with rfl | hlt
  · exact h.mem_last
  · exact h.mem i hlt _ (Set.left_mem_Icc.2 (h.lt i hlt).le)

/-- The partition is monotone up to `n`. -/
theorem le_of_le (h : PiecewiseC1In U γ t n) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    t i ≤ t j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (ih (Nat.le_of_succ_le hj)).trans (h.lt j hj).le

/-- The whole curve over `[t 0, t n]` lies in `U`. -/
theorem mem_Icc (h : PiecewiseC1In U γ t n) : ∀ s ∈ Set.Icc (t 0) (t n), γ s ∈ U := by
  induction n with
  | zero =>
    intro s hs
    rw [le_antisymm hs.2 hs.1]
    exact h.mem_zero
  | succ n ih =>
    intro s hs
    rcases le_total s (t n) with hsn | hsn
    · exact ih h.pred s ⟨hs.1, hsn⟩
    · exact h.mem n n.lt_succ_self s ⟨hsn, hs.2⟩

/-- A two-piece curve as a partition with `n = 2`. -/
theorem of_two_pieces {a b c : ℝ} (hac : a < c) (hcb : c < b)
    (hU₁ : ∀ s ∈ Set.Icc a c, γ s ∈ U) (hU₂ : ∀ s ∈ Set.Icc c b, γ s ∈ U)
    (hγ₁ : ContDiffOn ℝ 1 γ (Set.Icc a c)) (hγ₂ : ContDiffOn ℝ 1 γ (Set.Icc c b)) :
    PiecewiseC1In U γ (fun i => if i = 0 then a else if i = 1 then c else b) 2 := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, ?_⟩
  · interval_cases i
    · simpa using hac
    · simpa using hcb
  · interval_cases i
    · simpa using hU₁
    · simpa using hU₂
  · interval_cases i
    · simpa using hγ₁
    · simpa using hγ₂
  · simpa using hU₁ a (Set.left_mem_Icc.2 hac.le)

end PiecewiseC1In

/-- **The line integral over the whole interval is the sum over the pieces.** The field is
continuous on `U`. The integrability used is `intervalIntegrable_lineIntegrand` on each piece. -/
theorem sum_lineIntegral_pieces (hB : ContinuousOn B U) (h : PiecewiseC1In U γ t n) :
    ∑ i ∈ Finset.range n, lineIntegral B γ (t i) (t (i + 1)) = lineIntegral B γ (t 0) (t n) :=
  intervalIntegral.sum_integral_adjacent_intervals fun i hi =>
    intervalIntegrable_lineIntegrand (h.lt i hi).le (h.contDiffOn i hi)
      (hB.mono (by
        rintro _ ⟨s, hs, rfl⟩
        exact h.mem i hi s hs))

/-- The homotopy class, in `U`, of the piecewise `C¹` curve from `γ (t 0)` to `γ (t n)`: the
concatenation of the classes of the reparametrised pieces `arcPath`, in order. -/
noncomputable def chainClass : {n : ℕ} → (h : PiecewiseC1In U γ t n) →
    Path.Homotopic.Quotient (⟨γ (t 0), h.mem_zero⟩ : U) ⟨γ (t n), h.mem_last⟩
  | 0, h => Path.Homotopic.Quotient.refl (⟨γ (t 0), h.mem_zero⟩ : U)
  | n + 1, h => (chainClass h.pred).trans
      (.mk (arcPath (h.lt n n.lt_succ_self).le (h.mem n n.lt_succ_self)
        (h.contDiffOn n n.lt_succ_self).continuousOn))

/-- The class of the trivial partition is the constant class. -/
theorem chainClass_zero (h : PiecewiseC1In U γ t 0) :
    chainClass h = Path.Homotopic.Quotient.refl (⟨γ (t 0), h.mem_zero⟩ : U) :=
  rfl

/-- The class of a partition with one more piece is the concatenation with that piece. -/
theorem chainClass_succ (h : PiecewiseC1In U γ t (n + 1)) :
    chainClass h = (chainClass h.pred).trans
      (.mk (arcPath (h.lt n n.lt_succ_self).le (h.mem n n.lt_succ_self)
        (h.contDiffOn n n.lt_succ_self).continuousOn)) :=
  rfl

/-- **Finitely many pieces, as a sum.** The integral of `B♭` over the class of a piecewise `C¹`
curve is the sum of the line integrals over the pieces. -/
theorem pathClassIntegral_chainClass_eq_sum (hB : ContDiffOn ℝ 1 B U)
    (hcurl : ∀ x ∈ U, fieldCurl B x = 0) (h : PiecewiseC1In U γ t n) :
    pathClassIntegral (onOpens U fun y => flat (B y)) (chainClass h)
      = ∑ i ∈ Finset.range n, lineIntegral B γ (t i) (t (i + 1)) := by
  induction n with
  | zero => rw [chainClass_zero, pathClassIntegral_refl, Finset.sum_range_zero]
  | succ n ih =>
    rw [chainClass_succ, pathClassIntegral_trans, ih h.pred,
      pathClassIntegral_arcPath hB hcurl (h.lt n n.lt_succ_self) (h.mem n n.lt_succ_self)
        (h.contDiffOn n n.lt_succ_self), Finset.sum_range_succ]

/-- **Finitely many pieces: the integral over the path class is the line integral.** For a
field `B` that is `C¹` and curl-free on `U` and a piecewise `C¹` curve `γ` in `U` (not
necessarily closed), the integral of `B♭` over the class `chainClass` is
`lineIntegral B γ (t 0) (t n)`. -/
theorem pathClassIntegral_chainClass (hB : ContDiffOn ℝ 1 B U)
    (hcurl : ∀ x ∈ U, fieldCurl B x = 0) (h : PiecewiseC1In U γ t n) :
    pathClassIntegral (onOpens U fun y => flat (B y)) (chainClass h)
      = lineIntegral B γ (t 0) (t n) := by
  rw [pathClassIntegral_chainClass_eq_sum hB hcurl h, sum_lineIntegral_pieces hB.continuousOn h]

/-- The element of the fundamental group of `U` at `γ (t 0)` given by a closed piecewise `C¹`
curve. -/
noncomputable def chainLoop (h : PiecewiseC1In U γ t n) (hclosed : γ (t 0) = γ (t n)) :
    FundamentalGroup U ⟨γ (t 0), h.mem_zero⟩ :=
  .of ((chainClass h).cast rfl (Subtype.ext hclosed))

/-- **The circulation around a closed piecewise `C¹` curve is a de Rham period.** For a field
`B` that is `C¹` and curl-free on the open region `U`, and a curve `γ` that is `C¹` on each
piece `[t i, t (i + 1)]` of a partition `t 0 < … < t n`, lies in `U` there and closes up, the
circulation of `B` along `γ` over `[t 0, t n]` is the period of the closed 1-form `B♭` on the
class of the concatenated loop. -/
theorem lineIntegral_eq_periodHom_piecewise (hB : ContDiffOn ℝ 1 B U)
    (hcurl : ∀ x ∈ U, fieldCurl B x = 0) (h : PiecewiseC1In U γ t n)
    (hclosed : γ (t 0) = γ (t n)) :
    lineIntegral B γ (t 0) (t n)
      = periodHom (onOpens U fun y => flat (B y)) ⟨γ (t 0), h.mem_zero⟩
          (Additive.ofMul (chainLoop h hclosed)) := by
  rw [periodHom_apply]
  change _ = pathClassIntegral _ ((chainClass h).cast rfl (Subtype.ext hclosed))
  rw [pathClassIntegral_cast, pathClassIntegral_chainClass hB hcurl h]

/-- **Topology forbids a net circulation, piecewise `C¹` loops.** A vacuum field on a simply
connected open region has zero circulation around every closed piecewise `C¹` curve in the
region. The proof goes through the period: the loop class is trivial because the fundamental
group of the region is, and the period homomorphism vanishes on the trivial class. No potential
is constructed. -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.lineIntegral_eq_zero_of_piecewise
    [SimplyConnectedSpace U] (hV : VacuumField U B) (h : PiecewiseC1In U γ t n)
    (hclosed : γ (t 0) = γ (t n)) : lineIntegral B γ (t 0) (t n) = 0 := by
  rw [lineIntegral_eq_periodHom_piecewise (hV.contDiffOn.of_le (by norm_num)) hV.curl_eq_zero h
    hclosed, Subsingleton.elim (chainLoop h hclosed) 1, ofMul_one, map_zero]

end Piecewise

/-! ## Polygons -/

section Polygon

variable {U : Opens Space} {B : Space → Space} {p : ℕ → Space} {n : ℕ}

/-- The straight segment from `p` to `q`, parametrised by `s ∈ [0, 1]`. -/
def segCurve (p q : Space) (s : ℝ) : Space := p + s • (q - p)

/-- The segment starts at `p`. -/
@[simp] theorem segCurve_zero (p q : Space) : segCurve p q 0 = p := by
  simp [segCurve]

/-- The segment ends at `q`. -/
@[simp] theorem segCurve_one (p q : Space) : segCurve p q 1 = q := by
  simp [segCurve]

/-- The velocity of the segment is `q - p`. -/
theorem hasDerivAt_segCurve (p q : Space) (s : ℝ) : HasDerivAt (segCurve p q) (q - p) s := by
  have h := ((hasDerivAt_id s).smul_const (q - p)).const_add p
  rw [one_smul] at h
  exact h

/-- The velocity of the shifted segment `u ↦ segCurve p q (u - d)` is `q - p`. -/
theorem hasDerivAt_segCurve_sub (p q : Space) (d s : ℝ) :
    HasDerivAt (fun u : ℝ => segCurve p q (u - d)) (q - p) s := by
  have h := (((hasDerivAt_id s).sub_const d).smul_const (q - p)).const_add p
  rw [one_smul] at h
  exact h

/-- The segment is a smooth curve. -/
theorem contDiff_segCurve (p q : Space) : ContDiff ℝ 1 (segCurve p q) :=
  contDiff_const.add (contDiff_id.smul contDiff_const)

/-- The line integral along a segment, with the velocity written out. -/
theorem lineIntegral_segCurve (B : Space → Space) (p q : Space) :
    lineIntegral B (segCurve p q) 0 1 = ∫ s in (0 : ℝ)..1, ⟪B (segCurve p q s), q - p⟫ := by
  unfold lineIntegral
  congr 1
  funext s
  rw [(hasDerivAt_segCurve p q s).deriv]

/-- The polygonal curve through the points `p 0, p 1, …`: on `[i, i + 1]` it is the straight
segment from `p i` to `p (i + 1)`. -/
noncomputable def polyCurve (p : ℕ → Space) (s : ℝ) : Space :=
  segCurve (p ⌊s⌋₊) (p (⌊s⌋₊ + 1)) (s - ⌊s⌋₊)

/-- On the closed interval `[i, i + 1]` the polygonal curve is the `i`-th segment, including at
the right end point. -/
theorem polyCurve_eq_of_mem (p : ℕ → Space) (i : ℕ) {s : ℝ}
    (hs : s ∈ Set.Icc (i : ℝ) ((i + 1 : ℕ) : ℝ)) :
    polyCurve p s = segCurve (p i) (p (i + 1)) (s - i) := by
  have h0 : (0 : ℝ) ≤ s := (Nat.cast_nonneg i).trans hs.1
  rcases hs.2.eq_or_lt with rfl | hlt
  · unfold polyCurve
    rw [Nat.floor_natCast]
    simp [segCurve]
  · have hfl : ⌊s⌋₊ = i := (Nat.floor_eq_iff h0).2 ⟨hs.1, by exact_mod_cast hlt⟩
    unfold polyCurve
    rw [hfl]

/-- The polygonal curve passes through the vertices. -/
@[simp] theorem polyCurve_natCast (p : ℕ → Space) (i : ℕ) : polyCurve p (i : ℝ) = p i := by
  simp [polyCurve]

/-- **A polygon is a piecewise `C¹` curve.** If every edge `[p i, p (i + 1)]`, `i < n`, lies in
`U`, the polygonal curve with the partition `0 < 1 < … < n` is piecewise `C¹` in `U`. -/
theorem piecewiseC1In_polyCurve (hn : 0 < n)
    (hedge : ∀ i < n, ∀ s ∈ Set.Icc (0 : ℝ) 1, segCurve (p i) (p (i + 1)) s ∈ U) :
    PiecewiseC1In U (polyCurve p) (fun i => (i : ℝ)) n := by
  refine ⟨fun i _ => by simp, fun i hi s hs => ?_, fun i _ => ?_, ?_⟩
  · rw [polyCurve_eq_of_mem p i hs]
    refine hedge i hi _ ⟨sub_nonneg.2 hs.1, ?_⟩
    have := hs.2
    push_cast at this
    linarith
  · have hc : ContDiff ℝ 1 fun s : ℝ => segCurve (p i) (p (i + 1)) (s - i) :=
      (contDiff_segCurve _ _).comp (contDiff_id.sub contDiff_const)
    exact hc.contDiffOn.congr fun s hs => polyCurve_eq_of_mem p i hs
  · rw [polyCurve_natCast]
    simpa using hedge 0 hn 0 ⟨le_rfl, zero_le_one⟩

/-- The line integral along the `i`-th piece of the polygonal curve is the line integral along
the `i`-th segment. No hypothesis on the field. -/
theorem lineIntegral_polyCurve_piece (B : Space → Space) (p : ℕ → Space) (i : ℕ) :
    lineIntegral B (polyCurve p) (i : ℝ) ((i + 1 : ℕ) : ℝ)
      = lineIntegral B (segCurve (p i) (p (i + 1))) 0 1 := by
  have hle : (i : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by simp
  have h1 : lineIntegral B (polyCurve p) (i : ℝ) ((i + 1 : ℕ) : ℝ)
      = ∫ s in (i : ℝ)..((i + 1 : ℕ) : ℝ),
          ⟪B (segCurve (p i) (p (i + 1)) (s - i)), p (i + 1) - p i⟫ := by
    rw [lineIntegral, intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle,
      MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
    have hev : polyCurve p =ᶠ[𝓝 s] fun u => segCurve (p i) (p (i + 1)) (u - i) := by
      filter_upwards [Icc_mem_nhds hs.1 hs.2] with u hu using polyCurve_eq_of_mem p i hu
    rw [hev.deriv_eq, (hasDerivAt_segCurve_sub (p i) (p (i + 1)) (i : ℝ) s).deriv,
      polyCurve_eq_of_mem p i ⟨hs.1.le, hs.2.le⟩]
  rw [h1, lineIntegral_segCurve,
    intervalIntegral.integral_comp_sub_right
      (fun s => ⟪B (segCurve (p i) (p (i + 1)) s), p (i + 1) - p i⟫) (i : ℝ)]
  simp

/-- **The circulation around a polygon is a de Rham period.** For a field `B` that is `C¹` and
curl-free on the open region `U`, and points `p 0, …, p n = p 0` (`0 < n`) whose consecutive
edges lie in `U`, the sum of the line integrals of `B` along the edges is the period of `B♭` on
the class of the polygonal loop. -/
theorem sum_lineIntegral_segCurve_eq_periodHom (hB : ContDiffOn ℝ 1 B U)
    (hcurl : ∀ x ∈ U, fieldCurl B x = 0) (hn : 0 < n)
    (hedge : ∀ i < n, ∀ s ∈ Set.Icc (0 : ℝ) 1, segCurve (p i) (p (i + 1)) s ∈ U)
    (hclosed : p 0 = p n) :
    ∑ i ∈ Finset.range n, lineIntegral B (segCurve (p i) (p (i + 1))) 0 1
      = periodHom (onOpens U fun y => flat (B y))
          ⟨polyCurve p ((0 : ℕ) : ℝ), (piecewiseC1In_polyCurve hn hedge).mem_zero⟩
          (Additive.ofMul (chainLoop (piecewiseC1In_polyCurve hn hedge)
            (by rw [polyCurve_natCast, polyCurve_natCast]; exact hclosed))) := by
  rw [← lineIntegral_eq_periodHom_piecewise hB hcurl (piecewiseC1In_polyCurve hn hedge),
    ← sum_lineIntegral_pieces hB.continuousOn (piecewiseC1In_polyCurve hn hedge)]
  exact Finset.sum_congr rfl fun i _ => (lineIntegral_polyCurve_piece B p i).symm

/-- **A vacuum field in a simply connected region has zero circulation around every polygon in
it.** Derived from the period. -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.sum_lineIntegral_segCurve_eq_zero
    [SimplyConnectedSpace U] (hV : VacuumField U B) (hn : 0 < n)
    (hedge : ∀ i < n, ∀ s ∈ Set.Icc (0 : ℝ) 1, segCurve (p i) (p (i + 1)) s ∈ U)
    (hclosed : p 0 = p n) :
    ∑ i ∈ Finset.range n, lineIntegral B (segCurve (p i) (p (i + 1))) 0 1 = 0 := by
  rw [sum_lineIntegral_segCurve_eq_periodHom (hV.contDiffOn.of_le (by norm_num))
    hV.curl_eq_zero hn hedge hclosed, Subsingleton.elim (chainLoop _ _) 1, ofMul_one, map_zero]

/-- **A polygon has a genuine corner where the edge vectors differ.** At the vertex `p (i + 1)`
the polygonal curve has left derivative `p (i + 1) - p i` and right derivative
`p (i + 2) - p (i + 1)`; if these differ, it is not differentiable there. -/
theorem not_differentiableAt_polyCurve (p : ℕ → Space) (i : ℕ)
    (hne : p (i + 1) - p i ≠ p (i + 1 + 1) - p (i + 1)) :
    ¬ DifferentiableAt ℝ (polyCurve p) ((i + 1 : ℕ) : ℝ) := by
  intro hd
  have hD := hd.hasDerivAt
  have hside (j : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (j : ℝ) ((j + 1 : ℕ) : ℝ)) :
      HasDerivWithinAt (polyCurve p) (p (j + 1) - p j) (Set.Icc (j : ℝ) ((j + 1 : ℕ) : ℝ))
        x := by
    exact (hasDerivAt_segCurve_sub (p j) (p (j + 1)) (j : ℝ) x).hasDerivWithinAt.congr
      (fun u hu => polyCurve_eq_of_mem p j hu) (polyCurve_eq_of_mem p j hx)
  have hlt (j : ℕ) : (j : ℝ) < ((j + 1 : ℕ) : ℝ) := by simp
  have hl : ((i + 1 : ℕ) : ℝ) ∈ Set.Icc (i : ℝ) ((i + 1 : ℕ) : ℝ) :=
    Set.right_mem_Icc.2 (hlt i).le
  have hr : ((i + 1 : ℕ) : ℝ) ∈ Set.Icc ((i + 1 : ℕ) : ℝ) ((i + 1 + 1 : ℕ) : ℝ) :=
    Set.left_mem_Icc.2 (hlt (i + 1)).le
  have e1 := (uniqueDiffOn_Icc (hlt i) _ hl).eq_deriv _ hD.hasDerivWithinAt (hside i hl)
  have e2 := (uniqueDiffOn_Icc (hlt (i + 1)) _ hr).eq_deriv _ hD.hasDerivWithinAt
    (hside (i + 1) hr)
  exact hne (e1.symm.trans e2)

/-- **A polygon with a genuine corner is not `C¹` on the whole interval.** So the theorems of
`Theory/Fields/FormLoopCurrentInterval` do not apply to it. -/
theorem not_contDiffOn_polyCurve (p : ℕ → Space) {i n : ℕ} (hi : i + 1 < n)
    (hne : p (i + 1) - p i ≠ p (i + 1 + 1) - p (i + 1)) :
    ¬ ContDiffOn ℝ 1 (polyCurve p) (Set.Icc (0 : ℝ) n) := fun h =>
  not_differentiableAt_polyCurve p i hne
    ((h.differentiableOn one_ne_zero).differentiableAt
      (Icc_mem_nhds (by positivity) (by exact_mod_cast hi)))

end Polygon

end PlasmaLean.Forms
