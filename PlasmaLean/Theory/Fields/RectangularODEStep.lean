/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Tactic.Linarith

/-!
# A validated time step on a rectangular tube

A box of componentwise velocities encloses the right hand side throughout a state tube.
If the Euler enclosure at each intermediate time fits in that tube, an exact solution exists
through the step. Its endpoint lies in the narrower endpoint enclosure. Different coordinates
can attain their mean velocities at different times. No contraction test involving the time
step and the Lipschitz constant is required.
-/

public section
namespace PlasmaLean.Fields.RectangularODEStep

open Set Metric
open scoped NNReal

variable {ι : Type*}

private def clip (lo hi x : ι → ℝ) (i : ι) : ℝ := max (lo i) (min (x i) (hi i))

private theorem clip_mem {lo hi : ι → ℝ} (h : lo ≤ hi) (x : ι → ℝ) :
    clip lo hi x ∈ Icc lo hi :=
  ⟨fun _ => le_max_left _ _, fun i => max_le (h i) (min_le_right _ _)⟩

private theorem clip_fixed {lo hi x : ι → ℝ} (h : x ∈ Icc lo hi) : clip lo hi x = x := by
  funext i
  simp [clip, min_eq_left (h.2 i), max_eq_right (h.1 i)]

/-- For a forward step the two endpoint faces suffice to contain the full swept box.
The test works coordinatewise even if a velocity interval crosses zero. -/
theorem tube_of_endpoints {lo hi vlo vhi x₀ : ι → ℝ} {T : ℝ}
    (h₀ : x₀ ∈ Icc lo hi) (hl : lo ≤ x₀ + T • vlo) (hh : x₀ + T • vhi ≤ hi)
    {t : ℝ} (ht : t ∈ Icc 0 T) {v : ι → ℝ} (hv : v ∈ Icc vlo vhi) :
    x₀ + t • v ∈ Icc lo hi := by
  constructor
  · intro i
    change lo i ≤ x₀ i + t * v i
    rcases le_total 0 (v i) with hp | hn
    · linarith [h₀.1 i, mul_nonneg ht.1 hp]
    · have he : lo i ≤ x₀ i + T * vlo i := hl i
      linarith only [he, mul_le_mul_of_nonneg_left (hv.1 i) (ht.1.trans ht.2),
        mul_le_mul_of_nonpos_right ht.2 hn]
  · intro i
    change x₀ i + t * v i ≤ hi i
    rcases le_total (v i) 0 with hn | hp
    · linarith [h₀.2 i, mul_nonpos_of_nonneg_of_nonpos ht.1 hn]
    · have he : x₀ i + T * vhi i ≤ hi i := hh i
      linarith only [he, mul_le_mul_of_nonneg_left (hv.2 i) (ht.1.trans ht.2),
        mul_le_mul_of_nonneg_right ht.2 hp]

variable [Fintype ι]

private theorem clip_dist (lo hi x y : ι → ℝ) :
    dist (clip lo hi x) (clip lo hi y) ≤ dist x y := by
  apply (dist_pi_le_iff dist_nonneg).2
  intro i
  have h := ((LipschitzWith.id.min_const (hi i)).const_max (lo i)).dist_le_mul (x i) (y i)
  exact (by simpa [clip] using h : dist (clip lo hi x i) (clip lo hi y i) ≤ dist (x i) (y i)).trans
    (dist_le_pi_dist x y i)

/-- A componentwise velocity enclosure gives an exact, time-enclosed ODE step on a closed box.
To advance backward use the field with reversed clock and sign. The field needs regularity
only on the supplied spacetime tube. -/
theorem exists_step {f : ℝ → (ι → ℝ) → (ι → ℝ)} {lo hi vlo vhi x₀ : ι → ℝ}
    {T : ℝ} (hT : 0 ≤ T) (hbox : lo ≤ hi) {K : ℝ≥0}
    (hLip : ∀ t ∈ Icc 0 T, LipschitzOnWith K (f t) (Icc lo hi))
    (hCont : ∀ x ∈ Icc lo hi, ContinuousOn (fun t => f t x) (Icc 0 T))
    (hVel : ∀ t ∈ Icc 0 T, ∀ x ∈ Icc lo hi, f t x ∈ Icc vlo vhi)
    (hTube : ∀ t ∈ Icc 0 T, ∀ v ∈ Icc vlo vhi, x₀ + t • v ∈ Icc lo hi) :
    ∃ x : ℝ → (ι → ℝ), x 0 = x₀ ∧ ∀ t ∈ Icc 0 T,
      HasDerivWithinAt x (f t (x t)) (Icc 0 T) t ∧
      x t ∈ Icc lo hi ∧ ∃ v ∈ Icc vlo vhi, x t = x₀ + t • v := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := vlo) (b := vhi)).exists_bound_of_continuousOn
    (f := id) continuousOn_id
  let L : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  have hNorm (t) (ht : t ∈ Icc 0 T) (y) (hy : y ∈ Icc lo hi) : ‖f t y‖ ≤ L :=
    (hM _ (hVel t ht y hy)).trans (le_max_left _ _)
  let g := fun t x => f t (clip lo hi x)
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have pl : IsPicardLindelof g (tmin := 0) (tmax := T) ⟨0, h0⟩ x₀
      ⟨L * T, mul_nonneg L.2 hT⟩ 0 L K := by
    constructor
    · intro t ht
      apply lipschitzOnWith_iff_dist_le_mul.2
      intro x _ y _
      exact ((hLip t ht).dist_le_mul _ (clip_mem hbox x) _ (clip_mem hbox y)).trans
        (mul_le_mul_of_nonneg_left (clip_dist lo hi x y) K.2)
    · exact fun x _ => hCont _ (clip_mem hbox x)
    · exact fun t ht x _ => hNorm t ht _ (clip_mem hbox x)
    · change L * max (T - 0) (0 - 0) ≤ L * T - 0
      simp [max_eq_left hT]
  obtain ⟨x, hx, hd⟩ := pl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨x, hx, fun t ht => ?_⟩
  have reach : ∃ v ∈ Icc vlo vhi, x t = x₀ + t • v := by
    rcases ht.1.eq_or_lt with he | hp
    · subst t
      exact ⟨_, hVel 0 h0 _ (clip_mem hbox x₀), by simpa using hx⟩
    have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
    have ht' (i : ι) : ∃ w ∈ Ioo 0 t, g w (x w) i = (x t i - x 0 i) / (t - 0) := by
      apply exists_hasDerivAt_eq_slope (fun s => x s i) _ hp
      · intro s hs
        exact ((hasDerivWithinAt_pi.mp (hd s (hsub hs)) i).mono hsub).continuousWithinAt
      · intro s hs
        exact (hasDerivWithinAt_pi.mp (hd s (hsub (Ioo_subset_Icc_self hs))) i).hasDerivAt
          (Icc_mem_nhds hs.1 (hs.2.trans_le ht.2))
    choose w hw he using ht'
    have hv (i : ι) := hVel (w i) (hsub (Ioo_subset_Icc_self (hw i))) _ (clip_mem hbox (x (w i)))
    refine ⟨fun i => g (w i) (x (w i)) i, ⟨fun i => (hv i).1 i, fun i => (hv i).2 i⟩, ?_⟩
    funext i
    have hi := (eq_div_iff (by linarith : t - 0 ≠ 0)).mp (he i)
    rw [hx] at hi
    change x t i = x₀ i + t * g (w i) (x (w i)) i
    linarith
  obtain ⟨v, hv, he⟩ := reach
  have hm : x t ∈ Icc lo hi := he ▸ hTube t ht v hv
  exact ⟨by simpa [g, clip_fixed hm] using hd t ht, hm, v, hv, he⟩

end PlasmaLean.Fields.RectangularODEStep
