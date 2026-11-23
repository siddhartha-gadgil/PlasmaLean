/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorHeightAction
public import PlasmaLean.Theory.Geometry.PeriodicOrientedCrossings

/-!
# Comparing mirror actions at fixed trace coordinate

At one height, compare two field lines on a common finite coordinate interval. The
arclength density may change from line to line. Comparing its square times the
signed energy gap controls the clipped integrands through both turning points.
Strict inequality at an accessible point gives strict inequality of the integrals.
For identification with a single mirror-to-mirror action use the forbidden-cap
hypotheses of `action_eq_well_of_crossings` on each line separately.
-/

public section
noncomputable section

open Set Real MeasureTheory

namespace PlasmaLean.Kinetic.MirrorHeightAction

/-- Joint continuity of a finite fixed-bracket action in launch parameters and height
requires joint continuity of the traced quantities only on that bracket. -/
theorem continuousOn_action_family {X : Type*} [TopologicalSpace X] {U : Set X} {f w : X → ℝ → ℝ}
    {g : X → ℝ} {a b : ℝ} (hab : a ≤ b) (hg : ContinuousOn g U)
    (hf : ContinuousOn (fun p : X × ℝ => f p.1 p.2) (U ×ˢ Icc a b))
    (hw : ContinuousOn (fun p : X × ℝ => w p.1 p.2) (U ×ˢ Icc a b)) :
    ContinuousOn (fun x => action (f x) (w x) a b (g x)) U := by
  rw [continuousOn_iff_continuous_domRestrict]
  let trace : U × ℝ → X × ℝ := fun p => (p.1, projIcc a b hab p.2)
  have ct : Continuous trace := (continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd))
  have ht (p : U × ℝ) : trace p ∈ U ×ˢ Icc a b := ⟨p.1.2, (projIcc a b hab p.2).2⟩
  let density := fun (x : U) (t : ℝ) =>
    w x (projIcc a b hab t) * √(2 * (g x - f x (projIcc a b hab t)))
  have hc : Continuous (Function.uncurry density) :=
    (hw.comp_continuous ct ht).mul ((continuous_const.mul
      ((continuousOn_iff_continuous_domRestrict.mp hg).comp continuous_fst |>.sub
        (hf.comp_continuous ct ht))).sqrt)
  have ci := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := MeasureTheory.volume) hc a b
  apply ci.congr
  intro x
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  simp [density, projIcc_of_mem hab ht]

/-- The pointwise fixed-action height is continuous across all launch parameters.
The radial and angular coordinates may vary together in the launch space. -/
theorem exists_continuous_fixed_action_height {X : Type*} [TopologicalSpace X]
    {f w : X → ℝ → ℝ} {a b low high j : ℝ} (hab : a < b) (hh : low ≤ high)
    (hf : ContinuousOn (fun p : X × ℝ => f p.1 p.2) (univ ×ˢ Icc a b))
    (hw : ContinuousOn (fun p : X × ℝ => w p.1 p.2) (univ ×ˢ Icc a b))
    (hn : ∀ x t, t ∈ Icc a b → 0 ≤ w x t)
    (accessible : ∀ x, ∃ t ∈ Icc a b, f x t < low ∧ 0 < w x t)
    (left : ∀ x, action (f x) (w x) a b low < j)
    (right : ∀ x, j < action (f x) (w x) a b high) :
    ∃ u : X → ℝ, Continuous u ∧ ∀ x, u x ∈ Ioo low high ∧
      ∀ h ∈ Icc low high, action (f x) (w x) a b h = j ↔ h = u x := by
  let F := fun p : X × Icc low high => action (f p.1) (w p.1) a b p.2
  have restrict (x : X) {F : X → ℝ → ℝ}
      (hc : ContinuousOn (fun p : X × ℝ => F p.1 p.2) (univ ×ˢ Icc a b)) :
      ContinuousOn (F x) (Icc a b) := hc.comp (continuous_const.prodMk continuous_id).continuousOn
    fun _ ht => ⟨trivial, ht⟩
  have lift {G : X → ℝ → ℝ}
      (hc : ContinuousOn (fun p : X × ℝ => G p.1 p.2) (univ ×ˢ Icc a b)) :
      ContinuousOn (fun p : (X × Icc low high) × ℝ => G p.1.1 p.2) (univ ×ˢ Icc a b) :=
    hc.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd).continuousOn
      fun _ ht => ⟨trivial, ht.2⟩
  have cF : Continuous F := continuousOn_univ.mp (continuousOn_action_family hab.le
    (continuous_subtype_val.comp continuous_snd).continuousOn (lift hf) (lift hw))
  have roots (x : X) : ∃! h : Icc low high, F (x, h) = j := by
    obtain ⟨h, ⟨hr, he⟩, _⟩ := unique_height hab hh (restrict x hf) (restrict x hw)
      (hn x) (accessible x) (left x) (right x)
    have mono := strictMonoOn_action hab (restrict x hf) (restrict x hw) (hn x) (accessible x)
    exact ⟨⟨h, Ioo_subset_Icc_self hr⟩, he, fun k ek =>
      Subtype.ext (mono.injOn k.2.1 hr.1.le (ek.trans he.symm))⟩
  obtain ⟨u, cu, hu⟩ :=
    PeriodicLevelGraphs.exists_continuous_root_of_unique cF continuous_const roots
  refine ⟨fun x => u x, continuous_subtype_val.comp cu, fun x => ?_⟩
  have he := (hu x (u x)).mpr rfl
  change action (f x) (w x) a b (u x) = j at he
  refine ⟨⟨(u x).2.1.lt_of_ne (fun eq => (left x).ne (eq ▸ he)),
    (u x).2.2.lt_of_ne (fun eq => (right x).ne (eq ▸ he.symm))⟩, fun h hh => ?_⟩
  exact (hu x ⟨h, hh⟩).trans Subtype.ext_iff

/-- Squaring the trace density before taking the (clipped) real square root works on
the forbidden side of a mirror as well. -/
theorem density_eq_sqrt_weighted_gap {w : ℝ} (hw : 0 ≤ w) (h f : ℝ) :
    w * √(2 * (h - f)) = √(2 * (w ^ 2 * (h - f))) := by
  rw [show 2 * (w ^ 2 * (h - f)) = w ^ 2 * (2 * (h - f)) by ring,
    sqrt_mul (sq_nonneg w), sqrt_sq hw]

/-- Comparison on the accessible set of the first trace controls the whole integral.
Strict separation of the signed weighted gaps at a point accessible on the second
trace gives a strict action difference. -/
theorem action_lt_of_weighted_gap {a b h : ℝ} {f₁ f₂ w₁ w₂ : ℝ → ℝ} (hab : a < b)
    (hf₁ : ContinuousOn f₁ (Icc a b)) (hf₂ : ContinuousOn f₂ (Icc a b))
    (hw₁ : ContinuousOn w₁ (Icc a b)) (hw₂ : ContinuousOn w₂ (Icc a b))
    (hn₁ : ∀ t ∈ Icc a b, 0 ≤ w₁ t) (hn₂ : ∀ t ∈ Icc a b, 0 ≤ w₂ t)
    (compare : ∀ t ∈ Icc a b, f₁ t < h →
      w₁ t ^ 2 * (h - f₁ t) ≤ w₂ t ^ 2 * (h - f₂ t))
    (strict : ∃ t ∈ Icc a b, 0 < w₂ t ^ 2 * (h - f₂ t) ∧
      w₁ t ^ 2 * (h - f₁ t) < w₂ t ^ 2 * (h - f₂ t)) :
    action f₁ w₁ a b h < action f₂ w₂ a b h := by
  have cont {f w : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) (hw : ContinuousOn w (Icc a b)) :
      ContinuousOn (fun t => w t * √(2 * (h - f t))) (Icc a b) :=
    hw.mul ((continuousOn_const.mul (continuousOn_const.sub hf)).sqrt)
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hab (cont hf₁ hw₁) (cont hf₂ hw₂)
  · intro t ht
    have ht' := Ioc_subset_Icc_self ht
    by_cases allowed : f₁ t < h
    · rw [density_eq_sqrt_weighted_gap (hn₁ t ht'), density_eq_sqrt_weighted_gap (hn₂ t ht')]
      exact sqrt_le_sqrt (by linarith [compare t ht' allowed])
    · rw [sqrt_eq_zero_of_nonpos (show 2 * (h - f₁ t) ≤ 0 by linarith), mul_zero]
      exact mul_nonneg (hn₂ t ht') (sqrt_nonneg _)
  · obtain ⟨t, ht, ha, hs⟩ := strict
    refine ⟨t, ht, ?_⟩
    rw [density_eq_sqrt_weighted_gap (hn₁ t ht), density_eq_sqrt_weighted_gap (hn₂ t ht)]
    exact (sqrt_lt_sqrt_iff_of_pos (by linarith)).mpr (by linarith)

/-- Field strength strictly decreasing across the strip and nonnegative arclength
density nondecreasing across it make the action strictly increase in radius. Each
trace needs only one accessible point of positive density. -/
theorem strictMonoOn_action_of_trace_order {f w : ℝ → ℝ → ℝ} {a b h lo hi : ℝ} (hab : a < b)
    (hf : ∀ u ∈ Icc lo hi, ContinuousOn (f u) (Icc a b))
    (hw : ∀ u ∈ Icc lo hi, ContinuousOn (w u) (Icc a b))
    (hn : ∀ u ∈ Icc lo hi, ∀ t ∈ Icc a b, 0 ≤ w u t)
    (field : ∀ t ∈ Icc a b, StrictAntiOn (fun u => f u t) (Icc lo hi))
    (density : ∀ t ∈ Icc a b, MonotoneOn (fun u => w u t) (Icc lo hi))
    (accessible : ∀ u ∈ Icc lo hi, ∃ t ∈ Icc a b, f u t < h ∧ 0 < w u t) :
    StrictMonoOn (fun u => action (f u) (w u) a b h) (Icc lo hi) := by
  intro u hu v hv huv
  have bounds (t : ℝ) (ht : t ∈ Icc a b) : f v t < f u t ∧ w u t ^ 2 ≤ w v t ^ 2 :=
    ⟨field t ht hu hv huv, by
      have hle : w u t ≤ w v t := density t ht hu hv huv.le
      exact pow_le_pow_left₀ (hn u hu t ht) hle 2⟩
  apply action_lt_of_weighted_gap hab (hf u hu) (hf v hv) (hw u hu) (hw v hv) (hn u hu) (hn v hv)
  · intro t ht hft
    obtain ⟨fl, wl⟩ := bounds t ht
    exact mul_le_mul wl (by linarith) (sub_nonneg.mpr hft.le) (sq_nonneg _)
  · obtain ⟨t, ht, hft, hwt⟩ := accessible u hu
    obtain ⟨fl, wl⟩ := bounds t ht
    have hsq : 0 < w v t ^ 2 := (sq_pos_of_pos hwt).trans_le wl
    refine ⟨t, ht, mul_pos hsq (sub_pos.mpr (fl.trans hft)), ?_⟩
    exact (mul_le_mul_of_nonneg_right wl (sub_nonneg.mpr hft.le)).trans_lt
      (mul_lt_mul_of_pos_left (by linarith) hsq)

/-- If two accessible squared integrands are bounded by `M²`, their square-root
difference is at least their certified increment divided by `2M`. -/
theorem sqrt_gap_ge {p q M k : ℝ} (hM : 0 < M) (hp : 0 ≤ p) (hk : 0 ≤ k)
    (grow : k ≤ q - p) (upper : q ≤ M ^ 2) : k / (2 * M) ≤ √q - √p := by
  have hpq : p ≤ q := by linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hlow := sqrt_le_sqrt hpq
  have hup := sqrt_le_iff.mpr ⟨hM.le, upper⟩
  have hmul := mul_le_mul_of_nonneg_left (show √q + √p ≤ 2 * M by linarith)
    (sub_nonneg.mpr hlow)
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [grow, hmul, sq_sqrt hp, sq_sqrt hq]

/-- A signed squared-integrand increment `k` on the accessible core `[c,d]` gives
an action increment `(d-c)k/(2M)`. Elsewhere the comparison needs only preserve the
ordering of the clipped integrands. The same result applies with `k=m(v-u)` for
any two launch radii `u≤v`. -/
theorem action_gap_ge_of_core {f₁ f₂ w₁ w₂ : ℝ → ℝ} {a b c d h M k : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) (hM : 0 < M) (hk : 0 ≤ k)
    (hf₁ : ContinuousOn f₁ (Icc a b)) (hf₂ : ContinuousOn f₂ (Icc a b))
    (hw₁ : ContinuousOn w₁ (Icc a b)) (hw₂ : ContinuousOn w₂ (Icc a b))
    (hn₁ : ∀ t ∈ Icc a b, 0 ≤ w₁ t) (hn₂ : ∀ t ∈ Icc a b, 0 ≤ w₂ t)
    (compare : ∀ t ∈ Icc a b, f₁ t < h →
      w₁ t ^ 2 * (h - f₁ t) ≤ w₂ t ^ 2 * (h - f₂ t))
    (core : ∀ t ∈ Icc c d,
      0 ≤ 2 * (w₁ t ^ 2 * (h - f₁ t)) ∧
      k ≤ 2 * (w₂ t ^ 2 * (h - f₂ t)) - 2 * (w₁ t ^ 2 * (h - f₁ t)) ∧
      2 * (w₂ t ^ 2 * (h - f₂ t)) ≤ M ^ 2) :
    (d - c) * (k / (2 * M)) ≤ action f₂ w₂ a b h - action f₁ w₁ a b h := by
  let G := fun (f w : ℝ → ℝ) (t : ℝ) => w t * √(2 * (h - f t))
  have cont {f w : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) (hw : ContinuousOn w (Icc a b)) :
      ContinuousOn (G f w) (Icc a b) :=
    hw.mul ((continuousOn_const.mul (continuousOn_const.sub hf)).sqrt)
  let D := fun t => G f₂ w₂ t - G f₁ w₁ t
  have cD : ContinuousOn D (Icc a b) := (cont hf₂ hw₂).sub (cont hf₁ hw₁)
  have hab := hac.trans (hcd.trans hdb)
  have sub := Icc_subset_Icc hac hdb
  have hcompare (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ D t := by
    apply sub_nonneg.mpr
    dsimp [G]
    by_cases allowed : f₁ t < h
    · rw [density_eq_sqrt_weighted_gap (hn₁ t ht), density_eq_sqrt_weighted_gap (hn₂ t ht)]
      exact sqrt_le_sqrt (by linarith [compare t ht allowed])
    · rw [sqrt_eq_zero_of_nonpos (show 2 * (h - f₁ t) ≤ 0 by linarith), mul_zero]
      exact mul_nonneg (hn₂ t ht) (sqrt_nonneg _)
  have hcore (t : ℝ) (ht : t ∈ Icc c d) : k / (2 * M) ≤ D t := by
    dsimp [D, G]
    rw [density_eq_sqrt_weighted_gap (hn₁ t (sub ht)),
      density_eq_sqrt_weighted_gap (hn₂ t (sub ht))]
    obtain ⟨hp, hg, hm⟩ := core t ht
    exact sqrt_gap_ge hM hp hk hg hm
  calc
    _ = ∫ _ in c..d, k / (2 * M) := by rw [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ ∫ t in c..d, D t := intervalIntegral.integral_mono_on hcd intervalIntegrable_const
      ((cD.mono sub).intervalIntegrable_of_Icc hcd) hcore
    _ ≤ ∫ t in a..b, D t := intervalIntegral.integral_mono_interval hac hcd hdb
      ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => hcompare t (Ioc_subset_Icc_self ht))
      (cD.intervalIntegrable_of_Icc hab)
    _ = _ := intervalIntegral.integral_sub ((cont hf₂ hw₂).intervalIntegrable_of_Icc hab)
      ((cont hf₁ hw₁).intervalIntegrable_of_Icc hab)

/-- A decreasing field strength alone permits a decreasing action when the
arclength density also decreases. Both traces in this fixture are accessible. -/
theorem decreasing_density_counterexample :
    action (fun _ => -1) (fun _ => 1) 0 1 1 < action (fun _ => 0) (fun _ => 2) 0 1 1 := by
  apply action_lt_of_weighted_gap zero_lt_one continuousOn_const continuousOn_const
    continuousOn_const continuousOn_const
  · norm_num
  · norm_num
  · norm_num
  · exact ⟨0, by norm_num, by norm_num, by norm_num⟩

end PlasmaLean.Kinetic.MirrorHeightAction
