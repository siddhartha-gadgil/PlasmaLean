/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormLoopCurrent
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The loop current as a de Rham period: hypotheses on one period of the loop only

`Theory/Fields/FormLoopCurrent` identifies the poloidal circulation of the stellarator contract
with a de Rham period, for a poloidal loop that lies in the open region `U` and is `C¹` for
every real value of the parameter. Only `θ ∈ [-π, π]` enters the circulation. This file removes
the restriction: all hypotheses are on the interval of integration.

The method: a curve `γ` that is `C¹` on `[a, b]` is composed with the parameter
`smoothParam a b t = a + (b - a) * Real.smoothTransition t`, which is smooth on `ℝ`, takes
values in `[a, b]`, and is constant before `0` and after `1`. The composite is `C¹` on all of
`ℝ` and lies wherever `γ` does on `[a, b]`.

* `lineIntegral_comp_smoothParam`: the line integral of `B` along the composite over `[0, 1]`
  is the line integral along `γ` over `[a, b]`, for `γ` of class `C¹` on `[a, b]` and `B`
  continuous on the image.
* `intervalCurve`, `intervalPath`: the composite as a curve and as a loop in `U`.
* `lineIntegral_eq_periodHom`: **general closed curves.** For `B` of class `C¹` and curl-free on
  `U`, and `γ` of class `C¹` on `[a, b]` with values in `U` there and `γ a = γ b`, the
  circulation `lineIntegral B γ a b` is the period of `B♭` on the class of `intervalPath`.
* `intervalPath_homotopic`: when `γ` is continuous and in `U` on all of `ℝ`, `intervalPath` is
  homotopic to the loop `t ↦ γ (a + (b - a) t)`; so the class is that of
  `poloidalPath` in the poloidal case (`intervalPath_poloidal_homotopic`).
* `VacuumField.lineIntegral_eq_zero_of_simplyConnected`: a vacuum field on a simply connected
  region has zero circulation around such a curve. This is derived from the period: the
  fundamental group of the region is trivial, and the period homomorphism maps `0` to `0`.
* `poloidalCirculation_eq_periodHom_of_Icc`, `loopCurrent_eq_periodHom_div_of_Icc`,
  `VacuumField.poloidalCirculation_eq_zero_of_simplyConnected_of_Icc`,
  `VacuumField.loopCurrent_eq_zero_of_simplyConnected_of_Icc`: the poloidal statements with
  membership in `U` and `C¹` regularity on `[-π, π]` only.
* Periodic data: `poloidalLoop_periodic`, `poloidalLoop_closed_of_periodic`,
  `poloidalLoop_mem_of_periodic` (a `2π`-periodic loop closes up, and lies in `U` everywhere if
  it does on `[-π, π]`), their `FieldTorus` forms, and the period statements for a `FieldTorus`
  and for a surface of the contract clause `CurrentFreeTransform`, where closure is derived.

What is not proved: nothing is said about loops that are only piecewise `C¹`. The curve must be
`C¹` on the closed interval (one-sided at the end points); a corner at the base point
`γ a = γ b` is allowed, since no matching of the one-sided derivatives is assumed. The field is
required to be `C¹` and curl-free on the whole region `U`, not only near the loop.
-/

@[expose] public section

namespace PlasmaLean.Forms

open PlasmaLean.Vacuum PlasmaLean.Fields PlasmaLean.Contract
open TauCeti TopologicalSpace Topology
open scoped Manifold RealInnerProductSpace

/-! ## A smooth parameter with values in `[a, b]` -/

/-- The parameter `t ↦ a + (b - a) * Real.smoothTransition t`: smooth on `ℝ`, equal to `a` for
`t ≤ 0` and to `b` for `t ≥ 1`, with values in `[a, b]` when `a ≤ b`. -/
noncomputable def smoothParam (a b t : ℝ) : ℝ := a + (b - a) * Real.smoothTransition t

/-- The smooth parameter starts at `a`. -/
@[simp] theorem smoothParam_zero (a b : ℝ) : smoothParam a b 0 = a := by
  simp [smoothParam]

/-- The smooth parameter ends at `b`. -/
@[simp] theorem smoothParam_one (a b : ℝ) : smoothParam a b 1 = b := by
  simp [smoothParam]

/-- The smooth parameter stays in `[a, b]`. -/
theorem smoothParam_mem_Icc {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    smoothParam a b t ∈ Set.Icc a b := by
  have h0 := Real.smoothTransition.nonneg t
  have h1 := Real.smoothTransition.le_one t
  have hba : 0 ≤ b - a := sub_nonneg.2 hab
  constructor
  · unfold smoothParam
    nlinarith
  · unfold smoothParam
    nlinarith

/-- The smooth parameter is `C¹`. -/
theorem contDiff_smoothParam (a b : ℝ) : ContDiff ℝ 1 (smoothParam a b) :=
  contDiff_const.add (contDiff_const.mul (Real.smoothTransition.contDiff (n := 1)))

/-- A curve that is `C¹` on `[a, b]`, composed with the smooth parameter, is `C¹` on `ℝ`. -/
theorem contDiff_comp_smoothParam {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {γ : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b)) :
    ContDiff ℝ 1 fun t => γ (smoothParam a b t) :=
  hγ.comp_contDiff (contDiff_smoothParam a b) (smoothParam_mem_Icc hab)

/-- **Change of parameter on a closed interval.** For a curve `γ` of class `C¹` on `[a, b]` and
a field `B` continuous on the image of `[a, b]`, the line integral along `γ ∘ smoothParam a b`
over `[0, 1]` is the line integral along `γ` over `[a, b]`. -/
theorem lineIntegral_comp_smoothParam {B : Space → Space} {γ : ℝ → Space} {a b : ℝ}
    (hab : a < b) (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b))
    (hB : ContinuousOn B (γ '' Set.Icc a b)) :
    lineIntegral B (fun t => γ (smoothParam a b t)) 0 1 = lineIntegral B γ a b := by
  have hud : UniqueDiffOn ℝ (Set.Icc a b) := uniqueDiffOn_Icc hab
  set g : ℝ → ℝ := fun u => ⟪B (γ u), derivWithin γ (Set.Icc a b) u⟫ with hg
  have hgc : ContinuousOn g (Set.Icc a b) :=
    (hB.comp hγ.continuousOn (Set.mapsTo_image γ _)).inner
      (hγ.continuousOn_derivWithin hud le_rfl)
  have hs : ContDiff ℝ 1 (smoothParam a b) := contDiff_smoothParam a b
  have hsd (t : ℝ) : HasDerivAt (smoothParam a b) (deriv (smoothParam a b) t) t :=
    (hs.differentiable one_ne_zero t).hasDerivAt
  have hd (t : ℝ) : deriv (fun t => γ (smoothParam a b t)) t
      = deriv (smoothParam a b) t • derivWithin γ (Set.Icc a b) (smoothParam a b t) := by
    have hw : HasDerivWithinAt γ (derivWithin γ (Set.Icc a b) (smoothParam a b t))
        (Set.Icc a b) (smoothParam a b t) :=
      ((hγ.differentiableOn one_ne_zero) _ (smoothParam_mem_Icc hab.le t)).hasDerivWithinAt
    exact (hw.scomp_hasDerivAt t (hsd t) (smoothParam_mem_Icc hab.le)).deriv
  have hI : lineIntegral B (fun t => γ (smoothParam a b t)) 0 1
      = ∫ t in (0 : ℝ)..1, (g ∘ smoothParam a b) t * deriv (smoothParam a b) t := by
    unfold lineIntegral
    congr 1
    funext t
    rw [hd, inner_smul_right, mul_comm]
    rfl
  have himg : smoothParam a b '' Set.uIcc 0 1 ⊆ Set.Icc a b := by
    rintro _ ⟨t, -, rfl⟩
    exact smoothParam_mem_Icc hab.le t
  rw [hI, intervalIntegral.integral_comp_mul_deriv' (fun t _ => hsd t)
    (hs.continuous_deriv le_rfl).continuousOn (hgc.mono himg), smoothParam_zero,
    smoothParam_one, lineIntegral, intervalIntegral.integral_of_le hab.le,
    intervalIntegral.integral_of_le hab.le, MeasureTheory.integral_Ioc_eq_integral_Ioo,
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  simp only [hg]
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hu.1 hu.2)]

/-! ## Closed curves that are `C¹` on the interval of integration -/

section General

variable {U : Opens Space} {B : Space → Space} {γ : ℝ → Space} {a b : ℝ}

/-- The curve `γ`, traversed over `[a, b]` by the smooth parameter, as a curve in an open
region `U` that contains `γ t` for `t ∈ [a, b]`. -/
noncomputable def intervalCurve (γ : ℝ → Space) (hab : a ≤ b)
    (hU : ∀ t ∈ Set.Icc a b, γ t ∈ U) (t : ℝ) : U :=
  ⟨γ (smoothParam a b t), hU _ (smoothParam_mem_Icc hab t)⟩

/-- The value of `intervalCurve` as a point of space. -/
@[simp] theorem coe_intervalCurve (hab : a ≤ b) (hU : ∀ t ∈ Set.Icc a b, γ t ∈ U) (t : ℝ) :
    (intervalCurve γ hab hU t : Space) = γ (smoothParam a b t) :=
  rfl

/-- A curve that closes up over `[a, b]` gives a closed reparametrised curve. -/
theorem intervalCurve_one (hab : a ≤ b) (hU : ∀ t ∈ Set.Icc a b, γ t ∈ U)
    (hclosed : γ a = γ b) : intervalCurve γ hab hU 1 = intervalCurve γ hab hU 0 := by
  apply Subtype.ext
  simp only [coe_intervalCurve, smoothParam_one, smoothParam_zero]
  exact hclosed.symm

/-- The curve `γ` over `[a, b]` as a loop in the open region `U`, based at `γ a`. It needs `γ`
to be continuous on `[a, b]`, to lie in `U` there and to close up. -/
noncomputable def intervalPath (hab : a ≤ b) (hU : ∀ t ∈ Set.Icc a b, γ t ∈ U)
    (hcont : ContinuousOn γ (Set.Icc a b)) (hclosed : γ a = γ b) :
    Path (intervalCurve γ hab hU 0) (intervalCurve γ hab hU 0) where
  toFun t := intervalCurve γ hab hU t
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact hcont.comp_continuous
      ((contDiff_smoothParam a b).continuous.comp continuous_subtype_val)
      fun t => smoothParam_mem_Icc hab t
  source' := rfl
  target' := by simpa using intervalCurve_one hab hU hclosed

/-- **The circulation around a closed curve is a de Rham period.** For a field `B` that is `C¹`
and curl-free on the open region `U`, and a curve `γ` that is `C¹` on `[a, b]`, lies in `U`
there and closes up, the circulation of `B` along `γ` over `[a, b]` is the period of the closed
1-form `B♭` on the homotopy class of the loop. Nothing is assumed about `γ` outside `[a, b]`. -/
theorem lineIntegral_eq_periodHom (hB : ContDiffOn ℝ 1 B U)
    (hcurl : ∀ x ∈ U, fieldCurl B x = 0) (hab : a < b) (hU : ∀ t ∈ Set.Icc a b, γ t ∈ U)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b)) (hclosed : γ a = γ b) :
    lineIntegral B γ a b
      = periodHom (onOpens U fun y => flat (B y)) (intervalCurve γ hab.le hU 0)
          (Additive.ofMul (.of (.mk (intervalPath hab.le hU hγ.continuousOn hclosed)))) := by
  have himg : γ '' Set.Icc a b ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩
    exact hU t ht
  rw [periodHom_onOpens_flat hB hcurl (c := intervalCurve γ hab.le hU)
    (contDiff_comp_smoothParam hab.le hγ) (fun _ => rfl)]
  exact (lineIntegral_comp_smoothParam hab hγ (hB.continuousOn.mono himg)).symm

/-- **Consistency with the affine parametrisation.** When `γ` is continuous and lies in `U` for
every value of the parameter, the loop `intervalPath` is homotopic in `U` to the loop
`t ↦ γ (a + (b - a) t)`, `t ∈ [0, 1]`: the two differ by a change of parameter. -/
theorem intervalPath_homotopic (hab : a ≤ b) (hU : ∀ t, γ t ∈ U) (hcont : Continuous γ)
    (hclosed : γ a = γ b) {x : U} (p : Path x x)
    (hp : ∀ t : unitInterval, (p t : Space) = γ (a + (b - a) * t)) :
    ∃ hx : intervalCurve γ hab (fun t _ => hU t) 0 = x,
      (intervalPath hab (fun t _ => hU t) hcont.continuousOn hclosed).Homotopic
        (p.cast hx hx) := by
  have hx : intervalCurve γ hab (fun t _ => hU t) 0 = x := by
    apply Subtype.ext
    rw [coe_intervalCurve, smoothParam_zero, ← p.source, hp]
    simp
  refine ⟨hx, ?_⟩
  let f : unitInterval → unitInterval := fun t =>
    ⟨Real.smoothTransition t, Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hf : Continuous f :=
    (Real.smoothTransition.continuous.comp continuous_subtype_val).subtype_mk _
  have hf0 : f 0 = 0 := Subtype.ext (by simp [f])
  have hf1 : f 1 = 1 := Subtype.ext (by simp [f])
  have heq : intervalPath hab (fun t _ => hU t) hcont.continuousOn hclosed
      = (p.cast hx hx).reparam f hf hf0 hf1 := by
    refine Path.ext (funext fun t => Subtype.ext ?_)
    change γ (smoothParam a b t) = (p (f t) : Space)
    rw [hp]
    rfl
  rw [heq]
  exact ⟨(Path.Homotopy.reparam (p.cast hx hx) f hf hf0 hf1).symm⟩

/-- **Topology forbids a net circulation.** A vacuum field on a simply connected open region
has zero circulation around every curve that is `C¹` on `[a, b]`, lies in the region there and
closes up. The proof goes through the period: the loop class is trivial because the fundamental
group of the region is, and the period homomorphism vanishes on the trivial class. -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.lineIntegral_eq_zero_of_simplyConnected
    [SimplyConnectedSpace U] (h : VacuumField U B) (hab : a < b)
    (hU : ∀ t ∈ Set.Icc a b, γ t ∈ U) (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b))
    (hclosed : γ a = γ b) : lineIntegral B γ a b = 0 := by
  rw [lineIntegral_eq_periodHom (h.contDiffOn.of_le (by norm_num)) h.curl_eq_zero hab hU hγ
    hclosed]
  have h1 (g : FundamentalGroup U (intervalCurve γ hab.le hU 0)) :
      periodHom (onOpens U fun y => flat (B y)) (intervalCurve γ hab.le hU 0)
        (Additive.ofMul g) = 0 := by
    rw [Subsingleton.elim g 1, ofMul_one, map_zero]
  exact h1 _

end General

/-! ## The poloidal loop on `[-π, π]` -/

section Poloidal

variable {U : Opens Space} {B : Space → Space} {R z : ℝ → ℝ → ℝ} {φ₀ : ℝ}

/-- `-π < π`. -/
theorem neg_pi_lt_pi : -Real.pi < Real.pi := by
  linarith [Real.pi_pos]

/-- The poloidal loop of a torus whose profiles `R(·, φ₀)`, `z(·, φ₀)` are `C¹` on a set is
`C¹` on that set. -/
theorem contDiffOn_poloidalLoop {s : Set ℝ} (hR : ContDiffOn ℝ 1 (fun t => R t φ₀) s)
    (hz : ContDiffOn ℝ 1 (fun t => z t φ₀) s) : ContDiffOn ℝ 1 (poloidalLoop R z φ₀) s := by
  refine (contDiffOn_piLp 2).2 fun i => ?_
  fin_cases i
  · simpa [poloidalLoop, cylPoint] using hR.mul contDiffOn_const
  · simpa [poloidalLoop, cylPoint] using hR.mul contDiffOn_const
  · simpa [poloidalLoop, cylPoint] using hz

/-- **The poloidal circulation is a de Rham period, hypotheses on `[-π, π]` only.** For a field
`B` that is `C¹` and curl-free on the open region `U`, and a poloidal loop that is `C¹` on
`[-π, π]`, lies in `U` there and closes up, the circulation of `B` around the loop is the
period of the closed 1-form `B♭` on the homotopy class of the loop. -/
theorem poloidalCirculation_eq_periodHom_of_Icc (hB : ContDiffOn ℝ 1 B U)
    (hcurl : ∀ x ∈ U, fieldCurl B x = 0)
    (hU : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, poloidalLoop R z φ₀ θ ∈ U)
    (hγ : ContDiffOn ℝ 1 (poloidalLoop R z φ₀) (Set.Icc (-Real.pi) Real.pi))
    (hclosed : poloidalLoop R z φ₀ (-Real.pi) = poloidalLoop R z φ₀ Real.pi) :
    poloidalCirculation B R z φ₀
      = periodHom (onOpens U fun y => flat (B y))
          (intervalCurve (poloidalLoop R z φ₀) neg_pi_lt_pi.le hU 0)
          (Additive.ofMul (.of (.mk
            (intervalPath neg_pi_lt_pi.le hU hγ.continuousOn hclosed)))) :=
  lineIntegral_eq_periodHom hB hcurl neg_pi_lt_pi hU hγ hclosed

/-- **The Ampère loop current is a de Rham period divided by `μ₀`, hypotheses on `[-π, π]`
only.** -/
theorem loopCurrent_eq_periodHom_div_of_Icc (μ₀ : ℝ) (hB : ContDiffOn ℝ 1 B U)
    (hcurl : ∀ x ∈ U, fieldCurl B x = 0)
    (hU : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, poloidalLoop R z φ₀ θ ∈ U)
    (hγ : ContDiffOn ℝ 1 (poloidalLoop R z φ₀) (Set.Icc (-Real.pi) Real.pi))
    (hclosed : poloidalLoop R z φ₀ (-Real.pi) = poloidalLoop R z φ₀ Real.pi) :
    loopCurrent μ₀ B R z φ₀
      = periodHom (onOpens U fun y => flat (B y))
          (intervalCurve (poloidalLoop R z φ₀) neg_pi_lt_pi.le hU 0)
          (Additive.ofMul (.of (.mk
            (intervalPath neg_pi_lt_pi.le hU hγ.continuousOn hclosed)))) / μ₀ := by
  rw [loopCurrent, poloidalCirculation_eq_periodHom_of_Icc hB hcurl hU hγ hclosed]

/-- **Topology forbids a net current, hypotheses on `[-π, π]` only.** A vacuum field on a simply
connected open region has zero circulation around every poloidal loop that is `C¹` on
`[-π, π]`, lies in the region there and closes up. -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.poloidalCirculation_eq_zero_of_simplyConnected_of_Icc
    [SimplyConnectedSpace U] (h : VacuumField U B)
    (hU : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, poloidalLoop R z φ₀ θ ∈ U)
    (hγ : ContDiffOn ℝ 1 (poloidalLoop R z φ₀) (Set.Icc (-Real.pi) Real.pi))
    (hclosed : poloidalLoop R z φ₀ (-Real.pi) = poloidalLoop R z φ₀ Real.pi) :
    poloidalCirculation B R z φ₀ = 0 :=
  h.lineIntegral_eq_zero_of_simplyConnected neg_pi_lt_pi hU hγ hclosed

/-- **No net toroidal current in a simply connected vacuum region, hypotheses on `[-π, π]`
only.** -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.loopCurrent_eq_zero_of_simplyConnected_of_Icc
    [SimplyConnectedSpace U] (μ₀ : ℝ) (h : VacuumField U B)
    (hU : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, poloidalLoop R z φ₀ θ ∈ U)
    (hγ : ContDiffOn ℝ 1 (poloidalLoop R z φ₀) (Set.Icc (-Real.pi) Real.pi))
    (hclosed : poloidalLoop R z φ₀ (-Real.pi) = poloidalLoop R z φ₀ Real.pi) :
    loopCurrent μ₀ B R z φ₀ = 0 := by
  rw [loopCurrent, h.poloidalCirculation_eq_zero_of_simplyConnected_of_Icc hU hγ hclosed,
    zero_div]

/-- **The class is the one of `poloidalPath`.** Under the hypotheses of
`poloidalCirculation_eq_periodHom` (the loop is continuous and in `U` for every `θ`), the loop
`intervalPath` used here is homotopic in `U` to `poloidalPath`. -/
theorem intervalPath_poloidal_homotopic (hU : ∀ θ, poloidalLoop R z φ₀ θ ∈ U)
    (hcont : Continuous (poloidalLoop R z φ₀))
    (hclosed : poloidalLoop R z φ₀ Real.pi = poloidalLoop R z φ₀ (-Real.pi)) :
    ∃ hx : intervalCurve (poloidalLoop R z φ₀) neg_pi_lt_pi.le (fun θ _ => hU θ) 0
        = poloidalCurve hU 0,
      (intervalPath neg_pi_lt_pi.le (fun θ _ => hU θ) hcont.continuousOn hclosed.symm).Homotopic
        ((poloidalPath hU hcont hclosed).cast hx hx) :=
  intervalPath_homotopic neg_pi_lt_pi.le hU hcont hclosed.symm (poloidalPath hU hcont hclosed)
    fun _ => rfl

/-! ## Periodic surface data -/

/-- A torus whose profiles are `2π`-periodic in `θ` at `φ₀` has a `2π`-periodic poloidal
loop. -/
theorem poloidalLoop_periodic (hR : ∀ θ, R (θ + 2 * Real.pi) φ₀ = R θ φ₀)
    (hz : ∀ θ, z (θ + 2 * Real.pi) φ₀ = z θ φ₀) :
    Function.Periodic (poloidalLoop R z φ₀) (2 * Real.pi) := fun θ => by
  simp only [poloidalLoop, hR θ, hz θ]

/-- A `2π`-periodic poloidal loop closes up over `[-π, π]`. -/
theorem poloidalLoop_closed_of_periodic
    (hper : Function.Periodic (poloidalLoop R z φ₀) (2 * Real.pi)) :
    poloidalLoop R z φ₀ (-Real.pi) = poloidalLoop R z φ₀ Real.pi := by
  rw [← hper (-Real.pi)]
  congr 1
  ring

/-- A `2π`-periodic poloidal loop that lies in a set for `θ ∈ [-π, π]` lies in it for every
`θ`. -/
theorem poloidalLoop_mem_of_periodic {s : Set Space}
    (hper : Function.Periodic (poloidalLoop R z φ₀) (2 * Real.pi))
    (hU : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, poloidalLoop R z φ₀ θ ∈ s) (θ : ℝ) :
    poloidalLoop R z φ₀ θ ∈ s := by
  obtain ⟨y, hy, hxy⟩ := hper.exists_mem_Ico (by positivity) θ (-Real.pi)
  rw [hxy]
  refine hU y ⟨hy.1, ?_⟩
  have := hy.2
  linarith

/-- **Periodic data, period statement with `poloidalPath`.** For a `C¹` poloidal loop that is
`2π`-periodic and lies in `U` for `θ ∈ [-π, π]`, the hypotheses of
`poloidalCirculation_eq_periodHom` on membership for every `θ` and on closure are derived. -/
theorem poloidalCirculation_eq_periodHom_of_periodic (hB : ContDiffOn ℝ 1 B U)
    (hcurl : ∀ x ∈ U, fieldCurl B x = 0)
    (hper : Function.Periodic (poloidalLoop R z φ₀) (2 * Real.pi))
    (hU : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, poloidalLoop R z φ₀ θ ∈ U)
    (hγ : ContDiff ℝ 1 (poloidalLoop R z φ₀)) :
    poloidalCirculation B R z φ₀
      = periodHom (onOpens U fun y => flat (B y))
          (poloidalCurve (poloidalLoop_mem_of_periodic hper hU) 0)
          (Additive.ofMul (.of (.mk (poloidalPath (poloidalLoop_mem_of_periodic hper hU)
            hγ.continuous (poloidalLoop_closed_of_periodic hper).symm)))) :=
  poloidalCirculation_eq_periodHom hB hcurl _ hγ _

/-- **Periodic data, loop current.** -/
theorem loopCurrent_eq_periodHom_div_of_periodic (μ₀ : ℝ) (hB : ContDiffOn ℝ 1 B U)
    (hcurl : ∀ x ∈ U, fieldCurl B x = 0)
    (hper : Function.Periodic (poloidalLoop R z φ₀) (2 * Real.pi))
    (hU : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, poloidalLoop R z φ₀ θ ∈ U)
    (hγ : ContDiff ℝ 1 (poloidalLoop R z φ₀)) :
    loopCurrent μ₀ B R z φ₀
      = periodHom (onOpens U fun y => flat (B y))
          (poloidalCurve (poloidalLoop_mem_of_periodic hper hU) 0)
          (Additive.ofMul (.of (.mk (poloidalPath (poloidalLoop_mem_of_periodic hper hU)
            hγ.continuous (poloidalLoop_closed_of_periodic hper).symm)))) / μ₀ := by
  rw [loopCurrent, poloidalCirculation_eq_periodHom_of_periodic hB hcurl hper hU hγ]

/-- **Periodic data, simply connected region.** A vacuum field on a simply connected open
region has zero circulation around a `2π`-periodic poloidal loop that is `C¹` on `[-π, π]` and
lies in the region there. Closure is derived from periodicity. -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.poloidalCirculation_eq_zero_of_periodic
    [SimplyConnectedSpace U] (h : VacuumField U B)
    (hper : Function.Periodic (poloidalLoop R z φ₀) (2 * Real.pi))
    (hU : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, poloidalLoop R z φ₀ θ ∈ U)
    (hγ : ContDiffOn ℝ 1 (poloidalLoop R z φ₀) (Set.Icc (-Real.pi) Real.pi)) :
    poloidalCirculation B R z φ₀ = 0 :=
  h.poloidalCirculation_eq_zero_of_simplyConnected_of_Icc hU hγ
    (poloidalLoop_closed_of_periodic hper)

/-! ## The structures of the contract -/

variable {ι : ℝ}

/-- The poloidal loops of a `FieldTorus` are `2π`-periodic. -/
theorem _root_.PlasmaLean.Contract.FieldTorus.poloidalLoop_periodic (hT : FieldTorus B R z ι)
    (φ₀ : ℝ) : Function.Periodic (poloidalLoop R z φ₀) (2 * Real.pi) :=
  Forms.poloidalLoop_periodic (fun θ => hT.per_θ_R θ φ₀) (fun θ => hT.per_θ_z θ φ₀)

/-- The poloidal loops of a `FieldTorus` close up over `[-π, π]`. -/
theorem _root_.PlasmaLean.Contract.FieldTorus.poloidalLoop_closed (hT : FieldTorus B R z ι)
    (φ₀ : ℝ) : poloidalLoop R z φ₀ (-Real.pi) = poloidalLoop R z φ₀ Real.pi :=
  poloidalLoop_closed_of_periodic (hT.poloidalLoop_periodic φ₀)

/-- A poloidal loop of a `FieldTorus` that lies in a set for `θ ∈ [-π, π]` lies in it for every
`θ`. -/
theorem _root_.PlasmaLean.Contract.FieldTorus.poloidalLoop_mem (hT : FieldTorus B R z ι)
    {s : Set Space} (hU : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, poloidalLoop R z φ₀ θ ∈ s)
    (θ : ℝ) : poloidalLoop R z φ₀ θ ∈ s :=
  poloidalLoop_mem_of_periodic (hT.poloidalLoop_periodic φ₀) hU θ

/-- **The loop current of a `FieldTorus` is a de Rham period divided by `μ₀`.** The field is
`C¹` and curl-free on `U`; the poloidal loop is `C¹` on `[-π, π]` and lies in `U` there. That
the loop closes up is part of `FieldTorus`. -/
theorem _root_.PlasmaLean.Contract.FieldTorus.loopCurrent_eq_periodHom_div
    (hT : FieldTorus B R z ι) (μ₀ : ℝ) (hB : ContDiffOn ℝ 1 B U)
    (hcurl : ∀ x ∈ U, fieldCurl B x = 0)
    (hU : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, poloidalLoop R z φ₀ θ ∈ U)
    (hγ : ContDiffOn ℝ 1 (poloidalLoop R z φ₀) (Set.Icc (-Real.pi) Real.pi)) :
    loopCurrent μ₀ B R z φ₀
      = periodHom (onOpens U fun y => flat (B y))
          (intervalCurve (poloidalLoop R z φ₀) neg_pi_lt_pi.le hU 0)
          (Additive.ofMul (.of (.mk (intervalPath neg_pi_lt_pi.le hU hγ.continuousOn
            (hT.poloidalLoop_closed φ₀))))) / μ₀ :=
  loopCurrent_eq_periodHom_div_of_Icc μ₀ hB hcurl hU hγ (hT.poloidalLoop_closed φ₀)

/-- **A `FieldTorus` of a vacuum field in a simply connected region carries no net current.**
The poloidal loop is `C¹` on `[-π, π]` and lies in the region there. -/
theorem _root_.PlasmaLean.Contract.FieldTorus.loopCurrent_eq_zero_of_simplyConnected
    [SimplyConnectedSpace U] (hT : FieldTorus B R z ι) (μ₀ : ℝ) (h : VacuumField U B)
    (hU : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, poloidalLoop R z φ₀ θ ∈ U)
    (hγ : ContDiffOn ℝ 1 (poloidalLoop R z φ₀) (Set.Icc (-Real.pi) Real.pi)) :
    loopCurrent μ₀ B R z φ₀ = 0 :=
  h.loopCurrent_eq_zero_of_simplyConnected_of_Icc μ₀ hU hγ (hT.poloidalLoop_closed φ₀)

/-- **Clause C1 in a simply connected vacuum region.** For a family of surfaces satisfying the
contract clause `CurrentFreeTransform`, every surface whose poloidal loop lies, for
`θ ∈ [-π, π]`, in a simply connected open region on which `B` is a vacuum field has zero net
current. Periodicity and `C¹` regularity of the loop come from the clause. -/
theorem _root_.PlasmaLean.Contract.CurrentFreeTransform.current_eq_zero_of_simplyConnected
    [SimplyConnectedSpace U] {μ₀ Imax ιmin : ℝ} {S : Set SurfaceData}
    (hC : CurrentFreeTransform μ₀ B S Imax ιmin) (h : VacuumField U B) {s : SurfaceData}
    (hs : s ∈ S) (hU : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi, s.loop θ ∈ U) :
    s.current μ₀ B = 0 :=
  (hC.torus s hs).1.loopCurrent_eq_zero_of_simplyConnected μ₀ h hU
    (contDiff_poloidalLoop (hC.loop_R s hs) (hC.loop_z s hs)).contDiffOn

end Poloidal

end PlasmaLean.Forms
